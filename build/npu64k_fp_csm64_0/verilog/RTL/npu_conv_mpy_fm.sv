/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

//
// convolution multiplier array module
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv npu_conv_types.sv npu_conv_mpy_fm.sv
//

`include "npu_defines.v"
`include "npu_conv_macros.svh"

module npu_conv_mpy_fm
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter logic NPU_HAS_FLOAT = 1)
  (
   // Clock and reset
   input  logic                                            clk,        // Clock, all logic clocked at posedge
   input  logic                                            rst_a,      // Asynchronous reset, active high
   input  conv_mode_t                                      conv_mode,  // Convolution mode attribute
   input  logic                                            fm_en,      // enable pipeline
   input  mpy_cfg_t                                        mpy_cfg,    // 16b fm 
   output logic                                            busy,       // stall pipeline
   input  logic                                            first_row,  // first row in column
   input  stash_data_t                                     stash_data, // data from stash
   output mpy_fm_t       [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0] fm_out      // feature-map array output
   );
  // local wires
  logic    [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0]   fm_ren;           // feature-map register enable, broadcast over output channel and spatial dimension
  mpy_fm_t [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0]   fm_r;             // feature-map registers
  mpy_fm_t [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0]   fm_nxt;           // feature-map registers next state
  logic                                        delay_en;         // row delay line enable
  logic    [6:0]                               delay_row_r;      // row delay line
  logic    [6:0]                               delay_row_nxt;    // row delay line next state
  logic                                        inst_hi_r;
  logic                                        inst_hi_nxt;
  logic                                        inst_hi_en;
  logic                                        fm_dbl;

  
  //////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Functions
  //
  //////////////////////////////////////////////////////////////////////////////////////////////

  //
  // convert 2 8b values to input feature-map pair type
  //
  function automatic 
    mpy_fm_t                   // output is pair of int10,int8 values
    convert_fm(
               input pix_t i1, // msb/odd input
               input pix_t i0, // lsb/even input
               mpy_cfg_t   c   // multiplier configuration
               );
    // default output
    convert_fm = '0;
    // sign
    if (NPU_HAS_FLOAT && isfp16(c))
    begin
      logic [4:0] e;
      logic [3:0] int8_msb;
      // int8 has exponent, retain 0 and nan, adjust bias
      e                  = i1[6:2];
      convert_fm.sgn     = i1[7];
      convert_fm.nan     = &e;
      convert_fm.zero    = ~|e;
      int8_msb           = {e[4], ~{3{e[4]}}};
      convert_fm.int8    = {int8_msb, e[3:0]};
      // int10 has mantissa
      convert_fm.int10   = {i1[1:0], i0};
    end
    else if (NPU_HAS_FLOAT && isbf16(c))
    begin
      logic [7:0] e;
      // int8 has exponent
      e                  = {i1[6:0], i0[7]};
      convert_fm.sgn     = i1[7];
      convert_fm.nan     = &e;
      convert_fm.zero    = ~|e;
      convert_fm.int8    = e;
      // int10 has mantissa
      convert_fm.int10   = {i0[6:0],3'b000};
    end
    else //if (!NPU_HAS_FLOAT | ~(isbf16(c)|isfp16(c)))
    begin
      // always signed int8
      convert_fm.int8    = i1;
      // int10 to zero/sign extended int8
      if (c == i_16b8b_e || c == i_16b16b_e) 
      begin
        convert_fm.int10 = {2'd0,i0[7:0]};
      end
      else
      begin
        convert_fm.int10 = {{2{i0[7]}},i0[7:0]};
        convert_fm.sgn   = i0[7];
      end
    end
  endfunction : convert_fm


  //
  // function to shift some positions by two elements for depthwise layers
  //
  function automatic 
    mpy_fm_t [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0]                 // output one pairs of values per pair of multipliers
      init_nxt(
        input  mpy_fm_t [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0] ip,  // old state
        output logic    [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0] ten  // output enable
        );
    // default outputs
    ten      = '0;
    init_nxt = '0;
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
    for (int o = 0; o < ISIZE; o++)
    begin
      for (int v = 0; v < VSIZE; v++)
      begin
        for (int f = 0; f < 4; f++)
        begin
          init_nxt[v][o][ 1+f] = ip[v][o][ 0+f];
          init_nxt[v][o][ 6+f] = ip[v][o][ 5+f];
          init_nxt[v][o][11+f] = ip[v][o][10+f];
          ten     [v][o][ 1+f] = 1'b1;
          ten     [v][o][ 6+f] = 1'b1;
          ten     [v][o][11+f] = 1'b1;
        end
      end
    end
// spyglass enable_block SelfDeterminedExpr-ML
  endfunction : init_nxt

  
  //
  // shuffle and replicate vector for 3x? modes
  //
  function automatic
    pix_t [2:0][VSIZE-1:0][ISIZE-1:0] // output is stash data replicated over spatial dimensions
      shuf_s3(
        input stash_data_t ip         // input from stash
        );
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
    case (conv_mode)
    `VIVO(conv_mode_3x3dws1),
    `NINO(conv_mode_3x3dws1),
    `NINO(conv_mode_2x1s1):
      begin
        for (int v = 0; v < VSIZE; v++)
        begin
          for (int f = 0; f < 3; f++)
          begin
            shuf_s3[f][v] = ip[v+f];
          end
        end
      end
    `NINO(conv_mode_2x3dws2),
    `NINO(conv_mode_2x1g2s2),
    `NINO(conv_mode_2x1s2):
      begin
        for (int v = 0; v < VSIZE; v++)
        begin
          for (int f = 0; f < 2; f++)
          begin
            shuf_s3[f][v] = ip[2*v+f];
          end
        end
      end
    default: //      `NINO(conv_mode_3x3dws1dl2), `NINO(conv_mode_2x1s1dl2)
      begin
        for (int v = 0; v < VSIZE; v++)
        begin
          for (int f = 0; f < 3; f++)
          begin
            shuf_s3[f][v] = ip[v+2*f];
          end
        end
      end
    endcase // case (conv_mode)
// spyglass enable_block SelfDeterminedExpr-ML
  endfunction : shuf_s3



  //////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Assignments
  //
  //////////////////////////////////////////////////////////////////////////////////////////////
  assign fm_dbl = isfmdbl(mpy_cfg) || isfp(mpy_cfg);
  assign fm_out = fm_r;
  
  

  //////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Always blocks
  //
  //////////////////////////////////////////////////////////////////////////////////////////////


  // Feature-map register, next state
  // outputs: fm_ren, fm_nxt, inst_hi_nxt, inst_hi_en
  pix_t [VSIZE-1:0][ISIZE-1:0][2*ISIZE-1:0] nval;
  always_comb
  begin : fm_nxt_PROC
    pix_t [2:0][VSIZE-1:0][ISIZE-1:0]         s3;
    logic [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0]   nsel;
    // default outputs
    fm_nxt      = '0;
    fm_ren      = '0;
    inst_hi_nxt = 1'b0;
    inst_hi_en  = 1'b0;
    if ((conv_mode == `VIVO(conv_mode_3x3dws1)) || (conv_mode == `NINO(conv_mode_3x3dws1)) || (conv_mode == `NINO(conv_mode_2x3dws2)) || (conv_mode == `NINO(conv_mode_3x3dws1dl2)))
    begin
      logic [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0] ten; // enable from shifting
      // shift for 3x3 modes
      if (~inst_hi_r)
      begin
        fm_nxt |= init_nxt(fm_r, ten);
        fm_ren |= ten;
      end
    end
    s3 = shuf_s3(stash_data);
    // overlay new values on feature-map register
    nval = '0;
    nsel = '0;
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
    case (conv_mode)
    // depthwise
    `NINO(conv_mode_3x3dws1),
    `NINO(conv_mode_3x3dws1dl2):
      begin
        if (fm_dbl) 
        begin
          // insert at positions 0,1 10,11 20,21
          for (int o = 0; o < ISIZE/2; o++)
          begin
            for (int v = 0; v < VSIZE; v++)
            begin
              if (inst_hi_r) 
              begin
                nsel[v][o+ISIZE/2][0 ] |= 1'b1;
                nsel[v][o+ISIZE/2][5 ] |= 1'b1;
                nsel[v][o+ISIZE/2][10] |= 1'b1;
              end
              else 
              begin
                nsel[v][o        ][0 ] |= 1'b1;
                nsel[v][o        ][5 ] |= 1'b1;
                nsel[v][o        ][10] |= 1'b1;
              end
              nval[v][o        ][0 ] |= s3[0][v][o*2  ];
              nval[v][o        ][10] |= s3[1][v][o*2  ];
              nval[v][o        ][20] |= s3[2][v][o*2  ];
              nval[v][o        ][1 ] |= s3[0][v][o*2+1];
              nval[v][o        ][11] |= s3[1][v][o*2+1];
              nval[v][o        ][21] |= s3[2][v][o*2+1];
              nval[v][o+ISIZE/2][0 ] |= s3[0][v][o*2  ];
              nval[v][o+ISIZE/2][10] |= s3[1][v][o*2  ];
              nval[v][o+ISIZE/2][20] |= s3[2][v][o*2  ];
              nval[v][o+ISIZE/2][1 ] |= s3[0][v][o*2+1];
              nval[v][o+ISIZE/2][11] |= s3[1][v][o*2+1];
              nval[v][o+ISIZE/2][21] |= s3[2][v][o*2+1];
            end
          end
          inst_hi_nxt = ~inst_hi_r;
          inst_hi_en  = 1'b1;
        end
        else 
        begin
          // insert at even positions 0, 10, 20
          for (int o = 0; o < ISIZE; o++)
          begin
            for (int v = 0; v < VSIZE; v++)
            begin
              nsel[v][o][0 ] |= 1'b1;
              nsel[v][o][5 ] |= 1'b1;
              nsel[v][o][10] |= 1'b1;
              nval[v][o][0 ] |= s3[0][v][o];
              nval[v][o][10] |= s3[1][v][o];
              nval[v][o][20] |= s3[2][v][o];
            end
          end
        end // else: !if(fm_dbl)
      end // case: `NINO(conv_mode_3x3dws1),...
    `VIVO(conv_mode_3x3dws1):
      begin
        // insert at even positions 0, 10, 20
        for (int o = 0; o < ISIZE/2; o++)
        begin
          for (int v = 0; v < VSIZE; v++)
          begin
            nsel[v][o][0 ]         |= 1'b1;
            nsel[v][o][5 ]         |= 1'b1;
            nsel[v][o][10]         |= 1'b1;
            nsel[v][o+ISIZE/2][0 ] |= 1'b1;
            nsel[v][o+ISIZE/2][5 ] |= 1'b1;
            nsel[v][o+ISIZE/2][10] |= 1'b1;
            nval[v][o][0 ]         |= s3[0][v][o];
            nval[v][o][10]         |= s3[1][v][o];
            nval[v][o][20]         |= s3[0][v][o+ISIZE/2];
            nval[v][o+ISIZE/2][0 ] |= s3[0][v][o+ISIZE/2];
            nval[v][o+ISIZE/2][10] |= s3[1][v][o+ISIZE/2];
            nval[v][o+ISIZE/2][20] |= s3[1][v][o];
          end
        end
      end
    `NINO(conv_mode_2x3dws2):
      begin
        if (fm_dbl) 
        begin
          // insert at positions 0,1 10,11 
          for (int o = 0; o < ISIZE/2; o++)
          begin
            for (int v = 0; v < VSIZE; v++)
            begin
              if (inst_hi_r) 
              begin
                nsel[v][o+ISIZE/2][0 ] |= 1'b1;
                nsel[v][o+ISIZE/2][5 ] |= 1'b1;
              end
              else 
              begin
                nsel[v][o        ][0 ] |= 1'b1;
                nsel[v][o        ][5 ] |= 1'b1;
              end
              nval[v][o        ][0 ] |= s3[0][v][o*2  ];
              nval[v][o        ][10] |= s3[1][v][o*2  ];
              nval[v][o        ][1 ] |= s3[0][v][o*2+1];
              nval[v][o        ][11] |= s3[1][v][o*2+1];
              nval[v][o+ISIZE/2][0 ] |= s3[0][v][o*2  ];
              nval[v][o+ISIZE/2][10] |= s3[1][v][o*2  ];
              nval[v][o+ISIZE/2][1 ] |= s3[0][v][o*2+1];
              nval[v][o+ISIZE/2][11] |= s3[1][v][o*2+1];
            end
          end
          inst_hi_nxt = ~inst_hi_r;
          inst_hi_en  = 1'b1;
        end
        else 
        begin
          // insert at even positions 0, 10,
          for (int o = 0; o < ISIZE; o++)
          begin
            for (int v = 0; v < VSIZE; v++)
            begin
              nsel[v][o][0 ] |= 1'b1;
              nsel[v][o][5 ] |= 1'b1;
              nval[v][o][0 ] |= s3[0][v][o];
              nval[v][o][10] |= s3[1][v][o];
            end
          end
        end // else: !if(fm_dbl)
      end // case: `NINO(conv_mode_2x3dws2),...      
    `NINO(conv_mode_4x1dws1),
    `NINO(conv_mode_8x1dws1):
      begin
        if (fm_dbl) 
        begin
          // insert at positions 0..15
          for (int o = 0; o < ISIZE/2; o++)
          begin
            for (int v = 0; v < VSIZE; v++)
            begin
              for (int f = 0; f < 8; f++)
              begin
                if (inst_hi_r) 
                begin
                  nsel[v][o+ISIZE/2][f] |= 1'b1;
                end
                else 
                begin
                  nsel[v][o        ][f] |= 1'b1;
                end
                nval[v][o        ][2*f+0] |= stash_data[v+f][o*2  ];
                nval[v][o        ][2*f+1] |= stash_data[v+f][o*2+1];
                nval[v][o+ISIZE/2][2*f+0] |= stash_data[v+f][o*2  ];
                nval[v][o+ISIZE/2][2*f+1] |= stash_data[v+f][o*2+1];
              end
            end
          end
          inst_hi_nxt = ~inst_hi_r;
          inst_hi_en  = 1'b1;
        end
        else 
        begin
          // insert at positions 0..15
          for (int o = 0; o < ISIZE; o++)
          begin
            for (int v = 0; v < VSIZE; v++)
            begin
              for (int f = 0; f < 8; f++)
              begin
                nsel[v][o][f]     |= 1'b1;
                nval[v][o][2*f+0] |= stash_data[v+f][o];
              end
            end
          end
        end // else: !if(fm_dbl)
      end // case: `NINO(conv_mode_4x1dws1),...
    `NINO(conv_mode_4x1g2s1dl2):
      begin
        nsel |= '1;
        for (int i = 0; i < ISIZE/2; i++)
        begin
          for (int v = 0; v < VSIZE; v++)
          begin
            for (int o = 0; o < ISIZE/2; o++)
            begin
              nval[v][o        ][i          ] |= stash_data[v  ][i        ];
              nval[v][o        ][i+ISIZE/2  ] |= stash_data[v+2][i        ];
              nval[v][o        ][i+ISIZE    ] |= stash_data[v+4][i        ];
              nval[v][o        ][i+ISIZE/2*3] |= stash_data[v+6][i        ];
              nval[v][o+ISIZE/2][i          ] |= stash_data[v  ][i+ISIZE/2];
              nval[v][o+ISIZE/2][i+ISIZE/2  ] |= stash_data[v+2][i+ISIZE/2];
              nval[v][o+ISIZE/2][i+ISIZE    ] |= stash_data[v+4][i+ISIZE/2];
              nval[v][o+ISIZE/2][i+ISIZE/2*3] |= stash_data[v+6][i+ISIZE/2];
            end
          end
        end
      end
    `NINO(conv_mode_4x1g2s1):
      begin
        nsel |= '1;
        for (int i = 0; i < ISIZE/2; i++)
        begin
          for (int v = 0; v < VSIZE; v++)
          begin
            for (int o = 0; o < ISIZE/2; o++)
            begin
              nval[v][o        ][i          ] |= stash_data[v  ][i        ];
              nval[v][o        ][i+ISIZE/2  ] |= stash_data[v+1][i        ];
              nval[v][o        ][i+ISIZE    ] |= stash_data[v+2][i        ];
              nval[v][o        ][i+ISIZE/2*3] |= stash_data[v+3][i        ];
              nval[v][o+ISIZE/2][i          ] |= stash_data[v  ][i+ISIZE/2];
              nval[v][o+ISIZE/2][i+ISIZE/2  ] |= stash_data[v+1][i+ISIZE/2];
              nval[v][o+ISIZE/2][i+ISIZE    ] |= stash_data[v+2][i+ISIZE/2];
              nval[v][o+ISIZE/2][i+ISIZE/2*3] |= stash_data[v+3][i+ISIZE/2];
            end
          end
        end
      end
    `NINO(conv_mode_2x1g2s2):
      begin
      nsel |= '1;
        for (int v = 0; v < VSIZE; v++)
        begin
          for (int o = 0; o < ISIZE/2; o++)
          begin
            for (int i = 0; i < ISIZE/2; i++)
            begin
              nval[v][o        ][i        ] |= stash_data[2*v  ][i        ];
              nval[v][o        ][i+ISIZE/2] |= stash_data[2*v+1][i        ];
              nval[v][o+ISIZE/2][i        ] |= stash_data[2*v  ][i+ISIZE/2];
              nval[v][o+ISIZE/2][i+ISIZE/2] |= stash_data[2*v+1][i+ISIZE/2];
            end
          end
        end
      end
    `NINO(conv_mode_2x1s1),
    `NINO(conv_mode_2x1s2),
    `NINO(conv_mode_2x1s1dl2):
      begin
        nsel |= '1;
        for (int v = 0; v < VSIZE; v++)
        begin
          for (int i = 0; i < ISIZE; i++)
          begin
            for (int o = 0; o < ISIZE; o++)
            begin
              nval[v][o][i      ] |= s3[0][v][i];
              nval[v][o][i+ISIZE] |= s3[1][v][i];
            end
          end
        end
      end
    default: // `DINO(conv_mode_1x1), `NINO(conv_mode_1x1), `FC(conv_mode_fc)
      begin
        nsel |= '1;
        for (int v = 0; v < VSIZE; v++)
        begin
          for (int i = 0; i < ISIZE; i++)
          begin
            for (int o = 0; o < ISIZE; o++)
            begin
              nval[v][o][i      ] |= stash_data[v      ][i];
              nval[v][o][i+ISIZE] |= stash_data[v+VSIZE][i];
            end
          end
        end
      end
    endcase // case (conv_mode)
// spyglass enable_block SelfDeterminedExpr-ML

// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
    // overlay data
    for (int v = 0; v < VSIZE; v++)
    begin
      for (int i = 0; i < ISIZE; i++)
      begin
        for (int o = 0; o < ISIZE; o++)
        begin
          if (nsel[v][o][i])
          begin
            fm_nxt[v][o][i] |= convert_fm(nval[v][o][2*i+1], nval[v][o][2*i+0], mpy_cfg);
          end
        end
      end
    end
// spyglass enable_block SelfDeterminedExpr-ML
    fm_ren |= nsel;
    // always enable all in first cycle to clear feature-map
    if (first_row & (~inst_hi_r))
    begin
      fm_ren = '1;
    end
    // only enable if pipeline enabled
    if (~fm_en)
    begin
      fm_ren     = '0;
      inst_hi_en = 1'b0;
    end
  end : fm_nxt_PROC
  

  //
  // next state and control
  //
  // outputs: busy, delay_row_nxt, delay_en
  always_comb
  begin : ctrl_nxt_PROC
    // default outputs
    delay_row_nxt = '0;
    delay_en      = 1'b0;
    busy          = 1'b0;
    // mode dependent switch
    case (conv_mode)
    // depthwise
    `VIVO(conv_mode_3x3dws1),
    `NINO(conv_mode_3x3dws1):
      begin
        // v10ixpix_t per row
        // all cycles accept 1 line
        // busy during initial 2 lines per column
        busy             = first_row | (~fm_dbl && delay_row_r[0]) | (fm_dbl & (|delay_row_r[3:0] | (~inst_hi_r)));
        delay_row_nxt    = {1'b0, delay_row_r[4:0], first_row};
        delay_en         = busy;
      end
    `NINO(conv_mode_2x3dws2):
      begin
        // v16ixpix_t per row
        // all cycles accept 1 line
        // busy during initial 2 lines per column and even lines
        busy             = first_row | (|delay_row_r[1:0]) | (fm_dbl & (~inst_hi_r));
        delay_row_nxt[0] = (fm_dbl & ~inst_hi_r & ~first_row) ?  delay_row_r[0] 
                           : (first_row ? ~fm_dbl : ~delay_row_r[0]);
        delay_row_nxt[1] = fm_dbl & first_row;
        delay_en         = 1'b1;
      end
    `NINO(conv_mode_3x3dws1dl2):
      begin
        // v12ixpix_t per row
        // all cycles accept 1 line
        // busy during initial 4 lines per column
        busy          = first_row | (~fm_dbl && |delay_row_r[2:0]) | (fm_dbl & (|delay_row_r[6:0] | (~inst_hi_r)));
        delay_row_nxt = {delay_row_r[5:0], first_row};
        delay_en      = busy;
      end
    `NINO(conv_mode_4x1dws1),
    `NINO(conv_mode_8x1dws1):
      begin
        busy          = fm_dbl & (~inst_hi_r);
      end
    endcase // case (conv_mode)
    // gate with input enable
    if (~fm_en)
    begin
      delay_en    = 1'b0;
    end
  end : ctrl_nxt_PROC
  

  //
  // State registers
  //
  // outputs: inst_hi_r, delay_row_r, fm_r
  always_ff @(posedge clk or posedge rst_a)
  begin : state_reg_PROC
    if (rst_a == 1'b1)
    begin
      delay_row_r <= 3'b000;
      inst_hi_r   <= 1'b0;
      fm_r        <= '0;
    end
    else
    begin
      if (delay_en)
      begin
        delay_row_r <= delay_row_nxt;
      end
      if (inst_hi_en) 
      begin
        inst_hi_r <= inst_hi_nxt;
      end
      for (int i = 0; i < ISIZE; i++)
      begin
        for (int v = 0; v < VSIZE; v++)
        begin
          for (int o = 0; o < ISIZE; o++)
          begin
            if (fm_ren[v][o][i])
            begin
              fm_r[v][o][i] <= fm_nxt[v][o][i];
            end
          end
        end
      end
    end
  end : state_reg_PROC
  
endmodule : npu_conv_mpy_fm
