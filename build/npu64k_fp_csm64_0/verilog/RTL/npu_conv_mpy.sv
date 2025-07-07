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
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv npu_conv_types.sv npu_conv_mpy_fm.sv npu_conv_mpy_cf.sv npu_conv_mpy_ctrl.sv npu_conv_mpy.sv npu_conv_mpy_lane.sv npu_conv_mpy_prim.sv npu_conv_mpy_sum.sv npu_conv_mpy_mul.sv npu_conv_mpy_acc.sv
// analyze -format sverilog [list ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../npu_conv_types.sv ../npu_conv_mpy_fm.sv ../npu_conv_mpy_prim.sv ../npu_conv_mpy_cf.sv ../npu_conv_mpy_ctrl.sv ../npu_conv_mpy.sv ../npu_conv_mpy_lane.sv ../npu_conv_mpy_sum.sv ../npu_conv_mpy_mul.sv ../npu_conv_mpy_acc.sv]
//

`include "npu_defines.v"
`include "npu_conv_macros.svh"

module npu_conv_mpy
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter logic NPU_HAS_FLOAT = 1)
  (
   // Clock and reset
   input  logic                    clk,                 // Clock, all logic clocked at posedge
   input  logic                    rst_a,               // Asynchronous reset, active high
   // HLAPI interface
   input  logic                    hlapi_valid,         // Request new HLAPI start
   output logic                    hlapi_accept,        // Acknowledge new HLAPI start
   input  conv_hlapi_i_t           hlapi_i,             // HLAPI parameters
   // Stash interface
   input  logic                    stash_valid,         // Stash output to multipliers is valid
   output logic                    stash_accept,        // Multiplier accepts stash output
   input  stash_data_t             stash_data,          // Data from stash to multiplier
   // Coefficient interface
   input  logic                    coef_valid,          // Coefficient output to multipliers is valid
   output logic                    coef_accept,         // Multiplier accepts coefficient output
   input  coef_data_t              coef_data,           // Data from coefficients to multiplier
   input  logic                    coef_mode_fm,        // Matrix*Matrix indication 
   // AM read interface
   input  logic                    ar_valid,            // Accumulator is valid
   output logic                    ar_accept,           // Accumulator is accepted
   input  vyixacc_t                ar_acc,              // Read accumulators, double
   // AM write interface
   output logic                    aw_valid,            // Accumulator is valid
   input  logic                    aw_accept,           // Accumulator is accepted
   output vyixacc_t                aw_acc,              // Write accumulators, double
   output logic                    aw_keep,             // If true then to AM else to stream
   // Result handshake
   output logic                    hlapi_o_valid,       // HLAPI done handshake valid
   input  logic                    hlapi_o_accept       // HLAPI done handshake accept
   );
  //
  // Local wires
  //
  // Registered Attributes
  conv_mode_t                                          conv_mode;        // convolution mode attribute
  logic                                                onn;              // onn == 2
  logic                                                attr_en;          // hlapi is valid, capture mpy_cfg
  logic                                                del_r;            // hlapi is valid, Use to Gate mc2
  mpy_cfg_t                                            mpy_cfg;          // mpy_cfg
  // derived
  logic     [VSIZE-1:0][1:0]                           acc_en;           // even/odd row accumulator enable per column [dual][col]
  // stage 0 to stage 1 registers  
  logic                                                fm_en;            // feature-map input enable
  logic                                                fm_busy;          // if asserted, accept one more line before updating the iterator
  logic                                                fm_first_in_col;  // set for the first feature-map read in a column
  mpy_fm_t  [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0]          fm_in;            // feature-map registers
  logic                                                cf_en;            // coefficient input enable
  logic                                                ctrl_tgl;         // toggle control register
  logic     [1:0]                                      ctrl_sel;         // control register select
  logic                                                cf_first_in_tns;  // set for the first coefficient accept in the operation
  mpy_cf_t  [1:0][ISIZE-1:0][ISIZE-1:0]                cf_in;            // two sets of coefficient registers
  logic     [ISIZE-1:0]                                c_sel_nomerge;    // select even or odd set of coefficients
  logic     [ISIZE-1:0]                                c_sel_nomerge_r;  // select even or odd set of coefficients
  mpy_cf_t  [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0]          cf_sel;           // selected coefficients
  
  logic     [ISIZE-1:0][ISIZE/2-1:0][1:0][2:0]         ctrla_sel;        // even feature-map selector
  logic     [ISIZE-1:0][ISIZE/2-1:0][1:0][2:0]         ctrlb_sel;        // odd feature-map selector
  logic     [ISIZE-1:0][ISIZE/2-1:0][1:0][2:0]         ctrla_sel_r;      // even feature-map selector
  logic     [ISIZE-1:0][ISIZE/2-1:0][1:0][2:0]         ctrlb_sel_r;      // odd feature-map selector
  // stage 1 to stage 2 signals
  logic                                                mpy_en;           // multiplier output register enable
  mpy_fm_t  [VSIZE-1:0][ISIZE-1:0][ISIZE-1:0]          mpy_a;            // feature-map input
  // stage 2 to stage 3 signals
  logic                                                sum_en;           // summation output register enable
  // stage 3 to stage 4 signals
  logic                                                sn_en;            // summation/normalization output register enable
  logic                                                norm_en;          // normalization output register enable
  logic                                                a_init;           // initialize the accumulator (one cycle early)
  // accumulator serialization
  logic                                                iar_valid_r;      // accumulator read valid
  logic                                                iar_valid_nxt;    // valid next
  logic                                                iar_en;           // read accumulator register enable
  vyixacc_t                                            iar_r;            // accumulator read buffer
  logic                                                iar_valid;        // accumulator read valid
  logic                                                iar_accept;       // accumulator read accept
  vyixacc_t   [1:0]                                    iar_acc;          // accumulator read data
  logic                                                iaw_valid_r;      // accumulator writebuffer valid
  logic                                                iaw_valid_nxt;    // valid next
  logic                                                iaw_keep_r;       // accumulator to AM or stream
  logic                                                iaw_keep_nxt;     // accumulator to AM or stream
  logic                                                iaw_en;           // write accumulator register enable
  vyixacc_t                                            iaw_r;            // accumulator buffer
  vyixacc_t                                            iaw_nxt;
  vyixacc_t   [1:0]                                    iaw_acc;          // accumulator write data
  logic                                                iaw_valid;        // accumulator write valid
  logic                                                iaw_accept;       // accumulator write accept
  logic                                                iaw_keep;         // accumulator to AM or stream
  // Internal AM write interface to skid buffer
  logic                                                aws_valid;        // Accumulator is valid
  logic                                                aws_accept;       // Accumulator is accepted
  vyixacc_t                                            aws_acc;          // Write accumulators, double
  logic                                                aws_keep;         // If true then to AM else to stream
  logic                                                aws_int_valid;
  // buffer has valid accumulator
  logic                                                aw_buf_valid;

 
  //
  // Stage 0: Feature-map and coefficient registers
  //


  npu_conv_mpy_fm #(.NPU_HAS_FLOAT(NPU_HAS_FLOAT))
  u_fm_inst
    (
     .clk        ( clk             ),
     .rst_a      ( rst_a           ),
     .conv_mode  ( conv_mode       ),
     .fm_en      ( fm_en           ),
     .mpy_cfg    ( mpy_cfg         ),
     .busy       ( fm_busy         ),
     .first_row  ( fm_first_in_col ),
     .stash_data ( stash_data      ),
     .fm_out     ( fm_in           )
    );


  // coefficient mapping
  npu_conv_mpy_cf #(.NPU_HAS_FLOAT(NPU_HAS_FLOAT))
  u_cf_inst
    (
     .clk          ( clk             ),
     .rst_a        ( rst_a           ),
     .mpy_cfg      ( mpy_cfg         ),
     .conv_mode    ( conv_mode       ),
     .coef_mode_fm ( coef_mode_fm    ),
     .onn          ( onn             ),
     .cf_en        ( cf_en           ),
     .ctrl_tgl     ( ctrl_tgl        ),
     .ctrl_sel     ( ctrl_sel        ),
     .cf_first     ( cf_first_in_tns ),
     .coef_data    ( coef_data       ),
     .cf_out       ( cf_in           ),
     .ctrla_out    ( ctrla_sel       ),
     .ctrlb_out    ( ctrlb_sel       )
   );  

  
  //
  // Stage 1: Coefficient bank select and multiplier stage
  //


  always_ff @(posedge clk or posedge rst_a)
  begin : state_reg_PROC
    if (rst_a ==  1'b1)
    begin
      c_sel_nomerge_r <= '1;
      ctrla_sel_r     <= '0;
      ctrlb_sel_r     <= '0;
    end
    else
    begin
      if (cf_en | ctrl_tgl)
      begin
        ctrla_sel_r <= ctrla_sel;
        ctrlb_sel_r <= ctrlb_sel;
      end
      if (ctrl_tgl)
      begin
        c_sel_nomerge_r <= ~c_sel_nomerge_r;
      end
    end
  end :  state_reg_PROC

  
  // bank select
  // outputs: cf_sel
  always_comb
  begin : cf_sel_PROC
    for (int v = 0; v < VSIZE; v++)
    begin
      for (int i=0;i<ISIZE;i++)
      begin
        // seems to be better for area and congestion vs the |= approach
        cf_sel[v][i] = c_sel_nomerge_r[i] ? cf_in[0][i] : cf_in[1][i];
      end
    end
  end : cf_sel_PROC


  // multiplier array feature-map input selection
  // result is signed  int10 input for even, signed int9 for odd
  // output: mpy_a
  always_comb
  begin : mpy_nxt_PROC
    mpy_a = '0;
    for (int o = 0; o < ISIZE; o++) 
    begin
      for (int i = 0; i < ISIZE/2; i++) 
      begin
        logic [1:0][2:0] ca;
        logic [1:0][2:0] cb;
        ca = ctrla_sel_r[o][i];
        cb = ctrlb_sel_r[o][i];
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression
//SJ :Ignore (i * 4)
        for (int v = 0; v < VSIZE; v++) 
        begin
          mpy_a[v][o][i*2+0].nan  = fm_in[v][o][i*2+0].nan & ca[0][0];
          mpy_a[v][o][i*2+0].zero = fm_in[v][o][i*2+0].zero | (~ca[0][0]);
          mpy_a[v][o][i*2+0].sgn  = (fm_in[v][o][i*2+0].sgn & ca[0][0])|(fm_in[v][o][i*2+0].int8[7] & ca[0][1]) | (fm_in[v][o][i*2+1].sgn & ca[0][2]) ;
          mpy_a[v][o][i*2+0].int10 = ({10{ca[0][0]}} &                                  fm_in[v][o][i*2+0].int10)      |
                                     ({10{ca[0][1]}} & {{2{fm_in[v][o][i*2+0].int8[7]}},fm_in[v][o][i*2+0].int8})      |
                                     ({10{ca[0][2]}} &                                  fm_in[v][o][i*2+1].int10);
          mpy_a[v][o][i*2+0].int8  = ({ 8{ca[1][0]}} &                                  fm_in[v][o][i*2+0].int10[7:0]) |
                                     ({ 8{ca[1][1]}} &                                  fm_in[v][o][i*2+0].int8)       |
                                     ({ 8{ca[1][2]}} &                                  fm_in[v][o][i*2+1].int10[7:0]);
          mpy_a[v][o][i*2+1].nan  = fm_in[v][o][i*2+1].nan & cb[0][1];
          mpy_a[v][o][i*2+1].zero = fm_in[v][o][i*2+1].zero | (~cb[0][1]);
          mpy_a[v][o][i*2+1].sgn  = ( fm_in[v][o][i*2+0].int8[7]& cb[0][0]) | (fm_in[v][o][i*2+1].int8[7] & cb[0][2]) | (fm_in[v][o][i*2+1].sgn & cb[0][1]);
          mpy_a[v][o][i*2+1].int10 = ({10{cb[0][0]}} & {{2{fm_in[v][o][i*2+0].int8[7]}},fm_in[v][o][i*2+0].int8})      |
                                     ({10{cb[0][1]}} &                                  fm_in[v][o][i*2+1].int10)      |
                                     ({10{cb[0][2]}} & {{2{fm_in[v][o][i*2+1].int8[7]}},fm_in[v][o][i*2+1].int8}); 
          mpy_a[v][o][i*2+1].int8  = ({ 8{cb[1][0]}} &                                  fm_in[v][o][i*2+0].int8)       |
                                     ({ 8{cb[1][1]}} &                                  fm_in[v][o][i*2+1].int10[7:0]) |
                                     ({ 8{cb[1][2]}} &                                  fm_in[v][o][i*2+1].int8); 
        end
// spyglass enable_block SelfDeterminedExpr-ML
      end // for (int i = 0; i < ISIZE/2; i++)
    end // for (int o = 0; o < ISIZE; o++)
  end : mpy_nxt_PROC
  

  //
  // Stage 1 multipliers, stage 2 wallace tree, stage 3 normalization, stage 4 accumulation
  //

  for (genvar gv = 0; gv < VSIZE; gv++)
  begin : v_GEN
    ixacc_t [1:0]            ai;
    ixacc_t [1:0]            ao;
    // take a slice from the i/o accumulators
    assign ai                               = {iar_acc[1][gv], iar_acc[0][gv]};
    assign {iaw_acc[1][gv], iaw_acc[0][gv]} = ao;

    // lane instance
    npu_conv_mpy_lane #(.NPU_HAS_FLOAT(NPU_HAS_FLOAT))
    u_lane_inst
      (
       .clk     ( clk                       ),
       .rst_a   ( rst_a                     ),
       .mpy_cfg ( mpy_cfg                   ),
       .acc_en  ( acc_en[gv]                ),
       .mpy_en  ( mpy_en                    ),
       .sum_en  ( sum_en                    ),
       .sn_en   ( sn_en                     ),
       .norm_en ( norm_en                   ),
       .mpy_a   ( mpy_a[gv]                 ),
       .mpy_b   ( cf_sel[gv]                ),
       .a_init  ( a_init                    ),
       .ar_acc  ( ai                        ),
       .aw_acc  ( ao                        )
       );
  end : v_GEN


  //
  // Stage 3: Accumulator read, deserialization and accumulation
  //
  // next state of accumulator read buffer
  // outputs: iar_valid_nxt, iar_en, iar_valid, ar_accept
  assign iar_acc       = {ar_acc,iar_r};
  always_comb
  begin : acc_in_PROC
    // default outputs
    iar_valid     = 1'b0;
    iar_valid_nxt = 1'b0;
    ar_accept     = 1'b0;
    iar_en        = 1'b0;
    case (mpy_cfg)
    i_16b16b_e,
    i_sparse_e:
      begin
        // 48b or 2*32b integer input, collect two input accumulators
        if (iar_valid_r) 
        begin
          // buffer has valid data
          iar_valid_nxt = (~iar_accept) | (~ar_valid);
          iar_valid     = ar_valid;
          ar_accept     = iar_accept;
        end
        else 
        begin
          // buffer is empty
          iar_valid_nxt = ar_valid;
          iar_en        = ar_valid;
          ar_accept     = 1'b1;
        end
      end
    default:
      begin
        // 32b floating-point or integer input, always on low
        if (iar_valid_r) 
        begin
          iar_valid     = 1'b1;
          iar_valid_nxt = (~iar_accept) | ar_valid;
          ar_accept     = iar_accept;
          iar_en        = ar_valid & iar_accept;
        end
        else
        begin
          iar_valid_nxt = ar_valid;
          iar_en        = ar_valid;
          ar_accept     = 1'b1;
        end
      end
    endcase // case (mpy_cfg)
  end : acc_in_PROC
  

  // store input accumulator
  // outputs: iar_valid_r, iar_r
  always_ff @(posedge clk or posedge rst_a)
  begin : ar_reg_PROC
    if (rst_a == 1'b1)
    begin
      iar_valid_r <= 1'b0;
      iar_r       <= '0;
    end
    else 
    begin
      iar_valid_r <= iar_valid_nxt;
      if (iar_en)
      begin
        iar_r     <= ar_acc;
      end
    end
  end : ar_reg_PROC

  
  //
  // Stage 4: Accumulator serialization and write
  //
  // next state of write accumulator serialization buffer
  // outputs: aws_acc, iaw_nxt, iaw_valid_nxt, iaw_keep_nxt, iaw_en, aws_valid, iaw_accept, aws_keep
  assign iaw_keep_nxt  = iaw_keep;
  assign iaw_nxt       = iaw_acc[1];
  always_comb 
  begin : acc_out_PROC
    // default outputs
    aws_valid     = 1'b0;
    iaw_accept    = 1'b0;
    iaw_valid_nxt = 1'b0;
    iaw_en        = 1'b0;
    // select output
    if (iaw_valid_r)
    begin
      aws_keep     = iaw_keep_r;
      aws_acc      = iaw_r;
    end
    else
    begin
      aws_keep     = iaw_keep;
      aws_acc      = iaw_acc;
    end
    // next state
    case (mpy_cfg)
    i_sparse_e,
    i_16b16b_e:
      begin
        // double accumulator: serialize two output accumulators
        if (iaw_valid_r) 
        begin
          // buffer has valid data
          aws_valid     = 1'b1;
          iaw_accept    = 1'b0;
          iaw_valid_nxt = ~aws_accept;
        end
        else 
        begin
          // buffer is empty, first acc transparent from lane 0
          aws_valid     = iaw_valid;
          iaw_valid_nxt = iaw_valid&aws_accept;
          iaw_en        = iaw_valid&aws_accept;
          iaw_accept    = aws_accept;
        end
      end
    f_bfloat16_e,f_fp16_e:
      begin
        // in fp mode, iaw_r is always used, to allow extra
        // cycle for normalization of accumulator
        if (iaw_valid_r)
        begin
          // buffer has valid data
          aws_valid     = 1'b1;  
          iaw_valid_nxt = iaw_valid | (~aws_accept);
          iaw_en        = iaw_valid & aws_accept;
          iaw_accept    = aws_accept;
        end
        else
        begin
          // no valid data in buffer
          aws_valid     = 1'b0;
          iaw_valid_nxt = iaw_valid;
          iaw_en        = iaw_valid;
          iaw_accept    = 1'b1;
        end
      end
    default:
      begin
        // other modes use low accumulator only, transparently
        aws_valid     = iaw_valid;
        iaw_accept    = aws_accept;
      end
    endcase // case (mpy_cfg)
  end : acc_out_PROC
  
  
  // store odd write accumulator
  // outputs: iaw_valid_r, iaw_keep_r, iaw_r
  always_ff @(posedge clk or posedge rst_a)
  begin : aw_reg_PROC
    if (rst_a == 1'b1)
    begin
      iaw_valid_r  <= 1'b0;
      iaw_keep_r   <= 1'b0;
      iaw_r        <= '0;
    end
    else 
    begin
      iaw_valid_r  <= iaw_valid_nxt;
      if (iaw_en)
      begin
        iaw_r      <= iaw_nxt;
        iaw_keep_r <= iaw_keep_nxt;
      end
    end
  end : aw_reg_PROC
    

  //
  // AM write skid buffer
  //
  npu_skid
  #(
    .W ( $bits(vyixacc_t)+1 )
  )
  u_am_skid_inst
  (
    .clk          ( clk                ),   // clock
    .rst_a        ( rst_a              ),   // asynchronous reset, active high, synchronous deassertion
    .in_valid     ( aws_valid          ),   // input data valid
    .in_accept    ( aws_accept         ),   // accept input data
    .in_data      ( {aws_acc,aws_keep} ),   // input data
    .int_valid    ( aws_int_valid      ),   // internal state valid
    .out_valid    ( aw_valid           ),   // output data valid
    .out_accept   ( aw_accept          ),   // accept output data
    .out_data     ( {aw_acc,aw_keep}   )    // output data
  );
  
  
  //
  // Pipeline controller
  //
  assign aw_buf_valid = iaw_valid_r | aws_int_valid;
  npu_conv_mpy_ctrl
  #(
    .NPU_HAS_FLOAT(NPU_HAS_FLOAT)
  )
  u_ctrl_inst
  (
   .clk             ( clk             ),
   .rst_a           ( rst_a           ),
   .hlapi_valid     ( hlapi_valid     ),
   .hlapi_accept    ( hlapi_accept    ),
   .hlapi_i         ( hlapi_i         ),
   .stash_valid     ( stash_valid     ),
   .stash_accept    ( stash_accept    ),
   .coef_valid      ( coef_valid      ),
   .coef_accept     ( coef_accept     ),
   .ar_valid        ( iar_valid       ),
   .ar_accept       ( iar_accept      ),
   .aw_valid        ( iaw_valid       ),
   .aw_accept       ( iaw_accept      ),
   .aw_keep         ( iaw_keep        ),
   .aw_buf_valid    ( aw_buf_valid    ),
   .hlapi_o_valid   ( hlapi_o_valid   ),
   .hlapi_o_accept  ( hlapi_o_accept  ),
   .fm_en           ( fm_en           ),
   .fm_first_in_col ( fm_first_in_col ),
   .fm_busy         ( fm_busy         ),
   .cf_en           ( cf_en           ),
   .ctrl_tgl        ( ctrl_tgl        ),
   .ctrl_sel        ( ctrl_sel        ),
   .cf_first_in_tns ( cf_first_in_tns ),
   .mpy_en          ( mpy_en          ),
   .sum_en          ( sum_en          ),
   .sn_en           ( sn_en           ),
   .norm_en         ( norm_en         ),
   .a_init          ( a_init          ),
   .conv_mode       ( conv_mode       ),
   .onn             ( onn             ),
   .mpy_cfg         ( mpy_cfg         ),
   .del_r           ( del_r           ),
   .attr_en         ( attr_en         ),
   .acc_en          ( acc_en          )
   );

  
endmodule : npu_conv_mpy

