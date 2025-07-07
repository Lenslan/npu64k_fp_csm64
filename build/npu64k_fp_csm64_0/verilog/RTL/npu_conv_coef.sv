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
// convolution coefficient fetching module
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_fifo.sv ../../shared/RTL/npu_vm_read.sv npu_conv_types.sv npu_conv_coef_pipe.sv npu_conv_coef.sv
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_fifo.sv ../../../shared/RTL/npu_vm_read.sv ../npu_conv_types.sv ../npu_conv_coef_pipe.sv ../npu_conv_coef.sv"
//
 
`include "npu_defines.v"
`include "npu_vm_macros.svh"
`include "npu_conv_macros.svh"

module npu_conv_coef
  import npu_types::*;
  import npu_conv_types::*;
  #(
    parameter int NL2 = $clog2(NUM_COEF_QUEUE)         // Log 2 of number of parallel coeficient decoders
   )
  (
   //
   // Clock and reset
   //
   input  logic          clk,                          // Clock, all logic clocked at posedge
   input  logic          rst_a,                        // Asynchronous reset, active high
   // HLAPI interface
   input  logic          hlapi_valid,                  // Request new HLAPI start
   output logic          hlapi_accept,                 // Acknowledge new HLAPI start
   input  conv_hlapi_i_t hlapi_i,                      // HLAPI parameters
   //
   // External interfaces
   //
   `VMRMST((1<<NL2),vm_rd_),                           // 2^NL2 bank VM coefficient read interface
   //
   // Interface to MAC array
   //
   output logic          coef_valid,                   // Coefficient output to multipliers is valid
   input  logic          coef_accept,                  // Multiplier accepts coefficient output
   output logic          coef_mod_fm,                  // Matrix*Matrix indication                    
   output coef_data_t    coef_data                     // Data from coefficients to multiplier
   );
  //
  // Local parameters
  //
  localparam int N   = 1<<NL2;                // number of decoding pipelines
  localparam int B   = 1024/16;               // number of coefficient atoms
  localparam int BL2 = 7;                     // level counter width
  //
  // Types
  //
  // number of zero-points
  typedef enum logic [1:0] { zp16_e, zp32_e, zp128_e, zp256_e } zp_t;
  // zero-point loading state
  typedef enum logic [1:0] { zp_state_idle_e, zp_state_first_e, zp_state_second_e, zp_state_coef_e } zp_state_t;
  //
  // Local wires
  //
  // pipeline flow control
  logic                        soft_rst_nxt;  // reset after undefined length coefficient block has been read
  logic                        soft_rst_r;    // reset after undefined length coefficient block has been read
  logic       [N:0]            in_valid;      // parallel decoded coefficient block inputs
  logic       [N:0]            in_accept;
  logic       [N-1:0]          dec_valid;     // parallel decoded coefficient block outputs
  logic       [N-1:0]          dec_accept;
  coef_atom_t [N-1:0]          dec_atom;
  // HLAPI attributes registers
  logic                        attr_en;
  logic                        cf_dw3_r;      // 3x3 depthwise mode
  logic                        cf_dw3_nxt;    // next state
  coef_mode_t                  cf_mode_r;
  logic                        cf_4b_r;
  logic                        cf_zp_r;
  logic    [N-1:0]             cf_zp_nomerge_r;
  zp_t                         cf_zp_num_r;   // number of zero-points blocks to load, 16, 32, 128 or 256
  zp_t                         cf_zp_num_nxt;
  logic       [BL2-1:0]        cf_cnum_r;     // number of coefficients atoms to decode
  logic       [BL2-1:0]        cf_cnum_nxt;
  offset_t                     cf_padlim_r;
  offset_t                     cf_limit;
  logic       [4:0]            cf_bsmax_r;    // worst-case coefficient block length
  logic       [4:0]            cf_bsmax_nxt;  // worst-case coefficient block length next
  // pipeline counters
  logic                        pcnt_en;       // enable pipeline counter
  logic       [NL2-1:0]        pcnt_r;        // pipeline counter register
  logic       [NL2-1:0]        pcnt_nxt;      // pipeline counter register, next
  // padding logic for matmat mode
  logic                        pad_valid;
  logic                        pad_accept;
  logic       [3:0]            pad_last;
  // rotated dec pipeline signals
  logic       [N-1:0]          rot_valid;
  logic       [1:0][N-1:0]     dec_acceptd;   // rotated accept
  logic       [N-1:0]          rot_accept;
  coef_atom_t [N-1:0]          rot_atom;
  // decoding state
  logic                        zp_state_en;
  zp_state_t                   zp_state_r;
  zp_state_t  [N-1:0]          zp_state_nomerge_r;
  zp_state_t                   zp_state_nxt;
  // zero-point register
  logic                        zp_ld;         // load zero-point in first inn&qd
  logic  [N-1:0]               zp_ld_nomerge;         // load zero-point in first inn&qd
  logic                        coef_ld;       // load coefficients
  logic                        zp_val;        // zero-point valid
  logic                        zp_en;         // zero-point enable
  coef_t    [1:0][8*ISIZE-1:0] zp_r;          // register
  coef_t    [1:0][8*ISIZE-1:0] zp_nxt;        // next state
  coef_t      [1:0][ISIZE-1:0] zp_tmp;        // fc rotate reg
  // iterator interface
  offset_t    [4:0]            ziter;
  logic                        zit_req;
  logic                        zit_ack;
  logic                        ziti_ack;
  logic       [4:0]            zit_last;
  // append new elements to buffer
  logic       [B-1:0]          buf_en_tmp;
  logic       [BL2-1:0]        lvl_tmp;
  // output buffer
  logic                        lvl_en;        // enable level register
  logic       [BL2-1:0]        lvl_r;         // count atoms, max level=1024/16=64
  logic       [BL2-1:0]        lvl_nxt;       // count atoms, max level=1024/16=64 next
  logic       [B-1:0]          buf_en;        // buffer atom enable
  coef_atom_t [B-1:0]          buf_r;         // atom output buffer
  coef_atom_t [B-1:0]          buf_nxt;       // atom output buffer next
 

  //
  // Store HLAPI attributes
  //
  assign attr_en      = hlapi_valid & hlapi_accept;
  assign cf_dw3_nxt   = (hlapi_i.conv_mode == `NINO(conv_mode_3x3dws1)) ||
                        (hlapi_i.conv_mode == `VIVO(conv_mode_3x3dws1)) ||
                        (hlapi_i.conv_mode == `NINO(conv_mode_3x3dws1dl2));
  assign coef_mod_fm  = (cf_mode_r == coef_mode_fm);

  logic fm_dbl,cf_dbl,cf_4b,cf_zp;
  assign fm_dbl = hlapi_i.fm_cfg==fm_cfg_16b_e;
  assign cf_dbl = hlapi_i.cf_cfg==cf_cfg_16b_e;
  assign cf_4b = hlapi_i.cf_cfg==cf_cfg_4b_zp_e || hlapi_i.cf_cfg==cf_cfg_4b_nozp_e;
  assign cf_zp = hlapi_i.cf_cfg==cf_cfg_4b_zp_e || hlapi_i.cf_cfg==cf_cfg_8b_zp_e;

  logic is_conv_mode_fc;
  assign is_conv_mode_fc = hlapi_i.conv_mode==`FC(conv_mode_fc);

  // determine number of coefficient blocks for mode
  // outputs: cnum_nxt, cf_limit, cf_zp_num_nxt
  always_comb
  begin : cnum_PROC
    // decode coefficients
    casez ({hlapi_i.conv_mode,fm_dbl,cf_dbl})
    {`NINO(conv_mode_4x1g2s1),1'b?,1'b?},
    {`NINO(conv_mode_4x1g2s1dl2),1'b?,1'b?}:
      begin
        // grouped convolution requires 4*1*2*(ISIZE/2)*(ISIZE/2)=384 coefficients
        // no support for 16b fm or 16b cf
        cf_cnum_nxt = $unsigned(4*1*2*(ISIZE/2)*(ISIZE/2)/16);
      end
    {`DINO(conv_mode_1x1),1'b0,1'b0},
    {`NINO(conv_mode_2x1s1),1'b0,1'b0},
    {`NINO(conv_mode_2x1s2),1'b0,1'b0},
    {`NINO(conv_mode_2x1s1dl2),1'b0,1'b0},
    {`DINO(conv_mode_1x1),1'b1,1'b1},
    {`NINO(conv_mode_2x1s1),1'b1,1'b1},
    {`NINO(conv_mode_2x1s2),1'b1,1'b1},
    {`NINO(conv_mode_2x1s1dl2),1'b1,1'b1}:
      begin
        // normal convolution 8*8 or 16b*16b using 2*1*ISIZE*ISIZE=512 coefficients
        cf_cnum_nxt = $unsigned(2*1*ISIZE*ISIZE/16);
      end
    {`DINO(conv_mode_1x1),1'b0,1'b1},
    {`NINO(conv_mode_2x1s1),1'b0,1'b1},
    {`NINO(conv_mode_2x1s2),1'b0,1'b1},
    {`NINO(conv_mode_2x1s1dl2),1'b0,1'b1}:
      begin
        // normal convolution 8*16 using 2*2*1*ISIZE*ISIZE=1024 coefficients
        cf_cnum_nxt = $unsigned(2*2*1*ISIZE*ISIZE/16);
      end
    {`DINO(conv_mode_1x1),1'b1,1'b0},
    {`NINO(conv_mode_2x1s1),1'b1,1'b0},
    {`NINO(conv_mode_2x1s2),1'b1,1'b0},
    {`NINO(conv_mode_2x1s1dl2),1'b1,1'b0}:
      begin
        // normal convolution 16*8 using 1*1*ISIZE*ISIZE=256 coefficients
        cf_cnum_nxt = $unsigned(1*1*ISIZE*ISIZE/16);
      end
    {`NINO(conv_mode_3x3dws1),1'b?,1'b1},
    {`NINO(conv_mode_2x3dws2),1'b?,1'b1},
    {`NINO(conv_mode_3x3dws1dl2),1'b?,1'b1},
    {`NINO(conv_mode_8x1dws1),1'b?,1'b1}:
      begin
        // depthwise 8*16 or 16*16, 2*(8+spare)*ISIZE=256+spare*2 coefficients
        cf_cnum_nxt = $unsigned(2*8*ISIZE/16);
      end
    {`VIVO(conv_mode_3x3dws1),1'b?,1'b0},
    {`NINO(conv_mode_3x3dws1),1'b?,1'b0},
    {`NINO(conv_mode_2x3dws2),1'b?,1'b0},
    {`NINO(conv_mode_3x3dws1dl2),1'b?,1'b0},
    {`NINO(conv_mode_8x1dws1),1'b?,1'b0}:
      begin
        // depthwise 16*8, 8*8 a block per filter channel (8+spare)*ISIZE=128+spare coefficients
        cf_cnum_nxt = (hlapi_i.cf_cfg==cf_cfg_bf16_e || hlapi_i.cf_cfg==cf_cfg_fp16_e) ? $unsigned(2*8*ISIZE/16) : $unsigned(8*ISIZE/16);
      end
    {`NINO(conv_mode_2x1g2s2),1'b1,1'b?},
    {`NINO(conv_mode_1x1),1'b1,1'b?},
    {`FC(conv_mode_fc),1'b1,1'b0}:
      begin
        // 1x1i16o16, 16b*8 or 16*16 ISIZE*ISIZE/2=128 coefficients
        cf_cnum_nxt = $unsigned(ISIZE*ISIZE/2/16);
      end
    {`FC(conv_mode_fc),1'b0,1'b1}:
      begin
        // 1x1i16o16, 16b*8 or 16*16 ISIZE*ISIZE/2=128 coefficients
        cf_cnum_nxt = $unsigned(ISIZE*ISIZE*2/16);
      end
    default: // `NINO(conv_mode_2x1g2s2),` FC(conv_mode_fc), `NINO(conv_mode_1x1), 8*8
      begin
        // 1x1i16o16, 8*8 ISIZE*ISIZE=256 coefficients
        cf_cnum_nxt = $unsigned(ISIZE*ISIZE/16);
      end
    endcase // casez ({hlapi_i.conv_mode,fm_dbl,cf_dbl})
// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :No overflow and ignore
    if (hlapi_i.iter[6][1] || hlapi_i.iter[7][1])
    begin
      // double the coefficient atom count, inn|onn = 2
      cf_cnum_nxt = {cf_cnum_nxt,1'b0};
    end
// spyglass enable_block W164a
    // number of inner iterations
    if (is_conv_mode_fc)
    begin
      cf_limit = (VSIZE == 8) ? 'd8 : 'd2;
    end
    else
    begin
      cf_limit = 'd1;
    end
    // determine number of zero-points to load
    if ((hlapi_i.cf_mode == coef_mode_sparse))
    begin
      if (is_conv_mode_fc)
      begin
        // fully-connected mode and sparsity
        cf_zp_num_nxt = zp256_e;
      end
      else
      begin
        // convolution mode and sparsity
        cf_zp_num_nxt = zp32_e;
      end
    end
    else
    begin
      if (is_conv_mode_fc)
      begin
        // fully-connected mode and no sparsity
        cf_zp_num_nxt = zp128_e;
      end
      else if (hlapi_i.iter[7][1])
      begin
        // convolution mode and ONN==2
        cf_zp_num_nxt = zp32_e;
      end
      else
      begin
        // convolution mode and ONN==1
        cf_zp_num_nxt = zp16_e;
      end
    end
    // Compute max number of elements to pop from queues
    casez ({hlapi_i.cf_mode,cf_dw3_nxt,cf_4b})
    {coef_mode_sparse      ,1'b?,1'b0}: cf_bsmax_nxt = 5'd20;
    {coef_mode_sparse      ,1'b?,1'b1}: cf_bsmax_nxt = 5'd12; 
    {coef_mode_compressed  ,1'b0,1'b?}: cf_bsmax_nxt = 5'd18;
    {coef_mode_compressed  ,1'b1,1'b?}: cf_bsmax_nxt = 5'd20;
    {coef_mode_uncompressed,1'b1,1'b1}: cf_bsmax_nxt = 5'd9;
    {coef_mode_uncompressed,1'b0,1'b1}: cf_bsmax_nxt = 5'd8;
    {coef_mode_uncompressed,1'b1,1'b0}: cf_bsmax_nxt = 5'd18;
    default:                            cf_bsmax_nxt = 5'd16;
    endcase // casez ({cf_mode,cf_dw3,cf_4b})
  end : cnum_PROC
  

  // attributes registers
  // outputs: cf_dw3_r, cf_mode_r, cf_4b_r, cf_zp_r, cf_zp_num_r, cf_cnum_r, cf_padlim_r, cf_bsmax_r
  always_ff @(posedge clk or posedge rst_a)
  begin : attr_reg_PROC
    if (rst_a == 1'b1)
    begin
      // reset values
      cf_dw3_r    <= 1'b0;
      cf_mode_r   <= coef_mode_uncompressed;
      cf_4b_r     <= 1'b0;
      cf_zp_r     <= 1'b0;
      cf_zp_nomerge_r <= '0;
      cf_zp_num_r <= zp16_e;
      cf_cnum_r   <= '1;
      cf_padlim_r <= '0;
      cf_bsmax_r  <= '1;
    end
    else if (attr_en)
    begin
      cf_dw3_r    <= cf_dw3_nxt;
      cf_mode_r   <= hlapi_i.cf_mode;
      cf_4b_r     <= cf_4b;
      cf_zp_r     <= cf_zp;
      cf_zp_nomerge_r <= {N{cf_zp}};
      cf_zp_num_r <= cf_zp_num_nxt;
      cf_cnum_r   <= cf_cnum_nxt;
      cf_padlim_r <= hlapi_i.fm_padlim[1];
      cf_bsmax_r  <= cf_bsmax_nxt;
    end
  end : attr_reg_PROC
  

  //
  // Replicate handshakes
  //
  assign in_valid     = hlapi_valid & (in_accept == '1) & (~soft_rst_r) & (lvl_r == '0) ? '1 : '0;
  assign hlapi_accept = (in_accept == '1) & (~soft_rst_r) & (lvl_r == '0);


  //
  // Independent coefficient decoder pipelines
  //
  for (genvar gp = 0; gp < N; gp++)
  begin : pipe_GEN
    // create pipe dependent pointer stride
    vm_addr_t ptr;
    assign ptr = hlapi_i.cf_ptr + $unsigned(gp)*((hlapi_i.cf_mode == coef_mode_fm ? (hlapi_i.cf_offset[3]>>NL2) : 16'd1));

    npu_conv_coef_pipe
      #(
         .IDX ( gp  )
         )
    u_pipe_inst
      (
       .clk         ( clk            ),
       .rst_a       ( rst_a          ),
       .soft_rst    ( soft_rst_r     ),
       .in_valid    ( in_valid[gp]   ),
       .in_accept   ( in_accept[gp]  ),
       .hlapi_i     ( hlapi_i        ),
       .in_ptr      ( ptr            ),
       .cf_dw3      ( cf_dw3_r       ),
       .cf_4b       ( cf_4b_r        ),
       .cf_bsmax    ( cf_bsmax_r     ),
       .cf_mode     ( cf_mode_r      ),
       .cf_padlim   ( cf_padlim_r    ),
       `VMRINST_S(1,vm_rd_,vm_rd_,gp),
       .coef_valid  ( dec_valid[gp]  ),
       .coef_accept ( dec_accept[gp] ),
       .coef_padlast( pad_last       ),
       .coef_zp     ( zp_ld_nomerge[gp] ),
       .coef_data   ( dec_atom[gp]   )
       );
  end : pipe_GEN


  //
  // Rotate pipeline outputs to bring oldest to front
  //
// spyglass disable_block W164a
// spyglass disable_block W486
//SMD:Width mismatch
//SJ :intentionally drop msbs for '>>', and '<<' is intentional as well
  assign rot_valid   = {2{dec_valid}}  >> pcnt_r; // intentionally drop msbs
  assign dec_acceptd = {2{rot_accept}} << pcnt_r;
  assign dec_accept  = dec_acceptd[1] | dec_acceptd[0];
  // outputs: rot_atom
  always_comb
  begin : rot_PROC
    coef_atom_t [1:0][N-1:0] atom;
    // replicate input
    atom   = {2{dec_atom}};
    // shift
    for (int b = NL2-1; b >= 0; b--)
    begin
      if (pcnt_r[b])
      begin
        // shift by 1<<b 'atom'positions
        atom = atom >> ($bits(coef_atom_t)<<b);
      end
    end
    // take output slice
    rot_atom   = atom[0];
  end : rot_PROC
// spyglass enable_block W164a
// spyglass enable_block W486
  
  //
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected
  // Padding increment iterator
  //
  assign pad_valid  = in_valid[0] && in_accept[0] && (hlapi_i.cf_mode == coef_mode_fm);
  assign pad_accept = dec_valid[0] && dec_accept[0] && (cf_mode_r == coef_mode_fm);
  npu_iterator
    #(
      .N ( 4 ) // number of nested loops
      )
  u_piter_inst
    (
     .clk      ( clk                ),
     .rst_a    ( rst_a              ),
     .soft_rst ( 1'b0               ),
     .in_req   ( pad_valid          ),
     .in_ack   (                    ), // intentionally left unconnected
     .in_shp   ( hlapi_i.cf_iter    ), 
     .it_req   (                    ), // intentionally left unconnected
     .it_ack   ( pad_accept         ),
     .it_first (                    ), // intentionally left unconnected
     .it_last  ( pad_last           ),
     .it_vald  (                    )  // intentionally left unconnected
     );
  
  //
  // Zero-point iterator
  // Load zero-points at start of NO loop i.e. when first[3:2] == 3
  // Load coefficients after zero-points
  //
  assign ziter[3:0] = hlapi_i.iter[3:0];
  assign ziter[4]   = cf_limit;
  npu_iterator
  #(
    .N ( 5 ) // number of nested loops
  )
  u_iter_inst
  (
   .clk      ( clk                ),
   .rst_a    ( rst_a              ),
   .soft_rst ( 1'b0               ),
   .in_req   ( in_valid[N]        ),
   .in_ack   ( in_accept[N]       ),
   .in_shp   ( ziter              ), // [grp][no][ni][qd][fc]
   .it_req   ( zit_req            ),
   .it_ack   ( zit_ack            ),
   .it_first (                    ), // intentionally left open
   .it_last  ( zit_last           ),
   .it_vald  (                    )  // intentionally left open
   );
// spyglass enable_block W287b

`ifdef DUMP_COEF_ROT
  initial
  begin
    forever
    begin
      @(posedge clk);
      for (int i = 0; i < 8; i++)
        if (rot_valid[i] & rot_accept[i])
        begin
          $display("ROT %x", rot_atom[i].coef);
        end
    end
  end
`endif
  

  //
  // zero-point loading next state
  // outputs: zit_ack, zp_state_en, zp_state_nxt, zp_ld, coef_ld, soft_rst_nxt
  //
  always_comb
  begin : zp_nxt_PROC
    // default outputs
    zit_ack      = 1'b0;
    zp_state_en  = 1'b0;
    zp_state_nxt = zp_state_idle_e;
    zp_ld        = 1'b0;
    zp_ld_nomerge = '0;
    coef_ld      = 1'b0;
    soft_rst_nxt = 1'b0;
    // zero-point enabled

    for (int n=0;n<N;n++) begin
      zp_ld_nomerge[n] = zp_state_nomerge_r[n]==zp_state_first_e ||
               zp_state_nomerge_r[n]==zp_state_second_e ||
               (zp_state_nomerge_r[n]==zp_state_idle_e && cf_zp_nomerge_r[n]);
    end

    case (zp_state_r)
    zp_state_first_e:
      begin
        // first cycle of zero-point load
        zp_ld = 1'b1;
        if (zit_req & ziti_ack)
        begin
          zp_state_en  = 1'b1;
          zp_state_nxt = cf_zp_num_r == zp256_e ? zp_state_second_e : zp_state_coef_e;
        end
      end
    zp_state_second_e:
      begin
        // second cycle of zero-point load
        zp_ld = 1'b1;
        zp_state_nxt = zp_state_coef_e;
        if (zit_req & ziti_ack)
        begin
          // start coefficient block
          zp_state_en  = 1'b1;
        end
      end
    zp_state_coef_e:
      begin
        // decode block of coefficients
        coef_ld = 1'b1;
        zit_ack = ziti_ack;
        if (zit_req & ziti_ack)
        begin
          // done loading coefficients
          zp_state_en = 1'b1;
          if (zit_last == 5'b11111)
          begin
            // done, return to idle and soft reset
            zp_state_nxt = zp_state_idle_e;
            soft_rst_nxt = 1'b1;
          end
          else if (cf_zp_r && (&zit_last[4:2]))
          begin
            // load next set of zero-points
            zp_state_nxt = zp_state_first_e;
          end
          else
          begin
            // keep decoding coefficients
            zp_state_nxt = zp_state_coef_e;
          end
        end
      end
    default: // zp_state_idle_e
      begin
        if (cf_zp_r)
        begin
          // first decode of zero-points
          zp_ld = 1'b1;
          if (zit_req & ziti_ack)
          begin
            zp_state_en  = 1'b1;
            zp_state_nxt = cf_zp_num_r == zp256_e ? zp_state_second_e : zp_state_coef_e;
          end
        end
        else
        begin
          // decode coefficients
          coef_ld = 1'b1;
          zit_ack = ziti_ack;
          if (zit_req & ziti_ack && (zit_last == 5'b11111))
          begin
            soft_rst_nxt = 1'b1;
          end
        end
      end
    endcase // case (zp_state_r)
  end : zp_nxt_PROC
  

  //
  // append new elements to buffer and decode zero-points
  //
  // outputs: zp_val, zp_nxt, pcnt_nxt, buf_en_tmp, buf_nxt
  always_comb
  begin : append_PROC
    logic       [BL2-1:0] lvli;
    // default outputs
    zp_val       = 1'b0;
    zp_nxt       = '0;
    pcnt_nxt     = pcnt_r;
    // add coefficients to buffer, reset when accepted
    lvli         = coef_valid ? '0 : lvl_r;
    lvli[2:0]    = '0; // always read groups of 8*16 coefficients
    // shift new input by level
    buf_en_tmp   = {{(B-8){1'b0}}, 8'hff} << lvli;
    buf_nxt      = '0;
    buf_nxt[7:0] = rot_atom;
    for (int b = BL2-1; b >= 0; b--)
    begin
      if (lvli[b])
      begin
        // shift by 1<<b group positions
        buf_nxt = buf_nxt << ($bits(coef_atom_t)<<b);
      end
    end
    // increment level
    lvl_tmp = lvl_r + 'd8;
    // restart buffer after coefficient is accepted
    if (coef_valid)
    begin
      // reset buffer
      lvl_tmp       = (zp_ld | (~zit_req)) ? 'd0 : ((&dec_valid) ? 'd8 : 'd0);
      buf_en_tmp   |= {{(B-8){1'b0}}, 8'hff};
      buf_nxt[7:0] |= rot_atom;
    end
    // extract coefficients or zero-points
    case (cf_zp_num_r)
    zp256_e:
      begin       
        if (zp_state_r == zp_state_second_e)
        begin
          // second set of 128
          zp_nxt = zp_r;
          zp_nxt[0][79:64]  = rot_atom[0].coef;
          zp_nxt[1][79:64]  = rot_atom[1].coef;
          zp_nxt[0][95:80]  = rot_atom[2].coef;
          zp_nxt[1][95:80]  = rot_atom[3].coef;
          zp_nxt[0][111:96] = rot_atom[4].coef;
          zp_nxt[1][111:96] = rot_atom[5].coef;
          zp_nxt[0][127:112]= rot_atom[6].coef;
          zp_nxt[1][127:112]= rot_atom[7].coef;
        end
        else
        begin
          // first set of 128
          zp_nxt[0][15:0]   = rot_atom[0].coef;
          zp_nxt[1][15:0]   = rot_atom[1].coef;
          zp_nxt[0][31:16]  = rot_atom[2].coef;
          zp_nxt[1][31:16]  = rot_atom[3].coef;
          zp_nxt[0][47:32]  = rot_atom[4].coef;
          zp_nxt[1][47:32]  = rot_atom[5].coef;
          zp_nxt[0][63:48]  = rot_atom[6].coef;
          zp_nxt[1][63:48]  = rot_atom[7].coef;
        end
      end
    zp128_e:
      begin
        zp_nxt[0][15:0]   = rot_atom[0].coef;
        zp_nxt[0][31:16]  = rot_atom[1].coef;
        zp_nxt[0][47:32]  = rot_atom[2].coef;
        zp_nxt[0][63:48]  = rot_atom[3].coef;
        zp_nxt[0][79:64]  = rot_atom[4].coef;
        zp_nxt[0][95:80]  = rot_atom[5].coef;
        zp_nxt[0][111:96] = rot_atom[6].coef;
        zp_nxt[0][127:112]= rot_atom[7].coef;
        zp_nxt[1][15:0]   = rot_atom[0].coef;
        zp_nxt[1][31:16]  = rot_atom[1].coef;
        zp_nxt[1][47:32]  = rot_atom[2].coef;
        zp_nxt[1][63:48]  = rot_atom[3].coef;
        zp_nxt[1][79:64]  = rot_atom[4].coef;
        zp_nxt[1][95:80]  = rot_atom[5].coef;
        zp_nxt[1][111:96] = rot_atom[6].coef;
        zp_nxt[1][127:112]= rot_atom[7].coef;
      end
    zp32_e:
      begin
        zp_nxt[0][15:0]   = rot_atom[0].coef;
        zp_nxt[1][15:0]   = rot_atom[1].coef;
      end
    default: // zp16_e
      begin
        zp_nxt[0][15:0]   = rot_atom[0].coef;
        zp_nxt[1][15:0]   = rot_atom[0].coef;
      end
    endcase // case (cf_zp_num_r)
    if (zp_ld)
    begin
      case (cf_zp_num_r)
      zp256_e:
        begin
          zp_val = &dec_valid;
        end
      zp128_e:
        begin
          zp_val = &dec_valid;
        end
      zp32_e:
        begin
          zp_val = &rot_valid[1:0];
          pcnt_nxt = pcnt_r + 'd2;
        end
      default:
        begin
          zp_val   = rot_valid[0];
          pcnt_nxt = pcnt_r + 'd1;
        end
      endcase // case (cf_zp_num_r)
    end
    else
    begin
      // rotate zero-points in FC mode by 16 elements
      zp_nxt[0] = {zp_r[0][15:0], zp_r[0][127:16]};
      zp_nxt[1] = {zp_r[1][15:0], zp_r[1][127:16]};
    end
    pcnt_nxt = soft_rst_r ? '0 : pcnt_nxt;
    zp_nxt   = attr_en    ? '0 : zp_nxt;
  end : append_PROC


  //  
  // output flow control
  // outputs: ziti_ack, pcnt_en, lvl_en, buf_en, zp_en, rot_accept, lvl_nxt
  //
  always_comb
  begin : upd_PROC
    // default outputs
    zp_en      = coef_valid & coef_accept & ((cf_zp_num_r == zp256_e) | (cf_zp_num_r == zp128_e)); // rotate zero-points
    ziti_ack   = 1'b0;
    pcnt_en    = 1'b0;
    lvl_en     = 1'b0;
    buf_en     = '0;
    lvl_nxt    = '0;
    rot_accept = '0;
    if (zit_req && (coef_accept || !coef_valid))
    begin
      // valid iterator and no stall
      if (zp_ld & zp_val)
      begin
        // update zero-point
        case (cf_zp_num_r)
        zp256_e,
        zp128_e: rot_accept = 8'b11111111;
        zp32_e:  rot_accept = 8'b00000011;
        default: rot_accept = 8'b00000001;
        endcase
        ziti_ack = 1'b1;
        zp_en    = 1'b1;
        pcnt_en  = 1'b1;
        lvl_en   = 1'b1;
      end
      else if (coef_ld)
      begin
        lvl_en    = (coef_valid & coef_accept);
        if (&dec_valid)
        begin
          ziti_ack   = lvl_tmp[BL2-1:3] == cf_cnum_r[BL2-1:3];
          rot_accept = 8'b11111111;
          buf_en     = buf_en_tmp;
          lvl_en     = 1'b1;
        end
        lvl_nxt  |= lvl_tmp;
      end
      else if (coef_valid)
      begin
        // accepted so reset level
        lvl_en   = 1'b1;
      end
    end
    else if (coef_valid & coef_accept)
    begin
      // reset level
      lvl_en     = 1'b1;
    end
    pcnt_en |= soft_rst_r;
    zp_en   |= attr_en;
  end : upd_PROC

  
  //
  // state and output registers
  //
  // outputs: zp_state_r, lvl_r, pcnt_r, zp_r, buf_r, soft_rst_r
  always_ff @(posedge clk or posedge rst_a)
  begin : out_reg_PROC
    if (rst_a == 1'b1)
    begin
      zp_state_r <= zp_state_idle_e;
      zp_state_nomerge_r <= {N{zp_state_idle_e}};
      lvl_r      <= '0;
      pcnt_r     <= '0;
      zp_r       <= '0;
      buf_r      <= '0;
      soft_rst_r <= 1'b0;
    end
    else
    begin
      soft_rst_r <= soft_rst_nxt;
      if (zp_state_en)
      begin
        zp_state_r <= zp_state_nxt;
        zp_state_nomerge_r <= {N{zp_state_nxt}};
      end
      if (lvl_en)
      begin
        lvl_r <= lvl_nxt;
      end
      if (pcnt_en)
      begin
        pcnt_r <= pcnt_nxt;
      end
      if (zp_en)
      begin
        zp_r <= zp_nxt;
      end
      for (int b = 0; b < B; b++)
      begin
        if (buf_en[b])
        begin
          buf_r[b] <= buf_nxt[b];
        end
      end
    end
  end : out_reg_PROC


  //
  // assign outputs
  //
  assign coef_valid   = lvl_r == cf_cnum_r;
  assign coef_data.c  = buf_r;
  assign coef_data.zp = {zp_r[1][15:0], zp_r[0][15:0]};

  
`ifdef DUMP_COEF_ROT
  initial
  begin
    forever
    begin
      @(posedge clk);
      if (coef_valid & coef_accept)
        for (int i = 0; i < cf_cnum_r; i++)
          $display("ROT %x", coef_data.c[i].coef);
    end
  end
`endif

endmodule : npu_conv_coef
