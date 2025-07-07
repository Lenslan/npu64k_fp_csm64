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
// Top-level file for the convolution accelerator
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_clkgate.sv ../../shared/RTL/npu_2cyc_checker.sv ../../shared/RTL/npu_cdc_sync.sv ../../shared/RTL/npu_slice_int.sv ../../shared/RTL/npu_l1_clk_ctrl.sv ../../shared/RTL/npu_reset_ctrl.sv ../../shared/RTL/npu_fifo.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_vm_read.sv ../../shared/RTL/npu_am_agu.sv ../../shared/RTL/npu_am_read.sv ../../shared/RTL/npu_am_write.sv ../../shared/RTL/npu_shared_hl_ctrl_dma_mmio.sv ../../shared/RTL/npu_shared_hl_ctrl_dma_res.sv ../../shared/RTL/npu_shared_hl_ctrl_dma_mst.sv ../../shared/RTL/npu_shared_hl_ctrl_dma.sv ../../shared/RTL/npu_hs_broadcast.sv npu_conv_types.sv npu_conv_stash_quad_load.sv  npu_conv_stash_scalar.sv npu_conv_stash_vector.sv npu_conv_stash_pad_load.sv npu_conv_stash_pad_data.sv npu_conv_stash.sv npu_conv_coef_pipe.sv npu_conv_coef.sv npu_conv_mpy_fm.sv npu_conv_mpy_cf.sv npu_conv_mpy_ctrl.sv npu_conv_mpy_mul.sv npu_conv_mpy_prim.sv npu_conv_mpy.sv npu_conv_mpy_sum.sv npu_conv_mpy_acc.sv npu_conv_mpy_lane.sv npu_conv_top.sv
//
 
//`include "const.def"
`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"
`include "npu_vm_macros.svh"
`include "npu_am_macros.svh"



module npu_conv_top
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter int AXI_SLV_IDW=1,
    parameter logic NPU_HAS_FLOAT=1)       // Parameterizable ID width on AXI MMIO slave interface
  (
   //
   // Clock and reset
   //
   input logic      clk,                               // clock, all logic clocked at posedge
   input logic      rst_a,                             // asynchronous reset, active high
   input logic      test_mode,                         // disable datapath reset during scan test
   //
   // Interrupt and event
   //
   output logic     err_irq,                           // level error interrupt to processor
   output logic     irq,                               // level interrupt to processor
   output logic     ievt,                              // issue event pulse to processor
   output logic     devt,                              // done event pulse to processor
   //
   // interfaces
   //
   `AXISLV(AXI_SLV_IDW,64,1,1,1,1,1,mmio_axi_),        // AXI MMIO interface
   `AXIMST(1,64,1,1,1,1,1,descr_axi_),                 // AXI descriptor read/write
   `VMRMST(NUM_COEF_QUEUE+NUM_FM_QUEUE+CONV_PAD_LD_LANES,vm_rd_), // 3*VSIZE+1=25 bank VM feature-map read for stash, coefficients and padding
   `AMRMST(am_rd_,1),                                  // AM read
   `AMWMST(am_wr_,1),                                  // AM write
   // Accumulator stream for fused convolution and activation
   `STRMST(acc_,vyixacc_t),
   // Feature-map stream for FReLU
//   `STRMST(pix_,vyixpix_t),
   `TRCMST(trace_,1)
   );
  // local parameters
  localparam int HS_FMAP_STASH=1; localparam int HS_COEF_DEC=0; localparam int HS_MPY=2;
  localparam int HS_AM_RD=3;      localparam int HS_AM_WR=4;
  localparam int HSNUM=5;                     // number of handshake signals
  // local wires
  logic                      clk_en;          // clock enable for the accelerator compute core
  logic                      clk_or_en;       // clock enable for the accelerator compute core or AM write
  logic                      clk_gated;       // gated clock
  logic                      rst;             // synchronized reset, asyn assertion, sync deassertion
  logic                      rst_dp;          // reset compute datapath
  logic                      hlapi_i_valid;   // new HLAPI issue descriptor valid
  logic                      hlapi_i_accept;  // new HLAPI issue descriptor accept
  conv_hlapi_i_t             hlapi_i;         // HLAPI input descriptor
  conv_hlapi_i_t             hlapi_i_mc2;     // HLAPI input descriptor, multi-cycle path
  logic          [HSNUM-1:0] hlapi_v_valid;   // new HLAPI issue descriptor valid
  logic          [HSNUM-1:0] hlapi_v_accept;  // new HLAPI issue descriptor accept
  logic                      hlapi_o_valid;   // new HLAPI output descriptor valid
  logic                      hlapi_o_accept;  // new HLAPI output descriptor accept
  logic          [31:0]      hlapi_res;       // result from datapath to HLAPI
  logic          [31:0]      hlapi_stat;      // status from datapath to HLAPI
  logic                      stash_valid;     // stash output is valid
  logic                      stash_accept;    // stash output is accept
  stash_data_t               stash_data;      // data from stash to muliplier array
  logic                      coef_valid;      // coefficient output is valid
  logic                      coef_accept;     // coefficient output is accept
  coef_data_t                coef_data;       // data from coefficient decoder to muliplier array
  logic                      coef_mode_fm;    // Matrix*Matrix indication
  logic                      a_spat_one;      // Skip inner acc load/store
  am_agu_t                   a_pars;          // accumulator read AGU parameters
  logic                      ar_valid;        // accumulator read valid
  logic                      ar_accept;       // accumulator read accept
  vyixacc_t                  ar_data;         // accumulator read data
  logic                      aw_valid;        // accumulator write valid
  logic                      aw_accept;       // accumulator write accept
  vyixacc_t                  aw_data;         // accumulator write data
  logic          [1:0]       has_aw;          // indicate a new aw
  logic                      aw_keep;         // accumulator Keep


  //
  // Reset synchronizer
  //
  npu_reset_ctrl
  u_reset_ctrl_inst
    (
    .clk        ( clk       ),
    .rst_a      ( rst_a     ),
    .test_mode  ( test_mode ),
    .rst        ( rst       )
    );


  //
  // Clock gate control
  //
  assign clk_or_en = clk_en | ~hlapi_v_accept[HS_AM_WR];
  npu_l1_clk_ctrl
  u_l1_clkctrl_inst
    (
    .clk_in       ( clk       ),
    .clock_enable ( clk_or_en ),
    .clk_out      ( clk_gated )
    );


  //
  // MMIO&DMA control
  //
  localparam CONV_ID = (NPU_HAS_FLOAT==1) ? CONV_ID_FLT : CONV_ID_INT;
  assign hlapi_res  = '0;
  assign hlapi_stat = '0;
  npu_shared_hl_ctrl_dma
    #(
      .ID       ( CONV_ID        ),
      .MAJ      ( CONV_MAJ       ),
      .MIN      ( CONV_MIN       ),
      .SAXIIDW  ( AXI_SLV_IDW    ),
      // rest left to 1 for future bus ECC support
      .SAXIAWUW ( 1              ),
      .SAXIWUW  ( 1              ),
      .SAXIBUW  ( 1              ),
      .SAXIARUW ( 1              ),
      .SAXIRUW  ( 1              ),
      .MAXIAWUW ( 1              ),
      .MAXIWUW  ( 1              ),
      .MAXIBUW  ( 1              ),
      .MAXIARUW ( 1              ),
      .MAXIRUW  ( 1              ),
      // HLAPI data type
      .T        ( conv_hlapi_i_t )
      )
  u_ctrl_inst
    (
     // System interface
     .clk            ( clk            ),
     .rst_a          ( rst            ),
     .test_mode      ( test_mode      ),
     .clk_en         ( clk_en         ),
     .rst_dp         ( rst_dp         ),
     .err_irq        ( err_irq        ),
     .irq            ( irq            ),
     .ievent         ( ievt           ),
     .devent         ( devt           ),
     // AXI MMIO interface 64b wide data
     `AXIINST(mmio_axi_,mmio_axi_),
     // AXI DMA master interface for reading/writing descriptors 64b wide data
     `AXIINST(mst_axi_,descr_axi_),
     // Signals to accelerator datapath, controlled by valid/accept handshake
     .hlapi_i_valid  ( hlapi_i_valid  ),
     .hlapi_i_accept ( hlapi_i_accept ),
     .hlapi_i        ( hlapi_i        ),
     .hlapi_o_valid  ( hlapi_o_valid  ),
     .hlapi_o_accept ( hlapi_o_accept ),
     .hlapi_o_res    ( hlapi_res      ),
     .hlapi_o_stat   ( hlapi_stat     ),
     // trace interface
     `TRCINST_S(trace_,trace_,0)
     );


  //
  // Multi-cycle path on HLAPI input
  //
  npu_2cyc_checker 
    #(
      .WIDTH ( $bits(conv_hlapi_i_t) )
      )
  u_hl_mc2_inst
    (
     .clk      ( clk           ),
     .rst_a    ( rst_a         ),
     .valid    ( hlapi_i_valid ),
     .data_in  ( hlapi_i       ),
     .data_out ( hlapi_i_mc2   )
     );
  
  
  //
  // Broadcast HLAPI handshake signals
  //
  npu_hs_broadcast
    #(.NUM ( HSNUM ))
  u_hs_inst
  (
   .clk        ( clk_gated      ),
   .rst_a      ( rst_dp         ), 
   .hsi_valid  ( hlapi_i_valid  ),
   .hsi_accept ( hlapi_i_accept ),
   .hso_valid  ( hlapi_v_valid  ),
   .hso_accept ( hlapi_v_accept )
  );


  //
  // Stash
  //
  npu_conv_stash
  u_stash_inst
    (
    // clock and reset
    .clk          ( clk_gated         ),
    .rst_a        ( rst_dp            ),
    // HLAPI interface
    .hlapi_valid  ( hlapi_v_valid[HS_FMAP_STASH]  ),
    .hlapi_accept ( hlapi_v_accept[HS_FMAP_STASH] ),
    .hlapi_i      ( hlapi_i_mc2           ),
    // Feature-map VM read interface
   `VMRINST_S(NUM_FM_QUEUE+CONV_PAD_LD_LANES,vm_rd_,vm_rd_,0),
    // Interface to MAC array
    .stash_valid  ( stash_valid       ),
    .stash_accept ( stash_accept      ),
    .stash_data   ( stash_data        )
    );


  //
  // Coefficient decoder
  //
  npu_conv_coef
  u_coef_inst
    (
    // clock and reset
    .clk          ( clk_gated         ),
    .rst_a        ( rst_dp            ),
    // HLAPI interface
    .hlapi_valid  ( hlapi_v_valid[HS_COEF_DEC]  ),
    .hlapi_accept ( hlapi_v_accept[HS_COEF_DEC] ),
    .hlapi_i      ( hlapi_i_mc2       ),
    // Coefficient VM read interface
   `VMRINST_S(NUM_COEF_QUEUE,vm_rd_,vm_rd_,NUM_FM_QUEUE+CONV_PAD_LD_LANES),
    // Interface to MAC array
    .coef_valid   ( coef_valid        ),
    .coef_accept  ( coef_accept       ),
    .coef_mod_fm  ( coef_mode_fm      ),
    .coef_data    ( coef_data         )
    );


  //
  // MAC array
  //
  npu_conv_mpy #(.NPU_HAS_FLOAT(NPU_HAS_FLOAT))
  u_mpy_inst
    (
     // clock and reset
     .clk            ( clk_gated         ),
     .rst_a          ( rst_dp            ),
     // HLAPI interface
     .hlapi_valid    ( hlapi_v_valid[HS_MPY]  ),
     .hlapi_accept   ( hlapi_v_accept[HS_MPY] ),
     .hlapi_i        ( hlapi_i_mc2       ),
     // Interface to stash
     .stash_valid    ( stash_valid       ),
     .stash_accept   ( stash_accept      ),
     .stash_data     ( stash_data        ),
     // Coefficient interface
     .coef_valid     ( coef_valid        ),
     .coef_accept    ( coef_accept       ),
     .coef_data      ( coef_data         ),
     .coef_mode_fm   ( coef_mode_fm      ),
     // Accumulator read interface
     .ar_valid       ( ar_valid          ),
     .ar_accept      ( ar_accept         ),
     .ar_acc         ( ar_data           ),
     // Accumulator write interface
     .aw_valid       ( aw_valid          ),
     .aw_accept      ( aw_accept         ),
     .aw_acc         ( aw_data           ),
     .aw_keep        ( aw_keep           ),
     // Result handshake
     .hlapi_o_valid  ( hlapi_o_valid     ),
     .hlapi_o_accept ( hlapi_o_accept    )
     );


  //
  // Accumulator parameters
  //
  assign a_pars.addr    = hlapi_i_mc2.acc_ptr;
  // iterators [grp*no][ni*qd][col*row*onn]
  assign a_spat_one = hlapi_i_mc2.iter[7] == 'd1 && hlapi_i_mc2.iter[5] == 'd1 && hlapi_i_mc2.iter[4] == 'd1
                      && (~(hlapi_i_mc2.fm_cfg==fm_cfg_bf16_e||hlapi_i_mc2.fm_cfg==fm_cfg_fp16_e));
  assign a_pars.iter[0] = hlapi_i_mc2.iter[0];     // grp
  assign a_pars.iter[1] = hlapi_i_mc2.iter[1];     // no
  assign a_pars.iter[2] = a_spat_one ? 'd1 : hlapi_i_mc2.iter[2];     // ni
  assign a_pars.iter[3] = a_spat_one ? 'd1 : hlapi_i_mc2.iter[3];     // qd
  assign a_pars.iter[4] = hlapi_i_mc2.iter[4];     // col
  assign a_pars.iter[5] = hlapi_i_mc2.iter[5];     // row
                                               // inn not used
  assign a_pars.iter[6] = ((hlapi_i_mc2.fm_cfg==fm_cfg_16b_e && hlapi_i_mc2.cf_cfg==cf_cfg_16b_e) || 
                           (hlapi_i_mc2.cf_mode == coef_mode_sparse)) ? hlapi_i_mc2.iter[7] << 1  // onn
                          : hlapi_i_mc2.iter[7];

  //
  // Accumulator reading
  //
  npu_am_read
   #(
     .DEPTH ( 5 )
    )
  u_am_rd_inst
    (
   .clk        ( clk_gated                ),
   .rst_a      ( rst                      ),
   .in_valid   ( hlapi_v_valid[HS_AM_RD]  ),
   .in_accept  ( hlapi_v_accept[HS_AM_RD] ),
   .in_pars    ( a_pars                   ),
   .in_raw_en  ( ~a_spat_one              ),
   .in_use_acc ( hlapi_i_mc2.use_acc      ),
   .in_keep_acc( hlapi_i_mc2.keep_acc     ),
   .in_has_aw  ( has_aw                   ),
   `AMRINST_S  ( am_rd_,am_rd_,0          ),
   .out_valid  ( ar_valid                 ),
   .out_accept ( ar_accept                ),
   .out_acc    ( ar_data                  )
   );
  //
  // Accumulator writing
  //
  npu_am_write
  u_am_wr_inst
    (
   .clk        ( clk_gated                ),
   .rst_a      ( rst                      ),
   .in_valid   ( hlapi_v_valid[HS_AM_WR]  ),
   .in_accept  ( hlapi_v_accept[HS_AM_WR] ),
   .in_pars    ( a_pars                   ),
   .in_use_acc ( hlapi_i_mc2.use_acc      ),
   .in_keep_acc( hlapi_i_mc2.keep_acc     ),
   .out_valid  ( aw_valid                 ),
   .out_accept ( aw_accept                ),
   .out_acc    ( aw_data                  ),
   `STRINST    ( acc_,acc_),
   `AMWINST_S  ( am_wr_,am_wr_,0          )
   );


  // Decrement hazard counter
  assign has_aw = {am_wr_aw_consumed, acc_str_valid & acc_str_accept};

endmodule : npu_conv_top

