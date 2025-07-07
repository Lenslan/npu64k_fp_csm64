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
// Top-level file for the generic tensor operation accelerator
// vcs -sverilog ../../shared/RTL/npu_types.sv npu_gtoa_types.sv npu_gtoa_top.sv ../../shared/RTL/npu_cdc_sync.sv npu_gtoa_arb.sv npu_gtoa_bpar_rd.sv npu_gtoa_core.sv npu_gtoa_core_wrap.sv npu_gtoa_fu_alu_lut.sv npu_gtoa_fu_alu.sv npu_gtoa_fu_bpar.sv npu_gtoa_fu_in.sv npu_gtoa_fu_mul.sv npu_gtoa_fu_out.sv npu_gtoa_pool.sv npu_gtoa_pcu_issue.sv npu_gtoa_pcu_iter.sv npu_gtoa_pcu.sv npu_gtoa_rf.sv +incdir+../../shared/RTL ../../shared/RTL/npu_shared_hl_ctrl_dma.sv ../../shared/RTL/npu_clkgate.sv ../../shared/RTL/npu_l1_clk_ctrl.sv ../../shared/RTL/npu_vm_read.sv ../../shared/RTL/npu_vm_write.sv ../../shared/RTL/npu_fifo.sv ../../shared/RTL/npu_iterator.sv npu_gtoa_am_read.sv npu_gtoa_am_write.sv ../npu_gtoa_mp_dep_ctrl.sv ../npu_gtoa_mp_vm_lane_read.sv ../npu_gtoa_mp_vm_read.sv ../npu_gtoa_mp_vm_lane_write.sv ../npu_gtoa_mp_vm_write.sv ../../shared/RTL/npu_hs_broadcast.sv ../../shared/RTL/npu_vm_lane_read.sv ../../shared/RTL/npu_vm_lane_write.sv ../../shared/RTL/npu_slice_int.sv npu_gtoa_am_agu.sv ../../shared/RTL/npu_shared_hl_ctrl_dma_mmio.sv  ../../shared/RTL/npu_shared_hl_ctrl_dma_mst.sv  ../../shared/RTL/npu_shared_hl_ctrl_dma_res.sv ../../shared/RTL/npu_reset_ctrl.sv npu_gtoa_lane.sv -y $SYNOPSYS/dw/sim_ver +libext+.v
// analyze -format sverilog -vcs "../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_2cyc_checker.sv ../npu_gtoa_types.sv ../npu_gtoa_top.sv ../npu_gtoa_arb.sv ../npu_gtoa_bpar_rd.sv ../npu_gtoa_core.sv ../npu_gtoa_fu_alu_multi4.sv ../npu_gtoa_fu_alu.sv ../npu_gtoa_fu_bpar.sv ../npu_gtoa_fu_in.sv ../npu_gtoa_fu_mul.sv ../npu_gtoa_fu_out.sv ../npu_gtoa_pool.sv ../npu_gtoa_pcu_issue.sv ../npu_gtoa_pcu_iter.sv ../npu_gtoa_pcu.sv ../npu_gtoa_rf.sv +incdir+../../../shared/RTL ../../../shared/RTL/npu_shared_hl_ctrl_dma.sv ../../../shared/RTL/npu_clkgate.sv ../../../shared/RTL/npu_l1_clk_ctrl.sv ../../../shared/RTL/npu_vm_read.sv ../../../shared/RTL/npu_vm_write.sv ../../../shared/RTL/npu_fifo.sv ../../../shared/RTL/npu_iterator.sv ../npu_gtoa_am_read.sv ../npu_gtoa_am_write.sv ../npu_gtoa_mp_dep_ctrl.sv ../npu_gtoa_mp_vm_lane_read.sv ../npu_gtoa_mp_vm_read.sv ../npu_gtoa_mp_vm_lane_write.sv ../npu_gtoa_mp_vm_write.sv ../../../shared/RTL/npu_hs_broadcast.sv ../../../shared/RTL/npu_vm_lane_read.sv ../../../shared/RTL/npu_vm_lane_write.sv ../../../shared/RTL/npu_slice_int.sv ../npu_gtoa_am_agu.sv ../../../shared/RTL/npu_shared_hl_ctrl_dma_mmio.sv  ../../../shared/RTL/npu_shared_hl_ctrl_dma_mst.sv ../../../shared/RTL/npu_shared_hl_ctrl_dma_res.sv ../../../shared/RTL/npu_reset_ctrl.sv ../npu_gtoa_lane.sv"
// set_app_var link_library "* $target_library dw_foundation.sldb"
//

`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"
`include "npu_vm_macros.svh"
`include "npu_am_macros.svh"



module npu_gtoa_top
  import npu_types::*;
  import npu_gtoa_types::*;
  #(
    parameter int AXI_SLV_IDW=1                   // Parameterizable ID width on AXI MMIO interface
    )
  (
   //
   //
   // clock and reset
   //
   input  logic       clk,                        // clock, all logic clocked at posedge
   input  logic       rst_a,                      // asynchronous reset, active high
   input  logic       test_mode,                  // disable datapath reset during scan test
   input  logic [7:0] slc_id,                     // unique slice ID, static
   //    
   // interrupt and event
   //
   output logic       err_irq,                    // level error interrupt to processor
   output logic       irq,                        // level interrupt to processor
   output logic       ievt,                       // issue event pulse to processor
   output logic       devt,                       // done event pulse to processor
   //
   // interfaces
   //
   `AXISLV(AXI_SLV_IDW,64,1,1,1,1,1,mmio_axi_),   // AXI MMIO interface
   `AXIMST(1,64,1,1,1,1,1,descr_axi_),            // AXI descriptor read/write
   `VMRMST(VSIZE,vm_rd_),                         // Primary&secondary VM read
   `AMRMST(am_rd_,1),                             // Primarysecondary AM read
   `AMWMST(am_wr_,1),                             // Output accumulator store
   `STRSLV(acc_,vyixacc_t),                       // Input stream from conv
   `VMWMST(VSIZE,vm_wr_),                         // Output feature-map store
   `VMRMST(1,bpar_rd_),                           // breg Parameters read VM
   `VMRMST(2,mpst_rd_),                           // Maxpool stash read VM
   `VMWMST(2,mpst_wr_),                           // Maxpool stash write VM
   // Trace
   `TRCMST(trace_,1)
   );
  // local parameters
  localparam int HSNUM = 10;                  // number of handshake signals
  // local wires
  // general
  logic                      clk_en;          // clock enable for the accelerator compute core
  logic                      clk_en_eff;      // clock enable for the accelerator compute core
// spyglass disable_block W401
//SMD:Clock is not an input
//SJ :intentional generate
  logic                      clk_gated;       // gated clock
// spyglass enable_block W401
  logic                      clk_gated_half;  // half frequency gated clock
  logic                      tgl_r;           // half frequency enable toggle
  logic                      clk_half_en;     // half clock enable
  logic          [1:0]       cycle;           // half clock cycle indicator
  logic                      hlapi_i_valid;   // new HLAPI issue descriptor valid
  logic                      hlapi_i_valid_r; // registered valid
  logic                      hlapi_i_accept;  // new HLAPI issue descriptor accept
  act_hlapi_i_t              hlapi_i;         // HLAPI input descriptor
  act_hlapi_i_t              hlapi_i_mc3;     // HLAPI input descriptor, 3 multi-cycle
  logic          [HSNUM-1:0] hlapi_v_valid;   // new HLAPI issue descriptor valid
  logic          [HSNUM-1:0] hlapi_v_accept;  // new HLAPI issue descriptor accept
  logic                      hlapi_o_valid;   // new HLAPI output descriptor valid
  logic                      hlapi_o_accept;  // new HLAPI output descriptor accept
  logic          [31:0]      hlapi_o_res;     // result from datapath to HLAPI
  logic          [31:0]      hlapi_o_stat;    // status from datapath to HLAPI
  // VM&AM  interfaces before muxing
  `VMRWIRES(VSIZE,vm0_rd_);
  `VMRWIRES(VSIZE,vm1_rd_);
  `AMRWIRES(am0_rd_,1);
  `AMRWIRES(am1_rd_,1);
  // AGU HLAPI handshakes
  logic                      accr0_hlapi_valid;
  logic                      accr0_hlapi_accept;
  logic                      fm0_hlapi_valid;
  logic                      fm0_hlapi_accept;
  logic                      accr1_hlapi_valid;
  logic                      accr1_hlapi_accept;
  logic                      fm1_hlapi_valid;
  logic                      fm1_hlapi_accept;
  logic                      accw_hlapi_valid;
  logic                      accw_hlapi_accept;
  logic                      fmw_hlapi_valid;
  logic                      fmw_hlapi_accept;
  logic                      bpar_hlapi_valid;
  logic                      bpar_hlapi_accept;
  // input read and output write
  logic                      accr0_valid;
  logic                      accr0_accept;
  vyixacc_t                  accr0_data;
  logic                      fmr0_valid;
  logic                      fmr0_accept;
  vyixpix_t                  fmr0_data;
  logic                      accr1_valid;
  logic                      accr1_accept;
  vyixacc_t                  accr1_data;
  logic                      fmr1_valid;
  logic                      fmr1_accept;
  vyixpix_t                  fmr1_data;
  logic                      fstr1_valid;
  logic                      fstr1_accept;
  vyixpix_t                  fstr1_data;
  logic                      accw_valid;
  logic                      accw_accept;
  vyixacc_t                  accw_data;
  logic                      fmw_valid;
  logic                      fmw_accept;
  vyixpix_t                  fmw_data;
  // HLAPI fields
  act_hlapi_vm_agu_t         prim_fm;
  act_hlapi_vm_agu_t         secd_fm;
  act_hlapi_vm_agu_t         out_fm;
  act_hlapi_am_agu_t         prim_ac;
  act_hlapi_am_agu_t         secd_ac;
  act_hlapi_am_agu_t         out_ac;
  logic          [ISIZE-1:0] cmask;
  // input/output arbiter
  tmask_t                    ctrl_io_en;
  logic                      arb_rd0_valid;
  logic                      arb_rd1_valid;
  logic                      arb_wr_valid;
  logic                      arb_rd0_accept;
  logic                      arb_rd1_accept;
  logic                      arb_wr_accept;
  vyixacc_t                  arb_rd0_data;
  vyixacc_t                  arb_rd1_data;
  vyixacc_t                  arb_wr_data;
  // bpar loading
  logic                [5:0] core_bpar_q_lvl;
  logic                      core_bpar_pop_q;
  logic                [3:0] core_bpar_pop_q_num;
  ixacc_t [ACT_BREG_NUM-1:0] core_bpar_nxt;
  // gather controls
  logic                      in0_gather;          // gather hlapi
  logic                      gather_valid;        // new gather instruction
  logic                      gather_accept;       // accept gather instruction
  vm_addr_t  [VSIZE-1:0]     gather_vptr;         // gather vector pointer
  // gtoa_core internal signals
  logic                      core_iter_req;
  logic                      core_iter_ack;
  logic                      core_lut_init;
  logic                [1:0] core_in_valid;
  vyixacc_t            [1:0] core_in_data;
  logic                [1:0] core_in_accept;
  logic                      core_out_valid;
  logic                      core_out_accept;
  vyixacc_t                  core_out_data;
  logic                      core_out_dbl;
  logic                      rst;                 // synchronized reset
  logic                      rst_half;            // synchronized reset
  logic                      rst_dp;              // datapath reset
  // maxpooling read/write stash data
  buf_t                      mpbuf;
  act_pool_t                 pool_pars;
  logic                      pool_hlapi_rvalid;
  logic                      pool_hlapi_wvalid;
  logic                      pool_hlapi_raccept;
  logic                      pool_hlapi_waccept;
  offset_t [ACT_POOL_LOOPS-1:0] pool_offsets;
  logic [VSIZE-1:0]          core_pool_wen;
  logic                      mp_rd_valid;
  logic                      mp_rd_accept;
  ixpix_t              [1:0] mp_rd_data;
  logic                      mp_wr_valid;
  logic                      mp_wr_accept;
  ixpix_t              [1:0] mp_wr_data;
  logic                [1:0] mp_rd_hs;
  logic                [1:0] mp_wr_hs;
  logic                [1:0] mp_wr_nopend;
  logic                [1:0] mp_canrd;
  logic                [1:0] mp_canwr;
  logic                      mp_stash2;
  logic                [1:0] mask_i;
  logic                [1:0] mask_o;
  logic                      mp_rd_pars_en;
  logic                      mp_wr_pars_en;
  offset_t [ACT_FM_LOOPS-1:0] paditer;
  logic                      accw_dependency;
  logic                      fmw_dependency;

  

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
  // Reset synchronizer
  //
  npu_reset_ctrl
  u_reset_ctrl_half_inst
    (
    .clk        ( clk_gated_half),
    .rst_a      ( rst_dp    ),
    .test_mode  ( test_mode ),
    .rst        ( rst_half  )
    );
  
  //
  // Clock gate control
  //
  assign clk_en_eff = clk_en | tgl_r;
  npu_l1_clk_ctrl
  u_l1_clkctrl_inst
    (
    .clk_in       ( clk        ),
    .clock_enable ( clk_en_eff ),
    .clk_out      ( clk_gated  )
    );

  
  //
  // Half frequency clock gate
  //
  npu_clkgate
  u_l2_clkgate_half_inst
    (
    .clk_in       ( clk            ),
    .clock_enable ( clk_half_en    ),
    .clk_out      ( clk_gated_half )
    );
  always_ff @(posedge clk_gated or
              posedge rst)
  begin : tgl_reg_PROC
    if (rst == 1'b1)
    begin
      tgl_r <= 1'b0;
    end
    else
    begin
      tgl_r <= ~tgl_r;
    end
  end : tgl_reg_PROC
  assign clk_half_en = clk_en_eff & tgl_r;
  assign cycle       = {clk_half_en, ~clk_half_en};
  
  //
  // MMIO&DMA control
  //
`ifdef ACT_HAS_ALU1
  localparam int GTOA_ID0 = GTOA_ID_ALU2_STR0;
`else
  localparam int GTOA_ID0 = GTOA_ID_STR0;
`endif
  npu_shared_hl_ctrl_dma
    #(
      .ID       ( GTOA_ID0       ),
      .MAJ      ( GTOA_MAJ       ),
      .MIN      ( GTOA_MIN       ),
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
      .T        ( act_hlapi_i_t )
      )
  u_gtoa_ctrl_inst
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
     .hlapi_o_res    ( hlapi_o_res    ),
     .hlapi_o_stat   ( hlapi_o_stat   ),
     // trace interface
     `TRCINST_S(trace_,trace_,0)
     );


  //
  // Broadcast HLAPI handshake signals with conservative handshake
  //
  always_ff @(posedge clk or posedge rst_dp)
  begin : del_valid_reg_PROC
    if (rst_dp == 1'b1)
    begin
      hlapi_i_valid_r <= 1'b0;
    end
    else
    begin
      hlapi_i_valid_r <= hlapi_i_valid & (~hlapi_i_accept);
    end
  end : del_valid_reg_PROC
  npu_hs_broadcast
    #(
      .NUM ( HSNUM ),
      .CNS ( 1'b0  )
      )
  u_gtoa_hs_inst
  (
   .clk        ( clk_gated       ),
   .rst_a      ( rst_dp          ),
   .hsi_valid  ( hlapi_i_valid_r ),
   .hsi_accept ( hlapi_i_accept  ),
   .hso_valid  ( hlapi_v_valid   ),
   .hso_accept ( hlapi_v_accept  )
  );
  // multi-cycle path on HLAPI signals
  npu_3cyc_checker 
    #(
      .WIDTH ( $bits(act_hlapi_i_t) )
      )
  u_hl_mc3f2s_inst
    (
     .clk      ( clk           ),
     .rst_a    ( rst_a         ),
     .valid    ( hlapi_i_valid ),
     .data_in  ( hlapi_i       ),
     .data_out ( hlapi_i_mc3   )
     );
  

  //
  // VM read arbitration
  //
  for (genvar gi = 0; gi < VSIZE; gi = gi + 1)
  begin : vm_rarb_GEN
    logic       vm_cmd_en;
    logic       vm_rd_sel;
    assign vm_rd_cmd_valid[gi]   = vm0_rd_cmd_valid[gi] | vm1_rd_cmd_valid[gi];
    assign vm0_rd_cmd_accept[gi] = vm_rd_cmd_accept[gi] &  vm0_rd_cmd_valid[gi];
    assign vm1_rd_cmd_accept[gi] = vm_rd_cmd_accept[gi] & ~vm0_rd_cmd_valid[gi];
    assign vm_rd_cmd_addr[gi]    = vm0_rd_cmd_valid[gi] ? vm0_rd_cmd_addr[gi] : vm1_rd_cmd_addr[gi];
    assign vm0_rd_rvalid[gi]     = vm_rd_rvalid[gi] & ~vm_rd_sel;
    assign vm1_rd_rvalid[gi]     = vm_rd_rvalid[gi] &  vm_rd_sel;
    assign vm0_rd_rdata[gi]      = vm_rd_rdata[gi];
    assign vm1_rd_rdata[gi]      = vm_rd_rdata[gi];
    assign vm_cmd_en             = vm_rd_cmd_valid[gi] & vm_rd_cmd_accept[gi];
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :intentionally open
    npu_fifo
      #(
        .SIZE   ( 4    ),
        .DWIDTH ( 1    ),
        .FRCVAL ( 1'b1 ),
        .FRCACC ( 1'b1 )
        )
    u_vmq_inst
      (
       .clk          ( clk_gated             ),
       .rst_a        ( rst_dp                ),
       .valid_write  ( vm_cmd_en             ),
       .accept_write (                       ), // intentionally open, forced accept
       .data_write   ( vm1_rd_cmd_accept[gi] ),
       .valid_read   (                       ), // intentionally open, forced valid
       .accept_read  ( vm_rd_rvalid[gi]      ),
       .data_read    ( vm_rd_sel             )
       );
  end : vm_rarb_GEN
// spyglass enable_block W287b

  //
  // AM read arbitration
  //
  logic       am_cmd_en;
  logic       am_rd_sel;
  assign am_rd_cmd_valid   = am0_rd_cmd_valid | am1_rd_cmd_valid;
  assign am0_rd_cmd_accept = am_rd_cmd_accept &  am0_rd_cmd_valid;
  assign am1_rd_cmd_accept = am_rd_cmd_accept & ~am0_rd_cmd_valid;
  assign am_rd_cmd_addr    = am0_rd_cmd_valid ? am0_rd_cmd_addr : am1_rd_cmd_addr;
  assign am0_rd_rvalid     = am_rd_rvalid & ~am_rd_sel;
  assign am1_rd_rvalid     = am_rd_rvalid & am_rd_sel;
  assign am0_rd_rdata      = am_rd_rdata;
  assign am1_rd_rdata      = am_rd_rdata;
  assign am_cmd_en         = am_rd_cmd_valid & am_rd_cmd_accept;
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :intentionally open
  npu_fifo
    #(
      .SIZE   ( 4    ),
      .DWIDTH ( 1    ),
      .FRCVAL ( 1'b1 ),
      .FRCACC ( 1'b1 )
      )
  u_amq_inst
    (
     .clk          ( clk_gated         ),
     .rst_a        ( rst_dp            ),
     .valid_write  ( am_cmd_en         ),
     .accept_write (                   ), // intentionally open, forced accept
     .data_write   ( am1_rd_cmd_accept ),
     .valid_read   (                   ), // intentionally open, forced valid
     .accept_read  ( am_rd_rvalid      ),
     .data_read    ( am_rd_sel         )
     );
// spyglass enable_block W287b  

  //
  // Primary accumulator read
  //
  assign prim_ac           = hlapi_i_mc3.u.fu.primary.a.am_agu;
  assign accr0_hlapi_valid = hlapi_v_valid[0] & (~accw_dependency) & ((hlapi_i_mc3.u.fu.io_en & act_io_en_ac0_e) != '0) & (hlapi_i_mc3.typ == act_typ_fu_e);
  assign hlapi_v_accept[0] = accr0_hlapi_accept & (~accw_dependency);

  npu_gtoa_am_read
  u_gtoa_am0_rd_inst
    (
   .clk        ( clk_gated               ),
   .rst_a      ( rst_dp                  ),
   .in_valid   ( accr0_hlapi_valid       ),
   .in_accept  ( accr0_hlapi_accept      ),
   .in_pars    ( prim_ac                 ),
   `AMRINST_S(am_rd_,am0_rd_,0),
   .out_valid  ( accr0_valid             ),
   .out_accept ( accr0_accept            ),
   .out_acc    ( accr0_data              )
   );


  //
  // Primary feature-map read
  //
  assign fm0_hlapi_valid   = hlapi_v_valid[1] & (~fmw_dependency) & ((hlapi_i_mc3.u.fu.io_en & act_io_en_fm0_e) != '0 || (hlapi_i_mc3.u.fu.io_en & act_io_en_gth_e) != '0) & (hlapi_i_mc3.typ == act_typ_fu_e);
  assign hlapi_v_accept[1] = fm0_hlapi_accept & (~fmw_dependency);
  assign prim_fm           = hlapi_i_mc3.u.fu.primary.fm_agu;
  assign in0_gather        = (hlapi_i_mc3.u.fu.io_en & act_io_en_gth_e) != '0;
  
  npu_gtoa_vm_gather_read
    #(
      .R ( ACT_FM_LOOPS ),
      .G ( VSIZE        )
      )
  u_gtoa_vm0_lane_rd_inst
    (
     .clk            ( clk_gated          ),
     .rst_a          ( rst_dp             ),
     .in_valid       ( fm0_hlapi_valid    ),
     .in_accept      ( fm0_hlapi_accept   ),
     .in_gather      ( in0_gather         ),
     .iter           ( prim_fm.iter       ),
     .offset         ( prim_fm.offsets    ),
     .stride         ( prim_fm.stride     ),
     .ptr            ( prim_fm.ptr        ),
     .bf             ( prim_fm.buffer     ),
     .gather_valid   ( gather_valid       ),
     .gather_accept  ( gather_accept      ),
     .gather_vptr    ( gather_vptr        ),
     `VMRINST_S(VSIZE,vm_rd_,vm0_rd_,0),
     .out_valid      ( fmr0_valid         ),
     .out_accept     ( fmr0_accept        ),
     .out_data       ( fmr0_data          )
   );


  //
  // Secondary accumulator read
  //
  assign secd_ac            = hlapi_i_mc3.u.fu.secondary.a.am_agu;
  assign accr1_hlapi_valid  = hlapi_v_valid[2] & (~accw_dependency) & ((hlapi_i_mc3.u.fu.io_en & act_io_en_ac1_e) != '0) & (hlapi_i_mc3.typ == act_typ_fu_e);
  assign hlapi_v_accept[2]  = accr1_hlapi_accept & (~accw_dependency);

  npu_gtoa_am_read
  u_gtoa_am1_rd_inst
    (
   .clk        ( clk_gated          ),
   .rst_a      ( rst_dp             ),
   .in_valid   ( accr1_hlapi_valid  ),
   .in_accept  ( accr1_hlapi_accept ),
   .in_pars    ( secd_ac            ),
   `AMRINST_S(am_rd_,am1_rd_,0),
   .out_valid  ( accr1_valid        ),
   .out_accept ( accr1_accept       ),
   .out_acc    ( accr1_data         )
   );


  //
  // Secondary feature-map read
  //
  assign fm1_hlapi_valid   = hlapi_v_valid[3] & (~fmw_dependency) & ((hlapi_i_mc3.u.fu.io_en & act_io_en_fm1_e) != '0) & (hlapi_i_mc3.typ == act_typ_fu_e);
  assign hlapi_v_accept[3] = fm1_hlapi_accept & (~fmw_dependency);
  assign secd_fm           = hlapi_i_mc3.u.fu.secondary.fm_agu;

  npu_vm_lane_read
    #(
      .R ( ACT_FM_LOOPS ),
      .G ( VSIZE        )
      )
  u_gtoa_vm1_lane_rd_inst
    (
     .clk        ( clk_gated             ),
     .rst_a      ( rst_dp                ),
     .in_valid   ( fm1_hlapi_valid       ),
     .in_accept  ( fm1_hlapi_accept      ),
     .iter       ( secd_fm.iter          ),
     .offset     ( secd_fm.offsets       ),
     .stride     ( secd_fm.stride        ),
     .ptr        ( secd_fm.ptr           ),
     .bf         ( secd_fm.buffer        ),
     `VMRINST_S(VSIZE,vm_rd_,vm1_rd_,0),
     .out_valid  ( fmr1_valid            ),
     .out_accept ( fmr1_accept           ),
     .out_data   ( fmr1_data             )
     );


  //
  // Accumulator write
  //
  assign out_ac            = hlapi_i_mc3.u.fu.out.a.am_agu;
  assign accw_hlapi_valid  = hlapi_v_valid[4] & ((hlapi_i_mc3.u.fu.io_en & act_io_en_oac_e) != '0) & (hlapi_i_mc3.typ == act_typ_fu_e);
  assign hlapi_v_accept[4] = accw_hlapi_accept;

  npu_gtoa_am_write
  u_gtoa_am_wr_inst
    (
     .clk        ( clk_gated         ),
     .rst_a      ( rst_dp            ),
     .in_valid   ( accw_hlapi_valid  ),
     .in_accept  ( accw_hlapi_accept ),
     .in_pars    ( out_ac            ),
     .out_valid  ( accw_valid        ),
     .out_accept ( accw_accept       ),
     .out_acc    ( accw_data         ),
     `AMWINST_S(am_wr_,am_wr_,0)
   );

  // Accumulator write dependency
  npu_gtoa_prefetch_dep
  u_gtoa_accw_prefetch_dep
    (
     .clk            ( clk_gated         ),
     .rst_a          ( rst_dp            ),
     .hlp_accept     ( hlapi_i_accept    ),
     .in_wvalid      ( accw_hlapi_valid  ),
     .in_waccept     ( accw_hlapi_accept ),
     .wdep           ( accw_dependency   )
    );
  
  //
  // Feature-map write
  //
  assign fmw_hlapi_valid   = hlapi_v_valid[5] & ((hlapi_i_mc3.u.fu.io_en & act_io_en_ofm_e) != '0) & (hlapi_i_mc3.typ == act_typ_fu_e);
  assign hlapi_v_accept[5] = fmw_hlapi_accept;
  assign out_fm            = hlapi_i_mc3.u.fu.out.p.fm;
  assign cmask             = ~hlapi_i_mc3.u.fu.cmaskn;

  npu_vm_lane_write
    #(
      .R ( ACT_FM_LOOPS ),
      .G ( VSIZE        ),
      .V ( VSIZE        )
      )
  u_gtoa_vm_lane_wr_inst
    (
     .clk        ( clk_gated                     ),
     .rst_a      ( rst_dp                        ),
     .in_valid   ( fmw_hlapi_valid               ),
     .in_accept  ( fmw_hlapi_accept              ),
     .iter       ( out_fm.iter                   ),
     .offset     ( out_fm.offsets                ),
     .stride     ( out_fm.stride                 ),
     .ptr        ( out_fm.ptr                    ),
     .bf         ( out_fm.buffer                 ),
     .vmask      ( hlapi_i_mc3.u.fu.out.p.enable ),
     .cmask      ( cmask                         ),
     .out_valid  ( fmw_valid                     ),
     .out_accept ( fmw_accept                    ),
     .out_data   ( fmw_data                      ),
     `VMWINST_S(VSIZE,vm_wr_,vm_wr_,0)
   );

  // Feature-map write dependency
  npu_gtoa_prefetch_dep
  u_gtoa_fmw_prefetch_dep
    (
     .clk            ( clk_gated         ),
     .rst_a          ( rst_dp            ),
     .hlp_accept     ( hlapi_i_accept    ),
     .in_wvalid      ( fmw_hlapi_valid   ),
     .in_waccept     ( fmw_hlapi_accept  ),
     .wdep           ( fmw_dependency    )
    );
  
  //
  // input/output selection
  //
  npu_gtoa_arb
  u_gtoa_arb_inst
    (
     .clk            ( clk_gated         ),
     .rst_a          ( rst_dp            ),

     .io_en          ( ctrl_io_en        ),

     .accr0_valid    ( accr0_valid       ),
     .fmr0_valid     ( fmr0_valid        ),
     .astr0_valid    ( acc_str_valid     ),
     .arb_rd0_valid  ( arb_rd0_valid     ),

     .accr0_accept   ( accr0_accept      ),
     .fmr0_accept    ( fmr0_accept       ),
     .astr0_accept   ( acc_str_accept    ),
     .arb_rd0_accept ( arb_rd0_accept    ),

     .accr0_data     ( accr0_data        ),
     .fmr0_data      ( fmr0_data         ),
     .astr0_data     ( acc_str_data      ),
     .arb_rd0_data   ( arb_rd0_data      ),

     .accr1_valid    ( accr1_valid       ),
     .fmr1_valid     ( fmr1_valid        ),
     .fstr1_valid    ( fstr1_valid       ),
     .arb_rd1_valid  ( arb_rd1_valid     ),

     .accr1_accept   ( accr1_accept      ),
     .fmr1_accept    ( fmr1_accept       ),
     .fstr1_accept   ( fstr1_accept      ),
     .arb_rd1_accept ( arb_rd1_accept    ),

     .accr1_data     ( accr1_data        ),
     .fmr1_data      ( fmr1_data         ),
     .fstr1_data     ( fstr1_data        ),
     .arb_rd1_data   ( arb_rd1_data      ),

     .accw_valid     ( accw_valid        ),
     .fmw_valid      ( fmw_valid         ),
     .arb_wr_valid   ( arb_wr_valid      ),

     .accw_accept    ( accw_accept       ),
     .fmw_accept     ( fmw_accept        ),
     .arb_wr_accept  ( arb_wr_accept     ),

     .out_dbl        ( core_out_dbl      ),
     .accw_data      ( accw_data         ),
     .fmw_data       ( fmw_data          ),
     .arb_wr_data    ( arb_wr_data       )
    );

  
  //
  // bpar loading
  //
  assign bpar_hlapi_valid  = hlapi_v_valid[6] & (hlapi_i_mc3.typ == act_typ_fu_e) & (hlapi_i_mc3.u.fu.bnum != '0);
  assign hlapi_v_accept[6] = bpar_hlapi_accept | (hlapi_i_mc3.typ != act_typ_fu_e) | (hlapi_i_mc3.u.fu.bnum == '0);
  npu_gtoa_bpar_rd
  u_gtoa_bpar_rd_inst
    (
     .clk            ( clk_gated                ),
     .rst_a          ( rst_dp                   ),
     .hlapi_valid    ( bpar_hlapi_valid         ),
     .hlapi_accept   ( bpar_hlapi_accept        ),
     .hlapi_bptr     ( hlapi_i_mc3.u.fu.bptr    ),
     .hlapi_bnum     ( hlapi_i_mc3.u.fu.bnum    ),
     .hlapi_alay     ( hlapi_i_mc3.u.fu.acc_lay ),
     `VMRINST_S(1,vm_rd_, bpar_rd_,0),
     .bpar_q_lvl     ( core_bpar_q_lvl          ),
     .bpar_pop_q     ( core_bpar_pop_q          ),
     .bpar_pop_q_num ( core_bpar_pop_q_num      ),
     .bpar_out       ( core_bpar_nxt            )
    );


  //
  // Pool stash loading and storing
  //
  assign mpbuf.base        = 16'h0000;
  assign mpbuf.len         = 16'hffff;
  // only use stash if pooling over columns unless 2s2
  assign pool_hlapi_rvalid = hlapi_v_valid[7] &
                             pool_hlapi_waccept &
                             (hlapi_i_mc3.u.fu.out.p.pool.mode != pnone) &
                             (hlapi_i_mc3.u.fu.out.p.pool.mode != prow) &
                             (hlapi_i_mc3.u.fu.out.p.pool.size != p2s2) &
                             (hlapi_i_mc3.typ == act_typ_fu_e);
  assign pool_hlapi_wvalid = hlapi_v_valid[8] &
                             (hlapi_i_mc3.u.fu.out.p.pool.mode != pnone) &
                             (hlapi_i_mc3.u.fu.out.p.pool.mode != prow) &
                             (hlapi_i_mc3.u.fu.out.p.pool.size != p2s2) &
                             (hlapi_i_mc3.typ == act_typ_fu_e);
  assign pool_pars         = hlapi_i_mc3.u.fu.out.p.pool;
  assign core_pool_wen     = hlapi_i_mc3.u.fu.out.p.enable[VSIZE-1:0];
  assign mp_stash2         = hlapi_i_mc3.u.fu.out.p.pool.size == p3s1;
  assign hlapi_v_accept[7] = pool_hlapi_raccept & pool_hlapi_waccept;
  assign hlapi_v_accept[8] = pool_hlapi_waccept;

  // initialize pooling stash offsets
  always_comb
  begin : pool_offset_PROC
    // [ONN*modenum] increment linearly
    pool_offsets[ACT_POOL_LOOPS-1] = 'sd1;
    // [H] increment linearly
    pool_offsets[ACT_POOL_LOOPS-2] = 'sd1;
    // [W] reset to start of column
    pool_offsets[ACT_POOL_LOOPS-3] = '0;
    if (pool_pars.iter[ACT_POOL_LOOPS-1][0])
      pool_offsets[ACT_POOL_LOOPS-3] |= pool_pars.iter[ACT_POOL_LOOPS-2]<<0;
    if (pool_pars.iter[ACT_POOL_LOOPS-1][1])
      pool_offsets[ACT_POOL_LOOPS-3] |= pool_pars.iter[ACT_POOL_LOOPS-2]<<1;
    if (pool_pars.iter[ACT_POOL_LOOPS-1][2])
      pool_offsets[ACT_POOL_LOOPS-3] |= pool_pars.iter[ACT_POOL_LOOPS-2]<<2;
    pool_offsets[ACT_POOL_LOOPS-3] = 'sd1 - pool_offsets[ACT_POOL_LOOPS-3];
    // [C] increment linearly
    pool_offsets[ACT_POOL_LOOPS-4] = 'sd1;
    if (mp_stash2)
    begin
      pool_offsets[ACT_POOL_LOOPS-1] = pool_offsets[ACT_POOL_LOOPS-1] <<1;
      pool_offsets[ACT_POOL_LOOPS-2] = pool_offsets[ACT_POOL_LOOPS-2] <<1;
      pool_offsets[ACT_POOL_LOOPS-3] = pool_offsets[ACT_POOL_LOOPS-3] <<1;
      pool_offsets[ACT_POOL_LOOPS-4] = pool_offsets[ACT_POOL_LOOPS-4] <<1;
    end
  end : pool_offset_PROC

  assign mask_i[0]         = ((pool_pars.mode == pcol) | (pool_pars.mode == prowcol))
                             &(pool_pars.size != p2s2);
  assign mask_i[1]         = ((pool_pars.mode == pcol) | (pool_pars.mode == prowcol))
                             &(pool_pars.size == p3s1);
  assign mp_wr_nopend      = mask_o == 2'b01 ? {2{mpst_wr_cmd_accept[0]}} : mpst_wr_cmd_accept;
  assign mp_rd_pars_en     = pool_hlapi_rvalid & hlapi_v_accept[7];
  assign mp_wr_pars_en     = pool_hlapi_wvalid & hlapi_v_accept[8];

  //
  // Pool stash dependency control
  //
  for (genvar bnk = 0; bnk < 2; bnk++)
  begin : bnk_GEN
    npu_gtoa_mp_dep_ctrl
    u_gtoa_mp_dep_ctrl_inst
      (
       .clk            ( clk_gated         ),
       .rst_a          ( rst_dp            ),
       .rd_in_en       ( mp_rd_pars_en     ),
       .wr_in_en       ( mp_wr_pars_en     ),
       .iter           ( pool_pars.iter    ),
       .rd_hs          ( mp_rd_hs[bnk]     ),
       .wr_hs          ( mp_wr_hs[bnk]     ),
       .wr_nopend      ( mp_wr_nopend[bnk] ),
       .canrd          ( mp_canrd[bnk]     ),
       .canwr          ( mp_canwr[bnk]     )
      );
  end : bnk_GEN

  npu_gtoa_mp_vm_lane_read
    #(
      .R ( ACT_POOL_LOOPS ), // ONN, ROW, COL, NO
      .G ( 2              )
      )
  u_gtoa_mp_rd_inst
    (
     .clk        ( clk_gated         ),
     .rst_a      ( rst_dp            ),
     .in_valid   ( pool_hlapi_rvalid ),
     .in_accept  ( pool_hlapi_raccept),
     .iter       ( pool_pars.iter    ),
     .offset     ( pool_offsets      ),
     .stride     ( 16'd1             ),
     .ptr        ( pool_pars.ptr     ),
     .bf         ( mpbuf             ),
     .mask       ( mask_i            ),
     .mask_o     ( mask_o            ),
     .rd_hs      ( mp_rd_hs          ),
     .canrd      ( mp_canrd          ),
     `VMRINST_S(2,vm_rd_,mpst_rd_,0),
     .out_valid  ( mp_rd_valid       ),
     .out_accept ( mp_rd_accept      ),
     .out_data   ( mp_rd_data        )
   );
  npu_gtoa_mp_vm_lane_write
    #(
      .R ( ACT_POOL_LOOPS ),
      .G ( 2              ),
      .V ( 2              )
      )
  u_gtoa_mp_wr_inst
    (
     .clk        ( clk_gated         ),
     .rst_a      ( rst_dp            ),
     .in_valid   ( pool_hlapi_wvalid ),
     .in_accept  ( pool_hlapi_waccept),
     .iter       ( pool_pars.iter    ),
     .offset     ( pool_offsets      ),
     .stride     ( 16'd1             ),
     .ptr        ( pool_pars.ptr     ),
     .bf         ( mpbuf             ),
     .mask       ( mask_i            ),
     .wr_hs      ( mp_wr_hs          ),
     .canwr      ( mp_canwr          ),
     .out_valid  ( mp_wr_valid       ),
     .out_accept ( mp_wr_accept      ),
     .out_data   ( mp_wr_data        ),
     `VMWINST_S(2,vm_wr_,mpst_wr_,0)
   );

  
  //
  // Drive GTOA core inputs
  //
  assign core_iter_req     = hlapi_v_valid[9] & (hlapi_i_mc3.typ == act_typ_fu_e);
  assign core_lut_init     = hlapi_v_valid[9] & (hlapi_i_mc3.typ == act_typ_lut_e);
  assign hlapi_v_accept[9] = core_iter_ack;
  assign core_in_valid[0]  = arb_rd0_valid;
  assign core_in_valid[1]  = arb_rd1_valid;
  assign core_in_data[0]   = arb_rd0_data;
  assign core_in_data[1]   = arb_rd1_data;
  assign core_out_accept   = arb_wr_accept;
  
  //
  // GTOA core outputs
  //
  assign hlapi_o_stat     = 32'd0;
  assign arb_rd0_accept   = core_in_accept[0];
  assign arb_rd1_accept   = core_in_accept[1];
  assign arb_wr_valid     = core_out_valid;
  assign arb_wr_data      = core_out_data;
  

  //
  // GTOA core interface
  //
  npu_gtoa_core_wrap
  u_gtoa_wrap_inst
    (
     .clk                ( clk_gated                   ),
     .clk_half           ( clk_gated_half              ),
     .cycle              ( cycle                       ),
     .rst_a              ( rst_dp                      ),
     .rst_half           ( rst_half                    ),
     .slc_id             ( slc_id                      ),
     .iter_req           ( core_iter_req               ),
     .iter_ack           ( core_iter_ack               ),
     .iter_shp           ( hlapi_i_mc3.u.fu.iter       ),
     .iter_prog          ( hlapi_i_mc3.u.fu.act_prog   ),
     .iter_lay           ( hlapi_i_mc3.u.fu.acc_lay    ),
     .hlp_scalin         ( hlapi_i_mc3.u.fu.scl        ),
     .lut_init           ( core_lut_init               ),
     .lut_data           ( hlapi_i_mc3.u.lut           ),
     .hlapi_o_valid      ( hlapi_o_valid               ),
     .hlapi_o_accept     ( hlapi_o_accept              ),
     .hlapi_o_res        ( hlapi_o_res                 ),
     .bpar_q_lvl         ( core_bpar_q_lvl             ),
     .bpar_pop_q         ( core_bpar_pop_q             ),
     .bpar_pop_q_num     ( core_bpar_pop_q_num         ),
     .bpar_nxt           ( core_bpar_nxt               ),
     .cf_io_en           ( hlapi_i_mc3.u.fu.io_en      ),
     .cf_i0dbl           ( hlapi_i_mc3.u.fu.in_dbl0    ),
     .cf_i0fmode         ( hlapi_i_mc3.u.fu.in_fmode0  ),
     .cf_i1dbl           ( hlapi_i_mc3.u.fu.in_dbl1    ),
     .cf_i1fmode         ( hlapi_i_mc3.u.fu.in_fmode1  ),
     .cf_osat            ( hlapi_i_mc3.u.fu.out_sat    ),
     .cf_odbl            ( hlapi_i_mc3.u.fu.out_dbl    ),
     .cf_ofmode          ( hlapi_i_mc3.u.fu.out_fmode  ),
     .cf_paden           ( hlapi_i_mc3.u.fu.in_pen0    ),
     .cf_padmode         ( hlapi_i_mc3.u.fu.in_pmode   ),
     .cf_padinc          ( hlapi_i_mc3.u.fu.pad_inc    ),
     .cf_padlim          ( hlapi_i_mc3.u.fu.pad_lim    ),
     .cf_padpos          ( hlapi_i_mc3.u.fu.pad_pos    ),
     .cf_padoffs         ( hlapi_i_mc3.u.fu.pad_offs   ),
     .cf_paditer         ( paditer                     ),
     .cf_padstride       ( hlapi_i_mc3.u.fu.pad_stride ),
     .cf_prim_base       ( prim_fm.buffer.base         ),
     .cf_prim_offsets    ( prim_fm.offsets             ),
     .gather_valid       ( gather_valid                ),
     .gather_accept      ( gather_accept               ),
     .gather_prod        ( gather_vptr                 ),
     .pool_par           ( hlapi_i_mc3.u.fu.out.p.pool ),
     .mpst_rd_valid      ( mp_rd_valid                 ),
     .mpst_rd_accept     ( mp_rd_accept                ),
     .mpst_rd_data       ( mp_rd_data                  ),
     .mpst_wr_valid      ( mp_wr_valid                 ),
     .mpst_wr_accept     ( mp_wr_accept                ),
     .mpst_wr_data       ( mp_wr_data                  ),
     .ctrl_io_en         ( ctrl_io_en                  ),
     .in_valid           ( core_in_valid               ),
     .in_accept          ( core_in_accept              ),
     .in_data            ( core_in_data                ),
     .out_valid          ( core_out_valid              ),
     .out_accept         ( core_out_accept             ),
     .out_data           ( core_out_data               ),
     .out_dbl            ( core_out_dbl                )
   );
  // derive pad iterator
  always_comb
  begin : pad_iter_PROC
    if ((hlapi_i_mc3.u.fu.io_en & act_io_en_fm0_e) != '0)
    begin
      paditer = prim_fm.iter;
    end
    else
    begin
      for (int i = 0; i < ACT_FM_LOOPS-ACT_AM_LOOPS; i++)
      begin
        paditer[i] = 1;
      end
      for (int i = 0; i < ACT_AM_LOOPS; i++)
      begin
        paditer[i+ACT_FM_LOOPS-ACT_AM_LOOPS] = prim_ac.iter[i];
      end
    end
    if (hlapi_i_mc3.u.fu.in_dbl0)
    begin
      paditer[ACT_FM_LOOPS-1] = paditer[ACT_FM_LOOPS-1] >> 'd1;
    end
  end : pad_iter_PROC

  //
  // Tie feature-map streaming interface
  //
  assign fstr1_valid                    = 1'b0;
  assign fstr1_data                     = '0;

endmodule : npu_gtoa_top
