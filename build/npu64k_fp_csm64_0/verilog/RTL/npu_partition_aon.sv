
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

// NPU toplevel
// vcs -sverilog +define+DUMMY_SLICE -f ../../shared/RTL/npu_shared_manifest ../../npu_slice/RTL/npu_slice.sv npu_slice_top.sv npu_cln_wrap.sv npu_cln_group.sv npu_cln_1p5.sv npu_stu_top.sv dummy_modules/npuarc_hs_cluster_top.sv npu_l2arc_group.sv npu_debug_port.v  npu_jtag_port.v  npu_tap_controller.v npu_core.sv npu_top.sv


`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"


module npu_partition_aon
  import npu_types::*;
  import npu_ecc_types::*;
  (
  // power domain
  input  logic                                            grp_pwr_dwn_a,
// Async bridge && reset ctrl

  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst_axi_arvalid, // read command valid
  input  logic                        npu_mst_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst_axi_arsize  ,      // read command
  output logic          [32-1:0] npu_mst_axi_arsid,   // read command SID field
  output logic          [32-1:0] npu_mst_axi_arssid,  // read command SSID field
  // read data channel
  input  logic                        npu_mst_axi_rvalid,  // read data valid
  output logic                        npu_mst_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst_axi_rid,     // read data id
  input  logic          [512-1:0]   npu_mst_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst_axi_rresp,   // read response
  input  logic                        npu_mst_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst_axi_awvalid, // write command valid
  input  logic                        npu_mst_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst_axi_awsize  ,      // read command
  output logic          [32-1:0] npu_mst_axi_awsid,   // write command SID field
  output logic          [32-1:0] npu_mst_axi_awssid,  // write command SSID field
  // write data channel
  output logic                        npu_mst_axi_wvalid,  // write data valid
  input  logic                        npu_mst_axi_wready,  // write data accept
  output logic          [512-1:0]   npu_mst_axi_wdata,   // write data
  output logic          [512/8-1:0] npu_mst_axi_wstrb,   // write data strobe
  output logic                        npu_mst_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst_axi_bvalid,  // write response valid
  output logic                        npu_mst_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst_axi_bresp,    // write response

  input      logic                       npu_noc_clk,
  input      logic                       npu_noc_rst_a,
  input      logic                       grp_clk,
  input      logic                       grp_rst_a,

  `AXIASYNCSLV(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp_noc_axi_gals_),

  input   logic                          test_mode
);
  localparam E2E_HIER_LVL = 0;

  //-npu_mst_axi
  logic [SLICE_DMA_ARUW-1: 0] npu_mst_axi_aruser;
  logic [SLICE_DMA_RUW-1: 0]  npu_mst_axi_ruser;
  logic [SLICE_DMA_AWUW-1: 0] npu_mst_axi_awuser;
  logic [SLICE_DMA_WUW-1: 0]  npu_mst_axi_wuser;
  logic [SLICE_DMA_BUW-1: 0]  npu_mst_axi_buser;
  logic [4-1: 0] npu_mst_axi_arregion;
  logic [4-1: 0] npu_mst_axi_awregion;
  assign npu_mst_axi_ruser   = '0;
  assign npu_mst_axi_buser   = '0;
  assign npu_mst_axi_arsid   = npu_mst_axi_aruser[32+:32];
  assign npu_mst_axi_arssid  = npu_mst_axi_aruser[0+:32];
  assign npu_mst_axi_awsid   = npu_mst_axi_awuser[32+:32];
  assign npu_mst_axi_awssid  = npu_mst_axi_awuser[0+:32];

//NoC master
`AXIWIRES(5,`NPU_INT_AXI_DWIDTH,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,inoc_axi_);
`AXIWIRES(5,`NPU_INT_AXI_DWIDTH,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,noc_axi_);
`AXIWIRES(5,`NPU_INT_AXI_DWIDTH,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,inoc_nu_axi_);


`AXIASGS_EXT(npu_mst_axi_,noc_axi_);

  logic npu_noc_rst_sync;
  npu_reset_ctrl
  u_rst_inst
  (
    .clk       ( npu_noc_clk     ),
    .rst_a     ( npu_noc_rst_a   ),
    .rst       ( npu_noc_rst_sync),
    .test_mode ( test_mode       )
  );

  
  npu_axi_async_tgt
  #(
    .AXIIDW         ( 5                ),
    .AXIDW          ( 64*VSIZE         ),
    .AXIAWUW        ( SLICE_DMA_AWUW   ),
    .AXIWUW         ( SLICE_DMA_WUW    ),
    .AXIBUW         ( SLICE_DMA_BUW    ),
    .AXIARUW        ( SLICE_DMA_ARUW   ),
    .AXIRUW         ( SLICE_DMA_RUW    ),
    .AWFIFO_DEPTHL2 ( 1                ),
    .WFIFO_DEPTHL2  ( 3                ),
    .BFIFO_DEPTHL2  ( 1                ),
    .ARFIFO_DEPTHL2 ( 1                ),
    .RFIFO_DEPTHL2  ( 3                )
  )
  u_axi_tgt
  (
    .axi_mst_clk   ( npu_noc_clk       ), 
    .axi_mst_rst_a ( npu_noc_rst_a     ),
    .ini_pwr_dwn_a ( grp_pwr_dwn_a     ),
    .test_mode     ( test_mode         ),
    .clk_req_a     (                   ), // intentionally left open
    `AXIINST(axi_mst_,inoc_axi_),
    `AXIASYNCSSUB(axi_async_slv_,npu_grp_noc_axi_gals_)
  );

  npu_axi_slice
  #(
    .AXIIDW       ( 5               ),
    .AXIDW        ( `NPU_INT_AXI_DWIDTH),
    .AXIAWUW      ( SLICE_DMA_AWUW  ),
    .AXIWUW       ( SLICE_DMA_WUW   ),
    .AXIBUW       ( SLICE_DMA_BUW   ),
    .AXIARUW      ( SLICE_DMA_ARUW  ),
    .AXIRUW       ( SLICE_DMA_RUW   ),
    .NUMSLC       ( 1               ),
    .AWFIFO_DEPTH ( 2               ),
    .WFIFO_DEPTH  ( 2               ),
    .BFIFO_DEPTH  ( 0               ),
    .ARFIFO_DEPTH ( 2               ),
    .RFIFO_DEPTH  ( 0               )
  )
  u_slc_noc_inst
  (
   .clk   ( npu_noc_clk),
   .rst_a ( npu_noc_rst_sync),
   `AXIINST(axi_slv_,inoc_nu_axi_),
   `AXIINST(axi_mst_,noc_axi_)
   );


//BUS ECC

  `AXIASGNANU(inoc_axi_,inoc_nu_axi_);
  assign inoc_nu_axi_ar      = inoc_axi_ar;
  assign inoc_nu_axi_aw      = inoc_axi_aw;
  assign inoc_nu_axi_aruser  = {8'h0,inoc_axi_aruser[64-1:0]};
  assign inoc_nu_axi_awuser  = {8'h0,inoc_axi_awuser[64-1:0]};

endmodule : npu_partition_aon
