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
`include "arcsync_exported_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"
`include "npu_apb_macros.svh"


module npu_top
  import npu_types::*;
  import npu_ecc_types::*;
 (
  // General signals: clocks & reset
  input  logic                          npu_core_clk,           // Main clock and reset
  input  logic                          npu_core_rst_a,
  input  logic                          npu_noc_clk,            // NoC port clock and reset
  input  logic                          npu_noc_rst_a,
  input  logic                          npu_cfg_clk,            // Configuration port clock and reset
  input  logic                          npu_cfg_rst_a,
  input  logic                          nl2arc0_wdt_clk,   // WDT clock for L2ARC group ARC0
  input  logic                          nl2arc1_wdt_clk,   // WDT clock for L2ARC group ARC1
  input  logic [39:24]                  npu_csm_base,
  // per group clock enable, power-down and reset (at main clock)
  input  logic                          grp0_rst_a,
  input  logic                          grp0_clk_en_a,
  input  logic                          grp1_rst_a,
  input  logic                          grp1_clk_en_a,
  input  logic                          grp2_rst_a,
  input  logic                          grp2_clk_en_a,
  input  logic                          grp3_rst_a,
  input  logic                          grp3_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl0_clk,
  input  logic                          sl0_wdt_clk,
  input  logic                          sl0_rst_a,
  input  logic                          sl0_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl1_clk,
  input  logic                          sl1_wdt_clk,
  input  logic                          sl1_rst_a,
  input  logic                          sl1_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl2_clk,
  input  logic                          sl2_wdt_clk,
  input  logic                          sl2_rst_a,
  input  logic                          sl2_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl3_clk,
  input  logic                          sl3_wdt_clk,
  input  logic                          sl3_rst_a,
  input  logic                          sl3_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl4_clk,
  input  logic                          sl4_wdt_clk,
  input  logic                          sl4_rst_a,
  input  logic                          sl4_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl5_clk,
  input  logic                          sl5_wdt_clk,
  input  logic                          sl5_rst_a,
  input  logic                          sl5_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl6_clk,
  input  logic                          sl6_wdt_clk,
  input  logic                          sl6_rst_a,
  input  logic                          sl6_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl7_clk,
  input  logic                          sl7_wdt_clk,
  input  logic                          sl7_rst_a,
  input  logic                          sl7_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl8_clk,
  input  logic                          sl8_wdt_clk,
  input  logic                          sl8_rst_a,
  input  logic                          sl8_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl9_clk,
  input  logic                          sl9_wdt_clk,
  input  logic                          sl9_rst_a,
  input  logic                          sl9_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl10_clk,
  input  logic                          sl10_wdt_clk,
  input  logic                          sl10_rst_a,
  input  logic                          sl10_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl11_clk,
  input  logic                          sl11_wdt_clk,
  input  logic                          sl11_rst_a,
  input  logic                          sl11_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl12_clk,
  input  logic                          sl12_wdt_clk,
  input  logic                          sl12_rst_a,
  input  logic                          sl12_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl13_clk,
  input  logic                          sl13_wdt_clk,
  input  logic                          sl13_rst_a,
  input  logic                          sl13_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl14_clk,
  input  logic                          sl14_wdt_clk,
  input  logic                          sl14_rst_a,
  input  logic                          sl14_clk_en_a,
  // per slice clock, clock enable, power-down and reset
  input  logic                          sl15_clk,
  input  logic                          sl15_wdt_clk,
  input  logic                          sl15_rst_a,
  input  logic                          sl15_clk_en_a,
  input  logic                          nl2arc0_rst_a,
  input  logic                          nl2arc0_clk_en_a,
  output logic                          nl2arc0_evt_vm_irq,
  input  logic                          nl2arc1_rst_a,
  input  logic                          nl2arc1_clk_en_a,
  output logic                          nl2arc1_evt_vm_irq,
  input  logic                          nl2_rst_a,
  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-master axi
  //-npu_mst0_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst0_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst0_axi_arvalid, // read command valid
  input  logic                        npu_mst0_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst0_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst0_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst0_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst0_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst0_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst0_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst0_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst0_axi_arsize  ,      // read command
  // read data channel
  input  logic                        npu_mst0_axi_rvalid,  // read data valid
  output logic                        npu_mst0_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst0_axi_rid,     // read data id
  input  logic          [64-1:0]   npu_mst0_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst0_axi_rresp,   // read response
  input  logic                        npu_mst0_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst0_axi_awvalid, // write command valid
  input  logic                        npu_mst0_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst0_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst0_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst0_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst0_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst0_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst0_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst0_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst0_axi_awsize  ,      // read command
  // write data channel
  output logic                        npu_mst0_axi_wvalid,  // write data valid
  input  logic                        npu_mst0_axi_wready,  // write data accept
  output logic          [64-1:0]   npu_mst0_axi_wdata,   // write data
  output logic          [64/8-1:0] npu_mst0_axi_wstrb,   // write data strobe
  output logic                        npu_mst0_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst0_axi_bvalid,  // write response valid
  output logic                        npu_mst0_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst0_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst0_axi_bresp,    // write response
  //-npu_mst1_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst1_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst1_axi_arvalid, // read command valid
  input  logic                        npu_mst1_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst1_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst1_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst1_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst1_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst1_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst1_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst1_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst1_axi_arsize  ,      // read command
  output logic          [32-1:0] npu_mst1_axi_arsid,   // read command SID field
  output logic          [32-1:0] npu_mst1_axi_arssid,  // read command SSID field
  // read data channel
  input  logic                        npu_mst1_axi_rvalid,  // read data valid
  output logic                        npu_mst1_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst1_axi_rid,     // read data id
  input  logic          [512-1:0]   npu_mst1_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst1_axi_rresp,   // read response
  input  logic                        npu_mst1_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst1_axi_awvalid, // write command valid
  input  logic                        npu_mst1_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst1_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst1_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst1_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst1_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst1_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst1_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst1_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst1_axi_awsize  ,      // read command
  output logic          [32-1:0] npu_mst1_axi_awsid,   // write command SID field
  output logic          [32-1:0] npu_mst1_axi_awssid,  // write command SSID field
  // write data channel
  output logic                        npu_mst1_axi_wvalid,  // write data valid
  input  logic                        npu_mst1_axi_wready,  // write data accept
  output logic          [512-1:0]   npu_mst1_axi_wdata,   // write data
  output logic          [512/8-1:0] npu_mst1_axi_wstrb,   // write data strobe
  output logic                        npu_mst1_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst1_axi_bvalid,  // write response valid
  output logic                        npu_mst1_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst1_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst1_axi_bresp,    // write response
  //-npu_mst2_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst2_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst2_axi_arvalid, // read command valid
  input  logic                        npu_mst2_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst2_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst2_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst2_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst2_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst2_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst2_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst2_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst2_axi_arsize  ,      // read command
  output logic          [32-1:0] npu_mst2_axi_arsid,   // read command SID field
  output logic          [32-1:0] npu_mst2_axi_arssid,  // read command SSID field
  // read data channel
  input  logic                        npu_mst2_axi_rvalid,  // read data valid
  output logic                        npu_mst2_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst2_axi_rid,     // read data id
  input  logic          [512-1:0]   npu_mst2_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst2_axi_rresp,   // read response
  input  logic                        npu_mst2_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst2_axi_awvalid, // write command valid
  input  logic                        npu_mst2_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst2_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst2_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst2_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst2_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst2_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst2_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst2_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst2_axi_awsize  ,      // read command
  output logic          [32-1:0] npu_mst2_axi_awsid,   // write command SID field
  output logic          [32-1:0] npu_mst2_axi_awssid,  // write command SSID field
  // write data channel
  output logic                        npu_mst2_axi_wvalid,  // write data valid
  input  logic                        npu_mst2_axi_wready,  // write data accept
  output logic          [512-1:0]   npu_mst2_axi_wdata,   // write data
  output logic          [512/8-1:0] npu_mst2_axi_wstrb,   // write data strobe
  output logic                        npu_mst2_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst2_axi_bvalid,  // write response valid
  output logic                        npu_mst2_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst2_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst2_axi_bresp,    // write response
  //-npu_mst3_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst3_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst3_axi_arvalid, // read command valid
  input  logic                        npu_mst3_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst3_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst3_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst3_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst3_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst3_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst3_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst3_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst3_axi_arsize  ,      // read command
  output logic          [32-1:0] npu_mst3_axi_arsid,   // read command SID field
  output logic          [32-1:0] npu_mst3_axi_arssid,  // read command SSID field
  // read data channel
  input  logic                        npu_mst3_axi_rvalid,  // read data valid
  output logic                        npu_mst3_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst3_axi_rid,     // read data id
  input  logic          [512-1:0]   npu_mst3_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst3_axi_rresp,   // read response
  input  logic                        npu_mst3_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst3_axi_awvalid, // write command valid
  input  logic                        npu_mst3_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst3_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst3_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst3_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst3_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst3_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst3_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst3_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst3_axi_awsize  ,      // read command
  output logic          [32-1:0] npu_mst3_axi_awsid,   // write command SID field
  output logic          [32-1:0] npu_mst3_axi_awssid,  // write command SSID field
  // write data channel
  output logic                        npu_mst3_axi_wvalid,  // write data valid
  input  logic                        npu_mst3_axi_wready,  // write data accept
  output logic          [512-1:0]   npu_mst3_axi_wdata,   // write data
  output logic          [512/8-1:0] npu_mst3_axi_wstrb,   // write data strobe
  output logic                        npu_mst3_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst3_axi_bvalid,  // write response valid
  output logic                        npu_mst3_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst3_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst3_axi_bresp,    // write response
  //-npu_mst4_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst4_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst4_axi_arvalid, // read command valid
  input  logic                        npu_mst4_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst4_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst4_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst4_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst4_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst4_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst4_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst4_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst4_axi_arsize  ,      // read command
  output logic          [32-1:0] npu_mst4_axi_arsid,   // read command SID field
  output logic          [32-1:0] npu_mst4_axi_arssid,  // read command SSID field
  // read data channel
  input  logic                        npu_mst4_axi_rvalid,  // read data valid
  output logic                        npu_mst4_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst4_axi_rid,     // read data id
  input  logic          [512-1:0]   npu_mst4_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst4_axi_rresp,   // read response
  input  logic                        npu_mst4_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst4_axi_awvalid, // write command valid
  input  logic                        npu_mst4_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst4_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst4_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst4_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst4_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst4_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst4_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst4_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst4_axi_awsize  ,      // read command
  output logic          [32-1:0] npu_mst4_axi_awsid,   // write command SID field
  output logic          [32-1:0] npu_mst4_axi_awssid,  // write command SSID field
  // write data channel
  output logic                        npu_mst4_axi_wvalid,  // write data valid
  input  logic                        npu_mst4_axi_wready,  // write data accept
  output logic          [512-1:0]   npu_mst4_axi_wdata,   // write data
  output logic          [512/8-1:0] npu_mst4_axi_wstrb,   // write data strobe
  output logic                        npu_mst4_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst4_axi_bvalid,  // write response valid
  output logic                        npu_mst4_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst4_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst4_axi_bresp,    // write response

  //-slave dmi, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_dmi0_axi
  //axislv(1/*idw*/,`aw,`ISIZE*32/*dw*/,1/*argw*/,1/*awgw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/,0/*awcpl*/, npu_dmi0_axi_/*prefix*/)
  // read command channel
  input  logic                        npu_dmi0_axi_arvalid, // read command valid
  output logic                        npu_dmi0_axi_arready, // read command accept
  input  logic          [16-1:0]  npu_dmi0_axi_arid,    // read command ID
  input  logic          [40-1:0]   npu_dmi0_axi_araddr  ,      // read command
  input  logic          [3:0]         npu_dmi0_axi_arcache ,      // read command
  input  logic          [2:0]         npu_dmi0_axi_arprot  ,      // read command
  input  logic          [1-1:0]         npu_dmi0_axi_arlock  ,      // read command
  input  logic          [1:0]         npu_dmi0_axi_arburst ,      // read command
  input  logic          [3:0]         npu_dmi0_axi_arlen   ,      // read command
  input  logic          [2:0]         npu_dmi0_axi_arsize  ,      // read command
  // read data channel
  output logic                        npu_dmi0_axi_rvalid,  // read data valid
  input  logic                        npu_dmi0_axi_rready,  // read data accept
  output logic          [16-1:0]  npu_dmi0_axi_rid,     // read data id
  output logic          [512-1:0]   npu_dmi0_axi_rdata,   // read data
  output logic          [1:0]         npu_dmi0_axi_rresp,   // read response
  output logic                        npu_dmi0_axi_rlast,   // read last
  // write command channel
  input  logic                        npu_dmi0_axi_awvalid, // write command valid
  output logic                        npu_dmi0_axi_awready, // write command accept
  input  logic          [16-1:0]  npu_dmi0_axi_awid,    // write command ID
  input  logic          [40-1:0]   npu_dmi0_axi_awaddr  ,      // read command
  input  logic          [3:0]         npu_dmi0_axi_awcache ,      // read command
  input  logic          [2:0]         npu_dmi0_axi_awprot  ,      // read command
  input  logic          [1-1:0]         npu_dmi0_axi_awlock  ,      // read command
  input  logic          [1:0]         npu_dmi0_axi_awburst ,      // read command
  input  logic          [3:0]         npu_dmi0_axi_awlen   ,      // read command
  input  logic          [2:0]         npu_dmi0_axi_awsize  ,      // read command
  // write data channel
  input  logic                        npu_dmi0_axi_wvalid,  // write data valid
  output logic                        npu_dmi0_axi_wready,  // write data accept
  input  logic          [512-1:0]   npu_dmi0_axi_wdata,   // write data
  input  logic          [512/8-1:0] npu_dmi0_axi_wstrb,   // write data strobe
  input  logic                        npu_dmi0_axi_wlast,   // write data last
  // write response channel
  output logic                        npu_dmi0_axi_bvalid,  // write response valid
  input  logic                        npu_dmi0_axi_bready,  // write response accept
  output logic          [16-1:0]  npu_dmi0_axi_bid,     // write response id
  output logic          [1:0]         npu_dmi0_axi_bresp,   // write response


  // configuration slave AXI
  //axislv(1/*idw*/,`aw,`ISIZE*32/*dw*/,1/*argw*/,1/*awgw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/,0/*awcpl*/, npu_cfg_axi_/*prefix*/)
  // read command channel
  input  logic                        npu_cfg_axi_arvalid, // read command valid
  output logic                        npu_cfg_axi_arready, // read command accept
  input  logic          [16-1:0]  npu_cfg_axi_arid,    // read command ID
  input  logic          [40-1:0]   npu_cfg_axi_araddr  ,      // read command
  input  logic          [3:0]         npu_cfg_axi_arcache ,      // read command
  input  logic          [2:0]         npu_cfg_axi_arprot  ,      // read command
  input  logic          [1-1:0]         npu_cfg_axi_arlock  ,      // read command
  input  logic          [1:0]         npu_cfg_axi_arburst ,      // read command
  input  logic          [3:0]         npu_cfg_axi_arlen   ,      // read command
  input  logic          [2:0]         npu_cfg_axi_arsize  ,      // read command
  // read data channel
  output logic                        npu_cfg_axi_rvalid,  // read data valid
  input  logic                        npu_cfg_axi_rready,  // read data accept
  output logic          [16-1:0]  npu_cfg_axi_rid,     // read data id
  output logic          [32-1:0]   npu_cfg_axi_rdata,   // read data
  output logic          [1:0]         npu_cfg_axi_rresp,   // read response
  output logic                        npu_cfg_axi_rlast,   // read last
  // write command channel
  input  logic                        npu_cfg_axi_awvalid, // write command valid
  output logic                        npu_cfg_axi_awready, // write command accept
  input  logic          [16-1:0]  npu_cfg_axi_awid,    // write command ID
  input  logic          [40-1:0]   npu_cfg_axi_awaddr  ,      // read command
  input  logic          [3:0]         npu_cfg_axi_awcache ,      // read command
  input  logic          [2:0]         npu_cfg_axi_awprot  ,      // read command
  input  logic          [1-1:0]         npu_cfg_axi_awlock  ,      // read command
  input  logic          [1:0]         npu_cfg_axi_awburst ,      // read command
  input  logic          [3:0]         npu_cfg_axi_awlen   ,      // read command
  input  logic          [2:0]         npu_cfg_axi_awsize  ,      // read command
  // write data channel
  input  logic                        npu_cfg_axi_wvalid,  // write data valid
  output logic                        npu_cfg_axi_wready,  // write data accept
  input  logic          [32-1:0]   npu_cfg_axi_wdata,   // write data
  input  logic          [32/8-1:0] npu_cfg_axi_wstrb,   // write data strobe
  input  logic                        npu_cfg_axi_wlast,   // write data last
  // write response channel
  output logic                        npu_cfg_axi_bvalid,  // write response valid
  input  logic                        npu_cfg_axi_bready,  // write response accept
  output logic          [16-1:0]  npu_cfg_axi_bid,     // write response id
  output logic          [1:0]         npu_cfg_axi_bresp,   // write response

  input  logic                          nl2arc_pwr_dwn_a,
  input  logic                          nl2arc0_pwr_dwn_a,
  input  logic                          nl2arc1_pwr_dwn_a,
  input  logic                          grp0_pwr_dwn_a,
  input  logic                          grp1_pwr_dwn_a,
  input  logic                          grp2_pwr_dwn_a,
  input  logic                          grp3_pwr_dwn_a,
  input  logic                          sl0nl1arc_pwr_dwn_a,
  input  logic                          sl1nl1arc_pwr_dwn_a,
  input  logic                          sl2nl1arc_pwr_dwn_a,
  input  logic                          sl3nl1arc_pwr_dwn_a,
  input  logic                          sl4nl1arc_pwr_dwn_a,
  input  logic                          sl5nl1arc_pwr_dwn_a,
  input  logic                          sl6nl1arc_pwr_dwn_a,
  input  logic                          sl7nl1arc_pwr_dwn_a,
  input  logic                          sl8nl1arc_pwr_dwn_a,
  input  logic                          sl9nl1arc_pwr_dwn_a,
  input  logic                          sl10nl1arc_pwr_dwn_a,
  input  logic                          sl11nl1arc_pwr_dwn_a,
  input  logic                          sl12nl1arc_pwr_dwn_a,
  input  logic                          sl13nl1arc_pwr_dwn_a,
  input  logic                          sl14nl1arc_pwr_dwn_a,
  input  logic                          sl15nl1arc_pwr_dwn_a,

  // power domain
  // -l2arc
    // Power status                                                                                                     
  input logic                       nl2arc_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       nl2arc_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       nl2arc_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       nl2arc_pd_logic,    // Power down of power domain logics                     
    // NPU Group Power status
  input logic                       grp0_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp0_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp0_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp0_pd_logic,    // Power down of power domain logics                     
  // NPU Group Power status
  input logic                       grp1_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp1_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp1_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp1_pd_logic,    // Power down of power domain logics                     
  // NPU Group Power status
  input logic                       grp2_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp2_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp2_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp2_pd_logic,    // Power down of power domain logics                     
  // NPU Group Power status
  input logic                       grp3_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp3_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp3_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp3_pd_logic,    // Power down of power domain logics                     
  // - l1arcs
    // Power status                                                                                                     
  input logic                       sl0nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl0nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl0nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl0nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl1nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl1nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl1nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl1nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl2nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl2nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl2nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl2nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl3nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl3nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl3nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl3nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl4nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl4nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl4nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl4nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl5nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl5nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl5nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl5nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl6nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl6nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl6nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl6nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl7nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl7nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl7nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl7nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl8nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl8nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl8nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl8nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl9nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl9nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl9nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl9nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl10nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl10nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl10nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl10nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl11nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl11nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl11nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl11nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl12nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl12nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl12nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl12nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl13nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl13nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl13nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl13nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl14nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl14nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl14nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl14nl1arc_pd_logic,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl15nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl15nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl15nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl15nl1arc_pd_logic,    // Power down of power domain logics                       

  input  logic                          nl2arc_irq0_a, // From user-defined IRQ sources
  input  logic                          nl2arc_irq1_a,
  // L2 signals (#0)
  output logic                          nl2arc0_wdt_reset_error    ,
  output logic                          nl2arc0_wdt_reset_wdt_clk_error  ,
  // Boot
  input  logic [21:0]                   nl2arc0_intvbase_in,
  // Halt
  input  logic                          nl2arc0_arc_halt_req_a,
  output logic                          nl2arc0_arc_halt_ack,
  // Run
  input  logic                          nl2arc0_arc_run_req_a,
  output logic                          nl2arc0_arc_run_ack,
  // Status
  output logic                          nl2arc0_sys_sleep_r,
  output logic [2:0]                    nl2arc0_sys_sleep_mode_r,
  output logic                          nl2arc0_sys_halt_r,
  output logic                          nl2arc0_sys_tf_halt_r,
  // IRQ and Event
  input  logic [17:0]    nl2arc0_arc_irq_a,
  input  logic [17:0]    nl2arc0_arc_event_a,
  // L2 signals (#1)
  output logic                          nl2arc1_wdt_reset_error    ,
  output logic                          nl2arc1_wdt_reset_wdt_clk_error  ,
  // Boot
  input  logic [21:0]                   nl2arc1_intvbase_in,
  // Halt
  input  logic                          nl2arc1_arc_halt_req_a,
  output logic                          nl2arc1_arc_halt_ack,
  // Run
  input  logic                          nl2arc1_arc_run_req_a,
  output logic                          nl2arc1_arc_run_ack,
  // Status
  output logic                          nl2arc1_sys_sleep_r,
  output logic [2:0]                    nl2arc1_sys_sleep_mode_r,
  output logic                          nl2arc1_sys_halt_r,
  output logic                          nl2arc1_sys_tf_halt_r,
  // IRQ and Event
  input  logic [17:0]    nl2arc1_arc_irq_a,
  input  logic [17:0]    nl2arc1_arc_event_a,
  // L1 ARC in NPU SLice
  output logic                          sl0nl1arc_wdt_reset_error  ,
  output logic                          sl0nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl0nl1arc_intvbase_in,
  // Halt
  input  logic                          sl0nl1arc_arc_halt_req_a,
  output logic                          sl0nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl0nl1arc_arc_run_req_a,
  output logic                          sl0nl1arc_arc_run_ack,
  // Status
  output logic                          sl0nl1arc_sys_sleep_r,
  output logic [2:0]                    sl0nl1arc_sys_sleep_mode_r,
  output logic                          sl0nl1arc_sys_halt_r,
  output logic                          sl0nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl0nl1arc_arc_irq_a,
  output logic                          sl1nl1arc_wdt_reset_error  ,
  output logic                          sl1nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl1nl1arc_intvbase_in,
  // Halt
  input  logic                          sl1nl1arc_arc_halt_req_a,
  output logic                          sl1nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl1nl1arc_arc_run_req_a,
  output logic                          sl1nl1arc_arc_run_ack,
  // Status
  output logic                          sl1nl1arc_sys_sleep_r,
  output logic [2:0]                    sl1nl1arc_sys_sleep_mode_r,
  output logic                          sl1nl1arc_sys_halt_r,
  output logic                          sl1nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl1nl1arc_arc_irq_a,
  output logic                          sl2nl1arc_wdt_reset_error  ,
  output logic                          sl2nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl2nl1arc_intvbase_in,
  // Halt
  input  logic                          sl2nl1arc_arc_halt_req_a,
  output logic                          sl2nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl2nl1arc_arc_run_req_a,
  output logic                          sl2nl1arc_arc_run_ack,
  // Status
  output logic                          sl2nl1arc_sys_sleep_r,
  output logic [2:0]                    sl2nl1arc_sys_sleep_mode_r,
  output logic                          sl2nl1arc_sys_halt_r,
  output logic                          sl2nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl2nl1arc_arc_irq_a,
  output logic                          sl3nl1arc_wdt_reset_error  ,
  output logic                          sl3nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl3nl1arc_intvbase_in,
  // Halt
  input  logic                          sl3nl1arc_arc_halt_req_a,
  output logic                          sl3nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl3nl1arc_arc_run_req_a,
  output logic                          sl3nl1arc_arc_run_ack,
  // Status
  output logic                          sl3nl1arc_sys_sleep_r,
  output logic [2:0]                    sl3nl1arc_sys_sleep_mode_r,
  output logic                          sl3nl1arc_sys_halt_r,
  output logic                          sl3nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl3nl1arc_arc_irq_a,
  output logic                          sl4nl1arc_wdt_reset_error  ,
  output logic                          sl4nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl4nl1arc_intvbase_in,
  // Halt
  input  logic                          sl4nl1arc_arc_halt_req_a,
  output logic                          sl4nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl4nl1arc_arc_run_req_a,
  output logic                          sl4nl1arc_arc_run_ack,
  // Status
  output logic                          sl4nl1arc_sys_sleep_r,
  output logic [2:0]                    sl4nl1arc_sys_sleep_mode_r,
  output logic                          sl4nl1arc_sys_halt_r,
  output logic                          sl4nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl4nl1arc_arc_irq_a,
  output logic                          sl5nl1arc_wdt_reset_error  ,
  output logic                          sl5nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl5nl1arc_intvbase_in,
  // Halt
  input  logic                          sl5nl1arc_arc_halt_req_a,
  output logic                          sl5nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl5nl1arc_arc_run_req_a,
  output logic                          sl5nl1arc_arc_run_ack,
  // Status
  output logic                          sl5nl1arc_sys_sleep_r,
  output logic [2:0]                    sl5nl1arc_sys_sleep_mode_r,
  output logic                          sl5nl1arc_sys_halt_r,
  output logic                          sl5nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl5nl1arc_arc_irq_a,
  output logic                          sl6nl1arc_wdt_reset_error  ,
  output logic                          sl6nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl6nl1arc_intvbase_in,
  // Halt
  input  logic                          sl6nl1arc_arc_halt_req_a,
  output logic                          sl6nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl6nl1arc_arc_run_req_a,
  output logic                          sl6nl1arc_arc_run_ack,
  // Status
  output logic                          sl6nl1arc_sys_sleep_r,
  output logic [2:0]                    sl6nl1arc_sys_sleep_mode_r,
  output logic                          sl6nl1arc_sys_halt_r,
  output logic                          sl6nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl6nl1arc_arc_irq_a,
  output logic                          sl7nl1arc_wdt_reset_error  ,
  output logic                          sl7nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl7nl1arc_intvbase_in,
  // Halt
  input  logic                          sl7nl1arc_arc_halt_req_a,
  output logic                          sl7nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl7nl1arc_arc_run_req_a,
  output logic                          sl7nl1arc_arc_run_ack,
  // Status
  output logic                          sl7nl1arc_sys_sleep_r,
  output logic [2:0]                    sl7nl1arc_sys_sleep_mode_r,
  output logic                          sl7nl1arc_sys_halt_r,
  output logic                          sl7nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl7nl1arc_arc_irq_a,
  output logic                          sl8nl1arc_wdt_reset_error  ,
  output logic                          sl8nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl8nl1arc_intvbase_in,
  // Halt
  input  logic                          sl8nl1arc_arc_halt_req_a,
  output logic                          sl8nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl8nl1arc_arc_run_req_a,
  output logic                          sl8nl1arc_arc_run_ack,
  // Status
  output logic                          sl8nl1arc_sys_sleep_r,
  output logic [2:0]                    sl8nl1arc_sys_sleep_mode_r,
  output logic                          sl8nl1arc_sys_halt_r,
  output logic                          sl8nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl8nl1arc_arc_irq_a,
  output logic                          sl9nl1arc_wdt_reset_error  ,
  output logic                          sl9nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl9nl1arc_intvbase_in,
  // Halt
  input  logic                          sl9nl1arc_arc_halt_req_a,
  output logic                          sl9nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl9nl1arc_arc_run_req_a,
  output logic                          sl9nl1arc_arc_run_ack,
  // Status
  output logic                          sl9nl1arc_sys_sleep_r,
  output logic [2:0]                    sl9nl1arc_sys_sleep_mode_r,
  output logic                          sl9nl1arc_sys_halt_r,
  output logic                          sl9nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl9nl1arc_arc_irq_a,
  output logic                          sl10nl1arc_wdt_reset_error  ,
  output logic                          sl10nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl10nl1arc_intvbase_in,
  // Halt
  input  logic                          sl10nl1arc_arc_halt_req_a,
  output logic                          sl10nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl10nl1arc_arc_run_req_a,
  output logic                          sl10nl1arc_arc_run_ack,
  // Status
  output logic                          sl10nl1arc_sys_sleep_r,
  output logic [2:0]                    sl10nl1arc_sys_sleep_mode_r,
  output logic                          sl10nl1arc_sys_halt_r,
  output logic                          sl10nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl10nl1arc_arc_irq_a,
  output logic                          sl11nl1arc_wdt_reset_error  ,
  output logic                          sl11nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl11nl1arc_intvbase_in,
  // Halt
  input  logic                          sl11nl1arc_arc_halt_req_a,
  output logic                          sl11nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl11nl1arc_arc_run_req_a,
  output logic                          sl11nl1arc_arc_run_ack,
  // Status
  output logic                          sl11nl1arc_sys_sleep_r,
  output logic [2:0]                    sl11nl1arc_sys_sleep_mode_r,
  output logic                          sl11nl1arc_sys_halt_r,
  output logic                          sl11nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl11nl1arc_arc_irq_a,
  output logic                          sl12nl1arc_wdt_reset_error  ,
  output logic                          sl12nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl12nl1arc_intvbase_in,
  // Halt
  input  logic                          sl12nl1arc_arc_halt_req_a,
  output logic                          sl12nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl12nl1arc_arc_run_req_a,
  output logic                          sl12nl1arc_arc_run_ack,
  // Status
  output logic                          sl12nl1arc_sys_sleep_r,
  output logic [2:0]                    sl12nl1arc_sys_sleep_mode_r,
  output logic                          sl12nl1arc_sys_halt_r,
  output logic                          sl12nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl12nl1arc_arc_irq_a,
  output logic                          sl13nl1arc_wdt_reset_error  ,
  output logic                          sl13nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl13nl1arc_intvbase_in,
  // Halt
  input  logic                          sl13nl1arc_arc_halt_req_a,
  output logic                          sl13nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl13nl1arc_arc_run_req_a,
  output logic                          sl13nl1arc_arc_run_ack,
  // Status
  output logic                          sl13nl1arc_sys_sleep_r,
  output logic [2:0]                    sl13nl1arc_sys_sleep_mode_r,
  output logic                          sl13nl1arc_sys_halt_r,
  output logic                          sl13nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl13nl1arc_arc_irq_a,
  output logic                          sl14nl1arc_wdt_reset_error  ,
  output logic                          sl14nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl14nl1arc_intvbase_in,
  // Halt
  input  logic                          sl14nl1arc_arc_halt_req_a,
  output logic                          sl14nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl14nl1arc_arc_run_req_a,
  output logic                          sl14nl1arc_arc_run_ack,
  // Status
  output logic                          sl14nl1arc_sys_sleep_r,
  output logic [2:0]                    sl14nl1arc_sys_sleep_mode_r,
  output logic                          sl14nl1arc_sys_halt_r,
  output logic                          sl14nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl14nl1arc_arc_irq_a,
  output logic                          sl15nl1arc_wdt_reset_error  ,
  output logic                          sl15nl1arc_wdt_reset_wdt_clk_error,
  // Boot
  input  logic [21:0]                   sl15nl1arc_intvbase_in,
  // Halt
  input  logic                          sl15nl1arc_arc_halt_req_a,
  output logic                          sl15nl1arc_arc_halt_ack,
  // Run
  input  logic                          sl15nl1arc_arc_run_req_a,
  output logic                          sl15nl1arc_arc_run_ack,
  // Status
  output logic                          sl15nl1arc_sys_sleep_r,
  output logic [2:0]                    sl15nl1arc_sys_sleep_mode_r,
  output logic                          sl15nl1arc_sys_halt_r,
  output logic                          sl15nl1arc_sys_tf_halt_r,
  // IRQ and Event
  input  logic [1:0]    sl15nl1arc_arc_irq_a,
  // Slice 0 ECC SBE and DBE combined signals
  output logic                          sl0_ecc_sbe,
  output logic                          sl0_ecc_dbe,
  // Slice 1 ECC SBE and DBE combined signals
  output logic                          sl1_ecc_sbe,
  output logic                          sl1_ecc_dbe,
  // Slice 2 ECC SBE and DBE combined signals
  output logic                          sl2_ecc_sbe,
  output logic                          sl2_ecc_dbe,
  // Slice 3 ECC SBE and DBE combined signals
  output logic                          sl3_ecc_sbe,
  output logic                          sl3_ecc_dbe,
  // Slice 4 ECC SBE and DBE combined signals
  output logic                          sl4_ecc_sbe,
  output logic                          sl4_ecc_dbe,
  // Slice 5 ECC SBE and DBE combined signals
  output logic                          sl5_ecc_sbe,
  output logic                          sl5_ecc_dbe,
  // Slice 6 ECC SBE and DBE combined signals
  output logic                          sl6_ecc_sbe,
  output logic                          sl6_ecc_dbe,
  // Slice 7 ECC SBE and DBE combined signals
  output logic                          sl7_ecc_sbe,
  output logic                          sl7_ecc_dbe,
  // Slice 8 ECC SBE and DBE combined signals
  output logic                          sl8_ecc_sbe,
  output logic                          sl8_ecc_dbe,
  // Slice 9 ECC SBE and DBE combined signals
  output logic                          sl9_ecc_sbe,
  output logic                          sl9_ecc_dbe,
  // Slice 10 ECC SBE and DBE combined signals
  output logic                          sl10_ecc_sbe,
  output logic                          sl10_ecc_dbe,
  // Slice 11 ECC SBE and DBE combined signals
  output logic                          sl11_ecc_sbe,
  output logic                          sl11_ecc_dbe,
  // Slice 12 ECC SBE and DBE combined signals
  output logic                          sl12_ecc_sbe,
  output logic                          sl12_ecc_dbe,
  // Slice 13 ECC SBE and DBE combined signals
  output logic                          sl13_ecc_sbe,
  output logic                          sl13_ecc_dbe,
  // Slice 14 ECC SBE and DBE combined signals
  output logic                          sl14_ecc_sbe,
  output logic                          sl14_ecc_dbe,
  // Slice 15 ECC SBE and DBE combined signals
  output logic                          sl15_ecc_sbe,
  output logic                          sl15_ecc_dbe,
  // L2 ARC0 memory ECC error signal
  output logic                          nl2arc0_ecc_sbe,
  output logic                          nl2arc0_ecc_dbe,
  // L2 ARC1 memory ECC error signal
  output logic                          nl2arc1_ecc_sbe,
  output logic                          nl2arc1_ecc_dbe,
  // CSM memory SBE
  output logic                          grp0_scm_dbank_sbe,
  output logic                          grp0_scm_dbank_dbe,
  output logic                          grp1_scm_dbank_sbe,
  output logic                          grp1_scm_dbank_dbe,
  output logic                          grp2_scm_dbank_sbe,
  output logic                          grp2_scm_dbank_dbe,
  output logic                          grp3_scm_dbank_sbe,
  output logic                          grp3_scm_dbank_dbe,

  //ARC_Trace
  // CoreSight interface global signals
  input  logic                          atclken,
  input  logic                          atresetn,
  input  logic [63:0]                   atb_cstimestamp,
  // CoreSight interface of L2 core or L1 core in case of NPU HAS NO L2ARC
  input  logic                          atready,
  output logic [64-1:0]     atdata,
  output logic [3-1:0]      atbytes,
  output logic [6:0]                    atid,
  output logic                          atvalid,
  input  logic                          afvalid,
  output logic                          afready,
  input  logic                          syncreq,
  // CoreSight interface of NPU Slices
  input  logic                          swe_atready,
  output logic [64-1:0] swe_atdata,
  output logic [3-1:0]  swe_atbytes,
  output logic [6:0]                    swe_atid,
  output logic                          swe_atvalid,
  input  logic                          swe_afvalid,
  output logic                          swe_afready,
  input  logic                          swe_syncreq,
  // CTI signalling
  output logic [25:0]                   cti_rtt_filters,
  input  logic                          cti_trace_start,
  input  logic                          cti_trace_stop,

  // APB Interface for debugging and to ARC_Trace
  input  logic                          pclkdbg,
  input  logic                          presetdbgn,
  input  logic [31:2]                   arct0_paddrdbg,
  input  logic                          arct0_pseldbg,
  input  logic                          arct0_penabledbg,
  input  logic                          arct0_pwritedbg,
  input  logic [31:0]                   arct0_pwdatadbg,
  output logic                          arct0_preadydbg,
  output logic [31:0]                   arct0_prdatadbg,
  output logic                          arct0_pslverrdbg,
  input  logic                          arct0_dbgen,
  input  logic                          arct0_niden,
  input  logic                          sl0nl1arc_niden,
  input  logic                          sl0nl1arc_dbgen,
  input  logic                          sl1nl1arc_niden,
  input  logic                          sl1nl1arc_dbgen,
  input  logic                          sl2nl1arc_niden,
  input  logic                          sl2nl1arc_dbgen,
  input  logic                          sl3nl1arc_niden,
  input  logic                          sl3nl1arc_dbgen,
  input  logic                          sl4nl1arc_niden,
  input  logic                          sl4nl1arc_dbgen,
  input  logic                          sl5nl1arc_niden,
  input  logic                          sl5nl1arc_dbgen,
  input  logic                          sl6nl1arc_niden,
  input  logic                          sl6nl1arc_dbgen,
  input  logic                          sl7nl1arc_niden,
  input  logic                          sl7nl1arc_dbgen,
  input  logic                          sl8nl1arc_niden,
  input  logic                          sl8nl1arc_dbgen,
  input  logic                          sl9nl1arc_niden,
  input  logic                          sl9nl1arc_dbgen,
  input  logic                          sl10nl1arc_niden,
  input  logic                          sl10nl1arc_dbgen,
  input  logic                          sl11nl1arc_niden,
  input  logic                          sl11nl1arc_dbgen,
  input  logic                          sl12nl1arc_niden,
  input  logic                          sl12nl1arc_dbgen,
  input  logic                          sl13nl1arc_niden,
  input  logic                          sl13nl1arc_dbgen,
  input  logic                          sl14nl1arc_niden,
  input  logic                          sl14nl1arc_dbgen,
  input  logic                          sl15nl1arc_niden,
  input  logic                          sl15nl1arc_dbgen,
  input  logic                          nl2arc0_dbgen,
  input  logic                          nl2arc0_niden,
  input  logic                          nl2arc1_dbgen,
  input  logic                          nl2arc1_niden,
  input  logic [7:0]                    clusternum,
  input  logic                          test_mode
);

  localparam int L2IDW  = 2+$clog2(`NPU_AXI_TARGETS+1);
  localparam int CCMIDW = 1;


  logic                          arct_clk;
  logic                          arct_rst_an;
  `APBWIRES(32,32,arct_);
  `APBWIRES(16,32,arct1_);
  logic                          arct_dbg_prot_sel;
  assign arct_dbg_prot_sel = 1'b1; // fix to APB
  assign arct_clk          = pclkdbg;
  assign arct_rst_an       = presetdbgn;
  assign arct_psel         = arct0_pseldbg;
  assign arct_penable      = arct0_penabledbg;
  assign arct_paddr        = arct0_paddrdbg;
  assign arct_pwrite       = arct0_pwritedbg;
  assign arct_pwdata       = arct0_pwdatadbg;
  assign arct0_preadydbg   = arct_pready;
  assign arct0_prdatadbg   = arct_prdata;
  assign arct0_pslverrdbg  = arct_pslverr;
  //ARC_Trace
  logic                          at_clk_en;
  logic                          at_rst_an;
  assign at_clk_en = atclken;
  assign at_rst_an = atresetn;
  //NoC master
  `AXIASYNCWIRES(5,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,l2arc_noc_axi_gals_);
  `AXIASYNCWIRES(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp0_noc_axi_gals_);
  `AXIASYNCWIRES(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp1_noc_axi_gals_);
  `AXIASYNCWIRES(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp2_noc_axi_gals_);
  `AXIASYNCWIRES(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp3_noc_axi_gals_);


  //DMI slave
  `AXIASYNCWIRES(`NPU_AXI_TARGET_ID_WIDTH,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,dmi0_axi_gals_);

  //Config AXI
  // configuration slave AXI
  `AXIASYNCWIRES(`NPU_AXI_TARGET_ID_WIDTH,32,1,1,1,1,1,0,0,0,0,0,cfg_axi_gals_);

  logic                       sl0nl1arc_evt_vm_irq;
  logic                       sl1nl1arc_evt_vm_irq;
  logic                       sl2nl1arc_evt_vm_irq;
  logic                       sl3nl1arc_evt_vm_irq;
  logic                       sl4nl1arc_evt_vm_irq;
  logic                       sl5nl1arc_evt_vm_irq;
  logic                       sl6nl1arc_evt_vm_irq;
  logic                       sl7nl1arc_evt_vm_irq;
  logic                       sl8nl1arc_evt_vm_irq;
  logic                       sl9nl1arc_evt_vm_irq;
  logic                       sl10nl1arc_evt_vm_irq;
  logic                       sl11nl1arc_evt_vm_irq;
  logic                       sl12nl1arc_evt_vm_irq;
  logic                       sl13nl1arc_evt_vm_irq;
  logic                       sl14nl1arc_evt_vm_irq;
  logic                       sl15nl1arc_evt_vm_irq;
  logic                       grp0_evt_vm_irq;
  logic                       grp1_evt_vm_irq;
  logic                       grp2_evt_vm_irq;
  logic                       grp3_evt_vm_irq;
  // STU events and interrupts
  logic [`NPU_STU_CHAN_NUM-1:0]           stu_err_irq_a;
  logic [64-1: 0]     npu_grp0_vmid;
  logic [64-1: 0]     npu_grp1_vmid;
  logic [64-1: 0]     npu_grp2_vmid;
  logic [64-1: 0]     npu_grp3_vmid;



  //
  // Async AXI and debug interfaces per slice
  //
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl0nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl0nl1arc_ccm_axi_gals_);
  logic                                          sl0nl1arc_dbg_cmdval;
  logic [36:0]                                   sl0nl1arc_dbg_pack;
  logic [31:0]                                   sl0nl1arc_dbg_resp;
  // Trace
  logic                                          sl0_rtt_swe_val;
  logic [32:0]                                   sl0_rtt_swe_data;
  logic [7:0]                                    sl0_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl1nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl1nl1arc_ccm_axi_gals_);
  logic                                          sl1nl1arc_dbg_cmdval;
  logic [36:0]                                   sl1nl1arc_dbg_pack;
  logic [31:0]                                   sl1nl1arc_dbg_resp;
  // Trace
  logic                                          sl1_rtt_swe_val;
  logic [32:0]                                   sl1_rtt_swe_data;
  logic [7:0]                                    sl1_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl2nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl2nl1arc_ccm_axi_gals_);
  logic                                          sl2nl1arc_dbg_cmdval;
  logic [36:0]                                   sl2nl1arc_dbg_pack;
  logic [31:0]                                   sl2nl1arc_dbg_resp;
  // Trace
  logic                                          sl2_rtt_swe_val;
  logic [32:0]                                   sl2_rtt_swe_data;
  logic [7:0]                                    sl2_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl3nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl3nl1arc_ccm_axi_gals_);
  logic                                          sl3nl1arc_dbg_cmdval;
  logic [36:0]                                   sl3nl1arc_dbg_pack;
  logic [31:0]                                   sl3nl1arc_dbg_resp;
  // Trace
  logic                                          sl3_rtt_swe_val;
  logic [32:0]                                   sl3_rtt_swe_data;
  logic [7:0]                                    sl3_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl4nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl4nl1arc_ccm_axi_gals_);
  logic                                          sl4nl1arc_dbg_cmdval;
  logic [36:0]                                   sl4nl1arc_dbg_pack;
  logic [31:0]                                   sl4nl1arc_dbg_resp;
  // Trace
  logic                                          sl4_rtt_swe_val;
  logic [32:0]                                   sl4_rtt_swe_data;
  logic [7:0]                                    sl4_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl5nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl5nl1arc_ccm_axi_gals_);
  logic                                          sl5nl1arc_dbg_cmdval;
  logic [36:0]                                   sl5nl1arc_dbg_pack;
  logic [31:0]                                   sl5nl1arc_dbg_resp;
  // Trace
  logic                                          sl5_rtt_swe_val;
  logic [32:0]                                   sl5_rtt_swe_data;
  logic [7:0]                                    sl5_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl6nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl6nl1arc_ccm_axi_gals_);
  logic                                          sl6nl1arc_dbg_cmdval;
  logic [36:0]                                   sl6nl1arc_dbg_pack;
  logic [31:0]                                   sl6nl1arc_dbg_resp;
  // Trace
  logic                                          sl6_rtt_swe_val;
  logic [32:0]                                   sl6_rtt_swe_data;
  logic [7:0]                                    sl6_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl7nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl7nl1arc_ccm_axi_gals_);
  logic                                          sl7nl1arc_dbg_cmdval;
  logic [36:0]                                   sl7nl1arc_dbg_pack;
  logic [31:0]                                   sl7nl1arc_dbg_resp;
  // Trace
  logic                                          sl7_rtt_swe_val;
  logic [32:0]                                   sl7_rtt_swe_data;
  logic [7:0]                                    sl7_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl8nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl8nl1arc_ccm_axi_gals_);
  logic                                          sl8nl1arc_dbg_cmdval;
  logic [36:0]                                   sl8nl1arc_dbg_pack;
  logic [31:0]                                   sl8nl1arc_dbg_resp;
  // Trace
  logic                                          sl8_rtt_swe_val;
  logic [32:0]                                   sl8_rtt_swe_data;
  logic [7:0]                                    sl8_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl9nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl9nl1arc_ccm_axi_gals_);
  logic                                          sl9nl1arc_dbg_cmdval;
  logic [36:0]                                   sl9nl1arc_dbg_pack;
  logic [31:0]                                   sl9nl1arc_dbg_resp;
  // Trace
  logic                                          sl9_rtt_swe_val;
  logic [32:0]                                   sl9_rtt_swe_data;
  logic [7:0]                                    sl9_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl10nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl10nl1arc_ccm_axi_gals_);
  logic                                          sl10nl1arc_dbg_cmdval;
  logic [36:0]                                   sl10nl1arc_dbg_pack;
  logic [31:0]                                   sl10nl1arc_dbg_resp;
  // Trace
  logic                                          sl10_rtt_swe_val;
  logic [32:0]                                   sl10_rtt_swe_data;
  logic [7:0]                                    sl10_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl11nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl11nl1arc_ccm_axi_gals_);
  logic                                          sl11nl1arc_dbg_cmdval;
  logic [36:0]                                   sl11nl1arc_dbg_pack;
  logic [31:0]                                   sl11nl1arc_dbg_resp;
  // Trace
  logic                                          sl11_rtt_swe_val;
  logic [32:0]                                   sl11_rtt_swe_data;
  logic [7:0]                                    sl11_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl12nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl12nl1arc_ccm_axi_gals_);
  logic                                          sl12nl1arc_dbg_cmdval;
  logic [36:0]                                   sl12nl1arc_dbg_pack;
  logic [31:0]                                   sl12nl1arc_dbg_resp;
  // Trace
  logic                                          sl12_rtt_swe_val;
  logic [32:0]                                   sl12_rtt_swe_data;
  logic [7:0]                                    sl12_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl13nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl13nl1arc_ccm_axi_gals_);
  logic                                          sl13nl1arc_dbg_cmdval;
  logic [36:0]                                   sl13nl1arc_dbg_pack;
  logic [31:0]                                   sl13nl1arc_dbg_resp;
  // Trace
  logic                                          sl13_rtt_swe_val;
  logic [32:0]                                   sl13_rtt_swe_data;
  logic [7:0]                                    sl13_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl14nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl14nl1arc_ccm_axi_gals_);
  logic                                          sl14nl1arc_dbg_cmdval;
  logic [36:0]                                   sl14nl1arc_dbg_pack;
  logic [31:0]                                   sl14nl1arc_dbg_resp;
  // Trace
  logic                                          sl14_rtt_swe_val;
  logic [32:0]                                   sl14_rtt_swe_data;
  logic [7:0]                                    sl14_rtt_swe_ext;
  `AXIASYNCWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,sl15nl1arc_dev_axi_gals_);
  `AXIASYNCWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,1,0,0,1,sl15nl1arc_ccm_axi_gals_);
  logic                                          sl15nl1arc_dbg_cmdval;
  logic [36:0]                                   sl15nl1arc_dbg_pack;
  logic [31:0]                                   sl15nl1arc_dbg_resp;
  // Trace
  logic                                          sl15_rtt_swe_val;
  logic [32:0]                                   sl15_rtt_swe_data;
  logic [7:0]                                    sl15_rtt_swe_ext;
  logic [`NPU_SLICE_NUM-1:0][1:0]                l1_to_l2_event;
  logic [`NPU_SLICE_NUM-1:0][1:0]                l2_to_l1_event;
  logic [`NPU_SLICE_NUM-1:0][`NPU_SLICE_NUM-1:0] l1_peer_event_out;
  logic [`NPU_SLICE_NUM-1:0][`NPU_SLICE_NUM-1:0] l1_peer_event_in;
  // L2 ARC0 debug interface
  logic                                          nl2arc0_dbg_cmdval;
  logic [36:0]                                   nl2arc0_dbg_pack;
  logic [31:0]                                   nl2arc0_dbg_resp;
  // L2 ARC1 debug interface
  logic                                          nl2arc1_dbg_cmdval;
  logic [36:0]                                   nl2arc1_dbg_pack;
  logic [31:0]                                   nl2arc1_dbg_resp;

  logic [7:0]                                    nl2arc0_arcnum;
  logic [7:0]                                    nl2arc1_arcnum;
  `APBASYNCWIRES(16,32,sl0nl1arc_dbg_);
  `APBWIRES(16,32,sl0nl1arc_dbg1_);
  logic [7:0]                                    sl0nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl1nl1arc_dbg_);
  `APBWIRES(16,32,sl1nl1arc_dbg1_);
  logic [7:0]                                    sl1nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl2nl1arc_dbg_);
  `APBWIRES(16,32,sl2nl1arc_dbg1_);
  logic [7:0]                                    sl2nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl3nl1arc_dbg_);
  `APBWIRES(16,32,sl3nl1arc_dbg1_);
  logic [7:0]                                    sl3nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl4nl1arc_dbg_);
  `APBWIRES(16,32,sl4nl1arc_dbg1_);
  logic [7:0]                                    sl4nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl5nl1arc_dbg_);
  `APBWIRES(16,32,sl5nl1arc_dbg1_);
  logic [7:0]                                    sl5nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl6nl1arc_dbg_);
  `APBWIRES(16,32,sl6nl1arc_dbg1_);
  logic [7:0]                                    sl6nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl7nl1arc_dbg_);
  `APBWIRES(16,32,sl7nl1arc_dbg1_);
  logic [7:0]                                    sl7nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl8nl1arc_dbg_);
  `APBWIRES(16,32,sl8nl1arc_dbg1_);
  logic [7:0]                                    sl8nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl9nl1arc_dbg_);
  `APBWIRES(16,32,sl9nl1arc_dbg1_);
  logic [7:0]                                    sl9nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl10nl1arc_dbg_);
  `APBWIRES(16,32,sl10nl1arc_dbg1_);
  logic [7:0]                                    sl10nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl11nl1arc_dbg_);
  `APBWIRES(16,32,sl11nl1arc_dbg1_);
  logic [7:0]                                    sl11nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl12nl1arc_dbg_);
  `APBWIRES(16,32,sl12nl1arc_dbg1_);
  logic [7:0]                                    sl12nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl13nl1arc_dbg_);
  `APBWIRES(16,32,sl13nl1arc_dbg1_);
  logic [7:0]                                    sl13nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl14nl1arc_dbg_);
  `APBWIRES(16,32,sl14nl1arc_dbg1_);
  logic [7:0]                                    sl14nl1arc_arcnum;
  `APBASYNCWIRES(16,32,sl15nl1arc_dbg_);
  `APBWIRES(16,32,sl15nl1arc_dbg1_);
  logic [7:0]                                    sl15nl1arc_arcnum;

  `APBASYNCWIRES(16,32,arct_syn_);
  // ARC_Trace
  logic                          grp4_rtt_swe_val;
  logic [32:0]                   grp4_rtt_swe_data;
  logic [7:0]                    grp4_rtt_swe_ext;
  logic                          grp4_rtt_swe_prdcr_en;
  logic                          grp5_rtt_swe_val;
  logic [32:0]                   grp5_rtt_swe_data;
  logic [7:0]                    grp5_rtt_swe_ext;
  logic                          grp5_rtt_swe_prdcr_en;
  logic                          grp6_rtt_swe_val;
  logic [32:0]                   grp6_rtt_swe_data;
  logic [7:0]                    grp6_rtt_swe_ext;
  logic                          grp6_rtt_swe_prdcr_en;
  logic                          grp7_rtt_swe_val;
  logic [32:0]                   grp7_rtt_swe_data;
  logic [7:0]                    grp7_rtt_swe_ext;
  logic                          grp7_rtt_swe_prdcr_en;
  logic                          grp8_rtt_swe_val;
  logic [32:0]                   grp8_rtt_swe_data;
  logic [7:0]                    grp8_rtt_swe_ext;
  logic                          grp8_rtt_swe_prdcr_en;
  logic                          grp9_rtt_swe_val;
  logic [32:0]                   grp9_rtt_swe_data;
  logic [7:0]                    grp9_rtt_swe_ext;
  logic                          grp9_rtt_swe_prdcr_en;
  logic                          grp10_rtt_swe_val;
  logic [32:0]                   grp10_rtt_swe_data;
  logic [7:0]                    grp10_rtt_swe_ext;
  logic                          grp10_rtt_swe_prdcr_en;
  logic                          grp11_rtt_swe_val;
  logic [32:0]                   grp11_rtt_swe_data;
  logic [7:0]                    grp11_rtt_swe_ext;
  logic                          grp11_rtt_swe_prdcr_en;
  logic                          grp12_rtt_swe_val;
  logic [32:0]                   grp12_rtt_swe_data;
  logic [7:0]                    grp12_rtt_swe_ext;
  logic                          grp12_rtt_swe_prdcr_en;
  logic                          grp13_rtt_swe_val;
  logic [32:0]                   grp13_rtt_swe_data;
  logic [7:0]                    grp13_rtt_swe_ext;
  logic                          grp13_rtt_swe_prdcr_en;
  logic                          grp14_rtt_swe_val;
  logic [32:0]                   grp14_rtt_swe_data;
  logic [7:0]                    grp14_rtt_swe_ext;
  logic                          grp14_rtt_swe_prdcr_en;
  logic                          grp15_rtt_swe_val;
  logic [32:0]                   grp15_rtt_swe_data;
  logic [7:0]                    grp15_rtt_swe_ext;
  logic                          grp15_rtt_swe_prdcr_en;
  logic                          grp16_rtt_swe_val;
  logic [32:0]                   grp16_rtt_swe_data;
  logic [7:0]                    grp16_rtt_swe_ext;
  logic                          grp16_rtt_swe_prdcr_en;



  `APBASYNCWIRES(16,32,sl0nl1arc_);
  `APBASYNCWIRES(16,32,sl1nl1arc_);
  `APBASYNCWIRES(16,32,sl2nl1arc_);
  `APBASYNCWIRES(16,32,sl3nl1arc_);
  `APBASYNCWIRES(16,32,sl4nl1arc_);
  `APBASYNCWIRES(16,32,sl5nl1arc_);
  `APBASYNCWIRES(16,32,sl6nl1arc_);
  `APBASYNCWIRES(16,32,sl7nl1arc_);
  `APBASYNCWIRES(16,32,sl8nl1arc_);
  `APBASYNCWIRES(16,32,sl9nl1arc_);
  `APBASYNCWIRES(16,32,sl10nl1arc_);
  `APBASYNCWIRES(16,32,sl11nl1arc_);
  `APBASYNCWIRES(16,32,sl12nl1arc_);
  `APBASYNCWIRES(16,32,sl13nl1arc_);
  `APBASYNCWIRES(16,32,sl14nl1arc_);
  `APBASYNCWIRES(16,32,sl15nl1arc_);
  `APBASYNCWIRES(16,32,nl2arc0_);
  `APBASYNCWIRES(16,32,nl2arc1_);
  `APBASYNCWIRES(16,32,arct0_syn_);


  // Per group config interface
    `AXISYNCWIRES(1,32,1,1,1,1,1,0,0,0,0,0,axi_cfg_grp0_sync_);
    `AXISYNCWIRES(1,32,1,1,1,1,1,0,0,0,0,0,axi_cfg_grp1_sync_);
    `AXISYNCWIRES(1,32,1,1,1,1,1,0,0,0,0,0,axi_cfg_grp2_sync_);
    `AXISYNCWIRES(1,32,1,1,1,1,1,0,0,0,0,0,axi_cfg_grp3_sync_);
  // L2ARC interfaces
  `AXISYNCWIRES(CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,0,0,0,0,axi_ccm0_sync_);
  `AXISYNCWIRES(L2IDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,0,1,0,0,1,axi_mst0_sync_);
  `AXISYNCWIRES(CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,0,0,0,0,axi_ccm1_sync_);
  `AXISYNCWIRES(L2IDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,0,1,0,0,1,axi_mst1_sync_);
  `AXISYNCWIRES(CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,0,0,0,0,axi_ccm2_sync_);
  `AXISYNCWIRES(L2IDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,0,1,0,0,1,axi_mst2_sync_);
  `AXISYNCWIRES(CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,0,0,0,0,0,axi_ccm3_sync_);
  `AXISYNCWIRES(L2IDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,0,1,0,0,1,axi_mst3_sync_);



  npu_core
  u_npu_core
  (
    // clock and reset
    .npu_core_clk                ( npu_core_clk              ),
    .nl2_rst_a                   ( nl2_rst_a                 ),
    .grp0_scm_dbank_sbe                     (  grp0_scm_dbank_sbe        ),
    .grp0_scm_dbank_dbe                     (  grp0_scm_dbank_dbe        ),
    .grp1_scm_dbank_sbe                     (  grp1_scm_dbank_sbe        ),
    .grp1_scm_dbank_dbe                     (  grp1_scm_dbank_dbe        ),
    .grp2_scm_dbank_sbe                     (  grp2_scm_dbank_sbe        ),
    .grp2_scm_dbank_dbe                     (  grp2_scm_dbank_dbe        ),
    .grp3_scm_dbank_sbe                     (  grp3_scm_dbank_sbe        ),
    .grp3_scm_dbank_dbe                     (  grp3_scm_dbank_dbe        ),
    .nl2arc0_ecc_sbe                      ( nl2arc0_ecc_sbe          ),
    .nl2arc0_ecc_dbe                      ( nl2arc0_ecc_dbe          ),
    .nl2arc1_ecc_sbe                      ( nl2arc1_ecc_sbe          ),
    .nl2arc1_ecc_dbe                      ( nl2arc1_ecc_dbe          ),
    // per group clock enable, power-down and reset (at main clock)
    .grp0_rst_a               ( grp0_rst_a             ),
    .grp0_clk_en_a            ( grp0_clk_en_a          ),
    .npu_grp0_vmid            ( npu_grp0_vmid          ),
    .grp1_rst_a               ( grp1_rst_a             ),
    .grp1_clk_en_a            ( grp1_clk_en_a          ),
    .npu_grp1_vmid            ( npu_grp1_vmid          ),
    .grp2_rst_a               ( grp2_rst_a             ),
    .grp2_clk_en_a            ( grp2_clk_en_a          ),
    .npu_grp2_vmid            ( npu_grp2_vmid          ),
    .grp3_rst_a               ( grp3_rst_a             ),
    .grp3_clk_en_a            ( grp3_clk_en_a          ),
    .npu_grp3_vmid            ( npu_grp3_vmid          ),
    .nl2arc0_rst_a              ( nl2arc0_rst_a            ),
    .nl2arc0_clk_en_a           ( nl2arc0_clk_en_a         ),
    .nl2arc0_evt_vm_irq         ( nl2arc0_evt_vm_irq       ),

    .nl2arc1_rst_a              ( nl2arc1_rst_a            ),
    .nl2arc1_clk_en_a           ( nl2arc1_clk_en_a         ),
    .nl2arc1_evt_vm_irq         ( nl2arc1_evt_vm_irq       ),
    .ext_irq0_a                      ( nl2arc_irq0_a            ),
    .ext_irq1_a                      ( nl2arc_irq1_a            ),

    .nl2arc_isolate        ( nl2arc_isolate      ),
    .nl2arc_isolate_n      ( nl2arc_isolate_n    ),
    .nl2arc_pd_mem         ( nl2arc_pd_mem       ),
    .nl2arc_pd_logic       ( nl2arc_pd_logic     ),
    .grp0_isolate             ( grp0_isolate           ),
    .grp0_isolate_n           ( grp0_isolate_n         ),
    .grp0_pd_mem              ( grp0_pd_mem            ),
    .grp0_pd_logic            ( grp0_pd_logic          ),
    .grp1_isolate             ( grp1_isolate           ),
    .grp1_isolate_n           ( grp1_isolate_n         ),
    .grp1_pd_mem              ( grp1_pd_mem            ),
    .grp1_pd_logic            ( grp1_pd_logic          ),
    .grp2_isolate             ( grp2_isolate           ),
    .grp2_isolate_n           ( grp2_isolate_n         ),
    .grp2_pd_mem              ( grp2_pd_mem            ),
    .grp2_pd_logic            ( grp2_pd_logic          ),
    .grp3_isolate             ( grp3_isolate           ),
    .grp3_isolate_n           ( grp3_isolate_n         ),
    .grp3_pd_mem              ( grp3_pd_mem            ),
    .grp3_pd_logic            ( grp3_pd_logic          ),
    // async AXI interfaces
    `AXIASYNCSINST(sl0nl1arc_dev_axi_gals_,sl0nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl0nl1arc_ccm_axi_gals_,sl0nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl1nl1arc_dev_axi_gals_,sl1nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl1nl1arc_ccm_axi_gals_,sl1nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl2nl1arc_dev_axi_gals_,sl2nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl2nl1arc_ccm_axi_gals_,sl2nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl3nl1arc_dev_axi_gals_,sl3nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl3nl1arc_ccm_axi_gals_,sl3nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl4nl1arc_dev_axi_gals_,sl4nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl4nl1arc_ccm_axi_gals_,sl4nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl5nl1arc_dev_axi_gals_,sl5nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl5nl1arc_ccm_axi_gals_,sl5nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl6nl1arc_dev_axi_gals_,sl6nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl6nl1arc_ccm_axi_gals_,sl6nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl7nl1arc_dev_axi_gals_,sl7nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl7nl1arc_ccm_axi_gals_,sl7nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl8nl1arc_dev_axi_gals_,sl8nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl8nl1arc_ccm_axi_gals_,sl8nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl9nl1arc_dev_axi_gals_,sl9nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl9nl1arc_ccm_axi_gals_,sl9nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl10nl1arc_dev_axi_gals_,sl10nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl10nl1arc_ccm_axi_gals_,sl10nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl11nl1arc_dev_axi_gals_,sl11nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl11nl1arc_ccm_axi_gals_,sl11nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl12nl1arc_dev_axi_gals_,sl12nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl12nl1arc_ccm_axi_gals_,sl12nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl13nl1arc_dev_axi_gals_,sl13nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl13nl1arc_ccm_axi_gals_,sl13nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl14nl1arc_dev_axi_gals_,sl14nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl14nl1arc_ccm_axi_gals_,sl14nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSINST(sl15nl1arc_dev_axi_gals_,sl15nl1arc_dev_axi_gals_),
    `AXIASYNCMINST(sl15nl1arc_ccm_axi_gals_,sl15nl1arc_ccm_axi_gals_),

    .l1_to_l2_event                  ( l1_to_l2_event            ),
    .l2_to_l1_event                  ( l2_to_l1_event            ),
    .npu_csm_base                    ( npu_csm_base              ),

    //ARC_Trace
    .at_clk_en                                 ( at_clk_en                     ),
    .at_rst_an                                 ( at_rst_an                     ),
    .atb_cstimestamp                           ( atb_cstimestamp               ),
    .atready                                   ( atready                       ),
    .atdata                                    ( atdata                        ),
    .atbytes                                   ( atbytes                       ),
    .atid                                      ( atid                          ),
    .atvalid                                   ( atvalid                       ),
    .afvalid                                   ( afvalid                       ),
    .afready                                   ( afready                       ),
    .syncreq                                   ( syncreq                       ),
    .swe_atready                               ( swe_atready                   ),
    .swe_atdata                                ( swe_atdata                    ),
    .swe_atbytes                               ( swe_atbytes                   ),
    .swe_atid                                  ( swe_atid                      ),
    .swe_atvalid                               ( swe_atvalid                   ),
    .swe_afvalid                               ( swe_afvalid                   ),
    .swe_afready                               ( swe_afready                   ),
    .swe_syncreq                               ( swe_syncreq                   ),
    .cti_rtt_filters                           ( cti_rtt_filters               ),
    .cti_trace_start                           ( cti_trace_start               ),
    .cti_trace_stop                            ( cti_trace_stop                ),

    .arct0_dbgen                               ( arct0_dbgen                   ),
    .arct0_niden                               ( arct0_niden                   ),
    .arct_dbg_prot_sel                         ( arct_dbg_prot_sel             ),
    .arct_rst_an                               ( arct_rst_an                   ),

    .nl2arc0_dbgen                        ( nl2arc0_dbgen            ),
    .nl2arc0_niden                        ( nl2arc0_niden            ),
    .nl2arc1_dbgen                        ( nl2arc1_dbgen            ),
    .nl2arc1_niden                        ( nl2arc1_niden            ),

    .sl0_rtt_swe_val                        ( sl0_rtt_swe_val            ),
    .sl0_rtt_swe_data                       ( sl0_rtt_swe_data           ),
    .sl0_rtt_swe_ext                        ( sl0_rtt_swe_ext            ),
    .sl1_rtt_swe_val                        ( sl1_rtt_swe_val            ),
    .sl1_rtt_swe_data                       ( sl1_rtt_swe_data           ),
    .sl1_rtt_swe_ext                        ( sl1_rtt_swe_ext            ),
    .sl2_rtt_swe_val                        ( sl2_rtt_swe_val            ),
    .sl2_rtt_swe_data                       ( sl2_rtt_swe_data           ),
    .sl2_rtt_swe_ext                        ( sl2_rtt_swe_ext            ),
    .sl3_rtt_swe_val                        ( sl3_rtt_swe_val            ),
    .sl3_rtt_swe_data                       ( sl3_rtt_swe_data           ),
    .sl3_rtt_swe_ext                        ( sl3_rtt_swe_ext            ),
    .sl4_rtt_swe_val                        ( sl4_rtt_swe_val            ),
    .sl4_rtt_swe_data                       ( sl4_rtt_swe_data           ),
    .sl4_rtt_swe_ext                        ( sl4_rtt_swe_ext            ),
    .sl5_rtt_swe_val                        ( sl5_rtt_swe_val            ),
    .sl5_rtt_swe_data                       ( sl5_rtt_swe_data           ),
    .sl5_rtt_swe_ext                        ( sl5_rtt_swe_ext            ),
    .sl6_rtt_swe_val                        ( sl6_rtt_swe_val            ),
    .sl6_rtt_swe_data                       ( sl6_rtt_swe_data           ),
    .sl6_rtt_swe_ext                        ( sl6_rtt_swe_ext            ),
    .sl7_rtt_swe_val                        ( sl7_rtt_swe_val            ),
    .sl7_rtt_swe_data                       ( sl7_rtt_swe_data           ),
    .sl7_rtt_swe_ext                        ( sl7_rtt_swe_ext            ),
    .sl8_rtt_swe_val                        ( sl8_rtt_swe_val            ),
    .sl8_rtt_swe_data                       ( sl8_rtt_swe_data           ),
    .sl8_rtt_swe_ext                        ( sl8_rtt_swe_ext            ),
    .sl9_rtt_swe_val                        ( sl9_rtt_swe_val            ),
    .sl9_rtt_swe_data                       ( sl9_rtt_swe_data           ),
    .sl9_rtt_swe_ext                        ( sl9_rtt_swe_ext            ),
    .sl10_rtt_swe_val                        ( sl10_rtt_swe_val            ),
    .sl10_rtt_swe_data                       ( sl10_rtt_swe_data           ),
    .sl10_rtt_swe_ext                        ( sl10_rtt_swe_ext            ),
    .sl11_rtt_swe_val                        ( sl11_rtt_swe_val            ),
    .sl11_rtt_swe_data                       ( sl11_rtt_swe_data           ),
    .sl11_rtt_swe_ext                        ( sl11_rtt_swe_ext            ),
    .sl12_rtt_swe_val                        ( sl12_rtt_swe_val            ),
    .sl12_rtt_swe_data                       ( sl12_rtt_swe_data           ),
    .sl12_rtt_swe_ext                        ( sl12_rtt_swe_ext            ),
    .sl13_rtt_swe_val                        ( sl13_rtt_swe_val            ),
    .sl13_rtt_swe_data                       ( sl13_rtt_swe_data           ),
    .sl13_rtt_swe_ext                        ( sl13_rtt_swe_ext            ),
    .sl14_rtt_swe_val                        ( sl14_rtt_swe_val            ),
    .sl14_rtt_swe_data                       ( sl14_rtt_swe_data           ),
    .sl14_rtt_swe_ext                        ( sl14_rtt_swe_ext            ),
    .sl15_rtt_swe_val                        ( sl15_rtt_swe_val            ),
    .sl15_rtt_swe_data                       ( sl15_rtt_swe_data           ),
    .sl15_rtt_swe_ext                        ( sl15_rtt_swe_ext            ),

    .nl2arc0_wdt_clk           ( nl2arc0_wdt_clk                   ),
    .nl2arc1_wdt_clk           ( nl2arc1_wdt_clk                   ),
    .nl2arc0_wdt_reset_error         ( nl2arc0_wdt_reset_error           ),
    .nl2arc0_wdt_reset_wdt_clk_error ( nl2arc0_wdt_reset_wdt_clk_error   ),
    .clusternum                           ( clusternum                    ),
    .nl2arc0_intvbase_in             ( nl2arc0_intvbase_in      ),
    .nl2arc0_arc_halt_req_a          ( nl2arc0_arc_halt_req_a   ),
    .nl2arc0_arc_halt_ack            ( nl2arc0_arc_halt_ack     ),
    .nl2arc0_arc_run_req_a           ( nl2arc0_arc_run_req_a    ),
    .nl2arc0_arc_run_ack             ( nl2arc0_arc_run_ack      ),
    .nl2arc0_sys_sleep_r             ( nl2arc0_sys_sleep_r      ),
    .nl2arc0_sys_sleep_mode_r        ( nl2arc0_sys_sleep_mode_r ),
    .nl2arc0_sys_halt_r              ( nl2arc0_sys_halt_r       ),
    .nl2arc0_sys_tf_halt_r           ( nl2arc0_sys_tf_halt_r    ),
    .nl2arc0_arc_irq_a               ( nl2arc0_arc_irq_a        ),
    .nl2arc0_arc_event_a             ( nl2arc0_arc_event_a      ),
    .nl2arc1_wdt_reset_error         ( nl2arc1_wdt_reset_error           ),
    .nl2arc1_wdt_reset_wdt_clk_error ( nl2arc1_wdt_reset_wdt_clk_error   ),
    .nl2arc1_intvbase_in             ( nl2arc1_intvbase_in      ),
    .nl2arc1_arc_halt_req_a          ( nl2arc1_arc_halt_req_a   ),
    .nl2arc1_arc_halt_ack            ( nl2arc1_arc_halt_ack     ),
    .nl2arc1_arc_run_req_a           ( nl2arc1_arc_run_req_a    ),
    .nl2arc1_arc_run_ack             ( nl2arc1_arc_run_ack      ),
    .nl2arc1_sys_sleep_r             ( nl2arc1_sys_sleep_r      ),
    .nl2arc1_sys_sleep_mode_r        ( nl2arc1_sys_sleep_mode_r ),
    .nl2arc1_sys_halt_r              ( nl2arc1_sys_halt_r       ),
    .nl2arc1_sys_tf_halt_r           ( nl2arc1_sys_tf_halt_r    ),
    .nl2arc1_arc_irq_a               ( nl2arc1_arc_irq_a        ),
    .nl2arc1_arc_event_a             ( nl2arc1_arc_event_a      ),


      .npu_core_rst_a                  ( npu_core_rst_a              )
    , `APBASYNCINST(sl0nl1arc_dbg_,sl0nl1arc_dbg_)
    , `APBASYNCINST(sl1nl1arc_dbg_,sl1nl1arc_dbg_)
    , `APBASYNCINST(sl2nl1arc_dbg_,sl2nl1arc_dbg_)
    , `APBASYNCINST(sl3nl1arc_dbg_,sl3nl1arc_dbg_)
    , `APBASYNCINST(sl4nl1arc_dbg_,sl4nl1arc_dbg_)
    , `APBASYNCINST(sl5nl1arc_dbg_,sl5nl1arc_dbg_)
    , `APBASYNCINST(sl6nl1arc_dbg_,sl6nl1arc_dbg_)
    , `APBASYNCINST(sl7nl1arc_dbg_,sl7nl1arc_dbg_)
    , `APBASYNCINST(sl8nl1arc_dbg_,sl8nl1arc_dbg_)
    , `APBASYNCINST(sl9nl1arc_dbg_,sl9nl1arc_dbg_)
    , `APBASYNCINST(sl10nl1arc_dbg_,sl10nl1arc_dbg_)
    , `APBASYNCINST(sl11nl1arc_dbg_,sl11nl1arc_dbg_)
    , `APBASYNCINST(sl12nl1arc_dbg_,sl12nl1arc_dbg_)
    , `APBASYNCINST(sl13nl1arc_dbg_,sl13nl1arc_dbg_)
    , `APBASYNCINST(sl14nl1arc_dbg_,sl14nl1arc_dbg_)
    , `APBASYNCINST(sl15nl1arc_dbg_,sl15nl1arc_dbg_)
    ,.arct_clk                         ( arct_clk                    )
    ,`APBINST(arct_,arct_)
    , .sl0nl1arc_arcnum           ( sl0nl1arc_arcnum       )
    , .sl0nl1arc_evt_vm_irq_a     ( sl0nl1arc_evt_vm_irq   )
    , .sl0nl1arc_pwr_dwn_a        ( sl0nl1arc_pwr_dwn_a    )
    , .sl1nl1arc_arcnum           ( sl1nl1arc_arcnum       )
    , .sl1nl1arc_evt_vm_irq_a     ( sl1nl1arc_evt_vm_irq   )
    , .sl1nl1arc_pwr_dwn_a        ( sl1nl1arc_pwr_dwn_a    )
    , .sl2nl1arc_arcnum           ( sl2nl1arc_arcnum       )
    , .sl2nl1arc_evt_vm_irq_a     ( sl2nl1arc_evt_vm_irq   )
    , .sl2nl1arc_pwr_dwn_a        ( sl2nl1arc_pwr_dwn_a    )
    , .sl3nl1arc_arcnum           ( sl3nl1arc_arcnum       )
    , .sl3nl1arc_evt_vm_irq_a     ( sl3nl1arc_evt_vm_irq   )
    , .sl3nl1arc_pwr_dwn_a        ( sl3nl1arc_pwr_dwn_a    )
    , .sl4nl1arc_arcnum           ( sl4nl1arc_arcnum       )
    , .sl4nl1arc_evt_vm_irq_a     ( sl4nl1arc_evt_vm_irq   )
    , .sl4nl1arc_pwr_dwn_a        ( sl4nl1arc_pwr_dwn_a    )
    , .sl5nl1arc_arcnum           ( sl5nl1arc_arcnum       )
    , .sl5nl1arc_evt_vm_irq_a     ( sl5nl1arc_evt_vm_irq   )
    , .sl5nl1arc_pwr_dwn_a        ( sl5nl1arc_pwr_dwn_a    )
    , .sl6nl1arc_arcnum           ( sl6nl1arc_arcnum       )
    , .sl6nl1arc_evt_vm_irq_a     ( sl6nl1arc_evt_vm_irq   )
    , .sl6nl1arc_pwr_dwn_a        ( sl6nl1arc_pwr_dwn_a    )
    , .sl7nl1arc_arcnum           ( sl7nl1arc_arcnum       )
    , .sl7nl1arc_evt_vm_irq_a     ( sl7nl1arc_evt_vm_irq   )
    , .sl7nl1arc_pwr_dwn_a        ( sl7nl1arc_pwr_dwn_a    )
    , .sl8nl1arc_arcnum           ( sl8nl1arc_arcnum       )
    , .sl8nl1arc_evt_vm_irq_a     ( sl8nl1arc_evt_vm_irq   )
    , .sl8nl1arc_pwr_dwn_a        ( sl8nl1arc_pwr_dwn_a    )
    , .sl9nl1arc_arcnum           ( sl9nl1arc_arcnum       )
    , .sl9nl1arc_evt_vm_irq_a     ( sl9nl1arc_evt_vm_irq   )
    , .sl9nl1arc_pwr_dwn_a        ( sl9nl1arc_pwr_dwn_a    )
    , .sl10nl1arc_arcnum           ( sl10nl1arc_arcnum       )
    , .sl10nl1arc_evt_vm_irq_a     ( sl10nl1arc_evt_vm_irq   )
    , .sl10nl1arc_pwr_dwn_a        ( sl10nl1arc_pwr_dwn_a    )
    , .sl11nl1arc_arcnum           ( sl11nl1arc_arcnum       )
    , .sl11nl1arc_evt_vm_irq_a     ( sl11nl1arc_evt_vm_irq   )
    , .sl11nl1arc_pwr_dwn_a        ( sl11nl1arc_pwr_dwn_a    )
    , .sl12nl1arc_arcnum           ( sl12nl1arc_arcnum       )
    , .sl12nl1arc_evt_vm_irq_a     ( sl12nl1arc_evt_vm_irq   )
    , .sl12nl1arc_pwr_dwn_a        ( sl12nl1arc_pwr_dwn_a    )
    , .sl13nl1arc_arcnum           ( sl13nl1arc_arcnum       )
    , .sl13nl1arc_evt_vm_irq_a     ( sl13nl1arc_evt_vm_irq   )
    , .sl13nl1arc_pwr_dwn_a        ( sl13nl1arc_pwr_dwn_a    )
    , .sl14nl1arc_arcnum           ( sl14nl1arc_arcnum       )
    , .sl14nl1arc_evt_vm_irq_a     ( sl14nl1arc_evt_vm_irq   )
    , .sl14nl1arc_pwr_dwn_a        ( sl14nl1arc_pwr_dwn_a    )
    , .sl15nl1arc_arcnum           ( sl15nl1arc_arcnum       )
    , .sl15nl1arc_evt_vm_irq_a     ( sl15nl1arc_evt_vm_irq   )
    , .sl15nl1arc_pwr_dwn_a        ( sl15nl1arc_pwr_dwn_a    )
    , .grp0_pwr_dwn_a               ( grp0_pwr_dwn_a           )
    , .grp1_pwr_dwn_a               ( grp1_pwr_dwn_a           )
    , .grp2_pwr_dwn_a               ( grp2_pwr_dwn_a           )
    , .grp3_pwr_dwn_a               ( grp3_pwr_dwn_a           )
    , .nl2arc_pwr_dwn_a           ( nl2arc_pwr_dwn_a       )
    , .nl2arc0_pwr_dwn_a          ( nl2arc0_pwr_dwn_a      )
    , .nl2arc1_pwr_dwn_a          ( nl2arc1_pwr_dwn_a      )
    // ARC_Trace
    , .l1_peer_event_out               ( l1_peer_event_out           )
    , .l1_peer_event_in                ( l1_peer_event_in            )
    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst16_axi
    // read command channel
  , .npu_mst0_axi_arvalid            (npu_mst0_axi_arvalid)     // read command valid
  , .npu_mst0_axi_arready            (npu_mst0_axi_arready)     // read command accept
  , .npu_mst0_axi_arid               (npu_mst0_axi_arid   )     // read command ID
  , .npu_mst0_axi_araddr  (npu_mst0_axi_araddr  )   // read command
  , .npu_mst0_axi_arcache (npu_mst0_axi_arcache )   // read command
  , .npu_mst0_axi_arprot  (npu_mst0_axi_arprot  )   // read command
  , .npu_mst0_axi_arlock  (npu_mst0_axi_arlock  )   // read command
  , .npu_mst0_axi_arburst (npu_mst0_axi_arburst )   // read command
  , .npu_mst0_axi_arlen   (npu_mst0_axi_arlen   )   // read command
  , .npu_mst0_axi_arsize  (npu_mst0_axi_arsize  )   // read command
  , .npu_mst0_axi_rvalid  (npu_mst0_axi_rvalid )    // read data valid
  , .npu_mst0_axi_rready  (npu_mst0_axi_rready )    // read data accept
  , .npu_mst0_axi_rid     (npu_mst0_axi_rid    )    // read data id
  , .npu_mst0_axi_rdata   (npu_mst0_axi_rdata  )    // read data
  , .npu_mst0_axi_rresp   (npu_mst0_axi_rresp)    // read response
  , .npu_mst0_axi_rlast   (npu_mst0_axi_rlast  )    // read last
  , .npu_mst0_axi_awvalid (npu_mst0_axi_awvalid )   // write command valid
  , .npu_mst0_axi_awready (npu_mst0_axi_awready )   // write command accept
  , .npu_mst0_axi_awid    (npu_mst0_axi_awid    )   // write command ID
  , .npu_mst0_axi_awaddr  (npu_mst0_axi_awaddr  )   // read command
  , .npu_mst0_axi_awcache (npu_mst0_axi_awcache )   // read command
  , .npu_mst0_axi_awprot  (npu_mst0_axi_awprot  )   // read command
  , .npu_mst0_axi_awlock  (npu_mst0_axi_awlock  )   // read command
  , .npu_mst0_axi_awburst (npu_mst0_axi_awburst )   // read command
  , .npu_mst0_axi_awlen   (npu_mst0_axi_awlen   )   // read command
  , .npu_mst0_axi_awsize  (npu_mst0_axi_awsize  )   // read command
  , .npu_mst0_axi_wvalid  (npu_mst0_axi_wvalid  )   // write data valid
  , .npu_mst0_axi_wready  (npu_mst0_axi_wready  )   // write data accept
  , .npu_mst0_axi_wdata   (npu_mst0_axi_wdata   )   // write data
  , .npu_mst0_axi_wstrb   (npu_mst0_axi_wstrb   )   // write data strobe
  , .npu_mst0_axi_wlast   (npu_mst0_axi_wlast   )   // write data last
  , .npu_mst0_axi_bvalid  (npu_mst0_axi_bvalid  )   // write response valid
  , .npu_mst0_axi_bready  (npu_mst0_axi_bready  )   // write response accept
  , .npu_mst0_axi_bid     (npu_mst0_axi_bid     )   // write response id
  , .npu_mst0_axi_bresp   (npu_mst0_axi_bresp)    // read response
    //-slave dmi, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-npu_dmi0_axi
    //axislv(1/*idw*/,`aw,`ISIZE*32/*dw*/,1/*argw*/,1/*awgw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/,0/*awcpl*/, npu_dmi0_axi_/*prefix*/)
    // read command channel
  , .npu_dmi0_axi_arvalid            (npu_dmi0_axi_arvalid)     // read command valid
  , .npu_dmi0_axi_arready            (npu_dmi0_axi_arready)     // read command accept
  , .npu_dmi0_axi_arid               (npu_dmi0_axi_arid   )     // read command ID
  , .npu_dmi0_axi_araddr  (npu_dmi0_axi_araddr  )   // read command
  , .npu_dmi0_axi_arcache (npu_dmi0_axi_arcache )   // read command
  , .npu_dmi0_axi_arprot  (npu_dmi0_axi_arprot  )   // read command
  , .npu_dmi0_axi_arlock  (npu_dmi0_axi_arlock  )   // read command
  , .npu_dmi0_axi_arburst (npu_dmi0_axi_arburst )   // read command
  , .npu_dmi0_axi_arlen   (npu_dmi0_axi_arlen   )   // read command
  , .npu_dmi0_axi_arsize  (npu_dmi0_axi_arsize  )   // read command
  , .npu_dmi0_axi_rvalid  (npu_dmi0_axi_rvalid )    // read data valid
  , .npu_dmi0_axi_rready  (npu_dmi0_axi_rready )    // read data accept
  , .npu_dmi0_axi_rid     (npu_dmi0_axi_rid    )    // read data id
  , .npu_dmi0_axi_rdata   (npu_dmi0_axi_rdata  )    // read data
  , .npu_dmi0_axi_rresp   (npu_dmi0_axi_rresp)    // read response
  , .npu_dmi0_axi_rlast   (npu_dmi0_axi_rlast  )    // read last
  , .npu_dmi0_axi_awvalid (npu_dmi0_axi_awvalid )   // write command valid
  , .npu_dmi0_axi_awready (npu_dmi0_axi_awready )   // write command accept
  , .npu_dmi0_axi_awid    (npu_dmi0_axi_awid    )   // write command ID
  , .npu_dmi0_axi_awaddr  (npu_dmi0_axi_awaddr  )   // read command
  , .npu_dmi0_axi_awcache (npu_dmi0_axi_awcache )   // read command
  , .npu_dmi0_axi_awprot  (npu_dmi0_axi_awprot  )   // read command
  , .npu_dmi0_axi_awlock  (npu_dmi0_axi_awlock  )   // read command
  , .npu_dmi0_axi_awburst (npu_dmi0_axi_awburst )   // read command
  , .npu_dmi0_axi_awlen   (npu_dmi0_axi_awlen   )   // read command
  , .npu_dmi0_axi_awsize  (npu_dmi0_axi_awsize  )   // read command
  , .npu_dmi0_axi_wvalid  (npu_dmi0_axi_wvalid  )   // write data valid
  , .npu_dmi0_axi_wready  (npu_dmi0_axi_wready  )   // write data accept
  , .npu_dmi0_axi_wdata   (npu_dmi0_axi_wdata   )   // write data
  , .npu_dmi0_axi_wstrb   (npu_dmi0_axi_wstrb   )   // write data strobe
  , .npu_dmi0_axi_wlast   (npu_dmi0_axi_wlast   )   // write data last
  , .npu_dmi0_axi_bvalid  (npu_dmi0_axi_bvalid  )   // write response valid
  , .npu_dmi0_axi_bready  (npu_dmi0_axi_bready  )   // write response accept
  , .npu_dmi0_axi_bid     (npu_dmi0_axi_bid     )   // write response id
  , .npu_dmi0_axi_bresp   (npu_dmi0_axi_bresp)    // read response
    // Async bridge && reset ctrl
    , .npu_noc_clk                     ( npu_noc_clk                 )
    , .npu_noc_rst_a                   ( npu_noc_rst_a               )
    , .npu_cfg_clk                     ( npu_cfg_clk                 )
    , .npu_cfg_rst_a                   ( npu_cfg_rst_a               )
    , .sl0nl1arc_dbg_cmdval     ( sl0nl1arc_dbg_cmdval   )
    , .sl0nl1arc_dbg_pack       ( sl0nl1arc_dbg_pack     )
    , .sl0nl1arc_dbg_resp       ( sl0nl1arc_dbg_resp     )
    , .sl1nl1arc_dbg_cmdval     ( sl1nl1arc_dbg_cmdval   )
    , .sl1nl1arc_dbg_pack       ( sl1nl1arc_dbg_pack     )
    , .sl1nl1arc_dbg_resp       ( sl1nl1arc_dbg_resp     )
    , .sl2nl1arc_dbg_cmdval     ( sl2nl1arc_dbg_cmdval   )
    , .sl2nl1arc_dbg_pack       ( sl2nl1arc_dbg_pack     )
    , .sl2nl1arc_dbg_resp       ( sl2nl1arc_dbg_resp     )
    , .sl3nl1arc_dbg_cmdval     ( sl3nl1arc_dbg_cmdval   )
    , .sl3nl1arc_dbg_pack       ( sl3nl1arc_dbg_pack     )
    , .sl3nl1arc_dbg_resp       ( sl3nl1arc_dbg_resp     )
    , .sl4nl1arc_dbg_cmdval     ( sl4nl1arc_dbg_cmdval   )
    , .sl4nl1arc_dbg_pack       ( sl4nl1arc_dbg_pack     )
    , .sl4nl1arc_dbg_resp       ( sl4nl1arc_dbg_resp     )
    , .sl5nl1arc_dbg_cmdval     ( sl5nl1arc_dbg_cmdval   )
    , .sl5nl1arc_dbg_pack       ( sl5nl1arc_dbg_pack     )
    , .sl5nl1arc_dbg_resp       ( sl5nl1arc_dbg_resp     )
    , .sl6nl1arc_dbg_cmdval     ( sl6nl1arc_dbg_cmdval   )
    , .sl6nl1arc_dbg_pack       ( sl6nl1arc_dbg_pack     )
    , .sl6nl1arc_dbg_resp       ( sl6nl1arc_dbg_resp     )
    , .sl7nl1arc_dbg_cmdval     ( sl7nl1arc_dbg_cmdval   )
    , .sl7nl1arc_dbg_pack       ( sl7nl1arc_dbg_pack     )
    , .sl7nl1arc_dbg_resp       ( sl7nl1arc_dbg_resp     )
    , .sl8nl1arc_dbg_cmdval     ( sl8nl1arc_dbg_cmdval   )
    , .sl8nl1arc_dbg_pack       ( sl8nl1arc_dbg_pack     )
    , .sl8nl1arc_dbg_resp       ( sl8nl1arc_dbg_resp     )
    , .sl9nl1arc_dbg_cmdval     ( sl9nl1arc_dbg_cmdval   )
    , .sl9nl1arc_dbg_pack       ( sl9nl1arc_dbg_pack     )
    , .sl9nl1arc_dbg_resp       ( sl9nl1arc_dbg_resp     )
    , .sl10nl1arc_dbg_cmdval     ( sl10nl1arc_dbg_cmdval   )
    , .sl10nl1arc_dbg_pack       ( sl10nl1arc_dbg_pack     )
    , .sl10nl1arc_dbg_resp       ( sl10nl1arc_dbg_resp     )
    , .sl11nl1arc_dbg_cmdval     ( sl11nl1arc_dbg_cmdval   )
    , .sl11nl1arc_dbg_pack       ( sl11nl1arc_dbg_pack     )
    , .sl11nl1arc_dbg_resp       ( sl11nl1arc_dbg_resp     )
    , .sl12nl1arc_dbg_cmdval     ( sl12nl1arc_dbg_cmdval   )
    , .sl12nl1arc_dbg_pack       ( sl12nl1arc_dbg_pack     )
    , .sl12nl1arc_dbg_resp       ( sl12nl1arc_dbg_resp     )
    , .sl13nl1arc_dbg_cmdval     ( sl13nl1arc_dbg_cmdval   )
    , .sl13nl1arc_dbg_pack       ( sl13nl1arc_dbg_pack     )
    , .sl13nl1arc_dbg_resp       ( sl13nl1arc_dbg_resp     )
    , .sl14nl1arc_dbg_cmdval     ( sl14nl1arc_dbg_cmdval   )
    , .sl14nl1arc_dbg_pack       ( sl14nl1arc_dbg_pack     )
    , .sl14nl1arc_dbg_resp       ( sl14nl1arc_dbg_resp     )
    , .sl15nl1arc_dbg_cmdval     ( sl15nl1arc_dbg_cmdval   )
    , .sl15nl1arc_dbg_pack       ( sl15nl1arc_dbg_pack     )
    , .sl15nl1arc_dbg_resp       ( sl15nl1arc_dbg_resp     )
    // configuration slave AXI
    //axislv(1/*idw*/,`aw,`ISIZE*32/*dw*/,1/*argw*/,1/*awgw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/,0/*awcpl*/, npu_cfg_axi_/*prefix*/)
    // read command channel
  , .npu_cfg_axi_arvalid            (npu_cfg_axi_arvalid)     // read command valid
  , .npu_cfg_axi_arready            (npu_cfg_axi_arready)     // read command accept
  , .npu_cfg_axi_arid               (npu_cfg_axi_arid   )     // read command ID
  , .npu_cfg_axi_araddr  (npu_cfg_axi_araddr  )   // read command
  , .npu_cfg_axi_arcache (npu_cfg_axi_arcache )   // read command
  , .npu_cfg_axi_arprot  (npu_cfg_axi_arprot  )   // read command
  , .npu_cfg_axi_arlock  (npu_cfg_axi_arlock  )   // read command
  , .npu_cfg_axi_arburst (npu_cfg_axi_arburst )   // read command
  , .npu_cfg_axi_arlen   (npu_cfg_axi_arlen   )   // read command
  , .npu_cfg_axi_arsize  (npu_cfg_axi_arsize  )   // read command
  , .npu_cfg_axi_rvalid  (npu_cfg_axi_rvalid )    // read data valid
  , .npu_cfg_axi_rready  (npu_cfg_axi_rready )    // read data accept
  , .npu_cfg_axi_rid     (npu_cfg_axi_rid    )    // read data id
  , .npu_cfg_axi_rdata   (npu_cfg_axi_rdata  )    // read data
  , .npu_cfg_axi_rresp   (npu_cfg_axi_rresp)    // read response
  , .npu_cfg_axi_rlast   (npu_cfg_axi_rlast  )    // read last
  , .npu_cfg_axi_awvalid (npu_cfg_axi_awvalid )   // write command valid
  , .npu_cfg_axi_awready (npu_cfg_axi_awready )   // write command accept
  , .npu_cfg_axi_awid    (npu_cfg_axi_awid    )   // write command ID
  , .npu_cfg_axi_awaddr  (npu_cfg_axi_awaddr  )   // read command
  , .npu_cfg_axi_awcache (npu_cfg_axi_awcache )   // read command
  , .npu_cfg_axi_awprot  (npu_cfg_axi_awprot  )   // read command
  , .npu_cfg_axi_awlock  (npu_cfg_axi_awlock  )   // read command
  , .npu_cfg_axi_awburst (npu_cfg_axi_awburst )   // read command
  , .npu_cfg_axi_awlen   (npu_cfg_axi_awlen   )   // read command
  , .npu_cfg_axi_awsize  (npu_cfg_axi_awsize  )   // read command
  , .npu_cfg_axi_wvalid  (npu_cfg_axi_wvalid  )   // write data valid
  , .npu_cfg_axi_wready  (npu_cfg_axi_wready  )   // write data accept
  , .npu_cfg_axi_wdata   (npu_cfg_axi_wdata   )   // write data
  , .npu_cfg_axi_wstrb   (npu_cfg_axi_wstrb   )   // write data strobe
  , .npu_cfg_axi_wlast   (npu_cfg_axi_wlast   )   // write data last
  , .npu_cfg_axi_bvalid  (npu_cfg_axi_bvalid  )   // write response valid
  , .npu_cfg_axi_bready  (npu_cfg_axi_bready  )   // write response accept
  , .npu_cfg_axi_bid     (npu_cfg_axi_bid     )   // write response id
  , .npu_cfg_axi_bresp   (npu_cfg_axi_bresp)    // read response
    ,  .test_mode                      ( test_mode                 )

    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst1_axi_arvalid            (npu_mst1_axi_arvalid)     // read command valid
  , .npu_mst1_axi_arready            (npu_mst1_axi_arready)     // read command accept
  , .npu_mst1_axi_arid               (npu_mst1_axi_arid   )     // read command ID
  , .npu_mst1_axi_araddr  (npu_mst1_axi_araddr  )   // read command
  , .npu_mst1_axi_arcache (npu_mst1_axi_arcache )   // read command
  , .npu_mst1_axi_arprot  (npu_mst1_axi_arprot  )   // read command
  , .npu_mst1_axi_arlock  (npu_mst1_axi_arlock  )   // read command
  , .npu_mst1_axi_arburst (npu_mst1_axi_arburst )   // read command
  , .npu_mst1_axi_arlen   (npu_mst1_axi_arlen   )   // read command
  , .npu_mst1_axi_arsize  (npu_mst1_axi_arsize  )   // read command
  , .npu_mst1_axi_arsid(npu_mst1_axi_arsid)   // read command
  , .npu_mst1_axi_arssid(npu_mst1_axi_arssid)   // read command
  , .npu_mst1_axi_rvalid  (npu_mst1_axi_rvalid )    // read data valid
  , .npu_mst1_axi_rready  (npu_mst1_axi_rready )    // read data accept
  , .npu_mst1_axi_rid     (npu_mst1_axi_rid    )    // read data id
  , .npu_mst1_axi_rdata   (npu_mst1_axi_rdata  )    // read data
  , .npu_mst1_axi_rresp   (npu_mst1_axi_rresp)    // read response
  , .npu_mst1_axi_rlast   (npu_mst1_axi_rlast  )    // read last
  , .npu_mst1_axi_awvalid (npu_mst1_axi_awvalid )   // write command valid
  , .npu_mst1_axi_awready (npu_mst1_axi_awready )   // write command accept
  , .npu_mst1_axi_awid    (npu_mst1_axi_awid    )   // write command ID
  , .npu_mst1_axi_awaddr  (npu_mst1_axi_awaddr  )   // read command
  , .npu_mst1_axi_awcache (npu_mst1_axi_awcache )   // read command
  , .npu_mst1_axi_awprot  (npu_mst1_axi_awprot  )   // read command
  , .npu_mst1_axi_awlock  (npu_mst1_axi_awlock  )   // read command
  , .npu_mst1_axi_awburst (npu_mst1_axi_awburst )   // read command
  , .npu_mst1_axi_awlen   (npu_mst1_axi_awlen   )   // read command
  , .npu_mst1_axi_awsize  (npu_mst1_axi_awsize  )   // read command
  , .npu_mst1_axi_awsid(npu_mst1_axi_awsid)     // read command
  , .npu_mst1_axi_awssid(npu_mst1_axi_awssid)   // read command
  , .npu_mst1_axi_wvalid  (npu_mst1_axi_wvalid  )   // write data valid
  , .npu_mst1_axi_wready  (npu_mst1_axi_wready  )   // write data accept
  , .npu_mst1_axi_wdata   (npu_mst1_axi_wdata   )   // write data
  , .npu_mst1_axi_wstrb   (npu_mst1_axi_wstrb   )   // write data strobe
  , .npu_mst1_axi_wlast   (npu_mst1_axi_wlast   )   // write data last
  , .npu_mst1_axi_bvalid  (npu_mst1_axi_bvalid  )   // write response valid
  , .npu_mst1_axi_bready  (npu_mst1_axi_bready  )   // write response accept
  , .npu_mst1_axi_bid     (npu_mst1_axi_bid     )   // write response id
  , .npu_mst1_axi_bresp   (npu_mst1_axi_bresp)    // read response
    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst2_axi_arvalid            (npu_mst2_axi_arvalid)     // read command valid
  , .npu_mst2_axi_arready            (npu_mst2_axi_arready)     // read command accept
  , .npu_mst2_axi_arid               (npu_mst2_axi_arid   )     // read command ID
  , .npu_mst2_axi_araddr  (npu_mst2_axi_araddr  )   // read command
  , .npu_mst2_axi_arcache (npu_mst2_axi_arcache )   // read command
  , .npu_mst2_axi_arprot  (npu_mst2_axi_arprot  )   // read command
  , .npu_mst2_axi_arlock  (npu_mst2_axi_arlock  )   // read command
  , .npu_mst2_axi_arburst (npu_mst2_axi_arburst )   // read command
  , .npu_mst2_axi_arlen   (npu_mst2_axi_arlen   )   // read command
  , .npu_mst2_axi_arsize  (npu_mst2_axi_arsize  )   // read command
  , .npu_mst2_axi_arsid(npu_mst2_axi_arsid)   // read command
  , .npu_mst2_axi_arssid(npu_mst2_axi_arssid)   // read command
  , .npu_mst2_axi_rvalid  (npu_mst2_axi_rvalid )    // read data valid
  , .npu_mst2_axi_rready  (npu_mst2_axi_rready )    // read data accept
  , .npu_mst2_axi_rid     (npu_mst2_axi_rid    )    // read data id
  , .npu_mst2_axi_rdata   (npu_mst2_axi_rdata  )    // read data
  , .npu_mst2_axi_rresp   (npu_mst2_axi_rresp)    // read response
  , .npu_mst2_axi_rlast   (npu_mst2_axi_rlast  )    // read last
  , .npu_mst2_axi_awvalid (npu_mst2_axi_awvalid )   // write command valid
  , .npu_mst2_axi_awready (npu_mst2_axi_awready )   // write command accept
  , .npu_mst2_axi_awid    (npu_mst2_axi_awid    )   // write command ID
  , .npu_mst2_axi_awaddr  (npu_mst2_axi_awaddr  )   // read command
  , .npu_mst2_axi_awcache (npu_mst2_axi_awcache )   // read command
  , .npu_mst2_axi_awprot  (npu_mst2_axi_awprot  )   // read command
  , .npu_mst2_axi_awlock  (npu_mst2_axi_awlock  )   // read command
  , .npu_mst2_axi_awburst (npu_mst2_axi_awburst )   // read command
  , .npu_mst2_axi_awlen   (npu_mst2_axi_awlen   )   // read command
  , .npu_mst2_axi_awsize  (npu_mst2_axi_awsize  )   // read command
  , .npu_mst2_axi_awsid(npu_mst2_axi_awsid)     // read command
  , .npu_mst2_axi_awssid(npu_mst2_axi_awssid)   // read command
  , .npu_mst2_axi_wvalid  (npu_mst2_axi_wvalid  )   // write data valid
  , .npu_mst2_axi_wready  (npu_mst2_axi_wready  )   // write data accept
  , .npu_mst2_axi_wdata   (npu_mst2_axi_wdata   )   // write data
  , .npu_mst2_axi_wstrb   (npu_mst2_axi_wstrb   )   // write data strobe
  , .npu_mst2_axi_wlast   (npu_mst2_axi_wlast   )   // write data last
  , .npu_mst2_axi_bvalid  (npu_mst2_axi_bvalid  )   // write response valid
  , .npu_mst2_axi_bready  (npu_mst2_axi_bready  )   // write response accept
  , .npu_mst2_axi_bid     (npu_mst2_axi_bid     )   // write response id
  , .npu_mst2_axi_bresp   (npu_mst2_axi_bresp)    // read response
    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst3_axi_arvalid            (npu_mst3_axi_arvalid)     // read command valid
  , .npu_mst3_axi_arready            (npu_mst3_axi_arready)     // read command accept
  , .npu_mst3_axi_arid               (npu_mst3_axi_arid   )     // read command ID
  , .npu_mst3_axi_araddr  (npu_mst3_axi_araddr  )   // read command
  , .npu_mst3_axi_arcache (npu_mst3_axi_arcache )   // read command
  , .npu_mst3_axi_arprot  (npu_mst3_axi_arprot  )   // read command
  , .npu_mst3_axi_arlock  (npu_mst3_axi_arlock  )   // read command
  , .npu_mst3_axi_arburst (npu_mst3_axi_arburst )   // read command
  , .npu_mst3_axi_arlen   (npu_mst3_axi_arlen   )   // read command
  , .npu_mst3_axi_arsize  (npu_mst3_axi_arsize  )   // read command
  , .npu_mst3_axi_arsid(npu_mst3_axi_arsid)   // read command
  , .npu_mst3_axi_arssid(npu_mst3_axi_arssid)   // read command
  , .npu_mst3_axi_rvalid  (npu_mst3_axi_rvalid )    // read data valid
  , .npu_mst3_axi_rready  (npu_mst3_axi_rready )    // read data accept
  , .npu_mst3_axi_rid     (npu_mst3_axi_rid    )    // read data id
  , .npu_mst3_axi_rdata   (npu_mst3_axi_rdata  )    // read data
  , .npu_mst3_axi_rresp   (npu_mst3_axi_rresp)    // read response
  , .npu_mst3_axi_rlast   (npu_mst3_axi_rlast  )    // read last
  , .npu_mst3_axi_awvalid (npu_mst3_axi_awvalid )   // write command valid
  , .npu_mst3_axi_awready (npu_mst3_axi_awready )   // write command accept
  , .npu_mst3_axi_awid    (npu_mst3_axi_awid    )   // write command ID
  , .npu_mst3_axi_awaddr  (npu_mst3_axi_awaddr  )   // read command
  , .npu_mst3_axi_awcache (npu_mst3_axi_awcache )   // read command
  , .npu_mst3_axi_awprot  (npu_mst3_axi_awprot  )   // read command
  , .npu_mst3_axi_awlock  (npu_mst3_axi_awlock  )   // read command
  , .npu_mst3_axi_awburst (npu_mst3_axi_awburst )   // read command
  , .npu_mst3_axi_awlen   (npu_mst3_axi_awlen   )   // read command
  , .npu_mst3_axi_awsize  (npu_mst3_axi_awsize  )   // read command
  , .npu_mst3_axi_awsid(npu_mst3_axi_awsid)     // read command
  , .npu_mst3_axi_awssid(npu_mst3_axi_awssid)   // read command
  , .npu_mst3_axi_wvalid  (npu_mst3_axi_wvalid  )   // write data valid
  , .npu_mst3_axi_wready  (npu_mst3_axi_wready  )   // write data accept
  , .npu_mst3_axi_wdata   (npu_mst3_axi_wdata   )   // write data
  , .npu_mst3_axi_wstrb   (npu_mst3_axi_wstrb   )   // write data strobe
  , .npu_mst3_axi_wlast   (npu_mst3_axi_wlast   )   // write data last
  , .npu_mst3_axi_bvalid  (npu_mst3_axi_bvalid  )   // write response valid
  , .npu_mst3_axi_bready  (npu_mst3_axi_bready  )   // write response accept
  , .npu_mst3_axi_bid     (npu_mst3_axi_bid     )   // write response id
  , .npu_mst3_axi_bresp   (npu_mst3_axi_bresp)    // read response
    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst4_axi_arvalid            (npu_mst4_axi_arvalid)     // read command valid
  , .npu_mst4_axi_arready            (npu_mst4_axi_arready)     // read command accept
  , .npu_mst4_axi_arid               (npu_mst4_axi_arid   )     // read command ID
  , .npu_mst4_axi_araddr  (npu_mst4_axi_araddr  )   // read command
  , .npu_mst4_axi_arcache (npu_mst4_axi_arcache )   // read command
  , .npu_mst4_axi_arprot  (npu_mst4_axi_arprot  )   // read command
  , .npu_mst4_axi_arlock  (npu_mst4_axi_arlock  )   // read command
  , .npu_mst4_axi_arburst (npu_mst4_axi_arburst )   // read command
  , .npu_mst4_axi_arlen   (npu_mst4_axi_arlen   )   // read command
  , .npu_mst4_axi_arsize  (npu_mst4_axi_arsize  )   // read command
  , .npu_mst4_axi_arsid(npu_mst4_axi_arsid)   // read command
  , .npu_mst4_axi_arssid(npu_mst4_axi_arssid)   // read command
  , .npu_mst4_axi_rvalid  (npu_mst4_axi_rvalid )    // read data valid
  , .npu_mst4_axi_rready  (npu_mst4_axi_rready )    // read data accept
  , .npu_mst4_axi_rid     (npu_mst4_axi_rid    )    // read data id
  , .npu_mst4_axi_rdata   (npu_mst4_axi_rdata  )    // read data
  , .npu_mst4_axi_rresp   (npu_mst4_axi_rresp)    // read response
  , .npu_mst4_axi_rlast   (npu_mst4_axi_rlast  )    // read last
  , .npu_mst4_axi_awvalid (npu_mst4_axi_awvalid )   // write command valid
  , .npu_mst4_axi_awready (npu_mst4_axi_awready )   // write command accept
  , .npu_mst4_axi_awid    (npu_mst4_axi_awid    )   // write command ID
  , .npu_mst4_axi_awaddr  (npu_mst4_axi_awaddr  )   // read command
  , .npu_mst4_axi_awcache (npu_mst4_axi_awcache )   // read command
  , .npu_mst4_axi_awprot  (npu_mst4_axi_awprot  )   // read command
  , .npu_mst4_axi_awlock  (npu_mst4_axi_awlock  )   // read command
  , .npu_mst4_axi_awburst (npu_mst4_axi_awburst )   // read command
  , .npu_mst4_axi_awlen   (npu_mst4_axi_awlen   )   // read command
  , .npu_mst4_axi_awsize  (npu_mst4_axi_awsize  )   // read command
  , .npu_mst4_axi_awsid(npu_mst4_axi_awsid)     // read command
  , .npu_mst4_axi_awssid(npu_mst4_axi_awssid)   // read command
  , .npu_mst4_axi_wvalid  (npu_mst4_axi_wvalid  )   // write data valid
  , .npu_mst4_axi_wready  (npu_mst4_axi_wready  )   // write data accept
  , .npu_mst4_axi_wdata   (npu_mst4_axi_wdata   )   // write data
  , .npu_mst4_axi_wstrb   (npu_mst4_axi_wstrb   )   // write data strobe
  , .npu_mst4_axi_wlast   (npu_mst4_axi_wlast   )   // write data last
  , .npu_mst4_axi_bvalid  (npu_mst4_axi_bvalid  )   // write response valid
  , .npu_mst4_axi_bready  (npu_mst4_axi_bready  )   // write response accept
  , .npu_mst4_axi_bid     (npu_mst4_axi_bid     )   // write response id
  , .npu_mst4_axi_bresp   (npu_mst4_axi_bresp)    // read response
  );

  //
  // NPU slice instances
  //
  npu_slice_top
  u_l1core0
  (
   .clk                ( sl0_clk                ),
   .clk_en_a           ( sl0_clk_en_a           ),
   .rst_a              ( sl0_rst_a              ),
   .vmid               ( npu_grp0_vmid                  ),
   .evt_vm_irq         ( sl0nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl0nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl0nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl0nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl0nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl0nl1arc_arcnum             ),
   .intvbase_in        ( sl0nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl0nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl0nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl0nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl0nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl0nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl0nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl0nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl0nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl0nl1arc_arc_irq_a          ),
   .isolate_n          ( sl0nl1arc_isolate_n          ),
   .isolate            ( sl0nl1arc_isolate            ),
   .pd_mem             ( sl0nl1arc_pd_mem             ),
   .pd_logic           ( sl0nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[0]                ),
   .l2_event_a         ( l2_to_l1_event[0]                ),
   .l1_peer_send_event ( l1_peer_event_out[0]             ),
   .l1_peer_event_a    ( l1_peer_event_in[0]              ),
   .rtt_swe_val        ( sl0_rtt_swe_val                ),
   .rtt_swe_data       ( sl0_rtt_swe_data               ),
   .rtt_swe_ext        ( sl0_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl0nl1arc_dbgen              ),
   .arct_niden         ( sl0nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl0nl1arc_dbg_),
   .wdt_clk            ( sl0_wdt_clk                    ),
   .ecc_sbe            (sl0_ecc_sbe),
   .ecc_dbe            (sl0_ecc_dbe),
   .dbg_cmdval_a       ( sl0nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl0nl1arc_dbg_pack           ),
   .dbg_resp           ( sl0nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core1
  (
   .clk                ( sl1_clk                ),
   .clk_en_a           ( sl1_clk_en_a           ),
   .rst_a              ( sl1_rst_a              ),
   .vmid               ( npu_grp0_vmid                  ),
   .evt_vm_irq         ( sl1nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl1nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl1nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl1nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl1nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl1nl1arc_arcnum             ),
   .intvbase_in        ( sl1nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl1nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl1nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl1nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl1nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl1nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl1nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl1nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl1nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl1nl1arc_arc_irq_a          ),
   .isolate_n          ( sl1nl1arc_isolate_n          ),
   .isolate            ( sl1nl1arc_isolate            ),
   .pd_mem             ( sl1nl1arc_pd_mem             ),
   .pd_logic           ( sl1nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[1]                ),
   .l2_event_a         ( l2_to_l1_event[1]                ),
   .l1_peer_send_event ( l1_peer_event_out[1]             ),
   .l1_peer_event_a    ( l1_peer_event_in[1]              ),
   .rtt_swe_val        ( sl1_rtt_swe_val                ),
   .rtt_swe_data       ( sl1_rtt_swe_data               ),
   .rtt_swe_ext        ( sl1_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl1nl1arc_dbgen              ),
   .arct_niden         ( sl1nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl1nl1arc_dbg_),
   .wdt_clk            ( sl1_wdt_clk                    ),
   .ecc_sbe            (sl1_ecc_sbe),
   .ecc_dbe            (sl1_ecc_dbe),
   .dbg_cmdval_a       ( sl1nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl1nl1arc_dbg_pack           ),
   .dbg_resp           ( sl1nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core2
  (
   .clk                ( sl2_clk                ),
   .clk_en_a           ( sl2_clk_en_a           ),
   .rst_a              ( sl2_rst_a              ),
   .vmid               ( npu_grp0_vmid                  ),
   .evt_vm_irq         ( sl2nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl2nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl2nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl2nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl2nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl2nl1arc_arcnum             ),
   .intvbase_in        ( sl2nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl2nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl2nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl2nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl2nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl2nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl2nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl2nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl2nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl2nl1arc_arc_irq_a          ),
   .isolate_n          ( sl2nl1arc_isolate_n          ),
   .isolate            ( sl2nl1arc_isolate            ),
   .pd_mem             ( sl2nl1arc_pd_mem             ),
   .pd_logic           ( sl2nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[2]                ),
   .l2_event_a         ( l2_to_l1_event[2]                ),
   .l1_peer_send_event ( l1_peer_event_out[2]             ),
   .l1_peer_event_a    ( l1_peer_event_in[2]              ),
   .rtt_swe_val        ( sl2_rtt_swe_val                ),
   .rtt_swe_data       ( sl2_rtt_swe_data               ),
   .rtt_swe_ext        ( sl2_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl2nl1arc_dbgen              ),
   .arct_niden         ( sl2nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl2nl1arc_dbg_),
   .wdt_clk            ( sl2_wdt_clk                    ),
   .ecc_sbe            (sl2_ecc_sbe),
   .ecc_dbe            (sl2_ecc_dbe),
   .dbg_cmdval_a       ( sl2nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl2nl1arc_dbg_pack           ),
   .dbg_resp           ( sl2nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core3
  (
   .clk                ( sl3_clk                ),
   .clk_en_a           ( sl3_clk_en_a           ),
   .rst_a              ( sl3_rst_a              ),
   .vmid               ( npu_grp0_vmid                  ),
   .evt_vm_irq         ( sl3nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl3nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl3nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl3nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl3nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl3nl1arc_arcnum             ),
   .intvbase_in        ( sl3nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl3nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl3nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl3nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl3nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl3nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl3nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl3nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl3nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl3nl1arc_arc_irq_a          ),
   .isolate_n          ( sl3nl1arc_isolate_n          ),
   .isolate            ( sl3nl1arc_isolate            ),
   .pd_mem             ( sl3nl1arc_pd_mem             ),
   .pd_logic           ( sl3nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[3]                ),
   .l2_event_a         ( l2_to_l1_event[3]                ),
   .l1_peer_send_event ( l1_peer_event_out[3]             ),
   .l1_peer_event_a    ( l1_peer_event_in[3]              ),
   .rtt_swe_val        ( sl3_rtt_swe_val                ),
   .rtt_swe_data       ( sl3_rtt_swe_data               ),
   .rtt_swe_ext        ( sl3_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl3nl1arc_dbgen              ),
   .arct_niden         ( sl3nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl3nl1arc_dbg_),
   .wdt_clk            ( sl3_wdt_clk                    ),
   .ecc_sbe            (sl3_ecc_sbe),
   .ecc_dbe            (sl3_ecc_dbe),
   .dbg_cmdval_a       ( sl3nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl3nl1arc_dbg_pack           ),
   .dbg_resp           ( sl3nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core4
  (
   .clk                ( sl4_clk                ),
   .clk_en_a           ( sl4_clk_en_a           ),
   .rst_a              ( sl4_rst_a              ),
   .vmid               ( npu_grp1_vmid                  ),
   .evt_vm_irq         ( sl4nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl4nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl4nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl4nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl4nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl4nl1arc_arcnum             ),
   .intvbase_in        ( sl4nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl4nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl4nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl4nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl4nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl4nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl4nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl4nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl4nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl4nl1arc_arc_irq_a          ),
   .isolate_n          ( sl4nl1arc_isolate_n          ),
   .isolate            ( sl4nl1arc_isolate            ),
   .pd_mem             ( sl4nl1arc_pd_mem             ),
   .pd_logic           ( sl4nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[4]                ),
   .l2_event_a         ( l2_to_l1_event[4]                ),
   .l1_peer_send_event ( l1_peer_event_out[4]             ),
   .l1_peer_event_a    ( l1_peer_event_in[4]              ),
   .rtt_swe_val        ( sl4_rtt_swe_val                ),
   .rtt_swe_data       ( sl4_rtt_swe_data               ),
   .rtt_swe_ext        ( sl4_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl4nl1arc_dbgen              ),
   .arct_niden         ( sl4nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl4nl1arc_dbg_),
   .wdt_clk            ( sl4_wdt_clk                    ),
   .ecc_sbe            (sl4_ecc_sbe),
   .ecc_dbe            (sl4_ecc_dbe),
   .dbg_cmdval_a       ( sl4nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl4nl1arc_dbg_pack           ),
   .dbg_resp           ( sl4nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core5
  (
   .clk                ( sl5_clk                ),
   .clk_en_a           ( sl5_clk_en_a           ),
   .rst_a              ( sl5_rst_a              ),
   .vmid               ( npu_grp1_vmid                  ),
   .evt_vm_irq         ( sl5nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl5nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl5nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl5nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl5nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl5nl1arc_arcnum             ),
   .intvbase_in        ( sl5nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl5nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl5nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl5nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl5nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl5nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl5nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl5nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl5nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl5nl1arc_arc_irq_a          ),
   .isolate_n          ( sl5nl1arc_isolate_n          ),
   .isolate            ( sl5nl1arc_isolate            ),
   .pd_mem             ( sl5nl1arc_pd_mem             ),
   .pd_logic           ( sl5nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[5]                ),
   .l2_event_a         ( l2_to_l1_event[5]                ),
   .l1_peer_send_event ( l1_peer_event_out[5]             ),
   .l1_peer_event_a    ( l1_peer_event_in[5]              ),
   .rtt_swe_val        ( sl5_rtt_swe_val                ),
   .rtt_swe_data       ( sl5_rtt_swe_data               ),
   .rtt_swe_ext        ( sl5_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl5nl1arc_dbgen              ),
   .arct_niden         ( sl5nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl5nl1arc_dbg_),
   .wdt_clk            ( sl5_wdt_clk                    ),
   .ecc_sbe            (sl5_ecc_sbe),
   .ecc_dbe            (sl5_ecc_dbe),
   .dbg_cmdval_a       ( sl5nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl5nl1arc_dbg_pack           ),
   .dbg_resp           ( sl5nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core6
  (
   .clk                ( sl6_clk                ),
   .clk_en_a           ( sl6_clk_en_a           ),
   .rst_a              ( sl6_rst_a              ),
   .vmid               ( npu_grp1_vmid                  ),
   .evt_vm_irq         ( sl6nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl6nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl6nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl6nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl6nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl6nl1arc_arcnum             ),
   .intvbase_in        ( sl6nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl6nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl6nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl6nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl6nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl6nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl6nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl6nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl6nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl6nl1arc_arc_irq_a          ),
   .isolate_n          ( sl6nl1arc_isolate_n          ),
   .isolate            ( sl6nl1arc_isolate            ),
   .pd_mem             ( sl6nl1arc_pd_mem             ),
   .pd_logic           ( sl6nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[6]                ),
   .l2_event_a         ( l2_to_l1_event[6]                ),
   .l1_peer_send_event ( l1_peer_event_out[6]             ),
   .l1_peer_event_a    ( l1_peer_event_in[6]              ),
   .rtt_swe_val        ( sl6_rtt_swe_val                ),
   .rtt_swe_data       ( sl6_rtt_swe_data               ),
   .rtt_swe_ext        ( sl6_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl6nl1arc_dbgen              ),
   .arct_niden         ( sl6nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl6nl1arc_dbg_),
   .wdt_clk            ( sl6_wdt_clk                    ),
   .ecc_sbe            (sl6_ecc_sbe),
   .ecc_dbe            (sl6_ecc_dbe),
   .dbg_cmdval_a       ( sl6nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl6nl1arc_dbg_pack           ),
   .dbg_resp           ( sl6nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core7
  (
   .clk                ( sl7_clk                ),
   .clk_en_a           ( sl7_clk_en_a           ),
   .rst_a              ( sl7_rst_a              ),
   .vmid               ( npu_grp1_vmid                  ),
   .evt_vm_irq         ( sl7nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl7nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl7nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl7nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl7nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl7nl1arc_arcnum             ),
   .intvbase_in        ( sl7nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl7nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl7nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl7nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl7nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl7nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl7nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl7nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl7nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl7nl1arc_arc_irq_a          ),
   .isolate_n          ( sl7nl1arc_isolate_n          ),
   .isolate            ( sl7nl1arc_isolate            ),
   .pd_mem             ( sl7nl1arc_pd_mem             ),
   .pd_logic           ( sl7nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[7]                ),
   .l2_event_a         ( l2_to_l1_event[7]                ),
   .l1_peer_send_event ( l1_peer_event_out[7]             ),
   .l1_peer_event_a    ( l1_peer_event_in[7]              ),
   .rtt_swe_val        ( sl7_rtt_swe_val                ),
   .rtt_swe_data       ( sl7_rtt_swe_data               ),
   .rtt_swe_ext        ( sl7_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl7nl1arc_dbgen              ),
   .arct_niden         ( sl7nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl7nl1arc_dbg_),
   .wdt_clk            ( sl7_wdt_clk                    ),
   .ecc_sbe            (sl7_ecc_sbe),
   .ecc_dbe            (sl7_ecc_dbe),
   .dbg_cmdval_a       ( sl7nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl7nl1arc_dbg_pack           ),
   .dbg_resp           ( sl7nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core8
  (
   .clk                ( sl8_clk                ),
   .clk_en_a           ( sl8_clk_en_a           ),
   .rst_a              ( sl8_rst_a              ),
   .vmid               ( npu_grp2_vmid                  ),
   .evt_vm_irq         ( sl8nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl8nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl8nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl8nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl8nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl8nl1arc_arcnum             ),
   .intvbase_in        ( sl8nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl8nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl8nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl8nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl8nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl8nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl8nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl8nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl8nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl8nl1arc_arc_irq_a          ),
   .isolate_n          ( sl8nl1arc_isolate_n          ),
   .isolate            ( sl8nl1arc_isolate            ),
   .pd_mem             ( sl8nl1arc_pd_mem             ),
   .pd_logic           ( sl8nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[8]                ),
   .l2_event_a         ( l2_to_l1_event[8]                ),
   .l1_peer_send_event ( l1_peer_event_out[8]             ),
   .l1_peer_event_a    ( l1_peer_event_in[8]              ),
   .rtt_swe_val        ( sl8_rtt_swe_val                ),
   .rtt_swe_data       ( sl8_rtt_swe_data               ),
   .rtt_swe_ext        ( sl8_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl8nl1arc_dbgen              ),
   .arct_niden         ( sl8nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl8nl1arc_dbg_),
   .wdt_clk            ( sl8_wdt_clk                    ),
   .ecc_sbe            (sl8_ecc_sbe),
   .ecc_dbe            (sl8_ecc_dbe),
   .dbg_cmdval_a       ( sl8nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl8nl1arc_dbg_pack           ),
   .dbg_resp           ( sl8nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core9
  (
   .clk                ( sl9_clk                ),
   .clk_en_a           ( sl9_clk_en_a           ),
   .rst_a              ( sl9_rst_a              ),
   .vmid               ( npu_grp2_vmid                  ),
   .evt_vm_irq         ( sl9nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl9nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl9nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl9nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl9nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl9nl1arc_arcnum             ),
   .intvbase_in        ( sl9nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl9nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl9nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl9nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl9nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl9nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl9nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl9nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl9nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl9nl1arc_arc_irq_a          ),
   .isolate_n          ( sl9nl1arc_isolate_n          ),
   .isolate            ( sl9nl1arc_isolate            ),
   .pd_mem             ( sl9nl1arc_pd_mem             ),
   .pd_logic           ( sl9nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[9]                ),
   .l2_event_a         ( l2_to_l1_event[9]                ),
   .l1_peer_send_event ( l1_peer_event_out[9]             ),
   .l1_peer_event_a    ( l1_peer_event_in[9]              ),
   .rtt_swe_val        ( sl9_rtt_swe_val                ),
   .rtt_swe_data       ( sl9_rtt_swe_data               ),
   .rtt_swe_ext        ( sl9_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl9nl1arc_dbgen              ),
   .arct_niden         ( sl9nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl9nl1arc_dbg_),
   .wdt_clk            ( sl9_wdt_clk                    ),
   .ecc_sbe            (sl9_ecc_sbe),
   .ecc_dbe            (sl9_ecc_dbe),
   .dbg_cmdval_a       ( sl9nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl9nl1arc_dbg_pack           ),
   .dbg_resp           ( sl9nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core10
  (
   .clk                ( sl10_clk                ),
   .clk_en_a           ( sl10_clk_en_a           ),
   .rst_a              ( sl10_rst_a              ),
   .vmid               ( npu_grp2_vmid                  ),
   .evt_vm_irq         ( sl10nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl10nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl10nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl10nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl10nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl10nl1arc_arcnum             ),
   .intvbase_in        ( sl10nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl10nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl10nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl10nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl10nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl10nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl10nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl10nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl10nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl10nl1arc_arc_irq_a          ),
   .isolate_n          ( sl10nl1arc_isolate_n          ),
   .isolate            ( sl10nl1arc_isolate            ),
   .pd_mem             ( sl10nl1arc_pd_mem             ),
   .pd_logic           ( sl10nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[10]                ),
   .l2_event_a         ( l2_to_l1_event[10]                ),
   .l1_peer_send_event ( l1_peer_event_out[10]             ),
   .l1_peer_event_a    ( l1_peer_event_in[10]              ),
   .rtt_swe_val        ( sl10_rtt_swe_val                ),
   .rtt_swe_data       ( sl10_rtt_swe_data               ),
   .rtt_swe_ext        ( sl10_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl10nl1arc_dbgen              ),
   .arct_niden         ( sl10nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl10nl1arc_dbg_),
   .wdt_clk            ( sl10_wdt_clk                    ),
   .ecc_sbe            (sl10_ecc_sbe),
   .ecc_dbe            (sl10_ecc_dbe),
   .dbg_cmdval_a       ( sl10nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl10nl1arc_dbg_pack           ),
   .dbg_resp           ( sl10nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core11
  (
   .clk                ( sl11_clk                ),
   .clk_en_a           ( sl11_clk_en_a           ),
   .rst_a              ( sl11_rst_a              ),
   .vmid               ( npu_grp2_vmid                  ),
   .evt_vm_irq         ( sl11nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl11nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl11nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl11nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl11nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl11nl1arc_arcnum             ),
   .intvbase_in        ( sl11nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl11nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl11nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl11nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl11nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl11nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl11nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl11nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl11nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl11nl1arc_arc_irq_a          ),
   .isolate_n          ( sl11nl1arc_isolate_n          ),
   .isolate            ( sl11nl1arc_isolate            ),
   .pd_mem             ( sl11nl1arc_pd_mem             ),
   .pd_logic           ( sl11nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[11]                ),
   .l2_event_a         ( l2_to_l1_event[11]                ),
   .l1_peer_send_event ( l1_peer_event_out[11]             ),
   .l1_peer_event_a    ( l1_peer_event_in[11]              ),
   .rtt_swe_val        ( sl11_rtt_swe_val                ),
   .rtt_swe_data       ( sl11_rtt_swe_data               ),
   .rtt_swe_ext        ( sl11_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl11nl1arc_dbgen              ),
   .arct_niden         ( sl11nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl11nl1arc_dbg_),
   .wdt_clk            ( sl11_wdt_clk                    ),
   .ecc_sbe            (sl11_ecc_sbe),
   .ecc_dbe            (sl11_ecc_dbe),
   .dbg_cmdval_a       ( sl11nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl11nl1arc_dbg_pack           ),
   .dbg_resp           ( sl11nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core12
  (
   .clk                ( sl12_clk                ),
   .clk_en_a           ( sl12_clk_en_a           ),
   .rst_a              ( sl12_rst_a              ),
   .vmid               ( npu_grp3_vmid                  ),
   .evt_vm_irq         ( sl12nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl12nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl12nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl12nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl12nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl12nl1arc_arcnum             ),
   .intvbase_in        ( sl12nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl12nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl12nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl12nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl12nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl12nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl12nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl12nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl12nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl12nl1arc_arc_irq_a          ),
   .isolate_n          ( sl12nl1arc_isolate_n          ),
   .isolate            ( sl12nl1arc_isolate            ),
   .pd_mem             ( sl12nl1arc_pd_mem             ),
   .pd_logic           ( sl12nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[12]                ),
   .l2_event_a         ( l2_to_l1_event[12]                ),
   .l1_peer_send_event ( l1_peer_event_out[12]             ),
   .l1_peer_event_a    ( l1_peer_event_in[12]              ),
   .rtt_swe_val        ( sl12_rtt_swe_val                ),
   .rtt_swe_data       ( sl12_rtt_swe_data               ),
   .rtt_swe_ext        ( sl12_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl12nl1arc_dbgen              ),
   .arct_niden         ( sl12nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl12nl1arc_dbg_),
   .wdt_clk            ( sl12_wdt_clk                    ),
   .ecc_sbe            (sl12_ecc_sbe),
   .ecc_dbe            (sl12_ecc_dbe),
   .dbg_cmdval_a       ( sl12nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl12nl1arc_dbg_pack           ),
   .dbg_resp           ( sl12nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core13
  (
   .clk                ( sl13_clk                ),
   .clk_en_a           ( sl13_clk_en_a           ),
   .rst_a              ( sl13_rst_a              ),
   .vmid               ( npu_grp3_vmid                  ),
   .evt_vm_irq         ( sl13nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl13nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl13nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl13nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl13nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl13nl1arc_arcnum             ),
   .intvbase_in        ( sl13nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl13nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl13nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl13nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl13nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl13nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl13nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl13nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl13nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl13nl1arc_arc_irq_a          ),
   .isolate_n          ( sl13nl1arc_isolate_n          ),
   .isolate            ( sl13nl1arc_isolate            ),
   .pd_mem             ( sl13nl1arc_pd_mem             ),
   .pd_logic           ( sl13nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[13]                ),
   .l2_event_a         ( l2_to_l1_event[13]                ),
   .l1_peer_send_event ( l1_peer_event_out[13]             ),
   .l1_peer_event_a    ( l1_peer_event_in[13]              ),
   .rtt_swe_val        ( sl13_rtt_swe_val                ),
   .rtt_swe_data       ( sl13_rtt_swe_data               ),
   .rtt_swe_ext        ( sl13_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl13nl1arc_dbgen              ),
   .arct_niden         ( sl13nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl13nl1arc_dbg_),
   .wdt_clk            ( sl13_wdt_clk                    ),
   .ecc_sbe            (sl13_ecc_sbe),
   .ecc_dbe            (sl13_ecc_dbe),
   .dbg_cmdval_a       ( sl13nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl13nl1arc_dbg_pack           ),
   .dbg_resp           ( sl13nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core14
  (
   .clk                ( sl14_clk                ),
   .clk_en_a           ( sl14_clk_en_a           ),
   .rst_a              ( sl14_rst_a              ),
   .vmid               ( npu_grp3_vmid                  ),
   .evt_vm_irq         ( sl14nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl14nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl14nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl14nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl14nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl14nl1arc_arcnum             ),
   .intvbase_in        ( sl14nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl14nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl14nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl14nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl14nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl14nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl14nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl14nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl14nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl14nl1arc_arc_irq_a          ),
   .isolate_n          ( sl14nl1arc_isolate_n          ),
   .isolate            ( sl14nl1arc_isolate            ),
   .pd_mem             ( sl14nl1arc_pd_mem             ),
   .pd_logic           ( sl14nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[14]                ),
   .l2_event_a         ( l2_to_l1_event[14]                ),
   .l1_peer_send_event ( l1_peer_event_out[14]             ),
   .l1_peer_event_a    ( l1_peer_event_in[14]              ),
   .rtt_swe_val        ( sl14_rtt_swe_val                ),
   .rtt_swe_data       ( sl14_rtt_swe_data               ),
   .rtt_swe_ext        ( sl14_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl14nl1arc_dbgen              ),
   .arct_niden         ( sl14nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl14nl1arc_dbg_),
   .wdt_clk            ( sl14_wdt_clk                    ),
   .ecc_sbe            (sl14_ecc_sbe),
   .ecc_dbe            (sl14_ecc_dbe),
   .dbg_cmdval_a       ( sl14nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl14nl1arc_dbg_pack           ),
   .dbg_resp           ( sl14nl1arc_dbg_resp           )
   );
  npu_slice_top
  u_l1core15
  (
   .clk                ( sl15_clk                ),
   .clk_en_a           ( sl15_clk_en_a           ),
   .rst_a              ( sl15_rst_a              ),
   .vmid               ( npu_grp3_vmid                  ),
   .evt_vm_irq         ( sl15nl1arc_evt_vm_irq         ),
   `AXIASYNCMINST(npu_axi_gals_,sl15nl1arc_dev_axi_gals_),
   `AXIASYNCSINST(mmio_axi_gals_,sl15nl1arc_ccm_axi_gals_),
   .test_mode          ( test_mode                         ),
   .clusternum         ( clusternum                        ),
   .wdt_reset          ( sl15nl1arc_wdt_reset_error    ),
   .wdt_reset_wdt_clk  ( sl15nl1arc_wdt_reset_wdt_clk_error),
   .arcnum             ( sl15nl1arc_arcnum             ),
   .intvbase_in        ( sl15nl1arc_intvbase_in        ),
   .arc_halt_req_a     ( sl15nl1arc_arc_halt_req_a     ),
   .arc_halt_ack       ( sl15nl1arc_arc_halt_ack       ),
   .arc_run_req_a      ( sl15nl1arc_arc_run_req_a      ),
   .arc_run_ack        ( sl15nl1arc_arc_run_ack        ),
   .sys_sleep_r        ( sl15nl1arc_sys_sleep_r        ),
   .sys_sleep_mode_r   ( sl15nl1arc_sys_sleep_mode_r   ),
   .sys_halt_r         ( sl15nl1arc_sys_halt_r         ),
   .sys_tf_halt_r      ( sl15nl1arc_sys_tf_halt_r      ),
   .arc_irq_a          ( sl15nl1arc_arc_irq_a          ),
   .isolate_n          ( sl15nl1arc_isolate_n          ),
   .isolate            ( sl15nl1arc_isolate            ),
   .pd_mem             ( sl15nl1arc_pd_mem             ),
   .pd_logic           ( sl15nl1arc_pd_logic           ),
   .l2_send_event      ( l1_to_l2_event[15]                ),
   .l2_event_a         ( l2_to_l1_event[15]                ),
   .l1_peer_send_event ( l1_peer_event_out[15]             ),
   .l1_peer_event_a    ( l1_peer_event_in[15]              ),
   .rtt_swe_val        ( sl15_rtt_swe_val                ),
   .rtt_swe_data       ( sl15_rtt_swe_data               ),
   .rtt_swe_ext        ( sl15_rtt_swe_ext                ),
   .arct_dbg_prot_sel  ( arct_dbg_prot_sel                 ),
   .arct_dbgen         ( sl15nl1arc_dbgen              ),
   .arct_niden         ( sl15nl1arc_niden              ),
   .arct_rst_an        ( arct_rst_an                       ),
   `APBASYNCINST(dbg_as_,sl15nl1arc_dbg_),
   .wdt_clk            ( sl15_wdt_clk                    ),
   .ecc_sbe            (sl15_ecc_sbe),
   .ecc_dbe            (sl15_ecc_dbe),
   .dbg_cmdval_a       ( sl15nl1arc_dbg_cmdval         ),
   .dbg_pack_a         ( sl15nl1arc_dbg_pack           ),
   .dbg_resp           ( sl15nl1arc_dbg_resp           )
   );



endmodule : npu_top
