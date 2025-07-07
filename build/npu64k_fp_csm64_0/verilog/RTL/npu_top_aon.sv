
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
`include "npu_apb_macros.svh"






module npu_top_aon
  import npu_types::*;
  import npu_ecc_types::*;
 (
  output  logic  [7:0]                   nl2arc0_arcnum,
  `APBASYNCINI(16,32,nl2arc0_),
  output  logic  [7:0]                   nl2arc1_arcnum,
  `APBASYNCINI(16,32,nl2arc1_),
  output  logic  [7:0]                   sl0nl1arc_arcnum,
  input   logic                          sl0nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl0nl1arc_),
  output  logic  [7:0]                   sl1nl1arc_arcnum,
  input   logic                          sl1nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl1nl1arc_),
  output  logic  [7:0]                   sl2nl1arc_arcnum,
  input   logic                          sl2nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl2nl1arc_),
  output  logic  [7:0]                   sl3nl1arc_arcnum,
  input   logic                          sl3nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl3nl1arc_),
  output  logic  [7:0]                   sl4nl1arc_arcnum,
  input   logic                          sl4nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl4nl1arc_),
  output  logic  [7:0]                   sl5nl1arc_arcnum,
  input   logic                          sl5nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl5nl1arc_),
  output  logic  [7:0]                   sl6nl1arc_arcnum,
  input   logic                          sl6nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl6nl1arc_),
  output  logic  [7:0]                   sl7nl1arc_arcnum,
  input   logic                          sl7nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl7nl1arc_),
  output  logic  [7:0]                   sl8nl1arc_arcnum,
  input   logic                          sl8nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl8nl1arc_),
  output  logic  [7:0]                   sl9nl1arc_arcnum,
  input   logic                          sl9nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl9nl1arc_),
  output  logic  [7:0]                   sl10nl1arc_arcnum,
  input   logic                          sl10nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl10nl1arc_),
  output  logic  [7:0]                   sl11nl1arc_arcnum,
  input   logic                          sl11nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl11nl1arc_),
  output  logic  [7:0]                   sl12nl1arc_arcnum,
  input   logic                          sl12nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl12nl1arc_),
  output  logic  [7:0]                   sl13nl1arc_arcnum,
  input   logic                          sl13nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl13nl1arc_),
  output  logic  [7:0]                   sl14nl1arc_arcnum,
  input   logic                          sl14nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl14nl1arc_),
  output  logic  [7:0]                   sl15nl1arc_arcnum,
  input   logic                          sl15nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl15nl1arc_),
  input   logic                          arct_clk,
  input   logic                          arct_rst_an,   // async reset, active low
  `APBSLV(32,32,arct_),
  `APBASYNCINI(16,32,arct_syn_),
  // ARC_Trace
  output  logic                          grp4_rtt_swe_val,
  output  logic [32:0]                   grp4_rtt_swe_data,
  output  logic [7:0]                    grp4_rtt_swe_ext,
  output  logic                          grp5_rtt_swe_val,
  output  logic [32:0]                   grp5_rtt_swe_data,
  output  logic [7:0]                    grp5_rtt_swe_ext,
  output  logic                          grp6_rtt_swe_val,
  output  logic [32:0]                   grp6_rtt_swe_data,
  output  logic [7:0]                    grp6_rtt_swe_ext,
  output  logic                          grp7_rtt_swe_val,
  output  logic [32:0]                   grp7_rtt_swe_data,
  output  logic [7:0]                    grp7_rtt_swe_ext,
  output  logic                          grp8_rtt_swe_val,
  output  logic [32:0]                   grp8_rtt_swe_data,
  output  logic [7:0]                    grp8_rtt_swe_ext,
  output  logic                          grp9_rtt_swe_val,
  output  logic [32:0]                   grp9_rtt_swe_data,
  output  logic [7:0]                    grp9_rtt_swe_ext,
  output  logic                          grp10_rtt_swe_val,
  output  logic [32:0]                   grp10_rtt_swe_data,
  output  logic [7:0]                    grp10_rtt_swe_ext,
  output  logic                          grp11_rtt_swe_val,
  output  logic [32:0]                   grp11_rtt_swe_data,
  output  logic [7:0]                    grp11_rtt_swe_ext,
  output  logic                          grp12_rtt_swe_val,
  output  logic [32:0]                   grp12_rtt_swe_data,
  output  logic [7:0]                    grp12_rtt_swe_ext,
  output  logic                          grp13_rtt_swe_val,
  output  logic [32:0]                   grp13_rtt_swe_data,
  output  logic [7:0]                    grp13_rtt_swe_ext,
  output  logic                          grp14_rtt_swe_val,
  output  logic [32:0]                   grp14_rtt_swe_data,
  output  logic [7:0]                    grp14_rtt_swe_ext,
  output  logic                          grp15_rtt_swe_val,
  output  logic [32:0]                   grp15_rtt_swe_data,
  output  logic [7:0]                    grp15_rtt_swe_ext,
  output  logic                          grp16_rtt_swe_val,
  output  logic [32:0]                   grp16_rtt_swe_data,
  output  logic [7:0]                    grp16_rtt_swe_ext,
  input   logic [`NPU_STU_CHAN_NUM-1:0]                  stu_err_irq_a,
  input   logic [`NPU_SLICE_NUM-1:0][`NPU_SLICE_NUM-1:0] l1_peer_event_out,
  output  logic [`NPU_SLICE_NUM-1:0][`NPU_SLICE_NUM-1:0] l1_peer_event_in,
  output  logic                          grp0_evt_vm_irq,
  output  logic                          grp1_evt_vm_irq,
  output  logic                          grp2_evt_vm_irq,
  output  logic                          grp3_evt_vm_irq,
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
  // read data channel
  input  logic                        npu_mst_axi_rvalid,  // read data valid
  output logic                        npu_mst_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst_axi_rid,     // read data id
  input  logic          [64-1:0]   npu_mst_axi_rdata,   // read data
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
  // write data channel
  output logic                        npu_mst_axi_wvalid,  // write data valid
  input  logic                        npu_mst_axi_wready,  // write data accept
  output logic          [64-1:0]   npu_mst_axi_wdata,   // write data
  output logic          [64/8-1:0] npu_mst_axi_wstrb,   // write data strobe
  output logic                        npu_mst_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst_axi_bvalid,  // write response valid
  output logic                        npu_mst_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst_axi_bresp,    // write response
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
  input   logic                          npu_noc_clk,
  input   logic                          npu_noc_rst_a,
  input   logic                          npu_cfg_clk,
  input   logic                          npu_cfg_rst_a,
  input   logic                          sl0nl1arc_pwr_dwn_a,
  output  logic                          sl0nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl0nl1arc_dbg_pack,
  input   logic [31:0]                   sl0nl1arc_dbg_resp,
  input   logic                          sl1nl1arc_pwr_dwn_a,
  output  logic                          sl1nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl1nl1arc_dbg_pack,
  input   logic [31:0]                   sl1nl1arc_dbg_resp,
  input   logic                          sl2nl1arc_pwr_dwn_a,
  output  logic                          sl2nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl2nl1arc_dbg_pack,
  input   logic [31:0]                   sl2nl1arc_dbg_resp,
  input   logic                          sl3nl1arc_pwr_dwn_a,
  output  logic                          sl3nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl3nl1arc_dbg_pack,
  input   logic [31:0]                   sl3nl1arc_dbg_resp,
  input   logic                          sl4nl1arc_pwr_dwn_a,
  output  logic                          sl4nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl4nl1arc_dbg_pack,
  input   logic [31:0]                   sl4nl1arc_dbg_resp,
  input   logic                          sl5nl1arc_pwr_dwn_a,
  output  logic                          sl5nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl5nl1arc_dbg_pack,
  input   logic [31:0]                   sl5nl1arc_dbg_resp,
  input   logic                          sl6nl1arc_pwr_dwn_a,
  output  logic                          sl6nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl6nl1arc_dbg_pack,
  input   logic [31:0]                   sl6nl1arc_dbg_resp,
  input   logic                          sl7nl1arc_pwr_dwn_a,
  output  logic                          sl7nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl7nl1arc_dbg_pack,
  input   logic [31:0]                   sl7nl1arc_dbg_resp,
  input   logic                          sl8nl1arc_pwr_dwn_a,
  output  logic                          sl8nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl8nl1arc_dbg_pack,
  input   logic [31:0]                   sl8nl1arc_dbg_resp,
  input   logic                          sl9nl1arc_pwr_dwn_a,
  output  logic                          sl9nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl9nl1arc_dbg_pack,
  input   logic [31:0]                   sl9nl1arc_dbg_resp,
  input   logic                          sl10nl1arc_pwr_dwn_a,
  output  logic                          sl10nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl10nl1arc_dbg_pack,
  input   logic [31:0]                   sl10nl1arc_dbg_resp,
  input   logic                          sl11nl1arc_pwr_dwn_a,
  output  logic                          sl11nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl11nl1arc_dbg_pack,
  input   logic [31:0]                   sl11nl1arc_dbg_resp,
  input   logic                          sl12nl1arc_pwr_dwn_a,
  output  logic                          sl12nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl12nl1arc_dbg_pack,
  input   logic [31:0]                   sl12nl1arc_dbg_resp,
  input   logic                          sl13nl1arc_pwr_dwn_a,
  output  logic                          sl13nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl13nl1arc_dbg_pack,
  input   logic [31:0]                   sl13nl1arc_dbg_resp,
  input   logic                          sl14nl1arc_pwr_dwn_a,
  output  logic                          sl14nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl14nl1arc_dbg_pack,
  input   logic [31:0]                   sl14nl1arc_dbg_resp,
  input   logic                          sl15nl1arc_pwr_dwn_a,
  output  logic                          sl15nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl15nl1arc_dbg_pack,
  input   logic [31:0]                   sl15nl1arc_dbg_resp,
  // L2 ARC0 debug interface
  output  logic                          nl2arc0_dbg_cmdval,
  output  logic [36:0]                   nl2arc0_dbg_pack,
  input   logic [31:0]                   nl2arc0_dbg_resp,
  // L2 ARC1 debug interface
  output  logic                          nl2arc1_dbg_cmdval,
  output  logic [36:0]                   nl2arc1_dbg_pack,
  input   logic [31:0]                   nl2arc1_dbg_resp,
  // NoC master interfaces
  `AXIASYNCSLV(5,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,l2arc_noc_axi_gals_),
  // DMI slave interfaces
  `AXIASYNCMST(`NPU_AXI_TARGET_ID_WIDTH,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,dmi0_axi_gals_),
  // configuration slave AXI
  `AXIASYNCMST(`NPU_AXI_TARGET_ID_WIDTH,32,1,1,1,1,1,0,0,0,0,0,cfg_axi_gals_),
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
  input   logic                          grp0_pwr_dwn_a,
  input   logic                          grp1_pwr_dwn_a,
  input   logic                          grp2_pwr_dwn_a,
  input   logic                          grp3_pwr_dwn_a,
  input   logic                          nl2arc_pwr_dwn_a,
  input   logic                          test_mode,
  input   logic                          npu_core_clk,
  input   logic                          npu_core_rst_a
  );

  localparam HOR_SLC_NUM  = 1;
  localparam VER_SLC_NUM  = 1;
  localparam DIG_SLC_NUM  = 2;
  localparam E2E_HIER_LVL = 0;

  logic npu_cfg_rst_sync;
  npu_reset_ctrl 
  u_sync_cfg_rst
   (
    .clk        ( npu_cfg_clk   ),
    .rst_a      ( npu_cfg_rst_a ),
    .test_mode  ( test_mode     ),
    .rst        ( npu_cfg_rst_sync)
   );

  logic npu_noc_rst_sync;
  npu_reset_ctrl 
  u_sync_noc_rst
   (
    .clk        ( npu_noc_clk   ),
    .rst_a      ( npu_noc_rst_a ),
    .test_mode  ( test_mode     ),
    .rst        ( npu_noc_rst_sync)
   );



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
  //-npu_dmi0_axi
  logic [SLICE_DMA_ARUW-1: 0] npu_dmi0_axi_aruser;
  logic [SLICE_DMA_RUW-1: 0]  npu_dmi0_axi_ruser;
  logic [SLICE_DMA_AWUW-1: 0] npu_dmi0_axi_awuser;
  logic [SLICE_DMA_WUW-1: 0]  npu_dmi0_axi_wuser;
  logic [SLICE_DMA_BUW-1: 0]  npu_dmi0_axi_buser;
  logic [4-1: 0] npu_dmi0_axi_arregion;
  logic [4-1: 0] npu_dmi0_axi_awregion;
  assign npu_dmi0_axi_arregion = '0;
  assign npu_dmi0_axi_awregion = '0;
  assign npu_dmi0_axi_aruser   = '0;
  assign npu_dmi0_axi_awuser   = '0;
  assign npu_dmi0_axi_wuser    = '0;

  logic [SLICE_MMIO_ARUW-1: 0] npu_cfg_axi_aruser;
  logic [SLICE_MMIO_RUW-1: 0]  npu_cfg_axi_ruser;
  logic [SLICE_MMIO_AWUW-1: 0] npu_cfg_axi_awuser;
  logic [SLICE_MMIO_WUW-1: 0]  npu_cfg_axi_wuser;
  logic [SLICE_MMIO_BUW-1: 0]  npu_cfg_axi_buser;
  logic [4-1: 0] npu_cfg_axi_arregion;
  logic [4-1: 0] npu_cfg_axi_awregion;
  assign npu_cfg_axi_arregion = '0;
  assign npu_cfg_axi_awregion = '0;
  assign npu_cfg_axi_aruser   = '0;
  assign npu_cfg_axi_awuser   = '0;
  assign npu_cfg_axi_wuser    = '0;


  logic [`NPU_SLICE_NUM:0]                  jtag_td;
  //NoC master
  `AXIWIRES(5,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,il2arc_noc_axi_);
  `AXIWIRES(5,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,l2arc_noc_axi_);
  //DMI slave
  `AXIWIRESN(`NPU_AXI_TARGETS,`NPU_AXI_TARGET_ID_WIDTH,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,idmi_axi_);
  `AXIWIRESN(`NPU_AXI_TARGETS,`NPU_AXI_TARGET_ID_WIDTH,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,dmi_axi_);
  //Config AXI
  `AXIWIRES(`NPU_AXI_TARGET_ID_WIDTH,32,1,1,1,1,1,icfg_axi_);
  `AXIWIRES(`NPU_AXI_TARGET_ID_WIDTH,32,1,1,1,1,1,cfg_axi_);

  
// Constant Output Value
  // ARC_Trace
  assign grp4_rtt_swe_val  = 1'b0;
  assign grp4_rtt_swe_data = 33'b0;
  assign grp4_rtt_swe_ext  = 8'b0;
  assign grp5_rtt_swe_val  = 1'b0;
  assign grp5_rtt_swe_data = 33'b0;
  assign grp5_rtt_swe_ext  = 8'b0;
  assign grp6_rtt_swe_val  = 1'b0;
  assign grp6_rtt_swe_data = 33'b0;
  assign grp6_rtt_swe_ext  = 8'b0;
  assign grp7_rtt_swe_val  = 1'b0;
  assign grp7_rtt_swe_data = 33'b0;
  assign grp7_rtt_swe_ext  = 8'b0;
  assign grp8_rtt_swe_val  = 1'b0;
  assign grp8_rtt_swe_data = 33'b0;
  assign grp8_rtt_swe_ext  = 8'b0;
  assign grp9_rtt_swe_val  = 1'b0;
  assign grp9_rtt_swe_data = 33'b0;
  assign grp9_rtt_swe_ext  = 8'b0;
  assign grp10_rtt_swe_val  = 1'b0;
  assign grp10_rtt_swe_data = 33'b0;
  assign grp10_rtt_swe_ext  = 8'b0;
  assign grp11_rtt_swe_val  = 1'b0;
  assign grp11_rtt_swe_data = 33'b0;
  assign grp11_rtt_swe_ext  = 8'b0;
  assign grp12_rtt_swe_val  = 1'b0;
  assign grp12_rtt_swe_data = 33'b0;
  assign grp12_rtt_swe_ext  = 8'b0;
  assign grp13_rtt_swe_val  = 1'b0;
  assign grp13_rtt_swe_data = 33'b0;
  assign grp13_rtt_swe_ext  = 8'b0;
  assign grp14_rtt_swe_val  = 1'b0;
  assign grp14_rtt_swe_data = 33'b0;
  assign grp14_rtt_swe_ext  = 8'b0;
  assign grp15_rtt_swe_val  = 1'b0;
  assign grp15_rtt_swe_data = 33'b0;
  assign grp15_rtt_swe_ext  = 8'b0;
  assign grp16_rtt_swe_val  = 1'b0;
  assign grp16_rtt_swe_data = 33'b0;
  assign grp16_rtt_swe_ext  = 8'b0;


  //
  // Transpose peer events
  //
  always_comb
  begin : trans_PROC
    for (int i = 0; i < `NPU_SLICE_NUM; i++)
    begin
      for (int j = 0; j < `NPU_SLICE_NUM; j++)
      begin
        l1_peer_event_in[i][j]  = l1_peer_event_out[j][i];
      end
    end
  end : trans_PROC
  
// Async Bridge && JTAG
  
  
  //
  // Async AXI split bridges on NoC master ports, l2arc2noc, grp2noc
  //
  `AXIASGS_EXT(npu_mst_axi_,l2arc_noc_axi_);


  //
  // Target part of asynchronous bridge from L2ARC to NoC
  //
  npu_axi_async_tgt
  #(
    .AXIIDW         ( 5                 ),
    .AXIDW          ( 64                ),
    .AXIAWUW        ( SLICE_DMA_AWUW    ),
    .AXIWUW         ( SLICE_DMA_WUW     ),
    .AXIBUW         ( SLICE_DMA_BUW     ),
    .AXIARUW        ( SLICE_DMA_ARUW    ),
    .AXIRUW         ( SLICE_DMA_RUW     ),
    .AWFIFO_DEPTHL2 ( 1                 ),
    .WFIFO_DEPTHL2  ( 3                 ),
    .BFIFO_DEPTHL2  ( 1                 ),
    .ARFIFO_DEPTHL2 ( 1                 ),
    .RFIFO_DEPTHL2  ( 3                 )
  )
  u_axi_l2arc_noc_tgt_inst
  (
   .axi_mst_clk               ( npu_noc_clk                     ), 
   .axi_mst_rst_a             ( npu_noc_rst_a                   ),
   .ini_pwr_dwn_a             ( nl2arc_pwr_dwn_a              ),  
   .test_mode                 ( test_mode                       ),
   .clk_req_a                 (                                 ), // intentionally left open
   `AXIINST(axi_mst_,il2arc_noc_axi_),
   `AXIASYNCSSUB(axi_async_slv_,l2arc_noc_axi_gals_)
  );


  //
  // L2ARC NoC output register slice
  //
  npu_axi_slice
  #(
    .AXIIDW       ( 5               ),
    .AXIDW        ( 64              ),
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
   .clk                     ( npu_noc_clk               ),
   .rst_a                   ( npu_noc_rst_sync          ),
   `AXIINST(axi_slv_,il2arc_noc_axi_),
   `AXIINST(axi_mst_,l2arc_noc_axi_)
   );

  // Asynchronous bridges on DMI slave ports, noc2core
  //

  `AXIASGN_EXT(0,dmi_axi_,npu_dmi0_axi_);

  //
  // Initiator part of NoC DMI port async bridge
  //
  npu_axi_async_ini
  #(
    .AXIIDW         ( `NPU_AXI_TARGET_ID_WIDTH ),
    .AXIDW          ( 64*VSIZE                 ),
    .AXIAWUW        ( SLICE_DMA_AWUW           ),
    .AXIWUW         ( SLICE_DMA_WUW            ),
    .AXIBUW         ( SLICE_DMA_BUW            ),
    .AXIARUW        ( SLICE_DMA_ARUW           ),
    .AXIRUW         ( SLICE_DMA_RUW            ),
    .AWFIFO_DEPTHL2 ( 1                        ),
    .WFIFO_DEPTHL2  ( 3                        ),
    .BFIFO_DEPTHL2  ( 1                        ),
    .ARFIFO_DEPTHL2 ( 1                        ),
    .RFIFO_DEPTHL2  ( 3                        )
  )
  u_dmi0_ini_inst
  (
    .axi_slv_clk          ( npu_noc_clk                  ), 
    .axi_slv_rst_a        ( npu_noc_rst_a                ),
    .tgt_pwr_dwn_a        ( nl2arc_pwr_dwn_a           ),  
    .test_mode            ( test_mode                    ),
    `AXIINSTM(0,axi_slv_,idmi_axi_),
    `AXIASYNCMSUB(axi_async_mst_,dmi0_axi_gals_)
   );  


  //
  // Register slice on NoC DMI port
  //
  npu_axi_slice
  #(
    .AXIIDW       ( `NPU_AXI_TARGET_ID_WIDTH),
    .AXIDW        ( 64*VSIZE        ),
    .AXIAWUW      ( SLICE_DMA_AWUW  ),
    .AXIWUW       ( SLICE_DMA_WUW   ),
    .AXIBUW       ( SLICE_DMA_BUW   ),
    .AXIARUW      ( SLICE_DMA_ARUW  ),
    .AXIRUW       ( SLICE_DMA_RUW   ),
    .NUMSLC       ( 1               ),
    .AWFIFO_DEPTH ( 0               ),
    .WFIFO_DEPTH  ( 0               ),
    .BFIFO_DEPTH  ( 1               ),
    .ARFIFO_DEPTH ( 0               ),
    .RFIFO_DEPTH  ( 2               )
  )
  u_slc_dmi0_inst
  (
   .clk                    ( npu_noc_clk                  ),
   .rst_a                  ( npu_noc_rst_sync             ),
   `AXIINSTM(0,axi_slv_,dmi_axi_),
   `AXIINSTM(0,axi_mst_,idmi_axi_)
   );


  `AXIASG_EXT(cfg_axi_,npu_cfg_axi_);

  //
  // Initiator part of asynchronous bridge on configuration slave ports
  //
  npu_axi_async_ini
  #(
    .AXIIDW         ( `NPU_AXI_TARGET_ID_WIDTH ),
    .AXIDW          ( 32                       ),
    .AXIAWUW        ( 1                        ),
    .AXIWUW         ( 1                        ),
    .AXIBUW         ( 1                        ),
    .AXIARUW        ( 1                        ),
    .AXIRUW         ( 1                        ),
    .AWFIFO_DEPTHL2 ( 0                        ),
    .WFIFO_DEPTHL2  ( 0                        ),
    .BFIFO_DEPTHL2  ( 0                        ),
    .ARFIFO_DEPTHL2 ( 0                        ),
    .RFIFO_DEPTHL2  ( 0                        )
  )
  u_axi_cfg_ini_inst
  (
    .axi_slv_clk          ( npu_cfg_clk               ), 
    .axi_slv_rst_a        ( npu_cfg_rst_a             ),
    .tgt_pwr_dwn_a        ( nl2arc_pwr_dwn_a        ),  
    .test_mode            ( test_mode                 ),
    `AXIINST(axi_slv_,icfg_axi_),
    `AXIASYNCMSUB(axi_async_mst_,cfg_axi_gals_)
   );  

  //
  // Register slice on configuration slave ports
  //
  npu_axi_slice
  #(
    .AXIIDW       ( `NPU_AXI_TARGET_ID_WIDTH ),
    .AXIDW        ( 32                       ),
    .AXIAWUW      ( 1                        ),
    .AXIWUW       ( 1                        ),
    .AXIBUW       ( 1                        ),
    .AXIARUW      ( 1                        ),
    .AXIRUW       ( 1                        ),
    .NUMSLC       ( 1                        ),
    .AWFIFO_DEPTH ( 0                        ),
    .WFIFO_DEPTH  ( 0                        ),
    .BFIFO_DEPTH  ( 2                        ),
    .ARFIFO_DEPTH ( 0                        ),
    .RFIFO_DEPTH  ( 2                        )
  )
  u_slc_cfg_inst
  (
   .clk                    ( npu_cfg_clk           ),
   .rst_a                  ( npu_cfg_rst_sync      ),
   `AXIINST(axi_slv_,cfg_axi_),
   `AXIINST(axi_mst_,icfg_axi_)
   );
  
  
  assign nl2arc0_dbg_cmdval = '0;
  assign nl2arc0_dbg_pack   = '0;
  assign nl2arc1_dbg_cmdval = '0;
  assign nl2arc1_dbg_pack   = '0;
  assign sl0nl1arc_dbg_cmdval = '0;
  assign sl0nl1arc_dbg_pack   = '0;
  assign sl1nl1arc_dbg_cmdval = '0;
  assign sl1nl1arc_dbg_pack   = '0;
  assign sl2nl1arc_dbg_cmdval = '0;
  assign sl2nl1arc_dbg_pack   = '0;
  assign sl3nl1arc_dbg_cmdval = '0;
  assign sl3nl1arc_dbg_pack   = '0;
  assign sl4nl1arc_dbg_cmdval = '0;
  assign sl4nl1arc_dbg_pack   = '0;
  assign sl5nl1arc_dbg_cmdval = '0;
  assign sl5nl1arc_dbg_pack   = '0;
  assign sl6nl1arc_dbg_cmdval = '0;
  assign sl6nl1arc_dbg_pack   = '0;
  assign sl7nl1arc_dbg_cmdval = '0;
  assign sl7nl1arc_dbg_pack   = '0;
  assign sl8nl1arc_dbg_cmdval = '0;
  assign sl8nl1arc_dbg_pack   = '0;
  assign sl9nl1arc_dbg_cmdval = '0;
  assign sl9nl1arc_dbg_pack   = '0;
  assign sl10nl1arc_dbg_cmdval = '0;
  assign sl10nl1arc_dbg_pack   = '0;
  assign sl11nl1arc_dbg_cmdval = '0;
  assign sl11nl1arc_dbg_pack   = '0;
  assign sl12nl1arc_dbg_cmdval = '0;
  assign sl12nl1arc_dbg_pack   = '0;
  assign sl13nl1arc_dbg_cmdval = '0;
  assign sl13nl1arc_dbg_pack   = '0;
  assign sl14nl1arc_dbg_cmdval = '0;
  assign sl14nl1arc_dbg_pack   = '0;
  assign sl15nl1arc_dbg_cmdval = '0;
  assign sl15nl1arc_dbg_pack   = '0;


//BUS ECC



   assign  nl2arc0_arcnum = 8'd0;
   assign  sl0nl1arc_arcnum = 8'd1;
   assign  sl1nl1arc_arcnum = 8'd2;
   assign  sl2nl1arc_arcnum = 8'd3;
   assign  sl3nl1arc_arcnum = 8'd4;
   assign  sl4nl1arc_arcnum = 8'd5;
   assign  sl5nl1arc_arcnum = 8'd6;
   assign  sl6nl1arc_arcnum = 8'd7;
   assign  sl7nl1arc_arcnum = 8'd8;
   assign  sl8nl1arc_arcnum = 8'd9;
   assign  sl9nl1arc_arcnum = 8'd10;
   assign  sl10nl1arc_arcnum = 8'd11;
   assign  sl11nl1arc_arcnum = 8'd12;
   assign  sl12nl1arc_arcnum = 8'd13;
   assign  sl13nl1arc_arcnum = 8'd14;
   assign  sl14nl1arc_arcnum = 8'd15;
   assign  sl15nl1arc_arcnum = 8'd16;
   assign  nl2arc1_arcnum = 8'd17;

  assign grp0_evt_vm_irq  =   1'b0
                             ||  sl0nl1arc_evt_vm_irq_a
                             ||  sl1nl1arc_evt_vm_irq_a
                             ||  sl2nl1arc_evt_vm_irq_a
                             ||  sl3nl1arc_evt_vm_irq_a
                             ||  stu_err_irq_a[0]
                             ||  stu_err_irq_a[1]
                             ;

  assign grp1_evt_vm_irq  =   1'b0
                             ||  sl4nl1arc_evt_vm_irq_a
                             ||  sl5nl1arc_evt_vm_irq_a
                             ||  sl6nl1arc_evt_vm_irq_a
                             ||  sl7nl1arc_evt_vm_irq_a
                             ||  stu_err_irq_a[2]
                             ||  stu_err_irq_a[3]
                             ;

  assign grp2_evt_vm_irq  =   1'b0
                             ||  sl8nl1arc_evt_vm_irq_a
                             ||  sl9nl1arc_evt_vm_irq_a
                             ||  sl10nl1arc_evt_vm_irq_a
                             ||  sl11nl1arc_evt_vm_irq_a
                             ||  stu_err_irq_a[4]
                             ||  stu_err_irq_a[5]
                             ;

  assign grp3_evt_vm_irq  =   1'b0
                             ||  sl12nl1arc_evt_vm_irq_a
                             ||  sl13nl1arc_evt_vm_irq_a
                             ||  sl14nl1arc_evt_vm_irq_a
                             ||  sl15nl1arc_evt_vm_irq_a
                             ||  stu_err_irq_a[6]
                             ||  stu_err_irq_a[7]
                             ;


  logic [19-1:0]       arc_psel_port;    
  logic [19-1:0]       arc_penable_port; 
  logic [19-1:0][15:2] arc_paddr_port;   
  logic [19-1:0]       arc_pwrite_port;  
  logic [19-1:0][31:0] arc_pwdata_port;  
  logic [19-1:0]       arc_pready_port;
  logic [19-1:0][31:0] arc_prdata_port;  
  logic [19-1:0]       arc_pslverr_port;          


  //
  // APB bridge to ARCtrace
  //
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_arct_apb_async_bridge_rtt_inst
  (
   .pclk          ( arct_clk             ),
   .rst_a         ( ~arct_rst_an         ),
   .tgt_pwr_dwn_a ( nl2arc_pwr_dwn_a   ),
   .test_mode     ( test_mode            ),
   .ini_psel      ( arc_psel_port[0]    ),
   .ini_penable   ( arc_penable_port[0] ),
   .ini_paddr     ( arc_paddr_port[0]   ),
   .ini_pwrite    ( arc_pwrite_port[0]  ),
   .ini_pwdata    ( arc_pwdata_port[0]  ),
   .ini_pready    ( arc_pready_port[0]  ),
   .ini_prdata    ( arc_prdata_port[0]  ),
   .ini_pslverr   ( arc_pslverr_port[0] ),
   `APBASYNCINST(brg_,arct_syn_)
  );

  //
  // APB bridge to L2ARC0 debug port
  //
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_nl2arc0_apb_async_bridge_inst
  (
   .pclk          ( arct_clk             ),
   .rst_a         ( ~arct_rst_an         ),
   .tgt_pwr_dwn_a ( nl2arc_pwr_dwn_a   ),
   .test_mode     ( test_mode            ),
   .ini_psel      ( arc_psel_port[1]    ),
   .ini_penable   ( arc_penable_port[1] ),
   .ini_paddr     ( arc_paddr_port[1]   ),
   .ini_pwrite    ( arc_pwrite_port[1]  ),
   .ini_pwdata    ( arc_pwdata_port[1]  ),
   .ini_pready    ( arc_pready_port[1]  ),
   .ini_prdata    ( arc_prdata_port[1]  ),
   .ini_pslverr   ( arc_pslverr_port[1] ),
   `APBASYNCINST(brg_,nl2arc0_)
  );

  //
  // APB bridge to L2ARC1 debug port
  //
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_nl2arc1_apb_async_bridge_inst
  (
   .pclk          ( arct_clk             ),
   .rst_a         ( ~arct_rst_an         ),
   .tgt_pwr_dwn_a ( nl2arc_pwr_dwn_a   ),
   .test_mode     ( test_mode            ),
   .ini_psel      ( arc_psel_port[2]    ),
   .ini_penable   ( arc_penable_port[2] ),
   .ini_paddr     ( arc_paddr_port[2]   ),
   .ini_pwrite    ( arc_pwrite_port[2]  ),
   .ini_pwdata    ( arc_pwdata_port[2]  ),
   .ini_pready    ( arc_pready_port[2]  ),
   .ini_prdata    ( arc_prdata_port[2]  ),
   .ini_pslverr   ( arc_pslverr_port[2] ),
   `APBASYNCINST(brg_,nl2arc1_)
  );
 
  //
  // APB bridges to debug port of L1ARC cores
  //
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl0_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl0nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[3]        ),
  .ini_penable   ( arc_penable_port[3]     ),
  .ini_paddr     ( arc_paddr_port[3]       ),
  .ini_pwrite    ( arc_pwrite_port[3]      ),
  .ini_pwdata    ( arc_pwdata_port[3]      ),
  .ini_prdata    ( arc_prdata_port[3]      ),
  .ini_pslverr   ( arc_pslverr_port[3]     ),
  .ini_pready    ( arc_pready_port[3]      ),
  `APBASYNCINST(brg_,sl0nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl1_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl1nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[4]        ),
  .ini_penable   ( arc_penable_port[4]     ),
  .ini_paddr     ( arc_paddr_port[4]       ),
  .ini_pwrite    ( arc_pwrite_port[4]      ),
  .ini_pwdata    ( arc_pwdata_port[4]      ),
  .ini_prdata    ( arc_prdata_port[4]      ),
  .ini_pslverr   ( arc_pslverr_port[4]     ),
  .ini_pready    ( arc_pready_port[4]      ),
  `APBASYNCINST(brg_,sl1nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl2_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl2nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[5]        ),
  .ini_penable   ( arc_penable_port[5]     ),
  .ini_paddr     ( arc_paddr_port[5]       ),
  .ini_pwrite    ( arc_pwrite_port[5]      ),
  .ini_pwdata    ( arc_pwdata_port[5]      ),
  .ini_prdata    ( arc_prdata_port[5]      ),
  .ini_pslverr   ( arc_pslverr_port[5]     ),
  .ini_pready    ( arc_pready_port[5]      ),
  `APBASYNCINST(brg_,sl2nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl3_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl3nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[6]        ),
  .ini_penable   ( arc_penable_port[6]     ),
  .ini_paddr     ( arc_paddr_port[6]       ),
  .ini_pwrite    ( arc_pwrite_port[6]      ),
  .ini_pwdata    ( arc_pwdata_port[6]      ),
  .ini_prdata    ( arc_prdata_port[6]      ),
  .ini_pslverr   ( arc_pslverr_port[6]     ),
  .ini_pready    ( arc_pready_port[6]      ),
  `APBASYNCINST(brg_,sl3nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl4_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl4nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[7]        ),
  .ini_penable   ( arc_penable_port[7]     ),
  .ini_paddr     ( arc_paddr_port[7]       ),
  .ini_pwrite    ( arc_pwrite_port[7]      ),
  .ini_pwdata    ( arc_pwdata_port[7]      ),
  .ini_prdata    ( arc_prdata_port[7]      ),
  .ini_pslverr   ( arc_pslverr_port[7]     ),
  .ini_pready    ( arc_pready_port[7]      ),
  `APBASYNCINST(brg_,sl4nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl5_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl5nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[8]        ),
  .ini_penable   ( arc_penable_port[8]     ),
  .ini_paddr     ( arc_paddr_port[8]       ),
  .ini_pwrite    ( arc_pwrite_port[8]      ),
  .ini_pwdata    ( arc_pwdata_port[8]      ),
  .ini_prdata    ( arc_prdata_port[8]      ),
  .ini_pslverr   ( arc_pslverr_port[8]     ),
  .ini_pready    ( arc_pready_port[8]      ),
  `APBASYNCINST(brg_,sl5nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl6_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl6nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[9]        ),
  .ini_penable   ( arc_penable_port[9]     ),
  .ini_paddr     ( arc_paddr_port[9]       ),
  .ini_pwrite    ( arc_pwrite_port[9]      ),
  .ini_pwdata    ( arc_pwdata_port[9]      ),
  .ini_prdata    ( arc_prdata_port[9]      ),
  .ini_pslverr   ( arc_pslverr_port[9]     ),
  .ini_pready    ( arc_pready_port[9]      ),
  `APBASYNCINST(brg_,sl6nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl7_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl7nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[10]        ),
  .ini_penable   ( arc_penable_port[10]     ),
  .ini_paddr     ( arc_paddr_port[10]       ),
  .ini_pwrite    ( arc_pwrite_port[10]      ),
  .ini_pwdata    ( arc_pwdata_port[10]      ),
  .ini_prdata    ( arc_prdata_port[10]      ),
  .ini_pslverr   ( arc_pslverr_port[10]     ),
  .ini_pready    ( arc_pready_port[10]      ),
  `APBASYNCINST(brg_,sl7nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl8_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl8nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[11]        ),
  .ini_penable   ( arc_penable_port[11]     ),
  .ini_paddr     ( arc_paddr_port[11]       ),
  .ini_pwrite    ( arc_pwrite_port[11]      ),
  .ini_pwdata    ( arc_pwdata_port[11]      ),
  .ini_prdata    ( arc_prdata_port[11]      ),
  .ini_pslverr   ( arc_pslverr_port[11]     ),
  .ini_pready    ( arc_pready_port[11]      ),
  `APBASYNCINST(brg_,sl8nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl9_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl9nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[12]        ),
  .ini_penable   ( arc_penable_port[12]     ),
  .ini_paddr     ( arc_paddr_port[12]       ),
  .ini_pwrite    ( arc_pwrite_port[12]      ),
  .ini_pwdata    ( arc_pwdata_port[12]      ),
  .ini_prdata    ( arc_prdata_port[12]      ),
  .ini_pslverr   ( arc_pslverr_port[12]     ),
  .ini_pready    ( arc_pready_port[12]      ),
  `APBASYNCINST(brg_,sl9nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl10_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl10nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[13]        ),
  .ini_penable   ( arc_penable_port[13]     ),
  .ini_paddr     ( arc_paddr_port[13]       ),
  .ini_pwrite    ( arc_pwrite_port[13]      ),
  .ini_pwdata    ( arc_pwdata_port[13]      ),
  .ini_prdata    ( arc_prdata_port[13]      ),
  .ini_pslverr   ( arc_pslverr_port[13]     ),
  .ini_pready    ( arc_pready_port[13]      ),
  `APBASYNCINST(brg_,sl10nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl11_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl11nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[14]        ),
  .ini_penable   ( arc_penable_port[14]     ),
  .ini_paddr     ( arc_paddr_port[14]       ),
  .ini_pwrite    ( arc_pwrite_port[14]      ),
  .ini_pwdata    ( arc_pwdata_port[14]      ),
  .ini_prdata    ( arc_prdata_port[14]      ),
  .ini_pslverr   ( arc_pslverr_port[14]     ),
  .ini_pready    ( arc_pready_port[14]      ),
  `APBASYNCINST(brg_,sl11nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl12_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl12nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[15]        ),
  .ini_penable   ( arc_penable_port[15]     ),
  .ini_paddr     ( arc_paddr_port[15]       ),
  .ini_pwrite    ( arc_pwrite_port[15]      ),
  .ini_pwdata    ( arc_pwdata_port[15]      ),
  .ini_prdata    ( arc_prdata_port[15]      ),
  .ini_pslverr   ( arc_pslverr_port[15]     ),
  .ini_pready    ( arc_pready_port[15]      ),
  `APBASYNCINST(brg_,sl12nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl13_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl13nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[16]        ),
  .ini_penable   ( arc_penable_port[16]     ),
  .ini_paddr     ( arc_paddr_port[16]       ),
  .ini_pwrite    ( arc_pwrite_port[16]      ),
  .ini_pwdata    ( arc_pwdata_port[16]      ),
  .ini_prdata    ( arc_prdata_port[16]      ),
  .ini_pslverr   ( arc_pslverr_port[16]     ),
  .ini_pready    ( arc_pready_port[16]      ),
  `APBASYNCINST(brg_,sl13nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl14_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl14nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[17]        ),
  .ini_penable   ( arc_penable_port[17]     ),
  .ini_paddr     ( arc_paddr_port[17]       ),
  .ini_pwrite    ( arc_pwrite_port[17]      ),
  .ini_pwdata    ( arc_pwdata_port[17]      ),
  .ini_prdata    ( arc_prdata_port[17]      ),
  .ini_pslverr   ( arc_pslverr_port[17]     ),
  .ini_pready    ( arc_pready_port[17]      ),
  `APBASYNCINST(brg_,sl14nl1arc_)
  );
  npu_apb_bridge_ini
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_async_sl15_inst
  (
  .pclk          ( arct_clk                 ),
  .rst_a         (  ~arct_rst_an            ),
  .tgt_pwr_dwn_a ( sl15nl1arc_pwr_dwn_a ),
  .test_mode     ( test_mode                ),
  .ini_psel      ( arc_psel_port[18]        ),
  .ini_penable   ( arc_penable_port[18]     ),
  .ini_paddr     ( arc_paddr_port[18]       ),
  .ini_pwrite    ( arc_pwrite_port[18]      ),
  .ini_pwdata    ( arc_pwdata_port[18]      ),
  .ini_prdata    ( arc_prdata_port[18]      ),
  .ini_pslverr   ( arc_pslverr_port[18]     ),
  .ini_pready    ( arc_pready_port[18]      ),
  `APBASYNCINST(brg_,sl15nl1arc_)
  );

  //
  // APB coresight interface
  //
  arct_apb_ic
  #(
    .CLIENTS     ( `NPU_SLICE_NUM + `NPU_HAS_L2ARC + `DUO_L2ARC + `NPU_ARC_TRACE ),
    .ADDR_OFFSET ( 0 )
  )
  u_dw_apbic_inst
  (
   .clk          ( arct_clk         ),
   .rst_a        ( ~arct_rst_an     ),
   .test_mode    ( test_mode        ),
   .i_psel       ( arct_psel        ),
   .i_penable    ( arct_penable     ),
   .i_paddr      ( arct_paddr       ),
   .i_pwrite     ( arct_pwrite      ),
   .i_pwdata     ( arct_pwdata      ),
   .i_pready     ( arct_pready      ),
   .i_prdata     ( arct_prdata      ),
   .i_pslverr    ( arct_pslverr     ),
   .o_psel       ( arc_psel_port    ),
   .o_penable    ( arc_penable_port ), 
   .o_paddr      ( arc_paddr_port   ),
   .o_pwrite     ( arc_pwrite_port  ),
   .o_pwdata     ( arc_pwdata_port  ),   
   .o_pready     ( arc_pready_port  ),
   .o_prdata     ( arc_prdata_port  ), 
   .o_pslverr    ( arc_pslverr_port )
  );                                             


endmodule : npu_top_aon


