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



module npu_core_aon
  import npu_types::*;
  import npu_ecc_types::*;
(
  // per group clock enable, power-down and reset (at main clock)
  input  logic                          grp0_rst_a,
  input  logic                          grp1_rst_a,
  input  logic                          grp2_rst_a,
  input  logic                          grp3_rst_a,
  output  logic  [7:0]                   nl2arc0_arcnum,
  `APBASYNCINI(16,32,nl2arc0_),
  output  logic  [7:0]                   nl2arc1_arcnum,
  `APBASYNCINI(16,32,nl2arc1_),

  output logic                          grp0_evt_vm_irq,
  output logic                          grp1_evt_vm_irq,
  output logic                          grp2_evt_vm_irq,
  output logic                          grp3_evt_vm_irq,

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

  // STU events and interrupts
  input   logic  [`NPU_STU_CHAN_NUM-1:0] stu_err_irq_a,

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

  `AXIASYNCSLV(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp0_noc_axi_gals_),
  `AXIASYNCSLV(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp1_noc_axi_gals_),
  `AXIASYNCSLV(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp2_noc_axi_gals_),
  `AXIASYNCSLV(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp3_noc_axi_gals_),

  // DMI slave interfaces
  `AXIASYNCMST(`NPU_AXI_TARGET_ID_WIDTH,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,dmi0_axi_gals_),
  // configuration slave AXI
  `AXIASYNCMST(`NPU_AXI_TARGET_ID_WIDTH,32,1,1,1,1,1,0,0,0,0,0,cfg_axi_gals_),

  output  logic  [7:0]                   sl0nl1arc_arcnum,
  input   logic                          sl0nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl0nl1arc_dbg_),
  output  logic  [7:0]                   sl1nl1arc_arcnum,
  input   logic                          sl1nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl1nl1arc_dbg_),
  output  logic  [7:0]                   sl2nl1arc_arcnum,
  input   logic                          sl2nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl2nl1arc_dbg_),
  output  logic  [7:0]                   sl3nl1arc_arcnum,
  input   logic                          sl3nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl3nl1arc_dbg_),
  output  logic  [7:0]                   sl4nl1arc_arcnum,
  input   logic                          sl4nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl4nl1arc_dbg_),
  output  logic  [7:0]                   sl5nl1arc_arcnum,
  input   logic                          sl5nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl5nl1arc_dbg_),
  output  logic  [7:0]                   sl6nl1arc_arcnum,
  input   logic                          sl6nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl6nl1arc_dbg_),
  output  logic  [7:0]                   sl7nl1arc_arcnum,
  input   logic                          sl7nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl7nl1arc_dbg_),
  output  logic  [7:0]                   sl8nl1arc_arcnum,
  input   logic                          sl8nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl8nl1arc_dbg_),
  output  logic  [7:0]                   sl9nl1arc_arcnum,
  input   logic                          sl9nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl9nl1arc_dbg_),
  output  logic  [7:0]                   sl10nl1arc_arcnum,
  input   logic                          sl10nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl10nl1arc_dbg_),
  output  logic  [7:0]                   sl11nl1arc_arcnum,
  input   logic                          sl11nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl11nl1arc_dbg_),
  output  logic  [7:0]                   sl12nl1arc_arcnum,
  input   logic                          sl12nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl12nl1arc_dbg_),
  output  logic  [7:0]                   sl13nl1arc_arcnum,
  input   logic                          sl13nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl13nl1arc_dbg_),
  output  logic  [7:0]                   sl14nl1arc_arcnum,
  input   logic                          sl14nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl14nl1arc_dbg_),
  output  logic  [7:0]                   sl15nl1arc_arcnum,
  input   logic                          sl15nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl15nl1arc_dbg_),
  input   logic                          arct_clk,
  input   logic                          arct_rst_an,
  `APBSLV(32,32,arct_),
  input   logic [`NPU_SLICE_NUM-1:0][`NPU_SLICE_NUM-1:0] l1_peer_event_out,
  output  logic [`NPU_SLICE_NUM-1:0][`NPU_SLICE_NUM-1:0] l1_peer_event_in,
  // Async bridge && reset ctrl
  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
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


  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
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

  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
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

  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
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

  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
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
  input   logic                          npu_core_clk,
  input   logic                          npu_core_rst_a


);

  localparam int L2IDW  = 2+$clog2(`NPU_AXI_TARGETS+1);
  localparam int CCMIDW = 1;

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

  npu_top_aon 
  u_npu_top_aon
   (
      .npu_core_clk                    ( npu_core_clk                )
    , .npu_core_rst_a                  ( npu_core_rst_a              )
    , .nl2arc0_arcnum             ( nl2arc0_arcnum         )
    , .nl2arc1_arcnum             ( nl2arc1_arcnum         )
    , .grp0_evt_vm_irq              ( grp0_evt_vm_irq          )
    , .grp1_evt_vm_irq              ( grp1_evt_vm_irq          )
    , .grp2_evt_vm_irq              ( grp2_evt_vm_irq          )
    , .grp3_evt_vm_irq              ( grp3_evt_vm_irq          )
    , `APBASYNCINST(sl0nl1arc_,sl0nl1arc_dbg_)
    , `APBASYNCINST(sl1nl1arc_,sl1nl1arc_dbg_)
    , `APBASYNCINST(sl2nl1arc_,sl2nl1arc_dbg_)
    , `APBASYNCINST(sl3nl1arc_,sl3nl1arc_dbg_)
    , `APBASYNCINST(sl4nl1arc_,sl4nl1arc_dbg_)
    , `APBASYNCINST(sl5nl1arc_,sl5nl1arc_dbg_)
    , `APBASYNCINST(sl6nl1arc_,sl6nl1arc_dbg_)
    , `APBASYNCINST(sl7nl1arc_,sl7nl1arc_dbg_)
    , `APBASYNCINST(sl8nl1arc_,sl8nl1arc_dbg_)
    , `APBASYNCINST(sl9nl1arc_,sl9nl1arc_dbg_)
    , `APBASYNCINST(sl10nl1arc_,sl10nl1arc_dbg_)
    , `APBASYNCINST(sl11nl1arc_,sl11nl1arc_dbg_)
    , `APBASYNCINST(sl12nl1arc_,sl12nl1arc_dbg_)
    , `APBASYNCINST(sl13nl1arc_,sl13nl1arc_dbg_)
    , `APBASYNCINST(sl14nl1arc_,sl14nl1arc_dbg_)
    , `APBASYNCINST(sl15nl1arc_,sl15nl1arc_dbg_)
    ,.arct_clk                         ( arct_clk                    )
    ,.arct_rst_an                      ( arct_rst_an                 )
    ,`APBINST(arct_,arct_)
    ,`APBASYNCINST(nl2arc0_,nl2arc0_)
    ,`APBASYNCINST(nl2arc1_,nl2arc1_)
    , .sl0nl1arc_arcnum           ( sl0nl1arc_arcnum       )
    , .sl0nl1arc_evt_vm_irq_a     ( sl0nl1arc_evt_vm_irq_a )
    , .sl0nl1arc_pwr_dwn_a        ( sl0nl1arc_pwr_dwn_a    )
    , .sl1nl1arc_arcnum           ( sl1nl1arc_arcnum       )
    , .sl1nl1arc_evt_vm_irq_a     ( sl1nl1arc_evt_vm_irq_a )
    , .sl1nl1arc_pwr_dwn_a        ( sl1nl1arc_pwr_dwn_a    )
    , .sl2nl1arc_arcnum           ( sl2nl1arc_arcnum       )
    , .sl2nl1arc_evt_vm_irq_a     ( sl2nl1arc_evt_vm_irq_a )
    , .sl2nl1arc_pwr_dwn_a        ( sl2nl1arc_pwr_dwn_a    )
    , .sl3nl1arc_arcnum           ( sl3nl1arc_arcnum       )
    , .sl3nl1arc_evt_vm_irq_a     ( sl3nl1arc_evt_vm_irq_a )
    , .sl3nl1arc_pwr_dwn_a        ( sl3nl1arc_pwr_dwn_a    )
    , .sl4nl1arc_arcnum           ( sl4nl1arc_arcnum       )
    , .sl4nl1arc_evt_vm_irq_a     ( sl4nl1arc_evt_vm_irq_a )
    , .sl4nl1arc_pwr_dwn_a        ( sl4nl1arc_pwr_dwn_a    )
    , .sl5nl1arc_arcnum           ( sl5nl1arc_arcnum       )
    , .sl5nl1arc_evt_vm_irq_a     ( sl5nl1arc_evt_vm_irq_a )
    , .sl5nl1arc_pwr_dwn_a        ( sl5nl1arc_pwr_dwn_a    )
    , .sl6nl1arc_arcnum           ( sl6nl1arc_arcnum       )
    , .sl6nl1arc_evt_vm_irq_a     ( sl6nl1arc_evt_vm_irq_a )
    , .sl6nl1arc_pwr_dwn_a        ( sl6nl1arc_pwr_dwn_a    )
    , .sl7nl1arc_arcnum           ( sl7nl1arc_arcnum       )
    , .sl7nl1arc_evt_vm_irq_a     ( sl7nl1arc_evt_vm_irq_a )
    , .sl7nl1arc_pwr_dwn_a        ( sl7nl1arc_pwr_dwn_a    )
    , .sl8nl1arc_arcnum           ( sl8nl1arc_arcnum       )
    , .sl8nl1arc_evt_vm_irq_a     ( sl8nl1arc_evt_vm_irq_a )
    , .sl8nl1arc_pwr_dwn_a        ( sl8nl1arc_pwr_dwn_a    )
    , .sl9nl1arc_arcnum           ( sl9nl1arc_arcnum       )
    , .sl9nl1arc_evt_vm_irq_a     ( sl9nl1arc_evt_vm_irq_a )
    , .sl9nl1arc_pwr_dwn_a        ( sl9nl1arc_pwr_dwn_a    )
    , .sl10nl1arc_arcnum           ( sl10nl1arc_arcnum       )
    , .sl10nl1arc_evt_vm_irq_a     ( sl10nl1arc_evt_vm_irq_a )
    , .sl10nl1arc_pwr_dwn_a        ( sl10nl1arc_pwr_dwn_a    )
    , .sl11nl1arc_arcnum           ( sl11nl1arc_arcnum       )
    , .sl11nl1arc_evt_vm_irq_a     ( sl11nl1arc_evt_vm_irq_a )
    , .sl11nl1arc_pwr_dwn_a        ( sl11nl1arc_pwr_dwn_a    )
    , .sl12nl1arc_arcnum           ( sl12nl1arc_arcnum       )
    , .sl12nl1arc_evt_vm_irq_a     ( sl12nl1arc_evt_vm_irq_a )
    , .sl12nl1arc_pwr_dwn_a        ( sl12nl1arc_pwr_dwn_a    )
    , .sl13nl1arc_arcnum           ( sl13nl1arc_arcnum       )
    , .sl13nl1arc_evt_vm_irq_a     ( sl13nl1arc_evt_vm_irq_a )
    , .sl13nl1arc_pwr_dwn_a        ( sl13nl1arc_pwr_dwn_a    )
    , .sl14nl1arc_arcnum           ( sl14nl1arc_arcnum       )
    , .sl14nl1arc_evt_vm_irq_a     ( sl14nl1arc_evt_vm_irq_a )
    , .sl14nl1arc_pwr_dwn_a        ( sl14nl1arc_pwr_dwn_a    )
    , .sl15nl1arc_arcnum           ( sl15nl1arc_arcnum       )
    , .sl15nl1arc_evt_vm_irq_a     ( sl15nl1arc_evt_vm_irq_a )
    , .sl15nl1arc_pwr_dwn_a        ( sl15nl1arc_pwr_dwn_a    )
    , .grp0_pwr_dwn_a               ( grp0_pwr_dwn_a           )
    , .grp1_pwr_dwn_a               ( grp1_pwr_dwn_a           )
    , .grp2_pwr_dwn_a               ( grp2_pwr_dwn_a           )
    , .grp3_pwr_dwn_a               ( grp3_pwr_dwn_a           )
    , .nl2arc_pwr_dwn_a           ( nl2arc_pwr_dwn_a       )
    // ARC_Trace
    , `APBASYNCINST(arct_syn_,arct_syn_)
    , .grp4_rtt_swe_val             ( grp4_rtt_swe_val         )
    , .grp4_rtt_swe_data            ( grp4_rtt_swe_data        )
    , .grp4_rtt_swe_ext             ( grp4_rtt_swe_ext         )
    , .grp5_rtt_swe_val             ( grp5_rtt_swe_val         )
    , .grp5_rtt_swe_data            ( grp5_rtt_swe_data        )
    , .grp5_rtt_swe_ext             ( grp5_rtt_swe_ext         )
    , .grp6_rtt_swe_val             ( grp6_rtt_swe_val         )
    , .grp6_rtt_swe_data            ( grp6_rtt_swe_data        )
    , .grp6_rtt_swe_ext             ( grp6_rtt_swe_ext         )
    , .grp7_rtt_swe_val             ( grp7_rtt_swe_val         )
    , .grp7_rtt_swe_data            ( grp7_rtt_swe_data        )
    , .grp7_rtt_swe_ext             ( grp7_rtt_swe_ext         )
    , .grp8_rtt_swe_val             ( grp8_rtt_swe_val         )
    , .grp8_rtt_swe_data            ( grp8_rtt_swe_data        )
    , .grp8_rtt_swe_ext             ( grp8_rtt_swe_ext         )
    , .grp9_rtt_swe_val             ( grp9_rtt_swe_val         )
    , .grp9_rtt_swe_data            ( grp9_rtt_swe_data        )
    , .grp9_rtt_swe_ext             ( grp9_rtt_swe_ext         )
    , .grp10_rtt_swe_val             ( grp10_rtt_swe_val         )
    , .grp10_rtt_swe_data            ( grp10_rtt_swe_data        )
    , .grp10_rtt_swe_ext             ( grp10_rtt_swe_ext         )
    , .grp11_rtt_swe_val             ( grp11_rtt_swe_val         )
    , .grp11_rtt_swe_data            ( grp11_rtt_swe_data        )
    , .grp11_rtt_swe_ext             ( grp11_rtt_swe_ext         )
    , .grp12_rtt_swe_val             ( grp12_rtt_swe_val         )
    , .grp12_rtt_swe_data            ( grp12_rtt_swe_data        )
    , .grp12_rtt_swe_ext             ( grp12_rtt_swe_ext         )
    , .grp13_rtt_swe_val             ( grp13_rtt_swe_val         )
    , .grp13_rtt_swe_data            ( grp13_rtt_swe_data        )
    , .grp13_rtt_swe_ext             ( grp13_rtt_swe_ext         )
    , .grp14_rtt_swe_val             ( grp14_rtt_swe_val         )
    , .grp14_rtt_swe_data            ( grp14_rtt_swe_data        )
    , .grp14_rtt_swe_ext             ( grp14_rtt_swe_ext         )
    , .grp15_rtt_swe_val             ( grp15_rtt_swe_val         )
    , .grp15_rtt_swe_data            ( grp15_rtt_swe_data        )
    , .grp15_rtt_swe_ext             ( grp15_rtt_swe_ext         )
    , .grp16_rtt_swe_val             ( grp16_rtt_swe_val         )
    , .grp16_rtt_swe_data            ( grp16_rtt_swe_data        )
    , .grp16_rtt_swe_ext             ( grp16_rtt_swe_ext         )
// spyglass disable_block NoFeedThrus-ML
// SMD: No Feed Through
// SJ: Event Only shuffled in AON, has been registered in destination
    , .l1_peer_event_out               ( l1_peer_event_out           )
    , .l1_peer_event_in                ( l1_peer_event_in            )
// spyglass enable_block NoFeedThrus-ML
    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst17_axi
    // read command channel
  , .npu_mst_axi_arvalid            (npu_mst0_axi_arvalid)     // read command valid
  , .npu_mst_axi_arready            (npu_mst0_axi_arready)     // read command accept
  , .npu_mst_axi_arid               (npu_mst0_axi_arid   )     // read command ID
  , .npu_mst_axi_araddr  (npu_mst0_axi_araddr  )   // read command
  , .npu_mst_axi_arcache (npu_mst0_axi_arcache )   // read command
  , .npu_mst_axi_arprot  (npu_mst0_axi_arprot  )   // read command
  , .npu_mst_axi_arlock  (npu_mst0_axi_arlock  )   // read command
  , .npu_mst_axi_arburst (npu_mst0_axi_arburst )   // read command
  , .npu_mst_axi_arlen   (npu_mst0_axi_arlen   )   // read command
  , .npu_mst_axi_arsize  (npu_mst0_axi_arsize  )   // read command
  , .npu_mst_axi_rvalid  (npu_mst0_axi_rvalid )    // read data valid
  , .npu_mst_axi_rready  (npu_mst0_axi_rready )    // read data accept
  , .npu_mst_axi_rid     (npu_mst0_axi_rid    )    // read data id
  , .npu_mst_axi_rdata   (npu_mst0_axi_rdata  )    // read data
  , .npu_mst_axi_rresp   (npu_mst0_axi_rresp)    // read response
  , .npu_mst_axi_rlast   (npu_mst0_axi_rlast  )    // read last
  , .npu_mst_axi_awvalid (npu_mst0_axi_awvalid )   // write command valid
  , .npu_mst_axi_awready (npu_mst0_axi_awready )   // write command accept
  , .npu_mst_axi_awid    (npu_mst0_axi_awid    )   // write command ID
  , .npu_mst_axi_awaddr  (npu_mst0_axi_awaddr  )   // read command
  , .npu_mst_axi_awcache (npu_mst0_axi_awcache )   // read command
  , .npu_mst_axi_awprot  (npu_mst0_axi_awprot  )   // read command
  , .npu_mst_axi_awlock  (npu_mst0_axi_awlock  )   // read command
  , .npu_mst_axi_awburst (npu_mst0_axi_awburst )   // read command
  , .npu_mst_axi_awlen   (npu_mst0_axi_awlen   )   // read command
  , .npu_mst_axi_awsize  (npu_mst0_axi_awsize  )   // read command
  , .npu_mst_axi_wvalid  (npu_mst0_axi_wvalid  )   // write data valid
  , .npu_mst_axi_wready  (npu_mst0_axi_wready  )   // write data accept
  , .npu_mst_axi_wdata   (npu_mst0_axi_wdata   )   // write data
  , .npu_mst_axi_wstrb   (npu_mst0_axi_wstrb   )   // write data strobe
  , .npu_mst_axi_wlast   (npu_mst0_axi_wlast   )   // write data last
  , .npu_mst_axi_bvalid  (npu_mst0_axi_bvalid  )   // write response valid
  , .npu_mst_axi_bready  (npu_mst0_axi_bready  )   // write response accept
  , .npu_mst_axi_bid     (npu_mst0_axi_bid     )   // write response id
  , .npu_mst_axi_bresp   (npu_mst0_axi_bresp)    // read response
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
    , .stu_err_irq_a                   ( stu_err_irq_a               )
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
    // L2 ARC0 debug interface
    , .nl2arc0_dbg_cmdval         ( nl2arc0_dbg_cmdval     )
    , .nl2arc0_dbg_pack           ( nl2arc0_dbg_pack       )
    , .nl2arc0_dbg_resp           ( nl2arc0_dbg_resp       )
    // L2 ARC1 debug interface
    , .nl2arc1_dbg_cmdval         ( nl2arc1_dbg_cmdval     )
    , .nl2arc1_dbg_pack           ( nl2arc1_dbg_pack       )
    , .nl2arc1_dbg_resp           ( nl2arc1_dbg_resp       )
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
    ,
    `AXIASYNCSSUB(l2arc_noc_axi_gals_,l2arc_noc_axi_gals_),
    `AXIASYNCMSUB(dmi0_axi_gals_,dmi0_axi_gals_),
    `AXIASYNCMSUB(cfg_axi_gals_,cfg_axi_gals_),
    .test_mode                        ( test_mode                 )
    );

  //
  // Partition always on domain
  //
  npu_partition_aon
  u_npu_group0_aon
  (
    .npu_noc_clk            ( npu_noc_clk           )
  , .npu_noc_rst_a          ( npu_noc_rst_a         )
  , .grp_clk                ( npu_core_clk          )
  , .grp_rst_a              ( grp0_rst_a         )
  , .grp_pwr_dwn_a          ( grp0_pwr_dwn_a         )

    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst_axi_arvalid            (npu_mst1_axi_arvalid)     // read command valid
  , .npu_mst_axi_arready            (npu_mst1_axi_arready)     // read command accept
  , .npu_mst_axi_arid               (npu_mst1_axi_arid   )     // read command ID
  , .npu_mst_axi_araddr  (npu_mst1_axi_araddr  )   // read command
  , .npu_mst_axi_arcache (npu_mst1_axi_arcache )   // read command
  , .npu_mst_axi_arprot  (npu_mst1_axi_arprot  )   // read command
  , .npu_mst_axi_arlock  (npu_mst1_axi_arlock  )   // read command
  , .npu_mst_axi_arburst (npu_mst1_axi_arburst )   // read command
  , .npu_mst_axi_arlen   (npu_mst1_axi_arlen   )   // read command
  , .npu_mst_axi_arsize  (npu_mst1_axi_arsize  )   // read command
  , .npu_mst_axi_arsid(npu_mst1_axi_arsid)   // read command
  , .npu_mst_axi_arssid(npu_mst1_axi_arssid)   // read command
  , .npu_mst_axi_rvalid  (npu_mst1_axi_rvalid )    // read data valid
  , .npu_mst_axi_rready  (npu_mst1_axi_rready )    // read data accept
  , .npu_mst_axi_rid     (npu_mst1_axi_rid    )    // read data id
  , .npu_mst_axi_rdata   (npu_mst1_axi_rdata  )    // read data
  , .npu_mst_axi_rresp   (npu_mst1_axi_rresp)    // read response
  , .npu_mst_axi_rlast   (npu_mst1_axi_rlast  )    // read last
  , .npu_mst_axi_awvalid (npu_mst1_axi_awvalid )   // write command valid
  , .npu_mst_axi_awready (npu_mst1_axi_awready )   // write command accept
  , .npu_mst_axi_awid    (npu_mst1_axi_awid    )   // write command ID
  , .npu_mst_axi_awaddr  (npu_mst1_axi_awaddr  )   // read command
  , .npu_mst_axi_awcache (npu_mst1_axi_awcache )   // read command
  , .npu_mst_axi_awprot  (npu_mst1_axi_awprot  )   // read command
  , .npu_mst_axi_awlock  (npu_mst1_axi_awlock  )   // read command
  , .npu_mst_axi_awburst (npu_mst1_axi_awburst )   // read command
  , .npu_mst_axi_awlen   (npu_mst1_axi_awlen   )   // read command
  , .npu_mst_axi_awsize  (npu_mst1_axi_awsize  )   // read command
  , .npu_mst_axi_awsid(npu_mst1_axi_awsid)     // read command
  , .npu_mst_axi_awssid(npu_mst1_axi_awssid)   // read command
  , .npu_mst_axi_wvalid  (npu_mst1_axi_wvalid  )   // write data valid
  , .npu_mst_axi_wready  (npu_mst1_axi_wready  )   // write data accept
  , .npu_mst_axi_wdata   (npu_mst1_axi_wdata   )   // write data
  , .npu_mst_axi_wstrb   (npu_mst1_axi_wstrb   )   // write data strobe
  , .npu_mst_axi_wlast   (npu_mst1_axi_wlast   )   // write data last
  , .npu_mst_axi_bvalid  (npu_mst1_axi_bvalid  )   // write response valid
  , .npu_mst_axi_bready  (npu_mst1_axi_bready  )   // write response accept
  , .npu_mst_axi_bid     (npu_mst1_axi_bid     )   // write response id
  , .npu_mst_axi_bresp   (npu_mst1_axi_bresp)    // read response
   , `AXIASYNCSSUB(npu_grp_noc_axi_gals_,npu_grp0_noc_axi_gals_)
   , .test_mode             ( test_mode             )
  );

  //
  // Partition always on domain
  //
  npu_partition_aon
  u_npu_group1_aon
  (
    .npu_noc_clk            ( npu_noc_clk           )
  , .npu_noc_rst_a          ( npu_noc_rst_a         )
  , .grp_clk                ( npu_core_clk          )
  , .grp_rst_a              ( grp1_rst_a         )
  , .grp_pwr_dwn_a          ( grp1_pwr_dwn_a         )

    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst_axi_arvalid            (npu_mst2_axi_arvalid)     // read command valid
  , .npu_mst_axi_arready            (npu_mst2_axi_arready)     // read command accept
  , .npu_mst_axi_arid               (npu_mst2_axi_arid   )     // read command ID
  , .npu_mst_axi_araddr  (npu_mst2_axi_araddr  )   // read command
  , .npu_mst_axi_arcache (npu_mst2_axi_arcache )   // read command
  , .npu_mst_axi_arprot  (npu_mst2_axi_arprot  )   // read command
  , .npu_mst_axi_arlock  (npu_mst2_axi_arlock  )   // read command
  , .npu_mst_axi_arburst (npu_mst2_axi_arburst )   // read command
  , .npu_mst_axi_arlen   (npu_mst2_axi_arlen   )   // read command
  , .npu_mst_axi_arsize  (npu_mst2_axi_arsize  )   // read command
  , .npu_mst_axi_arsid(npu_mst2_axi_arsid)   // read command
  , .npu_mst_axi_arssid(npu_mst2_axi_arssid)   // read command
  , .npu_mst_axi_rvalid  (npu_mst2_axi_rvalid )    // read data valid
  , .npu_mst_axi_rready  (npu_mst2_axi_rready )    // read data accept
  , .npu_mst_axi_rid     (npu_mst2_axi_rid    )    // read data id
  , .npu_mst_axi_rdata   (npu_mst2_axi_rdata  )    // read data
  , .npu_mst_axi_rresp   (npu_mst2_axi_rresp)    // read response
  , .npu_mst_axi_rlast   (npu_mst2_axi_rlast  )    // read last
  , .npu_mst_axi_awvalid (npu_mst2_axi_awvalid )   // write command valid
  , .npu_mst_axi_awready (npu_mst2_axi_awready )   // write command accept
  , .npu_mst_axi_awid    (npu_mst2_axi_awid    )   // write command ID
  , .npu_mst_axi_awaddr  (npu_mst2_axi_awaddr  )   // read command
  , .npu_mst_axi_awcache (npu_mst2_axi_awcache )   // read command
  , .npu_mst_axi_awprot  (npu_mst2_axi_awprot  )   // read command
  , .npu_mst_axi_awlock  (npu_mst2_axi_awlock  )   // read command
  , .npu_mst_axi_awburst (npu_mst2_axi_awburst )   // read command
  , .npu_mst_axi_awlen   (npu_mst2_axi_awlen   )   // read command
  , .npu_mst_axi_awsize  (npu_mst2_axi_awsize  )   // read command
  , .npu_mst_axi_awsid(npu_mst2_axi_awsid)     // read command
  , .npu_mst_axi_awssid(npu_mst2_axi_awssid)   // read command
  , .npu_mst_axi_wvalid  (npu_mst2_axi_wvalid  )   // write data valid
  , .npu_mst_axi_wready  (npu_mst2_axi_wready  )   // write data accept
  , .npu_mst_axi_wdata   (npu_mst2_axi_wdata   )   // write data
  , .npu_mst_axi_wstrb   (npu_mst2_axi_wstrb   )   // write data strobe
  , .npu_mst_axi_wlast   (npu_mst2_axi_wlast   )   // write data last
  , .npu_mst_axi_bvalid  (npu_mst2_axi_bvalid  )   // write response valid
  , .npu_mst_axi_bready  (npu_mst2_axi_bready  )   // write response accept
  , .npu_mst_axi_bid     (npu_mst2_axi_bid     )   // write response id
  , .npu_mst_axi_bresp   (npu_mst2_axi_bresp)    // read response
   , `AXIASYNCSSUB(npu_grp_noc_axi_gals_,npu_grp1_noc_axi_gals_)
   , .test_mode             ( test_mode             )
  );

  //
  // Partition always on domain
  //
  npu_partition_aon
  u_npu_group2_aon
  (
    .npu_noc_clk            ( npu_noc_clk           )
  , .npu_noc_rst_a          ( npu_noc_rst_a         )
  , .grp_clk                ( npu_core_clk          )
  , .grp_rst_a              ( grp2_rst_a         )
  , .grp_pwr_dwn_a          ( grp2_pwr_dwn_a         )

    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst_axi_arvalid            (npu_mst3_axi_arvalid)     // read command valid
  , .npu_mst_axi_arready            (npu_mst3_axi_arready)     // read command accept
  , .npu_mst_axi_arid               (npu_mst3_axi_arid   )     // read command ID
  , .npu_mst_axi_araddr  (npu_mst3_axi_araddr  )   // read command
  , .npu_mst_axi_arcache (npu_mst3_axi_arcache )   // read command
  , .npu_mst_axi_arprot  (npu_mst3_axi_arprot  )   // read command
  , .npu_mst_axi_arlock  (npu_mst3_axi_arlock  )   // read command
  , .npu_mst_axi_arburst (npu_mst3_axi_arburst )   // read command
  , .npu_mst_axi_arlen   (npu_mst3_axi_arlen   )   // read command
  , .npu_mst_axi_arsize  (npu_mst3_axi_arsize  )   // read command
  , .npu_mst_axi_arsid(npu_mst3_axi_arsid)   // read command
  , .npu_mst_axi_arssid(npu_mst3_axi_arssid)   // read command
  , .npu_mst_axi_rvalid  (npu_mst3_axi_rvalid )    // read data valid
  , .npu_mst_axi_rready  (npu_mst3_axi_rready )    // read data accept
  , .npu_mst_axi_rid     (npu_mst3_axi_rid    )    // read data id
  , .npu_mst_axi_rdata   (npu_mst3_axi_rdata  )    // read data
  , .npu_mst_axi_rresp   (npu_mst3_axi_rresp)    // read response
  , .npu_mst_axi_rlast   (npu_mst3_axi_rlast  )    // read last
  , .npu_mst_axi_awvalid (npu_mst3_axi_awvalid )   // write command valid
  , .npu_mst_axi_awready (npu_mst3_axi_awready )   // write command accept
  , .npu_mst_axi_awid    (npu_mst3_axi_awid    )   // write command ID
  , .npu_mst_axi_awaddr  (npu_mst3_axi_awaddr  )   // read command
  , .npu_mst_axi_awcache (npu_mst3_axi_awcache )   // read command
  , .npu_mst_axi_awprot  (npu_mst3_axi_awprot  )   // read command
  , .npu_mst_axi_awlock  (npu_mst3_axi_awlock  )   // read command
  , .npu_mst_axi_awburst (npu_mst3_axi_awburst )   // read command
  , .npu_mst_axi_awlen   (npu_mst3_axi_awlen   )   // read command
  , .npu_mst_axi_awsize  (npu_mst3_axi_awsize  )   // read command
  , .npu_mst_axi_awsid(npu_mst3_axi_awsid)     // read command
  , .npu_mst_axi_awssid(npu_mst3_axi_awssid)   // read command
  , .npu_mst_axi_wvalid  (npu_mst3_axi_wvalid  )   // write data valid
  , .npu_mst_axi_wready  (npu_mst3_axi_wready  )   // write data accept
  , .npu_mst_axi_wdata   (npu_mst3_axi_wdata   )   // write data
  , .npu_mst_axi_wstrb   (npu_mst3_axi_wstrb   )   // write data strobe
  , .npu_mst_axi_wlast   (npu_mst3_axi_wlast   )   // write data last
  , .npu_mst_axi_bvalid  (npu_mst3_axi_bvalid  )   // write response valid
  , .npu_mst_axi_bready  (npu_mst3_axi_bready  )   // write response accept
  , .npu_mst_axi_bid     (npu_mst3_axi_bid     )   // write response id
  , .npu_mst_axi_bresp   (npu_mst3_axi_bresp)    // read response
   , `AXIASYNCSSUB(npu_grp_noc_axi_gals_,npu_grp2_noc_axi_gals_)
   , .test_mode             ( test_mode             )
  );

  //
  // Partition always on domain
  //
  npu_partition_aon
  u_npu_group3_aon
  (
    .npu_noc_clk            ( npu_noc_clk           )
  , .npu_noc_rst_a          ( npu_noc_rst_a         )
  , .grp_clk                ( npu_core_clk          )
  , .grp_rst_a              ( grp3_rst_a         )
  , .grp_pwr_dwn_a          ( grp3_pwr_dwn_a         )

    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst_axi_arvalid            (npu_mst4_axi_arvalid)     // read command valid
  , .npu_mst_axi_arready            (npu_mst4_axi_arready)     // read command accept
  , .npu_mst_axi_arid               (npu_mst4_axi_arid   )     // read command ID
  , .npu_mst_axi_araddr  (npu_mst4_axi_araddr  )   // read command
  , .npu_mst_axi_arcache (npu_mst4_axi_arcache )   // read command
  , .npu_mst_axi_arprot  (npu_mst4_axi_arprot  )   // read command
  , .npu_mst_axi_arlock  (npu_mst4_axi_arlock  )   // read command
  , .npu_mst_axi_arburst (npu_mst4_axi_arburst )   // read command
  , .npu_mst_axi_arlen   (npu_mst4_axi_arlen   )   // read command
  , .npu_mst_axi_arsize  (npu_mst4_axi_arsize  )   // read command
  , .npu_mst_axi_arsid(npu_mst4_axi_arsid)   // read command
  , .npu_mst_axi_arssid(npu_mst4_axi_arssid)   // read command
  , .npu_mst_axi_rvalid  (npu_mst4_axi_rvalid )    // read data valid
  , .npu_mst_axi_rready  (npu_mst4_axi_rready )    // read data accept
  , .npu_mst_axi_rid     (npu_mst4_axi_rid    )    // read data id
  , .npu_mst_axi_rdata   (npu_mst4_axi_rdata  )    // read data
  , .npu_mst_axi_rresp   (npu_mst4_axi_rresp)    // read response
  , .npu_mst_axi_rlast   (npu_mst4_axi_rlast  )    // read last
  , .npu_mst_axi_awvalid (npu_mst4_axi_awvalid )   // write command valid
  , .npu_mst_axi_awready (npu_mst4_axi_awready )   // write command accept
  , .npu_mst_axi_awid    (npu_mst4_axi_awid    )   // write command ID
  , .npu_mst_axi_awaddr  (npu_mst4_axi_awaddr  )   // read command
  , .npu_mst_axi_awcache (npu_mst4_axi_awcache )   // read command
  , .npu_mst_axi_awprot  (npu_mst4_axi_awprot  )   // read command
  , .npu_mst_axi_awlock  (npu_mst4_axi_awlock  )   // read command
  , .npu_mst_axi_awburst (npu_mst4_axi_awburst )   // read command
  , .npu_mst_axi_awlen   (npu_mst4_axi_awlen   )   // read command
  , .npu_mst_axi_awsize  (npu_mst4_axi_awsize  )   // read command
  , .npu_mst_axi_awsid(npu_mst4_axi_awsid)     // read command
  , .npu_mst_axi_awssid(npu_mst4_axi_awssid)   // read command
  , .npu_mst_axi_wvalid  (npu_mst4_axi_wvalid  )   // write data valid
  , .npu_mst_axi_wready  (npu_mst4_axi_wready  )   // write data accept
  , .npu_mst_axi_wdata   (npu_mst4_axi_wdata   )   // write data
  , .npu_mst_axi_wstrb   (npu_mst4_axi_wstrb   )   // write data strobe
  , .npu_mst_axi_wlast   (npu_mst4_axi_wlast   )   // write data last
  , .npu_mst_axi_bvalid  (npu_mst4_axi_bvalid  )   // write response valid
  , .npu_mst_axi_bready  (npu_mst4_axi_bready  )   // write response accept
  , .npu_mst_axi_bid     (npu_mst4_axi_bid     )   // write response id
  , .npu_mst_axi_bresp   (npu_mst4_axi_bresp)    // read response
   , `AXIASYNCSSUB(npu_grp_noc_axi_gals_,npu_grp3_noc_axi_gals_)
   , .test_mode             ( test_mode             )
  );


endmodule : npu_core_aon
