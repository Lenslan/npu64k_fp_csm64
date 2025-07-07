//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2012 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2012, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   alb_mss_fab: MxS bus switch including latency units, and protocol
//                    converters
//
// ===========================================================================
//
// Description:
//  Verilog module defining a switch module
//  Including support for multiple masters, slaves
//  and exclusive access support
//  Masters and slaves can have a mix of protocols (AXI/AHB_Lite/BVCI/APB)
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_mss_fab.vpp
//
// ===========================================================================
`include "alb_mss_fab_defines.v"
`timescale 1ns/10ps
module alb_mss_fab(
                   // Master section
                   // 0: AXI master interface, pref: npu_mst0_axi_, data-width: 64, r/w: rw, excl: 1
                   input   [5-1:0]   npu_mst0_axi_arid,
                   input               npu_mst0_axi_arvalid,
                   output              npu_mst0_axi_arready,
                   input   [40-1:0]   npu_mst0_axi_araddr,
                   input   [1:0]       npu_mst0_axi_arburst,
                   input   [2:0]       npu_mst0_axi_arsize,
                   input               npu_mst0_axi_arlock,
                   input   [4-1:0]   npu_mst0_axi_arlen,
                   input   [3:0]       npu_mst0_axi_arcache,
                   input   [2:0]       npu_mst0_axi_arprot,
                   output  [5-1:0]   npu_mst0_axi_rid,
                   output              npu_mst0_axi_rvalid,
                   input               npu_mst0_axi_rready,
                   output  [64-1:0]   npu_mst0_axi_rdata,
                   output  [1:0]       npu_mst0_axi_rresp,
                   output              npu_mst0_axi_rlast,
                   input   [5-1:0]   npu_mst0_axi_awid,
                   input               npu_mst0_axi_awvalid,
                   output              npu_mst0_axi_awready,
                   input   [40-1:0]   npu_mst0_axi_awaddr,
                   input   [1:0]       npu_mst0_axi_awburst,
                   input   [2:0]       npu_mst0_axi_awsize,
                   input               npu_mst0_axi_awlock,
                   input   [4-1:0]   npu_mst0_axi_awlen,
                   input   [3:0]       npu_mst0_axi_awcache,
                   input   [2:0]       npu_mst0_axi_awprot,
                   input               npu_mst0_axi_wvalid,
                   output              npu_mst0_axi_wready,
                   input   [64-1:0]   npu_mst0_axi_wdata,
                   input   [64/8-1:0] npu_mst0_axi_wstrb,
                   input               npu_mst0_axi_wlast,
                   output  [5-1:0]   npu_mst0_axi_bid,
                   output              npu_mst0_axi_bvalid,
                   input               npu_mst0_axi_bready,
                   output  [1:0]       npu_mst0_axi_bresp,
                   // 1: AXI master interface, pref: npu_mst1_axi_, data-width: 512, r/w: rw, excl: 1
                   input   [5-1:0]   npu_mst1_axi_arid,
                   input               npu_mst1_axi_arvalid,
                   output              npu_mst1_axi_arready,
                   input   [40-1:0]   npu_mst1_axi_araddr,
                   input   [1:0]       npu_mst1_axi_arburst,
                   input   [2:0]       npu_mst1_axi_arsize,
                   input               npu_mst1_axi_arlock,
                   input   [4-1:0]   npu_mst1_axi_arlen,
                   input   [3:0]       npu_mst1_axi_arcache,
                   input   [2:0]       npu_mst1_axi_arprot,
                   output  [5-1:0]   npu_mst1_axi_rid,
                   output              npu_mst1_axi_rvalid,
                   input               npu_mst1_axi_rready,
                   output  [512-1:0]   npu_mst1_axi_rdata,
                   output  [1:0]       npu_mst1_axi_rresp,
                   output              npu_mst1_axi_rlast,
                   input   [5-1:0]   npu_mst1_axi_awid,
                   input               npu_mst1_axi_awvalid,
                   output              npu_mst1_axi_awready,
                   input   [40-1:0]   npu_mst1_axi_awaddr,
                   input   [1:0]       npu_mst1_axi_awburst,
                   input   [2:0]       npu_mst1_axi_awsize,
                   input               npu_mst1_axi_awlock,
                   input   [4-1:0]   npu_mst1_axi_awlen,
                   input   [3:0]       npu_mst1_axi_awcache,
                   input   [2:0]       npu_mst1_axi_awprot,
                   input               npu_mst1_axi_wvalid,
                   output              npu_mst1_axi_wready,
                   input   [512-1:0]   npu_mst1_axi_wdata,
                   input   [512/8-1:0] npu_mst1_axi_wstrb,
                   input               npu_mst1_axi_wlast,
                   output  [5-1:0]   npu_mst1_axi_bid,
                   output              npu_mst1_axi_bvalid,
                   input               npu_mst1_axi_bready,
                   output  [1:0]       npu_mst1_axi_bresp,
                   // 2: AXI master interface, pref: npu_mst2_axi_, data-width: 512, r/w: rw, excl: 1
                   input   [5-1:0]   npu_mst2_axi_arid,
                   input               npu_mst2_axi_arvalid,
                   output              npu_mst2_axi_arready,
                   input   [40-1:0]   npu_mst2_axi_araddr,
                   input   [1:0]       npu_mst2_axi_arburst,
                   input   [2:0]       npu_mst2_axi_arsize,
                   input               npu_mst2_axi_arlock,
                   input   [4-1:0]   npu_mst2_axi_arlen,
                   input   [3:0]       npu_mst2_axi_arcache,
                   input   [2:0]       npu_mst2_axi_arprot,
                   output  [5-1:0]   npu_mst2_axi_rid,
                   output              npu_mst2_axi_rvalid,
                   input               npu_mst2_axi_rready,
                   output  [512-1:0]   npu_mst2_axi_rdata,
                   output  [1:0]       npu_mst2_axi_rresp,
                   output              npu_mst2_axi_rlast,
                   input   [5-1:0]   npu_mst2_axi_awid,
                   input               npu_mst2_axi_awvalid,
                   output              npu_mst2_axi_awready,
                   input   [40-1:0]   npu_mst2_axi_awaddr,
                   input   [1:0]       npu_mst2_axi_awburst,
                   input   [2:0]       npu_mst2_axi_awsize,
                   input               npu_mst2_axi_awlock,
                   input   [4-1:0]   npu_mst2_axi_awlen,
                   input   [3:0]       npu_mst2_axi_awcache,
                   input   [2:0]       npu_mst2_axi_awprot,
                   input               npu_mst2_axi_wvalid,
                   output              npu_mst2_axi_wready,
                   input   [512-1:0]   npu_mst2_axi_wdata,
                   input   [512/8-1:0] npu_mst2_axi_wstrb,
                   input               npu_mst2_axi_wlast,
                   output  [5-1:0]   npu_mst2_axi_bid,
                   output              npu_mst2_axi_bvalid,
                   input               npu_mst2_axi_bready,
                   output  [1:0]       npu_mst2_axi_bresp,
                   // 3: AXI master interface, pref: npu_mst3_axi_, data-width: 512, r/w: rw, excl: 1
                   input   [5-1:0]   npu_mst3_axi_arid,
                   input               npu_mst3_axi_arvalid,
                   output              npu_mst3_axi_arready,
                   input   [40-1:0]   npu_mst3_axi_araddr,
                   input   [1:0]       npu_mst3_axi_arburst,
                   input   [2:0]       npu_mst3_axi_arsize,
                   input               npu_mst3_axi_arlock,
                   input   [4-1:0]   npu_mst3_axi_arlen,
                   input   [3:0]       npu_mst3_axi_arcache,
                   input   [2:0]       npu_mst3_axi_arprot,
                   output  [5-1:0]   npu_mst3_axi_rid,
                   output              npu_mst3_axi_rvalid,
                   input               npu_mst3_axi_rready,
                   output  [512-1:0]   npu_mst3_axi_rdata,
                   output  [1:0]       npu_mst3_axi_rresp,
                   output              npu_mst3_axi_rlast,
                   input   [5-1:0]   npu_mst3_axi_awid,
                   input               npu_mst3_axi_awvalid,
                   output              npu_mst3_axi_awready,
                   input   [40-1:0]   npu_mst3_axi_awaddr,
                   input   [1:0]       npu_mst3_axi_awburst,
                   input   [2:0]       npu_mst3_axi_awsize,
                   input               npu_mst3_axi_awlock,
                   input   [4-1:0]   npu_mst3_axi_awlen,
                   input   [3:0]       npu_mst3_axi_awcache,
                   input   [2:0]       npu_mst3_axi_awprot,
                   input               npu_mst3_axi_wvalid,
                   output              npu_mst3_axi_wready,
                   input   [512-1:0]   npu_mst3_axi_wdata,
                   input   [512/8-1:0] npu_mst3_axi_wstrb,
                   input               npu_mst3_axi_wlast,
                   output  [5-1:0]   npu_mst3_axi_bid,
                   output              npu_mst3_axi_bvalid,
                   input               npu_mst3_axi_bready,
                   output  [1:0]       npu_mst3_axi_bresp,
                   // 4: AXI master interface, pref: npu_mst4_axi_, data-width: 512, r/w: rw, excl: 1
                   input   [5-1:0]   npu_mst4_axi_arid,
                   input               npu_mst4_axi_arvalid,
                   output              npu_mst4_axi_arready,
                   input   [40-1:0]   npu_mst4_axi_araddr,
                   input   [1:0]       npu_mst4_axi_arburst,
                   input   [2:0]       npu_mst4_axi_arsize,
                   input               npu_mst4_axi_arlock,
                   input   [4-1:0]   npu_mst4_axi_arlen,
                   input   [3:0]       npu_mst4_axi_arcache,
                   input   [2:0]       npu_mst4_axi_arprot,
                   output  [5-1:0]   npu_mst4_axi_rid,
                   output              npu_mst4_axi_rvalid,
                   input               npu_mst4_axi_rready,
                   output  [512-1:0]   npu_mst4_axi_rdata,
                   output  [1:0]       npu_mst4_axi_rresp,
                   output              npu_mst4_axi_rlast,
                   input   [5-1:0]   npu_mst4_axi_awid,
                   input               npu_mst4_axi_awvalid,
                   output              npu_mst4_axi_awready,
                   input   [40-1:0]   npu_mst4_axi_awaddr,
                   input   [1:0]       npu_mst4_axi_awburst,
                   input   [2:0]       npu_mst4_axi_awsize,
                   input               npu_mst4_axi_awlock,
                   input   [4-1:0]   npu_mst4_axi_awlen,
                   input   [3:0]       npu_mst4_axi_awcache,
                   input   [2:0]       npu_mst4_axi_awprot,
                   input               npu_mst4_axi_wvalid,
                   output              npu_mst4_axi_wready,
                   input   [512-1:0]   npu_mst4_axi_wdata,
                   input   [512/8-1:0] npu_mst4_axi_wstrb,
                   input               npu_mst4_axi_wlast,
                   output  [5-1:0]   npu_mst4_axi_bid,
                   output              npu_mst4_axi_bvalid,
                   input               npu_mst4_axi_bready,
                   output  [1:0]       npu_mst4_axi_bresp,
                   // 5: AXI master interface, pref: host_axi_, data-width: 64, r/w: rw, excl: 1
                   input   [1-1:0]   host_axi_arid,
                   input               host_axi_arvalid,
                   output              host_axi_arready,
                   input   [40-1:0]   host_axi_araddr,
                   input   [1:0]       host_axi_arburst,
                   input   [2:0]       host_axi_arsize,
                   input               host_axi_arlock,
                   input   [4-1:0]   host_axi_arlen,
                   input   [3:0]       host_axi_arcache,
                   input   [2:0]       host_axi_arprot,
                   output  [1-1:0]   host_axi_rid,
                   output              host_axi_rvalid,
                   input               host_axi_rready,
                   output  [64-1:0]   host_axi_rdata,
                   output  [1:0]       host_axi_rresp,
                   output              host_axi_rlast,
                   input   [1-1:0]   host_axi_awid,
                   input               host_axi_awvalid,
                   output              host_axi_awready,
                   input   [40-1:0]   host_axi_awaddr,
                   input   [1:0]       host_axi_awburst,
                   input   [2:0]       host_axi_awsize,
                   input               host_axi_awlock,
                   input   [4-1:0]   host_axi_awlen,
                   input   [3:0]       host_axi_awcache,
                   input   [2:0]       host_axi_awprot,
                   input               host_axi_wvalid,
                   output              host_axi_wready,
                   input   [64-1:0]   host_axi_wdata,
                   input   [64/8-1:0] host_axi_wstrb,
                   input               host_axi_wlast,
                   output  [1-1:0]   host_axi_bid,
                   output              host_axi_bvalid,
                   input               host_axi_bready,
                   output  [1:0]       host_axi_bresp,
                   // 6: AXI master interface, pref: bri4tb_, data-width: 32, r/w: rw, excl: 0
                   input   [4-1:0]   bri4tb_arid,
                   input               bri4tb_arvalid,
                   output              bri4tb_arready,
                   input   [40-1:0]   bri4tb_araddr,
                   input   [1:0]       bri4tb_arburst,
                   input   [2:0]       bri4tb_arsize,
                   input   [3:0]       bri4tb_arlen,
                   input   [3:0]       bri4tb_arcache,
                   input   [2:0]       bri4tb_arprot,
                   output  [4-1:0]   bri4tb_rid,
                   output              bri4tb_rvalid,
                   input               bri4tb_rready,
                   output  [32-1:0]   bri4tb_rdata,
                   output  [1:0]       bri4tb_rresp,
                   output              bri4tb_rlast,
                   input   [4-1:0]   bri4tb_awid,
                   input               bri4tb_awvalid,
                   output              bri4tb_awready,
                   input   [40-1:0]   bri4tb_awaddr,
                   input   [1:0]       bri4tb_awburst,
                   input   [2:0]       bri4tb_awsize,
                   input   [3:0]       bri4tb_awlen,
                   input   [3:0]       bri4tb_awcache,
                   input   [2:0]       bri4tb_awprot,
                   input   [4-1:0]   bri4tb_wid,
                   input               bri4tb_wvalid,
                   output              bri4tb_wready,
                   input   [32-1:0]   bri4tb_wdata,
                   input   [32/8-1:0] bri4tb_wstrb,
                   input               bri4tb_wlast,
                   output  [4-1:0]   bri4tb_bid,
                   output              bri4tb_bvalid,
                   input               bri4tb_bready,
                   output  [1:0]       bri4tb_bresp,
               // Slave interfaces
                 //     region 0, base: 917504 (0xe0000), address width: 28
                   // 0: AXI slave interface, data-width: 512, pref: npu_dmi0_axi_
                   output              npu_dmi0_axi_arvalid,
                   input               npu_dmi0_axi_arready,
                   output  [16-1:0]   npu_dmi0_axi_arid,
                   output  [40-1:0]   npu_dmi0_axi_araddr,
                   output  [1:0]       npu_dmi0_axi_arburst,
                   output  [2:0]       npu_dmi0_axi_arsize,
                   output  [3:0]       npu_dmi0_axi_arcache,
                   output  [2:0]       npu_dmi0_axi_arprot,

                   output               npu_dmi0_axi_arlock,
                   output   [3:0]       npu_dmi0_axi_arlen,
                   input   [16-1:0]   npu_dmi0_axi_rid,
                   input               npu_dmi0_axi_rvalid,
                   output              npu_dmi0_axi_rready,
                   input   [512-1:0]   npu_dmi0_axi_rdata,
                   input   [1:0]       npu_dmi0_axi_rresp,
                   input               npu_dmi0_axi_rlast,
                   output              npu_dmi0_axi_awvalid,
                   input               npu_dmi0_axi_awready,
                   output  [3:0]       npu_dmi0_axi_awcache,
                   output  [2:0]       npu_dmi0_axi_awprot,
                   output  [16-1:0]   npu_dmi0_axi_awid,
                   output  [40-1:0]   npu_dmi0_axi_awaddr,
                   output  [1:0]       npu_dmi0_axi_awburst,
                   output  [2:0]       npu_dmi0_axi_awsize,
                   output               npu_dmi0_axi_awlock,
                   output   [3:0]       npu_dmi0_axi_awlen,
                   output              npu_dmi0_axi_wvalid,
                   input               npu_dmi0_axi_wready,
                   output  [512-1:0]   npu_dmi0_axi_wdata,
                   output  [512/8-1:0] npu_dmi0_axi_wstrb,
                   output              npu_dmi0_axi_wlast,
                   input   [16-1:0]   npu_dmi0_axi_bid,
                   input               npu_dmi0_axi_bvalid,
                   output              npu_dmi0_axi_bready,
                   input   [1:0]       npu_dmi0_axi_bresp,

                 //     region 0, base: 983040 (0xf0000), address width: 20
                   // 1: AXI slave interface, data-width: 32, pref: npu_cfg_axi_
                   output              npu_cfg_axi_arvalid,
                   input               npu_cfg_axi_arready,
                   output  [16-1:0]   npu_cfg_axi_arid,
                   output  [40-1:0]   npu_cfg_axi_araddr,
                   output  [1:0]       npu_cfg_axi_arburst,
                   output  [2:0]       npu_cfg_axi_arsize,
                   output  [3:0]       npu_cfg_axi_arcache,
                   output  [2:0]       npu_cfg_axi_arprot,

                   output               npu_cfg_axi_arlock,
                   output   [3:0]       npu_cfg_axi_arlen,
                   input   [16-1:0]   npu_cfg_axi_rid,
                   input               npu_cfg_axi_rvalid,
                   output              npu_cfg_axi_rready,
                   input   [32-1:0]   npu_cfg_axi_rdata,
                   input   [1:0]       npu_cfg_axi_rresp,
                   input               npu_cfg_axi_rlast,
                   output              npu_cfg_axi_awvalid,
                   input               npu_cfg_axi_awready,
                   output  [3:0]       npu_cfg_axi_awcache,
                   output  [2:0]       npu_cfg_axi_awprot,
                   output  [16-1:0]   npu_cfg_axi_awid,
                   output  [40-1:0]   npu_cfg_axi_awaddr,
                   output  [1:0]       npu_cfg_axi_awburst,
                   output  [2:0]       npu_cfg_axi_awsize,
                   output               npu_cfg_axi_awlock,
                   output   [3:0]       npu_cfg_axi_awlen,
                   output              npu_cfg_axi_wvalid,
                   input               npu_cfg_axi_wready,
                   output  [32-1:0]   npu_cfg_axi_wdata,
                   output  [32/8-1:0] npu_cfg_axi_wstrb,
                   output              npu_cfg_axi_wlast,
                   input   [16-1:0]   npu_cfg_axi_bid,
                   input               npu_cfg_axi_bvalid,
                   output              npu_cfg_axi_bready,
                   input   [1:0]       npu_cfg_axi_bresp,

                 //     region 0, base: 868352 (0xd4000), address width: 24
                   // 2: AXI slave interface, data-width: 64, pref: arcsync_axi_
                   output              arcsync_axi_arvalid,
                   input               arcsync_axi_arready,
                   output  [16-1:0]   arcsync_axi_arid,
                   output  [40-1:0]   arcsync_axi_araddr,
                   output  [1:0]       arcsync_axi_arburst,
                   output  [2:0]       arcsync_axi_arsize,
                   output  [3:0]       arcsync_axi_arcache,
                   output  [2:0]       arcsync_axi_arprot,

                   output               arcsync_axi_arlock,
                   output   [3:0]       arcsync_axi_arlen,
                   input   [16-1:0]   arcsync_axi_rid,
                   input               arcsync_axi_rvalid,
                   output              arcsync_axi_rready,
                   input   [64-1:0]   arcsync_axi_rdata,
                   input   [1:0]       arcsync_axi_rresp,
                   input               arcsync_axi_rlast,
                   output              arcsync_axi_awvalid,
                   input               arcsync_axi_awready,
                   output  [3:0]       arcsync_axi_awcache,
                   output  [2:0]       arcsync_axi_awprot,
                   output  [16-1:0]   arcsync_axi_awid,
                   output  [40-1:0]   arcsync_axi_awaddr,
                   output  [1:0]       arcsync_axi_awburst,
                   output  [2:0]       arcsync_axi_awsize,
                   output               arcsync_axi_awlock,
                   output   [3:0]       arcsync_axi_awlen,
                   output              arcsync_axi_wvalid,
                   input               arcsync_axi_wready,
                   output  [64-1:0]   arcsync_axi_wdata,
                   output  [64/8-1:0] arcsync_axi_wstrb,
                   output              arcsync_axi_wlast,
                   input   [16-1:0]   arcsync_axi_bid,
                   input               arcsync_axi_bvalid,
                   output              arcsync_axi_bready,
                   input   [1:0]       arcsync_axi_bresp,

                 //     region 0, base: 0 (0x0), address width: 32
                   // 3: IBP slave interface, data-width: 128, pref: mss_mem_
                   output              mss_mem_cmd_valid,
                   input               mss_mem_cmd_accept,
                   output              mss_mem_cmd_read,
                   output  [32-1:0]   mss_mem_cmd_addr,
                   output              mss_mem_cmd_wrap,
                   output  [2:0]       mss_mem_cmd_data_size,
                   output  [3:0]       mss_mem_cmd_burst_size,
                   output              mss_mem_cmd_lock,
                   output              mss_mem_cmd_excl,
                   output  [1:0]       mss_mem_cmd_prot,
                   output  [3:0]       mss_mem_cmd_cache,
                   output  [1-1:0]  mss_mem_cmd_region,
                   output  [8-1:0] mss_mem_cmd_id, // side-signal to support exclusive memory access
                   output  [1-1:0] mss_mem_cmd_user, // side-signal to user signals
                   input               mss_mem_rd_valid,
                   output              mss_mem_rd_accept,
                   input               mss_mem_rd_excl_ok,
                   input   [128-1:0]   mss_mem_rd_data,
                   input               mss_mem_err_rd,
                   input               mss_mem_rd_last,
                   output              mss_mem_wr_valid,
                   input               mss_mem_wr_accept,
                   output  [128-1:0]   mss_mem_wr_data,
                   output  [128/8-1:0] mss_mem_wr_mask,
                   output              mss_mem_wr_last,
                   input               mss_mem_wr_done,
                   input               mss_mem_wr_excl_done,
                   input               mss_mem_err_wr,
                   output              mss_mem_wr_resp_accept,
                   // output system address base signal
                   // clock and clock enables
                   input               clk,
                   input               mss_clk,
                   input               mss_fab_mst0_clk_en,
                   input               mss_fab_mst1_clk_en,
                   input               mss_fab_mst2_clk_en,
                   input               mss_fab_mst3_clk_en,
                   input               mss_fab_mst4_clk_en,
                   input               mss_fab_mst5_clk_en,
                   input               mss_fab_mst6_clk_en,
                   input               mss_fab_slv0_clk_en,
                   input               mss_fab_slv1_clk_en,
                   input               mss_fab_slv2_clk_en,
                   input               mss_fab_slv3_clk_en,
                   input                rst_b
);

//Internal wires

//
//wires for master side
//


  wire                                  mst_npu_mst0_axi_ibp_cmd_valid;
  wire                                  mst_npu_mst0_axi_ibp_cmd_accept;
  wire                                  mst_npu_mst0_axi_ibp_cmd_read;
  wire  [49                -1:0]       mst_npu_mst0_axi_ibp_cmd_addr;
  wire                                  mst_npu_mst0_axi_ibp_cmd_wrap;
  wire  [3-1:0]       mst_npu_mst0_axi_ibp_cmd_data_size;
  wire  [4-1:0]       mst_npu_mst0_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       mst_npu_mst0_axi_ibp_cmd_prot;
  wire  [4-1:0]       mst_npu_mst0_axi_ibp_cmd_cache;
  wire                                  mst_npu_mst0_axi_ibp_cmd_lock;
  wire                                  mst_npu_mst0_axi_ibp_cmd_excl;

  wire                                  mst_npu_mst0_axi_ibp_rd_valid;
  wire                                  mst_npu_mst0_axi_ibp_rd_excl_ok;
  wire                                  mst_npu_mst0_axi_ibp_rd_accept;
  wire                                  mst_npu_mst0_axi_ibp_err_rd;
  wire  [64               -1:0]        mst_npu_mst0_axi_ibp_rd_data;
  wire                                  mst_npu_mst0_axi_ibp_rd_last;

  wire                                  mst_npu_mst0_axi_ibp_wr_valid;
  wire                                  mst_npu_mst0_axi_ibp_wr_accept;
  wire  [64               -1:0]        mst_npu_mst0_axi_ibp_wr_data;
  wire  [(64         /8)  -1:0]        mst_npu_mst0_axi_ibp_wr_mask;
  wire                                  mst_npu_mst0_axi_ibp_wr_last;

  wire                                  mst_npu_mst0_axi_ibp_wr_done;
  wire                                  mst_npu_mst0_axi_ibp_wr_excl_done;
  wire                                  mst_npu_mst0_axi_ibp_err_wr;
  wire                                  mst_npu_mst0_axi_ibp_wr_resp_accept;
wire [1-1:0] mst_npu_mst0_axi_ibp_cmd_rgon;



 wire [1-1:0] mst_npu_mst0_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_npu_mst0_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_npu_mst0_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_npu_mst0_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_npu_mst0_axi_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] mst_npu_mst0_axi_ibp_wd_chnl;

 wire [1-1:0] mst_npu_mst0_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_npu_mst0_axi_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] mst_npu_mst0_axi_ibp_rd_chnl;

 wire [1-1:0] mst_npu_mst0_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_npu_mst0_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_npu_mst0_axi_ibp_wrsp_chnl;

wire [1-1:0]mst_npu_mst0_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] mst_o_npu_mst0_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_o_npu_mst0_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_o_npu_mst0_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_o_npu_mst0_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_o_npu_mst0_axi_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] mst_o_npu_mst0_axi_ibp_wd_chnl;

 wire [1-1:0] mst_o_npu_mst0_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_o_npu_mst0_axi_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] mst_o_npu_mst0_axi_ibp_rd_chnl;

 wire [1-1:0] mst_o_npu_mst0_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_o_npu_mst0_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_o_npu_mst0_axi_ibp_wrsp_chnl;

wire [1-1:0] mst_o_npu_mst0_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] lat_i_npu_mst0_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] lat_i_npu_mst0_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] lat_i_npu_mst0_axi_ibp_cmd_chnl;

 wire [1-1:0] lat_i_npu_mst0_axi_ibp_wd_chnl_valid;
 wire [1-1:0] lat_i_npu_mst0_axi_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] lat_i_npu_mst0_axi_ibp_wd_chnl;

 wire [1-1:0] lat_i_npu_mst0_axi_ibp_rd_chnl_accept;
 wire [1-1:0] lat_i_npu_mst0_axi_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] lat_i_npu_mst0_axi_ibp_rd_chnl;

 wire [1-1:0] lat_i_npu_mst0_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] lat_i_npu_mst0_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] lat_i_npu_mst0_axi_ibp_wrsp_chnl;

wire [1-1:0] lat_i_npu_mst0_axi_ibp_cmd_chnl_rgon;


  wire                                  lat_i_npu_mst0_axi_ibp_cmd_valid;
  wire                                  lat_i_npu_mst0_axi_ibp_cmd_accept;
  wire                                  lat_i_npu_mst0_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_i_npu_mst0_axi_ibp_cmd_addr;
  wire                                  lat_i_npu_mst0_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_i_npu_mst0_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_i_npu_mst0_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_i_npu_mst0_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_i_npu_mst0_axi_ibp_cmd_cache;
  wire                                  lat_i_npu_mst0_axi_ibp_cmd_lock;
  wire                                  lat_i_npu_mst0_axi_ibp_cmd_excl;

  wire                                  lat_i_npu_mst0_axi_ibp_rd_valid;
  wire                                  lat_i_npu_mst0_axi_ibp_rd_excl_ok;
  wire                                  lat_i_npu_mst0_axi_ibp_rd_accept;
  wire                                  lat_i_npu_mst0_axi_ibp_err_rd;
  wire  [64               -1:0]        lat_i_npu_mst0_axi_ibp_rd_data;
  wire                                  lat_i_npu_mst0_axi_ibp_rd_last;

  wire                                  lat_i_npu_mst0_axi_ibp_wr_valid;
  wire                                  lat_i_npu_mst0_axi_ibp_wr_accept;
  wire  [64               -1:0]        lat_i_npu_mst0_axi_ibp_wr_data;
  wire  [(64         /8)  -1:0]        lat_i_npu_mst0_axi_ibp_wr_mask;
  wire                                  lat_i_npu_mst0_axi_ibp_wr_last;

  wire                                  lat_i_npu_mst0_axi_ibp_wr_done;
  wire                                  lat_i_npu_mst0_axi_ibp_wr_excl_done;
  wire                                  lat_i_npu_mst0_axi_ibp_err_wr;
  wire                                  lat_i_npu_mst0_axi_ibp_wr_resp_accept;


  wire                                  lat_o_npu_mst0_axi_ibp_cmd_valid;
  wire                                  lat_o_npu_mst0_axi_ibp_cmd_accept;
  wire                                  lat_o_npu_mst0_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_o_npu_mst0_axi_ibp_cmd_addr;
  wire                                  lat_o_npu_mst0_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_o_npu_mst0_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_o_npu_mst0_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_o_npu_mst0_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_o_npu_mst0_axi_ibp_cmd_cache;
  wire                                  lat_o_npu_mst0_axi_ibp_cmd_lock;
  wire                                  lat_o_npu_mst0_axi_ibp_cmd_excl;

  wire                                  lat_o_npu_mst0_axi_ibp_rd_valid;
  wire                                  lat_o_npu_mst0_axi_ibp_rd_excl_ok;
  wire                                  lat_o_npu_mst0_axi_ibp_rd_accept;
  wire                                  lat_o_npu_mst0_axi_ibp_err_rd;
  wire  [64               -1:0]        lat_o_npu_mst0_axi_ibp_rd_data;
  wire                                  lat_o_npu_mst0_axi_ibp_rd_last;

  wire                                  lat_o_npu_mst0_axi_ibp_wr_valid;
  wire                                  lat_o_npu_mst0_axi_ibp_wr_accept;
  wire  [64               -1:0]        lat_o_npu_mst0_axi_ibp_wr_data;
  wire  [(64         /8)  -1:0]        lat_o_npu_mst0_axi_ibp_wr_mask;
  wire                                  lat_o_npu_mst0_axi_ibp_wr_last;

  wire                                  lat_o_npu_mst0_axi_ibp_wr_done;
  wire                                  lat_o_npu_mst0_axi_ibp_wr_excl_done;
  wire                                  lat_o_npu_mst0_axi_ibp_err_wr;
  wire                                  lat_o_npu_mst0_axi_ibp_wr_resp_accept;


  wire                                  mst_npu_mst1_axi_ibp_cmd_valid;
  wire                                  mst_npu_mst1_axi_ibp_cmd_accept;
  wire                                  mst_npu_mst1_axi_ibp_cmd_read;
  wire  [49                -1:0]       mst_npu_mst1_axi_ibp_cmd_addr;
  wire                                  mst_npu_mst1_axi_ibp_cmd_wrap;
  wire  [3-1:0]       mst_npu_mst1_axi_ibp_cmd_data_size;
  wire  [4-1:0]       mst_npu_mst1_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       mst_npu_mst1_axi_ibp_cmd_prot;
  wire  [4-1:0]       mst_npu_mst1_axi_ibp_cmd_cache;
  wire                                  mst_npu_mst1_axi_ibp_cmd_lock;
  wire                                  mst_npu_mst1_axi_ibp_cmd_excl;

  wire                                  mst_npu_mst1_axi_ibp_rd_valid;
  wire                                  mst_npu_mst1_axi_ibp_rd_excl_ok;
  wire                                  mst_npu_mst1_axi_ibp_rd_accept;
  wire                                  mst_npu_mst1_axi_ibp_err_rd;
  wire  [512               -1:0]        mst_npu_mst1_axi_ibp_rd_data;
  wire                                  mst_npu_mst1_axi_ibp_rd_last;

  wire                                  mst_npu_mst1_axi_ibp_wr_valid;
  wire                                  mst_npu_mst1_axi_ibp_wr_accept;
  wire  [512               -1:0]        mst_npu_mst1_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        mst_npu_mst1_axi_ibp_wr_mask;
  wire                                  mst_npu_mst1_axi_ibp_wr_last;

  wire                                  mst_npu_mst1_axi_ibp_wr_done;
  wire                                  mst_npu_mst1_axi_ibp_wr_excl_done;
  wire                                  mst_npu_mst1_axi_ibp_err_wr;
  wire                                  mst_npu_mst1_axi_ibp_wr_resp_accept;
wire [1-1:0] mst_npu_mst1_axi_ibp_cmd_rgon;



 wire [1-1:0] mst_npu_mst1_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_npu_mst1_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_npu_mst1_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_npu_mst1_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_npu_mst1_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] mst_npu_mst1_axi_ibp_wd_chnl;

 wire [1-1:0] mst_npu_mst1_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_npu_mst1_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] mst_npu_mst1_axi_ibp_rd_chnl;

 wire [1-1:0] mst_npu_mst1_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_npu_mst1_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_npu_mst1_axi_ibp_wrsp_chnl;

wire [1-1:0]mst_npu_mst1_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] mst_o_npu_mst1_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_o_npu_mst1_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_o_npu_mst1_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_o_npu_mst1_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_o_npu_mst1_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] mst_o_npu_mst1_axi_ibp_wd_chnl;

 wire [1-1:0] mst_o_npu_mst1_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_o_npu_mst1_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] mst_o_npu_mst1_axi_ibp_rd_chnl;

 wire [1-1:0] mst_o_npu_mst1_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_o_npu_mst1_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_o_npu_mst1_axi_ibp_wrsp_chnl;

wire [1-1:0] mst_o_npu_mst1_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] lat_i_npu_mst1_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] lat_i_npu_mst1_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] lat_i_npu_mst1_axi_ibp_cmd_chnl;

 wire [1-1:0] lat_i_npu_mst1_axi_ibp_wd_chnl_valid;
 wire [1-1:0] lat_i_npu_mst1_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] lat_i_npu_mst1_axi_ibp_wd_chnl;

 wire [1-1:0] lat_i_npu_mst1_axi_ibp_rd_chnl_accept;
 wire [1-1:0] lat_i_npu_mst1_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] lat_i_npu_mst1_axi_ibp_rd_chnl;

 wire [1-1:0] lat_i_npu_mst1_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] lat_i_npu_mst1_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] lat_i_npu_mst1_axi_ibp_wrsp_chnl;

wire [1-1:0] lat_i_npu_mst1_axi_ibp_cmd_chnl_rgon;


  wire                                  lat_i_npu_mst1_axi_ibp_cmd_valid;
  wire                                  lat_i_npu_mst1_axi_ibp_cmd_accept;
  wire                                  lat_i_npu_mst1_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_i_npu_mst1_axi_ibp_cmd_addr;
  wire                                  lat_i_npu_mst1_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_i_npu_mst1_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_i_npu_mst1_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_i_npu_mst1_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_i_npu_mst1_axi_ibp_cmd_cache;
  wire                                  lat_i_npu_mst1_axi_ibp_cmd_lock;
  wire                                  lat_i_npu_mst1_axi_ibp_cmd_excl;

  wire                                  lat_i_npu_mst1_axi_ibp_rd_valid;
  wire                                  lat_i_npu_mst1_axi_ibp_rd_excl_ok;
  wire                                  lat_i_npu_mst1_axi_ibp_rd_accept;
  wire                                  lat_i_npu_mst1_axi_ibp_err_rd;
  wire  [512               -1:0]        lat_i_npu_mst1_axi_ibp_rd_data;
  wire                                  lat_i_npu_mst1_axi_ibp_rd_last;

  wire                                  lat_i_npu_mst1_axi_ibp_wr_valid;
  wire                                  lat_i_npu_mst1_axi_ibp_wr_accept;
  wire  [512               -1:0]        lat_i_npu_mst1_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        lat_i_npu_mst1_axi_ibp_wr_mask;
  wire                                  lat_i_npu_mst1_axi_ibp_wr_last;

  wire                                  lat_i_npu_mst1_axi_ibp_wr_done;
  wire                                  lat_i_npu_mst1_axi_ibp_wr_excl_done;
  wire                                  lat_i_npu_mst1_axi_ibp_err_wr;
  wire                                  lat_i_npu_mst1_axi_ibp_wr_resp_accept;


  wire                                  lat_o_npu_mst1_axi_ibp_cmd_valid;
  wire                                  lat_o_npu_mst1_axi_ibp_cmd_accept;
  wire                                  lat_o_npu_mst1_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_o_npu_mst1_axi_ibp_cmd_addr;
  wire                                  lat_o_npu_mst1_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_o_npu_mst1_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_o_npu_mst1_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_o_npu_mst1_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_o_npu_mst1_axi_ibp_cmd_cache;
  wire                                  lat_o_npu_mst1_axi_ibp_cmd_lock;
  wire                                  lat_o_npu_mst1_axi_ibp_cmd_excl;

  wire                                  lat_o_npu_mst1_axi_ibp_rd_valid;
  wire                                  lat_o_npu_mst1_axi_ibp_rd_excl_ok;
  wire                                  lat_o_npu_mst1_axi_ibp_rd_accept;
  wire                                  lat_o_npu_mst1_axi_ibp_err_rd;
  wire  [512               -1:0]        lat_o_npu_mst1_axi_ibp_rd_data;
  wire                                  lat_o_npu_mst1_axi_ibp_rd_last;

  wire                                  lat_o_npu_mst1_axi_ibp_wr_valid;
  wire                                  lat_o_npu_mst1_axi_ibp_wr_accept;
  wire  [512               -1:0]        lat_o_npu_mst1_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        lat_o_npu_mst1_axi_ibp_wr_mask;
  wire                                  lat_o_npu_mst1_axi_ibp_wr_last;

  wire                                  lat_o_npu_mst1_axi_ibp_wr_done;
  wire                                  lat_o_npu_mst1_axi_ibp_wr_excl_done;
  wire                                  lat_o_npu_mst1_axi_ibp_err_wr;
  wire                                  lat_o_npu_mst1_axi_ibp_wr_resp_accept;


  wire                                  mst_npu_mst2_axi_ibp_cmd_valid;
  wire                                  mst_npu_mst2_axi_ibp_cmd_accept;
  wire                                  mst_npu_mst2_axi_ibp_cmd_read;
  wire  [49                -1:0]       mst_npu_mst2_axi_ibp_cmd_addr;
  wire                                  mst_npu_mst2_axi_ibp_cmd_wrap;
  wire  [3-1:0]       mst_npu_mst2_axi_ibp_cmd_data_size;
  wire  [4-1:0]       mst_npu_mst2_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       mst_npu_mst2_axi_ibp_cmd_prot;
  wire  [4-1:0]       mst_npu_mst2_axi_ibp_cmd_cache;
  wire                                  mst_npu_mst2_axi_ibp_cmd_lock;
  wire                                  mst_npu_mst2_axi_ibp_cmd_excl;

  wire                                  mst_npu_mst2_axi_ibp_rd_valid;
  wire                                  mst_npu_mst2_axi_ibp_rd_excl_ok;
  wire                                  mst_npu_mst2_axi_ibp_rd_accept;
  wire                                  mst_npu_mst2_axi_ibp_err_rd;
  wire  [512               -1:0]        mst_npu_mst2_axi_ibp_rd_data;
  wire                                  mst_npu_mst2_axi_ibp_rd_last;

  wire                                  mst_npu_mst2_axi_ibp_wr_valid;
  wire                                  mst_npu_mst2_axi_ibp_wr_accept;
  wire  [512               -1:0]        mst_npu_mst2_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        mst_npu_mst2_axi_ibp_wr_mask;
  wire                                  mst_npu_mst2_axi_ibp_wr_last;

  wire                                  mst_npu_mst2_axi_ibp_wr_done;
  wire                                  mst_npu_mst2_axi_ibp_wr_excl_done;
  wire                                  mst_npu_mst2_axi_ibp_err_wr;
  wire                                  mst_npu_mst2_axi_ibp_wr_resp_accept;
wire [1-1:0] mst_npu_mst2_axi_ibp_cmd_rgon;



 wire [1-1:0] mst_npu_mst2_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_npu_mst2_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_npu_mst2_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_npu_mst2_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_npu_mst2_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] mst_npu_mst2_axi_ibp_wd_chnl;

 wire [1-1:0] mst_npu_mst2_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_npu_mst2_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] mst_npu_mst2_axi_ibp_rd_chnl;

 wire [1-1:0] mst_npu_mst2_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_npu_mst2_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_npu_mst2_axi_ibp_wrsp_chnl;

wire [1-1:0]mst_npu_mst2_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] mst_o_npu_mst2_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_o_npu_mst2_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_o_npu_mst2_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_o_npu_mst2_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_o_npu_mst2_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] mst_o_npu_mst2_axi_ibp_wd_chnl;

 wire [1-1:0] mst_o_npu_mst2_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_o_npu_mst2_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] mst_o_npu_mst2_axi_ibp_rd_chnl;

 wire [1-1:0] mst_o_npu_mst2_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_o_npu_mst2_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_o_npu_mst2_axi_ibp_wrsp_chnl;

wire [1-1:0] mst_o_npu_mst2_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] lat_i_npu_mst2_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] lat_i_npu_mst2_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] lat_i_npu_mst2_axi_ibp_cmd_chnl;

 wire [1-1:0] lat_i_npu_mst2_axi_ibp_wd_chnl_valid;
 wire [1-1:0] lat_i_npu_mst2_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] lat_i_npu_mst2_axi_ibp_wd_chnl;

 wire [1-1:0] lat_i_npu_mst2_axi_ibp_rd_chnl_accept;
 wire [1-1:0] lat_i_npu_mst2_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] lat_i_npu_mst2_axi_ibp_rd_chnl;

 wire [1-1:0] lat_i_npu_mst2_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] lat_i_npu_mst2_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] lat_i_npu_mst2_axi_ibp_wrsp_chnl;

wire [1-1:0] lat_i_npu_mst2_axi_ibp_cmd_chnl_rgon;


  wire                                  lat_i_npu_mst2_axi_ibp_cmd_valid;
  wire                                  lat_i_npu_mst2_axi_ibp_cmd_accept;
  wire                                  lat_i_npu_mst2_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_i_npu_mst2_axi_ibp_cmd_addr;
  wire                                  lat_i_npu_mst2_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_i_npu_mst2_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_i_npu_mst2_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_i_npu_mst2_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_i_npu_mst2_axi_ibp_cmd_cache;
  wire                                  lat_i_npu_mst2_axi_ibp_cmd_lock;
  wire                                  lat_i_npu_mst2_axi_ibp_cmd_excl;

  wire                                  lat_i_npu_mst2_axi_ibp_rd_valid;
  wire                                  lat_i_npu_mst2_axi_ibp_rd_excl_ok;
  wire                                  lat_i_npu_mst2_axi_ibp_rd_accept;
  wire                                  lat_i_npu_mst2_axi_ibp_err_rd;
  wire  [512               -1:0]        lat_i_npu_mst2_axi_ibp_rd_data;
  wire                                  lat_i_npu_mst2_axi_ibp_rd_last;

  wire                                  lat_i_npu_mst2_axi_ibp_wr_valid;
  wire                                  lat_i_npu_mst2_axi_ibp_wr_accept;
  wire  [512               -1:0]        lat_i_npu_mst2_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        lat_i_npu_mst2_axi_ibp_wr_mask;
  wire                                  lat_i_npu_mst2_axi_ibp_wr_last;

  wire                                  lat_i_npu_mst2_axi_ibp_wr_done;
  wire                                  lat_i_npu_mst2_axi_ibp_wr_excl_done;
  wire                                  lat_i_npu_mst2_axi_ibp_err_wr;
  wire                                  lat_i_npu_mst2_axi_ibp_wr_resp_accept;


  wire                                  lat_o_npu_mst2_axi_ibp_cmd_valid;
  wire                                  lat_o_npu_mst2_axi_ibp_cmd_accept;
  wire                                  lat_o_npu_mst2_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_o_npu_mst2_axi_ibp_cmd_addr;
  wire                                  lat_o_npu_mst2_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_o_npu_mst2_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_o_npu_mst2_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_o_npu_mst2_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_o_npu_mst2_axi_ibp_cmd_cache;
  wire                                  lat_o_npu_mst2_axi_ibp_cmd_lock;
  wire                                  lat_o_npu_mst2_axi_ibp_cmd_excl;

  wire                                  lat_o_npu_mst2_axi_ibp_rd_valid;
  wire                                  lat_o_npu_mst2_axi_ibp_rd_excl_ok;
  wire                                  lat_o_npu_mst2_axi_ibp_rd_accept;
  wire                                  lat_o_npu_mst2_axi_ibp_err_rd;
  wire  [512               -1:0]        lat_o_npu_mst2_axi_ibp_rd_data;
  wire                                  lat_o_npu_mst2_axi_ibp_rd_last;

  wire                                  lat_o_npu_mst2_axi_ibp_wr_valid;
  wire                                  lat_o_npu_mst2_axi_ibp_wr_accept;
  wire  [512               -1:0]        lat_o_npu_mst2_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        lat_o_npu_mst2_axi_ibp_wr_mask;
  wire                                  lat_o_npu_mst2_axi_ibp_wr_last;

  wire                                  lat_o_npu_mst2_axi_ibp_wr_done;
  wire                                  lat_o_npu_mst2_axi_ibp_wr_excl_done;
  wire                                  lat_o_npu_mst2_axi_ibp_err_wr;
  wire                                  lat_o_npu_mst2_axi_ibp_wr_resp_accept;


  wire                                  mst_npu_mst3_axi_ibp_cmd_valid;
  wire                                  mst_npu_mst3_axi_ibp_cmd_accept;
  wire                                  mst_npu_mst3_axi_ibp_cmd_read;
  wire  [49                -1:0]       mst_npu_mst3_axi_ibp_cmd_addr;
  wire                                  mst_npu_mst3_axi_ibp_cmd_wrap;
  wire  [3-1:0]       mst_npu_mst3_axi_ibp_cmd_data_size;
  wire  [4-1:0]       mst_npu_mst3_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       mst_npu_mst3_axi_ibp_cmd_prot;
  wire  [4-1:0]       mst_npu_mst3_axi_ibp_cmd_cache;
  wire                                  mst_npu_mst3_axi_ibp_cmd_lock;
  wire                                  mst_npu_mst3_axi_ibp_cmd_excl;

  wire                                  mst_npu_mst3_axi_ibp_rd_valid;
  wire                                  mst_npu_mst3_axi_ibp_rd_excl_ok;
  wire                                  mst_npu_mst3_axi_ibp_rd_accept;
  wire                                  mst_npu_mst3_axi_ibp_err_rd;
  wire  [512               -1:0]        mst_npu_mst3_axi_ibp_rd_data;
  wire                                  mst_npu_mst3_axi_ibp_rd_last;

  wire                                  mst_npu_mst3_axi_ibp_wr_valid;
  wire                                  mst_npu_mst3_axi_ibp_wr_accept;
  wire  [512               -1:0]        mst_npu_mst3_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        mst_npu_mst3_axi_ibp_wr_mask;
  wire                                  mst_npu_mst3_axi_ibp_wr_last;

  wire                                  mst_npu_mst3_axi_ibp_wr_done;
  wire                                  mst_npu_mst3_axi_ibp_wr_excl_done;
  wire                                  mst_npu_mst3_axi_ibp_err_wr;
  wire                                  mst_npu_mst3_axi_ibp_wr_resp_accept;
wire [1-1:0] mst_npu_mst3_axi_ibp_cmd_rgon;



 wire [1-1:0] mst_npu_mst3_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_npu_mst3_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_npu_mst3_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_npu_mst3_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_npu_mst3_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] mst_npu_mst3_axi_ibp_wd_chnl;

 wire [1-1:0] mst_npu_mst3_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_npu_mst3_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] mst_npu_mst3_axi_ibp_rd_chnl;

 wire [1-1:0] mst_npu_mst3_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_npu_mst3_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_npu_mst3_axi_ibp_wrsp_chnl;

wire [1-1:0]mst_npu_mst3_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] mst_o_npu_mst3_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_o_npu_mst3_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_o_npu_mst3_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_o_npu_mst3_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_o_npu_mst3_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] mst_o_npu_mst3_axi_ibp_wd_chnl;

 wire [1-1:0] mst_o_npu_mst3_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_o_npu_mst3_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] mst_o_npu_mst3_axi_ibp_rd_chnl;

 wire [1-1:0] mst_o_npu_mst3_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_o_npu_mst3_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_o_npu_mst3_axi_ibp_wrsp_chnl;

wire [1-1:0] mst_o_npu_mst3_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] lat_i_npu_mst3_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] lat_i_npu_mst3_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] lat_i_npu_mst3_axi_ibp_cmd_chnl;

 wire [1-1:0] lat_i_npu_mst3_axi_ibp_wd_chnl_valid;
 wire [1-1:0] lat_i_npu_mst3_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] lat_i_npu_mst3_axi_ibp_wd_chnl;

 wire [1-1:0] lat_i_npu_mst3_axi_ibp_rd_chnl_accept;
 wire [1-1:0] lat_i_npu_mst3_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] lat_i_npu_mst3_axi_ibp_rd_chnl;

 wire [1-1:0] lat_i_npu_mst3_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] lat_i_npu_mst3_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] lat_i_npu_mst3_axi_ibp_wrsp_chnl;

wire [1-1:0] lat_i_npu_mst3_axi_ibp_cmd_chnl_rgon;


  wire                                  lat_i_npu_mst3_axi_ibp_cmd_valid;
  wire                                  lat_i_npu_mst3_axi_ibp_cmd_accept;
  wire                                  lat_i_npu_mst3_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_i_npu_mst3_axi_ibp_cmd_addr;
  wire                                  lat_i_npu_mst3_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_i_npu_mst3_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_i_npu_mst3_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_i_npu_mst3_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_i_npu_mst3_axi_ibp_cmd_cache;
  wire                                  lat_i_npu_mst3_axi_ibp_cmd_lock;
  wire                                  lat_i_npu_mst3_axi_ibp_cmd_excl;

  wire                                  lat_i_npu_mst3_axi_ibp_rd_valid;
  wire                                  lat_i_npu_mst3_axi_ibp_rd_excl_ok;
  wire                                  lat_i_npu_mst3_axi_ibp_rd_accept;
  wire                                  lat_i_npu_mst3_axi_ibp_err_rd;
  wire  [512               -1:0]        lat_i_npu_mst3_axi_ibp_rd_data;
  wire                                  lat_i_npu_mst3_axi_ibp_rd_last;

  wire                                  lat_i_npu_mst3_axi_ibp_wr_valid;
  wire                                  lat_i_npu_mst3_axi_ibp_wr_accept;
  wire  [512               -1:0]        lat_i_npu_mst3_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        lat_i_npu_mst3_axi_ibp_wr_mask;
  wire                                  lat_i_npu_mst3_axi_ibp_wr_last;

  wire                                  lat_i_npu_mst3_axi_ibp_wr_done;
  wire                                  lat_i_npu_mst3_axi_ibp_wr_excl_done;
  wire                                  lat_i_npu_mst3_axi_ibp_err_wr;
  wire                                  lat_i_npu_mst3_axi_ibp_wr_resp_accept;


  wire                                  lat_o_npu_mst3_axi_ibp_cmd_valid;
  wire                                  lat_o_npu_mst3_axi_ibp_cmd_accept;
  wire                                  lat_o_npu_mst3_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_o_npu_mst3_axi_ibp_cmd_addr;
  wire                                  lat_o_npu_mst3_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_o_npu_mst3_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_o_npu_mst3_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_o_npu_mst3_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_o_npu_mst3_axi_ibp_cmd_cache;
  wire                                  lat_o_npu_mst3_axi_ibp_cmd_lock;
  wire                                  lat_o_npu_mst3_axi_ibp_cmd_excl;

  wire                                  lat_o_npu_mst3_axi_ibp_rd_valid;
  wire                                  lat_o_npu_mst3_axi_ibp_rd_excl_ok;
  wire                                  lat_o_npu_mst3_axi_ibp_rd_accept;
  wire                                  lat_o_npu_mst3_axi_ibp_err_rd;
  wire  [512               -1:0]        lat_o_npu_mst3_axi_ibp_rd_data;
  wire                                  lat_o_npu_mst3_axi_ibp_rd_last;

  wire                                  lat_o_npu_mst3_axi_ibp_wr_valid;
  wire                                  lat_o_npu_mst3_axi_ibp_wr_accept;
  wire  [512               -1:0]        lat_o_npu_mst3_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        lat_o_npu_mst3_axi_ibp_wr_mask;
  wire                                  lat_o_npu_mst3_axi_ibp_wr_last;

  wire                                  lat_o_npu_mst3_axi_ibp_wr_done;
  wire                                  lat_o_npu_mst3_axi_ibp_wr_excl_done;
  wire                                  lat_o_npu_mst3_axi_ibp_err_wr;
  wire                                  lat_o_npu_mst3_axi_ibp_wr_resp_accept;


  wire                                  mst_npu_mst4_axi_ibp_cmd_valid;
  wire                                  mst_npu_mst4_axi_ibp_cmd_accept;
  wire                                  mst_npu_mst4_axi_ibp_cmd_read;
  wire  [49                -1:0]       mst_npu_mst4_axi_ibp_cmd_addr;
  wire                                  mst_npu_mst4_axi_ibp_cmd_wrap;
  wire  [3-1:0]       mst_npu_mst4_axi_ibp_cmd_data_size;
  wire  [4-1:0]       mst_npu_mst4_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       mst_npu_mst4_axi_ibp_cmd_prot;
  wire  [4-1:0]       mst_npu_mst4_axi_ibp_cmd_cache;
  wire                                  mst_npu_mst4_axi_ibp_cmd_lock;
  wire                                  mst_npu_mst4_axi_ibp_cmd_excl;

  wire                                  mst_npu_mst4_axi_ibp_rd_valid;
  wire                                  mst_npu_mst4_axi_ibp_rd_excl_ok;
  wire                                  mst_npu_mst4_axi_ibp_rd_accept;
  wire                                  mst_npu_mst4_axi_ibp_err_rd;
  wire  [512               -1:0]        mst_npu_mst4_axi_ibp_rd_data;
  wire                                  mst_npu_mst4_axi_ibp_rd_last;

  wire                                  mst_npu_mst4_axi_ibp_wr_valid;
  wire                                  mst_npu_mst4_axi_ibp_wr_accept;
  wire  [512               -1:0]        mst_npu_mst4_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        mst_npu_mst4_axi_ibp_wr_mask;
  wire                                  mst_npu_mst4_axi_ibp_wr_last;

  wire                                  mst_npu_mst4_axi_ibp_wr_done;
  wire                                  mst_npu_mst4_axi_ibp_wr_excl_done;
  wire                                  mst_npu_mst4_axi_ibp_err_wr;
  wire                                  mst_npu_mst4_axi_ibp_wr_resp_accept;
wire [1-1:0] mst_npu_mst4_axi_ibp_cmd_rgon;



 wire [1-1:0] mst_npu_mst4_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_npu_mst4_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_npu_mst4_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_npu_mst4_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_npu_mst4_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] mst_npu_mst4_axi_ibp_wd_chnl;

 wire [1-1:0] mst_npu_mst4_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_npu_mst4_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] mst_npu_mst4_axi_ibp_rd_chnl;

 wire [1-1:0] mst_npu_mst4_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_npu_mst4_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_npu_mst4_axi_ibp_wrsp_chnl;

wire [1-1:0]mst_npu_mst4_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] mst_o_npu_mst4_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_o_npu_mst4_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_o_npu_mst4_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_o_npu_mst4_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_o_npu_mst4_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] mst_o_npu_mst4_axi_ibp_wd_chnl;

 wire [1-1:0] mst_o_npu_mst4_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_o_npu_mst4_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] mst_o_npu_mst4_axi_ibp_rd_chnl;

 wire [1-1:0] mst_o_npu_mst4_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_o_npu_mst4_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_o_npu_mst4_axi_ibp_wrsp_chnl;

wire [1-1:0] mst_o_npu_mst4_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] lat_i_npu_mst4_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] lat_i_npu_mst4_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] lat_i_npu_mst4_axi_ibp_cmd_chnl;

 wire [1-1:0] lat_i_npu_mst4_axi_ibp_wd_chnl_valid;
 wire [1-1:0] lat_i_npu_mst4_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] lat_i_npu_mst4_axi_ibp_wd_chnl;

 wire [1-1:0] lat_i_npu_mst4_axi_ibp_rd_chnl_accept;
 wire [1-1:0] lat_i_npu_mst4_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] lat_i_npu_mst4_axi_ibp_rd_chnl;

 wire [1-1:0] lat_i_npu_mst4_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] lat_i_npu_mst4_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] lat_i_npu_mst4_axi_ibp_wrsp_chnl;

wire [1-1:0] lat_i_npu_mst4_axi_ibp_cmd_chnl_rgon;


  wire                                  lat_i_npu_mst4_axi_ibp_cmd_valid;
  wire                                  lat_i_npu_mst4_axi_ibp_cmd_accept;
  wire                                  lat_i_npu_mst4_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_i_npu_mst4_axi_ibp_cmd_addr;
  wire                                  lat_i_npu_mst4_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_i_npu_mst4_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_i_npu_mst4_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_i_npu_mst4_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_i_npu_mst4_axi_ibp_cmd_cache;
  wire                                  lat_i_npu_mst4_axi_ibp_cmd_lock;
  wire                                  lat_i_npu_mst4_axi_ibp_cmd_excl;

  wire                                  lat_i_npu_mst4_axi_ibp_rd_valid;
  wire                                  lat_i_npu_mst4_axi_ibp_rd_excl_ok;
  wire                                  lat_i_npu_mst4_axi_ibp_rd_accept;
  wire                                  lat_i_npu_mst4_axi_ibp_err_rd;
  wire  [512               -1:0]        lat_i_npu_mst4_axi_ibp_rd_data;
  wire                                  lat_i_npu_mst4_axi_ibp_rd_last;

  wire                                  lat_i_npu_mst4_axi_ibp_wr_valid;
  wire                                  lat_i_npu_mst4_axi_ibp_wr_accept;
  wire  [512               -1:0]        lat_i_npu_mst4_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        lat_i_npu_mst4_axi_ibp_wr_mask;
  wire                                  lat_i_npu_mst4_axi_ibp_wr_last;

  wire                                  lat_i_npu_mst4_axi_ibp_wr_done;
  wire                                  lat_i_npu_mst4_axi_ibp_wr_excl_done;
  wire                                  lat_i_npu_mst4_axi_ibp_err_wr;
  wire                                  lat_i_npu_mst4_axi_ibp_wr_resp_accept;


  wire                                  lat_o_npu_mst4_axi_ibp_cmd_valid;
  wire                                  lat_o_npu_mst4_axi_ibp_cmd_accept;
  wire                                  lat_o_npu_mst4_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_o_npu_mst4_axi_ibp_cmd_addr;
  wire                                  lat_o_npu_mst4_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_o_npu_mst4_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_o_npu_mst4_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_o_npu_mst4_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_o_npu_mst4_axi_ibp_cmd_cache;
  wire                                  lat_o_npu_mst4_axi_ibp_cmd_lock;
  wire                                  lat_o_npu_mst4_axi_ibp_cmd_excl;

  wire                                  lat_o_npu_mst4_axi_ibp_rd_valid;
  wire                                  lat_o_npu_mst4_axi_ibp_rd_excl_ok;
  wire                                  lat_o_npu_mst4_axi_ibp_rd_accept;
  wire                                  lat_o_npu_mst4_axi_ibp_err_rd;
  wire  [512               -1:0]        lat_o_npu_mst4_axi_ibp_rd_data;
  wire                                  lat_o_npu_mst4_axi_ibp_rd_last;

  wire                                  lat_o_npu_mst4_axi_ibp_wr_valid;
  wire                                  lat_o_npu_mst4_axi_ibp_wr_accept;
  wire  [512               -1:0]        lat_o_npu_mst4_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        lat_o_npu_mst4_axi_ibp_wr_mask;
  wire                                  lat_o_npu_mst4_axi_ibp_wr_last;

  wire                                  lat_o_npu_mst4_axi_ibp_wr_done;
  wire                                  lat_o_npu_mst4_axi_ibp_wr_excl_done;
  wire                                  lat_o_npu_mst4_axi_ibp_err_wr;
  wire                                  lat_o_npu_mst4_axi_ibp_wr_resp_accept;


  wire                                  mst_host_axi_ibp_cmd_valid;
  wire                                  mst_host_axi_ibp_cmd_accept;
  wire                                  mst_host_axi_ibp_cmd_read;
  wire  [49                -1:0]       mst_host_axi_ibp_cmd_addr;
  wire                                  mst_host_axi_ibp_cmd_wrap;
  wire  [3-1:0]       mst_host_axi_ibp_cmd_data_size;
  wire  [4-1:0]       mst_host_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       mst_host_axi_ibp_cmd_prot;
  wire  [4-1:0]       mst_host_axi_ibp_cmd_cache;
  wire                                  mst_host_axi_ibp_cmd_lock;
  wire                                  mst_host_axi_ibp_cmd_excl;

  wire                                  mst_host_axi_ibp_rd_valid;
  wire                                  mst_host_axi_ibp_rd_excl_ok;
  wire                                  mst_host_axi_ibp_rd_accept;
  wire                                  mst_host_axi_ibp_err_rd;
  wire  [64               -1:0]        mst_host_axi_ibp_rd_data;
  wire                                  mst_host_axi_ibp_rd_last;

  wire                                  mst_host_axi_ibp_wr_valid;
  wire                                  mst_host_axi_ibp_wr_accept;
  wire  [64               -1:0]        mst_host_axi_ibp_wr_data;
  wire  [(64         /8)  -1:0]        mst_host_axi_ibp_wr_mask;
  wire                                  mst_host_axi_ibp_wr_last;

  wire                                  mst_host_axi_ibp_wr_done;
  wire                                  mst_host_axi_ibp_wr_excl_done;
  wire                                  mst_host_axi_ibp_err_wr;
  wire                                  mst_host_axi_ibp_wr_resp_accept;
wire [1-1:0] mst_host_axi_ibp_cmd_rgon;



 wire [1-1:0] mst_host_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_host_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_host_axi_ibp_cmd_chnl;

 wire [1-1:0] mst_host_axi_ibp_wd_chnl_valid;
 wire [1-1:0] mst_host_axi_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] mst_host_axi_ibp_wd_chnl;

 wire [1-1:0] mst_host_axi_ibp_rd_chnl_accept;
 wire [1-1:0] mst_host_axi_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] mst_host_axi_ibp_rd_chnl;

 wire [1-1:0] mst_host_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_host_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_host_axi_ibp_wrsp_chnl;

wire [1-1:0]mst_host_axi_ibp_cmd_chnl_rgon;



 wire [1-1:0] lat_i_host_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] lat_i_host_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] lat_i_host_axi_ibp_cmd_chnl;

 wire [1-1:0] lat_i_host_axi_ibp_wd_chnl_valid;
 wire [1-1:0] lat_i_host_axi_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] lat_i_host_axi_ibp_wd_chnl;

 wire [1-1:0] lat_i_host_axi_ibp_rd_chnl_accept;
 wire [1-1:0] lat_i_host_axi_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] lat_i_host_axi_ibp_rd_chnl;

 wire [1-1:0] lat_i_host_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] lat_i_host_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] lat_i_host_axi_ibp_wrsp_chnl;

wire [1-1:0] lat_i_host_axi_ibp_cmd_chnl_rgon;


  wire                                  lat_i_host_axi_ibp_cmd_valid;
  wire                                  lat_i_host_axi_ibp_cmd_accept;
  wire                                  lat_i_host_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_i_host_axi_ibp_cmd_addr;
  wire                                  lat_i_host_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_i_host_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_i_host_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_i_host_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_i_host_axi_ibp_cmd_cache;
  wire                                  lat_i_host_axi_ibp_cmd_lock;
  wire                                  lat_i_host_axi_ibp_cmd_excl;

  wire                                  lat_i_host_axi_ibp_rd_valid;
  wire                                  lat_i_host_axi_ibp_rd_excl_ok;
  wire                                  lat_i_host_axi_ibp_rd_accept;
  wire                                  lat_i_host_axi_ibp_err_rd;
  wire  [64               -1:0]        lat_i_host_axi_ibp_rd_data;
  wire                                  lat_i_host_axi_ibp_rd_last;

  wire                                  lat_i_host_axi_ibp_wr_valid;
  wire                                  lat_i_host_axi_ibp_wr_accept;
  wire  [64               -1:0]        lat_i_host_axi_ibp_wr_data;
  wire  [(64         /8)  -1:0]        lat_i_host_axi_ibp_wr_mask;
  wire                                  lat_i_host_axi_ibp_wr_last;

  wire                                  lat_i_host_axi_ibp_wr_done;
  wire                                  lat_i_host_axi_ibp_wr_excl_done;
  wire                                  lat_i_host_axi_ibp_err_wr;
  wire                                  lat_i_host_axi_ibp_wr_resp_accept;


  wire                                  lat_o_host_axi_ibp_cmd_valid;
  wire                                  lat_o_host_axi_ibp_cmd_accept;
  wire                                  lat_o_host_axi_ibp_cmd_read;
  wire  [49                -1:0]       lat_o_host_axi_ibp_cmd_addr;
  wire                                  lat_o_host_axi_ibp_cmd_wrap;
  wire  [3-1:0]       lat_o_host_axi_ibp_cmd_data_size;
  wire  [4-1:0]       lat_o_host_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_o_host_axi_ibp_cmd_prot;
  wire  [4-1:0]       lat_o_host_axi_ibp_cmd_cache;
  wire                                  lat_o_host_axi_ibp_cmd_lock;
  wire                                  lat_o_host_axi_ibp_cmd_excl;

  wire                                  lat_o_host_axi_ibp_rd_valid;
  wire                                  lat_o_host_axi_ibp_rd_excl_ok;
  wire                                  lat_o_host_axi_ibp_rd_accept;
  wire                                  lat_o_host_axi_ibp_err_rd;
  wire  [64               -1:0]        lat_o_host_axi_ibp_rd_data;
  wire                                  lat_o_host_axi_ibp_rd_last;

  wire                                  lat_o_host_axi_ibp_wr_valid;
  wire                                  lat_o_host_axi_ibp_wr_accept;
  wire  [64               -1:0]        lat_o_host_axi_ibp_wr_data;
  wire  [(64         /8)  -1:0]        lat_o_host_axi_ibp_wr_mask;
  wire                                  lat_o_host_axi_ibp_wr_last;

  wire                                  lat_o_host_axi_ibp_wr_done;
  wire                                  lat_o_host_axi_ibp_wr_excl_done;
  wire                                  lat_o_host_axi_ibp_err_wr;
  wire                                  lat_o_host_axi_ibp_wr_resp_accept;


  wire                                  mst_bri4tb_ibp_cmd_valid;
  wire                                  mst_bri4tb_ibp_cmd_accept;
  wire                                  mst_bri4tb_ibp_cmd_read;
  wire  [49                -1:0]       mst_bri4tb_ibp_cmd_addr;
  wire                                  mst_bri4tb_ibp_cmd_wrap;
  wire  [3-1:0]       mst_bri4tb_ibp_cmd_data_size;
  wire  [4-1:0]       mst_bri4tb_ibp_cmd_burst_size;
  wire  [2-1:0]       mst_bri4tb_ibp_cmd_prot;
  wire  [4-1:0]       mst_bri4tb_ibp_cmd_cache;
  wire                                  mst_bri4tb_ibp_cmd_lock;
  wire                                  mst_bri4tb_ibp_cmd_excl;

  wire                                  mst_bri4tb_ibp_rd_valid;
  wire                                  mst_bri4tb_ibp_rd_excl_ok;
  wire                                  mst_bri4tb_ibp_rd_accept;
  wire                                  mst_bri4tb_ibp_err_rd;
  wire  [32               -1:0]        mst_bri4tb_ibp_rd_data;
  wire                                  mst_bri4tb_ibp_rd_last;

  wire                                  mst_bri4tb_ibp_wr_valid;
  wire                                  mst_bri4tb_ibp_wr_accept;
  wire  [32               -1:0]        mst_bri4tb_ibp_wr_data;
  wire  [(32         /8)  -1:0]        mst_bri4tb_ibp_wr_mask;
  wire                                  mst_bri4tb_ibp_wr_last;

  wire                                  mst_bri4tb_ibp_wr_done;
  wire                                  mst_bri4tb_ibp_wr_excl_done;
  wire                                  mst_bri4tb_ibp_err_wr;
  wire                                  mst_bri4tb_ibp_wr_resp_accept;
wire [1-1:0] mst_bri4tb_ibp_cmd_rgon;



 wire [1-1:0] mst_bri4tb_ibp_cmd_chnl_valid;
 wire [1-1:0] mst_bri4tb_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] mst_bri4tb_ibp_cmd_chnl;

 wire [1-1:0] mst_bri4tb_ibp_wd_chnl_valid;
 wire [1-1:0] mst_bri4tb_ibp_wd_chnl_accept;
 wire [37 * 1 -1:0] mst_bri4tb_ibp_wd_chnl;

 wire [1-1:0] mst_bri4tb_ibp_rd_chnl_accept;
 wire [1-1:0] mst_bri4tb_ibp_rd_chnl_valid;
 wire [35 * 1 -1:0] mst_bri4tb_ibp_rd_chnl;

 wire [1-1:0] mst_bri4tb_ibp_wrsp_chnl_valid;
 wire [1-1:0] mst_bri4tb_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mst_bri4tb_ibp_wrsp_chnl;

wire [1-1:0]mst_bri4tb_ibp_cmd_chnl_rgon;



 wire [1-1:0] lat_i_bri4tb_ibp_cmd_chnl_valid;
 wire [1-1:0] lat_i_bri4tb_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] lat_i_bri4tb_ibp_cmd_chnl;

 wire [1-1:0] lat_i_bri4tb_ibp_wd_chnl_valid;
 wire [1-1:0] lat_i_bri4tb_ibp_wd_chnl_accept;
 wire [37 * 1 -1:0] lat_i_bri4tb_ibp_wd_chnl;

 wire [1-1:0] lat_i_bri4tb_ibp_rd_chnl_accept;
 wire [1-1:0] lat_i_bri4tb_ibp_rd_chnl_valid;
 wire [35 * 1 -1:0] lat_i_bri4tb_ibp_rd_chnl;

 wire [1-1:0] lat_i_bri4tb_ibp_wrsp_chnl_valid;
 wire [1-1:0] lat_i_bri4tb_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] lat_i_bri4tb_ibp_wrsp_chnl;

wire [1-1:0] lat_i_bri4tb_ibp_cmd_chnl_rgon;


  wire                                  lat_i_bri4tb_ibp_cmd_valid;
  wire                                  lat_i_bri4tb_ibp_cmd_accept;
  wire                                  lat_i_bri4tb_ibp_cmd_read;
  wire  [49                -1:0]       lat_i_bri4tb_ibp_cmd_addr;
  wire                                  lat_i_bri4tb_ibp_cmd_wrap;
  wire  [3-1:0]       lat_i_bri4tb_ibp_cmd_data_size;
  wire  [4-1:0]       lat_i_bri4tb_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_i_bri4tb_ibp_cmd_prot;
  wire  [4-1:0]       lat_i_bri4tb_ibp_cmd_cache;
  wire                                  lat_i_bri4tb_ibp_cmd_lock;
  wire                                  lat_i_bri4tb_ibp_cmd_excl;

  wire                                  lat_i_bri4tb_ibp_rd_valid;
  wire                                  lat_i_bri4tb_ibp_rd_excl_ok;
  wire                                  lat_i_bri4tb_ibp_rd_accept;
  wire                                  lat_i_bri4tb_ibp_err_rd;
  wire  [32               -1:0]        lat_i_bri4tb_ibp_rd_data;
  wire                                  lat_i_bri4tb_ibp_rd_last;

  wire                                  lat_i_bri4tb_ibp_wr_valid;
  wire                                  lat_i_bri4tb_ibp_wr_accept;
  wire  [32               -1:0]        lat_i_bri4tb_ibp_wr_data;
  wire  [(32         /8)  -1:0]        lat_i_bri4tb_ibp_wr_mask;
  wire                                  lat_i_bri4tb_ibp_wr_last;

  wire                                  lat_i_bri4tb_ibp_wr_done;
  wire                                  lat_i_bri4tb_ibp_wr_excl_done;
  wire                                  lat_i_bri4tb_ibp_err_wr;
  wire                                  lat_i_bri4tb_ibp_wr_resp_accept;


  wire                                  lat_o_bri4tb_ibp_cmd_valid;
  wire                                  lat_o_bri4tb_ibp_cmd_accept;
  wire                                  lat_o_bri4tb_ibp_cmd_read;
  wire  [49                -1:0]       lat_o_bri4tb_ibp_cmd_addr;
  wire                                  lat_o_bri4tb_ibp_cmd_wrap;
  wire  [3-1:0]       lat_o_bri4tb_ibp_cmd_data_size;
  wire  [4-1:0]       lat_o_bri4tb_ibp_cmd_burst_size;
  wire  [2-1:0]       lat_o_bri4tb_ibp_cmd_prot;
  wire  [4-1:0]       lat_o_bri4tb_ibp_cmd_cache;
  wire                                  lat_o_bri4tb_ibp_cmd_lock;
  wire                                  lat_o_bri4tb_ibp_cmd_excl;

  wire                                  lat_o_bri4tb_ibp_rd_valid;
  wire                                  lat_o_bri4tb_ibp_rd_excl_ok;
  wire                                  lat_o_bri4tb_ibp_rd_accept;
  wire                                  lat_o_bri4tb_ibp_err_rd;
  wire  [32               -1:0]        lat_o_bri4tb_ibp_rd_data;
  wire                                  lat_o_bri4tb_ibp_rd_last;

  wire                                  lat_o_bri4tb_ibp_wr_valid;
  wire                                  lat_o_bri4tb_ibp_wr_accept;
  wire  [32               -1:0]        lat_o_bri4tb_ibp_wr_data;
  wire  [(32         /8)  -1:0]        lat_o_bri4tb_ibp_wr_mask;
  wire                                  lat_o_bri4tb_ibp_wr_last;

  wire                                  lat_o_bri4tb_ibp_wr_done;
  wire                                  lat_o_bri4tb_ibp_wr_excl_done;
  wire                                  lat_o_bri4tb_ibp_err_wr;
  wire                                  lat_o_bri4tb_ibp_wr_resp_accept;
//
//wires for slave side
//

  wire                                  bs_o_npu_dmi0_axi_ibp_cmd_valid;
  wire                                  bs_o_npu_dmi0_axi_ibp_cmd_accept;
  wire                                  bs_o_npu_dmi0_axi_ibp_cmd_read;
  wire  [49                -1:0]       bs_o_npu_dmi0_axi_ibp_cmd_addr;
  wire                                  bs_o_npu_dmi0_axi_ibp_cmd_wrap;
  wire  [3-1:0]       bs_o_npu_dmi0_axi_ibp_cmd_data_size;
  wire  [4-1:0]       bs_o_npu_dmi0_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       bs_o_npu_dmi0_axi_ibp_cmd_prot;
  wire  [4-1:0]       bs_o_npu_dmi0_axi_ibp_cmd_cache;
  wire                                  bs_o_npu_dmi0_axi_ibp_cmd_lock;
  wire                                  bs_o_npu_dmi0_axi_ibp_cmd_excl;

  wire                                  bs_o_npu_dmi0_axi_ibp_rd_valid;
  wire                                  bs_o_npu_dmi0_axi_ibp_rd_excl_ok;
  wire                                  bs_o_npu_dmi0_axi_ibp_rd_accept;
  wire                                  bs_o_npu_dmi0_axi_ibp_err_rd;
  wire  [512               -1:0]        bs_o_npu_dmi0_axi_ibp_rd_data;
  wire                                  bs_o_npu_dmi0_axi_ibp_rd_last;

  wire                                  bs_o_npu_dmi0_axi_ibp_wr_valid;
  wire                                  bs_o_npu_dmi0_axi_ibp_wr_accept;
  wire  [512               -1:0]        bs_o_npu_dmi0_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        bs_o_npu_dmi0_axi_ibp_wr_mask;
  wire                                  bs_o_npu_dmi0_axi_ibp_wr_last;

  wire                                  bs_o_npu_dmi0_axi_ibp_wr_done;
  wire                                  bs_o_npu_dmi0_axi_ibp_wr_excl_done;
  wire                                  bs_o_npu_dmi0_axi_ibp_err_wr;
  wire                                  bs_o_npu_dmi0_axi_ibp_wr_resp_accept;
wire [0-1:0] bs_o_npu_dmi0_axi_ibp_cmd_region;



 wire [1-1:0] bs_o_npu_dmi0_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] bs_o_npu_dmi0_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] bs_o_npu_dmi0_axi_ibp_cmd_chnl;

 wire [1-1:0] bs_o_npu_dmi0_axi_ibp_wd_chnl_valid;
 wire [1-1:0] bs_o_npu_dmi0_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] bs_o_npu_dmi0_axi_ibp_wd_chnl;

 wire [1-1:0] bs_o_npu_dmi0_axi_ibp_rd_chnl_accept;
 wire [1-1:0] bs_o_npu_dmi0_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] bs_o_npu_dmi0_axi_ibp_rd_chnl;

 wire [1-1:0] bs_o_npu_dmi0_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] bs_o_npu_dmi0_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bs_o_npu_dmi0_axi_ibp_wrsp_chnl;

wire [0-1:0] bs_o_npu_dmi0_axi_ibp_cmd_chnl_region;



 wire [1-1:0] slv_i_npu_dmi0_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] slv_i_npu_dmi0_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] slv_i_npu_dmi0_axi_ibp_cmd_chnl;

 wire [1-1:0] slv_i_npu_dmi0_axi_ibp_wd_chnl_valid;
 wire [1-1:0] slv_i_npu_dmi0_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] slv_i_npu_dmi0_axi_ibp_wd_chnl;

 wire [1-1:0] slv_i_npu_dmi0_axi_ibp_rd_chnl_accept;
 wire [1-1:0] slv_i_npu_dmi0_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] slv_i_npu_dmi0_axi_ibp_rd_chnl;

 wire [1-1:0] slv_i_npu_dmi0_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] slv_i_npu_dmi0_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] slv_i_npu_dmi0_axi_ibp_wrsp_chnl;

wire [0-1:0] slv_i_npu_dmi0_axi_ibp_cmd_chnl_region;



 wire [1-1:0] slv_o_npu_dmi0_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] slv_o_npu_dmi0_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] slv_o_npu_dmi0_axi_ibp_cmd_chnl;

 wire [1-1:0] slv_o_npu_dmi0_axi_ibp_wd_chnl_valid;
 wire [1-1:0] slv_o_npu_dmi0_axi_ibp_wd_chnl_accept;
 wire [577 * 1 -1:0] slv_o_npu_dmi0_axi_ibp_wd_chnl;

 wire [1-1:0] slv_o_npu_dmi0_axi_ibp_rd_chnl_accept;
 wire [1-1:0] slv_o_npu_dmi0_axi_ibp_rd_chnl_valid;
 wire [515 * 1 -1:0] slv_o_npu_dmi0_axi_ibp_rd_chnl;

 wire [1-1:0] slv_o_npu_dmi0_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] slv_o_npu_dmi0_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] slv_o_npu_dmi0_axi_ibp_wrsp_chnl;

wire [0-1:0] slv_o_npu_dmi0_axi_ibp_cmd_chnl_region;


  wire                                  slv_o_npu_dmi0_axi_ibp_cmd_valid;
  wire                                  slv_o_npu_dmi0_axi_ibp_cmd_accept;
  wire                                  slv_o_npu_dmi0_axi_ibp_cmd_read;
  wire  [49                -1:0]       slv_o_npu_dmi0_axi_ibp_cmd_addr;
  wire                                  slv_o_npu_dmi0_axi_ibp_cmd_wrap;
  wire  [3-1:0]       slv_o_npu_dmi0_axi_ibp_cmd_data_size;
  wire  [4-1:0]       slv_o_npu_dmi0_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       slv_o_npu_dmi0_axi_ibp_cmd_prot;
  wire  [4-1:0]       slv_o_npu_dmi0_axi_ibp_cmd_cache;
  wire                                  slv_o_npu_dmi0_axi_ibp_cmd_lock;
  wire                                  slv_o_npu_dmi0_axi_ibp_cmd_excl;

  wire                                  slv_o_npu_dmi0_axi_ibp_rd_valid;
  wire                                  slv_o_npu_dmi0_axi_ibp_rd_excl_ok;
  wire                                  slv_o_npu_dmi0_axi_ibp_rd_accept;
  wire                                  slv_o_npu_dmi0_axi_ibp_err_rd;
  wire  [512               -1:0]        slv_o_npu_dmi0_axi_ibp_rd_data;
  wire                                  slv_o_npu_dmi0_axi_ibp_rd_last;

  wire                                  slv_o_npu_dmi0_axi_ibp_wr_valid;
  wire                                  slv_o_npu_dmi0_axi_ibp_wr_accept;
  wire  [512               -1:0]        slv_o_npu_dmi0_axi_ibp_wr_data;
  wire  [(512         /8)  -1:0]        slv_o_npu_dmi0_axi_ibp_wr_mask;
  wire                                  slv_o_npu_dmi0_axi_ibp_wr_last;

  wire                                  slv_o_npu_dmi0_axi_ibp_wr_done;
  wire                                  slv_o_npu_dmi0_axi_ibp_wr_excl_done;
  wire                                  slv_o_npu_dmi0_axi_ibp_err_wr;
  wire                                  slv_o_npu_dmi0_axi_ibp_wr_resp_accept;
wire [0-1:0] slv_o_npu_dmi0_axi_ibp_cmd_region;


  wire                                  bs_o_npu_cfg_axi_ibp_cmd_valid;
  wire                                  bs_o_npu_cfg_axi_ibp_cmd_accept;
  wire                                  bs_o_npu_cfg_axi_ibp_cmd_read;
  wire  [49                -1:0]       bs_o_npu_cfg_axi_ibp_cmd_addr;
  wire                                  bs_o_npu_cfg_axi_ibp_cmd_wrap;
  wire  [3-1:0]       bs_o_npu_cfg_axi_ibp_cmd_data_size;
  wire  [4-1:0]       bs_o_npu_cfg_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       bs_o_npu_cfg_axi_ibp_cmd_prot;
  wire  [4-1:0]       bs_o_npu_cfg_axi_ibp_cmd_cache;
  wire                                  bs_o_npu_cfg_axi_ibp_cmd_lock;
  wire                                  bs_o_npu_cfg_axi_ibp_cmd_excl;

  wire                                  bs_o_npu_cfg_axi_ibp_rd_valid;
  wire                                  bs_o_npu_cfg_axi_ibp_rd_excl_ok;
  wire                                  bs_o_npu_cfg_axi_ibp_rd_accept;
  wire                                  bs_o_npu_cfg_axi_ibp_err_rd;
  wire  [32               -1:0]        bs_o_npu_cfg_axi_ibp_rd_data;
  wire                                  bs_o_npu_cfg_axi_ibp_rd_last;

  wire                                  bs_o_npu_cfg_axi_ibp_wr_valid;
  wire                                  bs_o_npu_cfg_axi_ibp_wr_accept;
  wire  [32               -1:0]        bs_o_npu_cfg_axi_ibp_wr_data;
  wire  [(32         /8)  -1:0]        bs_o_npu_cfg_axi_ibp_wr_mask;
  wire                                  bs_o_npu_cfg_axi_ibp_wr_last;

  wire                                  bs_o_npu_cfg_axi_ibp_wr_done;
  wire                                  bs_o_npu_cfg_axi_ibp_wr_excl_done;
  wire                                  bs_o_npu_cfg_axi_ibp_err_wr;
  wire                                  bs_o_npu_cfg_axi_ibp_wr_resp_accept;
wire [0-1:0] bs_o_npu_cfg_axi_ibp_cmd_region;



 wire [1-1:0] bs_o_npu_cfg_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] bs_o_npu_cfg_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] bs_o_npu_cfg_axi_ibp_cmd_chnl;

 wire [1-1:0] bs_o_npu_cfg_axi_ibp_wd_chnl_valid;
 wire [1-1:0] bs_o_npu_cfg_axi_ibp_wd_chnl_accept;
 wire [37 * 1 -1:0] bs_o_npu_cfg_axi_ibp_wd_chnl;

 wire [1-1:0] bs_o_npu_cfg_axi_ibp_rd_chnl_accept;
 wire [1-1:0] bs_o_npu_cfg_axi_ibp_rd_chnl_valid;
 wire [35 * 1 -1:0] bs_o_npu_cfg_axi_ibp_rd_chnl;

 wire [1-1:0] bs_o_npu_cfg_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] bs_o_npu_cfg_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bs_o_npu_cfg_axi_ibp_wrsp_chnl;

wire [0-1:0] bs_o_npu_cfg_axi_ibp_cmd_chnl_region;



 wire [1-1:0] slv_i_npu_cfg_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] slv_i_npu_cfg_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] slv_i_npu_cfg_axi_ibp_cmd_chnl;

 wire [1-1:0] slv_i_npu_cfg_axi_ibp_wd_chnl_valid;
 wire [1-1:0] slv_i_npu_cfg_axi_ibp_wd_chnl_accept;
 wire [37 * 1 -1:0] slv_i_npu_cfg_axi_ibp_wd_chnl;

 wire [1-1:0] slv_i_npu_cfg_axi_ibp_rd_chnl_accept;
 wire [1-1:0] slv_i_npu_cfg_axi_ibp_rd_chnl_valid;
 wire [35 * 1 -1:0] slv_i_npu_cfg_axi_ibp_rd_chnl;

 wire [1-1:0] slv_i_npu_cfg_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] slv_i_npu_cfg_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] slv_i_npu_cfg_axi_ibp_wrsp_chnl;

wire [0-1:0] slv_i_npu_cfg_axi_ibp_cmd_chnl_region;



 wire [1-1:0] slv_o_npu_cfg_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] slv_o_npu_cfg_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] slv_o_npu_cfg_axi_ibp_cmd_chnl;

 wire [1-1:0] slv_o_npu_cfg_axi_ibp_wd_chnl_valid;
 wire [1-1:0] slv_o_npu_cfg_axi_ibp_wd_chnl_accept;
 wire [37 * 1 -1:0] slv_o_npu_cfg_axi_ibp_wd_chnl;

 wire [1-1:0] slv_o_npu_cfg_axi_ibp_rd_chnl_accept;
 wire [1-1:0] slv_o_npu_cfg_axi_ibp_rd_chnl_valid;
 wire [35 * 1 -1:0] slv_o_npu_cfg_axi_ibp_rd_chnl;

 wire [1-1:0] slv_o_npu_cfg_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] slv_o_npu_cfg_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] slv_o_npu_cfg_axi_ibp_wrsp_chnl;

wire [0-1:0] slv_o_npu_cfg_axi_ibp_cmd_chnl_region;


  wire                                  slv_o_npu_cfg_axi_ibp_cmd_valid;
  wire                                  slv_o_npu_cfg_axi_ibp_cmd_accept;
  wire                                  slv_o_npu_cfg_axi_ibp_cmd_read;
  wire  [49                -1:0]       slv_o_npu_cfg_axi_ibp_cmd_addr;
  wire                                  slv_o_npu_cfg_axi_ibp_cmd_wrap;
  wire  [3-1:0]       slv_o_npu_cfg_axi_ibp_cmd_data_size;
  wire  [4-1:0]       slv_o_npu_cfg_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       slv_o_npu_cfg_axi_ibp_cmd_prot;
  wire  [4-1:0]       slv_o_npu_cfg_axi_ibp_cmd_cache;
  wire                                  slv_o_npu_cfg_axi_ibp_cmd_lock;
  wire                                  slv_o_npu_cfg_axi_ibp_cmd_excl;

  wire                                  slv_o_npu_cfg_axi_ibp_rd_valid;
  wire                                  slv_o_npu_cfg_axi_ibp_rd_excl_ok;
  wire                                  slv_o_npu_cfg_axi_ibp_rd_accept;
  wire                                  slv_o_npu_cfg_axi_ibp_err_rd;
  wire  [32               -1:0]        slv_o_npu_cfg_axi_ibp_rd_data;
  wire                                  slv_o_npu_cfg_axi_ibp_rd_last;

  wire                                  slv_o_npu_cfg_axi_ibp_wr_valid;
  wire                                  slv_o_npu_cfg_axi_ibp_wr_accept;
  wire  [32               -1:0]        slv_o_npu_cfg_axi_ibp_wr_data;
  wire  [(32         /8)  -1:0]        slv_o_npu_cfg_axi_ibp_wr_mask;
  wire                                  slv_o_npu_cfg_axi_ibp_wr_last;

  wire                                  slv_o_npu_cfg_axi_ibp_wr_done;
  wire                                  slv_o_npu_cfg_axi_ibp_wr_excl_done;
  wire                                  slv_o_npu_cfg_axi_ibp_err_wr;
  wire                                  slv_o_npu_cfg_axi_ibp_wr_resp_accept;
wire [0-1:0] slv_o_npu_cfg_axi_ibp_cmd_region;


  wire                                  bs_o_arcsync_axi_ibp_cmd_valid;
  wire                                  bs_o_arcsync_axi_ibp_cmd_accept;
  wire                                  bs_o_arcsync_axi_ibp_cmd_read;
  wire  [49                -1:0]       bs_o_arcsync_axi_ibp_cmd_addr;
  wire                                  bs_o_arcsync_axi_ibp_cmd_wrap;
  wire  [3-1:0]       bs_o_arcsync_axi_ibp_cmd_data_size;
  wire  [4-1:0]       bs_o_arcsync_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       bs_o_arcsync_axi_ibp_cmd_prot;
  wire  [4-1:0]       bs_o_arcsync_axi_ibp_cmd_cache;
  wire                                  bs_o_arcsync_axi_ibp_cmd_lock;
  wire                                  bs_o_arcsync_axi_ibp_cmd_excl;

  wire                                  bs_o_arcsync_axi_ibp_rd_valid;
  wire                                  bs_o_arcsync_axi_ibp_rd_excl_ok;
  wire                                  bs_o_arcsync_axi_ibp_rd_accept;
  wire                                  bs_o_arcsync_axi_ibp_err_rd;
  wire  [64               -1:0]        bs_o_arcsync_axi_ibp_rd_data;
  wire                                  bs_o_arcsync_axi_ibp_rd_last;

  wire                                  bs_o_arcsync_axi_ibp_wr_valid;
  wire                                  bs_o_arcsync_axi_ibp_wr_accept;
  wire  [64               -1:0]        bs_o_arcsync_axi_ibp_wr_data;
  wire  [(64         /8)  -1:0]        bs_o_arcsync_axi_ibp_wr_mask;
  wire                                  bs_o_arcsync_axi_ibp_wr_last;

  wire                                  bs_o_arcsync_axi_ibp_wr_done;
  wire                                  bs_o_arcsync_axi_ibp_wr_excl_done;
  wire                                  bs_o_arcsync_axi_ibp_err_wr;
  wire                                  bs_o_arcsync_axi_ibp_wr_resp_accept;
wire [0-1:0] bs_o_arcsync_axi_ibp_cmd_region;



 wire [1-1:0] bs_o_arcsync_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] bs_o_arcsync_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] bs_o_arcsync_axi_ibp_cmd_chnl;

 wire [1-1:0] bs_o_arcsync_axi_ibp_wd_chnl_valid;
 wire [1-1:0] bs_o_arcsync_axi_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] bs_o_arcsync_axi_ibp_wd_chnl;

 wire [1-1:0] bs_o_arcsync_axi_ibp_rd_chnl_accept;
 wire [1-1:0] bs_o_arcsync_axi_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] bs_o_arcsync_axi_ibp_rd_chnl;

 wire [1-1:0] bs_o_arcsync_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] bs_o_arcsync_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bs_o_arcsync_axi_ibp_wrsp_chnl;

wire [0-1:0] bs_o_arcsync_axi_ibp_cmd_chnl_region;



 wire [1-1:0] slv_i_arcsync_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] slv_i_arcsync_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] slv_i_arcsync_axi_ibp_cmd_chnl;

 wire [1-1:0] slv_i_arcsync_axi_ibp_wd_chnl_valid;
 wire [1-1:0] slv_i_arcsync_axi_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] slv_i_arcsync_axi_ibp_wd_chnl;

 wire [1-1:0] slv_i_arcsync_axi_ibp_rd_chnl_accept;
 wire [1-1:0] slv_i_arcsync_axi_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] slv_i_arcsync_axi_ibp_rd_chnl;

 wire [1-1:0] slv_i_arcsync_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] slv_i_arcsync_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] slv_i_arcsync_axi_ibp_wrsp_chnl;

wire [0-1:0] slv_i_arcsync_axi_ibp_cmd_chnl_region;



 wire [1-1:0] slv_o_arcsync_axi_ibp_cmd_chnl_valid;
 wire [1-1:0] slv_o_arcsync_axi_ibp_cmd_chnl_accept;
 wire [66 * 1 -1:0] slv_o_arcsync_axi_ibp_cmd_chnl;

 wire [1-1:0] slv_o_arcsync_axi_ibp_wd_chnl_valid;
 wire [1-1:0] slv_o_arcsync_axi_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] slv_o_arcsync_axi_ibp_wd_chnl;

 wire [1-1:0] slv_o_arcsync_axi_ibp_rd_chnl_accept;
 wire [1-1:0] slv_o_arcsync_axi_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] slv_o_arcsync_axi_ibp_rd_chnl;

 wire [1-1:0] slv_o_arcsync_axi_ibp_wrsp_chnl_valid;
 wire [1-1:0] slv_o_arcsync_axi_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] slv_o_arcsync_axi_ibp_wrsp_chnl;

wire [0-1:0] slv_o_arcsync_axi_ibp_cmd_chnl_region;


  wire                                  slv_o_arcsync_axi_ibp_cmd_valid;
  wire                                  slv_o_arcsync_axi_ibp_cmd_accept;
  wire                                  slv_o_arcsync_axi_ibp_cmd_read;
  wire  [49                -1:0]       slv_o_arcsync_axi_ibp_cmd_addr;
  wire                                  slv_o_arcsync_axi_ibp_cmd_wrap;
  wire  [3-1:0]       slv_o_arcsync_axi_ibp_cmd_data_size;
  wire  [4-1:0]       slv_o_arcsync_axi_ibp_cmd_burst_size;
  wire  [2-1:0]       slv_o_arcsync_axi_ibp_cmd_prot;
  wire  [4-1:0]       slv_o_arcsync_axi_ibp_cmd_cache;
  wire                                  slv_o_arcsync_axi_ibp_cmd_lock;
  wire                                  slv_o_arcsync_axi_ibp_cmd_excl;

  wire                                  slv_o_arcsync_axi_ibp_rd_valid;
  wire                                  slv_o_arcsync_axi_ibp_rd_excl_ok;
  wire                                  slv_o_arcsync_axi_ibp_rd_accept;
  wire                                  slv_o_arcsync_axi_ibp_err_rd;
  wire  [64               -1:0]        slv_o_arcsync_axi_ibp_rd_data;
  wire                                  slv_o_arcsync_axi_ibp_rd_last;

  wire                                  slv_o_arcsync_axi_ibp_wr_valid;
  wire                                  slv_o_arcsync_axi_ibp_wr_accept;
  wire  [64               -1:0]        slv_o_arcsync_axi_ibp_wr_data;
  wire  [(64         /8)  -1:0]        slv_o_arcsync_axi_ibp_wr_mask;
  wire                                  slv_o_arcsync_axi_ibp_wr_last;

  wire                                  slv_o_arcsync_axi_ibp_wr_done;
  wire                                  slv_o_arcsync_axi_ibp_wr_excl_done;
  wire                                  slv_o_arcsync_axi_ibp_err_wr;
  wire                                  slv_o_arcsync_axi_ibp_wr_resp_accept;
wire [0-1:0] slv_o_arcsync_axi_ibp_cmd_region;


  wire                                  bs_o_mss_mem_ibp_cmd_valid;
  wire                                  bs_o_mss_mem_ibp_cmd_accept;
  wire                                  bs_o_mss_mem_ibp_cmd_read;
  wire  [41                -1:0]       bs_o_mss_mem_ibp_cmd_addr;
  wire                                  bs_o_mss_mem_ibp_cmd_wrap;
  wire  [3-1:0]       bs_o_mss_mem_ibp_cmd_data_size;
  wire  [4-1:0]       bs_o_mss_mem_ibp_cmd_burst_size;
  wire  [2-1:0]       bs_o_mss_mem_ibp_cmd_prot;
  wire  [4-1:0]       bs_o_mss_mem_ibp_cmd_cache;
  wire                                  bs_o_mss_mem_ibp_cmd_lock;
  wire                                  bs_o_mss_mem_ibp_cmd_excl;

  wire                                  bs_o_mss_mem_ibp_rd_valid;
  wire                                  bs_o_mss_mem_ibp_rd_excl_ok;
  wire                                  bs_o_mss_mem_ibp_rd_accept;
  wire                                  bs_o_mss_mem_ibp_err_rd;
  wire  [128               -1:0]        bs_o_mss_mem_ibp_rd_data;
  wire                                  bs_o_mss_mem_ibp_rd_last;

  wire                                  bs_o_mss_mem_ibp_wr_valid;
  wire                                  bs_o_mss_mem_ibp_wr_accept;
  wire  [128               -1:0]        bs_o_mss_mem_ibp_wr_data;
  wire  [(128         /8)  -1:0]        bs_o_mss_mem_ibp_wr_mask;
  wire                                  bs_o_mss_mem_ibp_wr_last;

  wire                                  bs_o_mss_mem_ibp_wr_done;
  wire                                  bs_o_mss_mem_ibp_wr_excl_done;
  wire                                  bs_o_mss_mem_ibp_err_wr;
  wire                                  bs_o_mss_mem_ibp_wr_resp_accept;
wire [49-1:0]  bs_o_mss_mem_ibp_cmd_addr_temp;
wire [1-1:0] bs_o_mss_mem_ibp_cmd_region;



 wire [1-1:0] bs_o_mss_mem_ibp_cmd_chnl_valid;
 wire [1-1:0] bs_o_mss_mem_ibp_cmd_chnl_accept;
 wire [58 * 1 -1:0] bs_o_mss_mem_ibp_cmd_chnl;

 wire [1-1:0] bs_o_mss_mem_ibp_wd_chnl_valid;
 wire [1-1:0] bs_o_mss_mem_ibp_wd_chnl_accept;
 wire [145 * 1 -1:0] bs_o_mss_mem_ibp_wd_chnl;

 wire [1-1:0] bs_o_mss_mem_ibp_rd_chnl_accept;
 wire [1-1:0] bs_o_mss_mem_ibp_rd_chnl_valid;
 wire [131 * 1 -1:0] bs_o_mss_mem_ibp_rd_chnl;

 wire [1-1:0] bs_o_mss_mem_ibp_wrsp_chnl_valid;
 wire [1-1:0] bs_o_mss_mem_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bs_o_mss_mem_ibp_wrsp_chnl;

wire [1-1:0] bs_o_mss_mem_ibp_cmd_chnl_region;



 wire [1-1:0] slv_i_mss_mem_ibp_cmd_chnl_valid;
 wire [1-1:0] slv_i_mss_mem_ibp_cmd_chnl_accept;
 wire [58 * 1 -1:0] slv_i_mss_mem_ibp_cmd_chnl;

 wire [1-1:0] slv_i_mss_mem_ibp_wd_chnl_valid;
 wire [1-1:0] slv_i_mss_mem_ibp_wd_chnl_accept;
 wire [145 * 1 -1:0] slv_i_mss_mem_ibp_wd_chnl;

 wire [1-1:0] slv_i_mss_mem_ibp_rd_chnl_accept;
 wire [1-1:0] slv_i_mss_mem_ibp_rd_chnl_valid;
 wire [131 * 1 -1:0] slv_i_mss_mem_ibp_rd_chnl;

 wire [1-1:0] slv_i_mss_mem_ibp_wrsp_chnl_valid;
 wire [1-1:0] slv_i_mss_mem_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] slv_i_mss_mem_ibp_wrsp_chnl;

wire [1-1:0] slv_i_mss_mem_ibp_cmd_chnl_region;



 wire [1-1:0] slv_o_mss_mem_ibp_cmd_chnl_valid;
 wire [1-1:0] slv_o_mss_mem_ibp_cmd_chnl_accept;
 wire [58 * 1 -1:0] slv_o_mss_mem_ibp_cmd_chnl;

 wire [1-1:0] slv_o_mss_mem_ibp_wd_chnl_valid;
 wire [1-1:0] slv_o_mss_mem_ibp_wd_chnl_accept;
 wire [145 * 1 -1:0] slv_o_mss_mem_ibp_wd_chnl;

 wire [1-1:0] slv_o_mss_mem_ibp_rd_chnl_accept;
 wire [1-1:0] slv_o_mss_mem_ibp_rd_chnl_valid;
 wire [131 * 1 -1:0] slv_o_mss_mem_ibp_rd_chnl;

 wire [1-1:0] slv_o_mss_mem_ibp_wrsp_chnl_valid;
 wire [1-1:0] slv_o_mss_mem_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] slv_o_mss_mem_ibp_wrsp_chnl;

wire [1-1:0] slv_o_mss_mem_ibp_cmd_chnl_region;


  wire                                  slv_o_mss_mem_ibp_cmd_valid;
  wire                                  slv_o_mss_mem_ibp_cmd_accept;
  wire                                  slv_o_mss_mem_ibp_cmd_read;
  wire  [41                -1:0]       slv_o_mss_mem_ibp_cmd_addr;
  wire                                  slv_o_mss_mem_ibp_cmd_wrap;
  wire  [3-1:0]       slv_o_mss_mem_ibp_cmd_data_size;
  wire  [4-1:0]       slv_o_mss_mem_ibp_cmd_burst_size;
  wire  [2-1:0]       slv_o_mss_mem_ibp_cmd_prot;
  wire  [4-1:0]       slv_o_mss_mem_ibp_cmd_cache;
  wire                                  slv_o_mss_mem_ibp_cmd_lock;
  wire                                  slv_o_mss_mem_ibp_cmd_excl;

  wire                                  slv_o_mss_mem_ibp_rd_valid;
  wire                                  slv_o_mss_mem_ibp_rd_excl_ok;
  wire                                  slv_o_mss_mem_ibp_rd_accept;
  wire                                  slv_o_mss_mem_ibp_err_rd;
  wire  [128               -1:0]        slv_o_mss_mem_ibp_rd_data;
  wire                                  slv_o_mss_mem_ibp_rd_last;

  wire                                  slv_o_mss_mem_ibp_wr_valid;
  wire                                  slv_o_mss_mem_ibp_wr_accept;
  wire  [128               -1:0]        slv_o_mss_mem_ibp_wr_data;
  wire  [(128         /8)  -1:0]        slv_o_mss_mem_ibp_wr_mask;
  wire                                  slv_o_mss_mem_ibp_wr_last;

  wire                                  slv_o_mss_mem_ibp_wr_done;
  wire                                  slv_o_mss_mem_ibp_wr_excl_done;
  wire                                  slv_o_mss_mem_ibp_err_wr;
  wire                                  slv_o_mss_mem_ibp_wr_resp_accept;
wire [1-1:0] slv_o_mss_mem_ibp_cmd_region;

    // Latency unit and performance monitor interfaces, strapped to 0
    wire  [7*12-1:0]  mss_fab_cfg_lat_w;
    wire  [7*12-1:0]  mss_fab_cfg_lat_r;
    wire  [7*10-1:0]  mss_fab_cfg_wr_bw;
    wire  [7*10-1:0]  mss_fab_cfg_rd_bw;

    wire  [7-1:0]    mss_fab_perf_awf;
    wire  [7-1:0]    mss_fab_perf_arf;
    wire  [7-1:0]    mss_fab_perf_aw;
    wire  [7-1:0]    mss_fab_perf_ar;
    wire  [7-1:0]    mss_fab_perf_w;
    wire  [7-1:0]    mss_fab_perf_wl;
    wire  [7-1:0]    mss_fab_perf_r;
    wire  [7-1:0]    mss_fab_perf_rl;
    wire  [7-1:0]    mss_fab_perf_b;
    assign mss_fab_cfg_lat_w = {(7*12){1'b0}};
    assign mss_fab_cfg_lat_r = {(7*12){1'b0}};
    assign mss_fab_cfg_wr_bw = {(7*10){1'b0}};
    assign mss_fab_cfg_rd_bw = {(7*10){1'b0}};



    // Master protocol converters
    wire [3-1:0] npu_mst0_axi_port_id;        // master0 port ID
    wire [1-1:0] npu_mst0_axi_aruser_signal;  // master0 user signal, user_iw >= 1
    wire [1-1:0] npu_mst0_axi_awuser_signal;  // master0 user signal
    wire [4-1:0]   npu_mst0_axi_sb_raddr;       // master0 side-band address (exclude iw)
    wire [4-1:0]   npu_mst0_axi_sb_waddr;       // master0 side-band address (exclude iw)
    assign npu_mst0_axi_port_id = 0;
    assign npu_mst0_axi_aruser_signal = {
                                   npu_mst0_axi_arprot[1]
                                  };
    assign npu_mst0_axi_awuser_signal = {
                                   npu_mst0_axi_awprot[1]
                                  };
    assign npu_mst0_axi_sb_raddr = {npu_mst0_axi_aruser_signal
                             ,npu_mst0_axi_port_id
                             };
    assign npu_mst0_axi_sb_waddr = {npu_mst0_axi_awuser_signal
                             ,npu_mst0_axi_port_id
                             };
    alb_mss_fab_axi2ibp #(.FORCE_TO_SINGLE(0),
                          .X_W(64),
                          .Y_W(64),
                          .RGON_W(1),
                          .BYPBUF_DEPTH(16),
                          .BUS_ID_W(5),
                          .CHNL_FIFO_DEPTH(0),
                          .ADDR_W(49),
                          .DATA_W(64)) u_npu_mst0_axi_prot_inst(
                                                     // AXI I/F
                                                     //read addr chl
                                                     .axi_arvalid(npu_mst0_axi_arvalid),
                                                     .axi_arready(npu_mst0_axi_arready),
                                                     .axi_araddr({npu_mst0_axi_sb_raddr,npu_mst0_axi_arid,npu_mst0_axi_araddr}),
                                                     .axi_arcache(npu_mst0_axi_arcache),
                                                     .axi_arprot(npu_mst0_axi_arprot),
                                                     .axi_arlock({1'b0,npu_mst0_axi_arlock}),
                                                     .axi_arlen(npu_mst0_axi_arlen[3:0]),
                                                     .axi_arburst(npu_mst0_axi_arburst),
                                                     .axi_arsize(npu_mst0_axi_arsize),
                                                     .axi_arregion(1'd0),
                                                     .axi_arid(npu_mst0_axi_arid),
                                                     // read data chl
                                                     .axi_rvalid(npu_mst0_axi_rvalid),
                                                     .axi_rready(npu_mst0_axi_rready),
                                                     .axi_rdata(npu_mst0_axi_rdata),
                                                     .axi_rresp(npu_mst0_axi_rresp),
                                                     .axi_rlast(npu_mst0_axi_rlast),
                                                     .axi_rid(npu_mst0_axi_rid),
                                                     //write addr chl
                                                     .axi_awvalid(npu_mst0_axi_awvalid),
                                                     .axi_awready(npu_mst0_axi_awready),
                                                     .axi_awaddr({npu_mst0_axi_sb_waddr,npu_mst0_axi_awid,npu_mst0_axi_awaddr}),
                                                     .axi_awcache(npu_mst0_axi_awcache),
                                                     .axi_awprot(npu_mst0_axi_awprot),
                                                     .axi_awlock({1'b0,npu_mst0_axi_awlock}),
                                                     .axi_awlen(npu_mst0_axi_awlen[3:0]),
                                                     .axi_awburst(npu_mst0_axi_awburst),
                                                     .axi_awsize(npu_mst0_axi_awsize),
                                                     .axi_awregion(1'd0),
                                                     .axi_awid(npu_mst0_axi_awid),
                                                     // write data chl
                                                     .axi_wvalid(npu_mst0_axi_wvalid),
                                                     .axi_wready(npu_mst0_axi_wready),
                                                     .axi_wdata(npu_mst0_axi_wdata),
                                                     .axi_wstrb(npu_mst0_axi_wstrb),
                                                     .axi_wlast(npu_mst0_axi_wlast),
                                                     //write resp chl
                                                     .axi_bvalid(npu_mst0_axi_bvalid),
                                                     .axi_bready(npu_mst0_axi_bready),
                                                     .axi_bresp(npu_mst0_axi_bresp),
                                                     .axi_bid(npu_mst0_axi_bid),
                                                     //IBP I/F

  .ibp_cmd_valid             (mst_npu_mst0_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_npu_mst0_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_npu_mst0_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_npu_mst0_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_npu_mst0_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_npu_mst0_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_npu_mst0_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_npu_mst0_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_npu_mst0_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_npu_mst0_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_npu_mst0_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_npu_mst0_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_npu_mst0_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_npu_mst0_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_npu_mst0_axi_ibp_err_rd),
  .ibp_rd_data               (mst_npu_mst0_axi_ibp_rd_data),
  .ibp_rd_last               (mst_npu_mst0_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_npu_mst0_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_npu_mst0_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_npu_mst0_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_npu_mst0_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_npu_mst0_axi_ibp_wr_last),

  .ibp_wr_done               (mst_npu_mst0_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_npu_mst0_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_npu_mst0_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_npu_mst0_axi_ibp_wr_resp_accept),
                                                     .ibp_cmd_rgon(mst_npu_mst0_axi_ibp_cmd_rgon),
                                                     //clock and resets
                                                     .clk(clk),
                                                     .bus_clk_en(1'b1),
                                                     .sync_rst_r(~rst_b),
                                                     .rst_a(~rst_b)
                                                     );




    wire [3-1:0] npu_mst1_axi_port_id;        // master1 port ID
    wire [1-1:0] npu_mst1_axi_aruser_signal;  // master1 user signal, user_iw >= 1
    wire [1-1:0] npu_mst1_axi_awuser_signal;  // master1 user signal
    wire [4-1:0]   npu_mst1_axi_sb_raddr;       // master1 side-band address (exclude iw)
    wire [4-1:0]   npu_mst1_axi_sb_waddr;       // master1 side-band address (exclude iw)
    assign npu_mst1_axi_port_id = 1;
    assign npu_mst1_axi_aruser_signal = {
                                   npu_mst1_axi_arprot[1]
                                  };
    assign npu_mst1_axi_awuser_signal = {
                                   npu_mst1_axi_awprot[1]
                                  };
    assign npu_mst1_axi_sb_raddr = {npu_mst1_axi_aruser_signal
                             ,npu_mst1_axi_port_id
                             };
    assign npu_mst1_axi_sb_waddr = {npu_mst1_axi_awuser_signal
                             ,npu_mst1_axi_port_id
                             };
    alb_mss_fab_axi2ibp #(.FORCE_TO_SINGLE(0),
                          .X_W(512),
                          .Y_W(512),
                          .RGON_W(1),
                          .BYPBUF_DEPTH(16),
                          .BUS_ID_W(5),
                          .CHNL_FIFO_DEPTH(0),
                          .ADDR_W(49),
                          .DATA_W(512)) u_npu_mst1_axi_prot_inst(
                                                     // AXI I/F
                                                     //read addr chl
                                                     .axi_arvalid(npu_mst1_axi_arvalid),
                                                     .axi_arready(npu_mst1_axi_arready),
                                                     .axi_araddr({npu_mst1_axi_sb_raddr,npu_mst1_axi_arid,npu_mst1_axi_araddr}),
                                                     .axi_arcache(npu_mst1_axi_arcache),
                                                     .axi_arprot(npu_mst1_axi_arprot),
                                                     .axi_arlock({1'b0,npu_mst1_axi_arlock}),
                                                     .axi_arlen(npu_mst1_axi_arlen[3:0]),
                                                     .axi_arburst(npu_mst1_axi_arburst),
                                                     .axi_arsize(npu_mst1_axi_arsize),
                                                     .axi_arregion(1'd0),
                                                     .axi_arid(npu_mst1_axi_arid),
                                                     // read data chl
                                                     .axi_rvalid(npu_mst1_axi_rvalid),
                                                     .axi_rready(npu_mst1_axi_rready),
                                                     .axi_rdata(npu_mst1_axi_rdata),
                                                     .axi_rresp(npu_mst1_axi_rresp),
                                                     .axi_rlast(npu_mst1_axi_rlast),
                                                     .axi_rid(npu_mst1_axi_rid),
                                                     //write addr chl
                                                     .axi_awvalid(npu_mst1_axi_awvalid),
                                                     .axi_awready(npu_mst1_axi_awready),
                                                     .axi_awaddr({npu_mst1_axi_sb_waddr,npu_mst1_axi_awid,npu_mst1_axi_awaddr}),
                                                     .axi_awcache(npu_mst1_axi_awcache),
                                                     .axi_awprot(npu_mst1_axi_awprot),
                                                     .axi_awlock({1'b0,npu_mst1_axi_awlock}),
                                                     .axi_awlen(npu_mst1_axi_awlen[3:0]),
                                                     .axi_awburst(npu_mst1_axi_awburst),
                                                     .axi_awsize(npu_mst1_axi_awsize),
                                                     .axi_awregion(1'd0),
                                                     .axi_awid(npu_mst1_axi_awid),
                                                     // write data chl
                                                     .axi_wvalid(npu_mst1_axi_wvalid),
                                                     .axi_wready(npu_mst1_axi_wready),
                                                     .axi_wdata(npu_mst1_axi_wdata),
                                                     .axi_wstrb(npu_mst1_axi_wstrb),
                                                     .axi_wlast(npu_mst1_axi_wlast),
                                                     //write resp chl
                                                     .axi_bvalid(npu_mst1_axi_bvalid),
                                                     .axi_bready(npu_mst1_axi_bready),
                                                     .axi_bresp(npu_mst1_axi_bresp),
                                                     .axi_bid(npu_mst1_axi_bid),
                                                     //IBP I/F

  .ibp_cmd_valid             (mst_npu_mst1_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_npu_mst1_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_npu_mst1_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_npu_mst1_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_npu_mst1_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_npu_mst1_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_npu_mst1_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_npu_mst1_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_npu_mst1_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_npu_mst1_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_npu_mst1_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_npu_mst1_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_npu_mst1_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_npu_mst1_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_npu_mst1_axi_ibp_err_rd),
  .ibp_rd_data               (mst_npu_mst1_axi_ibp_rd_data),
  .ibp_rd_last               (mst_npu_mst1_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_npu_mst1_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_npu_mst1_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_npu_mst1_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_npu_mst1_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_npu_mst1_axi_ibp_wr_last),

  .ibp_wr_done               (mst_npu_mst1_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_npu_mst1_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_npu_mst1_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_npu_mst1_axi_ibp_wr_resp_accept),
                                                     .ibp_cmd_rgon(mst_npu_mst1_axi_ibp_cmd_rgon),
                                                     //clock and resets
                                                     .clk(clk),
                                                     .bus_clk_en(1'b1),
                                                     .sync_rst_r(~rst_b),
                                                     .rst_a(~rst_b)
                                                     );




    wire [3-1:0] npu_mst2_axi_port_id;        // master2 port ID
    wire [1-1:0] npu_mst2_axi_aruser_signal;  // master2 user signal, user_iw >= 1
    wire [1-1:0] npu_mst2_axi_awuser_signal;  // master2 user signal
    wire [4-1:0]   npu_mst2_axi_sb_raddr;       // master2 side-band address (exclude iw)
    wire [4-1:0]   npu_mst2_axi_sb_waddr;       // master2 side-band address (exclude iw)
    assign npu_mst2_axi_port_id = 2;
    assign npu_mst2_axi_aruser_signal = {
                                   npu_mst2_axi_arprot[1]
                                  };
    assign npu_mst2_axi_awuser_signal = {
                                   npu_mst2_axi_awprot[1]
                                  };
    assign npu_mst2_axi_sb_raddr = {npu_mst2_axi_aruser_signal
                             ,npu_mst2_axi_port_id
                             };
    assign npu_mst2_axi_sb_waddr = {npu_mst2_axi_awuser_signal
                             ,npu_mst2_axi_port_id
                             };
    alb_mss_fab_axi2ibp #(.FORCE_TO_SINGLE(0),
                          .X_W(512),
                          .Y_W(512),
                          .RGON_W(1),
                          .BYPBUF_DEPTH(16),
                          .BUS_ID_W(5),
                          .CHNL_FIFO_DEPTH(0),
                          .ADDR_W(49),
                          .DATA_W(512)) u_npu_mst2_axi_prot_inst(
                                                     // AXI I/F
                                                     //read addr chl
                                                     .axi_arvalid(npu_mst2_axi_arvalid),
                                                     .axi_arready(npu_mst2_axi_arready),
                                                     .axi_araddr({npu_mst2_axi_sb_raddr,npu_mst2_axi_arid,npu_mst2_axi_araddr}),
                                                     .axi_arcache(npu_mst2_axi_arcache),
                                                     .axi_arprot(npu_mst2_axi_arprot),
                                                     .axi_arlock({1'b0,npu_mst2_axi_arlock}),
                                                     .axi_arlen(npu_mst2_axi_arlen[3:0]),
                                                     .axi_arburst(npu_mst2_axi_arburst),
                                                     .axi_arsize(npu_mst2_axi_arsize),
                                                     .axi_arregion(1'd0),
                                                     .axi_arid(npu_mst2_axi_arid),
                                                     // read data chl
                                                     .axi_rvalid(npu_mst2_axi_rvalid),
                                                     .axi_rready(npu_mst2_axi_rready),
                                                     .axi_rdata(npu_mst2_axi_rdata),
                                                     .axi_rresp(npu_mst2_axi_rresp),
                                                     .axi_rlast(npu_mst2_axi_rlast),
                                                     .axi_rid(npu_mst2_axi_rid),
                                                     //write addr chl
                                                     .axi_awvalid(npu_mst2_axi_awvalid),
                                                     .axi_awready(npu_mst2_axi_awready),
                                                     .axi_awaddr({npu_mst2_axi_sb_waddr,npu_mst2_axi_awid,npu_mst2_axi_awaddr}),
                                                     .axi_awcache(npu_mst2_axi_awcache),
                                                     .axi_awprot(npu_mst2_axi_awprot),
                                                     .axi_awlock({1'b0,npu_mst2_axi_awlock}),
                                                     .axi_awlen(npu_mst2_axi_awlen[3:0]),
                                                     .axi_awburst(npu_mst2_axi_awburst),
                                                     .axi_awsize(npu_mst2_axi_awsize),
                                                     .axi_awregion(1'd0),
                                                     .axi_awid(npu_mst2_axi_awid),
                                                     // write data chl
                                                     .axi_wvalid(npu_mst2_axi_wvalid),
                                                     .axi_wready(npu_mst2_axi_wready),
                                                     .axi_wdata(npu_mst2_axi_wdata),
                                                     .axi_wstrb(npu_mst2_axi_wstrb),
                                                     .axi_wlast(npu_mst2_axi_wlast),
                                                     //write resp chl
                                                     .axi_bvalid(npu_mst2_axi_bvalid),
                                                     .axi_bready(npu_mst2_axi_bready),
                                                     .axi_bresp(npu_mst2_axi_bresp),
                                                     .axi_bid(npu_mst2_axi_bid),
                                                     //IBP I/F

  .ibp_cmd_valid             (mst_npu_mst2_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_npu_mst2_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_npu_mst2_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_npu_mst2_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_npu_mst2_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_npu_mst2_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_npu_mst2_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_npu_mst2_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_npu_mst2_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_npu_mst2_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_npu_mst2_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_npu_mst2_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_npu_mst2_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_npu_mst2_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_npu_mst2_axi_ibp_err_rd),
  .ibp_rd_data               (mst_npu_mst2_axi_ibp_rd_data),
  .ibp_rd_last               (mst_npu_mst2_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_npu_mst2_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_npu_mst2_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_npu_mst2_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_npu_mst2_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_npu_mst2_axi_ibp_wr_last),

  .ibp_wr_done               (mst_npu_mst2_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_npu_mst2_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_npu_mst2_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_npu_mst2_axi_ibp_wr_resp_accept),
                                                     .ibp_cmd_rgon(mst_npu_mst2_axi_ibp_cmd_rgon),
                                                     //clock and resets
                                                     .clk(clk),
                                                     .bus_clk_en(1'b1),
                                                     .sync_rst_r(~rst_b),
                                                     .rst_a(~rst_b)
                                                     );




    wire [3-1:0] npu_mst3_axi_port_id;        // master3 port ID
    wire [1-1:0] npu_mst3_axi_aruser_signal;  // master3 user signal, user_iw >= 1
    wire [1-1:0] npu_mst3_axi_awuser_signal;  // master3 user signal
    wire [4-1:0]   npu_mst3_axi_sb_raddr;       // master3 side-band address (exclude iw)
    wire [4-1:0]   npu_mst3_axi_sb_waddr;       // master3 side-band address (exclude iw)
    assign npu_mst3_axi_port_id = 3;
    assign npu_mst3_axi_aruser_signal = {
                                   npu_mst3_axi_arprot[1]
                                  };
    assign npu_mst3_axi_awuser_signal = {
                                   npu_mst3_axi_awprot[1]
                                  };
    assign npu_mst3_axi_sb_raddr = {npu_mst3_axi_aruser_signal
                             ,npu_mst3_axi_port_id
                             };
    assign npu_mst3_axi_sb_waddr = {npu_mst3_axi_awuser_signal
                             ,npu_mst3_axi_port_id
                             };
    alb_mss_fab_axi2ibp #(.FORCE_TO_SINGLE(0),
                          .X_W(512),
                          .Y_W(512),
                          .RGON_W(1),
                          .BYPBUF_DEPTH(16),
                          .BUS_ID_W(5),
                          .CHNL_FIFO_DEPTH(0),
                          .ADDR_W(49),
                          .DATA_W(512)) u_npu_mst3_axi_prot_inst(
                                                     // AXI I/F
                                                     //read addr chl
                                                     .axi_arvalid(npu_mst3_axi_arvalid),
                                                     .axi_arready(npu_mst3_axi_arready),
                                                     .axi_araddr({npu_mst3_axi_sb_raddr,npu_mst3_axi_arid,npu_mst3_axi_araddr}),
                                                     .axi_arcache(npu_mst3_axi_arcache),
                                                     .axi_arprot(npu_mst3_axi_arprot),
                                                     .axi_arlock({1'b0,npu_mst3_axi_arlock}),
                                                     .axi_arlen(npu_mst3_axi_arlen[3:0]),
                                                     .axi_arburst(npu_mst3_axi_arburst),
                                                     .axi_arsize(npu_mst3_axi_arsize),
                                                     .axi_arregion(1'd0),
                                                     .axi_arid(npu_mst3_axi_arid),
                                                     // read data chl
                                                     .axi_rvalid(npu_mst3_axi_rvalid),
                                                     .axi_rready(npu_mst3_axi_rready),
                                                     .axi_rdata(npu_mst3_axi_rdata),
                                                     .axi_rresp(npu_mst3_axi_rresp),
                                                     .axi_rlast(npu_mst3_axi_rlast),
                                                     .axi_rid(npu_mst3_axi_rid),
                                                     //write addr chl
                                                     .axi_awvalid(npu_mst3_axi_awvalid),
                                                     .axi_awready(npu_mst3_axi_awready),
                                                     .axi_awaddr({npu_mst3_axi_sb_waddr,npu_mst3_axi_awid,npu_mst3_axi_awaddr}),
                                                     .axi_awcache(npu_mst3_axi_awcache),
                                                     .axi_awprot(npu_mst3_axi_awprot),
                                                     .axi_awlock({1'b0,npu_mst3_axi_awlock}),
                                                     .axi_awlen(npu_mst3_axi_awlen[3:0]),
                                                     .axi_awburst(npu_mst3_axi_awburst),
                                                     .axi_awsize(npu_mst3_axi_awsize),
                                                     .axi_awregion(1'd0),
                                                     .axi_awid(npu_mst3_axi_awid),
                                                     // write data chl
                                                     .axi_wvalid(npu_mst3_axi_wvalid),
                                                     .axi_wready(npu_mst3_axi_wready),
                                                     .axi_wdata(npu_mst3_axi_wdata),
                                                     .axi_wstrb(npu_mst3_axi_wstrb),
                                                     .axi_wlast(npu_mst3_axi_wlast),
                                                     //write resp chl
                                                     .axi_bvalid(npu_mst3_axi_bvalid),
                                                     .axi_bready(npu_mst3_axi_bready),
                                                     .axi_bresp(npu_mst3_axi_bresp),
                                                     .axi_bid(npu_mst3_axi_bid),
                                                     //IBP I/F

  .ibp_cmd_valid             (mst_npu_mst3_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_npu_mst3_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_npu_mst3_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_npu_mst3_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_npu_mst3_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_npu_mst3_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_npu_mst3_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_npu_mst3_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_npu_mst3_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_npu_mst3_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_npu_mst3_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_npu_mst3_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_npu_mst3_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_npu_mst3_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_npu_mst3_axi_ibp_err_rd),
  .ibp_rd_data               (mst_npu_mst3_axi_ibp_rd_data),
  .ibp_rd_last               (mst_npu_mst3_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_npu_mst3_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_npu_mst3_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_npu_mst3_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_npu_mst3_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_npu_mst3_axi_ibp_wr_last),

  .ibp_wr_done               (mst_npu_mst3_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_npu_mst3_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_npu_mst3_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_npu_mst3_axi_ibp_wr_resp_accept),
                                                     .ibp_cmd_rgon(mst_npu_mst3_axi_ibp_cmd_rgon),
                                                     //clock and resets
                                                     .clk(clk),
                                                     .bus_clk_en(1'b1),
                                                     .sync_rst_r(~rst_b),
                                                     .rst_a(~rst_b)
                                                     );




    wire [3-1:0] npu_mst4_axi_port_id;        // master4 port ID
    wire [1-1:0] npu_mst4_axi_aruser_signal;  // master4 user signal, user_iw >= 1
    wire [1-1:0] npu_mst4_axi_awuser_signal;  // master4 user signal
    wire [4-1:0]   npu_mst4_axi_sb_raddr;       // master4 side-band address (exclude iw)
    wire [4-1:0]   npu_mst4_axi_sb_waddr;       // master4 side-band address (exclude iw)
    assign npu_mst4_axi_port_id = 4;
    assign npu_mst4_axi_aruser_signal = {
                                   npu_mst4_axi_arprot[1]
                                  };
    assign npu_mst4_axi_awuser_signal = {
                                   npu_mst4_axi_awprot[1]
                                  };
    assign npu_mst4_axi_sb_raddr = {npu_mst4_axi_aruser_signal
                             ,npu_mst4_axi_port_id
                             };
    assign npu_mst4_axi_sb_waddr = {npu_mst4_axi_awuser_signal
                             ,npu_mst4_axi_port_id
                             };
    alb_mss_fab_axi2ibp #(.FORCE_TO_SINGLE(0),
                          .X_W(512),
                          .Y_W(512),
                          .RGON_W(1),
                          .BYPBUF_DEPTH(16),
                          .BUS_ID_W(5),
                          .CHNL_FIFO_DEPTH(0),
                          .ADDR_W(49),
                          .DATA_W(512)) u_npu_mst4_axi_prot_inst(
                                                     // AXI I/F
                                                     //read addr chl
                                                     .axi_arvalid(npu_mst4_axi_arvalid),
                                                     .axi_arready(npu_mst4_axi_arready),
                                                     .axi_araddr({npu_mst4_axi_sb_raddr,npu_mst4_axi_arid,npu_mst4_axi_araddr}),
                                                     .axi_arcache(npu_mst4_axi_arcache),
                                                     .axi_arprot(npu_mst4_axi_arprot),
                                                     .axi_arlock({1'b0,npu_mst4_axi_arlock}),
                                                     .axi_arlen(npu_mst4_axi_arlen[3:0]),
                                                     .axi_arburst(npu_mst4_axi_arburst),
                                                     .axi_arsize(npu_mst4_axi_arsize),
                                                     .axi_arregion(1'd0),
                                                     .axi_arid(npu_mst4_axi_arid),
                                                     // read data chl
                                                     .axi_rvalid(npu_mst4_axi_rvalid),
                                                     .axi_rready(npu_mst4_axi_rready),
                                                     .axi_rdata(npu_mst4_axi_rdata),
                                                     .axi_rresp(npu_mst4_axi_rresp),
                                                     .axi_rlast(npu_mst4_axi_rlast),
                                                     .axi_rid(npu_mst4_axi_rid),
                                                     //write addr chl
                                                     .axi_awvalid(npu_mst4_axi_awvalid),
                                                     .axi_awready(npu_mst4_axi_awready),
                                                     .axi_awaddr({npu_mst4_axi_sb_waddr,npu_mst4_axi_awid,npu_mst4_axi_awaddr}),
                                                     .axi_awcache(npu_mst4_axi_awcache),
                                                     .axi_awprot(npu_mst4_axi_awprot),
                                                     .axi_awlock({1'b0,npu_mst4_axi_awlock}),
                                                     .axi_awlen(npu_mst4_axi_awlen[3:0]),
                                                     .axi_awburst(npu_mst4_axi_awburst),
                                                     .axi_awsize(npu_mst4_axi_awsize),
                                                     .axi_awregion(1'd0),
                                                     .axi_awid(npu_mst4_axi_awid),
                                                     // write data chl
                                                     .axi_wvalid(npu_mst4_axi_wvalid),
                                                     .axi_wready(npu_mst4_axi_wready),
                                                     .axi_wdata(npu_mst4_axi_wdata),
                                                     .axi_wstrb(npu_mst4_axi_wstrb),
                                                     .axi_wlast(npu_mst4_axi_wlast),
                                                     //write resp chl
                                                     .axi_bvalid(npu_mst4_axi_bvalid),
                                                     .axi_bready(npu_mst4_axi_bready),
                                                     .axi_bresp(npu_mst4_axi_bresp),
                                                     .axi_bid(npu_mst4_axi_bid),
                                                     //IBP I/F

  .ibp_cmd_valid             (mst_npu_mst4_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_npu_mst4_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_npu_mst4_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_npu_mst4_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_npu_mst4_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_npu_mst4_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_npu_mst4_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_npu_mst4_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_npu_mst4_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_npu_mst4_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_npu_mst4_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_npu_mst4_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_npu_mst4_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_npu_mst4_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_npu_mst4_axi_ibp_err_rd),
  .ibp_rd_data               (mst_npu_mst4_axi_ibp_rd_data),
  .ibp_rd_last               (mst_npu_mst4_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_npu_mst4_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_npu_mst4_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_npu_mst4_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_npu_mst4_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_npu_mst4_axi_ibp_wr_last),

  .ibp_wr_done               (mst_npu_mst4_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_npu_mst4_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_npu_mst4_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_npu_mst4_axi_ibp_wr_resp_accept),
                                                     .ibp_cmd_rgon(mst_npu_mst4_axi_ibp_cmd_rgon),
                                                     //clock and resets
                                                     .clk(clk),
                                                     .bus_clk_en(1'b1),
                                                     .sync_rst_r(~rst_b),
                                                     .rst_a(~rst_b)
                                                     );




    wire [3-1:0] host_axi_port_id;        // master5 port ID
    wire [1-1:0] host_axi_aruser_signal;  // master5 user signal, user_iw >= 1
    wire [1-1:0] host_axi_awuser_signal;  // master5 user signal
    wire [8-1:0]   host_axi_sb_raddr;       // master5 side-band address (exclude iw)
    wire [8-1:0]   host_axi_sb_waddr;       // master5 side-band address (exclude iw)
    assign host_axi_port_id = 5;
    assign host_axi_aruser_signal = {
                                   host_axi_arprot[1]
                                  };
    assign host_axi_awuser_signal = {
                                   host_axi_awprot[1]
                                  };
    assign host_axi_sb_raddr = {host_axi_aruser_signal
                             ,host_axi_port_id
                             ,{4{1'b0}}
                             };
    assign host_axi_sb_waddr = {host_axi_awuser_signal
                             ,host_axi_port_id
                             ,{4{1'b0}}
                             };
    alb_mss_fab_axi2ibp #(.FORCE_TO_SINGLE(0),
                          .X_W(64),
                          .Y_W(64),
                          .RGON_W(1),
                          .BYPBUF_DEPTH(16),
                          .BUS_ID_W(1),
                          .CHNL_FIFO_DEPTH(0),
                          .ADDR_W(49),
                          .DATA_W(64)) u_host_axi_prot_inst(
                                                     // AXI I/F
                                                     //read addr chl
                                                     .axi_arvalid(host_axi_arvalid),
                                                     .axi_arready(host_axi_arready),
                                                     .axi_araddr({host_axi_sb_raddr,host_axi_arid,host_axi_araddr}),
                                                     .axi_arcache(host_axi_arcache),
                                                     .axi_arprot(host_axi_arprot),
                                                     .axi_arlock({1'b0,host_axi_arlock}),
                                                     .axi_arlen(host_axi_arlen[3:0]),
                                                     .axi_arburst(host_axi_arburst),
                                                     .axi_arsize(host_axi_arsize),
                                                     .axi_arregion(1'd0),
                                                     .axi_arid(host_axi_arid),
                                                     // read data chl
                                                     .axi_rvalid(host_axi_rvalid),
                                                     .axi_rready(host_axi_rready),
                                                     .axi_rdata(host_axi_rdata),
                                                     .axi_rresp(host_axi_rresp),
                                                     .axi_rlast(host_axi_rlast),
                                                     .axi_rid(host_axi_rid),
                                                     //write addr chl
                                                     .axi_awvalid(host_axi_awvalid),
                                                     .axi_awready(host_axi_awready),
                                                     .axi_awaddr({host_axi_sb_waddr,host_axi_awid,host_axi_awaddr}),
                                                     .axi_awcache(host_axi_awcache),
                                                     .axi_awprot(host_axi_awprot),
                                                     .axi_awlock({1'b0,host_axi_awlock}),
                                                     .axi_awlen(host_axi_awlen[3:0]),
                                                     .axi_awburst(host_axi_awburst),
                                                     .axi_awsize(host_axi_awsize),
                                                     .axi_awregion(1'd0),
                                                     .axi_awid(host_axi_awid),
                                                     // write data chl
                                                     .axi_wvalid(host_axi_wvalid),
                                                     .axi_wready(host_axi_wready),
                                                     .axi_wdata(host_axi_wdata),
                                                     .axi_wstrb(host_axi_wstrb),
                                                     .axi_wlast(host_axi_wlast),
                                                     //write resp chl
                                                     .axi_bvalid(host_axi_bvalid),
                                                     .axi_bready(host_axi_bready),
                                                     .axi_bresp(host_axi_bresp),
                                                     .axi_bid(host_axi_bid),
                                                     //IBP I/F

  .ibp_cmd_valid             (mst_host_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_host_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_host_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_host_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_host_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_host_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_host_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_host_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_host_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_host_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_host_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_host_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_host_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_host_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_host_axi_ibp_err_rd),
  .ibp_rd_data               (mst_host_axi_ibp_rd_data),
  .ibp_rd_last               (mst_host_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_host_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_host_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_host_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_host_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_host_axi_ibp_wr_last),

  .ibp_wr_done               (mst_host_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_host_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_host_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_host_axi_ibp_wr_resp_accept),
                                                     .ibp_cmd_rgon(mst_host_axi_ibp_cmd_rgon),
                                                     //clock and resets
                                                     .clk(mss_clk),
                                                     .bus_clk_en(mss_fab_mst5_clk_en),
                                                     .sync_rst_r(~rst_b),
                                                     .rst_a(~rst_b)
                                                     );




    wire [3-1:0] bri4tb_port_id;        // master6 port ID
    wire [1-1:0] bri4tb_aruser_signal;  // master6 user signal, user_iw >= 1
    wire [1-1:0] bri4tb_awuser_signal;  // master6 user signal
    wire [5-1:0]   bri4tb_sb_raddr;       // master6 side-band address (exclude iw)
    wire [5-1:0]   bri4tb_sb_waddr;       // master6 side-band address (exclude iw)
    assign bri4tb_port_id = 6;
    assign bri4tb_aruser_signal = {
                                   bri4tb_arprot[1]
                                  };
    assign bri4tb_awuser_signal = {
                                   bri4tb_awprot[1]
                                  };
    assign bri4tb_sb_raddr = {bri4tb_aruser_signal
                             ,bri4tb_port_id
                             ,{1{1'b0}}
                             };
    assign bri4tb_sb_waddr = {bri4tb_awuser_signal
                             ,bri4tb_port_id
                             ,{1{1'b0}}
                             };
    alb_mss_fab_axi2ibp #(.FORCE_TO_SINGLE(0),
                          .X_W(32),
                          .Y_W(32),
                          .RGON_W(1),
                          .BYPBUF_DEPTH(16),
                          .BUS_ID_W(4),
                          .CHNL_FIFO_DEPTH(0),
                          .ADDR_W(49),
                          .DATA_W(32)) u_bri4tb_prot_inst(
                                                     // AXI I/F
                                                     //read addr chl
                                                     .axi_arvalid(bri4tb_arvalid),
                                                     .axi_arready(bri4tb_arready),
                                                     .axi_araddr({bri4tb_sb_raddr,bri4tb_arid,bri4tb_araddr}),
                                                     .axi_arcache(bri4tb_arcache),
                                                     .axi_arprot(bri4tb_arprot),
                                                     .axi_arlock(2'd0),
                                                     .axi_arlen(bri4tb_arlen),
                                                     .axi_arburst(bri4tb_arburst),
                                                     .axi_arsize(bri4tb_arsize),
                                                     .axi_arregion(1'd0),
                                                     .axi_arid(bri4tb_arid),
                                                     // read data chl
                                                     .axi_rvalid(bri4tb_rvalid),
                                                     .axi_rready(bri4tb_rready),
                                                     .axi_rdata(bri4tb_rdata),
                                                     .axi_rresp(bri4tb_rresp),
                                                     .axi_rlast(bri4tb_rlast),
                                                     .axi_rid(bri4tb_rid),
                                                     //write addr chl
                                                     .axi_awvalid(bri4tb_awvalid),
                                                     .axi_awready(bri4tb_awready),
                                                     .axi_awaddr({bri4tb_sb_waddr,bri4tb_awid,bri4tb_awaddr}),
                                                     .axi_awcache(bri4tb_awcache),
                                                     .axi_awprot(bri4tb_awprot),
                                                     .axi_awlock(2'd0),
                                                     .axi_awlen(bri4tb_awlen),
                                                     .axi_awburst(bri4tb_awburst),
                                                     .axi_awsize(bri4tb_awsize),
                                                     .axi_awregion(1'd0),
                                                     .axi_awid(bri4tb_awid),
                                                     // write data chl
                                                     .axi_wvalid(bri4tb_wvalid),
                                                     .axi_wready(bri4tb_wready),
                                                     .axi_wdata(bri4tb_wdata),
                                                     .axi_wstrb(bri4tb_wstrb),
                                                     .axi_wlast(bri4tb_wlast),
                                                     //write resp chl
                                                     .axi_bvalid(bri4tb_bvalid),
                                                     .axi_bready(bri4tb_bready),
                                                     .axi_bresp(bri4tb_bresp),
                                                     .axi_bid(bri4tb_bid),
                                                     //IBP I/F

  .ibp_cmd_valid             (mst_bri4tb_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_bri4tb_ibp_cmd_accept),
  .ibp_cmd_read              (mst_bri4tb_ibp_cmd_read),
  .ibp_cmd_addr              (mst_bri4tb_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_bri4tb_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_bri4tb_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_bri4tb_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_bri4tb_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_bri4tb_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_bri4tb_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_bri4tb_ibp_cmd_excl),

  .ibp_rd_valid              (mst_bri4tb_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_bri4tb_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_bri4tb_ibp_rd_accept),
  .ibp_err_rd                (mst_bri4tb_ibp_err_rd),
  .ibp_rd_data               (mst_bri4tb_ibp_rd_data),
  .ibp_rd_last               (mst_bri4tb_ibp_rd_last),

  .ibp_wr_valid              (mst_bri4tb_ibp_wr_valid),
  .ibp_wr_accept             (mst_bri4tb_ibp_wr_accept),
  .ibp_wr_data               (mst_bri4tb_ibp_wr_data),
  .ibp_wr_mask               (mst_bri4tb_ibp_wr_mask),
  .ibp_wr_last               (mst_bri4tb_ibp_wr_last),

  .ibp_wr_done               (mst_bri4tb_ibp_wr_done),
  .ibp_wr_excl_done          (mst_bri4tb_ibp_wr_excl_done),
  .ibp_err_wr                (mst_bri4tb_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_bri4tb_ibp_wr_resp_accept),
                                                     .ibp_cmd_rgon(mst_bri4tb_ibp_cmd_rgon),
                                                     //clock and resets
                                                     .clk(mss_clk),
                                                     .bus_clk_en(mss_fab_mst6_clk_en),
                                                     .sync_rst_r(~rst_b),
                                                     .rst_a(~rst_b)
                                                     );






    // To support flexible clock ratio configuration, there is a clk_domain converting logic here
    // handles from master clock domain to ARCv2MSS fabric clock domain
    // If master port already support clock ratio, the signals are just bypassed to fabric
    // If master port doesn't support clock ratio, invloves two ibp_buffer to do domain conversion


    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(49),
                           .DATA_W(64),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_npu_mst0_axi__ibp2pack_inst(
                           .ibp_cmd_rgon(mst_npu_mst0_axi_ibp_cmd_rgon),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (mst_npu_mst0_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_npu_mst0_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_npu_mst0_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_npu_mst0_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_npu_mst0_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_npu_mst0_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_npu_mst0_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_npu_mst0_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_npu_mst0_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_npu_mst0_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_npu_mst0_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_npu_mst0_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_npu_mst0_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_npu_mst0_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_npu_mst0_axi_ibp_err_rd),
  .ibp_rd_data               (mst_npu_mst0_axi_ibp_rd_data),
  .ibp_rd_last               (mst_npu_mst0_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_npu_mst0_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_npu_mst0_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_npu_mst0_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_npu_mst0_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_npu_mst0_axi_ibp_wr_last),

  .ibp_wr_done               (mst_npu_mst0_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_npu_mst0_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_npu_mst0_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_npu_mst0_axi_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (mst_npu_mst0_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (mst_npu_mst0_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (mst_npu_mst0_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (mst_npu_mst0_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (mst_npu_mst0_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (mst_npu_mst0_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (mst_npu_mst0_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (mst_npu_mst0_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (mst_npu_mst0_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (mst_npu_mst0_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(mst_npu_mst0_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (mst_npu_mst0_axi_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(mst_npu_mst0_axi_ibp_cmd_chnl_rgon),
                           .ibp_cmd_chnl_user(),
                           .clk(clk),
                           .rst_a(~rst_b)
                           );
    // use master's (with prefix npu_mst0_axi_) clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(1),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_mst0_axi__ibp_buffer_0_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(mst_npu_mst0_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_npu_mst0_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_npu_mst0_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_npu_mst0_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_npu_mst0_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_npu_mst0_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_npu_mst0_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_npu_mst0_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_npu_mst0_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_npu_mst0_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_npu_mst0_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_npu_mst0_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_npu_mst0_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(mst_o_npu_mst0_axi_ibp_cmd_chnl_rgon),



    .o_ibp_cmd_chnl_valid  (mst_o_npu_mst0_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (mst_o_npu_mst0_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (mst_o_npu_mst0_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (mst_o_npu_mst0_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (mst_o_npu_mst0_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (mst_o_npu_mst0_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (mst_o_npu_mst0_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (mst_o_npu_mst0_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (mst_o_npu_mst0_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (mst_o_npu_mst0_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(mst_o_npu_mst0_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (mst_o_npu_mst0_axi_ibp_wrsp_chnl),

                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),
                             .ibp_buffer_idle(),
                             .clk(clk),
                             .rst_a(~rst_b)
                             );

    // use fabric's clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(1),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_mst0_axi__ibp_buffer_1_inst (
                             .i_ibp_clk_en(mss_fab_mst0_clk_en),
                             .i_ibp_cmd_chnl_rgon(mst_o_npu_mst0_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_o_npu_mst0_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_o_npu_mst0_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_o_npu_mst0_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_o_npu_mst0_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_o_npu_mst0_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_o_npu_mst0_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_o_npu_mst0_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_o_npu_mst0_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_o_npu_mst0_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_o_npu_mst0_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_o_npu_mst0_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_o_npu_mst0_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(lat_i_npu_mst0_axi_ibp_cmd_chnl_rgon),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (lat_i_npu_mst0_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (lat_i_npu_mst0_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (lat_i_npu_mst0_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (lat_i_npu_mst0_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (lat_i_npu_mst0_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (lat_i_npu_mst0_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (lat_i_npu_mst0_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (lat_i_npu_mst0_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (lat_i_npu_mst0_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (lat_i_npu_mst0_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(lat_i_npu_mst0_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (lat_i_npu_mst0_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );
    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(49),
                           .DATA_W(64),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_npu_mst0_axi__pack2ibp_inst(
                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(lat_i_npu_mst0_axi_ibp_cmd_chnl_rgon),



    .ibp_cmd_chnl_valid  (lat_i_npu_mst0_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (lat_i_npu_mst0_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (lat_i_npu_mst0_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (lat_i_npu_mst0_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (lat_i_npu_mst0_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (lat_i_npu_mst0_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (lat_i_npu_mst0_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (lat_i_npu_mst0_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (lat_i_npu_mst0_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (lat_i_npu_mst0_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(lat_i_npu_mst0_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (lat_i_npu_mst0_axi_ibp_wrsp_chnl),


  .ibp_cmd_valid             (lat_i_npu_mst0_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (lat_i_npu_mst0_axi_ibp_cmd_accept),
  .ibp_cmd_read              (lat_i_npu_mst0_axi_ibp_cmd_read),
  .ibp_cmd_addr              (lat_i_npu_mst0_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (lat_i_npu_mst0_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (lat_i_npu_mst0_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (lat_i_npu_mst0_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (lat_i_npu_mst0_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (lat_i_npu_mst0_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (lat_i_npu_mst0_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (lat_i_npu_mst0_axi_ibp_cmd_excl),

  .ibp_rd_valid              (lat_i_npu_mst0_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (lat_i_npu_mst0_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (lat_i_npu_mst0_axi_ibp_rd_accept),
  .ibp_err_rd                (lat_i_npu_mst0_axi_ibp_err_rd),
  .ibp_rd_data               (lat_i_npu_mst0_axi_ibp_rd_data),
  .ibp_rd_last               (lat_i_npu_mst0_axi_ibp_rd_last),

  .ibp_wr_valid              (lat_i_npu_mst0_axi_ibp_wr_valid),
  .ibp_wr_accept             (lat_i_npu_mst0_axi_ibp_wr_accept),
  .ibp_wr_data               (lat_i_npu_mst0_axi_ibp_wr_data),
  .ibp_wr_mask               (lat_i_npu_mst0_axi_ibp_wr_mask),
  .ibp_wr_last               (lat_i_npu_mst0_axi_ibp_wr_last),

  .ibp_wr_done               (lat_i_npu_mst0_axi_ibp_wr_done),
  .ibp_wr_excl_done          (lat_i_npu_mst0_axi_ibp_wr_excl_done),
  .ibp_err_wr                (lat_i_npu_mst0_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (lat_i_npu_mst0_axi_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon()
                           );

    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(49),
                           .DATA_W(512),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_npu_mst1_axi__ibp2pack_inst(
                           .ibp_cmd_rgon(mst_npu_mst1_axi_ibp_cmd_rgon),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (mst_npu_mst1_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_npu_mst1_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_npu_mst1_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_npu_mst1_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_npu_mst1_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_npu_mst1_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_npu_mst1_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_npu_mst1_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_npu_mst1_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_npu_mst1_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_npu_mst1_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_npu_mst1_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_npu_mst1_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_npu_mst1_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_npu_mst1_axi_ibp_err_rd),
  .ibp_rd_data               (mst_npu_mst1_axi_ibp_rd_data),
  .ibp_rd_last               (mst_npu_mst1_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_npu_mst1_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_npu_mst1_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_npu_mst1_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_npu_mst1_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_npu_mst1_axi_ibp_wr_last),

  .ibp_wr_done               (mst_npu_mst1_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_npu_mst1_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_npu_mst1_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_npu_mst1_axi_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (mst_npu_mst1_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (mst_npu_mst1_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (mst_npu_mst1_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (mst_npu_mst1_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (mst_npu_mst1_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (mst_npu_mst1_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (mst_npu_mst1_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (mst_npu_mst1_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (mst_npu_mst1_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (mst_npu_mst1_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(mst_npu_mst1_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (mst_npu_mst1_axi_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(mst_npu_mst1_axi_ibp_cmd_chnl_rgon),
                           .ibp_cmd_chnl_user(),
                           .clk(clk),
                           .rst_a(~rst_b)
                           );
    // use master's (with prefix npu_mst1_axi_) clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(1),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_mst1_axi__ibp_buffer_0_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(mst_npu_mst1_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_npu_mst1_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_npu_mst1_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_npu_mst1_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_npu_mst1_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_npu_mst1_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_npu_mst1_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_npu_mst1_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_npu_mst1_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_npu_mst1_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_npu_mst1_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_npu_mst1_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_npu_mst1_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(mst_o_npu_mst1_axi_ibp_cmd_chnl_rgon),



    .o_ibp_cmd_chnl_valid  (mst_o_npu_mst1_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (mst_o_npu_mst1_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (mst_o_npu_mst1_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (mst_o_npu_mst1_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (mst_o_npu_mst1_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (mst_o_npu_mst1_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (mst_o_npu_mst1_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (mst_o_npu_mst1_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (mst_o_npu_mst1_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (mst_o_npu_mst1_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(mst_o_npu_mst1_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (mst_o_npu_mst1_axi_ibp_wrsp_chnl),

                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),
                             .ibp_buffer_idle(),
                             .clk(clk),
                             .rst_a(~rst_b)
                             );

    // use fabric's clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(1),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_mst1_axi__ibp_buffer_1_inst (
                             .i_ibp_clk_en(mss_fab_mst1_clk_en),
                             .i_ibp_cmd_chnl_rgon(mst_o_npu_mst1_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_o_npu_mst1_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_o_npu_mst1_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_o_npu_mst1_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_o_npu_mst1_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_o_npu_mst1_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_o_npu_mst1_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_o_npu_mst1_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_o_npu_mst1_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_o_npu_mst1_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_o_npu_mst1_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_o_npu_mst1_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_o_npu_mst1_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(lat_i_npu_mst1_axi_ibp_cmd_chnl_rgon),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (lat_i_npu_mst1_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (lat_i_npu_mst1_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (lat_i_npu_mst1_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (lat_i_npu_mst1_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (lat_i_npu_mst1_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (lat_i_npu_mst1_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (lat_i_npu_mst1_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (lat_i_npu_mst1_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (lat_i_npu_mst1_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (lat_i_npu_mst1_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(lat_i_npu_mst1_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (lat_i_npu_mst1_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );
    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(49),
                           .DATA_W(512),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_npu_mst1_axi__pack2ibp_inst(
                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(lat_i_npu_mst1_axi_ibp_cmd_chnl_rgon),



    .ibp_cmd_chnl_valid  (lat_i_npu_mst1_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (lat_i_npu_mst1_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (lat_i_npu_mst1_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (lat_i_npu_mst1_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (lat_i_npu_mst1_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (lat_i_npu_mst1_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (lat_i_npu_mst1_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (lat_i_npu_mst1_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (lat_i_npu_mst1_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (lat_i_npu_mst1_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(lat_i_npu_mst1_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (lat_i_npu_mst1_axi_ibp_wrsp_chnl),


  .ibp_cmd_valid             (lat_i_npu_mst1_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (lat_i_npu_mst1_axi_ibp_cmd_accept),
  .ibp_cmd_read              (lat_i_npu_mst1_axi_ibp_cmd_read),
  .ibp_cmd_addr              (lat_i_npu_mst1_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (lat_i_npu_mst1_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (lat_i_npu_mst1_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (lat_i_npu_mst1_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (lat_i_npu_mst1_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (lat_i_npu_mst1_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (lat_i_npu_mst1_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (lat_i_npu_mst1_axi_ibp_cmd_excl),

  .ibp_rd_valid              (lat_i_npu_mst1_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (lat_i_npu_mst1_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (lat_i_npu_mst1_axi_ibp_rd_accept),
  .ibp_err_rd                (lat_i_npu_mst1_axi_ibp_err_rd),
  .ibp_rd_data               (lat_i_npu_mst1_axi_ibp_rd_data),
  .ibp_rd_last               (lat_i_npu_mst1_axi_ibp_rd_last),

  .ibp_wr_valid              (lat_i_npu_mst1_axi_ibp_wr_valid),
  .ibp_wr_accept             (lat_i_npu_mst1_axi_ibp_wr_accept),
  .ibp_wr_data               (lat_i_npu_mst1_axi_ibp_wr_data),
  .ibp_wr_mask               (lat_i_npu_mst1_axi_ibp_wr_mask),
  .ibp_wr_last               (lat_i_npu_mst1_axi_ibp_wr_last),

  .ibp_wr_done               (lat_i_npu_mst1_axi_ibp_wr_done),
  .ibp_wr_excl_done          (lat_i_npu_mst1_axi_ibp_wr_excl_done),
  .ibp_err_wr                (lat_i_npu_mst1_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (lat_i_npu_mst1_axi_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon()
                           );

    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(49),
                           .DATA_W(512),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_npu_mst2_axi__ibp2pack_inst(
                           .ibp_cmd_rgon(mst_npu_mst2_axi_ibp_cmd_rgon),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (mst_npu_mst2_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_npu_mst2_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_npu_mst2_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_npu_mst2_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_npu_mst2_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_npu_mst2_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_npu_mst2_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_npu_mst2_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_npu_mst2_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_npu_mst2_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_npu_mst2_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_npu_mst2_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_npu_mst2_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_npu_mst2_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_npu_mst2_axi_ibp_err_rd),
  .ibp_rd_data               (mst_npu_mst2_axi_ibp_rd_data),
  .ibp_rd_last               (mst_npu_mst2_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_npu_mst2_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_npu_mst2_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_npu_mst2_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_npu_mst2_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_npu_mst2_axi_ibp_wr_last),

  .ibp_wr_done               (mst_npu_mst2_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_npu_mst2_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_npu_mst2_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_npu_mst2_axi_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (mst_npu_mst2_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (mst_npu_mst2_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (mst_npu_mst2_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (mst_npu_mst2_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (mst_npu_mst2_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (mst_npu_mst2_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (mst_npu_mst2_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (mst_npu_mst2_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (mst_npu_mst2_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (mst_npu_mst2_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(mst_npu_mst2_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (mst_npu_mst2_axi_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(mst_npu_mst2_axi_ibp_cmd_chnl_rgon),
                           .ibp_cmd_chnl_user(),
                           .clk(clk),
                           .rst_a(~rst_b)
                           );
    // use master's (with prefix npu_mst2_axi_) clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(1),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_mst2_axi__ibp_buffer_0_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(mst_npu_mst2_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_npu_mst2_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_npu_mst2_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_npu_mst2_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_npu_mst2_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_npu_mst2_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_npu_mst2_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_npu_mst2_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_npu_mst2_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_npu_mst2_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_npu_mst2_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_npu_mst2_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_npu_mst2_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(mst_o_npu_mst2_axi_ibp_cmd_chnl_rgon),



    .o_ibp_cmd_chnl_valid  (mst_o_npu_mst2_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (mst_o_npu_mst2_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (mst_o_npu_mst2_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (mst_o_npu_mst2_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (mst_o_npu_mst2_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (mst_o_npu_mst2_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (mst_o_npu_mst2_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (mst_o_npu_mst2_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (mst_o_npu_mst2_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (mst_o_npu_mst2_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(mst_o_npu_mst2_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (mst_o_npu_mst2_axi_ibp_wrsp_chnl),

                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),
                             .ibp_buffer_idle(),
                             .clk(clk),
                             .rst_a(~rst_b)
                             );

    // use fabric's clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(1),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_mst2_axi__ibp_buffer_1_inst (
                             .i_ibp_clk_en(mss_fab_mst2_clk_en),
                             .i_ibp_cmd_chnl_rgon(mst_o_npu_mst2_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_o_npu_mst2_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_o_npu_mst2_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_o_npu_mst2_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_o_npu_mst2_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_o_npu_mst2_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_o_npu_mst2_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_o_npu_mst2_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_o_npu_mst2_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_o_npu_mst2_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_o_npu_mst2_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_o_npu_mst2_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_o_npu_mst2_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(lat_i_npu_mst2_axi_ibp_cmd_chnl_rgon),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (lat_i_npu_mst2_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (lat_i_npu_mst2_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (lat_i_npu_mst2_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (lat_i_npu_mst2_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (lat_i_npu_mst2_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (lat_i_npu_mst2_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (lat_i_npu_mst2_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (lat_i_npu_mst2_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (lat_i_npu_mst2_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (lat_i_npu_mst2_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(lat_i_npu_mst2_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (lat_i_npu_mst2_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );
    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(49),
                           .DATA_W(512),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_npu_mst2_axi__pack2ibp_inst(
                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(lat_i_npu_mst2_axi_ibp_cmd_chnl_rgon),



    .ibp_cmd_chnl_valid  (lat_i_npu_mst2_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (lat_i_npu_mst2_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (lat_i_npu_mst2_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (lat_i_npu_mst2_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (lat_i_npu_mst2_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (lat_i_npu_mst2_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (lat_i_npu_mst2_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (lat_i_npu_mst2_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (lat_i_npu_mst2_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (lat_i_npu_mst2_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(lat_i_npu_mst2_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (lat_i_npu_mst2_axi_ibp_wrsp_chnl),


  .ibp_cmd_valid             (lat_i_npu_mst2_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (lat_i_npu_mst2_axi_ibp_cmd_accept),
  .ibp_cmd_read              (lat_i_npu_mst2_axi_ibp_cmd_read),
  .ibp_cmd_addr              (lat_i_npu_mst2_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (lat_i_npu_mst2_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (lat_i_npu_mst2_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (lat_i_npu_mst2_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (lat_i_npu_mst2_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (lat_i_npu_mst2_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (lat_i_npu_mst2_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (lat_i_npu_mst2_axi_ibp_cmd_excl),

  .ibp_rd_valid              (lat_i_npu_mst2_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (lat_i_npu_mst2_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (lat_i_npu_mst2_axi_ibp_rd_accept),
  .ibp_err_rd                (lat_i_npu_mst2_axi_ibp_err_rd),
  .ibp_rd_data               (lat_i_npu_mst2_axi_ibp_rd_data),
  .ibp_rd_last               (lat_i_npu_mst2_axi_ibp_rd_last),

  .ibp_wr_valid              (lat_i_npu_mst2_axi_ibp_wr_valid),
  .ibp_wr_accept             (lat_i_npu_mst2_axi_ibp_wr_accept),
  .ibp_wr_data               (lat_i_npu_mst2_axi_ibp_wr_data),
  .ibp_wr_mask               (lat_i_npu_mst2_axi_ibp_wr_mask),
  .ibp_wr_last               (lat_i_npu_mst2_axi_ibp_wr_last),

  .ibp_wr_done               (lat_i_npu_mst2_axi_ibp_wr_done),
  .ibp_wr_excl_done          (lat_i_npu_mst2_axi_ibp_wr_excl_done),
  .ibp_err_wr                (lat_i_npu_mst2_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (lat_i_npu_mst2_axi_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon()
                           );

    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(49),
                           .DATA_W(512),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_npu_mst3_axi__ibp2pack_inst(
                           .ibp_cmd_rgon(mst_npu_mst3_axi_ibp_cmd_rgon),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (mst_npu_mst3_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_npu_mst3_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_npu_mst3_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_npu_mst3_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_npu_mst3_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_npu_mst3_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_npu_mst3_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_npu_mst3_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_npu_mst3_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_npu_mst3_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_npu_mst3_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_npu_mst3_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_npu_mst3_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_npu_mst3_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_npu_mst3_axi_ibp_err_rd),
  .ibp_rd_data               (mst_npu_mst3_axi_ibp_rd_data),
  .ibp_rd_last               (mst_npu_mst3_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_npu_mst3_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_npu_mst3_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_npu_mst3_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_npu_mst3_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_npu_mst3_axi_ibp_wr_last),

  .ibp_wr_done               (mst_npu_mst3_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_npu_mst3_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_npu_mst3_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_npu_mst3_axi_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (mst_npu_mst3_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (mst_npu_mst3_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (mst_npu_mst3_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (mst_npu_mst3_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (mst_npu_mst3_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (mst_npu_mst3_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (mst_npu_mst3_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (mst_npu_mst3_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (mst_npu_mst3_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (mst_npu_mst3_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(mst_npu_mst3_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (mst_npu_mst3_axi_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(mst_npu_mst3_axi_ibp_cmd_chnl_rgon),
                           .ibp_cmd_chnl_user(),
                           .clk(clk),
                           .rst_a(~rst_b)
                           );
    // use master's (with prefix npu_mst3_axi_) clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(1),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_mst3_axi__ibp_buffer_0_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(mst_npu_mst3_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_npu_mst3_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_npu_mst3_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_npu_mst3_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_npu_mst3_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_npu_mst3_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_npu_mst3_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_npu_mst3_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_npu_mst3_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_npu_mst3_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_npu_mst3_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_npu_mst3_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_npu_mst3_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(mst_o_npu_mst3_axi_ibp_cmd_chnl_rgon),



    .o_ibp_cmd_chnl_valid  (mst_o_npu_mst3_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (mst_o_npu_mst3_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (mst_o_npu_mst3_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (mst_o_npu_mst3_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (mst_o_npu_mst3_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (mst_o_npu_mst3_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (mst_o_npu_mst3_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (mst_o_npu_mst3_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (mst_o_npu_mst3_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (mst_o_npu_mst3_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(mst_o_npu_mst3_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (mst_o_npu_mst3_axi_ibp_wrsp_chnl),

                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),
                             .ibp_buffer_idle(),
                             .clk(clk),
                             .rst_a(~rst_b)
                             );

    // use fabric's clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(1),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_mst3_axi__ibp_buffer_1_inst (
                             .i_ibp_clk_en(mss_fab_mst3_clk_en),
                             .i_ibp_cmd_chnl_rgon(mst_o_npu_mst3_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_o_npu_mst3_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_o_npu_mst3_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_o_npu_mst3_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_o_npu_mst3_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_o_npu_mst3_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_o_npu_mst3_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_o_npu_mst3_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_o_npu_mst3_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_o_npu_mst3_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_o_npu_mst3_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_o_npu_mst3_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_o_npu_mst3_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(lat_i_npu_mst3_axi_ibp_cmd_chnl_rgon),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (lat_i_npu_mst3_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (lat_i_npu_mst3_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (lat_i_npu_mst3_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (lat_i_npu_mst3_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (lat_i_npu_mst3_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (lat_i_npu_mst3_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (lat_i_npu_mst3_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (lat_i_npu_mst3_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (lat_i_npu_mst3_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (lat_i_npu_mst3_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(lat_i_npu_mst3_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (lat_i_npu_mst3_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );
    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(49),
                           .DATA_W(512),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_npu_mst3_axi__pack2ibp_inst(
                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(lat_i_npu_mst3_axi_ibp_cmd_chnl_rgon),



    .ibp_cmd_chnl_valid  (lat_i_npu_mst3_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (lat_i_npu_mst3_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (lat_i_npu_mst3_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (lat_i_npu_mst3_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (lat_i_npu_mst3_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (lat_i_npu_mst3_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (lat_i_npu_mst3_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (lat_i_npu_mst3_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (lat_i_npu_mst3_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (lat_i_npu_mst3_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(lat_i_npu_mst3_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (lat_i_npu_mst3_axi_ibp_wrsp_chnl),


  .ibp_cmd_valid             (lat_i_npu_mst3_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (lat_i_npu_mst3_axi_ibp_cmd_accept),
  .ibp_cmd_read              (lat_i_npu_mst3_axi_ibp_cmd_read),
  .ibp_cmd_addr              (lat_i_npu_mst3_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (lat_i_npu_mst3_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (lat_i_npu_mst3_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (lat_i_npu_mst3_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (lat_i_npu_mst3_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (lat_i_npu_mst3_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (lat_i_npu_mst3_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (lat_i_npu_mst3_axi_ibp_cmd_excl),

  .ibp_rd_valid              (lat_i_npu_mst3_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (lat_i_npu_mst3_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (lat_i_npu_mst3_axi_ibp_rd_accept),
  .ibp_err_rd                (lat_i_npu_mst3_axi_ibp_err_rd),
  .ibp_rd_data               (lat_i_npu_mst3_axi_ibp_rd_data),
  .ibp_rd_last               (lat_i_npu_mst3_axi_ibp_rd_last),

  .ibp_wr_valid              (lat_i_npu_mst3_axi_ibp_wr_valid),
  .ibp_wr_accept             (lat_i_npu_mst3_axi_ibp_wr_accept),
  .ibp_wr_data               (lat_i_npu_mst3_axi_ibp_wr_data),
  .ibp_wr_mask               (lat_i_npu_mst3_axi_ibp_wr_mask),
  .ibp_wr_last               (lat_i_npu_mst3_axi_ibp_wr_last),

  .ibp_wr_done               (lat_i_npu_mst3_axi_ibp_wr_done),
  .ibp_wr_excl_done          (lat_i_npu_mst3_axi_ibp_wr_excl_done),
  .ibp_err_wr                (lat_i_npu_mst3_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (lat_i_npu_mst3_axi_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon()
                           );

    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(49),
                           .DATA_W(512),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_npu_mst4_axi__ibp2pack_inst(
                           .ibp_cmd_rgon(mst_npu_mst4_axi_ibp_cmd_rgon),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (mst_npu_mst4_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_npu_mst4_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_npu_mst4_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_npu_mst4_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_npu_mst4_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_npu_mst4_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_npu_mst4_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_npu_mst4_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_npu_mst4_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_npu_mst4_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_npu_mst4_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_npu_mst4_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_npu_mst4_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_npu_mst4_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_npu_mst4_axi_ibp_err_rd),
  .ibp_rd_data               (mst_npu_mst4_axi_ibp_rd_data),
  .ibp_rd_last               (mst_npu_mst4_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_npu_mst4_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_npu_mst4_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_npu_mst4_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_npu_mst4_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_npu_mst4_axi_ibp_wr_last),

  .ibp_wr_done               (mst_npu_mst4_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_npu_mst4_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_npu_mst4_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_npu_mst4_axi_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (mst_npu_mst4_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (mst_npu_mst4_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (mst_npu_mst4_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (mst_npu_mst4_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (mst_npu_mst4_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (mst_npu_mst4_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (mst_npu_mst4_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (mst_npu_mst4_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (mst_npu_mst4_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (mst_npu_mst4_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(mst_npu_mst4_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (mst_npu_mst4_axi_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(mst_npu_mst4_axi_ibp_cmd_chnl_rgon),
                           .ibp_cmd_chnl_user(),
                           .clk(clk),
                           .rst_a(~rst_b)
                           );
    // use master's (with prefix npu_mst4_axi_) clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(1),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_mst4_axi__ibp_buffer_0_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(mst_npu_mst4_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_npu_mst4_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_npu_mst4_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_npu_mst4_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_npu_mst4_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_npu_mst4_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_npu_mst4_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_npu_mst4_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_npu_mst4_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_npu_mst4_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_npu_mst4_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_npu_mst4_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_npu_mst4_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(mst_o_npu_mst4_axi_ibp_cmd_chnl_rgon),



    .o_ibp_cmd_chnl_valid  (mst_o_npu_mst4_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (mst_o_npu_mst4_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (mst_o_npu_mst4_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (mst_o_npu_mst4_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (mst_o_npu_mst4_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (mst_o_npu_mst4_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (mst_o_npu_mst4_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (mst_o_npu_mst4_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (mst_o_npu_mst4_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (mst_o_npu_mst4_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(mst_o_npu_mst4_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (mst_o_npu_mst4_axi_ibp_wrsp_chnl),

                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),
                             .ibp_buffer_idle(),
                             .clk(clk),
                             .rst_a(~rst_b)
                             );

    // use fabric's clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(1),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_mst4_axi__ibp_buffer_1_inst (
                             .i_ibp_clk_en(mss_fab_mst4_clk_en),
                             .i_ibp_cmd_chnl_rgon(mst_o_npu_mst4_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_o_npu_mst4_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_o_npu_mst4_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_o_npu_mst4_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_o_npu_mst4_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_o_npu_mst4_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_o_npu_mst4_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_o_npu_mst4_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_o_npu_mst4_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_o_npu_mst4_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_o_npu_mst4_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_o_npu_mst4_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_o_npu_mst4_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(lat_i_npu_mst4_axi_ibp_cmd_chnl_rgon),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (lat_i_npu_mst4_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (lat_i_npu_mst4_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (lat_i_npu_mst4_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (lat_i_npu_mst4_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (lat_i_npu_mst4_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (lat_i_npu_mst4_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (lat_i_npu_mst4_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (lat_i_npu_mst4_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (lat_i_npu_mst4_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (lat_i_npu_mst4_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(lat_i_npu_mst4_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (lat_i_npu_mst4_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );
    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(49),
                           .DATA_W(512),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_npu_mst4_axi__pack2ibp_inst(
                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(lat_i_npu_mst4_axi_ibp_cmd_chnl_rgon),



    .ibp_cmd_chnl_valid  (lat_i_npu_mst4_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (lat_i_npu_mst4_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (lat_i_npu_mst4_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (lat_i_npu_mst4_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (lat_i_npu_mst4_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (lat_i_npu_mst4_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (lat_i_npu_mst4_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (lat_i_npu_mst4_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (lat_i_npu_mst4_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (lat_i_npu_mst4_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(lat_i_npu_mst4_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (lat_i_npu_mst4_axi_ibp_wrsp_chnl),


  .ibp_cmd_valid             (lat_i_npu_mst4_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (lat_i_npu_mst4_axi_ibp_cmd_accept),
  .ibp_cmd_read              (lat_i_npu_mst4_axi_ibp_cmd_read),
  .ibp_cmd_addr              (lat_i_npu_mst4_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (lat_i_npu_mst4_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (lat_i_npu_mst4_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (lat_i_npu_mst4_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (lat_i_npu_mst4_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (lat_i_npu_mst4_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (lat_i_npu_mst4_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (lat_i_npu_mst4_axi_ibp_cmd_excl),

  .ibp_rd_valid              (lat_i_npu_mst4_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (lat_i_npu_mst4_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (lat_i_npu_mst4_axi_ibp_rd_accept),
  .ibp_err_rd                (lat_i_npu_mst4_axi_ibp_err_rd),
  .ibp_rd_data               (lat_i_npu_mst4_axi_ibp_rd_data),
  .ibp_rd_last               (lat_i_npu_mst4_axi_ibp_rd_last),

  .ibp_wr_valid              (lat_i_npu_mst4_axi_ibp_wr_valid),
  .ibp_wr_accept             (lat_i_npu_mst4_axi_ibp_wr_accept),
  .ibp_wr_data               (lat_i_npu_mst4_axi_ibp_wr_data),
  .ibp_wr_mask               (lat_i_npu_mst4_axi_ibp_wr_mask),
  .ibp_wr_last               (lat_i_npu_mst4_axi_ibp_wr_last),

  .ibp_wr_done               (lat_i_npu_mst4_axi_ibp_wr_done),
  .ibp_wr_excl_done          (lat_i_npu_mst4_axi_ibp_wr_excl_done),
  .ibp_err_wr                (lat_i_npu_mst4_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (lat_i_npu_mst4_axi_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon()
                           );

    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(49),
                           .DATA_W(64),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_host_axi__ibp2pack_inst(
                           .ibp_cmd_rgon(mst_host_axi_ibp_cmd_rgon),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (mst_host_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_host_axi_ibp_cmd_accept),
  .ibp_cmd_read              (mst_host_axi_ibp_cmd_read),
  .ibp_cmd_addr              (mst_host_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_host_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_host_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_host_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_host_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_host_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_host_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_host_axi_ibp_cmd_excl),

  .ibp_rd_valid              (mst_host_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_host_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_host_axi_ibp_rd_accept),
  .ibp_err_rd                (mst_host_axi_ibp_err_rd),
  .ibp_rd_data               (mst_host_axi_ibp_rd_data),
  .ibp_rd_last               (mst_host_axi_ibp_rd_last),

  .ibp_wr_valid              (mst_host_axi_ibp_wr_valid),
  .ibp_wr_accept             (mst_host_axi_ibp_wr_accept),
  .ibp_wr_data               (mst_host_axi_ibp_wr_data),
  .ibp_wr_mask               (mst_host_axi_ibp_wr_mask),
  .ibp_wr_last               (mst_host_axi_ibp_wr_last),

  .ibp_wr_done               (mst_host_axi_ibp_wr_done),
  .ibp_wr_excl_done          (mst_host_axi_ibp_wr_excl_done),
  .ibp_err_wr                (mst_host_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_host_axi_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (mst_host_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (mst_host_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (mst_host_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (mst_host_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (mst_host_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (mst_host_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (mst_host_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (mst_host_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (mst_host_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (mst_host_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(mst_host_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (mst_host_axi_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(mst_host_axi_ibp_cmd_chnl_rgon),
                           .ibp_cmd_chnl_user(),
                           .clk(mss_clk),
                           .rst_a(~rst_b)
                           );
    // bypass signals from master port to latency units
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_host_axi__ibp_buffer_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(mst_host_axi_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_host_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_host_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_host_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_host_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_host_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_host_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_host_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_host_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_host_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_host_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_host_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_host_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(lat_i_host_axi_ibp_cmd_chnl_rgon),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (lat_i_host_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (lat_i_host_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (lat_i_host_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (lat_i_host_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (lat_i_host_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (lat_i_host_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (lat_i_host_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (lat_i_host_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (lat_i_host_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (lat_i_host_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(lat_i_host_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (lat_i_host_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );

    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(49),
                           .DATA_W(64),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_host_axi__pack2ibp_inst(



    .ibp_cmd_chnl_valid  (lat_i_host_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (lat_i_host_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (lat_i_host_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (lat_i_host_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (lat_i_host_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (lat_i_host_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (lat_i_host_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (lat_i_host_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (lat_i_host_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (lat_i_host_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(lat_i_host_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (lat_i_host_axi_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(lat_i_host_axi_ibp_cmd_chnl_rgon),

  .ibp_cmd_valid             (lat_i_host_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (lat_i_host_axi_ibp_cmd_accept),
  .ibp_cmd_read              (lat_i_host_axi_ibp_cmd_read),
  .ibp_cmd_addr              (lat_i_host_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (lat_i_host_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (lat_i_host_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (lat_i_host_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (lat_i_host_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (lat_i_host_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (lat_i_host_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (lat_i_host_axi_ibp_cmd_excl),

  .ibp_rd_valid              (lat_i_host_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (lat_i_host_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (lat_i_host_axi_ibp_rd_accept),
  .ibp_err_rd                (lat_i_host_axi_ibp_err_rd),
  .ibp_rd_data               (lat_i_host_axi_ibp_rd_data),
  .ibp_rd_last               (lat_i_host_axi_ibp_rd_last),

  .ibp_wr_valid              (lat_i_host_axi_ibp_wr_valid),
  .ibp_wr_accept             (lat_i_host_axi_ibp_wr_accept),
  .ibp_wr_data               (lat_i_host_axi_ibp_wr_data),
  .ibp_wr_mask               (lat_i_host_axi_ibp_wr_mask),
  .ibp_wr_last               (lat_i_host_axi_ibp_wr_last),

  .ibp_wr_done               (lat_i_host_axi_ibp_wr_done),
  .ibp_wr_excl_done          (lat_i_host_axi_ibp_wr_excl_done),
  .ibp_err_wr                (lat_i_host_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (lat_i_host_axi_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon()
                           );

    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(49),
                           .DATA_W(32),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (32),
    .WD_CHNL_MASK_LSB        (33),
    .WD_CHNL_MASK_W          (4),
    .WD_CHNL_W               (37),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (32),
    .RD_CHNL_W               (35),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_bri4tb__ibp2pack_inst(
                           .ibp_cmd_rgon(mst_bri4tb_ibp_cmd_rgon),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (mst_bri4tb_ibp_cmd_valid),
  .ibp_cmd_accept            (mst_bri4tb_ibp_cmd_accept),
  .ibp_cmd_read              (mst_bri4tb_ibp_cmd_read),
  .ibp_cmd_addr              (mst_bri4tb_ibp_cmd_addr),
  .ibp_cmd_wrap              (mst_bri4tb_ibp_cmd_wrap),
  .ibp_cmd_data_size         (mst_bri4tb_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (mst_bri4tb_ibp_cmd_burst_size),
  .ibp_cmd_prot              (mst_bri4tb_ibp_cmd_prot),
  .ibp_cmd_cache             (mst_bri4tb_ibp_cmd_cache),
  .ibp_cmd_lock              (mst_bri4tb_ibp_cmd_lock),
  .ibp_cmd_excl              (mst_bri4tb_ibp_cmd_excl),

  .ibp_rd_valid              (mst_bri4tb_ibp_rd_valid),
  .ibp_rd_excl_ok            (mst_bri4tb_ibp_rd_excl_ok),
  .ibp_rd_accept             (mst_bri4tb_ibp_rd_accept),
  .ibp_err_rd                (mst_bri4tb_ibp_err_rd),
  .ibp_rd_data               (mst_bri4tb_ibp_rd_data),
  .ibp_rd_last               (mst_bri4tb_ibp_rd_last),

  .ibp_wr_valid              (mst_bri4tb_ibp_wr_valid),
  .ibp_wr_accept             (mst_bri4tb_ibp_wr_accept),
  .ibp_wr_data               (mst_bri4tb_ibp_wr_data),
  .ibp_wr_mask               (mst_bri4tb_ibp_wr_mask),
  .ibp_wr_last               (mst_bri4tb_ibp_wr_last),

  .ibp_wr_done               (mst_bri4tb_ibp_wr_done),
  .ibp_wr_excl_done          (mst_bri4tb_ibp_wr_excl_done),
  .ibp_err_wr                (mst_bri4tb_ibp_err_wr),
  .ibp_wr_resp_accept        (mst_bri4tb_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (mst_bri4tb_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (mst_bri4tb_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (mst_bri4tb_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (mst_bri4tb_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (mst_bri4tb_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (mst_bri4tb_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (mst_bri4tb_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (mst_bri4tb_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (mst_bri4tb_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (mst_bri4tb_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(mst_bri4tb_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (mst_bri4tb_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(mst_bri4tb_ibp_cmd_chnl_rgon),
                           .ibp_cmd_chnl_user(),
                           .clk(mss_clk),
                           .rst_a(~rst_b)
                           );
    // bypass signals from master port to latency units
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (32),
    .WD_CHNL_MASK_LSB        (33),
    .WD_CHNL_MASK_W          (4),
    .WD_CHNL_W               (37),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (32),
    .RD_CHNL_W               (35),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_bri4tb__ibp_buffer_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(mst_bri4tb_ibp_cmd_chnl_rgon),



    .i_ibp_cmd_chnl_valid  (mst_bri4tb_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mst_bri4tb_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mst_bri4tb_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mst_bri4tb_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mst_bri4tb_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mst_bri4tb_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mst_bri4tb_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mst_bri4tb_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mst_bri4tb_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mst_bri4tb_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mst_bri4tb_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mst_bri4tb_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(lat_i_bri4tb_ibp_cmd_chnl_rgon),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (lat_i_bri4tb_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (lat_i_bri4tb_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (lat_i_bri4tb_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (lat_i_bri4tb_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (lat_i_bri4tb_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (lat_i_bri4tb_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (lat_i_bri4tb_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (lat_i_bri4tb_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (lat_i_bri4tb_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (lat_i_bri4tb_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(lat_i_bri4tb_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (lat_i_bri4tb_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );

    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(49),
                           .DATA_W(32),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (32),
    .WD_CHNL_MASK_LSB        (33),
    .WD_CHNL_MASK_W          (4),
    .WD_CHNL_W               (37),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (32),
    .RD_CHNL_W               (35),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_bri4tb__pack2ibp_inst(



    .ibp_cmd_chnl_valid  (lat_i_bri4tb_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (lat_i_bri4tb_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (lat_i_bri4tb_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (lat_i_bri4tb_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (lat_i_bri4tb_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (lat_i_bri4tb_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (lat_i_bri4tb_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (lat_i_bri4tb_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (lat_i_bri4tb_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (lat_i_bri4tb_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(lat_i_bri4tb_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (lat_i_bri4tb_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(lat_i_bri4tb_ibp_cmd_chnl_rgon),

  .ibp_cmd_valid             (lat_i_bri4tb_ibp_cmd_valid),
  .ibp_cmd_accept            (lat_i_bri4tb_ibp_cmd_accept),
  .ibp_cmd_read              (lat_i_bri4tb_ibp_cmd_read),
  .ibp_cmd_addr              (lat_i_bri4tb_ibp_cmd_addr),
  .ibp_cmd_wrap              (lat_i_bri4tb_ibp_cmd_wrap),
  .ibp_cmd_data_size         (lat_i_bri4tb_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (lat_i_bri4tb_ibp_cmd_burst_size),
  .ibp_cmd_prot              (lat_i_bri4tb_ibp_cmd_prot),
  .ibp_cmd_cache             (lat_i_bri4tb_ibp_cmd_cache),
  .ibp_cmd_lock              (lat_i_bri4tb_ibp_cmd_lock),
  .ibp_cmd_excl              (lat_i_bri4tb_ibp_cmd_excl),

  .ibp_rd_valid              (lat_i_bri4tb_ibp_rd_valid),
  .ibp_rd_excl_ok            (lat_i_bri4tb_ibp_rd_excl_ok),
  .ibp_rd_accept             (lat_i_bri4tb_ibp_rd_accept),
  .ibp_err_rd                (lat_i_bri4tb_ibp_err_rd),
  .ibp_rd_data               (lat_i_bri4tb_ibp_rd_data),
  .ibp_rd_last               (lat_i_bri4tb_ibp_rd_last),

  .ibp_wr_valid              (lat_i_bri4tb_ibp_wr_valid),
  .ibp_wr_accept             (lat_i_bri4tb_ibp_wr_accept),
  .ibp_wr_data               (lat_i_bri4tb_ibp_wr_data),
  .ibp_wr_mask               (lat_i_bri4tb_ibp_wr_mask),
  .ibp_wr_last               (lat_i_bri4tb_ibp_wr_last),

  .ibp_wr_done               (lat_i_bri4tb_ibp_wr_done),
  .ibp_wr_excl_done          (lat_i_bri4tb_ibp_wr_excl_done),
  .ibp_err_wr                (lat_i_bri4tb_ibp_err_wr),
  .ibp_wr_resp_accept        (lat_i_bri4tb_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon()
                           );


    // Latency units
    alb_mss_fab_ibp_lat #(.a_w(49),
                          .d_w(64),
                          .depl2(0)
                          ) u_npu_mst0_axi_ibp_lat_inst(
                                                     // clock and reset
                                                     .clk(mss_clk),
                                                     .clk_en(1'b1),
                                                     .rst_b(rst_b),
                                                      // Input IBP I/F

  .i_ibp_cmd_valid             (lat_i_npu_mst0_axi_ibp_cmd_valid),
  .i_ibp_cmd_accept            (lat_i_npu_mst0_axi_ibp_cmd_accept),
  .i_ibp_cmd_read              (lat_i_npu_mst0_axi_ibp_cmd_read),
  .i_ibp_cmd_addr              (lat_i_npu_mst0_axi_ibp_cmd_addr),
  .i_ibp_cmd_wrap              (lat_i_npu_mst0_axi_ibp_cmd_wrap),
  .i_ibp_cmd_data_size         (lat_i_npu_mst0_axi_ibp_cmd_data_size),
  .i_ibp_cmd_burst_size        (lat_i_npu_mst0_axi_ibp_cmd_burst_size),
  .i_ibp_cmd_prot              (lat_i_npu_mst0_axi_ibp_cmd_prot),
  .i_ibp_cmd_cache             (lat_i_npu_mst0_axi_ibp_cmd_cache),
  .i_ibp_cmd_lock              (lat_i_npu_mst0_axi_ibp_cmd_lock),
  .i_ibp_cmd_excl              (lat_i_npu_mst0_axi_ibp_cmd_excl),

  .i_ibp_rd_valid              (lat_i_npu_mst0_axi_ibp_rd_valid),
  .i_ibp_rd_excl_ok            (lat_i_npu_mst0_axi_ibp_rd_excl_ok),
  .i_ibp_rd_accept             (lat_i_npu_mst0_axi_ibp_rd_accept),
  .i_ibp_err_rd                (lat_i_npu_mst0_axi_ibp_err_rd),
  .i_ibp_rd_data               (lat_i_npu_mst0_axi_ibp_rd_data),
  .i_ibp_rd_last               (lat_i_npu_mst0_axi_ibp_rd_last),

  .i_ibp_wr_valid              (lat_i_npu_mst0_axi_ibp_wr_valid),
  .i_ibp_wr_accept             (lat_i_npu_mst0_axi_ibp_wr_accept),
  .i_ibp_wr_data               (lat_i_npu_mst0_axi_ibp_wr_data),
  .i_ibp_wr_mask               (lat_i_npu_mst0_axi_ibp_wr_mask),
  .i_ibp_wr_last               (lat_i_npu_mst0_axi_ibp_wr_last),

  .i_ibp_wr_done               (lat_i_npu_mst0_axi_ibp_wr_done),
  .i_ibp_wr_excl_done          (lat_i_npu_mst0_axi_ibp_wr_excl_done),
  .i_ibp_err_wr                (lat_i_npu_mst0_axi_ibp_err_wr),
  .i_ibp_wr_resp_accept        (lat_i_npu_mst0_axi_ibp_wr_resp_accept),
                                                     // Output IBP I/F

  .o_ibp_cmd_valid             (lat_o_npu_mst0_axi_ibp_cmd_valid),
  .o_ibp_cmd_accept            (lat_o_npu_mst0_axi_ibp_cmd_accept),
  .o_ibp_cmd_read              (lat_o_npu_mst0_axi_ibp_cmd_read),
  .o_ibp_cmd_addr              (lat_o_npu_mst0_axi_ibp_cmd_addr),
  .o_ibp_cmd_wrap              (lat_o_npu_mst0_axi_ibp_cmd_wrap),
  .o_ibp_cmd_data_size         (lat_o_npu_mst0_axi_ibp_cmd_data_size),
  .o_ibp_cmd_burst_size        (lat_o_npu_mst0_axi_ibp_cmd_burst_size),
  .o_ibp_cmd_prot              (lat_o_npu_mst0_axi_ibp_cmd_prot),
  .o_ibp_cmd_cache             (lat_o_npu_mst0_axi_ibp_cmd_cache),
  .o_ibp_cmd_lock              (lat_o_npu_mst0_axi_ibp_cmd_lock),
  .o_ibp_cmd_excl              (lat_o_npu_mst0_axi_ibp_cmd_excl),

  .o_ibp_rd_valid              (lat_o_npu_mst0_axi_ibp_rd_valid),
  .o_ibp_rd_excl_ok            (lat_o_npu_mst0_axi_ibp_rd_excl_ok),
  .o_ibp_rd_accept             (lat_o_npu_mst0_axi_ibp_rd_accept),
  .o_ibp_err_rd                (lat_o_npu_mst0_axi_ibp_err_rd),
  .o_ibp_rd_data               (lat_o_npu_mst0_axi_ibp_rd_data),
  .o_ibp_rd_last               (lat_o_npu_mst0_axi_ibp_rd_last),

  .o_ibp_wr_valid              (lat_o_npu_mst0_axi_ibp_wr_valid),
  .o_ibp_wr_accept             (lat_o_npu_mst0_axi_ibp_wr_accept),
  .o_ibp_wr_data               (lat_o_npu_mst0_axi_ibp_wr_data),
  .o_ibp_wr_mask               (lat_o_npu_mst0_axi_ibp_wr_mask),
  .o_ibp_wr_last               (lat_o_npu_mst0_axi_ibp_wr_last),

  .o_ibp_wr_done               (lat_o_npu_mst0_axi_ibp_wr_done),
  .o_ibp_wr_excl_done          (lat_o_npu_mst0_axi_ibp_wr_excl_done),
  .o_ibp_err_wr                (lat_o_npu_mst0_axi_ibp_err_wr),
  .o_ibp_wr_resp_accept        (lat_o_npu_mst0_axi_ibp_wr_resp_accept),
                                                      // Profiler I/F
                                                     .cfg_lat_w(mss_fab_cfg_lat_w[0*12+:12]),
                                                     .cfg_lat_r(mss_fab_cfg_lat_r[0*12+:12]),
                                                     .cfg_wr_bw(mss_fab_cfg_wr_bw[0*10+:10]),
                                                     .cfg_rd_bw(mss_fab_cfg_rd_bw[0*10+:10]),
                                                     .perf_awf(mss_fab_perf_awf[0]),
                                                     .perf_arf(mss_fab_perf_arf[0]),
                                                     .perf_aw(mss_fab_perf_aw[0]),
                                                     .perf_ar(mss_fab_perf_ar[0]),
                                                     .perf_w(mss_fab_perf_w[0]),
                                                     .perf_wl(mss_fab_perf_wl[0]),
                                                     .perf_r(mss_fab_perf_r[0]),
                                                     .perf_rl(mss_fab_perf_rl[0]),
                                                     .perf_b(mss_fab_perf_b[0]));
    alb_mss_fab_ibp_lat #(.a_w(49),
                          .d_w(512),
                          .depl2(0)
                          ) u_npu_mst1_axi_ibp_lat_inst(
                                                     // clock and reset
                                                     .clk(mss_clk),
                                                     .clk_en(1'b1),
                                                     .rst_b(rst_b),
                                                      // Input IBP I/F

  .i_ibp_cmd_valid             (lat_i_npu_mst1_axi_ibp_cmd_valid),
  .i_ibp_cmd_accept            (lat_i_npu_mst1_axi_ibp_cmd_accept),
  .i_ibp_cmd_read              (lat_i_npu_mst1_axi_ibp_cmd_read),
  .i_ibp_cmd_addr              (lat_i_npu_mst1_axi_ibp_cmd_addr),
  .i_ibp_cmd_wrap              (lat_i_npu_mst1_axi_ibp_cmd_wrap),
  .i_ibp_cmd_data_size         (lat_i_npu_mst1_axi_ibp_cmd_data_size),
  .i_ibp_cmd_burst_size        (lat_i_npu_mst1_axi_ibp_cmd_burst_size),
  .i_ibp_cmd_prot              (lat_i_npu_mst1_axi_ibp_cmd_prot),
  .i_ibp_cmd_cache             (lat_i_npu_mst1_axi_ibp_cmd_cache),
  .i_ibp_cmd_lock              (lat_i_npu_mst1_axi_ibp_cmd_lock),
  .i_ibp_cmd_excl              (lat_i_npu_mst1_axi_ibp_cmd_excl),

  .i_ibp_rd_valid              (lat_i_npu_mst1_axi_ibp_rd_valid),
  .i_ibp_rd_excl_ok            (lat_i_npu_mst1_axi_ibp_rd_excl_ok),
  .i_ibp_rd_accept             (lat_i_npu_mst1_axi_ibp_rd_accept),
  .i_ibp_err_rd                (lat_i_npu_mst1_axi_ibp_err_rd),
  .i_ibp_rd_data               (lat_i_npu_mst1_axi_ibp_rd_data),
  .i_ibp_rd_last               (lat_i_npu_mst1_axi_ibp_rd_last),

  .i_ibp_wr_valid              (lat_i_npu_mst1_axi_ibp_wr_valid),
  .i_ibp_wr_accept             (lat_i_npu_mst1_axi_ibp_wr_accept),
  .i_ibp_wr_data               (lat_i_npu_mst1_axi_ibp_wr_data),
  .i_ibp_wr_mask               (lat_i_npu_mst1_axi_ibp_wr_mask),
  .i_ibp_wr_last               (lat_i_npu_mst1_axi_ibp_wr_last),

  .i_ibp_wr_done               (lat_i_npu_mst1_axi_ibp_wr_done),
  .i_ibp_wr_excl_done          (lat_i_npu_mst1_axi_ibp_wr_excl_done),
  .i_ibp_err_wr                (lat_i_npu_mst1_axi_ibp_err_wr),
  .i_ibp_wr_resp_accept        (lat_i_npu_mst1_axi_ibp_wr_resp_accept),
                                                     // Output IBP I/F

  .o_ibp_cmd_valid             (lat_o_npu_mst1_axi_ibp_cmd_valid),
  .o_ibp_cmd_accept            (lat_o_npu_mst1_axi_ibp_cmd_accept),
  .o_ibp_cmd_read              (lat_o_npu_mst1_axi_ibp_cmd_read),
  .o_ibp_cmd_addr              (lat_o_npu_mst1_axi_ibp_cmd_addr),
  .o_ibp_cmd_wrap              (lat_o_npu_mst1_axi_ibp_cmd_wrap),
  .o_ibp_cmd_data_size         (lat_o_npu_mst1_axi_ibp_cmd_data_size),
  .o_ibp_cmd_burst_size        (lat_o_npu_mst1_axi_ibp_cmd_burst_size),
  .o_ibp_cmd_prot              (lat_o_npu_mst1_axi_ibp_cmd_prot),
  .o_ibp_cmd_cache             (lat_o_npu_mst1_axi_ibp_cmd_cache),
  .o_ibp_cmd_lock              (lat_o_npu_mst1_axi_ibp_cmd_lock),
  .o_ibp_cmd_excl              (lat_o_npu_mst1_axi_ibp_cmd_excl),

  .o_ibp_rd_valid              (lat_o_npu_mst1_axi_ibp_rd_valid),
  .o_ibp_rd_excl_ok            (lat_o_npu_mst1_axi_ibp_rd_excl_ok),
  .o_ibp_rd_accept             (lat_o_npu_mst1_axi_ibp_rd_accept),
  .o_ibp_err_rd                (lat_o_npu_mst1_axi_ibp_err_rd),
  .o_ibp_rd_data               (lat_o_npu_mst1_axi_ibp_rd_data),
  .o_ibp_rd_last               (lat_o_npu_mst1_axi_ibp_rd_last),

  .o_ibp_wr_valid              (lat_o_npu_mst1_axi_ibp_wr_valid),
  .o_ibp_wr_accept             (lat_o_npu_mst1_axi_ibp_wr_accept),
  .o_ibp_wr_data               (lat_o_npu_mst1_axi_ibp_wr_data),
  .o_ibp_wr_mask               (lat_o_npu_mst1_axi_ibp_wr_mask),
  .o_ibp_wr_last               (lat_o_npu_mst1_axi_ibp_wr_last),

  .o_ibp_wr_done               (lat_o_npu_mst1_axi_ibp_wr_done),
  .o_ibp_wr_excl_done          (lat_o_npu_mst1_axi_ibp_wr_excl_done),
  .o_ibp_err_wr                (lat_o_npu_mst1_axi_ibp_err_wr),
  .o_ibp_wr_resp_accept        (lat_o_npu_mst1_axi_ibp_wr_resp_accept),
                                                      // Profiler I/F
                                                     .cfg_lat_w(mss_fab_cfg_lat_w[1*12+:12]),
                                                     .cfg_lat_r(mss_fab_cfg_lat_r[1*12+:12]),
                                                     .cfg_wr_bw(mss_fab_cfg_wr_bw[1*10+:10]),
                                                     .cfg_rd_bw(mss_fab_cfg_rd_bw[1*10+:10]),
                                                     .perf_awf(mss_fab_perf_awf[1]),
                                                     .perf_arf(mss_fab_perf_arf[1]),
                                                     .perf_aw(mss_fab_perf_aw[1]),
                                                     .perf_ar(mss_fab_perf_ar[1]),
                                                     .perf_w(mss_fab_perf_w[1]),
                                                     .perf_wl(mss_fab_perf_wl[1]),
                                                     .perf_r(mss_fab_perf_r[1]),
                                                     .perf_rl(mss_fab_perf_rl[1]),
                                                     .perf_b(mss_fab_perf_b[1]));
    alb_mss_fab_ibp_lat #(.a_w(49),
                          .d_w(512),
                          .depl2(0)
                          ) u_npu_mst2_axi_ibp_lat_inst(
                                                     // clock and reset
                                                     .clk(mss_clk),
                                                     .clk_en(1'b1),
                                                     .rst_b(rst_b),
                                                      // Input IBP I/F

  .i_ibp_cmd_valid             (lat_i_npu_mst2_axi_ibp_cmd_valid),
  .i_ibp_cmd_accept            (lat_i_npu_mst2_axi_ibp_cmd_accept),
  .i_ibp_cmd_read              (lat_i_npu_mst2_axi_ibp_cmd_read),
  .i_ibp_cmd_addr              (lat_i_npu_mst2_axi_ibp_cmd_addr),
  .i_ibp_cmd_wrap              (lat_i_npu_mst2_axi_ibp_cmd_wrap),
  .i_ibp_cmd_data_size         (lat_i_npu_mst2_axi_ibp_cmd_data_size),
  .i_ibp_cmd_burst_size        (lat_i_npu_mst2_axi_ibp_cmd_burst_size),
  .i_ibp_cmd_prot              (lat_i_npu_mst2_axi_ibp_cmd_prot),
  .i_ibp_cmd_cache             (lat_i_npu_mst2_axi_ibp_cmd_cache),
  .i_ibp_cmd_lock              (lat_i_npu_mst2_axi_ibp_cmd_lock),
  .i_ibp_cmd_excl              (lat_i_npu_mst2_axi_ibp_cmd_excl),

  .i_ibp_rd_valid              (lat_i_npu_mst2_axi_ibp_rd_valid),
  .i_ibp_rd_excl_ok            (lat_i_npu_mst2_axi_ibp_rd_excl_ok),
  .i_ibp_rd_accept             (lat_i_npu_mst2_axi_ibp_rd_accept),
  .i_ibp_err_rd                (lat_i_npu_mst2_axi_ibp_err_rd),
  .i_ibp_rd_data               (lat_i_npu_mst2_axi_ibp_rd_data),
  .i_ibp_rd_last               (lat_i_npu_mst2_axi_ibp_rd_last),

  .i_ibp_wr_valid              (lat_i_npu_mst2_axi_ibp_wr_valid),
  .i_ibp_wr_accept             (lat_i_npu_mst2_axi_ibp_wr_accept),
  .i_ibp_wr_data               (lat_i_npu_mst2_axi_ibp_wr_data),
  .i_ibp_wr_mask               (lat_i_npu_mst2_axi_ibp_wr_mask),
  .i_ibp_wr_last               (lat_i_npu_mst2_axi_ibp_wr_last),

  .i_ibp_wr_done               (lat_i_npu_mst2_axi_ibp_wr_done),
  .i_ibp_wr_excl_done          (lat_i_npu_mst2_axi_ibp_wr_excl_done),
  .i_ibp_err_wr                (lat_i_npu_mst2_axi_ibp_err_wr),
  .i_ibp_wr_resp_accept        (lat_i_npu_mst2_axi_ibp_wr_resp_accept),
                                                     // Output IBP I/F

  .o_ibp_cmd_valid             (lat_o_npu_mst2_axi_ibp_cmd_valid),
  .o_ibp_cmd_accept            (lat_o_npu_mst2_axi_ibp_cmd_accept),
  .o_ibp_cmd_read              (lat_o_npu_mst2_axi_ibp_cmd_read),
  .o_ibp_cmd_addr              (lat_o_npu_mst2_axi_ibp_cmd_addr),
  .o_ibp_cmd_wrap              (lat_o_npu_mst2_axi_ibp_cmd_wrap),
  .o_ibp_cmd_data_size         (lat_o_npu_mst2_axi_ibp_cmd_data_size),
  .o_ibp_cmd_burst_size        (lat_o_npu_mst2_axi_ibp_cmd_burst_size),
  .o_ibp_cmd_prot              (lat_o_npu_mst2_axi_ibp_cmd_prot),
  .o_ibp_cmd_cache             (lat_o_npu_mst2_axi_ibp_cmd_cache),
  .o_ibp_cmd_lock              (lat_o_npu_mst2_axi_ibp_cmd_lock),
  .o_ibp_cmd_excl              (lat_o_npu_mst2_axi_ibp_cmd_excl),

  .o_ibp_rd_valid              (lat_o_npu_mst2_axi_ibp_rd_valid),
  .o_ibp_rd_excl_ok            (lat_o_npu_mst2_axi_ibp_rd_excl_ok),
  .o_ibp_rd_accept             (lat_o_npu_mst2_axi_ibp_rd_accept),
  .o_ibp_err_rd                (lat_o_npu_mst2_axi_ibp_err_rd),
  .o_ibp_rd_data               (lat_o_npu_mst2_axi_ibp_rd_data),
  .o_ibp_rd_last               (lat_o_npu_mst2_axi_ibp_rd_last),

  .o_ibp_wr_valid              (lat_o_npu_mst2_axi_ibp_wr_valid),
  .o_ibp_wr_accept             (lat_o_npu_mst2_axi_ibp_wr_accept),
  .o_ibp_wr_data               (lat_o_npu_mst2_axi_ibp_wr_data),
  .o_ibp_wr_mask               (lat_o_npu_mst2_axi_ibp_wr_mask),
  .o_ibp_wr_last               (lat_o_npu_mst2_axi_ibp_wr_last),

  .o_ibp_wr_done               (lat_o_npu_mst2_axi_ibp_wr_done),
  .o_ibp_wr_excl_done          (lat_o_npu_mst2_axi_ibp_wr_excl_done),
  .o_ibp_err_wr                (lat_o_npu_mst2_axi_ibp_err_wr),
  .o_ibp_wr_resp_accept        (lat_o_npu_mst2_axi_ibp_wr_resp_accept),
                                                      // Profiler I/F
                                                     .cfg_lat_w(mss_fab_cfg_lat_w[2*12+:12]),
                                                     .cfg_lat_r(mss_fab_cfg_lat_r[2*12+:12]),
                                                     .cfg_wr_bw(mss_fab_cfg_wr_bw[2*10+:10]),
                                                     .cfg_rd_bw(mss_fab_cfg_rd_bw[2*10+:10]),
                                                     .perf_awf(mss_fab_perf_awf[2]),
                                                     .perf_arf(mss_fab_perf_arf[2]),
                                                     .perf_aw(mss_fab_perf_aw[2]),
                                                     .perf_ar(mss_fab_perf_ar[2]),
                                                     .perf_w(mss_fab_perf_w[2]),
                                                     .perf_wl(mss_fab_perf_wl[2]),
                                                     .perf_r(mss_fab_perf_r[2]),
                                                     .perf_rl(mss_fab_perf_rl[2]),
                                                     .perf_b(mss_fab_perf_b[2]));
    alb_mss_fab_ibp_lat #(.a_w(49),
                          .d_w(512),
                          .depl2(0)
                          ) u_npu_mst3_axi_ibp_lat_inst(
                                                     // clock and reset
                                                     .clk(mss_clk),
                                                     .clk_en(1'b1),
                                                     .rst_b(rst_b),
                                                      // Input IBP I/F

  .i_ibp_cmd_valid             (lat_i_npu_mst3_axi_ibp_cmd_valid),
  .i_ibp_cmd_accept            (lat_i_npu_mst3_axi_ibp_cmd_accept),
  .i_ibp_cmd_read              (lat_i_npu_mst3_axi_ibp_cmd_read),
  .i_ibp_cmd_addr              (lat_i_npu_mst3_axi_ibp_cmd_addr),
  .i_ibp_cmd_wrap              (lat_i_npu_mst3_axi_ibp_cmd_wrap),
  .i_ibp_cmd_data_size         (lat_i_npu_mst3_axi_ibp_cmd_data_size),
  .i_ibp_cmd_burst_size        (lat_i_npu_mst3_axi_ibp_cmd_burst_size),
  .i_ibp_cmd_prot              (lat_i_npu_mst3_axi_ibp_cmd_prot),
  .i_ibp_cmd_cache             (lat_i_npu_mst3_axi_ibp_cmd_cache),
  .i_ibp_cmd_lock              (lat_i_npu_mst3_axi_ibp_cmd_lock),
  .i_ibp_cmd_excl              (lat_i_npu_mst3_axi_ibp_cmd_excl),

  .i_ibp_rd_valid              (lat_i_npu_mst3_axi_ibp_rd_valid),
  .i_ibp_rd_excl_ok            (lat_i_npu_mst3_axi_ibp_rd_excl_ok),
  .i_ibp_rd_accept             (lat_i_npu_mst3_axi_ibp_rd_accept),
  .i_ibp_err_rd                (lat_i_npu_mst3_axi_ibp_err_rd),
  .i_ibp_rd_data               (lat_i_npu_mst3_axi_ibp_rd_data),
  .i_ibp_rd_last               (lat_i_npu_mst3_axi_ibp_rd_last),

  .i_ibp_wr_valid              (lat_i_npu_mst3_axi_ibp_wr_valid),
  .i_ibp_wr_accept             (lat_i_npu_mst3_axi_ibp_wr_accept),
  .i_ibp_wr_data               (lat_i_npu_mst3_axi_ibp_wr_data),
  .i_ibp_wr_mask               (lat_i_npu_mst3_axi_ibp_wr_mask),
  .i_ibp_wr_last               (lat_i_npu_mst3_axi_ibp_wr_last),

  .i_ibp_wr_done               (lat_i_npu_mst3_axi_ibp_wr_done),
  .i_ibp_wr_excl_done          (lat_i_npu_mst3_axi_ibp_wr_excl_done),
  .i_ibp_err_wr                (lat_i_npu_mst3_axi_ibp_err_wr),
  .i_ibp_wr_resp_accept        (lat_i_npu_mst3_axi_ibp_wr_resp_accept),
                                                     // Output IBP I/F

  .o_ibp_cmd_valid             (lat_o_npu_mst3_axi_ibp_cmd_valid),
  .o_ibp_cmd_accept            (lat_o_npu_mst3_axi_ibp_cmd_accept),
  .o_ibp_cmd_read              (lat_o_npu_mst3_axi_ibp_cmd_read),
  .o_ibp_cmd_addr              (lat_o_npu_mst3_axi_ibp_cmd_addr),
  .o_ibp_cmd_wrap              (lat_o_npu_mst3_axi_ibp_cmd_wrap),
  .o_ibp_cmd_data_size         (lat_o_npu_mst3_axi_ibp_cmd_data_size),
  .o_ibp_cmd_burst_size        (lat_o_npu_mst3_axi_ibp_cmd_burst_size),
  .o_ibp_cmd_prot              (lat_o_npu_mst3_axi_ibp_cmd_prot),
  .o_ibp_cmd_cache             (lat_o_npu_mst3_axi_ibp_cmd_cache),
  .o_ibp_cmd_lock              (lat_o_npu_mst3_axi_ibp_cmd_lock),
  .o_ibp_cmd_excl              (lat_o_npu_mst3_axi_ibp_cmd_excl),

  .o_ibp_rd_valid              (lat_o_npu_mst3_axi_ibp_rd_valid),
  .o_ibp_rd_excl_ok            (lat_o_npu_mst3_axi_ibp_rd_excl_ok),
  .o_ibp_rd_accept             (lat_o_npu_mst3_axi_ibp_rd_accept),
  .o_ibp_err_rd                (lat_o_npu_mst3_axi_ibp_err_rd),
  .o_ibp_rd_data               (lat_o_npu_mst3_axi_ibp_rd_data),
  .o_ibp_rd_last               (lat_o_npu_mst3_axi_ibp_rd_last),

  .o_ibp_wr_valid              (lat_o_npu_mst3_axi_ibp_wr_valid),
  .o_ibp_wr_accept             (lat_o_npu_mst3_axi_ibp_wr_accept),
  .o_ibp_wr_data               (lat_o_npu_mst3_axi_ibp_wr_data),
  .o_ibp_wr_mask               (lat_o_npu_mst3_axi_ibp_wr_mask),
  .o_ibp_wr_last               (lat_o_npu_mst3_axi_ibp_wr_last),

  .o_ibp_wr_done               (lat_o_npu_mst3_axi_ibp_wr_done),
  .o_ibp_wr_excl_done          (lat_o_npu_mst3_axi_ibp_wr_excl_done),
  .o_ibp_err_wr                (lat_o_npu_mst3_axi_ibp_err_wr),
  .o_ibp_wr_resp_accept        (lat_o_npu_mst3_axi_ibp_wr_resp_accept),
                                                      // Profiler I/F
                                                     .cfg_lat_w(mss_fab_cfg_lat_w[3*12+:12]),
                                                     .cfg_lat_r(mss_fab_cfg_lat_r[3*12+:12]),
                                                     .cfg_wr_bw(mss_fab_cfg_wr_bw[3*10+:10]),
                                                     .cfg_rd_bw(mss_fab_cfg_rd_bw[3*10+:10]),
                                                     .perf_awf(mss_fab_perf_awf[3]),
                                                     .perf_arf(mss_fab_perf_arf[3]),
                                                     .perf_aw(mss_fab_perf_aw[3]),
                                                     .perf_ar(mss_fab_perf_ar[3]),
                                                     .perf_w(mss_fab_perf_w[3]),
                                                     .perf_wl(mss_fab_perf_wl[3]),
                                                     .perf_r(mss_fab_perf_r[3]),
                                                     .perf_rl(mss_fab_perf_rl[3]),
                                                     .perf_b(mss_fab_perf_b[3]));
    alb_mss_fab_ibp_lat #(.a_w(49),
                          .d_w(512),
                          .depl2(0)
                          ) u_npu_mst4_axi_ibp_lat_inst(
                                                     // clock and reset
                                                     .clk(mss_clk),
                                                     .clk_en(1'b1),
                                                     .rst_b(rst_b),
                                                      // Input IBP I/F

  .i_ibp_cmd_valid             (lat_i_npu_mst4_axi_ibp_cmd_valid),
  .i_ibp_cmd_accept            (lat_i_npu_mst4_axi_ibp_cmd_accept),
  .i_ibp_cmd_read              (lat_i_npu_mst4_axi_ibp_cmd_read),
  .i_ibp_cmd_addr              (lat_i_npu_mst4_axi_ibp_cmd_addr),
  .i_ibp_cmd_wrap              (lat_i_npu_mst4_axi_ibp_cmd_wrap),
  .i_ibp_cmd_data_size         (lat_i_npu_mst4_axi_ibp_cmd_data_size),
  .i_ibp_cmd_burst_size        (lat_i_npu_mst4_axi_ibp_cmd_burst_size),
  .i_ibp_cmd_prot              (lat_i_npu_mst4_axi_ibp_cmd_prot),
  .i_ibp_cmd_cache             (lat_i_npu_mst4_axi_ibp_cmd_cache),
  .i_ibp_cmd_lock              (lat_i_npu_mst4_axi_ibp_cmd_lock),
  .i_ibp_cmd_excl              (lat_i_npu_mst4_axi_ibp_cmd_excl),

  .i_ibp_rd_valid              (lat_i_npu_mst4_axi_ibp_rd_valid),
  .i_ibp_rd_excl_ok            (lat_i_npu_mst4_axi_ibp_rd_excl_ok),
  .i_ibp_rd_accept             (lat_i_npu_mst4_axi_ibp_rd_accept),
  .i_ibp_err_rd                (lat_i_npu_mst4_axi_ibp_err_rd),
  .i_ibp_rd_data               (lat_i_npu_mst4_axi_ibp_rd_data),
  .i_ibp_rd_last               (lat_i_npu_mst4_axi_ibp_rd_last),

  .i_ibp_wr_valid              (lat_i_npu_mst4_axi_ibp_wr_valid),
  .i_ibp_wr_accept             (lat_i_npu_mst4_axi_ibp_wr_accept),
  .i_ibp_wr_data               (lat_i_npu_mst4_axi_ibp_wr_data),
  .i_ibp_wr_mask               (lat_i_npu_mst4_axi_ibp_wr_mask),
  .i_ibp_wr_last               (lat_i_npu_mst4_axi_ibp_wr_last),

  .i_ibp_wr_done               (lat_i_npu_mst4_axi_ibp_wr_done),
  .i_ibp_wr_excl_done          (lat_i_npu_mst4_axi_ibp_wr_excl_done),
  .i_ibp_err_wr                (lat_i_npu_mst4_axi_ibp_err_wr),
  .i_ibp_wr_resp_accept        (lat_i_npu_mst4_axi_ibp_wr_resp_accept),
                                                     // Output IBP I/F

  .o_ibp_cmd_valid             (lat_o_npu_mst4_axi_ibp_cmd_valid),
  .o_ibp_cmd_accept            (lat_o_npu_mst4_axi_ibp_cmd_accept),
  .o_ibp_cmd_read              (lat_o_npu_mst4_axi_ibp_cmd_read),
  .o_ibp_cmd_addr              (lat_o_npu_mst4_axi_ibp_cmd_addr),
  .o_ibp_cmd_wrap              (lat_o_npu_mst4_axi_ibp_cmd_wrap),
  .o_ibp_cmd_data_size         (lat_o_npu_mst4_axi_ibp_cmd_data_size),
  .o_ibp_cmd_burst_size        (lat_o_npu_mst4_axi_ibp_cmd_burst_size),
  .o_ibp_cmd_prot              (lat_o_npu_mst4_axi_ibp_cmd_prot),
  .o_ibp_cmd_cache             (lat_o_npu_mst4_axi_ibp_cmd_cache),
  .o_ibp_cmd_lock              (lat_o_npu_mst4_axi_ibp_cmd_lock),
  .o_ibp_cmd_excl              (lat_o_npu_mst4_axi_ibp_cmd_excl),

  .o_ibp_rd_valid              (lat_o_npu_mst4_axi_ibp_rd_valid),
  .o_ibp_rd_excl_ok            (lat_o_npu_mst4_axi_ibp_rd_excl_ok),
  .o_ibp_rd_accept             (lat_o_npu_mst4_axi_ibp_rd_accept),
  .o_ibp_err_rd                (lat_o_npu_mst4_axi_ibp_err_rd),
  .o_ibp_rd_data               (lat_o_npu_mst4_axi_ibp_rd_data),
  .o_ibp_rd_last               (lat_o_npu_mst4_axi_ibp_rd_last),

  .o_ibp_wr_valid              (lat_o_npu_mst4_axi_ibp_wr_valid),
  .o_ibp_wr_accept             (lat_o_npu_mst4_axi_ibp_wr_accept),
  .o_ibp_wr_data               (lat_o_npu_mst4_axi_ibp_wr_data),
  .o_ibp_wr_mask               (lat_o_npu_mst4_axi_ibp_wr_mask),
  .o_ibp_wr_last               (lat_o_npu_mst4_axi_ibp_wr_last),

  .o_ibp_wr_done               (lat_o_npu_mst4_axi_ibp_wr_done),
  .o_ibp_wr_excl_done          (lat_o_npu_mst4_axi_ibp_wr_excl_done),
  .o_ibp_err_wr                (lat_o_npu_mst4_axi_ibp_err_wr),
  .o_ibp_wr_resp_accept        (lat_o_npu_mst4_axi_ibp_wr_resp_accept),
                                                      // Profiler I/F
                                                     .cfg_lat_w(mss_fab_cfg_lat_w[4*12+:12]),
                                                     .cfg_lat_r(mss_fab_cfg_lat_r[4*12+:12]),
                                                     .cfg_wr_bw(mss_fab_cfg_wr_bw[4*10+:10]),
                                                     .cfg_rd_bw(mss_fab_cfg_rd_bw[4*10+:10]),
                                                     .perf_awf(mss_fab_perf_awf[4]),
                                                     .perf_arf(mss_fab_perf_arf[4]),
                                                     .perf_aw(mss_fab_perf_aw[4]),
                                                     .perf_ar(mss_fab_perf_ar[4]),
                                                     .perf_w(mss_fab_perf_w[4]),
                                                     .perf_wl(mss_fab_perf_wl[4]),
                                                     .perf_r(mss_fab_perf_r[4]),
                                                     .perf_rl(mss_fab_perf_rl[4]),
                                                     .perf_b(mss_fab_perf_b[4]));
    alb_mss_fab_ibp_lat #(.a_w(49),
                          .d_w(64),
                          .depl2(0)
                          ) u_host_axi_ibp_lat_inst(
                                                     // clock and reset
                                                     .clk(mss_clk),
                                                     .clk_en(1'b1),
                                                     .rst_b(rst_b),
                                                      // Input IBP I/F

  .i_ibp_cmd_valid             (lat_i_host_axi_ibp_cmd_valid),
  .i_ibp_cmd_accept            (lat_i_host_axi_ibp_cmd_accept),
  .i_ibp_cmd_read              (lat_i_host_axi_ibp_cmd_read),
  .i_ibp_cmd_addr              (lat_i_host_axi_ibp_cmd_addr),
  .i_ibp_cmd_wrap              (lat_i_host_axi_ibp_cmd_wrap),
  .i_ibp_cmd_data_size         (lat_i_host_axi_ibp_cmd_data_size),
  .i_ibp_cmd_burst_size        (lat_i_host_axi_ibp_cmd_burst_size),
  .i_ibp_cmd_prot              (lat_i_host_axi_ibp_cmd_prot),
  .i_ibp_cmd_cache             (lat_i_host_axi_ibp_cmd_cache),
  .i_ibp_cmd_lock              (lat_i_host_axi_ibp_cmd_lock),
  .i_ibp_cmd_excl              (lat_i_host_axi_ibp_cmd_excl),

  .i_ibp_rd_valid              (lat_i_host_axi_ibp_rd_valid),
  .i_ibp_rd_excl_ok            (lat_i_host_axi_ibp_rd_excl_ok),
  .i_ibp_rd_accept             (lat_i_host_axi_ibp_rd_accept),
  .i_ibp_err_rd                (lat_i_host_axi_ibp_err_rd),
  .i_ibp_rd_data               (lat_i_host_axi_ibp_rd_data),
  .i_ibp_rd_last               (lat_i_host_axi_ibp_rd_last),

  .i_ibp_wr_valid              (lat_i_host_axi_ibp_wr_valid),
  .i_ibp_wr_accept             (lat_i_host_axi_ibp_wr_accept),
  .i_ibp_wr_data               (lat_i_host_axi_ibp_wr_data),
  .i_ibp_wr_mask               (lat_i_host_axi_ibp_wr_mask),
  .i_ibp_wr_last               (lat_i_host_axi_ibp_wr_last),

  .i_ibp_wr_done               (lat_i_host_axi_ibp_wr_done),
  .i_ibp_wr_excl_done          (lat_i_host_axi_ibp_wr_excl_done),
  .i_ibp_err_wr                (lat_i_host_axi_ibp_err_wr),
  .i_ibp_wr_resp_accept        (lat_i_host_axi_ibp_wr_resp_accept),
                                                     // Output IBP I/F

  .o_ibp_cmd_valid             (lat_o_host_axi_ibp_cmd_valid),
  .o_ibp_cmd_accept            (lat_o_host_axi_ibp_cmd_accept),
  .o_ibp_cmd_read              (lat_o_host_axi_ibp_cmd_read),
  .o_ibp_cmd_addr              (lat_o_host_axi_ibp_cmd_addr),
  .o_ibp_cmd_wrap              (lat_o_host_axi_ibp_cmd_wrap),
  .o_ibp_cmd_data_size         (lat_o_host_axi_ibp_cmd_data_size),
  .o_ibp_cmd_burst_size        (lat_o_host_axi_ibp_cmd_burst_size),
  .o_ibp_cmd_prot              (lat_o_host_axi_ibp_cmd_prot),
  .o_ibp_cmd_cache             (lat_o_host_axi_ibp_cmd_cache),
  .o_ibp_cmd_lock              (lat_o_host_axi_ibp_cmd_lock),
  .o_ibp_cmd_excl              (lat_o_host_axi_ibp_cmd_excl),

  .o_ibp_rd_valid              (lat_o_host_axi_ibp_rd_valid),
  .o_ibp_rd_excl_ok            (lat_o_host_axi_ibp_rd_excl_ok),
  .o_ibp_rd_accept             (lat_o_host_axi_ibp_rd_accept),
  .o_ibp_err_rd                (lat_o_host_axi_ibp_err_rd),
  .o_ibp_rd_data               (lat_o_host_axi_ibp_rd_data),
  .o_ibp_rd_last               (lat_o_host_axi_ibp_rd_last),

  .o_ibp_wr_valid              (lat_o_host_axi_ibp_wr_valid),
  .o_ibp_wr_accept             (lat_o_host_axi_ibp_wr_accept),
  .o_ibp_wr_data               (lat_o_host_axi_ibp_wr_data),
  .o_ibp_wr_mask               (lat_o_host_axi_ibp_wr_mask),
  .o_ibp_wr_last               (lat_o_host_axi_ibp_wr_last),

  .o_ibp_wr_done               (lat_o_host_axi_ibp_wr_done),
  .o_ibp_wr_excl_done          (lat_o_host_axi_ibp_wr_excl_done),
  .o_ibp_err_wr                (lat_o_host_axi_ibp_err_wr),
  .o_ibp_wr_resp_accept        (lat_o_host_axi_ibp_wr_resp_accept),
                                                      // Profiler I/F
                                                     .cfg_lat_w(mss_fab_cfg_lat_w[5*12+:12]),
                                                     .cfg_lat_r(mss_fab_cfg_lat_r[5*12+:12]),
                                                     .cfg_wr_bw(mss_fab_cfg_wr_bw[5*10+:10]),
                                                     .cfg_rd_bw(mss_fab_cfg_rd_bw[5*10+:10]),
                                                     .perf_awf(mss_fab_perf_awf[5]),
                                                     .perf_arf(mss_fab_perf_arf[5]),
                                                     .perf_aw(mss_fab_perf_aw[5]),
                                                     .perf_ar(mss_fab_perf_ar[5]),
                                                     .perf_w(mss_fab_perf_w[5]),
                                                     .perf_wl(mss_fab_perf_wl[5]),
                                                     .perf_r(mss_fab_perf_r[5]),
                                                     .perf_rl(mss_fab_perf_rl[5]),
                                                     .perf_b(mss_fab_perf_b[5]));
    alb_mss_fab_ibp_lat #(.a_w(49),
                          .d_w(32),
                          .depl2(0)
                          ) u_bri4tb_ibp_lat_inst(
                                                     // clock and reset
                                                     .clk(mss_clk),
                                                     .clk_en(1'b1),
                                                     .rst_b(rst_b),
                                                      // Input IBP I/F

  .i_ibp_cmd_valid             (lat_i_bri4tb_ibp_cmd_valid),
  .i_ibp_cmd_accept            (lat_i_bri4tb_ibp_cmd_accept),
  .i_ibp_cmd_read              (lat_i_bri4tb_ibp_cmd_read),
  .i_ibp_cmd_addr              (lat_i_bri4tb_ibp_cmd_addr),
  .i_ibp_cmd_wrap              (lat_i_bri4tb_ibp_cmd_wrap),
  .i_ibp_cmd_data_size         (lat_i_bri4tb_ibp_cmd_data_size),
  .i_ibp_cmd_burst_size        (lat_i_bri4tb_ibp_cmd_burst_size),
  .i_ibp_cmd_prot              (lat_i_bri4tb_ibp_cmd_prot),
  .i_ibp_cmd_cache             (lat_i_bri4tb_ibp_cmd_cache),
  .i_ibp_cmd_lock              (lat_i_bri4tb_ibp_cmd_lock),
  .i_ibp_cmd_excl              (lat_i_bri4tb_ibp_cmd_excl),

  .i_ibp_rd_valid              (lat_i_bri4tb_ibp_rd_valid),
  .i_ibp_rd_excl_ok            (lat_i_bri4tb_ibp_rd_excl_ok),
  .i_ibp_rd_accept             (lat_i_bri4tb_ibp_rd_accept),
  .i_ibp_err_rd                (lat_i_bri4tb_ibp_err_rd),
  .i_ibp_rd_data               (lat_i_bri4tb_ibp_rd_data),
  .i_ibp_rd_last               (lat_i_bri4tb_ibp_rd_last),

  .i_ibp_wr_valid              (lat_i_bri4tb_ibp_wr_valid),
  .i_ibp_wr_accept             (lat_i_bri4tb_ibp_wr_accept),
  .i_ibp_wr_data               (lat_i_bri4tb_ibp_wr_data),
  .i_ibp_wr_mask               (lat_i_bri4tb_ibp_wr_mask),
  .i_ibp_wr_last               (lat_i_bri4tb_ibp_wr_last),

  .i_ibp_wr_done               (lat_i_bri4tb_ibp_wr_done),
  .i_ibp_wr_excl_done          (lat_i_bri4tb_ibp_wr_excl_done),
  .i_ibp_err_wr                (lat_i_bri4tb_ibp_err_wr),
  .i_ibp_wr_resp_accept        (lat_i_bri4tb_ibp_wr_resp_accept),
                                                     // Output IBP I/F

  .o_ibp_cmd_valid             (lat_o_bri4tb_ibp_cmd_valid),
  .o_ibp_cmd_accept            (lat_o_bri4tb_ibp_cmd_accept),
  .o_ibp_cmd_read              (lat_o_bri4tb_ibp_cmd_read),
  .o_ibp_cmd_addr              (lat_o_bri4tb_ibp_cmd_addr),
  .o_ibp_cmd_wrap              (lat_o_bri4tb_ibp_cmd_wrap),
  .o_ibp_cmd_data_size         (lat_o_bri4tb_ibp_cmd_data_size),
  .o_ibp_cmd_burst_size        (lat_o_bri4tb_ibp_cmd_burst_size),
  .o_ibp_cmd_prot              (lat_o_bri4tb_ibp_cmd_prot),
  .o_ibp_cmd_cache             (lat_o_bri4tb_ibp_cmd_cache),
  .o_ibp_cmd_lock              (lat_o_bri4tb_ibp_cmd_lock),
  .o_ibp_cmd_excl              (lat_o_bri4tb_ibp_cmd_excl),

  .o_ibp_rd_valid              (lat_o_bri4tb_ibp_rd_valid),
  .o_ibp_rd_excl_ok            (lat_o_bri4tb_ibp_rd_excl_ok),
  .o_ibp_rd_accept             (lat_o_bri4tb_ibp_rd_accept),
  .o_ibp_err_rd                (lat_o_bri4tb_ibp_err_rd),
  .o_ibp_rd_data               (lat_o_bri4tb_ibp_rd_data),
  .o_ibp_rd_last               (lat_o_bri4tb_ibp_rd_last),

  .o_ibp_wr_valid              (lat_o_bri4tb_ibp_wr_valid),
  .o_ibp_wr_accept             (lat_o_bri4tb_ibp_wr_accept),
  .o_ibp_wr_data               (lat_o_bri4tb_ibp_wr_data),
  .o_ibp_wr_mask               (lat_o_bri4tb_ibp_wr_mask),
  .o_ibp_wr_last               (lat_o_bri4tb_ibp_wr_last),

  .o_ibp_wr_done               (lat_o_bri4tb_ibp_wr_done),
  .o_ibp_wr_excl_done          (lat_o_bri4tb_ibp_wr_excl_done),
  .o_ibp_err_wr                (lat_o_bri4tb_ibp_err_wr),
  .o_ibp_wr_resp_accept        (lat_o_bri4tb_ibp_wr_resp_accept),
                                                      // Profiler I/F
                                                     .cfg_lat_w(mss_fab_cfg_lat_w[6*12+:12]),
                                                     .cfg_lat_r(mss_fab_cfg_lat_r[6*12+:12]),
                                                     .cfg_wr_bw(mss_fab_cfg_wr_bw[6*10+:10]),
                                                     .cfg_rd_bw(mss_fab_cfg_rd_bw[6*10+:10]),
                                                     .perf_awf(mss_fab_perf_awf[6]),
                                                     .perf_arf(mss_fab_perf_arf[6]),
                                                     .perf_aw(mss_fab_perf_aw[6]),
                                                     .perf_ar(mss_fab_perf_ar[6]),
                                                     .perf_w(mss_fab_perf_w[6]),
                                                     .perf_wl(mss_fab_perf_wl[6]),
                                                     .perf_r(mss_fab_perf_r[6]),
                                                     .perf_rl(mss_fab_perf_rl[6]),
                                                     .perf_b(mss_fab_perf_b[6]));

    // Bus switch
    // all master and slave ports are aligned to system space
    alb_mss_bus_switch u_switch_inst(
                                                   // master side
                                                   .npu_mst0_axi_bs_ibp_cmd_valid(lat_o_npu_mst0_axi_ibp_cmd_valid),
                                                   .npu_mst0_axi_bs_ibp_cmd_accept(lat_o_npu_mst0_axi_ibp_cmd_accept),
                                                   .npu_mst0_axi_bs_ibp_cmd_read(lat_o_npu_mst0_axi_ibp_cmd_read),
                                                   .npu_mst0_axi_bs_ibp_cmd_addr(lat_o_npu_mst0_axi_ibp_cmd_addr),
                                                   .npu_mst0_axi_bs_ibp_cmd_wrap(lat_o_npu_mst0_axi_ibp_cmd_wrap),
                                                   .npu_mst0_axi_bs_ibp_cmd_data_size(lat_o_npu_mst0_axi_ibp_cmd_data_size),
                                                   .npu_mst0_axi_bs_ibp_cmd_burst_size(lat_o_npu_mst0_axi_ibp_cmd_burst_size),
                                                   .npu_mst0_axi_bs_ibp_cmd_lock(lat_o_npu_mst0_axi_ibp_cmd_lock),
                                                   .npu_mst0_axi_bs_ibp_cmd_excl(lat_o_npu_mst0_axi_ibp_cmd_excl),
                                                   .npu_mst0_axi_bs_ibp_cmd_prot(lat_o_npu_mst0_axi_ibp_cmd_prot),
                                                   .npu_mst0_axi_bs_ibp_cmd_cache(lat_o_npu_mst0_axi_ibp_cmd_cache),
                                                   .npu_mst0_axi_bs_ibp_rd_valid(lat_o_npu_mst0_axi_ibp_rd_valid),
                                                   .npu_mst0_axi_bs_ibp_rd_accept(lat_o_npu_mst0_axi_ibp_rd_accept),
                                                   .npu_mst0_axi_bs_ibp_rd_data(lat_o_npu_mst0_axi_ibp_rd_data),
                                                   .npu_mst0_axi_bs_ibp_rd_last(lat_o_npu_mst0_axi_ibp_rd_last),
                                                   .npu_mst0_axi_bs_ibp_err_rd(lat_o_npu_mst0_axi_ibp_err_rd),
                                                   .npu_mst0_axi_bs_ibp_rd_excl_ok(lat_o_npu_mst0_axi_ibp_rd_excl_ok),
                                                   .npu_mst0_axi_bs_ibp_wr_valid(lat_o_npu_mst0_axi_ibp_wr_valid),
                                                   .npu_mst0_axi_bs_ibp_wr_accept(lat_o_npu_mst0_axi_ibp_wr_accept),
                                                   .npu_mst0_axi_bs_ibp_wr_data(lat_o_npu_mst0_axi_ibp_wr_data),
                                                   .npu_mst0_axi_bs_ibp_wr_mask(lat_o_npu_mst0_axi_ibp_wr_mask),
                                                   .npu_mst0_axi_bs_ibp_wr_last(lat_o_npu_mst0_axi_ibp_wr_last),
                                                   .npu_mst0_axi_bs_ibp_wr_done(lat_o_npu_mst0_axi_ibp_wr_done),
                                                   .npu_mst0_axi_bs_ibp_wr_excl_done(lat_o_npu_mst0_axi_ibp_wr_excl_done),
                                                   .npu_mst0_axi_bs_ibp_err_wr(lat_o_npu_mst0_axi_ibp_err_wr),
                                                   .npu_mst0_axi_bs_ibp_wr_resp_accept(lat_o_npu_mst0_axi_ibp_wr_resp_accept),

                                                   .npu_mst1_axi_bs_ibp_cmd_valid(lat_o_npu_mst1_axi_ibp_cmd_valid),
                                                   .npu_mst1_axi_bs_ibp_cmd_accept(lat_o_npu_mst1_axi_ibp_cmd_accept),
                                                   .npu_mst1_axi_bs_ibp_cmd_read(lat_o_npu_mst1_axi_ibp_cmd_read),
                                                   .npu_mst1_axi_bs_ibp_cmd_addr(lat_o_npu_mst1_axi_ibp_cmd_addr),
                                                   .npu_mst1_axi_bs_ibp_cmd_wrap(lat_o_npu_mst1_axi_ibp_cmd_wrap),
                                                   .npu_mst1_axi_bs_ibp_cmd_data_size(lat_o_npu_mst1_axi_ibp_cmd_data_size),
                                                   .npu_mst1_axi_bs_ibp_cmd_burst_size(lat_o_npu_mst1_axi_ibp_cmd_burst_size),
                                                   .npu_mst1_axi_bs_ibp_cmd_lock(lat_o_npu_mst1_axi_ibp_cmd_lock),
                                                   .npu_mst1_axi_bs_ibp_cmd_excl(lat_o_npu_mst1_axi_ibp_cmd_excl),
                                                   .npu_mst1_axi_bs_ibp_cmd_prot(lat_o_npu_mst1_axi_ibp_cmd_prot),
                                                   .npu_mst1_axi_bs_ibp_cmd_cache(lat_o_npu_mst1_axi_ibp_cmd_cache),
                                                   .npu_mst1_axi_bs_ibp_rd_valid(lat_o_npu_mst1_axi_ibp_rd_valid),
                                                   .npu_mst1_axi_bs_ibp_rd_accept(lat_o_npu_mst1_axi_ibp_rd_accept),
                                                   .npu_mst1_axi_bs_ibp_rd_data(lat_o_npu_mst1_axi_ibp_rd_data),
                                                   .npu_mst1_axi_bs_ibp_rd_last(lat_o_npu_mst1_axi_ibp_rd_last),
                                                   .npu_mst1_axi_bs_ibp_err_rd(lat_o_npu_mst1_axi_ibp_err_rd),
                                                   .npu_mst1_axi_bs_ibp_rd_excl_ok(lat_o_npu_mst1_axi_ibp_rd_excl_ok),
                                                   .npu_mst1_axi_bs_ibp_wr_valid(lat_o_npu_mst1_axi_ibp_wr_valid),
                                                   .npu_mst1_axi_bs_ibp_wr_accept(lat_o_npu_mst1_axi_ibp_wr_accept),
                                                   .npu_mst1_axi_bs_ibp_wr_data(lat_o_npu_mst1_axi_ibp_wr_data),
                                                   .npu_mst1_axi_bs_ibp_wr_mask(lat_o_npu_mst1_axi_ibp_wr_mask),
                                                   .npu_mst1_axi_bs_ibp_wr_last(lat_o_npu_mst1_axi_ibp_wr_last),
                                                   .npu_mst1_axi_bs_ibp_wr_done(lat_o_npu_mst1_axi_ibp_wr_done),
                                                   .npu_mst1_axi_bs_ibp_wr_excl_done(lat_o_npu_mst1_axi_ibp_wr_excl_done),
                                                   .npu_mst1_axi_bs_ibp_err_wr(lat_o_npu_mst1_axi_ibp_err_wr),
                                                   .npu_mst1_axi_bs_ibp_wr_resp_accept(lat_o_npu_mst1_axi_ibp_wr_resp_accept),

                                                   .npu_mst2_axi_bs_ibp_cmd_valid(lat_o_npu_mst2_axi_ibp_cmd_valid),
                                                   .npu_mst2_axi_bs_ibp_cmd_accept(lat_o_npu_mst2_axi_ibp_cmd_accept),
                                                   .npu_mst2_axi_bs_ibp_cmd_read(lat_o_npu_mst2_axi_ibp_cmd_read),
                                                   .npu_mst2_axi_bs_ibp_cmd_addr(lat_o_npu_mst2_axi_ibp_cmd_addr),
                                                   .npu_mst2_axi_bs_ibp_cmd_wrap(lat_o_npu_mst2_axi_ibp_cmd_wrap),
                                                   .npu_mst2_axi_bs_ibp_cmd_data_size(lat_o_npu_mst2_axi_ibp_cmd_data_size),
                                                   .npu_mst2_axi_bs_ibp_cmd_burst_size(lat_o_npu_mst2_axi_ibp_cmd_burst_size),
                                                   .npu_mst2_axi_bs_ibp_cmd_lock(lat_o_npu_mst2_axi_ibp_cmd_lock),
                                                   .npu_mst2_axi_bs_ibp_cmd_excl(lat_o_npu_mst2_axi_ibp_cmd_excl),
                                                   .npu_mst2_axi_bs_ibp_cmd_prot(lat_o_npu_mst2_axi_ibp_cmd_prot),
                                                   .npu_mst2_axi_bs_ibp_cmd_cache(lat_o_npu_mst2_axi_ibp_cmd_cache),
                                                   .npu_mst2_axi_bs_ibp_rd_valid(lat_o_npu_mst2_axi_ibp_rd_valid),
                                                   .npu_mst2_axi_bs_ibp_rd_accept(lat_o_npu_mst2_axi_ibp_rd_accept),
                                                   .npu_mst2_axi_bs_ibp_rd_data(lat_o_npu_mst2_axi_ibp_rd_data),
                                                   .npu_mst2_axi_bs_ibp_rd_last(lat_o_npu_mst2_axi_ibp_rd_last),
                                                   .npu_mst2_axi_bs_ibp_err_rd(lat_o_npu_mst2_axi_ibp_err_rd),
                                                   .npu_mst2_axi_bs_ibp_rd_excl_ok(lat_o_npu_mst2_axi_ibp_rd_excl_ok),
                                                   .npu_mst2_axi_bs_ibp_wr_valid(lat_o_npu_mst2_axi_ibp_wr_valid),
                                                   .npu_mst2_axi_bs_ibp_wr_accept(lat_o_npu_mst2_axi_ibp_wr_accept),
                                                   .npu_mst2_axi_bs_ibp_wr_data(lat_o_npu_mst2_axi_ibp_wr_data),
                                                   .npu_mst2_axi_bs_ibp_wr_mask(lat_o_npu_mst2_axi_ibp_wr_mask),
                                                   .npu_mst2_axi_bs_ibp_wr_last(lat_o_npu_mst2_axi_ibp_wr_last),
                                                   .npu_mst2_axi_bs_ibp_wr_done(lat_o_npu_mst2_axi_ibp_wr_done),
                                                   .npu_mst2_axi_bs_ibp_wr_excl_done(lat_o_npu_mst2_axi_ibp_wr_excl_done),
                                                   .npu_mst2_axi_bs_ibp_err_wr(lat_o_npu_mst2_axi_ibp_err_wr),
                                                   .npu_mst2_axi_bs_ibp_wr_resp_accept(lat_o_npu_mst2_axi_ibp_wr_resp_accept),

                                                   .npu_mst3_axi_bs_ibp_cmd_valid(lat_o_npu_mst3_axi_ibp_cmd_valid),
                                                   .npu_mst3_axi_bs_ibp_cmd_accept(lat_o_npu_mst3_axi_ibp_cmd_accept),
                                                   .npu_mst3_axi_bs_ibp_cmd_read(lat_o_npu_mst3_axi_ibp_cmd_read),
                                                   .npu_mst3_axi_bs_ibp_cmd_addr(lat_o_npu_mst3_axi_ibp_cmd_addr),
                                                   .npu_mst3_axi_bs_ibp_cmd_wrap(lat_o_npu_mst3_axi_ibp_cmd_wrap),
                                                   .npu_mst3_axi_bs_ibp_cmd_data_size(lat_o_npu_mst3_axi_ibp_cmd_data_size),
                                                   .npu_mst3_axi_bs_ibp_cmd_burst_size(lat_o_npu_mst3_axi_ibp_cmd_burst_size),
                                                   .npu_mst3_axi_bs_ibp_cmd_lock(lat_o_npu_mst3_axi_ibp_cmd_lock),
                                                   .npu_mst3_axi_bs_ibp_cmd_excl(lat_o_npu_mst3_axi_ibp_cmd_excl),
                                                   .npu_mst3_axi_bs_ibp_cmd_prot(lat_o_npu_mst3_axi_ibp_cmd_prot),
                                                   .npu_mst3_axi_bs_ibp_cmd_cache(lat_o_npu_mst3_axi_ibp_cmd_cache),
                                                   .npu_mst3_axi_bs_ibp_rd_valid(lat_o_npu_mst3_axi_ibp_rd_valid),
                                                   .npu_mst3_axi_bs_ibp_rd_accept(lat_o_npu_mst3_axi_ibp_rd_accept),
                                                   .npu_mst3_axi_bs_ibp_rd_data(lat_o_npu_mst3_axi_ibp_rd_data),
                                                   .npu_mst3_axi_bs_ibp_rd_last(lat_o_npu_mst3_axi_ibp_rd_last),
                                                   .npu_mst3_axi_bs_ibp_err_rd(lat_o_npu_mst3_axi_ibp_err_rd),
                                                   .npu_mst3_axi_bs_ibp_rd_excl_ok(lat_o_npu_mst3_axi_ibp_rd_excl_ok),
                                                   .npu_mst3_axi_bs_ibp_wr_valid(lat_o_npu_mst3_axi_ibp_wr_valid),
                                                   .npu_mst3_axi_bs_ibp_wr_accept(lat_o_npu_mst3_axi_ibp_wr_accept),
                                                   .npu_mst3_axi_bs_ibp_wr_data(lat_o_npu_mst3_axi_ibp_wr_data),
                                                   .npu_mst3_axi_bs_ibp_wr_mask(lat_o_npu_mst3_axi_ibp_wr_mask),
                                                   .npu_mst3_axi_bs_ibp_wr_last(lat_o_npu_mst3_axi_ibp_wr_last),
                                                   .npu_mst3_axi_bs_ibp_wr_done(lat_o_npu_mst3_axi_ibp_wr_done),
                                                   .npu_mst3_axi_bs_ibp_wr_excl_done(lat_o_npu_mst3_axi_ibp_wr_excl_done),
                                                   .npu_mst3_axi_bs_ibp_err_wr(lat_o_npu_mst3_axi_ibp_err_wr),
                                                   .npu_mst3_axi_bs_ibp_wr_resp_accept(lat_o_npu_mst3_axi_ibp_wr_resp_accept),

                                                   .npu_mst4_axi_bs_ibp_cmd_valid(lat_o_npu_mst4_axi_ibp_cmd_valid),
                                                   .npu_mst4_axi_bs_ibp_cmd_accept(lat_o_npu_mst4_axi_ibp_cmd_accept),
                                                   .npu_mst4_axi_bs_ibp_cmd_read(lat_o_npu_mst4_axi_ibp_cmd_read),
                                                   .npu_mst4_axi_bs_ibp_cmd_addr(lat_o_npu_mst4_axi_ibp_cmd_addr),
                                                   .npu_mst4_axi_bs_ibp_cmd_wrap(lat_o_npu_mst4_axi_ibp_cmd_wrap),
                                                   .npu_mst4_axi_bs_ibp_cmd_data_size(lat_o_npu_mst4_axi_ibp_cmd_data_size),
                                                   .npu_mst4_axi_bs_ibp_cmd_burst_size(lat_o_npu_mst4_axi_ibp_cmd_burst_size),
                                                   .npu_mst4_axi_bs_ibp_cmd_lock(lat_o_npu_mst4_axi_ibp_cmd_lock),
                                                   .npu_mst4_axi_bs_ibp_cmd_excl(lat_o_npu_mst4_axi_ibp_cmd_excl),
                                                   .npu_mst4_axi_bs_ibp_cmd_prot(lat_o_npu_mst4_axi_ibp_cmd_prot),
                                                   .npu_mst4_axi_bs_ibp_cmd_cache(lat_o_npu_mst4_axi_ibp_cmd_cache),
                                                   .npu_mst4_axi_bs_ibp_rd_valid(lat_o_npu_mst4_axi_ibp_rd_valid),
                                                   .npu_mst4_axi_bs_ibp_rd_accept(lat_o_npu_mst4_axi_ibp_rd_accept),
                                                   .npu_mst4_axi_bs_ibp_rd_data(lat_o_npu_mst4_axi_ibp_rd_data),
                                                   .npu_mst4_axi_bs_ibp_rd_last(lat_o_npu_mst4_axi_ibp_rd_last),
                                                   .npu_mst4_axi_bs_ibp_err_rd(lat_o_npu_mst4_axi_ibp_err_rd),
                                                   .npu_mst4_axi_bs_ibp_rd_excl_ok(lat_o_npu_mst4_axi_ibp_rd_excl_ok),
                                                   .npu_mst4_axi_bs_ibp_wr_valid(lat_o_npu_mst4_axi_ibp_wr_valid),
                                                   .npu_mst4_axi_bs_ibp_wr_accept(lat_o_npu_mst4_axi_ibp_wr_accept),
                                                   .npu_mst4_axi_bs_ibp_wr_data(lat_o_npu_mst4_axi_ibp_wr_data),
                                                   .npu_mst4_axi_bs_ibp_wr_mask(lat_o_npu_mst4_axi_ibp_wr_mask),
                                                   .npu_mst4_axi_bs_ibp_wr_last(lat_o_npu_mst4_axi_ibp_wr_last),
                                                   .npu_mst4_axi_bs_ibp_wr_done(lat_o_npu_mst4_axi_ibp_wr_done),
                                                   .npu_mst4_axi_bs_ibp_wr_excl_done(lat_o_npu_mst4_axi_ibp_wr_excl_done),
                                                   .npu_mst4_axi_bs_ibp_err_wr(lat_o_npu_mst4_axi_ibp_err_wr),
                                                   .npu_mst4_axi_bs_ibp_wr_resp_accept(lat_o_npu_mst4_axi_ibp_wr_resp_accept),

                                                   .host_axi_bs_ibp_cmd_valid(lat_o_host_axi_ibp_cmd_valid),
                                                   .host_axi_bs_ibp_cmd_accept(lat_o_host_axi_ibp_cmd_accept),
                                                   .host_axi_bs_ibp_cmd_read(lat_o_host_axi_ibp_cmd_read),
                                                   .host_axi_bs_ibp_cmd_addr(lat_o_host_axi_ibp_cmd_addr),
                                                   .host_axi_bs_ibp_cmd_wrap(lat_o_host_axi_ibp_cmd_wrap),
                                                   .host_axi_bs_ibp_cmd_data_size(lat_o_host_axi_ibp_cmd_data_size),
                                                   .host_axi_bs_ibp_cmd_burst_size(lat_o_host_axi_ibp_cmd_burst_size),
                                                   .host_axi_bs_ibp_cmd_lock(lat_o_host_axi_ibp_cmd_lock),
                                                   .host_axi_bs_ibp_cmd_excl(lat_o_host_axi_ibp_cmd_excl),
                                                   .host_axi_bs_ibp_cmd_prot(lat_o_host_axi_ibp_cmd_prot),
                                                   .host_axi_bs_ibp_cmd_cache(lat_o_host_axi_ibp_cmd_cache),
                                                   .host_axi_bs_ibp_rd_valid(lat_o_host_axi_ibp_rd_valid),
                                                   .host_axi_bs_ibp_rd_accept(lat_o_host_axi_ibp_rd_accept),
                                                   .host_axi_bs_ibp_rd_data(lat_o_host_axi_ibp_rd_data),
                                                   .host_axi_bs_ibp_rd_last(lat_o_host_axi_ibp_rd_last),
                                                   .host_axi_bs_ibp_err_rd(lat_o_host_axi_ibp_err_rd),
                                                   .host_axi_bs_ibp_rd_excl_ok(lat_o_host_axi_ibp_rd_excl_ok),
                                                   .host_axi_bs_ibp_wr_valid(lat_o_host_axi_ibp_wr_valid),
                                                   .host_axi_bs_ibp_wr_accept(lat_o_host_axi_ibp_wr_accept),
                                                   .host_axi_bs_ibp_wr_data(lat_o_host_axi_ibp_wr_data),
                                                   .host_axi_bs_ibp_wr_mask(lat_o_host_axi_ibp_wr_mask),
                                                   .host_axi_bs_ibp_wr_last(lat_o_host_axi_ibp_wr_last),
                                                   .host_axi_bs_ibp_wr_done(lat_o_host_axi_ibp_wr_done),
                                                   .host_axi_bs_ibp_wr_excl_done(lat_o_host_axi_ibp_wr_excl_done),
                                                   .host_axi_bs_ibp_err_wr(lat_o_host_axi_ibp_err_wr),
                                                   .host_axi_bs_ibp_wr_resp_accept(lat_o_host_axi_ibp_wr_resp_accept),

                                                   .bri4tb_bs_ibp_cmd_valid(lat_o_bri4tb_ibp_cmd_valid),
                                                   .bri4tb_bs_ibp_cmd_accept(lat_o_bri4tb_ibp_cmd_accept),
                                                   .bri4tb_bs_ibp_cmd_read(lat_o_bri4tb_ibp_cmd_read),
                                                   .bri4tb_bs_ibp_cmd_addr(lat_o_bri4tb_ibp_cmd_addr),
                                                   .bri4tb_bs_ibp_cmd_wrap(lat_o_bri4tb_ibp_cmd_wrap),
                                                   .bri4tb_bs_ibp_cmd_data_size(lat_o_bri4tb_ibp_cmd_data_size),
                                                   .bri4tb_bs_ibp_cmd_burst_size(lat_o_bri4tb_ibp_cmd_burst_size),
                                                   .bri4tb_bs_ibp_cmd_lock(lat_o_bri4tb_ibp_cmd_lock),
                                                   .bri4tb_bs_ibp_cmd_excl(lat_o_bri4tb_ibp_cmd_excl),
                                                   .bri4tb_bs_ibp_cmd_prot(lat_o_bri4tb_ibp_cmd_prot),
                                                   .bri4tb_bs_ibp_cmd_cache(lat_o_bri4tb_ibp_cmd_cache),
                                                   .bri4tb_bs_ibp_rd_valid(lat_o_bri4tb_ibp_rd_valid),
                                                   .bri4tb_bs_ibp_rd_accept(lat_o_bri4tb_ibp_rd_accept),
                                                   .bri4tb_bs_ibp_rd_data(lat_o_bri4tb_ibp_rd_data),
                                                   .bri4tb_bs_ibp_rd_last(lat_o_bri4tb_ibp_rd_last),
                                                   .bri4tb_bs_ibp_err_rd(lat_o_bri4tb_ibp_err_rd),
                                                   .bri4tb_bs_ibp_rd_excl_ok(lat_o_bri4tb_ibp_rd_excl_ok),
                                                   .bri4tb_bs_ibp_wr_valid(lat_o_bri4tb_ibp_wr_valid),
                                                   .bri4tb_bs_ibp_wr_accept(lat_o_bri4tb_ibp_wr_accept),
                                                   .bri4tb_bs_ibp_wr_data(lat_o_bri4tb_ibp_wr_data),
                                                   .bri4tb_bs_ibp_wr_mask(lat_o_bri4tb_ibp_wr_mask),
                                                   .bri4tb_bs_ibp_wr_last(lat_o_bri4tb_ibp_wr_last),
                                                   .bri4tb_bs_ibp_wr_done(lat_o_bri4tb_ibp_wr_done),
                                                   .bri4tb_bs_ibp_wr_excl_done(lat_o_bri4tb_ibp_wr_excl_done),
                                                   .bri4tb_bs_ibp_err_wr(lat_o_bri4tb_ibp_err_wr),
                                                   .bri4tb_bs_ibp_wr_resp_accept(lat_o_bri4tb_ibp_wr_resp_accept),

                                                   // slave side
                                                   .npu_dmi0_axi_bs_ibp_cmd_valid(bs_o_npu_dmi0_axi_ibp_cmd_valid),
                                                   .npu_dmi0_axi_bs_ibp_cmd_accept(bs_o_npu_dmi0_axi_ibp_cmd_accept),
                                                   .npu_dmi0_axi_bs_ibp_cmd_read(bs_o_npu_dmi0_axi_ibp_cmd_read),
                                                   .npu_dmi0_axi_bs_ibp_cmd_addr(bs_o_npu_dmi0_axi_ibp_cmd_addr),
                                                   .npu_dmi0_axi_bs_ibp_cmd_wrap(bs_o_npu_dmi0_axi_ibp_cmd_wrap),
                                                   .npu_dmi0_axi_bs_ibp_cmd_data_size(bs_o_npu_dmi0_axi_ibp_cmd_data_size),
                                                   .npu_dmi0_axi_bs_ibp_cmd_burst_size(bs_o_npu_dmi0_axi_ibp_cmd_burst_size),
                                                   .npu_dmi0_axi_bs_ibp_cmd_lock(bs_o_npu_dmi0_axi_ibp_cmd_lock),
                                                   .npu_dmi0_axi_bs_ibp_cmd_excl(bs_o_npu_dmi0_axi_ibp_cmd_excl),
                                                   .npu_dmi0_axi_bs_ibp_cmd_prot(bs_o_npu_dmi0_axi_ibp_cmd_prot),
                                                   .npu_dmi0_axi_bs_ibp_cmd_cache(bs_o_npu_dmi0_axi_ibp_cmd_cache),
                                                   .npu_dmi0_axi_bs_ibp_cmd_region(bs_o_npu_dmi0_axi_ibp_cmd_region),
                                                   .npu_dmi0_axi_bs_ibp_rd_valid(bs_o_npu_dmi0_axi_ibp_rd_valid),
                                                   .npu_dmi0_axi_bs_ibp_rd_accept(bs_o_npu_dmi0_axi_ibp_rd_accept),
                                                   .npu_dmi0_axi_bs_ibp_rd_data(bs_o_npu_dmi0_axi_ibp_rd_data),
                                                   .npu_dmi0_axi_bs_ibp_rd_last(bs_o_npu_dmi0_axi_ibp_rd_last),
                                                   .npu_dmi0_axi_bs_ibp_err_rd(bs_o_npu_dmi0_axi_ibp_err_rd),
                                                   .npu_dmi0_axi_bs_ibp_rd_excl_ok(bs_o_npu_dmi0_axi_ibp_rd_excl_ok),
                                                   .npu_dmi0_axi_bs_ibp_wr_valid(bs_o_npu_dmi0_axi_ibp_wr_valid),
                                                   .npu_dmi0_axi_bs_ibp_wr_accept(bs_o_npu_dmi0_axi_ibp_wr_accept),
                                                   .npu_dmi0_axi_bs_ibp_wr_data(bs_o_npu_dmi0_axi_ibp_wr_data),
                                                   .npu_dmi0_axi_bs_ibp_wr_mask(bs_o_npu_dmi0_axi_ibp_wr_mask),
                                                   .npu_dmi0_axi_bs_ibp_wr_last(bs_o_npu_dmi0_axi_ibp_wr_last),
                                                   .npu_dmi0_axi_bs_ibp_wr_done(bs_o_npu_dmi0_axi_ibp_wr_done),
                                                   .npu_dmi0_axi_bs_ibp_wr_excl_done(bs_o_npu_dmi0_axi_ibp_wr_excl_done),
                                                   .npu_dmi0_axi_bs_ibp_err_wr(bs_o_npu_dmi0_axi_ibp_err_wr),
                                                   .npu_dmi0_axi_bs_ibp_wr_resp_accept(bs_o_npu_dmi0_axi_ibp_wr_resp_accept),

                                                   .npu_cfg_axi_bs_ibp_cmd_valid(bs_o_npu_cfg_axi_ibp_cmd_valid),
                                                   .npu_cfg_axi_bs_ibp_cmd_accept(bs_o_npu_cfg_axi_ibp_cmd_accept),
                                                   .npu_cfg_axi_bs_ibp_cmd_read(bs_o_npu_cfg_axi_ibp_cmd_read),
                                                   .npu_cfg_axi_bs_ibp_cmd_addr(bs_o_npu_cfg_axi_ibp_cmd_addr),
                                                   .npu_cfg_axi_bs_ibp_cmd_wrap(bs_o_npu_cfg_axi_ibp_cmd_wrap),
                                                   .npu_cfg_axi_bs_ibp_cmd_data_size(bs_o_npu_cfg_axi_ibp_cmd_data_size),
                                                   .npu_cfg_axi_bs_ibp_cmd_burst_size(bs_o_npu_cfg_axi_ibp_cmd_burst_size),
                                                   .npu_cfg_axi_bs_ibp_cmd_lock(bs_o_npu_cfg_axi_ibp_cmd_lock),
                                                   .npu_cfg_axi_bs_ibp_cmd_excl(bs_o_npu_cfg_axi_ibp_cmd_excl),
                                                   .npu_cfg_axi_bs_ibp_cmd_prot(bs_o_npu_cfg_axi_ibp_cmd_prot),
                                                   .npu_cfg_axi_bs_ibp_cmd_cache(bs_o_npu_cfg_axi_ibp_cmd_cache),
                                                   .npu_cfg_axi_bs_ibp_cmd_region(bs_o_npu_cfg_axi_ibp_cmd_region),
                                                   .npu_cfg_axi_bs_ibp_rd_valid(bs_o_npu_cfg_axi_ibp_rd_valid),
                                                   .npu_cfg_axi_bs_ibp_rd_accept(bs_o_npu_cfg_axi_ibp_rd_accept),
                                                   .npu_cfg_axi_bs_ibp_rd_data(bs_o_npu_cfg_axi_ibp_rd_data),
                                                   .npu_cfg_axi_bs_ibp_rd_last(bs_o_npu_cfg_axi_ibp_rd_last),
                                                   .npu_cfg_axi_bs_ibp_err_rd(bs_o_npu_cfg_axi_ibp_err_rd),
                                                   .npu_cfg_axi_bs_ibp_rd_excl_ok(bs_o_npu_cfg_axi_ibp_rd_excl_ok),
                                                   .npu_cfg_axi_bs_ibp_wr_valid(bs_o_npu_cfg_axi_ibp_wr_valid),
                                                   .npu_cfg_axi_bs_ibp_wr_accept(bs_o_npu_cfg_axi_ibp_wr_accept),
                                                   .npu_cfg_axi_bs_ibp_wr_data(bs_o_npu_cfg_axi_ibp_wr_data),
                                                   .npu_cfg_axi_bs_ibp_wr_mask(bs_o_npu_cfg_axi_ibp_wr_mask),
                                                   .npu_cfg_axi_bs_ibp_wr_last(bs_o_npu_cfg_axi_ibp_wr_last),
                                                   .npu_cfg_axi_bs_ibp_wr_done(bs_o_npu_cfg_axi_ibp_wr_done),
                                                   .npu_cfg_axi_bs_ibp_wr_excl_done(bs_o_npu_cfg_axi_ibp_wr_excl_done),
                                                   .npu_cfg_axi_bs_ibp_err_wr(bs_o_npu_cfg_axi_ibp_err_wr),
                                                   .npu_cfg_axi_bs_ibp_wr_resp_accept(bs_o_npu_cfg_axi_ibp_wr_resp_accept),

                                                   .arcsync_axi_bs_ibp_cmd_valid(bs_o_arcsync_axi_ibp_cmd_valid),
                                                   .arcsync_axi_bs_ibp_cmd_accept(bs_o_arcsync_axi_ibp_cmd_accept),
                                                   .arcsync_axi_bs_ibp_cmd_read(bs_o_arcsync_axi_ibp_cmd_read),
                                                   .arcsync_axi_bs_ibp_cmd_addr(bs_o_arcsync_axi_ibp_cmd_addr),
                                                   .arcsync_axi_bs_ibp_cmd_wrap(bs_o_arcsync_axi_ibp_cmd_wrap),
                                                   .arcsync_axi_bs_ibp_cmd_data_size(bs_o_arcsync_axi_ibp_cmd_data_size),
                                                   .arcsync_axi_bs_ibp_cmd_burst_size(bs_o_arcsync_axi_ibp_cmd_burst_size),
                                                   .arcsync_axi_bs_ibp_cmd_lock(bs_o_arcsync_axi_ibp_cmd_lock),
                                                   .arcsync_axi_bs_ibp_cmd_excl(bs_o_arcsync_axi_ibp_cmd_excl),
                                                   .arcsync_axi_bs_ibp_cmd_prot(bs_o_arcsync_axi_ibp_cmd_prot),
                                                   .arcsync_axi_bs_ibp_cmd_cache(bs_o_arcsync_axi_ibp_cmd_cache),
                                                   .arcsync_axi_bs_ibp_cmd_region(bs_o_arcsync_axi_ibp_cmd_region),
                                                   .arcsync_axi_bs_ibp_rd_valid(bs_o_arcsync_axi_ibp_rd_valid),
                                                   .arcsync_axi_bs_ibp_rd_accept(bs_o_arcsync_axi_ibp_rd_accept),
                                                   .arcsync_axi_bs_ibp_rd_data(bs_o_arcsync_axi_ibp_rd_data),
                                                   .arcsync_axi_bs_ibp_rd_last(bs_o_arcsync_axi_ibp_rd_last),
                                                   .arcsync_axi_bs_ibp_err_rd(bs_o_arcsync_axi_ibp_err_rd),
                                                   .arcsync_axi_bs_ibp_rd_excl_ok(bs_o_arcsync_axi_ibp_rd_excl_ok),
                                                   .arcsync_axi_bs_ibp_wr_valid(bs_o_arcsync_axi_ibp_wr_valid),
                                                   .arcsync_axi_bs_ibp_wr_accept(bs_o_arcsync_axi_ibp_wr_accept),
                                                   .arcsync_axi_bs_ibp_wr_data(bs_o_arcsync_axi_ibp_wr_data),
                                                   .arcsync_axi_bs_ibp_wr_mask(bs_o_arcsync_axi_ibp_wr_mask),
                                                   .arcsync_axi_bs_ibp_wr_last(bs_o_arcsync_axi_ibp_wr_last),
                                                   .arcsync_axi_bs_ibp_wr_done(bs_o_arcsync_axi_ibp_wr_done),
                                                   .arcsync_axi_bs_ibp_wr_excl_done(bs_o_arcsync_axi_ibp_wr_excl_done),
                                                   .arcsync_axi_bs_ibp_err_wr(bs_o_arcsync_axi_ibp_err_wr),
                                                   .arcsync_axi_bs_ibp_wr_resp_accept(bs_o_arcsync_axi_ibp_wr_resp_accept),

                                                   .mss_mem_bs_ibp_cmd_valid(bs_o_mss_mem_ibp_cmd_valid),
                                                   .mss_mem_bs_ibp_cmd_accept(bs_o_mss_mem_ibp_cmd_accept),
                                                   .mss_mem_bs_ibp_cmd_read(bs_o_mss_mem_ibp_cmd_read),
                                                   .mss_mem_bs_ibp_cmd_addr(bs_o_mss_mem_ibp_cmd_addr_temp),
                                                   .mss_mem_bs_ibp_cmd_wrap(bs_o_mss_mem_ibp_cmd_wrap),
                                                   .mss_mem_bs_ibp_cmd_data_size(bs_o_mss_mem_ibp_cmd_data_size),
                                                   .mss_mem_bs_ibp_cmd_burst_size(bs_o_mss_mem_ibp_cmd_burst_size),
                                                   .mss_mem_bs_ibp_cmd_lock(bs_o_mss_mem_ibp_cmd_lock),
                                                   .mss_mem_bs_ibp_cmd_excl(bs_o_mss_mem_ibp_cmd_excl),
                                                   .mss_mem_bs_ibp_cmd_prot(bs_o_mss_mem_ibp_cmd_prot),
                                                   .mss_mem_bs_ibp_cmd_cache(bs_o_mss_mem_ibp_cmd_cache),
                                                   .mss_mem_bs_ibp_cmd_region(bs_o_mss_mem_ibp_cmd_region),
                                                   .mss_mem_bs_ibp_rd_valid(bs_o_mss_mem_ibp_rd_valid),
                                                   .mss_mem_bs_ibp_rd_accept(bs_o_mss_mem_ibp_rd_accept),
                                                   .mss_mem_bs_ibp_rd_data(bs_o_mss_mem_ibp_rd_data),
                                                   .mss_mem_bs_ibp_rd_last(bs_o_mss_mem_ibp_rd_last),
                                                   .mss_mem_bs_ibp_err_rd(bs_o_mss_mem_ibp_err_rd),
                                                   .mss_mem_bs_ibp_rd_excl_ok(bs_o_mss_mem_ibp_rd_excl_ok),
                                                   .mss_mem_bs_ibp_wr_valid(bs_o_mss_mem_ibp_wr_valid),
                                                   .mss_mem_bs_ibp_wr_accept(bs_o_mss_mem_ibp_wr_accept),
                                                   .mss_mem_bs_ibp_wr_data(bs_o_mss_mem_ibp_wr_data),
                                                   .mss_mem_bs_ibp_wr_mask(bs_o_mss_mem_ibp_wr_mask),
                                                   .mss_mem_bs_ibp_wr_last(bs_o_mss_mem_ibp_wr_last),
                                                   .mss_mem_bs_ibp_wr_done(bs_o_mss_mem_ibp_wr_done),
                                                   .mss_mem_bs_ibp_wr_excl_done(bs_o_mss_mem_ibp_wr_excl_done),
                                                   .mss_mem_bs_ibp_err_wr(bs_o_mss_mem_ibp_err_wr),
                                                   .mss_mem_bs_ibp_wr_resp_accept(bs_o_mss_mem_ibp_wr_resp_accept),

                                                   // clock and reset
                                                   .clk(mss_clk),
                                                   .rst_a(~rst_b)
                                                   );
assign bs_o_mss_mem_ibp_cmd_addr = {bs_o_mss_mem_ibp_cmd_addr_temp[9+40-1:40],bs_o_mss_mem_ibp_cmd_addr_temp[32-1:0]};

    // To support flexible clock ratio configuration, there is a clk_domain converting logic here
    // handles from ARCv2MSS fabric clock domain to slave clock domain
    // If slave port already support clock ratio, the signals are just bypassed from fabric
    // If slave port doesn't support clock ratio, invloves two ibp_buffer to do domain conversion
      //
      // current slave prefix is npu_dmi0_axi_, cfree attr is 0, ratio attr is 0
      //
    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(49),
                           .DATA_W(512),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(0)
                           ) u_npu_dmi0_axi__ibp2pack_inst(
                           .ibp_cmd_rgon(bs_o_npu_dmi0_axi_ibp_cmd_region),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (bs_o_npu_dmi0_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (bs_o_npu_dmi0_axi_ibp_cmd_accept),
  .ibp_cmd_read              (bs_o_npu_dmi0_axi_ibp_cmd_read),
  .ibp_cmd_addr              (bs_o_npu_dmi0_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (bs_o_npu_dmi0_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (bs_o_npu_dmi0_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (bs_o_npu_dmi0_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (bs_o_npu_dmi0_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (bs_o_npu_dmi0_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (bs_o_npu_dmi0_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (bs_o_npu_dmi0_axi_ibp_cmd_excl),

  .ibp_rd_valid              (bs_o_npu_dmi0_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (bs_o_npu_dmi0_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (bs_o_npu_dmi0_axi_ibp_rd_accept),
  .ibp_err_rd                (bs_o_npu_dmi0_axi_ibp_err_rd),
  .ibp_rd_data               (bs_o_npu_dmi0_axi_ibp_rd_data),
  .ibp_rd_last               (bs_o_npu_dmi0_axi_ibp_rd_last),

  .ibp_wr_valid              (bs_o_npu_dmi0_axi_ibp_wr_valid),
  .ibp_wr_accept             (bs_o_npu_dmi0_axi_ibp_wr_accept),
  .ibp_wr_data               (bs_o_npu_dmi0_axi_ibp_wr_data),
  .ibp_wr_mask               (bs_o_npu_dmi0_axi_ibp_wr_mask),
  .ibp_wr_last               (bs_o_npu_dmi0_axi_ibp_wr_last),

  .ibp_wr_done               (bs_o_npu_dmi0_axi_ibp_wr_done),
  .ibp_wr_excl_done          (bs_o_npu_dmi0_axi_ibp_wr_excl_done),
  .ibp_err_wr                (bs_o_npu_dmi0_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (bs_o_npu_dmi0_axi_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (bs_o_npu_dmi0_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bs_o_npu_dmi0_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bs_o_npu_dmi0_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bs_o_npu_dmi0_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bs_o_npu_dmi0_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bs_o_npu_dmi0_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bs_o_npu_dmi0_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bs_o_npu_dmi0_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bs_o_npu_dmi0_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bs_o_npu_dmi0_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bs_o_npu_dmi0_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bs_o_npu_dmi0_axi_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(bs_o_npu_dmi0_axi_ibp_cmd_chnl_region),
                           .ibp_cmd_chnl_user(),
                           .clk(mss_clk),
                           .rst_a(~rst_b)
                           );
    // use fabric's clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(1),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(0),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_dmi0_axi__ibp_buffer_0_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(bs_o_npu_dmi0_axi_ibp_cmd_chnl_region),



    .i_ibp_cmd_chnl_valid  (bs_o_npu_dmi0_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (bs_o_npu_dmi0_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (bs_o_npu_dmi0_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (bs_o_npu_dmi0_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (bs_o_npu_dmi0_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (bs_o_npu_dmi0_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (bs_o_npu_dmi0_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (bs_o_npu_dmi0_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (bs_o_npu_dmi0_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (bs_o_npu_dmi0_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(bs_o_npu_dmi0_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (bs_o_npu_dmi0_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(mss_fab_slv0_clk_en),
                             .o_ibp_cmd_chnl_rgon(slv_i_npu_dmi0_axi_ibp_cmd_chnl_region),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (slv_i_npu_dmi0_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (slv_i_npu_dmi0_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (slv_i_npu_dmi0_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (slv_i_npu_dmi0_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (slv_i_npu_dmi0_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (slv_i_npu_dmi0_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (slv_i_npu_dmi0_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (slv_i_npu_dmi0_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (slv_i_npu_dmi0_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (slv_i_npu_dmi0_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(slv_i_npu_dmi0_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (slv_i_npu_dmi0_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );

    // use slave's clock (with prefix npu_dmi0_axi_) and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(1),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(0),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_dmi0_axi__ibp_buffer_1_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(slv_i_npu_dmi0_axi_ibp_cmd_chnl_region),



    .i_ibp_cmd_chnl_valid  (slv_i_npu_dmi0_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (slv_i_npu_dmi0_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (slv_i_npu_dmi0_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (slv_i_npu_dmi0_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (slv_i_npu_dmi0_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (slv_i_npu_dmi0_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (slv_i_npu_dmi0_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (slv_i_npu_dmi0_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (slv_i_npu_dmi0_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (slv_i_npu_dmi0_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(slv_i_npu_dmi0_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (slv_i_npu_dmi0_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(slv_o_npu_dmi0_axi_ibp_cmd_chnl_region),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (slv_o_npu_dmi0_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (slv_o_npu_dmi0_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (slv_o_npu_dmi0_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (slv_o_npu_dmi0_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (slv_o_npu_dmi0_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (slv_o_npu_dmi0_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (slv_o_npu_dmi0_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (slv_o_npu_dmi0_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (slv_o_npu_dmi0_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (slv_o_npu_dmi0_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(slv_o_npu_dmi0_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (slv_o_npu_dmi0_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(clk),
                             .rst_a(~rst_b)
                             );
    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(49),
                           .DATA_W(512),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (512),
    .WD_CHNL_MASK_LSB        (513),
    .WD_CHNL_MASK_W          (64),
    .WD_CHNL_W               (577),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (512),
    .RD_CHNL_W               (515),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(0)
                           ) u_npu_dmi0_axi__pack2ibp_inst(
                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(slv_o_npu_dmi0_axi_ibp_cmd_chnl_region),



    .ibp_cmd_chnl_valid  (slv_o_npu_dmi0_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (slv_o_npu_dmi0_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (slv_o_npu_dmi0_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (slv_o_npu_dmi0_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (slv_o_npu_dmi0_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (slv_o_npu_dmi0_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (slv_o_npu_dmi0_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (slv_o_npu_dmi0_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (slv_o_npu_dmi0_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (slv_o_npu_dmi0_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(slv_o_npu_dmi0_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (slv_o_npu_dmi0_axi_ibp_wrsp_chnl),


  .ibp_cmd_valid             (slv_o_npu_dmi0_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (slv_o_npu_dmi0_axi_ibp_cmd_accept),
  .ibp_cmd_read              (slv_o_npu_dmi0_axi_ibp_cmd_read),
  .ibp_cmd_addr              (slv_o_npu_dmi0_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (slv_o_npu_dmi0_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (slv_o_npu_dmi0_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (slv_o_npu_dmi0_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (slv_o_npu_dmi0_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (slv_o_npu_dmi0_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (slv_o_npu_dmi0_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (slv_o_npu_dmi0_axi_ibp_cmd_excl),

  .ibp_rd_valid              (slv_o_npu_dmi0_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (slv_o_npu_dmi0_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (slv_o_npu_dmi0_axi_ibp_rd_accept),
  .ibp_err_rd                (slv_o_npu_dmi0_axi_ibp_err_rd),
  .ibp_rd_data               (slv_o_npu_dmi0_axi_ibp_rd_data),
  .ibp_rd_last               (slv_o_npu_dmi0_axi_ibp_rd_last),

  .ibp_wr_valid              (slv_o_npu_dmi0_axi_ibp_wr_valid),
  .ibp_wr_accept             (slv_o_npu_dmi0_axi_ibp_wr_accept),
  .ibp_wr_data               (slv_o_npu_dmi0_axi_ibp_wr_data),
  .ibp_wr_mask               (slv_o_npu_dmi0_axi_ibp_wr_mask),
  .ibp_wr_last               (slv_o_npu_dmi0_axi_ibp_wr_last),

  .ibp_wr_done               (slv_o_npu_dmi0_axi_ibp_wr_done),
  .ibp_wr_excl_done          (slv_o_npu_dmi0_axi_ibp_wr_excl_done),
  .ibp_err_wr                (slv_o_npu_dmi0_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (slv_o_npu_dmi0_axi_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon(slv_o_npu_dmi0_axi_ibp_cmd_region)
                           );

      //
      // current slave prefix is npu_cfg_axi_, cfree attr is 0, ratio attr is 0
      //
    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(49),
                           .DATA_W(32),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (32),
    .WD_CHNL_MASK_LSB        (33),
    .WD_CHNL_MASK_W          (4),
    .WD_CHNL_W               (37),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (32),
    .RD_CHNL_W               (35),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(0)
                           ) u_npu_cfg_axi__ibp2pack_inst(
                           .ibp_cmd_rgon(bs_o_npu_cfg_axi_ibp_cmd_region),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (bs_o_npu_cfg_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (bs_o_npu_cfg_axi_ibp_cmd_accept),
  .ibp_cmd_read              (bs_o_npu_cfg_axi_ibp_cmd_read),
  .ibp_cmd_addr              (bs_o_npu_cfg_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (bs_o_npu_cfg_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (bs_o_npu_cfg_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (bs_o_npu_cfg_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (bs_o_npu_cfg_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (bs_o_npu_cfg_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (bs_o_npu_cfg_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (bs_o_npu_cfg_axi_ibp_cmd_excl),

  .ibp_rd_valid              (bs_o_npu_cfg_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (bs_o_npu_cfg_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (bs_o_npu_cfg_axi_ibp_rd_accept),
  .ibp_err_rd                (bs_o_npu_cfg_axi_ibp_err_rd),
  .ibp_rd_data               (bs_o_npu_cfg_axi_ibp_rd_data),
  .ibp_rd_last               (bs_o_npu_cfg_axi_ibp_rd_last),

  .ibp_wr_valid              (bs_o_npu_cfg_axi_ibp_wr_valid),
  .ibp_wr_accept             (bs_o_npu_cfg_axi_ibp_wr_accept),
  .ibp_wr_data               (bs_o_npu_cfg_axi_ibp_wr_data),
  .ibp_wr_mask               (bs_o_npu_cfg_axi_ibp_wr_mask),
  .ibp_wr_last               (bs_o_npu_cfg_axi_ibp_wr_last),

  .ibp_wr_done               (bs_o_npu_cfg_axi_ibp_wr_done),
  .ibp_wr_excl_done          (bs_o_npu_cfg_axi_ibp_wr_excl_done),
  .ibp_err_wr                (bs_o_npu_cfg_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (bs_o_npu_cfg_axi_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (bs_o_npu_cfg_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bs_o_npu_cfg_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bs_o_npu_cfg_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bs_o_npu_cfg_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bs_o_npu_cfg_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bs_o_npu_cfg_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bs_o_npu_cfg_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bs_o_npu_cfg_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bs_o_npu_cfg_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bs_o_npu_cfg_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bs_o_npu_cfg_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bs_o_npu_cfg_axi_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(bs_o_npu_cfg_axi_ibp_cmd_chnl_region),
                           .ibp_cmd_chnl_user(),
                           .clk(mss_clk),
                           .rst_a(~rst_b)
                           );
    // use fabric's clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(1),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (32),
    .WD_CHNL_MASK_LSB        (33),
    .WD_CHNL_MASK_W          (4),
    .WD_CHNL_W               (37),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (32),
    .RD_CHNL_W               (35),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(0),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_cfg_axi__ibp_buffer_0_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(bs_o_npu_cfg_axi_ibp_cmd_chnl_region),



    .i_ibp_cmd_chnl_valid  (bs_o_npu_cfg_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (bs_o_npu_cfg_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (bs_o_npu_cfg_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (bs_o_npu_cfg_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (bs_o_npu_cfg_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (bs_o_npu_cfg_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (bs_o_npu_cfg_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (bs_o_npu_cfg_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (bs_o_npu_cfg_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (bs_o_npu_cfg_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(bs_o_npu_cfg_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (bs_o_npu_cfg_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(mss_fab_slv1_clk_en),
                             .o_ibp_cmd_chnl_rgon(slv_i_npu_cfg_axi_ibp_cmd_chnl_region),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (slv_i_npu_cfg_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (slv_i_npu_cfg_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (slv_i_npu_cfg_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (slv_i_npu_cfg_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (slv_i_npu_cfg_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (slv_i_npu_cfg_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (slv_i_npu_cfg_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (slv_i_npu_cfg_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (slv_i_npu_cfg_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (slv_i_npu_cfg_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(slv_i_npu_cfg_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (slv_i_npu_cfg_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );

    // use slave's clock (with prefix npu_cfg_axi_) and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(1),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (32),
    .WD_CHNL_MASK_LSB        (33),
    .WD_CHNL_MASK_W          (4),
    .WD_CHNL_W               (37),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (32),
    .RD_CHNL_W               (35),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(0),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_npu_cfg_axi__ibp_buffer_1_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(slv_i_npu_cfg_axi_ibp_cmd_chnl_region),



    .i_ibp_cmd_chnl_valid  (slv_i_npu_cfg_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (slv_i_npu_cfg_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (slv_i_npu_cfg_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (slv_i_npu_cfg_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (slv_i_npu_cfg_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (slv_i_npu_cfg_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (slv_i_npu_cfg_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (slv_i_npu_cfg_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (slv_i_npu_cfg_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (slv_i_npu_cfg_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(slv_i_npu_cfg_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (slv_i_npu_cfg_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(slv_o_npu_cfg_axi_ibp_cmd_chnl_region),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (slv_o_npu_cfg_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (slv_o_npu_cfg_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (slv_o_npu_cfg_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (slv_o_npu_cfg_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (slv_o_npu_cfg_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (slv_o_npu_cfg_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (slv_o_npu_cfg_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (slv_o_npu_cfg_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (slv_o_npu_cfg_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (slv_o_npu_cfg_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(slv_o_npu_cfg_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (slv_o_npu_cfg_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(clk),
                             .rst_a(~rst_b)
                             );
    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(49),
                           .DATA_W(32),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (32),
    .WD_CHNL_MASK_LSB        (33),
    .WD_CHNL_MASK_W          (4),
    .WD_CHNL_W               (37),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (32),
    .RD_CHNL_W               (35),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(0)
                           ) u_npu_cfg_axi__pack2ibp_inst(
                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(slv_o_npu_cfg_axi_ibp_cmd_chnl_region),



    .ibp_cmd_chnl_valid  (slv_o_npu_cfg_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (slv_o_npu_cfg_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (slv_o_npu_cfg_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (slv_o_npu_cfg_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (slv_o_npu_cfg_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (slv_o_npu_cfg_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (slv_o_npu_cfg_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (slv_o_npu_cfg_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (slv_o_npu_cfg_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (slv_o_npu_cfg_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(slv_o_npu_cfg_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (slv_o_npu_cfg_axi_ibp_wrsp_chnl),


  .ibp_cmd_valid             (slv_o_npu_cfg_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (slv_o_npu_cfg_axi_ibp_cmd_accept),
  .ibp_cmd_read              (slv_o_npu_cfg_axi_ibp_cmd_read),
  .ibp_cmd_addr              (slv_o_npu_cfg_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (slv_o_npu_cfg_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (slv_o_npu_cfg_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (slv_o_npu_cfg_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (slv_o_npu_cfg_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (slv_o_npu_cfg_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (slv_o_npu_cfg_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (slv_o_npu_cfg_axi_ibp_cmd_excl),

  .ibp_rd_valid              (slv_o_npu_cfg_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (slv_o_npu_cfg_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (slv_o_npu_cfg_axi_ibp_rd_accept),
  .ibp_err_rd                (slv_o_npu_cfg_axi_ibp_err_rd),
  .ibp_rd_data               (slv_o_npu_cfg_axi_ibp_rd_data),
  .ibp_rd_last               (slv_o_npu_cfg_axi_ibp_rd_last),

  .ibp_wr_valid              (slv_o_npu_cfg_axi_ibp_wr_valid),
  .ibp_wr_accept             (slv_o_npu_cfg_axi_ibp_wr_accept),
  .ibp_wr_data               (slv_o_npu_cfg_axi_ibp_wr_data),
  .ibp_wr_mask               (slv_o_npu_cfg_axi_ibp_wr_mask),
  .ibp_wr_last               (slv_o_npu_cfg_axi_ibp_wr_last),

  .ibp_wr_done               (slv_o_npu_cfg_axi_ibp_wr_done),
  .ibp_wr_excl_done          (slv_o_npu_cfg_axi_ibp_wr_excl_done),
  .ibp_err_wr                (slv_o_npu_cfg_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (slv_o_npu_cfg_axi_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon(slv_o_npu_cfg_axi_ibp_cmd_region)
                           );

      //
      // current slave prefix is arcsync_axi_, cfree attr is 0, ratio attr is 0
      //
    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(49),
                           .DATA_W(64),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(0)
                           ) u_arcsync_axi__ibp2pack_inst(
                           .ibp_cmd_rgon(bs_o_arcsync_axi_ibp_cmd_region),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (bs_o_arcsync_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (bs_o_arcsync_axi_ibp_cmd_accept),
  .ibp_cmd_read              (bs_o_arcsync_axi_ibp_cmd_read),
  .ibp_cmd_addr              (bs_o_arcsync_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (bs_o_arcsync_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (bs_o_arcsync_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (bs_o_arcsync_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (bs_o_arcsync_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (bs_o_arcsync_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (bs_o_arcsync_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (bs_o_arcsync_axi_ibp_cmd_excl),

  .ibp_rd_valid              (bs_o_arcsync_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (bs_o_arcsync_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (bs_o_arcsync_axi_ibp_rd_accept),
  .ibp_err_rd                (bs_o_arcsync_axi_ibp_err_rd),
  .ibp_rd_data               (bs_o_arcsync_axi_ibp_rd_data),
  .ibp_rd_last               (bs_o_arcsync_axi_ibp_rd_last),

  .ibp_wr_valid              (bs_o_arcsync_axi_ibp_wr_valid),
  .ibp_wr_accept             (bs_o_arcsync_axi_ibp_wr_accept),
  .ibp_wr_data               (bs_o_arcsync_axi_ibp_wr_data),
  .ibp_wr_mask               (bs_o_arcsync_axi_ibp_wr_mask),
  .ibp_wr_last               (bs_o_arcsync_axi_ibp_wr_last),

  .ibp_wr_done               (bs_o_arcsync_axi_ibp_wr_done),
  .ibp_wr_excl_done          (bs_o_arcsync_axi_ibp_wr_excl_done),
  .ibp_err_wr                (bs_o_arcsync_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (bs_o_arcsync_axi_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (bs_o_arcsync_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bs_o_arcsync_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bs_o_arcsync_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bs_o_arcsync_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bs_o_arcsync_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bs_o_arcsync_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bs_o_arcsync_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bs_o_arcsync_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bs_o_arcsync_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bs_o_arcsync_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bs_o_arcsync_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bs_o_arcsync_axi_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(bs_o_arcsync_axi_ibp_cmd_chnl_region),
                           .ibp_cmd_chnl_user(),
                           .clk(mss_clk),
                           .rst_a(~rst_b)
                           );
    // use fabric's clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(1),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(0),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_arcsync_axi__ibp_buffer_0_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(bs_o_arcsync_axi_ibp_cmd_chnl_region),



    .i_ibp_cmd_chnl_valid  (bs_o_arcsync_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (bs_o_arcsync_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (bs_o_arcsync_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (bs_o_arcsync_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (bs_o_arcsync_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (bs_o_arcsync_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (bs_o_arcsync_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (bs_o_arcsync_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (bs_o_arcsync_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (bs_o_arcsync_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(bs_o_arcsync_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (bs_o_arcsync_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(mss_fab_slv2_clk_en),
                             .o_ibp_cmd_chnl_rgon(slv_i_arcsync_axi_ibp_cmd_chnl_region),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (slv_i_arcsync_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (slv_i_arcsync_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (slv_i_arcsync_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (slv_i_arcsync_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (slv_i_arcsync_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (slv_i_arcsync_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (slv_i_arcsync_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (slv_i_arcsync_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (slv_i_arcsync_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (slv_i_arcsync_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(slv_i_arcsync_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (slv_i_arcsync_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );

    // use slave's clock (with prefix arcsync_axi_) and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(1),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(0),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_arcsync_axi__ibp_buffer_1_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(slv_i_arcsync_axi_ibp_cmd_chnl_region),



    .i_ibp_cmd_chnl_valid  (slv_i_arcsync_axi_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (slv_i_arcsync_axi_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (slv_i_arcsync_axi_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (slv_i_arcsync_axi_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (slv_i_arcsync_axi_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (slv_i_arcsync_axi_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (slv_i_arcsync_axi_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (slv_i_arcsync_axi_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (slv_i_arcsync_axi_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (slv_i_arcsync_axi_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(slv_i_arcsync_axi_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (slv_i_arcsync_axi_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(slv_o_arcsync_axi_ibp_cmd_chnl_region),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (slv_o_arcsync_axi_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (slv_o_arcsync_axi_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (slv_o_arcsync_axi_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (slv_o_arcsync_axi_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (slv_o_arcsync_axi_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (slv_o_arcsync_axi_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (slv_o_arcsync_axi_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (slv_o_arcsync_axi_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (slv_o_arcsync_axi_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (slv_o_arcsync_axi_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(slv_o_arcsync_axi_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (slv_o_arcsync_axi_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(clk),
                             .rst_a(~rst_b)
                             );
    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(49),
                           .DATA_W(64),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (49),
    .CMD_CHNL_W              (66),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (64),
    .WD_CHNL_MASK_LSB        (65),
    .WD_CHNL_MASK_W          (8),
    .WD_CHNL_W               (73),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (64),
    .RD_CHNL_W               (67),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(0)
                           ) u_arcsync_axi__pack2ibp_inst(
                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(slv_o_arcsync_axi_ibp_cmd_chnl_region),



    .ibp_cmd_chnl_valid  (slv_o_arcsync_axi_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (slv_o_arcsync_axi_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (slv_o_arcsync_axi_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (slv_o_arcsync_axi_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (slv_o_arcsync_axi_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (slv_o_arcsync_axi_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (slv_o_arcsync_axi_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (slv_o_arcsync_axi_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (slv_o_arcsync_axi_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (slv_o_arcsync_axi_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(slv_o_arcsync_axi_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (slv_o_arcsync_axi_ibp_wrsp_chnl),


  .ibp_cmd_valid             (slv_o_arcsync_axi_ibp_cmd_valid),
  .ibp_cmd_accept            (slv_o_arcsync_axi_ibp_cmd_accept),
  .ibp_cmd_read              (slv_o_arcsync_axi_ibp_cmd_read),
  .ibp_cmd_addr              (slv_o_arcsync_axi_ibp_cmd_addr),
  .ibp_cmd_wrap              (slv_o_arcsync_axi_ibp_cmd_wrap),
  .ibp_cmd_data_size         (slv_o_arcsync_axi_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (slv_o_arcsync_axi_ibp_cmd_burst_size),
  .ibp_cmd_prot              (slv_o_arcsync_axi_ibp_cmd_prot),
  .ibp_cmd_cache             (slv_o_arcsync_axi_ibp_cmd_cache),
  .ibp_cmd_lock              (slv_o_arcsync_axi_ibp_cmd_lock),
  .ibp_cmd_excl              (slv_o_arcsync_axi_ibp_cmd_excl),

  .ibp_rd_valid              (slv_o_arcsync_axi_ibp_rd_valid),
  .ibp_rd_excl_ok            (slv_o_arcsync_axi_ibp_rd_excl_ok),
  .ibp_rd_accept             (slv_o_arcsync_axi_ibp_rd_accept),
  .ibp_err_rd                (slv_o_arcsync_axi_ibp_err_rd),
  .ibp_rd_data               (slv_o_arcsync_axi_ibp_rd_data),
  .ibp_rd_last               (slv_o_arcsync_axi_ibp_rd_last),

  .ibp_wr_valid              (slv_o_arcsync_axi_ibp_wr_valid),
  .ibp_wr_accept             (slv_o_arcsync_axi_ibp_wr_accept),
  .ibp_wr_data               (slv_o_arcsync_axi_ibp_wr_data),
  .ibp_wr_mask               (slv_o_arcsync_axi_ibp_wr_mask),
  .ibp_wr_last               (slv_o_arcsync_axi_ibp_wr_last),

  .ibp_wr_done               (slv_o_arcsync_axi_ibp_wr_done),
  .ibp_wr_excl_done          (slv_o_arcsync_axi_ibp_wr_excl_done),
  .ibp_err_wr                (slv_o_arcsync_axi_ibp_err_wr),
  .ibp_wr_resp_accept        (slv_o_arcsync_axi_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon(slv_o_arcsync_axi_ibp_cmd_region)
                           );

      //
      // current slave prefix is mss_mem_, cfree attr is 0, ratio attr is 0
      //
    // pack the IBP interface
    alb_mss_fab_ibp2pack #(
                           .ADDR_W(41),
                           .DATA_W(128),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (41),
    .CMD_CHNL_W              (58),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (128),
    .WD_CHNL_MASK_LSB        (129),
    .WD_CHNL_MASK_W          (16),
    .WD_CHNL_W               (145),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (128),
    .RD_CHNL_W               (131),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_mss_mem__ibp2pack_inst(
                           .ibp_cmd_rgon(bs_o_mss_mem_ibp_cmd_region),
                           .ibp_cmd_user(1'b0),

  .ibp_cmd_valid             (bs_o_mss_mem_ibp_cmd_valid),
  .ibp_cmd_accept            (bs_o_mss_mem_ibp_cmd_accept),
  .ibp_cmd_read              (bs_o_mss_mem_ibp_cmd_read),
  .ibp_cmd_addr              (bs_o_mss_mem_ibp_cmd_addr),
  .ibp_cmd_wrap              (bs_o_mss_mem_ibp_cmd_wrap),
  .ibp_cmd_data_size         (bs_o_mss_mem_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (bs_o_mss_mem_ibp_cmd_burst_size),
  .ibp_cmd_prot              (bs_o_mss_mem_ibp_cmd_prot),
  .ibp_cmd_cache             (bs_o_mss_mem_ibp_cmd_cache),
  .ibp_cmd_lock              (bs_o_mss_mem_ibp_cmd_lock),
  .ibp_cmd_excl              (bs_o_mss_mem_ibp_cmd_excl),

  .ibp_rd_valid              (bs_o_mss_mem_ibp_rd_valid),
  .ibp_rd_excl_ok            (bs_o_mss_mem_ibp_rd_excl_ok),
  .ibp_rd_accept             (bs_o_mss_mem_ibp_rd_accept),
  .ibp_err_rd                (bs_o_mss_mem_ibp_err_rd),
  .ibp_rd_data               (bs_o_mss_mem_ibp_rd_data),
  .ibp_rd_last               (bs_o_mss_mem_ibp_rd_last),

  .ibp_wr_valid              (bs_o_mss_mem_ibp_wr_valid),
  .ibp_wr_accept             (bs_o_mss_mem_ibp_wr_accept),
  .ibp_wr_data               (bs_o_mss_mem_ibp_wr_data),
  .ibp_wr_mask               (bs_o_mss_mem_ibp_wr_mask),
  .ibp_wr_last               (bs_o_mss_mem_ibp_wr_last),

  .ibp_wr_done               (bs_o_mss_mem_ibp_wr_done),
  .ibp_wr_excl_done          (bs_o_mss_mem_ibp_wr_excl_done),
  .ibp_err_wr                (bs_o_mss_mem_ibp_err_wr),
  .ibp_wr_resp_accept        (bs_o_mss_mem_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (bs_o_mss_mem_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bs_o_mss_mem_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bs_o_mss_mem_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bs_o_mss_mem_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bs_o_mss_mem_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bs_o_mss_mem_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bs_o_mss_mem_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bs_o_mss_mem_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bs_o_mss_mem_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bs_o_mss_mem_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bs_o_mss_mem_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bs_o_mss_mem_ibp_wrsp_chnl),

                           .ibp_cmd_chnl_rgon(bs_o_mss_mem_ibp_cmd_chnl_region),
                           .ibp_cmd_chnl_user(),
                           .clk(mss_clk),
                           .rst_a(~rst_b)
                           );
    // use fabric's clock and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(0),
                             .O_IBP_SUPPORT_RTIO(1),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (41),
    .CMD_CHNL_W              (58),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (128),
    .WD_CHNL_MASK_LSB        (129),
    .WD_CHNL_MASK_W          (16),
    .WD_CHNL_W               (145),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (128),
    .RD_CHNL_W               (131),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_mss_mem__ibp_buffer_0_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(bs_o_mss_mem_ibp_cmd_chnl_region),



    .i_ibp_cmd_chnl_valid  (bs_o_mss_mem_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (bs_o_mss_mem_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (bs_o_mss_mem_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (bs_o_mss_mem_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (bs_o_mss_mem_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (bs_o_mss_mem_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (bs_o_mss_mem_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (bs_o_mss_mem_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (bs_o_mss_mem_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (bs_o_mss_mem_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(bs_o_mss_mem_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (bs_o_mss_mem_ibp_wrsp_chnl),

                             .o_ibp_clk_en(mss_fab_slv3_clk_en),
                             .o_ibp_cmd_chnl_rgon(slv_i_mss_mem_ibp_cmd_chnl_region),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (slv_i_mss_mem_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (slv_i_mss_mem_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (slv_i_mss_mem_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (slv_i_mss_mem_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (slv_i_mss_mem_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (slv_i_mss_mem_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (slv_i_mss_mem_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (slv_i_mss_mem_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (slv_i_mss_mem_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (slv_i_mss_mem_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(slv_i_mss_mem_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (slv_i_mss_mem_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );

    // use slave's clock (with prefix mss_mem_) and clk_en for sampling
    alb_mss_fab_ibp_buffer #(.I_IBP_SUPPORT_RTIO(1),
                             .O_IBP_SUPPORT_RTIO(0),
                             .OUTSTAND_NUM(64),
                             .OUTSTAND_CNT_W(6),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (41),
    .CMD_CHNL_W              (58),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (128),
    .WD_CHNL_MASK_LSB        (129),
    .WD_CHNL_MASK_W          (16),
    .WD_CHNL_W               (145),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (128),
    .RD_CHNL_W               (131),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                             .RGON_W(1),
                             .USER_W(1),
                             .CMD_CHNL_FIFO_MWHILE(0),
                             .WDATA_CHNL_FIFO_MWHILE(0),
                             .RDATA_CHNL_FIFO_MWHILE(0),
                             .WRESP_CHNL_FIFO_MWHILE(0),
                             .CMD_CHNL_FIFO_DEPTH(0),
                             .WDATA_CHNL_FIFO_DEPTH(0),
                             .RDATA_CHNL_FIFO_DEPTH(0),
                             .WRESP_CHNL_FIFO_DEPTH(0)
                             ) u_mss_mem__ibp_buffer_1_inst (
                             .i_ibp_clk_en(1'b1),
                             .i_ibp_cmd_chnl_rgon(slv_i_mss_mem_ibp_cmd_chnl_region),



    .i_ibp_cmd_chnl_valid  (slv_i_mss_mem_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (slv_i_mss_mem_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (slv_i_mss_mem_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (slv_i_mss_mem_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (slv_i_mss_mem_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (slv_i_mss_mem_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (slv_i_mss_mem_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (slv_i_mss_mem_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (slv_i_mss_mem_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (slv_i_mss_mem_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(slv_i_mss_mem_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (slv_i_mss_mem_ibp_wrsp_chnl),

                             .o_ibp_clk_en(1'b1),
                             .o_ibp_cmd_chnl_rgon(slv_o_mss_mem_ibp_cmd_chnl_region),
                             .i_ibp_cmd_chnl_user(1'b0),
                             .o_ibp_cmd_chnl_user(),



    .o_ibp_cmd_chnl_valid  (slv_o_mss_mem_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (slv_o_mss_mem_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (slv_o_mss_mem_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (slv_o_mss_mem_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (slv_o_mss_mem_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (slv_o_mss_mem_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (slv_o_mss_mem_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (slv_o_mss_mem_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (slv_o_mss_mem_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (slv_o_mss_mem_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(slv_o_mss_mem_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (slv_o_mss_mem_ibp_wrsp_chnl),

                             .ibp_buffer_idle(),
                             .clk(mss_clk),
                             .rst_a(~rst_b)
                             );
    // unpack the IBP interface
    alb_mss_fab_pack2ibp #(
                           .ADDR_W(41),
                           .DATA_W(128),
                           .USER_W(1),



    .CMD_CHNL_READ           (0),
    .CMD_CHNL_WRAP           (1),
    .CMD_CHNL_DATA_SIZE_LSB  (2),
    .CMD_CHNL_DATA_SIZE_W    (3),
    .CMD_CHNL_BURST_SIZE_LSB (5),
    .CMD_CHNL_BURST_SIZE_W   (4),
    .CMD_CHNL_PROT_LSB       (9),
    .CMD_CHNL_PROT_W         (2),
    .CMD_CHNL_CACHE_LSB      (11),
    .CMD_CHNL_CACHE_W        (4),
    .CMD_CHNL_LOCK           (15),
    .CMD_CHNL_EXCL           (16),
    .CMD_CHNL_ADDR_LSB       (17),
    .CMD_CHNL_ADDR_W         (41),
    .CMD_CHNL_W              (58),

    .WD_CHNL_LAST            (0),
    .WD_CHNL_DATA_LSB        (1),
    .WD_CHNL_DATA_W          (128),
    .WD_CHNL_MASK_LSB        (129),
    .WD_CHNL_MASK_W          (16),
    .WD_CHNL_W               (145),

    .RD_CHNL_ERR_RD          (0),
    .RD_CHNL_RD_EXCL_OK      (2),
    .RD_CHNL_RD_LAST         (1),
    .RD_CHNL_RD_DATA_LSB     (3),
    .RD_CHNL_RD_DATA_W       (128),
    .RD_CHNL_W               (131),

    .WRSP_CHNL_WR_DONE       (0),
    .WRSP_CHNL_WR_EXCL_DONE  (1),
    .WRSP_CHNL_ERR_WR        (2),
    .WRSP_CHNL_W             (3),
                           .RGON_W(1)
                           ) u_mss_mem__pack2ibp_inst(
                           .ibp_cmd_chnl_user(1'b0),
                           .ibp_cmd_chnl_rgon(slv_o_mss_mem_ibp_cmd_chnl_region),



    .ibp_cmd_chnl_valid  (slv_o_mss_mem_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (slv_o_mss_mem_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (slv_o_mss_mem_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (slv_o_mss_mem_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (slv_o_mss_mem_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (slv_o_mss_mem_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (slv_o_mss_mem_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (slv_o_mss_mem_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (slv_o_mss_mem_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (slv_o_mss_mem_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(slv_o_mss_mem_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (slv_o_mss_mem_ibp_wrsp_chnl),


  .ibp_cmd_valid             (slv_o_mss_mem_ibp_cmd_valid),
  .ibp_cmd_accept            (slv_o_mss_mem_ibp_cmd_accept),
  .ibp_cmd_read              (slv_o_mss_mem_ibp_cmd_read),
  .ibp_cmd_addr              (slv_o_mss_mem_ibp_cmd_addr),
  .ibp_cmd_wrap              (slv_o_mss_mem_ibp_cmd_wrap),
  .ibp_cmd_data_size         (slv_o_mss_mem_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (slv_o_mss_mem_ibp_cmd_burst_size),
  .ibp_cmd_prot              (slv_o_mss_mem_ibp_cmd_prot),
  .ibp_cmd_cache             (slv_o_mss_mem_ibp_cmd_cache),
  .ibp_cmd_lock              (slv_o_mss_mem_ibp_cmd_lock),
  .ibp_cmd_excl              (slv_o_mss_mem_ibp_cmd_excl),

  .ibp_rd_valid              (slv_o_mss_mem_ibp_rd_valid),
  .ibp_rd_excl_ok            (slv_o_mss_mem_ibp_rd_excl_ok),
  .ibp_rd_accept             (slv_o_mss_mem_ibp_rd_accept),
  .ibp_err_rd                (slv_o_mss_mem_ibp_err_rd),
  .ibp_rd_data               (slv_o_mss_mem_ibp_rd_data),
  .ibp_rd_last               (slv_o_mss_mem_ibp_rd_last),

  .ibp_wr_valid              (slv_o_mss_mem_ibp_wr_valid),
  .ibp_wr_accept             (slv_o_mss_mem_ibp_wr_accept),
  .ibp_wr_data               (slv_o_mss_mem_ibp_wr_data),
  .ibp_wr_mask               (slv_o_mss_mem_ibp_wr_mask),
  .ibp_wr_last               (slv_o_mss_mem_ibp_wr_last),

  .ibp_wr_done               (slv_o_mss_mem_ibp_wr_done),
  .ibp_wr_excl_done          (slv_o_mss_mem_ibp_wr_excl_done),
  .ibp_err_wr                (slv_o_mss_mem_ibp_err_wr),
  .ibp_wr_resp_accept        (slv_o_mss_mem_ibp_wr_resp_accept),
                           .ibp_cmd_user(),
                           .ibp_cmd_rgon(slv_o_mss_mem_ibp_cmd_region)
                           );


    // Output protocol converters

wire [1:0]npu_dmi0_axi_arlock_temp;
wire [1:0]npu_dmi0_axi_awlock_temp;
assign npu_dmi0_axi_arlock = npu_dmi0_axi_arlock_temp[0];
assign npu_dmi0_axi_awlock = npu_dmi0_axi_awlock_temp[0];

    alb_mss_fab_ibp2axi #(
                          .CHNL_FIFO_DEPTH(2),
                          .ID_W(16),
                          .ADDR_W(40),
                          .DATA_W(512)) u_npu_dmi0_axi_prot_inst(
                                                    .clk(clk),
                                                    .bus_clk_en(1'b1),
                                                    .rst_a(~rst_b),
                                                    //IBP I/F
                                                    .ibp_cmd_user(1'b0),
                                                    .axi_aruser(),
                                                    .axi_awuser(),
                                                    .ibp_cmd_valid(slv_o_npu_dmi0_axi_ibp_cmd_valid),
                                                    .ibp_cmd_accept(slv_o_npu_dmi0_axi_ibp_cmd_accept),
                                                    .ibp_cmd_read(slv_o_npu_dmi0_axi_ibp_cmd_read),
                                                    .ibp_cmd_addr(slv_o_npu_dmi0_axi_ibp_cmd_addr[40-1:0]),
                                                    .ibp_cmd_wrap(slv_o_npu_dmi0_axi_ibp_cmd_wrap),
                                                    .ibp_cmd_data_size(slv_o_npu_dmi0_axi_ibp_cmd_data_size),
                                                    .ibp_cmd_burst_size(slv_o_npu_dmi0_axi_ibp_cmd_burst_size),
                                                    .ibp_cmd_prot(slv_o_npu_dmi0_axi_ibp_cmd_prot),
                                                    .ibp_cmd_cache(slv_o_npu_dmi0_axi_ibp_cmd_cache),
                                                    .ibp_cmd_lock(slv_o_npu_dmi0_axi_ibp_cmd_lock),
                                                    .ibp_cmd_excl(slv_o_npu_dmi0_axi_ibp_cmd_excl),

                                                    .ibp_rd_valid(slv_o_npu_dmi0_axi_ibp_rd_valid),
                                                    .ibp_rd_accept(slv_o_npu_dmi0_axi_ibp_rd_accept),
                                                    .ibp_rd_data(slv_o_npu_dmi0_axi_ibp_rd_data),
                                                    .ibp_err_rd(slv_o_npu_dmi0_axi_ibp_err_rd),
                                                    .ibp_rd_last(slv_o_npu_dmi0_axi_ibp_rd_last),
                                                    .ibp_rd_excl_ok(slv_o_npu_dmi0_axi_ibp_rd_excl_ok),

                                                    .ibp_wr_valid(slv_o_npu_dmi0_axi_ibp_wr_valid),
                                                    .ibp_wr_accept(slv_o_npu_dmi0_axi_ibp_wr_accept),
                                                    .ibp_wr_data(slv_o_npu_dmi0_axi_ibp_wr_data),
                                                    .ibp_wr_mask(slv_o_npu_dmi0_axi_ibp_wr_mask),
                                                    .ibp_wr_last(slv_o_npu_dmi0_axi_ibp_wr_last),

                                                    .ibp_wr_done(slv_o_npu_dmi0_axi_ibp_wr_done),
                                                    .ibp_wr_excl_done(slv_o_npu_dmi0_axi_ibp_wr_excl_done),
                                                    .ibp_err_wr(slv_o_npu_dmi0_axi_ibp_err_wr),
                                                    .ibp_wr_resp_accept(slv_o_npu_dmi0_axi_ibp_wr_resp_accept),
                                                    //extra id signals
                                                    .ibp_cmd_chnl_id({16{1'b0}}),
                                                    .ibp_rd_chnl_id(),
                                                    .ibp_wd_chnl_id({16{1'b0}}),
                                                    .ibp_wrsp_chnl_id(),
                                                    // AXI I/F
                                                    .axi_arvalid(npu_dmi0_axi_arvalid),
                                                    .axi_arready(npu_dmi0_axi_arready),
                                                    .axi_araddr(npu_dmi0_axi_araddr),
                                                    .axi_arburst(npu_dmi0_axi_arburst),
                                                    .axi_arsize(npu_dmi0_axi_arsize),
                                                    .axi_arlen(npu_dmi0_axi_arlen),
                                                    .axi_arcache(npu_dmi0_axi_arcache),
                                                    .axi_arprot(npu_dmi0_axi_arprot),
                                                    .axi_arlock(npu_dmi0_axi_arlock_temp),
                                                    .axi_arid(npu_dmi0_axi_arid),
                                                    .axi_awvalid(npu_dmi0_axi_awvalid),
                                                    .axi_awready(npu_dmi0_axi_awready),
                                                    .axi_awaddr(npu_dmi0_axi_awaddr),
                                                    .axi_awcache(npu_dmi0_axi_awcache),
                                                    .axi_awprot(npu_dmi0_axi_awprot),
                                                    .axi_awlock(npu_dmi0_axi_awlock_temp),
                                                    .axi_awburst(npu_dmi0_axi_awburst),
                                                    .axi_awsize(npu_dmi0_axi_awsize),
                                                    .axi_awlen(npu_dmi0_axi_awlen),
                                                    .axi_awid(npu_dmi0_axi_awid),
                                                    .axi_rvalid(npu_dmi0_axi_rvalid),
                                                    .axi_rready(npu_dmi0_axi_rready),
                                                    .axi_rdata(npu_dmi0_axi_rdata),
                                                    .axi_rresp(npu_dmi0_axi_rresp),
                                                    .axi_rlast(npu_dmi0_axi_rlast),
                                                    .axi_rid(npu_dmi0_axi_rid),
                                                    .axi_wvalid(npu_dmi0_axi_wvalid),
                                                    .axi_wready(npu_dmi0_axi_wready),
                                                    .axi_wdata(npu_dmi0_axi_wdata),
                                                    .axi_wstrb(npu_dmi0_axi_wstrb),
                                                    .axi_wlast(npu_dmi0_axi_wlast),
                                                    .axi_wid(),
                                                    .axi_bid(npu_dmi0_axi_bid),
                                                    .axi_bvalid(npu_dmi0_axi_bvalid),
                                                    .axi_bready(npu_dmi0_axi_bready),
                                                    .axi_bresp(npu_dmi0_axi_bresp));



wire [1:0]npu_cfg_axi_arlock_temp;
wire [1:0]npu_cfg_axi_awlock_temp;
assign npu_cfg_axi_arlock = npu_cfg_axi_arlock_temp[0];
assign npu_cfg_axi_awlock = npu_cfg_axi_awlock_temp[0];

    alb_mss_fab_ibp2axi #(
                          .CHNL_FIFO_DEPTH(2),
                          .ID_W(16),
                          .ADDR_W(40),
                          .DATA_W(32)) u_npu_cfg_axi_prot_inst(
                                                    .clk(clk),
                                                    .bus_clk_en(1'b1),
                                                    .rst_a(~rst_b),
                                                    //IBP I/F
                                                    .ibp_cmd_user(1'b0),
                                                    .axi_aruser(),
                                                    .axi_awuser(),
                                                    .ibp_cmd_valid(slv_o_npu_cfg_axi_ibp_cmd_valid),
                                                    .ibp_cmd_accept(slv_o_npu_cfg_axi_ibp_cmd_accept),
                                                    .ibp_cmd_read(slv_o_npu_cfg_axi_ibp_cmd_read),
                                                    .ibp_cmd_addr(slv_o_npu_cfg_axi_ibp_cmd_addr[40-1:0]),
                                                    .ibp_cmd_wrap(slv_o_npu_cfg_axi_ibp_cmd_wrap),
                                                    .ibp_cmd_data_size(slv_o_npu_cfg_axi_ibp_cmd_data_size),
                                                    .ibp_cmd_burst_size(slv_o_npu_cfg_axi_ibp_cmd_burst_size),
                                                    .ibp_cmd_prot(slv_o_npu_cfg_axi_ibp_cmd_prot),
                                                    .ibp_cmd_cache(slv_o_npu_cfg_axi_ibp_cmd_cache),
                                                    .ibp_cmd_lock(slv_o_npu_cfg_axi_ibp_cmd_lock),
                                                    .ibp_cmd_excl(slv_o_npu_cfg_axi_ibp_cmd_excl),

                                                    .ibp_rd_valid(slv_o_npu_cfg_axi_ibp_rd_valid),
                                                    .ibp_rd_accept(slv_o_npu_cfg_axi_ibp_rd_accept),
                                                    .ibp_rd_data(slv_o_npu_cfg_axi_ibp_rd_data),
                                                    .ibp_err_rd(slv_o_npu_cfg_axi_ibp_err_rd),
                                                    .ibp_rd_last(slv_o_npu_cfg_axi_ibp_rd_last),
                                                    .ibp_rd_excl_ok(slv_o_npu_cfg_axi_ibp_rd_excl_ok),

                                                    .ibp_wr_valid(slv_o_npu_cfg_axi_ibp_wr_valid),
                                                    .ibp_wr_accept(slv_o_npu_cfg_axi_ibp_wr_accept),
                                                    .ibp_wr_data(slv_o_npu_cfg_axi_ibp_wr_data),
                                                    .ibp_wr_mask(slv_o_npu_cfg_axi_ibp_wr_mask),
                                                    .ibp_wr_last(slv_o_npu_cfg_axi_ibp_wr_last),

                                                    .ibp_wr_done(slv_o_npu_cfg_axi_ibp_wr_done),
                                                    .ibp_wr_excl_done(slv_o_npu_cfg_axi_ibp_wr_excl_done),
                                                    .ibp_err_wr(slv_o_npu_cfg_axi_ibp_err_wr),
                                                    .ibp_wr_resp_accept(slv_o_npu_cfg_axi_ibp_wr_resp_accept),
                                                    //extra id signals
                                                    .ibp_cmd_chnl_id({16{1'b0}}),
                                                    .ibp_rd_chnl_id(),
                                                    .ibp_wd_chnl_id({16{1'b0}}),
                                                    .ibp_wrsp_chnl_id(),
                                                    // AXI I/F
                                                    .axi_arvalid(npu_cfg_axi_arvalid),
                                                    .axi_arready(npu_cfg_axi_arready),
                                                    .axi_araddr(npu_cfg_axi_araddr),
                                                    .axi_arburst(npu_cfg_axi_arburst),
                                                    .axi_arsize(npu_cfg_axi_arsize),
                                                    .axi_arlen(npu_cfg_axi_arlen),
                                                    .axi_arcache(npu_cfg_axi_arcache),
                                                    .axi_arprot(npu_cfg_axi_arprot),
                                                    .axi_arlock(npu_cfg_axi_arlock_temp),
                                                    .axi_arid(npu_cfg_axi_arid),
                                                    .axi_awvalid(npu_cfg_axi_awvalid),
                                                    .axi_awready(npu_cfg_axi_awready),
                                                    .axi_awaddr(npu_cfg_axi_awaddr),
                                                    .axi_awcache(npu_cfg_axi_awcache),
                                                    .axi_awprot(npu_cfg_axi_awprot),
                                                    .axi_awlock(npu_cfg_axi_awlock_temp),
                                                    .axi_awburst(npu_cfg_axi_awburst),
                                                    .axi_awsize(npu_cfg_axi_awsize),
                                                    .axi_awlen(npu_cfg_axi_awlen),
                                                    .axi_awid(npu_cfg_axi_awid),
                                                    .axi_rvalid(npu_cfg_axi_rvalid),
                                                    .axi_rready(npu_cfg_axi_rready),
                                                    .axi_rdata(npu_cfg_axi_rdata),
                                                    .axi_rresp(npu_cfg_axi_rresp),
                                                    .axi_rlast(npu_cfg_axi_rlast),
                                                    .axi_rid(npu_cfg_axi_rid),
                                                    .axi_wvalid(npu_cfg_axi_wvalid),
                                                    .axi_wready(npu_cfg_axi_wready),
                                                    .axi_wdata(npu_cfg_axi_wdata),
                                                    .axi_wstrb(npu_cfg_axi_wstrb),
                                                    .axi_wlast(npu_cfg_axi_wlast),
                                                    .axi_wid(),
                                                    .axi_bid(npu_cfg_axi_bid),
                                                    .axi_bvalid(npu_cfg_axi_bvalid),
                                                    .axi_bready(npu_cfg_axi_bready),
                                                    .axi_bresp(npu_cfg_axi_bresp));



wire [1:0]arcsync_axi_arlock_temp;
wire [1:0]arcsync_axi_awlock_temp;
assign arcsync_axi_arlock = arcsync_axi_arlock_temp[0];
assign arcsync_axi_awlock = arcsync_axi_awlock_temp[0];

    alb_mss_fab_ibp2axi #(
                          .CHNL_FIFO_DEPTH(2),
                          .ID_W(16),
                          .ADDR_W(40),
                          .DATA_W(64)) u_arcsync_axi_prot_inst(
                                                    .clk(clk),
                                                    .bus_clk_en(1'b1),
                                                    .rst_a(~rst_b),
                                                    //IBP I/F
                                                    .ibp_cmd_user(1'b0),
                                                    .axi_aruser(),
                                                    .axi_awuser(),
                                                    .ibp_cmd_valid(slv_o_arcsync_axi_ibp_cmd_valid),
                                                    .ibp_cmd_accept(slv_o_arcsync_axi_ibp_cmd_accept),
                                                    .ibp_cmd_read(slv_o_arcsync_axi_ibp_cmd_read),
                                                    .ibp_cmd_addr(slv_o_arcsync_axi_ibp_cmd_addr[40-1:0]),
                                                    .ibp_cmd_wrap(slv_o_arcsync_axi_ibp_cmd_wrap),
                                                    .ibp_cmd_data_size(slv_o_arcsync_axi_ibp_cmd_data_size),
                                                    .ibp_cmd_burst_size(slv_o_arcsync_axi_ibp_cmd_burst_size),
                                                    .ibp_cmd_prot(slv_o_arcsync_axi_ibp_cmd_prot),
                                                    .ibp_cmd_cache(slv_o_arcsync_axi_ibp_cmd_cache),
                                                    .ibp_cmd_lock(slv_o_arcsync_axi_ibp_cmd_lock),
                                                    .ibp_cmd_excl(slv_o_arcsync_axi_ibp_cmd_excl),

                                                    .ibp_rd_valid(slv_o_arcsync_axi_ibp_rd_valid),
                                                    .ibp_rd_accept(slv_o_arcsync_axi_ibp_rd_accept),
                                                    .ibp_rd_data(slv_o_arcsync_axi_ibp_rd_data),
                                                    .ibp_err_rd(slv_o_arcsync_axi_ibp_err_rd),
                                                    .ibp_rd_last(slv_o_arcsync_axi_ibp_rd_last),
                                                    .ibp_rd_excl_ok(slv_o_arcsync_axi_ibp_rd_excl_ok),

                                                    .ibp_wr_valid(slv_o_arcsync_axi_ibp_wr_valid),
                                                    .ibp_wr_accept(slv_o_arcsync_axi_ibp_wr_accept),
                                                    .ibp_wr_data(slv_o_arcsync_axi_ibp_wr_data),
                                                    .ibp_wr_mask(slv_o_arcsync_axi_ibp_wr_mask),
                                                    .ibp_wr_last(slv_o_arcsync_axi_ibp_wr_last),

                                                    .ibp_wr_done(slv_o_arcsync_axi_ibp_wr_done),
                                                    .ibp_wr_excl_done(slv_o_arcsync_axi_ibp_wr_excl_done),
                                                    .ibp_err_wr(slv_o_arcsync_axi_ibp_err_wr),
                                                    .ibp_wr_resp_accept(slv_o_arcsync_axi_ibp_wr_resp_accept),
                                                    //extra id signals
                                                    .ibp_cmd_chnl_id({16{1'b0}}),
                                                    .ibp_rd_chnl_id(),
                                                    .ibp_wd_chnl_id({16{1'b0}}),
                                                    .ibp_wrsp_chnl_id(),
                                                    // AXI I/F
                                                    .axi_arvalid(arcsync_axi_arvalid),
                                                    .axi_arready(arcsync_axi_arready),
                                                    .axi_araddr(arcsync_axi_araddr),
                                                    .axi_arburst(arcsync_axi_arburst),
                                                    .axi_arsize(arcsync_axi_arsize),
                                                    .axi_arlen(arcsync_axi_arlen),
                                                    .axi_arcache(arcsync_axi_arcache),
                                                    .axi_arprot(arcsync_axi_arprot),
                                                    .axi_arlock(arcsync_axi_arlock_temp),
                                                    .axi_arid(arcsync_axi_arid),
                                                    .axi_awvalid(arcsync_axi_awvalid),
                                                    .axi_awready(arcsync_axi_awready),
                                                    .axi_awaddr(arcsync_axi_awaddr),
                                                    .axi_awcache(arcsync_axi_awcache),
                                                    .axi_awprot(arcsync_axi_awprot),
                                                    .axi_awlock(arcsync_axi_awlock_temp),
                                                    .axi_awburst(arcsync_axi_awburst),
                                                    .axi_awsize(arcsync_axi_awsize),
                                                    .axi_awlen(arcsync_axi_awlen),
                                                    .axi_awid(arcsync_axi_awid),
                                                    .axi_rvalid(arcsync_axi_rvalid),
                                                    .axi_rready(arcsync_axi_rready),
                                                    .axi_rdata(arcsync_axi_rdata),
                                                    .axi_rresp(arcsync_axi_rresp),
                                                    .axi_rlast(arcsync_axi_rlast),
                                                    .axi_rid(arcsync_axi_rid),
                                                    .axi_wvalid(arcsync_axi_wvalid),
                                                    .axi_wready(arcsync_axi_wready),
                                                    .axi_wdata(arcsync_axi_wdata),
                                                    .axi_wstrb(arcsync_axi_wstrb),
                                                    .axi_wlast(arcsync_axi_wlast),
                                                    .axi_wid(),
                                                    .axi_bid(arcsync_axi_bid),
                                                    .axi_bvalid(arcsync_axi_bvalid),
                                                    .axi_bready(arcsync_axi_bready),
                                                    .axi_bresp(arcsync_axi_bresp));



    assign mss_mem_cmd_valid = slv_o_mss_mem_ibp_cmd_valid;
    assign mss_mem_cmd_read  = slv_o_mss_mem_ibp_cmd_read;
    assign mss_mem_cmd_addr  = slv_o_mss_mem_ibp_cmd_addr[32-1:0];
    assign mss_mem_cmd_wrap  = slv_o_mss_mem_ibp_cmd_wrap;
    assign mss_mem_cmd_data_size = slv_o_mss_mem_ibp_cmd_data_size;
    assign mss_mem_cmd_burst_size = slv_o_mss_mem_ibp_cmd_burst_size;
    assign mss_mem_cmd_lock  = slv_o_mss_mem_ibp_cmd_lock;
    assign mss_mem_cmd_excl  = slv_o_mss_mem_ibp_cmd_excl;
    assign mss_mem_cmd_prot  = slv_o_mss_mem_ibp_cmd_prot;
    assign mss_mem_cmd_cache = slv_o_mss_mem_ibp_cmd_cache;
    assign mss_mem_cmd_region = slv_o_mss_mem_ibp_cmd_region;
    assign mss_mem_cmd_id    = slv_o_mss_mem_ibp_cmd_addr[32+8-1:32];
    assign mss_mem_cmd_user  = slv_o_mss_mem_ibp_cmd_addr[41-1:32+8];

    assign mss_mem_rd_accept = slv_o_mss_mem_ibp_rd_accept;

    assign mss_mem_wr_valid  = slv_o_mss_mem_ibp_wr_valid;
    assign mss_mem_wr_data   = slv_o_mss_mem_ibp_wr_data;
    assign mss_mem_wr_mask   = slv_o_mss_mem_ibp_wr_mask;
    assign mss_mem_wr_last   = slv_o_mss_mem_ibp_wr_last;

    assign mss_mem_wr_resp_accept = slv_o_mss_mem_ibp_wr_resp_accept;

    assign slv_o_mss_mem_ibp_cmd_accept = mss_mem_cmd_accept;
    assign slv_o_mss_mem_ibp_rd_valid  = mss_mem_rd_valid;
    assign slv_o_mss_mem_ibp_rd_excl_ok = mss_mem_rd_excl_ok;
    assign slv_o_mss_mem_ibp_rd_data   = mss_mem_rd_data;
    assign slv_o_mss_mem_ibp_err_rd    = mss_mem_err_rd;
    assign slv_o_mss_mem_ibp_rd_last   = mss_mem_rd_last;
    assign slv_o_mss_mem_ibp_wr_accept = mss_mem_wr_accept;
    assign slv_o_mss_mem_ibp_wr_done   = mss_mem_wr_done;
    assign slv_o_mss_mem_ibp_wr_excl_done = mss_mem_wr_excl_done;
    assign slv_o_mss_mem_ibp_err_wr    = mss_mem_err_wr;

    // output system address base signal

endmodule // alb_mss_fab_bus
