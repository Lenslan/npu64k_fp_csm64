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


`include "npu_defines.v"
`include "arcsync_defines.v"

module core_sys_stub
  import npu_types::*;
(
  // Cluster 0
  //    cl_num_core = 18
  //    cl_type     = 0
  //    cl_pfx      = 
  //    cl_itf_only = 0

  // --------------------------------------------------------------------------
  // NPX
  // --------------------------------------------------------------------------
  //-NPU CL0 AXI msater interface to NoC itf=0
  input logic  [32-1:0]      npu_mst1_axi_arsid,
  input logic  [32-1:0]      npu_mst1_axi_arssid,
  input logic  [32-1:0]      npu_mst1_axi_awsid,
  input logic  [32-1:0]      npu_mst1_axi_awssid,
  input logic  [32-1:0]      npu_mst2_axi_arsid,
  input logic  [32-1:0]      npu_mst2_axi_arssid,
  input logic  [32-1:0]      npu_mst2_axi_awsid,
  input logic  [32-1:0]      npu_mst2_axi_awssid,
  input logic  [32-1:0]      npu_mst3_axi_arsid,
  input logic  [32-1:0]      npu_mst3_axi_arssid,
  input logic  [32-1:0]      npu_mst3_axi_awsid,
  input logic  [32-1:0]      npu_mst3_axi_awssid,
  input logic  [32-1:0]      npu_mst4_axi_arsid,
  input logic  [32-1:0]      npu_mst4_axi_arssid,
  input logic  [32-1:0]      npu_mst4_axi_awsid,
  input logic  [32-1:0]      npu_mst4_axi_awssid,

  //-NPU CL0 DMI AXI interface from NoC
  //-npu_dmi0_axi


  input logic        sl0_ecc_sbe,
  input logic        sl0_ecc_dbe,
  input logic        sl1_ecc_sbe,
  input logic        sl1_ecc_dbe,
  input logic        sl2_ecc_sbe,
  input logic        sl2_ecc_dbe,
  input logic        sl3_ecc_sbe,
  input logic        sl3_ecc_dbe,
  input logic        sl4_ecc_sbe,
  input logic        sl4_ecc_dbe,
  input logic        sl5_ecc_sbe,
  input logic        sl5_ecc_dbe,
  input logic        sl6_ecc_sbe,
  input logic        sl6_ecc_dbe,
  input logic        sl7_ecc_sbe,
  input logic        sl7_ecc_dbe,
  input logic        sl8_ecc_sbe,
  input logic        sl8_ecc_dbe,
  input logic        sl9_ecc_sbe,
  input logic        sl9_ecc_dbe,
  input logic        sl10_ecc_sbe,
  input logic        sl10_ecc_dbe,
  input logic        sl11_ecc_sbe,
  input logic        sl11_ecc_dbe,
  input logic        sl12_ecc_sbe,
  input logic        sl12_ecc_dbe,
  input logic        sl13_ecc_sbe,
  input logic        sl13_ecc_dbe,
  input logic        sl14_ecc_sbe,
  input logic        sl14_ecc_dbe,
  input logic        sl15_ecc_sbe,
  input logic        sl15_ecc_dbe,
  input logic        grp0_scm_dbank_sbe,
  input logic        grp0_scm_dbank_dbe,
  input logic        grp1_scm_dbank_sbe,
  input logic        grp1_scm_dbank_dbe,
  input logic        grp2_scm_dbank_sbe,
  input logic        grp2_scm_dbank_dbe,
  input logic        grp3_scm_dbank_sbe,
  input logic        grp3_scm_dbank_dbe,
  input logic        nl2arc0_ecc_sbe,
  input logic        nl2arc0_ecc_dbe,
  input logic        nl2arc1_ecc_sbe,
  input logic        nl2arc1_ecc_dbe,



  // Cluster 1
  //    cl_num_core = 4
  //    cl_type     = 1
  //    cl_pfx      = v0
  //    cl_itf_only = 1


  // --------------------------------------------------------------------------
  // VPX
  // --------------------------------------------------------------------------



  // Cluster 2
  //    cl_num_core = 1
  //    cl_type     = 2
  //    cl_pfx      = h0
  //    cl_itf_only = 1



  // --------------------------------------------------------------------------
  // Host
  // --------------------------------------------------------------------------
  //-Host AXI interface to npu system
  //aximst(1/*idw*/,32/*aw*/,64/*dw*/,1/*argw*/,1/*awgw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/,0/*awcpl*/, host_axi_/*pref*/)
  // read command channel
  output logic                        host_axi_arvalid, // read command valid
  input  logic                        host_axi_arready, // read command accept
  output logic          [1-1:0]  host_axi_arid,    // read command ID
  output logic          [40-1:0]   host_axi_araddr  ,      // read command
  output logic          [3:0]         host_axi_arcache ,      // read command
  output logic          [2:0]         host_axi_arprot  ,      // read command
  output logic          [1-1:0]         host_axi_arlock  ,      // read command
  output logic          [1:0]         host_axi_arburst ,      // read command
  output logic          [3:0]         host_axi_arlen   ,      // read command
  output logic          [2:0]         host_axi_arsize  ,      // read command
  // read data channel
  input  logic                        host_axi_rvalid,  // read data valid
  output logic                        host_axi_rready,  // read data accept
  input  logic          [1-1:0]  host_axi_rid,     // read data id
  input  logic          [64-1:0]   host_axi_rdata,   // read data
  input  logic          [1:0]         host_axi_rresp,   // read response
  input  logic                        host_axi_rlast,   // read last
  // write command channel
  output logic                        host_axi_awvalid, // write command valid
  input  logic                        host_axi_awready, // write command accept
  output logic          [1-1:0]  host_axi_awid,    // write command ID
  output logic          [40-1:0]   host_axi_awaddr  ,      // read command
  output logic          [3:0]         host_axi_awcache ,      // read command
  output logic          [2:0]         host_axi_awprot  ,      // read command
  output logic          [1-1:0]         host_axi_awlock  ,      // read command
  output logic          [1:0]         host_axi_awburst ,      // read command
  output logic          [3:0]         host_axi_awlen   ,      // read command
  output logic          [2:0]         host_axi_awsize  ,      // read command
  // write data channel
  output logic                        host_axi_wvalid,  // write data valid
  input  logic                        host_axi_wready,  // write data accept
  output logic          [64-1:0]   host_axi_wdata,   // write data
  output logic          [64/8-1:0] host_axi_wstrb,   // write data strobe
  output logic                        host_axi_wlast,   // write data last
  // write response channel
  input  logic                        host_axi_bvalid,  // write response valid
  output logic                        host_axi_bready,  // write response accept
  input  logic          [1-1:0]  host_axi_bid,     // write response id
  input  logic          [1:0]         host_axi_bresp,    // write response


  //-ARCSync
  //--DMI AXI interface from NoC

  input logic mss_clk,
  input logic arcsync_clk,
  input logic arcsync_rst_a


);

  //-NPU AXI msater interface to NoC
  //-npu_mst0_axi
  //-NPU AXI msater interface to NoC
  //-npu_mst1_axi
  //-NPU AXI msater interface to NoC
  //-npu_mst2_axi
  //-NPU AXI msater interface to NoC
  //-npu_mst3_axi
  //-NPU AXI msater interface to NoC
  //-npu_mst4_axi

  //-NPU DMI AXI interface from NoC
  //-npu_dmi0_axi

















  initial
    begin
  //-Host AXI interface to npu system
    host_axi_arvalid = '0;
    host_axi_arid    = '0;
    host_axi_araddr  = '0;
    host_axi_arcache = '0;
    host_axi_arprot  = 3'b1; // privileged access
    host_axi_arlock  = '0;
    host_axi_arburst = '0;
    host_axi_arlen   = '0;
    host_axi_arsize  = '0;
    host_axi_rready  = '0;
    host_axi_awvalid = '0;
    host_axi_awid    = '0;
    host_axi_awaddr  = '0;
    host_axi_awcache = '0;
    host_axi_awprot  = 3'b1; // privileged access
    host_axi_awlock  = '0;
    host_axi_awburst = '0;
    host_axi_awlen   = '0;
    host_axi_awsize  = '0;
    host_axi_wvalid  = '0;
    host_axi_wdata   = '0;
    host_axi_wstrb   = '0;
    host_axi_wlast   = '0;
    host_axi_bready  = '0;
    end


  //-ARCSync DMI


endmodule
