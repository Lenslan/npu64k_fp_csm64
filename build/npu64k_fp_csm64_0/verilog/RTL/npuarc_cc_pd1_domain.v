// Library ARCv2CC-3.2.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2014 Synopsys, Inc. All rights reserved.
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
//   ####    ####           #####   #####    ##             #####    ####   #    #
//  #    #  #    #          #    #  #    #  # #             #    #  #    #  ##  ##
//  #       #               #    #  #    #    #             #    #  #    #  # ## #
//  #       #               #####   #    #    #             #    #  #    #  #    #
//  #    #  #    #          #       #    #    #             #    #  #    #  #    #
//   ####    ####  #######  #       #####   #####  #######  #####    ####   #    #
//
// ===========================================================================
//
// Description:
//  Verilog source of the Cluster pd1_domain top module.
//
// ===========================================================================

// Set simulation timescale
//
`include   "const.def"

// Macro definitions for the top-level Verilog files.
//
`include   "npuarc_cc_exported_defines.v"
`include   "npuarc_cc_defines.v"








`include   "npuarc_biu_defines.v"









module npuarc_cc_pd1_domain
(


    output          biu_l1_clk_enable,
    input           biu_accept_en,
    input           biu_clk,

    output          cc_aux_l1_clk_enable,
    input           cc_aux_accept_en,





// leda NTL_CON13C off
// LMD: non driving port
// LJ: some IBP signals are not needed, but are supplied as inputs by default
// leda NTL_CON37 off
// LMD:  Signal/Net must read from the input por
// LJ: some IBP signals are not needed, but are supplied as inputs by default

  ////////// Core 0 interface signals ////////////////////////////////////////
  //



  //////////// IFU IBP interface for core 0 //////////////////////////////////
  //
  input  wire                     ifu_ibus_cmd_valid,
  output wire                     ifu_ibus_cmd_accept,
  input  wire [39:0]      ifu_ibus_cmd_addr,
  input  wire                     ifu_ibus_cmd_wrap,
  input  wire [3:0]               ifu_ibus_cmd_cache,
  input  wire [3:0]               ifu_ibus_cmd_burst_size,
  input  wire [1:0]               ifu_ibus_cmd_prot,
  //
  output wire                     ifu_ibus_rd_valid,
  output wire                     ifu_ibus_err_rd,
  input  wire                     ifu_ibus_rd_accept,
  output wire [`npuarc_CC_BUS_RANGE]     ifu_ibus_rd_data,
  output wire                     ifu_ibus_rd_last,

  //////////// LQWQ IBP interface for core 0 ///////////////////////////////////
  //
  input  wire                     lqwq_mem_cmd_valid,
  input  wire                     lqwq_mem_cmd_cache,
  output wire                     lqwq_mem_cmd_accept,
  input  wire                     lqwq_mem_cmd_read,
  input  wire [39:0]      lqwq_mem_cmd_addr,
  input  wire                     lqwq_mem_cmd_burst_size,
  input  wire [2:0]               lqwq_mem_cmd_data_size,
  input  wire                     lqwq_mem_cmd_lock,
  input  wire                     lqwq_mem_cmd_excl,
  input  wire [1:0]               lqwq_mem_cmd_prot,
  //
  output wire                     lqwq_mem_rd_valid,
  output wire                     lqwq_mem_err_rd,
  output wire                     lqwq_mem_rd_excl_ok,
  input  wire                     lqwq_mem_rd_accept,
  output wire [`npuarc_CC_BUS_RANGE]     lqwq_mem_rd_data,
  output wire                     lqwq_mem_rd_last,

  input  wire                     lqwq_mem_wr_valid,
  output wire                     lqwq_mem_wr_accept,
  input  wire [`npuarc_CC_BUS_RANGE]     lqwq_mem_wr_data,
  input  wire [`npuarc_CC_MASK_RANGE]    lqwq_mem_wr_mask,
  input  wire                     lqwq_mem_wr_last,
  output wire                     lqwq_mem_wr_done,
  output wire                     lqwq_mem_wr_excl_done,
  output wire                     lqwq_mem_err_wr,
  input  wire                     lqwq_mem_wr_resp_accept,

  ////////// RF IBP interface for core 0 /////////////////////////////////////
  //
  input  wire                        rf_cmd_valid,
  output wire                        rf_cmd_accept,
  input  wire                        rf_cmd_read,
  input  wire [39:0]         rf_cmd_addr,
  input  wire [1:0]                  rf_cmd_prot,
  input  wire                        rf_cmd_wrap,
  input  wire [3:0]                  rf_cmd_burst_size,
  input  wire [3:0]                  rf_cmd_cache,
  input  wire                        rf_cmd_excl,
  input  wire                        rf_cmd_lock,
  input  wire [2:0]                  rf_cmd_data_size,
  //
  output wire                        rf_rd_valid,
  output wire                        rf_rd_last,
  output wire                        rf_err_rd,
  output wire [127:0]  rf_rd_data,
  input  wire                        rf_rd_accept,

  ////////// CB IBP interface for core 0 /////////////////////////////////////
  //
  input  wire                        cb_cmd_valid,
  output wire                        cb_cmd_accept,
  input  wire                        cb_cmd_read,
  input  wire [39:0]         cb_cmd_addr,
  input  wire [1:0]                  cb_cmd_prot,
  input  wire                        cb_cmd_wrap,
  input  wire [3:0]                  cb_cmd_burst_size,
  input  wire [3:0]                  cb_cmd_cache,
  input  wire                        cb_cmd_excl,
  input  wire                        cb_cmd_lock,
  input  wire [2:0]                  cb_cmd_data_size,
  //
  input  wire                        cb_wr_valid,
  output wire                        cb_wr_accept,
  input  wire                        cb_wr_last,
  input  wire [127:0]  cb_wr_data,
  input  wire [15:0] cb_wr_mask,
  output wire                        cb_wr_done,
  output wire                        cb_err_wr,
  input  wire                        cb_wr_resp_accept,


  ////////// dccm_dmi_ IBP port for core 0 ///////////////////////////////////////
  //
  //         dccm_dmi_ port Command channel for core 0
  //
  output wire                     dccm_dmi_cmd_valid,
  input  wire                     dccm_dmi_cmd_accept,
  output wire                     dccm_dmi_cmd_read,
  output wire [24-1:3]   dccm_dmi_cmd_addr,
  //
  //         dccm_dmi_ port Read Data channel for core 0
  //
  input  wire                     dccm_dmi_rd_valid,
  output wire                     dccm_dmi_rd_accept,
  input  wire                     dccm_dmi_err_rd,
  input  wire [`npuarc_CC_DMI_BUS_RANGE] dccm_dmi_rd_data,
  //
  //         dccm_dmi_ port Write Data channel for core 0
  //
  output wire                     dccm_dmi_wr_valid,
  input  wire                     dccm_dmi_wr_accept,
  output wire [`npuarc_CC_DMI_BUS_RANGE] dccm_dmi_wr_data,
  output wire [`npuarc_CC_DMI_MASK_RANGE]dccm_dmi_wr_mask,
  //
  //         dccm_dmi_ port Write Response channel for core 0
  //
  input  wire                     dccm_dmi_wr_done,
  input  wire                     dccm_dmi_err_wr,

  ////////// Auxiliary interface to the cc_aux module for core 0 /////////////
  //
  // Read and Status Channel from core 
  input  wire                       aux_rs_valid,
  input  wire [`npuarc_CC_AUX_ADDR_RANGE]  aux_rs_addr,
  input  wire [`npuarc_CC_AUX_RGN_RANGE]   aux_rs_region,
  input  wire                       aux_rs_read,
  input  wire                       aux_rs_write,
  //
  output wire [`npuarc_CC_AUX_STAT_RANGE]  aux_rs_status,
  output wire [`npuarc_CC_AUX_DATA_RANGE]  aux_rs_data,
  output wire                       aux_rs_accept,
  //
  // Write Channel from core 
  input  wire                       aux_wr_valid,
  input  wire [`npuarc_CC_AUX_ADDR_RANGE]  aux_wr_addr,
  input  wire [`npuarc_CC_AUX_RGN_RANGE]   aux_wr_region,
  input  wire [`npuarc_CC_AUX_DATA_RANGE]  aux_wr_data,
  //
  output wire                       aux_wr_allow,
  //
  // Commit Channel from core 
  input  wire                       aux_cm_phase,
  input  wire                       aux_cm_valid,










  ////////// External AXI memory interface port 0 ////////////////////////////
  //
  output wire [4-1:0]   cbu_axi_arid,
  input  wire [4-1:0]   cbu_axi_rid,
  output wire                           cbu_axi_arvalid,
  input  wire                           cbu_axi_arready,
  output wire [39:0]            cbu_axi_araddr,
  output wire [3:0]                     cbu_axi_arcache,
  output wire [2:0]                     cbu_axi_arprot,
  output wire [1:0]                     cbu_axi_arburst,
  output wire [3:0]                     cbu_axi_arlen,
  input  wire                           cbu_axi_rvalid,
  output wire                           cbu_axi_rready,
  input  wire [64-1:0               ]  cbu_axi_rdata,
  input  wire [1:0]                     cbu_axi_rresp,
  input  wire                           cbu_axi_rlast,
  output wire [2:0]                     cbu_axi_arsize,
  output wire [1:0]                     cbu_axi_arlock,
  output wire [4-1:0]   cbu_axi_awid,
  output wire [4-1:0]   cbu_axi_wid,
  input  wire [4-1:0]   cbu_axi_bid,
  output wire                           cbu_axi_awvalid,
  input  wire                           cbu_axi_awready,
  input  wire                           cbu_axi_wready,
  input  wire                           cbu_axi_bvalid,
  input  wire [1:0]                     cbu_axi_bresp,
  output wire [39:0]            cbu_axi_awaddr,
  output wire [3:0]                     cbu_axi_awcache,
  output wire [2:0]                     cbu_axi_awprot,
  output wire [1:0]                     cbu_axi_awlock,
  output wire [1:0]                     cbu_axi_awburst,
  output wire [3:0]                     cbu_axi_awlen,
  output wire [2:0]                     cbu_axi_awsize,
  output wire                           cbu_axi_wvalid,
  output wire [64-1:0               ]  cbu_axi_wdata,
  output wire [(64/8)-1:0           ]  cbu_axi_wstrb,
  output wire                           cbu_axi_wlast,
  output wire                           cbu_axi_bready,








// The interface for sccm_ dmi ports






  //// The AXI bus
  input                                sccm_axi_arvalid,
  output                               sccm_axi_arready,
  input  [16  -1:0]     sccm_axi_arid,
  input  [24-1:0]         sccm_axi_araddr,
  input  [2    -1:0]     sccm_axi_arregion,
  input  [2-1:0]     sccm_axi_arburst,
  input  [4-1:0]     sccm_axi_arlen,
  input  [3-1:0]     sccm_axi_arsize,

  output                               sccm_axi_rvalid,
  input                                sccm_axi_rready,
  output [16  -1:0]     sccm_axi_rid,
  output [64-1:0]         sccm_axi_rdata,
  output [2-1:0]     sccm_axi_rresp,
  output                               sccm_axi_rlast,

  input                                sccm_axi_awvalid,
  output                               sccm_axi_awready,
  input  [16  -1:0]     sccm_axi_awid,
  input  [24-1:0]         sccm_axi_awaddr,
  input  [2    -1:0]     sccm_axi_awregion,
  input  [2-1:0]     sccm_axi_awburst,
  input  [4-1:0]     sccm_axi_awlen,
  input  [3-1:0]     sccm_axi_awsize,

  input                                sccm_axi_wvalid,
  output                               sccm_axi_wready,
  input  [64-1:0]         sccm_axi_wdata,
  input  [(64/8)-1:0]     sccm_axi_wstrb,
  input                                sccm_axi_wlast,

  output                               sccm_axi_bvalid,
  input                                sccm_axi_bready,
  output [16  -1:0]     sccm_axi_bid,
  output [2-1:0]     sccm_axi_bresp,









  output                             biu_dmi_clk_en_req,







  output                   biu2pdm_idle,
  output                   biu2pdm_l2c_idle,



  output                              cc_top_cg_en_gaux_cmd_valid,
  input                               cc_top_cg_en_gaux_cmd_accept,
  output [`npuarc_CC_GAUX_CMD_WIDTH-1:0]     cc_top_cg_en_gaux_cmd,
  input                               cc_top_cg_en_gaux_res_valid,
  output                              cc_top_cg_en_gaux_res_accept,
  input  [`npuarc_CC_GAUX_RES_WIDTH-1:0]     cc_top_cg_en_gaux_res_data,
  output                              cc_top_cg_en_gaux_wen_valid,
  output [`npuarc_CC_GAUX_WADDR_WIDTH-1:0]   cc_top_cg_en_gaux_wen_addr,
  output [`npuarc_CC_GAUX_WDATA_WIDTH-1:0]   cc_top_cg_en_gaux_wen_data,
  output                              cc_gaux_idle,

  ////////// Bus clock/clock enable inputs /////////////////////////////////////////
  //
  input                             mbus_clk_en,
  input                             dbus_clk_en,




// spyglass disable_block W240
// SMD: Input declared but not read
// SJ: STU not use this signal
  input                          cc_misc_clk,
// spyglass enable_block W240






  ////////// General input signals ///////////////////////////////////////////
  //
  // spyglass disable_block W240
  // SMD: declared but not read
  // SJ: do not care this wrn
  input                             cc_pd1_rst_a,
  input                             cc_pd1_rst,
  input                             cc_pd1_clk,


  // spyglass enable_block W240
    input  wire [7:0]                 clusternum, // for cluster_id register.
  output wire [7:0]                 core_clusternum,


  input                             cc_biu_l1_cg_dis,
  input                             cc_top_l1_cg_dis,


  // spyglass disable_block W240
  // SMD: declared but not read
  // SJ: do not care this wrn
 //this is ungate clock for monitor idle/busy status register using
  input                             clk,
  // spyglass enable_block W240



  // spyglass disable_block W240
  // SMD: declared but not read
  // SJ: do not care this wrn
  input  wire                       test_mode
  // spyglass enable_block W240


// leda NTL_CON13C on
// leda NTL_CON37 on
);



// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning

// Communicate the cluster number to core 0 in the cluster.
assign core_clusternum   = clusternum;



//========================== Wire declarations ===============================




  wire [`npuarc_CC_GAUX_CORE_ID_RANGE]     cc_top_cg_en_gaux_wen_core_id;





//==================== Component instantiations ==============================







// vccm_clk_en_req driven by stu and vdmi



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the Bus Interface Unit (BIU)                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: low order bits (0-2) are unused in output port
  wire [24-1:0]   dccm_dmi_cmd_addr_full;
  assign dccm_dmi_cmd_addr = dccm_dmi_cmd_addr_full[24-1:3];
// leda NTL_CON13A on





// leda WV951025 off
// LMD: Unconnected port is found
// LJ: some IBP signals are intentionally unused
// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// LMD: Module instantiation is not fully bound
// LJ: some IBP output ports are intentionally unused


npuarc_biu_top u_biu_top (







  //////////// IFU IBP interface from core 0 ////////////////////////////////
  //
  .ifu_ibp_cmd_valid          (ifu_ibus_cmd_valid),
  .ifu_ibp_cmd_accept         (ifu_ibus_cmd_accept),
  .ifu_ibp_cmd_read           (1'b1),    // always reads, never writes
  .ifu_ibp_cmd_addr           (ifu_ibus_cmd_addr),
  .ifu_ibp_cmd_wrap           (ifu_ibus_cmd_wrap),
  .ifu_ibp_cmd_data_size      (3'b011),  // always 64 bits
  .ifu_ibp_cmd_burst_size     (ifu_ibus_cmd_burst_size),
  .ifu_ibp_cmd_prot           (ifu_ibus_cmd_prot),
  .ifu_ibp_cmd_cache          (ifu_ibus_cmd_cache),
  .ifu_ibp_cmd_lock           (1'b0),
  .ifu_ibp_cmd_excl           (1'b0),
  //
// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
  .ifu_ibp_rd_valid           (ifu_ibus_rd_valid),
  .ifu_ibp_err_rd             (ifu_ibus_err_rd),
  .ifu_ibp_rd_excl_ok         (),
  .ifu_ibp_rd_accept          (ifu_ibus_rd_accept),
  .ifu_ibp_rd_data            (ifu_ibus_rd_data),
  .ifu_ibp_rd_last            (ifu_ibus_rd_last),
  //
  .ifu_ibp_wr_valid           (1'b0),    // never asserted
  .ifu_ibp_wr_accept          (),
  .ifu_ibp_wr_data            ({`npuarc_CC_BUS_WIDTH{1'b0}}),   // never used
  .ifu_ibp_wr_mask            ({`npuarc_CC_BUS_WIDTH/8{1'b0}}), // never asserted
  .ifu_ibp_wr_last            (1'b0),    // never asserted
  //
  .ifu_ibp_wr_done            (),
  .ifu_ibp_wr_excl_done       (),
  .ifu_ibp_err_wr             (),
  .ifu_ibp_wr_resp_accept     (1'b1),    // always accept
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

  .lqwq_ibp_cmd_valid           (lqwq_mem_cmd_valid),
  .lqwq_ibp_cmd_read            (lqwq_mem_cmd_read),
  .lqwq_ibp_cmd_wrap            (1'b0),    // never wraps
  .lqwq_ibp_cmd_burst_size      ({3'd0, lqwq_mem_cmd_burst_size}),
  .lqwq_ibp_cmd_data_size       (lqwq_mem_cmd_data_size),
  .lqwq_ibp_cmd_lock            (lqwq_mem_cmd_lock),
  .lqwq_ibp_cmd_excl            (lqwq_mem_cmd_excl),
  .lqwq_ibp_cmd_addr            (lqwq_mem_cmd_addr),
  .lqwq_ibp_cmd_prot            (lqwq_mem_cmd_prot),
  .lqwq_ibp_cmd_accept          (lqwq_mem_cmd_accept),
  .lqwq_ibp_cmd_cache           ({lqwq_mem_cmd_cache, 3'b000}),

  .lqwq_ibp_rd_valid            (lqwq_mem_rd_valid),
  .lqwq_ibp_rd_data             (lqwq_mem_rd_data),
  .lqwq_ibp_rd_last             (lqwq_mem_rd_last),
  .lqwq_ibp_err_rd              (lqwq_mem_err_rd),
  .lqwq_ibp_rd_excl_ok          (lqwq_mem_rd_excl_ok),
  .lqwq_ibp_rd_accept           (lqwq_mem_rd_accept),

  .lqwq_ibp_wr_valid            (lqwq_mem_wr_valid),
  .lqwq_ibp_wr_data             (lqwq_mem_wr_data),
  .lqwq_ibp_wr_mask             (lqwq_mem_wr_mask),
  .lqwq_ibp_wr_last             (lqwq_mem_wr_last),
  .lqwq_ibp_wr_accept           (lqwq_mem_wr_accept),
  //
  .lqwq_ibp_wr_done             (lqwq_mem_wr_done),
  .lqwq_ibp_err_wr              (lqwq_mem_err_wr),
  .lqwq_ibp_wr_excl_done        (lqwq_mem_wr_excl_done),
  .lqwq_ibp_wr_resp_accept      (lqwq_mem_wr_resp_accept),




  ////////// Separate refill+copyback IBPs for core 0 to BIU /////////////////
  //
  // Data-cache refill IBP direct from core 0 to the BIU (read only)
  .dmu_rbu_ibp_cmd_valid      (rf_cmd_valid),
  .dmu_rbu_ibp_cmd_accept     (rf_cmd_accept),
  .dmu_rbu_ibp_cmd_read       (rf_cmd_read),
  .dmu_rbu_ibp_cmd_addr       (rf_cmd_addr),
  .dmu_rbu_ibp_cmd_wrap       (rf_cmd_wrap),
  .dmu_rbu_ibp_cmd_data_size  (rf_cmd_data_size),
  .dmu_rbu_ibp_cmd_burst_size (rf_cmd_burst_size),
  .dmu_rbu_ibp_cmd_prot       (rf_cmd_prot),
  .dmu_rbu_ibp_cmd_cache      (rf_cmd_cache),
  .dmu_rbu_ibp_cmd_lock       (rf_cmd_lock),
  .dmu_rbu_ibp_cmd_excl       (rf_cmd_excl),

// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
  .dmu_rbu_ibp_rd_valid       (rf_rd_valid),
  .dmu_rbu_ibp_rd_accept      (rf_rd_accept),
  .dmu_rbu_ibp_err_rd         (rf_err_rd),
  .dmu_rbu_ibp_rd_excl_ok     (),
  .dmu_rbu_ibp_rd_data        (rf_rd_data),
  .dmu_rbu_ibp_rd_last        (rf_rd_last),

  .dmu_rbu_ibp_wr_valid       (1'b0),  // never assert
  .dmu_rbu_ibp_wr_accept      (),
  .dmu_rbu_ibp_wr_data        (128'd0), // default zeros
  .dmu_rbu_ibp_wr_mask        (16'd0),  // default zeros
  .dmu_rbu_ibp_wr_last        (1'b0),  // never assert

  .dmu_rbu_ibp_wr_done        (),
  .dmu_rbu_ibp_wr_excl_done   (),
  .dmu_rbu_ibp_err_wr         (),
  .dmu_rbu_ibp_wr_resp_accept (1'b0),  // never assert
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b
  //
  // Data-cache copy-back IBP direct from core 0 to the BIU (write-only)
  //
  .dmu_wbu_ibp_cmd_valid      (cb_cmd_valid),
  .dmu_wbu_ibp_cmd_accept     (cb_cmd_accept),
  .dmu_wbu_ibp_cmd_read       (cb_cmd_read),
  .dmu_wbu_ibp_cmd_wrap       (cb_cmd_wrap),
  .dmu_wbu_ibp_cmd_addr       (cb_cmd_addr),
  .dmu_wbu_ibp_cmd_burst_size (cb_cmd_burst_size),
  .dmu_wbu_ibp_cmd_data_size  (cb_cmd_data_size),
  .dmu_wbu_ibp_cmd_lock       (cb_cmd_lock),
  .dmu_wbu_ibp_cmd_excl       (cb_cmd_excl),
  .dmu_wbu_ibp_cmd_prot       (cb_cmd_prot),
  .dmu_wbu_ibp_cmd_cache      (cb_cmd_cache),

// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
  .dmu_wbu_ibp_rd_valid       (),
  .dmu_wbu_ibp_rd_accept      (1'b0),  // never assert
  .dmu_wbu_ibp_err_rd         (),
  .dmu_wbu_ibp_rd_excl_ok     (),
  .dmu_wbu_ibp_rd_data        (),
  .dmu_wbu_ibp_rd_last        (),

  .dmu_wbu_ibp_wr_valid       (cb_wr_valid),
  .dmu_wbu_ibp_wr_accept      (cb_wr_accept),
  .dmu_wbu_ibp_wr_data        (cb_wr_data),
  .dmu_wbu_ibp_wr_mask        (cb_wr_mask),
  .dmu_wbu_ibp_wr_last        (cb_wr_last),

  .dmu_wbu_ibp_wr_done        (cb_wr_done),
  .dmu_wbu_ibp_wr_excl_done   (),
  .dmu_wbu_ibp_err_wr         (cb_err_wr),
  .dmu_wbu_ibp_wr_resp_accept (cb_wr_resp_accept),
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b


  ////////// dccm_dmi_ IBP port for core 0 ///////////////////////////////////////
  //
// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
  .dccm_dmi_ibp_cmd_valid      (dccm_dmi_cmd_valid),
  .dccm_dmi_ibp_cmd_accept     (dccm_dmi_cmd_accept),
  .dccm_dmi_ibp_cmd_read       (dccm_dmi_cmd_read),
  .dccm_dmi_ibp_cmd_addr       (dccm_dmi_cmd_addr_full),
  .dccm_dmi_ibp_cmd_wrap       (),
  .dccm_dmi_ibp_cmd_burst_size (),
  .dccm_dmi_ibp_cmd_data_size  (),
  .dccm_dmi_ibp_cmd_lock       (),
  .dccm_dmi_ibp_cmd_excl       (),
  .dccm_dmi_ibp_cmd_prot       (),
  .dccm_dmi_ibp_cmd_cache      (),

  //
  .dccm_dmi_ibp_rd_valid     (dccm_dmi_rd_valid),
  .dccm_dmi_ibp_rd_accept    (dccm_dmi_rd_accept),
  .dccm_dmi_ibp_err_rd       (dccm_dmi_err_rd),
  .dccm_dmi_ibp_rd_data      (dccm_dmi_rd_data),
  .dccm_dmi_ibp_rd_excl_ok   (1'b0),
  .dccm_dmi_ibp_rd_last      (1'b1),
  //
  .dccm_dmi_ibp_wr_valid     (dccm_dmi_wr_valid),
  .dccm_dmi_ibp_wr_accept    (dccm_dmi_wr_accept),
  .dccm_dmi_ibp_wr_data      (dccm_dmi_wr_data),
  .dccm_dmi_ibp_wr_mask      (dccm_dmi_wr_mask),
  .dccm_dmi_ibp_wr_last      (),
  //
  .dccm_dmi_ibp_wr_done         (dccm_dmi_wr_done),
  .dccm_dmi_ibp_err_wr          (dccm_dmi_err_wr),
  .dccm_dmi_ibp_wr_excl_done    (1'b0),
  .dccm_dmi_ibp_wr_resp_accept  (),
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b












  ////////// External AXI memory interface port 0 ////////////////////////////
  //
  .cbu_axi_arid               (cbu_axi_arid),
  .cbu_axi_rid                (cbu_axi_rid ),
  .cbu_axi_arvalid            (cbu_axi_arvalid),
  .cbu_axi_arready            (cbu_axi_arready),
  .cbu_axi_araddr             (cbu_axi_araddr),
  .cbu_axi_arcache            (cbu_axi_arcache),
  .cbu_axi_arprot             (cbu_axi_arprot),
  .cbu_axi_arburst            (cbu_axi_arburst),
  .cbu_axi_arlen              (cbu_axi_arlen),
  .cbu_axi_rvalid             (cbu_axi_rvalid),
  .cbu_axi_rready             (cbu_axi_rready),
  .cbu_axi_rdata              (cbu_axi_rdata),
  .cbu_axi_rresp              (cbu_axi_rresp),
  .cbu_axi_rlast              (cbu_axi_rlast),
  .cbu_axi_arsize             (cbu_axi_arsize),
  .cbu_axi_arlock             (cbu_axi_arlock),
  .cbu_axi_awid               (cbu_axi_awid),
  .cbu_axi_wid                (cbu_axi_wid ),
  .cbu_axi_bid                (cbu_axi_bid ),
  .cbu_axi_awvalid            (cbu_axi_awvalid),
  .cbu_axi_awready            (cbu_axi_awready),
  .cbu_axi_awaddr             (cbu_axi_awaddr),
  .cbu_axi_awcache            (cbu_axi_awcache),
  .cbu_axi_awprot             (cbu_axi_awprot),
  .cbu_axi_awlock             (cbu_axi_awlock),
  .cbu_axi_awburst            (cbu_axi_awburst),
  .cbu_axi_awlen              (cbu_axi_awlen),
  .cbu_axi_awsize             (cbu_axi_awsize),
  .cbu_axi_wvalid             (cbu_axi_wvalid),
  .cbu_axi_wready             (cbu_axi_wready),
  .cbu_axi_wdata              (cbu_axi_wdata),
  .cbu_axi_wstrb              (cbu_axi_wstrb),
  .cbu_axi_wlast              (cbu_axi_wlast),
  .cbu_axi_bvalid             (cbu_axi_bvalid),
  .cbu_axi_bready             (cbu_axi_bready),
  .cbu_axi_bresp              (cbu_axi_bresp),








/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////
// The interface for sccm_ dmi ports





  //// The AXI bus
  .sccm_axi_arregion   (sccm_axi_arregion),
  .sccm_axi_arid       (sccm_axi_arid    ),
  .sccm_axi_arvalid    (sccm_axi_arvalid ),
  .sccm_axi_arready    (sccm_axi_arready ),
  .sccm_axi_araddr     (sccm_axi_araddr  ),
  .sccm_axi_arburst    (sccm_axi_arburst ),
  .sccm_axi_arlen      (sccm_axi_arlen   ),
  .sccm_axi_arsize     (sccm_axi_arsize  ),
  .sccm_axi_arlock     (2'b0),
  .sccm_axi_arcache    (4'b0),
  .sccm_axi_arprot     (3'b0),

  .sccm_axi_rvalid     (sccm_axi_rvalid  ),
  .sccm_axi_rready     (sccm_axi_rready  ),
  .sccm_axi_rid        (sccm_axi_rid     ),
  .sccm_axi_rdata      (sccm_axi_rdata   ),
  .sccm_axi_rresp      (sccm_axi_rresp   ),
  .sccm_axi_rlast      (sccm_axi_rlast   ),

  .sccm_axi_awvalid    (sccm_axi_awvalid ),
  .sccm_axi_awready    (sccm_axi_awready ),
  .sccm_axi_awid       (sccm_axi_awid    ),
  .sccm_axi_awaddr     (sccm_axi_awaddr  ),
  .sccm_axi_awregion   (sccm_axi_awregion),
  .sccm_axi_awburst    (sccm_axi_awburst ),
  .sccm_axi_awlen      (sccm_axi_awlen   ),
  .sccm_axi_awsize     (sccm_axi_awsize  ),
  .sccm_axi_awlock     (2'b0),
  .sccm_axi_awcache    (4'b0),
  .sccm_axi_awprot     (3'b0),

  .sccm_axi_wvalid     (sccm_axi_wvalid  ),
  .sccm_axi_wready     (sccm_axi_wready  ),
  .sccm_axi_wdata      (sccm_axi_wdata   ),
  .sccm_axi_wstrb      (sccm_axi_wstrb   ),
  .sccm_axi_wlast      (sccm_axi_wlast   ),

  .sccm_axi_bvalid     (sccm_axi_bvalid  ),
  .sccm_axi_bready     (sccm_axi_bready  ),
  .sccm_axi_bid        (sccm_axi_bid     ),
  .sccm_axi_bresp      (sccm_axi_bresp   ),






  .biu2pdm_idle       (biu2pdm_idle    ),
  .biu2pdm_l2c_idle   (biu2pdm_l2c_idle),



  //
  .mbus_clk_en                       (mbus_clk_en),
  .dbus_clk_en                       (dbus_clk_en),

  .biu_dmi_clk_en_req         (biu_dmi_clk_en_req),
  .biu_l1gt_clk_enable        (biu_l1_clk_enable),
  .biu_l1_cg_dis              (cc_biu_l1_cg_dis),
  .biu_accept_en              (biu_accept_en),

  .rst_a                   (cc_pd1_rst_a),
  .nmi_restart_r                 (1'b0),
  .clk_gated               (biu_clk),
  .clk_ungated             (clk),
  .test_mode               (test_mode)
);
// leda WV951025 on
// leda B_1011 on
// spyglass enable_block W287b



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the CC_VCCM_ARBITRATION_UNIT                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////









//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the cc_aux module                                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
npuarc_cc_aux u_cc_aux (


  ////////// Core 0 interface signals ///////////////////////////////////////
  //
  // Read and Status Channel from core 0
  .aux_rs_valid        (aux_rs_valid),
  .aux_rs_addr         (aux_rs_addr),
  .aux_rs_region       (aux_rs_region),
  .aux_rs_read         (aux_rs_read),
  .aux_rs_write        (aux_rs_write),
  //
  .aux_rs_status       (aux_rs_status),
  .aux_rs_data         (aux_rs_data),
  .aux_rs_accept       (aux_rs_accept),
  //
  // Write Channel from core 0
  .aux_wr_valid        (aux_wr_valid),
  .aux_wr_addr         (aux_wr_addr),
  .aux_wr_region       (aux_wr_region),
  .aux_wr_data         (aux_wr_data),
  //
  .aux_wr_allow        (aux_wr_allow),
  //

  // Commit Channel from core 0
  .aux_cm_phase        (aux_cm_phase),
  .aux_cm_valid        (aux_cm_valid),

  ////////// GAUX interface //////////////////////////////////////////////////
  //
  .cc_gaux_idle                (cc_gaux_idle),
  .cc_top_cg_en_gaux_cmd_valid     (cc_top_cg_en_gaux_cmd_valid),
  .cc_top_cg_en_gaux_cmd_accept    (cc_top_cg_en_gaux_cmd_accept),
  .cc_top_cg_en_gaux_cmd           (cc_top_cg_en_gaux_cmd),
  .cc_top_cg_en_gaux_res_valid     (cc_top_cg_en_gaux_res_valid),
  .cc_top_cg_en_gaux_res_accept    (cc_top_cg_en_gaux_res_accept),
  .cc_top_cg_en_gaux_res_data      (cc_top_cg_en_gaux_res_data),
  .cc_top_cg_en_gaux_wen_valid     (cc_top_cg_en_gaux_wen_valid),
  .cc_top_cg_en_gaux_wen_addr      (cc_top_cg_en_gaux_wen_addr),
  .cc_top_cg_en_gaux_wen_data      (cc_top_cg_en_gaux_wen_data),
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
  .cc_top_cg_en_gaux_wen_core_id   (cc_top_cg_en_gaux_wen_core_id),
// spyglass enable_block UnloadedOutTerm-ML

  .cc_aux_l1_clk_enable      (cc_aux_l1_clk_enable),
  .cc_aux_accept_en          (cc_aux_accept_en),
  .cc_top_l1_cg_dis          (cc_top_l1_cg_dis),
  ////////// General input signals ///////////////////////////////////////////
  //
  .rst_a              (cc_pd1_rst           ),
  .nmi_restart_r                   (1'b0),
  .ungated_clk        (clk),
  .clk                (cc_misc_clk           )
  );









// spyglass enable_block W528






endmodule // cc_pd1_domain
