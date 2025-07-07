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
//   ####    ####            #####   ####   #####
//  #    #  #    #             #    #    #  #    #
//  #       #                  #    #    #  #    #
//  #       #                  #    #    #  #####
//  #    #  #    #             #    #    #  #
//   ####    ####  #######     #     ####   #
//
// ===========================================================================
//
// Description:
//  Verilog source of the Coherent Cluster top-level structural module.
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











module npuarc_cc_top
(





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

  output                   cc_idle,




  ////////// Bus clock/clock enable inputs /////////////////////////////////////////
  //
  input                             mbus_clk_en,
  input                             dbus_clk_en,
















  // Clock gating for core 0.
  input                              cpu_clk_enable,
  output                             l1_cg_dis,
  output                             l1_accept_en,
  // @@@ This is a hack to satisfy HIERGEN
  //
  output                             c0clk,


  ///////// NMI CC module signals ///////////////////////////////////////////


  ////////// General input signals ///////////////////////////////////////////
  //
  input  wire                       clk,
  input  wire                       rst_a,
  input  wire [7:0]                 clusternum, // for cluster_id register.
  output wire [7:0]                 core_clusternum,
  output wire                       clk_ungated,


  input  wire                       test_mode

// leda NTL_CON13C on
// leda NTL_CON37 on
);



`ifdef VERILATOR  // {
wire                             i_test_mode = 1'b0;
`else  // } {
wire                             i_test_mode = test_mode;
`endif // }



// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning

//========================== Wire declarations ===============================

//==================== Component instantiations ==============================


// spyglass disable_block Reset_info09a
// SMD: reset net unconstrained
// SJ: internal generated reset signal
wire cc_pd1_rst;
wire cc_pd1_rst_a;

// spyglass enable_block Reset_info09a
wire cc_pd1_clk;




wire                                     cc_top_cg_en_gaux_cmd_valid;
wire                                     cc_top_cg_en_gaux_cmd_accept;
wire [`npuarc_CC_GAUX_CMD_WIDTH-1:0]            cc_top_cg_en_gaux_cmd;
wire                                     cc_top_cg_en_gaux_res_valid;
wire                                     cc_top_cg_en_gaux_res_accept;
wire [`npuarc_CC_GAUX_RES_WIDTH-1:0]            cc_top_cg_en_gaux_res_data;
wire                                     cc_top_cg_en_gaux_wen_valid;
wire [`npuarc_CC_GAUX_WADDR_WIDTH-1:0]          cc_top_cg_en_gaux_wen_addr;
wire [`npuarc_CC_GAUX_WDATA_WIDTH-1:0]          cc_top_cg_en_gaux_wen_data;


wire                                     biu_l1_clk_enable;
wire                                     biu_accept_en;
wire                                     biu_l1_clk;




wire                                     biu2pdm_idle;
wire                                     biu2pdm_l2c_idle;





wire                                     cc_gaux_idle;





wire                                     cc_misc_l1_clk;


wire                                      cc_aux_l1_clk_enable;
wire                                      cc_aux_accept_en;

wire                                      cc_biu_l1_cg_dis;
wire                                      cc_top_l1_cg_dis;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the cc_aon_wrap module, it is a wrapper around the always-on //
// modules:                                                                 //
//        -- cc_aon_reset_ctrl                                              //
//        -- cc_top_aon_regs                                                //
//        -- cc_pdm_top                                                     //
//        -- cc_pdm_resync_in                                               //
//        -- cc_clock_ctrl                                                  //
//        -- cc_mem_power_ctrl                                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
npuarc_cc_aon_wrap u_cc_aon_wrap (
  .l1_cg_dis           (l1_cg_dis),
  .cc_biu_l1_cg_dis           (cc_biu_l1_cg_dis),
  .cc_top_l1_cg_dis           (cc_top_l1_cg_dis),
  .cc_misc_l1_clk                (cc_misc_l1_clk),
  .cc_aux_l1_clk_enable     (cc_aux_l1_clk_enable),
  .cc_aux_accept_en         (cc_aux_accept_en),
  .cc_gaux_idle (cc_gaux_idle),


  .cc_top_cg_en_gaux_cmd_valid  (cc_top_cg_en_gaux_cmd_valid),
  .cc_top_cg_en_gaux_cmd_accept (cc_top_cg_en_gaux_cmd_accept),
  .cc_top_cg_en_gaux_cmd        (cc_top_cg_en_gaux_cmd),
  .cc_top_cg_en_gaux_res_valid  (cc_top_cg_en_gaux_res_valid),
  .cc_top_cg_en_gaux_res_accept (cc_top_cg_en_gaux_res_accept),
  .cc_top_cg_en_gaux_res_data   (cc_top_cg_en_gaux_res_data),
  .cc_top_cg_en_gaux_wen_valid  (cc_top_cg_en_gaux_wen_valid),
  .cc_top_cg_en_gaux_wen_addr   (cc_top_cg_en_gaux_wen_addr),
  .cc_top_cg_en_gaux_wen_data   (cc_top_cg_en_gaux_wen_data),
  

  .biu_l1_clk_enable          (biu_l1_clk_enable),
  .biu_accept_en              (biu_accept_en),
  .biu_l1_clk                 (biu_l1_clk),
  .l1_clk_enable       (cpu_clk_enable),
  .l1_accept_en        (l1_accept_en),
  .l1_clk              (c0clk),




  // cc pdm interface with biu
  .biu_idle                   (biu2pdm_idle),

  .cc_idle                   (cc_idle),


  .cc_pd1_rst_a               (cc_pd1_rst_a),
  .cc_pd1_rst                 (cc_pd1_rst),
  .cc_pd1_clk                 (cc_pd1_clk),





  // global clock and reset input
  .clk                        (clk),     // clock
  .rst_a                      (rst_a),          // async CC reset
  .test_mode                  (i_test_mode)       // test mode to bypass FFs
);

// spyglass enable_block W528

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the cc_pd1_domain module, it is a wrapper around the none    //
// always-on module                                                         //
// modules:                                                                 //
//        -- alb_scu                                                        //
//        -- slc_top                                                        //
//        -- llm_top                                                        //
//        -- cc_sm_mux                                                      //
//        -- sm_data*_ram                                                   //
//        -- xdma_top                                                       //
//        -- biu_aux                                                        //
//        -- biu_top                                                        //
//        -- cc_direct_ioc                                                  //
//        -- cc_aux_plr                                                     //
//        -- cc_aux                                                         //
//        -- cc_dma_irq_wiring                                              //
//        -- cc_uaux                                                        //
//        -- cc_lbu_base_preprc                                             //
//        -- dma_server                                                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////








npuarc_cc_pd1_domain u_cc_pd1_domain (
  .clk                        (clk),
  .cc_misc_clk                (cc_misc_l1_clk),


  .cc_biu_l1_cg_dis           (cc_biu_l1_cg_dis),
  .cc_top_l1_cg_dis           (cc_top_l1_cg_dis),
  .cc_aux_l1_clk_enable     (cc_aux_l1_clk_enable),
  .cc_aux_accept_en         (cc_aux_accept_en),

  .biu_l1_clk_enable          (biu_l1_clk_enable),
  .biu_accept_en              (biu_accept_en),
  .biu_clk                   (biu_l1_clk),





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
  .ifu_ibus_cmd_valid           (ifu_ibus_cmd_valid),
  .ifu_ibus_cmd_accept          (ifu_ibus_cmd_accept),
  .ifu_ibus_cmd_addr            (ifu_ibus_cmd_addr),
  .ifu_ibus_cmd_wrap            (ifu_ibus_cmd_wrap),
  .ifu_ibus_cmd_cache           (ifu_ibus_cmd_cache),
  .ifu_ibus_cmd_burst_size      (ifu_ibus_cmd_burst_size),
  .ifu_ibus_cmd_prot            (ifu_ibus_cmd_prot),
  //
  .ifu_ibus_rd_valid            (ifu_ibus_rd_valid),
  .ifu_ibus_err_rd              (ifu_ibus_err_rd),
  .ifu_ibus_rd_accept           (ifu_ibus_rd_accept),
  .ifu_ibus_rd_data             (ifu_ibus_rd_data),
  .ifu_ibus_rd_last             (ifu_ibus_rd_last),

  //////////// LQWQ IBP interface for core 0 ///////////////////////////////////
  //
  .lqwq_mem_cmd_valid           (lqwq_mem_cmd_valid),
  .lqwq_mem_cmd_cache           (lqwq_mem_cmd_cache),
  .lqwq_mem_cmd_accept          (lqwq_mem_cmd_accept),
  .lqwq_mem_cmd_read            (lqwq_mem_cmd_read),
  .lqwq_mem_cmd_addr            (lqwq_mem_cmd_addr),
  .lqwq_mem_cmd_burst_size      (lqwq_mem_cmd_burst_size),
  .lqwq_mem_cmd_data_size       (lqwq_mem_cmd_data_size),
  .lqwq_mem_cmd_lock            (lqwq_mem_cmd_lock),
  .lqwq_mem_cmd_excl            (lqwq_mem_cmd_excl),
  .lqwq_mem_cmd_prot            (lqwq_mem_cmd_prot),
  //
  .lqwq_mem_rd_valid            (lqwq_mem_rd_valid),
  .lqwq_mem_err_rd              (lqwq_mem_err_rd),
  .lqwq_mem_rd_excl_ok          (lqwq_mem_rd_excl_ok),
  .lqwq_mem_rd_accept           (lqwq_mem_rd_accept),
  .lqwq_mem_rd_data             (lqwq_mem_rd_data),
  .lqwq_mem_rd_last             (lqwq_mem_rd_last),
  .lqwq_mem_wr_valid            (lqwq_mem_wr_valid),
  .lqwq_mem_wr_accept           (lqwq_mem_wr_accept),
  .lqwq_mem_wr_data             (lqwq_mem_wr_data),
  .lqwq_mem_wr_mask             (lqwq_mem_wr_mask),
  .lqwq_mem_wr_last             (lqwq_mem_wr_last),
  .lqwq_mem_wr_done             (lqwq_mem_wr_done),
  .lqwq_mem_wr_excl_done        (lqwq_mem_wr_excl_done),
  .lqwq_mem_err_wr              (lqwq_mem_err_wr),
  .lqwq_mem_wr_resp_accept      (lqwq_mem_wr_resp_accept),

  ////////// RF IBP interface for core 0 /////////////////////////////////////
  //
  .rf_cmd_valid               (rf_cmd_valid),
  .rf_cmd_accept              (rf_cmd_accept),
  .rf_cmd_read                (rf_cmd_read),
  .rf_cmd_addr                (rf_cmd_addr),
  .rf_cmd_prot                (rf_cmd_prot),
  .rf_cmd_wrap                (rf_cmd_wrap),
  .rf_cmd_burst_size          (rf_cmd_burst_size),
  .rf_cmd_cache               (rf_cmd_cache),
  .rf_cmd_excl                (rf_cmd_excl),
  .rf_cmd_lock                (rf_cmd_lock),
  .rf_cmd_data_size           (rf_cmd_data_size),
  .rf_rd_valid                (rf_rd_valid),
  .rf_rd_last                 (rf_rd_last),
  .rf_err_rd                  (rf_err_rd),
  .rf_rd_data                 (rf_rd_data),
  .rf_rd_accept               (rf_rd_accept),

  ////////// CB IBP interface for core 0 /////////////////////////////////////
  //
  .cb_cmd_valid               (cb_cmd_valid),
  .cb_cmd_accept              (cb_cmd_accept),
  .cb_cmd_read                (cb_cmd_read),
  .cb_cmd_addr                (cb_cmd_addr),
  .cb_cmd_prot                (cb_cmd_prot),
  .cb_cmd_wrap                (cb_cmd_wrap),
  .cb_cmd_burst_size          (cb_cmd_burst_size),
  .cb_cmd_cache               (cb_cmd_cache),
  .cb_cmd_excl                (cb_cmd_excl),
  .cb_cmd_lock                (cb_cmd_lock),
  .cb_cmd_data_size           (cb_cmd_data_size),
  .cb_wr_valid                (cb_wr_valid),
  .cb_wr_accept               (cb_wr_accept),
  .cb_wr_last                 (cb_wr_last),
  .cb_wr_data                 (cb_wr_data),
  .cb_wr_mask                 (cb_wr_mask),
  .cb_wr_done                 (cb_wr_done),
  .cb_err_wr                  (cb_err_wr),
  .cb_wr_resp_accept          (cb_wr_resp_accept),


  ////////// dccm_dmi_ IBP port for core 0 ///////////////////////////////////////
  //
  //         dccm_dmi_ port Command channel for core 0
  //
  .dccm_dmi_cmd_valid    (dccm_dmi_cmd_valid),
  .dccm_dmi_cmd_accept   (dccm_dmi_cmd_accept),
  .dccm_dmi_cmd_read     (dccm_dmi_cmd_read),
  .dccm_dmi_cmd_addr     (dccm_dmi_cmd_addr),
  //
  //         dccm_dmi_ port Read Data channel for core 0
  //
  .dccm_dmi_rd_valid     (dccm_dmi_rd_valid),
  .dccm_dmi_rd_accept    (dccm_dmi_rd_accept),
  .dccm_dmi_err_rd       (dccm_dmi_err_rd),
  .dccm_dmi_rd_data      (dccm_dmi_rd_data),
  //
  //         dccm_dmi_ port Write Data channel for core 0
  //
  .dccm_dmi_wr_valid     (dccm_dmi_wr_valid),
  .dccm_dmi_wr_accept    (dccm_dmi_wr_accept),
  .dccm_dmi_wr_data      (dccm_dmi_wr_data),
  .dccm_dmi_wr_mask      (dccm_dmi_wr_mask ),
  //
  //         dccm_dmi_ port Write Response channel for core 0
  //
  .dccm_dmi_wr_done      (dccm_dmi_wr_done),
  .dccm_dmi_err_wr       (dccm_dmi_err_wr),

  ////////// Auxiliary interface to the cc_aux module for core 0 /////////////
  //
  // Read and Status Channel from core 
  .aux_rs_valid               (aux_rs_valid),
  .aux_rs_addr                (aux_rs_addr),
  .aux_rs_region              (aux_rs_region),
  .aux_rs_read                (aux_rs_read),
  .aux_rs_write               (aux_rs_write),
  //
  .aux_rs_status              (aux_rs_status),
  .aux_rs_data                (aux_rs_data),
  .aux_rs_accept              (aux_rs_accept),
  .aux_wr_valid               (aux_wr_valid),
  .aux_wr_addr                (aux_wr_addr),
  .aux_wr_region              (aux_wr_region),
  .aux_wr_data                (aux_wr_data),
  .aux_wr_allow               (aux_wr_allow),
  //
  // Commit Channel from core 
  .aux_cm_phase               (aux_cm_phase),
  .aux_cm_valid               (aux_cm_valid),










  ////////// External AXI memory interface port 0 ////////////////////////////
  //
  .cbu_axi_arid                      (cbu_axi_arid),
  .cbu_axi_rid                       (cbu_axi_rid),
  .cbu_axi_arvalid                   (cbu_axi_arvalid),
  .cbu_axi_arready                   (cbu_axi_arready),
  .cbu_axi_araddr                    (cbu_axi_araddr),
  .cbu_axi_arcache                   (cbu_axi_arcache),
  .cbu_axi_arprot                    (cbu_axi_arprot),
  .cbu_axi_arburst                   (cbu_axi_arburst),
  .cbu_axi_arlen                     (cbu_axi_arlen),
  .cbu_axi_rvalid                    (cbu_axi_rvalid),
  .cbu_axi_rready                    (cbu_axi_rready),
  .cbu_axi_rdata                     (cbu_axi_rdata),
  .cbu_axi_rresp                     (cbu_axi_rresp),
  .cbu_axi_rlast                     (cbu_axi_rlast),
  .cbu_axi_arsize                    (cbu_axi_arsize),
  .cbu_axi_arlock                    (cbu_axi_arlock),
  .cbu_axi_awid                      (cbu_axi_awid),
  .cbu_axi_wid                       (cbu_axi_wid),
  .cbu_axi_bid                       (cbu_axi_bid),
  .cbu_axi_awvalid                   (cbu_axi_awvalid),
  .cbu_axi_awready                   (cbu_axi_awready),
  .cbu_axi_wready                    (cbu_axi_wready),
  .cbu_axi_bvalid                    (cbu_axi_bvalid),
  .cbu_axi_bresp                     (cbu_axi_bresp),
  .cbu_axi_awaddr                    (cbu_axi_awaddr),
  .cbu_axi_awcache                   (cbu_axi_awcache),
  .cbu_axi_awprot                    (cbu_axi_awprot),
  .cbu_axi_awlock                    (cbu_axi_awlock),
  .cbu_axi_awburst                   (cbu_axi_awburst),
  .cbu_axi_awlen                     (cbu_axi_awlen),
  .cbu_axi_awsize                    (cbu_axi_awsize),
  .cbu_axi_wvalid                    (cbu_axi_wvalid),
  .cbu_axi_wdata                     (cbu_axi_wdata),
  .cbu_axi_wstrb                     (cbu_axi_wstrb),
  .cbu_axi_wlast                     (cbu_axi_wlast),
  .cbu_axi_bready                    (cbu_axi_bready),







// The interface for sccm_ dmi ports





  //// The AXI bus
  .sccm_axi_arvalid             (sccm_axi_arvalid),
  .sccm_axi_arready             (sccm_axi_arready),
  .sccm_axi_arid                (sccm_axi_arid),
  .sccm_axi_araddr              (sccm_axi_araddr),
  .sccm_axi_arregion            (sccm_axi_arregion),
  .sccm_axi_arburst             (sccm_axi_arburst),
  .sccm_axi_arlen               (sccm_axi_arlen),
  .sccm_axi_arsize              (sccm_axi_arsize),
  .sccm_axi_rvalid              (sccm_axi_rvalid),
  .sccm_axi_rready              (sccm_axi_rready),
  .sccm_axi_rid                 (sccm_axi_rid),
  .sccm_axi_rdata               (sccm_axi_rdata),
  .sccm_axi_rresp               (sccm_axi_rresp),
  .sccm_axi_rlast               (sccm_axi_rlast),
  .sccm_axi_awvalid             (sccm_axi_awvalid),
  .sccm_axi_awready             (sccm_axi_awready),
  .sccm_axi_awid                (sccm_axi_awid),
  .sccm_axi_awaddr              (sccm_axi_awaddr),
  .sccm_axi_awregion            (sccm_axi_awregion),
  .sccm_axi_awburst             (sccm_axi_awburst),
  .sccm_axi_awlen               (sccm_axi_awlen),
  .sccm_axi_awsize              (sccm_axi_awsize),
  .sccm_axi_wvalid              (sccm_axi_wvalid),
  .sccm_axi_wready              (sccm_axi_wready),
  .sccm_axi_wdata               (sccm_axi_wdata),
  .sccm_axi_wstrb               (sccm_axi_wstrb),
  .sccm_axi_wlast               (sccm_axi_wlast),
  .sccm_axi_bvalid              (sccm_axi_bvalid),
  .sccm_axi_bready              (sccm_axi_bready),
  .sccm_axi_bid                 (sccm_axi_bid),
  .sccm_axi_bresp               (sccm_axi_bresp),









  .biu_dmi_clk_en_req         (biu_dmi_clk_en_req),



  .biu2pdm_idle                      (biu2pdm_idle),
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
  .biu2pdm_l2c_idle                  (biu2pdm_l2c_idle),
// spyglass enable_block UnloadedOutTerm-ML


  .cc_top_cg_en_gaux_cmd_valid           (cc_top_cg_en_gaux_cmd_valid),
  .cc_top_cg_en_gaux_cmd_accept          (cc_top_cg_en_gaux_cmd_accept),
  .cc_top_cg_en_gaux_cmd                 (cc_top_cg_en_gaux_cmd),
  .cc_top_cg_en_gaux_res_valid           (cc_top_cg_en_gaux_res_valid),
  .cc_top_cg_en_gaux_res_accept          (cc_top_cg_en_gaux_res_accept),
  .cc_top_cg_en_gaux_res_data            (cc_top_cg_en_gaux_res_data),
  .cc_top_cg_en_gaux_wen_valid           (cc_top_cg_en_gaux_wen_valid),
  .cc_top_cg_en_gaux_wen_addr            (cc_top_cg_en_gaux_wen_addr),
  .cc_top_cg_en_gaux_wen_data            (cc_top_cg_en_gaux_wen_data),
  .cc_gaux_idle                      (cc_gaux_idle),

  ////////// Bus clock/clock enable inputs /////////////////////////////////////////
  //
  .mbus_clk_en                             (mbus_clk_en),
  .dbus_clk_en                             (dbus_clk_en),










  ////////// General input signals ///////////////////////////////////////////
  //
  .cc_pd1_rst_a                      (cc_pd1_rst_a),
  .cc_pd1_rst                        (cc_pd1_rst),
  .cc_pd1_clk                        (cc_pd1_clk),
  .clusternum                        (clusternum), // for cluster_id register.
  .core_clusternum            (core_clusternum),



  .test_mode                         (i_test_mode)

// leda NTL_CON13C on
// leda NTL_CON37 on
);



assign clk_ungated = clk;

endmodule // cc_top
