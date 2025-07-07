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
//
// ===========================================================================
//
// Description:
//  Verilog module of CCM bridge within BIU
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"





// Set simulation timescale
//
`include "const.def"

module npuarc_biu_ccm_bridge
// leda G_521_2_B off
// LMD: Use lowercase letters for all signal reg, net and port names
// LJ: Pfx may include the uppercase, so disable the lint checking rule
  (

  output                               biu_dmi_clk_en_req,


  input                                dbus_clk_en,

// leda NTL_CON13C off
// LMD: non driving internal net
// LJ: Some signals bit field are indeed no driven
// leda NTL_CON37 off
// LMD: Signal/Net must read from the input port in module
// LJ: Some signals bit field are indeed not read and used


  input   [2            -1:0]       sccm_axi_arregion,
  input                                   sccm_axi_arvalid,
  output                                  sccm_axi_arready,
  input   [16              -1:0]       sccm_axi_arid,
  input   [24                -1:0]       sccm_axi_araddr,
  input   [2-1:0]       sccm_axi_arburst,
  input   [4-1:0]       sccm_axi_arlen,
  input   [3-1:0]       sccm_axi_arsize,
  input   [4-1:0]       sccm_axi_arcache,
  input   [3-1:0]       sccm_axi_arprot,
  input   [2-1:0]       sccm_axi_arlock,

  output                                  sccm_axi_rvalid,
  input                                   sccm_axi_rready,
  output  [16              -1:0]       sccm_axi_rid,
  output  [64                -1:0]       sccm_axi_rdata,
  output  [2-1:0]       sccm_axi_rresp,
  output                                  sccm_axi_rlast,

  input   [2            -1:0]       sccm_axi_awregion,
  input                                   sccm_axi_awvalid,
  output                                  sccm_axi_awready,
  input   [16              -1:0]       sccm_axi_awid,
  input   [24            -1:0]           sccm_axi_awaddr,
  input   [2-1:0]       sccm_axi_awburst,
  input   [4-1:0]       sccm_axi_awlen,
  input   [3-1:0]       sccm_axi_awsize,
  input   [4-1:0]       sccm_axi_awcache,
  input   [3-1:0]       sccm_axi_awprot,
  input   [2-1:0]       sccm_axi_awlock,

  input                                   sccm_axi_wvalid,
  output                                  sccm_axi_wready,
  input   [64              -1:0]         sccm_axi_wdata,
  input   [(64          /8)-1:0]         sccm_axi_wstrb,
  input                                   sccm_axi_wlast,

  output                                  sccm_axi_bvalid,
  input                                   sccm_axi_bready,
  output  [16              -1:0]       sccm_axi_bid,
  output  [2-1:0]       sccm_axi_bresp,




  output                                  dccm_dmi_ibp_cmd_valid,
  input                                   dccm_dmi_ibp_cmd_accept,
  output                                  dccm_dmi_ibp_cmd_read,
  output  [24                -1:0]       dccm_dmi_ibp_cmd_addr,
  output                                  dccm_dmi_ibp_cmd_wrap,
  output  [3-1:0]       dccm_dmi_ibp_cmd_data_size,
  output  [4-1:0]       dccm_dmi_ibp_cmd_burst_size,
  output  [2-1:0]       dccm_dmi_ibp_cmd_prot,
  output  [4-1:0]       dccm_dmi_ibp_cmd_cache,
  output                                  dccm_dmi_ibp_cmd_lock,
  output                                  dccm_dmi_ibp_cmd_excl,

  input                                   dccm_dmi_ibp_rd_valid,
  input                                   dccm_dmi_ibp_rd_excl_ok,
  output                                  dccm_dmi_ibp_rd_accept,
  input                                   dccm_dmi_ibp_err_rd,
  input   [64               -1:0]        dccm_dmi_ibp_rd_data,
  input                                   dccm_dmi_ibp_rd_last,

  output                                  dccm_dmi_ibp_wr_valid,
  input                                   dccm_dmi_ibp_wr_accept,
  output  [64               -1:0]        dccm_dmi_ibp_wr_data,
  output  [8  -1:0]                    dccm_dmi_ibp_wr_mask,
  output                                  dccm_dmi_ibp_wr_last,

  input                                   dccm_dmi_ibp_wr_done,
  input                                   dccm_dmi_ibp_wr_excl_done,
  input                                   dccm_dmi_ibp_err_wr,
  output                                  dccm_dmi_ibp_wr_resp_accept,


// leda NTL_CON37 on
// leda NTL_CON13C on

  output biu_dmi_idle,
  input sync_rst_r,
  input async_rst ,
  input nmi_restart_r,
  input rst_a     ,
  input clk
);

wire dccm_dmi_ibp_req;



assign biu_dmi_clk_en_req =  1'b0
   | dccm_dmi_ibp_req
  ;










//**************************






//**************************






//**************************


// spyglass disable_block Clock_info03a
// SMD: clock net unconstrained
// SJ: no need to constrain
  wire clk_gated_biu_sccm;
// spyglass enable_block Clock_info03a



  wire  [2 -1:0] sccm_dmi_slv_ibp_cmd_rgon;
  wire  [2 -1:0] sccm_dmi_slv_ibp_cmd_user = sccm_dmi_slv_ibp_cmd_rgon;


  wire                                  sccm_dmi_slv_ibp_cmd_valid;
  wire                                  sccm_dmi_slv_ibp_cmd_accept;
  wire                                  sccm_dmi_slv_ibp_cmd_read;
  wire  [24                -1:0]       sccm_dmi_slv_ibp_cmd_addr;
  wire                                  sccm_dmi_slv_ibp_cmd_wrap;
  wire  [3-1:0]       sccm_dmi_slv_ibp_cmd_data_size;
  wire  [4-1:0]       sccm_dmi_slv_ibp_cmd_burst_size;
  wire  [2-1:0]       sccm_dmi_slv_ibp_cmd_prot;
  wire  [4-1:0]       sccm_dmi_slv_ibp_cmd_cache;
  wire                                  sccm_dmi_slv_ibp_cmd_lock;
  wire                                  sccm_dmi_slv_ibp_cmd_excl;

  wire                                  sccm_dmi_slv_ibp_rd_valid;
  wire                                  sccm_dmi_slv_ibp_rd_excl_ok;
  wire                                  sccm_dmi_slv_ibp_rd_accept;
  wire                                  sccm_dmi_slv_ibp_err_rd;
  wire  [64               -1:0]        sccm_dmi_slv_ibp_rd_data;
  wire                                  sccm_dmi_slv_ibp_rd_last;

  wire                                  sccm_dmi_slv_ibp_wr_valid;
  wire                                  sccm_dmi_slv_ibp_wr_accept;
  wire  [64               -1:0]        sccm_dmi_slv_ibp_wr_data;
  wire  [8  -1:0]                    sccm_dmi_slv_ibp_wr_mask;
  wire                                  sccm_dmi_slv_ibp_wr_last;

  wire                                  sccm_dmi_slv_ibp_wr_done;
  wire                                  sccm_dmi_slv_ibp_wr_excl_done;
  wire                                  sccm_dmi_slv_ibp_err_wr;
  wire                                  sccm_dmi_slv_ibp_wr_resp_accept;

npuarc_biu_sccm_dmi_slv u_biu_sccm_dmi_slv
  (
























  .sccm_axi_arregion   (sccm_axi_arregion),
  .sccm_axi_arvalid    (sccm_axi_arvalid),
  .sccm_axi_arready    (sccm_axi_arready),
  .sccm_axi_arid       (sccm_axi_arid   ),
  .sccm_axi_araddr     (sccm_axi_araddr ),
  .sccm_axi_arburst    (sccm_axi_arburst),
  .sccm_axi_arlen      (sccm_axi_arlen  ),
  .sccm_axi_arsize     (sccm_axi_arsize ),
  .sccm_axi_arcache    (sccm_axi_arcache),
  .sccm_axi_arprot     (sccm_axi_arprot ),
  .sccm_axi_arlock     (sccm_axi_arlock ),

  .sccm_axi_rvalid     (sccm_axi_rvalid),
  .sccm_axi_rready     (sccm_axi_rready),
  .sccm_axi_rid        (sccm_axi_rid   ),
  .sccm_axi_rdata      (sccm_axi_rdata ),
  .sccm_axi_rresp      (sccm_axi_rresp ),
  .sccm_axi_rlast      (sccm_axi_rlast ),

  .sccm_axi_awregion   (sccm_axi_awregion),
  .sccm_axi_awvalid    (sccm_axi_awvalid),
  .sccm_axi_awready    (sccm_axi_awready),
  .sccm_axi_awid       (sccm_axi_awid   ),
  .sccm_axi_awaddr     (sccm_axi_awaddr ),
  .sccm_axi_awburst    (sccm_axi_awburst),
  .sccm_axi_awlen      (sccm_axi_awlen  ),
  .sccm_axi_awsize     (sccm_axi_awsize ),
  .sccm_axi_awcache    (sccm_axi_awcache),
  .sccm_axi_awprot     (sccm_axi_awprot ),
  .sccm_axi_awlock     (sccm_axi_awlock ),

  .sccm_axi_wvalid      (sccm_axi_wvalid),
  .sccm_axi_wready      (sccm_axi_wready),
  .sccm_axi_wdata       (sccm_axi_wdata ),
  .sccm_axi_wstrb       (sccm_axi_wstrb ),
  .sccm_axi_wlast       (sccm_axi_wlast ),

  .sccm_axi_bvalid   (sccm_axi_bvalid),
  .sccm_axi_bready   (sccm_axi_bready),
  .sccm_axi_bid      (sccm_axi_bid   ),
  .sccm_axi_bresp    (sccm_axi_bresp ),



  .sccm_dmi_slv_ibp_cmd_valid             (sccm_dmi_slv_ibp_cmd_valid),
  .sccm_dmi_slv_ibp_cmd_accept            (sccm_dmi_slv_ibp_cmd_accept),
  .sccm_dmi_slv_ibp_cmd_read              (sccm_dmi_slv_ibp_cmd_read),
  .sccm_dmi_slv_ibp_cmd_addr              (sccm_dmi_slv_ibp_cmd_addr),
  .sccm_dmi_slv_ibp_cmd_wrap              (sccm_dmi_slv_ibp_cmd_wrap),
  .sccm_dmi_slv_ibp_cmd_data_size         (sccm_dmi_slv_ibp_cmd_data_size),
  .sccm_dmi_slv_ibp_cmd_burst_size        (sccm_dmi_slv_ibp_cmd_burst_size),
  .sccm_dmi_slv_ibp_cmd_prot              (sccm_dmi_slv_ibp_cmd_prot),
  .sccm_dmi_slv_ibp_cmd_cache             (sccm_dmi_slv_ibp_cmd_cache),
  .sccm_dmi_slv_ibp_cmd_lock              (sccm_dmi_slv_ibp_cmd_lock),
  .sccm_dmi_slv_ibp_cmd_excl              (sccm_dmi_slv_ibp_cmd_excl),

  .sccm_dmi_slv_ibp_rd_valid              (sccm_dmi_slv_ibp_rd_valid),
  .sccm_dmi_slv_ibp_rd_excl_ok            (sccm_dmi_slv_ibp_rd_excl_ok),
  .sccm_dmi_slv_ibp_rd_accept             (sccm_dmi_slv_ibp_rd_accept),
  .sccm_dmi_slv_ibp_err_rd                (sccm_dmi_slv_ibp_err_rd),
  .sccm_dmi_slv_ibp_rd_data               (sccm_dmi_slv_ibp_rd_data),
  .sccm_dmi_slv_ibp_rd_last               (sccm_dmi_slv_ibp_rd_last),

  .sccm_dmi_slv_ibp_wr_valid              (sccm_dmi_slv_ibp_wr_valid),
  .sccm_dmi_slv_ibp_wr_accept             (sccm_dmi_slv_ibp_wr_accept),
  .sccm_dmi_slv_ibp_wr_data               (sccm_dmi_slv_ibp_wr_data),
  .sccm_dmi_slv_ibp_wr_mask               (sccm_dmi_slv_ibp_wr_mask),
  .sccm_dmi_slv_ibp_wr_last               (sccm_dmi_slv_ibp_wr_last),

  .sccm_dmi_slv_ibp_wr_done               (sccm_dmi_slv_ibp_wr_done),
  .sccm_dmi_slv_ibp_wr_excl_done          (sccm_dmi_slv_ibp_wr_excl_done),
  .sccm_dmi_slv_ibp_err_wr                (sccm_dmi_slv_ibp_err_wr),
  .sccm_dmi_slv_ibp_wr_resp_accept        (sccm_dmi_slv_ibp_wr_resp_accept),
    .sccm_dmi_slv_ibp_cmd_rgon (sccm_dmi_slv_ibp_cmd_rgon),


  .dbus_clk_en(dbus_clk_en),
  .clk                                      (clk                           ),
  .sync_rst_r                               (sync_rst_r                    ),
  .async_rst                                (async_rst                     ),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a                                    (rst_a)
);


    wire sccm_dmi_idle;


wire sccm_dmi_tmp_idle;
   npuarc_biu_slv_axi_idle sccm_axi_idle
  (
      .axi_arvalid(sccm_axi_arvalid),
      .axi_arready(sccm_axi_arready),
      .axi_awvalid(sccm_axi_awvalid),
      .axi_awready(sccm_axi_awready),
      .axi_rvalid (sccm_axi_rvalid ),
      .axi_rready (sccm_axi_rready ),
      .axi_rlast  (sccm_axi_rlast  ),
      .axi_wvalid (sccm_axi_wvalid ),
      .axi_wready (sccm_axi_wready ),
      .axi_wlast  (sccm_axi_wlast  ),
      .axi_bvalid (sccm_axi_bvalid ),
      .axi_bready (sccm_axi_bready ),

      .axi_idle   (sccm_dmi_tmp_idle),
      .bus_clk_en (dbus_clk_en),
      .clk        (clk),
      .nmi_restart_r (nmi_restart_r ),
      .rst_a      (rst_a)
  );

assign sccm_dmi_idle = sccm_dmi_tmp_idle & (~sccm_axi_arvalid) & (~sccm_axi_awvalid) & (~sccm_axi_wvalid);




  wire  [2 -1:0] sccm_dmiibp_slv_ibp_cmd_user;


  wire                                  sccm_dmiibp_slv_ibp_cmd_valid;
  wire                                  sccm_dmiibp_slv_ibp_cmd_accept;
  wire                                  sccm_dmiibp_slv_ibp_cmd_read;
  wire  [24                -1:0]       sccm_dmiibp_slv_ibp_cmd_addr;
  wire                                  sccm_dmiibp_slv_ibp_cmd_wrap;
  wire  [3-1:0]       sccm_dmiibp_slv_ibp_cmd_data_size;
  wire  [4-1:0]       sccm_dmiibp_slv_ibp_cmd_burst_size;
  wire  [2-1:0]       sccm_dmiibp_slv_ibp_cmd_prot;
  wire  [4-1:0]       sccm_dmiibp_slv_ibp_cmd_cache;
  wire                                  sccm_dmiibp_slv_ibp_cmd_lock;
  wire                                  sccm_dmiibp_slv_ibp_cmd_excl;

  wire                                  sccm_dmiibp_slv_ibp_rd_valid;
  wire                                  sccm_dmiibp_slv_ibp_rd_excl_ok;
  wire                                  sccm_dmiibp_slv_ibp_rd_accept;
  wire                                  sccm_dmiibp_slv_ibp_err_rd;
  wire  [64               -1:0]        sccm_dmiibp_slv_ibp_rd_data;
  wire                                  sccm_dmiibp_slv_ibp_rd_last;

  wire                                  sccm_dmiibp_slv_ibp_wr_valid;
  wire                                  sccm_dmiibp_slv_ibp_wr_accept;
  wire  [64               -1:0]        sccm_dmiibp_slv_ibp_wr_data;
  wire  [8  -1:0]                    sccm_dmiibp_slv_ibp_wr_mask;
  wire                                  sccm_dmiibp_slv_ibp_wr_last;

  wire                                  sccm_dmiibp_slv_ibp_wr_done;
  wire                                  sccm_dmiibp_slv_ibp_wr_excl_done;
  wire                                  sccm_dmiibp_slv_ibp_err_wr;
  wire                                  sccm_dmiibp_slv_ibp_wr_resp_accept;

npuarc_biu_sccm_dmiibp_slv u_biu_sccm_dmiibp_slv
  (

























    .sccm_dmi_slv_ibp_cmd_user (sccm_dmi_slv_ibp_cmd_user),

  .sccm_dmi_slv_ibp_cmd_valid             (sccm_dmi_slv_ibp_cmd_valid),
  .sccm_dmi_slv_ibp_cmd_accept            (sccm_dmi_slv_ibp_cmd_accept),
  .sccm_dmi_slv_ibp_cmd_read              (sccm_dmi_slv_ibp_cmd_read),
  .sccm_dmi_slv_ibp_cmd_addr              (sccm_dmi_slv_ibp_cmd_addr),
  .sccm_dmi_slv_ibp_cmd_wrap              (sccm_dmi_slv_ibp_cmd_wrap),
  .sccm_dmi_slv_ibp_cmd_data_size         (sccm_dmi_slv_ibp_cmd_data_size),
  .sccm_dmi_slv_ibp_cmd_burst_size        (sccm_dmi_slv_ibp_cmd_burst_size),
  .sccm_dmi_slv_ibp_cmd_prot              (sccm_dmi_slv_ibp_cmd_prot),
  .sccm_dmi_slv_ibp_cmd_cache             (sccm_dmi_slv_ibp_cmd_cache),
  .sccm_dmi_slv_ibp_cmd_lock              (sccm_dmi_slv_ibp_cmd_lock),
  .sccm_dmi_slv_ibp_cmd_excl              (sccm_dmi_slv_ibp_cmd_excl),

  .sccm_dmi_slv_ibp_rd_valid              (sccm_dmi_slv_ibp_rd_valid),
  .sccm_dmi_slv_ibp_rd_excl_ok            (sccm_dmi_slv_ibp_rd_excl_ok),
  .sccm_dmi_slv_ibp_rd_accept             (sccm_dmi_slv_ibp_rd_accept),
  .sccm_dmi_slv_ibp_err_rd                (sccm_dmi_slv_ibp_err_rd),
  .sccm_dmi_slv_ibp_rd_data               (sccm_dmi_slv_ibp_rd_data),
  .sccm_dmi_slv_ibp_rd_last               (sccm_dmi_slv_ibp_rd_last),

  .sccm_dmi_slv_ibp_wr_valid              (sccm_dmi_slv_ibp_wr_valid),
  .sccm_dmi_slv_ibp_wr_accept             (sccm_dmi_slv_ibp_wr_accept),
  .sccm_dmi_slv_ibp_wr_data               (sccm_dmi_slv_ibp_wr_data),
  .sccm_dmi_slv_ibp_wr_mask               (sccm_dmi_slv_ibp_wr_mask),
  .sccm_dmi_slv_ibp_wr_last               (sccm_dmi_slv_ibp_wr_last),

  .sccm_dmi_slv_ibp_wr_done               (sccm_dmi_slv_ibp_wr_done),
  .sccm_dmi_slv_ibp_wr_excl_done          (sccm_dmi_slv_ibp_wr_excl_done),
  .sccm_dmi_slv_ibp_err_wr                (sccm_dmi_slv_ibp_err_wr),
  .sccm_dmi_slv_ibp_wr_resp_accept        (sccm_dmi_slv_ibp_wr_resp_accept),


  .sccm_dmiibp_slv_ibp_cmd_valid             (sccm_dmiibp_slv_ibp_cmd_valid),
  .sccm_dmiibp_slv_ibp_cmd_accept            (sccm_dmiibp_slv_ibp_cmd_accept),
  .sccm_dmiibp_slv_ibp_cmd_read              (sccm_dmiibp_slv_ibp_cmd_read),
  .sccm_dmiibp_slv_ibp_cmd_addr              (sccm_dmiibp_slv_ibp_cmd_addr),
  .sccm_dmiibp_slv_ibp_cmd_wrap              (sccm_dmiibp_slv_ibp_cmd_wrap),
  .sccm_dmiibp_slv_ibp_cmd_data_size         (sccm_dmiibp_slv_ibp_cmd_data_size),
  .sccm_dmiibp_slv_ibp_cmd_burst_size        (sccm_dmiibp_slv_ibp_cmd_burst_size),
  .sccm_dmiibp_slv_ibp_cmd_prot              (sccm_dmiibp_slv_ibp_cmd_prot),
  .sccm_dmiibp_slv_ibp_cmd_cache             (sccm_dmiibp_slv_ibp_cmd_cache),
  .sccm_dmiibp_slv_ibp_cmd_lock              (sccm_dmiibp_slv_ibp_cmd_lock),
  .sccm_dmiibp_slv_ibp_cmd_excl              (sccm_dmiibp_slv_ibp_cmd_excl),

  .sccm_dmiibp_slv_ibp_rd_valid              (sccm_dmiibp_slv_ibp_rd_valid),
  .sccm_dmiibp_slv_ibp_rd_excl_ok            (sccm_dmiibp_slv_ibp_rd_excl_ok),
  .sccm_dmiibp_slv_ibp_rd_accept             (sccm_dmiibp_slv_ibp_rd_accept),
  .sccm_dmiibp_slv_ibp_err_rd                (sccm_dmiibp_slv_ibp_err_rd),
  .sccm_dmiibp_slv_ibp_rd_data               (sccm_dmiibp_slv_ibp_rd_data),
  .sccm_dmiibp_slv_ibp_rd_last               (sccm_dmiibp_slv_ibp_rd_last),

  .sccm_dmiibp_slv_ibp_wr_valid              (sccm_dmiibp_slv_ibp_wr_valid),
  .sccm_dmiibp_slv_ibp_wr_accept             (sccm_dmiibp_slv_ibp_wr_accept),
  .sccm_dmiibp_slv_ibp_wr_data               (sccm_dmiibp_slv_ibp_wr_data),
  .sccm_dmiibp_slv_ibp_wr_mask               (sccm_dmiibp_slv_ibp_wr_mask),
  .sccm_dmiibp_slv_ibp_wr_last               (sccm_dmiibp_slv_ibp_wr_last),

  .sccm_dmiibp_slv_ibp_wr_done               (sccm_dmiibp_slv_ibp_wr_done),
  .sccm_dmiibp_slv_ibp_wr_excl_done          (sccm_dmiibp_slv_ibp_wr_excl_done),
  .sccm_dmiibp_slv_ibp_err_wr                (sccm_dmiibp_slv_ibp_err_wr),
  .sccm_dmiibp_slv_ibp_wr_resp_accept        (sccm_dmiibp_slv_ibp_wr_resp_accept),
    .sccm_dmiibp_slv_ibp_cmd_user (sccm_dmiibp_slv_ibp_cmd_user),


  .clk                                      (clk                           ),
  .sync_rst_r                               (sync_rst_r                    ),
  .async_rst                                (async_rst                     ),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a                                    (rst_a)
);








  wire sccm_dmiibp_slv_ibp_rd_chnl_valid = sccm_dmiibp_slv_ibp_rd_valid | sccm_dmiibp_slv_ibp_rd_excl_ok | sccm_dmiibp_slv_ibp_err_rd;
  wire sccm_dmiibp_slv_ibp_wrsp_chnl_valid = sccm_dmiibp_slv_ibp_wr_done | sccm_dmiibp_slv_ibp_wr_excl_done | sccm_dmiibp_slv_ibp_err_wr;
  wire sccm_dmiibp_slv_ibp_idle;
  npuarc_biu_ccmb_ibp_idle
  #(
   .OUTSTAND_NUM  (10),
   .OUTSTAND_CNT_W(4)
    )
  u_sccm_dmiibp_slv_ibp_idle (
  .i_ibp_idle            (sccm_dmiibp_slv_ibp_idle),

  .i_ibp_cmd_chnl_valid  (sccm_dmiibp_slv_ibp_cmd_valid),
  .i_ibp_cmd_chnl_accept (sccm_dmiibp_slv_ibp_cmd_accept),
  .i_ibp_cmd_chnl_read   (sccm_dmiibp_slv_ibp_cmd_read),

  .i_ibp_rd_chnl_valid   (sccm_dmiibp_slv_ibp_rd_chnl_valid),
  .i_ibp_rd_chnl_accept  (sccm_dmiibp_slv_ibp_rd_accept),
  .i_ibp_rd_chnl_last    (sccm_dmiibp_slv_ibp_rd_last),

  .i_ibp_wrsp_chnl_valid (sccm_dmiibp_slv_ibp_wrsp_chnl_valid),
  .i_ibp_wrsp_chnl_accept(sccm_dmiibp_slv_ibp_wr_resp_accept),
  .clk        (clk),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a      (rst_a)
  );


  wire biu_biu_sccm_any_ibp_in = 1'b0
           | sccm_dmiibp_slv_ibp_cmd_valid
           ;

  wire biu_biu_sccm_ibp_idle = 1'b1
           & sccm_dmiibp_slv_ibp_idle
           ;

  wire biu_biu_sccm_clk_en =    biu_biu_sccm_any_ibp_in
                                 | (~biu_biu_sccm_ibp_idle);

  npuarc_biu_clk_ctrl u_biu_biu_sccm_clkctrl (
    .clk_gated  (clk_gated_biu_sccm),
    .nmi_restart_r  (nmi_restart_r),
    .clkctrl_en (biu_biu_sccm_clk_en),
    .clk        (clk  ),
    .rst_a      (rst_a)
    );

  wire  [2 -1:0] sccm_mst_ibp_cmd_chnl_user;



 wire [1-1:0] sccm_mst_ibp_cmd_chnl_valid;
 wire [1-1:0] sccm_mst_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] sccm_mst_ibp_cmd_chnl;

 wire [1-1:0] sccm_mst_ibp_wd_chnl_valid;
 wire [1-1:0] sccm_mst_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] sccm_mst_ibp_wd_chnl;

 wire [1-1:0] sccm_mst_ibp_rd_chnl_accept;
 wire [1-1:0] sccm_mst_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] sccm_mst_ibp_rd_chnl;

 wire [1-1:0] sccm_mst_ibp_wrsp_chnl_valid;
 wire [1-1:0] sccm_mst_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] sccm_mst_ibp_wrsp_chnl;


 npuarc_biu_sccm_mst u_biu_sccm_mst
   (







  .sccm_dmiibp_slv_ibp_cmd_valid             (sccm_dmiibp_slv_ibp_cmd_valid),
  .sccm_dmiibp_slv_ibp_cmd_accept            (sccm_dmiibp_slv_ibp_cmd_accept),
  .sccm_dmiibp_slv_ibp_cmd_read              (sccm_dmiibp_slv_ibp_cmd_read),
  .sccm_dmiibp_slv_ibp_cmd_addr              (sccm_dmiibp_slv_ibp_cmd_addr),
  .sccm_dmiibp_slv_ibp_cmd_wrap              (sccm_dmiibp_slv_ibp_cmd_wrap),
  .sccm_dmiibp_slv_ibp_cmd_data_size         (sccm_dmiibp_slv_ibp_cmd_data_size),
  .sccm_dmiibp_slv_ibp_cmd_burst_size        (sccm_dmiibp_slv_ibp_cmd_burst_size),
  .sccm_dmiibp_slv_ibp_cmd_prot              (sccm_dmiibp_slv_ibp_cmd_prot),
  .sccm_dmiibp_slv_ibp_cmd_cache             (sccm_dmiibp_slv_ibp_cmd_cache),
  .sccm_dmiibp_slv_ibp_cmd_lock              (sccm_dmiibp_slv_ibp_cmd_lock),
  .sccm_dmiibp_slv_ibp_cmd_excl              (sccm_dmiibp_slv_ibp_cmd_excl),

  .sccm_dmiibp_slv_ibp_rd_valid              (sccm_dmiibp_slv_ibp_rd_valid),
  .sccm_dmiibp_slv_ibp_rd_excl_ok            (sccm_dmiibp_slv_ibp_rd_excl_ok),
  .sccm_dmiibp_slv_ibp_rd_accept             (sccm_dmiibp_slv_ibp_rd_accept),
  .sccm_dmiibp_slv_ibp_err_rd                (sccm_dmiibp_slv_ibp_err_rd),
  .sccm_dmiibp_slv_ibp_rd_data               (sccm_dmiibp_slv_ibp_rd_data),
  .sccm_dmiibp_slv_ibp_rd_last               (sccm_dmiibp_slv_ibp_rd_last),

  .sccm_dmiibp_slv_ibp_wr_valid              (sccm_dmiibp_slv_ibp_wr_valid),
  .sccm_dmiibp_slv_ibp_wr_accept             (sccm_dmiibp_slv_ibp_wr_accept),
  .sccm_dmiibp_slv_ibp_wr_data               (sccm_dmiibp_slv_ibp_wr_data),
  .sccm_dmiibp_slv_ibp_wr_mask               (sccm_dmiibp_slv_ibp_wr_mask),
  .sccm_dmiibp_slv_ibp_wr_last               (sccm_dmiibp_slv_ibp_wr_last),

  .sccm_dmiibp_slv_ibp_wr_done               (sccm_dmiibp_slv_ibp_wr_done),
  .sccm_dmiibp_slv_ibp_wr_excl_done          (sccm_dmiibp_slv_ibp_wr_excl_done),
  .sccm_dmiibp_slv_ibp_err_wr                (sccm_dmiibp_slv_ibp_err_wr),
  .sccm_dmiibp_slv_ibp_wr_resp_accept        (sccm_dmiibp_slv_ibp_wr_resp_accept),
    .sccm_dmiibp_slv_ibp_cmd_user (sccm_dmiibp_slv_ibp_cmd_user),




    .sccm_mst_ibp_cmd_chnl_valid  (sccm_mst_ibp_cmd_chnl_valid),
    .sccm_mst_ibp_cmd_chnl_accept (sccm_mst_ibp_cmd_chnl_accept),
    .sccm_mst_ibp_cmd_chnl        (sccm_mst_ibp_cmd_chnl),

    .sccm_mst_ibp_rd_chnl_valid   (sccm_mst_ibp_rd_chnl_valid),
    .sccm_mst_ibp_rd_chnl_accept  (sccm_mst_ibp_rd_chnl_accept),
    .sccm_mst_ibp_rd_chnl         (sccm_mst_ibp_rd_chnl),

    .sccm_mst_ibp_wd_chnl_valid   (sccm_mst_ibp_wd_chnl_valid),
    .sccm_mst_ibp_wd_chnl_accept  (sccm_mst_ibp_wd_chnl_accept),
    .sccm_mst_ibp_wd_chnl         (sccm_mst_ibp_wd_chnl),

    .sccm_mst_ibp_wrsp_chnl_valid (sccm_mst_ibp_wrsp_chnl_valid),
    .sccm_mst_ibp_wrsp_chnl_accept(sccm_mst_ibp_wrsp_chnl_accept),
    .sccm_mst_ibp_wrsp_chnl       (sccm_mst_ibp_wrsp_chnl),

   .sccm_mst_ibp_cmd_chnl_user (sccm_mst_ibp_cmd_chnl_user),
   .clk                                      (clk_gated_biu_sccm          ),
   .nmi_restart_r (nmi_restart_r ),
   .rst_a                                    (rst_a        )
 );


  wire  [2 -1:0] sccm_mst_ibp_cmd_chnl_rgon = sccm_mst_ibp_cmd_chnl_user;
 npuarc_biu_sccm_slv u_biu_sccm_slv
  (





























    .sccm_mst_ibp_cmd_chnl_valid  (sccm_mst_ibp_cmd_chnl_valid),
    .sccm_mst_ibp_cmd_chnl_accept (sccm_mst_ibp_cmd_chnl_accept),
    .sccm_mst_ibp_cmd_chnl        (sccm_mst_ibp_cmd_chnl),

    .sccm_mst_ibp_rd_chnl_valid   (sccm_mst_ibp_rd_chnl_valid),
    .sccm_mst_ibp_rd_chnl_accept  (sccm_mst_ibp_rd_chnl_accept),
    .sccm_mst_ibp_rd_chnl         (sccm_mst_ibp_rd_chnl),

    .sccm_mst_ibp_wd_chnl_valid   (sccm_mst_ibp_wd_chnl_valid),
    .sccm_mst_ibp_wd_chnl_accept  (sccm_mst_ibp_wd_chnl_accept),
    .sccm_mst_ibp_wd_chnl         (sccm_mst_ibp_wd_chnl),

    .sccm_mst_ibp_wrsp_chnl_valid (sccm_mst_ibp_wrsp_chnl_valid),
    .sccm_mst_ibp_wrsp_chnl_accept(sccm_mst_ibp_wrsp_chnl_accept),
    .sccm_mst_ibp_wrsp_chnl       (sccm_mst_ibp_wrsp_chnl),



  .dccm_dmi_ibp_cmd_valid             (dccm_dmi_ibp_cmd_valid),
  .dccm_dmi_ibp_cmd_accept            (dccm_dmi_ibp_cmd_accept),
  .dccm_dmi_ibp_cmd_read              (dccm_dmi_ibp_cmd_read),
  .dccm_dmi_ibp_cmd_addr              (dccm_dmi_ibp_cmd_addr),
  .dccm_dmi_ibp_cmd_wrap              (dccm_dmi_ibp_cmd_wrap),
  .dccm_dmi_ibp_cmd_data_size         (dccm_dmi_ibp_cmd_data_size),
  .dccm_dmi_ibp_cmd_burst_size        (dccm_dmi_ibp_cmd_burst_size),
  .dccm_dmi_ibp_cmd_prot              (dccm_dmi_ibp_cmd_prot),
  .dccm_dmi_ibp_cmd_cache             (dccm_dmi_ibp_cmd_cache),
  .dccm_dmi_ibp_cmd_lock              (dccm_dmi_ibp_cmd_lock),
  .dccm_dmi_ibp_cmd_excl              (dccm_dmi_ibp_cmd_excl),

  .dccm_dmi_ibp_rd_valid              (dccm_dmi_ibp_rd_valid),
  .dccm_dmi_ibp_rd_excl_ok            (dccm_dmi_ibp_rd_excl_ok),
  .dccm_dmi_ibp_rd_accept             (dccm_dmi_ibp_rd_accept),
  .dccm_dmi_ibp_err_rd                (dccm_dmi_ibp_err_rd),
  .dccm_dmi_ibp_rd_data               (dccm_dmi_ibp_rd_data),
  .dccm_dmi_ibp_rd_last               (dccm_dmi_ibp_rd_last),

  .dccm_dmi_ibp_wr_valid              (dccm_dmi_ibp_wr_valid),
  .dccm_dmi_ibp_wr_accept             (dccm_dmi_ibp_wr_accept),
  .dccm_dmi_ibp_wr_data               (dccm_dmi_ibp_wr_data),
  .dccm_dmi_ibp_wr_mask               (dccm_dmi_ibp_wr_mask),
  .dccm_dmi_ibp_wr_last               (dccm_dmi_ibp_wr_last),

  .dccm_dmi_ibp_wr_done               (dccm_dmi_ibp_wr_done),
  .dccm_dmi_ibp_wr_excl_done          (dccm_dmi_ibp_wr_excl_done),
  .dccm_dmi_ibp_err_wr                (dccm_dmi_ibp_err_wr),
  .dccm_dmi_ibp_wr_resp_accept        (dccm_dmi_ibp_wr_resp_accept),
  .dccm_dmi_ibp_req(dccm_dmi_ibp_req),


  .clk                                      (clk_gated_biu_sccm          ),
  .sync_rst_r                               (sync_rst_r                    ),
  .async_rst                                (async_rst                         ),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a                                    (rst_a)
);


//**************************

assign biu_dmi_idle = 1'b1
        & sccm_dmi_idle
        & (~biu_biu_sccm_clk_en)
        ;


// leda G_521_2_B on

endmodule // biu_ccm_bridge


