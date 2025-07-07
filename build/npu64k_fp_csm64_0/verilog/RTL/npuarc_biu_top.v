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
// ######    ###   #     #         ####### ####### ######
// #     #    #    #     #            #    #     # #     #
// #     #    #    #     #            #    #     # #     #
// ######     #    #     #            #    #     # ######
// #     #    #    #     #            #    #     # #
// #     #    #    #     #            #    #     # #
// ######    ###    #####  #######    #    ####### #
//
// ===========================================================================
//
// Description:
//  Verilog module of BIU top
//
// ===========================================================================

// Configuration-dependent macro definitions
//

`include "npuarc_biu_defines.v"




// Set simulation timescale
//
`include "const.def"



module npuarc_biu_top
// leda G_521_2_B off
// LMD: Use lowercase letters for all signal reg, net and port names
// LJ: Pfx may include the uppercase, so disable the lint checking rule
  (
// leda NTL_CON13C off
// LMD: non driving internal net
// LJ: Some signals bit field are indeed no driven
// leda NTL_CON37 off
// LMD: Signal/Net must read from the input port in module
// LJ: Some signals bit field are indeed not read and used




  input                                   ifu_ibp_cmd_valid,
  output                                  ifu_ibp_cmd_accept,
  input                                   ifu_ibp_cmd_read,
  input   [40                -1:0]       ifu_ibp_cmd_addr,
  input                                   ifu_ibp_cmd_wrap,
  input   [3-1:0]       ifu_ibp_cmd_data_size,
  input   [4-1:0]       ifu_ibp_cmd_burst_size,
  input   [2-1:0]       ifu_ibp_cmd_prot,
  input   [4-1:0]       ifu_ibp_cmd_cache,
  input                                   ifu_ibp_cmd_lock,
  input                                   ifu_ibp_cmd_excl,

  output                                  ifu_ibp_rd_valid,
  output                                  ifu_ibp_rd_excl_ok,
  input                                   ifu_ibp_rd_accept,
  output                                  ifu_ibp_err_rd,
  output  [64               -1:0]        ifu_ibp_rd_data,
  output                                  ifu_ibp_rd_last,

  input                                   ifu_ibp_wr_valid,
  output                                  ifu_ibp_wr_accept,
  input   [64               -1:0]        ifu_ibp_wr_data,
  input   [8  -1:0]                    ifu_ibp_wr_mask,
  input                                   ifu_ibp_wr_last,

  output                                  ifu_ibp_wr_done,
  output                                  ifu_ibp_wr_excl_done,
  output                                  ifu_ibp_err_wr,
  input                                   ifu_ibp_wr_resp_accept,




  input                                   lqwq_ibp_cmd_valid,
  output                                  lqwq_ibp_cmd_accept,
  input                                   lqwq_ibp_cmd_read,
  input   [40                -1:0]       lqwq_ibp_cmd_addr,
  input                                   lqwq_ibp_cmd_wrap,
  input   [3-1:0]       lqwq_ibp_cmd_data_size,
  input   [4-1:0]       lqwq_ibp_cmd_burst_size,
  input   [2-1:0]       lqwq_ibp_cmd_prot,
  input   [4-1:0]       lqwq_ibp_cmd_cache,
  input                                   lqwq_ibp_cmd_lock,
  input                                   lqwq_ibp_cmd_excl,

  output                                  lqwq_ibp_rd_valid,
  output                                  lqwq_ibp_rd_excl_ok,
  input                                   lqwq_ibp_rd_accept,
  output                                  lqwq_ibp_err_rd,
  output  [64               -1:0]        lqwq_ibp_rd_data,
  output                                  lqwq_ibp_rd_last,

  input                                   lqwq_ibp_wr_valid,
  output                                  lqwq_ibp_wr_accept,
  input   [64               -1:0]        lqwq_ibp_wr_data,
  input   [8  -1:0]                    lqwq_ibp_wr_mask,
  input                                   lqwq_ibp_wr_last,

  output                                  lqwq_ibp_wr_done,
  output                                  lqwq_ibp_wr_excl_done,
  output                                  lqwq_ibp_err_wr,
  input                                   lqwq_ibp_wr_resp_accept,




  input                                   dmu_rbu_ibp_cmd_valid,
  output                                  dmu_rbu_ibp_cmd_accept,
  input                                   dmu_rbu_ibp_cmd_read,
  input   [40                -1:0]       dmu_rbu_ibp_cmd_addr,
  input                                   dmu_rbu_ibp_cmd_wrap,
  input   [3-1:0]       dmu_rbu_ibp_cmd_data_size,
  input   [4-1:0]       dmu_rbu_ibp_cmd_burst_size,
  input   [2-1:0]       dmu_rbu_ibp_cmd_prot,
  input   [4-1:0]       dmu_rbu_ibp_cmd_cache,
  input                                   dmu_rbu_ibp_cmd_lock,
  input                                   dmu_rbu_ibp_cmd_excl,

  output                                  dmu_rbu_ibp_rd_valid,
  output                                  dmu_rbu_ibp_rd_excl_ok,
  input                                   dmu_rbu_ibp_rd_accept,
  output                                  dmu_rbu_ibp_err_rd,
  output  [128               -1:0]        dmu_rbu_ibp_rd_data,
  output                                  dmu_rbu_ibp_rd_last,

  input                                   dmu_rbu_ibp_wr_valid,
  output                                  dmu_rbu_ibp_wr_accept,
  input   [128               -1:0]        dmu_rbu_ibp_wr_data,
  input   [16  -1:0]                    dmu_rbu_ibp_wr_mask,
  input                                   dmu_rbu_ibp_wr_last,

  output                                  dmu_rbu_ibp_wr_done,
  output                                  dmu_rbu_ibp_wr_excl_done,
  output                                  dmu_rbu_ibp_err_wr,
  input                                   dmu_rbu_ibp_wr_resp_accept,


  input                                   dmu_wbu_ibp_cmd_valid,
  output                                  dmu_wbu_ibp_cmd_accept,
  input                                   dmu_wbu_ibp_cmd_read,
  input   [40                -1:0]       dmu_wbu_ibp_cmd_addr,
  input                                   dmu_wbu_ibp_cmd_wrap,
  input   [3-1:0]       dmu_wbu_ibp_cmd_data_size,
  input   [4-1:0]       dmu_wbu_ibp_cmd_burst_size,
  input   [2-1:0]       dmu_wbu_ibp_cmd_prot,
  input   [4-1:0]       dmu_wbu_ibp_cmd_cache,
  input                                   dmu_wbu_ibp_cmd_lock,
  input                                   dmu_wbu_ibp_cmd_excl,

  output                                  dmu_wbu_ibp_rd_valid,
  output                                  dmu_wbu_ibp_rd_excl_ok,
  input                                   dmu_wbu_ibp_rd_accept,
  output                                  dmu_wbu_ibp_err_rd,
  output  [128               -1:0]        dmu_wbu_ibp_rd_data,
  output                                  dmu_wbu_ibp_rd_last,

  input                                   dmu_wbu_ibp_wr_valid,
  output                                  dmu_wbu_ibp_wr_accept,
  input   [128               -1:0]        dmu_wbu_ibp_wr_data,
  input   [16  -1:0]                    dmu_wbu_ibp_wr_mask,
  input                                   dmu_wbu_ibp_wr_last,

  output                                  dmu_wbu_ibp_wr_done,
  output                                  dmu_wbu_ibp_wr_excl_done,
  output                                  dmu_wbu_ibp_err_wr,
  input                                   dmu_wbu_ibp_wr_resp_accept,



  output                                  cbu_axi_arvalid,
  input                                   cbu_axi_arready,
  output  [4              -1:0]       cbu_axi_arid,
  output  [40                -1:0]       cbu_axi_araddr,
  output  [2-1:0]       cbu_axi_arburst,
  output  [4-1:0]       cbu_axi_arlen,
  output  [3-1:0]       cbu_axi_arsize,
  output  [4-1:0]       cbu_axi_arcache,
  output  [3-1:0]       cbu_axi_arprot,
  output  [2-1:0]       cbu_axi_arlock,

  input                                   cbu_axi_rvalid,
  output                                  cbu_axi_rready,
  input   [4              -1:0]       cbu_axi_rid,
  input   [64                -1:0]       cbu_axi_rdata,
  input   [2-1:0]       cbu_axi_rresp,
  input                                   cbu_axi_rlast,

  output                                  cbu_axi_awvalid,
  input                                   cbu_axi_awready,
  output  [4              -1:0]       cbu_axi_awid,
  output  [40            -1:0]           cbu_axi_awaddr,
  output  [2-1:0]       cbu_axi_awburst,
  output  [4-1:0]       cbu_axi_awlen,
  output  [3-1:0]       cbu_axi_awsize,
  output  [4-1:0]       cbu_axi_awcache,
  output  [3-1:0]       cbu_axi_awprot,
  output  [2-1:0]       cbu_axi_awlock,

  output  [4              -1:0]       cbu_axi_wid,
  output                                  cbu_axi_wvalid,
  input                                   cbu_axi_wready,
  output  [64              -1:0]         cbu_axi_wdata,
  output  [(64          /8)-1:0]         cbu_axi_wstrb,
  output                                  cbu_axi_wlast,

  input                                   cbu_axi_bvalid,
  output                                  cbu_axi_bready,
  input   [4              -1:0]       cbu_axi_bid,
  input   [2-1:0]       cbu_axi_bresp,






// leda NTL_CON37 on
// leda NTL_CON13C on


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















/////////////////////////////////////////////////////////
// Clock signals
//
// support for seperate clk
// clock enable signal to control the 1:N clock ratios
  input                                mbus_clk_en,
  input                                dbus_clk_en,



// <core_pfx>biu_dmi_clk_en_req is asserted after received the transactions at DMI
// target interface. The core clock might be temporarily switched on during
// sleep or halt state to service requests from DMI target interface.
  output                               biu_dmi_clk_en_req,


// leda NTL_CON13C off
// LMD: non driving internal net
// LJ: Some signals are indeed non driving when DMI port is not configured on
// leda NTL_CON37 off
// LMD: Signal/Net must read from the input port in module
// LJ: Some signals bit field are indeed not read and used when DMI port is not configured on
  output                                   biu2pdm_idle,
  output                                   biu_l1gt_clk_enable,



  input                                    biu_l1_cg_dis,
  input                                    biu_accept_en,
  output                                   biu2pdm_l2c_idle,
//
// leda NTL_CON13C on
// leda NTL_CON37 on
  input                                rst_a, // reset signal
  input                                nmi_restart_r, // NMI reset signal
  input                                clk_gated,
  input                                clk_ungated,
  input                                test_mode
);




// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning

// spyglass disable_block Reset_info09a
// SMD: reset net unconstrained
// SJ: is constrained
wire rst;
// spyglass enable_block Reset_info09a

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: This signal is only used for the DMI/IOC slave bus port
wire sync_rst_r;
// leda NTL_CON13A on

npuarc_biu_reset_ctrl u_biu_reset_ctrl(
  .clk                        (clk_gated),
  .rst_a                      (rst_a),

// spyglass disable_block W402b
// SMD: is gated or internally generated
// SJ: do not care this wrn
  .rst                        (rst),
// spyglass enable_block W402b

// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
  .sync_rst_r                 (sync_rst_r),
// spyglass enable_block UnloadedOutTerm-ML

  .test_mode                  (test_mode)
);


  wire                                  bfed_ifu_merg_ibp_cmd_valid;
  wire                                  bfed_ifu_merg_ibp_cmd_accept;
  wire                                  bfed_ifu_merg_ibp_cmd_read;
  wire  [40                -1:0]       bfed_ifu_merg_ibp_cmd_addr;
  wire                                  bfed_ifu_merg_ibp_cmd_wrap;
  wire  [3-1:0]       bfed_ifu_merg_ibp_cmd_data_size;
  wire  [4-1:0]       bfed_ifu_merg_ibp_cmd_burst_size;
  wire  [2-1:0]       bfed_ifu_merg_ibp_cmd_prot;
  wire  [4-1:0]       bfed_ifu_merg_ibp_cmd_cache;
  wire                                  bfed_ifu_merg_ibp_cmd_lock;
  wire                                  bfed_ifu_merg_ibp_cmd_excl;

  wire                                  bfed_ifu_merg_ibp_rd_valid;
  wire                                  bfed_ifu_merg_ibp_rd_excl_ok;
  wire                                  bfed_ifu_merg_ibp_rd_accept;
  wire                                  bfed_ifu_merg_ibp_err_rd;
  wire  [64               -1:0]        bfed_ifu_merg_ibp_rd_data;
  wire                                  bfed_ifu_merg_ibp_rd_last;

  wire                                  bfed_ifu_merg_ibp_wr_valid;
  wire                                  bfed_ifu_merg_ibp_wr_accept;
  wire  [64               -1:0]        bfed_ifu_merg_ibp_wr_data;
  wire  [8  -1:0]                    bfed_ifu_merg_ibp_wr_mask;
  wire                                  bfed_ifu_merg_ibp_wr_last;

  wire                                  bfed_ifu_merg_ibp_wr_done;
  wire                                  bfed_ifu_merg_ibp_wr_excl_done;
  wire                                  bfed_ifu_merg_ibp_err_wr;
  wire                                  bfed_ifu_merg_ibp_wr_resp_accept;

  wire                                  bfed_lq_wq_ibp_cmd_valid;
  wire                                  bfed_lq_wq_ibp_cmd_accept;
  wire                                  bfed_lq_wq_ibp_cmd_read;
  wire  [40                -1:0]       bfed_lq_wq_ibp_cmd_addr;
  wire                                  bfed_lq_wq_ibp_cmd_wrap;
  wire  [3-1:0]       bfed_lq_wq_ibp_cmd_data_size;
  wire  [4-1:0]       bfed_lq_wq_ibp_cmd_burst_size;
  wire  [2-1:0]       bfed_lq_wq_ibp_cmd_prot;
  wire  [4-1:0]       bfed_lq_wq_ibp_cmd_cache;
  wire                                  bfed_lq_wq_ibp_cmd_lock;
  wire                                  bfed_lq_wq_ibp_cmd_excl;

  wire                                  bfed_lq_wq_ibp_rd_valid;
  wire                                  bfed_lq_wq_ibp_rd_excl_ok;
  wire                                  bfed_lq_wq_ibp_rd_accept;
  wire                                  bfed_lq_wq_ibp_err_rd;
  wire  [64               -1:0]        bfed_lq_wq_ibp_rd_data;
  wire                                  bfed_lq_wq_ibp_rd_last;

  wire                                  bfed_lq_wq_ibp_wr_valid;
  wire                                  bfed_lq_wq_ibp_wr_accept;
  wire  [64               -1:0]        bfed_lq_wq_ibp_wr_data;
  wire  [8  -1:0]                    bfed_lq_wq_ibp_wr_mask;
  wire                                  bfed_lq_wq_ibp_wr_last;

  wire                                  bfed_lq_wq_ibp_wr_done;
  wire                                  bfed_lq_wq_ibp_wr_excl_done;
  wire                                  bfed_lq_wq_ibp_err_wr;
  wire                                  bfed_lq_wq_ibp_wr_resp_accept;

  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_read;
  wire  [40                -1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap;
  wire  [3-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size;
  wire  [4-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size;
  wire  [2-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot;
  wire  [4-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl;

  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_valid;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_accept;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_err_rd;
  wire  [128               -1:0]        bfed_dmu_rbu_dmu_wbu_ibp_rd_data;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_last;

  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_valid;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_accept;
  wire  [128               -1:0]        bfed_dmu_rbu_dmu_wbu_ibp_wr_data;
  wire  [16  -1:0]                    bfed_dmu_rbu_dmu_wbu_ibp_wr_mask;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_last;

  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_done;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_err_wr;
  wire                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept;




wire biu_l1_clock_active;

reg  biu_ratio_l1_clock_active;





wire biu_preprc_ibp_idle;
wire biu_preprc_l2c_ibp_idle;

//////////////////////////////////////////////////////////////
//
// To reduce dynamic power consumed on clock network,
// need to support automatic clock gating with SW program control
//
// the high-level clock gating will be added on clock root
// the clock gate enable signals is registered to avoid timing
// issue

//  There would be some gap cycles to monitor incoming transaction
//   and respond transactions
//    -- handshake valid/accept cutting on all intput ports is needed

//////////////////////////////////////////////////////////////




  wire                                  ifu_cvt_ibp_cmd_valid;
  wire                                  ifu_cvt_ibp_cmd_accept;
  wire                                  ifu_cvt_ibp_cmd_read;
  wire  [40                -1:0]       ifu_cvt_ibp_cmd_addr;
  wire                                  ifu_cvt_ibp_cmd_wrap;
  wire  [3-1:0]       ifu_cvt_ibp_cmd_data_size;
  wire  [4-1:0]       ifu_cvt_ibp_cmd_burst_size;
  wire  [2-1:0]       ifu_cvt_ibp_cmd_prot;
  wire  [4-1:0]       ifu_cvt_ibp_cmd_cache;
  wire                                  ifu_cvt_ibp_cmd_lock;
  wire                                  ifu_cvt_ibp_cmd_excl;

  wire                                  ifu_cvt_ibp_rd_valid;
  wire                                  ifu_cvt_ibp_rd_excl_ok;
  wire                                  ifu_cvt_ibp_rd_accept;
  wire                                  ifu_cvt_ibp_err_rd;
  wire  [64               -1:0]        ifu_cvt_ibp_rd_data;
  wire                                  ifu_cvt_ibp_rd_last;

  wire                                  ifu_cvt_ibp_wr_valid;
  wire                                  ifu_cvt_ibp_wr_accept;
  wire  [64               -1:0]        ifu_cvt_ibp_wr_data;
  wire  [8  -1:0]                    ifu_cvt_ibp_wr_mask;
  wire                                  ifu_cvt_ibp_wr_last;

  wire                                  ifu_cvt_ibp_wr_done;
  wire                                  ifu_cvt_ibp_wr_excl_done;
  wire                                  ifu_cvt_ibp_err_wr;
  wire                                  ifu_cvt_ibp_wr_resp_accept;

assign ifu_cvt_ibp_cmd_valid      = ifu_ibp_cmd_valid & biu_l1_clock_active;
assign ifu_ibp_cmd_accept       = ifu_cvt_ibp_cmd_accept & biu_l1_clock_active;
assign ifu_cvt_ibp_cmd_read       = ifu_ibp_cmd_read;
assign ifu_cvt_ibp_cmd_addr       = ifu_ibp_cmd_addr;
assign ifu_cvt_ibp_cmd_wrap       = ifu_ibp_cmd_wrap;
assign ifu_cvt_ibp_cmd_data_size  = ifu_ibp_cmd_data_size;
assign ifu_cvt_ibp_cmd_burst_size = ifu_ibp_cmd_burst_size;
assign ifu_cvt_ibp_cmd_prot       = ifu_ibp_cmd_prot;
assign ifu_cvt_ibp_cmd_cache      = ifu_ibp_cmd_cache;
assign ifu_cvt_ibp_cmd_lock       = ifu_ibp_cmd_lock;
assign ifu_cvt_ibp_cmd_excl       = ifu_ibp_cmd_excl;

assign ifu_ibp_rd_valid        = ifu_cvt_ibp_rd_valid;
assign ifu_ibp_rd_excl_ok      = ifu_cvt_ibp_rd_excl_ok;
assign ifu_cvt_ibp_rd_accept      = ifu_ibp_rd_accept;
assign ifu_ibp_err_rd          = ifu_cvt_ibp_err_rd;
assign ifu_ibp_rd_data         = ifu_cvt_ibp_rd_data;
assign ifu_ibp_rd_last         = ifu_cvt_ibp_rd_last;

assign ifu_cvt_ibp_wr_valid       = ifu_ibp_wr_valid & biu_l1_clock_active;
assign ifu_ibp_wr_accept        = ifu_cvt_ibp_wr_accept & biu_l1_clock_active;
assign ifu_cvt_ibp_wr_data        = ifu_ibp_wr_data;
assign ifu_cvt_ibp_wr_mask        = ifu_ibp_wr_mask;
assign ifu_cvt_ibp_wr_last        = ifu_ibp_wr_last;

assign ifu_ibp_wr_done         = ifu_cvt_ibp_wr_done;
assign ifu_ibp_wr_excl_done    = ifu_cvt_ibp_wr_excl_done;
assign ifu_ibp_err_wr          = ifu_cvt_ibp_err_wr;
assign ifu_cvt_ibp_wr_resp_accept = ifu_ibp_wr_resp_accept;






  wire                                  lqwq_cvt_ibp_cmd_valid;
  wire                                  lqwq_cvt_ibp_cmd_accept;
  wire                                  lqwq_cvt_ibp_cmd_read;
  wire  [40                -1:0]       lqwq_cvt_ibp_cmd_addr;
  wire                                  lqwq_cvt_ibp_cmd_wrap;
  wire  [3-1:0]       lqwq_cvt_ibp_cmd_data_size;
  wire  [4-1:0]       lqwq_cvt_ibp_cmd_burst_size;
  wire  [2-1:0]       lqwq_cvt_ibp_cmd_prot;
  wire  [4-1:0]       lqwq_cvt_ibp_cmd_cache;
  wire                                  lqwq_cvt_ibp_cmd_lock;
  wire                                  lqwq_cvt_ibp_cmd_excl;

  wire                                  lqwq_cvt_ibp_rd_valid;
  wire                                  lqwq_cvt_ibp_rd_excl_ok;
  wire                                  lqwq_cvt_ibp_rd_accept;
  wire                                  lqwq_cvt_ibp_err_rd;
  wire  [64               -1:0]        lqwq_cvt_ibp_rd_data;
  wire                                  lqwq_cvt_ibp_rd_last;

  wire                                  lqwq_cvt_ibp_wr_valid;
  wire                                  lqwq_cvt_ibp_wr_accept;
  wire  [64               -1:0]        lqwq_cvt_ibp_wr_data;
  wire  [8  -1:0]                    lqwq_cvt_ibp_wr_mask;
  wire                                  lqwq_cvt_ibp_wr_last;

  wire                                  lqwq_cvt_ibp_wr_done;
  wire                                  lqwq_cvt_ibp_wr_excl_done;
  wire                                  lqwq_cvt_ibp_err_wr;
  wire                                  lqwq_cvt_ibp_wr_resp_accept;

assign lqwq_cvt_ibp_cmd_valid      = lqwq_ibp_cmd_valid & biu_l1_clock_active;
assign lqwq_ibp_cmd_accept       = lqwq_cvt_ibp_cmd_accept & biu_l1_clock_active;
assign lqwq_cvt_ibp_cmd_read       = lqwq_ibp_cmd_read;
assign lqwq_cvt_ibp_cmd_addr       = lqwq_ibp_cmd_addr;
assign lqwq_cvt_ibp_cmd_wrap       = lqwq_ibp_cmd_wrap;
assign lqwq_cvt_ibp_cmd_data_size  = lqwq_ibp_cmd_data_size;
assign lqwq_cvt_ibp_cmd_burst_size = lqwq_ibp_cmd_burst_size;
assign lqwq_cvt_ibp_cmd_prot       = lqwq_ibp_cmd_prot;
assign lqwq_cvt_ibp_cmd_cache      = lqwq_ibp_cmd_cache;
assign lqwq_cvt_ibp_cmd_lock       = lqwq_ibp_cmd_lock;
assign lqwq_cvt_ibp_cmd_excl       = lqwq_ibp_cmd_excl;

assign lqwq_ibp_rd_valid        = lqwq_cvt_ibp_rd_valid;
assign lqwq_ibp_rd_excl_ok      = lqwq_cvt_ibp_rd_excl_ok;
assign lqwq_cvt_ibp_rd_accept      = lqwq_ibp_rd_accept;
assign lqwq_ibp_err_rd          = lqwq_cvt_ibp_err_rd;
assign lqwq_ibp_rd_data         = lqwq_cvt_ibp_rd_data;
assign lqwq_ibp_rd_last         = lqwq_cvt_ibp_rd_last;

assign lqwq_cvt_ibp_wr_valid       = lqwq_ibp_wr_valid & biu_l1_clock_active;
assign lqwq_ibp_wr_accept        = lqwq_cvt_ibp_wr_accept & biu_l1_clock_active;
assign lqwq_cvt_ibp_wr_data        = lqwq_ibp_wr_data;
assign lqwq_cvt_ibp_wr_mask        = lqwq_ibp_wr_mask;
assign lqwq_cvt_ibp_wr_last        = lqwq_ibp_wr_last;

assign lqwq_ibp_wr_done         = lqwq_cvt_ibp_wr_done;
assign lqwq_ibp_wr_excl_done    = lqwq_cvt_ibp_wr_excl_done;
assign lqwq_ibp_err_wr          = lqwq_cvt_ibp_err_wr;
assign lqwq_cvt_ibp_wr_resp_accept = lqwq_ibp_wr_resp_accept;






  wire                                  dmu_rbu_cvt_ibp_cmd_valid;
  wire                                  dmu_rbu_cvt_ibp_cmd_accept;
  wire                                  dmu_rbu_cvt_ibp_cmd_read;
  wire  [40                -1:0]       dmu_rbu_cvt_ibp_cmd_addr;
  wire                                  dmu_rbu_cvt_ibp_cmd_wrap;
  wire  [3-1:0]       dmu_rbu_cvt_ibp_cmd_data_size;
  wire  [4-1:0]       dmu_rbu_cvt_ibp_cmd_burst_size;
  wire  [2-1:0]       dmu_rbu_cvt_ibp_cmd_prot;
  wire  [4-1:0]       dmu_rbu_cvt_ibp_cmd_cache;
  wire                                  dmu_rbu_cvt_ibp_cmd_lock;
  wire                                  dmu_rbu_cvt_ibp_cmd_excl;

  wire                                  dmu_rbu_cvt_ibp_rd_valid;
  wire                                  dmu_rbu_cvt_ibp_rd_excl_ok;
  wire                                  dmu_rbu_cvt_ibp_rd_accept;
  wire                                  dmu_rbu_cvt_ibp_err_rd;
  wire  [128               -1:0]        dmu_rbu_cvt_ibp_rd_data;
  wire                                  dmu_rbu_cvt_ibp_rd_last;

  wire                                  dmu_rbu_cvt_ibp_wr_valid;
  wire                                  dmu_rbu_cvt_ibp_wr_accept;
  wire  [128               -1:0]        dmu_rbu_cvt_ibp_wr_data;
  wire  [16  -1:0]                    dmu_rbu_cvt_ibp_wr_mask;
  wire                                  dmu_rbu_cvt_ibp_wr_last;

  wire                                  dmu_rbu_cvt_ibp_wr_done;
  wire                                  dmu_rbu_cvt_ibp_wr_excl_done;
  wire                                  dmu_rbu_cvt_ibp_err_wr;
  wire                                  dmu_rbu_cvt_ibp_wr_resp_accept;

assign dmu_rbu_cvt_ibp_cmd_valid      = dmu_rbu_ibp_cmd_valid & biu_l1_clock_active;
assign dmu_rbu_ibp_cmd_accept       = dmu_rbu_cvt_ibp_cmd_accept & biu_l1_clock_active;
assign dmu_rbu_cvt_ibp_cmd_read       = dmu_rbu_ibp_cmd_read;
assign dmu_rbu_cvt_ibp_cmd_addr       = dmu_rbu_ibp_cmd_addr;
assign dmu_rbu_cvt_ibp_cmd_wrap       = dmu_rbu_ibp_cmd_wrap;
assign dmu_rbu_cvt_ibp_cmd_data_size  = dmu_rbu_ibp_cmd_data_size;
assign dmu_rbu_cvt_ibp_cmd_burst_size = dmu_rbu_ibp_cmd_burst_size;
assign dmu_rbu_cvt_ibp_cmd_prot       = dmu_rbu_ibp_cmd_prot;
assign dmu_rbu_cvt_ibp_cmd_cache      = dmu_rbu_ibp_cmd_cache;
assign dmu_rbu_cvt_ibp_cmd_lock       = dmu_rbu_ibp_cmd_lock;
assign dmu_rbu_cvt_ibp_cmd_excl       = dmu_rbu_ibp_cmd_excl;

assign dmu_rbu_ibp_rd_valid        = dmu_rbu_cvt_ibp_rd_valid;
assign dmu_rbu_ibp_rd_excl_ok      = dmu_rbu_cvt_ibp_rd_excl_ok;
assign dmu_rbu_cvt_ibp_rd_accept      = dmu_rbu_ibp_rd_accept;
assign dmu_rbu_ibp_err_rd          = dmu_rbu_cvt_ibp_err_rd;
assign dmu_rbu_ibp_rd_data         = dmu_rbu_cvt_ibp_rd_data;
assign dmu_rbu_ibp_rd_last         = dmu_rbu_cvt_ibp_rd_last;

assign dmu_rbu_cvt_ibp_wr_valid       = dmu_rbu_ibp_wr_valid & biu_l1_clock_active;
assign dmu_rbu_ibp_wr_accept        = dmu_rbu_cvt_ibp_wr_accept & biu_l1_clock_active;
assign dmu_rbu_cvt_ibp_wr_data        = dmu_rbu_ibp_wr_data;
assign dmu_rbu_cvt_ibp_wr_mask        = dmu_rbu_ibp_wr_mask;
assign dmu_rbu_cvt_ibp_wr_last        = dmu_rbu_ibp_wr_last;

assign dmu_rbu_ibp_wr_done         = dmu_rbu_cvt_ibp_wr_done;
assign dmu_rbu_ibp_wr_excl_done    = dmu_rbu_cvt_ibp_wr_excl_done;
assign dmu_rbu_ibp_err_wr          = dmu_rbu_cvt_ibp_err_wr;
assign dmu_rbu_cvt_ibp_wr_resp_accept = dmu_rbu_ibp_wr_resp_accept;



  wire                                  dmu_wbu_cvt_ibp_cmd_valid;
  wire                                  dmu_wbu_cvt_ibp_cmd_accept;
  wire                                  dmu_wbu_cvt_ibp_cmd_read;
  wire  [40                -1:0]       dmu_wbu_cvt_ibp_cmd_addr;
  wire                                  dmu_wbu_cvt_ibp_cmd_wrap;
  wire  [3-1:0]       dmu_wbu_cvt_ibp_cmd_data_size;
  wire  [4-1:0]       dmu_wbu_cvt_ibp_cmd_burst_size;
  wire  [2-1:0]       dmu_wbu_cvt_ibp_cmd_prot;
  wire  [4-1:0]       dmu_wbu_cvt_ibp_cmd_cache;
  wire                                  dmu_wbu_cvt_ibp_cmd_lock;
  wire                                  dmu_wbu_cvt_ibp_cmd_excl;

  wire                                  dmu_wbu_cvt_ibp_rd_valid;
  wire                                  dmu_wbu_cvt_ibp_rd_excl_ok;
  wire                                  dmu_wbu_cvt_ibp_rd_accept;
  wire                                  dmu_wbu_cvt_ibp_err_rd;
  wire  [128               -1:0]        dmu_wbu_cvt_ibp_rd_data;
  wire                                  dmu_wbu_cvt_ibp_rd_last;

  wire                                  dmu_wbu_cvt_ibp_wr_valid;
  wire                                  dmu_wbu_cvt_ibp_wr_accept;
  wire  [128               -1:0]        dmu_wbu_cvt_ibp_wr_data;
  wire  [16  -1:0]                    dmu_wbu_cvt_ibp_wr_mask;
  wire                                  dmu_wbu_cvt_ibp_wr_last;

  wire                                  dmu_wbu_cvt_ibp_wr_done;
  wire                                  dmu_wbu_cvt_ibp_wr_excl_done;
  wire                                  dmu_wbu_cvt_ibp_err_wr;
  wire                                  dmu_wbu_cvt_ibp_wr_resp_accept;

assign dmu_wbu_cvt_ibp_cmd_valid      = dmu_wbu_ibp_cmd_valid & biu_l1_clock_active;
assign dmu_wbu_ibp_cmd_accept       = dmu_wbu_cvt_ibp_cmd_accept & biu_l1_clock_active;
assign dmu_wbu_cvt_ibp_cmd_read       = dmu_wbu_ibp_cmd_read;
assign dmu_wbu_cvt_ibp_cmd_addr       = dmu_wbu_ibp_cmd_addr;
assign dmu_wbu_cvt_ibp_cmd_wrap       = dmu_wbu_ibp_cmd_wrap;
assign dmu_wbu_cvt_ibp_cmd_data_size  = dmu_wbu_ibp_cmd_data_size;
assign dmu_wbu_cvt_ibp_cmd_burst_size = dmu_wbu_ibp_cmd_burst_size;
assign dmu_wbu_cvt_ibp_cmd_prot       = dmu_wbu_ibp_cmd_prot;
assign dmu_wbu_cvt_ibp_cmd_cache      = dmu_wbu_ibp_cmd_cache;
assign dmu_wbu_cvt_ibp_cmd_lock       = dmu_wbu_ibp_cmd_lock;
assign dmu_wbu_cvt_ibp_cmd_excl       = dmu_wbu_ibp_cmd_excl;

assign dmu_wbu_ibp_rd_valid        = dmu_wbu_cvt_ibp_rd_valid;
assign dmu_wbu_ibp_rd_excl_ok      = dmu_wbu_cvt_ibp_rd_excl_ok;
assign dmu_wbu_cvt_ibp_rd_accept      = dmu_wbu_ibp_rd_accept;
assign dmu_wbu_ibp_err_rd          = dmu_wbu_cvt_ibp_err_rd;
assign dmu_wbu_ibp_rd_data         = dmu_wbu_cvt_ibp_rd_data;
assign dmu_wbu_ibp_rd_last         = dmu_wbu_cvt_ibp_rd_last;

assign dmu_wbu_cvt_ibp_wr_valid       = dmu_wbu_ibp_wr_valid & biu_l1_clock_active;
assign dmu_wbu_ibp_wr_accept        = dmu_wbu_cvt_ibp_wr_accept & biu_l1_clock_active;
assign dmu_wbu_cvt_ibp_wr_data        = dmu_wbu_ibp_wr_data;
assign dmu_wbu_cvt_ibp_wr_mask        = dmu_wbu_ibp_wr_mask;
assign dmu_wbu_cvt_ibp_wr_last        = dmu_wbu_ibp_wr_last;

assign dmu_wbu_ibp_wr_done         = dmu_wbu_cvt_ibp_wr_done;
assign dmu_wbu_ibp_wr_excl_done    = dmu_wbu_cvt_ibp_wr_excl_done;
assign dmu_wbu_ibp_err_wr          = dmu_wbu_cvt_ibp_err_wr;
assign dmu_wbu_cvt_ibp_wr_resp_accept = dmu_wbu_ibp_wr_resp_accept;



npuarc_biu_ibp_preprc u_biu_ibp_preprc(



  .ifu_ibp_cmd_valid             (ifu_cvt_ibp_cmd_valid),
  .ifu_ibp_cmd_accept            (ifu_cvt_ibp_cmd_accept),
  .ifu_ibp_cmd_read              (ifu_cvt_ibp_cmd_read),
  .ifu_ibp_cmd_addr              (ifu_cvt_ibp_cmd_addr),
  .ifu_ibp_cmd_wrap              (ifu_cvt_ibp_cmd_wrap),
  .ifu_ibp_cmd_data_size         (ifu_cvt_ibp_cmd_data_size),
  .ifu_ibp_cmd_burst_size        (ifu_cvt_ibp_cmd_burst_size),
  .ifu_ibp_cmd_prot              (ifu_cvt_ibp_cmd_prot),
  .ifu_ibp_cmd_cache             (ifu_cvt_ibp_cmd_cache),
  .ifu_ibp_cmd_lock              (ifu_cvt_ibp_cmd_lock),
  .ifu_ibp_cmd_excl              (ifu_cvt_ibp_cmd_excl),

  .ifu_ibp_rd_valid              (ifu_cvt_ibp_rd_valid),
  .ifu_ibp_rd_excl_ok            (ifu_cvt_ibp_rd_excl_ok),
  .ifu_ibp_rd_accept             (ifu_cvt_ibp_rd_accept),
  .ifu_ibp_err_rd                (ifu_cvt_ibp_err_rd),
  .ifu_ibp_rd_data               (ifu_cvt_ibp_rd_data),
  .ifu_ibp_rd_last               (ifu_cvt_ibp_rd_last),

  .ifu_ibp_wr_valid              (ifu_cvt_ibp_wr_valid),
  .ifu_ibp_wr_accept             (ifu_cvt_ibp_wr_accept),
  .ifu_ibp_wr_data               (ifu_cvt_ibp_wr_data),
  .ifu_ibp_wr_mask               (ifu_cvt_ibp_wr_mask),
  .ifu_ibp_wr_last               (ifu_cvt_ibp_wr_last),

  .ifu_ibp_wr_done               (ifu_cvt_ibp_wr_done),
  .ifu_ibp_wr_excl_done          (ifu_cvt_ibp_wr_excl_done),
  .ifu_ibp_err_wr                (ifu_cvt_ibp_err_wr),
  .ifu_ibp_wr_resp_accept        (ifu_cvt_ibp_wr_resp_accept),



  .bfed_ifu_merg_ibp_cmd_valid             (bfed_ifu_merg_ibp_cmd_valid),
  .bfed_ifu_merg_ibp_cmd_accept            (bfed_ifu_merg_ibp_cmd_accept),
  .bfed_ifu_merg_ibp_cmd_read              (bfed_ifu_merg_ibp_cmd_read),
  .bfed_ifu_merg_ibp_cmd_addr              (bfed_ifu_merg_ibp_cmd_addr),
  .bfed_ifu_merg_ibp_cmd_wrap              (bfed_ifu_merg_ibp_cmd_wrap),
  .bfed_ifu_merg_ibp_cmd_data_size         (bfed_ifu_merg_ibp_cmd_data_size),
  .bfed_ifu_merg_ibp_cmd_burst_size        (bfed_ifu_merg_ibp_cmd_burst_size),
  .bfed_ifu_merg_ibp_cmd_prot              (bfed_ifu_merg_ibp_cmd_prot),
  .bfed_ifu_merg_ibp_cmd_cache             (bfed_ifu_merg_ibp_cmd_cache),
  .bfed_ifu_merg_ibp_cmd_lock              (bfed_ifu_merg_ibp_cmd_lock),
  .bfed_ifu_merg_ibp_cmd_excl              (bfed_ifu_merg_ibp_cmd_excl),

  .bfed_ifu_merg_ibp_rd_valid              (bfed_ifu_merg_ibp_rd_valid),
  .bfed_ifu_merg_ibp_rd_excl_ok            (bfed_ifu_merg_ibp_rd_excl_ok),
  .bfed_ifu_merg_ibp_rd_accept             (bfed_ifu_merg_ibp_rd_accept),
  .bfed_ifu_merg_ibp_err_rd                (bfed_ifu_merg_ibp_err_rd),
  .bfed_ifu_merg_ibp_rd_data               (bfed_ifu_merg_ibp_rd_data),
  .bfed_ifu_merg_ibp_rd_last               (bfed_ifu_merg_ibp_rd_last),

  .bfed_ifu_merg_ibp_wr_valid              (bfed_ifu_merg_ibp_wr_valid),
  .bfed_ifu_merg_ibp_wr_accept             (bfed_ifu_merg_ibp_wr_accept),
  .bfed_ifu_merg_ibp_wr_data               (bfed_ifu_merg_ibp_wr_data),
  .bfed_ifu_merg_ibp_wr_mask               (bfed_ifu_merg_ibp_wr_mask),
  .bfed_ifu_merg_ibp_wr_last               (bfed_ifu_merg_ibp_wr_last),

  .bfed_ifu_merg_ibp_wr_done               (bfed_ifu_merg_ibp_wr_done),
  .bfed_ifu_merg_ibp_wr_excl_done          (bfed_ifu_merg_ibp_wr_excl_done),
  .bfed_ifu_merg_ibp_err_wr                (bfed_ifu_merg_ibp_err_wr),
  .bfed_ifu_merg_ibp_wr_resp_accept        (bfed_ifu_merg_ibp_wr_resp_accept),



  .lqwq_ibp_cmd_valid             (lqwq_cvt_ibp_cmd_valid),
  .lqwq_ibp_cmd_accept            (lqwq_cvt_ibp_cmd_accept),
  .lqwq_ibp_cmd_read              (lqwq_cvt_ibp_cmd_read),
  .lqwq_ibp_cmd_addr              (lqwq_cvt_ibp_cmd_addr),
  .lqwq_ibp_cmd_wrap              (lqwq_cvt_ibp_cmd_wrap),
  .lqwq_ibp_cmd_data_size         (lqwq_cvt_ibp_cmd_data_size),
  .lqwq_ibp_cmd_burst_size        (lqwq_cvt_ibp_cmd_burst_size),
  .lqwq_ibp_cmd_prot              (lqwq_cvt_ibp_cmd_prot),
  .lqwq_ibp_cmd_cache             (lqwq_cvt_ibp_cmd_cache),
  .lqwq_ibp_cmd_lock              (lqwq_cvt_ibp_cmd_lock),
  .lqwq_ibp_cmd_excl              (lqwq_cvt_ibp_cmd_excl),

  .lqwq_ibp_rd_valid              (lqwq_cvt_ibp_rd_valid),
  .lqwq_ibp_rd_excl_ok            (lqwq_cvt_ibp_rd_excl_ok),
  .lqwq_ibp_rd_accept             (lqwq_cvt_ibp_rd_accept),
  .lqwq_ibp_err_rd                (lqwq_cvt_ibp_err_rd),
  .lqwq_ibp_rd_data               (lqwq_cvt_ibp_rd_data),
  .lqwq_ibp_rd_last               (lqwq_cvt_ibp_rd_last),

  .lqwq_ibp_wr_valid              (lqwq_cvt_ibp_wr_valid),
  .lqwq_ibp_wr_accept             (lqwq_cvt_ibp_wr_accept),
  .lqwq_ibp_wr_data               (lqwq_cvt_ibp_wr_data),
  .lqwq_ibp_wr_mask               (lqwq_cvt_ibp_wr_mask),
  .lqwq_ibp_wr_last               (lqwq_cvt_ibp_wr_last),

  .lqwq_ibp_wr_done               (lqwq_cvt_ibp_wr_done),
  .lqwq_ibp_wr_excl_done          (lqwq_cvt_ibp_wr_excl_done),
  .lqwq_ibp_err_wr                (lqwq_cvt_ibp_err_wr),
  .lqwq_ibp_wr_resp_accept        (lqwq_cvt_ibp_wr_resp_accept),



  .bfed_lq_wq_ibp_cmd_valid             (bfed_lq_wq_ibp_cmd_valid),
  .bfed_lq_wq_ibp_cmd_accept            (bfed_lq_wq_ibp_cmd_accept),
  .bfed_lq_wq_ibp_cmd_read              (bfed_lq_wq_ibp_cmd_read),
  .bfed_lq_wq_ibp_cmd_addr              (bfed_lq_wq_ibp_cmd_addr),
  .bfed_lq_wq_ibp_cmd_wrap              (bfed_lq_wq_ibp_cmd_wrap),
  .bfed_lq_wq_ibp_cmd_data_size         (bfed_lq_wq_ibp_cmd_data_size),
  .bfed_lq_wq_ibp_cmd_burst_size        (bfed_lq_wq_ibp_cmd_burst_size),
  .bfed_lq_wq_ibp_cmd_prot              (bfed_lq_wq_ibp_cmd_prot),
  .bfed_lq_wq_ibp_cmd_cache             (bfed_lq_wq_ibp_cmd_cache),
  .bfed_lq_wq_ibp_cmd_lock              (bfed_lq_wq_ibp_cmd_lock),
  .bfed_lq_wq_ibp_cmd_excl              (bfed_lq_wq_ibp_cmd_excl),

  .bfed_lq_wq_ibp_rd_valid              (bfed_lq_wq_ibp_rd_valid),
  .bfed_lq_wq_ibp_rd_excl_ok            (bfed_lq_wq_ibp_rd_excl_ok),
  .bfed_lq_wq_ibp_rd_accept             (bfed_lq_wq_ibp_rd_accept),
  .bfed_lq_wq_ibp_err_rd                (bfed_lq_wq_ibp_err_rd),
  .bfed_lq_wq_ibp_rd_data               (bfed_lq_wq_ibp_rd_data),
  .bfed_lq_wq_ibp_rd_last               (bfed_lq_wq_ibp_rd_last),

  .bfed_lq_wq_ibp_wr_valid              (bfed_lq_wq_ibp_wr_valid),
  .bfed_lq_wq_ibp_wr_accept             (bfed_lq_wq_ibp_wr_accept),
  .bfed_lq_wq_ibp_wr_data               (bfed_lq_wq_ibp_wr_data),
  .bfed_lq_wq_ibp_wr_mask               (bfed_lq_wq_ibp_wr_mask),
  .bfed_lq_wq_ibp_wr_last               (bfed_lq_wq_ibp_wr_last),

  .bfed_lq_wq_ibp_wr_done               (bfed_lq_wq_ibp_wr_done),
  .bfed_lq_wq_ibp_wr_excl_done          (bfed_lq_wq_ibp_wr_excl_done),
  .bfed_lq_wq_ibp_err_wr                (bfed_lq_wq_ibp_err_wr),
  .bfed_lq_wq_ibp_wr_resp_accept        (bfed_lq_wq_ibp_wr_resp_accept),



  .dmu_rbu_ibp_cmd_valid             (dmu_rbu_cvt_ibp_cmd_valid),
  .dmu_rbu_ibp_cmd_accept            (dmu_rbu_cvt_ibp_cmd_accept),
  .dmu_rbu_ibp_cmd_read              (dmu_rbu_cvt_ibp_cmd_read),
  .dmu_rbu_ibp_cmd_addr              (dmu_rbu_cvt_ibp_cmd_addr),
  .dmu_rbu_ibp_cmd_wrap              (dmu_rbu_cvt_ibp_cmd_wrap),
  .dmu_rbu_ibp_cmd_data_size         (dmu_rbu_cvt_ibp_cmd_data_size),
  .dmu_rbu_ibp_cmd_burst_size        (dmu_rbu_cvt_ibp_cmd_burst_size),
  .dmu_rbu_ibp_cmd_prot              (dmu_rbu_cvt_ibp_cmd_prot),
  .dmu_rbu_ibp_cmd_cache             (dmu_rbu_cvt_ibp_cmd_cache),
  .dmu_rbu_ibp_cmd_lock              (dmu_rbu_cvt_ibp_cmd_lock),
  .dmu_rbu_ibp_cmd_excl              (dmu_rbu_cvt_ibp_cmd_excl),

  .dmu_rbu_ibp_rd_valid              (dmu_rbu_cvt_ibp_rd_valid),
  .dmu_rbu_ibp_rd_excl_ok            (dmu_rbu_cvt_ibp_rd_excl_ok),
  .dmu_rbu_ibp_rd_accept             (dmu_rbu_cvt_ibp_rd_accept),
  .dmu_rbu_ibp_err_rd                (dmu_rbu_cvt_ibp_err_rd),
  .dmu_rbu_ibp_rd_data               (dmu_rbu_cvt_ibp_rd_data),
  .dmu_rbu_ibp_rd_last               (dmu_rbu_cvt_ibp_rd_last),

  .dmu_rbu_ibp_wr_valid              (dmu_rbu_cvt_ibp_wr_valid),
  .dmu_rbu_ibp_wr_accept             (dmu_rbu_cvt_ibp_wr_accept),
  .dmu_rbu_ibp_wr_data               (dmu_rbu_cvt_ibp_wr_data),
  .dmu_rbu_ibp_wr_mask               (dmu_rbu_cvt_ibp_wr_mask),
  .dmu_rbu_ibp_wr_last               (dmu_rbu_cvt_ibp_wr_last),

  .dmu_rbu_ibp_wr_done               (dmu_rbu_cvt_ibp_wr_done),
  .dmu_rbu_ibp_wr_excl_done          (dmu_rbu_cvt_ibp_wr_excl_done),
  .dmu_rbu_ibp_err_wr                (dmu_rbu_cvt_ibp_err_wr),
  .dmu_rbu_ibp_wr_resp_accept        (dmu_rbu_cvt_ibp_wr_resp_accept),


  .dmu_wbu_ibp_cmd_valid             (dmu_wbu_cvt_ibp_cmd_valid),
  .dmu_wbu_ibp_cmd_accept            (dmu_wbu_cvt_ibp_cmd_accept),
  .dmu_wbu_ibp_cmd_read              (dmu_wbu_cvt_ibp_cmd_read),
  .dmu_wbu_ibp_cmd_addr              (dmu_wbu_cvt_ibp_cmd_addr),
  .dmu_wbu_ibp_cmd_wrap              (dmu_wbu_cvt_ibp_cmd_wrap),
  .dmu_wbu_ibp_cmd_data_size         (dmu_wbu_cvt_ibp_cmd_data_size),
  .dmu_wbu_ibp_cmd_burst_size        (dmu_wbu_cvt_ibp_cmd_burst_size),
  .dmu_wbu_ibp_cmd_prot              (dmu_wbu_cvt_ibp_cmd_prot),
  .dmu_wbu_ibp_cmd_cache             (dmu_wbu_cvt_ibp_cmd_cache),
  .dmu_wbu_ibp_cmd_lock              (dmu_wbu_cvt_ibp_cmd_lock),
  .dmu_wbu_ibp_cmd_excl              (dmu_wbu_cvt_ibp_cmd_excl),

  .dmu_wbu_ibp_rd_valid              (dmu_wbu_cvt_ibp_rd_valid),
  .dmu_wbu_ibp_rd_excl_ok            (dmu_wbu_cvt_ibp_rd_excl_ok),
  .dmu_wbu_ibp_rd_accept             (dmu_wbu_cvt_ibp_rd_accept),
  .dmu_wbu_ibp_err_rd                (dmu_wbu_cvt_ibp_err_rd),
  .dmu_wbu_ibp_rd_data               (dmu_wbu_cvt_ibp_rd_data),
  .dmu_wbu_ibp_rd_last               (dmu_wbu_cvt_ibp_rd_last),

  .dmu_wbu_ibp_wr_valid              (dmu_wbu_cvt_ibp_wr_valid),
  .dmu_wbu_ibp_wr_accept             (dmu_wbu_cvt_ibp_wr_accept),
  .dmu_wbu_ibp_wr_data               (dmu_wbu_cvt_ibp_wr_data),
  .dmu_wbu_ibp_wr_mask               (dmu_wbu_cvt_ibp_wr_mask),
  .dmu_wbu_ibp_wr_last               (dmu_wbu_cvt_ibp_wr_last),

  .dmu_wbu_ibp_wr_done               (dmu_wbu_cvt_ibp_wr_done),
  .dmu_wbu_ibp_wr_excl_done          (dmu_wbu_cvt_ibp_wr_excl_done),
  .dmu_wbu_ibp_err_wr                (dmu_wbu_cvt_ibp_err_wr),
  .dmu_wbu_ibp_wr_resp_accept        (dmu_wbu_cvt_ibp_wr_resp_accept),


  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid             (bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept            (bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_read              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_read),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size         (bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size        (bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache             (bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl),

  .bfed_dmu_rbu_dmu_wbu_ibp_rd_valid              (bfed_dmu_rbu_dmu_wbu_ibp_rd_valid),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok            (bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_accept             (bfed_dmu_rbu_dmu_wbu_ibp_rd_accept),
  .bfed_dmu_rbu_dmu_wbu_ibp_err_rd                (bfed_dmu_rbu_dmu_wbu_ibp_err_rd),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_data               (bfed_dmu_rbu_dmu_wbu_ibp_rd_data),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_last               (bfed_dmu_rbu_dmu_wbu_ibp_rd_last),

  .bfed_dmu_rbu_dmu_wbu_ibp_wr_valid              (bfed_dmu_rbu_dmu_wbu_ibp_wr_valid),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_accept             (bfed_dmu_rbu_dmu_wbu_ibp_wr_accept),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_data               (bfed_dmu_rbu_dmu_wbu_ibp_wr_data),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_mask               (bfed_dmu_rbu_dmu_wbu_ibp_wr_mask),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_last               (bfed_dmu_rbu_dmu_wbu_ibp_wr_last),

  .bfed_dmu_rbu_dmu_wbu_ibp_wr_done               (bfed_dmu_rbu_dmu_wbu_ibp_wr_done),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done          (bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done),
  .bfed_dmu_rbu_dmu_wbu_ibp_err_wr                (bfed_dmu_rbu_dmu_wbu_ibp_err_wr),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept        (bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept),

  .biu_preprc_ibp_idle                      (biu_preprc_ibp_idle),
  .biu_preprc_active                        (biu_preprc_active),
  .biu_preprc_l2c_ibp_idle                  (biu_preprc_l2c_ibp_idle),
  .clk                                      (clk_gated  ),
  .nmi_restart_r                            (nmi_restart_r        ),
  .rst_a                                    (rst        )
  );








// support for seperate lbus_clk

npuarc_biu_bus_bridge u_biu_bus_bridge
  (
  .mbus_clk_en (mbus_clk_en),//





  .bfed_ifu_merg_ibp_cmd_valid             (bfed_ifu_merg_ibp_cmd_valid),
  .bfed_ifu_merg_ibp_cmd_accept            (bfed_ifu_merg_ibp_cmd_accept),
  .bfed_ifu_merg_ibp_cmd_read              (bfed_ifu_merg_ibp_cmd_read),
  .bfed_ifu_merg_ibp_cmd_addr              (bfed_ifu_merg_ibp_cmd_addr),
  .bfed_ifu_merg_ibp_cmd_wrap              (bfed_ifu_merg_ibp_cmd_wrap),
  .bfed_ifu_merg_ibp_cmd_data_size         (bfed_ifu_merg_ibp_cmd_data_size),
  .bfed_ifu_merg_ibp_cmd_burst_size        (bfed_ifu_merg_ibp_cmd_burst_size),
  .bfed_ifu_merg_ibp_cmd_prot              (bfed_ifu_merg_ibp_cmd_prot),
  .bfed_ifu_merg_ibp_cmd_cache             (bfed_ifu_merg_ibp_cmd_cache),
  .bfed_ifu_merg_ibp_cmd_lock              (bfed_ifu_merg_ibp_cmd_lock),
  .bfed_ifu_merg_ibp_cmd_excl              (bfed_ifu_merg_ibp_cmd_excl),

  .bfed_ifu_merg_ibp_rd_valid              (bfed_ifu_merg_ibp_rd_valid),
  .bfed_ifu_merg_ibp_rd_excl_ok            (bfed_ifu_merg_ibp_rd_excl_ok),
  .bfed_ifu_merg_ibp_rd_accept             (bfed_ifu_merg_ibp_rd_accept),
  .bfed_ifu_merg_ibp_err_rd                (bfed_ifu_merg_ibp_err_rd),
  .bfed_ifu_merg_ibp_rd_data               (bfed_ifu_merg_ibp_rd_data),
  .bfed_ifu_merg_ibp_rd_last               (bfed_ifu_merg_ibp_rd_last),

  .bfed_ifu_merg_ibp_wr_valid              (bfed_ifu_merg_ibp_wr_valid),
  .bfed_ifu_merg_ibp_wr_accept             (bfed_ifu_merg_ibp_wr_accept),
  .bfed_ifu_merg_ibp_wr_data               (bfed_ifu_merg_ibp_wr_data),
  .bfed_ifu_merg_ibp_wr_mask               (bfed_ifu_merg_ibp_wr_mask),
  .bfed_ifu_merg_ibp_wr_last               (bfed_ifu_merg_ibp_wr_last),

  .bfed_ifu_merg_ibp_wr_done               (bfed_ifu_merg_ibp_wr_done),
  .bfed_ifu_merg_ibp_wr_excl_done          (bfed_ifu_merg_ibp_wr_excl_done),
  .bfed_ifu_merg_ibp_err_wr                (bfed_ifu_merg_ibp_err_wr),
  .bfed_ifu_merg_ibp_wr_resp_accept        (bfed_ifu_merg_ibp_wr_resp_accept),



  .bfed_lq_wq_ibp_cmd_valid             (bfed_lq_wq_ibp_cmd_valid),
  .bfed_lq_wq_ibp_cmd_accept            (bfed_lq_wq_ibp_cmd_accept),
  .bfed_lq_wq_ibp_cmd_read              (bfed_lq_wq_ibp_cmd_read),
  .bfed_lq_wq_ibp_cmd_addr              (bfed_lq_wq_ibp_cmd_addr),
  .bfed_lq_wq_ibp_cmd_wrap              (bfed_lq_wq_ibp_cmd_wrap),
  .bfed_lq_wq_ibp_cmd_data_size         (bfed_lq_wq_ibp_cmd_data_size),
  .bfed_lq_wq_ibp_cmd_burst_size        (bfed_lq_wq_ibp_cmd_burst_size),
  .bfed_lq_wq_ibp_cmd_prot              (bfed_lq_wq_ibp_cmd_prot),
  .bfed_lq_wq_ibp_cmd_cache             (bfed_lq_wq_ibp_cmd_cache),
  .bfed_lq_wq_ibp_cmd_lock              (bfed_lq_wq_ibp_cmd_lock),
  .bfed_lq_wq_ibp_cmd_excl              (bfed_lq_wq_ibp_cmd_excl),

  .bfed_lq_wq_ibp_rd_valid              (bfed_lq_wq_ibp_rd_valid),
  .bfed_lq_wq_ibp_rd_excl_ok            (bfed_lq_wq_ibp_rd_excl_ok),
  .bfed_lq_wq_ibp_rd_accept             (bfed_lq_wq_ibp_rd_accept),
  .bfed_lq_wq_ibp_err_rd                (bfed_lq_wq_ibp_err_rd),
  .bfed_lq_wq_ibp_rd_data               (bfed_lq_wq_ibp_rd_data),
  .bfed_lq_wq_ibp_rd_last               (bfed_lq_wq_ibp_rd_last),

  .bfed_lq_wq_ibp_wr_valid              (bfed_lq_wq_ibp_wr_valid),
  .bfed_lq_wq_ibp_wr_accept             (bfed_lq_wq_ibp_wr_accept),
  .bfed_lq_wq_ibp_wr_data               (bfed_lq_wq_ibp_wr_data),
  .bfed_lq_wq_ibp_wr_mask               (bfed_lq_wq_ibp_wr_mask),
  .bfed_lq_wq_ibp_wr_last               (bfed_lq_wq_ibp_wr_last),

  .bfed_lq_wq_ibp_wr_done               (bfed_lq_wq_ibp_wr_done),
  .bfed_lq_wq_ibp_wr_excl_done          (bfed_lq_wq_ibp_wr_excl_done),
  .bfed_lq_wq_ibp_err_wr                (bfed_lq_wq_ibp_err_wr),
  .bfed_lq_wq_ibp_wr_resp_accept        (bfed_lq_wq_ibp_wr_resp_accept),



  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid             (bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept            (bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_read              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_read),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size         (bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size        (bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache             (bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock),
  .bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl),

  .bfed_dmu_rbu_dmu_wbu_ibp_rd_valid              (bfed_dmu_rbu_dmu_wbu_ibp_rd_valid),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok            (bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_accept             (bfed_dmu_rbu_dmu_wbu_ibp_rd_accept),
  .bfed_dmu_rbu_dmu_wbu_ibp_err_rd                (bfed_dmu_rbu_dmu_wbu_ibp_err_rd),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_data               (bfed_dmu_rbu_dmu_wbu_ibp_rd_data),
  .bfed_dmu_rbu_dmu_wbu_ibp_rd_last               (bfed_dmu_rbu_dmu_wbu_ibp_rd_last),

  .bfed_dmu_rbu_dmu_wbu_ibp_wr_valid              (bfed_dmu_rbu_dmu_wbu_ibp_wr_valid),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_accept             (bfed_dmu_rbu_dmu_wbu_ibp_wr_accept),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_data               (bfed_dmu_rbu_dmu_wbu_ibp_wr_data),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_mask               (bfed_dmu_rbu_dmu_wbu_ibp_wr_mask),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_last               (bfed_dmu_rbu_dmu_wbu_ibp_wr_last),

  .bfed_dmu_rbu_dmu_wbu_ibp_wr_done               (bfed_dmu_rbu_dmu_wbu_ibp_wr_done),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done          (bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done),
  .bfed_dmu_rbu_dmu_wbu_ibp_err_wr                (bfed_dmu_rbu_dmu_wbu_ibp_err_wr),
  .bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept        (bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept),



  .cbu_axi_arvalid    (cbu_axi_arvalid),
  .cbu_axi_arready    (cbu_axi_arready),
  .cbu_axi_arid       (cbu_axi_arid   ),
  .cbu_axi_araddr     (cbu_axi_araddr ),
  .cbu_axi_arburst    (cbu_axi_arburst),
  .cbu_axi_arlen      (cbu_axi_arlen  ),
  .cbu_axi_arsize     (cbu_axi_arsize ),
  .cbu_axi_arcache    (cbu_axi_arcache),
  .cbu_axi_arprot     (cbu_axi_arprot ),
  .cbu_axi_arlock     (cbu_axi_arlock ),

  .cbu_axi_rvalid     (cbu_axi_rvalid),
  .cbu_axi_rready     (cbu_axi_rready),
  .cbu_axi_rid        (cbu_axi_rid   ),
  .cbu_axi_rdata      (cbu_axi_rdata ),
  .cbu_axi_rresp      (cbu_axi_rresp ),
  .cbu_axi_rlast      (cbu_axi_rlast ),

  .cbu_axi_awvalid    (cbu_axi_awvalid),
  .cbu_axi_awready    (cbu_axi_awready),
  .cbu_axi_awid       (cbu_axi_awid   ),
  .cbu_axi_awaddr     (cbu_axi_awaddr ),
  .cbu_axi_awburst    (cbu_axi_awburst),
  .cbu_axi_awlen      (cbu_axi_awlen  ),
  .cbu_axi_awsize     (cbu_axi_awsize ),
  .cbu_axi_awcache    (cbu_axi_awcache),
  .cbu_axi_awprot     (cbu_axi_awprot ),
  .cbu_axi_awlock     (cbu_axi_awlock ),

  .cbu_axi_wid         (cbu_axi_wid   ),
  .cbu_axi_wvalid      (cbu_axi_wvalid),
  .cbu_axi_wready      (cbu_axi_wready),
  .cbu_axi_wdata       (cbu_axi_wdata ),
  .cbu_axi_wstrb       (cbu_axi_wstrb ),
  .cbu_axi_wlast       (cbu_axi_wlast ),

  .cbu_axi_bvalid   (cbu_axi_bvalid),
  .cbu_axi_bready   (cbu_axi_bready),
  .cbu_axi_bid      (cbu_axi_bid   ),
  .cbu_axi_bresp    (cbu_axi_bresp ),




  .rst_a (rst),
  .nmi_restart_r (nmi_restart_r),
  .clk   (clk_gated)
);





wire biu_dmi_idle;


  wire  [2            -1:0]       sccm_cvt_axi_arregion;
  wire                                  sccm_cvt_axi_arvalid;
  wire                                  sccm_cvt_axi_arready;
  wire  [16              -1:0]       sccm_cvt_axi_arid;
  wire  [24                -1:0]       sccm_cvt_axi_araddr;
  wire  [2-1:0]       sccm_cvt_axi_arburst;
  wire  [4-1:0]       sccm_cvt_axi_arlen;
  wire  [3-1:0]       sccm_cvt_axi_arsize;
  wire  [4-1:0]       sccm_cvt_axi_arcache;
  wire  [3-1:0]       sccm_cvt_axi_arprot;
  wire  [2-1:0]       sccm_cvt_axi_arlock;

  wire                                  sccm_cvt_axi_rvalid;
  wire                                  sccm_cvt_axi_rready;
  wire  [16              -1:0]       sccm_cvt_axi_rid;
  wire  [64                -1:0]       sccm_cvt_axi_rdata;
  wire  [2-1:0]       sccm_cvt_axi_rresp;
  wire                                  sccm_cvt_axi_rlast;

  wire  [2            -1:0]       sccm_cvt_axi_awregion;
  wire                                  sccm_cvt_axi_awvalid;
  wire                                  sccm_cvt_axi_awready;
  wire  [16              -1:0]       sccm_cvt_axi_awid;
  wire  [24            -1:0]           sccm_cvt_axi_awaddr;
  wire  [2-1:0]       sccm_cvt_axi_awburst;
  wire  [4-1:0]       sccm_cvt_axi_awlen;
  wire  [3-1:0]       sccm_cvt_axi_awsize;
  wire  [4-1:0]       sccm_cvt_axi_awcache;
  wire  [3-1:0]       sccm_cvt_axi_awprot;
  wire  [2-1:0]       sccm_cvt_axi_awlock;

  wire                                  sccm_cvt_axi_wvalid;
  wire                                  sccm_cvt_axi_wready;
  wire  [64              -1:0]         sccm_cvt_axi_wdata;
  wire  [(64          /8)-1:0]         sccm_cvt_axi_wstrb;
  wire                                  sccm_cvt_axi_wlast;

  wire                                  sccm_cvt_axi_bvalid;
  wire                                  sccm_cvt_axi_bready;
  wire  [16              -1:0]       sccm_cvt_axi_bid;
  wire  [2-1:0]       sccm_cvt_axi_bresp;


assign sccm_cvt_axi_arregion = sccm_axi_arregion;
assign sccm_cvt_axi_arvalid = sccm_axi_arvalid & biu_ratio_l1_clock_active;
assign sccm_axi_arready = sccm_cvt_axi_arready & biu_ratio_l1_clock_active;
assign sccm_cvt_axi_arid    = sccm_axi_arid;
assign sccm_cvt_axi_araddr  = sccm_axi_araddr;
assign sccm_cvt_axi_arburst = sccm_axi_arburst;
assign sccm_cvt_axi_arlen   = sccm_axi_arlen;
assign sccm_cvt_axi_arsize  = sccm_axi_arsize;
assign sccm_cvt_axi_arcache = sccm_axi_arcache;
assign sccm_cvt_axi_arprot  = sccm_axi_arprot;
assign sccm_cvt_axi_arlock  = sccm_axi_arlock;

assign sccm_axi_rvalid     = sccm_cvt_axi_rvalid;
assign sccm_cvt_axi_rready  = sccm_axi_rready;
assign sccm_axi_rid        = sccm_cvt_axi_rid;
assign sccm_axi_rdata      = sccm_cvt_axi_rdata;
assign sccm_axi_rresp      = sccm_cvt_axi_rresp;
assign sccm_axi_rlast      = sccm_cvt_axi_rlast;

assign sccm_cvt_axi_awregion = sccm_axi_awregion;
assign sccm_cvt_axi_awvalid = sccm_axi_awvalid & biu_ratio_l1_clock_active;
assign sccm_axi_awready = sccm_cvt_axi_awready & biu_ratio_l1_clock_active;
assign sccm_cvt_axi_awid    = sccm_axi_awid;
assign sccm_cvt_axi_awaddr  = sccm_axi_awaddr;
assign sccm_cvt_axi_awburst = sccm_axi_awburst;
assign sccm_cvt_axi_awlen   = sccm_axi_awlen;
assign sccm_cvt_axi_awsize  = sccm_axi_awsize;
assign sccm_cvt_axi_awcache = sccm_axi_awcache;
assign sccm_cvt_axi_awprot  = sccm_axi_awprot;
assign sccm_cvt_axi_awlock  = sccm_axi_awlock;

assign sccm_cvt_axi_wvalid  = sccm_axi_wvalid & biu_ratio_l1_clock_active;
assign sccm_axi_wready  = sccm_cvt_axi_wready  & biu_ratio_l1_clock_active;
assign sccm_cvt_axi_wdata   = sccm_axi_wdata;
assign sccm_cvt_axi_wstrb   = sccm_axi_wstrb;
assign sccm_cvt_axi_wlast   = sccm_axi_wlast;

assign sccm_axi_bvalid     = sccm_cvt_axi_bvalid;
assign sccm_cvt_axi_bready  = sccm_axi_bready;
assign sccm_axi_bid        = sccm_cvt_axi_bid;
assign sccm_axi_bresp      = sccm_cvt_axi_bresp;

    


wire biu_ccm_ibp_idle = 1'b1 
                        ;


npuarc_biu_ccm_bridge u_biu_ccm_bridge
  (

  .biu_dmi_clk_en_req(biu_dmi_clk_en_req),


  .dbus_clk_en (dbus_clk_en),


  .sccm_axi_arregion   (sccm_cvt_axi_arregion),
  .sccm_axi_arvalid    (sccm_cvt_axi_arvalid),
  .sccm_axi_arready    (sccm_cvt_axi_arready),
  .sccm_axi_arid       (sccm_cvt_axi_arid   ),
  .sccm_axi_araddr     (sccm_cvt_axi_araddr ),
  .sccm_axi_arburst    (sccm_cvt_axi_arburst),
  .sccm_axi_arlen      (sccm_cvt_axi_arlen  ),
  .sccm_axi_arsize     (sccm_cvt_axi_arsize ),
  .sccm_axi_arcache    (sccm_cvt_axi_arcache),
  .sccm_axi_arprot     (sccm_cvt_axi_arprot ),
  .sccm_axi_arlock     (sccm_cvt_axi_arlock ),

  .sccm_axi_rvalid     (sccm_cvt_axi_rvalid),
  .sccm_axi_rready     (sccm_cvt_axi_rready),
  .sccm_axi_rid        (sccm_cvt_axi_rid   ),
  .sccm_axi_rdata      (sccm_cvt_axi_rdata ),
  .sccm_axi_rresp      (sccm_cvt_axi_rresp ),
  .sccm_axi_rlast      (sccm_cvt_axi_rlast ),

  .sccm_axi_awregion   (sccm_cvt_axi_awregion),
  .sccm_axi_awvalid    (sccm_cvt_axi_awvalid),
  .sccm_axi_awready    (sccm_cvt_axi_awready),
  .sccm_axi_awid       (sccm_cvt_axi_awid   ),
  .sccm_axi_awaddr     (sccm_cvt_axi_awaddr ),
  .sccm_axi_awburst    (sccm_cvt_axi_awburst),
  .sccm_axi_awlen      (sccm_cvt_axi_awlen  ),
  .sccm_axi_awsize     (sccm_cvt_axi_awsize ),
  .sccm_axi_awcache    (sccm_cvt_axi_awcache),
  .sccm_axi_awprot     (sccm_cvt_axi_awprot ),
  .sccm_axi_awlock     (sccm_cvt_axi_awlock ),

  .sccm_axi_wvalid      (sccm_cvt_axi_wvalid),
  .sccm_axi_wready      (sccm_cvt_axi_wready),
  .sccm_axi_wdata       (sccm_cvt_axi_wdata ),
  .sccm_axi_wstrb       (sccm_cvt_axi_wstrb ),
  .sccm_axi_wlast       (sccm_cvt_axi_wlast ),

  .sccm_axi_bvalid   (sccm_cvt_axi_bvalid),
  .sccm_axi_bready   (sccm_cvt_axi_bready),
  .sccm_axi_bid      (sccm_cvt_axi_bid   ),
  .sccm_axi_bresp    (sccm_cvt_axi_bresp ),


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




  .biu_dmi_idle                             (biu_dmi_idle                  ),
  .sync_rst_r                               (sync_rst_r                    ),
  .async_rst                                (rst_a                         ),
  .rst_a                                    (rst                           ),
  .nmi_restart_r                            (nmi_restart_r                 ),

  .clk                                      (clk_ungated                   )
);







assign biu2pdm_idle = 1'b1
               & biu_preprc_ibp_idle
             ;


assign biu2pdm_l2c_idle = 1'b1
               & biu_preprc_l2c_ibp_idle
             ;




// spyglass disable_block Ac_conv01
// SMD:  Ac_conv01 Convergence, 2 synchronizers converge on combinational gate
// SJ: These signals are independent which is not need to be cared
wire biu_top_active_raw = 1'b0
               | biu_preprc_active
               | ifu_ibp_cmd_valid
               | lqwq_ibp_cmd_valid
               | dmu_rbu_ibp_cmd_valid
               | dmu_wbu_ibp_cmd_valid
               | (~biu_dmi_idle)
               | sccm_axi_arvalid
               | sccm_axi_awvalid
               | sccm_axi_wvalid
               | (~biu_ccm_ibp_idle)                     
             ;
// spyglass enable_block Ac_conv01

wire biu_l1gt_clk_enable_prel = biu_l1_cg_dis
                             || biu_top_active_raw
                                ;
//wire biu_l1gt_clk_enable_prel = 1'b1;

// spyglass disable_block Reset_sync04
// SMD: Asynchronous reset signal is synchronized at least twice
// SJ: The rst to different unit's l1 gate control is okay
//The l1gt_clk_enable signal is flopped out by free-running clock
reg biu_l1gt_clk_enable_prel_r;

always @(posedge clk_ungated or posedge rst)
begin : biu_l1gt_clk_enable_prel_r_PROC
  if (rst == 1'b1) begin
    biu_l1gt_clk_enable_prel_r <= 1'b1;
  end else if (nmi_restart_r == 1'b1) begin
    biu_l1gt_clk_enable_prel_r <= 1'b1;
  end else begin
    biu_l1gt_clk_enable_prel_r <= biu_l1gt_clk_enable_prel;
  end
end
assign biu_l1gt_clk_enable = biu_l1gt_clk_enable_prel_r;
// spyglass enable_block Reset_sync04


/////////////////////////////////////////////////////////////////
// Level-1 idle FSM
// Three states:
// (1) Active: only accept transactions when the FSM is in the active state
// (2) GOING_IDLE: there is a de-assertion of biu_l1gt_clk_enable_prel going to gate the level-1 clock
// (3) IDLE: state to forbid transaction accept and wait clock to be activated
/////////////////////////////////////////////////////////////////

reg [1:0] l1_state_r;
reg [1:0] l1_state_nxt;


localparam FSM_ACTIVE     = 2'b00;
localparam FSM_GOING_IDLE = 2'b01;
localparam FSM_IDLE       = 2'b10;

always @(posedge clk_ungated or posedge rst)
begin: l1_fsm_reg_PROC
  if (rst == 1'b1)
  begin
    l1_state_r      <= FSM_IDLE;
  end
  else if (nmi_restart_r == 1'b1)
  begin
    l1_state_r      <= FSM_ACTIVE;
  end
  else begin
    l1_state_r      <= l1_state_nxt;
  end
end

always @*
begin: l1_fsm_main_PROC
  l1_state_nxt    = l1_state_r;

  case (l1_state_r)
  FSM_ACTIVE:
             begin
               if (biu_l1gt_clk_enable_prel == 1'b0) begin
                   // BIU is going to be idle
                   l1_state_nxt = FSM_GOING_IDLE;
               end
             end
  FSM_GOING_IDLE:
             begin
               if (biu_accept_en == 1'b0) begin
                   // BIU receive indication of cc_clock_ctrl clock will be gated
                   l1_state_nxt = FSM_IDLE;
               end
             end
  default:
             begin
               if ((biu_accept_en == 1'b1) && (dbus_clk_en == 1'b1)) begin
                   // BIU level-1 clock is active, going to accept transaction
                   l1_state_nxt = FSM_ACTIVE;
               end
             end
  endcase

end

assign biu_l1_clock_active = (l1_state_r == FSM_ACTIVE);
// spyglass disable_block  FlopEConst
// SMD: Enable pin tie to constant
// SJ: No care about the warning
always @(posedge clk_ungated or posedge rst)
begin : biu_ratio_l1_clock_active_PROC
  if (rst == 1'b1) begin
    biu_ratio_l1_clock_active <= 1'b0;
  end
  else if ((nmi_restart_r == 1'b1) & dbus_clk_en) begin
    biu_ratio_l1_clock_active <= 1'b1;
  end
  else if (dbus_clk_en)begin
    if ((l1_state_r == FSM_IDLE) & biu_accept_en) begin
      biu_ratio_l1_clock_active <= 1'b1;
    end else if ((~biu_l1gt_clk_enable_prel) & (l1_state_r == FSM_ACTIVE)) begin
      biu_ratio_l1_clock_active <= 1'b0;
    end else begin
      biu_ratio_l1_clock_active <= biu_l1_clock_active;
    end
  end
end
// spyglass enable_block  FlopEConst







// spyglass enable_block W528
// leda G_521_2_B on
endmodule // biu_top


