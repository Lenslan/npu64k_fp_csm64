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
//  IBP preprocessor
//
// ===========================================================================
//
// Description:
//  This module preprocess all the upstream IBPs to BIU
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"

// Set simulation timescale
//
`include "const.def"


module npuarc_biu_ibp_preprc (




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




  output                                  bfed_ifu_merg_ibp_cmd_valid,
  input                                   bfed_ifu_merg_ibp_cmd_accept,
  output                                  bfed_ifu_merg_ibp_cmd_read,
  output  [40                -1:0]       bfed_ifu_merg_ibp_cmd_addr,
  output                                  bfed_ifu_merg_ibp_cmd_wrap,
  output  [3-1:0]       bfed_ifu_merg_ibp_cmd_data_size,
  output  [4-1:0]       bfed_ifu_merg_ibp_cmd_burst_size,
  output  [2-1:0]       bfed_ifu_merg_ibp_cmd_prot,
  output  [4-1:0]       bfed_ifu_merg_ibp_cmd_cache,
  output                                  bfed_ifu_merg_ibp_cmd_lock,
  output                                  bfed_ifu_merg_ibp_cmd_excl,

  input                                   bfed_ifu_merg_ibp_rd_valid,
  input                                   bfed_ifu_merg_ibp_rd_excl_ok,
  output                                  bfed_ifu_merg_ibp_rd_accept,
  input                                   bfed_ifu_merg_ibp_err_rd,
  input   [64               -1:0]        bfed_ifu_merg_ibp_rd_data,
  input                                   bfed_ifu_merg_ibp_rd_last,

  output                                  bfed_ifu_merg_ibp_wr_valid,
  input                                   bfed_ifu_merg_ibp_wr_accept,
  output  [64               -1:0]        bfed_ifu_merg_ibp_wr_data,
  output  [8  -1:0]                    bfed_ifu_merg_ibp_wr_mask,
  output                                  bfed_ifu_merg_ibp_wr_last,

  input                                   bfed_ifu_merg_ibp_wr_done,
  input                                   bfed_ifu_merg_ibp_wr_excl_done,
  input                                   bfed_ifu_merg_ibp_err_wr,
  output                                  bfed_ifu_merg_ibp_wr_resp_accept,


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




  output                                  bfed_lq_wq_ibp_cmd_valid,
  input                                   bfed_lq_wq_ibp_cmd_accept,
  output                                  bfed_lq_wq_ibp_cmd_read,
  output  [40                -1:0]       bfed_lq_wq_ibp_cmd_addr,
  output                                  bfed_lq_wq_ibp_cmd_wrap,
  output  [3-1:0]       bfed_lq_wq_ibp_cmd_data_size,
  output  [4-1:0]       bfed_lq_wq_ibp_cmd_burst_size,
  output  [2-1:0]       bfed_lq_wq_ibp_cmd_prot,
  output  [4-1:0]       bfed_lq_wq_ibp_cmd_cache,
  output                                  bfed_lq_wq_ibp_cmd_lock,
  output                                  bfed_lq_wq_ibp_cmd_excl,

  input                                   bfed_lq_wq_ibp_rd_valid,
  input                                   bfed_lq_wq_ibp_rd_excl_ok,
  output                                  bfed_lq_wq_ibp_rd_accept,
  input                                   bfed_lq_wq_ibp_err_rd,
  input   [64               -1:0]        bfed_lq_wq_ibp_rd_data,
  input                                   bfed_lq_wq_ibp_rd_last,

  output                                  bfed_lq_wq_ibp_wr_valid,
  input                                   bfed_lq_wq_ibp_wr_accept,
  output  [64               -1:0]        bfed_lq_wq_ibp_wr_data,
  output  [8  -1:0]                    bfed_lq_wq_ibp_wr_mask,
  output                                  bfed_lq_wq_ibp_wr_last,

  input                                   bfed_lq_wq_ibp_wr_done,
  input                                   bfed_lq_wq_ibp_wr_excl_done,
  input                                   bfed_lq_wq_ibp_err_wr,
  output                                  bfed_lq_wq_ibp_wr_resp_accept,


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



  output                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_read,
  output  [40                -1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap,
  output  [3-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size,
  output  [4-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size,
  output  [2-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot,
  output  [4-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl,

  input                                   bfed_dmu_rbu_dmu_wbu_ibp_rd_valid,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_accept,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_err_rd,
  input   [128               -1:0]        bfed_dmu_rbu_dmu_wbu_ibp_rd_data,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_rd_last,

  output                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_valid,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_wr_accept,
  output  [128               -1:0]        bfed_dmu_rbu_dmu_wbu_ibp_wr_data,
  output  [16  -1:0]                    bfed_dmu_rbu_dmu_wbu_ibp_wr_mask,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_last,

  input                                   bfed_dmu_rbu_dmu_wbu_ibp_wr_done,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_err_wr,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept,

  output biu_preprc_ibp_idle,
  output biu_preprc_active, // ibp_preprc moduel active with either incorming transactions or pending transactions
  output biu_preprc_l2c_ibp_idle,
  input  clk,  // clock signal
  input  nmi_restart_r,  // NMI reset signal
  input  rst_a // reset signal

  );
// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning



wire ifu_ibp_idle;




wire lqwq_ibp_idle;




wire dmu_rbu_ibp_idle;

wire dmu_wbu_ibp_idle;







assign biu_preprc_l2c_ibp_idle = 1'b1






  ;




assign biu_preprc_ibp_idle = 1'b1
   & ifu_ibp_idle

   & lqwq_ibp_idle

   & dmu_rbu_ibp_idle

   & dmu_wbu_ibp_idle
   ;


assign biu_preprc_active = ~(biu_preprc_ibp_idle)
   | ifu_ibp_cmd_valid
   | lqwq_ibp_cmd_valid
   | dmu_rbu_ibp_cmd_valid
   | dmu_wbu_ibp_cmd_valid
   ;



// spyglass disable_block Clock_info03a
// SMD: clock net unconstrained
// SJ: no need to constrain
wire preprc_ifu_merg_clk_gated;
// spyglass enable_block Clock_info03a

wire preprc_ifu_merg_ibp_in = 1'b0
   | ifu_ibp_cmd_valid
   ;

wire preprc_ifu_merg_ibp_idle = 1'b1
   & ifu_ibp_idle
   ;

wire preprc_ifu_merg_ibp_clk_enable = preprc_ifu_merg_ibp_in
                                     | (~preprc_ifu_merg_ibp_idle);

npuarc_biu_clk_ctrl u_preprc_ifu_merg_clkctrl (
  .clk        (clk  ),
  .nmi_restart_r (nmi_restart_r),
  .clkctrl_en (preprc_ifu_merg_ibp_clk_enable),
  .clk_gated  (preprc_ifu_merg_clk_gated),
  .rst_a      (rst_a)
  );
// spyglass disable_block Clock_info03a
// SMD: clock net unconstrained
// SJ: no need to constrain
wire preprc_lq_wq_clk_gated;
// spyglass enable_block Clock_info03a

wire preprc_lq_wq_ibp_in = 1'b0
   | lqwq_ibp_cmd_valid
   ;

wire preprc_lq_wq_ibp_idle = 1'b1
   & lqwq_ibp_idle
   ;

wire preprc_lq_wq_ibp_clk_enable = preprc_lq_wq_ibp_in
                                     | (~preprc_lq_wq_ibp_idle);

npuarc_biu_clk_ctrl u_preprc_lq_wq_clkctrl (
  .clk        (clk  ),
  .nmi_restart_r (nmi_restart_r),
  .clkctrl_en (preprc_lq_wq_ibp_clk_enable),
  .clk_gated  (preprc_lq_wq_clk_gated),
  .rst_a      (rst_a)
  );
// spyglass disable_block Clock_info03a
// SMD: clock net unconstrained
// SJ: no need to constrain
wire preprc_dmu_rbu_dmu_wbu_clk_gated;
// spyglass enable_block Clock_info03a

wire preprc_dmu_rbu_dmu_wbu_ibp_in = 1'b0
   | dmu_rbu_ibp_cmd_valid
   | dmu_wbu_ibp_cmd_valid
   ;

wire preprc_dmu_rbu_dmu_wbu_ibp_idle = 1'b1
   & dmu_rbu_ibp_idle
   & dmu_wbu_ibp_idle
   ;

wire preprc_dmu_rbu_dmu_wbu_ibp_clk_enable = preprc_dmu_rbu_dmu_wbu_ibp_in
                                     | (~preprc_dmu_rbu_dmu_wbu_ibp_idle);

npuarc_biu_clk_ctrl u_preprc_dmu_rbu_dmu_wbu_clkctrl (
  .clk        (clk  ),
  .nmi_restart_r (nmi_restart_r),
  .clkctrl_en (preprc_dmu_rbu_dmu_wbu_ibp_clk_enable),
  .clk_gated  (preprc_dmu_rbu_dmu_wbu_clk_gated),
  .rst_a      (rst_a)
  );











 wire [1-1:0] ifu_ibp_cmd_chnl_valid;
 wire [1-1:0] ifu_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] ifu_ibp_cmd_chnl;

 wire [1-1:0] ifu_ibp_wd_chnl_valid;
 wire [1-1:0] ifu_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] ifu_ibp_wd_chnl;

 wire [1-1:0] ifu_ibp_rd_chnl_accept;
 wire [1-1:0] ifu_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] ifu_ibp_rd_chnl;

 wire [1-1:0] ifu_ibp_wrsp_chnl_valid;
 wire [1-1:0] ifu_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] ifu_ibp_wrsp_chnl;


// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_preprc_ibp2pack
  #(
    .ADDR_W (40),
    .DATA_W (64),



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
    .USER_W(1),
    .RGON_W(1)
    )
u_ifu_ibp2pack
  (
    .rst_a                     (rst_a),
    .nmi_restart_r (nmi_restart_r ),
    .clk                       (preprc_ifu_merg_clk_gated  ),

  .ibp_cmd_valid             (ifu_ibp_cmd_valid),
  .ibp_cmd_accept            (ifu_ibp_cmd_accept),
  .ibp_cmd_read              (ifu_ibp_cmd_read),
  .ibp_cmd_addr              (ifu_ibp_cmd_addr),
  .ibp_cmd_wrap              (ifu_ibp_cmd_wrap),
  .ibp_cmd_data_size         (ifu_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (ifu_ibp_cmd_burst_size),
  .ibp_cmd_prot              (ifu_ibp_cmd_prot),
  .ibp_cmd_cache             (ifu_ibp_cmd_cache),
  .ibp_cmd_lock              (ifu_ibp_cmd_lock),
  .ibp_cmd_excl              (ifu_ibp_cmd_excl),

  .ibp_rd_valid              (ifu_ibp_rd_valid),
  .ibp_rd_excl_ok            (ifu_ibp_rd_excl_ok),
  .ibp_rd_accept             (ifu_ibp_rd_accept),
  .ibp_err_rd                (ifu_ibp_err_rd),
  .ibp_rd_data               (ifu_ibp_rd_data),
  .ibp_rd_last               (ifu_ibp_rd_last),

  .ibp_wr_valid              (ifu_ibp_wr_valid),
  .ibp_wr_accept             (ifu_ibp_wr_accept),
  .ibp_wr_data               (ifu_ibp_wr_data),
  .ibp_wr_mask               (ifu_ibp_wr_mask),
  .ibp_wr_last               (ifu_ibp_wr_last),

  .ibp_wr_done               (ifu_ibp_wr_done),
  .ibp_wr_excl_done          (ifu_ibp_wr_excl_done),
  .ibp_err_wr                (ifu_ibp_err_wr),
  .ibp_wr_resp_accept        (ifu_ibp_wr_resp_accept),

    .ibp_cmd_rgon              (1'b0),
    .ibp_cmd_user              (1'b0),




    .ibp_cmd_chnl_valid  (ifu_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (ifu_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (ifu_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (ifu_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (ifu_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (ifu_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (ifu_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (ifu_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (ifu_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (ifu_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(ifu_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (ifu_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
    .ibp_cmd_chnl_rgon         (),
    .ibp_cmd_chnl_user         ()
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on

npuarc_biu_preprc_ibp_chnl_idle
  #(



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
   .OUTSTAND_NUM  (4),
   .OUTSTAND_CNT_W(2)
    )
  u_ifu_ibp_chnl_idle (
  .i_ibp_idle            (ifu_ibp_idle),

  .i_ibp_cmd_chnl_valid  (ifu_ibp_cmd_chnl_valid),
  .i_ibp_cmd_chnl_accept (ifu_ibp_cmd_chnl_accept),
  .i_ibp_cmd_chnl        (ifu_ibp_cmd_chnl),

  .i_ibp_rd_chnl_valid   (ifu_ibp_rd_chnl_valid),
  .i_ibp_rd_chnl_accept  (ifu_ibp_rd_chnl_accept),
  .i_ibp_rd_chnl         (ifu_ibp_rd_chnl),

  .i_ibp_wrsp_chnl_valid (ifu_ibp_wrsp_chnl_valid),
  .i_ibp_wrsp_chnl_accept(ifu_ibp_wrsp_chnl_accept),
  .clk        (preprc_ifu_merg_clk_gated  ),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a      (rst_a)
  );











 wire [1-1:0] ifu_merg_ibp_cmd_chnl_valid;
 wire [1-1:0] ifu_merg_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] ifu_merg_ibp_cmd_chnl;

 wire [1-1:0] ifu_merg_ibp_wd_chnl_valid;
 wire [1-1:0] ifu_merg_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] ifu_merg_ibp_wd_chnl;

 wire [1-1:0] ifu_merg_ibp_rd_chnl_accept;
 wire [1-1:0] ifu_merg_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] ifu_merg_ibp_rd_chnl;

 wire [1-1:0] ifu_merg_ibp_wrsp_chnl_valid;
 wire [1-1:0] ifu_merg_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] ifu_merg_ibp_wrsp_chnl;


  assign ifu_merg_ibp_cmd_chnl_valid     = ifu_ibp_cmd_chnl_valid  ;
  assign ifu_ibp_cmd_chnl_accept    = ifu_merg_ibp_cmd_chnl_accept ;
  assign ifu_merg_ibp_cmd_chnl           = ifu_ibp_cmd_chnl        ;

  assign ifu_merg_ibp_wd_chnl_valid      = ifu_ibp_wd_chnl_valid   ;
  assign ifu_ibp_wd_chnl_accept     = ifu_merg_ibp_wd_chnl_accept  ;
  assign ifu_merg_ibp_wd_chnl            = ifu_ibp_wd_chnl         ;

  assign ifu_merg_ibp_rd_chnl_accept     = ifu_ibp_rd_chnl_accept  ;
  assign ifu_ibp_rd_chnl_valid      = ifu_merg_ibp_rd_chnl_valid   ;
  assign ifu_ibp_rd_chnl            = ifu_merg_ibp_rd_chnl         ;

  assign ifu_merg_ibp_wrsp_chnl_accept   = ifu_ibp_wrsp_chnl_accept;
  assign ifu_ibp_wrsp_chnl_valid    = ifu_merg_ibp_wrsp_chnl_valid ;
  assign ifu_ibp_wrsp_chnl          = ifu_merg_ibp_wrsp_chnl       ;






 wire [1-1:0] bfed_ifu_merg_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_ifu_merg_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_ifu_merg_ibp_cmd_chnl;

 wire [1-1:0] bfed_ifu_merg_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_ifu_merg_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] bfed_ifu_merg_ibp_wd_chnl;

 wire [1-1:0] bfed_ifu_merg_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_ifu_merg_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] bfed_ifu_merg_ibp_rd_chnl;

 wire [1-1:0] bfed_ifu_merg_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_ifu_merg_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_ifu_merg_ibp_wrsp_chnl;


  assign bfed_ifu_merg_ibp_cmd_chnl_valid     = ifu_merg_ibp_cmd_chnl_valid  ;
  assign ifu_merg_ibp_cmd_chnl_accept    = bfed_ifu_merg_ibp_cmd_chnl_accept ;
  assign bfed_ifu_merg_ibp_cmd_chnl           = ifu_merg_ibp_cmd_chnl        ;

  assign bfed_ifu_merg_ibp_wd_chnl_valid      = ifu_merg_ibp_wd_chnl_valid   ;
  assign ifu_merg_ibp_wd_chnl_accept     = bfed_ifu_merg_ibp_wd_chnl_accept  ;
  assign bfed_ifu_merg_ibp_wd_chnl            = ifu_merg_ibp_wd_chnl         ;

  assign bfed_ifu_merg_ibp_rd_chnl_accept     = ifu_merg_ibp_rd_chnl_accept  ;
  assign ifu_merg_ibp_rd_chnl_valid      = bfed_ifu_merg_ibp_rd_chnl_valid   ;
  assign ifu_merg_ibp_rd_chnl            = bfed_ifu_merg_ibp_rd_chnl         ;

  assign bfed_ifu_merg_ibp_wrsp_chnl_accept   = ifu_merg_ibp_wrsp_chnl_accept;
  assign ifu_merg_ibp_wrsp_chnl_valid    = bfed_ifu_merg_ibp_wrsp_chnl_valid ;
  assign ifu_merg_ibp_wrsp_chnl          = bfed_ifu_merg_ibp_wrsp_chnl       ;





 wire [1-1:0] splt_bfed_ifu_merg_ibp_cmd_chnl_valid;
 wire [1-1:0] splt_bfed_ifu_merg_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] splt_bfed_ifu_merg_ibp_cmd_chnl;

 wire [1-1:0] splt_bfed_ifu_merg_ibp_wd_chnl_valid;
 wire [1-1:0] splt_bfed_ifu_merg_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] splt_bfed_ifu_merg_ibp_wd_chnl;

 wire [1-1:0] splt_bfed_ifu_merg_ibp_rd_chnl_accept;
 wire [1-1:0] splt_bfed_ifu_merg_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] splt_bfed_ifu_merg_ibp_rd_chnl;

 wire [1-1:0] splt_bfed_ifu_merg_ibp_wrsp_chnl_valid;
 wire [1-1:0] splt_bfed_ifu_merg_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] splt_bfed_ifu_merg_ibp_wrsp_chnl;

  assign splt_bfed_ifu_merg_ibp_cmd_chnl_valid     = bfed_ifu_merg_ibp_cmd_chnl_valid  ;
  assign bfed_ifu_merg_ibp_cmd_chnl_accept    = splt_bfed_ifu_merg_ibp_cmd_chnl_accept ;
  assign splt_bfed_ifu_merg_ibp_cmd_chnl           = bfed_ifu_merg_ibp_cmd_chnl        ;

  assign splt_bfed_ifu_merg_ibp_wd_chnl_valid      = bfed_ifu_merg_ibp_wd_chnl_valid   ;
  assign bfed_ifu_merg_ibp_wd_chnl_accept     = splt_bfed_ifu_merg_ibp_wd_chnl_accept  ;
  assign splt_bfed_ifu_merg_ibp_wd_chnl            = bfed_ifu_merg_ibp_wd_chnl         ;

  assign splt_bfed_ifu_merg_ibp_rd_chnl_accept     = bfed_ifu_merg_ibp_rd_chnl_accept  ;
  assign bfed_ifu_merg_ibp_rd_chnl_valid      = splt_bfed_ifu_merg_ibp_rd_chnl_valid   ;
  assign bfed_ifu_merg_ibp_rd_chnl            = splt_bfed_ifu_merg_ibp_rd_chnl         ;

  assign splt_bfed_ifu_merg_ibp_wrsp_chnl_accept   = bfed_ifu_merg_ibp_wrsp_chnl_accept;
  assign bfed_ifu_merg_ibp_wrsp_chnl_valid    = splt_bfed_ifu_merg_ibp_wrsp_chnl_valid ;
  assign bfed_ifu_merg_ibp_wrsp_chnl          = splt_bfed_ifu_merg_ibp_wrsp_chnl       ;




 wire [1-1:0] bfed_splt_bfed_ifu_merg_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_splt_bfed_ifu_merg_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_splt_bfed_ifu_merg_ibp_cmd_chnl;

 wire [1-1:0] bfed_splt_bfed_ifu_merg_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_splt_bfed_ifu_merg_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] bfed_splt_bfed_ifu_merg_ibp_wd_chnl;

 wire [1-1:0] bfed_splt_bfed_ifu_merg_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_splt_bfed_ifu_merg_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] bfed_splt_bfed_ifu_merg_ibp_rd_chnl;

 wire [1-1:0] bfed_splt_bfed_ifu_merg_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_splt_bfed_ifu_merg_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_splt_bfed_ifu_merg_ibp_wrsp_chnl;

  assign bfed_splt_bfed_ifu_merg_ibp_cmd_chnl_valid     = splt_bfed_ifu_merg_ibp_cmd_chnl_valid  ;
  assign splt_bfed_ifu_merg_ibp_cmd_chnl_accept    = bfed_splt_bfed_ifu_merg_ibp_cmd_chnl_accept ;
  assign bfed_splt_bfed_ifu_merg_ibp_cmd_chnl           = splt_bfed_ifu_merg_ibp_cmd_chnl        ;

  assign bfed_splt_bfed_ifu_merg_ibp_wd_chnl_valid      = splt_bfed_ifu_merg_ibp_wd_chnl_valid   ;
  assign splt_bfed_ifu_merg_ibp_wd_chnl_accept     = bfed_splt_bfed_ifu_merg_ibp_wd_chnl_accept  ;
  assign bfed_splt_bfed_ifu_merg_ibp_wd_chnl            = splt_bfed_ifu_merg_ibp_wd_chnl         ;

  assign bfed_splt_bfed_ifu_merg_ibp_rd_chnl_accept     = splt_bfed_ifu_merg_ibp_rd_chnl_accept  ;
  assign splt_bfed_ifu_merg_ibp_rd_chnl_valid      = bfed_splt_bfed_ifu_merg_ibp_rd_chnl_valid   ;
  assign splt_bfed_ifu_merg_ibp_rd_chnl            = bfed_splt_bfed_ifu_merg_ibp_rd_chnl         ;

  assign bfed_splt_bfed_ifu_merg_ibp_wrsp_chnl_accept   = splt_bfed_ifu_merg_ibp_wrsp_chnl_accept;
  assign splt_bfed_ifu_merg_ibp_wrsp_chnl_valid    = bfed_splt_bfed_ifu_merg_ibp_wrsp_chnl_valid ;
  assign splt_bfed_ifu_merg_ibp_wrsp_chnl          = bfed_splt_bfed_ifu_merg_ibp_wrsp_chnl       ;

// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_preprc_pack2ibp
  #(
    .ADDR_W (40),
    .DATA_W (64),



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
    .USER_W(1),
    .RGON_W(1)
    )
u_bfed_splt_bfed_ifu_merg_pack2ibp
  (

  .ibp_cmd_valid             (bfed_ifu_merg_ibp_cmd_valid),
  .ibp_cmd_accept            (bfed_ifu_merg_ibp_cmd_accept),
  .ibp_cmd_read              (bfed_ifu_merg_ibp_cmd_read),
  .ibp_cmd_addr              (bfed_ifu_merg_ibp_cmd_addr),
  .ibp_cmd_wrap              (bfed_ifu_merg_ibp_cmd_wrap),
  .ibp_cmd_data_size         (bfed_ifu_merg_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (bfed_ifu_merg_ibp_cmd_burst_size),
  .ibp_cmd_prot              (bfed_ifu_merg_ibp_cmd_prot),
  .ibp_cmd_cache             (bfed_ifu_merg_ibp_cmd_cache),
  .ibp_cmd_lock              (bfed_ifu_merg_ibp_cmd_lock),
  .ibp_cmd_excl              (bfed_ifu_merg_ibp_cmd_excl),

  .ibp_rd_valid              (bfed_ifu_merg_ibp_rd_valid),
  .ibp_rd_excl_ok            (bfed_ifu_merg_ibp_rd_excl_ok),
  .ibp_rd_accept             (bfed_ifu_merg_ibp_rd_accept),
  .ibp_err_rd                (bfed_ifu_merg_ibp_err_rd),
  .ibp_rd_data               (bfed_ifu_merg_ibp_rd_data),
  .ibp_rd_last               (bfed_ifu_merg_ibp_rd_last),

  .ibp_wr_valid              (bfed_ifu_merg_ibp_wr_valid),
  .ibp_wr_accept             (bfed_ifu_merg_ibp_wr_accept),
  .ibp_wr_data               (bfed_ifu_merg_ibp_wr_data),
  .ibp_wr_mask               (bfed_ifu_merg_ibp_wr_mask),
  .ibp_wr_last               (bfed_ifu_merg_ibp_wr_last),

  .ibp_wr_done               (bfed_ifu_merg_ibp_wr_done),
  .ibp_wr_excl_done          (bfed_ifu_merg_ibp_wr_excl_done),
  .ibp_err_wr                (bfed_ifu_merg_ibp_err_wr),
  .ibp_wr_resp_accept        (bfed_ifu_merg_ibp_wr_resp_accept),





    .ibp_cmd_chnl_valid  (bfed_splt_bfed_ifu_merg_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bfed_splt_bfed_ifu_merg_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bfed_splt_bfed_ifu_merg_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bfed_splt_bfed_ifu_merg_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bfed_splt_bfed_ifu_merg_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bfed_splt_bfed_ifu_merg_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bfed_splt_bfed_ifu_merg_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bfed_splt_bfed_ifu_merg_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bfed_splt_bfed_ifu_merg_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bfed_splt_bfed_ifu_merg_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bfed_splt_bfed_ifu_merg_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bfed_splt_bfed_ifu_merg_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
    .ibp_cmd_chnl_rgon              (1'b0),
    .ibp_cmd_chnl_user              (1'b0),
    .ibp_cmd_rgon         (),
    .ibp_cmd_user         ()
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on











 wire [1-1:0] lqwq_ibp_cmd_chnl_valid;
 wire [1-1:0] lqwq_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] lqwq_ibp_cmd_chnl;

 wire [1-1:0] lqwq_ibp_wd_chnl_valid;
 wire [1-1:0] lqwq_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] lqwq_ibp_wd_chnl;

 wire [1-1:0] lqwq_ibp_rd_chnl_accept;
 wire [1-1:0] lqwq_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] lqwq_ibp_rd_chnl;

 wire [1-1:0] lqwq_ibp_wrsp_chnl_valid;
 wire [1-1:0] lqwq_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] lqwq_ibp_wrsp_chnl;


// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_preprc_ibp2pack
  #(
    .ADDR_W (40),
    .DATA_W (64),



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
    .USER_W(1),
    .RGON_W(1)
    )
u_lqwq_ibp2pack
  (
    .rst_a                     (rst_a),
    .nmi_restart_r (nmi_restart_r ),
    .clk                       (preprc_lq_wq_clk_gated  ),

  .ibp_cmd_valid             (lqwq_ibp_cmd_valid),
  .ibp_cmd_accept            (lqwq_ibp_cmd_accept),
  .ibp_cmd_read              (lqwq_ibp_cmd_read),
  .ibp_cmd_addr              (lqwq_ibp_cmd_addr),
  .ibp_cmd_wrap              (lqwq_ibp_cmd_wrap),
  .ibp_cmd_data_size         (lqwq_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (lqwq_ibp_cmd_burst_size),
  .ibp_cmd_prot              (lqwq_ibp_cmd_prot),
  .ibp_cmd_cache             (lqwq_ibp_cmd_cache),
  .ibp_cmd_lock              (lqwq_ibp_cmd_lock),
  .ibp_cmd_excl              (lqwq_ibp_cmd_excl),

  .ibp_rd_valid              (lqwq_ibp_rd_valid),
  .ibp_rd_excl_ok            (lqwq_ibp_rd_excl_ok),
  .ibp_rd_accept             (lqwq_ibp_rd_accept),
  .ibp_err_rd                (lqwq_ibp_err_rd),
  .ibp_rd_data               (lqwq_ibp_rd_data),
  .ibp_rd_last               (lqwq_ibp_rd_last),

  .ibp_wr_valid              (lqwq_ibp_wr_valid),
  .ibp_wr_accept             (lqwq_ibp_wr_accept),
  .ibp_wr_data               (lqwq_ibp_wr_data),
  .ibp_wr_mask               (lqwq_ibp_wr_mask),
  .ibp_wr_last               (lqwq_ibp_wr_last),

  .ibp_wr_done               (lqwq_ibp_wr_done),
  .ibp_wr_excl_done          (lqwq_ibp_wr_excl_done),
  .ibp_err_wr                (lqwq_ibp_err_wr),
  .ibp_wr_resp_accept        (lqwq_ibp_wr_resp_accept),

    .ibp_cmd_rgon              (1'b0),
    .ibp_cmd_user              (1'b0),




    .ibp_cmd_chnl_valid  (lqwq_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (lqwq_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (lqwq_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (lqwq_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (lqwq_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (lqwq_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (lqwq_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (lqwq_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (lqwq_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (lqwq_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(lqwq_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (lqwq_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
    .ibp_cmd_chnl_rgon         (),
    .ibp_cmd_chnl_user         ()
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on

npuarc_biu_preprc_ibp_chnl_idle
  #(



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
   .OUTSTAND_NUM  (8),
   .OUTSTAND_CNT_W(3)
    )
  u_lqwq_ibp_chnl_idle (
  .i_ibp_idle            (lqwq_ibp_idle),

  .i_ibp_cmd_chnl_valid  (lqwq_ibp_cmd_chnl_valid),
  .i_ibp_cmd_chnl_accept (lqwq_ibp_cmd_chnl_accept),
  .i_ibp_cmd_chnl        (lqwq_ibp_cmd_chnl),

  .i_ibp_rd_chnl_valid   (lqwq_ibp_rd_chnl_valid),
  .i_ibp_rd_chnl_accept  (lqwq_ibp_rd_chnl_accept),
  .i_ibp_rd_chnl         (lqwq_ibp_rd_chnl),

  .i_ibp_wrsp_chnl_valid (lqwq_ibp_wrsp_chnl_valid),
  .i_ibp_wrsp_chnl_accept(lqwq_ibp_wrsp_chnl_accept),
  .clk        (preprc_lq_wq_clk_gated  ),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a      (rst_a)
  );











 wire [1-1:0] lq_wq_ibp_cmd_chnl_valid;
 wire [1-1:0] lq_wq_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] lq_wq_ibp_cmd_chnl;

 wire [1-1:0] lq_wq_ibp_wd_chnl_valid;
 wire [1-1:0] lq_wq_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] lq_wq_ibp_wd_chnl;

 wire [1-1:0] lq_wq_ibp_rd_chnl_accept;
 wire [1-1:0] lq_wq_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] lq_wq_ibp_rd_chnl;

 wire [1-1:0] lq_wq_ibp_wrsp_chnl_valid;
 wire [1-1:0] lq_wq_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] lq_wq_ibp_wrsp_chnl;


  assign lq_wq_ibp_cmd_chnl_valid     = lqwq_ibp_cmd_chnl_valid  ;
  assign lqwq_ibp_cmd_chnl_accept    = lq_wq_ibp_cmd_chnl_accept ;
  assign lq_wq_ibp_cmd_chnl           = lqwq_ibp_cmd_chnl        ;

  assign lq_wq_ibp_wd_chnl_valid      = lqwq_ibp_wd_chnl_valid   ;
  assign lqwq_ibp_wd_chnl_accept     = lq_wq_ibp_wd_chnl_accept  ;
  assign lq_wq_ibp_wd_chnl            = lqwq_ibp_wd_chnl         ;

  assign lq_wq_ibp_rd_chnl_accept     = lqwq_ibp_rd_chnl_accept  ;
  assign lqwq_ibp_rd_chnl_valid      = lq_wq_ibp_rd_chnl_valid   ;
  assign lqwq_ibp_rd_chnl            = lq_wq_ibp_rd_chnl         ;

  assign lq_wq_ibp_wrsp_chnl_accept   = lqwq_ibp_wrsp_chnl_accept;
  assign lqwq_ibp_wrsp_chnl_valid    = lq_wq_ibp_wrsp_chnl_valid ;
  assign lqwq_ibp_wrsp_chnl          = lq_wq_ibp_wrsp_chnl       ;






 wire [1-1:0] bfed_lq_wq_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_lq_wq_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_lq_wq_ibp_cmd_chnl;

 wire [1-1:0] bfed_lq_wq_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_lq_wq_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] bfed_lq_wq_ibp_wd_chnl;

 wire [1-1:0] bfed_lq_wq_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_lq_wq_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] bfed_lq_wq_ibp_rd_chnl;

 wire [1-1:0] bfed_lq_wq_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_lq_wq_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_lq_wq_ibp_wrsp_chnl;


  assign bfed_lq_wq_ibp_cmd_chnl_valid     = lq_wq_ibp_cmd_chnl_valid  ;
  assign lq_wq_ibp_cmd_chnl_accept    = bfed_lq_wq_ibp_cmd_chnl_accept ;
  assign bfed_lq_wq_ibp_cmd_chnl           = lq_wq_ibp_cmd_chnl        ;

  assign bfed_lq_wq_ibp_wd_chnl_valid      = lq_wq_ibp_wd_chnl_valid   ;
  assign lq_wq_ibp_wd_chnl_accept     = bfed_lq_wq_ibp_wd_chnl_accept  ;
  assign bfed_lq_wq_ibp_wd_chnl            = lq_wq_ibp_wd_chnl         ;

  assign bfed_lq_wq_ibp_rd_chnl_accept     = lq_wq_ibp_rd_chnl_accept  ;
  assign lq_wq_ibp_rd_chnl_valid      = bfed_lq_wq_ibp_rd_chnl_valid   ;
  assign lq_wq_ibp_rd_chnl            = bfed_lq_wq_ibp_rd_chnl         ;

  assign bfed_lq_wq_ibp_wrsp_chnl_accept   = lq_wq_ibp_wrsp_chnl_accept;
  assign lq_wq_ibp_wrsp_chnl_valid    = bfed_lq_wq_ibp_wrsp_chnl_valid ;
  assign lq_wq_ibp_wrsp_chnl          = bfed_lq_wq_ibp_wrsp_chnl       ;





 wire [1-1:0] splt_bfed_lq_wq_ibp_cmd_chnl_valid;
 wire [1-1:0] splt_bfed_lq_wq_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] splt_bfed_lq_wq_ibp_cmd_chnl;

 wire [1-1:0] splt_bfed_lq_wq_ibp_wd_chnl_valid;
 wire [1-1:0] splt_bfed_lq_wq_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] splt_bfed_lq_wq_ibp_wd_chnl;

 wire [1-1:0] splt_bfed_lq_wq_ibp_rd_chnl_accept;
 wire [1-1:0] splt_bfed_lq_wq_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] splt_bfed_lq_wq_ibp_rd_chnl;

 wire [1-1:0] splt_bfed_lq_wq_ibp_wrsp_chnl_valid;
 wire [1-1:0] splt_bfed_lq_wq_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] splt_bfed_lq_wq_ibp_wrsp_chnl;

  assign splt_bfed_lq_wq_ibp_cmd_chnl_valid     = bfed_lq_wq_ibp_cmd_chnl_valid  ;
  assign bfed_lq_wq_ibp_cmd_chnl_accept    = splt_bfed_lq_wq_ibp_cmd_chnl_accept ;
  assign splt_bfed_lq_wq_ibp_cmd_chnl           = bfed_lq_wq_ibp_cmd_chnl        ;

  assign splt_bfed_lq_wq_ibp_wd_chnl_valid      = bfed_lq_wq_ibp_wd_chnl_valid   ;
  assign bfed_lq_wq_ibp_wd_chnl_accept     = splt_bfed_lq_wq_ibp_wd_chnl_accept  ;
  assign splt_bfed_lq_wq_ibp_wd_chnl            = bfed_lq_wq_ibp_wd_chnl         ;

  assign splt_bfed_lq_wq_ibp_rd_chnl_accept     = bfed_lq_wq_ibp_rd_chnl_accept  ;
  assign bfed_lq_wq_ibp_rd_chnl_valid      = splt_bfed_lq_wq_ibp_rd_chnl_valid   ;
  assign bfed_lq_wq_ibp_rd_chnl            = splt_bfed_lq_wq_ibp_rd_chnl         ;

  assign splt_bfed_lq_wq_ibp_wrsp_chnl_accept   = bfed_lq_wq_ibp_wrsp_chnl_accept;
  assign bfed_lq_wq_ibp_wrsp_chnl_valid    = splt_bfed_lq_wq_ibp_wrsp_chnl_valid ;
  assign bfed_lq_wq_ibp_wrsp_chnl          = splt_bfed_lq_wq_ibp_wrsp_chnl       ;




 wire [1-1:0] bfed_splt_bfed_lq_wq_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_splt_bfed_lq_wq_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_splt_bfed_lq_wq_ibp_cmd_chnl;

 wire [1-1:0] bfed_splt_bfed_lq_wq_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_splt_bfed_lq_wq_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] bfed_splt_bfed_lq_wq_ibp_wd_chnl;

 wire [1-1:0] bfed_splt_bfed_lq_wq_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_splt_bfed_lq_wq_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] bfed_splt_bfed_lq_wq_ibp_rd_chnl;

 wire [1-1:0] bfed_splt_bfed_lq_wq_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_splt_bfed_lq_wq_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_splt_bfed_lq_wq_ibp_wrsp_chnl;

  assign bfed_splt_bfed_lq_wq_ibp_cmd_chnl_valid     = splt_bfed_lq_wq_ibp_cmd_chnl_valid  ;
  assign splt_bfed_lq_wq_ibp_cmd_chnl_accept    = bfed_splt_bfed_lq_wq_ibp_cmd_chnl_accept ;
  assign bfed_splt_bfed_lq_wq_ibp_cmd_chnl           = splt_bfed_lq_wq_ibp_cmd_chnl        ;

  assign bfed_splt_bfed_lq_wq_ibp_wd_chnl_valid      = splt_bfed_lq_wq_ibp_wd_chnl_valid   ;
  assign splt_bfed_lq_wq_ibp_wd_chnl_accept     = bfed_splt_bfed_lq_wq_ibp_wd_chnl_accept  ;
  assign bfed_splt_bfed_lq_wq_ibp_wd_chnl            = splt_bfed_lq_wq_ibp_wd_chnl         ;

  assign bfed_splt_bfed_lq_wq_ibp_rd_chnl_accept     = splt_bfed_lq_wq_ibp_rd_chnl_accept  ;
  assign splt_bfed_lq_wq_ibp_rd_chnl_valid      = bfed_splt_bfed_lq_wq_ibp_rd_chnl_valid   ;
  assign splt_bfed_lq_wq_ibp_rd_chnl            = bfed_splt_bfed_lq_wq_ibp_rd_chnl         ;

  assign bfed_splt_bfed_lq_wq_ibp_wrsp_chnl_accept   = splt_bfed_lq_wq_ibp_wrsp_chnl_accept;
  assign splt_bfed_lq_wq_ibp_wrsp_chnl_valid    = bfed_splt_bfed_lq_wq_ibp_wrsp_chnl_valid ;
  assign splt_bfed_lq_wq_ibp_wrsp_chnl          = bfed_splt_bfed_lq_wq_ibp_wrsp_chnl       ;

// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_preprc_pack2ibp
  #(
    .ADDR_W (40),
    .DATA_W (64),



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
    .USER_W(1),
    .RGON_W(1)
    )
u_bfed_splt_bfed_lq_wq_pack2ibp
  (

  .ibp_cmd_valid             (bfed_lq_wq_ibp_cmd_valid),
  .ibp_cmd_accept            (bfed_lq_wq_ibp_cmd_accept),
  .ibp_cmd_read              (bfed_lq_wq_ibp_cmd_read),
  .ibp_cmd_addr              (bfed_lq_wq_ibp_cmd_addr),
  .ibp_cmd_wrap              (bfed_lq_wq_ibp_cmd_wrap),
  .ibp_cmd_data_size         (bfed_lq_wq_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (bfed_lq_wq_ibp_cmd_burst_size),
  .ibp_cmd_prot              (bfed_lq_wq_ibp_cmd_prot),
  .ibp_cmd_cache             (bfed_lq_wq_ibp_cmd_cache),
  .ibp_cmd_lock              (bfed_lq_wq_ibp_cmd_lock),
  .ibp_cmd_excl              (bfed_lq_wq_ibp_cmd_excl),

  .ibp_rd_valid              (bfed_lq_wq_ibp_rd_valid),
  .ibp_rd_excl_ok            (bfed_lq_wq_ibp_rd_excl_ok),
  .ibp_rd_accept             (bfed_lq_wq_ibp_rd_accept),
  .ibp_err_rd                (bfed_lq_wq_ibp_err_rd),
  .ibp_rd_data               (bfed_lq_wq_ibp_rd_data),
  .ibp_rd_last               (bfed_lq_wq_ibp_rd_last),

  .ibp_wr_valid              (bfed_lq_wq_ibp_wr_valid),
  .ibp_wr_accept             (bfed_lq_wq_ibp_wr_accept),
  .ibp_wr_data               (bfed_lq_wq_ibp_wr_data),
  .ibp_wr_mask               (bfed_lq_wq_ibp_wr_mask),
  .ibp_wr_last               (bfed_lq_wq_ibp_wr_last),

  .ibp_wr_done               (bfed_lq_wq_ibp_wr_done),
  .ibp_wr_excl_done          (bfed_lq_wq_ibp_wr_excl_done),
  .ibp_err_wr                (bfed_lq_wq_ibp_err_wr),
  .ibp_wr_resp_accept        (bfed_lq_wq_ibp_wr_resp_accept),





    .ibp_cmd_chnl_valid  (bfed_splt_bfed_lq_wq_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bfed_splt_bfed_lq_wq_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bfed_splt_bfed_lq_wq_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bfed_splt_bfed_lq_wq_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bfed_splt_bfed_lq_wq_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bfed_splt_bfed_lq_wq_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bfed_splt_bfed_lq_wq_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bfed_splt_bfed_lq_wq_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bfed_splt_bfed_lq_wq_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bfed_splt_bfed_lq_wq_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bfed_splt_bfed_lq_wq_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bfed_splt_bfed_lq_wq_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
    .ibp_cmd_chnl_rgon              (1'b0),
    .ibp_cmd_chnl_user              (1'b0),
    .ibp_cmd_rgon         (),
    .ibp_cmd_user         ()
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on











 wire [1-1:0] dmu_rbu_ibp_cmd_chnl_valid;
 wire [1-1:0] dmu_rbu_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] dmu_rbu_ibp_cmd_chnl;

 wire [1-1:0] dmu_rbu_ibp_wd_chnl_valid;
 wire [1-1:0] dmu_rbu_ibp_wd_chnl_accept;
 wire [145 * 1 -1:0] dmu_rbu_ibp_wd_chnl;

 wire [1-1:0] dmu_rbu_ibp_rd_chnl_accept;
 wire [1-1:0] dmu_rbu_ibp_rd_chnl_valid;
 wire [131 * 1 -1:0] dmu_rbu_ibp_rd_chnl;

 wire [1-1:0] dmu_rbu_ibp_wrsp_chnl_valid;
 wire [1-1:0] dmu_rbu_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] dmu_rbu_ibp_wrsp_chnl;


// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_preprc_ibp2pack
  #(
    .ADDR_W (40),
    .DATA_W (128),



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
    .USER_W(1),
    .RGON_W(1)
    )
u_dmu_rbu_ibp2pack
  (
    .rst_a                     (rst_a),
    .nmi_restart_r (nmi_restart_r ),
    .clk                       (preprc_dmu_rbu_dmu_wbu_clk_gated  ),

  .ibp_cmd_valid             (dmu_rbu_ibp_cmd_valid),
  .ibp_cmd_accept            (dmu_rbu_ibp_cmd_accept),
  .ibp_cmd_read              (dmu_rbu_ibp_cmd_read),
  .ibp_cmd_addr              (dmu_rbu_ibp_cmd_addr),
  .ibp_cmd_wrap              (dmu_rbu_ibp_cmd_wrap),
  .ibp_cmd_data_size         (dmu_rbu_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (dmu_rbu_ibp_cmd_burst_size),
  .ibp_cmd_prot              (dmu_rbu_ibp_cmd_prot),
  .ibp_cmd_cache             (dmu_rbu_ibp_cmd_cache),
  .ibp_cmd_lock              (dmu_rbu_ibp_cmd_lock),
  .ibp_cmd_excl              (dmu_rbu_ibp_cmd_excl),

  .ibp_rd_valid              (dmu_rbu_ibp_rd_valid),
  .ibp_rd_excl_ok            (dmu_rbu_ibp_rd_excl_ok),
  .ibp_rd_accept             (dmu_rbu_ibp_rd_accept),
  .ibp_err_rd                (dmu_rbu_ibp_err_rd),
  .ibp_rd_data               (dmu_rbu_ibp_rd_data),
  .ibp_rd_last               (dmu_rbu_ibp_rd_last),

  .ibp_wr_valid              (dmu_rbu_ibp_wr_valid),
  .ibp_wr_accept             (dmu_rbu_ibp_wr_accept),
  .ibp_wr_data               (dmu_rbu_ibp_wr_data),
  .ibp_wr_mask               (dmu_rbu_ibp_wr_mask),
  .ibp_wr_last               (dmu_rbu_ibp_wr_last),

  .ibp_wr_done               (dmu_rbu_ibp_wr_done),
  .ibp_wr_excl_done          (dmu_rbu_ibp_wr_excl_done),
  .ibp_err_wr                (dmu_rbu_ibp_err_wr),
  .ibp_wr_resp_accept        (dmu_rbu_ibp_wr_resp_accept),

    .ibp_cmd_rgon              (1'b0),
    .ibp_cmd_user              (1'b0),




    .ibp_cmd_chnl_valid  (dmu_rbu_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (dmu_rbu_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (dmu_rbu_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (dmu_rbu_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (dmu_rbu_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (dmu_rbu_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (dmu_rbu_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (dmu_rbu_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (dmu_rbu_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (dmu_rbu_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(dmu_rbu_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (dmu_rbu_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
    .ibp_cmd_chnl_rgon         (),
    .ibp_cmd_chnl_user         ()
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on

npuarc_biu_preprc_ibp_chnl_idle
  #(



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
   .OUTSTAND_NUM  (8),
   .OUTSTAND_CNT_W(3)
    )
  u_dmu_rbu_ibp_chnl_idle (
  .i_ibp_idle            (dmu_rbu_ibp_idle),

  .i_ibp_cmd_chnl_valid  (dmu_rbu_ibp_cmd_chnl_valid),
  .i_ibp_cmd_chnl_accept (dmu_rbu_ibp_cmd_chnl_accept),
  .i_ibp_cmd_chnl        (dmu_rbu_ibp_cmd_chnl),

  .i_ibp_rd_chnl_valid   (dmu_rbu_ibp_rd_chnl_valid),
  .i_ibp_rd_chnl_accept  (dmu_rbu_ibp_rd_chnl_accept),
  .i_ibp_rd_chnl         (dmu_rbu_ibp_rd_chnl),

  .i_ibp_wrsp_chnl_valid (dmu_rbu_ibp_wrsp_chnl_valid),
  .i_ibp_wrsp_chnl_accept(dmu_rbu_ibp_wrsp_chnl_accept),
  .clk        (preprc_dmu_rbu_dmu_wbu_clk_gated  ),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a      (rst_a)
  );




 wire [1-1:0] dmu_wbu_ibp_cmd_chnl_valid;
 wire [1-1:0] dmu_wbu_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] dmu_wbu_ibp_cmd_chnl;

 wire [1-1:0] dmu_wbu_ibp_wd_chnl_valid;
 wire [1-1:0] dmu_wbu_ibp_wd_chnl_accept;
 wire [145 * 1 -1:0] dmu_wbu_ibp_wd_chnl;

 wire [1-1:0] dmu_wbu_ibp_rd_chnl_accept;
 wire [1-1:0] dmu_wbu_ibp_rd_chnl_valid;
 wire [131 * 1 -1:0] dmu_wbu_ibp_rd_chnl;

 wire [1-1:0] dmu_wbu_ibp_wrsp_chnl_valid;
 wire [1-1:0] dmu_wbu_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] dmu_wbu_ibp_wrsp_chnl;


// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_preprc_ibp2pack
  #(
    .ADDR_W (40),
    .DATA_W (128),



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
    .USER_W(1),
    .RGON_W(1)
    )
u_dmu_wbu_ibp2pack
  (
    .rst_a                     (rst_a),
    .nmi_restart_r (nmi_restart_r ),
    .clk                       (preprc_dmu_rbu_dmu_wbu_clk_gated  ),

  .ibp_cmd_valid             (dmu_wbu_ibp_cmd_valid),
  .ibp_cmd_accept            (dmu_wbu_ibp_cmd_accept),
  .ibp_cmd_read              (dmu_wbu_ibp_cmd_read),
  .ibp_cmd_addr              (dmu_wbu_ibp_cmd_addr),
  .ibp_cmd_wrap              (dmu_wbu_ibp_cmd_wrap),
  .ibp_cmd_data_size         (dmu_wbu_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (dmu_wbu_ibp_cmd_burst_size),
  .ibp_cmd_prot              (dmu_wbu_ibp_cmd_prot),
  .ibp_cmd_cache             (dmu_wbu_ibp_cmd_cache),
  .ibp_cmd_lock              (dmu_wbu_ibp_cmd_lock),
  .ibp_cmd_excl              (dmu_wbu_ibp_cmd_excl),

  .ibp_rd_valid              (dmu_wbu_ibp_rd_valid),
  .ibp_rd_excl_ok            (dmu_wbu_ibp_rd_excl_ok),
  .ibp_rd_accept             (dmu_wbu_ibp_rd_accept),
  .ibp_err_rd                (dmu_wbu_ibp_err_rd),
  .ibp_rd_data               (dmu_wbu_ibp_rd_data),
  .ibp_rd_last               (dmu_wbu_ibp_rd_last),

  .ibp_wr_valid              (dmu_wbu_ibp_wr_valid),
  .ibp_wr_accept             (dmu_wbu_ibp_wr_accept),
  .ibp_wr_data               (dmu_wbu_ibp_wr_data),
  .ibp_wr_mask               (dmu_wbu_ibp_wr_mask),
  .ibp_wr_last               (dmu_wbu_ibp_wr_last),

  .ibp_wr_done               (dmu_wbu_ibp_wr_done),
  .ibp_wr_excl_done          (dmu_wbu_ibp_wr_excl_done),
  .ibp_err_wr                (dmu_wbu_ibp_err_wr),
  .ibp_wr_resp_accept        (dmu_wbu_ibp_wr_resp_accept),

    .ibp_cmd_rgon              (1'b0),
    .ibp_cmd_user              (1'b0),




    .ibp_cmd_chnl_valid  (dmu_wbu_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (dmu_wbu_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (dmu_wbu_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (dmu_wbu_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (dmu_wbu_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (dmu_wbu_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (dmu_wbu_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (dmu_wbu_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (dmu_wbu_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (dmu_wbu_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(dmu_wbu_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (dmu_wbu_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
    .ibp_cmd_chnl_rgon         (),
    .ibp_cmd_chnl_user         ()
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on

npuarc_biu_preprc_ibp_chnl_idle
  #(



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
   .OUTSTAND_NUM  (8),
   .OUTSTAND_CNT_W(3)
    )
  u_dmu_wbu_ibp_chnl_idle (
  .i_ibp_idle            (dmu_wbu_ibp_idle),

  .i_ibp_cmd_chnl_valid  (dmu_wbu_ibp_cmd_chnl_valid),
  .i_ibp_cmd_chnl_accept (dmu_wbu_ibp_cmd_chnl_accept),
  .i_ibp_cmd_chnl        (dmu_wbu_ibp_cmd_chnl),

  .i_ibp_rd_chnl_valid   (dmu_wbu_ibp_rd_chnl_valid),
  .i_ibp_rd_chnl_accept  (dmu_wbu_ibp_rd_chnl_accept),
  .i_ibp_rd_chnl         (dmu_wbu_ibp_rd_chnl),

  .i_ibp_wrsp_chnl_valid (dmu_wbu_ibp_wrsp_chnl_valid),
  .i_ibp_wrsp_chnl_accept(dmu_wbu_ibp_wrsp_chnl_accept),
  .clk        (preprc_dmu_rbu_dmu_wbu_clk_gated  ),
  .nmi_restart_r (nmi_restart_r ),
  .rst_a      (rst_a)
  );











 wire [1-1:0] dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid;
 wire [1-1:0] dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] dmu_rbu_dmu_wbu_ibp_cmd_chnl;

 wire [1-1:0] dmu_rbu_dmu_wbu_ibp_wd_chnl_valid;
 wire [1-1:0] dmu_rbu_dmu_wbu_ibp_wd_chnl_accept;
 wire [145 * 1 -1:0] dmu_rbu_dmu_wbu_ibp_wd_chnl;

 wire [1-1:0] dmu_rbu_dmu_wbu_ibp_rd_chnl_accept;
 wire [1-1:0] dmu_rbu_dmu_wbu_ibp_rd_chnl_valid;
 wire [131 * 1 -1:0] dmu_rbu_dmu_wbu_ibp_rd_chnl;

 wire [1-1:0] dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid;
 wire [1-1:0] dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] dmu_rbu_dmu_wbu_ibp_wrsp_chnl;


   npuarc_biu_preprc_ibp_rwmerg
    #(



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
      .USER_W(1),
      .RO_IS_FULL_IBP(0),
      .OUTSTAND_NUM  (8),
      .OUTSTAND_CNT_W(3)
    ) u_dmu_rbu_dmu_wbu_ibp_rwmerg (




    .ro_ibp_cmd_chnl_valid  (dmu_rbu_ibp_cmd_chnl_valid),
    .ro_ibp_cmd_chnl_accept (dmu_rbu_ibp_cmd_chnl_accept),
    .ro_ibp_cmd_chnl        (dmu_rbu_ibp_cmd_chnl),

    .ro_ibp_rd_chnl_valid   (dmu_rbu_ibp_rd_chnl_valid),
    .ro_ibp_rd_chnl_accept  (dmu_rbu_ibp_rd_chnl_accept),
    .ro_ibp_rd_chnl         (dmu_rbu_ibp_rd_chnl),

    .ro_ibp_wd_chnl_valid   (dmu_rbu_ibp_wd_chnl_valid),
    .ro_ibp_wd_chnl_accept  (dmu_rbu_ibp_wd_chnl_accept),
    .ro_ibp_wd_chnl         (dmu_rbu_ibp_wd_chnl),

    .ro_ibp_wrsp_chnl_valid (dmu_rbu_ibp_wrsp_chnl_valid),
    .ro_ibp_wrsp_chnl_accept(dmu_rbu_ibp_wrsp_chnl_accept),
    .ro_ibp_wrsp_chnl       (dmu_rbu_ibp_wrsp_chnl),




    .wo_ibp_cmd_chnl_valid  (dmu_wbu_ibp_cmd_chnl_valid),
    .wo_ibp_cmd_chnl_accept (dmu_wbu_ibp_cmd_chnl_accept),
    .wo_ibp_cmd_chnl        (dmu_wbu_ibp_cmd_chnl),

    .wo_ibp_rd_chnl_valid   (dmu_wbu_ibp_rd_chnl_valid),
    .wo_ibp_rd_chnl_accept  (dmu_wbu_ibp_rd_chnl_accept),
    .wo_ibp_rd_chnl         (dmu_wbu_ibp_rd_chnl),

    .wo_ibp_wd_chnl_valid   (dmu_wbu_ibp_wd_chnl_valid),
    .wo_ibp_wd_chnl_accept  (dmu_wbu_ibp_wd_chnl_accept),
    .wo_ibp_wd_chnl         (dmu_wbu_ibp_wd_chnl),

    .wo_ibp_wrsp_chnl_valid (dmu_wbu_ibp_wrsp_chnl_valid),
    .wo_ibp_wrsp_chnl_accept(dmu_wbu_ibp_wrsp_chnl_accept),
    .wo_ibp_wrsp_chnl       (dmu_wbu_ibp_wrsp_chnl),




    .rw_ibp_cmd_chnl_valid  (dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid),
    .rw_ibp_cmd_chnl_accept (dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept),
    .rw_ibp_cmd_chnl        (dmu_rbu_dmu_wbu_ibp_cmd_chnl),

    .rw_ibp_rd_chnl_valid   (dmu_rbu_dmu_wbu_ibp_rd_chnl_valid),
    .rw_ibp_rd_chnl_accept  (dmu_rbu_dmu_wbu_ibp_rd_chnl_accept),
    .rw_ibp_rd_chnl         (dmu_rbu_dmu_wbu_ibp_rd_chnl),

    .rw_ibp_wd_chnl_valid   (dmu_rbu_dmu_wbu_ibp_wd_chnl_valid),
    .rw_ibp_wd_chnl_accept  (dmu_rbu_dmu_wbu_ibp_wd_chnl_accept),
    .rw_ibp_wd_chnl         (dmu_rbu_dmu_wbu_ibp_wd_chnl),

    .rw_ibp_wrsp_chnl_valid (dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid),
    .rw_ibp_wrsp_chnl_accept(dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept),
    .rw_ibp_wrsp_chnl       (dmu_rbu_dmu_wbu_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
       .ro_ibp_cmd_chnl_user(1'b0),
       .wo_ibp_cmd_chnl_user(1'b0),
       .rw_ibp_cmd_chnl_user(),
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b
     .clk            (preprc_dmu_rbu_dmu_wbu_clk_gated  ),
     .nmi_restart_r (nmi_restart_r ),
     .rst_a          (rst_a)
     );





 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl;

 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept;
 wire [145 * 1 -1:0] bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl;

 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid;
 wire [131 * 1 -1:0] bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl;

 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl;


  assign bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid     = dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid  ;
  assign dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept    = bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl           = dmu_rbu_dmu_wbu_ibp_cmd_chnl        ;

  assign bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid      = dmu_rbu_dmu_wbu_ibp_wd_chnl_valid   ;
  assign dmu_rbu_dmu_wbu_ibp_wd_chnl_accept     = bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept  ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl            = dmu_rbu_dmu_wbu_ibp_wd_chnl         ;

  assign bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept     = dmu_rbu_dmu_wbu_ibp_rd_chnl_accept  ;
  assign dmu_rbu_dmu_wbu_ibp_rd_chnl_valid      = bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid   ;
  assign dmu_rbu_dmu_wbu_ibp_rd_chnl            = bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl         ;

  assign bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept   = dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept;
  assign dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid    = bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid ;
  assign dmu_rbu_dmu_wbu_ibp_wrsp_chnl          = bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl       ;





 wire [1-1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid;
 wire [1-1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl;

 wire [1-1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid;
 wire [1-1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept;
 wire [145 * 1 -1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl;

 wire [1-1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept;
 wire [1-1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid;
 wire [131 * 1 -1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl;

 wire [1-1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid;
 wire [1-1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl;

  assign splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid     = bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid  ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept    = splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept ;
  assign splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl           = bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl        ;

  assign splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid      = bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid   ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept     = splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept  ;
  assign splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl            = bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl         ;

  assign splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept     = bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept  ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid      = splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid   ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl            = splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl         ;

  assign splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept   = bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept;
  assign bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid    = splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl          = splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl       ;




 wire [1-1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl;

 wire [1-1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept;
 wire [145 * 1 -1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl;

 wire [1-1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid;
 wire [131 * 1 -1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl;

 wire [1-1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl;

// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_preprc_ibp_buffer
  #(
    .I_IBP_SUPPORT_RTIO    (0),
    .O_IBP_SUPPORT_RTIO    (0),
    .OUTSTAND_NUM    (8),
    .OUTSTAND_CNT_W  (3),
    .USER_W          (1),
    .RGON_W          (1),



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
    .THROUGH_MODE       (0),
    .CMD_CHNL_FIFO_MWHILE  (0),
    .WDATA_CHNL_FIFO_MWHILE(0),
    .RDATA_CHNL_FIFO_MWHILE(0),
    .WRESP_CHNL_FIFO_MWHILE(0),
    .CMD_CHNL_FIFO_DEPTH(2),
    .WDATA_CHNL_FIFO_DEPTH(2),
    .RDATA_CHNL_FIFO_DEPTH(2),
    .WRESP_CHNL_FIFO_DEPTH(2)
    )
 u_splt_bfed_dmu_rbu_dmu_wbu_ibp_buffer(
// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
    .ibp_buffer_idle       (),
    .o_ibp_cmd_chnl_rgon   (),
    .o_ibp_cmd_chnl_user   (),
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b
    .i_ibp_clk_en          (1'b1),
    .o_ibp_clk_en          (1'b1),
    .i_ibp_cmd_chnl_rgon   (1'b0),
    .i_ibp_cmd_chnl_user   (1'b0),




    .i_ibp_cmd_chnl_valid  (splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl),





    .o_ibp_cmd_chnl_valid  (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl),

    .rst_a               (rst_a),
    .nmi_restart_r (nmi_restart_r ),
    .clk                 (preprc_dmu_rbu_dmu_wbu_clk_gated  )
);

// leda NTL_CON10 on
// leda NTL_CON10B on
// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_preprc_pack2ibp
  #(
    .ADDR_W (40),
    .DATA_W (128),



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
    .CMD_CHNL_ADDR_W         (40),
    .CMD_CHNL_W              (57),

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
    .USER_W(1),
    .RGON_W(1)
    )
u_bfed_splt_bfed_dmu_rbu_dmu_wbu_pack2ibp
  (

  .ibp_cmd_valid             (bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid),
  .ibp_cmd_accept            (bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept),
  .ibp_cmd_read              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_read),
  .ibp_cmd_addr              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr),
  .ibp_cmd_wrap              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap),
  .ibp_cmd_data_size         (bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size),
  .ibp_cmd_prot              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot),
  .ibp_cmd_cache             (bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache),
  .ibp_cmd_lock              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock),
  .ibp_cmd_excl              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl),

  .ibp_rd_valid              (bfed_dmu_rbu_dmu_wbu_ibp_rd_valid),
  .ibp_rd_excl_ok            (bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok),
  .ibp_rd_accept             (bfed_dmu_rbu_dmu_wbu_ibp_rd_accept),
  .ibp_err_rd                (bfed_dmu_rbu_dmu_wbu_ibp_err_rd),
  .ibp_rd_data               (bfed_dmu_rbu_dmu_wbu_ibp_rd_data),
  .ibp_rd_last               (bfed_dmu_rbu_dmu_wbu_ibp_rd_last),

  .ibp_wr_valid              (bfed_dmu_rbu_dmu_wbu_ibp_wr_valid),
  .ibp_wr_accept             (bfed_dmu_rbu_dmu_wbu_ibp_wr_accept),
  .ibp_wr_data               (bfed_dmu_rbu_dmu_wbu_ibp_wr_data),
  .ibp_wr_mask               (bfed_dmu_rbu_dmu_wbu_ibp_wr_mask),
  .ibp_wr_last               (bfed_dmu_rbu_dmu_wbu_ibp_wr_last),

  .ibp_wr_done               (bfed_dmu_rbu_dmu_wbu_ibp_wr_done),
  .ibp_wr_excl_done          (bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done),
  .ibp_err_wr                (bfed_dmu_rbu_dmu_wbu_ibp_err_wr),
  .ibp_wr_resp_accept        (bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept),





    .ibp_cmd_chnl_valid  (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bfed_splt_bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
    .ibp_cmd_chnl_rgon              (1'b0),
    .ibp_cmd_chnl_user              (1'b0),
    .ibp_cmd_rgon         (),
    .ibp_cmd_user         ()
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on





// spyglass enable_block W528
endmodule // biu_ibp_preprc




