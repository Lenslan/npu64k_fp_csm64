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
//  Verilog module of biu_cbu master port
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"

// Set simulation timescale
//
`include "const.def"



module npuarc_biu_cbu_mst
// leda G_521_2_B off
// LMD: Use lowercase letters for all signal reg, net and port names
// LJ: Pfx may include the uppercase, so disable the lint checking rule
  (





  input                                   bfed_core0_nllm_l2ifu_ibp_cmd_valid,
  output                                  bfed_core0_nllm_l2ifu_ibp_cmd_accept,
  input                                   bfed_core0_nllm_l2ifu_ibp_cmd_read,
  input   [40                -1:0]       bfed_core0_nllm_l2ifu_ibp_cmd_addr,
  input                                   bfed_core0_nllm_l2ifu_ibp_cmd_wrap,
  input   [3-1:0]       bfed_core0_nllm_l2ifu_ibp_cmd_data_size,
  input   [4-1:0]       bfed_core0_nllm_l2ifu_ibp_cmd_burst_size,
  input   [2-1:0]       bfed_core0_nllm_l2ifu_ibp_cmd_prot,
  input   [4-1:0]       bfed_core0_nllm_l2ifu_ibp_cmd_cache,
  input                                   bfed_core0_nllm_l2ifu_ibp_cmd_lock,
  input                                   bfed_core0_nllm_l2ifu_ibp_cmd_excl,

  output                                  bfed_core0_nllm_l2ifu_ibp_rd_valid,
  output                                  bfed_core0_nllm_l2ifu_ibp_rd_excl_ok,
  input                                   bfed_core0_nllm_l2ifu_ibp_rd_accept,
  output                                  bfed_core0_nllm_l2ifu_ibp_err_rd,
  output  [64               -1:0]        bfed_core0_nllm_l2ifu_ibp_rd_data,
  output                                  bfed_core0_nllm_l2ifu_ibp_rd_last,

  input                                   bfed_core0_nllm_l2ifu_ibp_wr_valid,
  output                                  bfed_core0_nllm_l2ifu_ibp_wr_accept,
  input   [64               -1:0]        bfed_core0_nllm_l2ifu_ibp_wr_data,
  input   [8  -1:0]                    bfed_core0_nllm_l2ifu_ibp_wr_mask,
  input                                   bfed_core0_nllm_l2ifu_ibp_wr_last,

  output                                  bfed_core0_nllm_l2ifu_ibp_wr_done,
  output                                  bfed_core0_nllm_l2ifu_ibp_wr_excl_done,
  output                                  bfed_core0_nllm_l2ifu_ibp_err_wr,
  input                                   bfed_core0_nllm_l2ifu_ibp_wr_resp_accept,


  input                                   bfed_lq_wq_ibp_cmd_valid,
  output                                  bfed_lq_wq_ibp_cmd_accept,
  input                                   bfed_lq_wq_ibp_cmd_read,
  input   [40                -1:0]       bfed_lq_wq_ibp_cmd_addr,
  input                                   bfed_lq_wq_ibp_cmd_wrap,
  input   [3-1:0]       bfed_lq_wq_ibp_cmd_data_size,
  input   [4-1:0]       bfed_lq_wq_ibp_cmd_burst_size,
  input   [2-1:0]       bfed_lq_wq_ibp_cmd_prot,
  input   [4-1:0]       bfed_lq_wq_ibp_cmd_cache,
  input                                   bfed_lq_wq_ibp_cmd_lock,
  input                                   bfed_lq_wq_ibp_cmd_excl,

  output                                  bfed_lq_wq_ibp_rd_valid,
  output                                  bfed_lq_wq_ibp_rd_excl_ok,
  input                                   bfed_lq_wq_ibp_rd_accept,
  output                                  bfed_lq_wq_ibp_err_rd,
  output  [64               -1:0]        bfed_lq_wq_ibp_rd_data,
  output                                  bfed_lq_wq_ibp_rd_last,

  input                                   bfed_lq_wq_ibp_wr_valid,
  output                                  bfed_lq_wq_ibp_wr_accept,
  input   [64               -1:0]        bfed_lq_wq_ibp_wr_data,
  input   [8  -1:0]                    bfed_lq_wq_ibp_wr_mask,
  input                                   bfed_lq_wq_ibp_wr_last,

  output                                  bfed_lq_wq_ibp_wr_done,
  output                                  bfed_lq_wq_ibp_wr_excl_done,
  output                                  bfed_lq_wq_ibp_err_wr,
  input                                   bfed_lq_wq_ibp_wr_resp_accept,


  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_valid,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_cmd_accept,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_read,
  input   [40                -1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_addr,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_wrap,
  input   [3-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_data_size,
  input   [4-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_burst_size,
  input   [2-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_prot,
  input   [4-1:0]       bfed_dmu_rbu_dmu_wbu_ibp_cmd_cache,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_lock,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_cmd_excl,

  output                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_valid,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_excl_ok,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_rd_accept,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_err_rd,
  output  [128               -1:0]        bfed_dmu_rbu_dmu_wbu_ibp_rd_data,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_rd_last,

  input                                   bfed_dmu_rbu_dmu_wbu_ibp_wr_valid,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_accept,
  input   [128               -1:0]        bfed_dmu_rbu_dmu_wbu_ibp_wr_data,
  input   [16  -1:0]                    bfed_dmu_rbu_dmu_wbu_ibp_wr_mask,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_wr_last,

  output                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_done,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_wr_excl_done,
  output                                  bfed_dmu_rbu_dmu_wbu_ibp_err_wr,
  input                                   bfed_dmu_rbu_dmu_wbu_ibp_wr_resp_accept,


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


  input                                  mbus_clk_en,
  input                                  clk,
  input                                  nmi_restart_r, // NMI reset signal
  input                                  rst_a
);

// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning





/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////
// Pack all the IBP buses




 wire [1-1:0] bfed_core0_nllm_l2ifu_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_core0_nllm_l2ifu_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_core0_nllm_l2ifu_ibp_cmd_chnl;

 wire [1-1:0] bfed_core0_nllm_l2ifu_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_core0_nllm_l2ifu_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] bfed_core0_nllm_l2ifu_ibp_wd_chnl;

 wire [1-1:0] bfed_core0_nllm_l2ifu_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_core0_nllm_l2ifu_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] bfed_core0_nllm_l2ifu_ibp_rd_chnl;

 wire [1-1:0] bfed_core0_nllm_l2ifu_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_core0_nllm_l2ifu_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_core0_nllm_l2ifu_ibp_wrsp_chnl;



    wire [1-1:0] bfed_core0_nllm_l2ifu_ibp_cmd_user = {1{1'b0}};
    wire [1-1:0] bfed_core0_nllm_l2ifu_ibp_cmd_chnl_user;

// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_bfed_core0_nllm_l2ifu_ibp_cmd_chnl_rgon;
// spyglass enable_block W240
// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_ibp2pack
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
u_bfed_core0_nllm_l2ifu_ibp2pack
  (
    .rst_a                     (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                       (clk               ) ,

  .ibp_cmd_valid             (bfed_core0_nllm_l2ifu_ibp_cmd_valid),
  .ibp_cmd_accept            (bfed_core0_nllm_l2ifu_ibp_cmd_accept),
  .ibp_cmd_read              (bfed_core0_nllm_l2ifu_ibp_cmd_read),
  .ibp_cmd_addr              (bfed_core0_nllm_l2ifu_ibp_cmd_addr),
  .ibp_cmd_wrap              (bfed_core0_nllm_l2ifu_ibp_cmd_wrap),
  .ibp_cmd_data_size         (bfed_core0_nllm_l2ifu_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (bfed_core0_nllm_l2ifu_ibp_cmd_burst_size),
  .ibp_cmd_prot              (bfed_core0_nllm_l2ifu_ibp_cmd_prot),
  .ibp_cmd_cache             (bfed_core0_nllm_l2ifu_ibp_cmd_cache),
  .ibp_cmd_lock              (bfed_core0_nllm_l2ifu_ibp_cmd_lock),
  .ibp_cmd_excl              (bfed_core0_nllm_l2ifu_ibp_cmd_excl),

  .ibp_rd_valid              (bfed_core0_nllm_l2ifu_ibp_rd_valid),
  .ibp_rd_excl_ok            (bfed_core0_nllm_l2ifu_ibp_rd_excl_ok),
  .ibp_rd_accept             (bfed_core0_nllm_l2ifu_ibp_rd_accept),
  .ibp_err_rd                (bfed_core0_nllm_l2ifu_ibp_err_rd),
  .ibp_rd_data               (bfed_core0_nllm_l2ifu_ibp_rd_data),
  .ibp_rd_last               (bfed_core0_nllm_l2ifu_ibp_rd_last),

  .ibp_wr_valid              (bfed_core0_nllm_l2ifu_ibp_wr_valid),
  .ibp_wr_accept             (bfed_core0_nllm_l2ifu_ibp_wr_accept),
  .ibp_wr_data               (bfed_core0_nllm_l2ifu_ibp_wr_data),
  .ibp_wr_mask               (bfed_core0_nllm_l2ifu_ibp_wr_mask),
  .ibp_wr_last               (bfed_core0_nllm_l2ifu_ibp_wr_last),

  .ibp_wr_done               (bfed_core0_nllm_l2ifu_ibp_wr_done),
  .ibp_wr_excl_done          (bfed_core0_nllm_l2ifu_ibp_wr_excl_done),
  .ibp_err_wr                (bfed_core0_nllm_l2ifu_ibp_err_wr),
  .ibp_wr_resp_accept        (bfed_core0_nllm_l2ifu_ibp_wr_resp_accept),

    .ibp_cmd_rgon              (1'b1),
    .ibp_cmd_user              (bfed_core0_nllm_l2ifu_ibp_cmd_user),




    .ibp_cmd_chnl_valid  (bfed_core0_nllm_l2ifu_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bfed_core0_nllm_l2ifu_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bfed_core0_nllm_l2ifu_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bfed_core0_nllm_l2ifu_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bfed_core0_nllm_l2ifu_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bfed_core0_nllm_l2ifu_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bfed_core0_nllm_l2ifu_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bfed_core0_nllm_l2ifu_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bfed_core0_nllm_l2ifu_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bfed_core0_nllm_l2ifu_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bfed_core0_nllm_l2ifu_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bfed_core0_nllm_l2ifu_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
    .ibp_cmd_chnl_rgon         (unused_bfed_core0_nllm_l2ifu_ibp_cmd_chnl_rgon),
// spyglass enable_block UnloadedOutTerm-ML
    .ibp_cmd_chnl_user         (bfed_core0_nllm_l2ifu_ibp_cmd_chnl_user)
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on






 wire [1-1:0] bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl;

 wire [1-1:0] bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl;

 wire [1-1:0] bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl;

 wire [1-1:0] bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl;

wire [1-1:0] bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_user;


  assign bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_valid     = bfed_core0_nllm_l2ifu_ibp_cmd_chnl_valid  ;
  assign bfed_core0_nllm_l2ifu_ibp_cmd_chnl_accept    = bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_accept ;
  assign bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl           = bfed_core0_nllm_l2ifu_ibp_cmd_chnl        ;

  assign bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_valid      = bfed_core0_nllm_l2ifu_ibp_wd_chnl_valid   ;
  assign bfed_core0_nllm_l2ifu_ibp_wd_chnl_accept     = bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_accept  ;
  assign bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl            = bfed_core0_nllm_l2ifu_ibp_wd_chnl         ;

  assign bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_accept     = bfed_core0_nllm_l2ifu_ibp_rd_chnl_accept  ;
  assign bfed_core0_nllm_l2ifu_ibp_rd_chnl_valid      = bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_valid   ;
  assign bfed_core0_nllm_l2ifu_ibp_rd_chnl            = bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl         ;

  assign bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_accept   = bfed_core0_nllm_l2ifu_ibp_wrsp_chnl_accept;
  assign bfed_core0_nllm_l2ifu_ibp_wrsp_chnl_valid    = bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_valid ;
  assign bfed_core0_nllm_l2ifu_ibp_wrsp_chnl          = bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl       ;

  assign bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_user      = bfed_core0_nllm_l2ifu_ibp_cmd_chnl_user;


// Covert the bfed_core0_nllm_l2ifu_bfed_ IBP width



 wire [1-1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_valid;
 wire [1-1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl;

 wire [1-1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_valid;
 wire [1-1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl;

 wire [1-1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_accept;
 wire [1-1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl;

 wire [1-1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_valid;
 wire [1-1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl;

wire [1-1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_user;

// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_bfed_core0_nllm_l2ifu_bfed_ibpx2ibpy_o_ibp_cmd_chnl_rgon;
// spyglass enable_block W240
npuarc_biu_ibpx2ibpy
  #(
     .N2W_SUPPORT_NARROW_TRANS (1),
    .W2N_SUPPORT_BURST_TRANS  (1),

    .BYPBUF_WD_CHNL (0),
    .SPLT_FIFO_DEPTH (8),
    .X_W  (64),
    .Y_W  (64),



    .X_CMD_CHNL_READ           (0),
    .X_CMD_CHNL_WRAP           (1),
    .X_CMD_CHNL_DATA_SIZE_LSB  (2),
    .X_CMD_CHNL_DATA_SIZE_W    (3),
    .X_CMD_CHNL_BURST_SIZE_LSB (5),
    .X_CMD_CHNL_BURST_SIZE_W   (4),
    .X_CMD_CHNL_PROT_LSB       (9),
    .X_CMD_CHNL_PROT_W         (2),
    .X_CMD_CHNL_CACHE_LSB      (11),
    .X_CMD_CHNL_CACHE_W        (4),
    .X_CMD_CHNL_LOCK           (15),
    .X_CMD_CHNL_EXCL           (16),
    .X_CMD_CHNL_ADDR_LSB       (17),
    .X_CMD_CHNL_ADDR_W         (40),
    .X_CMD_CHNL_W              (57),

    .X_WD_CHNL_LAST            (0),
    .X_WD_CHNL_DATA_LSB        (1),
    .X_WD_CHNL_DATA_W          (64),
    .X_WD_CHNL_MASK_LSB        (65),
    .X_WD_CHNL_MASK_W          (8),
    .X_WD_CHNL_W               (73),

    .X_RD_CHNL_ERR_RD          (0),
    .X_RD_CHNL_RD_EXCL_OK      (2),
    .X_RD_CHNL_RD_LAST         (1),
    .X_RD_CHNL_RD_DATA_LSB     (3),
    .X_RD_CHNL_RD_DATA_W       (64),
    .X_RD_CHNL_W               (67),

    .X_WRSP_CHNL_WR_DONE       (0),
    .X_WRSP_CHNL_WR_EXCL_DONE  (1),
    .X_WRSP_CHNL_ERR_WR        (2),
    .X_WRSP_CHNL_W             (3),



    .Y_CMD_CHNL_READ           (0),
    .Y_CMD_CHNL_WRAP           (1),
    .Y_CMD_CHNL_DATA_SIZE_LSB  (2),
    .Y_CMD_CHNL_DATA_SIZE_W    (3),
    .Y_CMD_CHNL_BURST_SIZE_LSB (5),
    .Y_CMD_CHNL_BURST_SIZE_W   (4),
    .Y_CMD_CHNL_PROT_LSB       (9),
    .Y_CMD_CHNL_PROT_W         (2),
    .Y_CMD_CHNL_CACHE_LSB      (11),
    .Y_CMD_CHNL_CACHE_W        (4),
    .Y_CMD_CHNL_LOCK           (15),
    .Y_CMD_CHNL_EXCL           (16),
    .Y_CMD_CHNL_ADDR_LSB       (17),
    .Y_CMD_CHNL_ADDR_W         (40),
    .Y_CMD_CHNL_W              (57),

    .Y_WD_CHNL_LAST            (0),
    .Y_WD_CHNL_DATA_LSB        (1),
    .Y_WD_CHNL_DATA_W          (64),
    .Y_WD_CHNL_MASK_LSB        (65),
    .Y_WD_CHNL_MASK_W          (8),
    .Y_WD_CHNL_W               (73),

    .Y_RD_CHNL_ERR_RD          (0),
    .Y_RD_CHNL_RD_EXCL_OK      (2),
    .Y_RD_CHNL_RD_LAST         (1),
    .Y_RD_CHNL_RD_DATA_LSB     (3),
    .Y_RD_CHNL_RD_DATA_W       (64),
    .Y_RD_CHNL_W               (67),

    .Y_WRSP_CHNL_WR_DONE       (0),
    .Y_WRSP_CHNL_WR_EXCL_DONE  (1),
    .Y_WRSP_CHNL_ERR_WR        (2),
    .Y_WRSP_CHNL_W             (3),
    .X_USER_W  (1),
    .Y_USER_W  (1),
    .X_RGON_W  (1),
    .Y_RGON_W  (1)
    )
 u_bfed_core0_nllm_l2ifu_bfed_ibp64toibp64 (
    .i_ibp_cmd_chnl_rgon   (1'b1),



    .i_ibp_cmd_chnl_valid  (bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl),

    .i_ibp_cmd_chnl_user   (bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_user),





    .o_ibp_cmd_chnl_valid  (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
    .o_ibp_cmd_chnl_rgon   (unused_bfed_core0_nllm_l2ifu_bfed_ibpx2ibpy_o_ibp_cmd_chnl_rgon),
// spyglass enable_block UnloadedOutTerm-ML
    .o_ibp_cmd_chnl_user   (cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_user),
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

    .rst_a               (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                 (clk               )
);


wire bfed_core0_nllm_l2ifu_bfed_ibp_cmd_write_burst_en = 0;
wire [1+1-1:0] cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_wbursten_and_user =
         {bfed_core0_nllm_l2ifu_bfed_ibp_cmd_write_burst_en, cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_user};




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



    wire [1-1:0] bfed_lq_wq_ibp_cmd_user = {1{1'b0}};
    wire [1-1:0] bfed_lq_wq_ibp_cmd_chnl_user;

// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_bfed_lq_wq_ibp_cmd_chnl_rgon;
// spyglass enable_block W240
// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_ibp2pack
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
u_bfed_lq_wq_ibp2pack
  (
    .rst_a                     (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                       (clk               ) ,

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

    .ibp_cmd_rgon              (1'b1),
    .ibp_cmd_user              (bfed_lq_wq_ibp_cmd_user),




    .ibp_cmd_chnl_valid  (bfed_lq_wq_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bfed_lq_wq_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bfed_lq_wq_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bfed_lq_wq_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bfed_lq_wq_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bfed_lq_wq_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bfed_lq_wq_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bfed_lq_wq_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bfed_lq_wq_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bfed_lq_wq_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bfed_lq_wq_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bfed_lq_wq_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
    .ibp_cmd_chnl_rgon         (unused_bfed_lq_wq_ibp_cmd_chnl_rgon),
// spyglass enable_block UnloadedOutTerm-ML
    .ibp_cmd_chnl_user         (bfed_lq_wq_ibp_cmd_chnl_user)
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on






 wire [1-1:0] bfed_lq_wq_bfed_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_lq_wq_bfed_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_lq_wq_bfed_ibp_cmd_chnl;

 wire [1-1:0] bfed_lq_wq_bfed_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_lq_wq_bfed_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] bfed_lq_wq_bfed_ibp_wd_chnl;

 wire [1-1:0] bfed_lq_wq_bfed_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_lq_wq_bfed_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] bfed_lq_wq_bfed_ibp_rd_chnl;

 wire [1-1:0] bfed_lq_wq_bfed_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_lq_wq_bfed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_lq_wq_bfed_ibp_wrsp_chnl;

wire [1-1:0] bfed_lq_wq_bfed_ibp_cmd_chnl_user;


  assign bfed_lq_wq_bfed_ibp_cmd_chnl_valid     = bfed_lq_wq_ibp_cmd_chnl_valid  ;
  assign bfed_lq_wq_ibp_cmd_chnl_accept    = bfed_lq_wq_bfed_ibp_cmd_chnl_accept ;
  assign bfed_lq_wq_bfed_ibp_cmd_chnl           = bfed_lq_wq_ibp_cmd_chnl        ;

  assign bfed_lq_wq_bfed_ibp_wd_chnl_valid      = bfed_lq_wq_ibp_wd_chnl_valid   ;
  assign bfed_lq_wq_ibp_wd_chnl_accept     = bfed_lq_wq_bfed_ibp_wd_chnl_accept  ;
  assign bfed_lq_wq_bfed_ibp_wd_chnl            = bfed_lq_wq_ibp_wd_chnl         ;

  assign bfed_lq_wq_bfed_ibp_rd_chnl_accept     = bfed_lq_wq_ibp_rd_chnl_accept  ;
  assign bfed_lq_wq_ibp_rd_chnl_valid      = bfed_lq_wq_bfed_ibp_rd_chnl_valid   ;
  assign bfed_lq_wq_ibp_rd_chnl            = bfed_lq_wq_bfed_ibp_rd_chnl         ;

  assign bfed_lq_wq_bfed_ibp_wrsp_chnl_accept   = bfed_lq_wq_ibp_wrsp_chnl_accept;
  assign bfed_lq_wq_ibp_wrsp_chnl_valid    = bfed_lq_wq_bfed_ibp_wrsp_chnl_valid ;
  assign bfed_lq_wq_ibp_wrsp_chnl          = bfed_lq_wq_bfed_ibp_wrsp_chnl       ;

  assign bfed_lq_wq_bfed_ibp_cmd_chnl_user      = bfed_lq_wq_ibp_cmd_chnl_user;


// Covert the bfed_lq_wq_bfed_ IBP width



 wire [1-1:0] cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_valid;
 wire [1-1:0] cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] cvted_bfed_lq_wq_bfed_ibp_cmd_chnl;

 wire [1-1:0] cvted_bfed_lq_wq_bfed_ibp_wd_chnl_valid;
 wire [1-1:0] cvted_bfed_lq_wq_bfed_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] cvted_bfed_lq_wq_bfed_ibp_wd_chnl;

 wire [1-1:0] cvted_bfed_lq_wq_bfed_ibp_rd_chnl_accept;
 wire [1-1:0] cvted_bfed_lq_wq_bfed_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] cvted_bfed_lq_wq_bfed_ibp_rd_chnl;

 wire [1-1:0] cvted_bfed_lq_wq_bfed_ibp_wrsp_chnl_valid;
 wire [1-1:0] cvted_bfed_lq_wq_bfed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] cvted_bfed_lq_wq_bfed_ibp_wrsp_chnl;

wire [1-1:0] cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_user;

// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_bfed_lq_wq_bfed_ibpx2ibpy_o_ibp_cmd_chnl_rgon;
// spyglass enable_block W240
npuarc_biu_ibpx2ibpy
  #(
     .N2W_SUPPORT_NARROW_TRANS (1),
    .W2N_SUPPORT_BURST_TRANS  (1),

    .BYPBUF_WD_CHNL (0),
    .SPLT_FIFO_DEPTH (8),
    .X_W  (64),
    .Y_W  (64),



    .X_CMD_CHNL_READ           (0),
    .X_CMD_CHNL_WRAP           (1),
    .X_CMD_CHNL_DATA_SIZE_LSB  (2),
    .X_CMD_CHNL_DATA_SIZE_W    (3),
    .X_CMD_CHNL_BURST_SIZE_LSB (5),
    .X_CMD_CHNL_BURST_SIZE_W   (4),
    .X_CMD_CHNL_PROT_LSB       (9),
    .X_CMD_CHNL_PROT_W         (2),
    .X_CMD_CHNL_CACHE_LSB      (11),
    .X_CMD_CHNL_CACHE_W        (4),
    .X_CMD_CHNL_LOCK           (15),
    .X_CMD_CHNL_EXCL           (16),
    .X_CMD_CHNL_ADDR_LSB       (17),
    .X_CMD_CHNL_ADDR_W         (40),
    .X_CMD_CHNL_W              (57),

    .X_WD_CHNL_LAST            (0),
    .X_WD_CHNL_DATA_LSB        (1),
    .X_WD_CHNL_DATA_W          (64),
    .X_WD_CHNL_MASK_LSB        (65),
    .X_WD_CHNL_MASK_W          (8),
    .X_WD_CHNL_W               (73),

    .X_RD_CHNL_ERR_RD          (0),
    .X_RD_CHNL_RD_EXCL_OK      (2),
    .X_RD_CHNL_RD_LAST         (1),
    .X_RD_CHNL_RD_DATA_LSB     (3),
    .X_RD_CHNL_RD_DATA_W       (64),
    .X_RD_CHNL_W               (67),

    .X_WRSP_CHNL_WR_DONE       (0),
    .X_WRSP_CHNL_WR_EXCL_DONE  (1),
    .X_WRSP_CHNL_ERR_WR        (2),
    .X_WRSP_CHNL_W             (3),



    .Y_CMD_CHNL_READ           (0),
    .Y_CMD_CHNL_WRAP           (1),
    .Y_CMD_CHNL_DATA_SIZE_LSB  (2),
    .Y_CMD_CHNL_DATA_SIZE_W    (3),
    .Y_CMD_CHNL_BURST_SIZE_LSB (5),
    .Y_CMD_CHNL_BURST_SIZE_W   (4),
    .Y_CMD_CHNL_PROT_LSB       (9),
    .Y_CMD_CHNL_PROT_W         (2),
    .Y_CMD_CHNL_CACHE_LSB      (11),
    .Y_CMD_CHNL_CACHE_W        (4),
    .Y_CMD_CHNL_LOCK           (15),
    .Y_CMD_CHNL_EXCL           (16),
    .Y_CMD_CHNL_ADDR_LSB       (17),
    .Y_CMD_CHNL_ADDR_W         (40),
    .Y_CMD_CHNL_W              (57),

    .Y_WD_CHNL_LAST            (0),
    .Y_WD_CHNL_DATA_LSB        (1),
    .Y_WD_CHNL_DATA_W          (64),
    .Y_WD_CHNL_MASK_LSB        (65),
    .Y_WD_CHNL_MASK_W          (8),
    .Y_WD_CHNL_W               (73),

    .Y_RD_CHNL_ERR_RD          (0),
    .Y_RD_CHNL_RD_EXCL_OK      (2),
    .Y_RD_CHNL_RD_LAST         (1),
    .Y_RD_CHNL_RD_DATA_LSB     (3),
    .Y_RD_CHNL_RD_DATA_W       (64),
    .Y_RD_CHNL_W               (67),

    .Y_WRSP_CHNL_WR_DONE       (0),
    .Y_WRSP_CHNL_WR_EXCL_DONE  (1),
    .Y_WRSP_CHNL_ERR_WR        (2),
    .Y_WRSP_CHNL_W             (3),
    .X_USER_W  (1),
    .Y_USER_W  (1),
    .X_RGON_W  (1),
    .Y_RGON_W  (1)
    )
 u_bfed_lq_wq_bfed_ibp64toibp64 (
    .i_ibp_cmd_chnl_rgon   (1'b1),



    .i_ibp_cmd_chnl_valid  (bfed_lq_wq_bfed_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (bfed_lq_wq_bfed_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (bfed_lq_wq_bfed_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (bfed_lq_wq_bfed_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (bfed_lq_wq_bfed_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (bfed_lq_wq_bfed_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (bfed_lq_wq_bfed_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (bfed_lq_wq_bfed_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (bfed_lq_wq_bfed_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (bfed_lq_wq_bfed_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(bfed_lq_wq_bfed_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (bfed_lq_wq_bfed_ibp_wrsp_chnl),

    .i_ibp_cmd_chnl_user   (bfed_lq_wq_bfed_ibp_cmd_chnl_user),





    .o_ibp_cmd_chnl_valid  (cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (cvted_bfed_lq_wq_bfed_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (cvted_bfed_lq_wq_bfed_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (cvted_bfed_lq_wq_bfed_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (cvted_bfed_lq_wq_bfed_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (cvted_bfed_lq_wq_bfed_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (cvted_bfed_lq_wq_bfed_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (cvted_bfed_lq_wq_bfed_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (cvted_bfed_lq_wq_bfed_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(cvted_bfed_lq_wq_bfed_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (cvted_bfed_lq_wq_bfed_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
    .o_ibp_cmd_chnl_rgon   (unused_bfed_lq_wq_bfed_ibpx2ibpy_o_ibp_cmd_chnl_rgon),
// spyglass enable_block UnloadedOutTerm-ML
    .o_ibp_cmd_chnl_user   (cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_user),
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

    .rst_a               (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                 (clk               )
);


wire bfed_lq_wq_bfed_ibp_cmd_write_burst_en = 0;
wire [1+1-1:0] cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_wbursten_and_user =
         {bfed_lq_wq_bfed_ibp_cmd_write_burst_en, cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_user};




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



    wire [1-1:0] bfed_dmu_rbu_dmu_wbu_ibp_cmd_user = {1{1'b0}};
    wire [1-1:0] bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_user;

// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_rgon;
// spyglass enable_block W240
// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_ibp2pack
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
u_bfed_dmu_rbu_dmu_wbu_ibp2pack
  (
    .rst_a                     (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                       (clk               ) ,

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

    .ibp_cmd_rgon              (1'b1),
    .ibp_cmd_user              (bfed_dmu_rbu_dmu_wbu_ibp_cmd_user),




    .ibp_cmd_chnl_valid  (bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
    .ibp_cmd_chnl_rgon         (unused_bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_rgon),
// spyglass enable_block UnloadedOutTerm-ML
    .ibp_cmd_chnl_user         (bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_user)
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on






 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl;

 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_accept;
 wire [145 * 1 -1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl;

 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_valid;
 wire [131 * 1 -1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl;

 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl;

wire [1-1:0] bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_user;


  assign bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_valid     = bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_valid  ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_accept    = bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_accept ;
  assign bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl           = bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl        ;

  assign bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_valid      = bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_valid   ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl_accept     = bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_accept  ;
  assign bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl            = bfed_dmu_rbu_dmu_wbu_ibp_wd_chnl         ;

  assign bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_accept     = bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_accept  ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl_valid      = bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_valid   ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_rd_chnl            = bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl         ;

  assign bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_accept   = bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_accept;
  assign bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl_valid    = bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_valid ;
  assign bfed_dmu_rbu_dmu_wbu_ibp_wrsp_chnl          = bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl       ;

  assign bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_user      = bfed_dmu_rbu_dmu_wbu_ibp_cmd_chnl_user;


// Covert the bfed_dmu_rbu_dmu_wbu_bfed_ IBP width



 wire [1-1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_valid;
 wire [1-1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl;

 wire [1-1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_valid;
 wire [1-1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl;

 wire [1-1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_accept;
 wire [1-1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl;

 wire [1-1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_valid;
 wire [1-1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl;

wire [1-1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_user;

// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_bfed_dmu_rbu_dmu_wbu_bfed_ibpx2ibpy_o_ibp_cmd_chnl_rgon;
// spyglass enable_block W240
npuarc_biu_ibpx2ibpy
  #(
     .N2W_SUPPORT_NARROW_TRANS (1),
    .W2N_SUPPORT_BURST_TRANS  (1),

    .BYPBUF_WD_CHNL (0),
    .SPLT_FIFO_DEPTH (8),
    .X_W  (128),
    .Y_W  (64),



    .X_CMD_CHNL_READ           (0),
    .X_CMD_CHNL_WRAP           (1),
    .X_CMD_CHNL_DATA_SIZE_LSB  (2),
    .X_CMD_CHNL_DATA_SIZE_W    (3),
    .X_CMD_CHNL_BURST_SIZE_LSB (5),
    .X_CMD_CHNL_BURST_SIZE_W   (4),
    .X_CMD_CHNL_PROT_LSB       (9),
    .X_CMD_CHNL_PROT_W         (2),
    .X_CMD_CHNL_CACHE_LSB      (11),
    .X_CMD_CHNL_CACHE_W        (4),
    .X_CMD_CHNL_LOCK           (15),
    .X_CMD_CHNL_EXCL           (16),
    .X_CMD_CHNL_ADDR_LSB       (17),
    .X_CMD_CHNL_ADDR_W         (40),
    .X_CMD_CHNL_W              (57),

    .X_WD_CHNL_LAST            (0),
    .X_WD_CHNL_DATA_LSB        (1),
    .X_WD_CHNL_DATA_W          (128),
    .X_WD_CHNL_MASK_LSB        (129),
    .X_WD_CHNL_MASK_W          (16),
    .X_WD_CHNL_W               (145),

    .X_RD_CHNL_ERR_RD          (0),
    .X_RD_CHNL_RD_EXCL_OK      (2),
    .X_RD_CHNL_RD_LAST         (1),
    .X_RD_CHNL_RD_DATA_LSB     (3),
    .X_RD_CHNL_RD_DATA_W       (128),
    .X_RD_CHNL_W               (131),

    .X_WRSP_CHNL_WR_DONE       (0),
    .X_WRSP_CHNL_WR_EXCL_DONE  (1),
    .X_WRSP_CHNL_ERR_WR        (2),
    .X_WRSP_CHNL_W             (3),



    .Y_CMD_CHNL_READ           (0),
    .Y_CMD_CHNL_WRAP           (1),
    .Y_CMD_CHNL_DATA_SIZE_LSB  (2),
    .Y_CMD_CHNL_DATA_SIZE_W    (3),
    .Y_CMD_CHNL_BURST_SIZE_LSB (5),
    .Y_CMD_CHNL_BURST_SIZE_W   (4),
    .Y_CMD_CHNL_PROT_LSB       (9),
    .Y_CMD_CHNL_PROT_W         (2),
    .Y_CMD_CHNL_CACHE_LSB      (11),
    .Y_CMD_CHNL_CACHE_W        (4),
    .Y_CMD_CHNL_LOCK           (15),
    .Y_CMD_CHNL_EXCL           (16),
    .Y_CMD_CHNL_ADDR_LSB       (17),
    .Y_CMD_CHNL_ADDR_W         (40),
    .Y_CMD_CHNL_W              (57),

    .Y_WD_CHNL_LAST            (0),
    .Y_WD_CHNL_DATA_LSB        (1),
    .Y_WD_CHNL_DATA_W          (64),
    .Y_WD_CHNL_MASK_LSB        (65),
    .Y_WD_CHNL_MASK_W          (8),
    .Y_WD_CHNL_W               (73),

    .Y_RD_CHNL_ERR_RD          (0),
    .Y_RD_CHNL_RD_EXCL_OK      (2),
    .Y_RD_CHNL_RD_LAST         (1),
    .Y_RD_CHNL_RD_DATA_LSB     (3),
    .Y_RD_CHNL_RD_DATA_W       (64),
    .Y_RD_CHNL_W               (67),

    .Y_WRSP_CHNL_WR_DONE       (0),
    .Y_WRSP_CHNL_WR_EXCL_DONE  (1),
    .Y_WRSP_CHNL_ERR_WR        (2),
    .Y_WRSP_CHNL_W             (3),
    .X_USER_W  (1),
    .Y_USER_W  (1),
    .X_RGON_W  (1),
    .Y_RGON_W  (1)
    )
 u_bfed_dmu_rbu_dmu_wbu_bfed_ibp128toibp64 (
    .i_ibp_cmd_chnl_rgon   (1'b1),



    .i_ibp_cmd_chnl_valid  (bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl),

    .i_ibp_cmd_chnl_user   (bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_user),





    .o_ibp_cmd_chnl_valid  (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
    .o_ibp_cmd_chnl_rgon   (unused_bfed_dmu_rbu_dmu_wbu_bfed_ibpx2ibpy_o_ibp_cmd_chnl_rgon),
// spyglass enable_block UnloadedOutTerm-ML
    .o_ibp_cmd_chnl_user   (cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_user),
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

    .rst_a               (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                 (clk               )
);


wire bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_write_burst_en = 0;
wire [1+1-1:0] cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_wbursten_and_user =
         {bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_write_burst_en, cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_user};












// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: Dummy signals are indeed no driven
wire cming_dummy0;
wire cming_dummy1;
wire cming_ibp_lockable_dummy;
// leda NTL_CON13A on


// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: When there is no ibp compr, this signal no driving indeed
wire [4*3 -1:0] cming_ibp_uniq_id;
wire [(1+1)*3 -1:0] cming_ibp_cmd_chnl_wbursten_and_user;
wire [3 -1:0] cming_ibp_lockable;
// leda NTL_CON13A on



 wire [3-1:0] cming_ibp_cmd_chnl_valid;
 wire [3-1:0] cming_ibp_cmd_chnl_accept;
 wire [57 * 3 -1:0] cming_ibp_cmd_chnl;

 wire [3-1:0] cming_ibp_wd_chnl_valid;
 wire [3-1:0] cming_ibp_wd_chnl_accept;
 wire [73 * 3 -1:0] cming_ibp_wd_chnl;

 wire [3-1:0] cming_ibp_rd_chnl_accept;
 wire [3-1:0] cming_ibp_rd_chnl_valid;
 wire [67 * 3 -1:0] cming_ibp_rd_chnl;

 wire [3-1:0] cming_ibp_wrsp_chnl_valid;
 wire [3-1:0] cming_ibp_wrsp_chnl_accept;
 wire [3 * 3 -1:0] cming_ibp_wrsp_chnl;




    // no more 16 FIFO depth allowed to hurt timing



wire bfed_core0_nllm_l2ifu_bfed_ibp_lockable = 0;
wire bfed_lq_wq_bfed_ibp_lockable = 1;
wire bfed_dmu_rbu_dmu_wbu_bfed_ibp_lockable = 0;

// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0 / logic 1
// LJ: No care about the constant here
assign {cming_ibp_lockable_dummy,
        cming_ibp_lockable}
        = {
            1'b0
                  ,bfed_core0_nllm_l2ifu_bfed_ibp_lockable
                  ,bfed_lq_wq_bfed_ibp_lockable
                  ,bfed_dmu_rbu_dmu_wbu_bfed_ibp_lockable
   };

// leda NTL_CON16 on



// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0 / logic 1
// LJ: No care about the constant here
assign
  {
    cming_dummy0,
    cming_ibp_uniq_id,
    cming_ibp_cmd_chnl_wbursten_and_user,
    cming_ibp_cmd_chnl,
    cming_ibp_cmd_chnl_valid,
    cming_ibp_wd_chnl,
    cming_ibp_wd_chnl_valid,
    cming_ibp_rd_chnl_accept,
    cming_ibp_wrsp_chnl_accept
    }
  =
  {
    1'b1
              ,4'd0
              ,4'd1
              ,4'd2
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_wbursten_and_user
                  ,cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_wbursten_and_user
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_wbursten_and_user
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl
                  ,cvted_bfed_lq_wq_bfed_ibp_cmd_chnl
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_valid
                  ,cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_valid
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_valid
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl
                  ,cvted_bfed_lq_wq_bfed_ibp_wd_chnl
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_valid
                  ,cvted_bfed_lq_wq_bfed_ibp_wd_chnl_valid
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_valid
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_accept
                  ,cvted_bfed_lq_wq_bfed_ibp_rd_chnl_accept
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_accept
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_accept
                  ,cvted_bfed_lq_wq_bfed_ibp_wrsp_chnl_accept
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_accept
  };
// leda NTL_CON16 on

// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0 / logic 1
// LJ: No care about the constant here
assign
  {
    cming_dummy1
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl
                  ,cvted_bfed_lq_wq_bfed_ibp_rd_chnl
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_rd_chnl_valid
                  ,cvted_bfed_lq_wq_bfed_ibp_rd_chnl_valid
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_rd_chnl_valid
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl
                  ,cvted_bfed_lq_wq_bfed_ibp_wrsp_chnl
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wrsp_chnl_valid
                  ,cvted_bfed_lq_wq_bfed_ibp_wrsp_chnl_valid
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wrsp_chnl_valid
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_cmd_chnl_accept
                  ,cvted_bfed_lq_wq_bfed_ibp_cmd_chnl_accept
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_cmd_chnl_accept
                  ,cvted_bfed_core0_nllm_l2ifu_bfed_ibp_wd_chnl_accept
                  ,cvted_bfed_lq_wq_bfed_ibp_wd_chnl_accept
                  ,cvted_bfed_dmu_rbu_dmu_wbu_bfed_ibp_wd_chnl_accept
  }
  =
    {
    1'b1,
    cming_ibp_rd_chnl,
    cming_ibp_rd_chnl_valid,
    cming_ibp_wrsp_chnl,
    cming_ibp_wrsp_chnl_valid,
    cming_ibp_cmd_chnl_accept,
    cming_ibp_wd_chnl_accept
    } ;
// leda NTL_CON16 on





 wire [1-1:0] cmed_ibp_cmd_chnl_valid;
 wire [1-1:0] cmed_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] cmed_ibp_cmd_chnl;

 wire [1-1:0] cmed_ibp_wd_chnl_valid;
 wire [1-1:0] cmed_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] cmed_ibp_wd_chnl;

 wire [1-1:0] cmed_ibp_rd_chnl_accept;
 wire [1-1:0] cmed_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] cmed_ibp_rd_chnl;

 wire [1-1:0] cmed_ibp_wrsp_chnl_valid;
 wire [1-1:0] cmed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] cmed_ibp_wrsp_chnl;


// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: Some of ID signals are not used
wire [1-1:0] cmed_ibp_cmd_chnl_user;
wire [4-1:0] cmed_ibp_cmd_chnl_id;
wire [4-1:0] cmed_ibp_wd_chnl_id;
wire [4-1:0] cmed_ibp_rd_chnl_id;
wire [4-1:0] cmed_ibp_wrsp_chnl_id;
wire cmed_ibp_cmd_write_burst_en;
// leda NTL_CON13A on
// Compress all IBPs into one IBP
npuarc_biu_ibp_compr_id
  #(
    .COMP_NUM         (3),
    .COMP_FIFO_WIDTH  (4),
    .COMP_FIFO_DEPTH  (16),




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

    .USER_W           (1+1),
    .RGON_W           (1),
    .ID_WIDTH         (4)
    )
 u_cming_ibp_compr(
    .i_bus_ibp_uniq_id         (cming_ibp_uniq_id),
    .i_bus_ibp_cmd_chnl_user   (cming_ibp_cmd_chnl_wbursten_and_user),
    .i_bus_ibp_lockable        (cming_ibp_lockable),




    .i_bus_ibp_cmd_chnl_valid  (cming_ibp_cmd_chnl_valid),
    .i_bus_ibp_cmd_chnl_accept (cming_ibp_cmd_chnl_accept),
    .i_bus_ibp_cmd_chnl        (cming_ibp_cmd_chnl),

    .i_bus_ibp_rd_chnl_valid   (cming_ibp_rd_chnl_valid),
    .i_bus_ibp_rd_chnl_accept  (cming_ibp_rd_chnl_accept),
    .i_bus_ibp_rd_chnl         (cming_ibp_rd_chnl),

    .i_bus_ibp_wd_chnl_valid   (cming_ibp_wd_chnl_valid),
    .i_bus_ibp_wd_chnl_accept  (cming_ibp_wd_chnl_accept),
    .i_bus_ibp_wd_chnl         (cming_ibp_wd_chnl),

    .i_bus_ibp_wrsp_chnl_valid (cming_ibp_wrsp_chnl_valid),
    .i_bus_ibp_wrsp_chnl_accept(cming_ibp_wrsp_chnl_accept),
    .i_bus_ibp_wrsp_chnl       (cming_ibp_wrsp_chnl),




    .o_ibp_cmd_chnl_valid  (cmed_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (cmed_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (cmed_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (cmed_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (cmed_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (cmed_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (cmed_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (cmed_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (cmed_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (cmed_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(cmed_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (cmed_ibp_wrsp_chnl),

// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
    .o_ibp_cmd_chnl_id         (cmed_ibp_cmd_chnl_id),
    .o_ibp_cmd_chnl_user       ({cmed_ibp_cmd_write_burst_en,cmed_ibp_cmd_chnl_user}),
    .o_ibp_wd_chnl_id          (cmed_ibp_wd_chnl_id),
// spyglass enable_block UnloadedOutTerm-ML
    .o_ibp_rd_chnl_id          (cmed_ibp_rd_chnl_id),
    .o_ibp_wrsp_chnl_id        (cmed_ibp_wrsp_chnl_id),
    .rst_a                     (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                       (clk               )
);






 wire [1-1:0] bfed_cmed_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_cmed_ibp_cmd_chnl_accept;
 wire [57 * 1 -1:0] bfed_cmed_ibp_cmd_chnl;

 wire [1-1:0] bfed_cmed_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_cmed_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] bfed_cmed_ibp_wd_chnl;

 wire [1-1:0] bfed_cmed_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_cmed_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] bfed_cmed_ibp_rd_chnl;

 wire [1-1:0] bfed_cmed_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_cmed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_cmed_ibp_wrsp_chnl;

wire [1-1:0] bfed_cmed_ibp_cmd_chnl_user;
wire [4-1:0] bfed_cmed_ibp_cmd_chnl_id;
wire [4-1:0] bfed_cmed_ibp_wd_chnl_id;
wire [4-1:0] bfed_cmed_ibp_rd_chnl_id;
wire [4-1:0] bfed_cmed_ibp_wrsp_chnl_id;
wire bfed_cmed_ibp_cmd_write_burst_en;

  assign bfed_cmed_ibp_cmd_chnl_valid     = cmed_ibp_cmd_chnl_valid  ;
  assign cmed_ibp_cmd_chnl_accept    = bfed_cmed_ibp_cmd_chnl_accept ;
  assign bfed_cmed_ibp_cmd_chnl           = cmed_ibp_cmd_chnl        ;

  assign bfed_cmed_ibp_wd_chnl_valid      = cmed_ibp_wd_chnl_valid   ;
  assign cmed_ibp_wd_chnl_accept     = bfed_cmed_ibp_wd_chnl_accept  ;
  assign bfed_cmed_ibp_wd_chnl            = cmed_ibp_wd_chnl         ;

  assign bfed_cmed_ibp_rd_chnl_accept     = cmed_ibp_rd_chnl_accept  ;
  assign cmed_ibp_rd_chnl_valid      = bfed_cmed_ibp_rd_chnl_valid   ;
  assign cmed_ibp_rd_chnl            = bfed_cmed_ibp_rd_chnl         ;

  assign bfed_cmed_ibp_wrsp_chnl_accept   = cmed_ibp_wrsp_chnl_accept;
  assign cmed_ibp_wrsp_chnl_valid    = bfed_cmed_ibp_wrsp_chnl_valid ;
  assign cmed_ibp_wrsp_chnl          = bfed_cmed_ibp_wrsp_chnl       ;

  assign bfed_cmed_ibp_cmd_chnl_user      = cmed_ibp_cmd_chnl_user;
  assign bfed_cmed_ibp_cmd_write_burst_en   = cmed_ibp_cmd_write_burst_en;

  assign bfed_cmed_ibp_cmd_chnl_id   = cmed_ibp_cmd_chnl_id  ;
  assign bfed_cmed_ibp_wd_chnl_id    = cmed_ibp_wd_chnl_id   ;
  assign cmed_ibp_rd_chnl_id         = bfed_cmed_ibp_rd_chnl_id   ;
  assign cmed_ibp_wrsp_chnl_id       = bfed_cmed_ibp_wrsp_chnl_id ;



  wire                                  cbu_ibp_cmd_valid;
  wire                                  cbu_ibp_cmd_accept;
  wire                                  cbu_ibp_cmd_read;
  wire  [40                -1:0]       cbu_ibp_cmd_addr;
  wire                                  cbu_ibp_cmd_wrap;
  wire  [3-1:0]       cbu_ibp_cmd_data_size;
  wire  [4-1:0]       cbu_ibp_cmd_burst_size;
  wire  [2-1:0]       cbu_ibp_cmd_prot;
  wire  [4-1:0]       cbu_ibp_cmd_cache;
  wire                                  cbu_ibp_cmd_lock;
  wire                                  cbu_ibp_cmd_excl;

  wire                                  cbu_ibp_rd_valid;
  wire                                  cbu_ibp_rd_excl_ok;
  wire                                  cbu_ibp_rd_accept;
  wire                                  cbu_ibp_err_rd;
  wire  [64               -1:0]        cbu_ibp_rd_data;
  wire                                  cbu_ibp_rd_last;

  wire                                  cbu_ibp_wr_valid;
  wire                                  cbu_ibp_wr_accept;
  wire  [64               -1:0]        cbu_ibp_wr_data;
  wire  [8  -1:0]                    cbu_ibp_wr_mask;
  wire                                  cbu_ibp_wr_last;

  wire                                  cbu_ibp_wr_done;
  wire                                  cbu_ibp_wr_excl_done;
  wire                                  cbu_ibp_err_wr;
  wire                                  cbu_ibp_wr_resp_accept;


// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: Only AXI configuration use this user bit
wire [1-1:0] bfed_cmed_ibp_cmd_user;
// leda NTL_CON13A on
// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_bfed_cmed_pack2ibp_o_ibp_cmd_rgon;
// spyglass enable_block W240
// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_pack2ibp
  #(
    .ADDR_W                  (40),
    .DATA_W                  (64),



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
    .USER_W                  (1),
    .RGON_W                  (1)

    )
u_bfed_cmed_pack2ibp
  (
    .ibp_cmd_chnl_rgon         (1'b1),
    .ibp_cmd_chnl_user         (bfed_cmed_ibp_cmd_chnl_user),
    .ibp_cmd_user              (bfed_cmed_ibp_cmd_user),




    .ibp_cmd_chnl_valid  (bfed_cmed_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (bfed_cmed_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (bfed_cmed_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (bfed_cmed_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (bfed_cmed_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (bfed_cmed_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (bfed_cmed_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (bfed_cmed_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (bfed_cmed_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (bfed_cmed_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(bfed_cmed_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (bfed_cmed_ibp_wrsp_chnl),


  .ibp_cmd_valid             (cbu_ibp_cmd_valid),
  .ibp_cmd_accept            (cbu_ibp_cmd_accept),
  .ibp_cmd_read              (cbu_ibp_cmd_read),
  .ibp_cmd_addr              (cbu_ibp_cmd_addr),
  .ibp_cmd_wrap              (cbu_ibp_cmd_wrap),
  .ibp_cmd_data_size         (cbu_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (cbu_ibp_cmd_burst_size),
  .ibp_cmd_prot              (cbu_ibp_cmd_prot),
  .ibp_cmd_cache             (cbu_ibp_cmd_cache),
  .ibp_cmd_lock              (cbu_ibp_cmd_lock),
  .ibp_cmd_excl              (cbu_ibp_cmd_excl),

  .ibp_rd_valid              (cbu_ibp_rd_valid),
  .ibp_rd_excl_ok            (cbu_ibp_rd_excl_ok),
  .ibp_rd_accept             (cbu_ibp_rd_accept),
  .ibp_err_rd                (cbu_ibp_err_rd),
  .ibp_rd_data               (cbu_ibp_rd_data),
  .ibp_rd_last               (cbu_ibp_rd_last),

  .ibp_wr_valid              (cbu_ibp_wr_valid),
  .ibp_wr_accept             (cbu_ibp_wr_accept),
  .ibp_wr_data               (cbu_ibp_wr_data),
  .ibp_wr_mask               (cbu_ibp_wr_mask),
  .ibp_wr_last               (cbu_ibp_wr_last),

  .ibp_wr_done               (cbu_ibp_wr_done),
  .ibp_wr_excl_done          (cbu_ibp_wr_excl_done),
  .ibp_err_wr                (cbu_ibp_err_wr),
  .ibp_wr_resp_accept        (cbu_ibp_wr_resp_accept),

// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
    .ibp_cmd_rgon              (unused_bfed_cmed_pack2ibp_o_ibp_cmd_rgon)
// spyglass enable_block UnloadedOutTerm-ML
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on



// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_bfed_cmed_ibp2axi_axi_aruser;
wire unused_bfed_cmed_ibp2axi_axi_awuser;
wire unused_bfed_cmed_ibp2axi_ahb_hexcl;
wire unused_bfed_cmed_ibp2axi_bvci_excl;
// spyglass enable_block W240

npuarc_biu_ibp2axi
  #(
    .ID_W  (4),
    .USER_W  (1),
    .OUT_CMD_NUM  (16),
    .OUT_CMD_CNT_W(4),


    .CHNL_FIFO_DEPTH (2),
    .ADDR_W(40),
    .DATA_W(64)
    )
  u_bfed_cmed_ibp2axi (

  .ibp_cmd_valid             (cbu_ibp_cmd_valid),
  .ibp_cmd_accept            (cbu_ibp_cmd_accept),
  .ibp_cmd_read              (cbu_ibp_cmd_read),
  .ibp_cmd_addr              (cbu_ibp_cmd_addr),
  .ibp_cmd_wrap              (cbu_ibp_cmd_wrap),
  .ibp_cmd_data_size         (cbu_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (cbu_ibp_cmd_burst_size),
  .ibp_cmd_prot              (cbu_ibp_cmd_prot),
  .ibp_cmd_cache             (cbu_ibp_cmd_cache),
  .ibp_cmd_lock              (cbu_ibp_cmd_lock),
  .ibp_cmd_excl              (cbu_ibp_cmd_excl),

  .ibp_rd_valid              (cbu_ibp_rd_valid),
  .ibp_rd_excl_ok            (cbu_ibp_rd_excl_ok),
  .ibp_rd_accept             (cbu_ibp_rd_accept),
  .ibp_err_rd                (cbu_ibp_err_rd),
  .ibp_rd_data               (cbu_ibp_rd_data),
  .ibp_rd_last               (cbu_ibp_rd_last),

  .ibp_wr_valid              (cbu_ibp_wr_valid),
  .ibp_wr_accept             (cbu_ibp_wr_accept),
  .ibp_wr_data               (cbu_ibp_wr_data),
  .ibp_wr_mask               (cbu_ibp_wr_mask),
  .ibp_wr_last               (cbu_ibp_wr_last),

  .ibp_wr_done               (cbu_ibp_wr_done),
  .ibp_wr_excl_done          (cbu_ibp_wr_excl_done),
  .ibp_err_wr                (cbu_ibp_err_wr),
  .ibp_wr_resp_accept        (cbu_ibp_wr_resp_accept),

    .ibp_cmd_user              (bfed_cmed_ibp_cmd_user ),
    .ibp_cmd_chnl_id           (bfed_cmed_ibp_cmd_chnl_id ),
    .ibp_rd_chnl_id            (bfed_cmed_ibp_rd_chnl_id  ),
    .ibp_wd_chnl_id            (bfed_cmed_ibp_wd_chnl_id  ),
    .ibp_wrsp_chnl_id          (bfed_cmed_ibp_wrsp_chnl_id),


// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
//// The AXI bus

  .axi_arvalid    (cbu_axi_arvalid),
  .axi_arready    (cbu_axi_arready),
  .axi_arid       (cbu_axi_arid   ),
  .axi_araddr     (cbu_axi_araddr ),
  .axi_arburst    (cbu_axi_arburst),
  .axi_arlen      (cbu_axi_arlen  ),
  .axi_arsize     (cbu_axi_arsize ),
  .axi_arcache    (cbu_axi_arcache),
  .axi_arprot     (cbu_axi_arprot ),
  .axi_arlock     (cbu_axi_arlock ),

  .axi_rvalid     (cbu_axi_rvalid),
  .axi_rready     (cbu_axi_rready),
  .axi_rid        (cbu_axi_rid   ),
  .axi_rdata      (cbu_axi_rdata ),
  .axi_rresp      (cbu_axi_rresp ),
  .axi_rlast      (cbu_axi_rlast ),

  .axi_awvalid    (cbu_axi_awvalid),
  .axi_awready    (cbu_axi_awready),
  .axi_awid       (cbu_axi_awid   ),
  .axi_awaddr     (cbu_axi_awaddr ),
  .axi_awburst    (cbu_axi_awburst),
  .axi_awlen      (cbu_axi_awlen  ),
  .axi_awsize     (cbu_axi_awsize ),
  .axi_awcache    (cbu_axi_awcache),
  .axi_awprot     (cbu_axi_awprot ),
  .axi_awlock     (cbu_axi_awlock ),

  .axi_wid         (cbu_axi_wid   ),
  .axi_wvalid      (cbu_axi_wvalid),
  .axi_wready      (cbu_axi_wready),
  .axi_wdata       (cbu_axi_wdata ),
  .axi_wstrb       (cbu_axi_wstrb ),
  .axi_wlast       (cbu_axi_wlast ),

  .axi_bvalid   (cbu_axi_bvalid),
  .axi_bready   (cbu_axi_bready),
  .axi_bid      (cbu_axi_bid   ),
  .axi_bresp    (cbu_axi_bresp ),

    .axi_aruser(unused_bfed_cmed_ibp2axi_axi_aruser),
    .axi_awuser(unused_bfed_cmed_ibp2axi_axi_awuser),


// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b


    .bus_clk_en          (mbus_clk_en        ),
    .rst_a               (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                 (clk               )
);




// spyglass enable_block W528
// leda G_521_2_B on

endmodule // biu_cbu_mst


