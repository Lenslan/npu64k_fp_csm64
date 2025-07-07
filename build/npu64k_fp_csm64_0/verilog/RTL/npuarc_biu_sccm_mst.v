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
//  Verilog module of biu_sccm master port
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"

// Set simulation timescale
//
`include "const.def"



module npuarc_biu_sccm_mst
// leda G_521_2_B off
// LMD: Use lowercase letters for all signal reg, net and port names
// LJ: Pfx may include the uppercase, so disable the lint checking rule
  (







  input                                   sccm_dmiibp_slv_ibp_cmd_valid,
  output                                  sccm_dmiibp_slv_ibp_cmd_accept,
  input                                   sccm_dmiibp_slv_ibp_cmd_read,
  input   [24                -1:0]       sccm_dmiibp_slv_ibp_cmd_addr,
  input                                   sccm_dmiibp_slv_ibp_cmd_wrap,
  input   [3-1:0]       sccm_dmiibp_slv_ibp_cmd_data_size,
  input   [4-1:0]       sccm_dmiibp_slv_ibp_cmd_burst_size,
  input   [2-1:0]       sccm_dmiibp_slv_ibp_cmd_prot,
  input   [4-1:0]       sccm_dmiibp_slv_ibp_cmd_cache,
  input                                   sccm_dmiibp_slv_ibp_cmd_lock,
  input                                   sccm_dmiibp_slv_ibp_cmd_excl,

  output                                  sccm_dmiibp_slv_ibp_rd_valid,
  output                                  sccm_dmiibp_slv_ibp_rd_excl_ok,
  input                                   sccm_dmiibp_slv_ibp_rd_accept,
  output                                  sccm_dmiibp_slv_ibp_err_rd,
  output  [64               -1:0]        sccm_dmiibp_slv_ibp_rd_data,
  output                                  sccm_dmiibp_slv_ibp_rd_last,

  input                                   sccm_dmiibp_slv_ibp_wr_valid,
  output                                  sccm_dmiibp_slv_ibp_wr_accept,
  input   [64               -1:0]        sccm_dmiibp_slv_ibp_wr_data,
  input   [8  -1:0]                    sccm_dmiibp_slv_ibp_wr_mask,
  input                                   sccm_dmiibp_slv_ibp_wr_last,

  output                                  sccm_dmiibp_slv_ibp_wr_done,
  output                                  sccm_dmiibp_slv_ibp_wr_excl_done,
  output                                  sccm_dmiibp_slv_ibp_err_wr,
  input                                   sccm_dmiibp_slv_ibp_wr_resp_accept,
             input  [2 -1:0]      sccm_dmiibp_slv_ibp_cmd_user,




 output [1-1:0] sccm_mst_ibp_cmd_chnl_valid,
 input  [1-1:0] sccm_mst_ibp_cmd_chnl_accept,
 output [41 * 1 -1:0] sccm_mst_ibp_cmd_chnl,

 output [1-1:0] sccm_mst_ibp_wd_chnl_valid,
 input  [1-1:0] sccm_mst_ibp_wd_chnl_accept,
 output [73 * 1 -1:0] sccm_mst_ibp_wd_chnl,

 output [1-1:0] sccm_mst_ibp_rd_chnl_accept,
 input  [1-1:0] sccm_mst_ibp_rd_chnl_valid,
 input  [67 * 1 -1:0] sccm_mst_ibp_rd_chnl,

 input  [1-1:0] sccm_mst_ibp_wrsp_chnl_valid,
 output [1-1:0] sccm_mst_ibp_wrsp_chnl_accept,
 input  [3 * 1 -1:0] sccm_mst_ibp_wrsp_chnl,

             output  [2 -1:0]      sccm_mst_ibp_cmd_chnl_user,
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




 wire [1-1:0] sccm_dmiibp_slv_ibp_cmd_chnl_valid;
 wire [1-1:0] sccm_dmiibp_slv_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] sccm_dmiibp_slv_ibp_cmd_chnl;

 wire [1-1:0] sccm_dmiibp_slv_ibp_wd_chnl_valid;
 wire [1-1:0] sccm_dmiibp_slv_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] sccm_dmiibp_slv_ibp_wd_chnl;

 wire [1-1:0] sccm_dmiibp_slv_ibp_rd_chnl_accept;
 wire [1-1:0] sccm_dmiibp_slv_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] sccm_dmiibp_slv_ibp_rd_chnl;

 wire [1-1:0] sccm_dmiibp_slv_ibp_wrsp_chnl_valid;
 wire [1-1:0] sccm_dmiibp_slv_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] sccm_dmiibp_slv_ibp_wrsp_chnl;



    wire [2-1:0] sccm_dmiibp_slv_ibp_cmd_chnl_user;

// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_sccm_dmiibp_slv_ibp_cmd_chnl_rgon;
// spyglass enable_block W240
// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_ibp2pack
  #(
    .ADDR_W (24),
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
    .CMD_CHNL_ADDR_W         (24),
    .CMD_CHNL_W              (41),

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
    .USER_W(2),
    .RGON_W(1)
    )
u_sccm_dmiibp_slv_ibp2pack
  (
    .rst_a                     (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                       (clk               ) ,

  .ibp_cmd_valid             (sccm_dmiibp_slv_ibp_cmd_valid),
  .ibp_cmd_accept            (sccm_dmiibp_slv_ibp_cmd_accept),
  .ibp_cmd_read              (sccm_dmiibp_slv_ibp_cmd_read),
  .ibp_cmd_addr              (sccm_dmiibp_slv_ibp_cmd_addr),
  .ibp_cmd_wrap              (sccm_dmiibp_slv_ibp_cmd_wrap),
  .ibp_cmd_data_size         (sccm_dmiibp_slv_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (sccm_dmiibp_slv_ibp_cmd_burst_size),
  .ibp_cmd_prot              (sccm_dmiibp_slv_ibp_cmd_prot),
  .ibp_cmd_cache             (sccm_dmiibp_slv_ibp_cmd_cache),
  .ibp_cmd_lock              (sccm_dmiibp_slv_ibp_cmd_lock),
  .ibp_cmd_excl              (sccm_dmiibp_slv_ibp_cmd_excl),

  .ibp_rd_valid              (sccm_dmiibp_slv_ibp_rd_valid),
  .ibp_rd_excl_ok            (sccm_dmiibp_slv_ibp_rd_excl_ok),
  .ibp_rd_accept             (sccm_dmiibp_slv_ibp_rd_accept),
  .ibp_err_rd                (sccm_dmiibp_slv_ibp_err_rd),
  .ibp_rd_data               (sccm_dmiibp_slv_ibp_rd_data),
  .ibp_rd_last               (sccm_dmiibp_slv_ibp_rd_last),

  .ibp_wr_valid              (sccm_dmiibp_slv_ibp_wr_valid),
  .ibp_wr_accept             (sccm_dmiibp_slv_ibp_wr_accept),
  .ibp_wr_data               (sccm_dmiibp_slv_ibp_wr_data),
  .ibp_wr_mask               (sccm_dmiibp_slv_ibp_wr_mask),
  .ibp_wr_last               (sccm_dmiibp_slv_ibp_wr_last),

  .ibp_wr_done               (sccm_dmiibp_slv_ibp_wr_done),
  .ibp_wr_excl_done          (sccm_dmiibp_slv_ibp_wr_excl_done),
  .ibp_err_wr                (sccm_dmiibp_slv_ibp_err_wr),
  .ibp_wr_resp_accept        (sccm_dmiibp_slv_ibp_wr_resp_accept),

    .ibp_cmd_rgon              (1'b1),
    .ibp_cmd_user              (sccm_dmiibp_slv_ibp_cmd_user),




    .ibp_cmd_chnl_valid  (sccm_dmiibp_slv_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (sccm_dmiibp_slv_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (sccm_dmiibp_slv_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (sccm_dmiibp_slv_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (sccm_dmiibp_slv_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (sccm_dmiibp_slv_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (sccm_dmiibp_slv_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (sccm_dmiibp_slv_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (sccm_dmiibp_slv_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (sccm_dmiibp_slv_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(sccm_dmiibp_slv_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (sccm_dmiibp_slv_ibp_wrsp_chnl),


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
    .ibp_cmd_chnl_rgon         (unused_sccm_dmiibp_slv_ibp_cmd_chnl_rgon),
// spyglass enable_block UnloadedOutTerm-ML
    .ibp_cmd_chnl_user         (sccm_dmiibp_slv_ibp_cmd_chnl_user)
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on






 wire [1-1:0] sccm_dmiibp_slv_bfed_ibp_cmd_chnl_valid;
 wire [1-1:0] sccm_dmiibp_slv_bfed_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] sccm_dmiibp_slv_bfed_ibp_cmd_chnl;

 wire [1-1:0] sccm_dmiibp_slv_bfed_ibp_wd_chnl_valid;
 wire [1-1:0] sccm_dmiibp_slv_bfed_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] sccm_dmiibp_slv_bfed_ibp_wd_chnl;

 wire [1-1:0] sccm_dmiibp_slv_bfed_ibp_rd_chnl_accept;
 wire [1-1:0] sccm_dmiibp_slv_bfed_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] sccm_dmiibp_slv_bfed_ibp_rd_chnl;

 wire [1-1:0] sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_valid;
 wire [1-1:0] sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] sccm_dmiibp_slv_bfed_ibp_wrsp_chnl;

wire [2-1:0] sccm_dmiibp_slv_bfed_ibp_cmd_chnl_user;


  assign sccm_dmiibp_slv_bfed_ibp_cmd_chnl_valid     = sccm_dmiibp_slv_ibp_cmd_chnl_valid  ;
  assign sccm_dmiibp_slv_ibp_cmd_chnl_accept    = sccm_dmiibp_slv_bfed_ibp_cmd_chnl_accept ;
  assign sccm_dmiibp_slv_bfed_ibp_cmd_chnl           = sccm_dmiibp_slv_ibp_cmd_chnl        ;

  assign sccm_dmiibp_slv_bfed_ibp_wd_chnl_valid      = sccm_dmiibp_slv_ibp_wd_chnl_valid   ;
  assign sccm_dmiibp_slv_ibp_wd_chnl_accept     = sccm_dmiibp_slv_bfed_ibp_wd_chnl_accept  ;
  assign sccm_dmiibp_slv_bfed_ibp_wd_chnl            = sccm_dmiibp_slv_ibp_wd_chnl         ;

  assign sccm_dmiibp_slv_bfed_ibp_rd_chnl_accept     = sccm_dmiibp_slv_ibp_rd_chnl_accept  ;
  assign sccm_dmiibp_slv_ibp_rd_chnl_valid      = sccm_dmiibp_slv_bfed_ibp_rd_chnl_valid   ;
  assign sccm_dmiibp_slv_ibp_rd_chnl            = sccm_dmiibp_slv_bfed_ibp_rd_chnl         ;

  assign sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_accept   = sccm_dmiibp_slv_ibp_wrsp_chnl_accept;
  assign sccm_dmiibp_slv_ibp_wrsp_chnl_valid    = sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_valid ;
  assign sccm_dmiibp_slv_ibp_wrsp_chnl          = sccm_dmiibp_slv_bfed_ibp_wrsp_chnl       ;

  assign sccm_dmiibp_slv_bfed_ibp_cmd_chnl_user      = sccm_dmiibp_slv_ibp_cmd_chnl_user;


// Covert the sccm_dmiibp_slv_bfed_ IBP width



 wire [1-1:0] cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_valid;
 wire [1-1:0] cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl;

 wire [1-1:0] cvted_sccm_dmiibp_slv_bfed_ibp_wd_chnl_valid;
 wire [1-1:0] cvted_sccm_dmiibp_slv_bfed_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] cvted_sccm_dmiibp_slv_bfed_ibp_wd_chnl;

 wire [1-1:0] cvted_sccm_dmiibp_slv_bfed_ibp_rd_chnl_accept;
 wire [1-1:0] cvted_sccm_dmiibp_slv_bfed_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] cvted_sccm_dmiibp_slv_bfed_ibp_rd_chnl;

 wire [1-1:0] cvted_sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_valid;
 wire [1-1:0] cvted_sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] cvted_sccm_dmiibp_slv_bfed_ibp_wrsp_chnl;

wire [2-1:0] cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_user;

// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_sccm_dmiibp_slv_bfed_ibpx2ibpy_o_ibp_cmd_chnl_rgon;
// spyglass enable_block W240
npuarc_biu_ibpx2ibpy
  #(
     .N2W_SUPPORT_NARROW_TRANS (0),
    .W2N_SUPPORT_BURST_TRANS  (1),

    .BYPBUF_WD_CHNL (0),
    .SPLT_FIFO_DEPTH (10),
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
    .X_CMD_CHNL_ADDR_W         (24),
    .X_CMD_CHNL_W              (41),

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
    .Y_CMD_CHNL_ADDR_W         (24),
    .Y_CMD_CHNL_W              (41),

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
    .X_USER_W  (2),
    .Y_USER_W  (2),
    .X_RGON_W  (1),
    .Y_RGON_W  (1)
    )
 u_sccm_dmiibp_slv_bfed_ibp64toibp64 (
    .i_ibp_cmd_chnl_rgon   (1'b1),



    .i_ibp_cmd_chnl_valid  (sccm_dmiibp_slv_bfed_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (sccm_dmiibp_slv_bfed_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (sccm_dmiibp_slv_bfed_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (sccm_dmiibp_slv_bfed_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (sccm_dmiibp_slv_bfed_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (sccm_dmiibp_slv_bfed_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (sccm_dmiibp_slv_bfed_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (sccm_dmiibp_slv_bfed_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (sccm_dmiibp_slv_bfed_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (sccm_dmiibp_slv_bfed_ibp_wrsp_chnl),

    .i_ibp_cmd_chnl_user   (sccm_dmiibp_slv_bfed_ibp_cmd_chnl_user),





    .o_ibp_cmd_chnl_valid  (cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (cvted_sccm_dmiibp_slv_bfed_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (cvted_sccm_dmiibp_slv_bfed_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (cvted_sccm_dmiibp_slv_bfed_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (cvted_sccm_dmiibp_slv_bfed_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (cvted_sccm_dmiibp_slv_bfed_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (cvted_sccm_dmiibp_slv_bfed_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (cvted_sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(cvted_sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (cvted_sccm_dmiibp_slv_bfed_ibp_wrsp_chnl),


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
    .o_ibp_cmd_chnl_rgon   (unused_sccm_dmiibp_slv_bfed_ibpx2ibpy_o_ibp_cmd_chnl_rgon),
// spyglass enable_block UnloadedOutTerm-ML
    .o_ibp_cmd_chnl_user   (cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_user),
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

    .rst_a               (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                 (clk               )
);


wire sccm_dmiibp_slv_bfed_ibp_cmd_write_burst_en = 0;
wire [2+1-1:0] cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_wbursten_and_user =
         {sccm_dmiibp_slv_bfed_ibp_cmd_write_burst_en, cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_user};












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
wire [1*1 -1:0] cming_ibp_uniq_id;
wire [(2+1)*1 -1:0] cming_ibp_cmd_chnl_wbursten_and_user;
wire [1 -1:0] cming_ibp_lockable;
// leda NTL_CON13A on



 wire [1-1:0] cming_ibp_cmd_chnl_valid;
 wire [1-1:0] cming_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] cming_ibp_cmd_chnl;

 wire [1-1:0] cming_ibp_wd_chnl_valid;
 wire [1-1:0] cming_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] cming_ibp_wd_chnl;

 wire [1-1:0] cming_ibp_rd_chnl_accept;
 wire [1-1:0] cming_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] cming_ibp_rd_chnl;

 wire [1-1:0] cming_ibp_wrsp_chnl_valid;
 wire [1-1:0] cming_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] cming_ibp_wrsp_chnl;







wire sccm_dmiibp_slv_bfed_ibp_lockable = 0;

// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0 / logic 1
// LJ: No care about the constant here
assign {cming_ibp_lockable_dummy,
        cming_ibp_lockable}
        = {
            1'b0
                  ,sccm_dmiibp_slv_bfed_ibp_lockable
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
              ,1'd0
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_wbursten_and_user
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_valid
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_wd_chnl
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_wd_chnl_valid
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_rd_chnl_accept
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_accept
  };
// leda NTL_CON16 on

// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0 / logic 1
// LJ: No care about the constant here
assign
  {
    cming_dummy1
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_rd_chnl
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_rd_chnl_valid
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_wrsp_chnl
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_wrsp_chnl_valid
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_cmd_chnl_accept
                  ,cvted_sccm_dmiibp_slv_bfed_ibp_wd_chnl_accept
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
 wire [41 * 1 -1:0] cmed_ibp_cmd_chnl;

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
wire [2-1:0] cmed_ibp_cmd_chnl_user;
wire [1-1:0] cmed_ibp_cmd_chnl_id;
wire [1-1:0] cmed_ibp_wd_chnl_id;
wire cmed_ibp_cmd_write_burst_en;
// leda NTL_CON13A on
// Compress all IBPs into one IBP
npuarc_biu_ibp_compr
  #(
    .COMP_NUM         (1),
    .COMP_FIFO_WIDTH  (1),
    .COMP_FIFO_DEPTH  (10),




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
    .CMD_CHNL_ADDR_W         (24),
    .CMD_CHNL_W              (41),

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

    .USER_W           (2+1),
    .RGON_W           (1),
    .ID_WIDTH         (1)
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
    .rst_a                     (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                       (clk               )
);




 wire [1-1:0] bfed_cmed_ibp_cmd_chnl_valid;
 wire [1-1:0] bfed_cmed_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] bfed_cmed_ibp_cmd_chnl;

 wire [1-1:0] bfed_cmed_ibp_wd_chnl_valid;
 wire [1-1:0] bfed_cmed_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] bfed_cmed_ibp_wd_chnl;

 wire [1-1:0] bfed_cmed_ibp_rd_chnl_accept;
 wire [1-1:0] bfed_cmed_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] bfed_cmed_ibp_rd_chnl;

 wire [1-1:0] bfed_cmed_ibp_wrsp_chnl_valid;
 wire [1-1:0] bfed_cmed_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] bfed_cmed_ibp_wrsp_chnl;

wire [2-1:0] bfed_cmed_ibp_cmd_chnl_user;


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




  wire                                  sccm_mst_ibp_cmd_valid;
  wire                                  sccm_mst_ibp_cmd_accept;
  wire                                  sccm_mst_ibp_cmd_read;
  wire  [24                -1:0]       sccm_mst_ibp_cmd_addr;
  wire                                  sccm_mst_ibp_cmd_wrap;
  wire  [3-1:0]       sccm_mst_ibp_cmd_data_size;
  wire  [4-1:0]       sccm_mst_ibp_cmd_burst_size;
  wire  [2-1:0]       sccm_mst_ibp_cmd_prot;
  wire  [4-1:0]       sccm_mst_ibp_cmd_cache;
  wire                                  sccm_mst_ibp_cmd_lock;
  wire                                  sccm_mst_ibp_cmd_excl;

  wire                                  sccm_mst_ibp_rd_valid;
  wire                                  sccm_mst_ibp_rd_excl_ok;
  wire                                  sccm_mst_ibp_rd_accept;
  wire                                  sccm_mst_ibp_err_rd;
  wire  [64               -1:0]        sccm_mst_ibp_rd_data;
  wire                                  sccm_mst_ibp_rd_last;

  wire                                  sccm_mst_ibp_wr_valid;
  wire                                  sccm_mst_ibp_wr_accept;
  wire  [64               -1:0]        sccm_mst_ibp_wr_data;
  wire  [8  -1:0]                    sccm_mst_ibp_wr_mask;
  wire                                  sccm_mst_ibp_wr_last;

  wire                                  sccm_mst_ibp_wr_done;
  wire                                  sccm_mst_ibp_wr_excl_done;
  wire                                  sccm_mst_ibp_err_wr;
  wire                                  sccm_mst_ibp_wr_resp_accept;

    wire [2-1:0] sccm_mst_ibp_cmd_user;
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
    .ADDR_W                  (24),
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
    .CMD_CHNL_ADDR_W         (24),
    .CMD_CHNL_W              (41),

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
    .USER_W                  (2),
    .RGON_W                  (1)

    )
u_bfed_cmed_pack2ibp
  (
    .ibp_cmd_chnl_rgon   (1'b1),
    .ibp_cmd_chnl_user   (bfed_cmed_ibp_cmd_chnl_user),



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



  .ibp_cmd_valid             (sccm_mst_ibp_cmd_valid),
  .ibp_cmd_accept            (sccm_mst_ibp_cmd_accept),
  .ibp_cmd_read              (sccm_mst_ibp_cmd_read),
  .ibp_cmd_addr              (sccm_mst_ibp_cmd_addr),
  .ibp_cmd_wrap              (sccm_mst_ibp_cmd_wrap),
  .ibp_cmd_data_size         (sccm_mst_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (sccm_mst_ibp_cmd_burst_size),
  .ibp_cmd_prot              (sccm_mst_ibp_cmd_prot),
  .ibp_cmd_cache             (sccm_mst_ibp_cmd_cache),
  .ibp_cmd_lock              (sccm_mst_ibp_cmd_lock),
  .ibp_cmd_excl              (sccm_mst_ibp_cmd_excl),

  .ibp_rd_valid              (sccm_mst_ibp_rd_valid),
  .ibp_rd_excl_ok            (sccm_mst_ibp_rd_excl_ok),
  .ibp_rd_accept             (sccm_mst_ibp_rd_accept),
  .ibp_err_rd                (sccm_mst_ibp_err_rd),
  .ibp_rd_data               (sccm_mst_ibp_rd_data),
  .ibp_rd_last               (sccm_mst_ibp_rd_last),

  .ibp_wr_valid              (sccm_mst_ibp_wr_valid),
  .ibp_wr_accept             (sccm_mst_ibp_wr_accept),
  .ibp_wr_data               (sccm_mst_ibp_wr_data),
  .ibp_wr_mask               (sccm_mst_ibp_wr_mask),
  .ibp_wr_last               (sccm_mst_ibp_wr_last),

  .ibp_wr_done               (sccm_mst_ibp_wr_done),
  .ibp_wr_excl_done          (sccm_mst_ibp_wr_excl_done),
  .ibp_err_wr                (sccm_mst_ibp_err_wr),
  .ibp_wr_resp_accept        (sccm_mst_ibp_wr_resp_accept),

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
    .ibp_cmd_rgon   (unused_bfed_cmed_pack2ibp_o_ibp_cmd_rgon),
    .ibp_cmd_user   (sccm_mst_ibp_cmd_user)
// spyglass enable_block UnloadedOutTerm-ML
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );
// leda NTL_CON10 on
// leda NTL_CON10B on

// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_sccm_mst_ibp2pack_o_ibp_cmd_rgon;
// spyglass enable_block W240
npuarc_biu_ibp2pack
  #(
    .ADDR_W                  (24),
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
    .CMD_CHNL_ADDR_W         (24),
    .CMD_CHNL_W              (41),

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
    .USER_W                  (2),
    .RGON_W                  (1)
    )
u_sccm_mst_ibp2pack
  (
    .rst_a                     (rst_a),
    .nmi_restart_r             (nmi_restart_r),
    .clk                       (clk               ) ,

  .ibp_cmd_valid             (sccm_mst_ibp_cmd_valid),
  .ibp_cmd_accept            (sccm_mst_ibp_cmd_accept),
  .ibp_cmd_read              (sccm_mst_ibp_cmd_read),
  .ibp_cmd_addr              (sccm_mst_ibp_cmd_addr),
  .ibp_cmd_wrap              (sccm_mst_ibp_cmd_wrap),
  .ibp_cmd_data_size         (sccm_mst_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (sccm_mst_ibp_cmd_burst_size),
  .ibp_cmd_prot              (sccm_mst_ibp_cmd_prot),
  .ibp_cmd_cache             (sccm_mst_ibp_cmd_cache),
  .ibp_cmd_lock              (sccm_mst_ibp_cmd_lock),
  .ibp_cmd_excl              (sccm_mst_ibp_cmd_excl),

  .ibp_rd_valid              (sccm_mst_ibp_rd_valid),
  .ibp_rd_excl_ok            (sccm_mst_ibp_rd_excl_ok),
  .ibp_rd_accept             (sccm_mst_ibp_rd_accept),
  .ibp_err_rd                (sccm_mst_ibp_err_rd),
  .ibp_rd_data               (sccm_mst_ibp_rd_data),
  .ibp_rd_last               (sccm_mst_ibp_rd_last),

  .ibp_wr_valid              (sccm_mst_ibp_wr_valid),
  .ibp_wr_accept             (sccm_mst_ibp_wr_accept),
  .ibp_wr_data               (sccm_mst_ibp_wr_data),
  .ibp_wr_mask               (sccm_mst_ibp_wr_mask),
  .ibp_wr_last               (sccm_mst_ibp_wr_last),

  .ibp_wr_done               (sccm_mst_ibp_wr_done),
  .ibp_wr_excl_done          (sccm_mst_ibp_wr_excl_done),
  .ibp_err_wr                (sccm_mst_ibp_err_wr),
  .ibp_wr_resp_accept        (sccm_mst_ibp_wr_resp_accept),

    .ibp_cmd_rgon   (1'b1),
    .ibp_cmd_user   (sccm_mst_ibp_cmd_user),




    .ibp_cmd_chnl_valid  (sccm_mst_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (sccm_mst_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (sccm_mst_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (sccm_mst_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (sccm_mst_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (sccm_mst_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (sccm_mst_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (sccm_mst_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (sccm_mst_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (sccm_mst_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(sccm_mst_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (sccm_mst_ibp_wrsp_chnl),


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
    .ibp_cmd_chnl_rgon         (unused_sccm_mst_ibp2pack_o_ibp_cmd_rgon),
// spyglass enable_block UnloadedOutTerm-ML
    .ibp_cmd_chnl_user         (sccm_mst_ibp_cmd_chnl_user)
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

   );







// spyglass enable_block W528
// leda G_521_2_B on

endmodule // biu_sccm_mst


