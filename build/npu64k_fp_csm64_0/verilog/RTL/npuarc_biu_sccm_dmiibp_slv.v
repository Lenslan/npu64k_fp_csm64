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
//  Verilog module of biu_sccm_dmiibp slave port
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"

// Set simulation timescale
//
`include "const.def"




module npuarc_biu_sccm_dmiibp_slv
// leda G_521_2_B off
// LMD: Use lowercase letters for all signal reg, net and port names
// LJ: Pfx may include the uppercase, so disable the lint checking rule
  (

























  input  [2 -1:0]      sccm_dmi_slv_ibp_cmd_user,

  input                                   sccm_dmi_slv_ibp_cmd_valid,
  output                                  sccm_dmi_slv_ibp_cmd_accept,
  input                                   sccm_dmi_slv_ibp_cmd_read,
  input   [24                -1:0]       sccm_dmi_slv_ibp_cmd_addr,
  input                                   sccm_dmi_slv_ibp_cmd_wrap,
  input   [3-1:0]       sccm_dmi_slv_ibp_cmd_data_size,
  input   [4-1:0]       sccm_dmi_slv_ibp_cmd_burst_size,
  input   [2-1:0]       sccm_dmi_slv_ibp_cmd_prot,
  input   [4-1:0]       sccm_dmi_slv_ibp_cmd_cache,
  input                                   sccm_dmi_slv_ibp_cmd_lock,
  input                                   sccm_dmi_slv_ibp_cmd_excl,

  output                                  sccm_dmi_slv_ibp_rd_valid,
  output                                  sccm_dmi_slv_ibp_rd_excl_ok,
  input                                   sccm_dmi_slv_ibp_rd_accept,
  output                                  sccm_dmi_slv_ibp_err_rd,
  output  [64               -1:0]        sccm_dmi_slv_ibp_rd_data,
  output                                  sccm_dmi_slv_ibp_rd_last,

  input                                   sccm_dmi_slv_ibp_wr_valid,
  output                                  sccm_dmi_slv_ibp_wr_accept,
  input   [64               -1:0]        sccm_dmi_slv_ibp_wr_data,
  input   [8  -1:0]                    sccm_dmi_slv_ibp_wr_mask,
  input                                   sccm_dmi_slv_ibp_wr_last,

  output                                  sccm_dmi_slv_ibp_wr_done,
  output                                  sccm_dmi_slv_ibp_wr_excl_done,
  output                                  sccm_dmi_slv_ibp_err_wr,
  input                                   sccm_dmi_slv_ibp_wr_resp_accept,


  output                                  sccm_dmiibp_slv_ibp_cmd_valid,
  input                                   sccm_dmiibp_slv_ibp_cmd_accept,
  output                                  sccm_dmiibp_slv_ibp_cmd_read,
  output  [24                -1:0]       sccm_dmiibp_slv_ibp_cmd_addr,
  output                                  sccm_dmiibp_slv_ibp_cmd_wrap,
  output  [3-1:0]       sccm_dmiibp_slv_ibp_cmd_data_size,
  output  [4-1:0]       sccm_dmiibp_slv_ibp_cmd_burst_size,
  output  [2-1:0]       sccm_dmiibp_slv_ibp_cmd_prot,
  output  [4-1:0]       sccm_dmiibp_slv_ibp_cmd_cache,
  output                                  sccm_dmiibp_slv_ibp_cmd_lock,
  output                                  sccm_dmiibp_slv_ibp_cmd_excl,

  input                                   sccm_dmiibp_slv_ibp_rd_valid,
  input                                   sccm_dmiibp_slv_ibp_rd_excl_ok,
  output                                  sccm_dmiibp_slv_ibp_rd_accept,
  input                                   sccm_dmiibp_slv_ibp_err_rd,
  input   [64               -1:0]        sccm_dmiibp_slv_ibp_rd_data,
  input                                   sccm_dmiibp_slv_ibp_rd_last,

  output                                  sccm_dmiibp_slv_ibp_wr_valid,
  input                                   sccm_dmiibp_slv_ibp_wr_accept,
  output  [64               -1:0]        sccm_dmiibp_slv_ibp_wr_data,
  output  [8  -1:0]                    sccm_dmiibp_slv_ibp_wr_mask,
  output                                  sccm_dmiibp_slv_ibp_wr_last,

  input                                   sccm_dmiibp_slv_ibp_wr_done,
  input                                   sccm_dmiibp_slv_ibp_wr_excl_done,
  input                                   sccm_dmiibp_slv_ibp_err_wr,
  output                                  sccm_dmiibp_slv_ibp_wr_resp_accept,
  output [2 -1:0] sccm_dmiibp_slv_ibp_cmd_user,



  input                                   clk,
// leda NTL_CON13C off
// LMD: non driving internal net
// LJ: Some signals bit field are indeed no driven
  // spyglass disable_block W240
  // SMD: declared but not read
  // SJ: do not care this wrn
  input                                   sync_rst_r,
  // spyglass enable_block W240
  // spyglass disable_block W240
  // SMD: declared but not read
  // SJ: do not care this wrn
  input                                   async_rst,
  // spyglass enable_block W240
// leda NTL_CON13C on
  input                                   nmi_restart_r,
  input                                   rst_a
);


// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning




// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_i_ibp_cmd_rgon;
// spyglass enable_block W240

wire [2 -1:0] i_ibp_cmd_chnl_user;



 wire [1-1:0] i_ibp_cmd_chnl_valid;
 wire [1-1:0] i_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] i_ibp_cmd_chnl;

 wire [1-1:0] i_ibp_wd_chnl_valid;
 wire [1-1:0] i_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] i_ibp_wd_chnl;

 wire [1-1:0] i_ibp_rd_chnl_accept;
 wire [1-1:0] i_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] i_ibp_rd_chnl;

 wire [1-1:0] i_ibp_wrsp_chnl_valid;
 wire [1-1:0] i_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] i_ibp_wrsp_chnl;









wire [2 -1:0] sccm_dmi_slv_ibp_cmd_chnl_user;



 wire [1-1:0] sccm_dmi_slv_ibp_cmd_chnl_valid;
 wire [1-1:0] sccm_dmi_slv_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] sccm_dmi_slv_ibp_cmd_chnl;

 wire [1-1:0] sccm_dmi_slv_ibp_wd_chnl_valid;
 wire [1-1:0] sccm_dmi_slv_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] sccm_dmi_slv_ibp_wd_chnl;

 wire [1-1:0] sccm_dmi_slv_ibp_rd_chnl_accept;
 wire [1-1:0] sccm_dmi_slv_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] sccm_dmi_slv_ibp_rd_chnl;

 wire [1-1:0] sccm_dmi_slv_ibp_wrsp_chnl_valid;
 wire [1-1:0] sccm_dmi_slv_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] sccm_dmi_slv_ibp_wrsp_chnl;


// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_sccm_dmi_slv_ibp_cmd_chnl_rgon;
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
u_sccm_dmi_slv_ibp2pack
  (
    .rst_a                     (rst_a),
    .nmi_restart_r (nmi_restart_r ),
    .clk                       (clk               ) ,
    .ibp_cmd_user              (sccm_dmi_slv_ibp_cmd_user),
    .ibp_cmd_chnl_user         (sccm_dmi_slv_ibp_cmd_chnl_user),

  .ibp_cmd_valid             (sccm_dmi_slv_ibp_cmd_valid),
  .ibp_cmd_accept            (sccm_dmi_slv_ibp_cmd_accept),
  .ibp_cmd_read              (sccm_dmi_slv_ibp_cmd_read),
  .ibp_cmd_addr              (sccm_dmi_slv_ibp_cmd_addr),
  .ibp_cmd_wrap              (sccm_dmi_slv_ibp_cmd_wrap),
  .ibp_cmd_data_size         (sccm_dmi_slv_ibp_cmd_data_size),
  .ibp_cmd_burst_size        (sccm_dmi_slv_ibp_cmd_burst_size),
  .ibp_cmd_prot              (sccm_dmi_slv_ibp_cmd_prot),
  .ibp_cmd_cache             (sccm_dmi_slv_ibp_cmd_cache),
  .ibp_cmd_lock              (sccm_dmi_slv_ibp_cmd_lock),
  .ibp_cmd_excl              (sccm_dmi_slv_ibp_cmd_excl),

  .ibp_rd_valid              (sccm_dmi_slv_ibp_rd_valid),
  .ibp_rd_excl_ok            (sccm_dmi_slv_ibp_rd_excl_ok),
  .ibp_rd_accept             (sccm_dmi_slv_ibp_rd_accept),
  .ibp_err_rd                (sccm_dmi_slv_ibp_err_rd),
  .ibp_rd_data               (sccm_dmi_slv_ibp_rd_data),
  .ibp_rd_last               (sccm_dmi_slv_ibp_rd_last),

  .ibp_wr_valid              (sccm_dmi_slv_ibp_wr_valid),
  .ibp_wr_accept             (sccm_dmi_slv_ibp_wr_accept),
  .ibp_wr_data               (sccm_dmi_slv_ibp_wr_data),
  .ibp_wr_mask               (sccm_dmi_slv_ibp_wr_mask),
  .ibp_wr_last               (sccm_dmi_slv_ibp_wr_last),

  .ibp_wr_done               (sccm_dmi_slv_ibp_wr_done),
  .ibp_wr_excl_done          (sccm_dmi_slv_ibp_wr_excl_done),
  .ibp_err_wr                (sccm_dmi_slv_ibp_err_wr),
  .ibp_wr_resp_accept        (sccm_dmi_slv_ibp_wr_resp_accept),



    .ibp_cmd_chnl_valid  (sccm_dmi_slv_ibp_cmd_chnl_valid),
    .ibp_cmd_chnl_accept (sccm_dmi_slv_ibp_cmd_chnl_accept),
    .ibp_cmd_chnl        (sccm_dmi_slv_ibp_cmd_chnl),

    .ibp_rd_chnl_valid   (sccm_dmi_slv_ibp_rd_chnl_valid),
    .ibp_rd_chnl_accept  (sccm_dmi_slv_ibp_rd_chnl_accept),
    .ibp_rd_chnl         (sccm_dmi_slv_ibp_rd_chnl),

    .ibp_wd_chnl_valid   (sccm_dmi_slv_ibp_wd_chnl_valid),
    .ibp_wd_chnl_accept  (sccm_dmi_slv_ibp_wd_chnl_accept),
    .ibp_wd_chnl         (sccm_dmi_slv_ibp_wd_chnl),

    .ibp_wrsp_chnl_valid (sccm_dmi_slv_ibp_wrsp_chnl_valid),
    .ibp_wrsp_chnl_accept(sccm_dmi_slv_ibp_wrsp_chnl_accept),
    .ibp_wrsp_chnl       (sccm_dmi_slv_ibp_wrsp_chnl),

    .ibp_cmd_rgon              (1'b0),
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
    .ibp_cmd_chnl_rgon         (unused_sccm_dmi_slv_ibp_cmd_chnl_rgon)
// spyglass enable_block UnloadedOutTerm-ML
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b
   );
// leda NTL_CON10 on
// leda NTL_CON10B on


  assign i_ibp_cmd_chnl_valid     = sccm_dmi_slv_ibp_cmd_chnl_valid  ;
  assign sccm_dmi_slv_ibp_cmd_chnl_accept    = i_ibp_cmd_chnl_accept ;
  assign i_ibp_cmd_chnl           = sccm_dmi_slv_ibp_cmd_chnl        ;

  assign i_ibp_wd_chnl_valid      = sccm_dmi_slv_ibp_wd_chnl_valid   ;
  assign sccm_dmi_slv_ibp_wd_chnl_accept     = i_ibp_wd_chnl_accept  ;
  assign i_ibp_wd_chnl            = sccm_dmi_slv_ibp_wd_chnl         ;

  assign i_ibp_rd_chnl_accept     = sccm_dmi_slv_ibp_rd_chnl_accept  ;
  assign sccm_dmi_slv_ibp_rd_chnl_valid      = i_ibp_rd_chnl_valid   ;
  assign sccm_dmi_slv_ibp_rd_chnl            = i_ibp_rd_chnl         ;

  assign i_ibp_wrsp_chnl_accept   = sccm_dmi_slv_ibp_wrsp_chnl_accept;
  assign sccm_dmi_slv_ibp_wrsp_chnl_valid    = i_ibp_wrsp_chnl_valid ;
  assign sccm_dmi_slv_ibp_wrsp_chnl          = i_ibp_wrsp_chnl       ;

  assign i_ibp_cmd_chnl_user      = sccm_dmi_slv_ibp_cmd_chnl_user;









// Covert the IBP width



 wire [1-1:0] cvted_i_ibp_cmd_chnl_valid;
 wire [1-1:0] cvted_i_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] cvted_i_ibp_cmd_chnl;

 wire [1-1:0] cvted_i_ibp_wd_chnl_valid;
 wire [1-1:0] cvted_i_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] cvted_i_ibp_wd_chnl;

 wire [1-1:0] cvted_i_ibp_rd_chnl_accept;
 wire [1-1:0] cvted_i_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] cvted_i_ibp_rd_chnl;

 wire [1-1:0] cvted_i_ibp_wrsp_chnl_valid;
 wire [1-1:0] cvted_i_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] cvted_i_ibp_wrsp_chnl;

wire [2 -1:0] cvted_i_ibp_cmd_chnl_user;

// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_ibpx2ibpy_o_ibp_cmd_chnl_rgon;
// spyglass enable_block W240

npuarc_biu_ibpx2ibpy
  #(
           .N2W_SUPPORT_NARROW_TRANS (1),
           .W2N_SUPPORT_BURST_TRANS  (0),

    .SPLT_FIFO_DEPTH      (10),
    .BYPBUF_WD_CHNL       (0),
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

    .X_USER_W(2),
    .Y_USER_W(2),
    .X_RGON_W  (1),
    .Y_RGON_W  (1)
    )
 u_i_ibp64toibp64 (



    .i_ibp_cmd_chnl_valid  (i_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (i_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (i_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (i_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (i_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (i_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (i_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (i_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (i_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (i_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(i_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (i_ibp_wrsp_chnl),





    .o_ibp_cmd_chnl_valid  (cvted_i_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (cvted_i_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (cvted_i_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (cvted_i_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (cvted_i_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (cvted_i_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (cvted_i_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (cvted_i_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (cvted_i_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (cvted_i_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(cvted_i_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (cvted_i_ibp_wrsp_chnl),

    .i_ibp_cmd_chnl_user   (i_ibp_cmd_chnl_user),
    .o_ibp_cmd_chnl_user   (cvted_i_ibp_cmd_chnl_user),
    .i_ibp_cmd_chnl_rgon   (1'b0),
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
    .o_ibp_cmd_chnl_rgon   (unused_ibpx2ibpy_o_ibp_cmd_chnl_rgon),
// spyglass enable_block UnloadedOutTerm-ML
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b
    .rst_a               (rst_a),
    .nmi_restart_r (nmi_restart_r ),
    .clk                 (clk               )
);

// Buffer the IBP for better timing

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: The region is not used for IOC port
wire [2-1:0] mid_ibp_cmd_chnl_user;
// leda NTL_CON13A on



 wire [1-1:0] mid_ibp_cmd_chnl_valid;
 wire [1-1:0] mid_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] mid_ibp_cmd_chnl;

 wire [1-1:0] mid_ibp_wd_chnl_valid;
 wire [1-1:0] mid_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] mid_ibp_wd_chnl;

 wire [1-1:0] mid_ibp_rd_chnl_accept;
 wire [1-1:0] mid_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] mid_ibp_rd_chnl;

 wire [1-1:0] mid_ibp_wrsp_chnl_valid;
 wire [1-1:0] mid_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mid_ibp_wrsp_chnl;


  assign mid_ibp_cmd_chnl_valid     = cvted_i_ibp_cmd_chnl_valid  ;
  assign cvted_i_ibp_cmd_chnl_accept    = mid_ibp_cmd_chnl_accept ;
  assign mid_ibp_cmd_chnl           = cvted_i_ibp_cmd_chnl        ;

  assign mid_ibp_wd_chnl_valid      = cvted_i_ibp_wd_chnl_valid   ;
  assign cvted_i_ibp_wd_chnl_accept     = mid_ibp_wd_chnl_accept  ;
  assign mid_ibp_wd_chnl            = cvted_i_ibp_wd_chnl         ;

  assign mid_ibp_rd_chnl_accept     = cvted_i_ibp_rd_chnl_accept  ;
  assign cvted_i_ibp_rd_chnl_valid      = mid_ibp_rd_chnl_valid   ;
  assign cvted_i_ibp_rd_chnl            = mid_ibp_rd_chnl         ;

  assign mid_ibp_wrsp_chnl_accept   = cvted_i_ibp_wrsp_chnl_accept;
  assign cvted_i_ibp_wrsp_chnl_valid    = mid_ibp_wrsp_chnl_valid ;
  assign cvted_i_ibp_wrsp_chnl          = mid_ibp_wrsp_chnl       ;

  assign mid_ibp_cmd_chnl_user      = cvted_i_ibp_cmd_chnl_user;







 wire [1-1:0] pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl_valid;
 wire [1-1:0] pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl;

 wire [1-1:0] pre_bind_sccm_dmiibp_slv_ibp_wd_chnl_valid;
 wire [1-1:0] pre_bind_sccm_dmiibp_slv_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] pre_bind_sccm_dmiibp_slv_ibp_wd_chnl;

 wire [1-1:0] pre_bind_sccm_dmiibp_slv_ibp_rd_chnl_accept;
 wire [1-1:0] pre_bind_sccm_dmiibp_slv_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] pre_bind_sccm_dmiibp_slv_ibp_rd_chnl;

 wire [1-1:0] pre_bind_sccm_dmiibp_slv_ibp_wrsp_chnl_valid;
 wire [1-1:0] pre_bind_sccm_dmiibp_slv_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] pre_bind_sccm_dmiibp_slv_ibp_wrsp_chnl;

wire [2-1:0] pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl_user;




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


wire pre_bind_sccm_dmiibp_slv_ibp_rgon_hit = 1'b1;








// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: Dummy signals are indeed no driven
wire mid_ibp_split_indicator_dummy;
// leda NTL_CON13A on
wire [1-1:0] mid_ibp_split_indicator;



// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0 / logic 1
// LJ: No care about the constant here
assign {
    mid_ibp_split_indicator_dummy,
    mid_ibp_split_indicator
    } = { 1'b0
       , pre_bind_sccm_dmiibp_slv_ibp_rgon_hit
        };
// leda NTL_CON16 on

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: Dummy signals are indeed no driven
wire mid_splt_dummy0;
wire mid_splt_dummy1;
// leda NTL_CON13A on



 wire [1-1:0] mid_splt_ibp_cmd_chnl_valid;
 wire [1-1:0] mid_splt_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] mid_splt_ibp_cmd_chnl;

 wire [1-1:0] mid_splt_ibp_wd_chnl_valid;
 wire [1-1:0] mid_splt_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] mid_splt_ibp_wd_chnl;

 wire [1-1:0] mid_splt_ibp_rd_chnl_accept;
 wire [1-1:0] mid_splt_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] mid_splt_ibp_rd_chnl;

 wire [1-1:0] mid_splt_ibp_wrsp_chnl_valid;
 wire [1-1:0] mid_splt_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] mid_splt_ibp_wrsp_chnl;

wire [2*1-1:0] mid_splt_ibp_cmd_chnl_user;
npuarc_biu_ibp_split
  #(
    .ALLOW_DIFF_BRANCH  (1),
    .SPLT_NUM  (1),
    .USER_W  (2),



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
    .SPLT_FIFO_WIDTH  (1),
    .SPLT_FIFO_DEPTH  (10)
  )
u_mid_ibp_splitter(
    .i_ibp_split_indicator  (mid_ibp_split_indicator  ),

    .i_ibp_cmd_chnl_user    (mid_ibp_cmd_chnl_user    ),
    .o_bus_ibp_cmd_chnl_user(mid_splt_ibp_cmd_chnl_user),




    .i_ibp_cmd_chnl_valid  (mid_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (mid_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (mid_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (mid_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (mid_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (mid_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (mid_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (mid_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (mid_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (mid_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(mid_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (mid_ibp_wrsp_chnl),




    .o_bus_ibp_cmd_chnl_valid  (mid_splt_ibp_cmd_chnl_valid),
    .o_bus_ibp_cmd_chnl_accept (mid_splt_ibp_cmd_chnl_accept),
    .o_bus_ibp_cmd_chnl        (mid_splt_ibp_cmd_chnl),

    .o_bus_ibp_rd_chnl_valid   (mid_splt_ibp_rd_chnl_valid),
    .o_bus_ibp_rd_chnl_accept  (mid_splt_ibp_rd_chnl_accept),
    .o_bus_ibp_rd_chnl         (mid_splt_ibp_rd_chnl),

    .o_bus_ibp_wd_chnl_valid   (mid_splt_ibp_wd_chnl_valid),
    .o_bus_ibp_wd_chnl_accept  (mid_splt_ibp_wd_chnl_accept),
    .o_bus_ibp_wd_chnl         (mid_splt_ibp_wd_chnl),

    .o_bus_ibp_wrsp_chnl_valid (mid_splt_ibp_wrsp_chnl_valid),
    .o_bus_ibp_wrsp_chnl_accept(mid_splt_ibp_wrsp_chnl_accept),
    .o_bus_ibp_wrsp_chnl       (mid_splt_ibp_wrsp_chnl),

    .rst_a               (rst_a),
    .nmi_restart_r (nmi_restart_r ),
    .clk                 (clk               )
);

// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0 / logic 1
// LJ: No care about the constant here
assign
  {
    mid_splt_dummy0
       , pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl_user
       , pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl
       , pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl_valid
       , pre_bind_sccm_dmiibp_slv_ibp_wd_chnl
       , pre_bind_sccm_dmiibp_slv_ibp_wd_chnl_valid
       , pre_bind_sccm_dmiibp_slv_ibp_rd_chnl_accept
       , pre_bind_sccm_dmiibp_slv_ibp_wrsp_chnl_accept
  }
  =
    {
    1'b1,
    mid_splt_ibp_cmd_chnl_user,
    mid_splt_ibp_cmd_chnl,
    mid_splt_ibp_cmd_chnl_valid,
    mid_splt_ibp_wd_chnl,
    mid_splt_ibp_wd_chnl_valid,
    mid_splt_ibp_rd_chnl_accept,
    mid_splt_ibp_wrsp_chnl_accept
    } ;
// leda NTL_CON16 on

// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0 / logic 1
// LJ: No care about the constant here
assign
  {
    mid_splt_dummy1,
    mid_splt_ibp_rd_chnl,
    mid_splt_ibp_rd_chnl_valid,
    mid_splt_ibp_wrsp_chnl,
    mid_splt_ibp_wrsp_chnl_valid,
    mid_splt_ibp_cmd_chnl_accept,
    mid_splt_ibp_wd_chnl_accept
    }
  =
  {
      1'b1
       , pre_bind_sccm_dmiibp_slv_ibp_rd_chnl
       , pre_bind_sccm_dmiibp_slv_ibp_rd_chnl_valid
       , pre_bind_sccm_dmiibp_slv_ibp_wrsp_chnl
       , pre_bind_sccm_dmiibp_slv_ibp_wrsp_chnl_valid
       , pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl_accept
       , pre_bind_sccm_dmiibp_slv_ibp_wd_chnl_accept
  };
// leda NTL_CON16 on




wire pre_bind_buf_sccm_dmiibp_slv_ibp_idle;

wire [2-1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl_user;



 wire [1-1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl_valid;
 wire [1-1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl_accept;
 wire [41 * 1 -1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl;

 wire [1-1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_wd_chnl_valid;
 wire [1-1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_wd_chnl_accept;
 wire [73 * 1 -1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_wd_chnl;

 wire [1-1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_rd_chnl_accept;
 wire [1-1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_rd_chnl_valid;
 wire [67 * 1 -1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_rd_chnl;

 wire [1-1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_wrsp_chnl_valid;
 wire [1-1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_wrsp_chnl_accept;
 wire [3 * 1 -1:0] pre_bind_buf_sccm_dmiibp_slv_ibp_wrsp_chnl;


  assign pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl_valid     = pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl_valid  ;
  assign pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl_accept    = pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl_accept ;
  assign pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl           = pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl        ;

  assign pre_bind_buf_sccm_dmiibp_slv_ibp_wd_chnl_valid      = pre_bind_sccm_dmiibp_slv_ibp_wd_chnl_valid   ;
  assign pre_bind_sccm_dmiibp_slv_ibp_wd_chnl_accept     = pre_bind_buf_sccm_dmiibp_slv_ibp_wd_chnl_accept  ;
  assign pre_bind_buf_sccm_dmiibp_slv_ibp_wd_chnl            = pre_bind_sccm_dmiibp_slv_ibp_wd_chnl         ;

  assign pre_bind_buf_sccm_dmiibp_slv_ibp_rd_chnl_accept     = pre_bind_sccm_dmiibp_slv_ibp_rd_chnl_accept  ;
  assign pre_bind_sccm_dmiibp_slv_ibp_rd_chnl_valid      = pre_bind_buf_sccm_dmiibp_slv_ibp_rd_chnl_valid   ;
  assign pre_bind_sccm_dmiibp_slv_ibp_rd_chnl            = pre_bind_buf_sccm_dmiibp_slv_ibp_rd_chnl         ;

  assign pre_bind_buf_sccm_dmiibp_slv_ibp_wrsp_chnl_accept   = pre_bind_sccm_dmiibp_slv_ibp_wrsp_chnl_accept;
  assign pre_bind_sccm_dmiibp_slv_ibp_wrsp_chnl_valid    = pre_bind_buf_sccm_dmiibp_slv_ibp_wrsp_chnl_valid ;
  assign pre_bind_sccm_dmiibp_slv_ibp_wrsp_chnl          = pre_bind_buf_sccm_dmiibp_slv_ibp_wrsp_chnl       ;

  assign pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl_user      = pre_bind_sccm_dmiibp_slv_ibp_cmd_chnl_user;
  assign pre_bind_buf_sccm_dmiibp_slv_ibp_idle               = 1'b1;


wire sccm_dmiibp_slv_ibp_cwbind_ibp_req;

wire  [2 -1:0]      sccm_dmiibp_slv_ibp_cmd_chnl_user;


npuarc_biu_ibp_cwbind
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
    .OUT_CMD_CNT_W(4),
    .OUT_CMD_NUM  (10),
    .O_RESP_ALWAYS_ACCEPT (0),
    .ENABLE_CWBIND (0)
    )
u_sccm_dmiibp_slv_ibp_cwbind
  (
    .i_ibp_cmd_chnl_user  (pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl_user),
    .o_ibp_cmd_chnl_user  (sccm_dmiibp_slv_ibp_cmd_chnl_user),



    .i_ibp_cmd_chnl_valid  (pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl_valid),
    .i_ibp_cmd_chnl_accept (pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl_accept),
    .i_ibp_cmd_chnl        (pre_bind_buf_sccm_dmiibp_slv_ibp_cmd_chnl),

    .i_ibp_rd_chnl_valid   (pre_bind_buf_sccm_dmiibp_slv_ibp_rd_chnl_valid),
    .i_ibp_rd_chnl_accept  (pre_bind_buf_sccm_dmiibp_slv_ibp_rd_chnl_accept),
    .i_ibp_rd_chnl         (pre_bind_buf_sccm_dmiibp_slv_ibp_rd_chnl),

    .i_ibp_wd_chnl_valid   (pre_bind_buf_sccm_dmiibp_slv_ibp_wd_chnl_valid),
    .i_ibp_wd_chnl_accept  (pre_bind_buf_sccm_dmiibp_slv_ibp_wd_chnl_accept),
    .i_ibp_wd_chnl         (pre_bind_buf_sccm_dmiibp_slv_ibp_wd_chnl),

    .i_ibp_wrsp_chnl_valid (pre_bind_buf_sccm_dmiibp_slv_ibp_wrsp_chnl_valid),
    .i_ibp_wrsp_chnl_accept(pre_bind_buf_sccm_dmiibp_slv_ibp_wrsp_chnl_accept),
    .i_ibp_wrsp_chnl       (pre_bind_buf_sccm_dmiibp_slv_ibp_wrsp_chnl),




    .o_ibp_cmd_chnl_valid  (sccm_dmiibp_slv_ibp_cmd_chnl_valid),
    .o_ibp_cmd_chnl_accept (sccm_dmiibp_slv_ibp_cmd_chnl_accept),
    .o_ibp_cmd_chnl        (sccm_dmiibp_slv_ibp_cmd_chnl),

    .o_ibp_rd_chnl_valid   (sccm_dmiibp_slv_ibp_rd_chnl_valid),
    .o_ibp_rd_chnl_accept  (sccm_dmiibp_slv_ibp_rd_chnl_accept),
    .o_ibp_rd_chnl         (sccm_dmiibp_slv_ibp_rd_chnl),

    .o_ibp_wd_chnl_valid   (sccm_dmiibp_slv_ibp_wd_chnl_valid),
    .o_ibp_wd_chnl_accept  (sccm_dmiibp_slv_ibp_wd_chnl_accept),
    .o_ibp_wd_chnl         (sccm_dmiibp_slv_ibp_wd_chnl),

    .o_ibp_wrsp_chnl_valid (sccm_dmiibp_slv_ibp_wrsp_chnl_valid),
    .o_ibp_wrsp_chnl_accept(sccm_dmiibp_slv_ibp_wrsp_chnl_accept),
    .o_ibp_wrsp_chnl       (sccm_dmiibp_slv_ibp_wrsp_chnl),

// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
    .i_ibp_clk_en_req  (sccm_dmiibp_slv_ibp_cwbind_ibp_req),
// spyglass enable_block UnloadedOutTerm-ML
    .clk               (clk                           ),
    .nmi_restart_r (nmi_restart_r ),
    .rst_a             (rst_a)
   );



// Declare unused ports
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ: Unused instance ports are port-mapped but not connected
wire unused_sccm_dmiibp_slv__ibp_cmd_rgon;
// spyglass enable_block W240
// leda NTL_CON10 off
// leda NTL_CON10B off
// LMD: output tied to supply Ranges
// LJ: No care about the constant tied
npuarc_biu_pack2ibp
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
    .RGON_W (1)
    )
// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
u_sccm_dmiibp_slv_pack2ibp
  (
    .ibp_cmd_chnl_user  (sccm_dmiibp_slv_ibp_cmd_chnl_user),
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Connected to floating net
// SJ: do not care this wrn
    .ibp_cmd_user  (sccm_dmiibp_slv_ibp_cmd_user),
    .ibp_cmd_rgon              (unused_sccm_dmiibp_slv__ibp_cmd_rgon),
// spyglass enable_block UnloadedOutTerm-ML


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

    .ibp_cmd_chnl_rgon         (1'b0)
   );
// leda B_1011 on
// leda WV951025 on
// spyglass enable_block W287b

// leda NTL_CON10 on
// leda NTL_CON10B on






// spyglass enable_block W528



// leda G_521_2_B on

endmodule // biu_sccm_dmiibp_slv




