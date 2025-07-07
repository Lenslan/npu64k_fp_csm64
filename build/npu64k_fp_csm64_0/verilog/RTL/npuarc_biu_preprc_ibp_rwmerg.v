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
//  biu_preprc_ibp_rwmerg
// ===========================================================================
//
// Description:
//  Verilog module to merge the read-only and write-only IBP
//
// ===========================================================================
// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"

// Set simulation timescale
//
`include "const.def"



module npuarc_biu_preprc_ibp_rwmerg
 #(
// leda W175 off
// LMD: A parameter XXX has been defined but is not used
// LJ: We always list out all IBP relevant defines although not used



    parameter CMD_CHNL_READ           = 0,
    parameter CMD_CHNL_WRAP           = 1,
    parameter CMD_CHNL_DATA_SIZE_LSB  = 2,
    parameter CMD_CHNL_DATA_SIZE_W    = 3,
    parameter CMD_CHNL_BURST_SIZE_LSB = 5,
    parameter CMD_CHNL_BURST_SIZE_W   = 4,
    parameter CMD_CHNL_PROT_LSB       = 9,
    parameter CMD_CHNL_PROT_W         = 2,
    parameter CMD_CHNL_CACHE_LSB      = 11,
    parameter CMD_CHNL_CACHE_W        = 4,
    parameter CMD_CHNL_LOCK           = 15,
    parameter CMD_CHNL_EXCL           = 16,
    parameter CMD_CHNL_ADDR_LSB       = 17,
    parameter CMD_CHNL_ADDR_W         = 32,
    parameter CMD_CHNL_W              = 49,

    parameter WD_CHNL_LAST            = 0,
    parameter WD_CHNL_DATA_LSB        = 1,
    parameter WD_CHNL_DATA_W          = 32,
    parameter WD_CHNL_MASK_LSB        = 33,
    parameter WD_CHNL_MASK_W          = 4,
    parameter WD_CHNL_W               = 37,

    parameter RD_CHNL_ERR_RD          = 0,
    parameter RD_CHNL_RD_EXCL_OK      = 2,
    parameter RD_CHNL_RD_LAST         = 1,
    parameter RD_CHNL_RD_DATA_LSB     = 3,
    parameter RD_CHNL_RD_DATA_W       = 32,
    parameter RD_CHNL_W               = 35,

    parameter WRSP_CHNL_WR_DONE       = 0,
    parameter WRSP_CHNL_WR_EXCL_DONE  = 1,
    parameter WRSP_CHNL_ERR_WR        = 2,
    parameter WRSP_CHNL_W             = 3,
   parameter USER_W = 1,
   parameter RO_IS_FULL_IBP = 0,
   parameter OUTSTAND_NUM = 4,
   parameter OUTSTAND_CNT_W = 2
 // leda W175 on
 ) (
  // ro IBP is read-only
  // command channel
  input  ro_ibp_cmd_chnl_valid,
  output ro_ibp_cmd_chnl_accept,
  input  [CMD_CHNL_W-1:0] ro_ibp_cmd_chnl,
  input  [USER_W-1:0] ro_ibp_cmd_chnl_user,
  //
  // read data channel
  output ro_ibp_rd_chnl_valid,
  input  ro_ibp_rd_chnl_accept,
  output [RD_CHNL_W-1:0] ro_ibp_rd_chnl,
  //
  // leda NTL_CON13C off
  // LMD: non driving internal net
  // LJ: Some signals bit field are indeed no driven
  // leda NTL_CON37 off
  // LMD: Signal/Net must read from the input port in module
  // LJ: Some signals bit field are indeed not read and used

  // write data channel
  // spyglass disable_block W240
  // SMD: input port declared but not read
  // SJ: No care about the warning
  input  ro_ibp_wd_chnl_valid,
  // spyglass enable_block W240

  output ro_ibp_wd_chnl_accept,
  // spyglass disable_block W240
  // SMD: input port declared but not read
  // SJ: No care about the warning
  input  [WD_CHNL_W-1:0] ro_ibp_wd_chnl,
  // spyglass enable_block W240
  //
  // write response channel
  output ro_ibp_wrsp_chnl_valid,

  // spyglass disable_block W240
  // SMD: input port declared but not read
  // SJ: No care about the warning
  input  ro_ibp_wrsp_chnl_accept,
  // spyglass enable_block W240
  output [WRSP_CHNL_W-1:0] ro_ibp_wrsp_chnl,

  // leda NTL_CON37 on
  // leda NTL_CON13C on

  // leda NTL_CON13C off
  // LMD: non driving internal net
  // LJ: Some signals bit field are indeed no driven
  // leda NTL_CON37 off
  // LMD: Signal/Net must read from the input port in module
  // LJ: Some signals bit field are indeed not read and used

  // wo IBP is write-only
  // command channel
  input  wo_ibp_cmd_chnl_valid,
  output wo_ibp_cmd_chnl_accept,
  input  [CMD_CHNL_W-1:0] wo_ibp_cmd_chnl,
  input  [USER_W-1:0] wo_ibp_cmd_chnl_user,
  //
  // read data channel
  output wo_ibp_rd_chnl_valid,
  // spyglass disable_block W240
  // SMD: input port declared but not read
  // SJ: No care about the warning
  input  wo_ibp_rd_chnl_accept,
  // spyglass enable_block W240
  output [RD_CHNL_W-1:0] wo_ibp_rd_chnl,

  //
  // write data channel
  input  wo_ibp_wd_chnl_valid,
  output wo_ibp_wd_chnl_accept,
  input  [WD_CHNL_W-1:0] wo_ibp_wd_chnl,
  //
  // write response channel
  output wo_ibp_wrsp_chnl_valid,
  input  wo_ibp_wrsp_chnl_accept,
  output [WRSP_CHNL_W-1:0] wo_ibp_wrsp_chnl,
  // leda NTL_CON37 on
  // leda NTL_CON13C on


  // command channel
  output rw_ibp_cmd_chnl_valid,
  input  rw_ibp_cmd_chnl_accept,
  output [CMD_CHNL_W-1:0] rw_ibp_cmd_chnl,
  output [USER_W-1:0] rw_ibp_cmd_chnl_user,
  //
  // read data channel
  input  rw_ibp_rd_chnl_valid,
  output rw_ibp_rd_chnl_accept,
  input  [RD_CHNL_W-1:0] rw_ibp_rd_chnl,
  //
  // write data channel
  output rw_ibp_wd_chnl_valid,
  input  rw_ibp_wd_chnl_accept,
  output [WD_CHNL_W-1:0] rw_ibp_wd_chnl,
  //
  // write response channel
  input  rw_ibp_wrsp_chnl_valid,
  output rw_ibp_wrsp_chnl_accept,
  input  [WRSP_CHNL_W-1:0] rw_ibp_wrsp_chnl,
  /////////
  input                         clk,  // clock signal
  input                         nmi_restart_r, // NMI reset signal
  input                         rst_a // reset signal
  );


generate//{
  if(RO_IS_FULL_IBP == 0) begin:ro_is_not_ful_ibp_gen//{
    assign ro_ibp_wd_chnl_accept = 1'b0;
    assign ro_ibp_wrsp_chnl= {WRSP_CHNL_W{1'b0}};
    assign ro_ibp_wrsp_chnl_valid= 1'b0;

    assign wo_ibp_rd_chnl_valid = 1'b0;
    assign wo_ibp_rd_chnl       = {RD_CHNL_W{1'b0}};

    // Count how much of the cmd is waiting write burst data
    //
    reg [OUTSTAND_CNT_W:0] wo_cmd_wait_wd_cnt_r;
    wire wo_cmd_wait_wd_cnt_ovf = (wo_cmd_wait_wd_cnt_r == $unsigned(OUTSTAND_NUM));
    wire wo_cmd_wait_wd_cnt_udf = (wo_cmd_wait_wd_cnt_r == {OUTSTAND_CNT_W+1{1'b0}});
    // The ibp wr burst counter increased when a IBP write command accepted to the cmd stage
    // also note no overflow allowed
    wire wo_cmd_wait_wd_cnt_inc = wo_ibp_cmd_chnl_valid & wo_ibp_cmd_chnl_accept & (~wo_ibp_cmd_chnl[CMD_CHNL_READ]);
    // The ibp wr burst counter decreased when a last beat of IBP write burst accepted to wd stage
    // also note no underflow allowed
    wire wo_cmd_wait_wd_cnt_dec = (wo_ibp_wd_chnl_valid & wo_ibp_wd_chnl_accept & wo_ibp_wd_chnl[WD_CHNL_LAST]);
    wire wo_cmd_wait_wd_cnt_ena = wo_cmd_wait_wd_cnt_inc | wo_cmd_wait_wd_cnt_dec;
    // leda B_3200 off
    // leda B_3219 off
    // LMD: Unequal length operand in bit/arithmetic operator
    // LJ: there is no overflow risk
    // leda W484 off
    // LMD: Possible loss of carry/borrow in addition/subtraction
    // LJ: there is no overflow risk
    // leda BTTF_D002 off
    // LMD: Unequal length LHS and RHS in assignment
    // LJ: there is no overflow risk
    wire [OUTSTAND_CNT_W:0] wo_cmd_wait_wd_cnt_nxt =
          ( wo_cmd_wait_wd_cnt_inc & (~wo_cmd_wait_wd_cnt_dec)) ? (wo_cmd_wait_wd_cnt_r + 1'b1)
        : (~wo_cmd_wait_wd_cnt_inc &  wo_cmd_wait_wd_cnt_dec) ? (wo_cmd_wait_wd_cnt_r - 1'b1)
        : wo_cmd_wait_wd_cnt_r ;
    // leda B_3219 on
    // leda B_3200 on
    // leda W484 on
    // leda BTTF_D002 on

    always @(posedge clk or posedge rst_a)
    begin : wo_cmd_wait_wd_cnt_DFFEAR_PROC
      if (rst_a == 1'b1) begin
          wo_cmd_wait_wd_cnt_r        <= {OUTSTAND_CNT_W+1{1'b0}};
      end
      else if (nmi_restart_r == 1'b1) begin
          wo_cmd_wait_wd_cnt_r        <= {OUTSTAND_CNT_W+1{1'b0}};
      end
      else if (wo_cmd_wait_wd_cnt_ena == 1'b1) begin
          wo_cmd_wait_wd_cnt_r        <= wo_cmd_wait_wd_cnt_nxt;
      end
    end


    wire ro_ibp_cmd_chnl_accept_pre;
    wire ro_ibp_cmd_chnl_valid_pre;
    assign ro_ibp_cmd_chnl_accept = ro_ibp_cmd_chnl_accept_pre ;
    assign ro_ibp_cmd_chnl_valid_pre  = ro_ibp_cmd_chnl_valid  ;

    wire wo_ibp_cmd_chnl_valid_pre;
    wire wo_ibp_cmd_chnl_accept_pre;
    assign wo_ibp_cmd_chnl_valid_pre = wo_ibp_cmd_chnl_valid   & (~wo_cmd_wait_wd_cnt_ovf);
    assign wo_ibp_cmd_chnl_accept = wo_ibp_cmd_chnl_accept_pre & (~wo_cmd_wait_wd_cnt_ovf);

    wire wo_cmd_wait_wd = wo_ibp_cmd_chnl_accept | (~wo_cmd_wait_wd_cnt_udf);
    wire wo_ibp_wd_chnl_accept_pre;
    wire wo_ibp_wd_chnl_valid_pre;
    assign wo_ibp_wd_chnl_valid_pre = wo_ibp_wd_chnl_valid & wo_cmd_wait_wd;
    assign wo_ibp_wd_chnl_accept = wo_ibp_wd_chnl_accept_pre & wo_cmd_wait_wd;

    wire byp_ro_ibp_cmd_chnl_accept;
    wire byp_ro_ibp_cmd_chnl_valid;
    wire [CMD_CHNL_W-1:0] byp_ro_ibp_cmd_chnl;
    wire [USER_W-1:0] byp_ro_ibp_cmd_chnl_user;

    wire byp_wo_ibp_cmd_chnl_accept;
    wire byp_wo_ibp_cmd_chnl_valid;
    wire [CMD_CHNL_W-1:0] byp_wo_ibp_cmd_chnl;
    wire [USER_W-1:0] byp_wo_ibp_cmd_chnl_user;

    wire byp_wo_ibp_wd_chnl_valid;
    wire byp_wo_ibp_wd_chnl_accept;
    wire [WD_CHNL_W-1:0] byp_wo_ibp_wd_chnl;


    npuarc_biu_preprc_bypbuf #(
      .BUF_DEPTH(1),
      .BUF_WIDTH(CMD_CHNL_W+USER_W)
    ) u_ro_ibp_cmd_bypbuf (
      .i_ready    (ro_ibp_cmd_chnl_accept_pre),
      .i_valid    (ro_ibp_cmd_chnl_valid_pre),
      .i_data     ({ro_ibp_cmd_chnl,ro_ibp_cmd_chnl_user}),
      .o_ready    (byp_ro_ibp_cmd_chnl_accept),
      .o_valid    (byp_ro_ibp_cmd_chnl_valid),
      .o_data     ({byp_ro_ibp_cmd_chnl, byp_ro_ibp_cmd_chnl_user}),

      .clk        (clk  ),
      .nmi_restart_r (nmi_restart_r ),
      .rst_a      (rst_a)
      );

    npuarc_biu_preprc_bypbuf #(
      .BUF_DEPTH(1),
      .BUF_WIDTH(CMD_CHNL_W+USER_W)
    ) u_wo_ibp_cmd_bypbuf (
      .i_ready    (wo_ibp_cmd_chnl_accept_pre),
      .i_valid    (wo_ibp_cmd_chnl_valid_pre),
      .i_data     ({wo_ibp_cmd_chnl,wo_ibp_cmd_chnl_user}),
      .o_ready    (byp_wo_ibp_cmd_chnl_accept),
      .o_valid    (byp_wo_ibp_cmd_chnl_valid),
      .o_data     ({byp_wo_ibp_cmd_chnl,byp_wo_ibp_cmd_chnl_user}),
      .clk        (clk  ),
      .nmi_restart_r (nmi_restart_r ),
      .rst_a      (rst_a)
      );


    npuarc_biu_preprc_bypbuf #(
      .BUF_DEPTH(1),
      .BUF_WIDTH(WD_CHNL_W)
    ) u_wr_wd_bypbuf (
      .i_ready    (wo_ibp_wd_chnl_accept_pre),
      .i_valid    (wo_ibp_wd_chnl_valid_pre),
      .i_data     (wo_ibp_wd_chnl),
      .o_ready    (byp_wo_ibp_wd_chnl_accept),
      .o_valid    (byp_wo_ibp_wd_chnl_valid),
      .o_data     (byp_wo_ibp_wd_chnl),
      .clk        (clk  ),
      .nmi_restart_r (nmi_restart_r ),
      .rst_a      (rst_a)
      );



    wire rw_ibp_cmd_chnl_hashked = rw_ibp_cmd_chnl_valid & rw_ibp_cmd_chnl_accept;
    wire [1:0] ibp_rdwr_merg_req = {
                          byp_ro_ibp_cmd_chnl_valid,
                          byp_wo_ibp_cmd_chnl_valid
                               };

    wire [2-1:0] ibp_rdwr_merg_grt;

    wire sel_ro_ibp_cmd;
    wire sel_wo_ibp_cmd;

    assign { sel_ro_ibp_cmd,
             sel_wo_ibp_cmd} = ibp_rdwr_merg_grt;
    // Maintain the round-robin
    npuarc_biu_preprc_rrobin # (
      .ARB_NUM(2)
      ) u_ibp_rdwr_merg_token(
      .req_vector          (ibp_rdwr_merg_req),
      .grt_vector          (ibp_rdwr_merg_grt),
      .arb_taken           (rw_ibp_cmd_chnl_hashked),
      .clk                 (clk                ),
      .nmi_restart_r (nmi_restart_r ),
      .rst_a               (rst_a              )
    );


    wire o_cmd_wait_wd_cnt_ovf;
    assign byp_wo_ibp_cmd_chnl_accept = (sel_wo_ibp_cmd) & rw_ibp_cmd_chnl_accept & (~o_cmd_wait_wd_cnt_ovf);
    assign byp_ro_ibp_cmd_chnl_accept = (sel_ro_ibp_cmd) & rw_ibp_cmd_chnl_accept & (~o_cmd_wait_wd_cnt_ovf);
    assign rw_ibp_cmd_chnl_valid= ((sel_ro_ibp_cmd & byp_ro_ibp_cmd_chnl_valid) | (sel_wo_ibp_cmd & byp_wo_ibp_cmd_chnl_valid )) & (~o_cmd_wait_wd_cnt_ovf);

    assign rw_ibp_cmd_chnl      = (({CMD_CHNL_W{sel_ro_ibp_cmd}} & byp_ro_ibp_cmd_chnl ) | ({CMD_CHNL_W{sel_wo_ibp_cmd}} & byp_wo_ibp_cmd_chnl  ));
    assign rw_ibp_cmd_chnl_user = (({USER_W{sel_ro_ibp_cmd}} & byp_ro_ibp_cmd_chnl_user ) | ({USER_W{sel_wo_ibp_cmd}} & byp_wo_ibp_cmd_chnl_user  ));

    assign ro_ibp_rd_chnl_valid  = rw_ibp_rd_chnl_valid;
    assign ro_ibp_rd_chnl        = rw_ibp_rd_chnl;
    assign rw_ibp_rd_chnl_accept = ro_ibp_rd_chnl_accept;

    // Count how much of the cmd is waiting write burst data
    //
    reg [OUTSTAND_CNT_W:0] o_cmd_wait_wd_cnt_r;
    assign o_cmd_wait_wd_cnt_ovf = (o_cmd_wait_wd_cnt_r == $unsigned(OUTSTAND_NUM));
    wire o_cmd_wait_wd_cnt_udf = (o_cmd_wait_wd_cnt_r == {OUTSTAND_CNT_W+1{1'b0}});
    // The ibp wr burst counter increased when a IBP write command accepted to the cmd stage
    // also note no overflow allowed
    wire o_cmd_wait_wd_cnt_inc = rw_ibp_cmd_chnl_valid & rw_ibp_cmd_chnl_accept & (~rw_ibp_cmd_chnl[CMD_CHNL_READ]);
    // The ibp wr burst counter decreased when a last beat of IBP write burst accepted to wd stage
    // also note no underflow allowed
    wire o_cmd_wait_wd_cnt_dec = (rw_ibp_wd_chnl_valid & rw_ibp_wd_chnl_accept & rw_ibp_wd_chnl[WD_CHNL_LAST]);
    wire o_cmd_wait_wd_cnt_ena = o_cmd_wait_wd_cnt_inc | o_cmd_wait_wd_cnt_dec;
    // leda B_3200 off
    // leda B_3219 off
    // LMD: Unequal length operand in bit/arithmetic operator
    // LJ: there is no overflow risk
    // leda W484 off
    // LMD: Possible loss of carry/borrow in addition/subtraction
    // LJ: there is no overflow risk
    // leda BTTF_D002 off
    // LMD: Unequal length LHS and RHS in assignment
    // LJ: there is no overflow risk
    wire [OUTSTAND_CNT_W:0] o_cmd_wait_wd_cnt_nxt =
          ( o_cmd_wait_wd_cnt_inc & (~o_cmd_wait_wd_cnt_dec)) ? (o_cmd_wait_wd_cnt_r + 1'b1)
        : (~o_cmd_wait_wd_cnt_inc &  o_cmd_wait_wd_cnt_dec) ? (o_cmd_wait_wd_cnt_r - 1'b1)
        : o_cmd_wait_wd_cnt_r ;
    // leda B_3219 on
    // leda B_3200 on
    // leda W484 on
    // leda BTTF_D002 on
    always @(posedge clk or posedge rst_a)
    begin : o_cmd_wait_wd_cnt_DFFEAR_PROC
      if (rst_a == 1'b1) begin
          o_cmd_wait_wd_cnt_r        <= {OUTSTAND_CNT_W+1{1'b0}};
      end
      else if (nmi_restart_r == 1'b1) begin
          o_cmd_wait_wd_cnt_r        <= {OUTSTAND_CNT_W+1{1'b0}};
      end
      else if (o_cmd_wait_wd_cnt_ena == 1'b1) begin
          o_cmd_wait_wd_cnt_r        <= o_cmd_wait_wd_cnt_nxt;
      end
    end

    wire o_cmd_wait_wd = (rw_ibp_cmd_chnl_valid & (~rw_ibp_cmd_chnl[CMD_CHNL_READ])) | (~o_cmd_wait_wd_cnt_udf);

    assign byp_wo_ibp_wd_chnl_accept  = rw_ibp_wd_chnl_accept & o_cmd_wait_wd;
    assign rw_ibp_wd_chnl_valid       = byp_wo_ibp_wd_chnl_valid & o_cmd_wait_wd;
    assign rw_ibp_wd_chnl             = byp_wo_ibp_wd_chnl;

    assign wo_ibp_wrsp_chnl_valid          = rw_ibp_wrsp_chnl_valid;
    assign wo_ibp_wrsp_chnl                = rw_ibp_wrsp_chnl;
    assign rw_ibp_wrsp_chnl_accept         = wo_ibp_wrsp_chnl_accept;
  end//}

  else begin:ro_is_ful_ibp_gen //{
   // Pass it through here
    npuarc_biu_preprc_ibp_bypbuf
  #(

    .THROUGH_MODE (0),
    .OUTSTAND_NUM   (OUTSTAND_NUM  ),
    .OUTSTAND_CNT_W (OUTSTAND_CNT_W),
    .CMD_CHNL_READ          (CMD_CHNL_READ          ),
    .CMD_CHNL_WRAP          (CMD_CHNL_WRAP          ),
    .CMD_CHNL_DATA_SIZE_LSB (CMD_CHNL_DATA_SIZE_LSB ),
    .CMD_CHNL_DATA_SIZE_W   (CMD_CHNL_DATA_SIZE_W   ),
    .CMD_CHNL_BURST_SIZE_LSB(CMD_CHNL_BURST_SIZE_LSB),
    .CMD_CHNL_BURST_SIZE_W  (CMD_CHNL_BURST_SIZE_W  ),
    .CMD_CHNL_PROT_LSB      (CMD_CHNL_PROT_LSB      ),
    .CMD_CHNL_PROT_W        (CMD_CHNL_PROT_W        ),
    .CMD_CHNL_CACHE_LSB     (CMD_CHNL_CACHE_LSB     ),
    .CMD_CHNL_CACHE_W       (CMD_CHNL_CACHE_W       ),
    .CMD_CHNL_LOCK          (CMD_CHNL_LOCK          ),
    .CMD_CHNL_EXCL          (CMD_CHNL_EXCL          ),
    .CMD_CHNL_ADDR_LSB      (CMD_CHNL_ADDR_LSB      ),
    .CMD_CHNL_ADDR_W        (CMD_CHNL_ADDR_W        ),
    .CMD_CHNL_W             (CMD_CHNL_W             ),

    .WD_CHNL_LAST           (WD_CHNL_LAST           ),
    .WD_CHNL_DATA_LSB       (WD_CHNL_DATA_LSB       ),
    .WD_CHNL_DATA_W         (WD_CHNL_DATA_W         ),
    .WD_CHNL_MASK_LSB       (WD_CHNL_MASK_LSB       ),
    .WD_CHNL_MASK_W         (WD_CHNL_MASK_W         ),
    .WD_CHNL_W              (WD_CHNL_W              ),

    .RD_CHNL_ERR_RD         (RD_CHNL_ERR_RD         ),
    .RD_CHNL_RD_EXCL_OK     (RD_CHNL_RD_EXCL_OK     ),
    .RD_CHNL_RD_LAST        (RD_CHNL_RD_LAST        ),
    .RD_CHNL_RD_DATA_LSB    (RD_CHNL_RD_DATA_LSB    ),
    .RD_CHNL_RD_DATA_W      (RD_CHNL_RD_DATA_W      ),
    .RD_CHNL_W              (RD_CHNL_W              ),

    .WRSP_CHNL_WR_DONE      (WRSP_CHNL_WR_DONE      ),
    .WRSP_CHNL_WR_EXCL_DONE (WRSP_CHNL_WR_EXCL_DONE ),
    .WRSP_CHNL_ERR_WR       (WRSP_CHNL_ERR_WR       ),
    .WRSP_CHNL_W            (WRSP_CHNL_W            ),

    .RGON_W(1),
    .USER_W(USER_W),
    // The stage FIFO entries
    .CMD_CHNL_FIFO_DEPTH   (1),
    .WDATA_CHNL_FIFO_DEPTH (1),
    .RDATA_CHNL_FIFO_DEPTH (0),
    .WRESP_CHNL_FIFO_DEPTH (0)
    ) u_biu_preprc_ibp_bypbuf (
      .i_ibp_cmd_chnl_rgon(1'b1),
      .i_ibp_cmd_chnl_user(ro_ibp_cmd_chnl_user),
// leda B_1011 off
// leda WV951025 off
// LMD: Port is not completely connected
// LJ: unused in this instantiation
// spyglass disable_block W287b
// SMD: Instance output port is not connected
// SJ: No care about the warning
      .o_ibp_cmd_chnl_rgon(),
      .ibp_buffer_idle (),
// spyglass enable_block W287b
// leda B_1011 on
// leda WV951025 on
      .o_ibp_cmd_chnl_user(rw_ibp_cmd_chnl_user),

      .i_ibp_cmd_chnl_valid   (ro_ibp_cmd_chnl_valid  ),
      .i_ibp_cmd_chnl_accept  (ro_ibp_cmd_chnl_accept ),
      .i_ibp_cmd_chnl         (ro_ibp_cmd_chnl        ),
      .i_ibp_rd_chnl_valid    (ro_ibp_rd_chnl_valid   ),
      .i_ibp_rd_chnl_accept   (ro_ibp_rd_chnl_accept  ),
      .i_ibp_rd_chnl          (ro_ibp_rd_chnl         ),
      .i_ibp_wd_chnl_valid    (ro_ibp_wd_chnl_valid   ),
      .i_ibp_wd_chnl_accept   (ro_ibp_wd_chnl_accept  ),
      .i_ibp_wd_chnl          (ro_ibp_wd_chnl         ),
      .i_ibp_wrsp_chnl_valid  (ro_ibp_wrsp_chnl_valid ),
      .i_ibp_wrsp_chnl_accept (ro_ibp_wrsp_chnl_accept),
      .i_ibp_wrsp_chnl        (ro_ibp_wrsp_chnl       ),

      .o_ibp_cmd_chnl_valid   (rw_ibp_cmd_chnl_valid  ),
      .o_ibp_cmd_chnl_accept  (rw_ibp_cmd_chnl_accept ),
      .o_ibp_cmd_chnl         (rw_ibp_cmd_chnl        ),
      .o_ibp_rd_chnl_valid    (rw_ibp_rd_chnl_valid   ),
      .o_ibp_rd_chnl_accept   (rw_ibp_rd_chnl_accept  ),
      .o_ibp_rd_chnl          (rw_ibp_rd_chnl         ),
      .o_ibp_wd_chnl_valid    (rw_ibp_wd_chnl_valid   ),
      .o_ibp_wd_chnl_accept   (rw_ibp_wd_chnl_accept  ),
      .o_ibp_wd_chnl          (rw_ibp_wd_chnl         ),
      .o_ibp_wrsp_chnl_valid  (rw_ibp_wrsp_chnl_valid ),
      .o_ibp_wrsp_chnl_accept (rw_ibp_wrsp_chnl_accept),
      .o_ibp_wrsp_chnl        (rw_ibp_wrsp_chnl       ),

      .clk  (clk),
      .nmi_restart_r (nmi_restart_r ),
      .rst_a(rst_a)
    );

    assign wo_ibp_cmd_chnl_accept = 1'b0;
    assign wo_ibp_rd_chnl_valid   = 1'b0;
    assign wo_ibp_rd_chnl = {RD_CHNL_W{1'b0}};
    assign wo_ibp_wd_chnl_accept = 1'b0;
    assign wo_ibp_wrsp_chnl_valid = 1'b0;
    assign wo_ibp_wrsp_chnl = {WRSP_CHNL_W{1'b0}};
  end//}
endgenerate//}


endmodule //biu_preprc_ibp_rwmerg
