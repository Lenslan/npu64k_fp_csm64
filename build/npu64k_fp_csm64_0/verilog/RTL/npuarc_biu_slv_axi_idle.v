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
//  AXI IDLE detector
//
// ===========================================================================
//
// Configuration-dependent macro definitions
//
// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_biu_slv_axi_idle
  (
  input  bus_clk_en,

  input  axi_arvalid,
  input  axi_arready,

  input  axi_awvalid,
  input  axi_awready,

  input  axi_rvalid,
  input  axi_rready,
  input  axi_rlast,

  input  axi_wvalid,
  input  axi_wready,
  input  axi_wlast,

  input  axi_bvalid,
  input  axi_bready,

  output axi_idle,

  input  clk,  // clock signal
  input  nmi_restart_r, // NMI reset signal
  input  rst_a // reset signal
  );


// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning
localparam OUT_CMD_CNT_W  = 10;
localparam OUT_CMD_NUM  = 1024;


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
//
// Count how much of the write commands outstanding
reg [OUT_CMD_CNT_W-1:0] wait_w_cnt_r;
wire wait_w_cnt_ovf;
wire wait_w_cnt_udf;
assign wait_w_cnt_ovf = (wait_w_cnt_r == $unsigned(OUT_CMD_NUM));
assign wait_w_cnt_udf = (wait_w_cnt_r == {OUT_CMD_CNT_W{1'b0}});
// The ibp wr cmd counter increased when a write trsancation going
wire wait_w_cnt_inc = bus_clk_en & axi_awvalid & axi_awready;
// The ibp wr cmd counter decreased when a IBP write response sent back
wire wait_w_cnt_dec = bus_clk_en & axi_wvalid & axi_wready & axi_wlast;
wire wait_w_cnt_ena = (wait_w_cnt_inc | wait_w_cnt_dec);
wire [OUT_CMD_CNT_W-1:0] wait_w_cnt_nxt =
      ( wait_w_cnt_inc & (~wait_w_cnt_dec)) ? (wait_w_cnt_r + 1'b1)
    : (~wait_w_cnt_inc &  wait_w_cnt_dec) ? (wait_w_cnt_r - 1'b1)
    : wait_w_cnt_r ;

// spyglass disable_block Ar_asyncdeassert01
// SMD: domain mismatch for cnt_r
// SJ: rtt_clk, clk are all same clock domain

// spyglass disable_block Ar_unsync01
// SMD: different clock domain synchronizer for cnt_r
// SJ: rtt_clk, clk are all same clock domain

// spyglass disable_block Reset_sync02
// SMD: ResetInDomain, from mcip_clk to clk
// SJ: rtt_clk, clk are all same clock domain
always @(posedge clk or posedge rst_a)
begin : wait_w_cnt_DFFEAR_PROC
  if (rst_a == 1'b1) begin
      wait_w_cnt_r        <= {OUT_CMD_CNT_W{1'b0}};
  end
  else if (nmi_restart_r == 1'b1) begin
      wait_w_cnt_r        <= {OUT_CMD_CNT_W{1'b0}};
  end
  else if (wait_w_cnt_ena == 1'b1) begin
      wait_w_cnt_r        <= wait_w_cnt_nxt;
  end
end
// spyglass enable_block Ar_asyncdeassert01
// spyglass enable_block Ar_unsync01
// spyglass enable_block Reset_sync02

reg wait_cmd_r;
wire wait_cmd_nxt = (bus_clk_en & axi_wvalid & axi_wready & ~(axi_awvalid & axi_awready) & wait_w_cnt_udf) ?
                      1'b1 : (bus_clk_en & axi_awvalid & axi_awready) ? 1'b0 : wait_cmd_r;

always @(posedge clk or posedge rst_a)
begin : wait_cmd_DFFEAR_PROC
  if (rst_a == 1'b1) begin
      wait_cmd_r        <= 1'b0;
  end
  else if (nmi_restart_r == 1'b1) begin
      wait_cmd_r        <= 1'b0;
  end
  else begin
      wait_cmd_r        <= wait_cmd_nxt;
  end
end

//
//
// Count how much of the write commands outstanding
reg [OUT_CMD_CNT_W-1:0] aw_cnt_r;
wire aw_cnt_ovf;
wire aw_cnt_udf;
assign aw_cnt_ovf = (aw_cnt_r == $unsigned(OUT_CMD_NUM));
assign aw_cnt_udf = (aw_cnt_r == {OUT_CMD_CNT_W{1'b0}});
// The ibp wr cmd counter increased when a write trsancation going
wire aw_cnt_inc = bus_clk_en & axi_awvalid & axi_awready;
// The ibp wr cmd counter decreased when a IBP write response sent back
wire aw_cnt_dec = axi_bvalid & bus_clk_en & axi_bready;
wire aw_cnt_ena = (aw_cnt_inc | aw_cnt_dec);
wire [OUT_CMD_CNT_W-1:0] aw_cnt_nxt =
      ( aw_cnt_inc & (~aw_cnt_dec)) ? (aw_cnt_r + 1'b1)
    : (~aw_cnt_inc &  aw_cnt_dec) ? (aw_cnt_r - 1'b1)
    : aw_cnt_r ;

always @(posedge clk or posedge rst_a)
begin : aw_cnt_DFFEAR_PROC
  if (rst_a == 1'b1) begin
      aw_cnt_r        <= {OUT_CMD_CNT_W{1'b0}};
  end
  else if (nmi_restart_r == 1'b1) begin
      aw_cnt_r        <= {OUT_CMD_CNT_W{1'b0}};
  end
  else if (aw_cnt_ena == 1'b1) begin
      aw_cnt_r        <= aw_cnt_nxt;
  end
end
//

// Count how much of the read commands outstanding
reg [OUT_CMD_CNT_W-1:0] ar_cnt_r;
wire ar_cnt_ovf;
wire ar_cnt_udf;
assign ar_cnt_ovf = (ar_cnt_r == $unsigned(OUT_CMD_NUM));
assign ar_cnt_udf = (ar_cnt_r == {OUT_CMD_CNT_W{1'b0}});
// The ibp_rd cmd counter increased when a IBP read command accepted
wire ar_cnt_inc = bus_clk_en & axi_arvalid & axi_arready;
// The ibp_rd cmd counter decreased when a IBP read response (last) sent back to ibp
wire ar_cnt_dec = axi_rvalid & bus_clk_en & axi_rready & axi_rlast;
wire ar_cnt_ena = (ar_cnt_inc | ar_cnt_dec ) ;
wire [OUT_CMD_CNT_W-1:0] ar_cnt_nxt =
      ( ar_cnt_inc & (~ar_cnt_dec)) ? (ar_cnt_r + 1'b1)
    : (~ar_cnt_inc &  ar_cnt_dec) ? (ar_cnt_r - 1'b1)
    : ar_cnt_r ;

always @(posedge clk or posedge rst_a)
begin : ar_cnt_DFFEAR_PROC
  if (rst_a == 1'b1) begin
      ar_cnt_r        <= {OUT_CMD_CNT_W{1'b0}};
  end
  else if (nmi_restart_r == 1'b1) begin
      ar_cnt_r        <= {OUT_CMD_CNT_W{1'b0}};
  end
  else if (ar_cnt_ena == 1'b1) begin
      ar_cnt_r        <= ar_cnt_nxt;
  end
end
//
// leda B_3200 on
// leda W484 on
// leda BTTF_D002 on
// leda B_3219 on


assign axi_idle = (aw_cnt_udf & ar_cnt_udf & wait_w_cnt_udf) & (~axi_arvalid) & (~axi_awvalid) & (~axi_wvalid) & (~wait_cmd_r);

// spyglass enable_block W528

endmodule
