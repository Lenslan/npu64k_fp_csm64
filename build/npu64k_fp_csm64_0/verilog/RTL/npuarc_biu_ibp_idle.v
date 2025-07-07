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
//  Idle checker
//
// ===========================================================================
//
// Description:
//  This module check if the ibp is idle
//  Only 1 oustanding allowed
//
// ===========================================================================
// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"

// Set simulation timescale
//
`include "const.def"
module npuarc_biu_ibp_idle
  #(

  parameter OUTSTAND_CNT_W  = 4,
  parameter OUTSTAND_NUM  = 16
    )
  (
  ////////////
  // The "i_xxx" bus is the one IBP in
  output i_ibp_idle,//Any transaction accepted
  //
  // command channel
  input  i_ibp_cmd_chnl_valid,
  input  i_ibp_cmd_chnl_accept,
  input  i_ibp_cmd_chnl_read,
  //
  // read data channel
  // This module do not support rd_abort
  input  i_ibp_rd_chnl_valid,
  input  i_ibp_rd_chnl_accept,
  input  i_ibp_rd_chnl_last,
  //
  // write response channel
  input  i_ibp_wrsp_chnl_valid,
  input  i_ibp_wrsp_chnl_accept,
  ////////
  input  clk,  // clock signal
  input  nmi_restart_r,  // NMI reset signal
  input  rst_a // reset signal
  );

// spyglass disable_block W528
// SMD: Variable set but not read
// SJ: No care about the warning




//
// Count how much of the write commands outstanding
reg [OUTSTAND_CNT_W:0] out_wr_cmd_cnt_r;
wire out_wr_cmd_cnt_ovf;
wire out_wr_cmd_cnt_udf;
assign out_wr_cmd_cnt_ovf = (out_wr_cmd_cnt_r == $unsigned(OUTSTAND_NUM));
assign out_wr_cmd_cnt_udf = (out_wr_cmd_cnt_r == {OUTSTAND_CNT_W+1{1'b0}});
// The ibp wr cmd counter increased when a write trsancation going
wire out_wr_cmd_cnt_inc = i_ibp_cmd_chnl_valid & i_ibp_cmd_chnl_accept & (~i_ibp_cmd_chnl_read);
// The ibp wr cmd counter decreased when a IBP write response sent back
wire out_wr_cmd_cnt_dec = i_ibp_wrsp_chnl_valid & i_ibp_wrsp_chnl_accept;
wire out_wr_cmd_cnt_ena = (out_wr_cmd_cnt_inc | out_wr_cmd_cnt_dec);
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
wire [OUTSTAND_CNT_W:0] out_wr_cmd_cnt_nxt =
      ( out_wr_cmd_cnt_inc & (~out_wr_cmd_cnt_dec)) ? (out_wr_cmd_cnt_r + 1'b1)
    : (~out_wr_cmd_cnt_inc &  out_wr_cmd_cnt_dec) ? (out_wr_cmd_cnt_r - 1'b1)
    : out_wr_cmd_cnt_r ;
// leda B_3219 on
// leda B_3200 on
// leda W484 on
// leda BTTF_D002 on

always @(posedge clk or posedge rst_a)
begin : out_wr_cmd_cnt_DFFEAR_PROC
  if (rst_a == 1'b1) begin
      out_wr_cmd_cnt_r        <= {OUTSTAND_CNT_W+1{1'b0}};
  end
  else if (nmi_restart_r == 1'b1) begin
      out_wr_cmd_cnt_r        <= {OUTSTAND_CNT_W+1{1'b0}};
  end
  else if (out_wr_cmd_cnt_ena == 1'b1) begin
      out_wr_cmd_cnt_r        <= out_wr_cmd_cnt_nxt;
  end
end
//

// Count how much of the read commands outstanding
reg [OUTSTAND_CNT_W:0] out_rd_cmd_cnt_r;
wire out_rd_cmd_cnt_ovf;
wire out_rd_cmd_cnt_udf;
assign out_rd_cmd_cnt_ovf = (out_rd_cmd_cnt_r == $unsigned(OUTSTAND_NUM));
assign out_rd_cmd_cnt_udf = (out_rd_cmd_cnt_r == {OUTSTAND_CNT_W+1{1'b0}});
// The ibp_rd cmd counter increased when a IBP read command accepted
wire out_rd_cmd_cnt_inc = i_ibp_cmd_chnl_valid & i_ibp_cmd_chnl_accept & i_ibp_cmd_chnl_read;
// The ibp_rd cmd counter decreased when a IBP read response (last) sent back to ibp
wire out_rd_cmd_cnt_dec = i_ibp_rd_chnl_valid & i_ibp_rd_chnl_accept & i_ibp_rd_chnl_last;
wire out_rd_cmd_cnt_ena = (out_rd_cmd_cnt_inc | out_rd_cmd_cnt_dec ) ;
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
wire [OUTSTAND_CNT_W:0] out_rd_cmd_cnt_nxt =
      ( out_rd_cmd_cnt_inc & (~out_rd_cmd_cnt_dec)) ? (out_rd_cmd_cnt_r + 1'b1)
    : (~out_rd_cmd_cnt_inc &  out_rd_cmd_cnt_dec) ? (out_rd_cmd_cnt_r - 1'b1)
    : out_rd_cmd_cnt_r ;
// leda B_3219 on
// leda B_3200 on
// leda W484 on
// leda BTTF_D002 on

always @(posedge clk or posedge rst_a)
begin : out_rd_cmd_cnt_DFFEAR_PROC
  if (rst_a == 1'b1) begin
      out_rd_cmd_cnt_r        <= {OUTSTAND_CNT_W+1{1'b0}};
  end
  else if (nmi_restart_r == 1'b1) begin
      out_rd_cmd_cnt_r        <= {OUTSTAND_CNT_W+1{1'b0}};
  end
  else if (out_rd_cmd_cnt_ena == 1'b1) begin
      out_rd_cmd_cnt_r        <= out_rd_cmd_cnt_nxt;
  end
end
//
assign i_ibp_idle = (out_wr_cmd_cnt_udf & out_rd_cmd_cnt_udf);


// spyglass enable_block W528

endmodule
