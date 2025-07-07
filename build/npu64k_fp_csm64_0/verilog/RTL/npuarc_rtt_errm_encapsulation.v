// Library ARC_Trace-3.0.999999999
// Copyright (C) 2012-2016 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   rtt_errm_encapsulation
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_errm_encapsulation.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_errm_encapsulation (

rtt_clk,

sys_reset,
pr_num,
msg_type_lost,
msg_type_lost_r,
msg_type_recovered,

timestamp,

err_msg_valid,
err_msg

);


input rtt_clk;

input sys_reset;
input [`npuarc_PRNUM_WDT-1:0] pr_num;

input [`npuarc_MSG_TYPE_LOST_WDT-1:0] msg_type_lost;
input [`npuarc_MSG_TYPE_LOST_WDT-1:0] msg_type_recovered;
input [`npuarc_TSTAMP_WDT-1:0]timestamp;

output reg [`npuarc_MSG_TYPE_LOST_WDT-1:0] msg_type_lost_r;
output err_msg_valid;
output [`npuarc_ERRM_WDT-1:0] err_msg;

reg [`npuarc_ERRM_WDT-1:0] err_msg;
wire [`npuarc_MSG_TYPE_LOST_WDT-1:0] msg_type_lost_s;

wire err_msg_valid;
wire [5:0] tcode;
wire [`npuarc_PRNUM_WDT-1:0]src;
wire [`npuarc_TSTAMP_WDT-1:0] time_stamp;
wire [`npuarc_ETYPE_WDT-1:0] etype;

wire [7:0] errm_mdo [4:0];
wire [1:0] errm_mseo[4:0];

/**************************************************/
//msg_type_lost_r bus holds the information corresponding to the type of message lost
//due to buffer overflow condition corresponding to the that particular message type.
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin :MSG_TYPE_LOST_R_PROC
    if(sys_reset == 1'b1)
      msg_type_lost_r <= `npuarc_MSG_TYPE_LOST_WDT'd0;
    else
      msg_type_lost_r <= (msg_type_lost_r | msg_type_lost) & (~msg_type_recovered);
  end

//Message valid signal
assign err_msg_valid = |((~msg_type_lost_r) & msg_type_lost);

//Message type encoding
assign tcode = 6'd8;

//Core/Producer number in multi-core configuration
assign src = pr_num;

//Error code,hard-coded to zero to indicate the buffer overflow condition.
assign etype =`npuarc_ETYPE_WDT'b0;
assign time_stamp = timestamp;
assign  msg_type_lost_s = (~msg_type_lost_r & msg_type_lost);

//---------------------
//ERROR MESSAGE
//---------------------

assign errm_mdo[0] = {etype[1:0],tcode[5:0]};
assign errm_mdo[1] = {msg_type_lost_s[5:2],(msg_type_lost_s[1] || msg_type_lost_s[10]),msg_type_lost_s[0],etype[3:2]};
assign errm_mdo[2] = {time_stamp[1:0],msg_type_lost_s[11],3'b0,(msg_type_lost_s[9] || msg_type_lost_s[8] || msg_type_lost_s[7]),msg_type_lost_s[6]};
assign errm_mdo[3] = {2'b0,time_stamp[7:2]};
assign errm_mdo[4] = 8'b0;
assign errm_mseo[0] = 2'b00;
assign errm_mseo[1] = 2'b00;
assign errm_mseo[2] = |time_stamp[7:2] ? 2'b00 : 2'b11;
assign errm_mseo[3] = |time_stamp[7:2] ? 2'b11 : 2'b00;
assign errm_mseo[4] = 2'b00;



always @*
  begin : ERR_MSG_PROC
    err_msg [7:0] = errm_mdo[0];
    err_msg [17:10] = errm_mdo[1];
    err_msg [27:20] = errm_mdo[2];
    err_msg [37:30] = errm_mdo[3];
    err_msg [47:40] = errm_mdo[4];
    err_msg [9:8] = errm_mseo[0];
    err_msg [19:18] = errm_mseo[1];
    err_msg [29:28] = errm_mseo[2];
    err_msg [39:38] = errm_mseo[3];
    err_msg [49:48] = errm_mseo[4];
  end

endmodule
