// Library ARC_Trace-3.0.999999999
// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
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
//   rtt_wpm_encapsulation
//
// ===========================================================================
//
// Description:
//
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_wpm_encapsulation.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_wpm_encapsulation (

pr0_watchpoint_val,

pr_num,
timestamp,

wp_msg_valid,
wp_msg

);

input  [`npuarc_PR_WP-1:0]    pr0_watchpoint_val;
input [`npuarc_PRNUM_WDT-1:0] pr_num;
input [`npuarc_TSTAMP_WDT-1:0] timestamp;

output wp_msg_valid;
output [`npuarc_WPM_WDT-1:0]wp_msg;

reg [`npuarc_WPM_WDT-1:0]wp_msg;
wire [7:0] wp_mdo [3:0] ;
wire [1:0] wp_mseo[3:0] ;
wire [5:0] tcode;
wire [`npuarc_PRNUM_WDT-1:0]src;

assign wp_msg_valid = |(pr0_watchpoint_val);
assign tcode = 6'd15;
assign src = pr_num;

assign wp_mdo[0] = {pr0_watchpoint_val[1:0],tcode[5:0]};
assign wp_mdo[1] = |pr0_watchpoint_val[7:2] ? {2'b0,pr0_watchpoint_val[7:2]} : timestamp[7:0];
assign wp_mdo[2] = |pr0_watchpoint_val[7:2] ? timestamp[7:0] : 8'b0;
assign wp_mdo[3] = 8'b0;

assign wp_mseo[0] = |pr0_watchpoint_val[7:2] ? 2'b00 : 2'b01;
assign wp_mseo[1] = |pr0_watchpoint_val[7:2] ? 2'b01 : 2'b11;
assign wp_mseo[2] = |pr0_watchpoint_val[7:2] ? 2'b11 : 2'b00;
assign wp_mseo[3] = 2'b0;

always @*
  begin :WP_MSG_PROC
    wp_msg [7:0] = wp_mdo[0];
    wp_msg [17:10] = wp_mdo[1];
    wp_msg [27:20] = wp_mdo[2];
    wp_msg [37:30] = wp_mdo[3];
    wp_msg [9:8] = wp_mseo[0];
    wp_msg [19:18] = wp_mseo[1];
    wp_msg [29:28] = wp_mseo[2];
    wp_msg [39:38] = wp_mseo[3];
  end




endmodule
