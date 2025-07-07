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
//   rtt_rfm_encapsulation
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_rfm_encapsulation.vpp
//
// ===========================================================================



`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_rfm_encapsulation (

rfm_en,
pr_num,
sys_halt_r,

i_cnt,
hist,
hist_trig,
inst_commit,
ptc_msg_valid,
pt_msg_valid,

rtt_time_stamp_en,
timestamp,

rcode,

rf_msg_valid,
rf_msg

);

//leda NTL_CON32 off

input rfm_en;
input [`npuarc_PRNUM_WDT-1:0] pr_num;
input sys_halt_r;

input [`npuarc_I_CNT-1:0] i_cnt;
input [`npuarc_HIST_WDT-1:0] hist;
input hist_trig;
input inst_commit;
input ptc_msg_valid;
input pt_msg_valid;

input rtt_time_stamp_en;
input [`npuarc_TSTAMP_WDT-1:0]timestamp;

output [`npuarc_RCODE_WDT-1:0] rcode;

output rf_msg_valid;
output [`npuarc_RFM_WDT-1:0] rf_msg;

reg [`npuarc_RFM_WDT-1:0] rf_msg;

wire rf_msg_valid;
wire [5:0] tcode;
wire [`npuarc_PRNUM_WDT-1:0]src;
wire [`npuarc_TSTAMP_WDT-1:0] time_stamp;
wire [`npuarc_RCODE_WDT-1:0] rcode;
wire [`npuarc_RDAT_WDT-1:0] rdata;

wire [7:0] rfm_mdo [6:0];
wire [1:0] rfm_mseo[6:0];

wire i_cnt_rolled;
wire i_cnt_wrap_by1;
wire rf_icnt_hist;
wire hist_qual;
wire not_pt_ptc_valid;
assign not_pt_ptc_valid = ~(pt_msg_valid || ptc_msg_valid);
assign hist_qual = hist_trig && not_pt_ptc_valid;
assign i_cnt_wrap_by1 = (&i_cnt && inst_commit);
assign i_cnt_rolled = i_cnt_wrap_by1;
assign rf_icnt_hist = i_cnt_rolled && hist_qual;
assign rf_msg_valid = rfm_en && ((i_cnt_wrap_by1 && not_pt_ptc_valid) ||
                                 hist_qual ||
                                 rf_icnt_hist || (rtt_time_stamp_en && (&time_stamp) && (~sys_halt_r)));
assign rcode = rf_icnt_hist     ? 4'b0010 :
               ((i_cnt_wrap_by1 && not_pt_ptc_valid) ? 4'b0000 : hist_qual ? 4'b0001 : 4'b1000);
assign rdata = rf_icnt_hist     ? hist[31:0] :
               (hist_qual && (!(i_cnt_wrap_by1 && not_pt_ptc_valid))) ? hist[31:0] : 32'h0;
assign time_stamp = timestamp;


assign tcode = 6'd27;
assign src = pr_num;

assign rfm_mdo[0] = {rcode[1:0],tcode[5:0]};
assign rfm_mdo[1] = {(~|rcode[2:0] ? time_stamp[5:0] : rdata[5:0]),rcode[3:2]};
assign rfm_mdo[2] = ~|rcode[2:0] ? {6'b0,time_stamp[7:6]} :(~|rdata[31:6] ? time_stamp[7:0] : rdata[13:6]);
assign rfm_mdo[3] = ~|rcode[2:0] ? 8'h00 : (~|rdata[31:6] ? 8'h00 : ~|rdata[31:14] ? time_stamp[7:0] : rdata[21:14]);
assign rfm_mdo[4] = ~|rcode[2:0] ? 8'h00 : (~|rdata[31:6] ? 8'h00 : ~|rdata[31:14] ? 8'h00 : ~|rdata[31:22] ? time_stamp[7:0] : rdata[29:22]);
assign rfm_mdo[5] = ~|rcode[2:0] ? 8'h00 : (~|rdata[31:6] ? 8'h00 : ~|rdata[31:14] ? 8'h00 : ~|rdata[31:22] ? 8'h00 : ~|rdata[31:30] ? time_stamp[7:0] : {6'b0,rdata[31:30]});
assign rfm_mdo[6] = ~|rcode[2:0] ? 8'h00 : (~|rdata[31:6] ? 8'h00 : ~|rdata[31:14] ? 8'h00 : ~|rdata[31:22] ? 8'h00 : ~|rdata[31:30] ? 8'h00 : time_stamp[7:0]);

assign rfm_mseo[0] = 2'b00;
assign rfm_mseo[1] = ~|rcode[2:0] ? (~|time_stamp[7:6] ? 2'b11 : 2'b00) : ( ~|rdata[31:6] ? 2'b01 : 2'b00);
assign rfm_mseo[2] = ~|rcode[2:0] ? (~|time_stamp[7:6] ? 2'b00 : 2'b11) : (~|rdata[31:6] ? 2'b11 : ~|rdata[31:14] ? 2'b01 : 2'b00);
assign rfm_mseo[3] = ~|rcode[2:0] ? 2'b00 : (~|rdata[31:6] ? 2'b00 : ~|rdata[31:14] ? 2'b11 : ~|rdata[31:22] ? 2'b01 : 2'b00);
assign rfm_mseo[4] = ~|rcode[2:0] ? 2'b00 : (~|rdata[31:6] ? 2'b00 : ~|rdata[31:14] ? 2'b00 : ~|rdata[31:22] ? 2'b11 : ~|rdata[31:30] ? 2'b01 : 2'b00);
assign rfm_mseo[5] = ~|rcode[2:0] ? 2'b00 : (~|rdata[31:6] ? 2'b00 : ~|rdata[31:14] ? 2'b00 : ~|rdata[31:22] ? 2'b00 : ~|rdata[31:30] ? 2'b11 : 2'b01);
assign rfm_mseo[6] = ~|rcode[2:0] ? 2'b00 : (~|rdata[31:6] ? 2'b00 : ~|rdata[31:14] ? 2'b00 : ~|rdata[31:22] ? 2'b00 : ~|rdata[31:30] ? 2'b00 : 2'b11);

always @*
  begin : RF_MSG_PROC
    rf_msg [7:0] = rfm_mdo[0];
    rf_msg [17:10] = rfm_mdo[1];
    rf_msg [27:20] = rfm_mdo[2];
    rf_msg [37:30] = rfm_mdo[3];
    rf_msg [47:40] = rfm_mdo[4];
    rf_msg [57:50] = rfm_mdo[5];
    rf_msg [67:60] = rfm_mdo[6];
    rf_msg [9:8] = rfm_mseo[0];
    rf_msg [19:18] = rfm_mseo[1];
    rf_msg [29:28] = rfm_mseo[2];
    rf_msg [39:38] = rfm_mseo[3];
    rf_msg [49:48] = rfm_mseo[4];
    rf_msg [59:58] = rfm_mseo[5];
    rf_msg [69:68] = rfm_mseo[6];
  end

//leda NTL_CON32 on

endmodule
