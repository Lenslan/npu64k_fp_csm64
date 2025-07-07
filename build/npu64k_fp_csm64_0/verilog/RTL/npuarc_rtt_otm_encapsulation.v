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
//   rtt_otm_encapsulation
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_otm_encapsulation.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_otm_encapsulation (
 rtt_clk,
 rst_a,

pid_wr_en,
processid,

pr_num,
timestamp,

ot_msg_valid,
ot_msg

);

input  rtt_clk;
input  rst_a;

input pid_wr_en;
input [`npuarc_RTT_PID-1:0] processid;
input [`npuarc_PRNUM_WDT-1:0] pr_num;
input [`npuarc_TSTAMP_WDT-1:0] timestamp;

output ot_msg_valid;
output [`npuarc_OTM_WDT-1:0]ot_msg;

reg [`npuarc_OTM_WDT-1:0]ot_msg;
wire [`npuarc_PRNUM_WDT-1:0]src;
wire [7:0] ot_mdo [3:0] ;
wire [1:0] ot_mseo[3:0] ;
wire [5:0] tcode;
reg pid_wr_en_r;
reg [`npuarc_RTT_PID-1:0] processid_r;

/**************************************************/
//Process ID field of OTM message.
/**************************************************/
always @ (posedge rtt_clk or posedge rst_a)
begin : PID_PROC
  if (rst_a == 1'b1) begin
   pid_wr_en_r <= 1'b0;
   processid_r <= {`npuarc_RTT_PID{1'b0}};
  end
   else begin
   pid_wr_en_r <= pid_wr_en;
   processid_r <= processid;
   end
end


//Message valid signal
assign ot_msg_valid =pid_wr_en_r;

//Message type encoding
assign tcode = 6'd2;

//Core/Producer number in multi-core configuration
assign src = pr_num;

//---------------------
//OWNER-SHIP TRACE
//---------------------

assign ot_mdo[0] = {processid_r[1:0],tcode[5:0]};
assign ot_mdo[1] = {timestamp[1:0],processid_r[7:2]};
assign ot_mdo[2] = {2'b0,timestamp[7:2]};
assign ot_mdo[3] = {8'b0};

assign ot_mseo[0] = 2'b00;
assign ot_mseo[1] = |timestamp[7:2] ? 2'b00 : 2'b11;
assign ot_mseo[2] = |timestamp[7:2] ? 2'b11 : 2'b00;
assign ot_mseo[3] = 2'b00;


always @*
  begin : OT_MSG_PROC
    ot_msg [7:0] = ot_mdo[0];
    ot_msg [17:10] = ot_mdo[1];
    ot_msg [27:20] = ot_mdo[2];
    ot_msg [37:30] = ot_mdo[3];
    ot_msg [9:8] = ot_mseo[0];
    ot_msg [19:18] = ot_mseo[1];
    ot_msg [29:28] = ot_mseo[2];
    ot_msg [39:38] = ot_mseo[3];
  end




endmodule
