// Library ARC_Trace-3.0.999999999
// Copyright (C) 2017 Synopsys, Inc. All rights reserved.
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
//   rtt_cstm_encapsulation
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_cstm_encapsulation.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_cstm_encapsulation (
rtt_clk,
rst_a,

cstm_en,
p0_csts_en,
atb_syncreq,
resource_full,
rfm_rcode,
exception,
exception_rtn,
pr0_inst_commit,
flush_cmd,
flush_done,

timestamp,
cstimestamp,

cst_msg_valid,
cst_msg
);

input rtt_clk;
input rst_a;

input cstm_en;
input p0_csts_en;
input atb_syncreq;
input resource_full;
input [`npuarc_RCODE_WDT-1:0] rfm_rcode;
input exception;
input exception_rtn;
input pr0_inst_commit;
input flush_cmd;
input flush_done;
input [`npuarc_TSTAMP_WDT-1:0] timestamp;
input [`npuarc_CST_WDT-1:0]    cstimestamp;

output cst_msg_valid;
output [`npuarc_CSTM_WDT-1:0] cst_msg;

wire cst_msg_valid;
reg [`npuarc_CSTM_WDT-1:0] cst_msg;

wire [5:0] tcode;

wire [7:0] cstm_mdo [9:0];
wire [1:0] cstm_mseo[9:0];

reg flush;
reg flush_d1;
wire flush_in;

/**************************************************/
//flush - flag to indicate active flush operation
/**************************************************/
always @ (posedge rtt_clk or posedge rst_a)
  begin : FLUSH_PROC
    if(rst_a == 1'b1)
      flush <= 1'b0;
    else if(flush_done)
      flush <= 1'b0;
    else if(flush_cmd)
      flush <= 1'b1;
  end

// Edge detect
always @ (posedge rtt_clk or posedge rst_a)
  begin : FLUSH_PROC_D1
    if(rst_a == 1'b1)
      flush_d1 <= 1'b0;
    else if(flush_done)
      flush_d1 <= 1'b0;
    else if(flush)
      flush_d1 <= 1'b1;
  end

assign flush_in = flush && ~flush_d1;

//Message valid signal
assign cst_msg_valid =  cstm_en && p0_csts_en && ((resource_full && (rfm_rcode==4'b1000)) || exception || atb_syncreq || flush_in ||
(exception_rtn && pr0_inst_commit));

//Message type encoding
assign tcode = 6'd61;

//---------------------
//ERROR MESSAGE
//---------------------

assign cstm_mdo[0] = {cstimestamp[1:0],tcode[5:0]};
assign cstm_mdo[1] =  ~|cstimestamp[63:2] ? timestamp[7:0] : cstimestamp[9:2];
assign cstm_mdo[2] =  ~|cstimestamp[63:2] ? 8'b0 : ~|cstimestamp[63:10] ? timestamp[7:0] : cstimestamp[17:10];
assign cstm_mdo[3] =  ~|cstimestamp[63:2] ? 8'b0 : ~|cstimestamp[63:10] ? 8'b0 : ~|cstimestamp[63:18] ? timestamp[7:0] : cstimestamp[25:18];
assign cstm_mdo[4] =  ~|cstimestamp[63:2] ? 8'b0 : ~|cstimestamp[63:10] ? 8'b0 : ~|cstimestamp[63:18] ? 8'b0 : ~|cstimestamp[63:26] ? timestamp[7:0] : cstimestamp[33:26];
assign cstm_mdo[5] =  ~|cstimestamp[63:2] ? 8'b0 : ~|cstimestamp[63:10] ? 8'b0 : ~|cstimestamp[63:18] ? 8'b0 : ~|cstimestamp[63:26] ? 8'b0 : ~|cstimestamp[63:34] ? timestamp[7:0] : cstimestamp[41:34];
assign cstm_mdo[6] =  ~|cstimestamp[63:2] ? 8'b0 : ~|cstimestamp[63:10] ? 8'b0 : ~|cstimestamp[63:18] ? 8'b0 : ~|cstimestamp[63:26] ? 8'b0 : ~|cstimestamp[63:34] ? 8'b0 : ~|cstimestamp[63:42] ? timestamp[7:0] : cstimestamp[49:42];
assign cstm_mdo[7] =  ~|cstimestamp[63:2] ? 8'b0 : ~|cstimestamp[63:10] ? 8'b0 : ~|cstimestamp[63:18] ? 8'b0 : ~|cstimestamp[63:26] ? 8'b0 : ~|cstimestamp[63:34] ? 8'b0 : ~|cstimestamp[63:42] ? 8'b0 : ~|cstimestamp[63:50] ? timestamp[7:0] : cstimestamp[57:50];
assign cstm_mdo[8] =  ~|cstimestamp[63:2] ? 8'b0 : ~|cstimestamp[63:10] ? 8'b0 : ~|cstimestamp[63:18] ? 8'b0 : ~|cstimestamp[63:26] ? 8'b0 : ~|cstimestamp[63:34] ? 8'b0 : ~|cstimestamp[63:42] ? 8'b0 : ~|cstimestamp[63:50] ? 8'b0 : ~|cstimestamp[63:58] ? timestamp[7:0] : {2'b0,cstimestamp[63:58]};
assign cstm_mdo[9] =  ~|cstimestamp[63:2] ? 8'b0 : ~|cstimestamp[63:10] ? 8'b0 : ~|cstimestamp[63:18] ? 8'b0 : ~|cstimestamp[63:26] ? 8'b0 : ~|cstimestamp[63:34] ? 8'b0 : ~|cstimestamp[63:42] ? 8'b0 : ~|cstimestamp[63:50] ? 8'b0 : ~|cstimestamp[63:58] ? 8'b0: timestamp[7:0];

assign cstm_mseo[0] =  ~|cstimestamp[63:2] ? 2'b01 : 2'b00;
assign cstm_mseo[1] =  ~|cstimestamp[63:2] ? 2'b11 : ~|cstimestamp[63:10] ? 2'b01 : 2'b00;
assign cstm_mseo[2] =  ~|cstimestamp[63:2] ? 2'b00 : ~|cstimestamp[63:10] ? 2'b11 : ~|cstimestamp[63:18] ? 2'b01 : 2'b00;
assign cstm_mseo[3] =  ~|cstimestamp[63:2] ? 2'b00 : ~|cstimestamp[63:10] ? 2'b00 : ~|cstimestamp[63:18] ? 2'b11 : ~|cstimestamp[63:26] ? 2'b01 : 2'b00;
assign cstm_mseo[4] =  ~|cstimestamp[63:2] ? 2'b00 : ~|cstimestamp[63:10] ? 2'b00 : ~|cstimestamp[63:18] ? 2'b00 : ~|cstimestamp[63:26] ? 2'b11 : ~|cstimestamp[63:34] ? 2'b01 : 2'b00;
assign cstm_mseo[5] =  ~|cstimestamp[63:2] ? 2'b00 : ~|cstimestamp[63:10] ? 2'b00 : ~|cstimestamp[63:18] ? 2'b00 : ~|cstimestamp[63:26] ? 2'b00 : ~|cstimestamp[63:34] ? 2'b11 : ~|cstimestamp[63:42] ? 2'b01 : 2'b00;
assign cstm_mseo[6] =  ~|cstimestamp[63:2] ? 2'b00 : ~|cstimestamp[63:10] ? 2'b00 : ~|cstimestamp[63:18] ? 2'b00 : ~|cstimestamp[63:26] ? 2'b00 : ~|cstimestamp[63:34] ? 2'b00 : ~|cstimestamp[63:42] ? 2'b11 : ~|cstimestamp[63:50] ? 2'b01 : 2'b00;
assign cstm_mseo[7] =  ~|cstimestamp[63:2] ? 2'b00 : ~|cstimestamp[63:10] ? 2'b00 : ~|cstimestamp[63:18] ? 2'b00 : ~|cstimestamp[63:26] ? 2'b00 : ~|cstimestamp[63:34] ? 2'b00 : ~|cstimestamp[63:42] ? 2'b00 : ~|cstimestamp[63:50] ? 2'b11 : ~|cstimestamp[63:58] ? 2'b01 : 2'b00;
assign cstm_mseo[8] =  ~|cstimestamp[63:2] ? 2'b00 : ~|cstimestamp[63:10] ? 2'b00 : ~|cstimestamp[63:18] ? 2'b00 : ~|cstimestamp[63:26] ? 2'b00 : ~|cstimestamp[63:34] ? 2'b00 : ~|cstimestamp[63:42] ? 2'b00 : ~|cstimestamp[63:50] ? 2'b00 : ~|cstimestamp[63:58] ? 2'b11 : 2'b01;
assign cstm_mseo[9] =  ~|cstimestamp[63:2] ? 2'b00 : ~|cstimestamp[63:10] ? 2'b00 : ~|cstimestamp[63:18] ? 2'b00 : ~|cstimestamp[63:26] ? 2'b00 : ~|cstimestamp[63:34] ? 2'b00 : ~|cstimestamp[63:42] ? 2'b00 : ~|cstimestamp[63:50] ? 2'b00 : ~|cstimestamp[63:58] ? 2'b00 : 2'b11;

always @*
  begin : CST_MSG_PROC
    cst_msg [7:0]   = cstm_mdo[0];
    cst_msg [17:10] = cstm_mdo[1];
    cst_msg [27:20] = cstm_mdo[2];
    cst_msg [37:30] = cstm_mdo[3];
    cst_msg [47:40] = cstm_mdo[4];
    cst_msg [57:50] = cstm_mdo[5];
    cst_msg [67:60] = cstm_mdo[6];
    cst_msg [77:70] = cstm_mdo[7];
    cst_msg [87:80] = cstm_mdo[8];
    cst_msg [97:90] = cstm_mdo[9];
    cst_msg [9:8]   = cstm_mseo[0];
    cst_msg [19:18] = cstm_mseo[1];
    cst_msg [29:28] = cstm_mseo[2];
    cst_msg [39:38] = cstm_mseo[3];
    cst_msg [49:48] = cstm_mseo[4];
    cst_msg [59:58] = cstm_mseo[5];
    cst_msg [69:68] = cstm_mseo[6];
    cst_msg [79:78] = cstm_mseo[7];
    cst_msg [89:88] = cstm_mseo[8];
    cst_msg [99:98] = cstm_mseo[9];
  end

endmodule
