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
//   rtt_pc_encapsulation
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_pc_encapsulation.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_pc_encapsulation #(parameter PCM_WDT_PP = 70, parameter PC_PP = 31) (

rtt_clk,

sys_reset,

pr_num,

pr0_filter_pc,
pr0_inst_commit,
ptc_msg_valid,
exception,
interrupt,
zd_loop,

timestamp,

pc_msg_valid,
pc_msg

);

input rtt_clk;

input sys_reset;
input [`npuarc_PRNUM_WDT-1:0] pr_num;

input [PC_PP-1:0] pr0_filter_pc;
input pr0_inst_commit;
input ptc_msg_valid;
input exception;
input interrupt;
input zd_loop;

input [`npuarc_TSTAMP_WDT-1:0]timestamp;

output pc_msg_valid;
output [PCM_WDT_PP-1:0] pc_msg;

reg [PCM_WDT_PP-1:0] pc_msg;
wire pc_msg_valid;
wire [5:0] tcode;
wire [`npuarc_PRNUM_WDT-1:0]src;
wire [`npuarc_TSTAMP_WDT-1:0] time_stamp;

wire [4:0] sync;

wire [7:0] pc_mdo_nons [6:0];
wire [1:0] pc_mseo_nons[6:0];
wire first_pc_msg;
wire [30:0] pr0_filter_pc_i;

reg first_pc_msg_r;

assign first_pc_msg = pr0_inst_commit || zd_loop || exception ||interrupt;

/**************************************************/
//Conditions for generating PC message
//1. First commit signal after the filters
//2. Zero-delay loop detected
//3. Exception occured
//4. Interrupt occured
/**************************************************/
always @ (posedge rtt_clk or posedge sys_reset)
  begin : FIRST_PC_MSG_R_PROC
    if(sys_reset == 1'b1)
      first_pc_msg_r <= 1'b0;
    else if(ptc_msg_valid)
      first_pc_msg_r <= 1'b0;
    else if(first_pc_msg)
      first_pc_msg_r <= 1'b1;
  end

//PC assignment
generate if (PC_PP != 31) begin: pad_pc_1
assign pr0_filter_pc_i = {{(31-PC_PP){1'b0}},pr0_filter_pc};
end else begin: pad_pc_0
assign pr0_filter_pc_i = pr0_filter_pc;
end
endgenerate

//Message valid signal
assign pc_msg_valid = first_pc_msg && (!first_pc_msg_r);

//SYNC code
assign sync = 5'd5;

//Message type encoding
assign tcode = 6'd9;

//Core/Producer number in multi-core configuration
assign src = pr_num;
assign time_stamp = timestamp;

//---------------------
//PC-SYNC MESSAGE
//---------------------

assign pc_mdo_nons[0] = {sync[1:0],tcode[5:0]};
assign pc_mdo_nons[1] = {3'b000,2'b00,sync[4:2]};
assign pc_mdo_nons[2] = pr0_filter_pc_i[7:0];
assign pc_mdo_nons[3] = ~|pr0_filter_pc_i[30:8] ?  time_stamp : pr0_filter_pc_i[15:8];
assign pc_mdo_nons[4] = ~|pr0_filter_pc_i[30:8] ?  2'b00 : ~|pr0_filter_pc_i[30:16] ? time_stamp : pr0_filter_pc_i[23:16];
assign pc_mdo_nons[5] = ~|pr0_filter_pc_i[30:8] ?  2'b00 : ~|pr0_filter_pc_i[30:16] ? 2'b00 : ~|pr0_filter_pc_i[30:24] ? time_stamp : {1'b0,pr0_filter_pc_i[30:24]};
assign pc_mdo_nons[6] = ~|pr0_filter_pc_i[30:8] ?  2'b00 : ~|pr0_filter_pc_i[30:16] ? 2'b00 : ~|pr0_filter_pc_i[30:24] ? 2'b00 : time_stamp;

assign pc_mseo_nons[0] = 2'b00;
assign pc_mseo_nons[1] = 2'b01;
assign pc_mseo_nons[2] = ~|pr0_filter_pc_i[30:8] ?  2'b01 : 2'b00;
assign pc_mseo_nons[3] = ~|pr0_filter_pc_i[30:8] ?  2'b11 : ~|pr0_filter_pc_i[30:16] ?  2'b01 : 2'b00;
assign pc_mseo_nons[4] = ~|pr0_filter_pc_i[30:8] ?  2'b00 : ~|pr0_filter_pc_i[30:16] ? 2'b11 : ~|pr0_filter_pc_i[30:24] ?  2'b01 : 2'b00;
assign pc_mseo_nons[5] = ~|pr0_filter_pc_i[30:8] ?  2'b00 : ~|pr0_filter_pc_i[30:16] ? 2'b00 : ~|pr0_filter_pc_i[30:24] ? 2'b11 : 2'b01;
assign pc_mseo_nons[6] = ~|pr0_filter_pc_i[30:8] ?  2'b00 : ~|pr0_filter_pc_i[30:16] ? 2'b00 : ~|pr0_filter_pc_i[30:24] ? 2'b00 : 2'b11;

always @ *
  begin : PC_MSG_PROC
    pc_msg [7:0] = pc_mdo_nons[0];
    pc_msg [17:10] = pc_mdo_nons[1];
    pc_msg [27:20] = pc_mdo_nons[2];
    pc_msg [37:30] = pc_mdo_nons[3];
    pc_msg [47:40] = pc_mdo_nons[4];
    pc_msg [57:50] = pc_mdo_nons[5];
    pc_msg [67:60] = pc_mdo_nons[6];
    pc_msg [9:8] = pc_mseo_nons[0];
    pc_msg [19:18] = pc_mseo_nons[1];
    pc_msg [29:28] = pc_mseo_nons[2];
    pc_msg [39:38] = pc_mseo_nons[3];
    pc_msg [49:48] = pc_mseo_nons[4];
    pc_msg [59:58] = pc_mseo_nons[5];
    pc_msg [69:68] = pc_mseo_nons[6];
  end

endmodule
