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
//   rtt_daqm_encapsulation
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_daqm_encapsulation.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_swe_daqm_encapsulation (

p0_msg_en,
ext_num,

timestamp,
datain_val,
datain,

msg_valid,
msg
);


input wire p0_msg_en;
input wire [7:0] ext_num;
input wire [`npuarc_TSTAMP_WDT-1:0] timestamp;
input wire datain_val;
input wire [33-1:0] datain;

output wire msg_valid;
output reg [80-1:0] msg;


wire [5:0] tcode;
wire [3:0]  idtag;
assign idtag = {3'b0,datain[33-1]};

wire [31:0] sqdata;
assign sqdata = {datain[31:0]};
wire [7:0] msg_mdo [7:0];
wire [1:0] msg_mseo[7:0];




//Message valid signal
assign msg_valid =  datain_val && p0_msg_en;

//Message type encoding
assign tcode = 6'd7;

//---------------------
// DATA ACQUISITION MESSAGE
//---------------------

assign msg_mdo[0] = {idtag[1:0],tcode[5:0]};
assign msg_mdo[1] = {ext_num[5:0],idtag[3:2]};
assign msg_mdo[2] =  ~|ext_num[7:6] ? sqdata[7:0] : {6'b0,ext_num[7:6]};
assign msg_mdo[3] =  ~|ext_num[7:6] ? ~|sqdata[31:8] ? timestamp[7:0] : sqdata[15:8] : sqdata[7:0];
assign msg_mdo[4] =  ~|ext_num[7:6] ? ~|sqdata[31:8] ? 8'b0 : ~|sqdata[31:16] ? timestamp[7:0] : sqdata[23:16] : ~|sqdata[31:8] ? timestamp[7:0] : sqdata[15:8];
assign msg_mdo[5] =  ~|ext_num[7:6] ? ~|sqdata[31:8] ? 8'b0 : ~|sqdata[31:16] ? 8'b0 : ~|sqdata[31:24] ? timestamp[7:0] : sqdata[31:24] : ~|sqdata[31:8] ? 8'b0 : ~|sqdata[31:16] ? timestamp[7:0] : sqdata[23:16];
assign msg_mdo[6] =  ~|ext_num[7:6] ? ~|sqdata[31:8] ? 8'b0 : ~|sqdata[31:16] ? 8'b0 : ~|sqdata[31:24] ? 8'b0 : timestamp[7:0] : ~|sqdata[31:8] ? 8'b0 : ~|sqdata[31:16] ? 8'b0 : ~|sqdata[31:24] ? timestamp[7:0] : sqdata[31:24];
assign msg_mdo[7] =  ~|ext_num[7:6] ? 8'b0 : ~|sqdata[31:8] ? 8'b0 : ~|sqdata[31:8] ? 8'b0 : ~|sqdata[31:16] ? 8'b0 : ~|sqdata[31:24] ? 8'b0 : timestamp[7:0];

assign msg_mseo[0] =  2'b00;
assign msg_mseo[1] =  ~|ext_num[7:6] ? 2'b01 : 2'b00;
assign msg_mseo[2] =  ~|ext_num[7:6] ? ~|sqdata[31:8] ? 2'b01 : 2'b00 : 2'b01;
assign msg_mseo[3] =  ~|ext_num[7:6] ? ~|sqdata[31:8] ? 2'b11 : ~|sqdata[31:16] ? 2'b01 : 2'b00 : ~|sqdata[31:8] ? 2'b01 : 2'b00;
assign msg_mseo[4] =  ~|ext_num[7:6] ? ~|sqdata[31:8] ? 2'b00 : ~|sqdata[31:16] ? 2'b11 : ~|sqdata[31:24] ? 2'b01 : 2'b00 : ~|sqdata[31:8] ? 2'b11 : ~|sqdata[31:16] ? 2'b01 : 2'b00;
assign msg_mseo[5] =  ~|ext_num[7:6] ? ~|sqdata[31:8] ? 2'b00 : ~|sqdata[31:16] ? 2'b00 : ~|sqdata[31:24] ? 2'b11 : 2'b01 : ~|sqdata[31:8] ? 2'b00 : ~|sqdata[31:16] ? 2'b11 : ~|sqdata[31:24] ? 2'b01 : 2'b00;
assign msg_mseo[6] =  ~|ext_num[7:6] ? ~|sqdata[31:8] ? 2'b00 : ~|sqdata[31:16] ? 2'b00 : ~|sqdata[31:24] ? 2'b00 : 2'b11 : ~|sqdata[31:8] ? 2'b00 : ~|sqdata[31:16] ? 2'b00 : ~|sqdata[31:24] ? 2'b11 : 2'b01;
assign msg_mseo[7] =  ~|ext_num[7:6] ? 2'b00 : ~|sqdata[31:8] ? 2'b00 : ~|sqdata[31:16] ? 2'b00 : ~|sqdata[31:24] ? 2'b00 : 2'b11;

always @*
  begin : MSG_PROC
    msg[0 +:8] = msg_mdo[0];
    msg[10+:8] = msg_mdo[1];
    msg[20+:8] = msg_mdo[2];
    msg[30+:8] = msg_mdo[3];
    msg[40+:8] = msg_mdo[4];
    msg[50+:8] = msg_mdo[5];
    msg[60+:8] = msg_mdo[6];
    msg[70+:8] = msg_mdo[7];
    msg[8 +:2] = msg_mseo[0];
    msg[18+:2] = msg_mseo[1];
    msg[28+:2] = msg_mseo[2];
    msg[38+:2] = msg_mseo[3];
    msg[48+:2] = msg_mseo[4];
    msg[58+:2] = msg_mseo[5];
    msg[68+:2] = msg_mseo[6];
    msg[78+:2] = msg_mseo[7];
  end
endmodule
