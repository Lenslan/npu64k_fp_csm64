// Library ARC_Trace-3.0.999999999
// Copyright (C) 2012-2016 Synopsys, Inc. All rights reserved.
//
// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   rtt_swe_source_buf_arbitrator
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_swe_source_buf_arbitrator.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_swe_source_buf_arbitrator
(
rtt_clk,
rst_a,

rtt_time_stamp_en,
flush_done,
ptcm_done,
sbarb_done,

sbuf_empty,

data_in0,
data_in1,
data_in2,
data_in3,
data_in4,
data_in5,
data_in6,
data_in7,
data_in8,
data_in9,
data_in10,
data_in11,
data_in12,
data_in13,
data_in14,
data_in15,
data_in16,
data_in17,
data_in18,
data_in19,

msg_seq_order_q_rd_en,
msg_seq_order_q_rdata,  

arb_src0,
arb_src1,
arb_src2,
arb_val,

atb_sbuf_ack,
atb_sbuf_rden
);

localparam TSTAMP_SIZE= `npuarc_TSTAMP_WDT+`npuarc_TSTAMP_OF_WDT;
localparam TSCELLCNT_SIZE= 5;
localparam TSTAMP_INFOSIZE= TSCELLCNT_SIZE;
localparam SRC_ARB_PIPELINE= 0;
localparam FILL_SIZE= 5;

input rtt_clk;
input rst_a;

input rtt_time_stamp_en;
input flush_done;
input ptcm_done;
output sbarb_done;

input [180-1:0] data_in0;
input [180-1:0] data_in1;
input [180-1:0] data_in2;
input [180-1:0] data_in3;
input [180-1:0] data_in4;
input [180-1:0] data_in5;
input [180-1:0] data_in6;
input [180-1:0] data_in7;
input [180-1:0] data_in8;
input [180-1:0] data_in9;
input [180-1:0] data_in10;
input [180-1:0] data_in11;
input [180-1:0] data_in12;
input [180-1:0] data_in13;
input [180-1:0] data_in14;
input [180-1:0] data_in15;
input [180-1:0] data_in16;
input [180-1:0] data_in17;
input [180-1:0] data_in18;
input [180-1:0] data_in19;

input [20-1:0]  msg_seq_order_q_rdata;  
output wire     msg_seq_order_q_rd_en;

input [20-1:0] sbuf_empty;

output [180-1:0] arb_src0;
output [180-1:0] arb_src1;
output [180-1:0] arb_src2;
output [2:0] arb_val;

input [2:0] atb_sbuf_ack;
output [20-1:0] atb_sbuf_rden;

wire [180-1:0] data_in_ts0;
wire [180-1:0] data_in_ts1;
wire [180-1:0] data_in_ts2;
wire [180-1:0] data_in_ts3;
wire [180-1:0] data_in_ts4;
wire [180-1:0] data_in_ts5;
wire [180-1:0] data_in_ts6;
wire [180-1:0] data_in_ts7;
wire [180-1:0] data_in_ts8;
wire [180-1:0] data_in_ts9;
wire [180-1:0] data_in_ts10;
wire [180-1:0] data_in_ts11;
wire [180-1:0] data_in_ts12;
wire [180-1:0] data_in_ts13;
wire [180-1:0] data_in_ts14;
wire [180-1:0] data_in_ts15;
wire [180-1:0] data_in_ts16;
wire [180-1:0] data_in_ts17;
wire [180-1:0] data_in_ts18;
wire [180-1:0] data_in_ts19;

wire [TSCELLCNT_SIZE-1:0] ts_cell[20-1:0];

wire [20-1:0] req_int_p;
wire                    req_int_p_act;
wire [20-1:0] req;

reg  [20-1:0] arb_hit0;
reg  [20-1:0] arb_hit1;
reg  [20-1:0] arb_hit2;
wire [20-1:0] arb_hit0_ns;
wire [20-1:0] arb_hit1_ns;
wire [20-1:0] arb_hit2_ns;
wire [180-1:0] arb_src0in;
wire [180-1:0] arb_src1in;
wire [180-1:0] arb_src2in;
reg  [180-1:0] arb_src0_pre;
reg  [180-1:0] arb_src1_pre;
reg  [180-1:0] arb_src2_pre;
reg  [180-1:0] arb_src0;
reg  [180-1:0] arb_src1;
reg  [180-1:0] arb_src2;
reg  arb_val0;
reg  arb_val1;
reg  arb_val2;

wire [2:0] arb_val;

wire [2:0] atb_sbuf_ack;
wire [20-1:0] atb_ack_hit;
wire [20-1:0] atb_sbuf_rden;
reg  [20-1:0] rdin_val;
reg  sbarb_done;


assign ts_cell[0] = timestamp_info_tcode27(data_in0);
assign ts_cell[1] = timestamp_info_tcode8(data_in1);
assign ts_cell[2] = timestamp_info_7_3(data_in2);
assign ts_cell[3] = timestamp_info_7_3(data_in3);
assign ts_cell[4] = timestamp_info_7_3(data_in4);
assign ts_cell[5] = timestamp_info_7_3(data_in5);
assign ts_cell[6] = timestamp_info_7_3(data_in6);
assign ts_cell[7] = timestamp_info_7_3(data_in7);
assign ts_cell[8] = timestamp_info_7_3(data_in8);
assign ts_cell[9] = timestamp_info_7_3(data_in9);
assign ts_cell[10] = timestamp_info_7_3(data_in10);
assign ts_cell[11] = timestamp_info_7_3(data_in11);
assign ts_cell[12] = timestamp_info_7_3(data_in12);
assign ts_cell[13] = timestamp_info_7_3(data_in13);
assign ts_cell[14] = timestamp_info_7_3(data_in14);
assign ts_cell[15] = timestamp_info_7_3(data_in15);
assign ts_cell[16] = timestamp_info_7_3(data_in16);
assign ts_cell[17] = timestamp_info_7_3(data_in17);
assign ts_cell[18] = timestamp_info_7_3(data_in18);
assign ts_cell[19] = timestamp_info_9_1(data_in19);

assign req[0] = ~sbuf_empty[0];
assign req[1] = ~sbuf_empty[1];
assign req[2] = ~sbuf_empty[2];
assign req[3] = ~sbuf_empty[3];
assign req[4] = ~sbuf_empty[4];
assign req[5] = ~sbuf_empty[5];
assign req[6] = ~sbuf_empty[6];
assign req[7] = ~sbuf_empty[7];
assign req[8] = ~sbuf_empty[8];
assign req[9] = ~sbuf_empty[9];
assign req[10] = ~sbuf_empty[10];
assign req[11] = ~sbuf_empty[11];
assign req[12] = ~sbuf_empty[12];
assign req[13] = ~sbuf_empty[13];
assign req[14] = ~sbuf_empty[14];
assign req[15] = ~sbuf_empty[15];
assign req[16] = ~sbuf_empty[16];
assign req[17] = ~sbuf_empty[17];
assign req[18] = ~sbuf_empty[18];
assign req[19] = ~sbuf_empty[19];

assign atb_ack_hit = ({20{atb_sbuf_ack[0]}} & arb_hit0)|
               ({20{atb_sbuf_ack[1]}} & arb_hit1)|
               ({20{atb_sbuf_ack[2]}} & arb_hit2);


always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL0_REG
    if(rst_a == 1'b1)
      rdin_val[0] <= 1'b0;
    else if (atb_ack_hit[0] & sbuf_empty[0])
      rdin_val[0] <= 1'b0;
    else if (~rdin_val[0] && atb_sbuf_rden[0])
      rdin_val[0] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL1_REG
    if(rst_a == 1'b1)
      rdin_val[1] <= 1'b0;
    else if (atb_ack_hit[1] & sbuf_empty[1])
      rdin_val[1] <= 1'b0;
    else if (~rdin_val[1] && atb_sbuf_rden[1])
      rdin_val[1] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL2_REG
    if(rst_a == 1'b1)
      rdin_val[2] <= 1'b0;
    else if (atb_ack_hit[2] & sbuf_empty[2])
      rdin_val[2] <= 1'b0;
    else if (~rdin_val[2] && atb_sbuf_rden[2])
      rdin_val[2] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL3_REG
    if(rst_a == 1'b1)
      rdin_val[3] <= 1'b0;
    else if (atb_ack_hit[3] & sbuf_empty[3])
      rdin_val[3] <= 1'b0;
    else if (~rdin_val[3] && atb_sbuf_rden[3])
      rdin_val[3] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL4_REG
    if(rst_a == 1'b1)
      rdin_val[4] <= 1'b0;
    else if (atb_ack_hit[4] & sbuf_empty[4])
      rdin_val[4] <= 1'b0;
    else if (~rdin_val[4] && atb_sbuf_rden[4])
      rdin_val[4] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL5_REG
    if(rst_a == 1'b1)
      rdin_val[5] <= 1'b0;
    else if (atb_ack_hit[5] & sbuf_empty[5])
      rdin_val[5] <= 1'b0;
    else if (~rdin_val[5] && atb_sbuf_rden[5])
      rdin_val[5] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL6_REG
    if(rst_a == 1'b1)
      rdin_val[6] <= 1'b0;
    else if (atb_ack_hit[6] & sbuf_empty[6])
      rdin_val[6] <= 1'b0;
    else if (~rdin_val[6] && atb_sbuf_rden[6])
      rdin_val[6] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL7_REG
    if(rst_a == 1'b1)
      rdin_val[7] <= 1'b0;
    else if (atb_ack_hit[7] & sbuf_empty[7])
      rdin_val[7] <= 1'b0;
    else if (~rdin_val[7] && atb_sbuf_rden[7])
      rdin_val[7] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL8_REG
    if(rst_a == 1'b1)
      rdin_val[8] <= 1'b0;
    else if (atb_ack_hit[8] & sbuf_empty[8])
      rdin_val[8] <= 1'b0;
    else if (~rdin_val[8] && atb_sbuf_rden[8])
      rdin_val[8] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL9_REG
    if(rst_a == 1'b1)
      rdin_val[9] <= 1'b0;
    else if (atb_ack_hit[9] & sbuf_empty[9])
      rdin_val[9] <= 1'b0;
    else if (~rdin_val[9] && atb_sbuf_rden[9])
      rdin_val[9] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL10_REG
    if(rst_a == 1'b1)
      rdin_val[10] <= 1'b0;
    else if (atb_ack_hit[10] & sbuf_empty[10])
      rdin_val[10] <= 1'b0;
    else if (~rdin_val[10] && atb_sbuf_rden[10])
      rdin_val[10] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL11_REG
    if(rst_a == 1'b1)
      rdin_val[11] <= 1'b0;
    else if (atb_ack_hit[11] & sbuf_empty[11])
      rdin_val[11] <= 1'b0;
    else if (~rdin_val[11] && atb_sbuf_rden[11])
      rdin_val[11] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL12_REG
    if(rst_a == 1'b1)
      rdin_val[12] <= 1'b0;
    else if (atb_ack_hit[12] & sbuf_empty[12])
      rdin_val[12] <= 1'b0;
    else if (~rdin_val[12] && atb_sbuf_rden[12])
      rdin_val[12] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL13_REG
    if(rst_a == 1'b1)
      rdin_val[13] <= 1'b0;
    else if (atb_ack_hit[13] & sbuf_empty[13])
      rdin_val[13] <= 1'b0;
    else if (~rdin_val[13] && atb_sbuf_rden[13])
      rdin_val[13] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL14_REG
    if(rst_a == 1'b1)
      rdin_val[14] <= 1'b0;
    else if (atb_ack_hit[14] & sbuf_empty[14])
      rdin_val[14] <= 1'b0;
    else if (~rdin_val[14] && atb_sbuf_rden[14])
      rdin_val[14] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL15_REG
    if(rst_a == 1'b1)
      rdin_val[15] <= 1'b0;
    else if (atb_ack_hit[15] & sbuf_empty[15])
      rdin_val[15] <= 1'b0;
    else if (~rdin_val[15] && atb_sbuf_rden[15])
      rdin_val[15] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL16_REG
    if(rst_a == 1'b1)
      rdin_val[16] <= 1'b0;
    else if (atb_ack_hit[16] & sbuf_empty[16])
      rdin_val[16] <= 1'b0;
    else if (~rdin_val[16] && atb_sbuf_rden[16])
      rdin_val[16] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL17_REG
    if(rst_a == 1'b1)
      rdin_val[17] <= 1'b0;
    else if (atb_ack_hit[17] & sbuf_empty[17])
      rdin_val[17] <= 1'b0;
    else if (~rdin_val[17] && atb_sbuf_rden[17])
      rdin_val[17] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL18_REG
    if(rst_a == 1'b1)
      rdin_val[18] <= 1'b0;
    else if (atb_ack_hit[18] & sbuf_empty[18])
      rdin_val[18] <= 1'b0;
    else if (~rdin_val[18] && atb_sbuf_rden[18])
      rdin_val[18] <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL19_REG
    if(rst_a == 1'b1)
      rdin_val[19] <= 1'b0;
    else if (atb_ack_hit[19] & sbuf_empty[19])
      rdin_val[19] <= 1'b0;
    else if (~rdin_val[19] && atb_sbuf_rden[19])
      rdin_val[19] <= 1'b1;
  end

assign atb_sbuf_rden = req & (~rdin_val | ( rdin_val & atb_ack_hit));

assign data_in_ts0 = sdata_ts_qual_rfm(data_in0,rtt_time_stamp_en);
assign data_in_ts1 = sdata_ts_qual_errm(data_in1,rtt_time_stamp_en);
assign data_in_ts2 = sdata_ts_qual(ts_cell[2],data_in2,rtt_time_stamp_en);
assign data_in_ts3 = sdata_ts_qual(ts_cell[3],data_in3,rtt_time_stamp_en);
assign data_in_ts4 = sdata_ts_qual(ts_cell[4],data_in4,rtt_time_stamp_en);
assign data_in_ts5 = sdata_ts_qual(ts_cell[5],data_in5,rtt_time_stamp_en);
assign data_in_ts6 = sdata_ts_qual(ts_cell[6],data_in6,rtt_time_stamp_en);
assign data_in_ts7 = sdata_ts_qual(ts_cell[7],data_in7,rtt_time_stamp_en);
assign data_in_ts8 = sdata_ts_qual(ts_cell[8],data_in8,rtt_time_stamp_en);
assign data_in_ts9 = sdata_ts_qual(ts_cell[9],data_in9,rtt_time_stamp_en);
assign data_in_ts10 = sdata_ts_qual(ts_cell[10],data_in10,rtt_time_stamp_en);
assign data_in_ts11 = sdata_ts_qual(ts_cell[11],data_in11,rtt_time_stamp_en);
assign data_in_ts12 = sdata_ts_qual(ts_cell[12],data_in12,rtt_time_stamp_en);
assign data_in_ts13 = sdata_ts_qual(ts_cell[13],data_in13,rtt_time_stamp_en);
assign data_in_ts14 = sdata_ts_qual(ts_cell[14],data_in14,rtt_time_stamp_en);
assign data_in_ts15 = sdata_ts_qual(ts_cell[15],data_in15,rtt_time_stamp_en);
assign data_in_ts16 = sdata_ts_qual(ts_cell[16],data_in16,rtt_time_stamp_en);
assign data_in_ts17 = sdata_ts_qual(ts_cell[17],data_in17,rtt_time_stamp_en);
assign data_in_ts18 = sdata_ts_qual(ts_cell[18],data_in18,rtt_time_stamp_en);
assign data_in_ts19 = sdata_ts_qual_cstm(ts_cell[19],data_in19,rtt_time_stamp_en);


reg [20-1:0] msg_seq_order;

always @(posedge rtt_clk or posedge rst_a)
  begin
    if(rst_a)
       msg_seq_order <= 20'b0;
    else if(msg_seq_order_q_rd_en)
       msg_seq_order <= msg_seq_order_q_rdata;
    else if(|atb_sbuf_ack)    
       msg_seq_order <= msg_seq_order & ~atb_ack_hit;
  end

assign msg_seq_order_q_rd_en = (|atb_sbuf_rden || |(rdin_val & ~atb_ack_hit)) && (~|(msg_seq_order & ~atb_ack_hit));

assign req_int_p = msg_seq_order;
assign req_int_p_act = |req_int_p;

assign arb_hit0_ns = arb_winner(req_int_p);
assign arb_hit1_ns = arb_winner(req_int_p & ~arb_hit0_ns);
assign arb_hit2_ns = arb_winner(req_int_p & ~(arb_hit0_ns|arb_hit1_ns));

always @ (posedge rtt_clk or posedge rst_a)
  begin : ARB_HIT_REG
    if(rst_a == 1'b1) begin
      arb_hit0 <= {20{1'b0}};
      arb_hit1 <= {20{1'b0}};
      arb_hit2 <= {20{1'b0}};
    end
    else begin
       arb_hit0 <= arb_hit0_ns;
       arb_hit1 <= arb_hit1_ns;
       arb_hit2 <= arb_hit2_ns;
    end
  end


assign arb_src0in = source_mx(arb_hit0_ns,data_in_ts0,data_in_ts1,data_in_ts2,data_in_ts3,data_in_ts4,data_in_ts5,data_in_ts6,data_in_ts7,data_in_ts8,data_in_ts9,data_in_ts10,data_in_ts11,data_in_ts12,data_in_ts13,data_in_ts14,data_in_ts15,data_in_ts16,data_in_ts17,data_in_ts18,data_in_ts19);
assign arb_src1in = source_mx(arb_hit1_ns,data_in_ts0,data_in_ts1,data_in_ts2,data_in_ts3,data_in_ts4,data_in_ts5,data_in_ts6,data_in_ts7,data_in_ts8,data_in_ts9,data_in_ts10,data_in_ts11,data_in_ts12,data_in_ts13,data_in_ts14,data_in_ts15,data_in_ts16,data_in_ts17,data_in_ts18,data_in_ts19);
assign arb_src2in = source_mx(arb_hit2_ns,data_in_ts0,data_in_ts1,data_in_ts2,data_in_ts3,data_in_ts4,data_in_ts5,data_in_ts6,data_in_ts7,data_in_ts8,data_in_ts9,data_in_ts10,data_in_ts11,data_in_ts12,data_in_ts13,data_in_ts14,data_in_ts15,data_in_ts16,data_in_ts17,data_in_ts18,data_in_ts19);

assign arb_val = {arb_val2,arb_val1,arb_val0};
always @ (posedge rtt_clk or posedge rst_a)
  begin : ARB_VAL0_REG
    if(rst_a == 1'b1)
      arb_val0 <= 1'b0;
    else if (|atb_sbuf_ack)
       arb_val0 <= 1'b0;
    else if (|arb_hit0_ns)
       arb_val0 <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : ARB_VAL1_REG
    if(rst_a == 1'b1)
      arb_val1 <= 1'b0;
    else if (|atb_sbuf_ack)
       arb_val1 <= 1'b0;
    else if (|arb_hit1_ns)
       arb_val1 <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : ARB_VAL2_REG
    if(rst_a == 1'b1)
      arb_val2 <= 1'b0;
    else if (|atb_sbuf_ack)
       arb_val2 <= 1'b0;
    else if (|arb_hit2_ns)
       arb_val2 <= 1'b1;
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : ARB_SRC0_PRE_REG
    if(rst_a == 1'b1)
      arb_src0_pre <= {(180){1'b0}};
    else if (req_int_p_act)
       arb_src0_pre <= arb_src0in;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : ARB_SRC1_PRE_REG
    if(rst_a == 1'b1)
      arb_src1_pre <= {(180){1'b0}};
    else if (req_int_p_act)
       arb_src1_pre <= arb_src1in;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : ARB_SRC2_PRE_REG
    if(rst_a == 1'b1)
      arb_src2_pre <= {(180){1'b0}};
    else if (req_int_p_act)
       arb_src2_pre <= arb_src2in;
  end

always @*
begin: TS_QUAL_PROC
  arb_src0 = arb_src0_pre;
  arb_src1 = arb_src1_pre;
  arb_src2 = arb_src2_pre;
end

always @ (posedge rtt_clk or posedge rst_a)
  begin : SBARB_DONE_REG
    if(rst_a == 1'b1)
      sbarb_done <= 1'b0;
    else if (flush_done)
      sbarb_done <= 1'b0;
    else if (ptcm_done)
      sbarb_done <= ((~|arb_val) && (~|rdin_val));
  end


function automatic [20-1:0] arb_winner;
input [19:0] requests;
reg [20:0] repack;
reg [20:0] unpack;
begin
  unpack = requests;
  repack = (~unpack + 21'b1) & unpack;
  arb_winner = repack;
end
endfunction

function automatic [180-1:0] source_mx;
input [20-1:0] source;
input [180-1:0] data_in0;
input [180-1:0] data_in1;
input [180-1:0] data_in2;
input [180-1:0] data_in3;
input [180-1:0] data_in4;
input [180-1:0] data_in5;
input [180-1:0] data_in6;
input [180-1:0] data_in7;
input [180-1:0] data_in8;
input [180-1:0] data_in9;
input [180-1:0] data_in10;
input [180-1:0] data_in11;
input [180-1:0] data_in12;
input [180-1:0] data_in13;
input [180-1:0] data_in14;
input [180-1:0] data_in15;
input [180-1:0] data_in16;
input [180-1:0] data_in17;
input [180-1:0] data_in18;
input [180-1:0] data_in19;
reg [180-1:0] msg;
begin
  casez(source)     // synthesis parallel_case
    20'd1 : msg = data_in0;
    20'd2 : msg = data_in1;
    20'd4 : msg = data_in2;
    20'd8 : msg = data_in3;
    20'd16 : msg = data_in4;
    20'd32 : msg = data_in5;
    20'd64 : msg = data_in6;
    20'd128 : msg = data_in7;
    20'd256 : msg = data_in8;
    20'd512 : msg = data_in9;
    20'd1024 : msg = data_in10;
    20'd2048 : msg = data_in11;
    20'd4096 : msg = data_in12;
    20'd8192 : msg = data_in13;
    20'd16384 : msg = data_in14;
    20'd32768 : msg = data_in15;
    20'd65536 : msg = data_in16;
    20'd131072 : msg = data_in17;
    20'd262144 : msg = data_in18;
    20'd524288 : msg = data_in19;
  default : msg = {180{1'b0}};
  endcase
  source_mx = msg;
end
endfunction



function automatic [180-1:0] sdata_ts_qual;
input [4:0] ts_cell_in;
input [180-1:0] data_in;
input rtt_time_stamp_en;
reg [180-1:0] sdata_ts_qual_default;
reg [180-1:0] msg;
begin
  msg = data_in;
  casez(ts_cell_in)  // synthesis parallel_case
    5'd2  : sdata_ts_qual_default = {msg[180-1:30], 11 'b1,msg[18:0]};
    5'd3  : sdata_ts_qual_default = {msg[180-1:40], 11 'b1,msg[28:0]};
    5'd4  : sdata_ts_qual_default = {msg[180-1:50], 11 'b1,msg[38:0]};
    5'd5  : sdata_ts_qual_default = {msg[180-1:60], 11 'b1,msg[48:0]};
    5'd6  : sdata_ts_qual_default = {msg[180-1:70], 11 'b1,msg[58:0]};
    5'd7  : sdata_ts_qual_default = {msg[180-1:80], 11 'b1,msg[68:0]};
    5'd8  : sdata_ts_qual_default = {msg[180-1:90], 11 'b1,msg[78:0]};
    5'd9  : sdata_ts_qual_default = {msg[180-1:100],11 'b1,msg[88:0]};
    5'd10 : sdata_ts_qual_default = {msg[180-1:110],11 'b1,msg[98:0]};
    5'd11 : sdata_ts_qual_default = {msg[180-1:120],11 'b1,msg[108:0]};
    5'd12 : sdata_ts_qual_default = {msg[180-1:130],11 'b1,msg[118:0]};
    5'd13 : sdata_ts_qual_default = {msg[180-1:140],11 'b1,msg[128:0]};
    5'd14 : sdata_ts_qual_default = {msg[180-1:150],11 'b1,msg[138:0]};
    5'd15 : sdata_ts_qual_default = {msg[180-1:160],11 'b1,msg[148:0]};
    5'd16 : sdata_ts_qual_default = {msg[180-1:170],11 'b1,msg[158:0]};
    5'd17 : sdata_ts_qual_default = {11 'b1,msg[168:0]};
    default : sdata_ts_qual_default = {180{1'b0}};
  endcase

  sdata_ts_qual = rtt_time_stamp_en ? data_in[180-1:0]: sdata_ts_qual_default;
end
endfunction

function automatic [180-1:0] sdata_ts_qual_rfm;
input [180-1:0] data_in;
input rtt_time_stamp_en;
reg [180-1:0] msg;
begin
  msg = data_in;
  sdata_ts_qual_rfm = rtt_time_stamp_en ? data_in[180-1:0]:
                                          {msg[180-1:30],18'b0000000000_11000000,msg[11:0]};
end
endfunction

function automatic [180-1:0] sdata_ts_qual_errm;
input [180-1:0] data_in;
input rtt_time_stamp_en;
reg [180-1:0] msg;
begin
  msg = data_in;
  sdata_ts_qual_errm = rtt_time_stamp_en ? data_in[180-1:0]:{msg[180-1:40],14'b0000000000_1100,msg[25:0]};
end
endfunction

function automatic [180-1:0] sdata_ts_qual_cstm;
input [4:0] ts_cell_in;
input [180-1:0] data_in;
input rtt_time_stamp_en;
reg [180-1:0] sdata_ts_qual_default;
reg [180-1:0] msg;
begin
  msg = data_in;
  casez(ts_cell_in)  // synthesis parallel_case
    5'd1  : sdata_ts_qual_default = {msg[180-1:20], 12'b0000000000_10,msg[7:0]};  // single cell msg
    5'd2  : sdata_ts_qual_default = {msg[180-1:30], 11'b0000000000_1,msg[18:0]};
    5'd3  : sdata_ts_qual_default = {msg[180-1:40], 11'b0000000000_1,msg[28:0]};
    5'd4  : sdata_ts_qual_default = {msg[180-1:50], 11'b0000000000_1,msg[38:0]};
    5'd5  : sdata_ts_qual_default = {msg[180-1:60], 11'b0000000000_1,msg[48:0]};
    5'd6  : sdata_ts_qual_default = {msg[180-1:70], 11'b0000000000_1,msg[58:0]};
    5'd7  : sdata_ts_qual_default = {msg[180-1:80], 11'b0000000000_1,msg[68:0]};
    5'd8  : sdata_ts_qual_default = {msg[180-1:90], 11'b0000000000_1,msg[78:0]};
    5'd9  : sdata_ts_qual_default ={msg[180-1:100], 11'b0000000000_1,msg[88:0]};
    default : sdata_ts_qual_default = {180{1'b0}};
  endcase
  sdata_ts_qual_cstm = rtt_time_stamp_en ? data_in[180-1:0]:sdata_ts_qual_default;
end
endfunction

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_tcode27;  //rfm
input [180-1:0] data_in;
reg [180-1:0] msg;
begin
  msg = data_in;
  timestamp_info_tcode27 = msg[29] ? 5'd2: 5'd1;
end
endfunction

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_tcode8;  //errm
input [180-1:0] data_in;
reg [180-1:0] msg;
begin
  msg = data_in;
  timestamp_info_tcode8 = msg[39] ? 5'd3: 5'd2;
end
endfunction

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_9_1;
input [180-1:0] data_in;
reg [180-1:0] msg;
reg [8 :0] m_mseo_in;
begin
  msg = data_in;
  m_mseo_in = {
    msg[99 ],
    msg[89 ],
    msg[79 ],
    msg[69 ],
    msg[59 ],
    msg[49 ],
    msg[39 ],
    msg[29 ],
    msg[19 ]};
  casez(m_mseo_in) // synthesis parallel_case
    9'd1 : timestamp_info_9_1 = 5'd1;
    9'd2 : timestamp_info_9_1 = 5'd2;
    9'd4 : timestamp_info_9_1 = 5'd3;
    9'd8 : timestamp_info_9_1 = 5'd4;
    9'd16 : timestamp_info_9_1 = 5'd5;
    9'd32 : timestamp_info_9_1 = 5'd6;
    9'd64 : timestamp_info_9_1 = 5'd7;
    9'd128 : timestamp_info_9_1 = 5'd8;
    9'd256 : timestamp_info_9_1 = 5'd9;
    default : timestamp_info_9_1 = {TSTAMP_INFOSIZE{1'b0}};
  endcase
end
endfunction

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_7_3;
input [180-1:0] data_in;
reg [180-1:0] msg;
reg [4 :0] m_mseo_in;
begin
  msg = data_in;
  m_mseo_in = {
    msg[79 ],
    msg[69 ],
    msg[59 ],
    msg[49 ],
    msg[39 ]};
  casez(m_mseo_in) // synthesis parallel_case
    5'd1 : timestamp_info_7_3 = 5'd3;
    5'd2 : timestamp_info_7_3 = 5'd4;
    5'd4 : timestamp_info_7_3 = 5'd5;
    5'd8 : timestamp_info_7_3 = 5'd6;
    5'd16 : timestamp_info_7_3 = 5'd7;
    default : timestamp_info_7_3 = {TSTAMP_INFOSIZE{1'b0}};
  endcase
end
endfunction


endmodule
