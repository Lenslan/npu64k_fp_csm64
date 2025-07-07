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
//   rtt_atb_source_buf_arbitrator
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_atb_source_buf_arbitrator.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_atb_source_buf_arbitrator
(
rtt_clk,
rst_a,

rtt_time_stamp_en,
flush_done,
ptcm_done,
sbarb_done,

sbuf_empty0,
sbuf_empty1,
sbuf_empty2,
sbuf_empty3,
sbuf_empty4,
sbuf_empty5,
sbuf_empty6,
sbuf_empty9,
sbuf_empty10,
sbuf_empty11,
sbuf_empty12,
sbuf_empty13,


data_in0,
data_in1,
data_in2,
data_in3,
data_in4,
data_in9,
data_in10,
data_in11,
data_in12,
data_in13,

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
localparam FILL_SIZE= 4;

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
input [180-1:0] data_in9;
input [180-1:0] data_in10;
input [180-1:0] data_in11;
input [180-1:0] data_in12;
input [180-1:0] data_in13;


input [10-1:0]  msg_seq_order_q_rdata;  
output wire     msg_seq_order_q_rd_en;

input sbuf_empty0;
input sbuf_empty1;
input sbuf_empty2;
input sbuf_empty3;
input sbuf_empty4;
input sbuf_empty5;
input sbuf_empty6;
input sbuf_empty9;
input sbuf_empty10;
input sbuf_empty11;
input sbuf_empty12;
input sbuf_empty13;

output [180-1:0] arb_src0;
output [180-1:0] arb_src1;
output [180-1:0] arb_src2;
output [2:0] arb_val;

input [2:0] atb_sbuf_ack;
output [`npuarc_NUM_MSG_SRC-1:0] atb_sbuf_rden;


wire [180-1:0] data_in0_ts;
wire [180-1:0] data_in9_ts;
wire [180-1:0] data_in1_ts;
wire [180-1:0] data_in2_ts;
wire [180-1:0] data_in3_ts;
wire [180-1:0] data_in4_ts;
wire [180-1:0] data_in10_ts;
wire [180-1:0] data_in11_ts;
wire [180-1:0] data_in12_ts;
wire [180-1:0] data_in13_ts;

wire [TSCELLCNT_SIZE-1:0] ts_cell[13:0];

wire [`npuarc_NUM_MSG_SRC-1:0] req_prio_upper_in;
wire [`npuarc_NUM_MSG_SRC-1:0] req_prio_lower_in;
wire [`npuarc_NUM_MSG_SRC-1:0] req_int_p;
wire                    req_int_p_act;
wire [`npuarc_NUM_MSG_SRC-1:0] req;

reg  [`npuarc_NUM_MSG_SRC-1:0] arb_hit0;
reg  [`npuarc_NUM_MSG_SRC-1:0] arb_hit1;
reg  [`npuarc_NUM_MSG_SRC-1:0] arb_hit2;
wire [`npuarc_NUM_MSG_SRC-1:0] arb_hit0_ns;
wire [`npuarc_NUM_MSG_SRC-1:0] arb_hit1_ns;
wire [`npuarc_NUM_MSG_SRC-1:0] arb_hit2_ns;
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
wire [`npuarc_NUM_MSG_SRC-1:0] atb_ack_hit;
wire [`npuarc_NUM_MSG_SRC-1:0] atb_sbuf_rden;
reg  sbarb_done;


assign ts_cell[0] = timestamp_info_tcode2 (data_in0);
assign ts_cell[1] = timestamp_info_tcode27(data_in1);
assign ts_cell[2] = timestamp_info_tcode8 (data_in2);
assign ts_cell[3] = timestamp_info_tcode15(data_in3);
assign ts_cell[4] = timestamp_info_6_3    (data_in4);
assign ts_cell[5] = {(TSCELLCNT_SIZE){1'b0}};
assign ts_cell[6] = {(TSCELLCNT_SIZE){1'b0}};
assign ts_cell[7] = {(TSCELLCNT_SIZE){1'b0}};
assign ts_cell[9] = timestamp_info_6_2    (data_in9);
assign ts_cell[8] = {(TSCELLCNT_SIZE){1'b0}};
assign ts_cell[10] = timestamp_info_11_4  (data_in10);
assign ts_cell[11] = timestamp_info_11_4  (data_in11);
assign ts_cell[12] = timestamp_info_tcode0(data_in12);
assign ts_cell[13] = timestamp_info_9_1(data_in13);

assign req[0] = ~sbuf_empty0;
assign req[1] = ~sbuf_empty1;
assign req[2] = ~sbuf_empty2;
assign req[3] = ~sbuf_empty3;
assign req[4] = ~sbuf_empty4;
assign req[5] = ~sbuf_empty5;
assign req[6] = ~sbuf_empty6;
assign req[7] = 1'b0;
assign req[8] = 1'b0;
assign req[9] = ~sbuf_empty9;
assign req[10] = ~sbuf_empty10;
assign req[11] = ~sbuf_empty11;
assign req[12] = ~sbuf_empty12;
assign req[13] = ~sbuf_empty13;

assign atb_ack_hit = ({`npuarc_NUM_MSG_SRC{atb_sbuf_ack[0]}} & arb_hit0)|
               ({`npuarc_NUM_MSG_SRC{atb_sbuf_ack[1]}} & arb_hit1)|
               ({`npuarc_NUM_MSG_SRC{atb_sbuf_ack[2]}} & arb_hit2);


reg rdin_val0;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL0_REG
    if(rst_a == 1'b1)
      rdin_val0 <= 1'b0;
    else if (atb_ack_hit[0] & sbuf_empty0)
      rdin_val0 <= 1'b0;
    else if (~rdin_val0 && atb_sbuf_rden[0])
      rdin_val0 <= 1'b1;
  end
reg rdin_val1;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL1_REG
    if(rst_a == 1'b1)
      rdin_val1 <= 1'b0;
    else if (atb_ack_hit[1] & sbuf_empty1)
      rdin_val1 <= 1'b0;
    else if (~rdin_val1 && atb_sbuf_rden[1])
      rdin_val1 <= 1'b1;
  end
reg rdin_val2;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL2_REG
    if(rst_a == 1'b1)
      rdin_val2 <= 1'b0;
    else if (atb_ack_hit[2] & sbuf_empty2)
      rdin_val2 <= 1'b0;
    else if (~rdin_val2 && atb_sbuf_rden[2])
      rdin_val2 <= 1'b1;
  end
reg rdin_val3;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL3_REG
    if(rst_a == 1'b1)
      rdin_val3 <= 1'b0;
    else if (atb_ack_hit[3] & sbuf_empty3)
      rdin_val3 <= 1'b0;
    else if (~rdin_val3 && atb_sbuf_rden[3])
      rdin_val3 <= 1'b1;
  end
reg rdin_val4;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL4_REG
    if(rst_a == 1'b1)
      rdin_val4 <= 1'b0;
    else if (atb_ack_hit[4] & sbuf_empty4)
      rdin_val4 <= 1'b0;
    else if (~rdin_val4 && atb_sbuf_rden[4])
      rdin_val4 <= 1'b1;
  end
reg rdin_val5;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL5_REG
    if(rst_a == 1'b1)
      rdin_val5 <= 1'b0;
    else if (atb_ack_hit[5] & sbuf_empty5)
      rdin_val5 <= 1'b0;
    else if (~rdin_val5 && atb_sbuf_rden[5])
      rdin_val5 <= 1'b1;
  end
reg rdin_val6;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL6_REG
    if(rst_a == 1'b1)
      rdin_val6 <= 1'b0;
    else if (atb_ack_hit[6] & sbuf_empty6)
      rdin_val6 <= 1'b0;
    else if (~rdin_val6 && atb_sbuf_rden[6])
      rdin_val6 <= 1'b1;
  end
reg rdin_val9;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL9_REG
    if(rst_a == 1'b1)
      rdin_val9 <= 1'b0;
    else if (atb_ack_hit[9] & sbuf_empty9)
      rdin_val9 <= 1'b0;
    else if (~rdin_val9 && atb_sbuf_rden[9])
      rdin_val9 <= 1'b1;
  end
reg rdin_val10;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL10_REG
    if(rst_a == 1'b1)
      rdin_val10 <= 1'b0;
    else if (atb_ack_hit[10] & sbuf_empty10)
      rdin_val10 <= 1'b0;
    else if (~rdin_val10 && atb_sbuf_rden[10])
      rdin_val10 <= 1'b1;
  end
reg rdin_val11;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL11_REG
    if(rst_a == 1'b1)
      rdin_val11 <= 1'b0;
    else if (atb_ack_hit[11] & sbuf_empty11)
      rdin_val11 <= 1'b0;
    else if (~rdin_val11 && atb_sbuf_rden[11])
      rdin_val11 <= 1'b1;
  end
reg rdin_val12;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL12_REG
    if(rst_a == 1'b1)
      rdin_val12 <= 1'b0;
    else if (atb_ack_hit[12] & sbuf_empty12)
      rdin_val12 <= 1'b0;
    else if (~rdin_val12 && atb_sbuf_rden[12])
      rdin_val12 <= 1'b1;
  end
reg rdin_val13;
always @ (posedge rtt_clk or posedge rst_a)
  begin : RDIN_VAL13_REG
    if(rst_a == 1'b1)
      rdin_val13 <= 1'b0;
    else if (atb_ack_hit[13] & sbuf_empty13)
      rdin_val13 <= 1'b0;
    else if (~rdin_val13 && atb_sbuf_rden[13])
      rdin_val13 <= 1'b1;
  end

assign atb_sbuf_rden = {req[`npuarc_NUM_MSG_SRC-1:9],2'b0,req[6:0]} & ({~rdin_val13,~rdin_val12, ~rdin_val11,~rdin_val10,~rdin_val9,2'b0,~rdin_val6,~rdin_val5,~rdin_val4,~rdin_val3,~rdin_val2,~rdin_val1,~rdin_val0} |
                                                                ({rdin_val13,rdin_val12, rdin_val11, rdin_val10,rdin_val9,2'b0,rdin_val6,rdin_val5,rdin_val4,rdin_val3,rdin_val2,rdin_val1,rdin_val0} & atb_ack_hit));

//leda BTTF_D002 off
//leda W484 off




assign data_in0_ts = sdata_ts_qual_otm(data_in0,rtt_time_stamp_en);
assign data_in1_ts = sdata_ts_qual_rfm(ts_cell[1],data_in1,rtt_time_stamp_en);
assign data_in2_ts = sdata_ts_qual_errm(data_in2,rtt_time_stamp_en);
assign data_in3_ts = sdata_ts_qual_wpm(ts_cell[3],data_in3,rtt_time_stamp_en);
assign data_in4_ts = sdata_ts_qual(ts_cell[4],data_in4,rtt_time_stamp_en);
assign data_in9_ts = sdata_ts_qual(ts_cell[9],data_in9,rtt_time_stamp_en);
assign data_in10_ts = sdata_ts_qual(ts_cell[10],data_in10,rtt_time_stamp_en);
assign data_in11_ts = sdata_ts_qual(ts_cell[11],data_in11,rtt_time_stamp_en);
assign data_in12_ts = sdata_ts_qual_dsm(ts_cell[12],data_in12,rtt_time_stamp_en);
assign data_in13_ts = sdata_ts_qual_cstm(ts_cell[13],data_in13,rtt_time_stamp_en);

wire [`npuarc_NUM_MSG_SRC-1:0] rdin_val;
assign rdin_val = {rdin_val13,rdin_val12, rdin_val11, rdin_val10,rdin_val9,2'b0,rdin_val6,rdin_val5,rdin_val4,rdin_val3,rdin_val2,rdin_val1,rdin_val0};

wire [`npuarc_NUM_MSG_SRC-1:0] msg_seq_order_q_rdata1; 
reg [`npuarc_NUM_MSG_SRC-1:0] msg_seq_order; 

  assign msg_seq_order_q_rdata1 = {msg_seq_order_q_rdata[9:5],4'b0,msg_seq_order_q_rdata[4:0]};

always @(posedge rtt_clk or posedge rst_a)
  begin
    if(rst_a)
       msg_seq_order <= `npuarc_NUM_MSG_SRC'b0;
    else if(msg_seq_order_q_rd_en)
       msg_seq_order <= msg_seq_order_q_rdata1;
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
      arb_hit0 <= {`npuarc_NUM_MSG_SRC{1'b0}};
      arb_hit1 <= {`npuarc_NUM_MSG_SRC{1'b0}};
      arb_hit2 <= {`npuarc_NUM_MSG_SRC{1'b0}};
    end
    else begin
       arb_hit0 <= arb_hit0_ns;
       arb_hit1 <= arb_hit1_ns;
       arb_hit2 <= arb_hit2_ns;
    end
  end

assign arb_src0in = source_mx({arb_hit0_ns[13:9],arb_hit0_ns[6:0]},data_in0_ts, data_in1_ts, data_in2_ts, data_in3_ts, data_in4_ts, data_in9_ts,
                            data_in10_ts, data_in11_ts, data_in12_ts, data_in13_ts);
assign arb_src1in = source_mx({arb_hit1_ns[13:9],arb_hit1_ns[6:0]},data_in0_ts, data_in1_ts, data_in2_ts, data_in3_ts, data_in4_ts, data_in9_ts,
                            data_in10_ts, data_in11_ts, data_in12_ts, data_in13_ts);
assign arb_src2in = source_mx({arb_hit2_ns[13:9],arb_hit2_ns[6:0]},data_in0_ts, data_in1_ts, data_in2_ts, data_in3_ts, data_in4_ts, data_in9_ts,
                            data_in10_ts, data_in11_ts, data_in12_ts, data_in13_ts);
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
      sbarb_done <= ((~|arb_val) && (~|{rdin_val13,rdin_val12, rdin_val11, rdin_val10}) && (~|{rdin_val6,rdin_val5,rdin_val4,rdin_val3,rdin_val2,rdin_val1,rdin_val0}) );
  end


function automatic [`npuarc_NUM_MSG_SRC-1:0] arb_winner;
input [13:0] requests;
//yy = 13 - 4 = 9
// y = 9 + 1 = 10
reg [9:0] repack;
reg [9:0] unpack;
begin
  unpack = {requests[13:9],requests[4:0]};  //remove unused msg types
  repack = (~unpack + 10'b1) & unpack;
  arb_winner = {repack[9:5],4'b0,repack[4:0]};
end
endfunction

function automatic [180-1:0] source_mx;
input [`npuarc_NUM_MSG_SRC-1-2:0] source;
input [180-1:0] data_in0;
input [180-1:0] data_in1;
input [180-1:0] data_in2;
input [180-1:0] data_in3;
input [180-1:0] data_in4;
input [180-1:0] data_in9;
input [180-1:0] data_in10;
input [180-1:0] data_in11;
input [180-1:0] data_in12;
input [180-1:0] data_in13;
reg [180-1:0] msg;
begin
  casez({source[`npuarc_NUM_MSG_SRC-1-2:7],source[4:0]})     // synthesis parallel_case
  10'b0000000001 : msg = data_in0;
  10'b0000000010 : msg = data_in1;
  10'b0000000100 : msg = data_in2;
  10'b0000001000 : msg = data_in3;
  10'b0000010000 : msg = data_in4;
  10'b0000100000 : msg = data_in9;
  10'b0001000000 : msg = data_in10;
  10'b0010000000 : msg = data_in11;
  10'b0100000000 : msg = data_in12;
  10'b1000000000 : msg = data_in13;
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
    default : sdata_ts_qual_default = {180{1'b0}};
  endcase

  sdata_ts_qual = rtt_time_stamp_en ? data_in[180-1:0]: sdata_ts_qual_default;
end
endfunction

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_tcode2;  //otm
input [180-1:0] data_in;
reg [180-1:0] msg;
begin
  msg = data_in;
  timestamp_info_tcode2 = msg[29] ? 5'd2: 5'd1;
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

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_tcode0;  //dsm
input [180-1:0] data_in;
reg [180-1:0] msg;
begin
  msg = data_in;
  timestamp_info_tcode0 = msg[59] ? 5'd5: msg[49] ? 5'd4: 5'd0;
end
endfunction

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_tcode15;  //wpm
input [180-1:0] data_in;
reg [180-1:0] msg;
begin
  msg = data_in;
  timestamp_info_tcode15 = msg[29] ? 5'd2: 5'd1;
end
endfunction

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_tcode27;  //rfm
input [180-1:0] data_in;
reg [180-1:0] msg;
reg [5:0] m_mseo_in;
begin
  msg = data_in;
  m_mseo_in = {msg[69],msg[59],msg[49],msg[39],msg[29],msg[19]};
  casez(m_mseo_in) // synopys parallel_case
    6'b000001 : timestamp_info_tcode27 = 5'd1;
    6'b000010 : timestamp_info_tcode27 = 5'd2;
    6'b000100 : timestamp_info_tcode27 = 5'd3;
    6'b001000 : timestamp_info_tcode27 = 5'd4;
    6'b010000 : timestamp_info_tcode27 = 5'd5;
    6'b100000 : timestamp_info_tcode27 = 5'd6;
    default   : timestamp_info_tcode27 = 5'd0;
  endcase
end
endfunction



function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_6_3;
input [180-1:0] data_in;
reg [180-1:0] msg;
reg [3 :0] m_mseo_in;
begin
  msg = data_in;
  m_mseo_in = {
    msg[69 ],
    msg[59 ],
    msg[49 ],
    msg[39 ]};
  casez(m_mseo_in) // synthesis parallel_case
    4'd1 : timestamp_info_6_3 = 5'd3;
    4'd2 : timestamp_info_6_3 = 5'd4;
    4'd4 : timestamp_info_6_3 = 5'd5;
    4'd8 : timestamp_info_6_3 = 5'd6;
    default : timestamp_info_6_3 = {TSTAMP_INFOSIZE{1'b0}};
  endcase
end
endfunction

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_12_4;
input [180-1:0] data_in;
reg [180-1:0] msg;
reg [8 :0] m_mseo_in;
begin
  msg = data_in;
  m_mseo_in = {
    msg[129 ],
    msg[119 ],
    msg[109 ],
    msg[99 ],
    msg[89 ],
    msg[79 ],
    msg[69 ],
    msg[59 ],
    msg[49 ]};
  casez(m_mseo_in) // synthesis parallel_case
    9'd1 : timestamp_info_12_4 = 5'd4;
    9'd2 : timestamp_info_12_4 = 5'd5;
    9'd4 : timestamp_info_12_4 = 5'd6;
    9'd8 : timestamp_info_12_4 = 5'd7;
    9'd16 : timestamp_info_12_4 = 5'd8;
    9'd32 : timestamp_info_12_4 = 5'd9;
    9'd64 : timestamp_info_12_4 = 5'd10;
    9'd128 : timestamp_info_12_4 = 5'd11;
    9'd256 : timestamp_info_12_4 = 5'd12;
    default : timestamp_info_12_4 = {TSTAMP_INFOSIZE{1'b0}};
  endcase
end
endfunction

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_11_4;
input [180-1:0] data_in;
reg [180-1:0] msg;
reg [7 :0] m_mseo_in;
begin
  msg = data_in;
  m_mseo_in = {
    msg[119 ],
    msg[109 ],
    msg[99 ],
    msg[89 ],
    msg[79 ],
    msg[69 ],
    msg[59 ],
    msg[49 ]};
  casez(m_mseo_in) // synthesis parallel_case
    8'd1 : timestamp_info_11_4 = 5'd4;
    8'd2 : timestamp_info_11_4 = 5'd5;
    8'd4 : timestamp_info_11_4 = 5'd6;
    8'd8 : timestamp_info_11_4 = 5'd7;
    8'd16 : timestamp_info_11_4 = 5'd8;
    8'd32 : timestamp_info_11_4 = 5'd9;
    8'd64 : timestamp_info_11_4 = 5'd10;
    8'd128 : timestamp_info_11_4 = 5'd11;
    default : timestamp_info_11_4 = {TSTAMP_INFOSIZE{1'b0}};
  endcase
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

function automatic [TSTAMP_INFOSIZE-1:0] timestamp_info_6_2;
input [180-1:0] data_in;
reg [180-1:0] msg;
reg [4 :0] m_mseo_in;
begin
  msg = data_in;
  m_mseo_in = {
    msg[69 ],
    msg[59 ],
    msg[49 ],
    msg[39 ],
    msg[29 ]};
  casez(m_mseo_in) // synthesis parallel_case
    5'd1 : timestamp_info_6_2 = 5'd2;
    5'd2 : timestamp_info_6_2 = 5'd3;
    5'd4 : timestamp_info_6_2 = 5'd4;
    5'd8 : timestamp_info_6_2 = 5'd5;
    5'd16 : timestamp_info_6_2 = 5'd6;
    default : timestamp_info_6_2 = {TSTAMP_INFOSIZE{1'b0}};
  endcase
end
endfunction


function automatic [180-1:0] sdata_ts_qual_rfm;
input [4:0] ts_cell_in;
input [180-1:0] data_in;
input rtt_time_stamp_en;
reg [180-1:0] sdata_ts_qual_default;
reg tcode_dcode;
reg [180-1:0] msg;
begin
  msg = data_in;
  tcode_dcode =({msg[10],msg[7:6]} == 3'b0);
  casez(ts_cell_in)  // synthesis parallel_case
    5'd2  : sdata_ts_qual_default = {msg[180-1:30], 11'b0000000000_1,msg[18:0]};
    5'd3  : sdata_ts_qual_default = {msg[180-1:40], 11'b0000000000_1,msg[28:0]};
    5'd4  : sdata_ts_qual_default = {msg[180-1:50], 11'b0000000000_1,msg[38:0]};
    5'd5  : sdata_ts_qual_default = {msg[180-1:60], 11'b0000000000_1,msg[48:0]};
    5'd6  : sdata_ts_qual_default = {msg[180-1:70], 11'b0000000000_1,msg[58:0]};
    default : sdata_ts_qual_default = {180{1'b0}};
  endcase
  sdata_ts_qual_rfm = rtt_time_stamp_en ? data_in[180-1:0]:
                            tcode_dcode ? {msg[180-1:30],18'b0000000000_11000000,msg[11:0]}:
                                          sdata_ts_qual_default;
end
endfunction
function automatic [180-1:0] sdata_ts_qual_wpm;
input [4:0] ts_cell_in;
input [180-1:0] data_in;
input rtt_time_stamp_en;
reg [180-1:0] msg;
begin
  msg = data_in;
  sdata_ts_qual_wpm = rtt_time_stamp_en ? data_in[180-1:0]:
                        (ts_cell_in==2) ? {msg[180-1:30],11'b0000000000_1,msg[18:0]}:
                                          {msg[180-1:20],12'b0000000000_10,msg[7:0]};
end
endfunction

function automatic [180-1:0] sdata_ts_qual_otm;
input [180-1:0] data_in;
input rtt_time_stamp_en;
reg [180-1:0] msg;
begin
  msg = data_in;
  sdata_ts_qual_otm = rtt_time_stamp_en ? data_in[180-1:0]:{msg[180-1:30],14'b0000000000_1100,msg[15:0]};
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
function automatic [180-1:0] sdata_ts_qual_dsm;
input [4:0] ts_cell_in;
input [180-1:0] data_in;
input rtt_time_stamp_en;
reg [180-1:0] msg;
begin
  msg = data_in;
  sdata_ts_qual_dsm = rtt_time_stamp_en ? data_in[180-1:0]:
                      (|ts_cell_in)     ? {msg[180-1:60],14'b0000000000_1100,msg[45:0]}:
                                          {180{1'b0}};
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

endmodule
