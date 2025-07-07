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
//   arct_msg_parallelize
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o arct_msg_parallelize.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_atb_msg_parallelize
(
rtt_clk,
rst_a,

flush_cmd,
sbarb_done,
flush_done,
para_done,
para_busy,

sbuf_ack0,
sbuf_valid0,
sbuf_rdata0,
sbuf_ack1,
sbuf_valid1,
sbuf_rdata1,
sbuf_ack2,
sbuf_valid2,
sbuf_rdata2,

atb_fifo_req,
atb_fifo_ack,
atb_fifo_wdata
);

parameter BUMP_WDT=8;

localparam BUMP_MAX= 2**BUMP_WDT-2;
localparam BUMP_RETRY= 2**BUMP_WDT-4;
localparam [4:0] NUM_CELLS_IN_BEAT_OUT = 12;

input rtt_clk;
input rst_a;

input flush_cmd;
input sbarb_done;
input flush_done;
output para_done;
output para_busy;

output sbuf_ack0;
input  sbuf_valid0;
input [180-1:0] sbuf_rdata0;

output sbuf_ack1;
input  sbuf_valid1;
input [180-1:0] sbuf_rdata1;

output sbuf_ack2;
input  sbuf_valid2;
input [180-1:0] sbuf_rdata2;

output atb_fifo_req;
output [120-1:0] atb_fifo_wdata;
input  atb_fifo_ack;

reg  atb_fifo_req;
reg  [120-1:0] atb_fifo_wdata;
wire atb_fifo_ack;

reg  bump_req_d1;
reg  [120-1:0] atb_fifo_wdata_int;
reg  atb_fifo_req_int;
reg  atb_fifo_req_int_qual;

reg  sbuf_ack0;
reg  sbuf_ack1;
reg  sbuf_ack2;
reg  sbuf_ack0_int;
reg  sbuf_ack1_int;
reg  sbuf_ack2_int;
wire atb_fifo_accept_int;
wire atb_fifo_stalled_int;
wire atb_fifo_accept;
wire atb_fifo_stalled;

reg  [1:0] ready;                       // pipeline ready
reg  [180-1:0] m[0:2];           // source msg
reg  [1:0] token[0:2];                  // pointer to oldest source msg
reg  [1:0] token_p1[0:2];               // pipeline1 pointer to oldest source msg
wire [1:0] token_ns;
reg  [1:0] token_rid[0:2];              // reverse decode of token
reg  token0is3;                         // bump req input
reg  wd_ocpis0;                         // bump req input

reg  [180-1:0] st[0:2];          // holding reg
reg  [180-1:0] st_p1[0:2];       // pipeline1 holding reg
wire [180-1:0] st_load_in[0:2];  // holding reg next state
wire [180-1:0] st_shift_in[0:2]; // holding reg next state
reg  [2:0] st_load;                     // holding reg load enable
reg  [2:0] st_shift;                    // holding reg shift enable
wire [4:0] st_size[0:2];                // numebr of cells in holding reg
reg  [4:0] st_p1_size[0:2];             // pipeline1 numebr of cells in holding reg
wire [4:0] st_cc[0:2];                  // number of cells consumed in each holding reg
wire [4:0] st_cc2[0:2];                 // number of cells consumed in each holding reg
reg  [1:0] source_buf_vld1;
reg  [2:0] source_buf_vld2;

wire [120-1:0] stg_shiftl[0:2];  // number of cells to offset each stage for concatenation function
wire [120-1:0] stg_ord;          // Concatenate all stages
wire [4:0] stg_credits0;                // number of cells available
wire [4:0] stg_credits1;                // number of cells available
wire [5:0] stg_credits1_xx;
wire [4:0] stg_credits2;                // number of cells available
wire [5:0] stg_credits2_xx;
wire [4:0] stg_ocp[0:2];                // number of cells occupied in staging
reg  [4:0] stg_ocp_p1[0:2];             // pipeline1 number of cells occupied in staging
wire [4:0] stg_ord_ocp_int;             // number of cells occupied by stages 0 and 1
wire [5:0] stg_ord_ocp_int_xx;
reg  [4:0] stg_ord_ocp_int_p1;          // pipeline1 number of cells occupied by stages 0 and 1
wire [4:0] stg_ord_ocp_p2;              // number of cells occupied by stages 0,1, and 2
wire [5:0] stg_ord_ocp_p2_xx;

reg  [4:0] wd_ocp;                      // number of cells occupied
reg  [4:0] wd_ocp_p1;                   // pipeline1 number of cells occupied
wire [5:0] wd_ocp_p1_xx;
wire [4:0] wd_ocp_ns;
wire [5:0] wd_ocp_ns_xx;
wire [4:0] wd_ocp_bypass_p1;
wire stg_ocp_full_in;
reg  stg_ocp_full_d1;
wire stg_ocp_full;                      // beat is full
wire [4:0] wd_ocp_qual;

reg  [BUMP_WDT-1:0] bump_cnt;
wire bump_req;
wire bump_max;

wire para_done_in;
wire para_busy;
reg  para_done;

assign atb_fifo_accept_int  = atb_fifo_req_int && atb_fifo_ack;
assign atb_fifo_stalled_int = atb_fifo_req_int && ~atb_fifo_ack;
assign atb_fifo_accept      = atb_fifo_req && atb_fifo_ack;
assign atb_fifo_stalled     = atb_fifo_req && ~atb_fifo_ack;
assign bump_max = (bump_cnt==BUMP_MAX[BUMP_WDT-1:0]);
assign bump_req = bump_max && (&token_ns[0] && ~atb_fifo_stalled);

// Token points to the oldest staged msg. This msg's cells are allowed to egressed first followed by
// the next two oldest msgs' cells
always @*
  begin: TOKEN_PROC
    {token[1],token[2]} = (token[0]==2'b00) ? {2'b01,2'b10} :
                          (token[0]==2'b01) ? {2'b10,2'b00} :
                          (token[0]==2'b10) ? {2'b00,2'b01} : {2'b01,2'b10};
  // Reverse token is calculated to know which stage to reload as the token referenced entries egress.
    {token_rid[0],token_rid[1],token_rid[2]} = (token[0]==2'b00) ? {2'b00,2'b01,2'b10} :
                                               (token[0]==2'b01) ? {2'b10,2'b00,2'b01} :
                                               (token[0]==2'b10) ? {2'b01,2'b10,2'b00} : {2'b00,2'b01,2'b10};
  end

assign st_cc[0] = stg_ocp_p1[token_rid[0]];
assign st_cc[1] = stg_ocp_p1[token_rid[1]];
assign st_cc[2] = stg_ocp_p1[token_rid[2]];

assign st_cc2[0] = stg_ocp_p1[0];
assign st_cc2[1] = stg_ocp_p1[1];
assign st_cc2[2] = stg_ocp_p1[2];

reg  [2:0] src_ena[0:3];
reg  [1:0] src_ena1;
reg  [2:0] src_ena2;

always @*
  m[0] = sbuf_rdata0;

always @*
begin: ST_LOAD_PROC
  src_ena1 = 2'b00;
  src_ena2 = 3'b000;
  st_load  = 3'b000;
  source_buf_vld1= {sbuf_valid1,sbuf_valid0};
  source_buf_vld2= {sbuf_valid2,sbuf_valid1,sbuf_valid0};

  if (ready[0] && ~atb_fifo_stalled_int) begin
    st_load[0]= (st_cc[0] == st_p1_size[token_rid[0]]) ? (st_cc[1] == st_p1_size[token_rid[1]]) ? sbuf_valid0 :
                                                         (st_cc[2] == st_p1_size[token_rid[2]]) ? 1'b0 : sbuf_valid0 : 1'b0;

    source_buf_vld1 = {sbuf_valid1, (~st_load[0] & sbuf_valid0)};
    if (st_cc[1] == st_p1_size[token_rid[1]]) begin
      st_load[1]=|source_buf_vld1;
      src_ena1[0]=source_buf_vld1[0];
      src_ena1[1]=(source_buf_vld1 == 2'b10);
    end

    source_buf_vld2 = {sbuf_valid2, (~src_ena1[1] & sbuf_valid1), (~(st_load[0]|src_ena1[0]) & sbuf_valid0)};
    if (st_cc[2] == st_p1_size[token_rid[2]]) begin
    st_load[2]=|source_buf_vld2;
      casez(source_buf_vld2)
      3'b??1 : src_ena2[0]=1'b1;
      3'b?10 : src_ena2[1]=1'b1;
      3'b100 : src_ena2[2]=1'b1;
      default : src_ena2[2]=1'b0;
      endcase
    end
  end

  m[1]= st_load[0] ? sbuf_rdata1 : sbuf_rdata0;
  casez(source_buf_vld2)
  3'b??1 : m[2]=sbuf_rdata0;
  3'b?10 : m[2]=sbuf_rdata1;
  default : m[2]=sbuf_rdata2;
  endcase
  sbuf_ack0_int = st_load[0]  | src_ena1[0] | src_ena2[0];
  sbuf_ack1_int = src_ena1[1] | src_ena2[1];
  sbuf_ack2_int = src_ena2[2];
end

// 1 clk wide pulse generated acks
always @ (posedge rtt_clk or posedge rst_a)
  begin : SBUF_ACK0_P1REG
    if(rst_a == 1'b1)
      sbuf_ack0 <= 1'b0;
    else if (sbuf_ack0)
      sbuf_ack0 <= 1'b0;
    else if (~sbuf_ack0 && sbuf_ack0_int)
      sbuf_ack0 <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : SBUF_ACK1_P1REG
    if(rst_a == 1'b1)
      sbuf_ack1 <= 1'b0;
    else if (sbuf_ack1)
      sbuf_ack1 <= 1'b0;
    else if (~sbuf_ack1 && sbuf_ack1_int)
      sbuf_ack1 <= 1'b1;
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : SBUF_ACK2_P1REG
    if(rst_a == 1'b1)
      sbuf_ack2 <= 1'b0;
    else if (sbuf_ack2)
      sbuf_ack2 <= 1'b0;
    else if (~sbuf_ack2 && sbuf_ack2_int)
      sbuf_ack2 <= 1'b1;
  end

always @*
begin: ST_SHIFT_PROC
  st_shift[0] = ready[0] && |st_cc[0] && (~atb_fifo_stalled_int || atb_fifo_req_int_qual);
  st_shift[1] = ready[0] && |st_cc[1] && (~atb_fifo_stalled_int || atb_fifo_req_int_qual);
  st_shift[2] = ready[0] && |st_cc[2] && (~atb_fifo_stalled_int || atb_fifo_req_int_qual);
end

assign token_ns = (&token_p1[0] || ((st_p1_size[0]==st_cc2[0])&&(st_p1_size[1]==st_cc2[1])&&(st_p1_size[2]==st_cc2[2]))) ? // idle or consumed all holding cells
          (st_load[0] ? 2'b00 :
           st_load[1] ? 2'b01 :
           st_load[2] ? 2'b10 : 2'b11 ) :
          (|st_cc2[2] && (st_cc2[2] < st_p1_size[2])) ? token[2] :                                   // unconsumed cells from token[2], youngest of 3, so keep pointer on token[2]
          (|st_cc2[1] && (st_cc2[1] < st_p1_size[1])) ? token[1] :                                   // unconsumed cells from token[1], youngest of 2, so keep pointer on token[1]
          (|st_cc2[0] && (st_cc2[0] < st_p1_size[0])) ? token[0] :                                   // unconsumed cells from token[0], youngest of 1, so keep pointer on token[0]
          (|st_cc2[1] && (st_p1_size[1]==st_cc2[1]) && |st_p1_size[2] && ~|st_cc2[2]) ? token[2] :   // if all token[1] cells staged... check if token[2] blocked from staging
          (|st_cc2[0] && (st_p1_size[0]==st_cc2[0])) ? ((|st_p1_size[1] && ~|st_cc2[1]) ? token[1] : // if all token[0] cells staged... check if token[1] blocked from staging
                                                        (|st_p1_size[2] && ~|st_cc2[2]) ? token[2] : // else check if token[2] blocked from staging
                                                        2'b11) :  
           2'b11;

// calculate available credits in each stage based on #WD occupied cells
assign stg_credits0 = atb_fifo_req_int ? (atb_fifo_stalled ? 5'b0:NUM_CELLS_IN_BEAT_OUT) : NUM_CELLS_IN_BEAT_OUT-wd_ocp;
assign stg_ocp[0] = &token[0] ? 5'b0 : (st_size[token[0]]<=stg_credits0) ? st_size[token[0]]:stg_credits0;

// subsequent stages get the remaining credits less that consumed by previous stage
assign stg_credits1_xx = stg_credits0 - stg_ocp[0];
assign stg_credits1 = stg_credits1_xx[4:0];
assign stg_ocp[1] = (st_size[token[1]]<=stg_credits1)? st_size[token[1]]:stg_credits1;
assign stg_credits2_xx = stg_credits1 - stg_ocp[1];
assign stg_credits2 = stg_credits2_xx[4:0];
assign stg_ocp[2] = (st_size[token[2]]<=stg_credits2)? st_size[token[2]]:stg_credits2;
assign stg_ord_ocp_int_xx = stg_ocp[0]+stg_ocp[1];
assign stg_ord_ocp_int = stg_ord_ocp_int_xx[4:0];

// Stages are loaded with the next msg as their respective msg's cells egress. Each cycle, egressed cells are shifted out of staging.
// When all cells of the token'ed msg have eggressed, token is assigned to the oldest remaining stage.
assign st_load_in[0]  = ((token_ns == 2'b01) && st_load[2]) ? m[1]:m[0];
assign st_shift_in[0] = shift_cells(st_p1[token_rid[0]],st_cc[0]);

assign st_load_in[1]  = (token_ns == 2'b10) ? st_load[0] ? m[1]:m[0] : m[1];
assign st_shift_in[1] = shift_cells(st_p1[token_rid[1]],st_cc[1]);

assign st_load_in[2]  = (token_ns == 2'b01) ? m[0] : m[2];
assign st_shift_in[2] = shift_cells(st_p1[token_rid[2]],st_cc[2]);

assign st_size[0] = msg_size(st[0]);
assign st_size[1] = msg_size(st[1]);
assign st_size[2] = msg_size(st[2]);

always @ (posedge rtt_clk or posedge rst_a)
  begin : READY_REG
    if(rst_a == 1'b1)
      ready <= 2'b01;
    else if (~(atb_fifo_stalled  && atb_fifo_req_int) && (token_ns == 2'b11))
      ready <= 2'b01;
    else if (~(atb_fifo_stalled  && atb_fifo_req_int))
      ready <= {ready[0],ready[1]};
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : TOKEN_REG
    if(rst_a == 1'b1)
      token[0] <= 2'b11;
    else if (ready[0] && ~atb_fifo_stalled_int)
      token[0] <= token_ns;
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : HOLDING_REG0
    if(rst_a == 1'b1)
      st[0] <= {180{1'b0}};
    else if (st_load[0]||st_shift[0])
      st[0] <= st_load[0] ? st_load_in[0] : st_shift_in[0];
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : HOLDING_REG1
    if(rst_a == 1'b1)
      st[1] <= {180{1'b0}};
    else if (st_load[1]||st_shift[1])
      st[1] <= st_load[1] ? st_load_in[1] : st_shift_in[1];
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : HOLDING_REG2
    if(rst_a == 1'b1)
      st[2] <= {180{1'b0}};
    else if (st_load[2]||st_shift[2])
      st[2] <= st_load[2] ? st_load_in[2] : st_shift_in[2];
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : TOKEN_P1REG
    if(rst_a == 1'b1) begin
      token_p1[0] <= 2'b11;
      token_p1[1] <= 2'b01;
      token_p1[2] <= 2'b10;
    end
    else if (ready[1] && ~atb_fifo_stalled_int) begin
      token_p1[0] <= token[0];
      token_p1[1] <= token[1];
      token_p1[2] <= token[2];
    end
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : HOLDING_P1REG0
    if(rst_a == 1'b1)
      st_p1[0] <= {180{1'b0}};
    else if (ready[1])
      st_p1[0] <= st[token[0]];
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : ST_P1_SIZE_P1REG0
    if(rst_a == 1'b1)
      st_p1_size[0] <= 5'b0;
    else if (ready[1])
      st_p1_size[0] <= st_size[token[0]];
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : HOLDING_P1REG1
    if(rst_a == 1'b1)
      st_p1[1] <= {180{1'b0}};
    else if (ready[1])
      st_p1[1] <= st[token[1]];
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : ST_P1_SIZE_P1REG1
    if(rst_a == 1'b1)
      st_p1_size[1] <= 5'b0;
    else if (ready[1])
      st_p1_size[1] <= st_size[token[1]];
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : HOLDING_P1REG2
    if(rst_a == 1'b1)
      st_p1[2] <= {180{1'b0}};
    else if (ready[1])
      st_p1[2] <= st[token[2]];
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : ST_P1_SIZE_P1REG2
    if(rst_a == 1'b1)
      st_p1_size[2] <= 5'b0;
    else if (ready[1])
      st_p1_size[2] <= st_size[token[2]];
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : STG_XXX_OCP_P1_P1REG
    if(rst_a == 1'b1) begin
      stg_ocp_p1[0] <= 5'b0;
      stg_ocp_p1[1] <= 5'b0;
      stg_ocp_p1[2] <= 5'b0;
      stg_ord_ocp_int_p1 <= 5'b0;
    end
    else if (ready[1]) begin
      stg_ocp_p1[0] <= stg_ocp[0];
      stg_ocp_p1[1] <= stg_ocp[1];
      stg_ocp_p1[2] <= stg_ocp[2];
      stg_ord_ocp_int_p1 <= stg_ord_ocp_int;
    end
  end

assign stg_ord_ocp_p2_xx = stg_ord_ocp_int_p1+stg_ocp_p1[2];
assign stg_ord_ocp_p2 = stg_ord_ocp_p2_xx[4:0];

// sort msgs w/stage0 holding the oldest msg reference by token pointer
// shift each stage wrt to #WD occupied cells
assign wd_ocp_qual   = atb_fifo_req_int_qual ? 5'b0: wd_ocp_p1;
assign stg_shiftl[0] = &token_p1[0] ? {120{1'b0}} : lshift_cells(st_p1[0],wd_ocp_qual);
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self determined expression
// SJ:  Called function will enforce bitwidth truncation of sum
assign stg_shiftl[1] = lshift_cells(st_p1[1],(wd_ocp_qual+stg_ocp_p1[0]));
assign stg_shiftl[2] = lshift_cells(st_p1[2],(wd_ocp_qual+stg_ocp_p1[0])+(stg_ocp_p1[1]));
// spyglass enable_block SelfDeterminedExpr-ML

// OR the stages together keeping only the LSB 18 cells to form the incoming cells
assign stg_ord = (stg_shiftl[0]|stg_shiftl[1]|stg_shiftl[2]);

// OR incoming cells with current beat
always @ (posedge rtt_clk or posedge rst_a)
  begin : FIFO_WD_INT_REG
    if(rst_a == 1'b1)
      atb_fifo_wdata_int <= {120{1'b0}};
    else if (atb_fifo_req_int && ~atb_fifo_stalled)
      atb_fifo_wdata_int <= {120{1'b0}};
    else if (atb_fifo_req_int_qual)                             // send pending wd and latch incoming ord
      atb_fifo_wdata_int <= stg_ord;
    else if (~&token[0] && ready[0] && ~atb_fifo_req_int)       // concatenate ord value with current wd
      atb_fifo_wdata_int <= atb_fifo_wdata_int|stg_ord;
  end

assign wd_ocp_ns_xx = (stg_ord_ocp_p2 + wd_ocp_qual);
assign wd_ocp_ns= wd_ocp_ns_xx[4:0];

assign wd_ocp_bypass_p1 = stg_ord_ocp_p2;
always @ (posedge rtt_clk or posedge rst_a)
  begin : WD_OCP_REG
    if(rst_a == 1'b1)
      wd_ocp <= 5'b0;
    else if (atb_fifo_req_int && ~atb_fifo_stalled)
      wd_ocp <= 5'b0;
    else if (atb_fifo_req_int_qual)                             // send pending wd and latch incoming ord
      wd_ocp <= wd_ocp_bypass_p1;
    else if (~&token[0] && ~atb_fifo_req_int)
      wd_ocp <= wd_ocp_ns;
  end

assign wd_ocp_p1_xx = wd_ocp + stg_ord_ocp_p2;

always @ (posedge rtt_clk or posedge rst_a)
  begin : WD_OCP_PREG
    if(rst_a == 1'b1)
      wd_ocp_p1 <= 5'b0;
    else if (bump_req)
      wd_ocp_p1 <= (~&token[0] && ready[0] && ~atb_fifo_req_int) ? wd_ocp_p1_xx[4:0] : wd_ocp;
    else if (ready[1])
      wd_ocp_p1 <= (atb_fifo_req_int && ~atb_fifo_stalled) ? 5'b0 : wd_ocp;
  end

// reset bump count on req ack or when cells are occupying staging
// if already at max count then hold here
// else increment cnt if wd cells are occupied and staging is empty
always @ (posedge rtt_clk or posedge rst_a)
  begin : BUMP_CNT_REG
    if(rst_a == 1'b1)
      bump_cnt <= {BUMP_WDT{1'b0}};
    else if (atb_fifo_req_int)
      bump_cnt <= {BUMP_WDT{1'b0}};
    else if (~&bump_cnt && |wd_ocp)
      bump_cnt <= bump_cnt  + {{BUMP_WDT{1'b0}},1'b1};
    else if (&bump_cnt && ~bump_req_d1)
      bump_cnt <= BUMP_RETRY[BUMP_WDT-1:0];
  end

assign stg_ocp_full_in = (atb_fifo_req_int_qual ? wd_ocp_bypass_p1 : wd_ocp_ns)==12;
assign stg_ocp_full= ~stg_ocp_full_d1 && stg_ocp_full_in;
 always @ (posedge rtt_clk or posedge rst_a)
  begin : FULL__D1REG
    if(rst_a == 1'b1)
      stg_ocp_full_d1 <= 1'b0;
    else
      stg_ocp_full_d1 <= stg_ocp_full_in;
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : FIFO_WD_REQ_INT_REG
    if(rst_a == 1'b1)
      atb_fifo_req_int <= 1'b0;
    else if (((~bump_req_d1 || ~&token[0]) && stg_ocp_full) || (ready[0] && ~atb_fifo_req_int && ((~&token[0] && (stg_ord_ocp_p2==12)) || bump_req)))
      atb_fifo_req_int <= 1'b1;
    else if (~atb_fifo_stalled)
      atb_fifo_req_int <= 1'b0;
  end

// There are more cells instaging so keep processing next cells
always @ (posedge rtt_clk or posedge rst_a)
  begin : FIFO_WD_REQ_INT_QUAL_REG
    if(rst_a == 1'b1)
      atb_fifo_req_int_qual <= 1'b0;
    else
      atb_fifo_req_int_qual <= (atb_fifo_req_int && ~atb_fifo_stalled && ~&token[0]);
  end

//store until atready mux in idle padding
always @ (posedge rtt_clk or posedge rst_a)
  begin : BUMP_REQ_PIPE_REG
    if(rst_a == 1'b1)
      bump_req_d1 <= 1'b0;
    else if (atb_fifo_accept && ~(ready[0] && ~atb_fifo_req_int && bump_req))
      bump_req_d1 <= 1'b0;
    else
      bump_req_d1 <= (bump_req && ~stg_ocp_full);
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : WD_PIPE_REG
    if(rst_a == 1'b1)
      atb_fifo_wdata <= {120{1'b0}};
    else if (atb_fifo_req_int && ~atb_fifo_stalled)
      atb_fifo_wdata <= pad_idle(bump_req_d1, wd_ocp_p1, atb_fifo_wdata_int);
  end
always @ (posedge rtt_clk or posedge rst_a)
  begin : WD_REQ_PIPE_REG
    if(rst_a == 1'b1)
      atb_fifo_req <= 1'b0;
    else if (atb_fifo_accept && ~atb_fifo_req_int)
      atb_fifo_req <= 1'b0;
    else if (atb_fifo_req_int)
      atb_fifo_req <= 1'b1;
  end

function automatic [4:0] msg_size;      //only 1 End of messsage
input [180-1:0] msg;
reg [18-1:0] m_mseo_in;
begin
  m_mseo_in = {
    msg[17*10+9],
    msg[16*10+9],
    msg[15*10+9],
    msg[14*10+9],
    msg[13*10+9],
    msg[12*10+9],
    msg[11*10+9],
    msg[10*10+9],
    msg[9*10+9],
    msg[8*10+9],
    msg[7*10+9],
    msg[6*10+9],
    msg[5*10+9],
    msg[4*10+9],
    msg[3*10+9],
    msg[2*10+9],
    msg[1*10+9],
    msg[0*10+9]};
  casez(m_mseo_in)
  18'd1 : msg_size = 5'd1;
  18'd2 : msg_size = 5'd2;
  18'd4 : msg_size = 5'd3;
  18'd8 : msg_size = 5'd4;
  18'd16 : msg_size = 5'd5;
  18'd32 : msg_size = 5'd6;
  18'd64 : msg_size = 5'd7;
  18'd128 : msg_size = 5'd8;
  18'd256 : msg_size = 5'd9;
  18'd512 : msg_size = 5'd10;
  18'd1024 : msg_size = 5'd11;
  18'd2048 : msg_size = 5'd12;
  18'd4096 : msg_size = 5'd13;
  18'd8192 : msg_size = 5'd14;
  18'd16384 : msg_size = 5'd15;
  18'd32768 : msg_size = 5'd16;
  18'd65536 : msg_size = 5'd17;
  18'd131072 : msg_size = 5'd18;
  default : msg_size = 5'd0;
  endcase
end
endfunction

function automatic [120-1:0] pad_idle;
input bump_req;
input [4:0] cells_consumed;
input [120-1:0] data_in;
reg [120-1:0] idle_cells;
begin
  casez(cells_consumed)
  5'd1 :idle_cells = {{(120-20 ){1'b1}},10'h3_AA, data_in[0+:10]};
  5'd2 :idle_cells = {{(120-30 ){1'b1}},10'h3_AA, data_in[0+:20]};
  5'd3 :idle_cells = {{(120-40 ){1'b1}},10'h3_AA, data_in[0+:30]};
  5'd4 :idle_cells = {{(120-50 ){1'b1}},10'h3_AA, data_in[0+:40]};
  5'd5 :idle_cells = {{(120-60 ){1'b1}},10'h3_AA, data_in[0+:50]};
  5'd6 :idle_cells = {{(120-70 ){1'b1}},10'h3_AA, data_in[0+:60]};
  5'd7 :idle_cells = {{(120-80 ){1'b1}},10'h3_AA, data_in[0+:70]};
  5'd8 :idle_cells = {{(120-90 ){1'b1}},10'h3_AA, data_in[0+:80]};
  5'd9 :idle_cells = {{(120-100 ){1'b1}},10'h3_AA, data_in[0+:90]};
  5'd10 :idle_cells = {{(120-110 ){1'b1}},10'h3_AA, data_in[0+:100]};
  5'd11 :idle_cells = {                   10'h3_AA, data_in[0+:110]};
  5'd12: idle_cells = data_in[0+:120];
  default : idle_cells = {120{1'b1}};
  endcase
  pad_idle = bump_req ? idle_cells : data_in;
end
endfunction

function automatic [180-1:0] shift_cells;
input [180-1:0] stage;
input [4:0] cell_offset;
begin
  casez(cell_offset)
  5'd1 : shift_cells = {{10{1'b0}}, stage[(180-1) : 10 ]};
  5'd2 : shift_cells = {{20{1'b0}}, stage[(180-1) : 20 ]};
  5'd3 : shift_cells = {{30{1'b0}}, stage[(180-1) : 30 ]};
  5'd4 : shift_cells = {{40{1'b0}}, stage[(180-1) : 40 ]};
  5'd5 : shift_cells = {{50{1'b0}}, stage[(180-1) : 50 ]};
  5'd6 : shift_cells = {{60{1'b0}}, stage[(180-1) : 60 ]};
  5'd7 : shift_cells = {{70{1'b0}}, stage[(180-1) : 70 ]};
  5'd8 : shift_cells = {{80{1'b0}}, stage[(180-1) : 80 ]};
  5'd9 : shift_cells = {{90{1'b0}}, stage[(180-1) : 90 ]};
  5'd10 : shift_cells = {{100{1'b0}}, stage[(180-1) : 100 ]};
  5'd11 : shift_cells = {{110{1'b0}}, stage[(180-1) : 110 ]};
  5'd12 : shift_cells = {{120{1'b0}}, stage[(180-1) : 120 ]};
  5'd13 : shift_cells = {{130{1'b0}}, stage[(180-1) : 130 ]};
  5'd14 : shift_cells = {{140{1'b0}}, stage[(180-1) : 140 ]};
  5'd15 : shift_cells = {{150{1'b0}}, stage[(180-1) : 150 ]};
  5'd16 : shift_cells = {{160{1'b0}}, stage[(180-1) : 160 ]};
  5'd17 : shift_cells = {{170{1'b0}}, stage[(180-1) : 170 ]};
  5'd18 : shift_cells = {180{1'b0}};
  default : shift_cells = stage;
  endcase
end
endfunction

function automatic [120-1:0] lshift_cells;
input [180-1:0] stage;
input [4:0] cell_offset;
begin
  casez(cell_offset)
  5'd1 : lshift_cells = {stage[0+:(120-10 )], {10{1'b0}}};
  5'd2 : lshift_cells = {stage[0+:(120-20 )], {20{1'b0}}};
  5'd3 : lshift_cells = {stage[0+:(120-30 )], {30{1'b0}}};
  5'd4 : lshift_cells = {stage[0+:(120-40 )], {40{1'b0}}};
  5'd5 : lshift_cells = {stage[0+:(120-50 )], {50{1'b0}}};
  5'd6 : lshift_cells = {stage[0+:(120-60 )], {60{1'b0}}};
  5'd7 : lshift_cells = {stage[0+:(120-70 )], {70{1'b0}}};
  5'd8 : lshift_cells = {stage[0+:(120-80 )], {80{1'b0}}};
  5'd9 : lshift_cells = {stage[0+:(120-90 )], {90{1'b0}}};
  5'd10 : lshift_cells = {stage[0+:(120-100 )], {100{1'b0}}};
  5'd11 : lshift_cells = {stage[0+:(120-110 )], {110{1'b0}}};
  5'd12 : lshift_cells = {120{1'b0}};
  default : lshift_cells = stage[0+:120];
  endcase
end
endfunction

assign para_busy = atb_fifo_req || (~&token[0]) || (|wd_ocp);
assign para_done_in = flush_cmd && sbarb_done && (~atb_fifo_req) && token0is3 && wd_ocpis0;
always @ (posedge rtt_clk or posedge rst_a)
  begin : PARA_DONE_PROC
    if(rst_a == 1'b1)
      para_done <= 1'b0;
    else if (flush_done)
      para_done <= 1'b0;
    else if (para_done_in)
      para_done <= 1'b1;
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : PARA_CHKS_PROC
    if(rst_a == 1'b1) begin
      wd_ocpis0 <= 1'b0;
      token0is3 <= 1'b0;
    end
    else if (flush_done) begin
      wd_ocpis0 <= 1'b0;
      token0is3 <= 1'b0;
    end
    else if (flush_cmd) begin
      wd_ocpis0 <= ~|wd_ocp && ~|atb_fifo_wdata_int;
      token0is3 <= &token[0];
    end
  end

endmodule

