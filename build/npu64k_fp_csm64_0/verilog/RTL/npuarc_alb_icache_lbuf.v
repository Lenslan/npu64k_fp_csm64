// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
// ===========================================================================
//
// Description:
// This module implements line buffer for Icache that handles miss line load from main memory
// The interface to main memory is IBUS -- this block issues request to the IBUS 
//   and takes the read data from IBUS. The request is always a burst according to the cache line
//   size in the configuration.
// In the case of uncached access, it issues a single fetch block request for each I-cache request
// The line buffer size is fixed at 128bit (a fetch block)
//---------------------------------------------------------------------------- 
`include "npuarc_defines.v"
// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

// leda W389 off
// LMD: Multiple clocks in the module
// LJ:  this module requires two clocks (clk_ibus and clk) 
module npuarc_alb_icache_lbuf (
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  clk not used
// spyglass disable_block W240
// SMD: non driving port
// SJ : clk not used
  input clk,      //two cycle clock
// leda NTL_CON13C on
// spyglass enable_block W240
  input clk_en,   //clock gate control signal of clk
  input clk_ibus, //single cycle core clock
  input rst_a,
  input restart,

  /* signals driven by clk */
  input lf_start,
  input lf_kernel,
  input lf_uncache,
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input [`npuarc_PIADDR_RANGE] lf_addr,
  input [`npuarc_IC_ALIAS_IDX_RANGE]         lf_alias_idx,
  output reg [`npuarc_IC_ALIAS_IDX_RANGE]    lf_alias_idx_r,
// leda NTL_CON13C on
  input lf_err_clr,
  input [`npuarc_IC_WAYS_BITS-1:0] lf_req_way,
  output reg lbuf_en,
  output reg [`npuarc_PIADDR_RANGE] lf_addr_r,
 
  input dout_rdy,

  input hit_req,
  input bank_ctl,
  input [`npuarc_IM_BANKS-1:0] bank_sel,
  output line_hit,
  output line_in_cache, //data is from cache
  output hit, //data is from lbuf
//  output [`IC_DRAM_RANGE] hit_data,
  output [`npuarc_IC_LBUF_RANGE] hit_data,
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs
// LJ:  Not all bits work
  output reg [`npuarc_IC_WAYS_BITS-1:0] line_hit_way,
// leda NTL_CON32 on
  /* signals driven by clk_ibus */
  output reg lf_req,
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs
// LJ:  singal only sent to cpu_top
  output reg lf_req_kernel,
// leda NTL_CON32 on
  input lf_req_ack,
  output [`npuarc_PADDR_RANGE] lf_req_addr,
  output [3:0] lf_burst_size,
  output lf_req_wrap,
  output ifu_ibus_cmd_cache,

  input din_err,
  input [`npuarc_DOUBLE_RANGE] din,
  input din_vld,
  output din_accept,

//  output dout_vld,
  output dout_vld_urgent,
  output reg dout_err,
  output reg dout_err_nxt,
//  output [`IC_DRAM_RANGE] dout,
  output [`npuarc_IC_LBUF_RANGE] dout,
  output reg [`npuarc_IC_WAY_ADR_RANGE] dout_waddr

);

//leda BTTF_D002 off
//LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
//LJ:  the addition/subtration of less bits than the result are intentional 

//bus request control

//IBUS request parameters
parameter IBUS_BSIZE = `npuarc_IC_BSIZE;                 //bytes per IBUS request, we don't chop cache line so it sticks on IC_BSIZE
// spyglass disable_block W163 ParamWidthMismatch-ML 
// SMD: Significant bits of constant will be truncated
// SJ:  the addition/subtration of less bits than the result are intentional 
// SMD: Parameter width does not match width of value assigned
// SJ:  the addition/subtration of less bits than the result are intentional 
parameter [3:0] IBUS_BLEN = IBUS_BSIZE/`npuarc_DOUBLE_BE_SIZE; //burst length per request 
// spyglass enable_block W163 ParamWidthMismatch-ML 

//LBUF parameters
parameter LBUF_SIZE = `npuarc_IC_BYTE_WIDTH; //line buffer byte size = size of fetch block
parameter [3:0] LBUF_DP = LBUF_SIZE/`npuarc_DOUBLE_BE_SIZE;    //how many IBUS data in lbuf 
parameter LBUF_DP_LOG = (LBUF_DP==2) ? 1 :        //line buffr depth, always=2 in this design 
                        (LBUF_DP==4) ? 2 : 
                        (LBUF_DP==8) ? 3 : 
                        (LBUF_DP==16) ? 4 : 0; 


parameter [LBUF_DP_LOG:0] LBUF_DP_CNT = LBUF_SIZE/`npuarc_DOUBLE_BE_SIZE;    //how many IBUS data in lbuf for cnt

//`if (`IFU_128_OPTION == 1  && (`IC_BSIZE == `IC_BYTE_WIDTH))// {
//parameter LBUF_ITER = 1; //how many line buffer fill per cache line
//`else
parameter LBUF_ITER = (`npuarc_IC_BSIZE/`npuarc_IC_BYTE_WIDTH) - 1; //how many line buffer fill per cache line
//`endif   //}
parameter RD_INC = (`npuarc_IC_BYTE_WIDTH/`npuarc_DOUBLE_BE_SIZE); //how many ibus data per fetch block 

  reg dout_err_next;
  reg [`npuarc_IC_ALIAS_IDX_RANGE]      lf_alias_idx_nxt;
  wire [`npuarc_IC_ALIAS_IDX_RANGE]     lf_alias_idx_2cyc;
  wire [`npuarc_IC_ALIAS_IDX_RANGE]     lf_alias_idx_r_2cyc;

//sm for bus if, driven by core clock
//this implementation doesn't do pipelined line fill, one one line fill at one time
//  i.e no new line fill request until line data is filled in I$
reg lf_req_nxt;
reg lf_req_next;
reg lf_req_kernel_nxt;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg [`npuarc_PIADDR_RANGE] lf_addr_nxt;
// leda NTL_CON32 on
reg [1:0] state_nxt;
reg [1:0] state_next;
reg [1:0] state;
reg restart_clr_nxt;
reg restart_clr_next;
reg restart_clr;
reg lbuf_en_nxt;
reg lbuf_en_next;
reg lf_uncache_nxt;
reg lf_uncache_next;
reg lf_uncache_r;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs 
// LJ:  signal only sent to outside
reg lf_uncache_wrap_nxt;
reg lf_uncache_wrap_next;
// leda NTL_CON32 on
reg lf_uncache_wrap_r;
parameter IDLE = 2'b00;
parameter IC_REQ_START = 2'b01;
parameter UNCACHE_WAIT = 2'b10;
always @(*) 
begin: lf_state_PROC
  lf_req_nxt = lf_req;
  lf_req_kernel_nxt = lf_req_kernel;
  lf_addr_nxt = lf_addr_r;
  lf_alias_idx_nxt = lf_alias_idx_r;
  restart_clr_nxt = restart_clr;
  lf_uncache_nxt = lf_uncache_r;
  lf_uncache_wrap_nxt = lf_uncache_wrap_r;
  state_nxt = state;
//leda  W71 off
// LMD: Case statement without default clause and not all cases are covered
// LJ:  Default output assignments are from above
  case (state)
    IDLE: begin
      if (lf_start & clk_en) begin //lf_start is from clk2
        lf_req_nxt = 1'b1;
        lf_req_kernel_nxt = lf_kernel;
        lf_addr_nxt = {(`npuarc_PIADDR_BITS){1'b0}};
        lf_addr_nxt[`npuarc_PADDR_MSB:`npuarc_IC_WORD_BITS] = lf_addr[`npuarc_PADDR_MSB:`npuarc_IC_WORD_BITS];  //start from critical word
        lf_alias_idx_nxt = lf_alias_idx;
        lf_uncache_nxt = lf_uncache;
        lf_uncache_wrap_nxt = lf_uncache && (^bank_sel); //for uncache access, always wrap for single fetch
                                                       //so that it never crosses mem page boundary
        if (lf_uncache) begin
          lf_addr_nxt[`npuarc_IC_WORD_BITS-1] = lf_addr[`npuarc_IC_WORD_BITS-1]; //uncacheable request on bank basis 
        end
        else begin
          lf_addr_nxt[`npuarc_IC_WORD_BITS-1] = 1'b0;
        end
        state_nxt = IC_REQ_START;
      end  
    end
    IC_REQ_START: begin
      if (lf_uncache_r) begin
        if (restart) begin
          restart_clr_nxt = 1'b1;
        end
        if (lf_req_ack) begin
          lf_req_nxt = 1'b0;
          state_nxt = UNCACHE_WAIT;
        end
      end 
      else if (lf_req_ack) begin //ack can happen at same cycle as lf_req
        lf_req_nxt = 1'b0;
        state_nxt = IDLE;
      end
    end
    UNCACHE_WAIT: begin
      if (restart) begin
        restart_clr_nxt = 1'b1;
      end
// spyglass disable_block W415a
// SMD: signal assigned multiple times in the same always block
// SJ:  done on purpose, last one has priority. 
      if (!lbuf_en_nxt) begin
        state_nxt = IDLE;
        restart_clr_nxt = 1'b0;
// spyglass enable_block W415a
      end
    end
  endcase
//leda  W71 on
end //block: lf_state_PROC 

always @*
begin
    state_next             = state_nxt;
    lf_req_next            = lf_req_nxt;
    restart_clr_next       = restart_clr_nxt;
    lf_uncache_next        = lf_uncache_nxt;
    lf_uncache_wrap_next   = lf_uncache_wrap_nxt;
end

// LF STATE 
//
always @(posedge clk_ibus or posedge rst_a) 
begin: state_r_PROC
  if (rst_a == 1'b1)
  begin
    state            <= IDLE;
    lf_req           <= 1'b0;
    restart_clr       <= 1'b0;
    lf_uncache_r      <= 1'b0;
    lf_uncache_wrap_r <= 1'b0;
  end
  else
  begin
    state            <= state_next;
    lf_req           <= lf_req_next;
    restart_clr       <= restart_clr_next;
    lf_uncache_r      <= lf_uncache_next;
    lf_uncache_wrap_r <= lf_uncache_wrap_next;
  end
end // block: state_r_PROC

// spyglass disable_block STARC05-1.3.1.3 AsyncResetOtherUse
// SMD: Asynchronous reset signal used as non-reset/synchronous-reset
// SJ:  no functional issue
always @(posedge clk_ibus or posedge rst_a) 
begin: lf_r_PROC
  if (rst_a == 1'b1) begin
    lf_req_kernel     <= 1'b0;
    lf_addr_r         <= {(`npuarc_PIADDR_BITS){1'b0}};
    lf_alias_idx_r    <= {`npuarc_IC_ALIAS_BITS{1'b0}};
  end
  else begin
    lf_req_kernel     <= lf_req_kernel_nxt;
    lf_addr_r         <= lf_addr_nxt;
    lf_alias_idx_r    <= lf_alias_idx_nxt;
  end
end //block: lf_r_PROC

// spyglass enable_block STARC05-1.3.1.3

// Pass to the IBUS and L2 Cache if this transaction is cached or not.
// It is not cached in L1 or L2 when
// (1) The L1 Icache is disabled
// (2) There is an IFQ configured and no L1 Icache configured
// (3) It is an ICCM access
// (4) There is an MPU hit in an MPU area that is designated as uncached
// 
assign ifu_ibus_cmd_cache = ~lf_uncache_r;

//data path
reg [`npuarc_DOUBLE_RANGE] lbuf0;
reg [`npuarc_DOUBLE_RANGE] lbuf0_nxt;
reg [`npuarc_DOUBLE_RANGE] lbuf1;
reg [`npuarc_DOUBLE_RANGE] lbuf1_nxt;

reg [0:0] wr_ptr_nxt;          //count by ibus transactions 
reg [0:0] wr_ptr_next;          //count by ibus transactions 
reg [0:0] wr_ptr;          //count by ibus transactions 
reg [1:0] cnt_nxt;
reg [1:0] cnt_next;
reg [1:0] cnt;
reg [`npuarc_IC_WRD_BITS-1:0] wr_iter_cnt_nxt; //count by number of line buffers 
reg [`npuarc_IC_WRD_BITS-1:0] wr_iter_cnt_next; //count by number of line buffers 
reg [`npuarc_IC_WRD_BITS-1:0] wr_iter_cnt; //count by number of line buffers 
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs 
// LJ: not all bits have effect
reg [`npuarc_IC_WRD_BITS-1:0] rd_iter_cnt_nxt; //count by number of line buffers
reg [`npuarc_IC_WRD_BITS-1:0] rd_iter_cnt_next; //count by number of line buffers
reg [`npuarc_IC_WRD_BITS-1:0] rd_iter_cnt; //count by number of line buffers
// leda NTL_CON32 on
reg bank_ctl_r, bank_ctl_nxt;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs 
// LJ: used in function
reg [`npuarc_IC_WAYS_BITS-1:0] line_hit_way_nxt;
// leda NTL_CON32 on
reg [`npuarc_IC_WAY_ADR_RANGE] dout_waddr_nxt;


wire dout_vld_int;
assign dout_vld_int = (cnt >= $unsigned(RD_INC));
wire dout_rd;
assign dout_rd = dout_vld_int & dout_rdy & clk_en; 

// adding extra flop to cut the path from external to icache in ifu. Refer:star 9000805996
// din_vld_r, din_err_r, din_r
reg  din_vld_r;
reg  din_err_r;

wire [`npuarc_DOUBLE_RANGE] din_r;
wire din_accept_int;

wire din_accept_out;
wire clr_din_vld;
assign din_accept = (cnt < LBUF_DP_CNT);

assign din_accept_out = (~din_vld_r && ~din_err_r )|| ( clr_din_vld);
assign clr_din_vld = (din_vld_r || din_err_r) && din_accept_int;

wire din_vld_qual;

assign din_vld_qual = (din_vld||din_err) && din_accept; //qualify a ibus transaction 

wire [0:0] wr_ptr_inc;
// leda W484 off
// leda B_3219 off
// LMD: Possible loss of carry/borrow in addition/subtraction
// LJ:  pointer arithmetic, logic guards against overflow 

// spyglass disable_block WRN_1024
// SMD: unsigned argument passed to $unsigned function call
// SJ:  arguments unsigned by default
assign wr_ptr_inc = (wr_ptr==$unsigned(LBUF_DP-1)) ? 0 : wr_ptr + 1;
// leda W484 on
// spyglass enable_block WRN_1024
// leda B_3219 on


// adding extra flop to cut the path from external to icache in ifu. Refer:star 9000805996
// din_vld_r, din_err_r, din_r
always @(posedge clk_ibus or posedge rst_a) 
begin: din_vld_r_PROC
  if (rst_a == 1'b1) begin
    din_vld_r  <= 1'b0;
  end
  else begin
    din_vld_r  <= (din_vld && din_accept_out)
                  ? 1'b1                       // set
                  : (clr_din_vld ? 1'b0        // clear
                                 : din_vld_r);
  end
end //block: din_vld_r_PROC

always @(posedge clk_ibus or posedge rst_a) 
begin: din_err_r_PROC
  if (rst_a == 1'b1) begin
    din_err_r  <= 1'b0;
  end
  else begin
    din_err_r  <=  (din_err && din_accept_out)
                   ? 1'b1                      // set
                   : (clr_din_vld ? 1'b0       // clear
                                  : din_err_r);
  end
end //block: din_err_r_PROC

assign din_r = din;

always @*
begin
    wr_ptr_next = wr_ptr_nxt;
    cnt_next    = cnt_nxt;
    wr_iter_cnt_next = wr_iter_cnt_nxt;
    rd_iter_cnt_next = rd_iter_cnt_nxt;
    lbuf_en_next = lbuf_en_nxt;
    dout_err_next = dout_err_nxt;
end

always @(posedge clk_ibus or posedge rst_a) 
begin: lbuf_dp_reg_PROC
  if (rst_a == 1'b1) begin
    wr_ptr <= {1{1'b0}};
    cnt <= {1+1{1'b0}};
    wr_iter_cnt <= {`npuarc_IC_WRD_BITS{1'b0}};
    rd_iter_cnt <= {`npuarc_IC_WRD_BITS{1'b0}};
    lbuf_en <= 1'b0;
    dout_err <= 1'b0;
  end
  else begin
    wr_ptr <= wr_ptr_next;
    cnt <= cnt_next;
    wr_iter_cnt <= wr_iter_cnt_next;
    rd_iter_cnt <= rd_iter_cnt_next;
    lbuf_en <= lbuf_en_next;
    dout_err <= dout_err_next;
  end
end // block: lbuf_dp_reg_PROC


always @(posedge clk_ibus or posedge rst_a) 
begin: lbuf_dpath_reg_PROC
  if (rst_a == 1'b1) begin
    dout_waddr <= {`npuarc_IC_WAY_ADR_BITS{1'b0}};        
    bank_ctl_r <= 1'b0;
    line_hit_way <= `npuarc_IC_WAYS_BITS'd0;
  end
  else begin
    dout_waddr <= dout_waddr_nxt;
    bank_ctl_r <= bank_ctl_nxt;
    line_hit_way <= line_hit_way_nxt;
  end
end //block: lbuf_dpath_reg_PROC

always @(*)
begin: lbuf_dpath_PROC
    wr_ptr_nxt = wr_ptr;
    cnt_nxt = cnt;
    wr_iter_cnt_nxt = wr_iter_cnt;
    rd_iter_cnt_nxt = rd_iter_cnt;
    dout_waddr_nxt = dout_waddr;
    bank_ctl_nxt = bank_ctl_r;
    line_hit_way_nxt = line_hit_way;
    lbuf_en_nxt = lbuf_en;
    if (lf_start & clk_en) begin
      lbuf_en_nxt = 1'b1;
      wr_ptr_nxt = {1{1'b0}};
      wr_iter_cnt_nxt = {`npuarc_IC_WRD_BITS{1'b0}};
      rd_iter_cnt_nxt = {`npuarc_IC_WRD_BITS{1'b0}};
      cnt_nxt = {1+1{1'b0}};

      dout_waddr_nxt[`npuarc_IC_IDX_RANGE]= {lf_alias_idx[`npuarc_IC_ALIAS_IDX_RANGE], lf_addr[`npuarc_IC_UNALIASED_IDX_RANGE]};
      dout_waddr_nxt[`npuarc_IC_WRD_RANGE] = lf_addr[`npuarc_IC_WRD_RANGE]; //wrap around 


      bank_ctl_nxt = bank_ctl;
      line_hit_way_nxt = lf_req_way;
    end
    else begin
      if (din_vld_qual == 1'b1) begin
// leda B_3200 off
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction
// LJ:  pointer arithmetic, logic guards against overflow 
        cnt_nxt = cnt + 1; //count by ibus transactions
// leda W484 on
// leda B_3200 on
      end
      else if (dout_rd) begin //dout_rd and din_vld_qual are mutual exclusive
        cnt_nxt = {1+1{1'b0}}; 
      end
      if (dout_rd) begin //full line buffer got read
// spyglass disable_block WRN_1024
// SMD: unsigned argument passed to $unsigned function call
// SJ:  arguments unsigned by default
// leda B_3219 off
// leda B_3212 off
        if (lf_uncache_r || ($unsigned(rd_iter_cnt) == LBUF_ITER)) begin
// spyglass enable_block WRN_1024
// leda B_3219 on
// leda B_3212 on
 //         rd_done_nxt = 1'b1;
          lbuf_en_nxt = 1'b0;
          rd_iter_cnt_nxt = {`npuarc_IC_WRD_BITS{1'b0}};
        end
        else begin
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction
// LJ:  pointer arithmetic, logic guards against overflow 
          rd_iter_cnt_nxt = rd_iter_cnt + 1;
        end
//leda W314 off
//LMD: Converting vector(unsigned) to signle bit(logical)
//LJ : the configuration allows IC_WRD_RANGE to be single bit
        dout_waddr_nxt[`npuarc_IC_WRD_RANGE] = dout_waddr[`npuarc_IC_WRD_RANGE] + 1; //wrapped 
//leda W314 on
// leda W484 on
      end
// spyglass disable_block WRN_1024
// SMD: unsigned argument passed to $unsigned function call
// SJ:  arguments unsigned by default
      if (din_vld_qual == 1'b1) begin //one ibus transaction
// leda B_3219 off
// leda B_3212 off
        if (wr_ptr == $unsigned(LBUF_DP-1)) begin
          wr_ptr_nxt = {1{1'b0}};
          if (lf_uncache_r || ($unsigned(wr_iter_cnt) == LBUF_ITER)) begin
// leda B_3219 on
// leda B_3212 on
//            wr_done_nxt = 1'b1;
            wr_iter_cnt_nxt = {`npuarc_IC_WRD_BITS{1'b0}};
          end
          else begin
// spyglass enable_block WRN_1024
// leda B_3200 off
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction
// LJ:  pointer arithmetic, logic guards against overflow 
            wr_iter_cnt_nxt = wr_iter_cnt + 1'b1;
// leda W484 on
// leda B_3200 on
          end
        end  
        else begin

          wr_ptr_nxt = wr_ptr_inc;
// leda W484 on
        end
      end
    end
end //block: lbuf_dpath_PROC

always @(*)
begin: dout_err_PROC
  dout_err_nxt = dout_err;
  if (lf_err_clr & clk_en) begin //lf_err_clr will not happen during line fill  
    dout_err_nxt = 1'b0;
  end 
//else if (din_err) begin
  else if (din_err_r) begin //use the flop version. star 9000805996
    dout_err_nxt = 1'b1;
  end
end

// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ: the memory element doesn't need reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset

always @(posedge clk_ibus) 
begin: lbuf_mem_PROC
  if (din_vld_qual == 1'b1) begin
     lbuf0 <= lbuf0_nxt;
     lbuf1 <= lbuf1_nxt;
  end
end //block: lbuf_mem_PROC

always @ * 
begin: lbuf_mem_nxt_PROC
   lbuf0_nxt = lbuf0;
   lbuf1_nxt = lbuf1;
   case(wr_ptr)
    0: lbuf0_nxt = din_r;
    1: lbuf1_nxt = din_r;
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
     default: ;
// spyglass enable_block W193
   endcase
end //block: lbuf_mem_PROC
// leda NTL_RST03 on
// leda S_1C_R on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

assign dout = {lbuf1, lbuf0}; //simplified read because we only have two ibuf words in one fetch block

//buf hit detedction
// leda NTL_STR76 off
// LMD: A non-tristate net can have only one non-tristate driver
// LJ:  The 2 cycle checker asserts X on the a cycle signal as an assertion
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  some bits of pc are unused
// leda NTL_CON13A on
wire [`npuarc_IC_TAG_MSB:`npuarc_IC_IDX_LSB] lf_addr_r_2cyc;
// leda NTL_STR76 on

npuarc_alb_2cyc_checker #(`npuarc_IC_TAG_MSB-`npuarc_IC_IDX_LSB+1) u_alb_2cyc_checker_lf_addr_r (
  .data_in(lf_addr_r[`npuarc_IC_TAG_MSB:`npuarc_IC_IDX_LSB]),
  .data_out(lf_addr_r_2cyc),
  .clk(clk_ibus)
);

npuarc_alb_2cyc_checker #(`npuarc_IC_ALIAS_BITS) u_alb_2cyc_checker_alias (
  .data_in(lf_alias_idx),
  .data_out(lf_alias_idx_2cyc),
  .clk(clk_ibus)
);
npuarc_alb_2cyc_checker #(`npuarc_IC_ALIAS_BITS) u_alb_2cyc_checker_alias_r (
  .data_in(lf_alias_idx_r),
  .data_out(lf_alias_idx_r_2cyc),
  .clk(clk_ibus)
);

wire [`npuarc_IC_WRD_RANGE] lf_buf_ptr; //fetch block pointer in a cache line driver by write
wire [`npuarc_IC_WRD_BITS:0] wr_word_cnt; //fetch block count in write order

wire lf_buf_hit;
wire buf_hit;
wire [`npuarc_IC_WRD_RANGE] hit_ptr;
assign hit_ptr = lf_addr[`npuarc_IC_WRD_RANGE]; //request fetch block position in cache line 
assign wr_word_cnt = {1'b0, wr_iter_cnt}; 
wire req_misalign;
assign req_misalign = (&bank_sel) & bank_ctl; 
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction
// LJ:  pointer arithmetic, logic guards against overflow 
// spyglass disable_block W484 W164a
// SMD: Possible assignment overflow
// SMD: LHS width is less than RHS
// SJ:  pointer arithmetic, logic guards against overflow
assign lf_buf_ptr = lf_addr_r[`npuarc_IC_WRD_RANGE] + wr_word_cnt[`npuarc_IC_WRD_BITS-1:0]; 

assign line_hit = hit_req
                && (lf_alias_idx_2cyc == lf_alias_idx_r_2cyc)
                && (lf_addr[`npuarc_IC_TAG_MSB:`npuarc_IC_IDX_LSB] == lf_addr_r_2cyc[`npuarc_IC_TAG_MSB:`npuarc_IC_IDX_LSB]); 

assign lf_buf_hit = ( (cnt==$unsigned(RD_INC-1)) && din_vld_qual) && (hit_ptr == lf_buf_ptr[`npuarc_IC_WRD_RANGE]); //line buffer hit
//assign lf_buf_hit = ( (cnt==4)) && (hit_ptr == lf_buf_ptr[`IC_WRD_RANGE]); //line buffer hit 
assign buf_hit = hit_req && line_hit && lf_buf_hit; 
//assign hit = (lf_uncache_r) ? hit_req && dout_vld_int && (!(restart_clr||restart)) : 
assign hit = (lf_uncache_r) ? hit_req && dout_vld_int && (!(restart_clr||restart)) :
                              buf_hit && (!req_misalign); //unaligned dual fetch no hit to lbuf 

//line hit in cache detection
wire [`npuarc_IC_WRD_BITS-1:0] hit_wcnt_int;

assign hit_wcnt_int = hit_ptr - lf_addr_r[`npuarc_IC_WRD_RANGE] ; //distance to the initial pointer  
wire [`npuarc_IC_WRD_BITS:0] hit_wcnt;
assign hit_wcnt = {1'b0,hit_wcnt_int} + {`npuarc_IC_WRD_BITS'b0, bank_ctl}; 
assign line_in_cache = hit_req && line_hit && (!buf_hit) && (!dout_vld_int) && (wr_word_cnt > hit_wcnt); 

assign hit_data = (lf_uncache_r && bank_ctl_r) ? {lbuf0, lbuf1} : {lbuf1, lbuf0};

assign lf_req_addr = {lf_addr_r, `npuarc_PC_LSB'b0};

//assign dout_vld = dout_vld_int && (!(lf_uncache_r && (restart_clr||restart)));
assign dout_vld_urgent = dout_vld_int && (!lf_uncache_r);
//assign din_accept = (cnt < LBUF_DP_CNT);
assign din_accept_int = (cnt < LBUF_DP_CNT);

assign lf_req_wrap = (!lf_uncache_r) || lf_uncache_wrap_r;
// leda B_3200 off
// LMD: Unequal length operand in bit/arithmetic operator
// LJ:  pointer arithmetic, logic guards against overflow
// spyglass disable_block W163
// SMD: Significan bits of constant will be truncated
// SJ: logic guards against overflow 
assign lf_burst_size = (lf_uncache_r) ? LBUF_DP-1 : IBUS_BLEN-1;
// leda B_3200 on
// leda W484 on
//leda BTTF_D002 on
// spyglass enable_block W163
// spyglass enable_block W484 W164a

endmodule
// leda W389 on
