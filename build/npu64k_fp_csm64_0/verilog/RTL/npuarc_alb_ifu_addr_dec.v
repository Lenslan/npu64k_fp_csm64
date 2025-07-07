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
// This module takes the fetch request from upper stream and delivers to corresponding
//  instruction memory targets, i.e. ICCM0, ICCM1 and I cache
// It takes the ack signal from each memory controller and sends to upper stream for next fetch
// The fetch data won't go through this logic. Instead they directly go to the data mux
//  for merging and delivering to the fetch buffer
// It also pass down the branch info to the down stream
// its down pipe is data mux where the branch info is aligned with the fetch block data
// ===========================================================================


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_ifu_addr_dec_fifo_edc_err" }
//

`include "npuarc_defines.v"
// Set simulation timescale
//
`include "const.def"

module npuarc_alb_ifu_addr_dec (
  input clk,
  input rst_a,
  input restart,
  input bpu_restart,

  //memory fetch signals
  input fetch_iccm0,
  input fetch_iccm1,
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range

// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input [`npuarc_IM_BANKS-1:0] fetch_iccm0_bank,
  input [`npuarc_IM_BANKS-1:0] fetch_iccm1_bank,
  input [`npuarc_IM_BANKS+1:0] fetch_bank_ctl,
  input fetch_icache,
  input fetch_is_restart,
  input fetch_vec,
// leda NTL_CON13C on
// leda NTL_CON37 on
// spyglass enable_block W240


  input fetch_seq,
  input fetch_way_sec,
  input fetch_way_req,
  input fetch_way_force,
  input [`npuarc_IC_WAYS_BITS-1:0] fetch_way_ptr,
  input fetch_way_bank_id,
  input fetch_way_tail,
  input [`npuarc_PC_RANGE] fetch_addr0      ,
  input [`npuarc_IM_WRD_RANGE] fetch_addr1_offset ,
  input refetch,
  output fetch_rdy,

  //br info from BPU
  input brinfo_vld,
  input brinfo_is_restart,
  input brinfo_kill_2nd,
  input [`npuarc_IM_BANKS+1:0] brinfo_bank_ctl,
  input brinfo_is_br,
  input brinfo_is_br_last,
  input [`npuarc_PC_RANGE] brinfo_bta,
//input [`IM_WORD_BITS-1:`PC_LSB] brinfo_br_offset,
  input [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] brinfo_br_offset,
  input [`npuarc_BR_INFO_PKT_RANGE] brinfo_pkt,
  input brinfo_bta_miss,
//input [2:0] brinfo_bta_miss_offset,
  input [`npuarc_BR_INFO_OFFSET_RANGE] brinfo_bta_miss_offset,

  //a special signal from data_mux -- a fetch block is taken to fetch buffer if it's 1
  input fetch_data_take,

//output to memory targets
//it's request/ack based


//request
  output [`npuarc_PC_RANGE] fetch_icache_addr0 ,
  output [`npuarc_PC_RANGE] fetch_icache_addr1 ,
  output fetch_icache_req,
  output fetch_icache_vec,
  input fetch_icache_ack  ,
  output fetch_icache_seq,
  output fetch_icache_way_sec,
  output fetch_icache_way_req,
  output fetch_icache_way_force,
  output [`npuarc_IC_WAYS_BITS-1:0] fetch_icache_way_ptr,
  output fetch_icache_way_bank_id,
  output fetch_icache_way_tail,
  output fetch_icache_is_restart,

  output brinfo_id_vld,
  output brinfo_id_is_restart,
  output brinfo_id_kill_2nd,
  output brinfo_id_is_br,
  output brinfo_id_is_br_last,
  output [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] brinfo_id_br_offset,
  output [`npuarc_BR_INFO_PKT_RANGE] brinfo_id_pkt,
  output [`npuarc_PC_RANGE] brinfo_id_bta,
  output [`npuarc_IM_BANKS+1:0] brinfo_id_bank_ctl,
  output brinfo_id_bta_miss,
//output [2:0] brinfo_id_bta_miss_offset
  output [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] brinfo_id_bta_miss_offset 
);


wire fetch_id_fifo_full;
wire fetch_id_fifo_full_int;
wire fetch_id_fifo_empty;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  not used signal from fifo
wire fetch_id_fifo_afull;
wire fetch_id_fifo_aempty;
// leda NTL_CON13A on
///////////////////////////////// fetch addr gen /////////////////////////////////
//Bank1 address is concatination of address MSB and bank1 offset
//
wire [`npuarc_PC_RANGE] fetch_addr1_conv;
assign    fetch_addr1_conv = { fetch_addr0[`npuarc_PC_SIZE-1:`npuarc_IM_LINE_BITS],
                                         fetch_addr1_offset, {(`npuarc_IM_WORD_BITS-1){1'b0}} };
wire [`npuarc_PC_RANGE] fetch_addr0_int;
assign fetch_addr0_int = fetch_addr0;
wire [`npuarc_PC_RANGE] fetch_addr1_int;
assign fetch_addr1_int = fetch_addr1_conv;

////////////////////////// fetch request output gen //////////////////////////////
/////// fetch_id_fifo controls the switch from one memory to another memory
wire fetch_iccm0_ack_int;
assign fetch_iccm0_ack_int = 1'b0;
wire fetch_iccm0_int;
assign fetch_iccm0_int = 1'b0;
wire [`npuarc_IM_BANKS-1:0] fetch_iccm0_bank_int;
assign fetch_iccm0_bank_int = {`npuarc_IM_BANKS{1'b0}};
wire [`npuarc_IM_BANKS-1:0] fetch_iccm0_ack_int1;
assign fetch_iccm0_ack_int1 = {`npuarc_IM_BANKS{1'b0}};

wire fetch_iccm1_ack_int;
assign fetch_iccm1_ack_int = 1'b0;
wire fetch_iccm1_int;
assign fetch_iccm1_int = 1'b0;
wire [`npuarc_IM_BANKS-1:0] fetch_iccm1_bank_int;
assign fetch_iccm1_bank_int = {`npuarc_IM_BANKS{1'b0}};
wire [`npuarc_IM_BANKS-1:0] fetch_iccm1_ack_int1;
assign fetch_iccm1_ack_int1 = {`npuarc_IM_BANKS{1'b0}};

wire fetch_icache_int;
assign fetch_icache_int = fetch_icache && (!fetch_id_fifo_full_int);
wire fetch_icache_ack_int;
assign fetch_icache_ack_int = !fetch_icache | fetch_icache_ack;
assign fetch_icache_req = fetch_icache_int;
assign fetch_icache_addr0 = fetch_addr0_int;
assign fetch_icache_addr1 = fetch_addr1_int; 
assign fetch_icache_vec = fetch_vec;

assign fetch_icache_seq = fetch_seq;
assign fetch_icache_way_sec = fetch_way_sec;
assign fetch_icache_way_req = fetch_way_req;
assign fetch_icache_way_force = fetch_way_force;
assign fetch_icache_way_ptr = fetch_way_ptr;
assign fetch_icache_way_bank_id = fetch_way_bank_id;
assign fetch_icache_way_tail = fetch_way_tail;
assign fetch_icache_is_restart = fetch_is_restart;

//fetch rdy gen 
//
assign fetch_rdy = (fetch_iccm0_int & fetch_iccm0_ack_int) |
                   (fetch_iccm1_int & fetch_iccm1_ack_int) |
                   (fetch_icache_int & fetch_icache_ack_int);
 
wire [`npuarc_IM_BANKS-1:0] fetch_rdy_qual;
assign fetch_rdy_qual = (fetch_iccm0_bank_int & fetch_iccm0_ack_int1) |
                        (fetch_iccm1_bank_int & fetch_iccm1_ack_int1) |
                        ({`npuarc_IM_BANKS{fetch_icache_int&fetch_icache_ack_int}});

///////////////////////////////// fetch memory ID FIFO ////////////////////////////////
//The FIFO stores fetch memory target ID. 
// When It's empty the memory data is in fetch buffer
// If we have two back to fetches for different fetch target, we need to use the empty
// signal to identify the pipe is empty (before fetch buffer) and we can switch memory target 
//

//fetch bank control state machine
// it's used to handle split fetch
// In case of split it write to ID FIFO first and wait for second ack
// Restart force write to the ID FIFO and also clears previous ID fifo entry
reg fifo_wr_state, fifo_wr_state_nxt;
reg fetch_id_fifo_wr;
always @(*) 
begin: bank_ctl_sm_PROC
  fetch_id_fifo_wr = 1'b0;
  fifo_wr_state_nxt = fifo_wr_state;
//leda  W71 off
// LMD: Case statement without default clause and not all cases are covered
// LJ:  Default output assignments are from above
  case (fifo_wr_state)
    1'b0: begin
      if (bpu_restart) begin
        fetch_id_fifo_wr = fetch_rdy;
      end
      else if (!refetch & (|fetch_rdy_qual)) begin
        fetch_id_fifo_wr = fetch_rdy; 
        if (!fetch_bank_ctl[`npuarc_IM_BANKS+1]) begin //both bank needs fetch
          if (^fetch_rdy_qual) begin //only one is acked
            fifo_wr_state_nxt = 1'b1;
            fetch_id_fifo_wr = 1'b1;
          end
        end
      end
    end
    1'b1: begin
      if (bpu_restart) begin
        fetch_id_fifo_wr = fetch_rdy;
        fifo_wr_state_nxt = 1'b0;
      end
      else begin
        if (fetch_rdy) begin
          fifo_wr_state_nxt = 1'b0;
        end
      end
    end
  endcase
//leda  W71 on
end

always @(posedge clk or posedge rst_a) 
begin: fifo_wr_reg_PROC
  if (rst_a == 1'b1) begin
    fifo_wr_state <= 1'b0;
  end
  else begin
    fifo_wr_state <= fifo_wr_state_nxt;
  end
end

////////////////// memory ID FIFO instantiation ////////////////
//
wire fetch_id_fifo_rd ;
assign fetch_id_fifo_rd = fetch_data_take;
wire fetch_id_is_iccm0_fifo;
wire fetch_id_is_iccm1_fifo;
wire fetch_id_is_icache_fifo; 
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  not used signal from fifo
wire rdata_flop;
// leda NTL_CON13A on
npuarc_alb_ifu_addr_dec_fifo fetch_id_fifo (
  .clk (clk),
  .rst_a (rst_a),
  .restart(restart),

  .wr (fetch_id_fifo_wr),
  .wdata ({
     fetch_iccm0_int, 
     fetch_iccm1_int,
     fetch_icache_int}),
  .rd (fetch_id_fifo_rd),
  .rdata ({
     fetch_id_is_iccm0_fifo, 
     fetch_id_is_iccm1_fifo,
     fetch_id_is_icache_fifo}),
  .rdata_flop(rdata_flop),
  .full (fetch_id_fifo_full),
  .empty (fetch_id_fifo_empty),
  .afull (fetch_id_fifo_afull),
  .aempty (fetch_id_fifo_aempty)
);

//fetch memery target switch detection
//at restart, we force ready because previous fetch is discarded
//
wire fetch_id_diff;
assign fetch_id_diff = ((fetch_iccm0 ^ fetch_id_is_iccm0_fifo) |
                     (fetch_iccm1 ^ fetch_id_is_iccm1_fifo) |
                     (fetch_icache ^ fetch_id_is_icache_fifo) ) ;
assign fetch_id_fifo_full_int = !restart && (fetch_id_fifo_full || (!fetch_id_fifo_empty && fetch_id_diff));

//brinfo output
//
assign brinfo_id_vld = brinfo_vld;
assign brinfo_id_is_restart = brinfo_is_restart;
assign brinfo_id_kill_2nd = brinfo_kill_2nd; 
assign brinfo_id_is_br = brinfo_is_br;
assign brinfo_id_is_br_last = brinfo_is_br_last;
assign brinfo_id_bta = brinfo_bta;
assign brinfo_id_bank_ctl = brinfo_bank_ctl;
assign brinfo_id_br_offset = brinfo_br_offset;
assign brinfo_id_pkt = brinfo_pkt;
assign brinfo_id_bta_miss = brinfo_bta_miss;
assign brinfo_id_bta_miss_offset = brinfo_bta_miss_offset;

endmodule
