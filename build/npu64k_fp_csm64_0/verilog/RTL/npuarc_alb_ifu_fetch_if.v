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
// This is the interface module with BPU
// It's driven by clk2 that runs at every other core clock
// The BPU has two groups of output signals -- the fetch signals and the branch_info signals
//  -- The fetch signals are used to fetch memories.
//  -- the branch_info are one clk cycle delayed (two core clocks that is the branch cache delay). 
// To prevent timing path caused by stall to the BPU, it has a skid buffer with the ready signal 
// flopped
// Its down pipe is the address decoder   
// The module also stores the previous fetched memory address that is used for refetch
//     Currently only refetch of ICCM is implemented
//     Cache refetch would be in future revisions
// ===========================================================================

`include "npuarc_defines.v"

//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_ifu_fetch_if_fifo_edc_err" }
//D: error_signal { name: "alb_ifu_fetch_if_wp_fifo_edc_err" }
//
module npuarc_alb_ifu_fetch_if (
  input clk,
  input clk2_en,
  input rst_a ,
  input ifu_hlt_rdy,
  input hlt_restart,
  input fetch_restart,
  input mmu_restart,
  output ifu_active,
  output reg ifu_idle_r,
  output reg hlt_stall,
  
  //refetch switches from ICCM
  input [`npuarc_IM_BANKS-1:0] fetch_iccm0_kill, 
  input [`npuarc_IM_BANKS-1:0] fetch_iccm1_kill,

// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
// leda NTL_CON13C on
// leda NTL_CON37 on
 
  //memory fetch input from EXU
  input [`npuarc_PC_RANGE] fch_target,
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
  input [`npuarc_IM_LINE_BITS:3] fch_target_successor,
// leda NTL_CON13C on
// leda NTL_CON37 on
  input restart_way_vld,
  input[`npuarc_IC_WAYS_BITS_RANGE] restart_way,

  //memory fetch input from BPU
  input restart, 
  input restart_r,
  input bpu_restart, //restart happens at same cycle as fetch_req
  input restart_vec,
  input fetch_req,
  input fetch_iccm0,
  input fetch_iccm1,
  input fetch_icache,
  input [`npuarc_PC_RANGE] fetch_addr0,            //bank0 address         
  input [`npuarc_IM_WRD_RANGE] fetch_addr1_offset, //bank1 offset
  input [`npuarc_IM_BANKS:0] fetch_bank_ctl,       //specify which bank to fetch and if it's aligned
  input fetch_way_force,                    //icache force to use the predicted way
  input [`npuarc_IC_WAYS_BITS-1:0] fetch_way_ptr,  //icache way pointer               
  input fetch_seq,                          //sequential fetch
  input fetch_way_sec,                      //way prediction for secondary branch
  input fetch_way_req,                      //request feedback of the way from cache
  output fetch_rdy, //to qualify fetch_req. It's from the skid buffer that is flopped
  //signals that are from branch cache, it's delayed by one cycle vs fetch_req
  input brinfo_kill_2nd,
  input brinfo_is_br,
  input brinfo_is_br_last,
  input [`npuarc_PC_RANGE] brinfo_bta,
  input [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] brinfo_br_offset,
  input [`npuarc_BR_INFO_PKT_RANGE] brinfo_pkt,
  input brinfo_bta_miss,
//input [2:0] brinfo_bta_miss_offset,
  input [`npuarc_BR_INFO_OFFSET_RANGE] brinfo_bta_miss_offset,

  //fetch request output to each memory target
  output fetch_iccm0_out,
  output [`npuarc_IM_BANKS-1:0] fetch_iccm0_bank_out,
  output fetch_iccm1_out,
  output [`npuarc_IM_BANKS-1:0] fetch_iccm1_bank_out,
  output fetch_icache_out,
  output [`npuarc_PC_RANGE] fetch_addr0_out,
  output [`npuarc_IM_WRD_RANGE] fetch_addr1_offset_out, 
  output [`npuarc_IM_BANKS+1:0] fetch_bank_ctl_out, //MSB is single_bank ID, it's for timing fix
  output fetch_is_restart_out,
  output fetch_vec_out,
  output fetch_way_force_out,
  output [`npuarc_IC_WAYS_BITS-1:0] fetch_way_ptr_out,
  output fetch_seq_out,
  output fetch_way_sec_out,
  output fetch_way_req_out,
  output fetch_way_bank_id_out,
  output fetch_way_tail_out,
  output refetch,
  input fetch_out_rdy,

  //brinfo output to down pipe
  output reg brinfo_vld,
  output brinfo_kill_2nd_out,
  output [`npuarc_IM_BANKS+1:0] brinfo_bank_ctl_out,
  output reg brinfo_is_restart_out,
  output brinfo_is_br_out,
  output brinfo_is_br_last_out,
  output [`npuarc_PC_RANGE] brinfo_bta_out,
  output [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] brinfo_br_offset_out,
  output [`npuarc_BR_INFO_PKT_RANGE] brinfo_pkt_out,
  output brinfo_bta_miss_out,
//output [2:0] brinfo_bta_miss_offset_out
  output [`npuarc_BR_INFO_OFFSET_RANGE] brinfo_bta_miss_offset_out 
);

//decode fetch signals

//
wire fetch_req_int;
assign fetch_req_int = fetch_req & clk2_en; 
wire fetch_iccm0_int;
assign fetch_iccm0_int = fetch_req_int & fetch_iccm0;
wire fetch_iccm1_int;
assign fetch_iccm1_int = fetch_req_int & fetch_iccm1;
wire fetch_icache_int;
assign fetch_icache_int = fetch_req_int & fetch_icache;

wire fetch_iccm_kill;
assign fetch_iccm_kill = |{fetch_iccm0_kill, fetch_iccm1_kill};


wire restart_mis_align;
//assign restart_mis_align = fch_target[3];
assign restart_mis_align = fch_target[`npuarc_IC_BANK_SEL];
//wire restart_fetch_bank1;
//assign restart_fetch_bank1 = 1'b1;
wire restart_fetch_bank0;
//assign restart_fetch_bank0 = !fch_target[3] || 
assign restart_fetch_bank0 = !fch_target[`npuarc_IC_BANK_SEL]   
//                            (!(fch_target[`IM_WRD_RANGE] == {`IM_WRD_BITS{1'b1}}));
                          ||  (!(fch_target[`npuarc_IM_WRD_RANGE] == {`npuarc_IM_WRD_BITS{1'b1}}))
                           ;
wire [`npuarc_IM_BANKS:0] restart_bank_ctl;
assign restart_bank_ctl = {restart_mis_align,
                                       1'b1,//restart_fetch_bank1,
                                       restart_fetch_bank0};
reg [`npuarc_PC_RANGE] restart_addr0;
reg [`npuarc_IM_WRD_RANGE] restart_addr1_offset;
always @(*)
begin: restart_addr0_PROC
  restart_addr0 = fch_target;
  restart_addr1_offset = fch_target_successor[`npuarc_IM_WRD_RANGE]; 
  if (restart_mis_align) begin
    restart_addr0[`npuarc_IM_WRD_RANGE]  = fch_target_successor[`npuarc_IM_WRD_RANGE];
    restart_addr1_offset = fch_target[`npuarc_IM_WRD_RANGE]; 
  end
end

wire restart_fetch_iccm0;
assign restart_fetch_iccm0 = 1'b0;

wire restart_fetch_iccm1;
assign restart_fetch_iccm1 = 1'b0;

wire restart_fetch_icache;
assign restart_fetch_icache = 1'b1;

 
////////////////////// skid logic //////////////////////////////////
//A one deept FIFO stores the skid data 
//It's written when the pipe is not ready but there is a valid input
//
wire fetch_fifo_full;
wire fetch_fifo_empty;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  signal from fifo
wire fetch_fifo_afull;
wire fetch_fifo_aempty;
// leda NTL_CON13A on
wire fetch_vec_fifo; 
wire fetch_iccm0_fifo;
wire fetch_iccm1_fifo;
wire fetch_icache_fifo; 
wire [`npuarc_PC_RANGE] fetch_addr0_fifo;
wire [`npuarc_IM_WRD_RANGE] fetch_addr1_offset_fifo; 
wire fetch_restart_fifo;
wire [`npuarc_IM_BANKS:0] fetch_bank_ctl_fifo;
wire fetch_seq_fifo;
wire fetch_way_sec_fifo;
wire fetch_way_req_fifo;
wire fetch_way_force_fifo;
wire [`npuarc_IC_WAYS_BITS-1:0] fetch_way_ptr_fifo;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  signal from fifo
wire rdata_flop;
// leda NTL_CON13A on
wire fetch_out_rdy_int;
assign fetch_out_rdy_int = !fetch_iccm_kill & fetch_out_rdy & clk2_en;
reg  no_hlt_stall;

//muxes for writing to skid buffer 
wire restart_vec_muxed;
assign restart_vec_muxed = (fetch_restart) ? restart_vec : 1'b0;
wire [`npuarc_PC_RANGE] fetch_addr0_muxed;
assign fetch_addr0_muxed = (fetch_restart) ? restart_addr0 : fetch_addr0;
wire [`npuarc_IM_WRD_RANGE] fetch_addr1_offset_muxed;
assign fetch_addr1_offset_muxed = (fetch_restart) ? restart_addr1_offset : fetch_addr1_offset;
wire [`npuarc_IM_BANKS:0] fetch_bank_ctl_muxed;
assign fetch_bank_ctl_muxed = (fetch_restart) ? restart_bank_ctl : fetch_bank_ctl;
wire fetch_seq_muxed;
assign fetch_seq_muxed = (fetch_restart) ? 1'b0 : fetch_seq; 
wire fetch_way_sec_muxed;
assign fetch_way_sec_muxed = fetch_way_sec; //bpu supply it including restart value 
wire fetch_way_req_muxed;
assign fetch_way_req_muxed = fetch_way_req; //bpu supply it including restart value 
wire fetch_way_force_muxed;
assign fetch_way_force_muxed = (fetch_restart) ? restart_way_vld : fetch_way_force;
wire [`npuarc_IC_WAYS_BITS-1:0] fetch_way_ptr_muxed;
assign fetch_way_ptr_muxed = (fetch_restart) ? restart_way : fetch_way_ptr;
wire fetch_iccm0_muxed;
assign fetch_iccm0_muxed = (fetch_restart) ? restart_fetch_iccm0 : fetch_iccm0; 
wire fetch_iccm1_muxed;
assign fetch_iccm1_muxed = (fetch_restart) ? restart_fetch_iccm1 : fetch_iccm1; 
wire fetch_icache_muxed;
assign fetch_icache_muxed = (fetch_restart) ? restart_fetch_icache : fetch_icache;

assign fetch_rdy = fetch_fifo_empty && no_hlt_stall;
wire fetch_fifo_wr;
assign fetch_fifo_wr = (fetch_restart) ? (!bpu_restart) | (!fetch_out_rdy_int) :
                                       (!hlt_restart) & fetch_req_int & fetch_fifo_empty & (!fetch_out_rdy_int);
wire fetch_fifo_rd;
assign fetch_fifo_rd = fetch_fifo_full & (bpu_restart||(!restart_r)) && (fetch_out_rdy_int||fetch_restart); 
wire fetch_fifo_restart;
assign fetch_fifo_restart = fetch_restart || hlt_restart;
npuarc_alb_ifu_fetch_if_fifo fetch_fifo (
  .clk (clk),
  .rst_a (rst_a),
  .restart (fetch_fifo_restart),

  .wr (fetch_fifo_wr),
  .wdata ({
    restart,
    fetch_addr0_muxed,
    fetch_addr1_offset_muxed,
    fetch_bank_ctl_muxed, 
    restart_vec_muxed,
    fetch_seq_muxed,
    fetch_way_sec_muxed,
    fetch_way_req_muxed,
    fetch_way_force_muxed,
    fetch_way_ptr_muxed,
    fetch_iccm0_muxed, 
    fetch_iccm1_muxed, 
    fetch_icache_muxed}),
  .rd (fetch_fifo_rd),
  .rdata ({
    fetch_restart_fifo,
    fetch_addr0_fifo,
    fetch_addr1_offset_fifo,
    fetch_bank_ctl_fifo, 
    fetch_vec_fifo,
    fetch_seq_fifo,
    fetch_way_sec_fifo,
    fetch_way_req_fifo,
    fetch_way_force_fifo,
    fetch_way_ptr_fifo,
    fetch_iccm0_fifo, 
    fetch_iccm1_fifo, 
    fetch_icache_fifo}),
  .rdata_flop(rdata_flop),
  .full (fetch_fifo_full),
  .empty (fetch_fifo_empty),
  .afull (fetch_fifo_afull),
  .aempty (fetch_fifo_aempty)
);

wire [`npuarc_IM_BANKS-1:0] fetch_qual;
assign fetch_qual = fetch_bank_ctl[`npuarc_IM_BANKS-1:0];
wire [`npuarc_IM_BANKS-1:0] fetch_qual_fifo;
assign fetch_qual_fifo = fetch_bank_ctl_fifo[`npuarc_IM_BANKS-1:0];
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg [`npuarc_PC_RANGE] fetch_addr0_last; //we can remove its MSB if the kill is only for iccm

reg [`npuarc_IM_WRD_RANGE] fetch_addr1_offset_last; 
reg [`npuarc_IM_BANKS+1:0] brinfo_bank_ctl_last;
// leda NTL_CON32 on
wire bypass_fifo;
assign bypass_fifo = fetch_fifo_empty; //no entry in fifo at restart 
assign fetch_iccm0_bank_out[0] = (fetch_iccm_kill) ? fetch_iccm0_kill[0] : 
                             (fetch_restart) ? restart_bank_ctl[0] & restart_fetch_iccm0 & bpu_restart: 
                             (!bypass_fifo) ? fetch_qual_fifo[0] & fetch_iccm0_fifo & (!restart | bpu_restart): 
                                              fetch_qual[0] & fetch_iccm0_int;
assign fetch_iccm1_bank_out[0] = (fetch_iccm_kill) ? fetch_iccm1_kill[0] : 
                             (fetch_restart) ? restart_bank_ctl[0] & restart_fetch_iccm1 & bpu_restart: 
                             (!bypass_fifo) ? fetch_qual_fifo[0] & fetch_iccm1_fifo & (!restart | bpu_restart) : 
                                              fetch_qual[0] & fetch_iccm1_int;
assign fetch_iccm0_bank_out[1] = (fetch_iccm_kill) ? fetch_iccm0_kill[1] : 
                             (fetch_restart) ? restart_bank_ctl[1] & restart_fetch_iccm0 & bpu_restart: 
                             (!bypass_fifo) ? fetch_qual_fifo[1] & fetch_iccm0_fifo & (!restart | bpu_restart): 
                                              fetch_qual[1] & fetch_iccm0_int;
assign fetch_iccm1_bank_out[1] = (fetch_iccm_kill) ? fetch_iccm1_kill[1] : 
                             (fetch_restart) ? restart_bank_ctl[1] & restart_fetch_iccm1 & bpu_restart: 
                             (!bypass_fifo) ? fetch_qual_fifo[1] & fetch_iccm1_fifo & (!restart | bpu_restart) : 
                                              fetch_qual[1] & fetch_iccm1_int;
assign fetch_iccm0_out = (|fetch_iccm0_kill) ? 1'b1 :
                         (fetch_restart) ? restart_fetch_iccm0 & bpu_restart :
                         (!bypass_fifo) ? fetch_iccm0_fifo & (!restart | bpu_restart) :
                                          fetch_iccm0_int;
assign fetch_iccm1_out = (|fetch_iccm1_kill) ? 1'b1 :
                         (fetch_restart) ? restart_fetch_iccm1 & bpu_restart :
                         (!bypass_fifo) ? fetch_iccm1_fifo & (!restart | bpu_restart) : 
                                          fetch_iccm1_int;
assign fetch_icache_out = (fetch_restart) ? restart_fetch_icache & bpu_restart :
                          (!bypass_fifo) ? fetch_icache_fifo & (!restart | bpu_restart) :
                                           fetch_icache_int;
assign fetch_is_restart_out = (fetch_restart) ? 1'b1 :
                           (!bypass_fifo) ? fetch_restart_fifo : restart; 
wire fetch_out;
assign fetch_out = (fetch_restart) ? bpu_restart :
                 (!bypass_fifo) ? (!restart) | bpu_restart : fetch_req_int; 
wire [`npuarc_PC_RANGE] fetch_addr0_int; 
assign fetch_addr0_int = (fetch_restart) ? restart_addr0 :
                                   (!bypass_fifo) ? fetch_addr0_fifo : fetch_addr0;
wire [`npuarc_IM_WRD_RANGE] fetch_addr1_offset_int;
assign fetch_addr1_offset_int = (fetch_restart) ? restart_addr1_offset :
                                   (!bypass_fifo) ? fetch_addr1_offset_fifo : fetch_addr1_offset; 
wire [`npuarc_IM_BANKS:0] fetch_bank_ctl_tmp;
assign fetch_bank_ctl_tmp = (fetch_restart) ? restart_bank_ctl :
                                   (!bypass_fifo) ? fetch_bank_ctl_fifo : fetch_bank_ctl;
wire [`npuarc_IM_BANKS+1:0] fetch_bank_ctl_int;
assign fetch_bank_ctl_int = {^fetch_bank_ctl_tmp[`npuarc_IM_BANKS-1:0], fetch_bank_ctl_tmp};
wire fetch_vec_int;
assign fetch_vec_int = (fetch_restart) ? restart_vec:
                     (!bypass_fifo)  ? fetch_vec_fifo : 1'b0;
wire fetch_seq_int;
assign fetch_seq_int = (fetch_restart) ? 1'b0 : //restart cannot be sequential, tag fetch is must
                     (!bypass_fifo) ? fetch_seq_fifo : fetch_seq;
wire fetch_way_sec_int;
assign fetch_way_sec_int = (fetch_restart) ? fetch_way_sec : 
                     (!bypass_fifo) ? fetch_way_sec_fifo : fetch_way_sec;
wire fetch_way_req_int;
assign fetch_way_req_int =   (fetch_restart) ? fetch_way_req :
                           (!bypass_fifo) ? fetch_way_req_fifo : fetch_way_req; 
wire fetch_way_force_int;
assign fetch_way_force_int = (fetch_restart) ? restart_way_vld :
                           (!bypass_fifo) ? fetch_way_force_fifo : fetch_way_force;
wire [`npuarc_IC_WAYS_BITS-1:0] fetch_way_ptr_int;
assign fetch_way_ptr_int = (fetch_restart) ? restart_way :
                           (!bypass_fifo) ? fetch_way_ptr_fifo : fetch_way_ptr;

/////////////////////// registers for re-fetch /////////////////////////////
//This part would be moved to BPU together with the refetch mux
//
// VPOST OFF
reg [`npuarc_IM_BANKS+1:0] brinfo_bank_ctl_r;
always @(posedge clk or posedge rst_a)
begin: re_fetch_hold_PROC
  if (rst_a == 1'b1) begin
    fetch_addr0_last <= {`npuarc_PC_BITS{1'b0}}; 
    fetch_addr1_offset_last <= {`npuarc_IM_WRD_BITS{1'b0}}; 
    brinfo_bank_ctl_last <= {`npuarc_IM_BANKS+2{1'b0}};  
  end
  else begin
    if ( (fetch_req_int || (!bypass_fifo)) && clk2_en && fetch_out_rdy_int ) begin
      fetch_addr0_last <= fetch_addr0_int;
      fetch_addr1_offset_last <= fetch_addr1_offset_int; 
      brinfo_bank_ctl_last <= fetch_bank_ctl_int;
    end
  end
end //block: re_fetch_hold_PROC
// VPOST ON

//outputs
assign fetch_addr0_out = (fetch_iccm_kill) ? fetch_addr0_last : fetch_addr0_int;
assign fetch_addr1_offset_out = (fetch_iccm_kill) ? fetch_addr1_offset_last : fetch_addr1_offset_int;
assign fetch_bank_ctl_out = (fetch_iccm_kill)? brinfo_bank_ctl_last : fetch_bank_ctl_int;
assign fetch_vec_out = fetch_vec_int;
assign fetch_seq_out = fetch_seq_int;
assign fetch_way_sec_out = fetch_way_sec_int;
assign fetch_way_req_out = fetch_way_req_int;
assign fetch_way_force_out = fetch_way_force_int;
assign fetch_way_ptr_out = fetch_way_ptr_int;
 
assign refetch = fetch_iccm_kill; //this is the only case we are taking care of for refetch from top level

assign brinfo_kill_2nd_out = brinfo_kill_2nd;
assign brinfo_is_br_out = brinfo_is_br;
assign brinfo_is_br_last_out = brinfo_is_br_last;
assign brinfo_bta_out = brinfo_bta;
assign brinfo_br_offset_out = brinfo_br_offset;
assign brinfo_pkt_out = brinfo_pkt;
assign brinfo_bank_ctl_out = brinfo_bank_ctl_r;
assign brinfo_bta_miss_out = brinfo_bta_miss;
assign brinfo_bta_miss_offset_out = brinfo_bta_miss_offset;

////////////////////////// brinfo valid gen //////////////////////////
//Whenever the request input is granted, we need to store 
//  the one cycle delayed brinfo by this valid signal
wire way_pred_bank_id_nxt;

assign way_pred_bank_id_nxt = (brinfo_bank_ctl_r[`npuarc_IM_BANKS] ^ brinfo_br_offset[`npuarc_IM_WORD_BITS-1]) & ~fetch_restart;

wire way_pred_tail_nxt;
assign way_pred_tail_nxt = brinfo_is_br_out & (!brinfo_is_br_last);
wire brinfo_vld_nxt;
assign brinfo_vld_nxt = (fetch_req||fetch_restart) && (fetch_rdy||bpu_restart);
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs
// LJ:  a reg value to standard fifo
reg way_pred_bank_id_r;
reg way_pred_tail_r;

always @(posedge clk or posedge rst_a) 
begin: br_info_dly_ctl_PROC
  if (rst_a == 1'b1) begin
    brinfo_vld            <= 1'b0;
    brinfo_is_restart_out <= 1'b0;
    brinfo_bank_ctl_r     <= {`npuarc_IM_BANKS+2{1'b0}}; 
    way_pred_bank_id_r    <= 1'b0;
    way_pred_tail_r       <= 1'b0;
  end
  else if (clk2_en) begin
    brinfo_vld            <= brinfo_vld_nxt;
    brinfo_is_restart_out <= brinfo_vld_nxt ? restart            : brinfo_is_restart_out;
    brinfo_bank_ctl_r     <= brinfo_vld_nxt ? fetch_bank_ctl_int : brinfo_bank_ctl_r;
    // holding brinfo
    way_pred_bank_id_r    <= brinfo_vld ? way_pred_bank_id_nxt : way_pred_bank_id_r;
    way_pred_tail_r       <= brinfo_vld ? way_pred_tail_nxt    : way_pred_tail_r;
  end
end //block: br_info_dly_ctl_PROC
// leda NTL_CON32 on

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  signal from fifo
wire way_pred_info_fifo_full;
wire way_pred_info_fifo_afull;
wire way_pred_info_fifo_aempty;
wire way_pred_rdata_flop;
wire way_pred_bank_id_fifo;
wire way_pred_tail_fifo;
// leda NTL_CON13A on

wire way_pred_info_fifo_empty;
wire way_pred_bank_id_int;
assign way_pred_bank_id_int = (brinfo_vld) ? way_pred_bank_id_nxt : way_pred_bank_id_r;
wire way_pred_tail_int;
assign way_pred_tail_int = (restart) ? 1'b0 : (brinfo_vld) ? way_pred_tail_nxt : way_pred_tail_r; 
wire way_pred_info_fifo_bypass;
assign way_pred_info_fifo_bypass = (way_pred_info_fifo_empty || restart) && fetch_out && fetch_out_rdy;
wire way_pred_info_fifo_wr;
assign way_pred_info_fifo_wr = brinfo_vld_nxt && (!way_pred_info_fifo_bypass) && clk2_en;
wire way_pred_info_fifo_rd;
assign way_pred_info_fifo_rd = fetch_out && fetch_out_rdy && (!way_pred_info_fifo_bypass) && clk2_en; 
npuarc_alb_ifu_fetch_if_wp_fifo  way_pred_info_fifo (

  .clk (clk),
  .rst_a (rst_a),
  .restart(restart),
  .wr (way_pred_info_fifo_wr), 
  .wdata ({way_pred_bank_id_int, way_pred_tail_int}),
  .rd (way_pred_info_fifo_rd),
  .rdata ({way_pred_bank_id_fifo, way_pred_tail_fifo}),
  .rdata_flop(way_pred_rdata_flop),
  .full (way_pred_info_fifo_full),
  .empty (way_pred_info_fifo_empty), 
  .afull (way_pred_info_fifo_afull),
  .aempty (way_pred_info_fifo_aempty)
);  


assign fetch_way_bank_id_out = (way_pred_info_fifo_empty||restart) ? way_pred_bank_id_int : way_pred_bank_id_fifo;

assign fetch_way_tail_out = (way_pred_info_fifo_empty||restart) ? way_pred_tail_int : way_pred_tail_fifo;
//fetch restart/halt logic
parameter RUN = 2'd0;
parameter HALT_PRE_WAIT = 2'd1;
parameter HALT_POST_WAIT = 2'd2;
parameter HALTED = 2'd3;

reg [1:0] halt_state;
reg [1:0] pipe_wait_cnt;

assign ifu_active = (halt_state == RUN);

wire[1:0] halt_state_next;
reg [1:0] halt_state_nxt;
reg [1:0] pipe_wait_cnt_nxt;
reg       ifu_idle_nxt;
reg       hlt_stall_nxt;
reg       no_hlt_stall_nxt;

assign halt_state_next = 
                        halt_state_nxt;

// HALT STATE 
//
always @(posedge clk or posedge rst_a) 
begin: halt_state_r_PROC
  if (rst_a == 1'b1)
    halt_state      <= HALT_PRE_WAIT;
  else
    halt_state      <= halt_state_next;
end // block: halt_state_r_PROC

// spyglass disable_block STARC05-2.11.3.1
// SMD: Combinational and sequential parts of an FSM in same block
// SJ:  Design feature
always @(posedge clk or posedge rst_a) 
begin: halt_run_PROC
  if (rst_a == 1'b1) begin
    hlt_stall       <= 1'b1;
    no_hlt_stall    <= 1'b0;
    ifu_idle_r      <= 1'b0;
    pipe_wait_cnt   <= 2'b0;
  end
  else begin
//leda  W71 off
// LMD: Case statement without default clause and not all cases are covered
// LJ:  Default output assignments are from above
// leda B_3200 off
// leda W484 off
// leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  count will not overflow 
    hlt_stall       <= hlt_stall_nxt;
    no_hlt_stall    <= no_hlt_stall_nxt;
    ifu_idle_r      <= ifu_idle_nxt;
    pipe_wait_cnt   <= pipe_wait_cnt_nxt;
// leda BTTF_D002 on
// leda W484 on
// leda B_3200 on
//leda  W71 on
  end
end //block: halt_run_PROC 
// spyglass enable_block STARC05-2.11.3.1

always @(*) 
begin: halt_run_logic_PROC

  halt_state_nxt          = halt_state;
  pipe_wait_cnt_nxt       = pipe_wait_cnt;
  ifu_idle_nxt            = ifu_idle_r;
  hlt_stall_nxt           = hlt_stall;
  no_hlt_stall_nxt        = no_hlt_stall;

  // restart 
  if (fetch_restart 
         & (~mmu_restart)
       )  
  begin
    halt_state_nxt         = RUN;
    ifu_idle_nxt           = 1'b0;
    hlt_stall_nxt          = 1'b0;
    no_hlt_stall_nxt       = 1'b1;
  end
  else begin
    case (halt_state)
      RUN: begin
        if (hlt_restart) begin
          halt_state_nxt    = HALT_PRE_WAIT;
          hlt_stall_nxt     = 1'b1;
          no_hlt_stall_nxt  = 1'b0;
          pipe_wait_cnt_nxt = 2'b0; 
        end
      end
      HALT_PRE_WAIT: begin // so that fetch can get in the memories
        if ((&pipe_wait_cnt) && ifu_hlt_rdy) begin
          halt_state_nxt    = HALT_POST_WAIT;
          pipe_wait_cnt_nxt = 2'b0;
        end 
        else begin
          pipe_wait_cnt_nxt = pipe_wait_cnt + 1;
        end
      end
      HALT_POST_WAIT: begin // so that fetch can get output of the memories
        if (!ifu_hlt_rdy) begin // any mis-detection of ifu_hlt_rdy will roll back
          halt_state_nxt    = HALT_PRE_WAIT;
          pipe_wait_cnt_nxt = 2'b0;
        end
        else if ((&pipe_wait_cnt) && ifu_hlt_rdy) begin
          halt_state_nxt    = HALTED;
          ifu_idle_nxt      = 1'b1;
          pipe_wait_cnt_nxt = 2'b0;
        end 
        else begin
          pipe_wait_cnt_nxt = pipe_wait_cnt + 1;
        end
      end
      HALTED: begin
        ifu_idle_nxt        = 1'b1;
      end
    endcase    
  end
end //block: halt_run_logic_PROC 

endmodule
