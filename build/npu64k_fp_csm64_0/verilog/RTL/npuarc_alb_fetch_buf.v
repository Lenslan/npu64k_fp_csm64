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
// This module implements the fetch buffer that stores the fetch block from Imem
// It has a parameterized fetch buffer depth
// It takes a only cycle late ack signal from the alignment stage
// It can bypass the data input to the output incase its buffer is empty
// It measures the fetch buffer capacity and deliver ready signal (buf_data_in_rdy)
//  to the upper stream
// Down pipe is alignment 
// ===========================================================================
 
`include "npuarc_defines.v"
// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_fetch_buf_data_fifo_edc_err" }
//D: error_signal { name: "alb_fetch_buf_br_fifo_edc_err" }

module npuarc_alb_fetch_buf
  (
  input [`npuarc_IM_WIDTH-1:0]       buf_data_in,
  input [1:0]                 buf_data_in_vld,
  input [`npuarc_FCH_EXCPN_1H_RANGE] buf_data_in_err,

  input [`npuarc_ITLB_EXEC_PERM_RANGE] buf_data_in_experm,

  input                       buf_data_in_iprot_viol,

  input [`npuarc_IC_WAYS_BITS-1:0]   buf_data_in_way,

  input                       buf_in_ecc_enable,


  output                      buf_data_in_rdy,

  input                       buf_data_restart_in,
  input [1:0]                 buf_data_br_in,
  input [1:0]                 buf_data_first_word_in,
  input                       buf_data_br_last_in,
  input [`npuarc_PC_RANGE]           buf_data_bta_in,
  input [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] buf_data_br_offset_in,
  input [`npuarc_BR_INFO_PKT_RANGE]  buf_data_pkt_in,
  input [`npuarc_IM_BANKS-1:0]       buf_data_bank_ctl_in,

  // leda NTL_CON13C off
  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  all bits of used
  input [1:0]                 buf_data_bank_cnt_in,
  input [1:0]                 buf_bta_in_bank_cnt,
  // leda NTL_CON13C on  
  // leda NTL_CON37 on 

  input [`npuarc_IM_BANKS-1:0]       buf_bta_in_vld,
  input                       bta_tail_stall,
  output                      buf_bta_in_rdy,

  input                       buf_taken,
  input                       buf_taken_single,
  input [1:0]                 buf_taken_count_nxt,

///////////////////////////////////////////////////////////////////////
// Instruction interface to alignment 
//
  output reg [`npuarc_IM_WIDTH/2-1:0]      buf_data_out_w0,
  output reg                        buf_data_out_vld0,
  output reg [`npuarc_FCH_EXCPN_1H_RANGE]  buf_data_out_err0,

  output reg [`npuarc_ITLB_EXEC_PERM_RANGE] buf_data_out_experm0,

  output reg                        buf_data_out_iprot_viol0,

  output reg                        buf_out_ecc_enable0,


  output reg [`npuarc_IC_WAYS_BITS-1:0]    buf_data_out_way0,

///////////////////////////////////////////////////////////////////////
// Branch interface to alignment 
//
  output reg [`npuarc_BR_INFO_PKT_RANGE]       buf_data_out_pkt0,
  output reg [`npuarc_PC_RANGE]                buf_data_out_bta0,

  output reg [`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB]  buf_data_out_br_offset0,
  output reg                            buf_data_out_first_word0,
  output reg [1:0]                      buf_data_out_bank_ctl0,

  output reg [`npuarc_IM_WIDTH/2-1:0]      buf_data_out_w1,
  output reg                        buf_data_out_vld1,
  output reg [`npuarc_FCH_EXCPN_1H_RANGE]  buf_data_out_err1,

  output reg [`npuarc_ITLB_EXEC_PERM_RANGE] buf_data_out_experm1,

  output reg                        buf_data_out_iprot_viol1,

  output reg                        buf_out_ecc_enable1,


  output reg [`npuarc_IC_WAYS_BITS-1:0]    buf_data_out_way1,

///////////////////////////////////////////////////////////////////////
// Branch interface to alignment 
//
  output reg [`npuarc_BR_INFO_PKT_RANGE]       buf_data_out_pkt1,
  output reg [`npuarc_PC_RANGE]                buf_data_out_bta1,

  output reg [`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB]  buf_data_out_br_offset1,
  output reg                            buf_data_out_first_word1,
  output reg [1:0]                      buf_data_out_bank_ctl1,


  input                          clk,
  input                          clk2_en, //to qualify buffer inputs
  input                          rst_a,
  input                          restart
  );


/////////////////////////////////////////////////////////////////////////////////////////
// Local Signal Declarations
//
wire [1+1:0]    fetch_buf_cnt;
wire [1+1:0]    fetch_buf_cnt_nxt;

wire [1+1:0]    bta_buf_cnt;
wire [1+1:0]    bta_buf_cnt_nxt;

// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  all bits used
reg [1+1:0]     bta_buf_cnt_rd;
reg [1+1:0]     fetch_buf_cnt_rd;
// leda NTL_CON13A on

reg [`npuarc_IM_BANKS-1:0]   fifo_rd_ok;
wire [`npuarc_IM_BANKS-1:0]  fetch_buf_wr;
wire [`npuarc_IM_BANKS-1:0]  bta_buf_wr;
wire [`npuarc_IM_BANKS-1:0]  fetch_buf_rd;
wire [`npuarc_IM_BANKS-1:0]  buf_data_in_vld_qual;
wire [`npuarc_IM_BANKS-1:0]  buf_bta_in_vld_qual;
wire                  fifo_wr_ok;

wire                   buf_data_first_word_fifo0;

wire [`npuarc_PC_RANGE]       buf_data_bta_in_fifo0;
wire [`npuarc_IM_WIDTH/2-1:0] buf_data_in_fifo0;
wire [`npuarc_FCH_EXCPN_1H_RANGE] buf_data_in_err_fifo0;

wire [`npuarc_ITLB_EXEC_PERM_RANGE] buf_data_in_experm_fifo0;

wire                   buf_data_in_iprot_viol_fifo0;

wire [`npuarc_IC_WAYS_BITS-1:0] buf_data_in_way_fifo0;

wire                    buf_ecc_enable_fifo0;



wire [`npuarc_IM_BANKS-1:0]    buf_data_bank_ctl_in_fifo0;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused from fifo
wire                    buf_data_restart_fifo0;
wire                    buf_data_restart_fifo1;
wire                    buf_data_br_in_fifo0;
wire                    buf_data_br_last_in_fifo0;
wire [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] buf_data_br_offset_in_fifo0;
wire                    buf_data_br_in_fifo1;
wire                    buf_data_br_last_in_fifo1;
// leda NTL_CON13A on

wire [`npuarc_BR_INFO_PKT_RANGE] buf_data_pkt_in_fifo0;

wire                      buf_data_first_word_fifo1;

wire [`npuarc_PC_RANGE]          buf_data_bta_in_fifo1;
wire [`npuarc_IM_WIDTH/2-1:0]    buf_data_in_fifo1;
wire [`npuarc_FCH_EXCPN_1H_RANGE] buf_data_in_err_fifo1;

wire [`npuarc_ITLB_EXEC_PERM_RANGE] buf_data_in_experm_fifo1;

wire                      buf_data_in_iprot_viol_fifo1;

wire [`npuarc_IC_WAYS_BITS-1:0]   buf_data_in_way_fifo1;

wire                       buf_ecc_enable_fifo1;


wire [`npuarc_IM_BANKS-1:0]       buf_data_bank_ctl_in_fifo1;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused bit from fifo
wire [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] buf_data_br_offset_in_fifo1;
wire                           buf_data_restart_fifo_next0;
wire                           buf_data_restart_fifo_next1;
// leda NTL_CON13A on

wire [`npuarc_BR_INFO_PKT_RANGE]      buf_data_pkt_in_fifo1;

wire                           buf_data_first_word_fifo_next0;

wire [`npuarc_PC_RANGE]               buf_data_bta_in_fifo_next0;
wire [`npuarc_IM_WIDTH/2-1:0]         buf_data_in_fifo_next0;
wire [`npuarc_FCH_EXCPN_1H_RANGE]     buf_data_in_err_fifo_next0;

wire [`npuarc_ITLB_EXEC_PERM_RANGE]   buf_data_in_experm_fifo_next0;

wire                          buf_data_in_iprot_viol_fifo_next0;

wire [`npuarc_IC_WAYS_BITS-1:0]      buf_data_in_way_fifo_next0;

wire                          buf_ecc_enable_fifo_next0;


wire [`npuarc_IM_BANKS-1:0]          buf_data_bank_ctl_in_fifo_next0;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused bit from fifo
wire [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] buf_data_br_offset_in_fifo_next0;
wire                           buf_data_br_in_fifo_next0;
wire                           buf_data_br_last_in_fifo_next0;
// leda NTL_CON13A on

wire [`npuarc_BR_INFO_PKT_RANGE]      buf_data_pkt_in_fifo_next0;

wire                           buf_data_first_word_fifo_next1;

wire [`npuarc_PC_RANGE]               buf_data_bta_in_fifo_next1;
wire [`npuarc_IM_WIDTH/2-1:0]         buf_data_in_fifo_next1;
wire [`npuarc_FCH_EXCPN_1H_RANGE]     buf_data_in_err_fifo_next1;

wire [`npuarc_ITLB_EXEC_PERM_RANGE]   buf_data_in_experm_fifo_next1;

wire                           buf_data_in_iprot_viol_fifo_next1;

wire [`npuarc_IC_WAYS_BITS-1:0]       buf_data_in_way_fifo_next1;

wire                           buf_ecc_enable_fifo_next1;


wire [`npuarc_IM_BANKS-1:0]           buf_data_bank_ctl_in_fifo_next1;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused bit from fifo
wire [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] buf_data_br_offset_in_fifo_next1;
wire                           buf_data_br_in_fifo_next1;
wire                           buf_data_br_last_in_fifo_next1;
// leda NTL_CON13A on

wire [`npuarc_BR_INFO_PKT_RANGE]      buf_data_pkt_in_fifo_next1;

reg [`npuarc_IM_WIDTH/2-1:0]          buf_data_out_w0_int;
reg [`npuarc_IM_WIDTH/2-1:0]          buf_data_out_w1_int;



/////////////////////////////////////////////////////////////////////////////////////////
// Logic
//

assign  fetch_buf_rd = fifo_rd_ok;

assign  buf_data_in_vld_qual = buf_data_in_vld & {`npuarc_IM_BANKS{clk2_en}};

assign  buf_bta_in_vld_qual = buf_bta_in_vld & {`npuarc_IM_BANKS{clk2_en}};

// spyglass disable_block WRN_1024
// SMD: unsigned argument passed to $unsigned function call
// SJ:  arguments unsigned by default

assign   fifo_wr_ok = !bta_tail_stall &&
            ( fetch_buf_cnt_rd[1+1] || 
              ($unsigned(fetch_buf_cnt_rd[1:0]) <= $unsigned(`npuarc_FETCH_BUF_DEPTH-buf_data_bank_cnt_in)) );

wire bta_wr_ok;
assign  bta_wr_ok  = bta_buf_cnt_rd[1+1] ||
              ($unsigned(bta_buf_cnt_rd[1:0]) <= $unsigned(`npuarc_FETCH_BUF_DEPTH-buf_bta_in_bank_cnt));

// spyglass enable_block WRN_1024

/////////////////////////// FIFO that implements the storage for fetch buffer ////////////////
//bank data is stored seperately
//
//`if (`HAS_ICACHE == 1)
//alb_fetch_buf_fifo #(5+`IC_WAYS_BITS+`IM_BANKS+`IM_WORD_BITS-`PC_LSB+`IM_WIDTH/2+`BR_INFO_PKT_BITS, 
//`else
//alb_fetch_buf_fifo #(5+`IM_BANKS+`IM_WORD_BITS-`PC_LSB+`IM_WIDTH/2+`BR_INFO_PKT_BITS, 
//`endif

npuarc_alb_fetch_buf_data_fifo alb_fetch_buf_fifo_u(
  .clk(clk),
  .rst_a(rst_a),
  .restart(restart),
  .wr(fetch_buf_wr),
  .wdata0({buf_data_restart_in,
    buf_data_first_word_in[0],
    buf_data_br_in[0],
    buf_data_br_last_in,
    buf_data_bank_ctl_in,
    buf_data_br_offset_in,
    buf_data_pkt_in,
    buf_data_in_err, 
    buf_data_in_experm, 
    buf_data_in_iprot_viol, 
    buf_in_ecc_enable,

    buf_data_in_way,
    buf_data_in[`npuarc_IM_WIDTH/`npuarc_IM_BANKS-1:0]}),
  .wdata1({
    buf_data_restart_in,
    buf_data_first_word_in[1],
    buf_data_br_in[1],
    buf_data_br_last_in,
    buf_data_bank_ctl_in,
    buf_data_br_offset_in,
    buf_data_pkt_in,
    buf_data_in_err,
    buf_data_in_experm,
    buf_data_in_iprot_viol,
    buf_in_ecc_enable,

    buf_data_in_way,
    buf_data_in[`npuarc_IM_WIDTH-1:`npuarc_IM_WIDTH/`npuarc_IM_BANKS]}),
  .rd(fetch_buf_rd),
  .rdata0({
    buf_data_restart_fifo0,
    buf_data_first_word_fifo0,
    buf_data_br_in_fifo0,
    buf_data_br_last_in_fifo0,
    buf_data_bank_ctl_in_fifo0,
    buf_data_br_offset_in_fifo0,
    buf_data_pkt_in_fifo0,
    buf_data_in_err_fifo0, 
    buf_data_in_experm_fifo0, 
    buf_data_in_iprot_viol_fifo0, 
    buf_ecc_enable_fifo0,

    buf_data_in_way_fifo0,
    buf_data_in_fifo0}),
  .rdata1({
    buf_data_restart_fifo1,
    buf_data_first_word_fifo1,
    buf_data_br_in_fifo1,
    buf_data_br_last_in_fifo1,
    buf_data_bank_ctl_in_fifo1,
    buf_data_br_offset_in_fifo1,
    buf_data_pkt_in_fifo1,
    buf_data_in_err_fifo1, 
    buf_data_in_experm_fifo1, 
    buf_data_in_iprot_viol_fifo1, 
    buf_ecc_enable_fifo1,

    buf_data_in_way_fifo1,
    buf_data_in_fifo1}),
  .rdata_next0({
    buf_data_restart_fifo_next0,
    buf_data_first_word_fifo_next0,
    buf_data_br_in_fifo_next0,
    buf_data_br_last_in_fifo_next0,
    buf_data_bank_ctl_in_fifo_next0,
    buf_data_br_offset_in_fifo_next0,
    buf_data_pkt_in_fifo_next0,
    buf_data_in_err_fifo_next0, 
    buf_data_in_experm_fifo_next0, 
    buf_data_in_iprot_viol_fifo_next0, 
    buf_ecc_enable_fifo_next0,

    buf_data_in_way_fifo_next0,
    buf_data_in_fifo_next0}),
  .rdata_next1({
    buf_data_restart_fifo_next1,
    buf_data_first_word_fifo_next1,
    buf_data_br_in_fifo_next1,
    buf_data_br_last_in_fifo_next1,
    buf_data_bank_ctl_in_fifo_next1,
    buf_data_br_offset_in_fifo_next1,
    buf_data_pkt_in_fifo_next1,
    buf_data_in_err_fifo_next1, 
    buf_data_in_experm_fifo_next1, 
    buf_data_in_iprot_viol_fifo_next1, 
    buf_ecc_enable_fifo_next1,

    buf_data_in_way_fifo_next1,
    buf_data_in_fifo_next1}),
  .fifo_cnt(fetch_buf_cnt),
  .fifo_cnt_nxt (fetch_buf_cnt_nxt )
);

npuarc_alb_fetch_buf_br_fifo  alb_fetch_buf_bta_fifo_u(
  .clk(clk),
  .rst_a(rst_a),
  .restart(restart),
  .wr(bta_buf_wr),
  .wdata0(buf_data_bta_in),
  .wdata1(buf_data_bta_in),
  .rd(fetch_buf_rd),
  .rdata0(buf_data_bta_in_fifo0),
  .rdata1(buf_data_bta_in_fifo1),
  .rdata_next0(buf_data_bta_in_fifo_next0),
  .rdata_next1(buf_data_bta_in_fifo_next1),
  .fifo_cnt(bta_buf_cnt),
  .fifo_cnt_nxt(bta_buf_cnt_nxt)
);

reg [`npuarc_IM_WIDTH-1:0] buf_data ;
reg [`npuarc_PC_RANGE] buf_data_bta0 ;
reg [`npuarc_PC_RANGE] buf_data_bta1 ;
reg [`npuarc_FCH_EXCPN_1H_RANGE] buf_data_err0;
reg [`npuarc_FCH_EXCPN_1H_RANGE] buf_data_err1;
reg [`npuarc_ITLB_EXEC_PERM_RANGE] buf_data_experm0;
reg [`npuarc_ITLB_EXEC_PERM_RANGE] buf_data_experm1;
reg buf_data_iprot_viol0;
reg buf_data_iprot_viol1;
reg [1:0] buf_data_vld ;
reg [1:0] bta_data_vld ;
reg [1:0] buf_ecc_enable;

reg [`npuarc_IC_WAYS_BITS-1:0] buf_data_way0;
reg [`npuarc_IC_WAYS_BITS-1:0] buf_data_way1;
reg buf_data_first_word0 ;
reg buf_data_first_word1 ;
reg [`npuarc_IM_BANKS-1:0] buf_data_bank_ctl0;
reg [`npuarc_IM_BANKS-1:0] buf_data_bank_ctl1;
reg [`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB] buf_data_br_offset0;
reg [`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB] buf_data_br_offset1;
reg [`npuarc_BR_INFO_PKT_RANGE] buf_data_pkt0;
reg [`npuarc_BR_INFO_PKT_RANGE] buf_data_pkt1;

/////////////////// FIFO output mux for current output //////////////////////////
//depends on how many entries in the FIFO, the output can be from bypassed input 
//
always @(*) 
begin: bta_mux_PROC
  if (bta_buf_cnt==0) begin
    bta_data_vld[0] = buf_bta_in_vld_qual[0];
    bta_data_vld[1] = buf_bta_in_vld_qual[1];
    buf_data_bta0 = buf_data_bta_in;
    buf_data_bta1 = buf_data_bta_in;
  end
  else if (bta_buf_cnt==1) begin
    bta_data_vld[0] = 1'b1;
    bta_data_vld[1] = buf_bta_in_vld_qual[0];
    buf_data_bta0 = buf_data_bta_in_fifo0;
    buf_data_bta1 = buf_data_bta_in;
  end
  else begin
    if (bta_buf_cnt_rd[1+1]) begin
      bta_data_vld = 2'b00;
    end
    else begin
      bta_data_vld = 2'b11;
    end
    buf_data_bta0 = buf_data_bta_in_fifo0;
    buf_data_bta1 = buf_data_bta_in_fifo1;
  end
end

always @(*) 
begin: buf_mux_PROC
  if (fetch_buf_cnt==0) begin
    buf_data_vld[0] = buf_data_in_vld_qual[0];
    buf_data_vld[1] = buf_data_in_vld_qual[1];
    buf_data_err0 = buf_data_in_err;
    buf_data_err1 = buf_data_in_err;
    buf_data_experm0 = buf_data_in_experm;
    buf_data_experm1 = buf_data_in_experm;
    buf_data_iprot_viol0 = buf_data_in_iprot_viol;
    buf_data_iprot_viol1 = buf_data_in_iprot_viol;
    buf_ecc_enable = {buf_in_ecc_enable, buf_in_ecc_enable};
    buf_data_way0 = buf_data_in_way;
    buf_data_way1 = buf_data_in_way;
    buf_data = buf_data_in;
    buf_data_first_word0 = buf_data_first_word_in[0];
    buf_data_first_word1 = buf_data_first_word_in[1];
    buf_data_bank_ctl0 = buf_data_bank_ctl_in; 
    buf_data_bank_ctl1 = buf_data_bank_ctl_in; 
    buf_data_br_offset0 = buf_data_br_offset_in[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB]; 
    buf_data_br_offset1 = buf_data_br_offset_in[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB]; 
    buf_data_pkt0 = buf_data_pkt_in; 
    buf_data_pkt1 = buf_data_pkt_in; 
  end 
  else if (fetch_buf_cnt==1) begin
    buf_data_vld[0] = 1'b1;
    buf_data_vld[1] = buf_data_in_vld_qual[0];
    buf_data_err1 = buf_data_in_err;
    buf_data_err0 = buf_data_in_err_fifo0;
    buf_data_experm1 = buf_data_in_experm;
    buf_data_experm0 = buf_data_in_experm_fifo0;
    buf_data_iprot_viol1 = buf_data_in_iprot_viol;
    buf_data_iprot_viol0 = buf_data_in_iprot_viol_fifo0;
    buf_ecc_enable = {buf_in_ecc_enable, buf_ecc_enable_fifo0};
    buf_data_way0 = buf_data_in_way_fifo0;
    buf_data_way1 = buf_data_in_way;
    buf_data = {buf_data_in[`npuarc_IM_WIDTH/2-1:0], buf_data_in_fifo0};
    buf_data_first_word0 = buf_data_first_word_fifo0;
    buf_data_first_word1 = buf_data_first_word_in[0];
    buf_data_bank_ctl0 = buf_data_bank_ctl_in_fifo0;
    buf_data_bank_ctl1 = buf_data_bank_ctl_in;
    buf_data_br_offset0 = buf_data_br_offset_in_fifo0[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_br_offset1 = buf_data_br_offset_in[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_pkt0 = buf_data_pkt_in_fifo0;
    buf_data_pkt1 = buf_data_pkt_in;
  end
  else begin
    if (fetch_buf_cnt_rd[1+1]) begin
      buf_data_vld = 2'b00;
    end
    else begin
      buf_data_vld = 2'b11;
    end
    buf_data_err1 = buf_data_in_err_fifo1;
    buf_data_err0 = buf_data_in_err_fifo0;
    buf_data_experm1 = buf_data_in_experm_fifo1;
    buf_data_experm0 = buf_data_in_experm_fifo0;
    buf_data_iprot_viol1 = buf_data_in_iprot_viol_fifo1;
    buf_data_iprot_viol0 = buf_data_in_iprot_viol_fifo0;
    buf_ecc_enable = {buf_ecc_enable_fifo1, buf_ecc_enable_fifo0};
    buf_data_way0 = buf_data_in_way_fifo0;
    buf_data_way1 = buf_data_in_way_fifo1;
    buf_data = {buf_data_in_fifo1, buf_data_in_fifo0};
    buf_data_first_word0 = buf_data_first_word_fifo0;
    buf_data_first_word1 = buf_data_first_word_fifo1;
    buf_data_bank_ctl0 = buf_data_bank_ctl_in_fifo0;
    buf_data_bank_ctl1 = buf_data_bank_ctl_in_fifo1;
    buf_data_br_offset0 = buf_data_br_offset_in_fifo0[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_br_offset1 = buf_data_br_offset_in_fifo1[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_pkt0 = buf_data_pkt_in_fifo0;
    buf_data_pkt1 = buf_data_pkt_in_fifo1;
  end
end

reg [`npuarc_IM_WIDTH-1:0] buf_data_next;
reg [`npuarc_PC_RANGE] buf_data_bta0_next;
reg [`npuarc_PC_RANGE] buf_data_bta1_next;
reg [`npuarc_FCH_EXCPN_1H_RANGE] buf_data_err0_next;
reg [`npuarc_FCH_EXCPN_1H_RANGE] buf_data_err1_next;
reg [`npuarc_ITLB_EXEC_PERM_RANGE]   buf_data_experm0_next;
reg [`npuarc_ITLB_EXEC_PERM_RANGE]   buf_data_experm1_next;
reg buf_data_iprot_viol0_next;
reg buf_data_iprot_viol1_next;
reg [1:0] buf_data_vld_next;
reg [1:0] bta_data_vld_next;
reg [1:0] buf_ecc_enable_next;

reg [`npuarc_IC_WAYS_BITS-1:0] buf_data_way0_next;
reg [`npuarc_IC_WAYS_BITS-1:0] buf_data_way1_next;
reg buf_data_first_word_next0;
reg buf_data_first_word_next1;
reg [`npuarc_IM_BANKS-1:0] buf_data_bank_ctl_next0;
reg [`npuarc_IM_BANKS-1:0] buf_data_bank_ctl_next1;
reg [`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB] buf_data_br_offset_next0;
reg [`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB] buf_data_br_offset_next1;
reg [`npuarc_BR_INFO_PKT_RANGE] buf_data_pkt_next0;
reg [`npuarc_BR_INFO_PKT_RANGE] buf_data_pkt_next1;

///////////////////////////////// FIFO output mux for next output ///////////////////// 
//depends on how many entries in the FIFO, the output can be from bypassed input 
//
always @(*) 
begin: bta_next_mux_PROC
  if (bta_buf_cnt==2) begin
    buf_data_bta0_next = buf_data_bta_in;
    buf_data_bta1_next = buf_data_bta_in;
    bta_data_vld_next = buf_bta_in_vld_qual;
  end
  else begin
    buf_data_bta0_next = buf_data_bta_in_fifo_next0;
    buf_data_bta1_next = buf_data_bta_in_fifo_next1;
    if (bta_buf_cnt_rd[1+1] || (bta_buf_cnt <=1)) begin
    bta_data_vld_next = 2'b00;
    end
    else begin
    bta_data_vld_next = 2'b11;
    end 
  end
end

always @(*) 
begin: buf_next_mux_PROC
  if (fetch_buf_cnt==2) begin
    buf_data_next = buf_data_in;
    buf_data_vld_next = buf_data_in_vld_qual;
    buf_data_err1_next= buf_data_in_err;
    buf_data_err0_next= buf_data_in_err;
    buf_data_experm1_next= buf_data_in_experm;
    buf_data_experm0_next= buf_data_in_experm;
    buf_data_iprot_viol1_next= buf_data_in_iprot_viol;
    buf_data_iprot_viol0_next= buf_data_in_iprot_viol;
    buf_ecc_enable_next = {buf_in_ecc_enable, buf_in_ecc_enable};
    buf_data_way0_next = buf_data_in_way;
    buf_data_way1_next = buf_data_in_way;
    buf_data_first_word_next0 = buf_data_first_word_in[0];
    buf_data_first_word_next1 = buf_data_first_word_in[1];
    buf_data_bank_ctl_next0 = buf_data_bank_ctl_in;
    buf_data_bank_ctl_next1 = buf_data_bank_ctl_in;
    buf_data_br_offset_next0 = buf_data_br_offset_in[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_br_offset_next1 = buf_data_br_offset_in[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_pkt_next0 = buf_data_pkt_in;
    buf_data_pkt_next1 = buf_data_pkt_in;
  end
  else begin
    buf_data_next = {buf_data_in_fifo_next1, buf_data_in_fifo_next0};
    if (fetch_buf_cnt_rd[1+1] || (fetch_buf_cnt <=1)) begin
    buf_data_vld_next = 2'b00;
    end
    else begin
    buf_data_vld_next = 2'b11;
    end 
    buf_data_err1_next = buf_data_in_err_fifo_next1;
    buf_data_err0_next = buf_data_in_err_fifo_next0;
    buf_data_experm1_next = buf_data_in_experm_fifo_next1;
    buf_data_experm0_next = buf_data_in_experm_fifo_next0;
    buf_data_iprot_viol1_next = buf_data_in_iprot_viol_fifo_next1;
    buf_data_iprot_viol0_next = buf_data_in_iprot_viol_fifo_next0;
    buf_ecc_enable_next = {buf_ecc_enable_fifo_next1, buf_ecc_enable_fifo_next0};

    buf_data_way0_next = buf_data_in_way_fifo_next0;
    buf_data_way1_next = buf_data_in_way_fifo_next1;
    buf_data_first_word_next0 = buf_data_first_word_fifo_next0;
    buf_data_first_word_next1 = buf_data_first_word_fifo_next1;
    buf_data_bank_ctl_next0 = buf_data_bank_ctl_in_fifo_next0;
    buf_data_bank_ctl_next1 = buf_data_bank_ctl_in_fifo_next1;
    buf_data_br_offset_next0 = buf_data_br_offset_in_fifo_next0[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_br_offset_next1 = buf_data_br_offset_in_fifo_next1[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_pkt_next0 = buf_data_pkt_in_fifo_next0;
    buf_data_pkt_next1 = buf_data_pkt_in_fifo_next1;
  end
end

///////////////////////////// fifo read control ///////////////////////////
//the taken inputs decide on the read
//The taken inputs are one cycle delayed from actual cycle the data is read
//
reg [1:0] buf_rd_ptr;
always @(*) 
begin: buf_rd_ctl_PROC
  case ({buf_taken, buf_taken_single})
  2'b11: begin
    fifo_rd_ok = 2'b01;
    buf_rd_ptr = 2'd1;
  end
  2'b10: begin
    fifo_rd_ok = 2'b11;
    buf_rd_ptr = 2'd2;
  end
  default: begin
    fifo_rd_ok = 2'b0; 
    buf_rd_ptr = 2'd0;
  end
  endcase
end
 
always @(posedge clk or posedge rst_a) 
begin: cnt_rd_PROC
  if (rst_a == 1'b1) begin
    fetch_buf_cnt_rd <= 3'h0;
    bta_buf_cnt_rd   <= 3'h0;
  end
  else begin
// leda W484 off
//leda BTTF_D002 off
//LMD: Unequal length LHS and RHS in assignment LHS: x, RHS : y
//LJ:  allow negtive number of fetch_buf_cnt_rd from positive number subtraction
// spyglass disable_block W484
// SMD: Possible assignment overflow
// SJ:  
    fetch_buf_cnt_rd <= fetch_buf_cnt_nxt - { 1'h0, buf_taken_count_nxt };
    bta_buf_cnt_rd   <= bta_buf_cnt_nxt   - { 1'h0, buf_taken_count_nxt };
//leda BTTF_D002 on
// leda W484 on
// spyglass enable_block W484
  end
end
 
////////////////////////////////////// final output mux //////////////////////////////
//switch when buf_taken happens
//
always @(*) 
begin: buf_out_mux_PROC
  case (buf_rd_ptr) 
  2'd1: begin
    buf_data_out_w0_int = buf_data[`npuarc_IM_WIDTH-1:`npuarc_IM_WIDTH/2];
    buf_data_out_w1_int = buf_data_next[`npuarc_IM_WIDTH/2-1:0];
    buf_data_out_bta0 = buf_data_bta1;
    buf_data_out_bta1 = buf_data_bta0_next;
    buf_data_out_vld0 = buf_data_vld[1] & bta_data_vld[1] & ~restart;
    buf_data_out_vld1 = buf_data_vld_next[0] & bta_data_vld_next[0] & ~restart;
    buf_data_out_err0 = buf_data_err1;
    buf_data_out_err1 = buf_data_err0_next;
    buf_data_out_experm0 = buf_data_experm1;
    buf_data_out_experm1 = buf_data_experm0_next;
    buf_data_out_iprot_viol0 = buf_data_iprot_viol1;
    buf_data_out_iprot_viol1 = buf_data_iprot_viol0_next;
    buf_out_ecc_enable0 = buf_ecc_enable[1];
    buf_out_ecc_enable1 = buf_ecc_enable_next[0];
    buf_data_out_way0 = buf_data_way1;
    buf_data_out_way1 = buf_data_way0_next;
    buf_data_out_first_word0 = buf_data_first_word1;
    buf_data_out_first_word1 = buf_data_first_word_next0;
    buf_data_out_bank_ctl0 = buf_data_bank_ctl1;
    buf_data_out_bank_ctl1 = buf_data_bank_ctl_next0;
    buf_data_out_br_offset0 = buf_data_br_offset1[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_out_br_offset1 = buf_data_br_offset_next0[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_out_pkt0 = buf_data_pkt1;
    buf_data_out_pkt1 = buf_data_pkt_next0;
  end
  2'd2: begin
    buf_data_out_w0_int = buf_data_next[`npuarc_IM_WIDTH/2-1:0];
    buf_data_out_w1_int = buf_data_next[`npuarc_IM_WIDTH-1:`npuarc_IM_WIDTH/2];
    buf_data_out_bta0 = buf_data_bta0_next;
    buf_data_out_bta1 = buf_data_bta1_next;
    buf_data_out_vld0 = buf_data_vld_next[0] & bta_data_vld_next[0] & ~restart;
    buf_data_out_vld1 = buf_data_vld_next[1] & bta_data_vld_next[1] & ~restart;
    buf_data_out_err0 = buf_data_err0_next;
    buf_data_out_err1 = buf_data_err1_next;
    buf_data_out_experm0 = buf_data_experm0_next;
    buf_data_out_experm1 = buf_data_experm1_next;
    buf_data_out_iprot_viol0 = buf_data_iprot_viol0_next;
    buf_data_out_iprot_viol1 = buf_data_iprot_viol1_next;
    buf_out_ecc_enable0 = buf_ecc_enable_next[0];
    buf_out_ecc_enable1 = buf_ecc_enable_next[1];
    buf_data_out_way0 = buf_data_way0_next;
    buf_data_out_way1 = buf_data_way1_next;
    buf_data_out_first_word0 = buf_data_first_word_next0;
    buf_data_out_first_word1 = buf_data_first_word_next1;
    buf_data_out_bank_ctl0 = buf_data_bank_ctl_next0;
    buf_data_out_bank_ctl1 = buf_data_bank_ctl_next1;
    buf_data_out_br_offset0 = buf_data_br_offset_next0[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_out_br_offset1 = buf_data_br_offset_next1[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_out_pkt0 = buf_data_pkt_next0;
    buf_data_out_pkt1 = buf_data_pkt_next1;
  end
  default: begin
    buf_data_out_w0_int = buf_data[`npuarc_IM_WIDTH/2-1:0];
    buf_data_out_w1_int = buf_data[`npuarc_IM_WIDTH-1:`npuarc_IM_WIDTH/2];
    buf_data_out_bta0 = buf_data_bta0;
    buf_data_out_bta1 = buf_data_bta1;
    buf_data_out_vld0 = buf_data_vld[0] & bta_data_vld[0] & ~restart;
    buf_data_out_vld1 = buf_data_vld[1] & bta_data_vld[1] & ~restart;
    buf_data_out_err0 = buf_data_err0;
    buf_data_out_err1 = buf_data_err1;
    buf_data_out_experm0 = buf_data_experm0;
    buf_data_out_experm1 = buf_data_experm1;
    buf_data_out_iprot_viol0 = buf_data_iprot_viol0;
    buf_data_out_iprot_viol1 = buf_data_iprot_viol1;
    buf_out_ecc_enable0 = buf_ecc_enable[0];
    buf_out_ecc_enable1 = buf_ecc_enable[1];
    buf_data_out_way0 = buf_data_way0;
    buf_data_out_way1 = buf_data_way1;
    buf_data_out_first_word0 = buf_data_first_word0;
    buf_data_out_first_word1 = buf_data_first_word1;
    buf_data_out_bank_ctl0 = buf_data_bank_ctl0;
    buf_data_out_bank_ctl1 = buf_data_bank_ctl1;
    buf_data_out_br_offset0 = buf_data_br_offset0[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_out_br_offset1 = buf_data_br_offset1[`npuarc_IM_WORD_BITS-2:`npuarc_PC_LSB];
    buf_data_out_pkt0 = buf_data_pkt0;
    buf_data_out_pkt1 = buf_data_pkt1;
  end
  endcase
end
 
//endianess control for buf output
always @(*)
begin: endianess_PROC
//`if (`BYTE_ORDER == `HS_LITTLE_ENDIAN)
  buf_data_out_w0 = buf_data_out_w0_int;
  buf_data_out_w1 = buf_data_out_w1_int;
//`endif
end
 

//flow control with input that is operating in clk2
//
reg   in_rdy_r;
reg   bta_in_rdy_r;

wire  in_rdy;
wire  bta_in_rdy;

assign in_rdy = fifo_wr_ok;

assign bta_in_rdy = bta_wr_ok;

assign fetch_buf_wr = buf_data_in_vld_qual & {`npuarc_IM_BANKS{fifo_wr_ok}};

assign bta_buf_wr   = buf_bta_in_vld_qual & {`npuarc_IM_BANKS{bta_wr_ok}};
 
always @(posedge clk or posedge rst_a) 
begin: buf_regs_PROC
  if (rst_a == 1'b1) begin
    in_rdy_r <= 1'b0;
    bta_in_rdy_r <= 1'b0;
  end
  else begin
    in_rdy_r <= in_rdy | restart;
    bta_in_rdy_r <= bta_in_rdy | restart;
  end
end

//across clock boundaries, we need to tell clk2 that one data is taken
//
assign buf_data_in_rdy = in_rdy | in_rdy_r;
assign buf_bta_in_rdy = bta_in_rdy | bta_in_rdy_r;

 

endmodule

