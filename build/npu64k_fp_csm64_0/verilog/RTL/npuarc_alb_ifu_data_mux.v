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
//   This module muxes the instruction SRAM outputs.
//   The memories include ICCM0, ICCM1 and I$
//   As is controlled by the fetch request block (the address decoder) with use of
//    its output signal "fetch_data_mux_out_take", the output from the memories are
//    guaranteed mutual exclusive
//   This block also handles halt/run procedure as it tries to use the "restart" signal
//    propagated from the branch_info FIFO as a mark of beginning of the restart fetch
//   This block also detects split fetch -- the arrival time of the data from different bank
//    can be different. A state machine tracks the bank data integraty for a fetch block
//   It outputs the fetch block data to the fetch buffer
//    A dual bank fetch block could be split into two different outputs
//    However the brinfo uses the same entry from the beinf FIFO for the same fetch block anyway 
//   Down pipe: fetch buffer
// ===========================================================================
 
`include "npuarc_defines.v"
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_ifu_data_mux_fifo_edc_err" }
//
module npuarc_alb_ifu_data_mux (
  input      clk      ,
  input      core_clk ,
  input      rst_a    ,
  input      restart  ,
  
  //from memory targets


  input [`npuarc_IC_DRAM_RANGE]    fetch_icache_data,
  input [`npuarc_IM_BANKS-1:0]     fetch_icache_data_vld,
  input                     fetch_icache_data_err,
  output                    fetch_icache_data_rdy,
  input                     ic_iprot_viol,
  input                     ic_mpu_viol,

  input                     itlb_ovrlp_excpn,
  input                     itlb_miss_excpn,
  input                     itlb_ecc_err_excpn,
  input [`npuarc_ITLB_EXEC_PERM_RANGE]               itlb_exec_perm,

  input [`npuarc_IC_WAYS_BITS-1:0] fetch_icache_data_way,
  input                        fetch_icache_ecc_enable,
  output reg                fetch_data_mux_out_take,

  //branch  info interface
  input                        brinfo_id_vld,
  input                        brinfo_id_is_restart,
  input                        brinfo_id_kill_2nd,
  input                        brinfo_id_is_br,
  input                        brinfo_id_is_br_last,
  input  [`npuarc_PC_RANGE]           brinfo_id_bta,
  input  [`npuarc_IM_BANKS+1:0]       brinfo_id_bank_ctl,
  input  [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] brinfo_id_br_offset,
  input  [`npuarc_BR_INFO_PKT_RANGE]  brinfo_id_pkt,
  input                        brinfo_id_bta_miss,
//input  [2:0]                 brinfo_id_bta_miss_offset,
  input  [`npuarc_BR_INFO_OFFSET_RANGE] brinfo_id_bta_miss_offset,
  input                        bta_miss_update,

 //BTA miss feadback
  output reg                   bta_miss_disp_vld,
  output reg [`npuarc_PC_RANGE]       bta_miss_disp,

  //data to fetch buffer
  output reg [`npuarc_IM_WIDTH-1:0]   fetch_data_out,
  output reg [`npuarc_IM_BANKS-1:0]   fetch_data_vld_out,
  output [`npuarc_FCH_EXCPN_1H_RANGE] fetch_data_err_out,
  output                       dmux_iprot_viol,

  output [`npuarc_ITLB_EXEC_PERM_RANGE] fetch_data_exec_perm,

  output [`npuarc_IC_WAYS_BITS-1:0]   fetch_data_way_out,


  output                       fetch_ecc_enable,


  input                        fetch_data_rdy,

  // Branch info to fetch buffer 
  output reg [`npuarc_IM_BANKS-1:0]   bta_vld_out,
  output reg [1:0]             bta_bank_cnt_out,
  output reg [`npuarc_PC_RANGE]       bta_info_bta_out,
  output reg                   bta_tail_stall,
  input                        bta_rdy,

  output reg                   brinfo_restart_out,
  output reg [`npuarc_IM_BANKS-1:0]   brinfo_br_out,
  output reg [`npuarc_IM_BANKS-1:0]   brinfo_first_word_out,
  output reg                   brinfo_br_last_out,
  output reg [`npuarc_IM_BANKS-1:0]   brinfo_bank_ctl_out,
  output reg [1:0]             brinfo_bank_cnt_out,
  output reg [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] brinfo_br_offset_out,
  output reg [`npuarc_BR_INFO_PKT_RANGE] brinfo_pkt_out
  );


////////////////////////////////////////////////////////////////////////////////
// Local Signal Declarations
////////////////////////////////////////////////////////////////////////////////


/////////////////// fetch data input interface //////////////////////////
//
wire fetch_iccm0_addr_err_int;
assign fetch_iccm0_addr_err_int = 1'b0;
wire [`npuarc_IM_WIDTH-1:0] fetch_iccm0_data_int;
wire [`npuarc_IM_BANKS-1:0] fetch_iccm0_data_vld_int;
assign fetch_iccm0_data_vld_int = {`npuarc_IM_BANKS{1'b0}};

wire fetch_iccm1_addr_err_int;
assign fetch_iccm1_addr_err_int = 1'b0;
wire [`npuarc_IM_WIDTH-1:0] fetch_iccm1_data_int;
wire [`npuarc_IM_BANKS-1:0] fetch_iccm1_data_vld_int;
assign fetch_iccm1_data_vld_int = {`npuarc_IM_BANKS{1'b0}};

wire   fetch_viol;
assign fetch_viol = 1'b0
                  | (ic_iprot_viol & (|fetch_icache_data_vld))
                  | (ic_mpu_viol & (|fetch_icache_data_vld))
                  | itlb_ovrlp_excpn
                  | itlb_miss_excpn
                  | itlb_ecc_err_excpn
                  | (itlb_exec_perm[1:0] == 2'b00)
                  ;

parameter INST_NOP_S = 16'h78e0;

wire [`npuarc_IM_WIDTH-1:0] fetch_icache_data_int;

wire [`npuarc_IM_BANKS-1:0] fetch_icache_data_vld_int;
assign fetch_icache_data_vld_int =  fetch_icache_data_vld;
wire fetch_icache_data_err_int;
assign fetch_icache_data_err_int = fetch_icache_data_err;
assign fetch_icache_data_rdy = fetch_data_rdy;   //bypass rdy check as is only for ICCM 

wire [`npuarc_IC_WAYS_BITS-1:0] fetch_icache_data_way_int;
assign fetch_icache_data_way_int = fetch_icache_data_way;


///////////////////////////////////// data mux ////////////////////////////////////////
//

assign fetch_iccm0_data_int = {`npuarc_IM_WIDTH{1'b0}};

assign fetch_iccm1_data_int = {`npuarc_IM_WIDTH{1'b0}};

assign fetch_icache_data_int = fetch_icache_data; 

wire [`npuarc_IM_WIDTH-1:0] fetch_data_nop_s;
assign fetch_data_nop_s = 
                       {{`npuarc_ECC_BANK_BITS{1'b0}},{(`npuarc_IM_DWIDTH/32){INST_NOP_S}},
                        {`npuarc_ECC_BANK_BITS{1'b0}},{(`npuarc_IM_DWIDTH/32){INST_NOP_S}}
                       }; 

wire [`npuarc_IM_WIDTH-1:0] fetch_data_out_int;
assign  fetch_data_out_int =  fetch_viol ?
                              fetch_data_nop_s :
                              ( ( {`npuarc_IM_WIDTH{|fetch_iccm0_data_vld_int}} & fetch_iccm0_data_int )
                              | ( {`npuarc_IM_WIDTH{|fetch_iccm1_data_vld_int}} & fetch_iccm1_data_int )
                              | ( {`npuarc_IM_WIDTH{|fetch_icache_data_vld_int}} & fetch_icache_data_int )
                              );


wire [`npuarc_IM_BANKS-1:0] fetch_data_vld_comp_int;
assign fetch_data_vld_comp_int = fetch_iccm0_data_vld_int  
                               | fetch_iccm1_data_vld_int  
                               | fetch_icache_data_vld_int ;

//////////////////////////// fetch data output interface ///////////////////////////////////
//
reg [1:0] fetch_data_vld_int;
reg brinfo_vld_out;
reg brinfo_kill_2nd_int;
reg [`npuarc_IM_BANKS+1:0] brinfo_bank_ctl_int;
reg brinfo_bta_miss_int;
//reg [2:0] brinfo_bta_miss_offset_int;
reg [`npuarc_BR_INFO_OFFSET_RANGE] brinfo_bta_miss_offset_int;
reg [`npuarc_PC_RANGE] brinfo_bta_out;

always @(*) 
begin: bank_align_PROC
  if (brinfo_bank_ctl_int[`npuarc_IM_BANKS]) begin //bank swap
    fetch_data_out = {fetch_data_out_int[`npuarc_IM_WIDTH/2-1:0], fetch_data_out_int[`npuarc_IM_WIDTH-1:`npuarc_IM_WIDTH/2]};
    fetch_data_vld_int = {fetch_data_vld_comp_int[0], fetch_data_vld_comp_int[1]};
  end
  else begin
    fetch_data_out = fetch_data_out_int;
    fetch_data_vld_int = fetch_data_vld_comp_int;  
  end
end


// // IFU one-hot exception type (excl ecc)
// `define FCH_BUS_ERR_1H      0
// `define FCH_ADDR_ERR_1H     1
// `define FCH_ITLB_ERR_1H     2
// `define FCH_ITLB_MISS_1H    3
// `define FCH_ITLB_ECC_ERR_1H   4

assign fetch_data_err_out[0] = (|fetch_icache_data_vld_int) & fetch_icache_data_err_int;
assign fetch_data_err_out[1] = ((|fetch_iccm0_data_vld_int) & fetch_iccm0_addr_err_int) |
                               ((|fetch_iccm1_data_vld_int) & fetch_iccm1_addr_err_int);
assign fetch_data_err_out[2] = (|fetch_icache_data_vld_int) & itlb_ovrlp_excpn;
assign fetch_data_err_out[3] = (|fetch_icache_data_vld_int) & itlb_miss_excpn;
assign fetch_data_err_out[4] = (|fetch_icache_data_vld_int) & itlb_ecc_err_excpn;
assign fetch_data_exec_perm  = itlb_exec_perm;

assign dmux_iprot_viol       = (|fetch_icache_data_vld_int) & ic_iprot_viol;

assign fetch_data_way_out = fetch_icache_data_way_int;

assign fetch_ecc_enable = 
                          ((|fetch_icache_data_vld_int) & fetch_icache_ecc_enable & (!fetch_viol)) |
                          1'b0                                                    |
                          1'b0                                                 ;


////////////////////// SM for handling fetch bank split ///////////////////////
//
reg [1:0] fetch_state_nxt;
reg [1:0] fetch_state;
reg do_second;
always @(*) 
begin: bank_ctl_PROC
    fetch_state_nxt = fetch_state;
    fetch_data_vld_out = fetch_data_vld_int;
    do_second = 1'b0;
    fetch_data_mux_out_take = 1'b0;
    //signaling of data compeltion in fetch buffer
//leda  W71 off
// LMD: Case statement without default clause and not all cases are covered
//leda  DFT_022 off
// LMD: Incomplete case statement
// LJ:  Default output assignments are from above
    case (fetch_state)
      2'b00: begin
        if (brinfo_vld_out && (&brinfo_bank_ctl_int[`npuarc_IM_BANKS-1:0])) begin //(!brinfo_bank_ctl_int[`npuarc_IM_BANKS+1])) begin //dual fetch
          case (fetch_data_vld_int)
            2'b01: begin //only first data is valid, get it if fetch buffer is ready 
              if (fetch_data_rdy) begin 
                fetch_state_nxt = 2'b01;
              end
            end
            2'b10: begin //only second data is valid, supprese it and wait for first one
              fetch_data_vld_out[1] = 1'b0; 
            end
            2'b11: begin
              fetch_data_mux_out_take = fetch_data_rdy;
              fetch_data_vld_out[1] = !brinfo_kill_2nd_int && fetch_data_vld_int[1]; 
            end
          endcase
        end 
        else if (brinfo_vld_out) begin //single fetch
          if (fetch_data_vld_int[0] & fetch_data_rdy) begin
            fetch_data_mux_out_take = 1'b1;
          end
          else if (fetch_data_vld_int[0] && (!fetch_data_rdy)) begin
            fetch_state_nxt = 2'b10;
          end
        end
      end
      2'b01: begin //dual bank fetch with the first bank already in fetch buffer
        fetch_data_vld_out[0] = 1'b0; 
        fetch_data_vld_out[1] = !brinfo_kill_2nd_int && fetch_data_vld_int[1]; 
        do_second = 1'b1;
        if (fetch_data_vld_int[1] && fetch_data_rdy) begin
          fetch_data_mux_out_take = 1'b1;
          fetch_state_nxt = 2'b00;
        end
      end
      2'b10: begin //single bank fetch, new request to the other bank is killed
        fetch_data_vld_out[1] = 1'b0; 
        if (fetch_data_vld_int[0] && fetch_data_rdy) begin
          fetch_data_mux_out_take = 1'b1;
          fetch_state_nxt = 2'b00;
        end
      end   
    endcase  
//leda  DFT_022 on
//leda  W71 on
end //block: bank_ctl_PROC

always @(posedge clk or posedge rst_a) 
begin: fetch_state_PROC
  if (rst_a == 1'b1) begin
    fetch_state <= 2'b00;
  end
  else begin
    fetch_state <= restart ? 2'b00 : fetch_state_nxt;
  end
end //block: fetch_state_PROC
//////////////////////// brinfo FIFO to adapt to memory fetch delay /////////////////////
//
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  not used signals from fifo
wire brinfo_id_fifo_full;  
wire brinfo_id_fifo_afull; 
wire brinfo_id_fifo_aempty; 
wire [`npuarc_IM_BANKS+1:0] brinfo_bank_ctl_fifo;
// leda NTL_CON13A on
wire brinfo_id_fifo_empty;
wire brinfo_restart_fifo;
wire brinfo_br_fifo;
wire brinfo_br_last_fifo;
wire [`npuarc_PC_RANGE] brinfo_bta_fifo;

wire [`npuarc_IM_BANKS+1:0] brinfo_bank_ctl_flop;
wire [`npuarc_IM_WORD_BITS-1:`npuarc_PC_LSB] brinfo_br_offset_fifo;
wire [`npuarc_BR_INFO_PKT_RANGE] brinfo_pkt_fifo;
wire brinfo_bta_miss_fifo;
//wire [2:0] brinfo_bta_miss_offset_fifo;
wire [`npuarc_BR_INFO_OFFSET_RANGE] brinfo_bta_miss_offset_fifo;
wire brinfo_kill_2nd_fifo;

wire brinfo_id_fifo_bypass;
assign brinfo_id_fifo_bypass = brinfo_id_fifo_empty && fetch_data_mux_out_take; 
wire brinfo_id_fifo_wr;
assign brinfo_id_fifo_wr = brinfo_id_vld && (!brinfo_id_fifo_bypass) && (!restart); 
wire brinfo_id_fifo_rd;
assign brinfo_id_fifo_rd = fetch_data_mux_out_take && (!brinfo_id_fifo_bypass); 
npuarc_alb_ifu_data_mux_fifo brinfo_id_fifo (
  .clk (clk),
  .rst_a (rst_a),
  .restart (restart),

  .wr (brinfo_id_fifo_wr),
  .wdata ({
    brinfo_id_is_restart,
    brinfo_id_bta_miss,
    brinfo_id_bta_miss_offset,
    brinfo_id_kill_2nd,
    brinfo_id_is_br,
    brinfo_id_is_br_last,
    brinfo_id_br_offset,
    brinfo_id_pkt,
    brinfo_id_bta,
    brinfo_id_bank_ctl}),  
  .rd (brinfo_id_fifo_rd),
  .rdata ({brinfo_restart_fifo,
     brinfo_bta_miss_fifo,
     brinfo_bta_miss_offset_fifo,
     brinfo_kill_2nd_fifo,
     brinfo_br_fifo,
     brinfo_br_last_fifo,
     brinfo_br_offset_fifo,
     brinfo_pkt_fifo,
     brinfo_bta_fifo,
     brinfo_bank_ctl_fifo}),  
  .rdata_flop(brinfo_bank_ctl_flop),
  .full (brinfo_id_fifo_full),
  .empty (brinfo_id_fifo_empty),
  .afull (brinfo_id_fifo_afull),
  .aempty (brinfo_id_fifo_aempty)
);

////output for fetch output
//
always @(*) 
begin: br_info_bypass_PROC
  if (brinfo_id_fifo_empty) begin
    brinfo_vld_out = brinfo_id_vld; 
    brinfo_restart_out = brinfo_id_is_restart;
    brinfo_kill_2nd_int = brinfo_id_kill_2nd;
    brinfo_br_out[0] = brinfo_id_is_br & (!brinfo_id_br_offset[`npuarc_IM_WORD_BITS-1]);
    brinfo_br_out[1] = brinfo_id_is_br & brinfo_id_br_offset[`npuarc_IM_WORD_BITS-1];
    brinfo_br_last_out = brinfo_id_is_br_last;
    brinfo_bta_out = brinfo_id_bta;
    brinfo_bank_ctl_int = brinfo_id_bank_ctl;
    brinfo_br_offset_out = brinfo_id_br_offset;
    brinfo_pkt_out = brinfo_id_pkt;
    brinfo_bta_miss_int = brinfo_id_bta_miss;
    brinfo_bta_miss_offset_int = brinfo_id_bta_miss_offset;
    brinfo_first_word_out = 2'b01;
  end
  else begin
    brinfo_vld_out = 1'b1; 
    brinfo_restart_out = brinfo_restart_fifo;
    brinfo_kill_2nd_int = brinfo_kill_2nd_fifo;
    brinfo_br_out[0] = brinfo_br_fifo & (!brinfo_br_offset_fifo[`npuarc_IM_WORD_BITS-1]);
    brinfo_br_out[1] = brinfo_br_fifo & brinfo_br_offset_fifo[`npuarc_IM_WORD_BITS-1];
    brinfo_br_last_out = brinfo_br_last_fifo;
    brinfo_bta_out = brinfo_bta_fifo;
    brinfo_bank_ctl_int = brinfo_bank_ctl_flop;
    brinfo_br_offset_out = brinfo_br_offset_fifo;
    brinfo_pkt_out = brinfo_pkt_fifo;
    brinfo_bta_miss_int = brinfo_bta_miss_fifo;
    brinfo_bta_miss_offset_int = brinfo_bta_miss_offset_fifo;
    brinfo_first_word_out = 2'b01;
  end
end //block: br_info_bypass_PROC 

//convert bank_ctl format for fetch buffer
always @(*)
begin: bank_ctl_conv_PROC
  brinfo_bank_ctl_out[`npuarc_IM_BANKS-1] = brinfo_bank_ctl_int[`npuarc_IM_BANKS];
  if (do_second) begin
    brinfo_bank_ctl_out[0] = !brinfo_kill_2nd_int;
  end  
  else if (brinfo_kill_2nd_int) begin
    brinfo_bank_ctl_out[0] = 1'b1;
  end
  else begin
    brinfo_bank_ctl_out[0] = brinfo_bank_ctl_int[`npuarc_IM_BANKS+1];
  end
end //block: bank_ctl_conv_PROC



 
always @(*)
begin: bank_cnt_conv_PROC
  if (do_second) begin
    brinfo_bank_cnt_out = 2'd1;
  end
  else begin
    brinfo_bank_cnt_out = (brinfo_bank_ctl_int[`npuarc_IM_BANKS+1]) ? 2'd1 : 2'd2;
  end
end //block: bank_ctl_conv_PROC


//BTA miss handling
parameter [1:0] BTA_IDLE       = 2'd0;
parameter [1:0] BTA_WAIT_BANK1 = 2'd1;
parameter [1:0] BTA_WAIT_BANK0 = 2'd2; 
parameter [1:0] BTA_WAIT_RDY   = 2'd3; 
reg [1:0] bta_miss_state_nxt;
reg [1:0] bta_miss_state;
reg [2:0] bta_vld_state_nxt;
reg [2:0] bta_vld_state_r;
reg [31:0] bta_miss_ins_nxt;
reg [31:0] bta_miss_ins_r;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used
reg [`npuarc_IM_WIDTH-1:0] fetch_data_out_btamiss;
reg [`npuarc_IM_WIDTH-1:0] fetch_data_out_btamiss_int;
// leda NTL_CON13A on

// leda NTL_STR76 off
// LMD: A non-tristate net can have only one non-tristate driver
// LJ:  The 2 cycle checker asserts X on this signal as an assertion
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  not used range from checker
wire [31:0] bta_miss_ins_r_2cyc;
// leda NTL_CON13A on
wire bta_miss_err_r_2cyc;
// leda NTL_STR76 on

reg bta_miss_disp_vld_nxt;
reg bta_miss_err;
reg bta_miss_err_r;
reg [31:0] bta_ins;
reg bta_update_hold; //a signal from bta2buf output sm
wire ins_is_16bit;
always @(*)
begin: bta_miss_PROC
  bta_miss_state_nxt = bta_miss_state;
  bta_miss_ins_nxt = bta_miss_ins_r;
  bta_miss_disp_vld_nxt = 1'b0;
  bta_miss_err = 1'b0;
  case (bta_miss_state)
  BTA_IDLE: begin
    if (brinfo_vld_out && brinfo_bta_miss_int) begin
      case (brinfo_bta_miss_offset_int)
        3'b000,
        3'b001,
        3'b010: begin
          bta_miss_disp_vld_nxt = fetch_data_vld_out[0];
        end
        3'b011: begin
          bta_miss_disp_vld_nxt = (&fetch_data_vld_out[1:0]) || (fetch_data_vld_out[0] && ins_is_16bit);
          if (fetch_data_vld_out[0] && (!fetch_data_vld_out[1]) && (!ins_is_16bit)) begin //only one bank is available
            if (brinfo_bank_ctl_out[0]) begin //single bank access
              if (brinfo_br_last_out) begin //no tail for the remaining 16bit, flag error 
                bta_miss_disp_vld_nxt = 1'b1; //force valid as there is no tail to make it 32bit
                bta_miss_err = 1'b1;
              end
              else if (fetch_data_rdy) begin
                bta_miss_state_nxt = BTA_WAIT_BANK0;
              end
            end
            else if (!brinfo_bank_ctl_out[0] && fetch_data_rdy) begin //dual bank access
              bta_miss_state_nxt = BTA_WAIT_BANK1;
            end
            bta_miss_ins_nxt[15:0] = fetch_data_out_btamiss[63:48];
          end
        end
        3'b100,
        3'b101,
        3'b110: begin
          bta_miss_disp_vld_nxt = fetch_data_vld_out[1];
        end
        3'b111: begin
          bta_miss_disp_vld_nxt = fetch_data_vld_out[1] && ins_is_16bit;
          if (fetch_data_vld_out[1] && (!ins_is_16bit)) begin
            if (brinfo_br_last_out) begin 
              bta_miss_disp_vld_nxt = 1'b1; //force valid as there is no tail to make it 32bit
              bta_miss_err = 1'b1;
            end
            else if (fetch_data_rdy) begin
              bta_miss_state_nxt = BTA_WAIT_BANK0;
              bta_miss_ins_nxt[15:0]= fetch_data_out_btamiss[127:112];
            end
          end
        end
        default: begin
          bta_miss_state_nxt = bta_miss_state;
        end
      endcase
      if (bta_miss_disp_vld_nxt) begin
        bta_miss_ins_nxt = bta_ins;
        if (!fetch_data_mux_out_take) begin //wait for whole fetch to finish
          bta_miss_state_nxt = BTA_WAIT_RDY;
        end
      end
    end
  end
  BTA_WAIT_BANK0: begin
   if (fetch_data_vld_out[0]) begin
     bta_miss_disp_vld_nxt = 1'b1;
     bta_miss_ins_nxt[31:16] = fetch_data_out_btamiss[15:0];
     if (fetch_data_rdy) begin
       bta_miss_state_nxt = BTA_IDLE;
     end
     else begin
       bta_miss_state_nxt = BTA_WAIT_RDY;
     end
   end
  end
  BTA_WAIT_BANK1: begin
    if (fetch_data_vld_out[1]) begin
      bta_miss_disp_vld_nxt = 1'b1;
      bta_miss_ins_nxt[31:16] = fetch_data_out_btamiss[79:64];
      if (fetch_data_rdy) begin
        bta_miss_state_nxt = BTA_IDLE;
      end
      else begin
        bta_miss_state_nxt = BTA_WAIT_RDY;
      end
    end
  end
  BTA_WAIT_RDY: begin
     if (fetch_data_mux_out_take) begin
       bta_miss_state_nxt = BTA_IDLE;
     end
  end
  endcase
end
       
//instruction extraction and decoding
//always @(*) 
//begin: ins_extract_PROC
//  fetch_data_out_btamiss         = {`IM_WIDTH{1'b0}};
//`if (`BYTE_ORDER == `HS_BIG_ENDIAN)
//  fetch_data_out_btamiss[31:0]   = Big_endian_func(fetch_data_out[31:0]);
//  fetch_data_out_btamiss[63:32]  = Big_endian_func(fetch_data_out[63:32]);
//  fetch_data_out_btamiss[95:64]  = Big_endian_func(fetch_data_out[95:64]);
//  fetch_data_out_btamiss[127:96] = Big_endian_func(fetch_data_out[127:96]);
//`else
//  fetch_data_out_btamiss         = fetch_data_out;
//`endif
//
//  bta_ins = fetch_data_out_btamiss[31:0];
//  case (brinfo_bta_miss_offset_int)
//    3'd0: bta_ins = fetch_data_out_btamiss[31:0];
//    3'd1: bta_ins = fetch_data_out_btamiss[47:16];
//    3'd2: bta_ins = fetch_data_out_btamiss[63:32];
//    3'd3: bta_ins = fetch_data_out_btamiss[79:48];
//    3'd4: bta_ins = fetch_data_out_btamiss[95:64];
//    3'd5: bta_ins = fetch_data_out_btamiss[111:80];
//    3'd6: bta_ins = fetch_data_out_btamiss[127:96];
//    3'd7: bta_ins = {16'b0, fetch_data_out_btamiss[127:112]};
//    default: bta_ins = fetch_data_out_btamiss[31:0];
//  endcase
//end
always @(*) 
begin: ins_extract_PROC
//  fetch_data_out_btamiss_int = {`ECC_BANK_BITS'd0, fetch_data_out[`FD2A_RANGE],fetch_data_out[`FD0_RANGE]};
  fetch_data_out_btamiss_int = {`npuarc_ECC_IM_BITS'd0, fetch_data_out[127+`npuarc_ECC_BANK_BITS:64+`npuarc_ECC_BANK_BITS],fetch_data_out[`npuarc_FD0_RANGE]};

  fetch_data_out_btamiss         = fetch_data_out_btamiss_int;


  bta_ins = fetch_data_out_btamiss[31:0];
  case (brinfo_bta_miss_offset_int)
    `npuarc_BR_INFO_OFFSET_SIZE'd0 : bta_ins = fetch_data_out_btamiss[31:0];
    `npuarc_BR_INFO_OFFSET_SIZE'd1 : bta_ins = fetch_data_out_btamiss[47:16];
    `npuarc_BR_INFO_OFFSET_SIZE'd2 : bta_ins = fetch_data_out_btamiss[63:32];
    `npuarc_BR_INFO_OFFSET_SIZE'd3 : bta_ins = fetch_data_out_btamiss[79:48];
    `npuarc_BR_INFO_OFFSET_SIZE'd4 : bta_ins = fetch_data_out_btamiss[95:64];
    `npuarc_BR_INFO_OFFSET_SIZE'd5 : bta_ins = fetch_data_out_btamiss[111:80];
    `npuarc_BR_INFO_OFFSET_SIZE'd6 : bta_ins = fetch_data_out_btamiss[127:96];
    `npuarc_BR_INFO_OFFSET_SIZE'd7 : bta_ins = {16'b0, fetch_data_out_btamiss[112+15:112] };
    default: bta_ins = fetch_data_out_btamiss[31:0];
  endcase

end

npuarc_alb_2cyc_checker #(1+32) u_alb_2cyc_checker ( 
  .data_in({bta_miss_err_r, bta_miss_ins_r}),
  .data_out({bta_miss_err_r_2cyc, bta_miss_ins_r_2cyc}),
  .clk(core_clk)
);

//decoding instruction
always @(*) 
begin: ins_dec_PROC
  case ({bta_miss_err_r_2cyc, bta_miss_ins_r_2cyc[13:11]})
    //Bcc s21 -- 00000ssssssssss0_SSSSSSSSSSNQQQQQ
    //
    4'b0000: bta_miss_disp = { {11{bta_miss_ins_r_2cyc[16+15]}}, bta_miss_ins_r_2cyc[16+15:16+6], bta_miss_ins_r_2cyc[10:1] };  
    //BRcc s9 -- 00001xxxsssssss1_Sxxxxxxxxxxxxxxx     
    //
    4'b0001: bta_miss_disp = { {23{bta_miss_ins_r_2cyc[16+15]}}, bta_miss_ins_r_2cyc[16+15], bta_miss_ins_r_2cyc[7:1] };  
    //BRNE_S s8--11101bbb1sssssss
    //BREQ_S
    4'b0101: bta_miss_disp = { {24{bta_miss_ins_r_2cyc[6]}}, bta_miss_ins_r_2cyc[6:0] };
    //BEQ_S s10--11110xxsssssssss
    //
    // Bcc_S
    4'b0110: bta_miss_disp = { {22{bta_miss_ins_r_2cyc[8]}}, bta_miss_ins_r_2cyc[8:0] };
    //
    // DBNZ : (from npuarc_acode_tasks.v) offset = { {19{inst[5]}}, inst[5:0], inst[11:6], 1'b0 };
    4'b0100: bta_miss_disp[`npuarc_PC_RANGE] = { {19{bta_miss_ins_r_2cyc[16+5]}}, bta_miss_ins_r_2cyc[16+5:16+0], bta_miss_ins_r_2cyc[16+11:16+6]};
    //
    default:bta_miss_disp = {`npuarc_PC_BITS{1'b0}}; //force to 0 for invalid bta miss instruction
  endcase
end
 
assign ins_is_16bit = bta_ins[13]; 

//register displacement and state
always @(posedge clk or posedge rst_a) 
begin: bta_miss_reg_PROC
  if (rst_a == 1'b1) begin
    bta_miss_state    <= BTA_IDLE;
    bta_miss_disp_vld <= 1'b0;
    bta_miss_err_r    <= 1'b0;
  end
  else begin
    bta_miss_state    <= restart ? BTA_IDLE       : bta_miss_state_nxt;
    bta_miss_disp_vld <= restart ? 1'b0           : bta_miss_disp_vld_nxt;
    bta_miss_err_r    <= restart ? bta_miss_err_r : bta_miss_err;
  end
end

// VPOST OFF
always @(posedge clk or posedge rst_a) 
begin: bta_miss_ins_reg_PROC
  if (rst_a == 1'b1) begin
    bta_miss_ins_r    <= 32'b0;
  end
  else begin
    if (bta_update_hold) begin
      bta_miss_ins_r[`npuarc_PC_RANGE] <= brinfo_id_bta;
    end
    else begin
      bta_miss_ins_r <= bta_miss_ins_nxt;
    end
  end
end
// VPOST ON

//bta valid output logic
parameter [2:0] BTA_OUT_IDLE          = 3'b000;
parameter [2:0] BTA_OUT_WAIT_RES      = 3'b001;
parameter [2:0] BTA_OUT_WAIT_BTABUF   = 3'b010;
parameter [2:0] BTA_OUT_WAIT_TAIL     = 3'b011;
parameter [2:0] BTA_OUT_WAIT_BUF      = 3'b100;
parameter [2:0] BTA_OUT_WAIT_TAIL_BUF = 3'b101;
reg bta_info_last_nxt;
reg bta_info_last_r;
reg [`npuarc_IM_BANKS-1:0] bta_info_bank_vld_nxt;
reg [`npuarc_IM_BANKS-1:0] bta_info_bank_vld_r;
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  all bits of bus used
reg [1:0] bta_bank_cnt_nxt;
reg [1:0] bta_bank_cnt_r;
  // leda NTL_CON32 on
reg [1:0] bta_info_taken_nxt;
reg [1:0] bta_info_taken_r;
always @(*) 
begin: bta_vld_PROC
  bta_vld_out = {`npuarc_IM_BANKS{1'b0}};
  bta_bank_cnt_out = brinfo_bank_cnt_out;
  bta_info_bta_out = brinfo_bta_out;
  bta_update_hold = 1'b0;
  bta_tail_stall = 1'b0;
  bta_info_last_nxt = bta_info_last_r;
  bta_info_bank_vld_nxt = bta_info_bank_vld_r;
  bta_bank_cnt_nxt = bta_bank_cnt_r;
  bta_vld_state_nxt = bta_vld_state_r;
  if (fetch_data_mux_out_take) begin
//leda W484 off
//leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  addition of 1 is intentional
    bta_info_taken_nxt = bta_info_taken_r + 1;
//leda BTTF_D002 on
//leda W484 on
  end
  else begin
    bta_info_taken_nxt = bta_info_taken_r;
  end
//leda  W71 off
// LMD: Case statement without default clause and not all cases are covered
// LJ:  Default output assignments are from above
  case (bta_vld_state_r)
    BTA_OUT_IDLE: begin //detect bta_miss
      bta_info_taken_nxt = bta_info_taken_r;
      if (brinfo_vld_out & brinfo_bta_miss_int) begin //bta is missed wait for bta_miss_update from BPU
        bta_info_last_nxt = brinfo_br_last_out; 
        bta_info_bank_vld_nxt = (brinfo_kill_2nd_int) ? 2'b01: brinfo_bank_ctl_int[`npuarc_IM_BANKS-1:0];
        bta_bank_cnt_nxt = brinfo_bank_cnt_out;
        bta_info_taken_nxt = {1'b0, fetch_data_mux_out_take};
        bta_vld_state_nxt = BTA_OUT_WAIT_RES;
      end
      else begin
        bta_vld_out = fetch_data_vld_out; 
      end
    end
    BTA_OUT_WAIT_RES: begin //wait for bta resolution
      bta_info_bta_out = brinfo_id_bta; 
      bta_bank_cnt_out = bta_bank_cnt_r;
      if (bta_miss_update) begin
        bta_vld_out = bta_info_bank_vld_r[`npuarc_IM_BANKS-1:0];
        if (bta_rdy) begin
          if (!bta_info_last_r) begin
            bta_vld_state_nxt = BTA_OUT_WAIT_TAIL;
          end
          else if (|bta_info_taken_nxt) begin
            bta_vld_state_nxt = BTA_OUT_IDLE;
          end
          else begin
            bta_vld_state_nxt = BTA_OUT_WAIT_BUF; 
          end
        end
        else begin
          bta_update_hold = 1'b1;
          bta_vld_state_nxt = BTA_OUT_WAIT_BTABUF;
        end
      end
    end
    BTA_OUT_WAIT_BTABUF: begin //wait for data to get in bta buffer
      bta_bank_cnt_out = bta_bank_cnt_r;
      bta_info_bta_out = bta_miss_ins_r[`npuarc_PC_RANGE]; 
      bta_vld_out = bta_info_bank_vld_r[`npuarc_IM_BANKS-1:0];
      if (bta_rdy) begin
        if (!bta_info_last_r) begin
          bta_vld_state_nxt = BTA_OUT_WAIT_TAIL;
        end
        else if (|bta_info_taken_nxt) begin
          bta_vld_state_nxt = BTA_OUT_IDLE;
        end
        else begin
          bta_vld_state_nxt = BTA_OUT_WAIT_BUF;
        end
      end
    end
    BTA_OUT_WAIT_TAIL: begin //deliver tail info to bta buf
      bta_bank_cnt_out = 2'd1;
      bta_vld_out = `npuarc_IM_BANKS'b01; //tail is validated
      bta_tail_stall = 1'b1;
      if (bta_rdy) begin
        if (bta_info_taken_r[1]) begin          //tail is already taken from br_info_fifo
          //the tail cycle can take the cycle for a new bta_miss
          //we need to handle both at the same time
          //
          if (brinfo_vld_out & brinfo_bta_miss_int) begin //new bta missed appears
            bta_info_last_nxt = brinfo_br_last_out; 
            bta_info_bank_vld_nxt = (brinfo_kill_2nd_int) ? 2'b01: brinfo_bank_ctl_int[`npuarc_IM_BANKS-1:0];
            bta_bank_cnt_nxt = brinfo_bank_cnt_out;
            bta_info_taken_nxt = {1'b0, fetch_data_mux_out_take};
            bta_vld_state_nxt = BTA_OUT_WAIT_RES;
          end
          else begin
            bta_vld_state_nxt = BTA_OUT_IDLE;
          end
        end
        else if (bta_info_taken_nxt[1]) begin //tail is being taken this cycle
          bta_vld_state_nxt = BTA_OUT_IDLE;
        end
        else begin
          bta_vld_state_nxt = BTA_OUT_WAIT_TAIL_BUF;
        end
      end
    end
    BTA_OUT_WAIT_BUF: begin
      if (|bta_info_taken_nxt) begin
        bta_vld_state_nxt = BTA_OUT_IDLE;
      end
    end
    BTA_OUT_WAIT_TAIL_BUF: begin
      if (bta_info_taken_nxt[1]) begin
        bta_vld_state_nxt = BTA_OUT_IDLE;
      end
    end
    default: begin
      bta_vld_state_nxt = bta_vld_state_r;
    end
  endcase
//leda  W71 on
end   

always @(posedge clk or posedge rst_a)
begin: bta2buf_reg_PROC
  if (rst_a == 1'b1) begin
    bta_info_last_r     <= 1'b0;
    bta_info_bank_vld_r <= {`npuarc_IM_BANKS{1'b0}};
    bta_bank_cnt_r      <= 2'd0;
    bta_info_taken_r    <= 2'b00;
    bta_vld_state_r     <= BTA_OUT_IDLE;
  end
  else begin
    bta_info_last_r     <= bta_info_last_nxt;
    bta_info_bank_vld_r <= bta_info_bank_vld_nxt;
    bta_bank_cnt_r      <= bta_bank_cnt_nxt;
    bta_info_taken_r    <= bta_info_taken_nxt;
    bta_vld_state_r     <= restart ? BTA_OUT_IDLE : bta_vld_state_nxt;
  end
end


endmodule
