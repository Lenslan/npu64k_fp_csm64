// Library ARCv2HS-3.5.999999999
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
//
//    #     ####     ##     ####   #    #  ######
//    #    #    #   #  #   #    #  #    #  #
//    #    #       #    #  #       ######  #####
//    #    #       ######  #       #    #  #
//    #    #    #  #    #  #    #  #    #  #
//    #     ####   #    #   ####   #    #  ######
//
// ===========================================================================
//
// Description:
//  This module implements the Instruction Cache.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o icache_ctl.vpp
//
// ===========================================================================

//functional Descriptions --
//  1. This icache controller is designed for high speed processors
//  2. It supports variable cache memory size, line size and ways of associativity
//  3. It supports dynamic switching of tag-cache parallism. 
//  4. It supports software direct access of tag and cache memory by aux register control
//  5. It supports line hit at refill
//  6. it uses random replacement and invalidate the way being replaced before refill

//register access function descriptions
//  when aux_req is on, aux_req_mode defines mode of operations
//  aux_req_mode bit 0 : cache/tag memory read, normal read
//  aux_req_mode bit 1 : cache/tag memory read, direct read
//  aux_req_mode bit 2 : cache memory write, direct write
//  aux_req_mode bit 3 : tag memory write, direct write, 
//  aux_req_mode bit 4 : tag invalidate, all
//  aux_req_mode bit 5 : tag invalidate, line only
//  aux_req_mode bit 6 : tag line lock    
//  aux_req_mode bit 7 : tag line prefetch    
//----------------------------------------------------------------------------

`include "npuarc_defines.v"
// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: {clk : "edc_clk2" , clk_ibus : "edc_clk"}, rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_icache_lbuf_edc_err" }

// leda W389 off 
// LMD: Multiple clocks in the module
// LJ:  this module requires two clocks (clk_ibus-core_clk and clk-2cyc clk)

module npuarc_alb_icache_ctl (
  input clk,             //2 cycle clock
  input clk_en,          //2 cycle clock phase
  input clk2_en_r,       //2 cycle clock phase disregarding restart in an odd cycle
  input clk_ibus,        //ibus operates with core clock
  input rst_a,           //active high reset
  
  input exu_hlt_restart,     //halt
  input restart,        //asserted from fch_restart to bpu_restart
  input bpu_restart,    //a single pulse from bpu
  input ar_user_mode_r, //for ibus protection control

  //state report
  //
  output hlt_ready,     //for halt
  output reg mem_busy,  //for restart clock control

  //way prediction PC at restart
  //
  input mpd_pc_load,
  input [`npuarc_PC_RANGE] mpd_pc,
  input mpd_direction,
  input mpd_mispred,

  //fetch access interface
  //
  input [`npuarc_PC_RANGE] fetch_addr0,
  input [`npuarc_IC_WRD_RANGE] fetch_addr1_offset,
  input fetch_req,
  input fetch_is_restart,
  input [`npuarc_IC_BANKS:0] fetch_bank_ctl,
  input fetch_way_bank_id,
  input fetch_way_tail,
  input fetch_way_req,
  input fetch_vec,
  input fetch_seq,
  input fetch_way_sec,
  input fetch_way_force,
  input [`npuarc_IC_WAYS_BITS-1:0] fetch_way_ptr,
  output reg fetch_rdy,

  output reg itlb_lkup_valid,
  input  itlb_stall,
  input  jrsp_itlb_update,
  output [`npuarc_ADDR_RANGE] req_vaddr_r,
  // leda NTL_CON13C off 
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  input  [`npuarc_PADDR_RANGE] req_paddr,
  // leda NTL_CON13C on
  input                itlb_fail_r,
  input                itlb_miss_excpn_nxt,
  output reg           itlb_miss_excpn_r_r,
  input                itlb_ecc_err_excpn_nxt,
  output reg           itlb_ecc_err_excpn_r_r,
  input                itlb_ovrlp_excpn_nxt,
  output reg           itlb_ovrlp_excpn_r_r,
  input [`npuarc_ITLB_EXEC_PERM_RANGE]          itlb_exec_perm_nxt,
  output reg [`npuarc_ITLB_EXEC_PERM_RANGE]     itlb_exec_perm_r_r,

  output icache_tag_par_mode_r,

  //fetch data output
  //
  output reg [`npuarc_IC_WIDTH-1:0] fetch_data,
  output reg [`npuarc_IC_BANKS-1:0] fetch_data_vld,
  output reg fetch_data_err,
  output reg [`npuarc_IC_WAYS_BITS-1:0] fetch_data_way,
  input fetch_data_rdy,
  output                    ecc_enable,
  output     [`npuarc_IC_WAYS-1:0] ic_tag_ecc_en,

  //aux register access interface
  //
  input uncache_mode,
  input [3:0] ic_waylock,
  input aux_req,
  input aux_bist,
  output reg aux_ack,
  input [7:0] aux_req_mode,
  input [`npuarc_PIADDR_RANGE] aux_addr,
  input [`npuarc_IC_ALIAS_IDX_RANGE] aux_alias_r,
  input [`npuarc_DOUBLE_RANGE] aux_wdata,
  input [`npuarc_DOUBLE_BE_RANGE] aux_wmask,
  output reg [`npuarc_IC_BANK_WIDTH-1:0] aux_rdata,
  output aux_rdata_vld,
  output reg [`npuarc_PADDR_RANGE] aux_tag_rdata,
  output reg aux_tag_rdata_vld,
  output reg aux_req_fail,

  output reg [`npuarc_IC_TRAM_RANGE] aux_tag_mem_rdata, //actual tag mem data output

  //tag ram interface
  //
  output reg [`npuarc_IC_WAY_RANGE] tag_mem_cen,
  output reg tag_mem_wen,
  output reg [`npuarc_IC_IDX_RANGE] tag_mem_addr,
  output reg [`npuarc_IC_TWORD_RANGE] tag_mem_wdata,

  input [`npuarc_IC_TRAM_RANGE] tag_mem_rdata0,
  input [`npuarc_IC_TRAM_RANGE] tag_mem_rdata1,
  input [`npuarc_IC_TRAM_RANGE] tag_mem_rdata2,
  input [`npuarc_IC_TRAM_RANGE] tag_mem_rdata3,

  input [`npuarc_IC_WAYS-1:0] tag_ecc_error,

  
  //cache mem interface
  //
  output [`npuarc_IC_WAY_ADR_RANGE] cache_mem_addr0,
  output [`npuarc_IC_WAY_ADR_RANGE] cache_mem_addr1,
  output reg [`npuarc_IC_WAY_RANGE] cache_mem_cen,
  output reg cache_mem_wen,
  output reg [`npuarc_IC_BYTE_WIDTH-1:0] cache_mem_wem,
  output reg [`npuarc_IC_BANKS-1:0] cache_mem_bank_sel,
  output reg [`npuarc_IC_LBUF_RANGE] cache_mem_wdata,
    
  input [`npuarc_IC_DRAM_RANGE] cache_mem_rdata0,
  input [`npuarc_IC_DRAM_RANGE] cache_mem_rdata1,
  input [`npuarc_IC_DRAM_RANGE] cache_mem_rdata2,
  input [`npuarc_IC_DRAM_RANGE] cache_mem_rdata3,
  
  //output for way prediction
  //
  output way_for_pred_vld,
  output [`npuarc_IC_WAYS_BITS-1:0] way_for_pred,
  output reg way_sec_for_pred,
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Not all bits of bus used  
  output reg [`npuarc_PC_RANGE] way_for_pred_pc,
  // leda NTL_CON32 on
             
//  output way_miss_pred,
  output  reg          ifu_icache_miss_r,
  output  reg          ifu_way_pred_miss_r,
  output  reg          ifu_icache_hit_r,
// spyglass disable_block W240
// SMD: non driving port
// SJ : clk not used
  input                cycle2_r,
// spyglass enable_block W240

  output [`npuarc_PC_RGN_RANGE] ifetch_chk_addr,
  // MPU interface
  input                  ifetch_mpu_viol,
  output                 ic_mpu_viol, // cache output stage (data has mpu fetch viol)
  input                  ifetch_unc,  // indicator from the MPU that the current address in the tag stage of the pipeline is uncacheable
  // Instruction Fetch Protection (IFP) interface
  input                  ifetch_iprot_viol,
  output                 ic_iprot_viol,


  //line fill bus interface (IBUS)
  //
  output ifu_ibus_cmd_valid,
  output ifu_ibus_cmd_prot,
  input  ifu_ibus_cmd_accept,
  output [`npuarc_PADDR_RANGE] ifu_ibus_cmd_addr,
  output ifu_ibus_cmd_wrap,
  output ifu_ibus_cmd_cache,
  output [3:0] ifu_ibus_cmd_burst_size,
  input  ifu_ibus_rd_valid,
  output ifu_ibus_rd_accept,
  input  [`npuarc_DOUBLE_RANGE] ifu_ibus_rd_data,
  input  ifu_ibus_err_rd
);


//tag request signals
//
reg req_uncache;
reg req_uncache_r_r;
reg aux_req_tag_chk;
reg aux_req_tag_val; //onlt read tag but no update
reg aux_req_tag_mem;
reg [`npuarc_IC_WAY_RANGE] aux_req_tag_mem_cen;
reg aux_req_tag_mem_wen;
reg [`npuarc_IC_TWORD_RANGE] aux_req_tag_mem_wdata;
reg [`npuarc_PIADDR_RANGE] aux_req_tag_mem_addr;
reg [`npuarc_IC_ALIAS_IDX_RANGE] aux_req_tag_mem_addr_alias;
reg do_invld_all;
reg aux_do_invld_all;
reg req_way_req;
reg req_vec;
reg req_seq;
reg req_way_sec;
reg req_way_force;
reg req_way_update;
reg [`npuarc_IC_WAYS_BITS-1:0] req_way_ptr;

reg req_tag_stg;
reg req_tag_mem;
reg [`npuarc_IC_WAY_RANGE] req_tag_mem_cen;
reg req_tag_mem_wen;
reg [`npuarc_PIADDR_RANGE] req_tag_mem_addr;
reg [`npuarc_IC_WRD_RANGE] req_tag_mem_addr_offset;
reg [`npuarc_IC_TWORD_RANGE] req_tag_mem_wdata;
reg [`npuarc_IC_BANKS-1:0] req_bank_sel;
reg                 req_bank_ctl;
reg                 req_way_bank_id;
reg                 req_way_tail;
reg                 req_is_restart;
reg req_fetch_tag_chk;
reg req_err_tag_chk;
reg req_tag_invld;
reg aux_req_tag_invld;
reg req_cache_dir;
reg aux_req_cache_dir;
reg req_tag_lock;
reg aux_req_tag_lock;
reg aux_req_prefetch;

wire [`npuarc_IC_WAYS_BITS-1:0] aux_cache_mem_way;
assign aux_cache_mem_way = req_tag_mem_addr[`npuarc_IC_WAY_CACHE_RANGE];

reg req_tag_chk; //to enable miss detection of tag output
reg req_tag_val; //to only read tag but no update
reg aux_cache_rd_ack;
reg force_fetch_tag_chk;

//cache request signals, one cycle early
//
reg aux_req_cache_mem;
reg [`npuarc_IC_WAY_RANGE] aux_req_cache_mem_cen;
reg aux_req_cache_mem_wen;
reg req_cache_mem;
reg [`npuarc_IC_WAY_RANGE] req_cache_mem_cen;
reg req_cache_mem_wen;
//reg [`IC_BANKS-1:0] req_cache_mem_bank_sel;
reg [`npuarc_IC_BYTE_WIDTH-1:0] req_cache_mem_wem;
wire [`npuarc_IC_LBUF_RANGE] req_cache_mem_wdata;

//tag sm signals
//
reg [`npuarc_IC_IDX_RANGE] tag_idx_cnt;
reg [`npuarc_IC_IDX_RANGE] tag_idx_cnt_nxt;
reg [3:0] tag_state_nxt;
reg [3:0] tag_state_next;
reg [3:0] tag_state;
wire tag_stg_stall;
wire lf_on;
reg lf_start;
reg lf_uncache;
reg [`npuarc_PIADDR_RANGE] req_addr_r_conv;
wire [`npuarc_PIADDR_RANGE] lf_addr;
wire [`npuarc_PIADDR_RANGE] lf_addr_r;
reg lf_err_clr;
wire lf_stall;
reg  lf_stall_r;
wire cache_re_read_pre;
wire maybe_re_read_conflict;
wire re_read_conflict;
reg tag_chk;
reg tag_val;
reg tag_chk_clr;
wire tag_par_mode; //tag stage signal to identify fetch can access icache by way_force
reg tag_par_mode_clr;
reg tag_par_mode_nxt;
reg tag_par_mode_r;
//wire tag_seq_mode; //tage stage signal to identify a sequeutial fetch from last, tag check is skipped
reg tag_seq_mode_clr;
wire mode_par2ser_update;
reg mode_par2ser_update_r;
//reg [1:0] tag_seq_mode_r, tag_seq_mode_nxt;
reg tag_seq_mode_nxt; //
reg tag_seq_mode_r;   //tag stage signal to identify a sequential fetch from last, tag check is skipped
reg mode_update;
reg req_cache_dir_r;
wire aux_cache_rd_ack_pre;
reg aux_cache_rd_ack_r;
reg do_refetch_nxt;
reg do_refetch_r;
wire do_refetch;
reg arb_aux;
reg arb_fetch;
reg arb_refetch;
reg arb_line_err;
wire arb_ack;
reg tag_rdy;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  assertion use this signal
reg tag_start;
// leda NTL_CON13A on
reg cache_stg_on;
reg lock_line_err;
reg way_update;

//tag sm local registers
//
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg [`npuarc_PIADDR_RANGE] req_addr_nxt;
reg [`npuarc_PIADDR_RANGE] req_addr_r;
// leda NTL_CON32 on

  reg           req_addr_is_physical_r;
  reg           req_addr_is_physical_nxt;
  reg           req_addr_is_physical_next;
  reg           is_physical;

reg [`npuarc_IC_BANKS-1:0] req_bank_sel_nxt;
reg [`npuarc_IC_BANKS-1:0] req_bank_sel_next;
reg [`npuarc_IC_BANKS-1:0] req_bank_sel_r;
reg                 req_bank_ctl_nxt;
reg                 req_bank_ctl_r;
reg                 req_way_req_nxt;
reg                 req_way_req_next;
reg                 req_way_req_r;
reg                 req_way_bank_id_nxt;
reg                 req_way_bank_id_r;
reg                 req_way_tail_nxt;
reg                 req_way_tail_r;
reg                 req_is_restart_nxt;
reg                 req_is_restart_r;
reg [`npuarc_IC_WAYS_BITS-1:0] req_way_ptr_nxt;
reg [`npuarc_IC_WAYS_BITS-1:0] req_way_ptr_r;
reg [`npuarc_IC_WRD_RANGE] req_addr_offset_nxt;
reg [`npuarc_IC_WRD_RANGE] req_addr_offset_r;
reg req_for_fetch_nxt;
reg req_for_fetch_next;
reg req_for_fetch_r;
reg req_for_err_nxt;
reg req_for_err_r;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs 
// LJ:  used for monitoring
reg req_vec_nxt;
reg req_vec_r;
reg [`npuarc_IC_WAYS-1:0] tag_vld_nxt;
reg [`npuarc_IC_WAYS-1:0] tag_vld_next;
reg [`npuarc_IC_WAYS-1:0] tag_vld_r;
reg tag_miss_nxt;
reg tag_miss_next;
reg tag_miss_r;
// leda NTL_CON32 on
reg req_seq_nxt;
reg req_seq_next;
reg req_seq_r;
reg way_force_nxt;
reg way_force_r;
reg way_update_nxt;
reg way_update_r;
reg [1:0] last_is_aux_nxt;
reg [1:0] last_is_aux_next;
reg [1:0] last_is_aux_r;
reg req_lock_nxt;
reg req_lock_next;
reg req_lock_r;
reg req_prefetch_nxt;
reg req_prefetch_next;
reg req_prefetch_r;
reg req_uncache_nxt;
reg req_uncache_r;
reg req_tag_val_nxt;
reg req_tag_val_r;

reg [`npuarc_IC_WAYS-1:0] tag_mem_cen_r;
reg aux_ic_ctl_on_nxt;
reg aux_ic_ctl_on_next;
reg aux_ic_ctl_on;                     //set during actual aux icache operation

//wire fetch_seq_qual = fetch_seq && (!restart) && (!fetch_way_force);
wire fetch_seq_qual;
assign fetch_seq_qual = fetch_seq && (!restart);

reg itlb_lkup_valid_nxt;
assign icache_tag_par_mode_r = tag_par_mode_r;

reg  mpu_check_enable_nxt;
reg  mpu_check_enable_r;
reg  mpu_check_uncached_nxt;
reg  mpu_check_uncached_r;

reg  ifetch_mpu_viol_r;
reg  ifetch_mpu_viol_r_r;
assign   ic_mpu_viol    = tag_par_mode_r ? (ifetch_mpu_viol & mpu_check_enable_r & ~do_refetch)
                                         : ifetch_mpu_viol_r_r;
reg  ifetch_iprot_viol_r;
reg  ifetch_iprot_viol_r_r;
// automatic region protection violation associated with icache inst data presented to 
// ifu_data_mux/fetch_data_buffer
assign   ic_iprot_viol    = tag_par_mode_r ? (ifetch_iprot_viol & mpu_check_enable_r & ~do_refetch)
                                           : ifetch_iprot_viol_r_r;

//lbuf signals
//
wire lbuf_hit_req;
wire [`npuarc_IC_LBUF_RANGE] lbuf_dout;
wire [`npuarc_IC_LBUF_RANGE] lbuf_hit_data;
wire [`npuarc_IC_WAYS_BITS-1:0] lbuf_hit_way;
//wire lbuf_dout_vld;
wire lbuf_dout_vld_urgent;
wire lbuf_hit;       //data is in lbuf
wire lbuf_line_hit;  //addr is targeting miss line
wire lbuf_hit_cache; //data is in cache for miss line
wire lbuf_line_err;  //triggered by ibus error read, cleared when cache line is invalidated
wire dout_err_nxt;
wire lbuf_line_err_busy;
//wire lf_rd_done;
wire [`npuarc_IC_WAY_ADR_RANGE] cache_mem_wr_addr;

//signals from tag check
//
reg [`npuarc_IC_WAYS-1:0] tag_hit_ways_r;
wire ic_hit;
wire ic_miss;
wire [`npuarc_IC_WAYS-1:0] tag_hit_ways;
wire [`npuarc_IC_WAYS-1:0] tag_miss_ways;
wire [`npuarc_IC_WAYS-1:0] tag_eq;
wire [`npuarc_IC_WAYS-1:0] tag_vld;
wire [`npuarc_IC_WAYS-1:0] tag_lock;
wire [`npuarc_IC_WAYS-1:0] tag_hit;
wire [`npuarc_IC_WAYS_BITS-1:0] tag_hit_way_ptr;
wire [`npuarc_IC_WAYS_BITS-1:0] fetch_data_way_pre;
wire tag_miss;
reg tag_lock_all;
wire way_mis_pred;
reg way_write_ok;
reg [`npuarc_IC_WAYS_BITS:0] way_write_func;
reg [`npuarc_IC_WAYS_BITS-1:0] tag_update_way;
reg [`npuarc_IC_WAYS_BITS-1:0] tag_update_way_nxt;
reg [`npuarc_IC_WAYS_BITS-1:0] tag_update_way_r;

reg [9:0] pn_r;
reg [9:0] pn_next;
reg [8:0] pn2_r;
reg [8:0] pn2_next;
reg       rbit;
reg       rbit2;
reg [`npuarc_IC_WAYS_BITS-1:0] random_way; // binary encoded random way for 4-way cache, also use for 2-way
integer i,i2;
reg   first_limit;
reg   second_limit;
reg [2:0] rnum3;
reg pn_update;
reg [3:0] re_read_lock;
reg [3:0] tag_do_not_replace;
reg [3:0] tag_valid_or_do_not_replace;
reg [3:0] ic_waylock_r;

reg [`npuarc_IC_WAYS_BITS-1:0] first_invld_way;

//cache stg signals
//
reg tag_chk_r;
reg tag_val_r;
reg cache_re_read;
reg cache_re_read_tmp_r;
reg cache_stg_err;
reg cache_stg_on_r;
reg cache_stg_vld;
//reg cache_mem_busy;
wire cache_stg_stall;
wire cache_stg_stall_tag;
wire output_stg_stall;
wire uncache_data_done;

wire aux_use_cache_mem;



wire                  ifetch_viol;


  reg [`npuarc_IC_ALIAS_IDX_RANGE] req_tag_mem_addr_alias_idx;

  reg [`npuarc_IC_ALIAS_IDX_RANGE] req_addr_alias_idx_nxt;
  reg [`npuarc_IC_ALIAS_IDX_RANGE] req_addr_alias_idx_r;

  wire [`npuarc_IC_ALIAS_IDX_RANGE] lf_alias_idx;

  wire [`npuarc_IC_ALIAS_IDX_RANGE]  lf_alias_idx_r;

  assign lf_alias_idx = req_addr_alias_idx_r;


  
// Address for ECC coding


//////////////////////// request input muxes ///////////////////////////
//It prodeces request address, write data, read/write and cache_op info
//Request sources include (in order of priority) --
// 1.bus error from line buffer
// 2.Refetch due to way mis-prediction or line error
// 3.AUX register access
// 4.Normal fetch
// 

//mux control signal to put fetch at fastest timing path
//
wire req_sel_fetch;
assign req_sel_fetch = !(lbuf_line_err || aux_req || (do_refetch && (!restart)));  

always @(*) 
begin : tag_req_arb_PROC
  req_uncache = 1'b0;
  req_tag_chk = 1'b0;
  req_tag_val = 1'b0;
  req_tag_stg = 1'b0;
  req_tag_mem = 1'b0;
  req_tag_mem_cen = {`npuarc_IC_WAYS{1'b0}};
  req_tag_mem_wen = 1'b0;      
  req_tag_mem_addr = aux_addr;

  is_physical = 1'b1;

  req_tag_mem_addr_alias_idx = aux_alias_r;
  req_tag_mem_addr_offset = aux_addr[`npuarc_IC_WRD_RANGE];
  req_bank_sel = {`npuarc_IC_BANKS{1'b1}};
  req_bank_ctl = 1'b0;
  req_way_bank_id = 1'b0;
  req_way_tail = 1'b0;
  req_is_restart = 1'b0;
  req_way_req = 1'b0;
  req_tag_mem_wdata = aux_wdata[`npuarc_IC_TWORD_RANGE];
  req_tag_invld = 1'b0;
  req_tag_lock = 1'b0;
  req_cache_dir = 1'b0;
  req_cache_mem = 1'b0;
  req_cache_mem_cen = {`npuarc_IC_WAYS{1'b0}};
  req_cache_mem_wen = 1'b0;
//  req_cache_mem_bank_sel = {`IC_BANKS{1'b1}};
  arb_fetch = 1'b0;
  arb_aux = 1'b0;
  arb_refetch = 1'b0;
  arb_line_err = 1'b0;
  aux_ack = lock_line_err & clk_en;
  fetch_rdy = 1'b0;
  req_fetch_tag_chk = 1'b0;
  req_err_tag_chk = 1'b0;
  force_fetch_tag_chk = 1'b0;
  do_invld_all = 1'b0; 
  req_vec = 1'b0;
  req_seq = 1'b0;
  req_way_sec = 1'b0;
  req_way_force = 1'b0;
  req_way_update = 1'b0;
  req_way_ptr = {`npuarc_IC_WAYS_BITS{1'b0}};
  //mode control default value at restart
  //Default is set to parallel mode
  // and pre-sequential mode
  //
  if (restart) begin
    tag_par_mode_nxt = 1'b1;
//    tag_seq_mode_nxt = 2'b01;
    tag_seq_mode_nxt = 1'b1;
    mode_update = 1'b1;
  end
  else begin
    tag_par_mode_nxt = tag_par_mode_r;
    tag_seq_mode_nxt = tag_seq_mode_r;
    mode_update = 1'b0;
  end

  //tag request input mux, (also cache in par_mode)
  if (req_sel_fetch) begin
    //for uncache we need to make sure no line fill to avoid hitting line buffer
    //it's to garentee we have a dedicated line fetch for the uncache access
    //
    if (fetch_req && (!(lf_on && uncache_mode))) begin
      arb_fetch = 1'b1;
      req_tag_stg = 1'b1;
      req_tag_mem = 1'b1;
      req_tag_mem_wen = 1'b0;
      req_cache_mem = 1'b1;
      req_tag_chk = 1'b1;
      req_fetch_tag_chk = 1'b1;
      mode_update = arb_ack || restart;
    end
    //We ignore hit/miss at bpu_restart that forces cache access
    //
    force_fetch_tag_chk = bpu_restart;
    //fetch_rdy is independent of fetch_req
    fetch_rdy = arb_ack && (!(lf_on && uncache_mode));
    req_uncache = uncache_mode;

    //Clear parallel access of cache in case of
    //  1-- line buffer is busy or 
    //  2-- cache read-read due to line fill or
    //  3-- no way_force and no sequential fetch 
    //  4-- not uncache mode
    //  5-- any non-fetch access (aux, error, re-fetch)
    if ( uncache_mode || lf_on || cache_re_read || (!fetch_way_force && (!fetch_seq_qual)) ) begin
      tag_par_mode_nxt = 1'b0;
    end

    //sequential mode is enabled after first fetch from restart
    //sequential mode is disabled when 
    //1-- line buffer is busy
    //2-- fetch_seq=0 during sequential mode
    //3-- uncached mode
    //4-- any non-fetch access (aux, error, re-fetch)
    tag_seq_mode_nxt = 1'b1; // enter sequential mode after a regular fetch
    if ( uncache_mode || lf_on ) begin //leave sequential mode
      tag_seq_mode_nxt = 1'b0;
    end 


    req_way_force = tag_par_mode_nxt && fetch_way_force;
    req_way_update = fetch_way_force | fetch_way_req;

    // sequential mode is disabled during uncached mode or when the line buffer is busy 
//    req_seq = !uncache_mode && (!lf_on) && tag_seq_mode_r && fetch_seq_qual;
// fix sequential mode
    req_seq = !uncache_mode && (!lf_on) && tag_seq_mode_r && fetch_seq && (!restart);

    req_vec = fetch_vec;
    req_way_sec = fetch_way_sec; 
    req_way_ptr = fetch_way_ptr;
    req_tag_mem_addr = {{(`npuarc_PADDR_HI_SIZE){1'b0}}, fetch_addr0};

    is_physical = 1'b0;

    req_tag_mem_addr_alias_idx = fetch_addr0[`npuarc_IC_ALIAS_IDX_RANGE];
    req_tag_mem_addr_offset = fetch_addr1_offset;
    req_bank_sel = fetch_bank_ctl[`npuarc_IC_BANKS-1:0];
    req_bank_ctl = fetch_bank_ctl[`npuarc_IC_BANKS];
    req_way_bank_id = fetch_way_bank_id;
    req_is_restart  = fetch_is_restart;
    req_way_tail = fetch_way_tail;
    req_way_req = fetch_way_req;
    //way prediction only accesses a single tag way
    //
    if (req_way_force) begin
       req_tag_mem_cen[fetch_way_ptr] = req_tag_mem;
    end
    //Normally we access all the tag ways, however
    //Sequential access does not access any tag way
    //Same for uncache access
    //
    else if (!req_seq) begin 
      req_tag_mem_cen = {`npuarc_IC_WAYS{!uncache_mode&req_tag_mem}};
    end
  end // if (req_sel_fetch)
  //
  //lbuf error, the highest priority, triggers immediate reaction that invalidates the error cache line
  //
  else if (lbuf_line_err) begin
    arb_line_err = 1'b1;
    req_tag_stg = 1'b1;
    req_tag_chk = 1'b1;
    req_tag_mem = 1'b1;
    req_tag_mem_cen = {`npuarc_IC_WAYS{1'b1}};
    req_tag_mem_addr = lf_addr_r;

    is_physical = 1'b1;

    req_tag_mem_addr_alias_idx = lf_alias_idx_r;
    req_tag_invld = 1'b1;
    req_err_tag_chk = 1'b1;
    tag_par_mode_nxt = 1'b0;
    tag_seq_mode_nxt = 1'b0;
    mode_update = 1'b1;
  end  
  //refetch cannot be interrupted by aux so we put it at higher priority than aux
  //refetch if from a parallel mode miss detection. In this case we skip the line
  //fille cause by the miss detection. Instead we give a re-try hoping the tag is
  //hit with all the tag ways are accessed
  //
  else if (do_refetch) begin
    arb_refetch = 1'b1;
    req_tag_stg = 1'b1;
    fetch_rdy = 1'b0;
    req_tag_mem = 1'b1;
    req_tag_mem_cen = {`npuarc_IC_WAYS{1'b1}};
    req_tag_mem_wen = 1'b0;
    req_tag_mem_addr = req_addr_r;
    is_physical = 1'b0;

    req_tag_mem_addr_alias_idx = req_addr_alias_idx_r;
    req_tag_mem_addr_offset = req_addr_offset_r;
    req_cache_mem = 1'b1;
    req_tag_chk = 1'b1;
    req_fetch_tag_chk = 1'b1;
    force_fetch_tag_chk = 1'b1;
    req_bank_sel = req_bank_sel_r;
    req_bank_ctl = req_bank_ctl_r;
    req_way_bank_id = req_way_bank_id_r;
    req_is_restart = req_is_restart_r;
    req_way_tail = req_way_tail_r;
    req_way_update = way_update_r;
    tag_par_mode_nxt = 1'b0;
    tag_seq_mode_nxt = 1'b0;
    mode_update = 1'b1;
  end
  //we hold aux access if line fill is on
  //It makes sure aux access is not using
  //previous line buffer 
  //
  else if (aux_req && (!lf_on)) begin 
    arb_aux = 1'b1;
    req_tag_stg = 1'b1;
    aux_ack = arb_ack & clk_en;
    req_tag_chk = aux_req_tag_chk;
    req_tag_val = aux_req_tag_val;
    req_tag_mem = aux_req_tag_mem;
    req_tag_mem_cen = aux_req_tag_mem_cen;
    req_tag_mem_wen = aux_req_tag_mem_wen;
    req_cache_mem = aux_req_cache_mem;
    req_cache_mem_cen = aux_req_cache_mem_cen;
    req_cache_mem_wen = aux_req_cache_mem_wen;
    req_tag_mem_wdata = aux_req_tag_mem_wdata;
    req_tag_mem_addr = aux_req_tag_mem_addr;

    is_physical = 1'b1;

    req_tag_mem_addr_alias_idx = aux_req_tag_mem_addr_alias;
    req_tag_invld = aux_req_tag_invld;
    req_tag_lock = aux_req_tag_lock;
    req_cache_dir = aux_req_cache_dir;
    do_invld_all = aux_do_invld_all;
    tag_par_mode_nxt = 1'b0;
    tag_seq_mode_nxt = 1'b0;
    mode_update = 1'b1;
  end
end //block : tag_req_arb_PROC

assign arb_ack = tag_rdy;

///////////////////////////////////////////////////////////////////////////////
//////////////////////////////// TAG stage ////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
// TAG stage is under control of the TAG state machine
// the TAG state machine controls the pace of TAG/cache memory access
// Only at TAG_IDLE state that a new cache request can be taken 
//1. generate tag memory access signals and pipe down cache memory access signals 
//2. miss handling
//3. aux function handling
//4. uncache function handling
// Note --
//1. line buffer fill & hit detection is on the fly
//2. cache memory fill from line buffer is on the fly
//
parameter [3:0] TAG_IDLE = 4'd0;
parameter [3:0] TAG_LF_UPDATE = 4'd1;
parameter [3:0] TAG_LF_RD = 4'd2;
parameter [3:0] TAG_INVLD_ALL = 4'd3;
parameter [3:0] TAG_INVLD = 4'd4;
parameter [3:0] TAG_ERR_INVLD = 4'd5;
parameter [3:0] TAG_WAIT_LOCK = 4'd6;
parameter [3:0] TAG_UNCACHE_REQ = 4'd7;
parameter [3:0] TAG_UNCACHE_WAIT = 4'd8;

// 32b virtual addr for itlb lookup
// Use the registered address belonging to the TAG access;
// it's the converted version with adjustment for unalignment bank access.
assign req_vaddr_r = {req_addr_r_conv [`npuarc_PC_RANGE], 1'b0};
//mux control signal to put fetch at fastest timing path
//
wire tag_sel_fetch;
assign tag_sel_fetch = !(do_invld_all || req_tag_invld || req_tag_lock || req_tag_val);
//we force miss for aux access and uncache access
//we also force a new tag op with restart
//
//Proceed with a new request in following conditions, see "tag_sm_no_miss"
// 1-restart or refetch or 
// 2-tag hit
// Force miss condition in following conditions 
// 3-aux access is active 
// 4-uncache handling is active 
// 5-ITLB miss

// Handling of ITLB miss
// An ITLB miss is handled as if a tag miss occurred, but without triggering a line fill.
// By preventing a tag hit, the icache won't proceed and will wait until the ITLB miss is resolved.
// The itlb_stall signal indicates an ITLB miss in progress.
// The itlb_lkup_valid signal gates itlb_stall to apply only to cases of a regular icache access.
// Interaction with JTLB:
// When a JTBL hit occurs, in most cases the ITLB is updated by the JTLB after 5/7 cycles of stall and regular execution resumes.
// In the next cycle tag check should resume with the updated ITLB entry.
//   
  
  
wire tag_sm_no_miss;
assign tag_sm_no_miss = !( ic_miss                 //!(2)
                           ||(itlb_lkup_valid & itlb_stall)  //(5)
                           ||aux_ic_ctl_on         // (3)
                           || (req_uncache_r         // (4)
                               // in case of an instruction fetch protection violation
                               // force an uncached access into a cache hit
                               & ~ifetch_viol
                              )
                         )
                      || force_fetch_tag_chk;      // (1)

//Wait for following conditions to execute the new request. see "tag_sm_act" 
// 1-no stall from cache stage and
// 2-line fill finishes before aux request or error handling request
wire tag_sm_act;
assign tag_sm_act = ( !( lf_on && (aux_req||req_err_tag_chk) ) // (2) 
                    && (!tag_stg_stall))                       // (1) 
                || force_fetch_tag_chk;

always @(*) 
begin : tag_sm_PROC
  tag_mem_cen = {`npuarc_IC_WAYS{1'b0}};
  tag_mem_wen = req_tag_mem_wen;
  tag_mem_addr = {req_tag_mem_addr_alias_idx, req_tag_mem_addr[`npuarc_IC_UNALIASED_IDX_RANGE]};
  tag_mem_wdata = req_tag_mem_wdata;
  itlb_lkup_valid_nxt = 1'b0;
  mpu_check_enable_nxt = mpu_check_enable_r;
//  mpu_check_enable_nxt = 1'b0;
  mpu_check_uncached_nxt = mpu_check_uncached_r;
  cache_stg_on = 1'b0;
  tag_rdy = 1'b0;
  tag_start = 1'b0;
  pn_update = 1'b0;
  aux_req_fail = 1'b0;
  lf_start = 1'b0;
  lf_err_clr = 1'b0;
  lock_line_err = 1'b0;
  tag_par_mode_clr = 1'b0;
  tag_seq_mode_clr = 1'b0;
  way_write_ok = 1'b0;
  tag_update_way = {`npuarc_IC_WAYS_BITS{1'b0}};
  tag_chk = 1'b0; 
  tag_val = 1'b0;
  tag_chk_clr = 1'b0;
  lf_uncache = 1'b0;
  way_update = 1'b0;
  tag_state_nxt = tag_state;
  aux_ic_ctl_on_nxt = aux_ic_ctl_on;
  req_addr_nxt = req_addr_r;

  req_addr_is_physical_nxt = req_addr_is_physical_r;

  req_addr_alias_idx_nxt = req_addr_alias_idx_r;
  req_bank_sel_nxt = req_bank_sel_r;
  req_bank_ctl_nxt = req_bank_ctl_r;
  req_way_bank_id_nxt = req_way_bank_id_r;
  req_way_tail_nxt = req_way_tail_r;
  req_way_req_nxt = req_way_req_r;
  req_is_restart_nxt = req_is_restart_r;
  req_addr_offset_nxt = req_addr_offset_r;
  req_lock_nxt = req_lock_r;
  req_prefetch_nxt = req_prefetch_r;
  tag_idx_cnt_nxt = tag_idx_cnt; 
  req_uncache_nxt = req_uncache_r;
  req_tag_val_nxt = req_tag_val_r;
  tag_update_way_nxt = tag_update_way_r;
  req_for_fetch_nxt = req_for_fetch_r;
  req_for_err_nxt = req_for_err_r;
  req_vec_nxt = req_vec_r;
  req_seq_nxt = req_seq_r;
  way_force_nxt = way_force_r;
  req_way_ptr_nxt = req_way_ptr_r;
  way_update_nxt = way_update_r;
  last_is_aux_nxt = last_is_aux_r;
  do_refetch_nxt = do_refetch_r;
  tag_vld_nxt = tag_vld_r;
  tag_miss_nxt = tag_miss_r;
//leda  W71 off
// LMD: Case statement without default clause and not all cases are covered
// LJ:  Default output assignments are from above
  case (tag_state)
    TAG_IDLE: begin
      if (tag_sm_no_miss) begin                          //decision to response to new request
        if (tag_sm_act) begin                            //decision to take new request
          tag_rdy = !arb_aux;                            //aux ack is at the end of its handling
          tag_start = arb_fetch || arb_line_err || arb_refetch || arb_aux; //a test only signal
          req_lock_nxt = 1'b0;
          req_prefetch_nxt = 1'b0;
          req_tag_val_nxt = 1'b0;
          if (req_tag_mem) begin
             // Reevaluate the MPU check for all new tag requests 
             mpu_check_enable_nxt = 1'b0; 
            if (tag_sel_fetch) begin                     //normal fetch
              itlb_lkup_valid_nxt = 1'b1;
              // enable protection violation check for either cached or uncached fetch
              mpu_check_enable_nxt = 1'b1; 
              mpu_check_uncached_nxt = 1'b1; 
              tag_mem_cen = req_tag_mem_cen;
              cache_stg_on = req_cache_mem;
              tag_chk = req_tag_chk;
            end
            else if (do_invld_all) begin                 //invalidate full tag
              tag_state_nxt = TAG_INVLD_ALL;
              tag_idx_cnt_nxt = {`npuarc_IC_IDX_BITS{1'b0}};
            end
            else if (req_tag_invld) begin                //invalidate one line
              tag_state_nxt = TAG_INVLD;
              tag_mem_cen = req_tag_mem_cen;
              tag_chk = 1'b1;
            end
            else if (req_tag_lock) begin                 //lock one line
              req_lock_nxt = 1'b1;
              req_prefetch_nxt = aux_req_prefetch;       // select lock or prefetch version of the lock sequence
              cache_stg_on = req_cache_mem;
              tag_mem_cen = req_tag_mem_cen;
              tag_chk = 1'b1;
            end
            else if (req_tag_val) begin                  //read tag value
              req_tag_val_nxt = 1'b1;
              tag_mem_cen = req_tag_mem_cen;
              cache_stg_on = req_cache_mem;
              tag_chk = req_tag_chk;
              tag_val = 1'b1;
            end 
          end // if (req_tag_mem)
          if (req_tag_mem || req_cache_mem) begin
            req_uncache_nxt = req_uncache;
            req_addr_nxt = req_tag_mem_addr;

            req_addr_is_physical_nxt = is_physical;

            req_addr_alias_idx_nxt = req_tag_mem_addr_alias_idx;
            req_addr_offset_nxt = req_tag_mem_addr_offset;
            req_bank_sel_nxt = req_bank_sel;
            req_bank_ctl_nxt = req_bank_ctl;
            req_way_bank_id_nxt = req_way_bank_id;
            req_way_tail_nxt = req_way_tail;
            req_way_req_nxt = req_way_req;
            req_is_restart_nxt = req_is_restart;
            req_for_fetch_nxt = req_fetch_tag_chk; 
            req_for_err_nxt = req_err_tag_chk; 
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs 
// LJ:  used for monitoring
            req_vec_nxt = req_vec;
// leda NTL_CON32 on
            req_seq_nxt = req_seq;
            way_force_nxt = req_way_force;
            req_way_ptr_nxt = req_way_ptr;
            last_is_aux_nxt = {last_is_aux_r[0], arb_aux};
            //generate way data for BPU way prediction
            //disable way report if aux access is insterted
            //
            way_update_nxt = req_way_update 
                           && ( !(last_is_aux_r[0] || (last_is_aux_r[1] && req_way_tail_r)) 
                                || req_is_restart )
                           ; 
          end
          if (arb_refetch) begin
            do_refetch_nxt = 1'b0;
          end
          aux_ic_ctl_on_nxt = arb_aux && (!aux_bist);
          //way_update is a pulse when there is way_force and way_req 
          //it's invalidated by restart or refetch or aux request
          //
          way_update = way_update_r && (!req_is_restart) && (!arb_refetch) && (!arb_aux);
          if (!req_tag_stg) begin
// spyglass disable_block W415a
// SMD: signal assigned multiple times in same always block
            way_update_nxt = 1'b0;   //to kill tails of way_update_r for way_update pulse
// spyglass enable_block W415a
          end
        end // if (tag_sm_act)
        else
        begin
          // if the tag state machine is frozen, then retain the value of mpu_check_enable_r
          mpu_check_enable_nxt = mpu_check_enable_r;
        end
      end // if (tag_sm_no_miss)
      //miss or forced miss handling
      // 
      else begin 
        if (tag_seq_mode_r) begin //sequential mode is cleared at cache miss
          tag_seq_mode_clr = 1'b1;
        end
        //parallel mode is cleared at cache miss
        //refetch is triggered and line fetch is skipped
        //
        if (tag_par_mode_r) begin  
           tag_par_mode_clr = 1'b1;
           do_refetch_nxt = 1'b1;
        end
        //before processing new miss, wait until last line fill is done
        //
        else if (!lf_on
            // In case of an ITLB miss, wait until it is resolved and the ITLB update completed
               //  & (~itlb_stall) & (~jrsp_itlb_update)
                 & (req_addr_is_physical_r | ((~itlb_stall) & (~jrsp_itlb_update)))

                 ) 
        begin  

          mpu_check_uncached_nxt  = 1'b0;                  // clear uncached check flag 

          if (lbuf_line_err) begin                             //last line fill has error -- including line lock case
            tag_state_nxt = TAG_ERR_INVLD;
          end  
          else begin
            if (req_lock_r && tag_lock_all && tag_miss) begin //failed lock returns without line fill
              req_lock_nxt = 1'b0;
              req_prefetch_nxt = 1'b0;
              tag_rdy = 1'b1;
              aux_ic_ctl_on_nxt = 1'b0;
              aux_req_fail = 1'b1;
              tag_chk_clr = 1'b1; 
              tag_state_nxt = TAG_IDLE; 
            end 
            else if (req_lock_r && req_prefetch_r && (|tag_hit)) begin // prefetch that hits in the cache finishes immediately
              req_lock_nxt = 1'b0;
              req_prefetch_nxt = 1'b0;
              tag_rdy = 1'b1;
              aux_ic_ctl_on_nxt = 1'b0;
              aux_req_fail = 1'b0;
              tag_chk_clr = 1'b1; 
              tag_state_nxt = TAG_IDLE; 
            end 
            else if (req_tag_val_r) begin                     //aux memory read access
              aux_req_fail = aux_tag_rdata_vld                //fail at indirect read miss 
                           && tag_miss 
                           && (!req_cache_dir_r);
              if (aux_cache_rd_ack_r) begin
                req_tag_val_nxt = 1'b0;
                tag_rdy = 1'b1;
                aux_ic_ctl_on_nxt = 1'b0;
                tag_chk_clr = 1'b1;
                tag_state_nxt = TAG_IDLE; 
              end
            end  
            else begin                                       //otherwise go to line fetch 
              lf_start = 1'b1;
              {way_write_ok, 
               tag_update_way} = way_write_func;             //way replacement function
              if ( (tag_lock_all && (!req_lock_r))             //miss with all ways locked 
                 || req_uncache_r                            //uncache access
              //   || (ifetch_unc & mpu_check_enable_r)        // uncacheable MPU area detected 
                 || (ifetch_unc & mpu_check_uncached_r)        // uncacheable MPU area detected 
                 || (!way_write_ok)
                 ) begin                     //cannot find proper way for way replacement 
                req_uncache_nxt = 1'b1;      
                way_update_nxt = 1'b0;                       //disable BPU way update, because there is no way assignment
                lf_start = 1'b0;                             //go to uncache line fetch instead
                tag_state_nxt = TAG_UNCACHE_REQ;
              end 
              else begin                                     //Go tp update tag mem when we start line fetch
                tag_chk = req_lock_r;                        //read tag mem for another cycle to detect lock hit
                tag_vld_nxt = tag_vld;
                tag_miss_nxt = tag_miss; 
                tag_update_way_nxt = tag_update_way;
                pn_update = 1'b1;
                tag_state_nxt = TAG_LF_UPDATE;
              end
            end
          end
        end
      end
    end

    TAG_LF_UPDATE: begin 
      //tag update -- write the proper way to validate the fetch address in tag mem
      //lock is the only case we load line even it hits the line
      //
      tag_mem_cen[tag_update_way_r] = 1'b1;
      tag_mem_wen = 1'b1;
      tag_mem_wdata = {`npuarc_IC_TWORD_BITS{1'b0}};
      if (req_lock_r) begin
        tag_mem_addr = {aux_alias_r, aux_addr[`npuarc_IC_UNALIASED_IDX_RANGE]};
        tag_mem_wdata[`npuarc_IC_TAG_TAG_RANGE] = aux_addr[`npuarc_IC_TAG_RANGE];
        tag_mem_wdata[`npuarc_IC_TAG_LOCK_BIT] = ~req_prefetch_r;
        tag_mem_wdata[`npuarc_IC_TAG_VALID_BIT] = 1'b1;
        tag_state_nxt = TAG_LF_RD;
      end
      else begin
        tag_mem_addr = {lf_alias_idx, lf_addr[`npuarc_IC_UNALIASED_IDX_RANGE]};
        tag_mem_wdata[`npuarc_IC_TAG_TAG_RANGE] = lf_addr[`npuarc_IC_TAG_RANGE];
        tag_mem_wdata[`npuarc_IC_TAG_LOCK_BIT] = 1'b0;
        tag_mem_wdata[`npuarc_IC_TAG_VALID_BIT] = 1'b1;
        tag_state_nxt = TAG_LF_RD;
      end
    end
    TAG_LF_RD: begin
      //read back the tag entry for hit detection during and after line fill
      //during line fill a non-line hit request will check tag mem
      //
      tag_mem_cen = {`npuarc_IC_WAYS{1'b1}};
      tag_mem_wen = 1'b0;
      tag_mem_addr = {lf_alias_idx, lf_addr[`npuarc_IC_UNALIASED_IDX_RANGE]};
      if (req_lock_r) begin
        tag_state_nxt = TAG_WAIT_LOCK;
      end
      else begin
        tag_state_nxt = TAG_IDLE;
      end
    end
    TAG_INVLD_ALL: begin
      tag_mem_cen = {`npuarc_IC_WAYS{1'b1}};
      tag_mem_wen = 1'b1;
      tag_mem_addr = tag_idx_cnt;
      tag_mem_wdata = {`npuarc_IC_TWORD_BITS{1'b0}}; 
//leda W484 off
//leda B_3200 off
//leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  addition will not overflow 
      tag_idx_cnt_nxt = tag_idx_cnt + 1;
//leda BTTF_D002 on
//leda B_3200 on
//leda W484 on
      if (&tag_idx_cnt) begin
        tag_rdy = 1'b1;
        aux_ic_ctl_on_nxt = 1'b0;
        tag_chk_clr = 1'b1;
        tag_state_nxt = TAG_IDLE;
      end
    end 
    TAG_INVLD: begin
      tag_mem_wen = 1'b1;
      tag_mem_wdata = {`npuarc_IC_TWORD_BITS{1'b0}};
      if (req_for_err_r) begin
        tag_mem_cen[tag_update_way_r] = 1'b1; 
        tag_mem_addr = {lf_alias_idx_r, lf_addr_r[`npuarc_IC_UNALIASED_IDX_RANGE]};
        lf_err_clr = 1'b1;
        tag_seq_mode_clr = 1'b1;
      end
      else begin
        tag_mem_cen = tag_hit_ways; 
        tag_mem_addr = {aux_alias_r, aux_addr[`npuarc_IC_UNALIASED_IDX_RANGE]};
        aux_req_fail = tag_miss;
        tag_rdy = 1'b1;
        tag_chk_clr = 1'b1;
        aux_ic_ctl_on_nxt = 1'b0;
      end
      tag_chk_clr = 1'b1;
      tag_state_nxt = TAG_IDLE;
    end
    TAG_ERR_INVLD: begin                               //last line error is resolved here
      tag_mem_wen = 1'b1;
      tag_mem_cen[tag_update_way_r] = 1'b1;
      tag_mem_addr = {lf_alias_idx_r, lf_addr_r[`npuarc_IC_UNALIASED_IDX_RANGE]};
      tag_mem_wdata = {`npuarc_IC_TWORD_BITS{1'b0}};
      lf_err_clr = 1'b1;
      tag_seq_mode_clr = 1'b1;
      do_refetch_nxt = tag_chk_r;
      tag_chk_clr = 1'b1; 
      tag_state_nxt = TAG_IDLE;
    end 
    TAG_WAIT_LOCK: begin                              //complete the lock line fetch
      if (!lf_on) begin
        tag_rdy = 1'b1;
        aux_ic_ctl_on_nxt = 1'b0;
        req_lock_nxt = 1'b0;
        req_prefetch_nxt = 1'b0;
        tag_chk_clr = 1'b1; 
        tag_state_nxt = TAG_IDLE;
        if (lbuf_line_err) begin
          lock_line_err = 1'b1;
          aux_req_fail = 1'b1;
        end
      end
    end
    TAG_UNCACHE_REQ: begin
      //tag_chk_r=0 means a restart during 'miss' handling in TAG_IDLE state
      //where we ignored the restart for timing purposes, We have to pick it up here
      //
      if (restart || (!tag_chk_r)) begin
        req_uncache_nxt = 1'b0;
        tag_state_nxt = TAG_IDLE;
      end
      else if (!cache_stg_stall) begin //make sure no data output before uncache access
        lf_start = 1'b1;
        lf_uncache = 1'b1;
        tag_state_nxt = TAG_UNCACHE_WAIT;
      end
    end 
    TAG_UNCACHE_WAIT: begin
      //we wait for the uncached data going out before answering new requests
      //
      if (uncache_data_done || restart || exu_hlt_restart) begin
        req_uncache_nxt = 1'b0;
        tag_state_nxt = TAG_IDLE;
      end
    end
//leda  W71 on
  endcase
end //block : tag_sm_PROC

////////// tag control registers produced by tag state machine ///////////
//these registers are maintained by tag sm for its own use
//and also for down pipe usages (the cache stg)
//
wire do_refetch_nxt_nxt;
wire tag_par_mode_nxt_nxt;
wire tag_seq_mode_nxt_nxt;

assign   do_refetch_nxt_nxt  = restart ? 1'b0 : do_refetch_nxt;

assign   tag_par_mode_nxt_nxt = tag_par_mode_clr 
                              ? 1'b0 
                              : (mode_update 
                                ? tag_par_mode_nxt 
                                : tag_par_mode_r
                                );

assign   tag_seq_mode_nxt_nxt = (tag_seq_mode_clr & clk_en)
                              ? 1'b0
                              : ( (mode_update & clk_en) ? tag_seq_mode_nxt : tag_seq_mode_r);

wire ifetch_iprot_viol_nxt;
assign ifetch_iprot_viol_nxt  = mpu_check_enable_r & ifetch_iprot_viol;
wire ifetch_mpu_viol_nxt;
assign  ifetch_mpu_viol_nxt  = mpu_check_enable_r & ifetch_mpu_viol;

always @*
begin
    tag_state_next      = tag_state_nxt;
    req_way_req_next    = req_way_req_nxt;
    req_lock_next       = req_lock_nxt;
    req_prefetch_next   = req_prefetch_nxt;
    req_for_fetch_next  = req_for_fetch_nxt;
    req_seq_next        = req_seq_nxt;
    tag_vld_next        = tag_vld_nxt;
    tag_miss_next       = tag_miss_nxt;
end

// TAG STATE 
//
always @(posedge clk or posedge rst_a) 
begin: tag_state_r_PROC
  if (rst_a == 1'b1)
  begin
    tag_state            <= TAG_IDLE;
    req_way_req_r        <= 1'b0;
    req_lock_r           <= 1'b0;
    req_prefetch_r       <= 1'b0;
    req_for_fetch_r      <= 1'b0;
    req_seq_r            <= 1'b0;
    tag_vld_r            <= {`npuarc_IC_WAYS{1'b0}};
    tag_miss_r           <= 1'b0;
  end
  else
  begin
    tag_state            <= tag_state_next;
    req_way_req_r        <= req_way_req_next;
    req_lock_r           <= req_lock_next;
    req_prefetch_r       <= req_prefetch_next;
    req_for_fetch_r      <= req_for_fetch_next;
    req_seq_r            <= req_seq_next;
    tag_vld_r            <= tag_vld_next;
    tag_miss_r           <= tag_miss_next;
  end
end // block: tag_state_r_PROC
//
always @*
begin
    aux_ic_ctl_on_next   = aux_ic_ctl_on_nxt;
    req_bank_sel_next    = req_bank_sel_nxt;
    last_is_aux_next     = last_is_aux_nxt;
    req_addr_is_physical_next = req_addr_is_physical_nxt;
end


always @(posedge clk or posedge rst_a) 
begin: tag_ctrl_logic_r_PROC
  if (rst_a == 1'b1) begin
    aux_ic_ctl_on        <= 1'b0;
    req_bank_sel_r       <= {`npuarc_IC_BANKS{1'b0}};
    last_is_aux_r        <= 2'b00;
    req_addr_is_physical_r <= 1'b0;
  end
  else begin
    aux_ic_ctl_on        <= aux_ic_ctl_on_next;
    req_bank_sel_r       <= req_bank_sel_next;
    last_is_aux_r        <= last_is_aux_next;
    req_addr_is_physical_r <= req_addr_is_physical_next;
  end
end //block: tag_ctrl_logic_r_PROC
//
always @(posedge clk or posedge rst_a) 
begin: tag_logic_r_PROC
  if (rst_a == 1'b1) begin
    req_addr_r           <= {`npuarc_PIADDR_BITS{1'b0}};
    req_addr_alias_idx_r <= {`npuarc_IC_ALIAS_BITS{1'b0}};
    req_bank_ctl_r       <= 1'b0;
    req_way_bank_id_r    <= 1'b0;
    req_way_tail_r       <= 1'b0;
    req_addr_offset_r    <= {`npuarc_IC_WRD_BITS{1'b0}};
    req_for_err_r        <= 1'b0;
    req_vec_r            <= 1'b0;
    req_is_restart_r     <= 1'b0;
    way_force_r          <= 1'b0;
    req_way_ptr_r        <= {`npuarc_IC_WAYS_BITS{1'b0}};
    way_update_r         <= 1'b0;
    tag_update_way_r     <= {`npuarc_IC_WAYS_BITS{1'b0}};
    req_uncache_r        <= 1'b0;
    req_tag_val_r        <= 1'b0;
    do_refetch_r         <= 1'b0;
    tag_par_mode_r       <= 1'b0;
    tag_idx_cnt          <= {`npuarc_IC_IDX_BITS{1'b0}};
    tag_seq_mode_r       <= 1'b0;
    itlb_lkup_valid      <= 1'b0;
    mpu_check_enable_r   <= 1'b0;
    mpu_check_uncached_r <= 1'b0;
    ifetch_iprot_viol_r  <= 1'b0;
    ifetch_mpu_viol_r    <= 1'b0;
    ic_waylock_r         <= 4'b0;
  end
  else begin
    req_addr_r           <= req_addr_nxt;

    req_addr_alias_idx_r <= req_addr_alias_idx_nxt;
    req_bank_ctl_r       <= req_bank_ctl_nxt;
    req_addr_offset_r    <= req_addr_offset_nxt;
    req_for_err_r        <= req_for_err_nxt;
    req_vec_r            <= req_vec_nxt;
    req_is_restart_r     <= req_is_restart_nxt;
    way_force_r          <= way_force_nxt;
    req_way_ptr_r        <= req_way_ptr_nxt;
    way_update_r         <= way_update_nxt;
    tag_update_way_r     <= tag_update_way_nxt;
    req_uncache_r        <= req_uncache_nxt;
    req_tag_val_r        <= req_tag_val_nxt;
    tag_idx_cnt          <= tag_idx_cnt_nxt;
    req_way_bank_id_r    <= req_way_bank_id_nxt;
    req_way_tail_r       <= req_way_tail_nxt;
    do_refetch_r         <= do_refetch_nxt_nxt;
    tag_par_mode_r       <= tag_par_mode_nxt_nxt; 

    tag_seq_mode_r       <= tag_seq_mode_nxt_nxt;
    itlb_lkup_valid      <= itlb_lkup_valid_nxt;
    mpu_check_enable_r   <= mpu_check_enable_nxt;
    mpu_check_uncached_r <= mpu_check_uncached_nxt;
    ifetch_iprot_viol_r  <= ifetch_iprot_viol_nxt;
    ifetch_mpu_viol_r    <= ifetch_mpu_viol_nxt;

    // Transfer the ic_waylock register to the 2-cycle clock domain when it changes value.
    // Register ic_waylock is an AUX register in the 1-cycle clock domain, ic_waylock_r is in the 2-cycle clock domain
    ic_waylock_r         <= (ic_waylock != ic_waylock_r) ? ic_waylock : ic_waylock_r;
  end
end //block: tag_logic_r_PROC


// Performance counters:
// Keep track of regular cache accesses to be able to count cache misses.
wire   regular_cache_access;
assign regular_cache_access = req_sel_fetch & fetch_req & (~uncache_mode);

reg ifu_icache_miss_nxt;
reg ifu_icache_hit_nxt;
always @ * 
begin: count_nxt_PROC
  ifu_icache_miss_nxt = ifu_ibus_cmd_valid && ifu_ibus_cmd_accept && regular_cache_access;
  if (clk_en) begin
    ifu_icache_hit_nxt =  (regular_cache_access & ic_hit & tag_chk);
  end
  else begin
    ifu_icache_hit_nxt =  1'b0;
  end
end

// spyglass disable_block Reset_sync04
// SMD: Async reset signal is synchronized at least twice
// SJ:  Legacy code
always @(posedge clk_ibus or posedge rst_a) 
begin: count_PROC
  if (rst_a == 1'b1) begin
    ifu_icache_miss_r <= 1'b0;
    ifu_icache_hit_r <= 1'b0;
  end
  else begin
    // counter for icache miss
    ifu_icache_miss_r <= ifu_icache_miss_nxt;
    ifu_icache_hit_r  <= ifu_icache_hit_nxt;
  end
end
// spyglass enable_block Reset_sync04


//mode signals
assign tag_par_mode = (tag_par_mode_clr) ? 1'b0 : (mode_update) ? tag_par_mode_nxt : tag_par_mode_r;
//assign tag_seq_mode = tag_seq_mode_r[1];
assign mode_par2ser_update = (mode_update && tag_par_mode_r && (!tag_par_mode_nxt)) || tag_par_mode_clr;
      


/////////////////////////// line buffer  ////////////////////////////////////////////
//the line buffer issues bus request to fetch missed cache data from ibus
//the data from ibus will store in cache memory with this temporary (line) buffer  
//the line buffer detects fetch address hit and delivers the fetch data if it's a hit 
//
always @(*) 
begin: req_addr_conv_PROC
  req_addr_r_conv = req_addr_r;
  if (req_bank_ctl_r) begin //1 means bank mis-aligned fetch
    req_addr_r_conv[`npuarc_IC_WRD_RANGE] = req_addr_offset_r;
    req_addr_r_conv[`npuarc_IC_WORD_BITS-1] = 1'b1; //bankID bit, used for uncache access
  end
end
// leda NTL_CON13A off
// LMD: nondriving internal net range
// LJ:  Not all addr bits used
wire  [`npuarc_PIADDR_RANGE] req_paddr_bypass;
// leda NTL_CON13A on
assign lf_addr = (req_addr_is_physical_r) ? req_addr_r_conv : req_paddr[`npuarc_PIADDR_RANGE]; 
assign req_paddr_bypass[`npuarc_PIADDR_RANGE] = (req_addr_is_physical_r) ? req_addr_r : req_paddr[`npuarc_PIADDR_RANGE]; 

// MPU interface
// Pass the fetch address that goes to the line buffer to the MPU.
// This is the critical word first address that triggers the fetch to begin with.
assign ifetch_chk_addr = req_addr_r_conv[`npuarc_PC_RGN_RANGE];


wire lf_kernel;
wire lbuf_hit_cache_int;
assign lf_kernel = req_vec_r | (!ar_user_mode_r);
npuarc_alb_icache_lbuf alb_icache_lbuf_u (
  .clk(clk),
  .clk_en(clk_en),
  .clk_ibus(clk_ibus),
  .rst_a(rst_a),
  .restart(restart),
  .lf_req(ifu_ibus_cmd_valid),
  .lf_req_kernel(ifu_ibus_cmd_prot),
  .lf_req_ack(ifu_ibus_cmd_accept),
  .lf_req_addr(ifu_ibus_cmd_addr),
  .lf_burst_size(ifu_ibus_cmd_burst_size),
  .lf_req_wrap(ifu_ibus_cmd_wrap),
  .ifu_ibus_cmd_cache(ifu_ibus_cmd_cache),
  .lf_req_way(tag_update_way),

  .lf_start(lf_start),
  .lf_kernel(lf_kernel),
  .lf_uncache(lf_uncache),
  .lf_addr(lf_addr), //line address to be fetched
  .lf_alias_idx   (lf_alias_idx),
  .lf_alias_idx_r (lf_alias_idx_r),
  .lf_addr_r(lf_addr_r),
  .lf_err_clr(lf_err_clr),

  .din_err(ifu_ibus_err_rd),
  .din(ifu_ibus_rd_data),
  .din_vld(ifu_ibus_rd_valid),
  .din_accept(ifu_ibus_rd_accept),  

  .dout_vld_urgent(lbuf_dout_vld_urgent),
  .dout_err(lbuf_line_err_busy),   //cache stage signal
  .dout_err_nxt(dout_err_nxt),    //tag stage signal
  .dout_rdy(1'b1), // to do: remove
  .dout(lbuf_dout),
  .dout_waddr(cache_mem_wr_addr),

  .lbuf_en(lf_on),
  .hit_req(lbuf_hit_req),
  .bank_ctl(req_bank_ctl_r),
  .bank_sel(req_bank_sel_r),
  .line_hit(lbuf_line_hit),
  .line_hit_way(lbuf_hit_way),
  .line_in_cache(lbuf_hit_cache_int),
  .hit(lbuf_hit),
  .hit_data(lbuf_hit_data)
);
  assign lbuf_line_err = dout_err_nxt | lf_err_clr;

//we have to qualify lbuf_hit_cache from line buffer to avoid access of cache
//in uncache mode.
//Note -- it takes effect when uncache access hits a cacheable line fetch
assign lbuf_hit_cache = lbuf_hit_cache_int & (!(|tag_ecc_error)) & (!req_uncache_r) 
// In case of an ITLB miss prevent a line buffer hit and force a stall instead
                      & (!itlb_stall)
                   ;

////////////// pn gen for random replacement

always @(posedge clk or posedge rst_a) 
begin: pn_r_PROC
  if (rst_a == 1'b1) begin
    pn_r    <= 10'b1011001101; // seed value of the first 10-bit random generator
    pn2_r   <= 9'b011111111;   // seed value of the 2nd 9-bit random generator
  end
  else if (pn_update) begin
    pn_r    <= pn_next;
    pn2_r   <= pn2_next;
  end
end

always @*
begin: random_way_PROC
  random_way = {`npuarc_IC_WAYS_BITS{1'b0}};

  // calculate the next value for the first pseudo random polynomial
  // 10bit PN generator, polynomial is z**10 + z**7 + 1
    pn_next[9] = pn_r[8];
    pn_next[8] = pn_r[7];
    pn_next[7] = pn_r[6];
    pn_next[6] = pn_r[5];
    pn_next[5] = pn_r[4];
    pn_next[4] = pn_r[3];
    pn_next[3] = pn_r[2];
    pn_next[2] = pn_r[1];
    pn_next[1] = pn_r[0];
  pn_next[0] = pn_r[9] ^ pn_r[6];
  
  // get one random bit from the 10-bit random generator
  rbit = pn_r[0];

  // calculate the next value for the 2nd pseudo random polynomial
  // 9-bit PN generator, polynomial is z**9 + z**5 + 1
    pn2_next[8] = pn2_r[7];
    pn2_next[7] = pn2_r[6];
    pn2_next[6] = pn2_r[5];
    pn2_next[5] = pn2_r[4];
    pn2_next[4] = pn2_r[3];
    pn2_next[3] = pn2_r[2];
    pn2_next[2] = pn2_r[1];
    pn2_next[1] = pn2_r[0];
  pn2_next[0] = pn2_r[8] ^ pn2_r[4];
  
  // get one random bit from the 9-bit random generator
  rbit2 = pn2_r[0];

  // Random number generator for 1-out-of-3 numbers.
  // Generate a 3-bit one-hot encoded signal; exactly one bit for three is set, randomly.
  // Partition the 10-bit random number into thirds; each third corresponds to one of the three numbers.
  // The number 0 can't occur.
  first_limit  = (pn_r <= 10'd341);      // 1 to 341
  second_limit = (pn_r <= 10'd682);      // 1 to 682
  rnum3 = {~second_limit,                // 683 to 1023 = upper 341 numbers
           second_limit & ~first_limit,  // 342 to 682  = middle 341 numbers 
           first_limit                   // 1 to 341    = low 341 numbers
          };


  
  re_read_lock = 4'b0;
  re_read_lock[`npuarc_IC_WAYS-1:0] = {`npuarc_IC_WAYS{maybe_re_read_conflict}} & tag_hit_ways_r;
  tag_do_not_replace = 4'b0;
// spyglass disable_block W116
// SMD: For operator (|), left expression should match right expression
// SJ:  Harmless; tag_lock is 0 extended to 4b
  tag_do_not_replace = tag_lock | ic_waylock_r | re_read_lock;

  // indicate which ways are valid or locked
  // when replacing ways that are invalid avoid ways that are valid or locked
  tag_valid_or_do_not_replace = 4'b0;
  tag_valid_or_do_not_replace = tag_vld | tag_do_not_replace;
// spyglass enable_block W116

  
  // 4-way set-associative
  casez (tag_do_not_replace)
    4'b0000: random_way = { rbit2, rbit };
    4'b0001: random_way = Way_enc({rnum3[2:0], 1'b0});
    4'b0010: random_way = Way_enc({rnum3[2:1], 1'b0, rnum3[0] });
    4'b0011: random_way = Way_enc({ rbit, ~rbit,  2'b0});
    4'b0100: random_way = Way_enc({rnum3[2], 1'b0, rnum3[1:0] });
    4'b0101: random_way = Way_enc({ rbit, 1'b0, ~rbit,  1'b0});
    4'b0110: random_way = Way_enc({ rbit, 2'b0, ~rbit});
    4'b0111: random_way = 2'd3;
    4'b1000: random_way = Way_enc({1'b0, rnum3[2:0]});
    4'b1001: random_way = Way_enc({1'b0,  rbit, ~rbit,  1'b0});
    4'b1010: random_way = Way_enc({1'b0,  rbit, 1'b0, ~rbit});
    4'b1011: random_way = 2'd2;
    4'b1100: random_way = Way_enc({ 2'b0, rbit, ~rbit});
    4'b1101: random_way = 2'd1;
    4'b1110: random_way = 2'd0;
    4'b1111: random_way = 2'd0;
  endcase // casez (tag_do_not_replace)

  tag_lock_all = (tag_do_not_replace == 4'b1111);

  casez (tag_valid_or_do_not_replace)
    4'b???0: first_invld_way = 2'd0;
    4'b??01: first_invld_way = 2'd1;
    4'b?011: first_invld_way = 2'd2;
    default: first_invld_way = 2'd3;
  endcase



end


//////////////////// tag stage registers ////////////////////////////
//these registers are changing according to pipeline stall
//
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Not all bits of bus used
reg [`npuarc_IC_WAYS-1:0] req_cache_mem_cen_r;
reg req_cache_mem_wen_r; 
  // leda NTL_CON32 on
//tag&cache aux read regardless of hit/miss
//lock also needs cache stage for hit ways
//
wire tag_stg_vld_int;
assign tag_stg_vld_int = (tag_chk_r && ic_hit) || tag_val_r || (tag_chk_r && req_lock_r); 
assign tag_stg_stall = cache_stg_stall_tag && (tag_stg_vld_int || tag_par_mode_r || req_uncache_r_r);
wire tag_stg_vld;
assign tag_stg_vld = (tag_par_mode) ?  req_fetch_tag_chk : tag_stg_vld_int; //skip tag-mem in par mode

reg                         tag_chk_nxt;
reg                         tag_val_nxt;
reg [`npuarc_IC_WAYS-1:0]          tag_mem_cen_nxt;
reg                         cache_stg_on_nxt;
reg                         req_cache_dir_nxt;
reg [`npuarc_IC_WAYS-1:0]          req_cache_mem_cen_nxt;
reg                         req_cache_mem_wen_nxt;
reg                         tag_chk_next;
reg                         tag_val_next;
reg [`npuarc_IC_WAYS-1:0]          tag_mem_cen_next;
reg                         cache_stg_on_next;
reg                         req_cache_dir_next;
reg [`npuarc_IC_WAYS-1:0]          req_cache_mem_cen_next;
reg                         req_cache_mem_wen_next;

always@(*)
begin: tag_stage_logic1_PROC
  tag_chk_nxt               = tag_chk_r;
  tag_val_nxt               = tag_val_r;
  tag_mem_cen_nxt           = tag_mem_cen_r;
  cache_stg_on_nxt          = cache_stg_on_r;
  req_cache_dir_nxt         = req_cache_dir_r;
  req_cache_mem_cen_nxt     = req_cache_mem_cen_r;
  req_cache_mem_wen_nxt     = req_cache_mem_wen_r;

  //reset tag valid registers
  //
  if ( tag_chk_clr || (restart && (!(tag_chk||tag_val))) ) begin
    tag_chk_nxt           = 1'b0;
    tag_val_nxt           = 1'b0;
    tag_mem_cen_nxt       = {`npuarc_IC_WAYS{1'b0}};
    cache_stg_on_nxt      = 1'b0;
    req_cache_dir_nxt     = 1'b0;
    req_cache_mem_cen_nxt = {`npuarc_IC_WAYS{1'b0}};
  end
  //pass down new control info
  //
  else if (tag_chk || tag_val ) begin
    tag_chk_nxt           = tag_chk;
    tag_val_nxt           = tag_val;
    tag_mem_cen_nxt       = tag_mem_cen;
    cache_stg_on_nxt      = cache_stg_on; // pre-cache stage vld 
    req_cache_dir_nxt     = req_cache_dir;
    req_cache_mem_cen_nxt = req_cache_mem_cen;
    req_cache_mem_wen_nxt = req_cache_mem_wen;
  end
  //invalidate when miss is resolved and no new request
  //
  else if ( (tag_stg_vld_int||tag_val_r) && (!cache_stg_stall_tag)) begin
    tag_chk_nxt           = 1'b0;
    tag_val_nxt           = 1'b0;
    tag_mem_cen_nxt       = {`npuarc_IC_WAYS{1'b0}};
    cache_stg_on_nxt      = 1'b0;
    req_cache_dir_nxt     = 1'b0;
    req_cache_mem_cen_nxt = {`npuarc_IC_WAYS{1'b0}};
    req_cache_mem_wen_nxt = 1'b0;
  end
end // tag_stage_logic1_PROC

always @*
begin
    tag_chk_next           = tag_chk_nxt;          
    tag_val_next           = tag_val_nxt;
    tag_mem_cen_next       = tag_mem_cen_nxt;
    cache_stg_on_next      = cache_stg_on_nxt;
    req_cache_dir_next     = req_cache_dir_nxt;
    req_cache_mem_cen_next = req_cache_mem_cen_nxt;
    req_cache_mem_wen_next = req_cache_mem_wen_nxt;
end

always @(posedge clk or posedge rst_a) 
begin: tag_stage_reg1_PROC
  if (rst_a == 1'b1) begin
    tag_chk_r           <= 1'b0;
    tag_val_r           <= 1'b0;
    tag_mem_cen_r       <= {`npuarc_IC_WAYS{1'b0}};  // to remember which way of tag is being accessed
    cache_stg_on_r      <= 1'b0;              // to turn on cache stg at next cycle
    req_cache_dir_r     <= 1'b0;              // to turn on direct cache access (an aux function)
    req_cache_mem_cen_r <= {`npuarc_IC_WAYS{1'b0}};  // cache access cen  
    req_cache_mem_wen_r <= 1'b0;              // cache access wen 
  end
  else begin
    tag_chk_r           <= tag_chk_next;          
    tag_val_r           <= tag_val_next;
    tag_mem_cen_r       <= tag_mem_cen_next;
    cache_stg_on_r      <= cache_stg_on_next;
    req_cache_dir_r     <= req_cache_dir_next;
    req_cache_mem_cen_r <= req_cache_mem_cen_next;
    req_cache_mem_wen_r <= req_cache_mem_wen_next;
  end
end


//////////////////// tag hit/miss check ////////////////////////////////////
//We get the tags and line buffer, we decide if it's a hit
//We then output the data being hit
//The data will be available at next cycle after hit detection(serial access)
//For seq mode we are not remembering last hit tag by separate registers, 
//instead we still use tag mem output as is held on 
//
//
reg lbuf_line_hit_r;
//reg lbuf_line_err_r;
reg lbuf_hit_cache_r;
//reg lbuf_hit_r;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg [`npuarc_PC_RANGE] req_addr_r_r;
// leda NTL_CON32 on
reg [`npuarc_IC_WRD_RANGE] req_addr_offset_r_r;
reg [`npuarc_IC_BANKS-1:0] req_bank_sel_r_r;
reg fetch_tag_chk_r_r;

wire [`npuarc_IC_WAYS-1:0] tag_vld_int;



assign tag_eq[0]  = ( tag_mem_rdata0[`npuarc_IC_TAG_TAG_RANGE] == req_paddr_bypass[`npuarc_IC_TAG_RANGE] );
assign tag_vld_int[0]  = tag_mem_rdata0[`npuarc_IC_TAG_VALID_BIT] & (tag_mem_cen_r[0] | req_seq_r); //req_seq_ways[0]);
assign tag_vld[0]  = tag_vld_int[0] & (~tag_ecc_error[0]); 
assign tag_lock[0]  = (tag_mem_rdata0[`npuarc_IC_TAG_LOCK_BIT] & (tag_mem_cen_r[0] | req_seq_r));
assign tag_eq[1]  = ( tag_mem_rdata1[`npuarc_IC_TAG_TAG_RANGE] == req_paddr_bypass[`npuarc_IC_TAG_RANGE] );
assign tag_vld_int[1]  = tag_mem_rdata1[`npuarc_IC_TAG_VALID_BIT] & (tag_mem_cen_r[1] | req_seq_r); //req_seq_ways[1]);
assign tag_vld[1]  = tag_vld_int[1] & (~tag_ecc_error[1]); 
assign tag_lock[1]  = (tag_mem_rdata1[`npuarc_IC_TAG_LOCK_BIT] & (tag_mem_cen_r[1] | req_seq_r));
assign tag_eq[2]  = ( tag_mem_rdata2[`npuarc_IC_TAG_TAG_RANGE] == req_paddr_bypass[`npuarc_IC_TAG_RANGE] );
assign tag_vld_int[2]  = tag_mem_rdata2[`npuarc_IC_TAG_VALID_BIT] & (tag_mem_cen_r[2] | req_seq_r); //req_seq_ways[2]);
assign tag_vld[2]  = tag_vld_int[2] & (~tag_ecc_error[2]); 
assign tag_lock[2]  = (tag_mem_rdata2[`npuarc_IC_TAG_LOCK_BIT] & (tag_mem_cen_r[2] | req_seq_r));
assign tag_eq[3]  = ( tag_mem_rdata3[`npuarc_IC_TAG_TAG_RANGE] == req_paddr_bypass[`npuarc_IC_TAG_RANGE] );
assign tag_vld_int[3]  = tag_mem_rdata3[`npuarc_IC_TAG_VALID_BIT] & (tag_mem_cen_r[3] | req_seq_r); //req_seq_ways[3]);
assign tag_vld[3]  = tag_vld_int[3] & (~tag_ecc_error[3]); 
assign tag_lock[3]  = (tag_mem_rdata3[`npuarc_IC_TAG_LOCK_BIT] & (tag_mem_cen_r[3] | req_seq_r));
  
assign ifetch_viol =  1'b0
                   || (mpu_check_enable_r & ifetch_mpu_viol & ~do_refetch)
                   || (mpu_check_enable_r & ifetch_iprot_viol & ~do_refetch)
                   || (!itlb_stall & itlb_fail_r & (~req_addr_is_physical_r))
                   ;

// Force a cache hit to way 0 in case of a protection violation of an instruction fetch.
// This will prevent icache miss handling and a bus transaction for the violating fetch.
// This also occurs when the icache is disabled, but tag and data RAMs are not activated.
assign tag_hit = {4{restart && clk_en && (!clk2_en_r)}} | 
               (
                 ifetch_viol ? {{3{1'b0}}, 1'b1}
                             : ({`npuarc_IC_WAYS{!(req_uncache_r
                                            | itlb_stall
                                            )}} & tag_eq & tag_vld)
               );


assign tag_hit_ways = {`npuarc_IC_WAYS{tag_chk_r}} & tag_hit;
assign tag_miss_ways= {`npuarc_IC_WAYS{tag_chk_r}} & (~tag_hit); 
assign tag_miss = tag_chk_r & (!(|tag_hit));

assign lbuf_hit_req = tag_chk_r && lf_on; 

assign way_mis_pred = way_force_r && tag_miss;  

//hit/miss final result
//line hit is disabled in parallel mode, assuming data is in cache
//Note: seq mode also goes through tag check

wire lbuf_hit_qual;
// In case of ITLB miss, prevent a hit in the line buffer and resolve the TLB miss first
assign lbuf_hit_qual = lbuf_hit & (~itlb_stall);

assign ic_hit = (lbuf_line_hit) ? (lbuf_hit_qual || lbuf_hit_cache) : |tag_hit_ways; 
assign ic_miss = (lbuf_line_hit) ? (!(lbuf_hit_qual || lbuf_hit_cache)): &tag_miss_ways;

assign do_refetch = do_refetch_r || (tag_par_mode_r && tag_chk_r && (!(|(tag_eq & tag_vld))));

reg tag_stg_err;
reg tag_stg_err_r; // register to remember tag_stg_err
  
always @*
begin: icache_err_PROC
  if (restart)
    tag_stg_err = 1'b0;
  else
  begin
    tag_stg_err = (lbuf_line_hit & lbuf_line_err 
                    & ~itlb_stall
                  ) | tag_stg_err_r;
  end
end

always @(posedge clk or posedge rst_a)  // 2-cycle clock
begin: icache_err_r_PROC
  if (rst_a == 1'b1) begin
    tag_stg_err_r <= 1'b0;
  end
  else 
  begin
    tag_stg_err_r <= tag_stg_err;
  end
end


////////////////////////////////////////////////////////////////////////
///////         cache stage control registers and cache data      //////
////////////////////////////////////////////////////////////////////////
// Cache control signals are usually piped down from tag stage
// However parallel mode skips tag stage 
// Cache stage pass data either from line buffer or cache memory
//

// When the line fill buffer is full, it steals a cycle to empty the line buffer into the cache.
// The cycle stealing is indicated by lf_stall=1
// When lf_stall=1, in the same cycle a write to the data RAMs from the line buffer is set up.
// This stalls a transaction in the tag stage.
// The write is completed in the next cycle, when lf_stall_r=1.
// When the cache output stage is stalled, the cache RAM output cannot move to the fetch buffer.
// If at that moment the line fill buffer is written to the cache RAM, then the pending cache output is lost and needs to be read again.
// This is indicated with cache_re_read.
// Only the icache data RAMs are involved in this; the tag stage remains stalled.  
// In the cycle that lf_stall_r=1, also cache_re_read=1 to set up a read to restore the cache data RAM output.
// In that cycle any bus error in the tag stage should still remain there; the re-read keep the bus error, if any, of the cache stage.
  
assign lf_stall = lf_on && lbuf_dout_vld_urgent;                               

//line fill invalidates the cache memory output and needs to trigger re_read to restore the output data
//
//assign cache_re_read_pre = lf_on && lbuf_dout_vld_urgent && output_stg_stall; 
assign cache_re_read_pre = lf_stall && output_stg_stall; 

//stall signal for cache stage
//
assign cache_stg_stall = output_stg_stall || cache_re_read; 

//stall signal for tag stage
//
assign cache_stg_stall_tag = cache_stg_stall || lf_stall;

//detect the case that line replacement is using the same index as the I$ output 
// In this case the I$ output should have its data in I$ for re_read, i.e. it cannot be replaced
// we need to let the LF_UPDATE know this case so that it won't use the same way as I$output
  
//
assign maybe_re_read_conflict = cache_stg_stall 
                        && ({req_addr_alias_idx_r, req_addr_r[`npuarc_IC_UNALIASED_IDX_RANGE]} == req_addr_r_r[`npuarc_IC_IDX_RANGE]); 


reg                         cache_stg_vld_nxt;
reg                         cache_stg_vld_next;
reg                         cache_re_read_nxt;
reg                         cache_re_read_tmp_nxt;
reg                         cache_stg_err_nxt;
reg                         lf_stall_nxt;
reg                         lf_stall_next;
reg                         mode_par2ser_update_nxt;

reg [`npuarc_IC_WAYS-1:0]          tag_hit_ways_nxt;
reg                         fetch_tag_chk_r_nxt;
reg                         fetch_tag_chk_r_next;
reg [`npuarc_PC_RANGE]             req_addr_r_nxt;
reg [`npuarc_IC_WRD_RANGE]         req_addr_offset_r_nxt;
reg [`npuarc_IC_BANKS-1:0]         req_bank_sel_r_nxt;
reg                         req_uncache_r_nxt; 
reg                         req_uncache_r_next; 
reg                         ifetch_iprot_viol_r_nxt;
reg                         ifetch_mpu_viol_r_nxt;
reg                         itlb_miss_excpn_r_nxt;
reg                         itlb_ecc_err_excpn_r_nxt;
reg                         itlb_ovrlp_excpn_r_nxt;
reg [`npuarc_ITLB_EXEC_PERM_RANGE] itlb_exec_perm_r_nxt;
reg                         lbuf_hit_cache_nxt;
reg                         lbuf_hit_cache_next;
reg                         lbuf_line_hit_nxt;
reg                         lbuf_line_hit_next;
reg                         aux_tag_rdata_vld_nxt;
reg                         aux_cache_rd_ack_nxt;

always@ (*)
begin: tag_stage_logic2_PROC

  cache_stg_vld_nxt        = cache_stg_vld;
  cache_re_read_nxt        = cache_re_read;
  cache_re_read_tmp_nxt    = cache_re_read_tmp_r;
  cache_stg_err_nxt        = cache_stg_err;
  lf_stall_nxt             = lf_stall_r;
  mode_par2ser_update_nxt  = mode_par2ser_update_r;

  tag_hit_ways_nxt         = tag_hit_ways_r;
  fetch_tag_chk_r_nxt      = fetch_tag_chk_r_r;
  req_addr_r_nxt           = req_addr_r_r;
  req_addr_offset_r_nxt    = req_addr_offset_r_r;
  req_bank_sel_r_nxt       = req_bank_sel_r_r;
  req_uncache_r_nxt        = req_uncache_r_r; 
  ifetch_iprot_viol_r_nxt  = ifetch_iprot_viol_r_r;
  ifetch_mpu_viol_r_nxt    = ifetch_mpu_viol_r_r;
  itlb_miss_excpn_r_nxt    = itlb_miss_excpn_r_r;
  itlb_ecc_err_excpn_r_nxt = itlb_ecc_err_excpn_r_r;
  itlb_ovrlp_excpn_r_nxt   = itlb_ovrlp_excpn_r_r;
  itlb_exec_perm_r_nxt     = itlb_exec_perm_r_r;
  lbuf_hit_cache_nxt       = lbuf_hit_cache_r;
  lbuf_line_hit_nxt        = lbuf_line_hit_r;
  aux_tag_rdata_vld_nxt    = aux_tag_rdata_vld;
  aux_cache_rd_ack_nxt     = aux_cache_rd_ack_r;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////  Control paths of cache stage                                    //
/////////////////////////////////////////////////////////////////////////////////////
//
    // In paralell mode, cache access bypasses tag stage
    // 
    if (tag_par_mode) begin
      if (!cache_stg_stall) begin
        cache_stg_vld_nxt     = cache_stg_on;
      end
      cache_re_read_nxt       = 1'b0;
      cache_re_read_tmp_nxt   = 1'b0;
      cache_stg_err_nxt       = 1'b0;
      lf_stall_nxt            = 1'b0;
    end
    // In serial mode, restart will kill the previous cache fetch
    // In serial mode for aux operation, restart won't affect the pipe from tag stage to cache stage 
    //
    else if (restart && (!tag_stg_vld || req_for_fetch_r)) begin
      cache_stg_vld_nxt       = 1'b0;
      cache_re_read_nxt       = 1'b0;  
      cache_re_read_tmp_nxt   = 1'b0;  
      cache_stg_err_nxt       = 1'b0;  
      lf_stall_nxt            = 1'b0;
    end  
    // switching between serial and parallel mode will kill cache stage
    // 
    else if (!cache_stg_stall && (mode_par2ser_update || mode_par2ser_update_r)) begin //switching cycle from par to ser
      mode_par2ser_update_nxt = 1'b0;
      cache_stg_vld_nxt       = 1'b0;
      cache_re_read_nxt       = 1'b0;  
      cache_re_read_tmp_nxt   = 1'b0;  
      cache_stg_err_nxt       = 1'b0;  
      lf_stall_nxt            = 1'b0;
    end  
    else if (!cache_stg_stall || lf_stall || cache_re_read) begin
      // at line fill, cache output is invalidated, re_read is enabled if valid output is stalled
      // 
      if (lf_stall) begin
        cache_stg_vld_nxt     = 1'b0; // invalidate cache output if line fill
        cache_re_read_nxt     = cache_re_read_pre;  
        cache_re_read_tmp_nxt = 1'b0; 
        // Keep the error status for potential re_read
        //
        if (!cache_stg_stall) begin
          cache_stg_err_nxt   = tag_stg_err; 
        end
        else begin
          cache_stg_err_nxt   = tag_stg_err & cache_re_read_pre; 
        end
        lf_stall_nxt          = 1'b1;
      end
      // Re_read forces cache output to be valid
      // Otherwise cache is set to valid from tag stage
      //
      else begin
        cache_stg_vld_nxt     = cache_re_read | (cache_stg_on_r & tag_stg_vld);
        cache_re_read_nxt     = 1'b0;
        cache_re_read_tmp_nxt = cache_re_read; 
        // both cache_re_read and lf_stall_r are the cycles to re-fetch from cache memory
        // we should use the previous error state 
        //
        if (!cache_re_read && (!lf_stall_r)) begin
          cache_stg_err_nxt   = tag_stg_err;
        end
        lf_stall_nxt          = 1'b0;
      end
    end
    //we need to keep the status of par2ser if pipe line is stalled
    //
    else if (cache_stg_stall && mode_par2ser_update) begin 
      mode_par2ser_update_nxt = 1'b1;
    end

/////////////////////////////////////////////////////////////////////////////////////
/////////////////  Data paths of cache stage                                       //
/////////////////////////////////////////////////////////////////////////////////////
//
    if (tag_par_mode) begin //skip tag stage
      req_addr_r_nxt            = req_addr_nxt[`npuarc_PC_RANGE];
      req_addr_offset_r_nxt     = req_addr_offset_nxt;  
      req_bank_sel_r_nxt        = req_bank_sel_nxt;
      req_uncache_r_nxt         = req_uncache_nxt;
      fetch_tag_chk_r_nxt       = 1'b1;  
      if (fetch_way_force & fetch_req & (!cache_stg_stall)) begin
        tag_hit_ways_nxt        = Way_set_func(fetch_way_ptr);
      end
      lbuf_line_hit_nxt         = 1'b0;
//    lbuf_line_err_nxt         = 1'b0;
//    lbuf_hit_nxt              = 1'b0;
      lbuf_hit_cache_nxt        = 1'b0;
    end  
    else if (!cache_stg_stall) begin
      if (cache_stg_on_r && tag_stg_vld) begin //serialized tag and cache
        req_addr_r_nxt          = {req_addr_r[`npuarc_IC_UNALIASED_TAG_RANGE], req_addr_alias_idx_r, req_addr_r[`npuarc_IC_UNALIASED_IDX_MSB:1]};

        if (!restart) begin
          ifetch_iprot_viol_r_nxt = ifetch_iprot_viol & mpu_check_enable_r & ~do_refetch;
        end
        if (!restart) begin
          ifetch_mpu_viol_r_nxt  = ifetch_mpu_viol & mpu_check_enable_r & ~do_refetch;
        end
        if (!restart) begin
          itlb_miss_excpn_r_nxt    = itlb_miss_excpn_nxt;
          itlb_ecc_err_excpn_r_nxt = itlb_ecc_err_excpn_nxt;
          itlb_ovrlp_excpn_r_nxt   = itlb_ovrlp_excpn_nxt;
          itlb_exec_perm_r_nxt     = itlb_exec_perm_nxt;
        end
        req_addr_offset_r_nxt = req_addr_offset_r;
        req_bank_sel_r_nxt    = req_bank_sel_r;
        req_uncache_r_nxt     = req_uncache_r;
        fetch_tag_chk_r_nxt   = req_for_fetch_r;  
        if (req_cache_dir_r) begin
          tag_hit_ways_nxt    = req_cache_mem_cen_r;
        end
        else if (lbuf_line_hit) begin
          tag_hit_ways_nxt    = Way_set_func(lbuf_hit_way); 
        end
        else begin
          tag_hit_ways_nxt    = tag_hit_ways;
        end
        lbuf_line_hit_nxt     = lbuf_line_hit;
//      lbuf_line_err_nxt     = lbuf_line_err; // aligned with lbuf_hit
//      lbuf_hit_nxt          = lbuf_hit;
        lbuf_hit_cache_nxt    = lbuf_hit_cache;
      end
    end

    aux_tag_rdata_vld_nxt     = (tag_chk|tag_val) & (!req_fetch_tag_chk) & (!req_err_tag_chk);
    if (aux_cache_rd_ack_pre) begin
      aux_cache_rd_ack_nxt    = 1'b1;
    end
    else if (tag_state == TAG_IDLE) begin
      aux_cache_rd_ack_nxt    = 1'b0;
    end

    if (restart) begin
      ifetch_iprot_viol_r_nxt = 1'b0;
      ifetch_mpu_viol_r_nxt   = 1'b0;
      mode_par2ser_update_nxt = 1'b0;
    end

    if (restart) begin
      itlb_miss_excpn_r_nxt    = 1'b0;
      itlb_ecc_err_excpn_r_nxt = 1'b0;
      itlb_ovrlp_excpn_r_nxt   = 1'b0;
      itlb_exec_perm_r_nxt     = itlb_exec_perm_nxt;
    end
end // tag_stage_logic2_PROC

always @*
begin
    req_uncache_r_next     = req_uncache_r_nxt;
    fetch_tag_chk_r_next   = fetch_tag_chk_r_nxt;
    cache_stg_vld_next     = cache_stg_vld_nxt;
    lf_stall_next          = lf_stall_nxt;
    lbuf_hit_cache_next    = lbuf_hit_cache_nxt;
    lbuf_line_hit_next     = lbuf_line_hit_nxt;
end

always @(posedge clk or posedge rst_a) 
begin : tag_sr_stage_req2_PROC
  if (rst_a == 1'b1) begin
    req_uncache_r_r        <= 1'b0;
    fetch_tag_chk_r_r      <= 1'b0;
    cache_stg_vld          <= 1'b0;
    lf_stall_r             <= 1'b0;
    lbuf_hit_cache_r       <= 1'b0;
    lbuf_line_hit_r        <= 1'b0;
  end
  else begin
    req_uncache_r_r        <= req_uncache_r_next;
    fetch_tag_chk_r_r      <= fetch_tag_chk_r_next;
    cache_stg_vld          <= cache_stg_vld_next;
    lf_stall_r             <= lf_stall_next;
    lbuf_hit_cache_r       <= lbuf_hit_cache_next;
    lbuf_line_hit_r        <= lbuf_line_hit_next;
  end
end // block :  tag_sr_stage_req2_PROC

always @(posedge clk or posedge rst_a) 
begin: tag_stage_reg2_PROC
  if (rst_a == 1'b1) begin
    //cache stage registers 
    //
    tag_hit_ways_r         <= {`npuarc_IC_WAYS{1'b0}};
    req_addr_r_r           <= {`npuarc_PC_BITS{1'b0}};
    req_addr_offset_r_r    <= {`npuarc_IC_WRD_BITS{1'b0}}; 
    req_bank_sel_r_r       <= {`npuarc_IC_BANKS{1'b0}};
    ifetch_iprot_viol_r_r  <= 1'b0;
    ifetch_mpu_viol_r_r    <= 1'b0;
    itlb_miss_excpn_r_r    <= 1'b0;
    itlb_ecc_err_excpn_r_r <= 1'b0;
    itlb_ovrlp_excpn_r_r   <= 1'b0;
    itlb_exec_perm_r_r     <= 3'd0;
     cache_re_read          <= 1'b0;
    cache_re_read_tmp_r        <= 1'b0;
    cache_stg_err          <= 1'b0;
     mode_par2ser_update_r  <= 1'b0;
    aux_tag_rdata_vld      <= 1'b0;
    aux_cache_rd_ack_r     <= 1'b0;
  end
  else begin
/////////////////////////////////////////////////////////////////////////////////////
/////////////////  Control paths of cache stage                                    //
/////////////////////////////////////////////////////////////////////////////////////
//
    cache_re_read          <= cache_re_read_nxt;
    cache_re_read_tmp_r        <= cache_re_read_tmp_nxt;
    cache_stg_err          <= cache_stg_err_nxt;
    mode_par2ser_update_r  <= mode_par2ser_update_nxt;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////  Data paths of cache stage                                       //
/////////////////////////////////////////////////////////////////////////////////////
//
    tag_hit_ways_r         <= tag_hit_ways_nxt;
    req_addr_r_r           <= req_addr_r_nxt;
    req_addr_offset_r_r    <= req_addr_offset_r_nxt;
    req_bank_sel_r_r       <= req_bank_sel_r_nxt;
    ifetch_iprot_viol_r_r  <= ifetch_iprot_viol_r_nxt;
    ifetch_mpu_viol_r_r    <= ifetch_mpu_viol_r_nxt;
    itlb_miss_excpn_r_r    <= itlb_miss_excpn_r_nxt;
    itlb_ecc_err_excpn_r_r <= itlb_ecc_err_excpn_r_nxt;
    itlb_ovrlp_excpn_r_r   <= itlb_ovrlp_excpn_r_nxt;
    itlb_exec_perm_r_r     <= itlb_exec_perm_r_nxt;
    aux_tag_rdata_vld      <= aux_tag_rdata_vld_nxt;
    aux_cache_rd_ack_r     <= aux_cache_rd_ack_nxt;
  end
end

wire cache_out_for_fetch;
assign cache_out_for_fetch = fetch_tag_chk_r_r;
wire [`npuarc_IC_WAYS-1:0] cache_out_vld_ways;
assign  cache_out_vld_ways = tag_hit_ways_r;

/////////////////////performance counter conditions//////////

wire ifu_way_pred_miss_nxt, ifu_way_pred_miss_nxt_nxt;
   assign ifu_way_pred_miss_nxt = cache_out_for_fetch 
                                & cache_stg_vld 
                                & way_mis_pred 
                                & tag_par_mode_r
                                ;

   assign ifu_way_pred_miss_nxt_nxt = clk_en ? ifu_way_pred_miss_nxt : 1'b0;

//spyglass disable_block Reset_sync04
// SMD: Async reset signal is synchronized at least twice
// SJ:  Legacy code
always @(posedge clk or posedge rst_a)
begin: mis_pred_regs_PROC
  if (rst_a == 1'b1)
    ifu_way_pred_miss_r <= 1'b0;
  else 
  begin
    ifu_way_pred_miss_r <= ifu_way_pred_miss_nxt_nxt;
  end
end
//spyglass enable_block Reset_sync04


///////////////////// fetch output /////////////////////////
//
assign ecc_enable = (!lbuf_line_hit_r || lbuf_hit_cache_r || cache_re_read_tmp_r);
wire [`npuarc_IC_DRAM_RANGE] fetch_data_pre;

// signal no_bypass_select determines if critical word first bypass is used from the input line buffer
// If set to 0, then bypass is used; if set to 1 then regular access from cache RAMs is used.
wire no_bypass_select;
assign no_bypass_select=!lbuf_line_hit_r || lbuf_hit_cache_r || cache_re_read_tmp_r; 

//assign fetch_data_pre = (!lbuf_line_hit_r || lbuf_hit_cache_r || cache_re_read_tmp_r) ? 
assign fetch_data_pre = no_bypass_select ? 
  ( {`npuarc_IC_DRAM_BITS{cache_out_vld_ways[0]}} & cache_mem_rdata0 ) | 
  ( {`npuarc_IC_DRAM_BITS{cache_out_vld_ways[1]}} & cache_mem_rdata1 ) | 
  ( {`npuarc_IC_DRAM_BITS{cache_out_vld_ways[2]}} & cache_mem_rdata2 ) | 
  ( {`npuarc_IC_DRAM_BITS{cache_out_vld_ways[3]}} & cache_mem_rdata3 ) | 
//{`IC_DRAM_BITS{1'b0}} : {{`ECC_IC_BANK_BITS{1'b1}},lbuf_hit_data[127:64],
//                         {`ECC_IC_BANK_BITS{1'b1}},lbuf_hit_data[63:0]};
  {`npuarc_IC_DRAM_BITS{1'b0}} : {{`npuarc_ECC_IC_BANK_BITS{1'b1}},lbuf_hit_data[`npuarc_IM_DWIDTH-1:`npuarc_IM_DWIDTH/2], 
                           {`npuarc_ECC_IC_BANK_BITS{1'b1}},lbuf_hit_data[`npuarc_IM_DWIDTH/2-1:0]};
wire fetch_data_err_pre;


// mux bus error signal into the error signals that goes with the fetch data if bypass is used
assign fetch_data_err_pre = no_bypass_select ? cache_stg_err : lbuf_line_err_busy; 
//assign fetch_data_err_pre = cache_stg_err; 

assign fetch_data_way_pre = Way_enc(tag_hit_ways_r);

wire [`npuarc_IC_WIDTH-1:0] fetch_data_skid;
assign fetch_data_skid = fetch_data_pre;
wire fetch_data_vld_pre;
assign fetch_data_vld_pre = cache_out_for_fetch & cache_stg_vld & (!(way_mis_pred && tag_par_mode_r));
assign aux_cache_rd_ack_pre = !cache_out_for_fetch & cache_stg_vld;

assign output_stg_stall = !fetch_data_rdy && fetch_data_vld_pre; 
assign uncache_data_done = req_uncache_r_r && fetch_data_vld_pre && fetch_data_rdy; //uncache data is taken by down pipe

always @(*) 
begin: fetch_data_out_PROC
  fetch_data_vld = {`npuarc_IC_BANKS{fetch_data_vld_pre}} & req_bank_sel_r_r;
  fetch_data_err = fetch_data_err_pre;
  fetch_data_way = fetch_data_way_pre; 
  fetch_data = fetch_data_skid;
  aux_cache_rd_ack = aux_cache_rd_ack_pre;
end

////////////////// cache memory output signal generation ///////////////////
//
wire fetch_use_cache_mem;
reg [`npuarc_IC_WAY_ADR_RANGE] cache_mem_addr;
reg [`npuarc_IC_WRD_RANGE] cache_mem_addr_offset;

assign fetch_use_cache_mem = tag_par_mode || 
                               (req_for_fetch_r && (!lbuf_line_hit) && (|tag_hit_ways) 
                                && clk2_en_r
                               ); 

assign aux_use_cache_mem = aux_bist || (!cache_stg_stall && (!req_for_fetch_r) && cache_stg_on_r);

//mux control signal to put tag_par_mode at fastest path
//
wire cache_use_fetch;
assign cache_use_fetch = !((lf_on && lbuf_dout_vld_urgent) || aux_use_cache_mem || cache_re_read) && 
                        (!cache_stg_stall) && (fetch_use_cache_mem || lbuf_hit_cache);
 
always @(*) 
begin: cache_mem_out_PROC
  cache_mem_cen = {`npuarc_IC_WAYS{1'b0}};
  cache_mem_wen = 1'b0;
  cache_mem_wem = {`npuarc_IC_BYTE_WIDTH{1'b0}};
  cache_mem_wdata = {`npuarc_IC_LBUF_SIZE{1'b0}};
  cache_mem_addr = fetch_addr0[`npuarc_IC_WAY_ADR_RANGE]; 
  cache_mem_addr_offset = fetch_addr1_offset; 
  cache_mem_bank_sel = fetch_bank_ctl[`npuarc_IC_BANKS-1:0];
  //Cache memory access for fetch --
  //1. in paralell mode if the way is predicted, we fetch the way pointed by BPU
  //2. in paralell mode after way prediction, we keep using the same way as long as it's a hit  
  //3. in serial mode the hit way is used
  //we have "cache_use_fetch" for timing purposes
  //
  if (cache_use_fetch) begin
    if (tag_par_mode) begin
      if (fetch_way_force) begin
        cache_mem_cen[fetch_way_ptr] = cache_stg_on;                    // (1)
      end
      else begin
        cache_mem_cen = tag_hit_ways_r & {`npuarc_IC_WAYS{cache_stg_on}};      // (2)
      end
    end
    else begin
      cache_mem_cen = tag_hit_ways;                                     // (3)


      cache_mem_addr = {req_addr_alias_idx_r, req_addr_r[`npuarc_IC_UNALIASED_IDX_RANGE], req_addr_r[`npuarc_IC_WRD_RANGE]};

      cache_mem_addr_offset = req_addr_offset_r;
      cache_mem_bank_sel = req_bank_sel_r;
    end
  end
  //Cache memory access for other purposes --
  //case 0 -- line fill
  else if (lf_on && lbuf_dout_vld_urgent) begin
    cache_mem_cen[tag_update_way_r] = lbuf_dout_vld_urgent; //means cache write
    cache_mem_wen = 1'b1;
    cache_mem_wem = {`npuarc_IC_BYTE_WIDTH{1'b1}};
    cache_mem_wdata = lbuf_dout;
    cache_mem_addr = cache_mem_wr_addr;
    cache_mem_addr_offset = cache_mem_wr_addr[`npuarc_IC_WRD_RANGE];
    cache_mem_bank_sel = {`npuarc_IC_BANKS{1'b1}};
  end  
  //case 1 -- re_read cache, use last cycle info
  else if (cache_re_read) begin
    cache_mem_cen = tag_hit_ways_r;
    cache_mem_addr = req_addr_r_r[`npuarc_IC_WAY_ADR_RANGE]; 
    cache_mem_addr_offset = req_addr_offset_r_r;
    cache_mem_bank_sel = req_bank_sel_r_r;
  end
  //case 2 -- aux access
  else if (aux_use_cache_mem) begin
      if (req_cache_dir_r) begin
        cache_mem_cen = req_cache_mem_cen_r; 
        cache_mem_bank_sel = {req_addr_r[`npuarc_IC_BANK_WORD_BITS], !req_addr_r[`npuarc_IC_BANK_WORD_BITS]};
      end
      else begin
        cache_mem_cen = tag_hit_ways;
        cache_mem_bank_sel = {`npuarc_IC_BANKS{1'b1}};
      end
      cache_mem_wen = req_cache_mem_wen_r;
      cache_mem_wem = req_cache_mem_wem;
      cache_mem_wdata = req_cache_mem_wdata;
      cache_mem_addr = {req_addr_alias_idx_r, req_addr_r[`npuarc_IC_UNALIASED_IDX_RANGE], req_addr_r[`npuarc_IC_WRD_RANGE]};
      cache_mem_addr_offset = req_addr_offset_r;
  end
end
 
assign cache_mem_addr0 = cache_mem_addr;
assign cache_mem_addr1 = {cache_mem_addr[`npuarc_IC_IDX_RANGE], cache_mem_addr_offset};

////////////////// aux register read data source ///////////////////
//hard code to 128 bit IC width and 32bit aux_data width
//
always @(*)
begin: aux_tag_rdata_PROC 
  aux_tag_mem_rdata =
    ( {`npuarc_IC_TRAM_BITS{tag_mem_cen_r[0]}} & tag_mem_rdata0 ) |
    ( {`npuarc_IC_TRAM_BITS{tag_mem_cen_r[1]}} & tag_mem_rdata1 ) |
    ( {`npuarc_IC_TRAM_BITS{tag_mem_cen_r[2]}} & tag_mem_rdata2 ) |
    ( {`npuarc_IC_TRAM_BITS{tag_mem_cen_r[3]}} & tag_mem_rdata3 ) |
    {`npuarc_IC_TRAM_BITS{1'b0}};

  aux_tag_rdata = {`npuarc_PADDR_SIZE{1'b0}};
  if (req_cache_dir_r) begin
    aux_tag_rdata[0] = aux_tag_mem_rdata[`npuarc_IC_TAG_VALID_BIT];
    aux_tag_rdata[1] = aux_tag_mem_rdata[`npuarc_IC_TAG_LOCK_BIT];

    aux_tag_rdata[`npuarc_IC_TAG_RANGE] = aux_tag_mem_rdata[`npuarc_IC_TAG_TAG_RANGE];

  end
  else begin
    aux_tag_rdata[0] = |tag_hit; //valid bit
    aux_tag_rdata[1] = |(tag_hit & tag_lock); //lock bit
    aux_tag_rdata[`npuarc_IC_TAG_RANGE] = req_addr_r[`npuarc_IC_TAG_RANGE];
  end
end


assign req_cache_mem_wdata = (aux_bist) ? {`npuarc_IC_SIZE_MUL*2{aux_wdata}} : {`npuarc_IC_SIZE_MUL*4{aux_wdata[`npuarc_DATA_RANGE]}}; 
always @(*) 
begin: aux_cache_rdata_PROC
  req_cache_mem_wem = {`npuarc_IC_BYTE_WIDTH{1'b0}};
//leda  W71 off
// LMD: Case statement without default clause and not all cases are covered
// LJ:  Default output assignments are from above
  if (aux_bist) begin
    case (aux_addr[`npuarc_IC_WORD_BITS-1])
    1'b0: req_cache_mem_wem[7:0] = aux_wmask[7:0];
    1'b1: req_cache_mem_wem[15:8] = aux_wmask[7:0];
    endcase
  end
  else begin



    case (aux_addr[`npuarc_IC_WORD_BITS-1:`npuarc_DATA_WORD_BITS])
    2'd0: req_cache_mem_wem[3:0] = 4'hf;
    2'd1: req_cache_mem_wem[7:4] = 4'hf;
    2'd2: req_cache_mem_wem[11:8] = 4'hf;
    2'd3: req_cache_mem_wem[15:12] = 4'hf;




    endcase
  end

    case (aux_addr[`npuarc_IC_WORD_BITS-1:`npuarc_DATA_WORD_BITS])
    2'd0: aux_rdata = { {`npuarc_IC_BANK_WIDTH-32{1'b0}}, fetch_data[70:64],fetch_data[31:0]};
    2'd1: aux_rdata = { {`npuarc_IC_BANK_WIDTH-32{1'b0}}, fetch_data[77:71],fetch_data[63:32]};
    2'd2: aux_rdata = { {`npuarc_IC_BANK_WIDTH-32{1'b0}}, fetch_data[148:142],fetch_data[109:78]};
    2'd3: aux_rdata = { {`npuarc_IC_BANK_WIDTH-32{1'b0}}, fetch_data[155:149],fetch_data[141:110]};

    endcase


//leda  W71 on
end

assign aux_rdata_vld = aux_cache_rd_ack;

/////////////// way output for prediction  ///////////////
//
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg [`npuarc_PC_RANGE] way_for_pred_pc_nxt;
// leda NTL_CON32 on
reg [`npuarc_IC_WRD_RANGE] way_for_pred_offset_nxt;
reg [`npuarc_IC_WRD_RANGE] way_for_pred_offset_r;
reg way_sec_for_pred_nxt;
reg way_is_bta_nxt; 
reg way_is_bta_r; 

always @(*)
begin: way_pred_pc_nxy_PROC 
  way_for_pred_pc_nxt = way_for_pred_pc;
  way_sec_for_pred_nxt = way_sec_for_pred; 
  way_for_pred_offset_nxt = way_for_pred_offset_r;
  way_is_bta_nxt = way_is_bta_r;
  if (mpd_pc_load) begin
    if (mpd_mispred)
    begin
      way_for_pred_pc_nxt = mpd_pc;
      way_is_bta_nxt = mpd_direction;            //1-means allowing update of way in case of misprediction
    end
    way_sec_for_pred_nxt = req_way_sec; 
  end
  else if (fetch_req && fetch_rdy && clk_en) begin
    way_sec_for_pred_nxt = req_way_sec; 
    if (!fetch_is_restart) begin
      way_is_bta_nxt = 1'b1;
      if (req_way_tail_r) begin
        way_for_pred_pc_nxt[`npuarc_IM_WORD_BITS-1] = req_way_bank_id_r;
        if (req_way_bank_id_r) begin
          way_for_pred_pc_nxt[`npuarc_IC_WRD_RANGE] = way_for_pred_offset_r;
        end 
      end 
      else begin
        way_for_pred_pc_nxt = req_addr_r[`npuarc_PC_RANGE];
        way_for_pred_pc_nxt[`npuarc_IC_ALIAS_IDX_RANGE] = req_addr_alias_idx_r;
        way_for_pred_pc_nxt[`npuarc_IM_WORD_BITS-1] = req_way_bank_id;
        way_for_pred_offset_nxt = req_addr_offset_r;
        if (req_way_bank_id) begin
          way_for_pred_pc_nxt[`npuarc_IC_WRD_RANGE] = req_addr_offset_r;
        end
      end
    end
  end
end
   
always @(posedge clk_ibus or posedge rst_a) 
begin: way_pred_pc_out_PROC
  if (rst_a == 1'b1) begin
    way_for_pred_pc       <= {`npuarc_PC_BITS{1'b0}};
    way_for_pred_offset_r <= {`npuarc_IC_WRD_BITS{1'b0}};
    way_sec_for_pred      <= 1'b0; 
    way_is_bta_r          <= 1'b0;
  end
  else begin
    way_for_pred_pc       <= way_for_pred_pc_nxt;
    way_sec_for_pred      <= way_sec_for_pred_nxt; 
    way_for_pred_offset_r <= way_for_pred_offset_nxt;
    way_is_bta_r          <= way_is_bta_nxt;
  end
end

wire way_update_int;
assign way_update_int = way_update && (!restart);
assign way_for_pred_vld = way_update_int && way_is_bta_r && clk_en &&
                          (req_way_req_r || (req_way_ptr_r != tag_hit_way_ptr));
//assign way_miss_pred = way_update_int && clk_en && (req_way_ptr_r != tag_hit_way_ptr);
assign tag_hit_way_ptr = Way_enc_1(tag_hit_ways); 
assign way_for_pred = tag_hit_way_ptr;

////////////////////////////////////////////////////////////////////////
///////         aux register request decode                       //////
////////////////////////////////////////////////////////////////////////
parameter REG_CACHE_RD_IND = 0; // cache/tag memory read, normal read
parameter REG_CACHE_RD_DIR = 1; // cache/tag memory read, direct read
parameter REG_CACHE_WR_DIR = 2; // cache memory write, direct write
parameter REG_TAG_WR_DIR = 3;   // tag memory write, direct write
parameter REG_TAG_INVLD = 4;    // tag invalidate, all
parameter REG_TAG_INVLDL = 5;   // tag invalidate, line only
parameter REG_TAG_LOCK = 6;     // tag line lock
parameter REG_TAG_PREFETCH = 7; // tag line prefetch

always @(*)
begin: aux_cmd_decode_PROC 
  aux_req_tag_mem       = 1'b0;
  aux_req_tag_mem_cen   = {`npuarc_IC_WAYS{1'b0}};
  aux_req_tag_mem_wen   = 1'b0;
  aux_req_cache_mem     = 1'b0;
  aux_req_cache_mem_wen = 1'b0;
  aux_req_cache_mem_cen = {`npuarc_IC_WAYS{1'b0}};
  aux_req_tag_mem_addr  = aux_addr;
  aux_req_tag_mem_addr_alias  = aux_alias_r;
  aux_req_tag_mem_wdata = aux_wdata[`npuarc_IC_TWORD_RANGE];
  aux_req_tag_chk       = 1'b0;
  aux_req_cache_dir     = 1'b0;
  aux_do_invld_all      = 1'b0;
  aux_req_tag_invld     = 1'b0;
  aux_req_tag_lock      = 1'b0;
  aux_req_prefetch      = 1'b0;
  aux_req_tag_val       = 1'b0;

  if (aux_req_mode[REG_CACHE_RD_IND])
  begin
    aux_req_tag_mem = 1'b1;
    aux_req_tag_mem_cen = {`npuarc_IC_WAYS{1'b1}};
    aux_req_tag_chk = 1'b1;
    aux_req_cache_mem = 1'b1;
    aux_req_tag_val = 1'b1;
  end
  else
  if (aux_req_mode[REG_CACHE_RD_DIR])
  begin
    aux_req_tag_mem = 1'b1;
    aux_req_tag_mem_cen[aux_cache_mem_way] = 1'b1;
    aux_req_cache_mem = 1'b1;
    aux_req_cache_mem_cen[aux_cache_mem_way] = 1'b1;
    aux_req_cache_dir = 1'b1;
    aux_req_tag_val = 1'b1;
  end
  else
  if (aux_req_mode[REG_CACHE_WR_DIR])
  begin
    aux_req_tag_mem = 1'b1;
    aux_req_tag_mem_cen[aux_cache_mem_way] = 1'b1; //we enable tag read even if the tag is not used
                                                   //it's a case to support req_addr_r 2 cycle path
    aux_req_cache_mem = 1'b1;
    aux_req_cache_mem_wen = 1'b1;
    aux_req_cache_mem_cen[aux_cache_mem_way] = 1'b1;
    aux_req_cache_dir = 1'b1;
    aux_req_tag_val = 1'b1;
  end
  else
  if (aux_req_mode[REG_TAG_WR_DIR])
  begin
    aux_req_tag_mem = 1'b1;
    aux_req_tag_mem_cen[aux_cache_mem_way] = 1'b1;
    aux_req_tag_mem_wen = 1'b1;
    aux_req_cache_mem = 1'b1; //fake cache mem access to finish tag_val operation
    aux_req_cache_dir = 1'b1;
    aux_req_tag_val = 1'b1;
  end
  else
  if (aux_req_mode[REG_TAG_INVLD])
  begin
    aux_req_tag_mem = 1'b1;
    aux_req_tag_mem_cen = {`npuarc_IC_WAYS{1'b1}};
    aux_req_tag_mem_wen = 1'b1;
    aux_req_tag_mem_wdata = {`npuarc_IC_TWORD_BITS{1'b0}};  
    aux_req_tag_mem_addr = {`npuarc_PIADDR_BITS{1'b0}};
    aux_do_invld_all = 1'b1;
  end
  else
  if (aux_req_mode[REG_TAG_INVLDL])
  begin
    aux_req_tag_mem = 1'b1;
    aux_req_tag_mem_cen = {`npuarc_IC_WAYS{1'b1}};
    aux_req_tag_chk = 1'b1;
    aux_req_tag_invld = 1'b1;     
  end
  else
  if (aux_req_mode[REG_TAG_LOCK])
  begin
    aux_req_tag_mem = 1'b1;
    aux_req_tag_mem_cen = {`npuarc_IC_WAYS{1'b1}};
    aux_req_tag_chk = 1'b1;
    aux_req_tag_lock = 1'b1;
    aux_req_prefetch = 1'b0;  // do lock, not prefetch
    aux_req_cache_mem = 1'b1; //fake cache mem access to finish tag_lock operation
  end
  else
  if (aux_req_mode[REG_TAG_PREFETCH])
  begin
    aux_req_tag_mem = 1'b1;
    aux_req_tag_mem_cen = {`npuarc_IC_WAYS{1'b1}};
    aux_req_tag_chk = 1'b1;
    aux_req_tag_lock = 1'b1; // lock sequence is also used for prefetch
    aux_req_prefetch = 1'b1; // enable prefetch that doesn't lock
    aux_req_cache_mem = 1'b1; //fake cache mem access to finish prefetch operation
  end
  
end //block: aux_cmd_decode_PROC

//////////////// I-cache state report ///////////////////////////////
assign hlt_ready = (tag_state == TAG_IDLE) && (!lf_on) && (!cache_stg_on_r) &&
                   (!aux_req) && (!lbuf_line_err_busy);

//spyglass disable_block Clock_Reset_check02
// SMD: Potential race between flop
// SJ:  meme_busy controls its clock (by clock gate) conditionally by restart
//      if no restart, its clock runs every other core clock
//      Therefore there is no racing condition
always @(posedge clk or posedge rst_a) 
begin: mem_busy_PROC
  if (rst_a == 1'b1) begin
    mem_busy <= 1'b0;
  end
  else begin
    mem_busy <= (|tag_mem_cen) || (|cache_mem_cen); 
  end
end
//spyglass enable_block Clock_Reset_check02

////////////////////////////////////////////////////////////////////////
///////         functions                                         //////
////////////////////////////////////////////////////////////////////////
//
// 
//spyglass disable_block AutomaticFuncTask-ML
// SMD: Function not declared as automatic
// SJ:  Legacy code
function [`npuarc_IC_WAYS_BITS-1:0] Way_enc;
input [`npuarc_IC_WAYS-1:0] vld_in;
integer i;
integer j;
reg [31:0] way_enc_j;
begin
  j = 0;
  way_enc_j = 32'b0;
  for (i=0; i<`npuarc_IC_WAYS; i=i+1) begin
    if (vld_in[i]) j = i;
  end
  way_enc_j = $unsigned(j);
  Way_enc = way_enc_j[`npuarc_IC_WAYS_BITS-1:0];
end
endfunction

//
function [`npuarc_IC_WAYS_BITS-1:0] Way_enc_1;
input [`npuarc_IC_WAYS-1:0] vld_in;
integer i;
integer j;
reg [31:0] way_enc_1_j;
begin
  j = 0;
  way_enc_1_j = 32'b0;
  for (i=0; i<`npuarc_IC_WAYS; i=i+1) begin
    if (vld_in[i]) j = i;
  end
  way_enc_1_j = $unsigned(j);
  Way_enc_1 = way_enc_1_j[`npuarc_IC_WAYS_BITS-1:0];
end
endfunction
//

//Decode cache way pointer 
//
function [`npuarc_IC_WAYS-1:0] Way_set_func; 
input [`npuarc_IC_WAYS_BITS-1:0] way_num;
begin
  Way_set_func = {`npuarc_IC_WAYS{1'b0}};
  Way_set_func[way_num] = 1'b1;
end
endfunction
//spyglass enable_block AutomaticFuncTask-ML


reg way_found;
reg [`npuarc_IC_WAYS_BITS-1:0] way_temp;

always @(*)
begin: way_write_func_PROC



  if (req_lock_r && (!tag_miss)) begin         // (1)  
    way_found = 1'b1;
    way_temp = tag_hit_way_ptr;
  end
  else if (&tag_valid_or_do_not_replace) begin                   // (2,4)
    // All ways are valid or locked.
    // Use Random replacement.
    // This excludes ways that are locked or have a re_read conflict
    way_temp = random_way[`npuarc_IC_WAYS_BITS-1:0];
    way_found = ~tag_lock_all;
  end
  else begin                                 // (3,5)
    //Some ways are invalid; replace the first invalid way that is not locked
    //
    way_found = 1'b1;
    way_temp = first_invld_way;
  end
  way_write_func = {way_found, way_temp};
end

 

reg  [`npuarc_IC_WAY_RANGE] ic_tag_mem_ren_r;
wire [`npuarc_IC_WAY_RANGE] ic_tag_mem_ren_nxt;

assign ic_tag_mem_ren_nxt =
                           tag_mem_cen & {`npuarc_IC_WAYS{!tag_mem_wen}};

always @(posedge clk or posedge rst_a) 
begin: tag_mem_rd_en_reg_PROC
  if (rst_a == 1'b1) begin
    ic_tag_mem_ren_r <= {`npuarc_IC_WAYS{1'b0}};
  end
  else begin 
    ic_tag_mem_ren_r <= ic_tag_mem_ren_nxt;
  end
end

 
assign  ic_tag_ecc_en = ic_tag_mem_ren_r & {`npuarc_IC_WAYS{clk_en}};




endmodule

// leda W389 on

