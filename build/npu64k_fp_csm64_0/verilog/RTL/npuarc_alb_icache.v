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
//   vpp +q +o icache.vpp
//
// ===========================================================================

`include "npuarc_defines.v"
// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: {clk : "edc_clk2" , clk_ibus : "edc_clk"}, rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_icache_ctl_edc_err" }


module npuarc_alb_icache (
  ////////// General input signals ///////////////////////////////////////////
  //

  input                       clk,              // ifetch memory clock
  input                       clk_en,           // enable signal that generates clk
  input                       clk2_en_r,        //2 cycle clock phase disregarding restart in an odd cycle
  input                       clk_ibus,         // ibus clock, is core clock
  input                       rst_a,            // Asynchronous reset

  input                        dbg_cache_rst_disable_r,


  input                       exu_hlt_restart,
  input                       restart,
  input                       bpu_restart,
  input                       ar_user_mode_r,

  output                      hlt_ready,
  output                      mem_busy,
  output                      aux_busy,

  input                       mpd_pc_load,   //to load mispredicted PC
  input [`npuarc_PC_RANGE]           mpd_pc,        //mispredicted PC, for way prediction at restart
  input                       mpd_direction, //1-specifies BTA, 0-specifies fall though.
  input                       mpd_mispred,   //indicates a misprediction

  input      [`npuarc_IC_TRAM_RANGE] ic_tag_dout0,    // Data from tag RAM (per way)
  output [`npuarc_IC_TRAM_RANGE]     ic_tag_din0,     // Data to tag RAM (per way)
  output [`npuarc_IC_TRAM_MASK_RANGE] ic_tag_wem0,    // Address to tag RAM (per way)
  output [`npuarc_IC_IDX_RANGE]      ic_tag_addr0,    // Address to tag RAM (per way)
  output                      ic_tag_cen0,     // CEN to tag RAM (pos logic)
  output                      ic_tag_wen0,     // WEN to tag RAM (pos logic)

  input      [`npuarc_IC_TRAM_RANGE] ic_tag_dout1,    // Data from tag RAM (per way)
  output [`npuarc_IC_TRAM_RANGE]     ic_tag_din1,     // Data to tag RAM (per way)
  output [`npuarc_IC_TRAM_MASK_RANGE] ic_tag_wem1,    // Address to tag RAM (per way)
  output [`npuarc_IC_IDX_RANGE]      ic_tag_addr1,    // Address to tag RAM (per way)
  output                      ic_tag_cen1,     // CEN to tag RAM (pos logic)
  output                      ic_tag_wen1,     // WEN to tag RAM (pos logic)

  input      [`npuarc_IC_TRAM_RANGE] ic_tag_dout2,    // Data from tag RAM (per way)
  output [`npuarc_IC_TRAM_RANGE]     ic_tag_din2,     // Data to tag RAM (per way)
  output [`npuarc_IC_TRAM_MASK_RANGE] ic_tag_wem2,    // Address to tag RAM (per way)
  output [`npuarc_IC_IDX_RANGE]      ic_tag_addr2,    // Address to tag RAM (per way)
  output                      ic_tag_cen2,     // CEN to tag RAM (pos logic)
  output                      ic_tag_wen2,     // WEN to tag RAM (pos logic)

  input      [`npuarc_IC_TRAM_RANGE] ic_tag_dout3,    // Data from tag RAM (per way)
  output [`npuarc_IC_TRAM_RANGE]     ic_tag_din3,     // Data to tag RAM (per way)
  output [`npuarc_IC_TRAM_MASK_RANGE] ic_tag_wem3,    // Address to tag RAM (per way)
  output [`npuarc_IC_IDX_RANGE]      ic_tag_addr3,    // Address to tag RAM (per way)
  output                      ic_tag_cen3,     // CEN to tag RAM (pos logic)
  output                      ic_tag_wen3,     // WEN to tag RAM (pos logic)


  output [`npuarc_IC_BANK_WIDTH-1:0] ic_data_din0,    // Data to data RAM (per bank) 
  output [`npuarc_IC_ADR_RANGE]      ic_data_addr0,   // Address to data RAM (per bank)
  output                      ic_data_cen0,    // CEN to data RAM 
  output                      ic_data_wen0,    // WEN to data RAM
  output [`npuarc_IC_BANK_BYTE_SIZE-1:0] ic_data_wem0,// Write byte mask (per bank)
  input [`npuarc_IC_BANK_WIDTH-1:0]  ic_data_dout0,
  output [`npuarc_IC_BANK_WIDTH-1:0] ic_data_din1,    // Data to data RAM (per bank) 
  output [`npuarc_IC_ADR_RANGE]      ic_data_addr1,   // Address to data RAM (per bank)
  output                      ic_data_cen1,    // CEN to data RAM 
  output                      ic_data_wen1,    // WEN to data RAM
  output [`npuarc_IC_BANK_BYTE_SIZE-1:0] ic_data_wem1,// Write byte mask (per bank)
  input [`npuarc_IC_BANK_WIDTH-1:0]  ic_data_dout1,

  ////////// I-cache interface to the front-end fetch logic ////////////////
  //
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
  input  [`npuarc_PC_RANGE]          fa_pc_nxt0,      // PC of current fetch request
  input  [`npuarc_PC_RANGE]          fa_pc_nxt1,      // PC of current fetch request
// leda NTL_CON13C on
// leda NTL_CON37 on
  // MMU lookup interface / exceptions
  output                      itlb_lkup_valid,
  input                       itlb_stall,
  input                       jrsp_itlb_update,
  output [`npuarc_ADDR_RANGE]        req_vaddr_r,
  input  [`npuarc_PADDR_RANGE]       req_paddr,      // physical address for tag matching/ext mem
  input                       itlb_fail_r,
  input                       itlb_miss_excpn_nxt,
  output                      itlb_miss_excpn_r_r,
  input                       itlb_ecc_err_excpn_nxt,
  output                      itlb_ecc_err_excpn_r_r,
  input                       itlb_ovrlp_excpn_nxt,
  output                      itlb_ovrlp_excpn_r_r,
  input [`npuarc_ITLB_EXEC_PERM_RANGE]                 itlb_exec_perm_nxt,
  output [`npuarc_ITLB_EXEC_PERM_RANGE]                itlb_exec_perm_r_r,

  output                      icache_tag_par_mode_r,

  input                       fa_fetch,         // Request to access I-cache
  input                       fa_is_restart,    //the fetch is from a restart
  input  [`npuarc_IC_BANKS:0]        fa_bank_ctl,      //bit2=1 - bank mis align, bit1:0 fetch bank sel
  input                       fa_way_bank_id,    //it identifies the bank of last fetch, it's used when this fetch is a BTA 
  input                       fa_way_tail,
  input                       fa_vec,           //vector fetch, force to kernal mode on ibus
  input                       fa_seq,           //sequential fetch, tag check is skipped
  input                       fa_way_sec,       //way prediction for secondary branch
  input                       fa_way_req,       //sequential fetch and feedback the right way
  input                       fa_way_force,
  input  [`npuarc_IC_WAYS_BITS-1:0]  fa_way_ptr,
  output                      fa_rdy,

  output [`npuarc_IC_DRAM_RANGE]     fa_data,
  output [`npuarc_IC_BANKS-1:0]      fa_data_vld,
  output                      fa_data_err,
  output [`npuarc_IC_WAYS_BITS-1:0]  fa_data_way,
  input                       fa_data_rdy,

  input                       ecc_ifu_disable,
  output                      ecc_enable,
  output                      ic_tag_ecc_err,
  output                      ic_aux_data_ecc_err,

  output                      ic_aux_data_ecc_sb_err,
  output                      ic_tag_ecc_sb_err,
// `if (`HAS_SAFETY == 1)
  output reg                    fs_ic_tag_bank0_ecc_sb_error_r,
  output reg                    fs_ic_tag_bank0_ecc_db_error_r,
  output reg [`npuarc_IC_TAG_SYNDROME_MSB:0]  fs_ic_tag_bank0_syndrome_r,
  output reg                    fs_ic_tag_bank1_ecc_sb_error_r,
  output reg                    fs_ic_tag_bank1_ecc_db_error_r,
  output reg [`npuarc_IC_TAG_SYNDROME_MSB:0]  fs_ic_tag_bank1_syndrome_r,
  output reg                    fs_ic_tag_bank2_ecc_sb_error_r,
  output reg                    fs_ic_tag_bank2_ecc_db_error_r,
  output reg [`npuarc_IC_TAG_SYNDROME_MSB:0]  fs_ic_tag_bank2_syndrome_r,
  output reg                    fs_ic_tag_bank3_ecc_sb_error_r,
  output reg                    fs_ic_tag_bank3_ecc_db_error_r,
  output reg [`npuarc_IC_TAG_SYNDROME_MSB:0]  fs_ic_tag_bank3_syndrome_r,
// `endif

  output                      ifu_ivic,
  output                      ifu_ivil,
  output                      ifu_icache_miss_r,
  output                      ifu_way_pred_miss_r,
  output                      ifu_icache_hit_r,
  output                      ifu_icache_disabled,
  input                       cycle2_r,
  ////////// Interface to Icache Aux registers /////////////////////////////
  //
  input                       aux_read,         // Aux read operation
  input                       aux_write,        // Aux write operation
  input      [`npuarc_DATA_RANGE]    aux_wdata,        // Aux write data
  input                       aux_ic_ren_r,     // Aux read from IC register 
  input                       aux_ic_wen_r,     // Aux write to IC register
  input  [3:0]                aux_ic_raddr_r,   // Aux read addr from IC register 
  input  [3:0]                aux_ic_waddr_r,   // Aux write addr to IC register
  output [`npuarc_DATA_RANGE]        ic_aux_rdata,     // LR read data
  output                      ic_aux_illegal,   // SR/LR operation is illegal
  output                      ic_aux_k_rd,      // op needs Kernel R perm
  output                      ic_aux_k_wr,      // op needs Kernel W perm
  output                      ic_aux_unimpl,    // LR/SR reg is not present
  output                      ic_aux_serial_sr, // SR must serialize the pipe
  output                      ic_aux_strict_sr, // SR flush pipe 

  ///////////// outputs for way prediction //////////////////////////////
  //
  output [`npuarc_IC_WAYS_BITS-1:0]  way_for_pred,
  output                      way_sec_for_pred,
  output                      way_for_pred_vld,
  output [`npuarc_PC_RANGE]          way_for_pred_pc,

  ///////////// MPU/IFP Address to check ///////////////////////////////
  //
  output [`npuarc_PC_RGN_RANGE]      ifetch_chk_addr,

  ///////////// MPU interface //////////////////////////////////////////
  //
  input                       ifetch_mpu_viol,
  output                      ic_mpu_viol,
  input                       ifetch_unc,
  ///////////// Instr Fetch Protection (IFP) interface ////////////////
  // 
  input                       ifetch_iprot_viol,
  output                      ic_iprot_viol,



  //////////// Interface to the Bus Interface Unit /////////////////////
  //
  output                      ifu_ibus_cmd_valid,
  output                      ifu_ibus_cmd_prot,
  input                       ifu_ibus_cmd_accept,
  output   [`npuarc_PADDR_RANGE]     ifu_ibus_cmd_addr,
  output                      ifu_ibus_cmd_wrap,
  output                      ifu_ibus_cmd_cache,
  output   [3:0]              ifu_ibus_cmd_burst_size,

  input                       ifu_ibus_rd_valid,
  output                      ifu_ibus_rd_accept,
  input    [`npuarc_DOUBLE_RANGE]    ifu_ibus_rd_data,
  input                       ifu_ibus_err_rd
);


wire uncache_mode;
wire [3:0] ic_waylock;
wire reg_req;
wire reg_ack;
wire [7:0] reg_req_mode;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  bit 0 is unused in pc_range
wire [`npuarc_PADDR_RANGE] reg_addr;
// leda NTL_CON13A on
wire [`npuarc_DOUBLE_RANGE] reg_wdata;
wire [`npuarc_DOUBLE_BE_RANGE] reg_wmask; 
wire [`npuarc_IC_BANK_WIDTH-1:0] reg_rdata;
wire reg_rdata_vld;
wire [`npuarc_PADDR_RANGE] reg_tag_rdata;
wire reg_tag_rdata_vld;
wire reg_req_fail;

wire [`npuarc_IC_WAY_RANGE] tag_mem_cen;
wire tag_mem_wen;
wire [`npuarc_IC_IDX_RANGE] tag_mem_addr;
wire [`npuarc_IC_TWORD_RANGE] tag_mem_wdata;
wire [`npuarc_IC_TRAM_RANGE] tag_mem_rdata0;
wire [`npuarc_IC_TRAM_RANGE] tag_mem_rdata1;
wire [`npuarc_IC_TRAM_RANGE] tag_mem_rdata2;
wire [`npuarc_IC_TRAM_RANGE] tag_mem_rdata3;
wire [`npuarc_IC_TRAM_RANGE] aux_tag_mem_rdata;
       
wire [`npuarc_IC_WAY_RANGE] cache_mem_cen;
wire cache_mem_wen;
wire [`npuarc_IC_BYTE_WIDTH-1:0] cache_mem_wem;
wire [`npuarc_IC_BANKS-1:0] cache_mem_bank_sel;
//wire [`IC_DRAM_RANGE] cache_mem_wdata;
wire [`npuarc_IC_LBUF_RANGE] cache_mem_wdata;
wire [`npuarc_IC_DRAM_RANGE] cache_mem_rdata0;
wire [`npuarc_IC_DRAM_RANGE] cache_mem_rdata1;
wire [`npuarc_IC_DRAM_RANGE] cache_mem_rdata2;
wire [`npuarc_IC_DRAM_RANGE] cache_mem_rdata3;
wire [`npuarc_IC_WAY_ADR_RANGE] cache_mem_addr0;
wire [`npuarc_IC_WAY_ADR_RANGE] cache_mem_addr1;

//wire way_miss_pred;

wire [`npuarc_IC_WAYS-1:0] tag_ecc_error;
wire [`npuarc_IC_WAYS-1:0] ic_tag_ecc_en;
wire [`npuarc_IC_WAYS-1:0] tag_ecc_error_int;
wire [`npuarc_IC_WAYS-1:0] tag_ecc_sb_error_int;


//Swapping logic as ibus input is endian insensitive
wire [`npuarc_DOUBLE_RANGE] ifu_ibus_rd_data_int = ifu_ibus_rd_data;

  wire [`npuarc_IC_ALIAS_IDX_RANGE] aux_alias_r;

//////////////////// AUX register interface /////////////////////
//
npuarc_alb_icache_aux u_icache_aux(
  .clk(clk_ibus),
  .clk_en(clk_en),
  .rst_a(rst_a),


  .dbg_cache_rst_disable_r (dbg_cache_rst_disable_r),


  //input
  .aux_read(aux_read),
  .aux_write(aux_write),
  .aux_wen(aux_ic_wen_r),
  .aux_ren(aux_ic_ren_r),
  .aux_waddr(aux_ic_waddr_r),
  .aux_raddr(aux_ic_raddr_r),
  .aux_wdata(aux_wdata),

  //decode and send to icache_ctl
  .uncache_mode(uncache_mode),
  .ic_waylock(ic_waylock),
  .cache_op_req(reg_req),
  .cache_op_ack(reg_ack),
  .cache_op_mode(reg_req_mode),
  .cache_op_addr(reg_addr),
  .aux_alias_r(aux_alias_r),
  .cache_op_wdata(reg_wdata),
  .cache_op_wmask(reg_wmask),
  .cache_op_rdata(reg_rdata),
  .cache_op_rdata_vld(reg_rdata_vld),
  .cache_op_tag_rdata(reg_tag_rdata),
  .cache_op_tag_rdata_vld(reg_tag_rdata_vld),
  .aux_tag_mem_rdata(aux_tag_mem_rdata),
  .cache_op_fail(reg_req_fail),

  .ecc_ifu_disable        (ecc_ifu_disable        ),
  .ic_aux_data_ecc_err    (ic_aux_data_ecc_err    ),
  .ic_aux_data_ecc_sb_err (ic_aux_data_ecc_sb_err ),
  .ifu_ivic(ifu_ivic),
  .ifu_ivil(ifu_ivil),
  //status 
  .aux_busy(aux_busy),
  .ic_aux_rdata(ic_aux_rdata),
  .ic_aux_illegal(ic_aux_illegal),
  .ic_aux_k_rd(ic_aux_k_rd),
  .ic_aux_k_wr(ic_aux_k_wr),
  .ic_aux_unimpl(ic_aux_unimpl),
  .ic_aux_serial_sr(ic_aux_serial_sr),
  .ic_aux_strict_sr(ic_aux_strict_sr)
);

//////////////////// Cache controller /////////////////////
//
npuarc_alb_icache_ctl u_icache_ctl(



  .clk(clk),
  .clk_en(clk_en),
  .clk2_en_r(clk2_en_r),
  .clk_ibus(clk_ibus),
  .rst_a(rst_a), //active high reset
  .exu_hlt_restart (exu_hlt_restart),
  .restart(restart), //from exu until bpu_restart
  .bpu_restart(bpu_restart),
  .ar_user_mode_r(ar_user_mode_r),

  //cache state report
  .hlt_ready(hlt_ready),
  .mem_busy(mem_busy),

  //restart pc for way prediction
  .mpd_pc_load(mpd_pc_load),
  .mpd_pc(mpd_pc),
  .mpd_direction(mpd_direction),
  .mpd_mispred(mpd_mispred),

  //normal access interface
  .fetch_addr0(fa_pc_nxt0),
  .fetch_addr1_offset(fa_pc_nxt1[`npuarc_IC_WRD_RANGE]),
  .itlb_lkup_valid(itlb_lkup_valid),
  .itlb_stall(itlb_stall),
  .jrsp_itlb_update(jrsp_itlb_update),
  .req_vaddr_r(req_vaddr_r),
  .req_paddr(req_paddr),
  .itlb_fail_r(itlb_fail_r),
  .itlb_miss_excpn_nxt(itlb_miss_excpn_nxt),
  .itlb_miss_excpn_r_r(itlb_miss_excpn_r_r),
  .itlb_ecc_err_excpn_nxt(itlb_ecc_err_excpn_nxt),
  .itlb_ecc_err_excpn_r_r(itlb_ecc_err_excpn_r_r),
  .itlb_ovrlp_excpn_nxt(itlb_ovrlp_excpn_nxt),
  .itlb_ovrlp_excpn_r_r(itlb_ovrlp_excpn_r_r),
  .itlb_exec_perm_nxt(itlb_exec_perm_nxt),
  .itlb_exec_perm_r_r(itlb_exec_perm_r_r),
  .icache_tag_par_mode_r(icache_tag_par_mode_r),
  .fetch_req(fa_fetch),
  .fetch_is_restart(fa_is_restart),
  .fetch_bank_ctl(fa_bank_ctl),
  .fetch_vec(fa_vec),
  .fetch_seq(fa_seq),
  .fetch_way_bank_id(fa_way_bank_id),
  .fetch_way_tail(fa_way_tail),
  .fetch_way_sec(fa_way_sec),
  .fetch_way_req(fa_way_req),
  .fetch_way_force(fa_way_force),
  .fetch_way_ptr(fa_way_ptr),
  .fetch_data(fa_data),
  .fetch_data_vld(fa_data_vld),
  .fetch_data_err(fa_data_err),
  .fetch_data_way(fa_data_way),
  .fetch_rdy(fa_rdy),
  .fetch_data_rdy(fa_data_rdy),
  .ecc_enable    (ecc_enable),
  .ifu_icache_miss_r    (ifu_icache_miss_r  ),
  .ifu_way_pred_miss_r  (ifu_way_pred_miss_r),
  .ifu_icache_hit_r     (ifu_icache_hit_r   ),
  .cycle2_r             (cycle2_r           ),

  //register access interface
  .uncache_mode(uncache_mode),
  .ic_waylock(ic_waylock),
  .aux_req(reg_req),
  .aux_ack(reg_ack),
  .aux_bist(1'b0),
  .aux_req_mode(reg_req_mode),
  .aux_addr(reg_addr[`npuarc_PIADDR_RANGE]),
  .aux_alias_r(aux_alias_r),
  .aux_wdata(reg_wdata),
  .aux_wmask(reg_wmask),
  .aux_rdata(reg_rdata),
  .aux_rdata_vld(reg_rdata_vld),
  .aux_tag_rdata(reg_tag_rdata),
  .aux_tag_mem_rdata(aux_tag_mem_rdata),
  .aux_tag_rdata_vld(reg_tag_rdata_vld),
  .aux_req_fail(reg_req_fail),

//  .aux_ic_ctl_on(ic_ctl_cache_inst),

  //tag ram interface
  .tag_mem_cen(tag_mem_cen),
  .tag_mem_wen(tag_mem_wen),
  .tag_mem_addr(tag_mem_addr),
  .tag_mem_wdata(tag_mem_wdata),
  .tag_mem_rdata0(tag_mem_rdata0),
  .tag_mem_rdata1(tag_mem_rdata1),
  .tag_mem_rdata2(tag_mem_rdata2),
  .tag_mem_rdata3(tag_mem_rdata3),

  //cache mem interface
  .cache_mem_cen(cache_mem_cen),
  .cache_mem_wen(cache_mem_wen),
  .cache_mem_wem(cache_mem_wem),
  .cache_mem_bank_sel(cache_mem_bank_sel),
  .cache_mem_wdata(cache_mem_wdata),
  .cache_mem_rdata0(cache_mem_rdata0),
  .cache_mem_rdata1(cache_mem_rdata1),
  .cache_mem_rdata2(cache_mem_rdata2),
  .cache_mem_rdata3(cache_mem_rdata3),

  .tag_ecc_error  (tag_ecc_error),
  .ic_tag_ecc_en  (ic_tag_ecc_en),


  .cache_mem_addr0(cache_mem_addr0),
  .cache_mem_addr1(cache_mem_addr1),

  //outputs for way prediction
  .way_for_pred(way_for_pred),
  .way_sec_for_pred(way_sec_for_pred),
  .way_for_pred_vld(way_for_pred_vld),
  .way_for_pred_pc(way_for_pred_pc),
//  .way_miss_pred(way_miss_pred),

  // MPU/IFP interface
  .ifetch_chk_addr (ifetch_chk_addr),
  .ifetch_mpu_viol (ifetch_mpu_viol),
  .ic_mpu_viol (ic_mpu_viol),
  .ifetch_unc  (ifetch_unc),
  .ifetch_iprot_viol (ifetch_iprot_viol),
  .ic_iprot_viol (ic_iprot_viol),


  //line fill bus interface
  .ifu_ibus_cmd_valid(ifu_ibus_cmd_valid),
  .ifu_ibus_cmd_prot(ifu_ibus_cmd_prot),
  .ifu_ibus_cmd_accept(ifu_ibus_cmd_accept),
  .ifu_ibus_cmd_addr(ifu_ibus_cmd_addr),
  .ifu_ibus_cmd_wrap(ifu_ibus_cmd_wrap),
  .ifu_ibus_cmd_cache(ifu_ibus_cmd_cache),
  .ifu_ibus_cmd_burst_size(ifu_ibus_cmd_burst_size),

  .ifu_ibus_rd_valid(ifu_ibus_rd_valid),
  .ifu_ibus_rd_accept(ifu_ibus_rd_accept),
  .ifu_ibus_rd_data(ifu_ibus_rd_data_int),
  .ifu_ibus_err_rd(ifu_ibus_err_rd)

);

assign ifu_icache_disabled = uncache_mode;

//////////////////// Memory signal handling /////////////////////
//

wire [`npuarc_IC_TAG_ECC_CODE_MSB:0] tag_mem_wdata_ecc;
wire [`npuarc_IC_TAG_ECC_CODE_MSB:0] tag_mem_wdata_ecc_int =
                           tag_mem_wdata_ecc;

// Register the Icache tag memory output 
// Icache memories are accessed on alternate core clock cycles. The data output from the memory used on the second clock after the memory access 
// The register here captures the data on the first clock after the memory access, and makes the data available for use on the second cycle
// The signal used for capturing, clk_en, goes low for 1 cycle after the memory access and is used to capture the data
// No reset needed for this register as this is a data path
//
reg [`npuarc_IC_TRAM_RANGE] ic_tag_dout0_r;
reg [`npuarc_IC_TRAM_RANGE] ic_tag_dout1_r;
reg [`npuarc_IC_TRAM_RANGE] ic_tag_dout2_r;
reg [`npuarc_IC_TRAM_RANGE] ic_tag_dout3_r;
always @(posedge clk_ibus )
begin: ic_tag_dout_reg_PROC
  if (mem_busy & (~clk_en)) begin
// spyglass disable_block Ar_resetcross01 STARC-2.3.4.3
// SMD: unsynchronized reset crossing between flops in data path
// SJ:  Done on purpose, causes no issues, no resets required for these regs
     ic_tag_dout0_r <= ic_tag_dout0;
     ic_tag_dout1_r <= ic_tag_dout1;
     ic_tag_dout2_r <= ic_tag_dout2;
     ic_tag_dout3_r <= ic_tag_dout3;
// spyglass enable_block Ar_resetcross01 STARC-2.3.4.3
  end
end

  assign ic_tag_cen0 = tag_mem_cen[0];
  assign ic_tag_wen0 = tag_mem_wen;
  assign ic_tag_addr0 = tag_mem_addr;
  assign ic_tag_din0 = {tag_mem_wdata_ecc_int,tag_mem_wdata};
  assign ic_tag_wem0 = {{7{!ecc_ifu_disable}},{`npuarc_IC_TWORD_BITS{1'b1}}};
  assign tag_mem_rdata0 = ic_tag_dout0_r;
  assign ic_tag_cen1 = tag_mem_cen[1];
  assign ic_tag_wen1 = tag_mem_wen;
  assign ic_tag_addr1 = tag_mem_addr;
  assign ic_tag_din1 = {tag_mem_wdata_ecc_int,tag_mem_wdata};
  assign ic_tag_wem1 = {{7{!ecc_ifu_disable}},{`npuarc_IC_TWORD_BITS{1'b1}}};
  assign tag_mem_rdata1 = ic_tag_dout1_r;
  assign ic_tag_cen2 = tag_mem_cen[2];
  assign ic_tag_wen2 = tag_mem_wen;
  assign ic_tag_addr2 = tag_mem_addr;
  assign ic_tag_din2 = {tag_mem_wdata_ecc_int,tag_mem_wdata};
  assign ic_tag_wem2 = {{7{!ecc_ifu_disable}},{`npuarc_IC_TWORD_BITS{1'b1}}};
  assign tag_mem_rdata2 = ic_tag_dout2_r;
  assign ic_tag_cen3 = tag_mem_cen[3];
  assign ic_tag_wen3 = tag_mem_wen;
  assign ic_tag_addr3 = tag_mem_addr;
  assign ic_tag_din3 = {tag_mem_wdata_ecc_int,tag_mem_wdata};
  assign ic_tag_wem3 = {{7{!ecc_ifu_disable}},{`npuarc_IC_TWORD_BITS{1'b1}}};
  assign tag_mem_rdata3 = ic_tag_dout3_r;

//may-bank conversion
wire [`npuarc_IC_WAYS_BITS-1:0] way_ptr = Way_enc(cache_mem_cen);
  assign ic_data_cen0 = (|cache_mem_cen) & cache_mem_bank_sel[0];

  assign ic_data_wen0 = cache_mem_wen;
//  assign ic_data_wem0 = cache_mem_wem[`IC_BANK_BYTE_SIZE*(0+1)-1:`IC_BANK_BYTE_SIZE*0]; 

  assign ic_data_addr0 = {way_ptr, cache_mem_addr0};

wire [`npuarc_ECC_IC_BANK_BITS-1:0] cache_mem_wdata_ecc0;

wire [`npuarc_IC_BANK_BYTE_SIZE-1:`npuarc_IC_BANK_BYTE_DSIZE] ic_ecc_par_be0;
wire [`npuarc_IC_BANK_WIDTH-1:`npuarc_IC_BANK_DWIDTH] ic_ecc_par_data0;
assign  ic_ecc_par_be0 = 
                      {cache_mem_wem[4],cache_mem_wem[0]};

// spyglass disable_block W123
assign ic_ecc_par_data0 =
                      cache_mem_wdata_ecc0;
// spyglass enable_block W123

  assign ic_data_din0 = {ic_ecc_par_data0,cache_mem_wdata[`npuarc_IC_BANK_DWIDTH*(0+1)-1:`npuarc_IC_BANK_DWIDTH*0]};

  assign ic_data_wem0 = {(ic_ecc_par_be0 & {2{!ecc_ifu_disable}}),cache_mem_wem[`npuarc_IC_BYTE_WIDTH/2*(0+1)-1:`npuarc_IC_BYTE_WIDTH/2*0]}; 

  assign ic_data_cen1 = (|cache_mem_cen) & cache_mem_bank_sel[1];

  assign ic_data_wen1 = cache_mem_wen;
//  assign ic_data_wem1 = cache_mem_wem[`IC_BANK_BYTE_SIZE*(1+1)-1:`IC_BANK_BYTE_SIZE*1]; 

  assign ic_data_addr1 = {way_ptr, cache_mem_addr1};

wire [`npuarc_ECC_IC_BANK_BITS-1:0] cache_mem_wdata_ecc1;

wire [`npuarc_IC_BANK_BYTE_SIZE-1:`npuarc_IC_BANK_BYTE_DSIZE] ic_ecc_par_be1;
wire [`npuarc_IC_BANK_WIDTH-1:`npuarc_IC_BANK_DWIDTH] ic_ecc_par_data1;
assign  ic_ecc_par_be1 = 
                      {cache_mem_wem[12],cache_mem_wem[8]};

// spyglass disable_block W123
assign ic_ecc_par_data1 =
                      cache_mem_wdata_ecc1;
// spyglass enable_block W123

  assign ic_data_din1 = {ic_ecc_par_data1,cache_mem_wdata[`npuarc_IC_BANK_DWIDTH*(1+1)-1:`npuarc_IC_BANK_DWIDTH*1]};

  assign ic_data_wem1 = {(ic_ecc_par_be1 & {2{!ecc_ifu_disable}}),cache_mem_wem[`npuarc_IC_BYTE_WIDTH/2*(1+1)-1:`npuarc_IC_BYTE_WIDTH/2*1]}; 



// VPOST OFF
// Register the Icache data memory output 
// Icache memories are accessed on alternate core clock cycles. The data output from the memory used on the second clock after the memory access 
// The register here captures the data on the first clock after the memory access, and makes the data available for use on the second cycle
// The signal used for capturing, clk_en, goes low for 1 cycle after the memory access and is used to capture the data
// No reset needed for this register as this is a data path
reg [`npuarc_IC_BANK_WIDTH-1:0] ic_data_dout0_r;
reg [`npuarc_IC_BANK_WIDTH-1:0] ic_data_dout1_r;
always @(posedge clk_ibus )
begin: ic_dout_reg_PROC
  if (mem_busy & (~clk_en)) begin
// spyglass disable_block Ar_resetcross01 STARC-2.3.4.3
// SMD: unsynchronized reset crossing between flops in data path
// SJ:  Done on purpose, causes no issues, no resets required for these regs
     ic_data_dout0_r <= ic_data_dout0;
     ic_data_dout1_r <= ic_data_dout1;
// spyglass enable_block Ar_resetcross01 STARC-2.3.4.3
  end
end
// VPOST ON
assign cache_mem_rdata0 = 
  {ic_data_dout1_r,
   ic_data_dout0_r};
assign cache_mem_rdata1 = 
  {ic_data_dout1_r,
   ic_data_dout0_r};
assign cache_mem_rdata2 = 
  {ic_data_dout1_r,
   ic_data_dout0_r};
assign cache_mem_rdata3 = 
  {ic_data_dout1_r,
   ic_data_dout0_r};

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
  for (i=0; i<`npuarc_IC_WAYS; i=i+1) begin
    if (vld_in[i]) j = i;
  end
  way_enc_j = $unsigned(j);
  Way_enc = way_enc_j[`npuarc_IC_WAYS_BITS-1:0];
end
endfunction
//spyglass enable_block AutomaticFuncTask-ML


///////////////////////////////////////////////////////////////////////////////////////
// ECC Coding for the data to be written to the Cache Memory 
///////////////////////////////////////////////////////////////////////////////////////




 


wire [`npuarc_ECC_IC_BANK_BITS/2-1:0]              cache_mem_wdata_ecc00;

   npuarc_alb_ecc_gen32  u_alb_ecc_gen32_00(
                     .data              (cache_mem_wdata[31:0]),     // Data in
                     .ecc_code          (cache_mem_wdata_ecc00)      // ECC code out
   );


wire [`npuarc_ECC_IC_BANK_BITS/2-1:0]              cache_mem_wdata_ecc01;

   npuarc_alb_ecc_gen32  u_alb_ecc_gen32_01(
                     .data              (cache_mem_wdata[63:32]),     // Data in
                     .ecc_code          (cache_mem_wdata_ecc01)      // ECC code out
   );


wire [`npuarc_ECC_IC_BANK_BITS/2-1:0]              cache_mem_wdata_ecc10;

   npuarc_alb_ecc_gen32  u_alb_ecc_gen32_10(
                     .data              (cache_mem_wdata[95:64]),     // Data in
                     .ecc_code          (cache_mem_wdata_ecc10)      // ECC code out
   );


wire [`npuarc_ECC_IC_BANK_BITS/2-1:0]              cache_mem_wdata_ecc11;

   npuarc_alb_ecc_gen32  u_alb_ecc_gen32_11(
                     .data              (cache_mem_wdata[127:96]),     // Data in
                     .ecc_code          (cache_mem_wdata_ecc11)      // ECC code out
   );

   assign cache_mem_wdata_ecc0 = {
                                   cache_mem_wdata_ecc01,
                                   cache_mem_wdata_ecc00};
   assign cache_mem_wdata_ecc1 = {
                                   cache_mem_wdata_ecc11,
                                   cache_mem_wdata_ecc10};






// ECC code generation for tag memory
npuarc_ic_tag_ecc_encoder u0tag_alb_ecc_gen32 (
  .data_in        (tag_mem_wdata),
  .ecc            (tag_mem_wdata_ecc)
);

// ECC error detection for Tag Memory
wire        ic_tag_ecc_err0;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ: Out put from ECC module
wire        ic_tag_sb_ecc_err0;
wire        ic_tag_db_ecc_err0;
wire        ic_tag_double_ecc_err0;
wire        ic_tag_unknown_ecc_err0;


wire [`npuarc_IC_TAG_SYNDROME_MSB:0] ic_tag_syndrome0;

wire [`npuarc_IC_TWORD_RANGE] ic_tag_data_out_unused0;
wire [`npuarc_IC_TAG_ECC_CODE_MSB:0] ic_tag_ecc_out_unused0;

assign ic_tag_db_ecc_err0 = ic_tag_double_ecc_err0
                           | ic_tag_unknown_ecc_err0
						   ;
assign ic_tag_ecc_err0 = ic_tag_db_ecc_err0 | ic_tag_sb_ecc_err0;
// leda NTL_CON13A on


npuarc_ic_tag_ecc_decoder u0tag_alb_ecc_decoder (
  .enable                     (1'b1),
  .data_in                    (tag_mem_rdata0[`npuarc_IC_TWORD_RANGE]),
  .ecc_in                     (tag_mem_rdata0[`npuarc_IC_TRAM_MSB:`npuarc_IC_TRAM_MSB-`npuarc_IC_TAG_ECC_CODE_MSB]),

  .syndrome_out               (ic_tag_syndrome0),
  .single_err                 (ic_tag_sb_ecc_err0),
  .double_err                 (ic_tag_double_ecc_err0),
  .unknown_err                (ic_tag_unknown_ecc_err0),
  .ecc_out                    (ic_tag_ecc_out_unused0),
  .data_out                   (ic_tag_data_out_unused0)
);
wire        ic_tag_ecc_err1;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ: Out put from ECC module
wire        ic_tag_sb_ecc_err1;
wire        ic_tag_db_ecc_err1;
wire        ic_tag_double_ecc_err1;
wire        ic_tag_unknown_ecc_err1;


wire [`npuarc_IC_TAG_SYNDROME_MSB:0] ic_tag_syndrome1;

wire [`npuarc_IC_TWORD_RANGE] ic_tag_data_out_unused1;
wire [`npuarc_IC_TAG_ECC_CODE_MSB:0] ic_tag_ecc_out_unused1;

assign ic_tag_db_ecc_err1 = ic_tag_double_ecc_err1
                           | ic_tag_unknown_ecc_err1
						   ;
assign ic_tag_ecc_err1 = ic_tag_db_ecc_err1 | ic_tag_sb_ecc_err1;
// leda NTL_CON13A on


npuarc_ic_tag_ecc_decoder u1tag_alb_ecc_decoder (
  .enable                     (1'b1),
  .data_in                    (tag_mem_rdata1[`npuarc_IC_TWORD_RANGE]),
  .ecc_in                     (tag_mem_rdata1[`npuarc_IC_TRAM_MSB:`npuarc_IC_TRAM_MSB-`npuarc_IC_TAG_ECC_CODE_MSB]),

  .syndrome_out               (ic_tag_syndrome1),
  .single_err                 (ic_tag_sb_ecc_err1),
  .double_err                 (ic_tag_double_ecc_err1),
  .unknown_err                (ic_tag_unknown_ecc_err1),
  .ecc_out                    (ic_tag_ecc_out_unused1),
  .data_out                   (ic_tag_data_out_unused1)
);
wire        ic_tag_ecc_err2;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ: Out put from ECC module
wire        ic_tag_sb_ecc_err2;
wire        ic_tag_db_ecc_err2;
wire        ic_tag_double_ecc_err2;
wire        ic_tag_unknown_ecc_err2;


wire [`npuarc_IC_TAG_SYNDROME_MSB:0] ic_tag_syndrome2;

wire [`npuarc_IC_TWORD_RANGE] ic_tag_data_out_unused2;
wire [`npuarc_IC_TAG_ECC_CODE_MSB:0] ic_tag_ecc_out_unused2;

assign ic_tag_db_ecc_err2 = ic_tag_double_ecc_err2
                           | ic_tag_unknown_ecc_err2
						   ;
assign ic_tag_ecc_err2 = ic_tag_db_ecc_err2 | ic_tag_sb_ecc_err2;
// leda NTL_CON13A on


npuarc_ic_tag_ecc_decoder u2tag_alb_ecc_decoder (
  .enable                     (1'b1),
  .data_in                    (tag_mem_rdata2[`npuarc_IC_TWORD_RANGE]),
  .ecc_in                     (tag_mem_rdata2[`npuarc_IC_TRAM_MSB:`npuarc_IC_TRAM_MSB-`npuarc_IC_TAG_ECC_CODE_MSB]),

  .syndrome_out               (ic_tag_syndrome2),
  .single_err                 (ic_tag_sb_ecc_err2),
  .double_err                 (ic_tag_double_ecc_err2),
  .unknown_err                (ic_tag_unknown_ecc_err2),
  .ecc_out                    (ic_tag_ecc_out_unused2),
  .data_out                   (ic_tag_data_out_unused2)
);
wire        ic_tag_ecc_err3;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ: Out put from ECC module
wire        ic_tag_sb_ecc_err3;
wire        ic_tag_db_ecc_err3;
wire        ic_tag_double_ecc_err3;
wire        ic_tag_unknown_ecc_err3;


wire [`npuarc_IC_TAG_SYNDROME_MSB:0] ic_tag_syndrome3;

wire [`npuarc_IC_TWORD_RANGE] ic_tag_data_out_unused3;
wire [`npuarc_IC_TAG_ECC_CODE_MSB:0] ic_tag_ecc_out_unused3;

assign ic_tag_db_ecc_err3 = ic_tag_double_ecc_err3
                           | ic_tag_unknown_ecc_err3
						   ;
assign ic_tag_ecc_err3 = ic_tag_db_ecc_err3 | ic_tag_sb_ecc_err3;
// leda NTL_CON13A on


npuarc_ic_tag_ecc_decoder u3tag_alb_ecc_decoder (
  .enable                     (1'b1),
  .data_in                    (tag_mem_rdata3[`npuarc_IC_TWORD_RANGE]),
  .ecc_in                     (tag_mem_rdata3[`npuarc_IC_TRAM_MSB:`npuarc_IC_TRAM_MSB-`npuarc_IC_TAG_ECC_CODE_MSB]),

  .syndrome_out               (ic_tag_syndrome3),
  .single_err                 (ic_tag_sb_ecc_err3),
  .double_err                 (ic_tag_double_ecc_err3),
  .unknown_err                (ic_tag_unknown_ecc_err3),
  .ecc_out                    (ic_tag_ecc_out_unused3),
  .data_out                   (ic_tag_data_out_unused3)
);


// Generate error vector
assign tag_ecc_error[0] = ic_tag_ecc_err0 & (!ecc_ifu_disable);
assign tag_ecc_error_int[0] = ic_tag_db_ecc_err0 & ic_tag_ecc_en[0];
assign tag_ecc_sb_error_int[0] = ic_tag_sb_ecc_err0 & ic_tag_ecc_en[0];
assign tag_ecc_error[1] = ic_tag_ecc_err1 & (!ecc_ifu_disable);
assign tag_ecc_error_int[1] = ic_tag_db_ecc_err1 & ic_tag_ecc_en[1];
assign tag_ecc_sb_error_int[1] = ic_tag_sb_ecc_err1 & ic_tag_ecc_en[1];
assign tag_ecc_error[2] = ic_tag_ecc_err2 & (!ecc_ifu_disable);
assign tag_ecc_error_int[2] = ic_tag_db_ecc_err2 & ic_tag_ecc_en[2];
assign tag_ecc_sb_error_int[2] = ic_tag_sb_ecc_err2 & ic_tag_ecc_en[2];
assign tag_ecc_error[3] = ic_tag_ecc_err3 & (!ecc_ifu_disable);
assign tag_ecc_error_int[3] = ic_tag_db_ecc_err3 & ic_tag_ecc_en[3];
assign tag_ecc_sb_error_int[3] = ic_tag_sb_ecc_err3 & ic_tag_ecc_en[3];
assign ic_tag_ecc_err = |tag_ecc_error_int & (!ecc_ifu_disable);

assign ic_tag_ecc_sb_err = |tag_ecc_sb_error_int & (!ecc_ifu_disable);

wire [`npuarc_IC_WAYS-1:0] ic_tag_sb_ecc_error;
wire [`npuarc_IC_WAYS-1:0] ic_tag_db_ecc_error;

wire                ic_tag_ecc_valid;

assign ic_tag_sb_ecc_error[0] = ic_tag_sb_ecc_err0 & ic_tag_ecc_en[0] & (!ecc_ifu_disable);
assign ic_tag_sb_ecc_error[1] = ic_tag_sb_ecc_err1 & ic_tag_ecc_en[1] & (!ecc_ifu_disable);
assign ic_tag_sb_ecc_error[2] = ic_tag_sb_ecc_err2 & ic_tag_ecc_en[2] & (!ecc_ifu_disable);
assign ic_tag_sb_ecc_error[3] = ic_tag_sb_ecc_err3 & ic_tag_ecc_en[3] & (!ecc_ifu_disable);

assign ic_tag_db_ecc_error[0] = ic_tag_db_ecc_err0 & ic_tag_ecc_en[0] & (!ecc_ifu_disable);
assign ic_tag_db_ecc_error[1] = ic_tag_db_ecc_err1 & ic_tag_ecc_en[1] & (!ecc_ifu_disable);
assign ic_tag_db_ecc_error[2] = ic_tag_db_ecc_err2 & ic_tag_ecc_en[2] & (!ecc_ifu_disable);
assign ic_tag_db_ecc_error[3] = ic_tag_db_ecc_err3 & ic_tag_ecc_en[3] & (!ecc_ifu_disable);

assign ic_tag_ecc_valid = (|ic_tag_ecc_en);

// Register SBE signal

always @(posedge clk or posedge rst_a)
begin : ic_tag_sb_ecc_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_ic_tag_bank0_ecc_sb_error_r <= 1'b0;
    fs_ic_tag_bank1_ecc_sb_error_r <= 1'b0;
    fs_ic_tag_bank2_ecc_sb_error_r <= 1'b0;
    fs_ic_tag_bank3_ecc_sb_error_r <= 1'b0;
  end
  else
  begin
    fs_ic_tag_bank0_ecc_sb_error_r <= ic_tag_sb_ecc_error[0];
    fs_ic_tag_bank1_ecc_sb_error_r <= ic_tag_sb_ecc_error[1];
    fs_ic_tag_bank2_ecc_sb_error_r <= ic_tag_sb_ecc_error[2];
    fs_ic_tag_bank3_ecc_sb_error_r <= ic_tag_sb_ecc_error[3];
  end
end

// Register DBE signal

always @(posedge clk or posedge rst_a)
begin : ic_tag_db_ecc_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_ic_tag_bank0_ecc_db_error_r <= 1'b0;
    fs_ic_tag_bank1_ecc_db_error_r <= 1'b0;
    fs_ic_tag_bank2_ecc_db_error_r <= 1'b0;
    fs_ic_tag_bank3_ecc_db_error_r <= 1'b0;
  end
  else
  begin
    fs_ic_tag_bank0_ecc_db_error_r <= ic_tag_db_ecc_error[0];
    fs_ic_tag_bank1_ecc_db_error_r <= ic_tag_db_ecc_error[1];
    fs_ic_tag_bank2_ecc_db_error_r <= ic_tag_db_ecc_error[2];
    fs_ic_tag_bank3_ecc_db_error_r <= ic_tag_db_ecc_error[3];
  end
end


// Register Syndrome

always @(posedge clk or posedge rst_a)
begin : ic_tag_syndrome_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_ic_tag_bank0_syndrome_r <= {`npuarc_IC_TAG_SYNDROME_MSB+1{1'b0}};
    fs_ic_tag_bank1_syndrome_r <= {`npuarc_IC_TAG_SYNDROME_MSB+1{1'b0}};
    fs_ic_tag_bank2_syndrome_r <= {`npuarc_IC_TAG_SYNDROME_MSB+1{1'b0}};
    fs_ic_tag_bank3_syndrome_r <= {`npuarc_IC_TAG_SYNDROME_MSB+1{1'b0}};
  end
  else if (ic_tag_ecc_valid)
  begin
    fs_ic_tag_bank0_syndrome_r <= ic_tag_syndrome0;
    fs_ic_tag_bank1_syndrome_r <= ic_tag_syndrome1;
    fs_ic_tag_bank2_syndrome_r <= ic_tag_syndrome2;
    fs_ic_tag_bank3_syndrome_r <= ic_tag_syndrome3;
  end
end




endmodule
