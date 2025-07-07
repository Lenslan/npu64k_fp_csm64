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
//  ###                                     #
// #   #                              #     #
// #                                        #
// #       ####   # # ##   # # ##    ##    ####
// #      #    #  ## #  #  ## #  #    #     #
// #      #    #  #  #  #  #  #  #    #     #
// #      #    #  #  #  #  #  #  #    #     #
// #   #  #    #  #  #  #  #  #  #    #     #  #
//  ###    ####   #  #  #  #  #  #  #####    ##
//
// ===========================================================================
//
// @f:commit
//
// Description:
// @p
//  This module implements the Commit stage of the Albacore pipeline,
//  and forms the third stage of the Execute Pipeline.
//  It follows the |result| stage and precedes the |writeback| stage.
//  There main function of this stage of the pipeline is to determine whether
//  the commit-stage instruction will actually commit its results, and to
//  select the result data between already completed 2-cycle instructions
//  and 3-cycle instructions that yield a result in this pipeline stage.
// @e
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//
`include "npuarc_ucode_const.v"

// Set simulation timescale
//
`include "const.def"

/// determine if EIA extensions have 64-bit result at commit or post-commit


module npuarc_alb_commit (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                           clk,                // global clock
  input                           rst_a,              // asynchronous reset
  input                           wa_restart_r,       // CA stage gets killed
  input                           wa_restart_kill_r,  // 
  input                           holdup_excpn_r,  // 
  input                           hlt_restart_r,
  input      [1:0]                dc4_dtlb_miss_r,
  output reg                      wa_jtlb_lookup_start_r,
  output                          wa_jtlb_cancel,

  ////////// Control signals to/from IFU unit //////////////////////////////
  //

  ////////// Control signals to/from Debug unit //////////////////////////////
  //
  input                           db_active,          // Debug inst in pipe
  input                           db_active_r,        // Debug unit is active

  output                          ca_cmt_dbg_evt /* verilator public_flat */,     // Debug Insn. Commits
  output                          ca_finish_sgl_step,
  output                          ca_cmt_norm_evt,    // Commit NORM insn.
  output                          ca_cmt_uop_evt,     // Commti UOP insn.
  output                          ca_cmt_brk_evt,     // Commit BRK insn.
  output                          ca_cmt_isi_evt,     // Step-Instruction
  output reg                      ca_uop_active_set,

  input                           aps_halt,           // Halt due to AP match
  input                           aps_break,          // Break due to AP match
  output                          ca_sr_stall_rtie,   //

  ////////// Global Machine Reset state //////////////////////////////////////
  //
  output reg                      gb_sys_reset_done_r,// Reset process has complt.

  ////////// Machine Architectural state /////////////////////////////////////
  //
  input      [`npuarc_PC_RANGE]          ar_pc_r,            // AUX_PC
  input      [`npuarc_DATA_RANGE]        ar_aux_status32_r,  // STATUS32
  input                           ar_aux_user_mode_r, // arch. user mode
  input      [`npuarc_DATA_RANGE]        ar_aux_erstatus_r,  // ERSTATUS
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_DATA_RANGE]        ar_aux_bta_r,       // BTA
  input      [`npuarc_DATA_RANGE]        ar_aux_lp_start_r,  // LP_START
  input      [`npuarc_DATA_RANGE]        ar_aux_debug_r,     // DEBUG
// leda NTL_CON13C on

  input                           ar_tags_empty_r,    // retire queue is empty
 
  input                           wa_lock_flag_r,     // LF bit, for SCOND

  ////////// Input from Exec3-stage //////////////////////////////////////////
  //
  input                           ca_flag_wr_nxt,     //
  input      [`npuarc_DATA_RANGE]        ca_src0_nxt,        //
  input      [`npuarc_DATA_RANGE]        ca_src1_nxt,        //
  input      [`npuarc_DATA_RANGE]        ca_res_nxt,         //
  input      [`npuarc_PC_RANGE]          ca_target_nxt,      //
  input      [`npuarc_ADDR_RANGE]        x3_mem_addr_r,      //
  input                           x3_src0_pass,       //
  input                           x3_src1_pass,       //
  input                           x3_res_pass,        //
  input                           x3_target_pass,     //
  input                           x3_addr_pass,       //
  input                           x3_add_op_pass,     //
  input                           x3_alu_code_pass,   //

  input      [`npuarc_PC_INC_RANGE]      ca_pc_inc_nxt,      // Next PC increment
  input      [`npuarc_ZNCV_RANGE]        ca_zncv_nxt,        //
  input  [`npuarc_CA_CODE_WIDTH-1:0]     ca_code_nxt,        //

  input      [`npuarc_CA_P0_RANGE]       ca_p0_nxt,          //
  input      [`npuarc_CA_P1_RANGE]       ca_p1_nxt,          //
  input      [`npuarc_CA_P2_RANGE]       ca_p2_nxt,          //
  input      [`npuarc_CA_P3_RANGE]       ca_p3_nxt,          //
  input                           ca_cin_nxt,         //

  ////////// Dependency Pipeline Interface ///////////////////////////////////
  //
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  singal from dep_pipe. potential used
  input                           ca_pass_no_iprot,
// leda NTL_CON13C on  
// leda NTL_CON37 on
  input                           ca_pass,            //

  input                           ca_enable,          //
  input                           ca_stall,           //
  input                           ca_valid_r,         //
  input                           ca_done_r,          //

  input                           x3_pass,            //

  output reg                      ca_valid_nxt,       //
  output reg                      ca_wa1_conflict,    //
  output reg                      commit_inst,        //
  output                          ca_q_cond,          //


  output                          ca_with_carry_r,    //
  output                          ca_dest_cr_is_ext_r,// to eia dep logic
  input                           eia_ext_cond,       //
  input                           ca_eia_res_valid,   //
  input      [`npuarc_DATA_RANGE]        ca_eia_res_data,    //
  input      [`npuarc_DATA_RANGE]        ca_eia_res_data_hi, //
  input      [`npuarc_ZNCV_RANGE]        ca_eia_res_flags,   // 
  output                          ca_writes_acc_r,    //
  output                          ca_acc_wenb_r,      //
  output                          ca_locked_r,        //
  output reg                      ca_wlfc_op,         //
  output     [4:0]                ca_q_field_r,       //

  ////////// Graduation Interface ////////////////////////////////////////////
  //
  input                           ca_grad_req,        // 
  ////////// Retirement Interfaces ///////////////////////////////////////////
  //
  input                           dp_retire_rf_wenb,  //
  input      [`npuarc_GRAD_ADDR_RANGE]   dp_retire_rf_wa,    // 
  input      [`npuarc_ZNCV_RANGE]        dp_retire_zncv,     //
  input                           ar_zncv_upt_r,      // ZNCV update pending
  input                           dp_retire_rf_64,    // 
  input                           dp_retire_writes_acc, //
  input                           dmp_retire_req,     //
  input      [`npuarc_GRAD_TAG_RANGE]    dmp_retire_tag,     // 
  input                           dmp_scond_zflag,    // SCOND status result
  input                           dp_retire_scond,    // SCOND is retiring
  output reg                      dmp_retire_ack,     // 
  
  input                           div_retire_req,     // 
  input      [`npuarc_GRAD_TAG_RANGE]    div_retire_tag,     // 
  input      [`npuarc_DATA_RANGE]        div_rf_wdata_lo,    // 
  input                           div_retire_ovfl,    //
  input                           div_retire_sign,    //
  input                           div_retire_zero,    //
  output reg                      div_retire_ack,     // 



  input                           eia_disable_w0,
  input                           eia_retire_req,
  input      [`npuarc_GRAD_TAG_RANGE]    eia_retire_tag, 
  input      [`npuarc_DATA_RANGE]        eia_rf_wdata_lo,
  input      [`npuarc_ZNCV_RANGE]        eia_retire_flags,
  output reg                      eia_retire_ack, 
  output reg                      ca_retire_req,      // retirement request
  output reg [`npuarc_GRAD_TAG_RANGE]    ca_retire_tag,      // retirement tag
  output reg                      ca_retire_ack,      // retirement acknowledge
  
  ////////// Accumulator interface to Writeback stage ////////////////////////
  //

  input      [`npuarc_DATA_RANGE]        byp_acc_hi,         // up-to-date ACCH

  output     [`npuarc_DATA_RANGE]        ca_acch_res,        // CA-stage ACCH result   

  ////////// Forwarding/Bypass Interface /////////////////////////////////////
  //
  input                           fwd_ca_r0_wa_w0_lo, // 
  input                           fwd_ca_r0_wa_w1_lo, // 
  input                           fwd_ca_r1_wa_w0_lo, // 
  input                           fwd_ca_r1_wa_w1_lo, // 
  input                           fwd_ca_r0_wa_w0_hi, // 
  input                           fwd_ca_r1_wa_w0_hi, // 
  input                           fwd_ca_r0_wa_w1_hi, //
  input                           fwd_ca_r1_wa_w1_hi, //
  input                           fwd_ca_r1h_wa_w0_lo,
  input                           fwd_ca_r1h_wa_w1_lo,
  input                           fwd_ca_r1h_wa_w0_hi,
  input                           fwd_ca_r1h_wa_w1_hi,
  //
  input      [`npuarc_DATA_RANGE]        wa_rf_wdata0_lo_r,  //
  input      [`npuarc_DATA_RANGE]        wa_rf_wdata1_lo_r,  //
  input      [`npuarc_DATA_RANGE]        wa_rf_wdata0_hi_r,  //
  input      [`npuarc_DATA_RANGE]        wa_rf_wdata1_hi_r,  //
  input                           wa_cmt_norm_evt_r,  // Post-Commit of Insn.

  ////////// Inputs from Prediction Pipeline /////////////////////////////////
  //
  input                           ca_fragged_r,       // CA insn was fragged
  input                           ca_error_branch_r,
  input [`npuarc_BR_TYPE_RANGE]          ca_br_type_r,  // actual branch type at CA

  input                           dc4_replay,
// spyglass disable_block  W240
  input                           dc4_excpn,          //
  input [`npuarc_DMP_EXCPN_RANGE]        dc4_excpn_type,     //
// spyglass enable_block  W240

  ////////// Inputs from the ZOL pipeline ////////////////////////////////////
  //
  input                           ca_zol_lp_jmp,      // ZOL loop-back at CA
  
  ////////// Inputs from the Divide unit /////////////////////////////////////
  //

  ////////// Aux. Interface //////////////////////////////////////////////////
  //
  input      [`npuarc_DATA_RANGE]        aux_ca_lr_data,     //
  input                           aux_ca_serial_sr,   //
  input                           aux_ca_strict_sr,   //

  ////////// AUX. Interface to SR ////////////////////////////////////////////
  //
  input      [`npuarc_DATA_RANGE]        wa_sr_data_r,       // WA AUX. wdata
  input                           wa_status32_wen,    // WA AUX. writes STAT32
  input                           wa_debug_wen,       // WA AUX. debug
  input                           wa_pc_wen,          // Debug SR to PC
  output                          ca_in_kflag,        // 

  ////////// RTC Interface       ////////////////////////////////////////////
  //

  output                          rtc_na,             // RTC non-atomic

  ////////// DMP Data Interface //////////////////////////////////////////////
  //
  input      [`npuarc_DATA_RANGE]        dmp_dc4_rf_wdata_lo,//
  input      [`npuarc_DATA_RANGE]        dmp_dc4_rf_wdata_hi,//

  output reg [`npuarc_DATA_RANGE]        dc4_write_data_lo,  //
  output reg [`npuarc_DATA_RANGE]        dc4_write_data_hi,  //

  ////////// Multiply Pipe (MP4) Interface ///////////////////////////////////
  //
  input      [`npuarc_DATA_RANGE]        mp4_s_hi_r,         //
  input      [`npuarc_DATA_RANGE]        mp4_c_hi_r,         //
  input                           mp4_s_65_r,         //
  input                           mp4_c_65_r,         //
  output reg [`npuarc_DATA_RANGE]        ca_src0_r,          //
  output reg [`npuarc_DATA_RANGE]        ca_src1_r,          //

  ////////// Forwarding to Upstream stages ///////////////////////////////////
  //
  output reg [`npuarc_DATA_RANGE]        ca_byp_data0_lo,    //
  output reg [`npuarc_DATA_RANGE]        ca_byp_data1_lo,    //
  output reg [`npuarc_DATA_RANGE]        ca_byp_data0_hi,    //
  output reg [`npuarc_DATA_RANGE]        ca_byp_data1_hi,    //

  ///////////// Output for PCT ///////////////////////////////////////////////
  //
  output reg                      do_aux_replay_r, 
  output                          ca_lp_lpcc_evt,
  ////////// General outputs to the pipeline /////////////////////////////////
  //
  output reg [`npuarc_ADDR_RANGE]        ca_mem_addr_r,      //
  input      [`npuarc_PADDR_RANGE]       ca_phys_addr_r,     //
  output                          ca_fast_op_r,       //
  output                          ca_load_r,          //
  output                          ca_store_r,         //
  output                          ca_uop_inst_r,      //
  output reg [1:0]                ca_size_r,          //
  output                          ca_sex_r,           //
  output                          ca_cache_byp_r,     //
  output                          ca_pref,            // PREFETCH into L1
  output                          ca_pref_l2,         // PREFETCH into L2
  output                          ca_prefw,           // PREFETCHW
  output                          ca_pre_alloc,       // PREALLOC
  output     [`npuarc_ZNCV_RANGE]        ca_zncv_wen_r,      //
  output                          ca_dslot_r,         //
  output                          ca_jump_r,          // Insn. is Jump
  output                          ca_bcc_r,           // 
  output                          ca_brcc_bbit_r,     // 
  output                          ca_lr_op_r,         //
  output                          ca_sr_op_r,         //
  output                          ca_aux_cond,        //
  output reg                      ca_in_deslot,       // CA inst in DE/ES slot
  output                          ca_ei_op_r,         //
  output                          cmt_ei_evt,         // commit EI event
  output                          ca_in_eslot_r,
  output                          ca_btab_op_r,       //
  output                          ca_dmb_op_r,        // DMB insn at CA
  output     [2:0]                ca_dmb_type_r,      // DMB u3 operand at CA
  output reg                      ca_br_evt,

  output reg                      commit_normal_evt,

  output reg                      ca_br_or_jmp_all,
  output reg                      ca_indir_br,
  output reg                      ca_cmt_brk_inst,    // Commit Break inst
  output reg                      ca_cond_inst,       // inst is conditional   
  output reg                      ca_cond_met,        // condition met
  output                          rtt_dmp_retire,     // DMP retire rpt for Trace
  output                          rtt_dmp_null_ret,   // DMP null retire rpt for Trace
  output                          rtt_ca_pref,        // load with null dest for trace
  input                           dmp_retire_is_load, // DMP retire is Load
  output                          rtt_ca_scond,       // SCOND at CA for RTT
  output                          ca_trap_op_r,       // Insn. is TRAP
  output                          ca_rtie_op_r,       // Insn. is RTIE
   output                          ca_enter_op,        // Insn. is ENTER

  output                          ca_has_limm_r,      // Insn. has limm
  output                          ca_is_16bit,        // Insn. is 16 bit
  output reg                      ca_br_jmp_op,       // Insn. is BL, BLcc, BL_S, JL, JL_S, JLcc
  output reg                      ca_uop_active_r,    // UOP seq. is active
  output reg                      ca_uop_active_nxt,  // UOP seq. is active
  output reg                      ca_uop_predictable_r, // UOP seq. is predicted
  output reg                      ca_uop_enter_r,     // UOP seq. is ENTER_S
  output reg                      ca_uop_inprol_r,    // UOP seq. is prol
  output                          ca_uop_commit_r,    // Insn. is uop term.
  output                          ca_byte_size_r,     //
  output reg                      ca_cond,            // CA Insn. shall cmt.
  output reg [`npuarc_PC_RANGE]          ca_seq_pc_nxt,      // next seq. PC at CA
  output                          ca_aux_s32_stall,   // Status32 update
  output                          ca_loop_evt,        // LP instruction commits
  output reg                      ca_sleep_evt,       // any sleep inst commits
  output reg                      ca_wevt_evt,        // WEVT inst commits
  output reg                      ca_wlfc_evt,        // WLFC inst commits
  output                          ca_kflag_op,        // CA insn is KFLAG
  output                          ca_brk_op_r,        // CA Break inst
  output                          ca_div_op_r,        // CA insn is DIV or REM
  output                          ca_predicate_r,     // CA-stage predicate
  output reg   [`npuarc_PC_RANGE]        ca_target_r,        // CA-Target
  output                          ca_mpy_op_r,        // MPY operation at CA
  output                          ca_vector_op_r,     // SIMD operation at CA
  output                          ca_macu_r,          // MACU-type op at CA
  output                          sel_byp_acc,        // use WA/RF ACC value
  output reg   [`npuarc_GRAD_ADDR_RANGE] ca_grad_rf_wa1,     // graduation reg addr
  output reg   [`npuarc_ZNCV_RANGE]      ca_retire_flags,    // selected retirement flags
  output                          ca_iprot_viol_r,    // ifetch prot viol at CA

  ////////// Outputs to the ZOL pipeline /////////////////////////////////////
  //
  output                          ca_wa0_lpc_r,       //
  output                          ca_loop_op_r,       //
  output reg                      ca_branch_evt,      // branch, jump at CA
  
  ////////// Final branch resolution information to prediction pipe //////////
  //
  output reg                      ca_br_direction,    // branch direction
  output     [`npuarc_PC_RANGE]          ca_br_target,       // target or fall-thru
  output     [`npuarc_PC_RANGE]          ca_lp_end_nxt,      // next LP_END from LPcc
  output reg [`npuarc_PC_RANGE]          ca_br_fall_thru,    // fall-thru
  output reg                      ca_tail_pc_3,       // last hword of br/dslot
  input                           ca_br_taken,        // actual branch outcome
  output                          ca_leave_op_r,      // CA inst is LEAVE_S
  output reg                      ca_uop_inst,        // uop inst at CA
  output reg                      ca_br_or_jmp,        // CA inst is br or jmp
  output reg                      ca_iprot_replay,

  ////////// Exception management interface //////////////////////////////////
  //
  input                           excpn_restart,      // Excpn. & int restart req
  input      [`npuarc_PC_RANGE]          excpn_restart_pc,   // Excpn. & int restart PC
  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  Not all bits used 
  input      [`npuarc_INTEVT_RANGE]      excpn_evts,         // Excpn. events
  // leda NTL_CON37 on
  input                           ct_excpn_trap_r,    // Excpn. PT trap

  ////////// Interrupt management interface //////////////////////////////////
  //
  input      [`npuarc_INTEVT_RANGE]      int_evts,           // Interrupt events

  output                          rtt_leave_uop_cmt,  //leave uop has committed
  output reg                      int_load_active,    //context restore period


  ////////// Halt Management Interface ///////////////////////////////////////
  //
  input                           hlt_do_halt,        // Req. Halt
  input                           hlt_do_unhalt,      // Req. Unhalt
  input                           ca_triple_fault_set,// Triple fault event
  output reg                      ct_replay,          // Req. insn replay

  ////////// Outputs to the Writeback stage //////////////////////////////////
  //
  output     [`npuarc_RGF_ADDR_RANGE]    ca_rf_ra0_r,        // reg-read addr 0 at CA
  output     [`npuarc_RGF_ADDR_RANGE]    ca_rf_ra1_r,        // reg-read addr 1 at CA
  output     [`npuarc_RGF_ADDR_RANGE]    ca_rf_wa0_r,        //
  output                          ca_rf_wenb0_r,      //

  output reg [`npuarc_RGF_ADDR_RANGE]    wa_rf_wa1_nxt,      // write port 1 address
  output reg                      wa_rf_wenb1_nxt,    // write port 1 enable
  output reg                      wa_rf_wuop_nxt,     // write port is for uop load 
  output reg                      wa_rf_wenb1_64_nxt, // write port 1 64-bit
  output reg [`npuarc_DATA_RANGE]        wa_rf_wdata1_hi_nxt,//
  output reg                      ca_data1_hi_pass,   // update wa_rf_wdata1_hi_r
  output reg [`npuarc_DATA_RANGE]        wa_rf_wdata0_lo_nxt,//
  output reg                      ca_data0_lo_pass,   // update wa_rf_wdata0_lo_r
  output                          ca_rf_wenb0_64_r  , //
  output                          ca_cc_byp_64_haz_r, // no CA bypass to r0h
  output reg [`npuarc_DATA_RANGE]        wa_rf_wdata0_hi_nxt,//
  output reg                      ca_data0_hi_pass,   // update wa_rf_wdata0_hi_r
  output     [`npuarc_RGF_ADDR_RANGE]    ca_rf_wa1_r,        //
  output                          ca_rf_wenb1_r,      //
  output reg [`npuarc_DATA_RANGE]        wa_rf_wdata1_lo_nxt,//
  output reg                      ca_data1_lo_pass,   // update wa_rf_wdata1_lo_r
  output                          ca_rf_wenb1_64_r,   //
  output                          ca_rf_renb0_64_r,  //
  output                          ca_rf_renb1_64_r,  //
  output                          wa_rf_wenb0_64_nxt,//
  output                          wa_cmt_norm_evt_nxt,//
  output                          wa_cmt_uop_evt_nxt, //
  output                          wa_cmt_flag_evt_nxt,//
  output reg                      wa_lf_set_nxt,      //
  output reg                      wa_lf_clear_nxt,    //
  output reg                      wa_lf_double_nxt,   //
  output reg [`npuarc_PADDR_RANGE]       wa_lpa_nxt,         //
  output reg [`npuarc_WA_CODE_WIDTH-1:0] wa_code_nxt,        //
  output reg [`npuarc_PC_RANGE]          ar_pc_nxt,          // next arch. PC
  output reg                      ar_pc_pass,         // update arch. PC
  output     [`npuarc_PFLAG_RANGE]       wa_aux_status32_nxt,//
  output                          wa_aux_uop_flag_pass,//
  output                          wa_aux_flags_pass,  //
  output                          wa_aux_status32_pass //
);

// alu_alu_ca
//
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Signal from alu
wire  [`npuarc_DATA_RANGE]         alu_result_hi;
// leda NTL_CON13A on
wire  [`npuarc_DATA_RANGE]         alu_result_lo;
wire  [`npuarc_ZNCV_RANGE]         alu_result_zncv;
wire  [`npuarc_ZNCV_RANGE]         alu_result_zncv_sel;      // alu or eia
wire                        alu_brcc_cond;
reg                         dc4_jtlb_lookup_valid;
// @ca_cond_PROC
//
reg                         z_flag;
reg                         n_flag;
reg                         c_flag;
reg                         v_flag;
reg                         q_cond;
//reg                         ca_brcc_cond;
reg                         ca_flag_wr_r;

// @ca_replay_PROC:
//
wire                        ca_is_flag;
wire                        ca_flag_upt;
reg                         kill_replay;
reg                         replay_aux_strict_nxt;
reg                         replay_aux_serial_nxt;
reg                         replay_rtie_nxt;
reg                         do_aux_replay;

//reg                         replay_post_divz_nxt;
reg                         replay_post_sleep_sync_nxt;

// @ca_uop_active_PROC
//
reg                         ca_uop_state_cg0;
reg                         kill_uop_active;
reg                         insn_starts_uop;
reg                         start_prol;
reg                         ca_uop_active_clr;
reg                         ca_uop_predictable_nxt;
reg                         ca_uop_enter_nxt;
reg                         ca_uop_inprol_nxt;
//reg                         ca_uop_active;
reg                         gb_sys_reset_done_nxt;

// @dbg_evt_PROC
//
reg                         ct_valid;
reg                         cmt_dbg_evt;
reg                         cmt_brk_evt;
reg                         do_insn_step;
reg                         cmt_isi_evt;
reg                         ca_async_halt_evt;
reg                         ca_async_run_evt;

// @ca_ucode_PROC
//
reg   [`npuarc_WA_CODE_WIDTH-1:0]  ucode_out;
reg                         ca_disable_w0;
reg                         ca_disable_w1;

// @ca_commit_evt_PROC
reg                         commit_raw_evt;
reg                         commit_debug_evt;
reg                         commit_sleep_evt;
reg                         ca_rd_link0;
reg                         commit_uop_evt;
reg                         commit_flag_evt;

// @ar_pc_nxt_PROC
// leda NTL_CON13A off
//LMD: do not care carry bit
//LJ: can be ignored
reg                         dont_care;
reg                         dont_care_1;
// leda NTL_CON13A on
reg   [`npuarc_PC_RANGE]           ar_lp_start;          // lp_start without bit 0

// @ca_src_regs_PROC
//
reg   [`npuarc_DATA_RANGE]         ca_res_r;
reg   [`npuarc_ZNCV_RANGE]         ca_zncv_r;
reg   [`npuarc_PC_INC_RANGE]       ca_pc_inc_r;
reg   [`npuarc_CA_P0_RANGE]        ca_p0_r;
reg   [`npuarc_CA_P1_RANGE]        ca_p1_r;
reg   [`npuarc_CA_P2_RANGE]        ca_p2_r;
reg   [`npuarc_CA_P3_RANGE]        ca_p3_r;
reg                         ca_cin_r;
 
// The following registers are updated only when a late-evaluating ALU
// operation is received at CA. This isolates the CA-stage ALU from
// ucode transitions that would otherwise cause unecessary dynamic
// switching inside the alb_alu_ca module.
//
reg                         i_add_op_r;
reg                         i_or_op_r;
reg                         i_and_op_r;
reg                         i_xor_op_r;
reg                         i_mov_op_r;
reg                         i_signed_op_r;
reg                         i_src2_mask_sel_r;
reg                         i_byte_size_r;
reg                         i_half_size_r;
reg                         i_shift_op_r;
reg                         i_left_r;
reg                         i_rotate_r;
reg                         i_with_carry_r;
reg                         i_bit_op_r;
reg                         i_mask_op_r;
reg                         i_inv_src1_r;
reg                         i_inv_src2_r;


// @ca_replay_regs_PROC
//
reg                         replay_aux_serial_r;
reg                         replay_aux_strict_r;
reg                         replay_rtie_r;
//reg                         replay_post_divz_r;
reg                         replay_post_sleep_sync_r;

reg                         ca_src0_cg0;
reg                         ca_src1_cg0;
reg                         ca_res_cg0;
reg                         ca_target_cg0;
reg                         ca_mem_addr_cg0;

reg                         ca_px_cg0;
reg                         ca_code_cg0;
reg                         ca_alu_code_cg0;

// @ca_bypass_PROC
//
reg   [`npuarc_DATA_RANGE]         ca_byp_src0;          // bypassed ca_src0_r value
reg   [`npuarc_DATA_RANGE]         ca_byp_src1;          // bypassed ca_src1_r value

reg                         no_byp_ca_src0;       // don't bypass ca_src0_r
reg                         no_byp_ca_src1;       // don't bypass ca_src1_r

// @ca_result_PROC
//
reg   [`npuarc_DATA_RANGE]         false_res_lsw;        // least-sig word of false res
reg   [`npuarc_DATA_RANGE]         ca_false_res;         // CA result if cond is false
reg   [`npuarc_DATA_RANGE]         ca_cond_res;          // conditional CA result
reg   [`npuarc_DATA_RANGE]         ca_rf_wdata1_lo;      // selected write 1, lo
reg                         ca_sel_lr_data;       // select LR, AEX result
reg                         ca_sel_ca_alu;        // select late ALU result
reg                         ca_sel_stat32_data;   // select CLI result
reg   [`npuarc_DATA_RANGE]         false_res_msw;        // most-sig word of false res
reg   [`npuarc_DATA_RANGE]         ca_false_res_hi;      // CA result if cond is false
reg   [`npuarc_DATA_RANGE]         ca_cond_res_hi;       // conditional CA result

// @ca_fall_thru_PROC
//
reg                         ca_is_branch;         // CA insn is branch/jump
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  Lower bits are not used
// leda NTL_CON12A off
// LMD: undriven internal net
// LJ:  All bits are driven
//reg   [3:1]                 ca_tail_pc;           // PC offset
reg   [`npuarc_IC_BANK_SEL:1]                 ca_tail_pc;           // PC offset
// leda NTL_CON13A on
// leda NTL_CON12A on
// @ca_ctrl_regs_PROC
//
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg   [`npuarc_CA_CODE_WIDTH-1:0]  ca_code_r;
// leda NTL_CON32 on

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  ucode generated
// Library ARCv2HS-3.5.999999999
// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.

// Certain materials incorporated herein are copyright (C) 2010 - 2011,
// The University Court of the University of Edinburgh. All Rights Reserved.

assign ca_rf_wa0_r  = ca_code_r[`npuarc_RF_WA0_RANGE];  // generated code
assign ca_rf_wenb0_r  = ca_code_r[`npuarc_RF_WENB0_RANGE];  // generated code
assign ca_rf_wenb0_64_r  = ca_code_r[`npuarc_RF_WENB0_64_RANGE];  // generated code
assign ca_cc_byp_64_haz_r  = ca_code_r[`npuarc_CC_BYP_64_HAZ_RANGE];  // generated code
assign ca_has_limm_r  = ca_code_r[`npuarc_HAS_LIMM_RANGE];  // generated code
assign ca_is_16bit_r  = ca_code_r[`npuarc_IS_16BIT_RANGE];  // generated code
assign ca_sr_op_r   = ca_code_r[`npuarc_SR_OP_RANGE];  // generated code
assign ca_loop_op_r  = ca_code_r[`npuarc_LOOP_OP_RANGE];  // generated code
assign ca_locked_r  = ca_code_r[`npuarc_LOCKED_RANGE];  // generated code
assign ca_wa0_lpc_r  = ca_code_r[`npuarc_WA0_LPC_RANGE];  // generated code
assign ca_dslot_r   = ca_code_r[`npuarc_DSLOT_RANGE];  // generated code
wire   ca_sleep_op_r;  // generated code
assign ca_sleep_op_r  = ca_code_r[`npuarc_SLEEP_OP_RANGE];  // generated code
assign ca_acc_wenb_r  = ca_code_r[`npuarc_ACC_WENB_RANGE];  // generated code
assign ca_writes_acc_r  = ca_code_r[`npuarc_WRITES_ACC_RANGE];  // generated code
assign ca_lr_op_r   = ca_code_r[`npuarc_LR_OP_RANGE];  // generated code
assign ca_jump_r    = ca_code_r[`npuarc_JUMP_RANGE];  // generated code
assign ca_load_r    = ca_code_r[`npuarc_LOAD_RANGE];  // generated code
wire   ca_pref_r;  // generated code
assign ca_pref_r  = ca_code_r[`npuarc_PREF_RANGE];  // generated code
assign ca_store_r   = ca_code_r[`npuarc_STORE_RANGE];  // generated code
wire   ca_uop_prol_r;  // generated code
assign ca_uop_prol_r  = ca_code_r[`npuarc_UOP_PROL_RANGE];  // generated code
assign ca_rf_wa1_r  = ca_code_r[`npuarc_RF_WA1_RANGE];  // generated code
assign ca_rf_wenb1_r  = ca_code_r[`npuarc_RF_WENB1_RANGE];  // generated code
assign ca_rf_wenb1_64_r  = ca_code_r[`npuarc_RF_WENB1_64_RANGE];  // generated code
wire   ca_signed_op_r;  // generated code
assign ca_signed_op_r  = ca_code_r[`npuarc_SIGNED_OP_RANGE];  // generated code
wire   ca_double_size_r;  // generated code
assign ca_double_size_r  = ca_code_r[`npuarc_DOUBLE_SIZE_RANGE];  // generated code
wire   ca_half_size_r;  // generated code
assign ca_half_size_r  = ca_code_r[`npuarc_HALF_SIZE_RANGE];  // generated code
assign ca_byte_size_r  = ca_code_r[`npuarc_BYTE_SIZE_RANGE];  // generated code
assign ca_rtie_op_r  = ca_code_r[`npuarc_RTIE_OP_RANGE];  // generated code
wire   ca_enter_op_r;  // generated code
assign ca_enter_op_r  = ca_code_r[`npuarc_ENTER_OP_RANGE];  // generated code
assign ca_leave_op_r  = ca_code_r[`npuarc_LEAVE_OP_RANGE];  // generated code
assign ca_trap_op_r  = ca_code_r[`npuarc_TRAP_OP_RANGE];  // generated code
wire   ca_sync_op_r;  // generated code
assign ca_sync_op_r  = ca_code_r[`npuarc_SYNC_OP_RANGE];  // generated code
assign ca_brk_op_r  = ca_code_r[`npuarc_BRK_OP_RANGE];  // generated code
wire   ca_invalid_instr_r;  // generated code
assign ca_invalid_instr_r  = ca_code_r[`npuarc_INVALID_INSTR_RANGE];  // generated code
wire   ca_rgf_link_r;  // generated code
assign ca_rgf_link_r  = ca_code_r[`npuarc_RGF_LINK_RANGE];  // generated code
wire   ca_prod_sign_r;  // generated code
assign ca_prod_sign_r  = ca_code_r[`npuarc_PROD_SIGN_RANGE];  // generated code
assign ca_macu_r    = ca_code_r[`npuarc_MACU_RANGE];  // generated code
wire   ca_quad_op_r;  // generated code
assign ca_quad_op_r  = ca_code_r[`npuarc_QUAD_OP_RANGE];  // generated code
wire   ca_acc_op_r;  // generated code
assign ca_acc_op_r  = ca_code_r[`npuarc_ACC_OP_RANGE];  // generated code
assign ca_vector_op_r  = ca_code_r[`npuarc_VECTOR_OP_RANGE];  // generated code
wire   ca_dual_op_r;  // generated code
assign ca_dual_op_r  = ca_code_r[`npuarc_DUAL_OP_RANGE];  // generated code
assign ca_mpy_op_r  = ca_code_r[`npuarc_MPY_OP_RANGE];  // generated code
wire   ca_z_wen_r;  // generated code
assign ca_z_wen_r  = ca_code_r[`npuarc_Z_WEN_RANGE];  // generated code
wire   ca_n_wen_r;  // generated code
assign ca_n_wen_r  = ca_code_r[`npuarc_N_WEN_RANGE];  // generated code
wire   ca_c_wen_r;  // generated code
assign ca_c_wen_r  = ca_code_r[`npuarc_C_WEN_RANGE];  // generated code
wire   ca_v_wen_r;  // generated code
assign ca_v_wen_r  = ca_code_r[`npuarc_V_WEN_RANGE];  // generated code
wire   ca_kernel_op_r;  // generated code
assign ca_kernel_op_r  = ca_code_r[`npuarc_KERNEL_OP_RANGE];  // generated code
wire   ca_flag_op_r;  // generated code
assign ca_flag_op_r  = ca_code_r[`npuarc_FLAG_OP_RANGE];  // generated code
assign ca_bcc_r     = ca_code_r[`npuarc_BCC_RANGE];  // generated code
wire   ca_link_r;  // generated code
assign ca_link_r  = ca_code_r[`npuarc_LINK_RANGE];  // generated code
assign ca_brcc_bbit_r  = ca_code_r[`npuarc_BRCC_BBIT_RANGE];  // generated code
assign ca_cache_byp_r  = ca_code_r[`npuarc_CACHE_BYP_RANGE];  // generated code
wire   ca_slow_op_r;  // generated code
assign ca_slow_op_r  = ca_code_r[`npuarc_SLOW_OP_RANGE];  // generated code
assign ca_fast_op_r  = ca_code_r[`npuarc_FAST_OP_RANGE];  // generated code
assign ca_div_op_r  = ca_code_r[`npuarc_DIV_OP_RANGE];  // generated code
assign ca_btab_op_r  = ca_code_r[`npuarc_BTAB_OP_RANGE];  // generated code
assign ca_ei_op_r   = ca_code_r[`npuarc_EI_OP_RANGE];  // generated code
assign ca_in_eslot_r  = ca_code_r[`npuarc_IN_ESLOT_RANGE];  // generated code
wire   ca_rel_branch_r;  // generated code
assign ca_rel_branch_r  = ca_code_r[`npuarc_REL_BRANCH_RANGE];  // generated code
wire   ca_illegal_operand_r;  // generated code
assign ca_illegal_operand_r  = ca_code_r[`npuarc_ILLEGAL_OPERAND_RANGE];  // generated code
wire   ca_swap_op_r;  // generated code
assign ca_swap_op_r  = ca_code_r[`npuarc_SWAP_OP_RANGE];  // generated code
wire   ca_setcc_op_r;  // generated code
assign ca_setcc_op_r  = ca_code_r[`npuarc_SETCC_OP_RANGE];  // generated code
wire [2:0]  ca_cc_field_r;  // generated code
assign ca_cc_field_r  = ca_code_r[`npuarc_CC_FIELD_RANGE];  // generated code
assign ca_q_field_r  = ca_code_r[`npuarc_Q_FIELD_RANGE];  // generated code
assign ca_dest_cr_is_ext_r  = ca_code_r[`npuarc_DEST_CR_IS_EXT_RANGE];  // generated code
wire   ca_add_op_r;  // generated code
assign ca_add_op_r  = ca_code_r[`npuarc_ADD_OP_RANGE];  // generated code
wire   ca_and_op_r;  // generated code
assign ca_and_op_r  = ca_code_r[`npuarc_AND_OP_RANGE];  // generated code
wire   ca_or_op_r;  // generated code
assign ca_or_op_r  = ca_code_r[`npuarc_OR_OP_RANGE];  // generated code
wire   ca_xor_op_r;  // generated code
assign ca_xor_op_r  = ca_code_r[`npuarc_XOR_OP_RANGE];  // generated code
wire   ca_mov_op_r;  // generated code
assign ca_mov_op_r  = ca_code_r[`npuarc_MOV_OP_RANGE];  // generated code
assign ca_with_carry_r  = ca_code_r[`npuarc_WITH_CARRY_RANGE];  // generated code
wire   ca_simple_shift_op_r;  // generated code
assign ca_simple_shift_op_r  = ca_code_r[`npuarc_SIMPLE_SHIFT_OP_RANGE];  // generated code
wire   ca_left_shift_r;  // generated code
assign ca_left_shift_r  = ca_code_r[`npuarc_LEFT_SHIFT_RANGE];  // generated code
wire   ca_rotate_op_r;  // generated code
assign ca_rotate_op_r  = ca_code_r[`npuarc_ROTATE_OP_RANGE];  // generated code
wire   ca_inv_src1_r;  // generated code
assign ca_inv_src1_r  = ca_code_r[`npuarc_INV_SRC1_RANGE];  // generated code
wire   ca_inv_src2_r;  // generated code
assign ca_inv_src2_r  = ca_code_r[`npuarc_INV_SRC2_RANGE];  // generated code
wire   ca_bit_op_r;  // generated code
assign ca_bit_op_r  = ca_code_r[`npuarc_BIT_OP_RANGE];  // generated code
wire   ca_mask_op_r;  // generated code
assign ca_mask_op_r  = ca_code_r[`npuarc_MASK_OP_RANGE];  // generated code
wire   ca_src2_mask_sel_r;  // generated code
assign ca_src2_mask_sel_r  = ca_code_r[`npuarc_SRC2_MASK_SEL_RANGE];  // generated code
assign ca_uop_commit_r  = ca_code_r[`npuarc_UOP_COMMIT_RANGE];  // generated code
wire   ca_uop_epil_r;  // generated code
assign ca_uop_epil_r  = ca_code_r[`npuarc_UOP_EPIL_RANGE];  // generated code
wire   ca_uop_excpn_r;  // generated code
assign ca_uop_excpn_r  = ca_code_r[`npuarc_UOP_EXCPN_RANGE];  // generated code
assign ca_predicate_r  = ca_code_r[`npuarc_PREDICATE_RANGE];  // generated code
wire   ca_rf_renb0_r;  // generated code
assign ca_rf_renb0_r  = ca_code_r[`npuarc_RF_RENB0_RANGE];  // generated code
wire   ca_rf_renb1_r;  // generated code
assign ca_rf_renb1_r  = ca_code_r[`npuarc_RF_RENB1_RANGE];  // generated code
assign ca_rf_renb0_64_r  = ca_code_r[`npuarc_RF_RENB0_64_RANGE];  // generated code
assign ca_rf_renb1_64_r  = ca_code_r[`npuarc_RF_RENB1_64_RANGE];  // generated code
assign ca_rf_ra0_r  = ca_code_r[`npuarc_RF_RA0_RANGE];  // generated code
assign ca_rf_ra1_r  = ca_code_r[`npuarc_RF_RA1_RANGE];  // generated code
wire   ca_jli_src0_r;  // generated code
assign ca_jli_src0_r  = ca_code_r[`npuarc_JLI_SRC0_RANGE];  // generated code
assign ca_uop_inst_r  = ca_code_r[`npuarc_UOP_INST_RANGE];  // generated code
wire   ca_vec_shimm_r;  // generated code
assign ca_vec_shimm_r  = ca_code_r[`npuarc_VEC_SHIMM_RANGE];  // generated code
assign ca_iprot_viol_r  = ca_code_r[`npuarc_IPROT_VIOL_RANGE];  // generated code
assign ca_dmb_op_r  = ca_code_r[`npuarc_DMB_OP_RANGE];  // generated code
assign ca_dmb_type_r  = ca_code_r[`npuarc_DMB_TYPE_RANGE];  // generated code

// leda NTL_CON13A on
 assign ca_enter_op = ca_enter_op_r;  // ca_wires declares ca_enter_op_r

 reg                        ca_uop_is_leave;  // ca stage is at leave uop inst.


// @ca_rf_results_PROC
//
reg                         wa_writes_acc_nxt;    // next wa_write_acc_r
reg                         wa_acc_wenb_nxt;      // next wa_acc_wenb_r

reg                         ca_rf_wuop;           // is a special CA rf_wa1

// signal to indicate status32 update by load instruction during interrupt
// epilogue sequence.
//
reg                         wa_uopld_status32_nxt;

// @ca_atomic_PROC
//
reg                         ca_scond;


//LEAVE_s, ENTER_S are 16bit. keep the info until the uop senquense finished
reg uop_starter_is_16bit;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Implement reduced CA-stage ALU                                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_alu_ca u_alb_alu_ca(
  .src0_lo              (ca_src0_r            ),
  .src1_lo              (ca_src1_r            ),
  .ca_res_r             (ca_res_r             ),
  .src0_hi              (mp4_s_hi_r           ),
  .src1_hi              (mp4_c_hi_r           ),
  .src0_hi_65           (mp4_s_65_r           ),
  .src1_hi_65           (mp4_c_65_r           ),
  .ar_aux_status32_r    (ar_aux_status32_r    ),
  .ca_p0_r              (ca_p0_r              ),
  .ca_p1_r              (ca_p1_r              ),
  .ca_p2_r              (ca_p2_r              ),
  .ca_p3_r              (ca_p3_r              ),
  .byp_acc_hi           (byp_acc_hi           ),
  .v_flag               (v_flag               ),
  .ca_cin_r             (ca_cin_r             ),
  
  .ca_add_op_r          (i_add_op_r           ),
  .ca_bit_op_r          (i_bit_op_r           ),  
  .ca_mask_op_r         (i_mask_op_r          ),
  .ca_inv_src1_r        (i_inv_src1_r         ), 
  .ca_inv_src2_r        (i_inv_src2_r         ), 
  .ca_or_op_r           (i_or_op_r            ),
  .ca_and_op_r          (i_and_op_r           ),
  .ca_xor_op_r          (i_xor_op_r           ),
  .ca_mov_op_r          (i_mov_op_r           ),
  .ca_signed_op_r       (i_signed_op_r        ),
  .ca_src2_mask_sel_r   (i_src2_mask_sel_r    ), 
  .ca_byte_size_r       (i_byte_size_r        ),
  .ca_half_size_r       (i_half_size_r        ),
  .ca_simple_shift_op_r (i_shift_op_r         ),
  .ca_left_shift_r      (i_left_r             ),
  .ca_rotate_op_r       (i_rotate_r           ),
  .ca_with_carry_r      (i_with_carry_r       ),
  .ca_vec_shimm_r       (ca_vec_shimm_r       ),
  .ca_link_r            (ca_link_r            ),
  .ca_cc_field_r        (ca_cc_field_r        ),
  .ca_setcc_op_r        (ca_setcc_op_r        ),
  .ca_mpy_op_r          (ca_mpy_op_r          ),
  .ca_acc_wenb_r        (ca_acc_wenb_r        ),
  .ca_acc_op_r          (ca_acc_op_r          ),
  .ca_vector_op_r       (ca_vector_op_r       ),
  .ca_dual_op_r         (ca_dual_op_r         ),
  .ca_prod_sign_r       (ca_prod_sign_r       ),
  .ca_quad_op_r         (ca_quad_op_r         ),
  .ca_scond             (ca_scond             ),
  .dmp_scond_zflag      (dmp_scond_zflag      ),


  .result_lo            (alu_result_lo        ),
  .result_hi            (alu_result_hi        ),
  .alu_acch_res         (ca_acch_res          ),
  .result_zncv          (alu_result_zncv      ),
  .alu_brcc_cond        (alu_brcc_cond        )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_cond_PROC

  // Create synonyms for the flags used during the evaluation of the
  // 'cc'-field. Unlike, the comparable statement in X1, the flags we
  // use at this point are the architectural versions defined and
  // retained in WA.
  //
  z_flag = ar_aux_status32_r[`npuarc_Z_FLAG];
  n_flag = ar_aux_status32_r[`npuarc_N_FLAG];
  c_flag = ar_aux_status32_r[`npuarc_C_FLAG];
  v_flag = ar_aux_status32_r[`npuarc_V_FLAG];

  q_cond = 1'b1;                                     // Default is unconditional

  // Decode the condition code field for Bcc, Jcc and predication
  //
  case ( ca_q_field_r )
    5'h00:   q_cond =  1'b1;                           // Always (default)
    5'h01:   q_cond =  z_flag;                         // Zero
    5'h02:   q_cond = ~z_flag;                         // Non-Zero
    5'h03:   q_cond = ~n_flag;                         // Positive
    5'h04:   q_cond =  n_flag;                         // Negative
    5'h05:   q_cond =  c_flag;                         // Carry set
    5'h06:   q_cond = ~c_flag;                         // Carry clear
    5'h07:   q_cond =  v_flag;                         // Overflow set
    5'h08:   q_cond = ~v_flag;                         // Overflow clear
    5'h09:   q_cond = (n_flag & v_flag & (~z_flag))
                    | ((~n_flag) & (~v_flag) & (~z_flag)); // > signed
    5'h0a:   q_cond = (n_flag == v_flag);              // >= signed
    5'h0b:   q_cond = (n_flag != v_flag);              // < signed
    5'h0c:   q_cond = z_flag | (n_flag != v_flag);     // <= signed
    5'h0d:   q_cond = (~c_flag) & (~z_flag);           // > unsigned
    5'h0e:   q_cond = c_flag | z_flag;                 // <= unsigned
    5'h0f:   q_cond = (~n_flag) & (~z_flag);           // Positive non-zero
    default: q_cond = eia_ext_cond;
  endcase

  // If the current instruction in CA has been previously evaluated in
  // X1, we assume that any control ucode signals have been rescinded
  // if the q-field evaluated to false; otherwise, we revert to the
  // usual scheme.
  //
  ca_cond       = ca_valid_r
                & ca_predicate_r
                & (   ca_done_r
                    | q_cond
                  )
                ;
/*
  ca_brcc_cond  = ca_valid_r
                & ca_predicate_r
                & (   ca_done_r
                    | alu_brcc_cond
                  )
                ;
*/  
  // Status for RTT; instruction is conditional
  //
  ca_cond_inst  = ca_pass
                & (  ca_brcc_bbit_r
                   | (|ca_q_field_r))
                ;

  ca_cond_met   = ca_pass
                & (ca_brcc_bbit_r ? ca_br_taken : ca_cond)
                ;

  //==========================================================================
  // A branch should be taken in the following cases:
  //
  //  (a). a true condition for Bcc, Jcc, BLcc or JLcc; or a JLI_S or EI_S.
  //  (b). a false condition for LPcc, instructions;
  //  (c). a true condition for BRcc or BBITn.
  //  (d). the X1 instruction is in an execution slot of an EI_S instruction
  //  (e). a BI or BIH instruction (which is unconditional)
  //
  // Cases (c), (e) and (f) are all determined at the X1 stage, and will
  // be inherited via ca_done_r and ca_predicate_r.
  //
  ca_br_direction = (   (ca_cond    & (ca_bcc_r | ca_jump_r)) // (a) Bcc,Jcc,EI
                      | ((~ca_cond) & ca_loop_op_r)           // (b) LPcc false
                      | (alu_brcc_cond & ca_brcc_bbit_r)      // (c) BRcc
                      | ca_in_eslot_r                         // (d) in EI slot
                      | ca_btab_op_r                          // (e) BI,BIH
                    );

  //==========================================================================
  // Determine whether the scaled BI, BIH index register has the same value
  // as the index value required for a correct BTA prediction of the CA-stage 
  // BI, BIH instruction. The ca_target_r input register will contain the
  // value (ca_pred_bta_r - ca_seq_pc_r), which was pre-computed in SA.
  // If this is equal to the scaled index register value in ca_src1_r, then
  // the predicted BTA was correct. If not, then a BTA misprediction occurred.
  //


  // Detect when a replay due to dtlb miss has occurred
  //
  dc4_jtlb_lookup_valid =  ~ wa_restart_kill_r
                       &     dc4_replay      
                       &     (|dc4_dtlb_miss_r)
                       &   (~ hlt_restart_r)  
                       &   (~ ct_replay)
                       &   (~ excpn_restart)
                       &   (~ ca_error_branch_r)
                       &   (~ (aps_halt | aps_break))
                       &   (~ ca_iprot_viol_r)
                       &   (~ db_active_r)
                       ;


end // block: ca_cond_PROC

always @(posedge clk or posedge rst_a)
begin: wa_tlb_start_PROC
  if (rst_a == 1'b1)
  begin
    wa_jtlb_lookup_start_r    <= 1'b0;
  end
  else
  begin
    wa_jtlb_lookup_start_r  <= dc4_jtlb_lookup_valid;
  end
end // block: wa_tlb_start_PROC

assign wa_jtlb_cancel = wa_restart_r
                     & (~(  int_evts[`npuarc_INTEVT_INPROL] 
                          | int_evts[`npuarc_INTEVT_INEPIL])
                       )
                       ;



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial logic to determine the fall-through address of the current //
// instruction in the Commit stage. This is obtained from ca_mem_addr_r     //
// when the Commit-stage instruction is a branch. Otherwise it is provided  //
// by the next sequential instruction address after ar_pc_r.                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_fall_thru_PROC

  //==========================================================================
  // ca_br_or_jmp is asserted whenever the CA stage instruction is one that
  // should have its BTA prediction checked against ca_br_target.
  // Other types of branch, such as the phantom branch at a loop-end, or
  // the branch from a BI or BIH instruction, are checked against other
  // target addresses.
  // LPcc is predicted when it is conditional.
  //
  ca_br_or_jmp      = ca_loop_op_r
                    | ca_bcc_r
                    | ca_jump_r
                    | ca_brcc_bbit_r
                    | ca_rtie_op_r
                    | ca_in_eslot_r
                    ;
                  
  ca_is_branch      = ca_loop_op_r
                    | ca_bcc_r
                    | ca_jump_r
                    | ca_brcc_bbit_r
                    | ca_rtie_op_r
                    | ca_btab_op_r
                    ;

 ca_br_fall_thru    = ca_is_branch 
                    ? ca_mem_addr_r[`npuarc_PC_RANGE]
                    : ca_seq_pc_nxt;

// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential dont_care carry bit
//{dont_care_1, ca_tail_pc} = ca_br_fall_thru[3:1] + 3'b111;
 {dont_care_1, ca_tail_pc} = ca_br_fall_thru[`npuarc_IC_BANK_SEL:1] + {`npuarc_IC_BANK_SEL{1'b1}}; 
// leda B_3208 on
 
// the IM_DWIDTH of the ifu will determine which bit define the tail_pc or which bit select the bank
// IC_BANK_SEL==3 when IM_DWIDTH ==128. // IC_BANK_SEL==4 when IM_DWIDTH ==256. 
//ca_tail_pc_3       = ca_tail_pc[3];
 ca_tail_pc_3       = ca_tail_pc[`npuarc_IC_BANK_SEL]; 

end // block: ca_fall_thru_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial logic to forward the results from Writeback into the two   //
// source register operands at the Commit stage, for use as either the      //
// STore data or SR/AEX data.                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           src0_wa_w0_lo;
reg                           src0_wa_w1_lo;
reg                           src0_wa_w0_hi;
reg                           src0_wa_w1_hi;
reg                           ca_std_op;

always @*
begin: ca_bypass_PROC

  //==========================================================================
  // Define the conditions under which each WA-stage bypass result is to be
  // forwarded to the ca_byp_src0 operand.
  // Bypass results are required by ca_byp_src0, when the result is needed 
  // by a 64-bit STD operation to provide the upper 32 bits of store data.
  //
  ca_std_op       = ca_store_r & ca_double_size_r;
  
  src0_wa_w0_lo   = ca_std_op ? fwd_ca_r1h_wa_w0_lo : fwd_ca_r0_wa_w0_lo;
  src0_wa_w1_lo   = ca_std_op ? fwd_ca_r1h_wa_w1_lo : fwd_ca_r0_wa_w1_lo;
  src0_wa_w0_hi   = ca_std_op ? fwd_ca_r1h_wa_w0_hi : fwd_ca_r0_wa_w0_hi;
  src0_wa_w1_hi   = ca_std_op ? fwd_ca_r1h_wa_w1_hi : fwd_ca_r0_wa_w1_hi;

  //==========================================================================
  // Determine whether the current ca_src0_r value is up-to-date and therefore
  // does not need to by bypassed with a more recent value from the Writeback
  // stage result registers.
  //
  no_byp_ca_src0    = ~(   src0_wa_w0_lo // bypass src0 from write #0 lo
                         | src0_wa_w1_lo // bypass src0 from write #1 lo
                         | src0_wa_w0_hi // bypass src0 from write #0 hi
                         | src0_wa_w1_hi // bypass src0 from write #1 hi
                       )
                    ;

  //==========================================================================
  // Bypass network to select result values from the Writeback stage that are
  // more recent than the stale value in ca_src0_r.
  //
  ca_byp_src0       = ( {`npuarc_DATA_SIZE{no_byp_ca_src0}}  & ca_src0_r        )
                    | ( {`npuarc_DATA_SIZE{src0_wa_w0_lo}}   & wa_rf_wdata0_lo_r)
                    | ( {`npuarc_DATA_SIZE{src0_wa_w1_lo}}   & wa_rf_wdata1_lo_r)
                    | ( {`npuarc_DATA_SIZE{src0_wa_w0_hi}}   & wa_rf_wdata0_hi_r)
                    | ( {`npuarc_DATA_SIZE{src0_wa_w1_hi}}   & wa_rf_wdata1_hi_r)
                    ;

  //==========================================================================
  // Determine whether the current ca_src1_r value is up-to-date and therefore
  // does not need to by bypassed with a more recent value from the Writeback
  // stage result registers.
  //
  no_byp_ca_src1    = ~(   fwd_ca_r1_wa_w0_lo // bypass src1 from write #0 lo
                         | fwd_ca_r1_wa_w1_lo // bypass src1 from write #1 lo
                         | fwd_ca_r1_wa_w0_hi // bypass src1 from write #0 hi
                         | fwd_ca_r1_wa_w1_hi // bypass src1 from write #1 hi
                       )
                    ;

  //==========================================================================
  // Bypass network to select result values from the Writeback stage that are
  // more recent than the stale value in ca_src1_r.
  //
  ca_byp_src1       = ( {`npuarc_DATA_SIZE{no_byp_ca_src1}}     & ca_src1_r        )
                    | ( {`npuarc_DATA_SIZE{fwd_ca_r1_wa_w0_lo}} & wa_rf_wdata0_lo_r)
                    | ( {`npuarc_DATA_SIZE{fwd_ca_r1_wa_w1_lo}} & wa_rf_wdata1_lo_r)
                    | ( {`npuarc_DATA_SIZE{fwd_ca_r1_wa_w0_hi}} & wa_rf_wdata0_hi_r)
                    | ( {`npuarc_DATA_SIZE{fwd_ca_r1_wa_w1_hi}} & wa_rf_wdata1_hi_r)
                    ;

  //==========================================================================
  // *** BYTE_ORDER == HS_LITTLE_ENDIAN ***
  //
  //   Select the Store data value, for ST, STH and STB instructions, and the 
  //   lower 32 bits of Store data value for STD, from the bypassed src1
  //   channel.
  //
  dc4_write_data_lo = ca_byp_src1;

  //==========================================================================
  // *** BYTE_ORDER == HS_LITTLE_ENDIAN ***
  //
  //   Select the upper 32-bits of Store data value, for STD instructions,
  //   from the bypassed src0 channel.
  //
  dc4_write_data_hi = ca_byp_src0;  

end // block: ca_bypass_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial process to select the in-order results produced, and       //
// forwarded from the Commit stage.                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire [`npuarc_E_FLAG]              int_e_flag;   // status32 E flag
wire                        int_ie_flag;  // status32 IE flag
reg   [`npuarc_DATA_RANGE]         eia_ca_res_r0;
reg   [`npuarc_DATA_RANGE]         eia_ca_res_r1;

always @*
begin: ca_result_PROC

  //==========================================================================
  // Select the next conditional result for an ALU.<cc> instruction
  // This is done in two parts; firstly, the bypassed src0 or src1 is 
  // selected as the potential result value (depending on whether there is
  // a first source operand or not). Secondly, this result value is selected
  // over the ALU result if the conditional result is false.
  //
  false_res_lsw     = ca_rf_renb0_r ? ca_byp_src0 : ca_byp_src1;

  // Select the default hi-reg value hi for use when predicate is false
  //
  false_res_msw     = ca_add_op_r ? mp4_s_hi_r : ca_src1_r;


  eia_ca_res_r0        = ca_eia_res_data;
  eia_ca_res_r1        = ca_eia_res_data_hi;

  ca_false_res      = false_res_lsw;
  ca_false_res_hi   = false_res_msw;

  ca_cond_res       = q_cond 
                    ? (ca_eia_res_valid ? eia_ca_res_r0 : alu_result_lo)
                    : ca_false_res;

  //==========================================================================
  // Select the result value at the Commit stage, from the potential sources
  // of the instruction result. When 64-bit results are possible, this logic
  // selects the lower 32 bits of the overall 64-bit result.
  //
  // The possible result sources, and conditions under which they are each
  // selected, are:-
  //
  // (a) LR result data    - when LR or AEX is at CA and ca_cond is true
  //     (aux_ca_lr_data)
  //
  // (b) Late ALU result   - when not LR, and ca_done_r == 0
  //     (ca_cond_res)
  //
  // (c) Early ALU result  - when not LR, and ca_done_r == 1 (default)
  //     (ca_res_r)
  //
  ca_sel_lr_data    = ca_lr_op_r & ca_cond;
  ca_sel_ca_alu     = ~(ca_lr_op_r | ca_done_r);
  ca_sel_stat32_data= ca_flag_op_r & ca_signed_op_r & (~ca_cache_byp_r);

  casez ({ ca_sel_stat32_data, ca_sel_ca_alu, ca_sel_lr_data })
    3'b1??:   ca_byp_data0_lo = {26'd0, 1'b1, int_ie_flag, int_e_flag};  // (c)
    3'b01?:   ca_byp_data0_lo = ca_cond_res;                             // (a)
    3'b001:   ca_byp_data0_lo = aux_ca_lr_data;                          // (b)
    default:  ca_byp_data0_lo = ca_res_r;                                // (d)
  endcase
  
  //==========================================================================
  // Select the next conditional high-part result for a conditional
  // instruction with 64-bit register pair destination.
  // This is done in two parts; firstly, the CA-registered src0 or src1 is 
  // selected as the potential result value (depending on whether there is
  // a first source operand or not). Secondly, this result value is selected
  // over the upper 32-bits of the ALU result if the conditional status
  // is false.
  //   

/// ----------------------
/// ----------------------
  ca_cond_res_hi    = ca_predicate_r ?
                         (   (ca_eia_res_valid == 1'b1)
                            ? eia_ca_res_r1  
                            : alu_result_hi
                          )
                    : ca_false_res_hi;
/// ----------------------
/// ----------------------
/// ----------------------
/// ----------------------
/// ----------------------

  //==========================================================================
  // The forwarding result on port 0 (hi) is provided from one of two sources:
  //
  //  (a). The upper half of a 64-bit result from the MP4 stage
  //
  //  (b). The replicated lower half of all 32-bit results (for ease of 
  //       writing odd registers in a 64-bit enabled register file).
  //
  ca_byp_data0_hi   = ca_rf_wenb0_64_r 
                    ? ca_cond_res_hi
                    : ca_byp_data0_lo
                    ;

  //==========================================================================
  // *** BYTE_ORDER == HS_LITTLE_ENDIAN ***
  // The forwarding result on port 1 is always the DC4 Load data, assuming
  // we are committing an in-order Load instruction. If this is not the case
  // then the value driven on ca_byp_data1_lo (and ca_byp_data1_hi) is
  // irrelevant.
  //
  ca_byp_data1_lo   = dmp_dc4_rf_wdata_lo;
  ca_byp_data1_hi   = ca_rf_wenb1_64_r
                    ? dmp_dc4_rf_wdata_hi
                    : dmp_dc4_rf_wdata_lo
                    ;

  //==========================================================================
  // The in-order result on port 1 [31:0] is provided from one of two sources:
  //
  //  (a). The bypassed ca_src0_r operand, for all SR operations at the 
  //       Commit stage.
  //
  //  (b). The lower 32 bits of an in-order Load value from DC4, for all
  //       Load operations at the Commit stage.
  //
  // This port 1 (low) result value is passed on to wa_rf_wdata1_lo_nxt in
  // the ca_rf_results_PROC process, when an in-order Commit-stage instruciton
  // is selected for retirement. 
  // In case (b), the data is presented on the wa_sr_data_r bus when a 
  // Writeback-stage SR updates an auxiliary registers
  //
  ca_rf_wdata1_lo   = ca_sr_op_r
                    ? ca_byp_src0                 // (a)
                    : dmp_dc4_rf_wdata_lo         // (b)
                    ;
  
end // block: ca_result_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to select the outgoing results at this stage       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_rf_results_PROC

  //==========================================================================
  // ca_rf_wuop indicates whether a register write from current CA instruction 
  // will be part of a micro-op sequence. If the instruction graduates,
  // this information will be prepended to its address.
  //
  ca_rf_wuop              = ca_uop_inst_r
                          & (~ca_uop_is_leave)
                          ;
                          
  //==========================================================================
  // ca_grad_rf_wa1 represents the register write address that is stored in
  // the graduation buffer entry if the current CA instruction graduates 
  // without retirement. It comprises the ca_rf_wuop bit, indicating a special
  // uop write, and the actual register address from write channel 1.
  //
  ca_grad_rf_wa1          = {   (ca_rf_wuop & ca_rf_wa1_r[`npuarc_RGF_ADDR_MSB])
                              , ca_rf_wa1_r
                            }
                          ;
  
  //==========================================================================
  //
  wa_rf_wdata0_lo_nxt     = ca_byp_data0_lo
                          ;

  //==========================================================================
  //
  wa_rf_wdata0_hi_nxt     = ca_byp_data0_hi
                          ;

  wa_rf_wuop_nxt          = 1'b0;

  //==========================================================================
  // Arbitrate retirement from various sources of graduated instructions
  // and in-order Load results.
  //
  // Set default values for request and acknowledge signals
  // include requests from DMP, DIV/REM and FPU and EIA (where configured).
  //
  ca_retire_req           = dmp_retire_req
                          | div_retire_req
                          | eia_retire_req
                          ;
                          
  ca_retire_tag           = `npuarc_GRAD_TAG_BITS'd0;
  
  dmp_retire_ack          = 1'b0;
  div_retire_ack          = 1'b0;
  eia_retire_ack          = 1'b0;
  ca_retire_ack           = 1'b0;

  ca_retire_flags         = ca_zncv_r;

  wa_acc_wenb_nxt         = ca_acc_wenb_r & ca_pass & ca_cond;

  casez ({  dmp_retire_req
           ,1'b0
           ,div_retire_req
           ,1'b0
           ,eia_retire_req
         })
  5'b1????: // case: DMP retire request, (hence no in-order LD at CA)
    begin
    ca_retire_tag         = dmp_retire_tag;       // retire the DMP's tag
    dmp_retire_ack        = 1'b1;                 // acknowledge retirement
    ca_retire_ack         = 1'b1;                 // retirement is granted
    wa_rf_wuop_nxt        = dp_retire_rf_wenb     // uop load enable at WA
                          & dp_retire_rf_wa[`npuarc_GRAD_ADDR_MSB]
                          ;
    wa_rf_wenb1_nxt       = dp_retire_rf_wenb     // gpr load enable at WA
                          & (~(    dp_retire_rf_wa[`npuarc_GRAD_ADDR_MSB] 
                                & dp_retire_rf_wa[`npuarc_RGF_ADDR_MSB]
                             )) 
                          ;

    wa_rf_wa1_nxt         = dp_retire_rf_wa[`npuarc_RGF_ADDR_RANGE]; // get write reg

    wa_rf_wenb1_64_nxt    = dp_retire_rf_64        // select 64-bit write enable
                          ;
    wa_rf_wdata1_lo_nxt   = dmp_dc4_rf_wdata_lo;  // select load data
    wa_rf_wdata1_hi_nxt   = dp_retire_rf_64
                          ? dmp_dc4_rf_wdata_hi   // select upper load data
                          : dmp_dc4_rf_wdata_lo   // duplicate lower data
                          ;
    ca_retire_flags       = { (dmp_scond_zflag & dp_retire_scond), 3'b000 };


    end    

  5'b001??: // case: div/rem retire request, no DMP or vec retire request
    begin
    ca_retire_tag         = div_retire_tag;       // retire DIV unit's tag
    div_retire_ack        = 1'b1;                 // acknowledge retirement
    ca_retire_ack         = 1'b1;                 // retirement is granted
    wa_rf_wenb1_nxt       = dp_retire_rf_wenb;    // conditional writeback
    wa_rf_wdata1_lo_nxt   = div_rf_wdata_lo;      // select DIV/REM result
    wa_rf_wa1_nxt         = dp_retire_rf_wa[`npuarc_RGF_ADDR_RANGE]; // get write reg
    wa_rf_wdata1_hi_nxt   = div_rf_wdata_lo;      // duplicate lower data
    wa_rf_wenb1_64_nxt    = 1'b0;                 // DIV/REM is never 64-bit
    ca_retire_flags       = { div_retire_zero,
                              div_retire_sign,
                              1'b0,
                              div_retire_ovfl };
    end

  5'b00001: // case: EIA retire, no DMP, vec, div/rem or FPU retire request
    begin
    ca_retire_tag         = eia_retire_tag;       // retire EIA unit's tag
    eia_retire_ack        = 1'b1;                 // acknowledge retirement
    ca_retire_ack         = 1'b1;                 // retirement is granted
    wa_rf_wenb1_nxt       = dp_retire_rf_wenb;    // conditional writeback
    wa_rf_wa1_nxt         = dp_retire_rf_wa[`npuarc_RGF_ADDR_RANGE]; // get write reg
    wa_rf_wenb1_64_nxt    = dp_retire_rf_64;      // select 64-bit write enable
    wa_rf_wdata1_lo_nxt   = eia_rf_wdata_lo;      // select EIA result (low)
    wa_rf_wdata1_hi_nxt   = eia_rf_wdata_lo;      // duplicate lower data
    ca_retire_flags       = eia_retire_flags;     // select EIA result bflags


    end
  // default case: in-order LD or SR at CA, and no retirement request 
  //
  default:
    begin
    wa_rf_wa1_nxt         = ca_rf_wa1_r;          // provide destination reg
    
    // Write to port 1 when committing an in-order LD that is not graduating
    // or an SR operation, which guarantees never to request graduation.
    //
    wa_rf_wenb1_nxt       = ca_rf_wenb1_r & ca_pass & (~ca_grad_req)
                          & (~(ca_rf_wuop & ca_rf_wa1_r[`npuarc_RGF_ADDR_MSB]))
                          ;
    wa_rf_wuop_nxt        = ca_rf_wenb1_r & ca_pass & (~ca_grad_req)
                          & ca_rf_wuop
                          ;
    wa_rf_wdata1_lo_nxt   = ca_rf_wdata1_lo;      // in-order LD or SR data
    wa_rf_wdata1_hi_nxt   = ca_rf_wenb1_64_r      // check if LDD result
                          ? dmp_dc4_rf_wdata_hi   // select upper load data
                          : ca_rf_wdata1_lo       // duplicate lower data
                          ;
    wa_rf_wenb1_64_nxt    = ca_rf_wenb1_64_r & ca_pass & (~ca_grad_req);


    end
  endcase

  wa_writes_acc_nxt       = (dp_retire_writes_acc & ca_retire_ack)
                          | (ca_writes_acc_r & ca_pass & ca_cond & (~ca_grad_req))
                          ;

  wa_uopld_status32_nxt   = wa_rf_wuop_nxt
                          & (wa_rf_wa1_nxt == `npuarc_REG_STATUS32)
                          ;

  //==========================================================================
  // Detect a structural hazard on register file write port #1.
  // This hazard requires the Commit stage to stall (see alb_dep_pipe).
  //
  // This happens when there is a retirement occuring at the same time
  // as the commit-stage has a valid in-order write to port #1 that does
  // not itself request graduation.
  //
  ca_wa1_conflict         = ca_retire_ack
                          & (  (ca_rf_wenb1_r & (~ca_grad_req))
                              | ca_sr_op_r
                            )
                          ;
                                
end // block: ca_rf_results_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                         ca_brk_cond;   // Indicate break or halt operation

always @*
begin: ca_commit_evt_PROC

  // Commit-Event Hierarchy
  //
  // commit_inst
  // |
  // +-- commit_raw_evt
  //      |
  //      +-- commit_debug_evt
  //      |
  //      |     Event denoting the commit of a debug instruction.
  //      |
  //      +-- commit_normal_evt
  //      |      |
  //      |      +-- commit_flag_evt
  //      |
  //      +-- commit_uop_evt
  //
  //            Event denoting the commit of a constituent instruction
  //            of a multi-op. The commit of the sequence, and subsequent
  //            irreversible update to the machine state remains denoted by
  //            the assertion of commit_normal_evt on the final instruction
  //            of the sequence.
  //
  //
  commit_inst       =  ca_pass
                    & (~ct_replay)
                    ;

  //
  //
  commit_raw_evt    = commit_inst
                    & (~excpn_restart)
                    ;

  //==========================================================================
  // commit of debug instruction
  //
  commit_debug_evt  = commit_raw_evt
                    & db_active
                    ;


  //==========================================================================
  // COMMIT_UOP_EVT is assert on the commit of the initial (initating)
  // instruction of the multi-op sequence and for all constituent
  // instructions thereafter with the exception of the final,
  // terminal instruction.
  //
  commit_uop_evt    = (    commit_raw_evt
                        &  (ca_uop_active_r | insn_starts_uop)
                        & (~ca_uop_commit_r)
                      )
                    ;

  //==========================================================================
  // COMMIT_NORMAL_EVT denotes the commit of ordinary instruction.
  //
  commit_normal_evt =  commit_raw_evt
                    & (~ca_brk_cond)
                    & (~commit_uop_evt)
                    & (~ca_fragged_r)
                    & (~db_active)
                    ;

  //==========================================================================
  // commit_sleep_evt indicates that one of SLEEP, WEVT or WLFC instruction is 
  // committing, provided the instruction is not single-stepped.
  // This event will put the core to sleep if any other relevant conditions
  // for SLEEP, WEVT or WLFC are also met.
  //
  commit_sleep_evt  = ca_sleep_op_r
                    & commit_normal_evt
                    & (~ar_aux_debug_r[`npuarc_DEBUG_IS])
                    ;
                    
  //==========================================================================
  // ca_wevt_evt indicates a WEVT instruction is committing. This will put
  // the core to sleep unconditionally.
  //
  ca_wevt_evt       = commit_sleep_evt & ca_half_size_r & (!ca_byte_size_r);

  //==========================================================================
  // ca_wlfc_evt indicates a WLFC instruction is committing. This will put
  // the core to sleep if the lock-flag register is set.
  //
  ca_wlfc_evt       = commit_sleep_evt & ca_half_size_r &  ca_byte_size_r
                    & wa_lock_flag_r
                    ;

  //==========================================================================
  // ca_sleep_evt indicates that a SLEEP, WEVT or WLFC instruction is 
  // committing, and provided the instruction is not single-stepped this 
  // event will put the core to sleep.
  // This event is asserted whenever SLEEP or WEVT instructions commit,
  // or when WLFC instructions commit and the lock flag is set to 1.
  //
  ca_sleep_evt      = commit_sleep_evt 
                    & (!ca_half_size_r | (!ca_byte_size_r) | wa_lock_flag_r)
                    ;

  //==========================================================================
  // commit_flag_evt is asserted when a normal instruction commits without
  // graduating for later retirement, and the instruction updates flags,
  // or if a post-commit flag retirement takes place in the current cycle.
  // This signal will be asserted if a flag-setting instruction graduates
  // but has a false condition. This may happen for DIV.F or REM.F.
  // If such instructions appear in the delay-slot of a mispredicted branch,
  // then the pending_flag_upt_r signal will be already asserted, and the
  // commit of the DIV.F or REM.F must assert this signal to clear the
  // pending_flag_upt_r state.
  //
  commit_flag_evt   = (   commit_normal_evt
                        & ca_flag_upt
                        & (~(ca_grad_req & ca_cond))
                      )
                    | (ca_retire_req & ca_retire_ack & (|dp_retire_zncv))
                    ;
  
end // block: ca_commit_evt_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Determine the next architectural PC, as a function of the outcome of the //
// current Commit-stage instruction.                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                         ca_taken_cti; // 1 => valid CA inst is taken CTI

reg                         ca_br_delayed;// delayed branch is taken

wire                        ca_in_dslot;  // CA instr is in a delay-slot
wire                        ca_in_eslot;  // CA instr is in an exec-slot

assign  ca_in_dslot = ar_aux_status32_r[`npuarc_DE_FLAG];
assign  ca_in_eslot = ar_aux_status32_r[`npuarc_ES_FLAG];
assign  int_e_flag  = ar_aux_status32_r[`npuarc_E_FLAG];
assign  int_ie_flag = ar_aux_status32_r[`npuarc_IE_FLAG];

always @*
begin: ar_pc_nxt_PROC

  ca_brk_cond    = ca_brk_op_r                 // (1) break
                 | aps_break                   // (2) breakpoint
                 | aps_halt                    // (3) watchpoint

                 ;
  
  ca_in_deslot  = ca_valid_r
                & (ca_in_dslot | ca_in_eslot)
                ;
                
  ca_br_delayed = (ca_br_taken & ca_dslot_r)  // branch with dslot is taken
                ;
  
  ca_taken_cti  = (ca_br_taken & (~ca_dslot_r)) // branch without dslot is taken
                ;
  
  // ca_branch_evt disables ZOL loop-back
  //
  ca_branch_evt = ca_in_deslot
                | ca_taken_cti
                | ca_rtie_op_r
//                | ca_trap_op_r
                ;
  
  ca_br_evt     = (ca_in_deslot
                | ca_taken_cti)
                & (~db_active_r)
                & (~ca_brk_op_r)
                ;
  
  // Detect any branch or jump (taken or not taken)
  //
  ca_br_or_jmp_all  = ca_pass
                    & ( (~ca_cond & ca_loop_op_r) // LPcc false
                       | ca_bcc_r
                       | ca_jump_r
                       | ca_brcc_bbit_r
                       | ca_rtie_op_r
                       | ca_in_eslot_r
                       | ca_btab_op_r
                      );
  ca_rd_link0    = (ca_rf_ra0_r == 6'h1f)
                 &  ca_link_r;

  // indir branch includes 
  // 1. BI and BIH (target depends on source register)
  // 2. JLI_S and EI_S (target depends on JLI_BASE or EI_BASE registers)
  // 3. RTIE
  // 4. Jump instructions when either of the two register read enable ucode bits
  //    (rf_renb0, rf_renb1) are asserted.
  // 5. A jump that is performed by an instruction within a micro-op sequence.
  //    (exclude int/exc vector address; include implicit branch from vector
  //    address to exc. handler)
  //
  ca_indir_br       =  ca_pass
                    & (  ca_btab_op_r          // 1. BI, BIH
                       | ca_ei_op_r            // 2. EI_S inst
                       | ca_in_eslot           //    EI_S eslot
                       | ca_jli_src0_r         //    JLI_S
                       | ca_rtie_op_r          // 3. RTIE
                       | (  ca_jump_r          // 4. jump
                          & ( ( ca_rf_renb0_r  //   with reg rd en0
                                & (!ca_rd_link0) // exclude jl read link reg
                              )
                             | ca_rf_renb1_r   //   with reg rd en1
                            )
                         )
                       | (  ca_br_or_jmp_all   // 5. jump or br
                          & ca_uop_active_r    //   in uop seq
                         )
                      );


  ar_lp_start   = ar_aux_lp_start_r[`npuarc_PC_RANGE];

  //==========================================================================
  // Calculate the next sequential PC as a function of the current CA-stage
  // PC and the size of the current CA instruction. If the current CA
  // instruction commits in this cycle without performing any control
  // transfer (i.e. taken branch, jump, RTIE, delayed branch, ZOL loop-back),
  // then ar_pc_r will be updated with this value.
  //
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential dont_care carry bit
// spyglass disable_block W164b
  {dont_care, ca_seq_pc_nxt} = ar_pc_r + {28'd0, ca_pc_inc_r}
// leda B_3208 on
// spyglass enable_block W164b
                             ;

  //==========================================================================
  // Select the next value for ar_pc_next, from a prioritized list of possible
  // sources, depending on the outcome and type of the current instruction.
  //
  // (a). When taking an exception or interrupt.
  //      In this case, the exception or interrupt vector will be expected 
  //      as the next ar_pc_r.
  //
  //              -> ar_pc_nxt = excpn_restart_pc
  //
  // (b). When a debug operation is active, the next ar_pc_r value might be 
  //      set by a debug write to PC. As this may be the case, we set
  //      ar_pc_nxt to the result of the CA-stage instruction. 
  //
  //              -> ar_pc_nxt = ca_byp_data0_lo
  //
  // (c). When an instruction commits normally, then several possible values
  //      could be used to update ar_pc_r. These conditions are again in
  //      prioritized order, and are:
  //
  //       1.  Any instruction that halts the CPU, such as FLAG 1 or BRK,
  //           or an instruction that is a non-terminating micro-op from
  //           within a micro-sequence.
  //
  //              -> ar_pc_nxt = ar_pc_r
  //
  //       2.  A normally-committed instruction that is in a delay-slot
  //           or an execution-slot (STATUS32.DE == 1, or STATUS32.ES == 1).
  //
  //              -> ar_pc_nxt = ar_aux_bta_r
  //
  //       3.  A taken control-transfer instruction, without a delay-slot,
  //           including RTIE, EI_S and BI,BIH instructions.
  //
  //              -> ar_pc_nxt = ca_target_r
  //
  //       4.  An implicit loop-closing branch, caused by ar_pc_r == LP_END,
  //           when STATUS32.L == 0 and lp_count != 1.
  //
  //              -> ar_pc_nxt = ar_aux_lp_start_r
  //
  //       5.  None of the above conditions, from (a) thru (c).4.
  //
  //              -> ar_pc_nxt = ca_seq_pc_nxt;
  //
  //
  casez ({    excpn_restart
            ,   1'b0
              | wa_pc_wen
            , ca_brk_cond
            , ca_in_deslot
            , ca_taken_cti
            , ca_zol_lp_jmp
         })
    // -----------------------------------------------------------------------
    // Pattern      Assignment                         // Case   Active signal
    // -----------------------------------------------------------------------
    6'b1?????: ar_pc_nxt = excpn_restart_pc;       // (a) excpn_restart_pc
    6'b01????: ar_pc_nxt = wa_sr_data_r[`npuarc_PC_RANGE];    // (b) DBG SR to PC
    6'b001???: ar_pc_nxt = ar_pc_r;                    // (c).1  ca_brk_cond  
    6'b0001??: ar_pc_nxt = ar_aux_bta_r[`npuarc_PC_RANGE];    // (c).2  ca_in_deslot
    6'b00001?: ar_pc_nxt = ca_target_r;                // (c).3  ca_taken_cti
    6'b000001: ar_pc_nxt = ar_lp_start;                // (c).4  ca_zol_lp_jmp
    default:   ar_pc_nxt = ca_seq_pc_nxt;              // (c).5  None of above
    // -----------------------------------------------------------------------
  endcase

  // A new PC is passed to WA on the commit of a non-multi-op instruction
  // or on an exception.
  //
  ar_pc_pass        = (   commit_normal_evt
                        | wa_pc_wen
                      )
                    ;
end // block: ar_pc_nxt_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Generate the ca_size_r vector from ca_half_size_r, ca_byte_size and      //
// and ca_double_size_r.                                                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_size_PROC

  //==========================================================================
  // CA provides the re-encoded memory operand size field <zz> from the
  // current instruction, for use by the DMP. (00-b, 01-h, 10-w, 11-dw)
  //
  // Logically this is equivalent to:
  //
  //   ca_size_r     = { ((~ca_half_size_r) & (~ca_byte_size_r)),
  //                     (ca_half_size_r | ca_double_size_r)
  //                   };
  //
  casez ({   ca_half_size_r
           , ca_byte_size_r
           , ca_double_size_r
         })
    3'b1??:  ca_size_r = 2'b01; // 16-bit operation
    3'b01?:  ca_size_r = 2'b00; //  8-bit operation
    3'b001:  ca_size_r = 2'b11; // 64-bit operation
    3'b000:  ca_size_r = 2'b10; // 32-bit operation
    default: ca_size_r = 2'b10; // 32-bit operation
  endcase

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// 'alb_status32' module used to derive the next architectural value of     //
// AUX_STATUS32 as a function of the current machine state.                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign  alu_result_zncv_sel =
                              ca_eia_res_valid ? ca_eia_res_flags :
                              alu_result_zncv;

npuarc_alb_status32 u_alb_status32(
  .ar_aux_status32_r          (ar_aux_status32_r       ),
  .ar_aux_user_mode_r         (ar_aux_user_mode_r      ),
  .ar_aux_erstatus_r          (ar_aux_erstatus_r       ),
  .ca_valid_r                 (ca_valid_r              ),
  .ca_pass                    (ca_pass                 ),
  .ca_stall                   (ca_stall                ),
  .ca_src1_r                  (ca_src1_r               ),
  .ca_uop_active_r            (ca_uop_active_r         ),
  .ca_zncv_r                  (ca_zncv_r               ),
  .alu_result_zncv            (alu_result_zncv_sel     ),
  .ca_done_r                  (ca_done_r               ),
  .ca_br_delayed              (ca_br_delayed           ),
  .commit_normal_evt          (commit_normal_evt       ),
  .commit_uop_evt             (commit_uop_evt          ),
  .ca_cmt_brk_evt             (ca_cmt_brk_evt          ),
  .ca_triple_fault_set        (ca_triple_fault_set     ),

  .ca_cmt_sleep_evt           (ca_sleep_evt            ),
  .ca_cond                    (ca_cond                 ),
  .ca_q_cond                  (ca_q_cond               ),
  .ca_cmt_isi_evt             (ca_cmt_isi_evt          ),
  .db_active_r                (db_active_r             ),
  .single_step_active_r       (ar_aux_debug_r[`npuarc_DEBUG_IS]),
  .ar_tags_empty_r            (ar_tags_empty_r         ),
  .ca_finish_sgl_step         (ca_finish_sgl_step),
  .ca_predicate_r             (ca_predicate_r          ),
  .ca_async_halt_evt          (ca_async_halt_evt       ),
  .ca_async_run_evt           (ca_async_run_evt        ),
  .ca_flag_op_r               (ca_flag_op_r            ),
  .ca_byte_size_r             (ca_byte_size_r          ),
  .ca_signed_op_r             (ca_signed_op_r          ),
  .ca_cache_byp_r             (ca_cache_byp_r          ),
  .ca_loop_op_r               (ca_loop_op_r            ),
  .ca_trap_op_r               (ca_trap_op_r            ),
  .ca_z_wen_r                 (ca_z_wen_r              ),
  .ca_n_wen_r                 (ca_n_wen_r              ),
  .ca_c_wen_r                 (ca_c_wen_r              ),
  .ca_v_wen_r                 (ca_v_wen_r              ),
  .ca_ei_op_r                 (ca_ei_op_r              ),
  .ca_0_grad_flags            (1'b0),
  .ca_grad_req                (ca_grad_req             ),
  .ca_retire_flags            (ca_retire_flags         ),
  .dp_retire_zncv             (dp_retire_zncv          ),
  .ca_retire_ack              (ca_retire_ack           ),
  .ca_scond                   (ca_scond                ),
  .wa_sr_data_r               (wa_sr_data_r            ),
  .wa_status32_wen            (wa_status32_wen         ),
  .wa_rf_wdata1_lo_nxt        (wa_rf_wdata1_lo_nxt     ),
  .wa_uopld_status32_nxt      (wa_uopld_status32_nxt   ),
  .wa_debug_wen               (wa_debug_wen            ),
  .excpn_evts                 (excpn_evts              ),
  .int_evts                   (int_evts                ),
  .ca_kflag_op                (ca_kflag_op             ),
  .ca_is_flag                 (ca_is_flag              ),
  .ca_in_kflag                (ca_in_kflag             ),
  .ca_flag_upt                (ca_flag_upt             ),

  .wa_aux_status32_nxt        (wa_aux_status32_nxt     ),
  .wa_aux_uop_flag_pass       (wa_aux_uop_flag_pass    ),
  .wa_aux_flags_pass          (wa_aux_flags_pass       ),
  .wa_aux_status32_pass       (wa_aux_status32_pass    )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @ca_replay_PROC: Instruction replay logic                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_replay_PROC

  // Kill any instruction replay request on the following events
  // (typically the consequence of which is a serializing operation).
  //
  kill_replay            = ar_aux_debug_r[`npuarc_DEBUG_IS]
                         ;

  // Retain strict replay state on commit of a strictly serializing
  // SR instruction, or a KFLAG instruction.
  //
  replay_aux_strict_nxt  = (aux_ca_strict_sr | ca_is_flag | ca_kflag_op)
                         & (   commit_normal_evt
                             | commit_debug_evt
                           )
                         & (~kill_replay)
                         ;

  // Perform an AUX-related instruction replay upon the attempted
  // commit of an instruction after (1) the commit of a strictly
  // serializing AUX register operation, or (2) the commit of a
  // non-serializing AUX register operation which terminate the chain.
  //
  do_aux_replay          = (   replay_aux_strict_r     // (1)
                             | (   replay_aux_serial_r // (2)
///                                  & (~aux_ca_serial_sr & ca_valid_r)
                                 & (~(aux_ca_serial_sr | aux_ca_strict_sr) & ca_valid_r)
                                )
                           )
                         ;

  // Retain serializing state of current LR/SR operation for chaining.
  //
  // (1) New serializing request
  // (2) Preserve until replay is completed
  // (3) 
  //
  replay_aux_serial_nxt  = (
                              (   aux_ca_serial_sr        // (1)
                                & (   commit_normal_evt
                                    | commit_debug_evt
                                  )
                              )
                            | (   replay_aux_serial_r     // (2)
                                & (~wa_restart_r)
                                & (~do_aux_replay)
                              )
                           )
                         & (~kill_replay)                 // (3)
                         ;

  // On the completion of certain epilogue sequences, we are forced to
  // flush the pipeline to ensure that subsequent upstream
  // instructions have been fetched and executed with the correct
  // machine state.
  //
  replay_rtie_nxt        = ca_uop_epil_r
                         & ca_uop_commit_r
                         & commit_normal_evt
                         & (~wa_restart_r)
                         & (~kill_replay)
                         ;

  // If a DIV/REM instruction committed without writing a result
  // because of a div-by-zero status, then we must replay the
  // following instruction. This is because the dependency pip
  // assumes that an instruction with a named destination register
  // will always modify it. However, in the case of a div-by-zero,
  // when the EV_DivZero exception is disabled, the DIV/REM instruction
  // is not permitted to write its destination register. 
  //
 /*
  replay_post_divz_nxt   = ca_div_op_r
                         & div_divz_r
                         & commit_normal_evt
                         & (~wa_restart_r)
                         & (~kill_replay)
                         ;
*/
  // On commit of a SYNC or SLEEP instruction, replay the next instruction to
  // be committed to ensure that it has appropriately captured the
  // correct machine state during execution.
  //
  replay_post_sleep_sync_nxt   = (ca_sync_op_r | ca_sleep_op_r)
                               & commit_normal_evt 
                               & (~wa_restart_r)   
                               & (~kill_replay)    
                               ;                   

  // The instruction in CA shall not commit and will be replayed under
  // the following conditions:
  //
  //   (1) An access to a serializing AUX register.
  //
  //   (2) On the commit of epilogue sequences that require the
  //       serialization of upstream instructions.
  //
  //   (3) On the commit of a DIV or REM instruction for which there
  //       is a divide-by-zero status when EV_DivZero exceptions are
  //       disabled.
  //
  //   (4) On the commit of a SYNC or SLEEP instruction.
  //
  // NOTE: Disallow replay on debug transactions, as such transactions
  // are inherently serializing and therefore do not require this to
  // happen (also, we do not wish to assert an additional WA_RESTART,
  // the implication of which is to restart the IFU).
  //
  ct_replay              = (   do_aux_replay               // (1)
                             | replay_rtie_r               // (2)
//                             | replay_post_divz_r        // (3)
                             | replay_post_sleep_sync_r    // (4)
                           )
                         & (~db_active_r)
                         ;

  //==========================================================================
  // assert ca_iprot_replay when ca_iprot_viol_r is asserted and the current
  // CA instruction is ready to commit. This prevents asserting this 
  // signal if the instruction with ca_iprot_viol_r asserted gets killed
  // before it attempts to fully commit. When ca_iprot_viol_r is asserted,
  // it will prevent commit_inst from being asserted, via the ca_kill 
  // signal. However, the ca_pass_no_iprot signal is asserted when the
  // CA instruction is prevented from passing only by the ca_iprot_viol_r
  // signal, and therefore can be used to qualify the ca_iprot_replay signal. 
  //
  ca_iprot_replay        = ca_pass_no_iprot & ca_iprot_viol_r;
  

end // block: ca_replay_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @ca_uop_active_PROC: Multi-op pipeline interlock logic                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_uop_active_PROC

  //==========================================================================
  //
  kill_uop_active   = wa_restart_r & (~excpn_restart)
                    ;

  //==========================================================================
  //
  insn_starts_uop   = ca_valid_r
                    & (   ca_rtie_op_r
                        | ca_enter_op_r
                        | ca_leave_op_r
                      )
                    ;

  //==========================================================================
  // Signal indicating the start of an interrupt or exception prologue
  // sequence.
  //
  start_prol        =   excpn_restart
                    ;

  //==========================================================================
  // Set UOP_ACTIVE state on valid initiating condition.
  // 1. restart (except for int/excpn_prologue_evt) kills the active UOP 
  // 2. It is executed rtie/enter/leave instruction
  // 3. it is start of prologue
  //
  ca_uop_active_set = (~kill_uop_active)                     // (1)
                    & (   (insn_starts_uop & commit_raw_evt) // (2) 
                        | start_prol                         // (3)
                      )
                    ;

  //==========================================================================
  // Clear UOP_ACTIVE state on terminal/commiting instruction of sequence.
  // restart clears active UOP 
  //
  ca_uop_active_clr = ca_uop_commit_r
                    | wa_restart_r
                    | (dc4_replay & (~start_prol))
                    ;

  //==========================================================================
  // Register demarcating the period over which a multi-op sequence is
  // active in the pipeline (used specifically to hold-off events that
  // would otherwise distrupt the sequence, such as debug events and
  // halts).
  //
  ca_uop_active_nxt = (~kill_uop_active)
                    & (   ( ca_uop_active_set & (~ca_uop_active_r))
                        | (~ca_uop_active_clr &  ca_uop_active_r)
                      )
                    ;

  //==========================================================================
  // Annotation of UOP_ACTIVE state to indicate that current
  // micro-operation is a interrupt-/exception-prologue
  // sequence. Derived specifically to defeat STATUS32.{DE,ES}
  // architectural state before the sequence has committed.
  //
  ca_uop_inprol_nxt = (start_prol & (~ca_uop_inprol_r))
                    | (ca_uop_active_nxt & ca_uop_inprol_r)
                    ;

  //==========================================================================
  // Keep track of micro-op sequences with branch prediction.
  // Only LEAVE_S with opcode bit u[6]==1 is predicted.
  // The other micro-op sequences are not predicted.
  // For micro-op sequences that are predicted, branch prediction signals
  // are asserted by the EXU.
  //
  ca_uop_predictable_nxt  = ca_uop_active_nxt 
                        & (    ca_uop_predictable_r
                            | (   ca_leave_op_r
                                & (ca_br_type_r != 3'd`npuarc_BR_NOT_PREDICTED)
                              )
                          )
                        ;

  //==========================================================================
  // Keep track of an ENTER_S or LEAVE_S (without jump) micro-op sequence.
  //
  ca_uop_enter_nxt  = ca_uop_active_nxt 
                    & (   ca_uop_enter_r 
                        | ca_enter_op_r
                        | (   ca_leave_op_r
                            & (ca_br_type_r == 3'd`npuarc_BR_NOT_PREDICTED)
                          )
                       )
                    ;
/*
  //==========================================================================
  // Pipeline interlock derived from UOP_ACTIVE that becomes asserted
  // on the initial instruction of the sequence.
  //
  ca_uop_active     = (ca_uop_active_set | ca_uop_active_r)
                    ;
*/
  //==========================================================================
  // Update CA-stage uop_seq state, only on the commit of a
  // uop-instruction, or on the commit of a sequence, or when a
  // sequence is terminated early (by a pipeline flush from WA or break).
  //
  ca_uop_state_cg0  = commit_uop_evt
                    | commit_normal_evt
                    | (dc4_replay & ca_uop_active_r) 
                    | excpn_restart
                    | cmt_brk_evt
                    | holdup_excpn_r
                    ;

  //==========================================================================
  // Global reset done indicating that the initial machine reset process has
  // been issued and successfully completed.
  //
  gb_sys_reset_done_nxt  = gb_sys_reset_done_r
                         | (   (~gb_sys_reset_done_r)
                             & ca_uop_commit_r
                             & commit_normal_evt
                           )
                         ;

  //==========================================================================
  // ca_uop_inst indicates whether the Commit-stage instruction is a
  // uop instruction or an instruction that expands into a uop.
  //
  ca_uop_inst     = ca_rtie_op_r
                  | ca_uop_active_r
                  | ca_enter_op_r
                  | ca_leave_op_r
                  ;
  
end // block: ca_uop_active_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @dbg_evt_PROC: Combinatorial process to indentify the commit/retirement  //
// of debugger instructions.                                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: dbg_evt_PROC

  // 'Events' are killed by outstanding previously emitted instruction
  // that invoke post-commit operations (such as TRAP).
  //
  ct_valid          = ct_excpn_trap_r
                    ;


  // A debug instruction result retires on (1) the acknowledgement of
  // a retirement, (2) the commit of a non-load instruction, or (3) the
  // commit of a non-graduating load.
  //
  cmt_dbg_evt       = db_active
                    & (   ca_retire_ack                          // (1)
                        | (   commit_debug_evt
                            & (   (~ca_load_r)                   // (2)
                                | (ca_load_r & (~ca_grad_req))   // (3)
                              )
                          )
                      )
                    ;

  // A BRK instruction is present in CA and would otherwise commit in the
  // current cycle (i.e. the CA-stage is not stalled).
  //
  cmt_brk_evt       = ca_brk_cond    
                    & (
                        ( (aps_break | aps_halt) & ca_valid_r
                        & (~db_active_r)
                        & (~ct_replay) 
                        & (~excpn_restart)
                        )
                      |
                        ( ca_brk_op_r
                        & commit_raw_evt 
                        )
                      )
                    & (~ca_fragged_r)
                    & (~ca_error_branch_r)
                    & (~wa_restart_kill_r)
                    & (~ct_valid)
                    & (   ~ar_aux_status32_r[`npuarc_U_FLAG]
                        |  ar_aux_debug_r[`npuarc_DEBUG_UB]
                      )
                    ;

  // brk inst excluding actionpoint brk/hlt
  //
  ca_cmt_brk_inst   = ca_valid_r
                    & ca_brk_op_r
                    & cmt_brk_evt
                    & (~wa_restart_kill_r)
                    & (~ct_valid)
                    & (   ~ar_aux_status32_r[`npuarc_U_FLAG]
                        |  ar_aux_debug_r[`npuarc_DEBUG_UB]
                      )
                    ;


  // Perform an instruction step the cycle after the commit of a
  // normal-class instruction, but defer when such an instruction
  // invokes post-commit activity that cannot be held-off.
  //
  do_insn_step      = wa_cmt_norm_evt_r
                    & (~ct_valid)
                    ;

  // An Instruction Step Event is asserted on the cycle after the
  // commit of a normal-class instruction when DEBUG.IS is set.
  //
  cmt_isi_evt       = ar_aux_debug_r[`npuarc_DEBUG_IS]
                    & do_insn_step
                    ;

  // Asynchronously set or clear STATUS32.H on a request from the halt
  // management unit.
  //
  ca_async_halt_evt = hlt_do_halt;
  ca_async_run_evt  = hlt_do_unhalt;

end // block: dbg_evt_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_ctrl_PROC

  //==========================================================================
  //
  ca_valid_nxt      = x3_pass
                    ;

  //==========================================================================
  // ca_code_cg0 enables the update of the ca_code_r, ca_zncv_r, ca_pc_inc_r
  // and ca_flag_wr_r registers.
  //
  // ca_code_cg0 is asserted when:
  //
  //  (a). the CA stage is enabled to receive new input, and
  //  (b). either ca_valid_r or ca_valid_nxt (i.e. x3_pass)
  //
  // Condition (b) ensures that the CA ucode vector is updated whenever a
  // new instruction arrives or an exising instruction leaves. It does not
  // clock the ucode vector when it is already empty and nothing is arriving,
  // nor if it is full but not moving on to WA.
  //
  ca_code_cg0     = ca_enable & (ca_valid_r | x3_pass);

  //==========================================================================
  // register update enable signals for data-path inputs at the CA stage
  //
  ca_src0_cg0       = (ca_enable & x3_src0_pass);
  ca_src1_cg0       = (ca_enable & x3_src1_pass);
  ca_res_cg0        = (ca_enable & x3_res_pass);
  ca_target_cg0     = (ca_enable & x3_target_pass);
  ca_mem_addr_cg0   = (ca_enable & x3_addr_pass);

  //==========================================================================
  // register update enable signals for the CA-stage ALU, derived in X3.
  //
  ca_px_cg0         = (ca_enable & x3_add_op_pass);
  ca_alu_code_cg0   = (ca_enable & x3_alu_code_pass);

  //==========================================================================
  // ca_data*_*_pass signals indicate to the WA stage whether each of the
  // result data busses contains data that is ready to pass from CA to WA.
  // These signals are used in the WA stage to enable the input register
  // updates for these values.
  //
  ca_data0_lo_pass  = (   ca_pass
                        & (   ca_rf_wenb0_r
                            | ca_acc_wenb_r
                          )
                      )
                    | commit_debug_evt
                    ;
  
  ca_data1_lo_pass  = (   ca_pass
                        & (   (ca_rf_wenb1_r & (~ca_disable_w1))
                            | ca_sr_op_r
                          )
                      )
                    | ca_retire_ack
                    | commit_debug_evt
                    ;

  ca_data0_hi_pass  = ca_pass 
                    & (   ca_rf_wenb0_64_r
                        | (ca_rf_wenb0_r & ca_rf_wa0_r[0])
                      )
                    ;

  ca_data1_hi_pass  = (   ca_pass 
                        & (~ca_disable_w1)
                        & (   ca_rf_wenb1_64_r
                            | (ca_rf_wenb1_r & ca_rf_wa1_r[0])
                          )
                      )
                    | (   ca_retire_ack
                        & (   dp_retire_rf_64 
                            | (dp_retire_rf_wenb & dp_retire_rf_wa[0])
                          )
                      )
                    ;

end // block: ca_ctrl_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_ucode_PROC

  //==========================================================================
  // Assign the current CA microcode to the outgoing microcode vector prior
  // to modifications that may be needed in this cycle.
  //
  ucode_out                     = ca_code_r[`npuarc_WA_CODE_WIDTH-1:0];

  //==========================================================================
  // Defeat the enable signals for write port 0 if any non-LD instruction
  // graduates without retiring its result.
  // 
  ca_disable_w0                 = ca_grad_req
                                & (   1'b0
                                    | ca_div_op_r
                                    | eia_disable_w0
                                  )
                               ;

  //==========================================================================
  // Defeat the enable signals for write port 1 if any LD instruction
  // graduates without retiring its result.
  // 
  ca_disable_w1                 = ca_grad_req & ca_load_r;

  ucode_out[`npuarc_RF_WENB0_RANGE]    = ca_rf_wenb0_r    & (~ca_disable_w0) & (~ca_brk_cond);
  ucode_out[`npuarc_RF_WENB0_64_RANGE] = ca_rf_wenb0_64_r & (~ca_disable_w0) & (~ca_brk_cond);

  if ((ca_pass == 1'b0) || (ca_cond == 1'b0))
  begin
`include "npuarc_ucode_kill_wa.v"
  end

  // Restore the dslot bit in the microcode to prevent it from getting killed.
  // This is needed to set wa_dslot correctly.
  ucode_out[`npuarc_DSLOT_RANGE] =  ca_code_r[`npuarc_DSLOT_RANGE];

  // Set the next values for wa_writes_acc_r and maybe wa_acc_wenb_r, 
  // and these values must override any squashing of these signals due
  // to not committing the current CA-stage instruction. 
  //
  ucode_out[`npuarc_WRITES_ACC_RANGE]  = wa_writes_acc_nxt;
  ucode_out[`npuarc_ACC_WENB_RANGE]    = wa_acc_wenb_nxt;

  //==========================================================================
  //
  wa_code_nxt  = ucode_out;

end // block: ca_ucode_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to define the commit-stage signalling for LLOCK,   //
// SCOND instructions, and for LPA and LF updates.                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_atomic_PROC

  //==========================================================================
  // Decode an SCOND instruction in the Commit stage, for use in the ALU
  // when selecting dmp_scond_zflag as the next Z-flag result.
  //
  ca_scond      = ca_store_r & ca_locked_r;
  
  //==========================================================================
  // Decode a WLFC instruction in the Commit stage, for use in the dep-pipe
  // when detecting stall conditions with respect to graduated SCOND insns.
  //
  ca_wlfc_op    = ca_sleep_op_r & ca_half_size_r & ca_byte_size_r;
  
  //==========================================================================
  // Define the events that signal the commit of LLOCK and SCOND instructions.
  //
  // wa_lf_set_nxt indidates that the lock flag should be set to 1 as a
  // result of committing an in-order LLOCK instruction. This is also the
  // trigger for updating wa_lpa_r.
  //
  wa_lf_set_nxt  = ca_load_r & ca_locked_r & commit_normal_evt;
  
  // wa_lf_clear_nxt indicates that the lock flag should be cleared as the
  // result of completing an SCOND instruction. This happens in one of two
  // possible cases:
  //
  //  1. when an SCOND instruction commits without requesting graduation,
  //  2. when retiring an SCOND instruction from the graduation buffer, 
  //
  wa_lf_clear_nxt   = (   ca_scond                              // (1)
                        & commit_normal_evt
                        & (~ca_grad_req)
                      )
                    | dp_retire_scond                           // (2)
                    ;
  
  //=========================================================================
  // Define the size of the lock. This is determined by the size of the load 
  // locked
  //
  wa_lf_double_nxt  = (ca_size_r == 2'b11);
  
  //==========================================================================
  // Define the next value of the LPA register. The wa_lf_set_nxt signal
  // indicates when LPA is to be updated.
  //
  wa_lpa_nxt        = ca_phys_addr_r;

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// CA-stage input registers                                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: ca_uop_reg_PROC
  if (rst_a == 1'b1)
  begin
    ca_uop_active_r       <= 1'b0;
    ca_uop_predictable_r  <= 1'b0;
    ca_uop_enter_r        <= 1'b0;
    ca_uop_inprol_r       <= 1'b0;

  end
  else if (ca_uop_state_cg0 == 1'b1)
  begin
    ca_uop_active_r       <= ca_uop_active_nxt;
    ca_uop_predictable_r  <= ca_uop_predictable_nxt;
    ca_uop_enter_r        <= ca_uop_enter_nxt;
    ca_uop_inprol_r       <= ca_uop_inprol_nxt;
  
  end
end // block: ca_uop_reg_PROC

always @(posedge clk or posedge rst_a)
begin: ca_src_regs_PROC
  if (rst_a == 1'b1)
  begin
    ca_src0_r         <= `npuarc_DATA_SIZE'd0;
    ca_src1_r         <= `npuarc_DATA_SIZE'd0;
    ca_res_r          <= `npuarc_DATA_SIZE'd0;
    ca_target_r       <= `npuarc_PC_BITS'd0;
    ca_mem_addr_r     <= `npuarc_ADDR_SIZE'd0;
    ca_p0_r           <= `npuarc_CA_P0_BITS'd0;
    ca_p1_r           <= `npuarc_CA_P0_BITS'd0;
    ca_p2_r           <= `npuarc_CA_P2_BITS'd0;
    ca_p3_r           <= `npuarc_CA_P3_BITS'd0;
    ca_cin_r          <= 1'b0;
    i_or_op_r         <= 1'b0;
    i_and_op_r        <= 1'b0;
    i_xor_op_r        <= 1'b0;
    i_mov_op_r        <= 1'b0;
    i_signed_op_r     <= 1'b0;
    i_src2_mask_sel_r <= 1'b0;
    i_byte_size_r     <= 1'b0;
    i_half_size_r     <= 1'b0;
    i_shift_op_r      <= 1'b0;
    i_left_r          <= 1'b0;
    i_rotate_r        <= 1'b0;
    i_with_carry_r    <= 1'b0;
    i_add_op_r        <= 1'b0;
    i_bit_op_r        <= 1'b0;
    i_mask_op_r       <= 1'b0;
    i_inv_src1_r      <= 1'b0;
    i_inv_src2_r      <= 1'b0;
  end
  else
  begin
    if (ca_src0_cg0 == 1'b1)
      ca_src0_r         <= ca_src0_nxt;
    if (ca_src1_cg0 == 1'b1)
      ca_src1_r         <= ca_src1_nxt;
    if (ca_res_cg0 == 1'b1)
      ca_res_r          <= ca_res_nxt;
    if (ca_target_cg0 == 1'b1)
      ca_target_r       <= ca_target_nxt;
    if (ca_mem_addr_cg0 == 1'b1)
      ca_mem_addr_r     <= x3_mem_addr_r;
    if (ca_px_cg0 == 1'b1)
    begin
      ca_p0_r           <= ca_p0_nxt;
      ca_p1_r           <= ca_p1_nxt;
      ca_p2_r           <= ca_p2_nxt;
      ca_p3_r           <= ca_p3_nxt;
      ca_cin_r          <= ca_cin_nxt;
    end
    if (ca_alu_code_cg0 == 1'b1)
    begin
      i_or_op_r         <= ca_code_nxt[`npuarc_OR_OP_RANGE];
      i_and_op_r        <= ca_code_nxt[`npuarc_AND_OP_RANGE];
      i_xor_op_r        <= ca_code_nxt[`npuarc_XOR_OP_RANGE];
      i_mov_op_r        <= ca_code_nxt[`npuarc_MOV_OP_RANGE];
      i_signed_op_r     <= ca_code_nxt[`npuarc_SIGNED_OP_RANGE];
      i_src2_mask_sel_r <= ca_code_nxt[`npuarc_SRC2_MASK_SEL_RANGE];
      i_byte_size_r     <= ca_code_nxt[`npuarc_BYTE_SIZE_RANGE];
      i_half_size_r     <= ca_code_nxt[`npuarc_HALF_SIZE_RANGE];
      i_shift_op_r      <= ca_code_nxt[`npuarc_SIMPLE_SHIFT_OP_RANGE];
      i_left_r          <= ca_code_nxt[`npuarc_LEFT_SHIFT_RANGE];
      i_rotate_r        <= ca_code_nxt[`npuarc_ROTATE_OP_RANGE];
      i_with_carry_r    <= ca_code_nxt[`npuarc_WITH_CARRY_RANGE];
      i_bit_op_r        <= ca_code_nxt[`npuarc_BIT_OP_RANGE];
      i_add_op_r        <= ca_code_nxt[`npuarc_ADD_OP_RANGE];
      i_mask_op_r       <= ca_code_nxt[`npuarc_MASK_OP_RANGE];
      i_inv_src1_r      <= ca_code_nxt[`npuarc_INV_SRC1_RANGE];
      i_inv_src2_r      <= ca_code_nxt[`npuarc_INV_SRC2_RANGE];
    end
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: ca_ctrl_regs_PROC
  if (rst_a == 1'b1)
  begin
    ca_code_r       <= `npuarc_CA_CODE_WIDTH'd0;
    ca_zncv_r       <= 4'd0;
    ca_pc_inc_r     <= `npuarc_PC_INC_BITS'd0;
    ca_flag_wr_r    <= 1'b0;
  end
  else if (ca_code_cg0 == 1'b1)
  begin
    ca_code_r       <= ca_code_nxt;
    ca_zncv_r       <= ca_zncv_nxt;
    ca_pc_inc_r     <= ca_pc_inc_nxt;
    ca_flag_wr_r    <= ca_flag_wr_nxt;
  end
end // block: ca_ctrl_regs_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @ca_replay_regs_PROC: Sequential process to retain state for             //
// instructions to be replayed.                                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: ca_replay_regs_PROC
  if (rst_a == 1'b1)
  begin
    replay_aux_serial_r  <= 1'b0;
    replay_aux_strict_r  <= 1'b0;
    replay_rtie_r        <= 1'b0;
//    replay_post_divz_r   <= 1'b0;
    do_aux_replay_r       <= 1'b0;
    replay_post_sleep_sync_r   <= 1'b0;
  end
  else // if (commit_normal_evt == 1'b1)
  begin
    replay_aux_serial_r        <= replay_aux_serial_nxt;
    replay_aux_strict_r        <= replay_aux_strict_nxt;
    replay_rtie_r              <= replay_rtie_nxt;
    do_aux_replay_r       <= do_aux_replay;
 //   replay_post_divz_r         <= replay_post_divz_nxt;
    replay_post_sleep_sync_r   <= replay_post_sleep_sync_nxt;
  end
end // block: ca_replay_regs_PROC

always @(posedge clk or posedge rst_a)
begin: gb_sys_reset_done_reg_PROC
  if (rst_a == 1'b1)
    gb_sys_reset_done_r  <= 1'b0;
  else
    gb_sys_reset_done_r  <= gb_sys_reset_done_nxt;
end // block: gb_sys_reset_done_reg_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_pct_PROC

  // Insts that are Branch or Jump and includes Link
  ca_br_jmp_op          = ca_link_r
                        & ( ca_bcc_r
                          | ca_jump_r
                          )
                        ;

end // block: ca_pct_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output Assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
assign ca_pref             = ca_pref_r & (~ca_sex_r) & (~ca_cache_byp_r);           
assign ca_prefw            = ca_pref_r & (~ca_sex_r) &   ca_cache_byp_r;           
assign ca_pre_alloc        = ca_pref_r &   ca_sex_r  & (~ca_cache_byp_r);       
assign ca_pref_l2          = 1'b0;         

assign ca_zncv_wen_r       = {ca_z_wen_r,ca_n_wen_r,ca_c_wen_r,ca_v_wen_r};
assign ca_sex_r            = ca_signed_op_r;

assign ca_br_target        = ca_target_r;

assign ca_lp_end_nxt       = ca_target_r;

assign wa_cmt_norm_evt_nxt = commit_normal_evt;
assign wa_cmt_uop_evt_nxt  = commit_uop_evt;
assign wa_cmt_flag_evt_nxt = commit_flag_evt;
assign ca_cmt_dbg_evt      = cmt_dbg_evt;
assign ca_cmt_norm_evt     = commit_normal_evt;
assign ca_cmt_uop_evt      = commit_uop_evt;
assign ca_cmt_brk_evt      = cmt_brk_evt;
assign ca_cmt_isi_evt      = cmt_isi_evt;


assign ca_aux_cond         = ca_cond & (~cmt_brk_evt);   // Kill if inst killed but CA_PASS is high
assign ca_q_cond           = q_cond;

assign sel_byp_acc         = ~ca_acc_wenb_r;

assign ca_loop_evt         = commit_inst & ca_cond & ca_loop_op_r;
assign ca_lp_lpcc_evt         = commit_inst & ca_loop_op_r;
                             // lp and lpcc instructions

assign wa_rf_wenb0_64_nxt  = ucode_out[`npuarc_RF_WENB0_64_RANGE];
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// The ca_aux_s32_stall signal is used by LR operations at X3 to stall    //
// X3 in the case of an LR from STATUS32 that would miss the pending      //
// DE-bit update from the current Commit-stage instruction.               //
//                                                                        //
// The hazard is triggered in the Commit stage when:                      //
//  (1) flags may be updated by a flag setting operations                 //
//  (2) flags may be updated by kflag instruction                         //
//  (3) the CA instruction has a delay slot                               //
//  (4) a valid CA instruction is in a delay-slot (will clear DE later)   //
//  (5) flag update pending                                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

assign ca_aux_s32_stall    = ca_flag_wr_r                   // (1)
                           | ca_flag_op_r                   // (2)
                           | ca_dslot_r | ca_ei_op_r        // (3)
                           | (ca_in_deslot & ca_valid_r)    // (4)
                           | ar_zncv_upt_r                  // (5)
                           ;


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// RTC Non-Atomic invalidates the RTC high read operation if an           //
// interrupt or exception occurs during the period between LRs.           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

assign rtc_na              = excpn_evts[`npuarc_INTEVT_ENTER]
                           | int_evts[`npuarc_INTEVT_ENTER]
                           ;


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Delay RTIE operations until an appropriate number of cycles have       //
// elapsed since the most recent SR instruction.                          //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg  [2:0]                     sr_count;
wire [2:0]                     sr_count_nxt;
wire                           unused_carry;
assign {unused_carry, sr_count_nxt} = sr_count + (|sr_count);
always @(posedge clk or posedge rst_a) 
begin: sr_count_PROC
  if (rst_a == 1'b1) begin
    sr_count <= 3'd0;
  end
  else begin
    if (ca_sr_op_r) begin
      sr_count <= 3'd3;
    end
    else begin
      sr_count <= sr_count_nxt;
    end
  end
end

assign ca_sr_stall_rtie = (|sr_count) & ca_rtie_op_r;


//a state machine to control pipeline stall after commited interrupt epilogue sequence with context load from memory
//
wire ca_int_load;
assign  ca_int_load   = ca_valid_r & ca_load_r & ca_uop_inst_r; 
wire ca_int_load_vld;
assign  ca_int_load_vld = ca_pass & ca_int_load;
reg [1:0] int_load_state_r, int_load_state_nxt;
reg int_load_active_nxt;
parameter INT_LOAD_IDLE  = 2'b00;
parameter INT_LOAD_START = 2'b01;
parameter LEAVE_LOAD_START = 2'b10;
always @(*)
begin: int_epi_load_PROC
  int_load_state_nxt = int_load_state_r;
  int_load_active_nxt = int_load_active;
  ca_uop_is_leave = 1'b0;
  case (int_load_state_r)
    INT_LOAD_IDLE: begin
     if (ca_valid_r & ca_leave_op_r && ca_pass) begin
       int_load_state_nxt = LEAVE_LOAD_START;
     end
     if (ca_int_load_vld) begin
       int_load_state_nxt = INT_LOAD_START;
       int_load_active_nxt = 1'b1;
     end
    end
    INT_LOAD_START: begin
      if (ar_tags_empty_r & (!ca_load_r)) begin
        int_load_state_nxt = INT_LOAD_IDLE;
        int_load_active_nxt = 1'b0;
      end
    end
    LEAVE_LOAD_START: begin
      ca_uop_is_leave = 1'b1;
      if (ca_uop_commit_r || wa_restart_r) begin
        int_load_state_nxt = INT_LOAD_IDLE;
      end
    end
    default: begin
      int_load_state_nxt = int_load_state_r;
    end
  endcase
end

always @(posedge clk or posedge rst_a)
begin: int_load_reg_PROC
  if (rst_a == 1'b1) begin
    int_load_state_r <= INT_LOAD_IDLE;
    int_load_active  <= 1'b0;
  end
  else begin
    int_load_state_r <= int_load_state_nxt;
    int_load_active  <= int_load_active_nxt;
  end
end

reg ca_uop_is_leave_r;

always @(posedge clk or posedge rst_a)
begin: ca_uop_is_leave_reg_PROC
  if (rst_a == 1'b1) begin
    ca_uop_is_leave_r <= 1'b0;
  end
  else begin
    ca_uop_is_leave_r <= ca_uop_is_leave;
  end
end

assign rtt_leave_uop_cmt = ca_uop_is_leave_r & ca_uop_commit_r;

//LEAVE_s, ENTER_S are 16bit. keep the info until the uop senquense finished
always @(posedge clk or posedge rst_a)
begin: uop_starter_is_16bit_PROC
  if (rst_a == 1'b1) begin
    uop_starter_is_16bit   <= 1'b0;
  end
  else begin
    if (ca_uop_active_set & (ca_enter_op_r | ca_leave_op_r)) begin
      uop_starter_is_16bit <= 1'b1;
    end
    else if (kill_uop_active | ca_uop_active_clr) begin
      uop_starter_is_16bit <= 1'b0;
    end
  end
end
 

assign ca_is_16bit  = ca_is_16bit_r
                    | uop_starter_is_16bit & ca_uop_commit_r
                    ;

assign cmt_ei_evt   = ca_ei_op_r & commit_normal_evt;
assign rtt_dmp_retire      = dmp_retire_req & dmp_retire_ack & dmp_retire_is_load 
                           & (wa_rf_wenb1_nxt 
                             | wa_rf_wenb1_64_nxt
                             ); 
assign rtt_ca_pref         = ca_pref | ca_prefw | ca_pref_l2 | ca_pre_alloc
                           | (ca_load_r & (ca_rf_wa1_r == 'd62) & (~ca_grad_req))
                           ;

assign rtt_dmp_null_ret    = dmp_retire_req & dmp_retire_ack & dmp_retire_is_load
                           & (~rtt_dmp_retire);

assign rtt_ca_scond        = ca_scond;


endmodule
