// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2014 Synopsys, Inc. All rights reserved.
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
//----------------------------------------------------------------------------
//
// @f:alb_excpn_pipe
//
// Description:
// @p
//     This module implements the logic used to manage the processing of
//   exception and interrupt events.
// @e
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o alb_excpn_pipe.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_excpn_pipe (
// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,                // clock signal
  input                       rst_a,              // reset signal

  ////////// Debug Interface /////////////////////////////////////////////////
  //
  input                       db_active,          //
  output                      x3_db_exception,    // Debug instr
  output reg                  ca_db_exception_r,  // debug instruction caused exception
  output                      ca_db_exception,    // debug exception qualified

  ////////// Halt Control Interface //////////////////////////////////////////
  //
  input                       hlt_issue_reset,    //
  output                      excpn_hld_halt,     //
  output reg                  ca_triple_fault_set,   // error fetching dbl flt vec

  ////////// Machine Architectural state /////////////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_DATA_RANGE]    ar_aux_intvbase_r,  // AUX_INTVBASE
  input      [`npuarc_DATA_RANGE]    ar_aux_status32_r,  // AUX_STATUS32
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                       ar_tags_empty_r,    // grad buffer is empty  
// spyglass enable_block W240
  input      [`npuarc_DATA_RANGE]    ar_aux_debug_r,     // AUX_DEBUG
  input      [`npuarc_DATA_RANGE]    ar_aux_bta_r,       // AUX_BTA
  input                       pipe_block_ints,    // Halt blocks interrupts  
// leda NTL_CON13C on    
  input                       ar_aux_user_mode_r, // arch. user mode
  input      [`npuarc_PC_RANGE]      ar_pc_r,            //
  input      [`npuarc_PC_RANGE]      ar_pc_nxt,          //

  input      [`npuarc_DATA_RANGE]    ar_aux_irq_act_r,   // (arch.) IRQ_ACT_AUX

  ////////// Halt related state //////////////////////////////////////////////
  //

  ////////// Speculative Architectural state /////////////////////////////////////
  // The only difference from arch. status32 is the U_FLAG bit that cab be cleared
  // during uop sequence
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_DATA_RANGE]    sp_aux_status32_r,  // (spec.) STATUS32_AUX
// leda NTL_CON13C on
  input      [`npuarc_PFLAG_RANGE]   wa_aux_status32_r,  // flags held during prologue sequence


  ////////// AUX write interface /////////////////////////////////////////////
  //
  input      [`npuarc_DATA_RANGE]    wa_sr_data_r,       // WA SR write data
  input                       wa_erstatus_wen,    // WA ERSTATUS wen
  input                       wa_eret_wen,        // WA ERET wen
  input                       wa_erbta_wen,       // WA ERBTA wen
  input                       wa_ecr_wen,         // WA ECR wen
  input                       wa_efa_wen,         // WA EFA wen
  input                       wa_efae_wen,        // WA EFA EXT wen
  //
  input      [`npuarc_PC_RANGE]      wa_pc,              // WA PC

  ////////// Machine Architectural state (retained by EXCPN_PIPE) ////////////
  //
  output reg [`npuarc_DATA_RANGE]    ar_aux_erstatus_r,  // aux. ERSTATU32
  output reg [`npuarc_DATA_RANGE]    ar_aux_eret_r,      // aux. ERET
  output reg [`npuarc_DATA_RANGE]    ar_aux_ecr_r,       // aux. ECR
  output reg [`npuarc_DATA_RANGE]    ar_aux_erbta_r,     // aux. ERBTA
  output reg [`npuarc_DATA_RANGE]    ar_aux_efa_r,       // aux. EFA
  output reg [`npuarc_DATA_RANGE]    ar_aux_efae_r,      // aux. EFA EXT

  ////////// WA-stage Pipeline restart signal ////////////////////////////////
  //
  input                       x2_restart_r,       // X2 (spec.) restart
  input                       wa_restart_r,       // WA (arch.) restart
  input                       hlt_restart,        // Halt restart request
  input                       wa_restart_kill_r,  // WA kills CA
  input                       wa_sleep,
  input                       gb_sys_sleep_r,
  input                       dmp_queue_empty,
  input                       iexcpn_discarded,
  input                       st_instrs_discarded,

  ////////// ucode Interface to Pipeline /////////////////////////////////////
  //
  input                       x2_valid_r,         //
  input                       x2_uop_inst_r,      //
  input                       x2_invalid_instr_r, //
  input                       x2_illegal_operand_r,//
  input                       x2_jump_r,          //
  input                       x2_has_limm_r,      //
  input                       x2_rtie_op_r,       //
  input                       x2_leave_op_r,       //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  Not used in all config
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                       al_uop_epil,         //uop epil sm starts
// spyglass enable_block W240
// leda NTL_CON13C on

  input                       al_uop_has_limm,     // micro-op has LIMM
  input                       da_uop_u7_pcl,    // LEAVE_S u7 pcl bit
  input                       x2_rel_branch_r,    //
  input                       x2_kernel_op_r,     // X2 required kernel priv.
  input                       x2_rgf_link_r,      // X2 accesses ILINK
  input                       x2_brk_op_r,        // X2 is BRK
  input                       x2_multi_op_r,      // X2 is multi-op
  input                       x2_btab_op_r,       // X2 is BI{,H,C}

  input                       x2_in_dslot_r,      //
  input                       x2_ei_op_r,
  input                       x2_in_eslot_r,
  input                       x2_loop_op_r,
  input                       x2_zol_ill_seq_r,   // illegal inst (last ZOL)

  input                       x3_valid_r,         // valid insn at X3
  input                       x3_uop_inst_r,      //
  input                       x3_load_r,          //
  input                       x3_store_r,         //

  input                       x3_pref_r,          //
  
  input   [`npuarc_ADDR_RANGE]       x3_mem_addr_r,      //

  input                       x2_load_r,          //
  input                       x2_store_r,         //
  input   [1:0]               x2_size_r,          // X2-stage LD/ST size (ZZ)
  input                       x2_pref_r,
  input                       x2_locked_r,
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input   [`npuarc_ADDR_RANGE]       x2_mem_addr_r,      //
// leda NTL_CON13C on
  input                       x3_predicate_r,     // 
  input                       x3_iprot_viol_r,    // iprot viol at X3
  input                       x3_div_op_r,        // X3 insn is DIV

  ////////// Exception interface to Divide unit //////////////////////////////
  //
  input                       div_divz_r,         // Division by zero attempted

  ////////// Privilege Exception interface to APEX ///////////////////////////
  //
  input                       eia_x2_is_eia_instr,// x2 opcode is eia
  input                       eia_x2_kernel_cc,   // eia cond code is kernel 
  input                       eia_x2_kernel_cr,   // eia core reg is kernel 
  input   [5:0]               eia_x3_kernel_param,// ECR param for eia viol

  ////////// Instruction Issue handshake interface with the IFU //////////////
  //
  // leda NTL_CON13C off
  // LMD: non driving port range
  // LJ:  handshake interface
  input                       al_pass,            //
  input                       al_exception,       //
  input   [`npuarc_FCH_EXCPN_RANGE]  al_excpn_type,      //
  input [`npuarc_FCH_EINFO_RANGE]    al_excpn_info,      //

  input                       ca_uop_inprol_r,    // 
  input                       ca_uop_active_set,
  input                       dc3_excpn,          // DMP precise memory err exc
  input  [`npuarc_DMP_EXCPN_RANGE]   dc3_excpn_type,     // exception type
  input  [7:0]                dc3_excpn_code,     // cause code
  // leda NTL_CON13C on
  ////////// Action points interface /////////////////////////////////////////
  //
  input                       aps_hit_if,         // Hit on I-fetch AP
  input                       aps_hit_mr,         // Hit on Mem or aux-reg AP
  input      [`npuarc_APNUM_RANGE]   aps_active,         // Identity of active hit
  input                       aps_pcbrk,          // PC Break AP
  output reg                  ca_ap_excpn_r,      // To Aux Reg AP Exception
  output                      excpn_in_prologue,  // To AP

  ////////// AUX CTRL Interface //////////////////////////////////////////////
  //
  input                       x3_aux_unimpl_r,    //
  input                       x3_aux_illegal_r,   //
  input                       x3_aux_k_ro_r,      //
  input                       x3_aux_k_wr_r,      //

  ////////// DMP Exception and Replay Interface //////////////////////////////
  //
  input                       ca_replay,          //
  input                       ca_dc4_replay,      //
  input                       dc4_excpn,          //
  input [`npuarc_PADDR_RANGE]        dc4_excpn_mem_addr, //
                                                  //
  input [`npuarc_DMP_EXCPN_RANGE]    dc4_excpn_type,     //
  input                       dc4_excpn_user_mode_r,// DMP excpn privilege
// spyglass disable_block W240
// SMD: input declared but not used
// SJ:  unused in some configs
  input   [`npuarc_ADDR_RANGE]       ca_mem_addr_r,      // Mem Addr (CA)
// spyglass enable_block W240

  ////////// TLB Exceptions ///////////////////////////////////////////////////
  //
  input                       x3_lr_op_r,         // (x3) aux_write
  input                       x3_sr_op_r,         // (x3) aux_write
  input                       aux_mmu_ren_r,      // (X3) Aux MMU Select
  input [4:0]                 aux_mmu_raddr_r,    // (X3) Aux Address
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  input [`npuarc_DATA_RANGE]         x3_src0_r,          // (x3) aux write data
  // leda NTL_CON13C on
  input [`npuarc_ADDR_RANGE]         dmp_dc3_dtlb_efa,
  input                       dc3_dtlb_miss_excpn_r,
  input                       dc3_dtlb_ovrlp_excpn_r,
  input                       dc3_dtlb_protv_excpn_r,
  input                       dc3_dtlb_ecc_excpn_r,
  input                       al_ifu_err_nxtpg,
  input                       da_in_dslot_r,
  input                       da_orphan_dslot_r,
  input                       sa_link_r,

  output                      ca_tlb_miss_excpn,
  output [`npuarc_PD0_VPN_RANGE]     ca_tlb_miss_efa,
  output                      ca_m_chk_excpn,
  input  [`npuarc_PC_RANGE]          ca_seq_pc_nxt,      // next seq. PC at CA
  input                       x3_mpu_iprotv_r,    //
  input                       x3_mpu_dprotv_r,    //
  input [`npuarc_DATA_RANGE]         x3_mpu_efa_r,       //
  output reg                  ca_mpu_excpn_r,     // MPU Exception
  input                       x3_sc_protv_r,      //
  input [`npuarc_DATA_RANGE]         x3_sc_efa_r,        //


  ////////// Ucode inputs from the Pipeline (proper) /////////////////////////
  //
  input                       ca_valid_r,         // CA-stage validity
  input                       ca_trap_op_r,       //
  input                       ca_rtie_op_r,       //
  input                       ca_cmt_norm_evt,    // Normal instruction Commit
  input                       ca_cmt_uop_evt,     // UOP instruction Commit
  input                       ca_uop_commit_r,    // UOP last instruction
  input                       ca_byte_size_r,     //
  input                       ca_cmt_isi_evt,     // Commit of Insn.Step evt.
  input                       ct_replay,          // Post-Commit replay
  input                       ca_load_r,          // ca inst does load 
  input                       ca_store_r,         // ca inst does store
  input                       ca_sr_op_r,         // ca inst is sr
  input                       ca_lr_op_r,         // ca inst is lr 

// leda NTL_CON13C off
// LMD: non driving port
// LJ:  not all bits are used
  input      [`npuarc_DATA_RANGE]    ca_src1_r,          // Trap operand
// leda NTL_CON13C on
  input                       ca_uop_active_r,    // UOP instruction is active at CA that includes
                                                  // 1. start of prol to enter
                                                  // 2. start of rtie/enter/leave to exit

  ////////// Control Inputs from Dependency Pipeline /////////////////////////
  //
  input                       da_uop_busy_r,      // 
  input                       da_kill,            // DA stage is to be killed
  input                       da_enable,          // DA is able to receive input
  input                       da_pass,            // DA instruction ready to go
  input                       da_holdup,          // DA Stall (AL data invalid)
  input                       sa_kill,            // SA stage is to be killed
  input                       sa_enable,          // SA is able to receive input
  input                       sa_pass,            // SA instruction ready to go
  input                       x1_kill,            // X1 stage is to be killed
  input                       x1_enable,          // X1 is able to receive input
  input                       x1_pass,            // X1 instruction ready to go
  input                       x2_kill,            // X2 stage is to be killed
  input                       x2_enable,          // X2 is able to receive input
  input                       x2_pass,            // X2 instruction ready to go
  input                       x3_kill,            // X3 stage is to be killed
  input                       x3_enable,          // X3 is able to receive input
  input                       x3_pass,            // X3 instruction ready to go
  input                       ca_enable,          // CA is able to receive input
  input                       ca_pass,            // CA instruction ready to go
  input                       ca_kill,            // CA stage is to be killed

  ////////// Control Inputs from Prediction Pipeline /////////////////////////
  //
  input                       x1_in_dslot_r,      //
  output                      x2_fa0_transl,
  input                       x2_error_branch_r,  // disables exceptions
  input                       x3_error_branch_r,  // disables exceptions
  input                       ca_in_deslot,       // CA insn is in D or E slot
  input                       ca_zol_lp_jmp,      // CA insn jumps to LP_START
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input     [`npuarc_DATA_RANGE]     ar_aux_lp_start_r,  // LP_START aux register
// leda NTL_CON13C on

  ////////// Interrupt Interface /////////////////////////////////////////////
  //
  input                       irq_req,            //
  input      [7:0]            irq_num,            //
  input      [`npuarc_IRQLGN_RANGE]  irq_w,              //
  input                       irq_preempts,       //
  output reg [`npuarc_IRQLGN_RANGE]  irq_ack_w_r,        //

  output     [`npuarc_IRQN_RANGE]    cpu_accept_irq,     //
  output reg                  cpu_irq_select,     //
  output                      irq_ack,            //
  output     [7:0]            irq_ack_num,        //
  output     [`npuarc_DATA_RANGE]    ca_irq_act_nxt,     //
  output     [`npuarc_INTEVT_RANGE]  int_evts,           //
  output reg                  sp_kinv_r,          //
  output reg                  int_rtie_replay_r,  //
  output                      int_ilink_evt,      //
  input                       al_uop_sirq_haz,    //
  input                       int_load_active,    //
  output                      int_preempt,        //


  ////////// Exception Interface /////////////////////////////////////////////
  //
  output reg                  in_dbl_fault_excpn_r, // In double fault
  output reg [`npuarc_INTEVT_RANGE]  excpn_evts,         //
  output reg                  excpn_in_prologue_r,//
  output reg                  excpn_exit_evt,     // Excption RTIE executed
  output                      holdup_excpn_nxt,
  output reg                  holdup_excpn_r,

  output reg                  mem_excpn_ack_r,    //

  ////////// Pipeline flush/restart control interface ////////////////////////
  //
  output reg                  da_ifu_exception_r, // IFU fault
  output reg                  da_ifu_err_nxtpg_r, // IFU inst on next page
  output reg                  x2_excpn_stall,     // stall X2 in corner cases
  output reg                  ct_excpn_trap_r,    // Post-Commit Trap
  output reg                  ct_excpn_trap_nxt,  // TRAP in CA
  output reg                  excpn_restart,      //
  output reg [`npuarc_PC_RANGE]      excpn_restart_pc,   //
  output reg                  wa_restart_vec_r,   //
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  output reg [`npuarc_WA_RCMD_RANGE] wa_restart_cmd_r    //
// leda NTL_CON32 on
);

// @excpn_reset_PROC:
//
reg                      fsm_rst_cg0;        // Reset FSM state enable
reg [3-1:0]              fsm_rst_nxt;        // Reset FSM next state
reg                      excpn_reset_nxt;    //

// @x2_excpn_detect_PROC:
//
reg                      do_single_step;     //
reg                      aps_override_excpn; // AP Override Exception
reg                      x2_kill_excpn;      //
reg                      x2_kill_ifu_excpn;  // kill IFU excpns at X2
reg                      x2_is_cti;          //
reg                      x2_disallow_cti;    // Illegal dSlot sequence
reg                      x3_instr_err_nxt;   //
reg                      x3_instr_seq_nxt;   //
reg                      x3_seq_err_dslot_limm_nxt;

reg                      x2_is_invalid_brk;  // X2 is BRK in user-mode
reg                      x3_priv_viol_nxt;   //
reg                      x3_eia_priv_viol_nxt;      //
reg                      x3_eia_kernel_cc_viol_nxt; //

// @x3_aux_priv_PROC:
//
reg                      x3_aux_priv_viol;   // AUX. register violation
reg                      x3_aux_instr_err;   // Illegal AUX. access

// @x3_excpn_detect_PROC:
//
reg [`npuarc_X3_EXCPN_GRP_RANGE] x3_will_raise_excpn;//
reg                      x3_priv_viol;       //
reg                      x3_eia_priv_viol;   //
reg                      x3_instr_err;       //
reg [`npuarc_X3_EXCPN_GRP_RANGE] x3_take_excpn;      //
reg                      x3_take_db_excpn;   // Exception during Debug
// @x3_excpn_qual_PROC:
//
reg                      in_excpn_mode;
reg                      dc4_bus_mem_err_ae_q;
reg                      aps_hit_mr_ae_q;

reg                      ca_fch_excpn_nxt;
reg                      ca_fch_excpn_r;
reg                      ca_fchvec_viol;      // Fetch Vector violation

reg                      x3_non_exist_dmem;  //
reg                      x3_span_multi_dmem; //
reg                      dc4_ecc_int_merr;   //
reg                      dc4_bus_mem_err;     //

wire                     x3_mmu_inval_cmd_excpn;
reg                      dc3_dtlb_miss_excpn;
reg                      dc3_dtlb_protv_excpn;
reg                      dc3_dtlb_ovrlp_excpn;
wire                     ca_ecr_dtlb_miss;    // excpn cause
wire                     ca_ecr_itlb_miss;
wire                     ca_itlb_excpn;       // any itlb excpn (ca)

wire [`npuarc_PC_RANGE]         ca_itlb_fault_pc;        // PC of actual instr which had fault
wire [`npuarc_ADDR_RANGE]       ca_itlb_fault_pc_plus1;  // 31:0
wire [`npuarc_PD0_VPN_RANGE]    ca_itlb_fault_vpn_plus1; // 30:N

// leda NTL_CON13A off
// LMD: unused carry bit
// LJ:  can be ignored
wire                     ca_itlb_fault_vpn_carry; // crossing 2G transl mem boundary
// leda NTL_CON13A on
wire [`npuarc_ADDR_RANGE]       ca_itlb_efa;
reg                      x3_mpu_excpn;        // Exception is MPU
reg                      ca_mpu_will_excpn_r; // If Excpn is MPU
reg                      x3_ap_excpn;        // If Exception is AP
reg                      ca_ap_will_excpn_r; // If Exception is AP
reg                      x3_pc_excpn;        //
reg                      ca_excpn_reset_nxt; //
reg [7:0]                ca_ecr_vec_num_nxt; //
reg [7:0]                ca_ecr_cs_code_nxt; //
reg [7:0]                ca_ecr_param_nxt;   //
reg                       ca_efa_en_nxt;
reg [`npuarc_DATA_RANGE]         ca_efa_nxt;         //
reg [`npuarc_DATA_RANGE]         ca_efae_nxt;        //

// @ca_excpn_detect_PROC:
//
reg                      valid_alignment;    //
reg                      x3_alignment_viol_nxt;//
reg                      x3_alignment_viol_r;//
  
// @ca_excpn_detect_PROC:
//
reg                      ca_will_raise_excpn;//
reg                      ca_kill_excpn;      // Kill Exception
reg                      take_excpn;         //
reg                      take_trap;          //
reg                      take_int;           //
reg [7:0]                ecr_vec_num;        //
reg [7:0]                ecr_cs_code;        //
reg [7:0]                ecr_param;          //
reg                      trap_type;          //
reg                      ca_restart_vec;     //
reg [`npuarc_WA_RCMD_RANGE]     ca_restart_cmd;     //
reg                      ca_efa_dbl_fault;



reg                      ca_pkill_evt;       // prologue kill event 
wire                     ct_rtie_nopp_r;     //rtie with nopp 
wire [7:0]               irq_num_nopp_r;     //nopp_r irq_num
wire [`npuarc_IRQLGN_RANGE]     irq_w_nopp_r;       //nopp_r irq_w
reg  [7:0]               irq_num_muxed;      //use irq_num_nopp_r for ct_rtie_nopp_r
reg  [`npuarc_IRQLGN_RANGE]     irq_w_muxed;        //use irq_w_nopp_r for ct_rtie_nopp_r
reg                      int_qual;           //qualified interrupt request

// @excpn_regs_upt_PROC:
//
reg                      excpn_regs_cg0;     //
reg                      excpn_status_cg0;   //
reg                      ecr_regs_cg0;       //
reg                      aux_erstatus_cg0;   //
reg                      aux_eret_cg0;       //
reg                      aux_erbta_cg0;      //
reg                      aux_ecr_cg0;        //
reg                      aux_efa_cg0;        //
reg                      aux_efae_cg0;       //


// @ca_excpn_evts_PROC:
//
reg                      excpn_prologue_evt;
reg                      excpn_enter_evt;
reg                      excpn_epilogue_evt;

// @ca_excpn_region_PROC
//
reg                      excpn_in_prologue_nxt;
reg                      excpn_in_epilogue_nxt;

// @fch_excpn_ctrl_PROC:
//
reg                      da_cg0;
reg                      sa_cg0;
reg                      x1_cg0;
reg                      x2_cg0;
reg                      x3_cg0;
reg                      ca_cg0;
reg                      ca_db_cg0;
reg                      wa_cg0;

reg                      da_ifu_exception_nxt;
reg                      sa_ifu_exception_nxt;
reg                      x1_ifu_exception_nxt;
reg                      x2_ifu_exception_nxt;

reg                      x3_itlb_ecc_excpn_nxt;
reg                      x3_itlb_ovrlp_excpn_nxt;
reg                      x3_itlb_miss_excpn_nxt;
reg                      x3_itlb_protv_excpn_nxt;

reg                      x3_pgl_protv_viol_nxt;
reg                      x3_pgm_protv_viol_nxt;

reg                      x3_pgl_protv_fwd_nxt;
reg                      x3_pgm_protv_fwd_nxt;

reg                      x3_pgl_protv_viol_r;
reg                      x3_pgm_protv_viol_r;

reg                      x3_illegal_operand_r;

reg                      ca_pgl_protv_viol_r;
reg                      ca_pgm_protv_viol_r;

reg                      x3_ifberr_excp_nxt;
reg                      x3_ifaerr_excp_nxt;
reg                      x3_ifimerr_excp_nxt;

reg [`npuarc_X3_EXCPN_GRP_RANGE] ca_exception_nxt;
reg                      wa_restart_vec_nxt;
reg [`npuarc_WA_RCMD_RANGE]     wa_restart_cmd_nxt;

// @fch_excpn_regs_PROC:
//
reg                      sa_ifu_exception_r;
reg                      x1_ifu_exception_r;
reg                      x2_ifu_exception_r;

reg                      x3_itlb_ecc_excpn_r;
reg                      x3_itlb_ovrlp_excpn_r;
reg                      x3_itlb_miss_excpn_r;
reg                      x3_itlb_protv_excpn_r;

reg                      ca_itlb_ecc_excpn_r;
reg                      ca_itlb_ovrlp_excpn_r;
reg                      ca_itlb_protv_excpn_r;

reg                      x3_ifberr_excp_r;
reg                      x3_ifaerr_excp_r;
reg                      x3_ifimerr_excp_r;

reg                      x2_exchange;
reg                      x2_uop_unaligned;

reg                      x3_instr_err_r;
reg                      x3_instr_seq_r;
reg                      x3_seq_err_dslot_limm_r;
reg                      x3_priv_viol_r;
reg                      x3_eia_priv_viol_r;
reg                      x3_eia_kernel_cc_viol_r;
reg                      x3_div_divz;

reg [`npuarc_X3_EXCPN_GRP_RANGE] ca_exception_r;

reg [`npuarc_FCH_EXCPN_RANGE]   da_excpn_type_r;
reg [`npuarc_FCH_EXCPN_RANGE]   sa_excpn_type_r;
reg [`npuarc_FCH_EXCPN_RANGE]   x1_excpn_type_r;
reg [`npuarc_FCH_EXCPN_RANGE]   x2_excpn_type_r;

reg [`npuarc_FCH_EINFO_RANGE]   da_excpn_info_r;
reg [`npuarc_FCH_EINFO_RANGE]   sa_excpn_info_r;
reg [`npuarc_FCH_EINFO_RANGE]   x1_excpn_info_r;
reg [`npuarc_FCH_EINFO_RANGE]   x2_excpn_info_r;
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Not all bits used
reg [`npuarc_FCH_EINFO_RANGE]   x3_excpn_info_r;
reg [`npuarc_FCH_EINFO_RANGE]   ca_excpn_info_r;
  // leda NTL_CON32 on
// *_ifu_err_nxtpg_r : Instruction in word 1 irrespective of IFU error
reg                      sa_ifu_err_nxtpg_r;
reg                      x1_ifu_err_nxtpg_r;
reg                      x2_ifu_err_nxtpg_r;
reg                      x3_ifu_err_nxtpg_r;
reg                      ca_ifu_err_nxtpg_r;

wire                     da_fwd_itlb_excpn2sa;
reg                      x1_fwd_itlb_excpn2sa;
reg                      x2_fwd_itlb_excpn2sa;
reg                      x3_fwd_itlb_excpn2sa;
reg                      ca_fwd_itlb_excpn2sa;

wire                     da_fwd_protv_excpn2sa;
reg                      x1_fwd_protv_excpn2sa;
reg                      x2_fwd_protv_excpn2sa;

reg [`npuarc_FCH_EINFO_RANGE]   x1_fwd_excpn_info_r;
reg [`npuarc_FCH_EINFO_RANGE]   x2_fwd_excpn_info_r;

reg                      ca_excpn_reset_r;
reg [7:0]                ca_ecr_vec_num_r;
reg [7:0]                ca_ecr_cs_code_r;
reg [7:0]                ca_ecr_param_r;
reg                      ca_efa_en;
reg [`npuarc_DATA_RANGE]        ca_efa_r;
reg [`npuarc_DATA_RANGE]        ca_efae_r;

// @excpn_arch_regs_PROC:
//
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [`npuarc_PFLAG_RANGE]       aux_erstatus_r;
// leda NTL_CON32 on
reg [`npuarc_PC_RANGE]          aux_eret_r;
reg [`npuarc_PC_RANGE]          aux_erbta_r;
reg                      aux_ecr_p_r;
reg                      aux_ecr_u_r;
reg                      iexcpn_discarded_nxt;
reg                      iexcpn_discarded_r;
reg                      st_instrs_discarded_r;
reg                      st_instrs_discarded_nxt;
reg [7:0]                aux_ecr_vec_r;
reg [7:0]                aux_ecr_code_r;
reg [7:0]                aux_ecr_param_r;
reg [`npuarc_DATA_RANGE]        aux_efa_r;
reg [`npuarc_DATA_RANGE]        aux_efae_r;

// @excpn_region_regs_PROC:
//
reg                      excpn_in_cg0;
reg                      excpn_in_epilogue_r;

// @excpn_arch_PROC:
//
reg                      override_sr;
reg [`npuarc_PFLAG_RANGE]       aux_erstatus_nxt;
reg [`npuarc_PC_RANGE]          aux_eret_nxt;
reg [`npuarc_PC_RANGE]          aux_erbta_nxt;
reg                      aux_ecr_p_nxt;
reg                      aux_ecr_u_nxt;
reg [7:0]                aux_ecr_vec_nxt;
reg [7:0]                aux_ecr_code_nxt;
reg [7:0]                aux_ecr_param_nxt;
reg [`npuarc_DATA_RANGE]        ca_aux_efa_comp;
reg [`npuarc_DATA_RANGE]        aux_efa_nxt;
reg [`npuarc_DATA_RANGE]        ca_aux_efae_comp;
reg [`npuarc_DATA_RANGE]        aux_efae_nxt;

// @excpn_reset_regs_PROC:
//
reg [2:0]                fsm_rst_r;
reg                      excpn_reset_r;

// @uop_epil_active_PROC
reg                      uop_epil_active_r;
reg                      uop_excpn_status,uop_dmp_empty;

 wire x3_sc_protv_q = x3_sc_protv_r 
                    & !( excpn_evts[`npuarc_INTEVT_ENTER] 
                       | ca_trap_op_r)
                    ;

wire excpn_barrier;

assign excpn_barrier =  ( (~ar_aux_status32_r[`npuarc_EIH_FLAG]) |
                          ( (dmp_queue_empty | uop_excpn_status) & 
                            (ar_aux_status32_r[`npuarc_EIH_FLAG]) ) );

assign holdup_excpn_nxt = (ca_will_raise_excpn | ca_trap_op_r) & (~excpn_barrier);
always @(posedge clk or posedge rst_a)
begin
    if(rst_a)
        holdup_excpn_r <= 1'b0;
    else if(take_int)
        holdup_excpn_r <= 1'b0;
    else
        holdup_excpn_r <= holdup_excpn_r ? (~excpn_barrier) : holdup_excpn_nxt;
end

always @(posedge clk or posedge rst_a)
begin
    if(rst_a)
        uop_excpn_status <= 0;
    else if (take_excpn)
        uop_excpn_status <= 0;
    else if(ca_will_raise_excpn & (ca_uop_active_r))
        uop_excpn_status <= uop_dmp_empty;
    else if (ca_uop_commit_r)
        uop_excpn_status <= 0;
end

always @( posedge clk or posedge rst_a )
begin
    if(rst_a)
        uop_dmp_empty <= 0;
    else if(ca_uop_active_set)
        uop_dmp_empty <= dmp_queue_empty;
    else if(ca_uop_commit_r)
        uop_dmp_empty <= 0;
end

// Check for invalid cmd being written (sr) to MMU cmd reg
//
parameter [`npuarc_AUX_REG_RANGE]  AUX_ADDR_MMU_CMD = `npuarc_TLB_CMD_AUX;
parameter JTLB_CMD_WRITE    = 6'h1;  // Write
parameter JTLB_CMD_READ     = 6'h2;  // Read
parameter JTLB_CMD_GETIX    = 6'h3;  // Get index
parameter JTLB_CMD_PROBE    = 6'h4;  // Probe
parameter JTLB_CMD_WRITENI  = 6'h5;  // Write (no invalidation of utlbs)
parameter JTLB_CMD_IVUTLB   = 6'h6;  // Invalidate utlbs
parameter JTLB_CMD_INSERT   = 6'h7;  // Insert entry (and forward to utlb)
parameter JTLB_CMD_INSERTJ  = 6'hA;  // Insert entry (jtlb only)
parameter JTLB_CMD_DELETE   = 6'h8;  // Delete entry
parameter JTLB_CMD_DELETEIS = 6'h9;  // Delete entry (ignore share bits)

assign x3_mmu_inval_cmd_excpn =
             ~ar_aux_status32_r[`npuarc_U_FLAG]
           & x3_sr_op_r 
           & (~x3_lr_op_r) 
           & (~(x3_instr_err | x3_instr_seq_r))
           & (~x3_illegal_operand_r) 
           & aux_mmu_ren_r 
           & (aux_mmu_raddr_r == AUX_ADDR_MMU_CMD[4:0])
           // decode only non-reserved mmu cmd bits
           & (x3_src0_r[`npuarc_MMU_CMD_CMD_RANGE] != JTLB_CMD_WRITE   )
           & (x3_src0_r[`npuarc_MMU_CMD_CMD_RANGE] != JTLB_CMD_READ    )
           & (x3_src0_r[`npuarc_MMU_CMD_CMD_RANGE] != JTLB_CMD_GETIX   )
           & (x3_src0_r[`npuarc_MMU_CMD_CMD_RANGE] != JTLB_CMD_PROBE   )
           & (x3_src0_r[`npuarc_MMU_CMD_CMD_RANGE] != JTLB_CMD_WRITENI )
           & (x3_src0_r[`npuarc_MMU_CMD_CMD_RANGE] != JTLB_CMD_IVUTLB  )
           & (x3_src0_r[`npuarc_MMU_CMD_CMD_RANGE] != JTLB_CMD_INSERT  )
           & (x3_src0_r[`npuarc_MMU_CMD_CMD_RANGE] != JTLB_CMD_INSERTJ )
           & (x3_src0_r[`npuarc_MMU_CMD_CMD_RANGE] != JTLB_CMD_DELETE  )
           & (x3_src0_r[`npuarc_MMU_CMD_CMD_RANGE] != JTLB_CMD_DELETEIS)
           ;

// If a delay slot instruction has an itlb exception and it is not
// an orphaned delay slot, its exception must be transferred to
// it's parent branch (including excpn type and nxtpg flag)
//
assign da_fwd_itlb_excpn2sa = da_in_dslot_r 
                         &  sa_link_r
                         & (~da_orphan_dslot_r)
                         &  da_ifu_exception_r
                         & (~sa_ifu_exception_r)
                         ;

// If a delay slot instruction is not an orphaned delay slot, its 
// itlb execute permission information must be transferred to
// it's parent branch at the X2 stage, when STATUS32.U is always
// valid. At that point itlb protection violations are detected.
//
assign da_fwd_protv_excpn2sa = da_in_dslot_r 
                         &  sa_link_r
                         & (~da_orphan_dslot_r)
                         & (~da_ifu_exception_r)
                         & (~sa_ifu_exception_r)
                         ;

// Even if (a non-orphanded) delay slot's itlb exception has been
// transferred to it's parent branch, the EFA must reflect the actual
// instruction [fragment] address that experienced the itlb fault
//  (1) branch with dslot taking excep but actual fault was dslot (nxt seq pc)
//  (2) itlb fault on current instruction
//
assign  ca_itlb_fault_pc = ca_fwd_itlb_excpn2sa ?
                             ca_seq_pc_nxt : // (1)
                             ar_pc_r;        // (2)
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential carry bit
// leda B_3200 off
// LMD: Unequal length operand in bit/arithmetic operator 
// LJ:  add a single bit with zero extension is intentional
// Check if itlb fault was in the next page due to inst spanning page boundary
// calc page number of page after faulting instr PC page
//
assign {ca_itlb_fault_vpn_carry, ca_itlb_fault_vpn_plus1} = 
                      (ca_itlb_fault_pc[`npuarc_PD0_VPN_RANGE] + 1'b1);
// leda B_3208 on
// leda B_3200 on
assign  ca_itlb_fault_pc_plus1 = {1'b0,  // ca_itlb_efa_carry,
                       ca_itlb_fault_vpn_plus1,
                       `npuarc_MMU_POF_SZ0_WIDTH'd0};

// faulting inst may span MMU page boundary 
//    i. ITLB excep occured at next page address (efa is start of next page)
//    ii.ITLB excep occured at [PC] page address (efa is ar_pc_r)
//
  assign ca_itlb_nxtpg  = (ecr_vec_num == `npuarc_EV_PROT_V)
                    ? ( (~ca_pgl_protv_viol_r)
                      & ca_pgm_protv_viol_r)
                    : ca_ifu_err_nxtpg_r
                    ;

  assign  ca_itlb_efa = (ca_itlb_nxtpg == 1'b1)   // (3b)
                      ? ca_itlb_fault_pc_plus1         //   i.
                      : {ca_itlb_fault_pc, 1'b0}       //   ii.
                      ;



///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// Combinatorial process to manage the assertion of initial machine reset.   //
// Notably, this is the only exception that may be initiated internally      //
// in the absence of external stimulii.                                      //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

parameter RESET_IDLE            = 3'b000;
parameter RESET_HALTED          = 3'b001;
parameter RESET_DO_RESTART      = 3'b010;
parameter RESET_WAIT            = 3'b011;
parameter RESET_RUN             = 3'b100;

always @*
begin: excpn_reset_PROC

  // The reset state machine remains active until the reset process has
  // completed, then it is disabled for the remainder of execution.
  //
  fsm_rst_cg0  = (fsm_rst_r != RESET_RUN)
               ;

  // Simple state-machine to manage the transition out of reset.
  //
  case (fsm_rst_r)
    RESET_IDLE:
      fsm_rst_nxt   = RESET_HALTED;

   RESET_HALTED:
     // Wait until machine has been unhalted before issuing restart
     //
       fsm_rst_nxt  = hlt_issue_reset ? RESET_DO_RESTART : fsm_rst_r;

   RESET_DO_RESTART:
     // Issue restart to initiate the IFU and start the machine
     //
     fsm_rst_nxt    = RESET_WAIT;

   RESET_WAIT:
       fsm_rst_nxt  = ca_uop_commit_r ? RESET_RUN : fsm_rst_r;

   RESET_RUN:
     fsm_rst_nxt    = RESET_RUN;

   default:
     fsm_rst_nxt    = fsm_rst_r;

  endcase

  // Issue a pipeline restart on the transition in to the RUN state.
  //
  excpn_reset_nxt        = (fsm_rst_nxt == RESET_DO_RESTART)
                         ;

end // block: excpn_reset_PROC

  reg x2_leave_pcl;

always @*
begin: x2_excpn_detect_PROC

  // Kill IFU exceptions at X2 if this X2 instruction is killed by a
  // downstream instruction (or an older instruction at X2).
  //
  x2_kill_ifu_excpn      = x2_kill;
  
  // Kill any pending upstream exceptions when the pipeline is being
  // flushed, or when a multi-op sequence is active in X2
  // or when there is an error_branch
  //
  x2_kill_excpn          = ((wa_restart_r & (~x2_in_dslot_r)) 
                            | (x2_uop_inst_r & ar_aux_status32_r[`npuarc_AE_FLAG])
                            | x2_error_branch_r
                           )
                         ;
                         
  // Check if there is a LEAVE_S with jump instr
  //
  x2_leave_pcl = 1'b0;
  x2_leave_pcl = x2_leave_op_r & (da_uop_u7_pcl == 1);

  // The instruction in X2 is a control transfer instruction.
  //
  x2_is_cti              = x2_rtie_op_r
                         | x2_jump_r
                         | x2_rel_branch_r
                         | x2_btab_op_r
                         | x2_leave_pcl
                         ;

  // The state of X2 is such that a control transfer instruction must
  // be disallowed. At CTI is disallowed at X2 if the DE or ES flags
  // are set in the architectural STATUS32 register. The X2 stage
  // will stall, if there is a CTI in a delay slot, until those flags
  // are up-to-date.
  //
  x2_disallow_cti        = ~(x3_valid_r | ca_valid_r)
                         & (  ar_aux_status32_r[`npuarc_DE_FLAG]
                            | ar_aux_status32_r[`npuarc_ES_FLAG]
                           )
                         ;

  // Stall the X2 instruction if it is a CTI, and it was issued in
  // the delay-slot of another CTI. The stall continues until the
  // parent CTI is committed. When the stall condition is resolved,
  // the architecturally-committed value for STATUS32.DE will 
  // indicate whether the X2 instruction is actually in a dynamic
  // delay slot.
  // Also trigger an exception if the instruction in the delay slot
  // of a taken branch has a LIMM or a multi-op like ENTER_S/LEAVE_S.
  // Therefore, stall to wait for the branch to commit to be able to
  // decide if we're in the delay slot of a taken branch.
  //
  x2_excpn_stall         = (x2_is_cti 
                            | x2_has_limm_r
                            | x2_multi_op_r
                            | x2_ei_op_r
                          )
                         & x2_in_dslot_r
                         & (x3_valid_r | ca_valid_r)
                         & (~x2_error_branch_r)
                         ;

  // Detect an instruction error condition, to be passed onto X3.
  //
  x3_instr_err_nxt       = (~x2_kill_excpn)
                         & (   x2_invalid_instr_r
                             | x2_illegal_operand_r
                           )
                         & (~db_active)
                         ;

  // An instruction sequence error occurs on the following conditions:
  //
  //    (1) A CTI instruction is located in a D-/E-slot or otherwise
  //        in a location where it is disallowed.
  //
  //    (2) An instruction present in a 'D-SLOT' with a LIMM.
  //        An E-slot is allowed to have a LIMM.
  //
  //    (3) A branch/jump with delay slot, or an EI_S instruction,
  //        appears in the last instruction position of a zero-overhead
  //        loop.
  //
  //    (4) The instruction is a multi-op, which is specifically disallowed
  //        within a E-/D-SLOT context.
  //
  x3_instr_seq_nxt       =  x2_valid_r
                         & (~x2_kill_excpn)
                         & (~db_active)
                         & (   (x2_is_cti     & x2_disallow_cti)  // (1)
                             | (x2_in_dslot_r      // (2)
                                & ( x2_has_limm_r
                                  )
                                & x2_disallow_cti)
                             | x2_zol_ill_seq_r                   // (3)
                             | (x2_multi_op_r & x2_disallow_cti)  // (4)
                             | (x2_in_dslot_r & x2_ei_op_r     
                                & x2_disallow_cti)
                             | (x2_in_eslot_r
                                & ( x2_ei_op_r
                                    | x2_is_cti
                                    | x2_loop_op_r
                                    | x2_multi_op_r
                                  )
                               )
                           )
                         ;

  x3_seq_err_dslot_limm_nxt =  ar_aux_status32_r[`npuarc_DE_FLAG]
                            &  x2_has_limm_r;

  // A BRK raises a priviledge violation exception outside of
  // kernel-mode except when the DEBUG.UB (user-mode break) bit has
  // been set.
  //
  x2_is_invalid_brk      = x2_valid_r
                         & x2_brk_op_r
                         & ar_aux_status32_r[`npuarc_U_FLAG]
                         & (~ar_aux_debug_r[`npuarc_DEBUG_UB])
                         ;

  // An instruction in X2 raises a priviledge exception when
  // attempting to access a kernel-mode register when the machine is
  // operating in user-mode.
  //
  //    (1) The current instruction requires kernel-level priviledges
  //        to commit.
  //    (2) The instruction references ILINK.
  //    (3) A break instruction in the absence of DEBUG.UB
  //    (4/5) Allow if Interrupt Prologue/Epilogue UOP
  //
  x3_priv_viol_nxt       =  x2_valid_r
                         & (~x2_kill_excpn)
                         & ar_aux_status32_r[`npuarc_U_FLAG]
                         & (~db_active)
                         & (   x2_kernel_op_r                    // (1)
                             | x2_rgf_link_r                     // (2)
                             | x2_is_invalid_brk                 // (3)
                           )
                         & (~int_evts[`npuarc_INTEVT_INPROL])           // (4)
                         & (~int_evts[`npuarc_INTEVT_INEPIL])           // (5)
                         ;

  x3_eia_priv_viol_nxt   =  x2_valid_r
                         & (~x2_kill_excpn)
                         & ar_aux_status32_r[`npuarc_U_FLAG]
                         & (
                            (x2_kernel_op_r & eia_x2_is_eia_instr) |
                             eia_x2_kernel_cc |
                            (eia_x2_kernel_cr & (~x2_rgf_link_r))
                           )
                         & (~int_evts[`npuarc_INTEVT_INPROL])           // (4)
                         & (~int_evts[`npuarc_INTEVT_INEPIL])           // (5)
                         ;

  x3_eia_kernel_cc_viol_nxt =
                             x2_valid_r
                         & (~x2_kill_excpn)
                         &   ar_aux_status32_r[`npuarc_U_FLAG]
                         &   eia_x2_kernel_cc
                         & (~int_evts[`npuarc_INTEVT_INPROL])           // (4)
                         & (~int_evts[`npuarc_INTEVT_INEPIL])           // (5)
                         ;

end // block: x2_excpn_detect_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @x3_aux_priv_PROC: combinatorial process to calculate X3 aux. register   //
// privileges.                                                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: x3_aux_priv_PROC

  // AUX access priviledge violation
  //
  x3_aux_priv_viol       = x3_valid_r
                         & (ar_aux_status32_r[`npuarc_U_FLAG] & (!x3_uop_inst_r))
                         & (~db_active)
                         & (   x3_aux_k_ro_r
                             | x3_aux_k_wr_r
                           )
                         ;

  // Attempted access to unimplemented or illegal AUX. address.
  //
  x3_aux_instr_err       = x3_valid_r
                         & (   1'b0
                             | x3_aux_unimpl_r
                             | (x3_aux_illegal_r
                                & (~db_active)
                                )
                           )
                         ;

end // block: x3_aux_priv_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Qualify Exceptions prior to prority arbitration                          //
// Some exceptions are ignored when in exception mode                       //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
//
always @*
begin: x3_excpn_qual_PROC

  in_excpn_mode          = 1'b0
                         | ar_aux_status32_r[`npuarc_AE_FLAG]
                         | excpn_in_prologue_r
                         ; 

  dc4_bus_mem_err_ae_q   = dc4_bus_mem_err 
                         & ((~in_excpn_mode) | ar_aux_status32_r[`npuarc_EIH_FLAG])
                         ;

  aps_hit_mr_ae_q        = aps_hit_mr
                         & (~in_excpn_mode)
                         ;

end // block: x3_excpn_qual_PROC



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial process to calculate X3 stage exceptions before the final  //
// exception is enacted upon in CA.                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: x3_excpn_detect_PROC

  x3_will_raise_excpn    = `npuarc_X3_EXCPN_GRP_BITS'd0;
  x3_pc_excpn            = 1'b0;
  x3_mpu_excpn           = 1'b0;
  x3_ap_excpn            = 1'b0;

  ca_excpn_reset_nxt     = 1'b0;
  ca_ecr_vec_num_nxt     = 8'd0;
  ca_ecr_cs_code_nxt     = 8'd0;
  ca_ecr_param_nxt       = 8'd0;
  ca_efa_en_nxt          = 1'b0;
  ca_efa_nxt             = `npuarc_DATA_SIZE'd0;
  ca_efae_nxt            = `npuarc_DATA_SIZE'd0;
  ca_fch_excpn_nxt       = 1'b0;

  x3_priv_viol           = (x3_aux_priv_viol | x3_priv_viol_r)
                         & (x3_predicate_r)
                         & (~x3_instr_err_r)
                         & (~x3_eia_priv_viol_r)
                         ;

  x3_eia_priv_viol       = (x3_eia_priv_viol_r)
                         & (x3_predicate_r | x3_eia_kernel_cc_viol_r)
                         & (~x3_instr_err_r)
                         ;

  x3_instr_err           = ( x3_aux_instr_err
                           & x3_predicate_r
                           & (~x3_instr_err_r)
                           )
                         | x3_instr_err_r
                         ;

  x3_non_exist_dmem      = dc3_excpn
                         & (dc3_excpn_type == `npuarc_DMP_MEM_ERROR)
                         & (dc3_excpn_code == `npuarc_ECC_DMP_UNPOP_MEM)
                         ;

  x3_span_multi_dmem     = dc3_excpn
                         & (dc3_excpn_type == `npuarc_DMP_MEM_ERROR)
                         & (dc3_excpn_code == `npuarc_ECC_DMP_SP_MULT_MEM)
                         ;
  dc3_dtlb_miss_excpn    =  dc3_dtlb_miss_excpn_r 
                          & (x3_load_r | x3_store_r)
                          & (~x3_pref_r)
                          ;
  dc3_dtlb_protv_excpn   =  dc3_dtlb_protv_excpn_r
                          & (x3_load_r | x3_store_r)
                          & (~x3_pref_r)
                          ;
  dc3_dtlb_ovrlp_excpn   =  dc3_dtlb_ovrlp_excpn_r
                          & (x3_load_r | x3_store_r)
                          & (~x3_pref_r)
                          ;
 
  dc4_ecc_int_merr       = dc4_excpn
                         & (dc4_excpn_type == `npuarc_DMP_ECC_ERROR)
                         ;
                         

  dc4_bus_mem_err         = dc4_excpn
                         & (dc4_excpn_type == `npuarc_DMP_MEM_ERROR)
                         ;

  // (4) Enter clears DZ Flag
  x3_div_divz            = x3_valid_r
                         & x3_div_op_r
                         & x3_predicate_r
                         & (~x3_instr_err_r)
                         & div_divz_r
                         & ar_aux_status32_r[`npuarc_DZ_FLAG]
                         & (~ca_uop_inprol_r)          // (4)
                         ;

  // leda W226 off
  // LMD: Case select expression is constant
  // LJ:  A constant select expression is required in this case
  // leda W225 off
  // LMD: Case item expression is not constant
  // LJ:  A non-constant case-itme expression is required in this case
  //

  case (1'b1)

  // Priority 1: Reset
  //
  excpn_reset_r: 
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_RST]  = 1'b1;

    ca_excpn_reset_nxt   = 1'b1;
    ca_ecr_vec_num_nxt   = `npuarc_EV_RESET;
  end

  // Priority 2: Machine Check, double fault (detected / prioritized in ca stage)
  //

  // Priority 3: Machine Check, Fatal TLB Error
  //
  x3_itlb_ovrlp_excpn_r:
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_TLB_ERR] = 1'b1;
    ca_ecr_vec_num_nxt  = `npuarc_EV_M_CHECK;
    ca_ecr_cs_code_nxt  = 8'd1;
    ca_ecr_param_nxt    = 8'd0;
    ca_fch_excpn_nxt    = 1'b1;
  end

  dc3_dtlb_ovrlp_excpn: // use x3 version
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_TLB_ERR] = 1'b1;
    ca_ecr_vec_num_nxt  = `npuarc_EV_M_CHECK;
    ca_ecr_cs_code_nxt  = 8'd1;
    ca_ecr_param_nxt    = 8'd0;
    ca_efa_en_nxt       = 1'b1;
    ca_efa_nxt          = `npuarc_DATA_SIZE'd0
                        | dmp_dc3_dtlb_efa
                        ;
  end


  // Priority 4: Interrupt (detected / prioritized in ca stage)
  //


  // Priority --(21): Memory Error - External Bus Error (on data access)
  //
  dc4_bus_mem_err_ae_q: 
  begin

    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_IMPRCS]  = 1'b1;

    ca_ecr_vec_num_nxt   = `npuarc_EV_MEM_ERR;
    ca_ecr_cs_code_nxt   = `npuarc_ECC_DMP_BUS_ERR;
    ca_ecr_param_nxt [0] = dc4_excpn_user_mode_r;
    x3_pc_excpn          = dc4_excpn;

    ca_efa_en_nxt        = 1'b1;
    ca_efa_nxt           = dc4_excpn_mem_addr[`npuarc_DATA_RANGE];
    ca_efae_nxt[7:0]     = dc4_excpn_mem_addr[`npuarc_PADDR_MSB:`npuarc_DATA_SIZE];

  end

  // Priority --(22): Actionpoint Watchpoint
  //
  aps_hit_mr_ae_q: 
  begin

    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_IMPRCS]  = 1'b1;

    ca_ecr_vec_num_nxt   = `npuarc_EV_PRIV_V;
    ca_ecr_cs_code_nxt   = `npuarc_ECC_AP_HIT;
    ca_ecr_param_nxt[`npuarc_APNUM_RANGE] = aps_active;
    x3_pc_excpn          = 1'b1;
    x3_ap_excpn          = 1'b1;
  end




  // Priority 5: ITLB Miss
  //
  x3_itlb_ecc_excpn_r:  // 5a
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI] = 1'b1;
    ca_ecr_vec_num_nxt   = `npuarc_EV_M_CHECK;
    ca_ecr_cs_code_nxt  = 8'd2;
    ca_ecr_param_nxt    = 8'd0;
    ca_fch_excpn_nxt    = 1'b1;
  end
  
  x3_itlb_miss_excpn_r:  // 5b
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI] = 1'b1;
    ca_ecr_vec_num_nxt  = `npuarc_EV_ITLB_MISS;
    ca_ecr_cs_code_nxt  = `npuarc_ECC_ITLB_FAULT;
    ca_ecr_param_nxt    = 8'd0;
    ca_fch_excpn_nxt    = 1'b1;
  end


  // Priority 6a: ITLB Fault - Protection Violation
  //
  x3_itlb_protv_excpn_r:
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI] = 1'b1;
    ca_ecr_vec_num_nxt  = `npuarc_EV_PROT_V;
    ca_ecr_cs_code_nxt  = `npuarc_ECC_ITLB_FAULT;
    ca_ecr_param_nxt    = 8'd8;
    ca_fch_excpn_nxt    = 1'b1;
  end


  // Priority 6b: MPU Fault - Protection Violation
  //
  x3_mpu_iprotv_r: 
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI]  = 1'b1;
    x3_mpu_excpn         = x3_mpu_iprotv_r;

    ca_ecr_vec_num_nxt   = `npuarc_EV_PROT_V;
    ca_ecr_cs_code_nxt   = `npuarc_ECC_ITLB_FAULT;
    ca_ecr_param_nxt     = 8'h00
                         | 8'h04
                         ;
    ca_fch_excpn_nxt     = 1'b1;

    ca_efa_en_nxt        = 1'b1;
    ca_efa_nxt           = `npuarc_DATA_SIZE'd0
                         | x3_mpu_efa_r
                         ;

  end


  // Priority 7a: Memory Error (Instruction Fetch Memory Error, ext. bus error)
  //
  x3_ifberr_excp_r: 
  begin

    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI]  = 1'b1;

    ca_ecr_vec_num_nxt   = `npuarc_EV_MEM_ERR;
    ca_ecr_cs_code_nxt   = `npuarc_ECC_IF_EXT_MEM;
    ca_ecr_param_nxt [0] = ar_aux_status32_r[`npuarc_U_FLAG];
    ca_fch_excpn_nxt    = 1'b1;

  end

  // Priority 7b,7c: Memory Error (Instruction Fetch Memory (address) Error, unpopulated, multi region)
  //
  x3_ifaerr_excp_r: 
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI]  = 1'b1;
    ca_ecr_vec_num_nxt   = `npuarc_EV_MEM_ERR;
    ca_ecr_cs_code_nxt   = `npuarc_ECC_IF_UNPOP_MEM;
    ca_fch_excpn_nxt    = 1'b1;
  end

  // Priority 8: Privilege Violation (Actionpoint breakpoint)
  //
  aps_hit_if:
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI]  = 1'b1;
    x3_ap_excpn          = 1'b1;
    ca_ecr_vec_num_nxt   = `npuarc_EV_PRIV_V;
    ca_ecr_cs_code_nxt   = `npuarc_ECC_AP_HIT;
    ca_ecr_param_nxt[`npuarc_APNUM_RANGE] = aps_active;
  end

  // Priority 9: Machine Check (Instruction Fetch Internal Memory ECC Error)
  //
  x3_ifimerr_excp_r: 
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI]  = 1'b1;
    ca_ecr_vec_num_nxt   = `npuarc_EV_M_CHECK;
    ca_ecr_cs_code_nxt   = `npuarc_ECC_INS_FCH_IMERR;
    ca_fch_excpn_nxt    = 1'b1;

  end

  // Priority 10: Illegal Instruction Exception
  // Instr err priority over illegal sequence
  //
  (x3_instr_err | x3_instr_seq_r
   | x3_mmu_inval_cmd_excpn
  ):
  begin

    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI]  = 1'b1;

    ca_ecr_vec_num_nxt   = `npuarc_EV_INSTR_ERR;
    ca_ecr_cs_code_nxt   = ( (  x3_instr_err
                              | x3_mmu_inval_cmd_excpn
                              )
                           )
                         ? `npuarc_ECC_ILLEGAL_INS
                         : `npuarc_ECC_ILLEGAL_ISEQ
                         ;

  end


  // Priority 11a: Privilege Violation (Aux/core kernal only Reg access in user mode)
  //
  x3_priv_viol: 
  begin

    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI]  = 1'b1;

    ca_ecr_vec_num_nxt   = `npuarc_EV_PRIV_V;
    ca_ecr_cs_code_nxt   = `npuarc_ECC_PRIV_V;

  end

  // Priority 11b: Privilege Violation - Disabled Extension
  //
  x3_eia_priv_viol: 
  begin

    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI]  = 1'b1;

    ca_ecr_vec_num_nxt   = `npuarc_EV_PRIV_V;
    ca_ecr_cs_code_nxt   = eia_x3_kernel_param[5] ? `npuarc_ECC_KO_EXT : `npuarc_ECC_DISABLED_EXT;
    ca_ecr_param_nxt     = {3'h0,eia_x3_kernel_param[4:0]};

  end



  // Priority 12a: Memory Error on XY Access


  // Priority 13a: Extension Exception : FPU
  //

  // Priority 13b: Extension Exception : EIA/Apex
  //

  // Priority 14: Misaligned Data Access
  //
  x3_alignment_viol_r: 
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI]  = 1'b1;

    ca_ecr_vec_num_nxt   = `npuarc_EV_MALIGNED;
    ca_ecr_cs_code_nxt   = `npuarc_ECC_ILLEGAL_INS;
    //     
    ca_efa_en_nxt        = 1'b1;
    ca_efa_nxt           = `npuarc_DATA_SIZE'd0
                         | x3_mem_addr_r
                         ;
  end

  // Priority 15: DTLB miss
  //
  dc3_dtlb_ecc_excpn_r: // use x3 version
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI] = 1'b1;
    ca_ecr_vec_num_nxt  = `npuarc_EV_M_CHECK;
    ca_ecr_cs_code_nxt  = 8'd2;
    ca_ecr_param_nxt    = 8'd0;
    ca_efa_en_nxt       = 1'b1;
    ca_efa_nxt          = `npuarc_DATA_SIZE'd0
                        | dmp_dc3_dtlb_efa
                        ;
  end

  dc3_dtlb_miss_excpn: // use x3 version
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI] = 1'b1;
    ca_ecr_vec_num_nxt  = `npuarc_EV_DTLB_MISS;
    ca_ecr_cs_code_nxt  = ( x3_load_r & (~x3_store_r)) ? `npuarc_ECC_DTLB_LD :
                          (~x3_load_r &  x3_store_r) ? `npuarc_ECC_DTLB_ST :
                                                       `npuarc_ECC_DTLB_EX ;
    ca_ecr_param_nxt    = 8'd0;
    ca_efa_en_nxt       = 1'b1;
    ca_efa_nxt          = `npuarc_DATA_SIZE'd0
                        | dmp_dc3_dtlb_efa
                        ;
  end



  // Priority 16: Protection Violation (Data Access)
  // Equal priorities:
  //   MMU/DTLB
  //   MPU 
  //   Stack checking
  //

  dc3_dtlb_protv_excpn, // use x3 version
  x3_mpu_dprotv_r,
  x3_sc_protv_q, 
  1'b0:
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI2] = 1'b1;
    x3_mpu_excpn         = x3_mpu_dprotv_r;

    ca_ecr_vec_num_nxt   = `npuarc_EV_PROT_V;
    ca_ecr_cs_code_nxt   = { {8{x3_load_r}}  &  `npuarc_ECC_DTLB_LD}  // 8'h01
                         | { {8{x3_store_r}} &  `npuarc_ECC_DTLB_ST}; // 8'h02, EX is 8'h03

    ca_ecr_param_nxt     = 8'h00
                         | { {8{x3_sc_protv_q}} & 8'h02 }
                         | { {8{x3_mpu_dprotv_r}} & 8'h04 }
                         | { {8{dc3_dtlb_protv_excpn}} & 8'h08 }
                         ;

    ca_efa_en_nxt        = 1'b1;
    ca_efa_nxt           = `npuarc_DATA_SIZE'd0
                         | { {`npuarc_DATA_SIZE{x3_sc_protv_q}} & x3_sc_efa_r }
                         | { {`npuarc_DATA_SIZE{x3_mpu_dprotv_r}} & x3_mpu_efa_r }
                         | { {`npuarc_DATA_SIZE{dc3_dtlb_protv_excpn}} & dmp_dc3_dtlb_efa }
                         ;
  end

  // Priority 17a: Memory Error (non-exist loc)
  //
  x3_non_exist_dmem: 
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI2]  = 1'b1;
    ca_ecr_vec_num_nxt   = `npuarc_EV_MEM_ERR;
    ca_ecr_cs_code_nxt   = dc3_excpn_code;

    ca_efa_en_nxt        = 1'b1;
    ca_efa_nxt           = x3_mem_addr_r;

  end

  // Priority 17b: Memory Error (Span Multi)
  //
  x3_span_multi_dmem: 
  begin

    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_MIDPRI2]  = 1'b1;
    ca_ecr_vec_num_nxt   = `npuarc_EV_MEM_ERR;
    ca_ecr_cs_code_nxt   = dc3_excpn_code;

    ca_efa_en_nxt        = 1'b1;
    ca_efa_nxt           = x3_mem_addr_r;

  end

  // Priority 18: Machine Check (Data Memory Error) 
  // (detected / prioritized in ca stage)

  // Priority 19: Divide by zero
  //
  x3_div_divz: 
  begin
    x3_will_raise_excpn[`npuarc_X3_EXCPN_GRP_DIVZ]  = 1'b1;

    ca_ecr_vec_num_nxt   = `npuarc_EV_DIV_ZERO;
    ca_ecr_cs_code_nxt   = `npuarc_ECC_DIV_ZERO;
  end

  // Priority 20: Trap or SWI (detected / prioritized in ca stage) 
  //

   default: ;

  endcase

  // leda W226 on
  // leda W225 on

  // The instruction at X3 will to raise an exception in the next cycle.
  // If an instruction at X3 has the x3_error_branch_r signal set to 1,
  // then it will be killed when it reaches CA. Therefore, we ignore
  // any exceptions in this case.
  //
  x3_take_excpn          = x3_will_raise_excpn
                         & {`npuarc_X3_EXCPN_GRP_BITS{
                              (~x3_error_branch_r)
                            & (~x3_iprot_viol_r)
                            & (~db_active)
                           }}
                         ;

  // The debug instruction at X3 triggered an exception condition.
  // pass along this information to debugger
  //
  x3_take_db_excpn       = (|x3_will_raise_excpn) 
                         & (~x3_error_branch_r)
                         & (~x3_iprot_viol_r)
                         & (db_active)
                         ;

end // block: x3_excpn_detect_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @x2_excpn_PROC: Combinatorial process to detect CA-stage exception       //
// event.                                                                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: x2_excpn_PROC

  // Combinatorial logic to determine whether the current address used
  // by the current load/store instruction satisfies alignment constraints.
  //
  // For LL64_OPTION == 0, 64-bit LD/ST are flagged by the decoder as
  // invalid instructions, therefore there is no need to specifically
  // account for such a condition here.
  //
  casez ({   x2_size_r
           , x2_mem_addr_r[2:0]
           , x2_locked_r
         })
    6'b11_?00_0: valid_alignment     = 1'b1;   // 64-bit
    6'b11_000_1: valid_alignment     = 1'b1;   // 64-bit
    6'b01_??0_?: valid_alignment     = 1'b1;   // 16-bit
    6'b00_???_?: valid_alignment     = 1'b1;   //  8-bit
    6'b10_?00_?: valid_alignment     = 1'b1;   // 32-bit
    default:     valid_alignment     = 1'b0;   // otherwise, invalid
  endcase
  
  // There is no unaligned support for the EX instruction
  //
  x2_exchange      = x2_load_r     & x2_store_r;
  x2_uop_unaligned = x2_uop_inst_r & (| x2_mem_addr_r[1:0]);
    
  // Raise an alignment violation exception (MALIGNED) when alignment
  // checking has been enabled by ~STATUS32.AD and the alignment of
  // the current load/store address does not match the natural
  // alignment of the operation.
  //
  x3_alignment_viol_nxt  = (
                              (
                                  (~valid_alignment)
                                & (   (~ar_aux_status32_r[`npuarc_AD_FLAG])
                                    | x2_exchange
                                    | x2_uop_unaligned
                                    | x2_locked_r 
                                  )
                              )
                           )
                         & (  (x2_load_r & (!x2_pref_r))
                            | x2_store_r)
                         ;

end // block: x3_excpn_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial process to calculate CA stage exceptions and to initiate   //
// any actions to take place during WA.                                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_excpn_detect_PROC

  ca_will_raise_excpn = 1'b0;
  take_trap           = 1'b0;
  take_int            = 1'b0;
      ca_mpu_excpn_r  = 1'b0;
  ca_ap_excpn_r       = 1'b0;

  ecr_vec_num         = 8'd0;
  ecr_cs_code         = 8'd0;
  ecr_param           = 8'd0;
  ca_efa_dbl_fault    = 1'b0;
  ca_aux_efa_comp     = {ar_pc_r, 1'b0};
  ca_aux_efae_comp    = `npuarc_DATA_SIZE'd0;
//ca_aux_efae_comp    = ca_efae_r;

  ca_triple_fault_set = 1'b0;

  // SWI/TRAP are differentiated by the byte_size ucode bit which is
  // overloaded for this purpose. Both instructions assert the trap_op
  // ucode bit.
  //
  trap_type          = ca_byte_size_r;

  // to capture imprecise exception for recognition later when not in exception mode

  // Arbitrate exception vectors
  //
  // leda W226 off
  // LMD: Case select expression is constant
  // LJ:  A constant select expression is required in this case
  // leda W225 off
  // LMD: Case item expression is not constant
  // LJ:  A non-constant case-itme expression is required in this case

  case (1'b1)
    // Highest priority is an already committed exception for a post-commit
    // TRAP instruction, now in the writeback stage.
    //
    ct_excpn_trap_r: 
    begin
      ca_will_raise_excpn = 1'b1;
      ca_aux_efa_comp     = {wa_pc, 1'b0};         // (4)
      ecr_vec_num         = `npuarc_EV_TRAP;
    end


    // Priority 1: Reset detected in x3
    //--------------------------------------------------------------------------
    ca_exception_r[`npuarc_X3_EXCPN_GRP_RST] : 
    begin
      ca_will_raise_excpn = 1'b1;
      ecr_cs_code  = ca_ecr_cs_code_r;
      ecr_vec_num  = ca_ecr_vec_num_r;
      ecr_param    = ca_ecr_param_r;
    end // case : reset


    // Priority 2: Machine Check, Double Fault $EFA
    //--------------------------------------------------------------------------
        // any x3 detected exception
    (   (  |ca_exception_r[`npuarc_EXCPN_GRP_PRCS_RANGE] 
        | ca_exception_r[`npuarc_X3_EXCPN_GRP_IMPRCS]
        )
      & (ar_aux_status32_r[`npuarc_AE_FLAG] | excpn_in_prologue_r)
      & (~ct_rtie_nopp_r)
    ):
    begin  // detect triple fault due to error when fetching vector of a double fault
      if ( in_dbl_fault_excpn_r & ca_fchvec_viol &
           ca_fch_excpn_r )
      begin
        ca_triple_fault_set  = 1'b1;
      end
      ca_will_raise_excpn = 1'b1;
      ca_mpu_excpn_r      = ca_mpu_will_excpn_r;
      ca_ap_excpn_r       = ca_ap_will_excpn_r;
      ecr_cs_code  = `npuarc_ECC_DBL_FAULT;
      ecr_vec_num  = `npuarc_EV_M_CHECK;
      ecr_param    = 8'h00;
      if (ca_efa_en == 1'b1)
      begin
        ca_aux_efa_comp  = ca_efa_r;
      end  
      ca_efa_dbl_fault = 1'b1;

    end // case : double fault


    // Priority 3: Machine Check, Fatal TLB Errors (prioritized in x3)
    //--------------------------------------------------------------------------
    (ca_exception_r[`npuarc_X3_EXCPN_GRP_TLB_ERR] & (~ct_rtie_nopp_r)): 
    begin
      ca_will_raise_excpn = 1'b1;
      ecr_cs_code  = ca_ecr_cs_code_r;
      ecr_vec_num  = ca_ecr_vec_num_r;
      ecr_param    = ca_ecr_param_r;
      if ((ca_efa_en == 1'b1) || (ca_itlb_excpn == 1'b1))
      begin
        ca_aux_efa_comp = ca_itlb_excpn ? ca_itlb_efa : ca_efa_r;
        if (ca_itlb_excpn == 1'b1)
        begin
          ca_aux_efae_comp = ca_efae_r;
    end
      end
    end


    // Priority 4: Interrupt (from CA stage)
    //--------------------------------------------------------------------------
    int_qual: 
    begin
    //take_int starts an interrupt sequence. It's actully the ca_int_prolugue_evt
    //Upon this pulse is asserted the UOP sequencer should start its prologue sequence
    //int_qual guarentees take_int is fully commited in the pipeline
    // 
      take_int            = 1'b1;
      //in case we have both int_nopp (that is a cycle delayed from rtie commit), 
      //   and preempted interrupt, we take nopp_r
      if (ct_rtie_nopp_r) 
      begin
        ecr_vec_num       = irq_num_nopp_r;
      end
      else 
      begin 
        ecr_vec_num       = irq_num;
      end
    end 


    // Priority --: imprecise exceptions (prioritized in x3)
    //--------------------------------------------------------------------------
  (ca_exception_r[`npuarc_X3_EXCPN_GRP_IMPRCS] & (~ct_rtie_nopp_r)):
  begin
    ca_will_raise_excpn = 1'b1;
    ca_ap_excpn_r  = ca_ap_will_excpn_r;
    ecr_cs_code  = ca_ecr_cs_code_r;
    ecr_vec_num  = ca_ecr_vec_num_r;
    ecr_param    = ca_ecr_param_r;
    if (ca_efa_en == 1'b1)
    begin
      ca_aux_efa_comp  = ca_efa_r;              // (3a)
    end
  end


    // Priority 5-15: (prioritized in x3)
    //--------------------------------------------------------------------------
    (ca_exception_r[`npuarc_X3_EXCPN_GRP_MIDPRI] & (~ct_rtie_nopp_r)): 
    begin
      ca_will_raise_excpn = 1'b1;
      ca_mpu_excpn_r      = ca_mpu_will_excpn_r;
      ca_ap_excpn_r       = ca_ap_will_excpn_r;
      ecr_cs_code  = ca_ecr_cs_code_r;
      ecr_vec_num  = ca_ecr_vec_num_r;
      ecr_param    = ca_ecr_param_r;
      if ((ca_efa_en == 1'b1) || (ca_itlb_excpn == 1'b1))
      begin
        ca_aux_efa_comp = ca_itlb_excpn ? ca_itlb_efa : ca_efa_r;     // (3a)
        if (ca_itlb_excpn == 1'b1)
        begin
          ca_aux_efae_comp = ca_efae_r;
        end
      end
    end


  // Replay due to dtlb miss, preempts exceptions at priority 16 and below
  // to allow dtlb to get jtlb update, then generate any ld/st exception.
  // (Note: pri 16/17 exceptions may have already been preempted at x3)
    //
  ca_dc4_replay : ;  // ca_dtlb_miss_replay



    // Priority 16-17: (prioritized in x3)
    //--------------------------------------------------------------------------
    (ca_exception_r[`npuarc_X3_EXCPN_GRP_MIDPRI2] & (~ct_rtie_nopp_r)): 
    begin
      ca_will_raise_excpn = 1'b1;
      ca_mpu_excpn_r = ca_mpu_will_excpn_r;
      ca_ap_excpn_r  = ca_ap_will_excpn_r;
      ecr_cs_code  = ca_ecr_cs_code_r;
      ecr_vec_num  = ca_ecr_vec_num_r;
      ecr_param    = ca_ecr_param_r;

      if (ca_efa_en == 1'b1) // [timing] non needed for MIDPRI2 (alw en)
      begin
        ca_aux_efa_comp  = ca_efa_r;              // (3a)
      end
    end


    // Priority 18 : Machine check : internal data memory error $EFA
    //--------------------------------------------------------------------------
    dc4_ecc_int_merr:
    begin
      ca_will_raise_excpn = 1'b1;

      if (ar_aux_status32_r[`npuarc_AE_FLAG] == 1'b1)
      begin
        ecr_vec_num  = `npuarc_EV_M_CHECK;
        ecr_cs_code  = `npuarc_ECC_DBL_FAULT;
        ecr_param    = 8'd0;
        ca_efa_dbl_fault = 1'b1;
      end
      else 
      begin 
        ecr_vec_num  = `npuarc_EV_M_CHECK;
        ecr_cs_code  = `npuarc_ECC_DAT_ACC_IMERR;
        ecr_param    = 8'd0;


        ca_aux_efa_comp = ca_mem_addr_r;        // (2)


      end
    end // Excpn : dc4_ecc_int_merr


    // Priority 19: Divide by zero (prioritized in x3) $EFA_default
    //--------------------------------------------------------------------------
    (ca_exception_r[`npuarc_X3_EXCPN_GRP_DIVZ] & (~ct_rtie_nopp_r)): 
    begin
      ca_will_raise_excpn = 1'b1;
      ecr_cs_code  = ca_ecr_cs_code_r;
      ecr_vec_num  = ca_ecr_vec_num_r;
      ecr_param    = ca_ecr_param_r;
    end // case : TLB error


    // Priority 20: CA-stage invoked TRAP_S/SWI instruction $EFA
    //--------------------------------------------------------------------------
    (ca_trap_op_r & ca_valid_r): 
    begin
      ca_will_raise_excpn= ~trap_type;
      take_trap          =  trap_type;

      casez ({ ar_aux_status32_r[`npuarc_AE_FLAG]
            })
       1'b1:
       begin
         ecr_cs_code         = `npuarc_ECC_DBL_FAULT;
         ecr_vec_num         = `npuarc_EV_M_CHECK;

         ca_will_raise_excpn = 1'b1;
         take_trap           = 1'b0;
         ca_efa_dbl_fault    = 1'b1;
       end
       default:
       begin
         ecr_cs_code  = `npuarc_ECC_TRAP;
         ecr_vec_num  = (trap_type == 1'b0)
                      ? `npuarc_EV_SWI
                      : `npuarc_EV_TRAP
                      ;
         // trap_s and swi_s both set ECR.param to instruction bits [26:21]
         ecr_param    = {2'b0, ca_src1_r[5:0]};
       end
     endcase

    end // case : ca_trap


  default: ;

  endcase

  // leda W226 on
  // leda W225 on
  // When single-stepping, we wish to inhibit any exception that may
  // arise from the next instruction sitting in CA as this alias' with
  // the exception restart mechanism (unless we have already
  // committed to a post-commit exception).
  //
  do_single_step         =  ca_cmt_isi_evt
                         & (~ct_excpn_trap_r)
                         ;

  // Actionpoint break overrides an Exception
  // arise from the next instruction sitting in CA as this alias' with
  // the exception restart mechanism (unless we have already
  // committed to a post-commit exception).
  //
  aps_override_excpn     = aps_pcbrk
                         & (~ct_excpn_trap_r)
                         ;


  // Kill the exception in CA on when single stepping an instruction
  // or a WA-stage pipeline flush has occurred which will kill the
  // instruction in CA.
  //
  ca_kill_excpn          = do_single_step
                         | aps_override_excpn
                         | wa_restart_kill_r
                         | wa_sleep
                         | gb_sys_sleep_r
                         | hlt_restart
                         | ct_replay
                         ;

  // The machine shall take an exception if the current state of CA
  // raises an exception, and the CA stage is not being flushed,
  // and the debug interface (if present) is inactive.
  //
  take_excpn             = ca_will_raise_excpn 
                         & (~ca_kill_excpn)
                         & ((~excpn_in_prologue_r) | ca_efa_dbl_fault)
                         & (~ar_aux_status32_r[`npuarc_H_FLAG])
                         & excpn_barrier
                         & (~db_active)
                         ;

  // Defer TRAP event to post-commit for TRAP instructions when
  // applicable. Note, ct_excpn_trap_nxt may be asserted when
  // wa_restart_r is asserted, but only if the CA-stage TRAP
  // instruction is not killed by that pipeline restart. This can
  // happen if the TRAP instruction is in the delay-slot of a
  // late-mispredicted branch.
  //
  ct_excpn_trap_nxt      = take_trap
                         & (~ca_kill)
                         & (~ar_aux_status32_r[`npuarc_H_FLAG])
                         ;
// spyglass disable_block W398 STARC05-2.8.1.3
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
  // On a restart request, issue the appropriate restart command to
  // initiate the appropriate multi-op sequence.
  // In the case an exception breaks prol/epil sequence due to illegal
  // load/store instructions, we need to acknowledge the UOP sequencer
  // for following purposes --
  //  1. the sequence SM is reset to idle state
  //  2. For killed prologue sequence, issue j [ilink] at the end of exception
  //     handler (instead of j eret) to recover to normal program.
  //     This means the interrupt request is discarded. However as we haven't
  //     acked the interrupt yet which would happen at the end of the prol sequence,
  //     it can be taken as a another new interrupt. 
  //
  ca_restart_cmd                 = `npuarc_WA_RCMD_BITS'd0;
  ca_pkill_evt                   = 1'b0;
  casez ({   ca_kill_excpn
           , take_int 
           , take_excpn
           , 1'b0
           , ca_excpn_reset_r
         })
    5'b1_????: ca_restart_cmd                 = `npuarc_WA_RCMD_BITS'd0;
    5'b0_?1?1: ca_restart_cmd[`npuarc_RSRT_IS_RESET] = 1'b1;
    5'b0_?1?0,
    5'b0_??10: 
    begin
        ca_restart_cmd[`npuarc_RSRT_IS_EXCPN] = 1'b1;
        ca_restart_cmd[`npuarc_RSRT_IS_PKILL] = int_evts[`npuarc_INTEVT_INPROL]; 
        ca_pkill_evt                   = 1'b0
                                       | int_evts[`npuarc_INTEVT_INPROL]
                                       ;
    end
    5'b0_1000: begin
      ca_restart_cmd[`npuarc_RSRT_IS_IRQ]   = 1'b1;
      ca_restart_cmd[`npuarc_RSRT_IS_IRQ_CHAIN]   = ct_rtie_nopp_r;
    end

    default:
     begin
      ca_restart_cmd                    = `npuarc_WA_RCMD_BITS'd0;
      ca_pkill_evt                      = 1'b0;
     end

  endcase

  // Every restart request originating from the excpn_pipe takes place
  // from a location in the exception vector table, therefore this value
  // is constant.
  //
  ca_restart_vec         =  take_excpn
                         | int_evts[`npuarc_INTEVT_PROLOGUE]
                         ;

  // Assert an Exception Restart when we have decided to 'take' the
  // exception.
  //
  // NOTE: This signal must be sufficiently conditioned to ensure that
  // it is only asserted when it is known that an exception is to be
  // taken in the present clock cycle.
  //
  excpn_restart          = take_excpn 
                         | int_evts[`npuarc_INTEVT_PROLOGUE]
                         ;
  cpu_irq_select         = int_evts[`npuarc_INTEVT_PROLOGUE];

  // Derivation of restart PC as a location in the machines exception
  // table.
  //
  excpn_restart_pc   = {   ar_aux_intvbase_r[31:10]
                             , ecr_vec_num[7:0]
                             , 1'b0
                           }
                         ;


end // block: ca_excpn_detect_PROC
// spyglass enable_block W398 STARC05-2.8.1.3

always @*
begin : ca_violations_PROC


  // Detect Fetch Vector (in Prologue) violation
  // 1. Violation present
  // 2. In prologue
  // 3. Exception not killed
  // 4. Not Halted
  // 5. Not in debug
  //
  ca_fchvec_viol         = |ca_exception_r[2:0]
                         & excpn_in_prologue_r
                         & (~ca_kill_excpn)
                         & (~ar_aux_status32_r[`npuarc_H_FLAG])
                         & (~db_active)
                         ;



end // block 

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_ack_reg_PROC: to retain irq_w being taken (at take_int)         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//we memorize the level of interrupt when we decide to take it (take_int)
//We have to keep the irq number too that is through ecr_vec_num -> arc_PC
//
always @(posedge clk or posedge rst_a)
begin: irq_ack_reg_PROC
  if (rst_a == 1'b1)
  begin
    irq_ack_w_r     <= `npuarc_IRQLGN_BITS'd0;
  end
  else
  begin
    if (cpu_irq_select == 1'b1) begin
      if (ct_rtie_nopp_r) begin
        irq_ack_w_r <= irq_w_nopp_r;
      end
      else begin
        irq_ack_w_r <= irq_w;
      end
    end
  end
end // block: irq_ack_reg_PROC
reg [`npuarc_INT_NUM_RANGE]  irq_num_r;  // 

always @(posedge clk or posedge rst_a)
begin: irq_num_reg_PROC
  if (rst_a == 1'b1)
    irq_num_r <= `npuarc_INT_NUM_BITS'h0;
  else if (excpn_restart == 1'b1)
    irq_num_r <= excpn_restart_pc[`npuarc_INT_NUM_RANGE];
end // block: irq_num_reg_PROC
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @excpn_regs_upt_PROC: Combinatorial process to derive the                //
// appropriate conditions on which the various AUX. register relating       //
// to exceptions are to be updated.                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: excpn_regs_upt_PROC

  // Update exception state on entry to an exception context.
  //
  excpn_regs_cg0         = (take_excpn & excpn_restart & (!ca_excpn_reset_r))
                         ;
  //erstatus is updated at enter of ISR  
  //dependency pipe makes sure ar_status32 is up to date before committing enter of ISR 
  excpn_status_cg0       = excpn_evts[`npuarc_INTEVT_ENTER] 
                         ;

  aux_erstatus_cg0       = (excpn_status_cg0 | wa_erstatus_wen);
  aux_eret_cg0           = (excpn_regs_cg0 | wa_eret_wen);
  aux_erbta_cg0          = (excpn_regs_cg0 | wa_erbta_wen);


  // Update ECR on an exception, or on the commit of a TRAP/SWI
  // instruction.
  //
  ecr_regs_cg0           = (take_excpn & (~ct_excpn_trap_r))
                         | (ca_trap_op_r & ca_valid_r & (~ca_kill))
                         ;

  aux_ecr_cg0            = (ecr_regs_cg0 | wa_ecr_wen);

  aux_efa_cg0            = ( (  excpn_regs_cg0 
                              & (  ca_efa_en
                                 | ct_excpn_trap_r
                                )
                             )
                         | wa_efa_wen);
  aux_efae_cg0           = ( (  excpn_regs_cg0 
                              & (  ca_efa_en
                                 | ct_excpn_trap_r
                                )
                             )
                         | wa_efae_wen);
end // block: excpn_regs_upt_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial process to derive CA-stage exception-related events.       //
//                                                                          //
// Exception/Interrupts events denote cycles of interest during the         //
// lifetime lifetime of prologue and epilogue sequence. By                  //
// consequence, they are used to invoke updates the machine state.          //
//                                                                          //
// PROLOGUE_EVT:                                                            //
//                                                                          //
// ENTER_EVT:                                                               //
//                                                                          //
// EPILOGUE_EVT:                                                            //
//                                                                          //
// EXIT_EVT:                                                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_excpn_evts_PROC

  // Exception event derviations
  //
  excpn_prologue_evt     = take_excpn & (~ca_excpn_reset_r)
                         ;
  excpn_enter_evt        = ca_cmt_norm_evt
                         & ca_uop_commit_r
                         & excpn_in_prologue_r
                         ;
  excpn_epilogue_evt     = ca_cmt_uop_evt
                         & (   sp_aux_status32_r[`npuarc_AE_FLAG]
// leda W563 off
// LMD: Reduction of single bit expression is redundant
// LJ:  IRQ_ACT_ACT_RANGE can be single/multiple bits
                             | (!(|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]))
// leda W563 on
                           )
                         & ca_rtie_op_r
                         & ca_valid_r
                         & (~ca_kill)
                         ;
  excpn_exit_evt         = ca_cmt_norm_evt
                         & ca_uop_commit_r
                         & excpn_in_epilogue_r
                         ;

  // Exception events consolidation
  //
  excpn_evts             = {   excpn_prologue_evt
                             , 1'b0
                             , excpn_enter_evt
                             , excpn_epilogue_evt
                             , 1'b0
                             , excpn_exit_evt
                           }
                         ;

end // block: ca_excpn_evts_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ca_excpn_region_PROC

  // 'Exception-In' Prologue next state derivation.
  //
  excpn_in_prologue_nxt  =   excpn_prologue_evt & (~excpn_enter_evt)
                         ;

  // 'Exception-In' Epilogue next state derivation.
  //
  excpn_in_epilogue_nxt  =   excpn_epilogue_evt & (~excpn_exit_evt)
                         ;

  // 'Exception-In' clock gate enable.
  //
  excpn_in_cg0           = (excpn_prologue_evt | excpn_enter_evt)
                         | (excpn_epilogue_evt | excpn_exit_evt)
                         ;

end // block: ca_excpn_region_PROC

reg  int_ca_replay;

always @(*)
begin: interrupt_PROC
  // The machine shall take an interrupt if an preempted interrupt arises 
  // ct_rtie_nopp_r is a sepcial event when an rtie instruction is committed and a pending irq is qualified
  // as no-push-pop interrupt.
  // The interrupt is taken only under some conditions as is listed in the expression.
  // It's noted ct_rtie_nopp_r is a flopped version of irq response while int_preempt is current cycle
  // response to irq. We have to handle their arbitration where int_preempt should take higher priority
  //
  int_qual        = (int_preempt                         //interrupt request from irq_unit 
                    & (~(ca_load_r & ca_store_r))        //not executing EXchange
                    & (sp_aux_status32_r[`npuarc_IE_FLAG])      //interrupt is enabled
                    & (~sp_aux_status32_r[`npuarc_DE_FLAG])     //not in a delay slot inst
                    & (~sp_aux_status32_r[`npuarc_ES_FLAG])     //not in a ei_s inst
                    & (~sp_aux_status32_r[`npuarc_AE_FLAG])     //not in exception (commited)
                    & (~excpn_in_prologue_r)             //not in exception (prologue)
                    & (~ca_kill_excpn)                   //not in ca_kill_excpn as appliys to irq too
                    & (~pipe_block_ints)                 //not in halt
                    & (~db_active)                       //no debug active
                    & (~ca_uop_active_r)                 //no active prol/epil sequence at CA stage
                                                         //No active UOP prologue at DA (by ~ca_uop_active_r)
                    & (~uop_epil_active_r)               //No active UOP  epilogue at DA 
                    & (~al_uop_epil)                     //the start cycle os epil sequence at DA stage
                    & (~int_load_active)                 //no context restore (due to interrupt epilogue)
                    & (~al_uop_sirq_haz)                 //not in the cycles of calculating stack pointer offset
                    )
                  | ( ct_rtie_nopp_r                     //rtie with nopp 
                    )
                    ;

  int_ca_replay   = ca_replay
                  & (~wa_restart_r)                      // Replay not valid if WA Restart
                  & (~take_excpn)
                  ;

end


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_req_PROC: to produce the interrupt input to the handler           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//ct_rtie_nopp_r is a one cycle event to denote a nopp interrrupt being taken
//We need to hold the irq_num and irq_w for it to update the machine state
//properly.
// 
always @(*)
begin: irq_req_PROC
  if (ct_rtie_nopp_r) begin
    irq_w_muxed = irq_w_nopp_r;
    irq_num_muxed = irq_num_nopp_r;
  end
  else begin
    irq_w_muxed = irq_w;
    irq_num_muxed = irq_num;
  end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Interrupt (alb_interrupts) module instantiation                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_interrupts u_alb_interrupts(
  .clk                   (clk                    ),
  .rst_a                 (rst_a                  ),
  .ar_aux_irq_act_r      (ar_aux_irq_act_r       ),
  .ar_aux_status32_r     (ar_aux_status32_r      ),
  .ar_aux_user_mode_r    (ar_aux_user_mode_r     ),
  .sp_aux_status32_r     (sp_aux_status32_r      ),
  .irq_num_r             (irq_num_r              ),
  .ar_tags_empty_r       (ar_tags_empty_r        ),
  .ca_load_r             (ca_load_r              ),
  .db_active             (db_active              ),
  .ca_replay             (int_ca_replay          ),
  .ca_rtie_op_r          (ca_rtie_op_r           ),
  .ca_uop_commit_r       (ca_uop_commit_r        ),
  .ca_uop_active_r       (ca_uop_active_r        ),
  .ca_cmt_norm_evt       (ca_cmt_norm_evt        ),
  .ca_cmt_uop_evt        (ca_cmt_uop_evt         ),
  .take_int              (take_int               ),
  .ct_rtie_nopp_r        (ct_rtie_nopp_r         ),
  .irq_num_nopp_r        (irq_num_nopp_r         ),
  .irq_w_nopp_r          (irq_w_nopp_r           ),

  .irq_req               (irq_req                ),
  .irq_num               (irq_num_muxed          ),
  .irq_w                 (irq_w_muxed            ),
  .irq_preempts          (irq_preempts           ),
  .irq_ack_w_r           (irq_ack_w_r            ),
  .cpu_accept_irq        (cpu_accept_irq         ),
  .irq_ack               (irq_ack                ),
  .irq_ack_num           (irq_ack_num            ),

  .excpn_evts            (excpn_evts             ),
  .int_evts              (int_evts               ),
  .int_ilink_evt         (int_ilink_evt          ),
  .int_rtie_replay_r     (int_rtie_replay_r      ),
  .ca_pkill_evt          (ca_pkill_evt           ),
  .int_preempt           (int_preempt            ),
  .int_act_nxt           (ca_irq_act_nxt         )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @excpn_arch_PROC: combinatorial process in which the next state of       //
// EXCPN_PIPE retained architectural registers is calculated.               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: excpn_arch_nxt_PROC

  // -------------------------------------------------------------------------
  // Define the conditions under which a committing or post-committed
  // instruction should be overridden. In particular, in the case of
  // a post-committed SR to an exception register, we clobber the
  // value to be written with a new value written by the exception.
  //
  override_sr       = (take_excpn & excpn_restart) | (ca_trap_op_r & ca_pass)
                    ;

  // -------------------------------------------------------------------------
  //  ERSTATUS - Exception STATUS32 (0x402)
  //

  aux_erstatus_nxt  = `npuarc_PFLAG_BITS'd0;
  casez ({   excpn_evts[`npuarc_INTEVT_ENTER]
           , wa_erstatus_wen
         })
    2'b0_1: begin
      aux_erstatus_nxt                = `npuarc_PFLAG_BITS'd0;
      aux_erstatus_nxt[`npuarc_P_E_FLAG]     = wa_sr_data_r[`npuarc_E_FLAG];
      aux_erstatus_nxt[`npuarc_P_AE_FLAG]    = wa_sr_data_r[`npuarc_AE_FLAG];
      aux_erstatus_nxt[`npuarc_P_DE_FLAG]    = wa_sr_data_r[`npuarc_DE_FLAG];
      aux_erstatus_nxt[`npuarc_P_U_FLAG]     = wa_sr_data_r[`npuarc_U_FLAG];
      aux_erstatus_nxt[`npuarc_P_ZNCV_FLAG]  = wa_sr_data_r[`npuarc_ZNCV_RANGE];
      aux_erstatus_nxt[`npuarc_P_L_FLAG]     = wa_sr_data_r[`npuarc_L_FLAG];
      aux_erstatus_nxt[`npuarc_P_DZ_FLAG]    = wa_sr_data_r[`npuarc_DZ_FLAG];
      aux_erstatus_nxt[`npuarc_P_SC_FLAG]    = wa_sr_data_r[`npuarc_SC_FLAG];
      aux_erstatus_nxt[`npuarc_P_ES_FLAG]    = wa_sr_data_r[`npuarc_ES_FLAG];
      aux_erstatus_nxt[`npuarc_P_AD_FLAG]    = wa_sr_data_r[`npuarc_AD_FLAG];
      aux_erstatus_nxt[`npuarc_P_US_FLAG]    = wa_sr_data_r[`npuarc_US_FLAG];
      aux_erstatus_nxt[`npuarc_P_EIH_FLAG]   = wa_sr_data_r[`npuarc_EIH_FLAG];
      aux_erstatus_nxt[`npuarc_P_IE_FLAG]    = wa_sr_data_r[`npuarc_IE_FLAG];
    end
    default: begin
      aux_erstatus_nxt = wa_aux_status32_r;
    end
  endcase // case : ERSTATUS

  // -------------------------------------------------------------------------
  // ERET - Exception Return Register (0x400)
  //
  // ERET is updated under the following conditions, and for each condition
  // the next ERET value must be selected appropriately.
  //
  //  (1) On entry into an exception.
  //      -> set ERET to current PC
  //
  //  (2) On entry into an exception during interrupt prologue
  //      -> set ERET to current PC that is actually wa_pc
  //
  //  (3) When a TRAP_S is interrupted and it is located in either a delay-slot
  //      or an execution-slot.
  //      -> set ERET to the contents of the BTA register.
  //
  //  (4) When a TRAP_S is taken as the final instruction in a ZOL.
  //      -> set ERET to the contentes of the current LP_START register.
  //
  //  (5) When a TRAP_S is committed and cases (3) and (4) do not apply.
  //      -> set ERET to the next PC.
  //
  //  (6) A new value is written to ERET by an SR instruction, and none of
  //      the above exceptional conditions apply.
  //      -> set ERET to the SR write-data value.
  //
  aux_eret_nxt      = `npuarc_PC_BITS'd0;
  casez ({   take_excpn 
           , ca_pkill_evt                                   //interrupt no longer update eret
           , take_trap
           , ca_in_deslot
           , ca_zol_lp_jmp
         })
    5'b100??: aux_eret_nxt = ar_pc_r[`npuarc_PC_RANGE];            // (1)
    5'b110??: aux_eret_nxt = wa_pc[`npuarc_PC_RANGE];              // (2)
    5'b1?11?: aux_eret_nxt = ar_aux_bta_r[`npuarc_PC_RANGE];       // (3)
    5'b1?101: aux_eret_nxt = ar_aux_lp_start_r[`npuarc_PC_RANGE];  // (4)
    5'b1?100: aux_eret_nxt = ar_pc_nxt;                     // (5)
    default:  aux_eret_nxt = wa_sr_data_r[`npuarc_PC_RANGE];       // (6)
  endcase
 
  // -------------------------------------------------------------------------
  // ERBTA - Exception Branch Transfer Address (0x401)
  //
  aux_erbta_nxt     = `npuarc_PC_BITS'd0;
  casez ({   override_sr
           , wa_erbta_wen
         })
    2'b0_1:  aux_erbta_nxt = wa_sr_data_r[`npuarc_PC_RANGE];
    default: aux_erbta_nxt = ar_aux_bta_r[`npuarc_PC_RANGE];
  endcase

  // -------------------------------------------------------------------------
  // ECR - Exception Cause Register (0x403)
  //
  //     31    - 'P'
  //     30    - 'U'
  //  23:16    - Vector Number
  //  15:8     - Cause Code
  //   7:0     - Parameter
  //
  casez ({   override_sr
           , wa_ecr_wen
         })
    2'b0_1:  
    begin
      aux_ecr_p_nxt           = wa_sr_data_r[31];
      aux_ecr_u_nxt           = wa_sr_data_r[30];
      st_instrs_discarded_nxt = wa_sr_data_r[25];
      iexcpn_discarded_nxt    = wa_sr_data_r[24];
      aux_ecr_vec_nxt         = wa_sr_data_r[23:16];
      aux_ecr_code_nxt        = wa_sr_data_r[15:8];
      aux_ecr_param_nxt       = wa_sr_data_r[7:0];
    end
    default: 
    begin
      aux_ecr_p_nxt      = ca_pkill_evt;

      aux_ecr_u_nxt      = (ar_aux_user_mode_r != sp_aux_status32_r[`npuarc_U_FLAG])
                         ? 1'b1
                         : 1'b0
                         ;
      st_instrs_discarded_nxt = st_instrs_discarded ? 1'b1 : st_instrs_discarded_r;
      iexcpn_discarded_nxt    = iexcpn_discarded ? 1'b1 : iexcpn_discarded_r;
      aux_ecr_vec_nxt    = ecr_vec_num;
      aux_ecr_code_nxt   = ecr_cs_code;
      aux_ecr_param_nxt  = ecr_param;
    end
  endcase

  // Exception EFA ca_aux_efa_comp, determined in x3/ca priority trees, have
  // priority over sr to efa reg
  aux_efa_nxt     = `npuarc_DATA_SIZE'd0;
  casez ({   override_sr
           , wa_efa_wen
         })
    2'b0_1:  aux_efa_nxt = wa_sr_data_r;                // (1)
    default: aux_efa_nxt = ca_aux_efa_comp;             // (2-6)
  endcase



  aux_efae_nxt    = `npuarc_DATA_SIZE'd0;
  casez ({   override_sr
           , wa_efae_wen
         })
    2'b0_1:  aux_efae_nxt = wa_sr_data_r;               // (1)
    default: aux_efae_nxt = ca_aux_efae_comp;           // (2-6)
  endcase



end // block: excpn_arch_nxt_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial process to control the exception pipeline                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: fch_excpn_ctrl_PROC


  // DA-stage
  //
  da_cg0                 = (da_kill
                         | (al_pass 
                           & da_enable 
                           & (~da_holdup)       // DA stall AL data invalid
                           & ((~da_uop_busy_r)
                             | al_uop_has_limm)
                           ))
                         ;
  da_ifu_exception_nxt   = al_exception & (~da_kill) & (~da_holdup);

  // DA-stage
  //
  sa_cg0                 = (sa_kill | (da_pass & sa_enable));
  sa_ifu_exception_nxt   = da_ifu_exception_r & (~sa_kill)
                         & (~da_fwd_itlb_excpn2sa)
                         ;

  // X1-stage
  //
  x1_cg0                 = (x1_kill | (sa_pass & x1_enable));
  x1_ifu_exception_nxt   = (sa_ifu_exception_r | da_fwd_itlb_excpn2sa)
                         & (~x1_kill);

  // X3-stage
  //
  x2_cg0                 = x2_kill | (x1_pass & x2_enable);
  x2_ifu_exception_nxt   = x1_ifu_exception_r & (~wa_restart_r);

  // X3-stage
  //
  x3_cg0                 = x3_kill | (x2_pass & x3_enable);

  x3_itlb_ecc_excpn_nxt  = x2_ifu_exception_r 
                         & (~x2_kill_excpn)
                         & (x2_excpn_type_r == `npuarc_FCH_ITLB_ECC_ERR)
                         ;

  x3_itlb_ovrlp_excpn_nxt = x2_ifu_exception_r 
                         & (~x2_kill_excpn)
                         & (x2_excpn_type_r == `npuarc_FCH_ITLB_ERROR)
                         ;

  x3_itlb_miss_excpn_nxt = x2_ifu_exception_r 
                         & (~x2_kill_excpn)
                         & (x2_excpn_type_r == `npuarc_FCH_ITLB_MISS)
                         ;

  x3_pgl_protv_viol_nxt   = ((~x2_excpn_info_r [`npuarc_FCH_EINFO_KX0]) |   ar_aux_status32_r[`npuarc_U_FLAG])
                          & ((~x2_excpn_info_r [`npuarc_FCH_EINFO_UX0]) | (~ar_aux_status32_r[`npuarc_U_FLAG]))
                          & (~db_active)
                          ;

  x3_pgm_protv_viol_nxt   = x2_excpn_info_r [`npuarc_FCH_EINFO_IN_WRD1]
                          & ((~x2_excpn_info_r [`npuarc_FCH_EINFO_KX1]) |   ar_aux_status32_r[`npuarc_U_FLAG])
                          & ((~x2_excpn_info_r [`npuarc_FCH_EINFO_UX1]) | (~ar_aux_status32_r[`npuarc_U_FLAG]))
                          & (~db_active)
                          ;
  
  x3_pgl_protv_fwd_nxt    = x2_fwd_protv_excpn2sa
                          & ((~x2_fwd_excpn_info_r [`npuarc_FCH_EINFO_KX0]) |   ar_aux_status32_r[`npuarc_U_FLAG])
                          & ((~x2_fwd_excpn_info_r [`npuarc_FCH_EINFO_UX0]) | (~ar_aux_status32_r[`npuarc_U_FLAG]))
                          & (~db_active)
                          ;

  x3_pgm_protv_fwd_nxt    = x2_fwd_protv_excpn2sa
                          & x2_fwd_excpn_info_r [`npuarc_FCH_EINFO_IN_WRD1]
                          & ((~x2_fwd_excpn_info_r [`npuarc_FCH_EINFO_KX1]) |   ar_aux_status32_r[`npuarc_U_FLAG])
                          & ((~x2_fwd_excpn_info_r [`npuarc_FCH_EINFO_UX1]) | (~ar_aux_status32_r[`npuarc_U_FLAG]))
                          & (~db_active)
                          ;

  x3_itlb_protv_excpn_nxt = (   x3_pgl_protv_viol_nxt | x3_pgm_protv_viol_nxt
                              | x3_pgl_protv_fwd_nxt  | x3_pgm_protv_fwd_nxt  )
                          & (~ca_uop_inprol_r)
                          & (~x2_uop_inst_r)
                          & (~x2_kill_excpn)
                          & (~db_active)
                          ;

  x3_ifberr_excp_nxt     = x2_ifu_exception_r 
                         & (~x2_kill_ifu_excpn)
                         & (x2_excpn_type_r == `npuarc_FCH_BUS_ERROR)
                         ;

  x3_ifaerr_excp_nxt     = x2_ifu_exception_r 
                         & (~x2_kill_ifu_excpn)
                         & (x2_excpn_type_r == `npuarc_FCH_ADDR_ERROR)
                         ;

  x3_ifimerr_excp_nxt    = x2_ifu_exception_r
                         & (~x2_kill_ifu_excpn)
                         & (x2_excpn_type_r == `npuarc_FCH_ECC_ERROR)
                         ;


  // CA-stage
  //
  ca_cg0                 = excpn_reset_r              //
                         | ca_trap_op_r               //
                         | x3_pc_excpn                //
                         | wa_restart_r               //
                         | ca_excpn_reset_r           //
                         | (x3_pass & ca_enable       //
                           & (~db_active))
                         ;

  ca_db_cg0              = ca_cg0 
                         | x3_take_db_excpn
                         | ca_db_exception_r         //
                         ;

  ca_exception_nxt       = x3_take_excpn;
  // WA-stage
  //
  wa_cg0                 = wa_restart_r | take_excpn | take_trap
                         | int_evts[`npuarc_INTEVT_PROLOGUE]
                         | ca_replay
                         ;

  wa_restart_vec_nxt     = ca_restart_vec;
  wa_restart_cmd_nxt     = ca_restart_cmd;

end // block: fch_excpn_ctrl_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sequential process to maintain the exception pipeline state              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: fch_excpn_regs_PROC
  if (rst_a == 1'b1)
  begin
    da_ifu_exception_r   <= 1'b0;
    sa_ifu_exception_r   <= 1'b0;
    x1_ifu_exception_r   <= 1'b0;
    x2_ifu_exception_r   <= 1'b0;

    x3_itlb_ecc_excpn_r   <= 1'b0;
    x3_itlb_ovrlp_excpn_r <= 1'b0;
    x3_itlb_miss_excpn_r  <= 1'b0;
    x3_itlb_protv_excpn_r <= 1'b0;
    x3_pgl_protv_viol_r   <= 1'b0;
    x3_pgm_protv_viol_r   <= 1'b0;
    x3_illegal_operand_r  <= 1'b0;

    ca_itlb_ecc_excpn_r   <= 1'b0;
    ca_itlb_ovrlp_excpn_r <= 1'b0;
    ca_itlb_protv_excpn_r <= 1'b0;
    ca_pgl_protv_viol_r   <= 1'b0;
    ca_pgm_protv_viol_r   <= 1'b0;

    x3_ifberr_excp_r     <= 1'b0;
    x3_ifaerr_excp_r     <= 1'b0;
    x3_ifimerr_excp_r    <= 1'b0;
    ca_exception_r       <= `npuarc_X3_EXCPN_GRP_BITS'd0;
    ca_db_exception_r    <= 1'b0;

    da_excpn_type_r      <= `npuarc_FCH_EXCPN_BITS'd0;
    sa_excpn_type_r      <= `npuarc_FCH_EXCPN_BITS'd0;
    x1_excpn_type_r      <= `npuarc_FCH_EXCPN_BITS'd0;
    x2_excpn_type_r      <= `npuarc_FCH_EXCPN_BITS'd0;

    da_excpn_info_r     <= `npuarc_FCH_EINFO_BITS'd0;
    sa_excpn_info_r     <= `npuarc_FCH_EINFO_BITS'd0;
    x1_excpn_info_r     <= `npuarc_FCH_EINFO_BITS'd0;
    x2_excpn_info_r     <= `npuarc_FCH_EINFO_BITS'd0;
    x3_excpn_info_r     <= `npuarc_FCH_EINFO_BITS'd0;
    ca_excpn_info_r     <= `npuarc_FCH_EINFO_BITS'd0;

    da_ifu_err_nxtpg_r   <= 1'b0;
    sa_ifu_err_nxtpg_r   <= 1'b0;
    x1_ifu_err_nxtpg_r   <= 1'b0;
    x2_ifu_err_nxtpg_r   <= 1'b0;
    x3_ifu_err_nxtpg_r   <= 1'b0;
    ca_ifu_err_nxtpg_r   <= 1'b0;

//    sa_fwd_itlb_excpn2sa <= 1'b0;
    x1_fwd_itlb_excpn2sa <= 1'b0;
    x2_fwd_itlb_excpn2sa <= 1'b0;
    x3_fwd_itlb_excpn2sa <= 1'b0;
    ca_fwd_itlb_excpn2sa <= 1'b0;

    x1_fwd_protv_excpn2sa <= 1'b0;
    x2_fwd_protv_excpn2sa <= 1'b0;

    x1_fwd_excpn_info_r  <= 5'd0;
    x2_fwd_excpn_info_r  <= 5'd0;
    
    x3_instr_err_r       <= 1'b0;
    x3_instr_seq_r       <= 1'b0;
    x3_priv_viol_r       <= 1'b0;
    x3_seq_err_dslot_limm_r <= 1'b0;

    x3_eia_priv_viol_r   <= 1'b0;
    x3_eia_kernel_cc_viol_r <= 1'b0;
    x3_alignment_viol_r  <= 1'b0;

    ca_excpn_reset_r     <= 1'b0;
    ca_ecr_vec_num_r     <= 8'd0;
    ca_ecr_cs_code_r     <= 8'd0;
    ca_ecr_param_r       <= 8'd0;
    ca_fch_excpn_r       <= 1'b0;

    ca_ap_will_excpn_r   <= 1'b0;
    ca_mpu_will_excpn_r  <= 1'b0;
    ca_efa_en            <= 1'b0;
    ca_efa_r             <= `npuarc_DATA_SIZE'd0;
    ca_efae_r            <= `npuarc_DATA_SIZE'd0;
    ct_excpn_trap_r      <= 1'b0;
    wa_restart_vec_r     <= 1'b0;
    wa_restart_cmd_r     <= `npuarc_WA_RCMD_BITS'd0;
  end
  else
  begin

    if (da_cg0 == 1'b1)
    begin
      da_ifu_exception_r <= da_ifu_exception_nxt;
      da_excpn_type_r    <= al_excpn_type;
      da_excpn_info_r    <= al_excpn_info;
      da_ifu_err_nxtpg_r <= al_ifu_err_nxtpg & (~da_kill);
    end

    if (sa_cg0 == 1'b1)
    begin
      sa_ifu_exception_r <= sa_ifu_exception_nxt;
      sa_excpn_type_r    <= da_excpn_type_r;
      sa_excpn_info_r    <= da_excpn_info_r;
      sa_ifu_err_nxtpg_r <= da_ifu_err_nxtpg_r & (~sa_kill);
//      sa_fwd_itlb_excpn2sa <= 1'b0;
    end

    if (x1_cg0 == 1'b1)
    begin
      x1_ifu_exception_r <= x1_ifu_exception_nxt;
      x1_excpn_info_r    <= sa_excpn_info_r;
      x1_excpn_type_r    <= da_fwd_itlb_excpn2sa ?
                              da_excpn_type_r :
                              sa_excpn_type_r ;

      x1_ifu_err_nxtpg_r <= da_fwd_itlb_excpn2sa ?
                              da_ifu_err_nxtpg_r :
                              sa_ifu_err_nxtpg_r ;
      x1_fwd_itlb_excpn2sa <= da_fwd_itlb_excpn2sa;
      x1_fwd_excpn_info_r  <= da_excpn_info_r;
      x1_fwd_protv_excpn2sa <= da_fwd_protv_excpn2sa;
    end

    if (x2_cg0 == 1'b1)
    begin
      x2_ifu_exception_r <= x2_ifu_exception_nxt;
      x2_excpn_type_r    <= x1_excpn_type_r;
      x2_excpn_info_r    <= x1_excpn_info_r;
      x2_ifu_err_nxtpg_r <= x1_ifu_err_nxtpg_r & (~x2_kill | x1_in_dslot_r);
      x2_fwd_itlb_excpn2sa <= x1_fwd_itlb_excpn2sa;
      x2_fwd_excpn_info_r  <= x1_fwd_excpn_info_r;
      x2_fwd_protv_excpn2sa <= x1_fwd_protv_excpn2sa;
    end

    if (x3_cg0 == 1'b1)
    begin
      x3_instr_err_r     <= x3_instr_err_nxt       & (~x2_kill);
      x3_instr_seq_r     <= x3_instr_seq_nxt       & (~x2_kill);
      x3_seq_err_dslot_limm_r <= x3_seq_err_dslot_limm_nxt; 

      x3_priv_viol_r     <= x3_priv_viol_nxt       & (~x2_kill);
      x3_eia_priv_viol_r <= x3_eia_priv_viol_nxt   & (~x2_kill);
      x3_eia_kernel_cc_viol_r <= x3_eia_kernel_cc_viol_nxt   & (~x2_kill);
      x3_alignment_viol_r<= x3_alignment_viol_nxt  & (~x2_kill);

      x3_itlb_ecc_excpn_r   <= x3_itlb_ecc_excpn_nxt;
      x3_itlb_ovrlp_excpn_r <= x3_itlb_ovrlp_excpn_nxt;
      x3_itlb_miss_excpn_r  <= x3_itlb_miss_excpn_nxt;
      x3_itlb_protv_excpn_r <= x3_itlb_protv_excpn_nxt;
      x3_pgl_protv_viol_r   <= x3_pgl_protv_viol_nxt 
                             | ( x3_pgl_protv_fwd_nxt
                               & (~x3_pgm_protv_viol_nxt))  // Do not forward if parent excpn
                             ;
      x3_pgm_protv_viol_r   <= x3_pgm_protv_viol_nxt
                             | ( x3_pgm_protv_fwd_nxt
                               & (~x3_pgl_protv_viol_nxt))
                             ;
      x3_illegal_operand_r  <= x2_illegal_operand_r;

      x3_ifberr_excp_r   <= x3_ifberr_excp_nxt;
      x3_ifaerr_excp_r   <= x3_ifaerr_excp_nxt;
      x3_ifimerr_excp_r  <= x3_ifimerr_excp_nxt;
      x3_excpn_info_r    <= x2_excpn_info_r;
      x3_ifu_err_nxtpg_r <= x2_ifu_err_nxtpg_r & (~x2_kill);
      x3_fwd_itlb_excpn2sa <= x2_fwd_itlb_excpn2sa 
                            | (x2_fwd_protv_excpn2sa
                              & (~(x3_pgl_protv_viol_nxt |x3_pgm_protv_viol_nxt))
                              )
                            ;
    end

    if (ca_db_cg0 == 1'b1)
    begin
      ca_db_exception_r  <= x3_take_db_excpn       & (~x3_kill);
    end
    if (ca_cg0 == 1'b1)
    begin
      ca_exception_r     <= ca_exception_nxt & {`npuarc_X3_EXCPN_GRP_BITS{(~x3_kill)}};
      ca_excpn_info_r    <= x3_excpn_info_r;
      ca_excpn_reset_r   <= ca_excpn_reset_nxt;
      ca_ecr_vec_num_r   <= ca_ecr_vec_num_nxt;
      ca_ecr_cs_code_r   <= ca_ecr_cs_code_nxt;
      ca_ecr_param_r     <= ca_ecr_param_nxt;
      ca_fch_excpn_r     <= ca_fch_excpn_nxt;
      ca_efa_en          <= ca_efa_en_nxt;
      ca_efa_r           <= ca_efa_nxt;
      ca_efae_r          <= ca_efae_nxt;
      ca_ifu_err_nxtpg_r  <= x3_ifu_err_nxtpg_r & (~x3_kill);

      ca_itlb_ecc_excpn_r   <= x3_itlb_ecc_excpn_r;
      ca_itlb_ovrlp_excpn_r <= x3_itlb_ovrlp_excpn_r;
      ca_itlb_protv_excpn_r <= x3_itlb_protv_excpn_r;
      ca_fwd_itlb_excpn2sa  <= x3_fwd_itlb_excpn2sa;
      ca_pgl_protv_viol_r   <= x3_pgl_protv_viol_r;
      ca_pgm_protv_viol_r   <= x3_pgm_protv_viol_r;

      ca_mpu_will_excpn_r <= x3_mpu_excpn          & (~x3_kill);
      ca_ap_will_excpn_r <= x3_ap_excpn            & (~x3_kill);
    end

    if (wa_cg0 == 1'b1)
    begin
      ct_excpn_trap_r    <= ct_excpn_trap_nxt;

      wa_restart_vec_r   <= wa_restart_vec_nxt;
      wa_restart_cmd_r   <= wa_restart_cmd_nxt;
    end
  end
end // block: fch_excpn_regs_PROC


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// @excpn_arch_PROC: Architectural state retained by EXCPN_PIPE.             //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

always @*
begin: excpn_arch_PROC

  // -------------------------------------------------------------------------
  // AUX_STATUS32 architectural register
  //
  ar_aux_erstatus_r               = `npuarc_DATA_SIZE'd0;
  ar_aux_erstatus_r[`npuarc_E_FLAG]      = aux_erstatus_r[`npuarc_P_E_FLAG];
  ar_aux_erstatus_r[`npuarc_AE_FLAG]     = aux_erstatus_r[`npuarc_P_AE_FLAG];
  ar_aux_erstatus_r[`npuarc_DE_FLAG]     = aux_erstatus_r[`npuarc_P_DE_FLAG];
  ar_aux_erstatus_r[`npuarc_U_FLAG]      = aux_erstatus_r[`npuarc_P_U_FLAG];
  ar_aux_erstatus_r[`npuarc_ZNCV_RANGE]  = aux_erstatus_r[`npuarc_P_ZNCV_FLAG];
  ar_aux_erstatus_r[`npuarc_L_FLAG]      = aux_erstatus_r[`npuarc_P_L_FLAG];
  ar_aux_erstatus_r[`npuarc_DZ_FLAG]     = aux_erstatus_r[`npuarc_P_DZ_FLAG];
  ar_aux_erstatus_r[`npuarc_SC_FLAG]     = aux_erstatus_r[`npuarc_P_SC_FLAG];
  ar_aux_erstatus_r[`npuarc_ES_FLAG]     = aux_erstatus_r[`npuarc_P_ES_FLAG];
  ar_aux_erstatus_r[`npuarc_AD_FLAG]     = aux_erstatus_r[`npuarc_P_AD_FLAG];
  ar_aux_erstatus_r[`npuarc_US_FLAG]     = aux_erstatus_r[`npuarc_P_US_FLAG];
  ar_aux_erstatus_r[`npuarc_IE_FLAG]     = aux_erstatus_r[`npuarc_P_IE_FLAG];
  ar_aux_erstatus_r[`npuarc_EIH_FLAG]    = aux_erstatus_r[`npuarc_P_EIH_FLAG];

  // -------------------------------------------------------------------------
  // AUX_ERET architectural register
  //
  ar_aux_eret_r          = `npuarc_DATA_SIZE'd0;
  ar_aux_eret_r[`npuarc_PC_RANGE]    = aux_eret_r;

  // -------------------------------------------------------------------------
  // AUX_ECR architectural register
  //
  ar_aux_ecr_r           = {   aux_ecr_p_r
                             , aux_ecr_u_r
                             , 4'd0
                             , st_instrs_discarded_r
                             , iexcpn_discarded_r
                             , aux_ecr_vec_r
                             , aux_ecr_code_r
                             , aux_ecr_param_r
                           }
                         ;

  // -------------------------------------------------------------------------
  // AUX_EFA architectural register
  //
  ar_aux_efa_r           = aux_efa_r;
  ar_aux_efae_r          = aux_efae_r;

  // -------------------------------------------------------------------------
  // AUX_ERBTA architectural register
  //
  ar_aux_erbta_r         = `npuarc_DATA_SIZE'd0;
  ar_aux_erbta_r[`npuarc_PC_RANGE]   = aux_erbta_r;

end // block: excpn_arch_PROC


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// @excpn_arch_regs_PROC: Architectural registers.                           //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: excpn_arch_regs_PROC
  if (rst_a == 1'b1)
  begin
    aux_erstatus_r         <= `npuarc_PFLAG_BITS'd0;
    aux_eret_r             <= `npuarc_PC_BITS'd0;
    aux_erbta_r            <= `npuarc_PC_BITS'd0;
    aux_ecr_p_r            <= 1'b0;
    aux_ecr_u_r            <= 1'b0;
    aux_ecr_vec_r          <= 8'd0;
    iexcpn_discarded_r     <= 1'b0;
    st_instrs_discarded_r  <= 1'b0;
    aux_ecr_code_r         <= 8'd0;
    aux_ecr_param_r        <= 8'd0;
    aux_efa_r              <= `npuarc_DATA_SIZE'd0;
    aux_efae_r             <= `npuarc_DATA_SIZE'd0;
  end
  else
  begin
    //erstatus is updated by sr or by exception enter event
    //
    if (aux_erstatus_cg0 == 1'b1)
      aux_erstatus_r  <= aux_erstatus_nxt;

    //eret&erbta is updated by sr or by excpetion taken event
    //
    if (aux_eret_cg0 == 1'b1)
      aux_eret_r      <= aux_eret_nxt;
    if (aux_erbta_cg0 == 1'b1)
      aux_erbta_r     <= aux_erbta_nxt;
    if (aux_ecr_cg0 == 1'b1)
    begin
      aux_ecr_p_r     <= aux_ecr_p_nxt;
      aux_ecr_u_r     <= aux_ecr_u_nxt;
      aux_ecr_vec_r   <= aux_ecr_vec_nxt;
      aux_ecr_code_r  <= aux_ecr_code_nxt;
      aux_ecr_param_r <= aux_ecr_param_nxt;
      iexcpn_discarded_r   <= iexcpn_discarded_nxt & ar_aux_status32_r[`npuarc_EIH_FLAG];
      st_instrs_discarded_r<= st_instrs_discarded_nxt & ar_aux_status32_r[`npuarc_EIH_FLAG];
    end
    if (aux_efa_cg0 == 1'b1)
    begin
      aux_efa_r       <= aux_efa_nxt;
    end
    if (aux_efae_cg0 == 1'b1)
    begin
      aux_efae_r      <= aux_efae_nxt;
    end
  end
end // block: excpn_arch_regs_PROC


always @(posedge clk or posedge rst_a)
begin: excpn_region_regs_PROC
  if (rst_a == 1'b1)
  begin
    excpn_in_prologue_r  <= 1'b0;
    excpn_in_epilogue_r  <= 1'b0;
  end
  else if (excpn_in_cg0 == 1'b1)
  begin
    excpn_in_prologue_r  <= excpn_in_prologue_nxt;
    excpn_in_epilogue_r  <= excpn_in_epilogue_nxt;
  end
end // block: excpn_region_regs_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sequential process to maintain the reset FSM state                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: excpn_reset_regs_PROC
  if (rst_a == 1'b1)
  begin
    fsm_rst_r       <= RESET_IDLE;
    excpn_reset_r   <= 1'b0;
  end
  else
    if (fsm_rst_cg0 == 1'b1)
    begin
      fsm_rst_r     <= fsm_rst_nxt;
      excpn_reset_r <= excpn_reset_nxt;
    end
end // block: excpn_reset_regs_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// generate kinv to invert current mode at CA stage during UOP sequnce      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
//when we see a aex instruction from uop sequence we force to kernal mode 
//
wire int_aex_evt;
assign int_aex_evt = ca_cmt_uop_evt
                 & ca_sr_op_r
                 & ca_lr_op_r
                 & ( int_evts[`npuarc_INTEVT_INPROL]
                   | int_evts[`npuarc_INTEVT_INEPIL]
                   )
                 ;

//during interrupt UOP sequence we need to 
//invert kernal/user mode for aex instruction that switches user/kernal stack
//The state of "inverted mode" exits at end of uop sequence 
// or when the uop is killed by exception/ca_replay
//
wire int_kinv_clr;
assign int_kinv_clr= excpn_evts[`npuarc_INTEVT_ENTER]
                    | int_evts[`npuarc_INTEVT_EXIT]
                    | int_evts[`npuarc_INTEVT_ENTER]
                    ;  

//The epilogue sequence can be killed by ca_replay
//we have to force to kernal mode for the replayed rtie
//
wire int_rtie_replay_set;
assign int_rtie_replay_set = int_evts[`npuarc_INTEVT_INEPIL]
                           & int_ca_replay
                           ;

//the "force kernal" state is cleared when rtie instruction 
// is commited
//
wire int_rtie_replay_clr;
assign int_rtie_replay_clr = ca_rtie_op_r
                           & ca_pass
                           & (~sp_aux_status32_r[`npuarc_AE_FLAG])
                           ;
reg sp_kinv_replay_r;
always @(posedge clk or posedge rst_a) 
begin: sp_kinv_PROC 
  if (rst_a == 1'b1) begin
    sp_kinv_r         <= 1'b0;
    sp_kinv_replay_r  <= 1'b0;
    int_rtie_replay_r <= 1'b0;
  end
  else begin
    if (int_aex_evt) begin
      sp_kinv_r <= 1'b1;
    end
    else if (int_kinv_clr) begin
      sp_kinv_r <= 1'b0;
    end
    else if (int_rtie_replay_clr & int_rtie_replay_r) begin
      sp_kinv_r <= sp_kinv_replay_r; // Restore the kinv bit
    end

    if (int_rtie_replay_set) begin
      sp_kinv_replay_r <= sp_kinv_r; // Save sp_kinv on replay
    end
    else if (int_rtie_replay_clr) begin
      sp_kinv_replay_r <= 1'b0;
    end

    if (int_rtie_replay_set) begin
      int_rtie_replay_r <= 1'b1;
    end
    else if (int_rtie_replay_clr) begin
      int_rtie_replay_r <= 1'b0;
    end
  end
end


//We need to disallow the IRQ request during epil sequence
//that starts from the speculative RTIE at DA stage
//upto the RTIE is committed
//
always @(posedge clk or posedge rst_a)
begin: uop_epil_active_PROC
  if (rst_a == 1'b1) begin
    uop_epil_active_r <= 1'b0;
  end
  else begin
    if (wa_restart_r || x2_restart_r) begin //cleared by restart
      uop_epil_active_r <= 1'b0;
    end
    else if (ca_uop_active_r) begin         //cleared after epil is commted
      uop_epil_active_r <= 1'b0;
    end
    else if (al_uop_epil) begin             //set during epil sm
      uop_epil_active_r <= 1'b1;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin: mem_err_ack_reg_PROC
  if (rst_a == 1'b1)
    mem_excpn_ack_r <= 1'b0;
  else
    mem_excpn_ack_r <= take_excpn
                     & (    (   (ecr_vec_num == `npuarc_EV_MEM_ERR) 
                              & (ecr_cs_code == `npuarc_ECC_DMP_BUS_ERR)
                            )
                         | (ecr_vec_num == `npuarc_EV_M_CHECK)
                       )
                     ;
end

// Track occurance of double fault
//
always @(posedge clk or posedge rst_a)
begin: in_dbl_fault_excpn_PROC
  if (rst_a == 1'b1) begin
    in_dbl_fault_excpn_r <= 1'b0;
  end
  else begin
    // set on taking double fault exception
    if (take_excpn & ca_efa_dbl_fault) begin
      in_dbl_fault_excpn_r <= 1'b1;
    end
    // cleared on exception exit
    else if (excpn_exit_evt | ~(ar_aux_status32_r[`npuarc_AE_FLAG])) begin
      in_dbl_fault_excpn_r <= 1'b0;
    end
  end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output Assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


assign ca_db_exception = ca_db_exception_r
                       ;


assign excpn_in_prologue = excpn_in_prologue_r;
assign excpn_hld_halt    = ca_trap_op_r
                         | ct_excpn_trap_r 
                         | dc4_excpn
                         | int_evts[`npuarc_INTEVT_INPROL]
                         | int_evts[`npuarc_INTEVT_INEPIL]
                         | excpn_in_prologue_r
                         ;

// assign ca_itlb_excpn      = take_excpn & 
//                             ( (ecr_vec_num == `EV_ITLB_MISS)
//                              | ca_itlb_protv_excpn_r
//                              | ca_itlb_ecc_excpn_r
//                              | ca_itlb_ovrlp_excpn_r
//                             );

assign ca_itlb_excpn      = ( (ca_ecr_vec_num_r == `npuarc_EV_ITLB_MISS)
                             | ca_itlb_protv_excpn_r
                             | ca_itlb_ecc_excpn_r
                             | ca_itlb_ovrlp_excpn_r
                            );

assign ca_ecr_dtlb_miss   = (ca_ecr_vec_num_r == `npuarc_EV_DTLB_MISS);
assign ca_ecr_itlb_miss   = (ca_ecr_vec_num_r == `npuarc_EV_ITLB_MISS);

assign ca_tlb_miss_excpn  = take_excpn &
                            (ca_ecr_dtlb_miss | ca_ecr_itlb_miss);

assign ca_tlb_miss_efa    = ca_aux_efa_comp[`npuarc_PD0_VPN_RANGE];

assign ca_m_chk_excpn     = take_excpn &
                            (ecr_vec_num == `npuarc_EV_M_CHECK);


assign x2_fa0_transl   = x2_excpn_info_r[`npuarc_FCH_EINFO_TVA0];

// spyglass enable_block W193

assign x3_db_exception = x3_take_db_excpn;
endmodule // alb_excpn_pipe
