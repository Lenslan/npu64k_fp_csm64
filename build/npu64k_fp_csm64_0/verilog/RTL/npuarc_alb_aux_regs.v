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
//    #     #     #  #     #         ######   #######   #####    #####
//   # #    #     #   #   #          #     #  #        #     #  #     #
//  #   #   #     #    # #           #     #  #        #        #
// #     #  #     #     #            ######   #####    #  ####   #####
// #######  #     #    # #           #   #    #        #     #        #
// #     #  #     #   #   #          #    #   #        #     #  #     #
// #     #   #####   #     #  #####  #     #  #######   #####    #####
//
// ===========================================================================
//
// Description:
//
//  This module implements a sub-set of the core auxiliary registers of the
//  ARCv2HS CPU. The registers implemented in this module are updated in
//  the Writeback stage of the the ARCv2HS pipeline, either by SR operations
//  or, in some cases, by an exception entry. 
//
//  Other auxiliary registers, that are updated implicitly as an instrution
//  progresses from CA to WA, are implemented in the CA/WA stages themselves.
//
// ==========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//
`include "npuarc_ucode_const.v"

// Definitions for all decode-related constants
//
`include "npuarc_decode_const.v"

// Set simulation timescale
//
`include "const.def"

//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 }, edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }


module npuarc_alb_aux_regs (
  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,                // global clock
  input                       rst_a,              // asynchronous reset signal
  input     [7:0]             arcnum,
  input     [7:0]             clusternum,         // for cluster id register

  ////////// Auxiliary interface for (CORE) SR/LR instructions ///////////////
  //
  input                       aux_write,          // (X3) SR ucode bit
  input                       aux_cr1_ren_r,      // 
  input                       aux_cr2_ren_r,      // 
  input                       aux_cr3_ren_r,      // 
  input                       aux_cr4_ren_r,      // 
  input                       aux_cr5_ren_r,      // 
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range  
  input     [10:0]            aux_core_raddr_r,   // (X3) Aux read/write addr
  input     [`npuarc_DATA_RANGE]     ca_src1_r,          // (WA) Op Write data  
// leda NTL_CON13C on
// leda NTL_CON37 on
  input                       aux_core_wen_r,     // (WA) Aux region select
  input     [10:0]            aux_core_waddr_r,   // (WA) Aux write address
  input     [`npuarc_DATA_RANGE]     wa_sr_data_r,       // (WA) Aux write data

  //
  output reg [`npuarc_DATA_RANGE]    core_aux_rdata,     // (X3) LR read data
  output reg                  core_aux_illegal,   // (X3) SR/LR illegal
  output reg                  core_aux_k_rd,      // (X3) need Kernel Read
  output reg                  core_aux_k_wr,      // (X3) need Kernel Write
  output reg                  core_aux_unimpl,    // (X3) Invalid Reg
  output reg                  core_aux_serial_sr, // (X3) SR group flush pipe
  output reg                  core_aux_strict_sr, // (X3) SR flush pipe
  output reg                  core_aux_stall,     // Core RAW Hazard detect
  //
  input                       sys_halt_ack_r,     // set DEBUG.EH bit

  ////////// Interface to debug unit, which affects LR/SR behavior ///////////
  //
  input                       db_active_r,        // Debug unit active


  output reg                  dbg_halt_r,

  ////////// PC pipeline interface (LR from PC32) ////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range 
  input     [`npuarc_DATA_RANGE]     x3_src0_r,          // Current PC when LR at X3
// leda NTL_CON13C on
  input     [`npuarc_PC_RANGE]       ar_pc_r,            // Next committed PC
  input     [`npuarc_PC_RANGE]       ca_target_r,        // eSlot Target

  ////////// Special auxiliary register values, for LR ///////////////////////
  //
  input     [`npuarc_DATA_RANGE]     ar_aux_status32_r,  // STATUS32 (speculative X3)
  input                       ca_aux_s32_stall,   // STATUS32 update pending
  input     [`npuarc_DATA_RANGE]     ar_aux_erstatus_r,  // ERSTATUS32 aux. register
  input     [`npuarc_DATA_RANGE]     ar_aux_eret_r,      // ERET aux. register
  input     [`npuarc_DATA_RANGE]     ar_aux_ecr_r,       // ECR aux. register
  input     [`npuarc_DATA_RANGE]     ar_aux_erbta_r,     // ERBTA aux. register
  input     [`npuarc_DATA_RANGE]     ar_aux_efa_r,       // EFA aux. register
  input     [`npuarc_DATA_RANGE]     ar_aux_efae_r,      // EFA EXT aux. register

  ////////// STATUS32 update Interface ///////////////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
// spyglass disable_block W240
// SMD: Input declared but not used
// SJ:  Depending on config some bits in signal will not be used
  input     [`npuarc_PFLAG_RANGE]    wa_aux_status32_nxt, // STATUS32 next state.   
  input     [`npuarc_PFLAG_RANGE]    wa_aux_status32_r,   // STATUS32 next state. 
// spyglass enable_block W240
// leda NTL_CON13C on                      
  input                       wa_aux_status32_pass,// CA updates STATUS32
  input                       ca_in_kflag,         // Cmt Kernel Flag update
                      

  output                      wa_status32_wen,    // WA writes STATUS32
  output                      wa_debug_wen,       // WA writes DEBUG
  ////////// Exception update Interface //////////////////////////////////////
  //
  output                      wa_erstatus_wen,    // WA writes ERSTATUS
  output                      wa_eret_wen,        // WA writes ERET
  output                      wa_erbta_wen,       // WA writes ERBTA
  output                      wa_ecr_wen,         // WA writes ECR
  output                      wa_efa_wen,         // WA writes EFA
  output                      wa_efae_wen,         // WA writes EFA

  ////////// Special auxiliary register updates //////////////////////////////
  //
  input                       ca_finish_sgl_step,
  input                       ca_cmt_brk_evt,     // CA cmts. BRK insn.
  input                       ca_normal_evt,      // normal instruction commit
  input                       ca_sleep_evt,       // sleep, wevt or wlfc commits
  input                       ca_wevt_evt,        // wevt inst commits
  input                       ca_wlfc_evt,        // wlfc inst commits
  input                       wlfc_wakeup,        // wlfc wakeup event occurs
  input                       sleep_hlt_wake,     // sleep hlt wake
  input                       wevt_wakeup_r,      // wevt wakeup event occurs
  input                       ca_uop_evt,         // non-final UOP inst commit
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
  input     [`npuarc_INTEVT_RANGE]   excpn_evts,         // Exception events
// leda NTL_CON13C on
// leda NTL_CON37 on
  //
  input                       ca_ei_op_r,         // EI present at CA
  input                       cmt_0_ei_evt,       // EI commits at CA
  input                       ca_brk_op_r,        //
  //
  input                       ca_dslot_r,         // br with dslot
  input                       ca_br_taken,        // actual branch outcome
  input     [`npuarc_PC_RANGE]       ca_br_target,       // BTA value if ca_dslot_r
  input     [`npuarc_PC_RANGE]       ca_lp_end_nxt,      // next LP_END from LPcc
  //
  input                       ca_loop_op_r,       // Loop
  input                       ca_loop_evt,        // update LP_START/LP_END
  input     [`npuarc_PC_RANGE]       ca_seq_pc_nxt,      // next LP_START from LPcc
  
  ////////// Committed and next auxiliary register values ////////////////////
  //
  output reg                  ca_aux_pc_wen,      // Debug write enable for PC
  
  output    [`npuarc_DATA_RANGE]     ar_aux_bta_r,       // BTA aux register

  input                       ca_triple_fault_set,// from excpn_pipe -> _tf_ bit
  input                       hlt_do_unhalt,
//output reg                  dbg_tf_r,           // = ar_aux_debug_r[`DEBUG_TF]
  input     [15:0]            ecc_flt_status,     // ECC Fault Status 
  output    [`npuarc_DATA_RANGE]     ar_aux_ecc_ctrl_r,  // ECC aux register
  input     [`npuarc_DATA_RANGE]     ecc_sbe_count_r,    // ECC single bit err count
  output reg[7:0]             ecc_sbe_clr,
  output                      ecc_sbe_dmp_clr,  // ECC single bit error count clear for DMP
  output reg [7:0]  aux_memseg_r,
  output    [`npuarc_DATA_RANGE]     ar_aux_stack_base_r,// STACK_BASE aux register
  output    [`npuarc_DATA_RANGE]     ar_aux_stack_top_r, // STACK_TOP  aux register
  output                      ar_sc_r,            // Stack Checking Enabled

  output                      ar_ae_r,            // Stack Checking Enabled

  output    [`npuarc_APS_RANGE]      ar_asr_r,           // ASR bits of Debug

  input                       aps_aux_serial_sr,  // SR insn must flush pipe
  input     [`npuarc_APS_RANGE]      aps_aux_written,    // Indicates write to AP[i]
  input     [`npuarc_APS_RANGE]      aps_status,         // AP Triggered
  input                       ca_ap_excpn_r,      // AP Excpn
  input                       aps_halt_ack,       // AP Halt Acknowleged
  output    [`npuarc_DATA_RANGE]     ar_aux_jli_base_r,  // JLI_BASE aux register
  output    [`npuarc_DATA_RANGE]     ar_aux_ldi_base_r,  // LDI_BASE aux register
  output    [`npuarc_DATA_RANGE]     ar_aux_ei_base_r,   // EI_BASE aux register

  input  [21:0]               intvbase_in,   // for external interrupt vector base
  output reg [21:0]           intvbase_in_r, // registered at 1st clk after reset

  output    [`npuarc_DATA_RANGE]     ar_aux_irq_ctrl_r,  // IRQ_CTRL aux register
  output    reg               ar_aux_irq_ctrl_upt_r, //write pulse of irq_ctrl
  output    reg               irq_ctrl_wen,
  input                       wa_uopld_jli_base,  // LD into JLI_BASE
  input                       wa_uopld_ldi_base,  // LD into LDI_BASE
  input                       wa_uopld_ei_base,   // LD into EI_BASE
  input                       wa_uopld_lp_start,  // LD into LP_START
  input                       wa_uopld_lp_end,    // LD into LP_END
  //
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Not all bits used
  input      [`npuarc_DATA_RANGE]    wa_uopld_data,      // UOP LD data into AUX. reg
  // leda NTL_CON13C on

  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Potential used from irq unit
  // spyglass disable_block W240
  // SMD: inputs declared but not used
  // SJ:  Potential used from irq unit
  input     [`npuarc_DATA_RANGE]     ar_aux_icause0_r,// (from alb_irq_unit)
  input     [`npuarc_DATA_RANGE]     ar_aux_icause1_r,// (from alb_irq_unit)
  input     [`npuarc_DATA_RANGE]     ar_aux_icause2_r,// (from alb_irq_unit)
  // spyglass enable_block W240
  // leda NTL_CON13C on
  // leda NTL_CON13C off
  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  Not all bits used
  input     [`npuarc_DATA_RANGE]     ca_irq_act_nxt,     // next IRQ ACT state
  // leda NTL_CON13C on
  // leda NTL_CON37 on
  output    [`npuarc_DATA_RANGE]     ar_aux_irq_act_r,   // IRQ_ACT aux register
  input                       ca_int_enter_evt,
  input                       ca_int_exit_evt,


  output reg[`npuarc_DATA_RANGE]     ar_aux_debug_r,     // DEBUG aux register
  output reg[`npuarc_DATA_RANGE]     ar_aux_debugi_r,    // DEBUGI aux register
  output reg                  dbg_we_r,           // WE bit of Debug
  output reg                  dbg_wf_r,           // WF bit of Debug


  output    [`npuarc_DATA_RANGE]     ar_aux_intvbase_r,  // INTVBASE aux register
  output    [`npuarc_DATA_RANGE]     ar_aux_lp_start_r,  // LP_START aux register
  output    [`npuarc_DATA_RANGE]     ar_aux_lp_end_r     // LP_END aux register
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Auxiliary registers, next state, select and write enable signals         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg     [`npuarc_PC_RANGE]         aux_lp_start_r;       // LP_START register
reg     [`npuarc_PC_RANGE]         aux_lp_start_nxt;
reg     [`npuarc_PC_RANGE]         aux_lp_start_next;
reg                         lp_start_sel;
reg                         lp_start_wen;

reg     [`npuarc_PC_RANGE]         aux_lp_end_r;         // LP_END register
reg     [`npuarc_PC_RANGE]         aux_lp_end_nxt;
reg     [`npuarc_PC_RANGE]         aux_lp_end_next;
reg                         lp_end_sel;
reg                         lp_end_wen;

reg     [`npuarc_DATA_RANGE]       aux_ecc_ctrl_r;       // ECC CTRL register
reg     [`npuarc_DATA_RANGE]       aux_ecc_ctrl_next;       // ECC CTRL register
reg     [`npuarc_DATA_RANGE]       aux_ecc_ctrl_nxt;
reg                         ecc_ctrl_sel;
reg                         ecc_ctrl_wen;
reg                         ecc_sbe_wen;
reg                         ecc_sbe_sel;
reg     [`npuarc_DATA_RANGE]       aux_ecc_sbe_count_r;       // ECC SBE COUNT register
reg     [`npuarc_DATA_RANGE]       aux_ecc_sbe_count_nxt;
reg     [2:0]               ecc_sbe_dmp_clr_r;
reg     [2:0]               ecc_sbe_dmp_clr_nxt;

reg     [`npuarc_DATA_RANGE]       aux_ustack_base_r;    // USTACK_BASE register
reg     [`npuarc_DATA_RANGE]       aux_ustack_base_nxt;
reg     [`npuarc_DATA_RANGE]       aux_ustack_base_next;
reg                         ustack_base_sel;
reg                         ustack_base_wen;

reg     [`npuarc_DATA_RANGE]       aux_ustack_top_r;     // USTACK_TOP register
reg     [`npuarc_DATA_RANGE]       aux_ustack_top_nxt;
reg     [`npuarc_DATA_RANGE]       aux_ustack_top_next;
reg                         ustack_top_sel;
reg                         ustack_top_wen;

reg     [`npuarc_DATA_RANGE]       aux_kstack_base_r;    // KSTACK_BASE register
reg     [`npuarc_DATA_RANGE]       aux_kstack_base_nxt;
reg     [`npuarc_DATA_RANGE]       aux_kstack_base_next;
reg                         kstack_base_sel;
reg                         kstack_base_wen;

reg     [`npuarc_DATA_RANGE]       aux_kstack_top_r;     // KSTACK_BASE register
reg     [`npuarc_DATA_RANGE]       aux_kstack_top_nxt;
reg     [`npuarc_DATA_RANGE]       aux_kstack_top_next;
reg                         kstack_top_sel;
reg                         kstack_top_wen;

reg                         after_cycle1;
reg     [`npuarc_PC_MSB:10]        aux_intvbase_r;       // Int. vector base
reg     [`npuarc_PC_MSB:10]        aux_intvbase_nxt;
reg     [`npuarc_PC_MSB:10]        aux_intvbase_next;
reg                         intvbase_sel;
reg                         intvbase_wen;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range:0-2
// LJ:  Some bits unused
reg     [`npuarc_DATA_RANGE]       aux_bta_r;            // BTA register
reg     [`npuarc_DATA_RANGE]       aux_bta_next;            // BTA register
// leda NTL_CON32 on
reg     [`npuarc_DATA_RANGE]       aux_bta_nxt;
reg                         bta_sel;
reg                         bta_wen;

wire     [31:0]             aux_cluster_id_r;

///// aux registers for exceptions ///////////////////////////////////////////
//
reg                         eret_sel;
reg                         eret_wen;

reg                         erstatus_sel;
reg                         erstatus_wen;

reg                         erbta_sel;
reg                         erbta_wen;

reg                         ecr_sel;
reg                         ecr_wen;

reg                         efa_sel;
reg                         efa_wen;

reg                         efae_sel;
reg                         efae_wen;

///// aux registers for interrupts ///////////////////////////////////////////

reg     [`npuarc_DATA_RANGE]       aux_user_sp_r;        // User SP register
reg     [`npuarc_DATA_RANGE]       aux_user_sp_nxt;
reg     [`npuarc_DATA_RANGE]       aux_user_sp_next;
reg                         user_sp_sel;
reg                         user_sp_wen;
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Not all bits of bus used
reg     [`npuarc_IRQ_CTRL_RANGE]   aux_irq_ctrl_r;       // IRQ_CTRL register
  // leda NTL_CON32 on
reg     [`npuarc_IRQ_CTRL_RANGE]   aux_irq_ctrl_nxt;
reg     [`npuarc_IRQ_CTRL_RANGE]   aux_irq_ctrl_next;
reg                         irq_ctrl_sel;
//reg                         irq_ctrl_wen;

reg     [`npuarc_IRQ_ACT_RANGE]    aux_irq_act_r;       // IRQ_ACT register
reg     [`npuarc_IRQ_ACT_RANGE]    aux_irq_act_nxt;
reg     [`npuarc_IRQ_ACT_RANGE]    aux_irq_act_next;
reg                         irq_act_sel;
reg                         irq_act_wen;
reg                         irq_act_u_wen;

//reg                         ca_int_prologue_evt;
//reg                         ca_int_enter_evt;
//reg                         ca_int_exit_evt;


reg     [`npuarc_PC_MSB:2]         aux_jli_base_r;       // JLI_BASE register
reg     [`npuarc_PC_MSB:2]         aux_jli_base_nxt;
reg     [`npuarc_PC_MSB:2]         aux_jli_base_next;
reg                         jli_base_sel;
reg                         jli_base_wen;

reg     [`npuarc_ADDR_MSB:2]       aux_ldi_base_r;       // LDI_BASE register
reg     [`npuarc_ADDR_MSB:2]       aux_ldi_base_nxt;
reg     [`npuarc_ADDR_MSB:2]       aux_ldi_base_next;
reg                         ldi_base_sel;
reg                         ldi_base_wen;

reg     [`npuarc_PC_MSB:2]         aux_ei_base_r;        // EI_BASE register
reg     [`npuarc_PC_MSB:2]         aux_ei_base_nxt;
reg     [`npuarc_PC_MSB:2]         aux_ei_base_next;
reg                         ei_base_sel;
reg                         ei_base_wen;

reg                         dbg_halt_nxt;

////////////////////////////////////////////////////////////////////////////
// DEBUG aux register                                                     //
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// The Debug auxiliary register is primarily for the use of the debug     //
// host. The host can read and write to this register, but only four      //
// bits (UB, RA, IS and FH) are writable.                                 //
//                                                                        //
// The Debug auxiliary register comprises the following bits              //
//                                                                        //
// FH : set by the Host by writing 1 to DEBUG.FH                          //
//    : cannot be cleared, but always reads as 0                          //
//    (no real storage needed)                                            //
//                                                                        //
// IS : set by the host to cause a single instruction to be executed      //
//    : cleared when the processor halts after single-stepping.           //
//                                                                        //
// RA : set to 1 on reset and writable by the Host.                       //
//                                                                        //
// ZZ : set by the processor when it enters the 'sleep' state.            //
//    : cleared by the processor when it leaves the 'sleep' state.        //
//                                                                        //
// UB : set by the Host by writing 1 to DEBUG.UB, to enable BREAK         //
//      instructions when in User mode.                                   //
//    : cleared by the Host, and on reset.                                //
//                                                                        //
// SM:  sleep mode bits. Set by the processor upon commiting a SLEEP      //
//      instruction                                                       //
//                                                                        //
// BH : set by the processor if a BREAK instruction halts the processor   //
//    : cleared by the processor when STATUS32.H is cleared.              //
//                                                                        //
// SH : set by the processor when it is halted due to a FLAG instruction. //
//    : cleared whenever the STATUS32.H bit is cleared for any reason.    //
//                                                                        //
// LD : non-writable, and always reads as 0 in this implementation.       //
//    (no real storage needed)                                            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
reg                         dbg_fh_nxt;       // FH bit of Debug

reg                         dbg_is_r;         // IS bit of Debug
reg                         dbg_is_nxt;
//reg                         dbg_is;
reg                         dbg_is_clr;

reg                         dbg_ub_r;         // UB bit of Debug
reg                         dbg_ub_nxt;

reg                         dbg_ra_r;         // RA bit of Debug
reg                         dbg_ra_nxt;

reg [`npuarc_EXT_SMODE_RANGE]      dbg_sm_r;         // SM bits of Debug
reg [`npuarc_EXT_SMODE_RANGE]      dbg_sm_nxt;
reg                         dbg_sm_cg0;

reg                         dbg_zz_r;         // ZZ bit of Debug
reg                         dbg_zz_nxt;

reg                         dbg_we_nxt;

reg                         dbg_wf_nxt;

reg                         dbg_bh_r;         // BH bit of Debug
reg                         dbg_bh_nxt;
reg                         dbg_sh_r;         // SH bit of Debug
reg                         dbg_sh_nxt;
reg                         dbg_sh_set_r;     // set DEBUG.SH 
reg                         dbg_sh_set_nxt;   // set SH next cycle
reg                         dbg_sh_clr;       // clr DEBUG.SH
reg                         dbg_eh_r;         // EH bit of Debug
reg                         dbg_eh_nxt;

reg                         dbg_tf_r;         // Triple Fault bit (27) of Debug Reg
reg                         dbg_tf_nxt;
reg                         dbg_tf_set;       // set DEBUG.TF 
reg                         dbg_tf_clr;       // clr DEBUG.TF

reg     [`npuarc_APS_RANGE]        dbg_asr_r;        // ASR bits of Debug
reg     [`npuarc_APS_RANGE]        dbg_asr_nxt;
reg                         dbg_ah_r;         // AH bit of Debug
reg                         dbg_ah_nxt;
reg                         aps_wen;          // Enable APS/AH updates
// leda NTL_CON13A off
// LMD: non driving internal net Range
// leda NTL_CON12A off
// LMD: undriven internal net Range
// LJ:  not all bits used in all configs
reg     [7:0]               dbg_asr_sr_data;  // 8-bit ASR write data
// leda NTL_CON12A on
// leda NTL_CON13A on

reg                         dbgi_e_r;             // E field of DebugI
reg                         dbgi_e_nxt;
reg                         debugi_sel;           // SR selects AUX_DEBUGI
reg                         debugi_wen;           // SR writes AUX_DEBUGI

//
reg                         aux_pc_sel;           // Debug SR to PC aux reg.
reg                         status32_sel;         // Debug SR to STATUS32
reg                         status32_wen;
reg                         debug_sel;            // SR selects AUX_DEBUG
reg                         memseg_sel;            // SR selects AUX_DEBUG
reg                         memseg_wen;           // SR writes AUX_DEBUG
reg                         debug_wen;            // SR writes AUX_DEBUG
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @aux_debug_nxt_PROC:                                                     //
//                                                                          //
// Combinatorial process to calculate/derive the state updates to the       //
// DEBUG and DEBUGI aux. registers.                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: aux_debug_nxt_PROC

  // -------------------------------------------------------------------------
  // DEBUG.FH - (force halt)
  //
  dbg_fh_nxt        = (debug_wen & wa_sr_data_r[`npuarc_DEBUG_FH])      // SR
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.IS - (instruction step)
  //
//  dbg_is            = 1'b0
//                    ;
  // Derive the condition on which AUX_DEBUG.IS should be cleared
  //
  dbg_is_clr        = ca_finish_sgl_step
                    | ca_cmt_brk_evt
                    ;

  dbg_is_nxt        = (debug_wen & wa_sr_data_r[`npuarc_DEBUG_IS])      // SR
                    | (dbg_is_r & (~dbg_is_clr))
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.RA - (reset applied)
  //
  //
  // (Register can only be updated by an external host, gated by debug_wen)
  //
  dbg_ra_nxt        = wa_sr_data_r[`npuarc_DEBUG_RA]                    // SR
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.UB - (user breakpoint)
  //
  //
  // (Register can only be updated by an external host, gated by debug_wen)
  //
  dbg_ub_nxt        = wa_sr_data_r[`npuarc_DEBUG_UB]                    // SR
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.SM - (sleep mode)
  //
  dbg_sm_cg0        = ca_sleep_evt
                    ;

  dbg_sm_nxt        = ca_src1_r [`npuarc_SMODE_RANGE]
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.ZZ - (sleep bit)
  //
  dbg_zz_nxt        = (~sleep_hlt_wake)
                    & (dbg_zz_r | ca_sleep_evt)
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.WE - (waiting for event, and hence asleep)
  //
  dbg_we_nxt        = (~wevt_wakeup_r)
                    & (~sleep_hlt_wake)
                    & (dbg_we_r | ca_wevt_evt)
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.WF - (waiting for lock-flag to be cleared, and hence asleep)
  //
  dbg_wf_nxt        = (~wlfc_wakeup)
                    & (~sleep_hlt_wake)
                    & (dbg_wf_r | ca_wlfc_evt)
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.BH - (break halt)
  //
  // Set on the assertion of a breakpoint and cleared when STATUS32.H
  // is cleared.
  //
  dbg_bh_nxt        = (   ca_cmt_brk_evt                           // set
                        & !(   1'b0
                             | aps_halt_ack
                           )
                        & ca_brk_op_r
                      ) 
                    | (   dbg_bh_r                               // clear
                        & (~(   wa_aux_status32_pass
                             & (~wa_aux_status32_nxt[`npuarc_P_H_FLAG])
                           ))
                      )
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.SH - (self halt)
  //
  // (1) Set on Halt set by Flag instruction, and retain until cleared
  //
  // (2) Cleared when STATUS32.H is written 0 by debug SR operation 
  // (3) or when a Single Step Instruction is completed.
  
  // Derive the condition under which AUX_DEBUG.SH should be set in the 
  // write-back stage. The dbg_sh_set_nxt signal is delayed by 1 cycle
  // to allow dbg_sh_r to become set after dbd_is_clr has been rescinded.
  //
  dbg_sh_set_nxt     = ca_in_kflag                               // (1)
                     & ca_normal_evt
                     & wa_aux_status32_pass
                     & wa_aux_status32_nxt[`npuarc_P_H_FLAG]
                     ;
                     
  dbg_sh_clr        = (    wa_aux_status32_pass                  // (2)
                        & (!wa_aux_status32_nxt[`npuarc_P_H_FLAG])
                      )
                    | dbg_is_clr                                 // (3)
                    ;
                        
  dbg_sh_nxt        = dbg_sh_set_r                               // (1)
                    | (dbg_sh_r & (!dbg_sh_clr))                   // (2,3)
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.TF - (Triple fault)
  //
  // (1) Set on detection of triple fault in excpn_pipe
  // (2) Cleared on halt exit (by debug host or run req pin)
  
  dbg_tf_set        = ca_triple_fault_set;
  dbg_tf_clr        = hlt_do_unhalt;             // ca_async_run_evt
                        
  dbg_tf_nxt        = dbg_tf_set
                    | (dbg_tf_r & (!dbg_tf_clr))
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.EH - (External halt)
  //
  dbg_eh_nxt        = sys_halt_ack_r                             // set
                    | (   dbg_eh_r                               // clear
                        & (~(   wa_aux_status32_pass
                             & (~wa_aux_status32_nxt[`npuarc_P_H_FLAG])
                           )) 
                      )
                    ;

  // -------------------------------------------------------------------------
  // DEBUG.ASR - 
  //
  // Set the next ASR field in the DEBUG register to the identity of any
  // Actionpoint that triggered, but clear bit i if Actionpoint i has any
  // of its auxiliary registers written to (indicated by aps_aux_written[i]).
  //
  // Firstly select the subset of the 8-bit SR data field that may be assigned 
  // to DEBUG.ASR. This is restricted to the number of Actionpoints configured,
  // when a sub-field of dbg_asr_sr_data is assigned to dbg_asr_nxt.
  //
  dbg_asr_sr_data   = wa_sr_data_r [`npuarc_DEBUG_ASR];
  
  casez ({  debug_wen
          ,   ( 1'b0
              | ca_ap_excpn_r 
              )
            & excpn_evts[`npuarc_INTEVT_PROLOGUE]
          , ( 1'b0
            | aps_halt_ack
            )
          , aps_aux_serial_sr
         })
    4'b1?_??: dbg_asr_nxt  = dbg_asr_sr_data[`npuarc_APS_RANGE];
    4'b01_??: dbg_asr_nxt  = aps_status;
    4'b00_1?: dbg_asr_nxt  = aps_status;
    4'b00_01: dbg_asr_nxt  = dbg_asr_r & (~aps_aux_written);
    default:  dbg_asr_nxt  = dbg_asr_r;
  endcase
    
  // -------------------------------------------------------------------------
  // DEBUG.AH - (Actionpoint halt)
  //
  dbg_ah_nxt        =  debug_wen
                    ? wa_sr_data_r [`npuarc_DEBUG_AH]
                    : ( (1'b0
                        | aps_halt_ack
                        )
                      | (dbg_ah_r & ar_aux_status32_r[`npuarc_H_FLAG])
                      )
                    ;


  // -------------------------------------------------------------------------
  // DEBUGI.E - (exception breakpoint)
  //
  // (Register can only be updated by an external host, gated by debugi_wen)
  //
  dbgi_e_nxt        = wa_sr_data_r[`npuarc_DEBUGI_E]
                    ;

end // block: aux_debug_nxt_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @ar_aux_debug_PROC: DEBUG/DEBUGI aux. registers                          //
//                                                                          //
// Combinatorial process to map internal debug registers to their           //
// architectural equivalents.                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: ar_aux_debug_PROC

  // AUX_DEBUG
  //
  ar_aux_debug_r              = `npuarc_DATA_SIZE'd0;
  ar_aux_debug_r[`npuarc_DEBUG_TF]   = dbg_tf_r;
  ar_aux_debug_r[`npuarc_DEBUG_SH]   = dbg_sh_r;
  ar_aux_debug_r[`npuarc_DEBUG_BH]   = dbg_bh_r;
  ar_aux_debug_r[`npuarc_DEBUG_UB]   = dbg_ub_r;
  ar_aux_debug_r[`npuarc_DEBUG_SM]   = dbg_sm_r;
  ar_aux_debug_r[`npuarc_DEBUG_ZZ]   = dbg_zz_r;
  ar_aux_debug_r[`npuarc_DEBUG_RA]   = dbg_ra_r;
  ar_aux_debug_r[`npuarc_DEBUG_EH]   = dbg_eh_r;
  ar_aux_debug_r[`npuarc_DEBUG_IS]   = dbg_is_r;
  ar_aux_debug_r[`npuarc_DEBUG_ASR]  = dbg_asr_r;
  ar_aux_debug_r[`npuarc_DEBUG_AH]   = dbg_ah_r;

  // AUX_DEBUGI
  //
  ar_aux_debugi_r               = `npuarc_DATA_SIZE'd0;
  ar_aux_debugi_r[`npuarc_DEBUGI_E]    = dbgi_e_r;

end // block: ar_aux_debug_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Assignment of architectural auxiliary registers to 32-bit vectors        //
// which define the values of ALL core auxiliary registers when read by an  //
// LR instruction. This includes core registers that are implemented in the //
// CA/WA stages due to special conditions for their update.                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire    [`npuarc_DATA_RANGE]       ar_aux_identity_r;
//wire    [`DATA_RANGE]       ar_aux_pc_r;
wire    [`npuarc_DATA_RANGE]       ar_aux_user_sp_r;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// IDENTITY (0x4) aux. register                                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign ar_aux_identity_r  = { `npuarc_CHIPID,
                              arcnum,
                              `npuarc_ARCVER
                            }
                          ;
//!BCR { num: 4, val: 84, name: "IDENTITY" }

assign ar_aux_lp_start_r  = {
                              aux_lp_start_r, 1'b0
                            }
                          ;

assign ar_aux_lp_end_r    = {
                              aux_lp_end_r, 1'b0
                            }
                          ;

assign ar_aux_stack_base_r = ar_aux_status32_r[`npuarc_U_FLAG]
                           ? aux_ustack_base_r 
                           : aux_kstack_base_r
                           ;
                           
assign ar_aux_stack_top_r  = ar_aux_status32_r[`npuarc_U_FLAG] 
                           ? aux_ustack_top_r  
                           : aux_kstack_top_r
                           ;

// Note: ar_aux_pc_r can be read correctly at CA or WA, but not
//       at X3, as there is currently no speculative copy of PC at X3.
//
/*
assign ar_aux_pc_r        = {
                              ar_pc_r, 1'b0
                            }
                          ;
*/
assign ar_aux_intvbase_r  = {
                              aux_intvbase_r, 10'd0
                            }
                          ;

assign ar_aux_bta_r       = {
                              aux_bta_r[`npuarc_PC_RANGE], 1'b0
                            }
                          ;

assign ar_aux_jli_base_r  = { aux_jli_base_r, 2'b00 };
assign ar_aux_ldi_base_r  = { aux_ldi_base_r, 2'b00 };
assign ar_aux_ei_base_r   = { aux_ei_base_r,  2'b00 };
assign aux_cluster_id_r   = { 24'b0, clusternum };
//!BCR { num: 664, val: 0, name: "CLUSTER_ID" }
assign ar_aux_user_sp_r   = aux_user_sp_r;

assign ar_aux_irq_ctrl_r  = {  `npuarc_IRQ_CTRL_UNUSED'd0
                              , aux_irq_ctrl_r[`npuarc_IRQ_CTRL_MSB]
                              , 1'b0                              
                              , aux_irq_ctrl_r[`npuarc_IRQ_CTRL_MSB-2:5]
                              , 4'd0
                              , aux_irq_ctrl_r[4:0]
                            }
                          ;

assign ar_aux_irq_act_r   = {   aux_irq_act_r[`npuarc_IRQ_ACT_MSB]
                              , `npuarc_IRQ_ACT_UNUSED'd0
                              , aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]
                            }
                          ;

//wire  in_dslot_r;
//wire  in_eslot_r;

//assign in_dslot_r = ar_aux_status32_r[`DE_FLAG];
//assign in_eslot_r = ar_aux_status32_r[`ES_FLAG];
assign ar_sc_r    = ar_aux_status32_r[`npuarc_SC_FLAG];

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic for selecting aux register value for an LR           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : aux_lr_perm_PROC

  core_aux_rdata      = `npuarc_DATA_SIZE'd0;
  core_aux_k_rd       = 1'b0;
  core_aux_k_wr       = 1'b0;
  core_aux_unimpl     = 1'b1;
  core_aux_illegal    = 1'b0;
  core_aux_serial_sr  = 1'b0;
  core_aux_strict_sr  = 1'b0;
  core_aux_stall      = 1'b0;


  if (aux_cr1_ren_r == 1'b1)  // Region 1
      case ({8'h00, aux_core_raddr_r [3:0]})

        `npuarc_LP_START_AUX:      // ANY_RW
        begin
          core_aux_rdata    = ar_aux_lp_start_r;
          core_aux_strict_sr= 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_stall    = ca_loop_op_r;
        end

        `npuarc_LP_END_AUX:        // ANY_RW
        begin
          core_aux_rdata    = ar_aux_lp_end_r;
          core_aux_strict_sr= 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_stall    = ca_loop_op_r;
        end

        `npuarc_IDENTITY_AUX:      // ANY_READ
        begin
          core_aux_rdata    = ar_aux_identity_r;
          core_aux_illegal  = aux_write;
          core_aux_unimpl   = 1'b0;
        end

        `npuarc_DEBUG_AUX:         // K_READ + DBG_WRITE
        begin
          core_aux_rdata    = ar_aux_debug_r;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_illegal  = aux_write 
                            & (~db_active_r)
                            ;
          core_aux_unimpl   = 1'b0;
        end

        `npuarc_MEMSEG_AUX:         // for MEMSEG
         begin
           core_aux_rdata    = { 24'd0
                               , aux_memseg_r
                               };
           core_aux_k_wr     = 1'b1;
           core_aux_k_rd     = 1'b1;
           core_aux_illegal  = aux_write 
                            & (~db_active_r)
                             ;
           core_aux_unimpl   = 1'b0;
         end


        `npuarc_PC_AUX:            // K_READ
        begin
          core_aux_rdata            = `npuarc_DATA_SIZE'd0;
          core_aux_rdata[`npuarc_PC_RANGE] = db_active_r
                                    ? ar_pc_r
                                    : (ca_ei_op_r
                                       ?  ca_target_r
                                       :  x3_src0_r[`npuarc_PC_RANGE]
                                      )
                                    ;
          core_aux_illegal          = aux_write & (~db_active_r);
          core_aux_unimpl           = 1'b0;
        end

        `npuarc_STATUS32_AUX:      // K_MASKED + DBG_WRITE
        begin
          // Read STATUS32 flags, but see only the ZNCV flags if in User mode
          // The debugger is able to read the full content of STATUS32
          //
          core_aux_rdata    = (   ar_aux_status32_r[`npuarc_U_FLAG]
                                & (~db_active_r)
                              )
                            ? (`npuarc_DATA_SIZE'h00000f00 & ar_aux_status32_r)
                            : ar_aux_status32_r
                            ;

          // Stall Core Aux LR if there is a active Status32 update in Commit
          core_aux_stall      = ca_aux_s32_stall & (~db_active_r);
          // Writeable within a debug operation, or within an epilogue
          // sequence (on restoration of the previously saved STATUS32).
          //
          core_aux_illegal  = aux_write & (~db_active_r);
          core_aux_unimpl   = 1'b0;
        end

        `npuarc_USER_SP_AUX:       // K_RW
        begin
          core_aux_rdata    = ar_aux_user_sp_r;

          // To access the USER_SP aux register, kernel permissions are
          // required when addressing directly. This register can
          // be changed in normal user-mode, however only if executing
          // -strictly- within the context of an interrupt/exception
          // prologue/epilogue uop sequence.
          //
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_unimpl   = 1'b0;
        end

        `npuarc_IRQ_CTRL_AUX:      // K_RW
        begin
          core_aux_rdata    = `npuarc_DATA_SIZE'd0
                            | ar_aux_irq_ctrl_r
                            ;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_serial_sr= 1'b1;
          core_aux_strict_sr= 1'b1;
        end

        `npuarc_STAT32P0_AUX:
        begin
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;

          core_aux_rdata    = `npuarc_DATA_SIZE'd0
                            ;
          core_aux_unimpl   = 1'b0
                            ;
        end

        `npuarc_DEBUGI_AUX:        //  K_READ + DBG_WRITE
        begin
          core_aux_rdata    = ar_aux_debugi_r;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_illegal  = aux_write & (~db_active_r);
          core_aux_unimpl   = 1'b0;
        end

       default:
       begin
   
      core_aux_k_rd       = 1'b0;
      core_aux_k_wr       = 1'b0;
      core_aux_unimpl     = 1'b1;
      core_aux_illegal    = 1'b0;
      core_aux_serial_sr  = 1'b0;
      core_aux_strict_sr  = 1'b0;

       end
  endcase // Region 1

  if (aux_cr2_ren_r == 1'b1)  // Region 2 : {01F, 025, 043}
    case ({5'h00, aux_core_raddr_r [6:0]})

        `npuarc_INTVBASE_AUX:      // K_RW
        begin
          core_aux_rdata    = ar_aux_intvbase_r;
          core_aux_k_rd     = 1'b1;
          core_aux_k_wr     = 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_serial_sr= 1'b1;
        end

        `npuarc_ECC_SBE_COUNT_AUX:
        begin
          core_aux_rdata    = aux_ecc_sbe_count_r;
          core_aux_k_rd     = 1'b1;
          core_aux_k_wr     = 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_serial_sr= 1'b1;
        end
        `npuarc_ECC_CTRL_AUX:      // ANY_READ
        begin
          core_aux_rdata    = aux_ecc_ctrl_r[`npuarc_DATA_RANGE];
          core_aux_k_rd     = 1'b1;
          core_aux_k_wr     = 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_serial_sr= 1'b1;
        end

        `npuarc_IRQ_ACT_AUX:       // K_RW
        begin
          core_aux_rdata    = ar_aux_irq_act_r;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_serial_sr= 1'b1;
          core_aux_strict_sr= 1'b1; 
        end

       default:
       begin
   
      core_aux_k_rd       = 1'b0;
      core_aux_k_wr       = 1'b0;
      core_aux_unimpl     = 1'b1;
      core_aux_illegal    = 1'b0;
      core_aux_serial_sr  = 1'b0;
      core_aux_strict_sr  = 1'b0;

       end
  endcase // Region 2


  if (aux_cr3_ren_r == 1'b1)  // Region 3 : aux range: 260-267
    case ({9'h04c, aux_core_raddr_r [2:0]})
        `npuarc_USTACK_BASE_AUX:   // K_RW
        begin
          core_aux_rdata    = aux_ustack_base_r;
          core_aux_k_wr     = 1'b1;
          core_aux_serial_sr= 1'b1;
          core_aux_unimpl   = 1'b0;
        end

        `npuarc_USTACK_TOP_AUX:    // K_RW
        begin
          core_aux_rdata    = aux_ustack_top_r;
          core_aux_k_wr     = 1'b1;
          core_aux_serial_sr= 1'b1;
          core_aux_unimpl   = 1'b0;
        end

        `npuarc_KSTACK_BASE_AUX:   // K_RW
        begin
          core_aux_rdata    = aux_kstack_base_r;
          core_aux_k_wr     = 1'b1;
          core_aux_serial_sr= 1'b1;
          core_aux_unimpl   = 1'b0;
        end

        `npuarc_KSTACK_TOP_AUX:    // K_RW
        begin
          core_aux_rdata    = aux_kstack_top_r;
          core_aux_k_wr     = 1'b1;
          core_aux_serial_sr= 1'b1;
          core_aux_unimpl   = 1'b0;
        end
       default:
       begin
   
      core_aux_k_rd       = 1'b0;
      core_aux_k_wr       = 1'b0;
      core_aux_unimpl     = 1'b1;
      core_aux_illegal    = 1'b0;
      core_aux_serial_sr  = 1'b0;
      core_aux_strict_sr  = 1'b0;

       end
  endcase // Region 3

  if (aux_cr4_ren_r == 1'b1)  // Region 4 : aux range: 290-298
    case ({8'h29, aux_core_raddr_r [3:0]})

        `npuarc_JLI_BASE_AUX:      // ANY_RW
        begin
          core_aux_rdata    = ar_aux_jli_base_r;
          core_aux_serial_sr= 1'b1;
          core_aux_unimpl   = 1'b0;
        end
 
        `npuarc_LDI_BASE_AUX:      // ANY_RW
        begin
          core_aux_rdata    = ar_aux_ldi_base_r;
          core_aux_serial_sr= 1'b1;
          core_aux_unimpl   = 1'b0;
        end
 
        `npuarc_EI_BASE_AUX:       // ANY_RW
        begin
          core_aux_rdata    = ar_aux_ei_base_r;
          core_aux_serial_sr= 1'b1;
          core_aux_unimpl   = 1'b0;
        end
        `npuarc_CLUSTER_ID_AUX:    // R
        begin
          core_aux_rdata    = aux_cluster_id_r;
          core_aux_serial_sr= 1'b1;
          core_aux_illegal  = aux_write;
          core_aux_unimpl   = 1'b0;
        end
        default:
        begin
          core_aux_k_rd       = 1'b0;
          core_aux_k_wr       = 1'b0;
          core_aux_unimpl     = 1'b1;
          core_aux_illegal    = 1'b0;
          core_aux_serial_sr  = 1'b0;
          core_aux_strict_sr  = 1'b0;
        end

  endcase // Region 4

  if (aux_cr5_ren_r == 1'b1)  // Region 5 : aux range: 400-404, 405, 412
    case ({7'h20, aux_core_raddr_r [4:0]})

        `npuarc_ERET_AUX:          // K_RW
        begin
          core_aux_rdata    = ar_aux_eret_r;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_serial_sr= 1'b1;
        end

        `npuarc_ERBTA_AUX:         // K_RW
        begin
          core_aux_rdata    = ar_aux_erbta_r;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_serial_sr= 1'b1;
        end

        `npuarc_ERSTATUS_AUX:      // K_RW
        begin
          core_aux_rdata    = ar_aux_erstatus_r;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_strict_sr= 1'b1;
        end

        `npuarc_ECR_AUX:           // K_RW
        begin
          core_aux_rdata    = ar_aux_ecr_r;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_unimpl   = 1'b0;
        end

        `npuarc_EFA_AUX:           // K_RW
        begin
          core_aux_rdata    = ar_aux_efa_r;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_unimpl   = 1'b0;
        end


        `npuarc_EFAE_AUX:          // K_RW
        begin
          core_aux_rdata    = ar_aux_efae_r;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_unimpl   = 1'b0;
        end

        `npuarc_BTA_AUX:           // K_RW
        begin
          core_aux_rdata    = ar_aux_bta_r;
          core_aux_k_wr     = 1'b1;
          core_aux_k_rd     = 1'b1;
          core_aux_unimpl   = 1'b0;
          core_aux_strict_sr= 1'b1;
          // Stall on BTA RAW Hazard
          // Stall for Exception BTA not required
          //   as pipe is flushed on Exception 
          core_aux_stall    =  ca_dslot_r
                             | ca_ei_op_r
                             ;
        end
       default:
       begin
   
      core_aux_k_rd       = 1'b0;
      core_aux_k_wr       = 1'b0;
      core_aux_unimpl     = 1'b1;
      core_aux_illegal    = 1'b0;
      core_aux_serial_sr  = 1'b0;
      core_aux_strict_sr  = 1'b0;
      core_aux_stall      = 1'b0;

       end
  endcase // Region 5

end // : aux_lr_perm_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Define write-enable signals for all SR-writable core auxiliary regs.   //
//                                                                        //
// Core aux register <reg>, will be updated at the end of the Writeback   //
// stage as a result of an SR instruction, if the <reg>_wen signal is     //
// asserted.                                                              //
//                                                                        //
// Certain special aux registers can be updated as a side-effect of a     //
// committing instruction, as that instruction enters the Writeback       //
// stage of the pipeline. These registers have a <reg>_sel signal to      //
// indicate when they are targetted by a WA-stage SR instruction.         //
// These special aux registers' <reg>_wen signal is the OR of their       //
// <reg>_sel signal and the special condition under which they are        //
// updated at the end of the Commit stage. If they are updated by the     //
// CA-stage instruction, then their new value is defined by that stage,   //
// and not by the wa_sr_data_r value.                                     //
//                                                                        //
// The <reg>_sel signals for external special registers are exported as   //
// outputs of this module, and will be used in the modules containing     //
// those special registers to update their values with the wa_sr_data_r   //
// value provided they are not being otherwise updated by the commit of   //
// an instruction or the acceptance of an exception or interrupts at the  //
// Commit stage. Those actions override the write from an SR operation.   //
//                                                                        //
// An SR-related aux-register write will only be enabled in WA if the     //
// corresponding address was deemed legal when the instruction was at     //
// the X3 stage. Hence, no further qualification is required here.        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : aux_sr_sel_PROC

  lp_start_sel        = 1'b0;
  lp_end_sel          = 1'b0;
  ustack_base_sel     = 1'b0;
  ustack_top_sel      = 1'b0;
  kstack_base_sel     = 1'b0;
  kstack_top_sel      = 1'b0;
  debug_sel           = 1'b0;
  memseg_sel          = 1'b0;
  debugi_sel          = 1'b0;
  intvbase_sel        = 1'b0;
  eret_sel            = 1'b0;
  erbta_sel           = 1'b0;
  erstatus_sel        = 1'b0;
  ecr_sel             = 1'b0;
  efa_sel             = 1'b0;
  efae_sel            = 1'b0;
  bta_sel             = 1'b0;
  aux_pc_sel          = 1'b0;
  ecc_ctrl_sel        = 1'b0;
  ecc_sbe_sel         = 1'b0;
  status32_sel        = 1'b0;
  jli_base_sel        = 1'b0;
  jli_base_sel        = 1'b0;
  ldi_base_sel        = 1'b0;
  ei_base_sel         = 1'b0;
  irq_ctrl_sel        = 1'b0;
  user_sp_sel         = 1'b0;
  irq_act_sel         = 1'b0;

  if (aux_core_wen_r == 1'b1)
    case ({1'b0, aux_core_waddr_r})
    `npuarc_LP_START_AUX:    lp_start_sel    = 1'b1;
    `npuarc_LP_END_AUX:      lp_end_sel      = 1'b1;
    `npuarc_USTACK_BASE_AUX: ustack_base_sel = 1'b1;
    `npuarc_USTACK_TOP_AUX:  ustack_top_sel  = 1'b1;
    `npuarc_KSTACK_BASE_AUX: kstack_base_sel = 1'b1;
    `npuarc_KSTACK_TOP_AUX:  kstack_top_sel  = 1'b1;
    `npuarc_DEBUG_AUX:       debug_sel       = 1'b1;
    `npuarc_MEMSEG_AUX:      memseg_sel      = 1'b1;
    `npuarc_DEBUGI_AUX:      debugi_sel      = 1'b1;
    `npuarc_PC_AUX:          aux_pc_sel      = 1'b1;
    `npuarc_ECC_CTRL_AUX:    ecc_ctrl_sel    = 1'b1;
    `npuarc_ECC_SBE_COUNT_AUX: ecc_sbe_sel   = 1'b1;
    `npuarc_STATUS32_AUX:    status32_sel    = 1'b1;
    `npuarc_INTVBASE_AUX:    intvbase_sel    = 1'b1;
    `npuarc_ERET_AUX:        eret_sel        = 1'b1;
    `npuarc_ERBTA_AUX:       erbta_sel       = 1'b1;
    `npuarc_ERSTATUS_AUX:    erstatus_sel    = 1'b1;
    `npuarc_ECR_AUX:         ecr_sel         = 1'b1;
    `npuarc_EFA_AUX:         efa_sel         = 1'b1;
    `npuarc_EFAE_AUX:        efae_sel        = 1'b1;
    `npuarc_BTA_AUX:         bta_sel         = 1'b1;
    `npuarc_JLI_BASE_AUX:    jli_base_sel    = 1'b1;
    `npuarc_LDI_BASE_AUX:    ldi_base_sel    = 1'b1;
    `npuarc_EI_BASE_AUX:     ei_base_sel     = 1'b1;
    `npuarc_IRQ_CTRL_AUX:    irq_ctrl_sel    = 1'b1;
    `npuarc_USER_SP_AUX:     user_sp_sel     = 1'b1;
    `npuarc_IRQ_ACT_AUX:     irq_act_sel     = 1'b1;
    default:
    begin
      lp_start_sel        = 1'b0;
      lp_end_sel          = 1'b0;
      ustack_base_sel     = 1'b0;
      ustack_top_sel      = 1'b0;
      kstack_base_sel     = 1'b0;
      kstack_top_sel      = 1'b0;
      debug_sel           = 1'b0;
      memseg_sel          = 1'b0;
      debugi_sel          = 1'b0;
      intvbase_sel        = 1'b0;
      eret_sel            = 1'b0;
      erbta_sel           = 1'b0;
      erstatus_sel        = 1'b0;
      ecr_sel             = 1'b0;
      efa_sel             = 1'b0;
      efae_sel            = 1'b0;
      bta_sel             = 1'b0;
      aux_pc_sel          = 1'b0;
      ecc_ctrl_sel        = 1'b0;
      status32_sel        = 1'b0;
      jli_base_sel        = 1'b0;
      jli_base_sel        = 1'b0;
      ldi_base_sel        = 1'b0;
      ei_base_sel         = 1'b0;
      irq_ctrl_sel        = 1'b0;
      user_sp_sel         = 1'b0;
      irq_act_sel         = 1'b0;
    end
    endcase // case (aux_core_waddr_r)
end //  aux_sr_sel_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Enabling the committal of Architectural State                          //
//                                                                        //
//  The committal of architectural state is special, in the sense         //
//  that we commit either the result of an instruction or else the        //
//  state change needed when an exception or interrupt takes place.       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : aux_wen_PROC

  //==========================================================================
  // LP_START is written when:
  //
  //  (1). an SR to LP_START is at the Writeback stage, or
  //  (2). an LPcc instruction commits with true predicate, or
  //  (3). an micro-op write to LP_START is committed.
  //
  lp_start_wen      = lp_start_sel                      // (1)
                    | (ca_loop_evt  & ca_normal_evt)    // (2)
                    | (wa_uopld_lp_start)               // (3)
                    ;

  lp_end_wen        = lp_end_sel
                    | (ca_loop_evt  & ca_normal_evt)
                    | (wa_uopld_lp_end)               // & ca_uop_evt)
                    ;

  ecc_ctrl_wen      = ecc_ctrl_sel
                    | (|ecc_flt_status)
                    ;
  ecc_sbe_wen       = ecc_sbe_sel;
  ecc_sbe_clr[0]    = ecc_sbe_sel &&(aux_ecc_sbe_count_nxt[3:0] ==4'b0000);
  ecc_sbe_clr[1]    = (ecc_sbe_sel &&(aux_ecc_sbe_count_nxt[7:4] ==4'b0000)) | ecc_sbe_dmp_clr_r[0];
  ecc_sbe_clr[2]    = ecc_sbe_sel &&(aux_ecc_sbe_count_nxt[11:8]==4'b0000);
  ecc_sbe_clr[3]    = ecc_sbe_sel &&(aux_ecc_sbe_count_nxt[15:12]==4'b0000);
  ecc_sbe_clr[4]    = ecc_sbe_sel &&(aux_ecc_sbe_count_nxt[19:16]==4'b0000);
  ecc_sbe_clr[5]    = (ecc_sbe_sel &&(aux_ecc_sbe_count_nxt[23:20]==4'b0000)) | ecc_sbe_dmp_clr_r[1];
  ecc_sbe_clr[6]    = (ecc_sbe_sel &&(aux_ecc_sbe_count_nxt[27:24]==4'b0000)) | ecc_sbe_dmp_clr_r[2];
  ecc_sbe_clr[7]    = ecc_sbe_sel &&(aux_ecc_sbe_count_nxt[31:28]==4'b0000);
  debug_wen         = debug_sel     & db_active_r;
  memseg_wen        = memseg_sel    & db_active_r;
  debugi_wen        = debugi_sel    & db_active_r;
  ca_aux_pc_wen     = aux_pc_sel    & db_active_r;
  status32_wen      = status32_sel  & db_active_r;

  aps_wen           = debug_wen
                    | (excpn_evts[`npuarc_INTEVT_PROLOGUE] & (1'b1
                      | ca_ap_excpn_r
                      ))
                    | (1'b0
                      | aps_halt_ack
                      )
                    | aps_aux_serial_sr
                    ;

  intvbase_wen      = intvbase_sel
                    ;

  eret_wen          = eret_sel
                    ; 
                   
  erbta_wen         = erbta_sel 
                    ;
  
  erstatus_wen      = erstatus_sel
                    ;


  ecr_wen           = ecr_sel 
                    ;

  efa_wen           = efa_sel
                    | excpn_evts[`npuarc_INTEVT_PROLOGUE]
                    ;


  efae_wen          = efae_sel
                    | excpn_evts[`npuarc_INTEVT_PROLOGUE]
                    ;


  // aux_bta_r is written whenever there is an SR to that register,
  // or when a taken branch with delay-slot commits normally,
  // or when aux_bta_r is restored from an exception bta register.
  // It is guaranteed that none of these conditions can be true
  // when committing a BRK or BRK_S instruction, and this prevents
  // the aux_bta_r register from updating on a break operation.
  //
  bta_wen           = bta_sel
                    | excpn_evts[`npuarc_INTEVT_EXIT]
                    | ( ( ca_normal_evt | ca_uop_evt)
                        & ( (ca_br_taken & ca_dslot_r)
                          | cmt_0_ei_evt)
                       )
                    ;

  jli_base_wen      = jli_base_sel
                    | (wa_uopld_jli_base)               // & ca_uop_evt)
                    ;

  ldi_base_wen      = ldi_base_sel
                    | (wa_uopld_ldi_base)               // & ca_uop_evt)
                    ;

  ei_base_wen       = ei_base_sel
                    | (wa_uopld_ei_base)               // & ca_uop_evt)
                    ;

  ustack_base_wen   = ustack_base_sel ;
  ustack_top_wen    = ustack_top_sel;
  kstack_base_wen   = kstack_base_sel;
  kstack_top_wen    = kstack_top_sel;

  irq_ctrl_wen      = irq_ctrl_sel;

  user_sp_wen       = user_sp_sel;

  // The IRQ_ACT_AUX is modified when:
  //
  //  (1) Explicitly addressed as the destination of an SR
  //      instruction.
  //  (2) On the termination/commit of an interrupt
  //      prologue sequence.
  //  (3) On the termination/commit of an interrupt
  //      epilogue sequence.
  //
// leda W563 off
// LMD: Reduction of single bit expression is redundant
// LJ:  IRQ_ACT_ACT_RANGE can be single/multiple bits

  irq_act_u_wen     = irq_act_sel
                    | (ca_int_enter_evt & (~(|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]))) 
                    | (ca_int_exit_evt  &  (|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]) & (~(|ca_irq_act_nxt[`npuarc_IRQ_ACT_ACT_RANGE])))
                    ;
// leda W563 on
  irq_act_wen       = irq_act_sel
                    | (ca_int_enter_evt | ca_int_exit_evt)
                    ;
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Muxing of Aux register next-values for SR and other operations           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//`if ((`HAS_INTERRUPTS > 0) && (`FIRQ_OPTION == 1))
//reg [`DATA_RANGE]             stat32p0_nxt;
//`endif

always @*
begin : aux_nxt_PROC

  aux_lp_start_nxt = (wa_uopld_lp_start == 1'b1)
                   ? wa_uopld_data[`npuarc_PC_RANGE]
                   : (   (lp_start_sel == 1'b1)
                       ? wa_sr_data_r[`npuarc_PC_RANGE]
                       : ca_seq_pc_nxt
                     )
                   ;
  aux_lp_end_nxt   = (wa_uopld_lp_end == 1'b1)
                   ? wa_uopld_data[`npuarc_PC_RANGE]
                   : (   (lp_end_sel == 1'b1)
                       ? wa_sr_data_r[`npuarc_PC_RANGE]
                       : ca_lp_end_nxt
                     )
                   ;

  aux_irq_ctrl_nxt = {   wa_sr_data_r[`npuarc_IRQ_CTRL_LP_BIT]
                       , wa_sr_data_r[`npuarc_IRQ_CTRL_M_BIT]
                       , wa_sr_data_r[`npuarc_IRQ_CTRL_U_BIT:`npuarc_IRQ_CTRL_B_BIT]
                         // Perform <= 16 saturation on NR-field as required
                         // by spec.
                         //
                       , ( wa_sr_data_r[`npuarc_IRQ_CTRL_NR_RANGE] > 5'b1_0000 )
                         ? 5'b1_0000
                         : wa_sr_data_r[`npuarc_IRQ_CTRL_NR_RANGE]
                     }
                   ;

  aux_irq_act_nxt  = (irq_act_sel == 1'b1)
                   ? {   wa_sr_data_r[`npuarc_IRQ_ACT_U_BIT]
                       , wa_sr_data_r[`npuarc_IRQ_ACT_ACT_RANGE]
                     }
                   : {   ca_irq_act_nxt[`npuarc_IRQ_ACT_U_BIT]
                       , ca_irq_act_nxt[`npuarc_IRQ_ACT_ACT_RANGE]
                     }
                   ;


  aux_user_sp_nxt  = wa_sr_data_r;

  aux_intvbase_nxt = wa_sr_data_r[`npuarc_PC_MSB:10];

  aux_ecc_ctrl_nxt = (ecc_ctrl_sel == 1'b1)
                   ? ( {(wa_sr_data_r[31:16] & aux_ecc_ctrl_r[31:16]),wa_sr_data_r[15:0]}
                     & (32'hF3EA003F)
                     )
                   : ( (  aux_ecc_ctrl_r[`npuarc_DATA_RANGE]
                       | {ecc_flt_status, {16{1'b0}}}
                       )
                     & (32'hF3EA003F)
                     )
                   ;
  aux_ecc_sbe_count_r = ecc_sbe_count_r;      // This is already registered signal

  aux_ecc_sbe_count_nxt = (ecc_sbe_sel == 1'b1)
                        ?  wa_sr_data_r[`npuarc_DATA_RANGE]
                        :  ecc_sbe_count_r;


  //============================================================
  // BTA update Procedure
  //  CA: BTA is updated for Branch taken with dSlot
  //  WA: BTA is updated for AUX SR
  //  To resolve BTA WAW hazard for SR followed by Branch taken
  //  BTA update for Branch taken has higher priority
  //
  // Priority:
  // (1) Exception INTEVT EXIT
  // (2) EI_S
  // (3) Branch Taken with dSlot
  // (4) SR BTA update
  // (5) Exception INTEVT Prologue
  // (6) Interrupt Enter
  //
  //
  casez ({ excpn_evts[`npuarc_INTEVT_EXIT],                        // (1)
           ca_ei_op_r,                                      // (2)
           (  (ca_normal_evt | ca_uop_evt)                  // (3)
            & ca_br_taken & ca_dslot_r
            ), 
           bta_sel,                                         // (4)
           excpn_evts[`npuarc_INTEVT_PROLOGUE],                    // (5)
           ca_int_enter_evt                                 // (6)
         })
    6'b1?????: aux_bta_nxt = ar_aux_erbta_r;                // (1)
    6'b01????: aux_bta_nxt = { ca_seq_pc_nxt, 1'b1 };       // (2)
    6'b001???: aux_bta_nxt = { ca_br_target, 1'b1 };        // (3)
    6'b0001??: aux_bta_nxt = wa_sr_data_r;                  // (4)
    6'b00001?: aux_bta_nxt = 32'd0;                         // (5)
    6'b000001: aux_bta_nxt = 32'd0;                         // (6)
    default:    aux_bta_nxt = { ca_br_target, 1'b1 };
  endcase

  aux_jli_base_nxt = (wa_uopld_jli_base == 1'b1)
                   ? wa_uopld_data[`npuarc_PC_MSB:2]
                   : wa_sr_data_r[`npuarc_PC_MSB:2]
                   ;
  aux_ldi_base_nxt = (wa_uopld_ldi_base == 1'b1)
                   ? wa_uopld_data[`npuarc_ADDR_MSB:2]
                   : wa_sr_data_r[`npuarc_ADDR_MSB:2]
                   ;
  aux_ei_base_nxt  = (wa_uopld_ei_base == 1'b1)
                   ? wa_uopld_data[`npuarc_PC_MSB:2]
                   : wa_sr_data_r[`npuarc_PC_MSB:2]
                   ;
  aux_ustack_base_nxt = wa_sr_data_r[`npuarc_ADDR_MSB:0]; 
  aux_ustack_top_nxt  = wa_sr_data_r[`npuarc_ADDR_MSB:0]; 
  aux_kstack_base_nxt = wa_sr_data_r[`npuarc_ADDR_MSB:0]; 
  aux_kstack_top_nxt  = wa_sr_data_r[`npuarc_ADDR_MSB:0];
end



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous blocks for architectural state updates                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg [7:0]  aux_memseg_next;
reg [21:0]           intvbase_in_next;
reg               ar_aux_irq_ctrl_upt_next;

always @*
begin : aux_comb_PROC

   aux_lp_start_next = aux_lp_start_r;
   aux_lp_end_next   = aux_lp_end_r;
   aux_memseg_next   = aux_memseg_r;
   aux_ustack_base_next = aux_ustack_base_r;
   aux_ustack_top_next  = aux_ustack_top_r;
   aux_kstack_base_next = aux_kstack_base_r;
   aux_kstack_top_next  = aux_kstack_top_r;
   aux_intvbase_next    = aux_intvbase_r;
   intvbase_in_next     = intvbase_in_r;
   aux_ecc_ctrl_next    = aux_ecc_ctrl_r;
   aux_bta_next         = aux_bta_r;
   aux_jli_base_next    = aux_jli_base_r;
   aux_ldi_base_next    = aux_ldi_base_r;
   aux_ei_base_next     = aux_ei_base_r;
   aux_irq_ctrl_next    = aux_irq_ctrl_r;
   ar_aux_irq_ctrl_upt_next = ar_aux_irq_ctrl_upt_r;
   aux_user_sp_next     = aux_user_sp_r;
   aux_irq_act_next     = aux_irq_act_r;

    if (lp_start_wen  == 1'b1)
      aux_lp_start_next     = aux_lp_start_nxt;
    if (lp_end_wen    == 1'b1)
      aux_lp_end_next       = aux_lp_end_nxt;
    if (memseg_wen    == 1'b1)
      aux_memseg_next       = wa_sr_data_r[7:0];
    if (ustack_base_wen == 1'b1) 
      aux_ustack_base_next  = aux_ustack_base_nxt;
    if (ustack_top_wen  == 1'b1) 
      aux_ustack_top_next   = aux_ustack_top_nxt;
    if (kstack_base_wen == 1'b1) 
      aux_kstack_base_next  = aux_kstack_base_nxt;
    if (kstack_top_wen  == 1'b1) 
      aux_kstack_top_next   = aux_kstack_top_nxt;
    if (intvbase_wen  
        || (~after_cycle1)
        )
      aux_intvbase_next     = after_cycle1 ? aux_intvbase_nxt : intvbase_in;
    if (~after_cycle1)
      intvbase_in_next      = intvbase_in;

    if (ecc_ctrl_wen    == 1'b1)
      aux_ecc_ctrl_next     = aux_ecc_ctrl_nxt;
    if (bta_wen       == 1'b1)
      aux_bta_next          = aux_bta_nxt;
    if (jli_base_wen  == 1'b1)
      aux_jli_base_next     = aux_jli_base_nxt;
    if (ldi_base_wen  == 1'b1)
      aux_ldi_base_next     = aux_ldi_base_nxt;
    if (ei_base_wen  == 1'b1)
      aux_ei_base_next      = aux_ei_base_nxt;
    if (irq_ctrl_wen == 1'b1)
      aux_irq_ctrl_next     = aux_irq_ctrl_nxt;
    ar_aux_irq_ctrl_upt_next   = irq_ctrl_wen;
    if (user_sp_wen == 1'b1)
      aux_user_sp_next      = aux_user_sp_nxt;
    if (irq_act_wen == 1'b1)
      aux_irq_act_next[`npuarc_IRQ_ACT_ACT_RANGE]  = aux_irq_act_nxt[`npuarc_IRQ_ACT_ACT_RANGE];
    if (irq_act_u_wen == 1'b1)
      aux_irq_act_next[`npuarc_IRQ_ACT_MSB]        = aux_irq_act_nxt[`npuarc_IRQ_ACT_MSB];
end


always @(posedge clk or posedge rst_a)
begin : aux_reg_PROC
  if (rst_a == 1'b1)
    begin
    aux_lp_start_r    <= `npuarc_PC_BITS'd0;
    aux_lp_end_r      <= `npuarc_PC_BITS'd0;
    aux_memseg_r      <= 8'd0;
    aux_ustack_base_r <= `npuarc_DATA_SIZE'd0;
    aux_ustack_top_r  <= `npuarc_DATA_SIZE'd0;
    aux_kstack_base_r <= `npuarc_DATA_SIZE'd0;
    aux_kstack_top_r  <= `npuarc_DATA_SIZE'd0;

    aux_intvbase_r    <=  22'd0;
    intvbase_in_r     <=  22'd0;
    after_cycle1      <=  1'b0;
    aux_ecc_ctrl_r    <= `npuarc_DATA_SIZE'd0;
    aux_bta_r         <= `npuarc_DATA_SIZE'd0;
    aux_jli_base_r    <= {`npuarc_PC_SIZE-2{1'b0}};
    aux_ldi_base_r    <= {`npuarc_ADDR_SIZE-2{1'b0}};
    aux_ei_base_r     <= {`npuarc_PC_SIZE-2{1'b0}};
    aux_irq_ctrl_r    <= {`npuarc_IRQ_CTRL_BITS{1'b0}};
    ar_aux_irq_ctrl_upt_r <= 1'b1; //we need to calculate sp_offset at reset
    aux_user_sp_r     <= {`npuarc_DATA_SIZE{1'b0}};
    aux_irq_act_r     <= {`npuarc_IRQ_ACT_BITS{1'b0}};
    end
  else
    begin
      aux_lp_start_r       <= aux_lp_start_next;
      aux_lp_end_r         <= aux_lp_end_next;
      aux_memseg_r         <= aux_memseg_next;
      aux_ustack_base_r    <= aux_ustack_base_next;
      aux_ustack_top_r     <= aux_ustack_top_next;
      aux_kstack_base_r    <= aux_kstack_base_next;
      aux_kstack_top_r     <= aux_kstack_top_next;
      after_cycle1 <= 1'b1;
// spyglass disable_block Ac_glitch04 Ac_unsync02
// SMD: glitches possible due to unsyc crossings
// SJ:  no logical dependencies to mcip domain
      aux_intvbase_r       <= aux_intvbase_next;
// spyglass enable_block Ac_glitch04 Ac_unsync02
// spyglass disable_block Ac_glitch04 Ac_unsync02
// SMD: glitches possible due to unsyc crossings
// SJ:  no logical dependencies to mcip domain
      intvbase_in_r        <= intvbase_in_next;
// spyglass enable_block Ac_glitch04 Ac_unsync02
      aux_ecc_ctrl_r       <= aux_ecc_ctrl_next;
      aux_bta_r            <= aux_bta_next;
      aux_jli_base_r       <= aux_jli_base_next;
      aux_ldi_base_r       <= aux_ldi_base_next;
      aux_ei_base_r        <= aux_ei_base_next;
      aux_irq_ctrl_r       <= aux_irq_ctrl_next;
    ar_aux_irq_ctrl_upt_r     <= ar_aux_irq_ctrl_upt_next;
      aux_user_sp_r        <= aux_user_sp_next;
      aux_irq_act_r       <= aux_irq_act_next;
  end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// DEBUG AUX register (bits that the machine can potentially alter).        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : sleep_state_PROC
  if (rst_a == 1'b1)
    begin
    dbg_tf_r     <=  1'b0;
    dbg_sh_r     <=  1'b0;
    dbg_is_r     <=  1'b0;
    dbg_bh_r     <=  1'b0;
    dbg_eh_r     <=  1'b0;
    dbg_ah_r     <=  1'b0;
    dbg_zz_r     <=  1'b0;
    dbg_we_r     <=  1'b0;
    dbg_wf_r     <=  1'b0;
    dbg_sh_set_r <=  1'b0;
    end
  else
    begin
    dbg_tf_r     <=  dbg_tf_nxt;
    dbg_sh_r     <=  dbg_sh_nxt;
    dbg_is_r     <=  dbg_is_nxt;
    dbg_bh_r     <=  dbg_bh_nxt;
    dbg_eh_r     <=  dbg_eh_nxt;
    dbg_ah_r     <=  dbg_ah_nxt;
    dbg_zz_r     <=  dbg_zz_nxt;
    dbg_we_r     <=  dbg_we_nxt;
    dbg_wf_r     <=  dbg_wf_nxt;
    dbg_sh_set_r <=  dbg_sh_set_nxt;
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// DEBUG AUX register (bits that only the host can alter).                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : dbg_reg_PROC
  if (rst_a == 1'b1)
    begin
    dbg_ub_r     <=  1'b0;
    dbg_ra_r     <=  1'b1;
    end
  else if (debug_wen == 1'b1)
    begin
    dbg_ub_r     <=  dbg_ub_nxt;
    dbg_ra_r     <=  dbg_ra_nxt;
    end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// DEBUG AUX register SM (sleep mode) field                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : dbg_sm_reg_PROC
  if (rst_a == 1'b1)
  begin
    dbg_sm_r     <=  {`npuarc_SLEEP_MODE_BITS{1'b0}};
  end
  else if (dbg_sm_cg0 == 1'b1)
  begin
    dbg_sm_r     <=  dbg_sm_nxt;
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// DEBUG AUX register ASR-field                                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : asr_reg_PROC
  if (rst_a == 1'b1)
    begin
    dbg_asr_r     <=  `npuarc_NUM_ACTIONPOINTS'd0;
    end
  else if (aps_wen == 1'b1)
    begin
    dbg_asr_r     <=  dbg_asr_nxt;
    end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// DEBUGI AUX register                                                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: dbgi_reg_PROC
  if (rst_a == 1'b1)
  begin
    dbgi_e_r     <= 1'b0;
  end
  else if (debugi_wen == 1'b1)
  begin
    dbgi_e_r     <= dbgi_e_nxt;
  end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Debug host initiated halt status                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dbg_halt_nxt_PROC
  // -------------------------------------------------------------------------
  // Set on host write of debug.fh bit and cleared when STATUS32.H is cleared.
  //
  dbg_halt_nxt      = ( dbg_fh_nxt                             // set
                      ) 
                    | (   dbg_halt_r                           // clear
                        & (~(   wa_aux_status32_pass
                             & (~wa_aux_status32_nxt[`npuarc_P_H_FLAG])
                           ))
                      )
                    ;
end

always @(posedge clk or posedge rst_a)
begin : dbg_halt_PROC
  if (rst_a == 1'b1)
    begin
    dbg_halt_r     <=  1'b0;
    end
  else
    begin
    dbg_halt_r     <=  dbg_halt_nxt;
    end
end

always @*
begin : ecc_sbe_dmp_clr_comb_PROC
    ecc_sbe_dmp_clr_nxt = ecc_sbe_dmp_clr_r;
    // DCCM
    //
    if (ecc_sbe_dmp_clr_r[0] & (ecc_sbe_count_r[7:4] == 4'b0000))
    begin
      ecc_sbe_dmp_clr_nxt[0]  = 1'b0;
    end
    else if (ecc_sbe_clr[1]) 
    begin
      ecc_sbe_dmp_clr_nxt[0]  = 1'b1;
    end
    
    // DC DATA
    //
    if (ecc_sbe_dmp_clr_r[1] & (ecc_sbe_count_r[23:20] == 4'b0000))
    begin
      ecc_sbe_dmp_clr_nxt[1] = 1'b0;
    end
    else if (ecc_sbe_clr[5]) 
    begin
      ecc_sbe_dmp_clr_nxt[1] = 1'b1;
    end

    // DC TAG
    //
    if (ecc_sbe_dmp_clr_r[2] & (ecc_sbe_count_r[27:24] == 4'b0000))
    begin
      ecc_sbe_dmp_clr_nxt[2] = 1'b0;
    end
    else if (ecc_sbe_clr[6])  // DC Tag
    begin
      ecc_sbe_dmp_clr_nxt[2] = 1'b1;
    end
end
always @(posedge clk or posedge rst_a)
begin : ecc_sbe_dmp_clr_reg_PROC
  if (rst_a == 1'b1)
  begin
    ecc_sbe_dmp_clr_r <= 3'b000;
  end
  else
  begin
    // DCCM
    //
    ecc_sbe_dmp_clr_r <= ecc_sbe_dmp_clr_nxt;
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output Assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign wa_status32_wen  = status32_wen;
assign wa_debug_wen     = debug_wen;
assign wa_erstatus_wen  = erstatus_wen;
assign wa_eret_wen      = eret_wen;
assign wa_erbta_wen     = erbta_wen;
assign wa_ecr_wen       = ecr_wen;
assign wa_efa_wen       = efa_wen;
assign wa_efae_wen      = efae_wen;

assign ar_ae_r    = ar_aux_status32_r[`npuarc_AE_FLAG];
wire [7:0] ar_dbg_asr;
assign ar_dbg_asr = ar_aux_debug_r[`npuarc_DEBUG_ASR];
assign ar_asr_r   = ar_dbg_asr[`npuarc_APS_RANGE];


assign ar_aux_ecc_ctrl_r  = aux_ecc_ctrl_r[`npuarc_DATA_RANGE];

assign ecc_sbe_dmp_clr = |ecc_sbe_dmp_clr_r;


  
endmodule  // alb_aux_regs
