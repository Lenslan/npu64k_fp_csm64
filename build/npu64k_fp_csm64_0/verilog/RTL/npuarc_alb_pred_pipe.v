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
//
//  #####   #####   ######  #####           #####      #    #####   ######
//  #    #  #    #  #       #    #          #    #     #    #    #  #
//  #    #  #    #  #####   #    #          #    #     #    #    #  #####
//  #####   #####   #       #    #          #####      #    #####   #
//  #       #   #   #       #    #          #          #    #       #
//  #       #    #  ######  #####  #######  #          #    #       ######
//
// ===========================================================================
//
// Description:
//
//  This module is responsible for pipelining the branch information that is
//  associated with each instruction in the EXU pipeline, and is also the
//  place where branch mispredictions are detected and signaled.
//
//  The X1 and CA stages are both capable of resolving a branch outcome, and
//  each of those stages provides those outcomes to this module. Within this
//  module other branch errors are detected, and mispredictions from CA and X1
//  are prioritized (CA first) before being registered at the output of the
//  module. These outputs drive the misprediction interface.
//
// ===========================================================================


// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_pred_pipe (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,              // clock signal
  input                       rst_a,            // reset signal
  input                       db_active,        // debug unit is active

  ////////// Machine Architectural state /////////////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_DATA_RANGE]    ar_aux_debug_r,   // committed DEBUG aux reg
  input      [`npuarc_DATA_RANGE]    ar_aux_status32_r,// committed STATUS32 aux reg
  input      [`npuarc_DATA_RANGE]    ar_aux_lp_start_r,// LP_START
// leda NTL_CON13C on
  ////////// Fetch-Restart Interface /////////////////////////////////////////
  //
  input                       fch_restart,      // fetch restart signal

  ////////// Instruction Issue handshake interface with the IFU //////////////
  //
  input                       al_pass,          // valid instruction arriving

  //////// Branch prediction information from IFU to Execution Unit //////////
  //
  input                       al_is_predicted,  // 1 => insn is predicted
  input                       al_prediction,    // 1 => valid prediction
  input   [`npuarc_PC_RANGE]         al_predicted_bta, // predicted br target
  input   [`npuarc_BR_TYPE_RANGE]    al_prediction_type,// type of branch prediction
  input                       al_error_branch,  // 1 => br error indicated
  input   [`npuarc_BR_INFO_RANGE]    al_branch_info,   // br info tag
  input                       al_with_dslot,    // pred branch has dslot

  //////// Branch prediction information from UOP_SEQ to Execution Unit //////
  //
  input                       al_uop_is_predicted,    // 1 => insn is predicted
  input                       al_uop_prediction,      // 1 => valid prediction
  input   [`npuarc_BR_TYPE_RANGE]    al_uop_prediction_type, // type of branch prediction
  input                       al_uop_with_dslot,      // pred branch has dslot

  ////////// Control Inputs from Dependency Pipeline /////////////////////////
  //
  input                       al_uop_pass,      // UOP in DA emits to AL
  input                       da_enable,        // DA is able to receive input
  input                       da_holdup,        // DA holdup signal
  input                       da_pass,          // DA instruction ready to go
  input                       sa_enable,        // SA is able to receive input
  input                       sa_pass,          // SA instruction ready to go
  input                       x1_enable,        // X1 is able to receive input
  input                       x1_pass,          // X1 instruction ready to go
  input                       x1_kill,          // X1 instruction is killed
  input                       x1_cond_ready,    // X1 flag condition is ready
  input                       x1_bta_ready,     // X1 BTA value is ready
  input                       x2_enable,        // X2 is able to receive input
  input                       x2_pass,          // X2 instruction ready to go
  input                       x3_enable,        // X3 is able to receive input
  input                       x3_pass,          // X3 instruction ready to go
  input                       ca_enable,        // CA is able to receive input
  input                       ca_pass,          // CA instruction ready to go
  input                       wa_enable,        // WA is able to receive input

  ////////// Indication of valid instructions at each EXU pipeline stage /////
  //
  input                       da_valid_r,       // Decode stage has valid insn
  input                       sa_valid_r,       // Operand stage has valid insn
  input                       x1_valid_r,       // Exec1 stage has valid insn
  input                       x2_valid_r,       // Exec2 stage has valid insn
  input                       x3_valid_r,       // Exec3 stage has valid insn
  input                       ca_valid_r,       // Commit stage has valid insn

  ////////// ucode signals from downstream stages ////////////////////////////
  //
  input                       da_dslot,         // DA inst has a delay slot
  input                       da_uop_prol_r,    // DA insn is in prologue
  input                       da_uop_busy_r,    //
  input                       da_ifu_exception_r,
  input                       da_ifu_err_nxtpg_r,
  input                       sa_link_r,        // SA inst has linkage
  input                       sa_dslot_r,       // SA inst has a delay slot
  input                       x1_dslot_r,       // X1 inst has dslot
  input                       x1_uop_epil_r,    // X1 is in epilogue
  input      [`npuarc_PC_RANGE]      sa_seq_pc_r,      // seq PC after SA insn
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_DATA_RANGE]    ar_aux_bta_r,     // BTA auxiliary register
// leda NTL_CON13C on
  input                       sa_ei_op_r,       // SA inst is EI_S
  input                       sa_leave_op_r,    // SA inst is LEAVE_S
  input                       x1_ei_op_r,       // X1 inst is EI_S
  input                       x1_btab_op_r,     // X1 inst is BI or BIH
  input                       x2_ei_op_r,       // X2 inst is EI_S
  input                       x3_ei_op_r,       // X3 inst is EI_S
  input                       ca_ei_op_r,       // CA inst is EI_S
  input                       ca_btab_op_r,     // CA inst is BI or BIH
  input                       ca_dslot_r,       // CA inst has dslot
  input                       ca_jump_r,        // CA inst is jump
  
  ////////// Early branch resolution information from SA stage ///////////////
  //
  input      [`npuarc_PC_RANGE]      sa_pc,            // PC of SA insn
  input      [`npuarc_BR_TYPE_RANGE] sa_br_type,       // actual branch type at SA
  input      [`npuarc_ISIZE_RANGE]   sa_commit_size,
  input                       sa_secondary,
  input                       sa_uop_inst_r,    // SA insn is part of uop seq
  input                       sa_uop_predictable_r, // SA uop seq has a predictable branch
  input                       sa_iprot_viol_r,  // iprot replay request

  ////////// Inputs to the Prediction pipeline ///////////////////////////////
  //
  input                       x1_uop_inst_r,    // X1 insn is part of uop seq

  ////////// Early branch resolution information from X1 stage ///////////////
  //
  input                       x1_br_direction,  // PC change direction at X1
  input                       x1_br_taken,      // Branch/jump taken at X1
  input      [`npuarc_PC_RANGE]      x1_br_target,     // target or fall-thru at X1
  input      [`npuarc_PC_RANGE]      x1_br_fall_thru,  // fall-thru address at X1
  input                       x1_bi_bta_mpd,    // BTA miss for BI, BIH insn
  input      [`npuarc_PC_RANGE]      x2_target_nxt,    // Next branch target for X2
  input      [`npuarc_PC_RANGE]      x1_link_addr,     // link address for calls
  output reg                  x1_predictable_r, // X1 has predictable branch
  output reg                  x1_is_eslot_r,    // X1 is in an eslot
  output reg [`npuarc_PC_RANGE]      x1_pred_bta_r,    // X1 predicted BTA or EI retn

  ////////// Early misprediction outputs from the ZOL pipeline ///////////////
  //
  input                       x1_early_pred_r,  // X1 has early ZOL prediction
  input                       x1_zol_mpd_dir,   // early ZOL mispred dir
  input                       sa_zol_hazard,    // ZOL hazard for SA
  input                       x1_zol_hazard_r,  //  ZOL hazard for X1

  ////////// Late branch resolution information from CA stage ////////////////
  //
  input      [`npuarc_PC_RANGE]      ar_pc_r,          // architectural next PC
  input                       ca_br_direction,  // branch direction at CA
  input      [`npuarc_PC_RANGE]      ca_br_target,     // branch target at CA
  input      [`npuarc_PC_RANGE]      ca_br_fall_thru,  // fall-thru address at CA
  input                       ca_br_or_jmp,     // CA inst is br or jmp
  input                       ca_leave_op_r,    // CA inst is LEAVE_S
  input                       ca_uop_inst,
  input                       ca_uop_active_r,  // CA is in a uop-sequence
  input                       ca_uop_predictable_r,// CA is in a predicted uop-sequence
  input                       ca_uop_enter_r,   // CA is in a ENTER_S uop-sequence
  input                       ca_uop_commit_r,  // CA is commiting a uop-seq.
  input                       ca_tail_pc_3,     //
  //
  output reg                  ca_br_taken,      // predictable br taken at CA
                                                // (excludes non-predicted br)
  input                       wa_cmt_norm_evt_nxt,// Normal commit at CA stage
  input                       ct_excpn_trap_nxt, // TRAP in CA
  input                       ca_sleep_evt,      // SLEEP in CA
  input                       ca_cmt_brk_evt,    // BREAK in CA
  input                       ca_iprot_viol_r,   // iprot violation at CA
  input                       ca_iprot_replay,   // iprot replay this cycle
                       
  ////////// Late misprediction outputs from the ZOL pipeline ////////////////
  //
  input                       ca_hit_lp_end,
  input                       ca_branch_evt,
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  from zol pipe unused port 
// leda NTL_CON13C on
  input                       ca_zol_mpd_dir,   // late ZOL mispred dir
  input                       ca_zol_mpd_bta,   // late ZOL mispred BTA
  input                       ca_zol_lp_jmp,    // late ZOL loop-back
  input                       ca_zol_branch,    // late ZOL phantom branch
                                                //  may be taken or not

  ////////// DMP Replay Interface ////////////////////////////////////////////
  //
  input                       dc4_replay,       // replay the instr at DC4

  ////////// Exception Interface /////////////////////////////////////////////
  //
  input                       excpn_restart,      // Excpn restart request
  input      [`npuarc_PC_RANGE]      excpn_restart_pc,   // Excpn restart PC

  ////////// Halt Interface /////////////////////////////////////////////////
  //
  input                       hlt_stop,         // Halt request IFU stop
  input                       hlt_restart,      // Halt restart request

  ////////// Instruction Replay Interface ///////////////////////////////////
  //
  input                       ct_replay,        // Insn replay request.

  ////////// Interface with DA stage /////////////////////////////////////////
  //
  output reg                  da_is_eslot,      // DA insn is in an eslot
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Not all bits of bus used
  output reg   [`npuarc_PC_RANGE]    x1_pc_r,          // X1 PC
  // leda NTL_CON32 on
  

  ////////// Misprediction and early restart interface ///////////////////////
  //
  output reg                  da_in_dslot_r,    // DA inst is in a dslot
  output reg                  sa_in_dslot_r,    // SA inst is in a dslot
  output reg                  x1_in_dslot_r,    // X1 inst is in a dslot
  output reg                  x2_in_dslot_r,    // X2 inst is in a dslot
  output reg                  x3_in_dslot_r,    // X3 inst is in a dslot
  output reg                  ca_in_dslot_r,    // CA inst is in a dslot
  //
  output reg                  da_is_predicted_r,// 1 => DA insn is predicted
  output reg                  da_prediction_r,  // 1 => DA valid prediction
  output reg                  da_orphan_dslot_r,// DA dslot is orphaned
  output reg [`npuarc_PC_RANGE]      da_pred_bta_r,    // DA predicted br target
  output reg [`npuarc_BR_TYPE_RANGE] da_prediction_type_r, // type of DA prediction
  output reg                  da_error_branch_r,// 1 => DA br error indicated
  //
  output reg                  sa_is_predicted_r,// SA insn has a prediction
  output reg                  sa_with_dslot_r,  // SA is predicted to have a delay slot
  output reg                  sa_prediction_r,  // SA predicted outcome
  output reg [`npuarc_PC_RANGE]      sa_pred_bta_r,    // SA predicted br target
  output reg                  sa_error_branch_r,// Fragged insn at SA
  output reg                  sa_error_branch,  // Fragged or aliased at SA

  output reg [`npuarc_BR_TYPE_RANGE] sa_prediction_type_r, // type of SA prediction
  //
  output reg                  x1_error_branch_r,// 1 => X1 error br indicated
  //
  output reg                  x2_restart_r,     // 1 => early restart request
  output reg [`npuarc_PC_RANGE]      x2_restart_pc_r,  // early restart PC
  output reg                  x2_mispred_r,     // 1 => X2 mispred. restart
  output reg                  x2_fragged_r,     // 1 => X2 insn was fragged
  output reg                  x2_error_branch_r,// 1 => X2 insn is error br
  output reg                  x2_pg_xing_replay_r, // replay on bl.d xing page
  output reg                  x2_pg_xing_dslot_r,  // dlost of bl.d xing page
//  output reg                  x2_late_pred_r,   // 1 => late branch/jump at X2
  output reg                  wa_mispred_r,     // 1 => WA mispred. restart
  //
  output reg                  x3_error_branch_r,// 1 => X3 br error indicated
  output reg                  x3_late_pred_r,   // 1 => late branch/jump at X3
  //
  output reg                  ca_is_predicted_r,// 1 => CA insn is predicted
  output reg                  ca_prediction_r,  // 1 => CA valid prediction
  output reg [`npuarc_BR_TYPE_RANGE] ca_br_type_r,      // actual branch type at CA
  output reg [`npuarc_PC_RANGE]      ca_pred_bta_r,    // CA predicted br target
  output reg                  ca_fragged_r,     // 1 => CA insn was fragged
  output reg                  ca_error_branch_r,// 1 => CA br error indicated
  output reg                  ca_pg_xing_replay_r,// Replay on bl.d xing page
  //
  output reg                  wa_restart_r,     // signals restart from WA
  output reg                  wa_restart_kill_r,// WA restart kills CA
  output reg [`npuarc_PC_RANGE]      wa_restart_pc_r,  // the restart PC at WA
  output reg                  wa_stop_r,        // EXU request IFU halt
  output reg                  wa_iprot_replay_r,// iprot replay at WA
  //
  output                      mpd_mispred,      // a misprediction occurred
  output                      mpd_direction,    // 1 => taken, 0 => not-taken
  output                      mpd_error_branch, // erroneous prediction made
  output                      mpd_is_predicted, // instruction had a prediction
  output                      mpd_mispred_outcome, // outcome was mispredicted
  output                      mpd_mispred_bta,  // BTA was mispredicted
  output  [`npuarc_BR_INFO_RANGE]    mpd_branch_info,  // branch info from IFU
  output                      mpd_dslot,        // branch has dslot
  output  [`npuarc_PC_RANGE]         mpd_seq_next_pc,  // link address for BL, JL
  output  [`npuarc_PC_RANGE]         mpd_pc,           // PC of mispred insn
  output  [`npuarc_BR_TYPE_RANGE]    mpd_type,         // misprediction branch type

  output                      mpd_early,        // 1=> early mispredict
                                                // 0=> late mispredict
  output                      mpd_tail_pc_3,
  output  [`npuarc_ISIZE_RANGE]      mpd_commit_size,
  output                      mpd_secondary,

  ////////// Hazard interface to the dependency pipeline /////////////////////
  //
  output reg                  da_eslot_stall,   // RAW hazard stall on BTA  
  output reg                  x1_dslot_stall,   // stall dslot with error br.

  ////////// Branch Commit interface /////////////////////////////////////////
  //
  // (some signals are provided directly from alb_writeback)
  //
  output                      wa_pass,            // valid branch-commit info
  output  [`npuarc_BR_TYPE_RANGE]    wa_type,            //
  output  [`npuarc_ISIZE_RANGE]      wa_commit_size,
  output                      wa_secondary,
  output                      wa_direction,       //
  output  [`npuarc_PC_RANGE]         wa_target,          //
  output                      wa_error_branch,    //
  output                      wa_is_predicted,    //
  output                      wa_mispred_outcome, //
  output  [`npuarc_BR_INFO_RANGE]    wa_branch_info,     // 
  output                      wa_commit_mispred_bta//
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Prediction pipeline register declarations                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//------ DA next states ------------------------------------------------------
reg                         da_is_pred_nxt;       // next prediction validity
reg                         da_prediction_nxt;    // prediction for AL insn
reg   [`npuarc_BR_TYPE_RANGE]      da_prediction_type_nxt;// type of AL prediction
reg                         da_error_branch_nxt;  // 1 => AL br error indicated
reg                         da_with_dslot_r;  // DA pred branch has dslot
reg                         da_with_dslot_nxt;    // AL pred branch has dslot
reg                         da_in_dslot_nxt;      // AL inst is in a dslot
reg                         da_orphan_dslot_nxt;  // AL dslot is orphaned

//------ DA stage ------------------------------------------------------------
reg   [`npuarc_BR_INFO_RANGE]      da_branch_info_r;     // DA br info tag

//------ SA stage ------------------------------------------------------------
reg   [`npuarc_BR_INFO_RANGE]      sa_branch_info_r;     // SA br info tag
reg                         sa_orphan_dslot_r;    // SA dslot is orphaned
reg                         sa_eslot_mpd_r;       // EI return mispredict at SA
reg                         sa_is_eslot_r;        // e-slot instruction at SA
reg                         sa_pg_xing_dslot_r;   // dslot of bl.d xing page

//------ X1 stage ------------------------------------------------------------
reg                         x1_is_predicted_r;    // 1 => X1 insn is predicted
reg                         x1_prediction_r;      // 1 => X1 valid prediction
reg   [`npuarc_BR_TYPE_RANGE]      x1_prediction_type_r; // type of X1 prediction
reg   [`npuarc_BR_INFO_RANGE]      x1_branch_info_r;     // X1 br info tag
reg                         x1_with_dslot_r;      // X1 pred branch has dslot
reg   [`npuarc_BR_TYPE_RANGE]      x1_br_type_r;         // actual branch type at X1
reg   [`npuarc_ISIZE_RANGE]        x1_commit_size_r;     //
reg                         x1_secondary_r;       //
reg                         x1_eslot_mpd_r;       // EI return mispredict at X1
reg                         x1_orphan_dslot_r;    // X1 dslot is orphaned
reg                         x1_uop_predictable_r; // UOP Seq with predictable 
                                                  //  branch at X1
reg                         x1_pg_xing_replay_r;  // Replay on bl.d xing page
reg                         x1_pg_xing_dslot_r;   // dslot of bl.d xing page
reg                         x3_pg_xing_replay_r;  // Replay on bl.d xing page

//------ X2 stage ------------------------------------------------------------
reg                         x2_is_predicted_r;    // 1 => X2 insn is predicted
reg                         x2_prediction_r;      // 1 => X2 valid prediction
reg   [`npuarc_PC_RANGE]           x2_pred_bta_r;        // X2 predicted br target
reg   [`npuarc_BR_TYPE_RANGE]      x2_prediction_type_r; // type of X2 prediction
reg   [`npuarc_BR_INFO_RANGE]      x2_branch_info_r;     // X2 br info tag
reg                         x2_with_dslot_r;      // X2 pred branch has dslot
reg   [`npuarc_BR_TYPE_RANGE]      x2_br_type_r;         // actual branch type at X2
reg   [`npuarc_ISIZE_RANGE]        x2_commit_size_r;     //
reg                         x2_secondary_r;       //
reg                         x2_predictable_r;     // X2 has predictable branch
reg                         x2_br_outcome_r;      // actual branch outcome at X2
reg                         x2_br_resolved_r;     // branch is resolved at X2
reg                         x2_orphan_dslot_r;    // X2 dslot is orphaned
reg                         x2_late_pred_r;   // 1 => late branch/jump at X2
reg                         x2_eslot_mpd_r;       // EI return mispredict at X2

//------ X3 stage ------------------------------------------------------------
reg                         x3_is_predicted_r;    // 1 => X3 insn is predicted
reg                         x3_prediction_r;      // 1 => X3 valid prediction
reg   [`npuarc_PC_RANGE]           x3_pred_bta_r;        // X3 predicted br target
reg   [`npuarc_BR_TYPE_RANGE]      x3_prediction_type_r; // type of X3 prediction
reg                         x3_fragged_r;         // 1 => X3 insn was fragged
reg   [`npuarc_BR_INFO_RANGE]      x3_branch_info_r;     // X3 br info tag
reg                         x3_with_dslot_r;      // X3 pred branch has dslot
reg   [`npuarc_BR_TYPE_RANGE]      x3_br_type_r;         // actual branch type at X3
reg   [`npuarc_ISIZE_RANGE]        x3_commit_size_r;     //
reg                         x3_secondary_r;       //
reg                         x3_predictable_r;     // X3 has predictable branch

reg                         x3_br_outcome_r;      // actual branch outcome at X3
reg                         x3_br_resolved_r;     // branch is resolved at X3
reg                         x3_orphan_dslot_r;    // X3 dslot is orphaned
reg                         x3_eslot_mpd_r;       // EI return mispredict at X3
                            
                            // If an early mispredict occurs at X2, either
                            // mispredicted outcome or BTA,
                            // then this is passed through the pipeline with:
                            //
reg                         x3_early_mispred_outcome_r; // X3 early misp outcom
reg                         x3_early_mispred_bta_r; // X3 early misp BTA

//------ CA stage ------------------------------------------------------------
reg   [`npuarc_BR_INFO_RANGE]      ca_branch_info_r;     // CA br info tag
reg                         ca_with_dslot_r;      // CA pred branch has dslot
reg   [`npuarc_ISIZE_RANGE]        ca_commit_size_r;     //
reg                         ca_secondary_r;       //
reg                         ca_predictable_r;     // CA has predictable branch
reg                         ca_br_outcome_r;      // actual branch outcome at CA
reg                         ca_br_resolved_r;     // branch is resolved at CA
//reg                         ca_eslot_mpd_r;       // EI return mispredict at CA
reg                         ca_early_mispred_outcome_r;
reg                         ca_early_mispred_bta_r;
reg                         ca_orphan_dslot_r;    // CA dslot is orphaned
reg [`npuarc_BR_TYPE_RANGE]        ca_type;              // br type for commit interface
reg [`npuarc_BR_TYPE_RANGE]        ca_prediction_type_r; // type of CA prediction

//------ Misprediction output registers --------------------------------------

reg                         mpd_mispred_r;        // a misprediction occurred
reg                         mpd_direction_r;      // 1 => taken, 0 => not-taken
reg                         mpd_error_branch_r;   // erroneous prediction made
reg                         mpd_is_predicted_r;   // mispred. had prediction
reg                         mpd_mispred_outcome_r;// outcome was mispredicted
reg                         mpd_mispred_bta_r;    // BTA was mispredicted
reg   [`npuarc_BR_INFO_RANGE]      mpd_branch_info_r;    // branch info from IFU
reg                         mpd_dslot_r;          // dslot for mpd branch
reg   [`npuarc_BR_TYPE_RANGE]      mpd_type_r;           // misprediction branch type
reg   [`npuarc_PC_RANGE]           mpd_seq_next_pc_r;    // next PC after mispred
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Not all bits of bus used
reg   [`npuarc_PC_RANGE]           mpd_pc_r;             // PC of mispred insn
  // leda NTL_CON32 on
reg                         mpd_early_r;          // early mispredict?
reg                         mpd_tail_pc_3_r;
reg   [`npuarc_ISIZE_RANGE]        mpd_commit_size_r;
reg                         mpd_secondary_r;
  
//------ Branch-commit output registers --------------------------------------

reg                         wa_pass_r;            // pass a committed WA insn
reg   [`npuarc_BR_TYPE_RANGE]      wa_br_type_r;         // actual branch type at WA
reg   [`npuarc_ISIZE_RANGE]        wa_commit_size_r;     //
reg                         wa_secondary_r;       //
reg                         wa_is_predicted_r;    // branch is predicted
reg   [`npuarc_PC_RANGE]           wa_target_r;          // committed branch target
reg                         wa_direction_r;       // committed branch direction
reg                         wa_error_branch_r;    // 1 => WA br error indicated
reg                         wa_mispred_outcome_r; // outcome was mispredicted
reg                         wa_mispred_bta_r;     // BTA was mispredicted
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range:0-2
// LJ:  Some bits unused
reg   [`npuarc_BR_INFO_RANGE]      wa_branch_info_r;     // 
// leda NTL_CON32 on
reg                         wa_pending_r;         // Br. commit is pending

//------ Pipeline Restart output registers -----------------------------------

reg                         ca_replay;            // replay request at CA
reg                         ca_flush;             // excpn or replay at CA
reg                         ca_restart_without_mispredict; 
                                                // flush or orphan dslot at CA
reg                         ca_restart;           // flush or mispredict at CA
reg                         ca_restart_kill_ca;   // flush kills CA
reg                         ca_stop;              // EXU requests halt

// BI BTA mispredict pipeline signals:
reg                         x2_bi_bta_mpd_r;
reg                         x3_bi_bta_mpd_r;
reg                         ca_bi_bta_mpd_r;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Enable signals for prediction pipeline registers                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                         da_ctrl_cg0;          // enable DA ctrl info
reg                         da_info_cg0;          // enable DA branch info
reg                         da_pred_cg0;          // enable DA prediction info
reg                         da_err_br_cg0;        // enable DA error branch info

reg                         sa_ctrl_cg0;          // enable SA ctrl info
reg                         sa_info_cg0;          // enable SA branch info
reg                         sa_pred_cg0;          // enable SA data info

reg                         x1_ctrl_cg0;          // enable X1 ctrl info
reg                         x1_info_cg0;          // enable X1 branch info
reg                         x1_pred_cg0;          // enable X1 data info

reg                         x2_ctrl_cg0;          // enable X2 ctrl info
reg                         x2_info_cg0;          // enable X2 branch info
reg                         x2_pred_cg0;          // enable X2 data info

reg                         x3_ctrl_cg0;          // enable X3 ctrl info
reg                         x3_info_cg0;          // enable X3 branch info
reg                         x3_pred_cg0;          // enable X3 data info

reg                         ca_ctrl_cg0;          // enable CA ctrl info
reg                         ca_info_cg0;          // enable CA branch info
reg                         ca_pred_cg0;          // enable CA data info

reg                         x2_mpd_cg0;           // enable mpd regs at X2
reg                         mpd_data_cg0;         // enable mpd data regs
reg                         brc_ctrl_cg0;         // enable mpd regs at WA
reg                         brc_data_cg0;         // enable br.commit data regs

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Nets for computing mispredictions at X1 and CA                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// misprediction info at DA
reg                         no_ei_parent;         // no insn from SA to CA
reg                         eslot_orphan;         // EI is separated from eslot
reg   [`npuarc_PC_RANGE]           eslot_target;         // jmp target of eslot insn
reg                         es_target_mpd;        // eslot target misprediction
reg                         es_outcome_mpd;       // eslot has outcome mispred
reg                         es_br_type_mpd;       // eslot has br type mispred
reg                         es_da_mpd;            // eslot mispredicted at DA

reg   [`npuarc_PC_RANGE]           sa_pred_bta_nxt;      // next sa_pred_bta_r
reg                         sa_eslot_mpd_nxt;     // next EI return mispredict
reg                         sa_predictable;       // SA insn should be predicted

// misprediction info at X1
reg                         x1_mispredict;        // a misprediction occurred
reg                         x1_direction;         // 1 => taken, 0 => not-taken
reg                         x1_error_branch;      // erroneous prediction at X1
reg                         x1_is_predicted;      // mispred. had prediction
reg                         x1_mispred_outcome;   // outcome was mispredicted
reg                         x1_mispred_bta;       // BTA was mispredicted
reg                         x1_resolve;           // 1 => can resolve a branch
reg                         x1_resolve_pred;      // outcome can be resolved
reg                         x1_resolve_bta;       // target can be resolved
reg   [`npuarc_PC_RANGE]           x1_restart_pc;        // fall-thru or target at X1
reg                         x2_br_resolved_nxt;   // branch is resolved in X1
reg                         x2_restart_nxt;       // Invoke X2 restart.
reg                         x2_late_pred_nxt;     // late prediction enters X2

// misprediction info at CA
reg                         ca_mispredict;        // a misprediction occurred
reg                         ca_direction;         // 1 => taken, 0 => not-taken
reg                         ca_is_predicted;      // mispred. had prediction
reg                         ca_mispred_outcome;   // outcome was mispredicted
reg                         ca_mispred_bta;       // BTA was mispredicted
reg                         ca_multiop_jump;      // Insn is jump of multi-op
reg                         ca_resolve;           // 1 => can resolve a branch
reg [`npuarc_PC_RANGE]             ca_target;            // branch target OR ZOL start
reg                         ca_br_jmp_mpd_bta;    // br/jmp BTA is mispredicted
reg                         ca_detect_err_br;     // type err br detected in CA

// multiplexed X1 or CA info
reg                         mpd_mispred_nxt;      // next mpd_mispred_r
reg                         mpd_direction_nxt;    // next mpd_direction_r
reg                         mpd_error_branch_nxt; // next mpd_error_branch_r
reg                         mpd_is_predicted_nxt; // next mpd_is_predicted_r
reg                         mpd_mispred_outcome_nxt; // next mispred_outcome_r
reg                         mpd_mispred_bta_nxt;  // next mispred_bta_r
reg   [`npuarc_BR_INFO_RANGE]      mpd_branch_info_nxt;  // next branch_info_r
reg                         mpd_dslot_nxt;        // dslot for mpd branch
reg   [`npuarc_BR_TYPE_RANGE]      mpd_type_nxt;         // misprediction branch type
reg   [`npuarc_PC_RANGE]           mpd_seq_next_pc_nxt;  // next PC after mispred
reg   [`npuarc_PC_RANGE]           mpd_pc_nxt;           // next mpd_pc
reg                         mpd_early_nxt;        // next mpd_early_r
reg                         mpd_tail_pc_3_nxt;
reg   [`npuarc_ISIZE_RANGE]        mpd_commit_size_nxt;
reg                         mpd_secondary_nxt;
 
reg                         al_in_dslot;          // arriving inst is in dslot
reg                         pipe_empty;           // stages DA..CA are empty
reg                         wa_pending_nxt;       // next value of wa_pending_r
reg   [`npuarc_PC_RANGE]           wa_restart_pc_nxt;    // next restart PC at WA
reg                         wa_pass_nxt;          // cmt prediction in WA
reg                         wa_direction_nxt;     // direction of br/jmp/zol
reg                         wa_mispred_outcome_nxt;
reg                         wa_mispred_bta_nxt;

// @x1_tail_pc_PROC
//
// leda NTL_CON13A off
// leda NTL_CON12A off
// LMD: non driving internal net
// LJ:  caused by addition operation
//reg   [3:1]                 x1_tail_pc;           // 
reg   [`npuarc_IC_BANK_SEL:1]                 x1_tail_pc;           // 
// leda NTL_CON13A on
// leda NTL_CON12A on
reg                         x1_tail_pc_3;         // 

// @x1_page_xing_PROC
//
reg                         sa_pg_xing_replay;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to determine whether the next arriving instruction //
// is considered to be in a delay slot. This is determined by any one of    //
// three possible scenarios:                                                //
//                                                                          //
//   (a). The pipeline is empty and STATUS32.DE == 1                        //
//   (b). The DA instruction is a branch/jump with delay slot               //
//   (c). The SA instruction is a branch/jump with delay slot, and there is //
//        no instruction at DA.                                             //
//                                                                          //
// Rules (b) and (c) rely on the constraint that a branch/jump with delay   //
// slot will not progress beyond SA until its delay-slot instruction has    //
// arrived at DA. Therefore, a newly-issued delay-slot instruction in AL    //
// must either see the previously-issued instruction at DA or SA (and this  //
// corresponds to cases (b) and (c) respectively), or else we are in a      //
// situation where a restart has occurred when STATUS32.DE == 1 (case a).   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : pred_in_dslot_PROC

  //==========================================================================
  // `pipe_empty' is asserted when the pipeline does not contain any valid
  // instructions in stages DA thru CA. In this case, the value of the
  // STATUS32.DE bit indicates whether the next issued instruction is
  // considered to be in a delay slot. If STATUS32.DE == 1 but pipe_empty is
  // not asserted, then some downstream instruction is the delay slot
  // associated with the most recently committed instruction. Any speculative
  // instruction that has not yet has its delay-slot issued, will still be
  // in stages DA or SA.
  // If downstream stages contain error branches they are still counted empty.
  //

  pipe_empty    = ~(    da_valid_r
                      | sa_valid_r
                      | (x1_valid_r & (~x1_error_branch_r))
                      | (x2_valid_r & (~x2_error_branch_r))
                      | (x3_valid_r & (~x3_error_branch_r))
                      | (ca_valid_r & (~ca_error_branch_r))
                   );

  //==========================================================================
  // `al_in_dslot' is asserted when the pipeline considers the next issued
  // instruction to be in a delay slot. This is determined by any one of
  // three possible scenarios:
  //
  //   (a). The pipeline is empty and STATUS32.DE == 1
  //   (b). The DA instruction is a branch/jump with delay slot
  //   (c). The SA instruction is a branch/jump with delay slot, and there
  //        is no instruction at DA.
  //
  // Rules (b) and (c) rely on the constraint that a branch/jump with delay
  // slot will not progress beyond SA until its delay-slot instruction has
  // arrived at DA. Therefore, a newly-issued delay-slot instruction in AL
  // must either see the previously-issued instruction at DA or SA (and this
  // corresponds to cases (b) and (c) respectively), or else we are in a
  // situation where a restart has occurred when STATUS32.DE == 1 (case a).
  //
  al_in_dslot   = (pipe_empty & ar_aux_status32_r[`npuarc_DE_FLAG])          // (a)
                | (da_valid_r & da_dslot & (~da_error_branch_r))      // (b)
                | (sa_valid_r & sa_dslot_r & (~da_valid_r))           // (c)
                ;

  //==========================================================================
  // da_orphan_dslot_nxt: next insn at DA is an orphan delay-slot instruction
  // i.e. it was not issued after its parent branch. This can happen if a
  // delay-slot instruction is replayed, or if an RTIE instruction returns
  // to a delay-slot instruction. A non-orphan delay-slot instruction will
  // always reach the DA stage with its parent branch in the SA stage. This is
  // because a branch with delay-slot is not permitted to progress beyond SA
  // until its delay-slot arrives into the DA stage. Therefore, if a new
  // instruction is valid on the issue interface (al_pass == 1), and the
  // STATUS32.DE bit is set to 1, and there are no instructions in the pipe
  // from SA to WA inclusive, then the arriving instruction must be an 
  // orphan delay-slot.
  //
  da_orphan_dslot_nxt     = al_pass
                          & al_in_dslot
                          & pipe_empty
                          ;

end // block: pred_in_dslot_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to define the next values for DA-stage prediction  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : pred_da_nxt_PROC

  if (da_uop_busy_r == 1'b1)
  begin
    //========================================================================
    // Prediction information retained by uop-seq module.
    //
    da_is_pred_nxt         = al_uop_is_predicted & (~fch_restart);
    da_prediction_nxt      = al_uop_prediction;
    da_prediction_type_nxt = al_uop_prediction_type;
    da_with_dslot_nxt      = al_uop_with_dslot;
  end
  else
  begin
    //========================================================================
    // da_is_pred_nxt:  1 => Decode stage receives a valid prediction.
    //
    da_is_pred_nxt        = al_is_predicted & (al_pass & (~fch_restart));

    //========================================================================
    // da_prediction_nxt: incoming taken/not-taken outcome for next DA insn
    //
    da_prediction_nxt     = al_prediction & al_is_predicted;
  
    //========================================================================
    // da_prediction_type_nxt: next prediction type for insn at DA
    //
    da_prediction_type_nxt = al_prediction_type;
  
    //========================================================================
    // da_with_dslot_nxt: 1 => next insn at DA is PREDICTED to HAVE a dslot
    //
    da_with_dslot_nxt     = al_with_dslot   & (al_pass & (~fch_restart));

  end
  
  //========================================================================
  // da_error_branch_nxt: 1 => error branch for next insn at DA
  //
  da_error_branch_nxt   = al_error_branch & (al_pass & (~fch_restart) & (~da_holdup));
  
  //==========================================================================
  // da_in_dslot_nxt: next insn at DA is EXPECTED to BE IN a dslot
  //
  // We consider the arriving instruction to be in a delay slot if there
  // is a downstream branch with delay slot that does not yet have its
  // delay slot instruction in in the pipeline, and an instruction is being
  // passed into the DA stage, and the next instructuion is not being
  // killed by a fch_restart signal.
  //
  da_in_dslot_nxt         = al_in_dslot
                          & (al_pass | al_uop_pass)
                          & (~fch_restart)
                          ;
  
end // pred_da_nxt_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to determine eslot return misprediction at DA      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : eslot_mpd_PROC

  //==========================================================================
  // `no_ei_parent' is asserted when the pipeline does not contain any valid
  // instructions in stages SA thru CA. In this case, the value of the
  // STATUS32.ES bit indicates whether the current DA instruction is
  // considered to be in an execution slot. 
  //
  no_ei_parent    = ~(    sa_valid_r
                        | x1_valid_r
                        | x2_valid_r
                        | x3_valid_r
                        | ca_valid_r
                     );

  //==========================================================================
  // Determine whether there is a read-after-write hazard on the BTA register
  // when we need to use it as the return address for an eslot instruction.
  // This is the case if there is a continuous sequence of empty pipeline
  // stages from SA to a valid downstream EI_S instruction.
  //
  eslot_orphan    = (ca_ei_op_r & (~(x3_valid_r | x2_valid_r | x1_valid_r | sa_valid_r)))
                  | (x3_ei_op_r & (~(x2_valid_r | x1_valid_r | sa_valid_r)))
                  | (x2_ei_op_r & (~(x1_valid_r | sa_valid_r)))
                  | (x1_ei_op_r & (~(sa_valid_r)))
                  ;

  //==========================================================================
  // Determine whether the current DA instruciton is in an EI_S execution
  // slot. There are two cases where this is true:
  //
  //  (a). There is an EI_S instruction at the SA stage, or
  //
  //  (b). There is no valid instruction in SA, X1, X2, X3 or CA, and
  //       the STATUS32.ES bit is set to 1. Override this if operating
  //       within a prologue context - typically on an exception
  //       within a ESLOT.
  //
  //  (c). The DA instruction is a ESLOT orphan.
  //
  da_is_eslot     = sa_ei_op_r                         // (a)
                  | (    no_ei_parent                  // (b)
                       & ar_aux_status32_r[`npuarc_ES_FLAG]
                       & (~da_uop_prol_r)
                       & (~db_active)
                    )
                  | eslot_orphan                       // (c)
                  ;
  
  //==========================================================================
  // If an eslot instruction is executing immediately after a pipeline flush, 
  // then the parent EI_S instruction will not be in SA, and then the return
  // address for the eslot instruciton will be contained in the BTA register. 
  // However, if the SA stage contains an EI_S instruction, then sa_seq_pc_r
  // is the eslot target. We only need to consider these two cases, as a
  // parent EI_S will not progress beyond SA until its child eslot instruction
  // is valid in DA. This relies on the fact that there is no da_stall, and
  // therefore an DA eslot cannot be left in DA when the SA EI_S insn moves
  // on to X1. However, if there is an exception on the eslot insn, it could
  // be replayed without its parent EI_S instruction in the pipeline. In this
  // case the BTA register provides the committed value of the eslot target.
  //
  eslot_target    = sa_ei_op_r
                  ? sa_seq_pc_r
                  : ar_aux_bta_r[`npuarc_PC_RANGE]
                  ;


  //==========================================================================
  // Any valid DA instruction that is an eslot orphan, will experience a
  // read-after-write hazard on the BTA register. This is because there is
  // an outstanding speculative definition of BTA due to an EI_S instruction
  // that is not at the SA stage (from where a speculative BTA can be used).
  //
  da_eslot_stall  = da_valid_r & eslot_orphan;
  
  //==========================================================================
  // Detect whether an eslot instruction in DA has a mispredicted unconditional
  // jump back to the eslot_target address. If it has, then we make a special
  // case by assigning the correct eslot_target address to sa_pred_bta_nxt and
  // set sa_eslot_mpd_nxt to 1, to indicate that sa_pred_bta_nxt contains
  // the actual rather than predicted target. The sa_eslot_mpd_nxt signal
  // indicates that a misprediction for the next SA instruction has already
  // been detected. We need to compute this early, and store the restart
  // PC in the prediction pipeline, as there is no spare register at the X1
  // stage to carry a jump target. This is because the eslot instruction can
  // be any instruction and may therefore use all of x1_src0_r..x1_src3_r.
  //
  es_target_mpd   = (da_pred_bta_r != eslot_target);
  
  es_outcome_mpd  = (da_is_predicted_r == 1'b0) || (da_prediction_r == 1'b0);
  
  es_br_type_mpd  =  (da_is_predicted_r == 1'b1)
                //  && (da_prediction_type_r != `BR_UNCONDITIONAL);
                  && (da_prediction_type_r != `npuarc_BR_RETURN);
  
  es_da_mpd       =  (da_is_eslot == 1'b1)
                  && (    (es_br_type_mpd == 1'b1)
                       || (es_outcome_mpd == 1'b1)
                       || (es_target_mpd  == 1'b1)
                     )
                  ;
  
  if (es_da_mpd == 1'b1)
    sa_pred_bta_nxt = eslot_target;
  else
    sa_pred_bta_nxt = da_pred_bta_r;

  sa_eslot_mpd_nxt  = es_da_mpd & da_pass;
     
end // eslot_mpd_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to define the pipeline register enable signals     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : pred_enables_PROC

  //==========================================================================
  // Enables the update of prediction info registers at DA
  //
  da_info_cg0   = da_enable & ((al_pass & (!da_holdup)) | fch_restart);


  //==========================================================================
  // Enables the update of the predicted BTA at DA. Note that da_enable is
  // always asserted when the DA stage is killed from either X2 or WA.
  // Hence, there is no requirement to include fch_restart in this signal.
  //
  da_pred_cg0   = da_enable & (~da_holdup) & al_pass & al_is_predicted;

  da_ctrl_cg0   = da_enable;

  da_err_br_cg0 = da_enable 
                & (   ((al_pass | da_is_predicted_r) & (~da_holdup))
                    | fch_restart
                  )
                ;
  
  sa_info_cg0   = sa_enable & da_pass;

  sa_pred_cg0   = sa_enable 
                & da_pass
                & (   da_is_predicted_r
                    | da_is_eslot
                  )
                ;
  
  sa_ctrl_cg0   = sa_enable;

  x1_info_cg0   = x1_enable & sa_pass;

  x1_pred_cg0   = x1_enable
                & sa_pass 
                & (~sa_uop_inst_r)
                & (   sa_is_predicted_r
                    | sa_eslot_mpd_r
                  )
                ;

  x1_ctrl_cg0   = x1_enable;

  x2_info_cg0   = x2_enable & x1_pass;

  x2_pred_cg0   = x2_enable
                & x1_pass
                & (   x1_is_predicted_r
                    | x1_eslot_mpd_r
                  )
                ;

  x2_ctrl_cg0   = x2_enable;

  x3_info_cg0   = x3_enable & x2_pass;

  x3_pred_cg0   = x3_enable
                & x2_pass
                & (   x2_is_predicted_r
                    | x2_eslot_mpd_r
                  )
                ;

  x3_ctrl_cg0   = x3_enable;

  ca_info_cg0   = ca_enable & x3_pass;

  ca_pred_cg0   = ca_enable
                & x3_pass
                & (   x3_is_predicted_r
                    | x3_eslot_mpd_r
                  )
                ;

  ca_ctrl_cg0   = ca_enable;

  //==========================================================================
  // Enable the X2-stage early misprediction control registers under either
  // of the following two conditions:
  //
  //  (a). Existing mispredictions must be cleared by a pipeline restart
  //  (b). There is an incoming early misprediction at the X1 stage
  //  (d). There is a fragmented error branch in the X1 stage
  //
  x2_mpd_cg0    = fch_restart                                     // (a)
                | (x1_pass & x2_enable & x1_mispredict)           // (b)
                | x1_error_branch_r                               // (d)
                ;

  //==========================================================================
  // Enable the Misprediction Interface output registers under any of 
  // the following three conditions:
  //
  //  (a). Existing mispredictions must be cleared by a pipeline restart
  //  (b). There is an incoming early misprediction at the X1 stage
  //  (c). There is an incoming late misprediction at the CA stage
  //
  mpd_data_cg0  = x2_mpd_cg0                                      // (a), (b)
                | (wa_enable & ca_mispredict)                     // (c)
                ;

  //==========================================================================
  // Enable the Branch Commit Interface data output registers under any of
  // the following conditions, provided there is not already a pending
  // branch-commit action in the branch-commit registers.
  //
  //  (a). There is a predictable branch to commit to the IFU, regardless
  //       of whether it was correctly or incorrectly predicted.
  //       OR: a commit stage ZOL jump that was not predicted in the SA stage
  //
  //  (b). The current wa_type field is non-zero. This enables the clock
  //       to the data registers of the branch-commit interface in order
  //       to remove the previous transaction.
  //
  brc_data_cg0  = (   ca_pass
                    & wa_enable
                    & (~wa_pending_r)
                    & (    ca_predictable_r  | ca_zol_branch       // (a)
                        | (|wa_br_type_r)                          // (b)
                      )
                  )
                | (   wa_enable
                    & (~wa_pending_r)
                    & (    (ca_error_branch_r | ca_detect_err_br | x2_pg_xing_dslot_r)
                        | wa_error_branch_r
                      )
                  )
                ;

  //==========================================================================
  // Enable the Branch Commit Interface control registers whenever the 
  // Writeback stage is enabled to receive new input.
  //
  brc_ctrl_cg0  = wa_enable & (wa_pass_r | wa_pass_nxt)
                | ca_restart
                ;

  //==========================================================================
  // Set wa_pending for a predicted uop branch that is not at the end
  // of the sequence. That can happen if it has a delay slot.
  // Branch commit signals need to be asserted with the last uop instr
  // in the sequence and wa_pending makes sure those signals remain registered.
  //
  wa_pending_nxt  = (ca_multiop_jump & ca_uop_active_r & (~ca_uop_commit_r))
                  | (wa_pending_r & (~ca_uop_commit_r))
                  ;

end // block: pred_enables_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to detect branch mispredictions at SA, X1 and CA   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : pred_detect_PROC

  //==========================================================================
  // `sa_predictable' is asserted when the SA branch type is not set to
  // BR_NOT_PREDICTED by the instruction decoding logic in alb_exec1.
  // A LEAVE_S instruction, with the pcl operand enabled, is given an
  // sa_br_type value of BR_RETURN, by the SA-stage branch-type decoder.
  // That allows this process to detect a mismatching prediction type.
  // However, the prediction associated with the LEAVE_S instruction must not
  // be resolved when the LEAVE_S instruction is at X1 (or CA for late
  // prediction), and the prediction check must be delayed to the J_S.D
  // micro-op.
  //
  sa_predictable      = (sa_br_type != 3'd`npuarc_BR_NOT_PREDICTED)
                      & (~sa_leave_op_r)
                      & (~sa_iprot_viol_r)
                      ;

  //==========================================================================
  // Determine whether there is a possible error branch at SA. This signal is
  // used only to select the restart PC from the SA stage. For an error branch
  // it must be the current sa_pc_r, otherwise it should be sa_seq_pc_r.
  //
  // There are two types of error branch; those caused by fragmented issue,
  // and those caused by a mismatch in prediction types, or mismatching
  // presence of a delay-slot, between what was issued and what was decoded.
  //
  // The rules for reporting an error branch are:
  //
  // 1. An error branch due to fragmented issue, indicated by the
  //    sa_error_branch_r signal, is always reported.
  //
  // 2. An error branch to to mismatching prediction types is reported only
  //    for instructions that were issued with a prediction.
  //
  // 3. An error branch due to mismatching prediction types is never
  //    reported on a micro-operation, i.e. when sa_uop_inst_r == 1.
  //
  // 4. An error branch due to mismatching prediction types may be
  //    reported if the prediction type is different from the decoded
  //    branch type.
  //
  // 5. An error branch due to mismatching prediction types may be
  //    reported if the prediction assumed the branch has a delay slot
  //    when it does not (or vice versa).
  //
  // Additionally:
  // 6. If al_error_branch is asserted simultaneously with the delay slot
  //    of a branch that is predicted to have a delay slot, then
  //    the branch instruction is treated as an error branch.
  //    If the branch is in SA then the delay slot has a rendez-vous in DA
  //    and we can rely on the da_error_branch_r signal to indicate
  //    the error branch for the delay slot.
  // 7. If there is a potential ZOL phantom branch, then postpone
  //    resolving the type error branch to CA.
  //
  sa_error_branch     = sa_error_branch_r                             // (1)
                      | (   sa_is_predicted_r                         // (2)
                          & (~sa_uop_inst_r)                          // (3)
                          & (   (sa_prediction_type_r != sa_br_type)  // (4)
                              | (sa_with_dslot_r      != sa_dslot_r)  // (5)
                            )
                          & (~sa_zol_hazard)                            // (7)
                        )
                      | (sa_is_predicted_r 
                         & sa_with_dslot_r & da_error_branch_r)         // (6)
                      ;

  // Detect an error branch in CA:
  // Most error branches are handled in X1, except those related to ZOL
  // phantom branches.
  // If there is a ZOL jump in CA, then we need to expect a 
  // predicted ZOL phantom branch. (1)
  // If there is another branch at the end of a ZOL loop body, the ZOL
  // branch is not predicted and there is no phantom branch. (2)
  // A ZOL phantom branch has type BR_CONDITIONAL. (3)
  // A ZOL phantom has no dslot. (4)
  // If there is no ZOL jump and there is a regular predicted branch, (5) 
  // then we need to check the type of that branch. (6) 
  // Also the dslot. (7)
  // UOP instructions injected by the UOP sequencer
  // are excluded from error checking because they
  // are not issued by the IFU and not predicted. (8)
 
  ca_detect_err_br = (ca_is_predicted_r
                      & (~ca_uop_inst)   // (8)
                      & ca_hit_lp_end    // (1)
                      & (~ca_branch_evt)   // (2)
                      & ( (ca_prediction_type_r != `npuarc_BR_CONDITIONAL) // (3)
                          |
                          ca_with_dslot_r // (4)
                        )
                     )
                   | (ca_is_predicted_r
                      & (~ca_uop_inst) // (8)
                      & (ca_branch_evt | (~ca_hit_lp_end))  // (5)
                      & ( (ca_prediction_type_r != ca_br_type_r) // (6)
                          |
                          (ca_with_dslot_r != ca_dslot_r)  // (7)
                        )
                     )
                   ;


                     
  //==========================================================================
  // Stall the X1 stage if it contains a delay-slot instruction with an
  // erroneous prediction, until all downstream pre-commit stages are empty.
  // This ensures that the error-branch misprediction at X2 will not be
  // superceded by a downstream misprediction from an earlier instruction.
  // However, this stall should not be applied if the X2-stage instruction
  // has the x2_pg_xing_replay_r bit set to 1, as we should allow the
  // error branch associated with the X1 instruction to precede the replay
  // that will happen when the X2 instruction reaches CA.
  // 
  x1_dslot_stall      = x1_in_dslot_r
                      & x1_error_branch_r
                      & (x2_valid_r | x3_valid_r | ca_valid_r)
                      & (~x2_pg_xing_replay_r)
                      & (~(x3_pg_xing_replay_r & (~x2_valid_r)))
                      & (~(ca_pg_xing_replay_r & (~x2_valid_r) & (~x3_valid_r)))
                      ;
                      
  //==========================================================================
  // Determine when a branch can be resolved at X1. This requires that the
  // X1 stage is valid, and it is not being killed in the current cycle,
  // and X1 contains a predictable branch, and all flag and target register
  // dependencies are satisfied at X1.
  // Furthermore, if an eslot prediction has already been made, then it
  // prevents a regular branch misprediction being reported. In this case, 
  // the x1_eslot_mpd_r signal indicates whether the return branch from the
  // eslot instruction was correctly predicted.
  // Exclude uop-sequence epilogues from early resolve; they are done in CA (a)
  //
  x1_resolve          = x1_valid_r
                      & x1_predictable_r
                      & x1_early_pred_r  // set to 1 when simple ZOL is used
                      & x1_cond_ready
                      & (~x1_in_dslot_r)
                      & (~x1_is_eslot_r)
                      & (~x1_zol_hazard_r) // postpone ZOL
                      & (~x1_kill)
                      & (~x1_error_branch_r)
                      & (~x1_uop_epil_r)     // (a)
                      ;

  x1_resolve_pred     = x1_resolve;

  x1_resolve_bta      = x1_resolve & x1_bta_ready
                      & (x1_prediction_r | x1_br_direction);

  //==========================================================================
  // Detect early misprediction of conditional branch/jump outcome at X1.
  // 
  x1_mispred_outcome  = (   x1_resolve_pred
                          & (x1_br_direction != x1_prediction_r))
                      | (x1_zol_mpd_dir & (~x1_predictable_r))
                      ;

  //==========================================================================
  // Detect early misprediction of Branch Target Address (BTA) at X1.
  // This requires that x1_resolve_bta is asserted to indicate that the
  // BTA value is available for use in the misprediction check.
  // The BTA mispredicton of an execution-slot instruction is given by the
  // x1_eslot_mpd_r signals.
  // The BTA misprediction of a BI, BIH instruction is computed in the 
  // alb_exec1 module, and is provided via x1_bi_bta_mpd. Otherwise,
  // a misprediction is indicated when x1_br_target is different from
  // the predicted x1_pred_bta_r value.
  //
  x1_mispred_bta      = (   x1_resolve_bta 
                          & (   x1_btab_op_r
                              ? x1_bi_bta_mpd
                              : (x1_br_target != x1_pred_bta_r)
                            )
                        )
                      | (   (~fch_restart)
                          & (   (x1_eslot_mpd_r & (~x1_error_branch_r))
                            )
                        )
                      ;

  x1_is_predicted     = x1_is_predicted_r;

  //==========================================================================
  // Detect erroneous branch predictions at X1, the error branch must not 
  // be asserted if the X1 stage is killed in the current cycle. 
  // In this case, the fault should not propagate to X2.
  //
  x1_error_branch     = x1_error_branch_r & (~x1_kill)
                      ;

  //==========================================================================
  // Derive x1_restart_pc as a function of the current predictor state
  // in X1. Override result of error branches to ensure that the current PC 
  // is appropriately replayed.
  //
  //

  casez ({   x1_error_branch
           , x1_br_taken
           , x1_eslot_mpd_r
           , 1'b0   // ZOL is resolved late, so don't need to mux here
         })
    4'b011?: x1_restart_pc = x1_pred_bta_r;
    4'b010?: x1_restart_pc = x2_target_nxt;
    4'b0001: x1_restart_pc = ar_aux_lp_start_r[`npuarc_PC_RANGE];
    default: x1_restart_pc = x1_br_fall_thru;
  endcase

  x2_br_resolved_nxt  = (x1_resolve | x1_error_branch | x1_is_eslot_r);
  
  x1_direction        = x1_br_direction & !x1_error_branch_r;

  x1_mispredict       = x1_pass
                      & (   x1_mispred_outcome
                          | x1_mispred_bta
                          | x1_error_branch
                        )
                      ;

  x2_late_pred_nxt    = x1_pass 
                      & (!x2_br_resolved_nxt)
                      & (x1_br_type_r != `npuarc_BR_NOT_PREDICTED)
                      ;

  //==========================================================================
  // Restart from X2 on misprediction or an orphan D-Slot unless
  // killed from downstream.
  //
  x2_restart_nxt      = (~x1_kill) & (x1_mispredict)
                      ;

  //==========================================================================
  // Identify the jump instruction in a multi-op sequence to which any
  // branch resolution should be applied.
  // This should only be done for uop sequences that are predicted.
  //
  ca_multiop_jump     = ca_uop_active_r
                      & ca_jump_r
                      & (   ca_uop_commit_r
                          | ca_dslot_r
                        )
                      ;

  //==========================================================================
  // Determine whether a branch should be resolved at CA. This requires that
  // the CA stage is valid, and it is not being killed in the current cycle,
  // that CA contains a predictable branch, and that branch has not already
  // been resolved (and possibly mispredicted early).
  // LEAVE_S instructions have an associated BR_RETURN prediction, but it
  // must not be resolved when the LEAVE_S instruction is at CA. Instead,
  // the prediction is resolved when the J_S.D jump to the return address,
  // if present, is at X1 or CA (depending on when it is able to be resolved).
  //
  ca_resolve          = ca_pass
                      & (~ca_br_resolved_r)
                      & (~ca_leave_op_r)
                      & (~ca_uop_active_r | ca_multiop_jump)
                      ;

  //==========================================================================
  // Compute the direction (1=taken versus 0=non-taken) for branches and
  // zero-overhead loop-backs, and detect whether the actual direction was
  // incorrectly predicted (ca_mispred_outcome).
  //
  ca_direction        = ca_br_direction
                      | ca_zol_lp_jmp
                      ;

  ca_mispred_outcome  = (ca_direction != ca_prediction_r)
                      | ca_zol_mpd_dir
                      ;

  //==========================================================================
  // Select the target of a control transfer that is present at the CA stage.
  // If an implicit zero-overhead loop-back occurs on completion of the 
  // current CA instruction, then ca_zol_lp_jmp is asserted, and then the
  // target is given by the LP_START register (ar_aux_lp_start_r).
  // Otherwise, the target is given by ca_br_target.
  //
  ca_target           = ca_zol_lp_jmp
                      ? ar_aux_lp_start_r[`npuarc_PC_RANGE]
                      : ca_br_target
                      ;

  //==========================================================================
  // Detect the misprediction of a branch target at the CA stage. 
  // The ca_br_jmp_mpd_bta signal indicates target mispredictions for all
  // control transfers except zero-overhead loop-back and BI or BIH jumps.
  //
  ca_br_jmp_mpd_bta   = ca_br_or_jmp
                      & (ca_prediction_r | ca_br_direction)
                      & (ca_br_target != ca_pred_bta_r)
                      & (~(ca_zol_lp_jmp))
                      & (~ca_btab_op_r)
                      ;
  
  //==========================================================================
  // Overall misprediction of Branch Target Address (BTA) at the CA stage.
  // This is computed as the logical OR of all mutually-exclusive sources
  // of BTA misprediction at the CA stage, including:
  //
  // (a). Regular branch and jump instructions
  //
  // (b). Implicit zero-overhead loop-backs
  //
  // (c). Jumps due to BI or BIH instructions
  //
  ca_mispred_bta      = ca_br_jmp_mpd_bta                   // (a)
                      | ca_zol_mpd_bta                      // (b)
                      | ca_bi_bta_mpd_r                       // (c)
                      ;

  ca_is_predicted     = ca_is_predicted_r;

  ca_mispredict       = ca_resolve
                      & (   ca_mispred_outcome
                          | ca_mispred_bta
                          | ca_error_branch_r
                          | ca_detect_err_br
                        )
                      ;

  //==========================================================================
  // Select the early or late branch outcome, which is needed when selecting
  // the correct next PC at the Commit stage. This excludes ZOL loop-back,
  // as that requires a different source of next PC (LP_START).
  //
  ca_br_taken         = ca_br_resolved_r
                      ? ca_br_outcome_r
                      : ca_br_direction
                      ;

  //==========================================================================
  // Branch prediction type to be used on mispredict and commit interfaces.
  // If the mispredict is for a uop sequence, then it must be a LEAVE_S
  // and therefore set mpd_type to BR_RETURN.
  //
  ca_type = ca_zol_branch ? `npuarc_BR_CONDITIONAL 
                          : (ca_uop_active_r ? `npuarc_BR_RETURN
                                             : ca_br_type_r
                             )
                           ;

  //==========================================================================
  // Select CA misprediction, if present, otherwise select X1 misprediction
  // During micro-op sequences ordinary branch prediction is turned off.
  // Use restart without mispredict, so set mpd_mispred=0.
  // Turn mpd_mispred only on for predictable UOP sequences.
  // That is LEAVE_S (with a jump).

  mpd_mispred_nxt     = ca_mispredict ? (~ca_uop_active_r | ca_uop_predictable_r)
                                      : (x1_mispredict & (~x1_uop_inst_r | x1_uop_predictable_r));
  mpd_early_nxt       = ~ca_mispredict;

  if (ca_mispredict == 1'b1)
    begin
    mpd_direction_nxt       = ca_direction;
    mpd_error_branch_nxt    = (ca_error_branch_r & (~ca_br_resolved_r)) | ca_detect_err_br;
    mpd_is_predicted_nxt    = ca_is_predicted;
    mpd_mispred_outcome_nxt = ca_mispred_outcome;
    mpd_mispred_bta_nxt     = ca_mispred_bta;
    mpd_branch_info_nxt     = ca_branch_info_r;
    mpd_dslot_nxt           = ca_dslot_r          & (~ca_uop_active_r);
    mpd_type_nxt            = ca_type;
    mpd_seq_next_pc_nxt     = ca_br_fall_thru;
    mpd_pc_nxt              = ar_pc_r;
    mpd_secondary_nxt       = ca_secondary_r;
    mpd_tail_pc_3_nxt       = ca_tail_pc_3;
    mpd_commit_size_nxt     = ca_commit_size_r;
    end
  else
    begin
    mpd_direction_nxt       = x1_direction;
    mpd_error_branch_nxt    = x1_error_branch     & x1_pass;
    mpd_is_predicted_nxt    = x1_is_predicted;
    mpd_mispred_outcome_nxt = x1_mispred_outcome;
    mpd_mispred_bta_nxt     = x1_mispred_bta;
    mpd_branch_info_nxt     = x1_branch_info_r;
    mpd_dslot_nxt           = x1_dslot_r & (~x1_uop_inst_r);
    mpd_type_nxt            = x1_br_type_r;
    mpd_seq_next_pc_nxt     = x1_link_addr;     // link address of subr call
    mpd_pc_nxt              = x1_pc_r;
    mpd_secondary_nxt       = x1_secondary_r;
    mpd_tail_pc_3_nxt       = x1_tail_pc_3;
    mpd_commit_size_nxt     = x1_commit_size_r;
    end

  //==========================================================================
  // Select the early or late branch/jump/loop direction, which is needed
  // by the Branch Commit interface to indicate the direction that was taken.
  // This comes from the early prediction (ca_br_outcome_r) if the branch
  // was resolved at X1. Otherwise it is the current CA-stage computation of
  // the branch direction (ca_br_direction) or the ZOL loop-back condition
  // (ca_zol_lp_jmp).
  //
  wa_direction_nxt        = ca_br_resolved_r
                          ? ca_br_outcome_r
                          : (ca_br_direction | ca_zol_lp_jmp)
                          ;
                      
  //==========================================================================
  // Select the early or late misprediction outcome, which is needed
  // by the Branch Commit interface to indicate when a misprediction occured.
  // This comes from the early misprediction (ca_early_mispred_outcome_r)
  // if the branch was resolved at X1. Otherwise it is the current CA-stage 
  // computation of the branch misprediction (ca_mispred_outcome).
  // Both options are gated with ca_is_predicted_r.
  //
  wa_mispred_outcome_nxt  = ca_br_resolved_r
                          ? (ca_early_mispred_outcome_r & ca_is_predicted_r)
                          : (ca_mispred_outcome         & ca_is_predicted_r)
                          ;
                          
  //==========================================================================
  // Select the early or late mispredicted BTA, which is needed by the Branch
  // Commit interface to indicate that the target of a prediction was
  // not accurate. This is the early mispredict BTA (ca_early_mispred_bta_r)
  // if the branch was resolved at X1. Otherwise it is the current CA-stage 
  // computation of the BTA misprediction (ca_mispred_bta).
  // Both options are gated with ca_is_predicted_r.
  //
  wa_mispred_bta_nxt      = ca_br_resolved_r
                          ? (ca_early_mispred_bta_r & ca_is_predicted_r)
                          : (ca_mispred_bta         & ca_is_predicted_r)
                          ;

end // block: pred_detect_PROC


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// Combinational process to manage and invoke WA-stage pipeline flush        //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

always @*
begin: flush_detect_PROC

  //==========================================================================
  // A replay is required in the next cycle, from the Writeback stage,
  // when a flush condition is detected from one of the following causes:
  //
  //   (a) A DC4 replay.
  //   (b) A halt request from either a synchronous pipeline event or
  //       asynchronous request.
  //   (c) An instruction replay request from the Commit stage.
  //   (d) A branch-and-link with dslot has an error branch on the dslot
  //       and the dslot crosses a page boundary.
  //   (e) An ifetch protection violation is valid at the CA stage.
  //
  // A flush will be defeated if a restart is currently asserted by the
  // Writeback stage.
  //
  ca_replay           = (~wa_restart_kill_r)
                      & (   dc4_replay            // (a)
                          | hlt_restart           // (b)
                          | ct_replay             // (c)
                          | ca_pg_xing_replay_r   // (d)
                          | ca_iprot_viol_r       // (e)
                        )
                      ;

  //==========================================================================
  // A commit-stage flush will always discard the entire contents of the
  // pre-commit pipeline from F1 to CA inclusive. A flush may be triggered
  // by any of the replay conditions or an exception. It excludes branch
  // mispredictions reported at CA, as they allow the CA instruction to
  // commit (except for error-branch mispredictions).
  //
  ca_flush            = excpn_restart
                      | ca_replay
                      ;

  // ca_restart_without_mispredict:
  // a flush (that discards the complete pipeline)
  // or an orphan delay slot (that commits)
  //
  ca_restart_without_mispredict = ca_flush 
                                |(ca_orphan_dslot_r & ca_pass)
                                ;
  //==========================================================================
  // A restart is required in the next cycle, from the Writeback stage,
  // if a flush condition is detected in CA in the current cycle, or if 
  // there is a late misprediction associated with the CA-stage instruction.
  // Mispredictions will not be resolved in CA if there is a pipeline flush
  // already in progress in the current cycle.
  //

  ca_restart          = ca_restart_without_mispredict
                      | (ca_mispredict 
                          & (~ar_aux_debug_r[`npuarc_DEBUG_IS] | ca_uop_active_r)
                          & (~ca_sleep_evt)
                        )
                      ;


  //==========================================================================
  // Kill CA in the next cycle, (as a consquence of a WA-stage
  // restart), on the following conditions:
  //
  //   (1) On a 'Halt'-restart, where CA is always killed regardless of
  //       its contents.
  //
  //   (2) On a mispredicted branch without a slot.
  //
  //
  // During single-step mode a halt event is triggered in CA whenever a normal
  // instruction commits. That shouldn't be killed by a restart in WA.
  // A sleep or trap instruction in an orphan delay slot or in the last position
  // of a ZOL body shouldn't be killed in the next cycle.
  //
  ca_restart_kill_ca  = hlt_restart                         // (1)
                      | (ca_mispredict & (~ca_dslot_r) 
                          & (~ar_aux_debug_r[`npuarc_DEBUG_IS])
                          & (~ct_excpn_trap_nxt)
                          & (~ca_sleep_evt)
                          & (~ca_cmt_brk_evt)
                        )                                    // (2)
                      | ct_replay
                      | dc4_replay
                      | excpn_restart
                      |(ca_orphan_dslot_r & ca_pass 
                          & (~ar_aux_debug_r[`npuarc_DEBUG_IS])
                          & (~ct_excpn_trap_nxt)
                          & (~ca_sleep_evt)
                       )
                      | ca_iprot_viol_r
                      ;
  
  //==========================================================================
  // EXU requests that IFU stop on the cycle after a WA_RESTART
  // request on halt events.
  //
  ca_stop             = (hlt_restart & hlt_stop)
                      | (db_active & dc4_replay)
                      ;

  //==========================================================================
  // The next restart PC address for the Writeback stage comes from one of
  // the following sources, according to their respective conditions. 
  // These are presented in priority order:
  //
  //  (a) excpn_restart_pc - when excpn_restart is asserted.
  //
  //  (b) ar_pc_r          - when ca_replay is asserted
  //
  //  (c) ca_br_target     - when excpn_restart and ca_replay are not 
  //                         asserted, and there is a taken branch at CA.
  //
  //
  //  (d) ca_bi_target     - when excpn_restart and ca_replay are not
  //                         asserted, and there is a BI or BIH instruction
  //                         at CA.
  //  (e) ar_lp_start_r    - when excpn_restart and ca_replay are not
  //                         asserted, and there is no taken branch, 
  //                         and a ZOL loop-back is detected.
  //
  //  (f) ca_br_fall_thru  - when excpn_restart and ca_replay are not
  //                         asserted, and there is no taken branch, 
  //                         and there is no ZOL loop-back detected.
  //
  //  (g) BTA  - when excpn_restart and ca_replay are not
  //                         asserted, and there is an orphan delay slot. 
  //
  //
  casez ({  excpn_restart,
            ca_replay, 
            ca_br_taken, 
            ca_btab_op_r, 
            (   ca_orphan_dslot_r
              | ar_aux_status32_r[`npuarc_DE_FLAG]
              | ar_aux_status32_r[`npuarc_ES_FLAG]
            ),
            ca_zol_lp_jmp
         })
    6'b000?00: wa_restart_pc_nxt = ca_br_fall_thru;                  // (f)
    6'b000?01: wa_restart_pc_nxt = ar_aux_lp_start_r[`npuarc_PC_RANGE];     // (e)
    6'b00110?: wa_restart_pc_nxt = ca_br_target;                     // (d)
    6'b00100?: wa_restart_pc_nxt = ca_br_target;                     // (c)
    6'b01????: wa_restart_pc_nxt = ar_pc_r;                          // (b)
    6'b00??1?: wa_restart_pc_nxt = ar_aux_bta_r[`npuarc_PC_RANGE];          // (g)
    default:   wa_restart_pc_nxt = excpn_restart_pc;                 // (a)
  endcase

  //==========================================================================
  // Create a transaction on the Branch Commit Interface when committing
  // an instruction.
  // Turn wa_pass off for micro-op instructions that don't participate 
  // in branch prediction. Only LEAVE_S is predicted.
  // The ENTER_S also needs to be committed to free up its issue resource 
  // in the IFU. All other micro-up sequences finish with a restart without
  // misprediction, that resets the IFU state.
  //
  wa_pass_nxt   = (   wa_cmt_norm_evt_nxt 
                    & (  (~ca_uop_active_r)
                        | ca_uop_predictable_r 
                        | ca_uop_enter_r
                      )
                  )
                | ((ca_error_branch_r | x2_pg_xing_dslot_r) & (~wa_restart_r) & (~ca_flush))
                ;

end // block: flush_detect_PROC


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// Combinational process to calculate x1_tail_pc_3                           //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
// leda W484 off
// LMD:  Possible loss of carry/borrow in addition/subtraction LHS : 3, RHS : 4
// LJ:  wrap-around on addition overflow is expected and required in this case
// leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  wrap-around on addition overflow is expected and required in this case
always @*
begin: x1_tail_pc_PROC

//x1_tail_pc      = x1_br_fall_thru[3:1] + 3'b111;
  x1_tail_pc      = x1_br_fall_thru[`npuarc_IC_BANK_SEL:1] + {`npuarc_IC_BANK_SEL{1'b1}};
//x1_tail_pc_3    = x1_tail_pc[3];
  x1_tail_pc_3    = x1_tail_pc[`npuarc_IC_BANK_SEL]; 

end 
/// leda BTTF_D002 on
// leda W484 on
////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// Combinational process to detect when a branch-and-link with delay slot    //
// has a delay-slot instruction (partially) in a different page from the     //
// parent branch, when the delay-slot instruction is also tagged as an       //
// error branch. In this case there may be an ITLB fault unreported on the   //
// delay-slot instruction, and therefore the parent branch is not able to    //
// commit. This requires that the parent branch is given the pg_xing_reply   //
// attribute at the SA stage, which it then carries down the pipeline to the //
// CA stage. This triggers two further actions, (1) at X3 and (2) at CA.     //
//                                                                           //
//  1. When the instruction reaches X3 it stalls there until a valid         //
//     instruction is present at X2. This is guaranteed to be the delay      //
//     slot instruction, and it is guaranteed to arrive. This is because     //
//     the pg_xing_replay attribute can be attached only to bl.d instructions//
//     that have rendezvoused with their delay-slot instruction at SA/DA.    //
//                                                                           //
//  2. When the instruction reaches CA it triggers a replay. This ensures    //
//     that the parent branch and its delay slot instruction are refetched.  //
//                                                                           //
// These two actions together ensure that the error branch on the delay-slot //
// instruction gets reported at X2 before the parent branch gets replayed.   //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

always @*
begin : x1_page_xing_PROC

  sa_pg_xing_replay = sa_valid_r & sa_link_r & sa_dslot_r
                    & da_valid_r & da_error_branch_r & da_ifu_err_nxtpg_r & da_ifu_exception_r
                    ;
  
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define state updates to pipelined control signals //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : pred_ctrl_regs_PROC

  if (rst_a == 1'b1)
    begin
    da_is_predicted_r     <= 1'b0;
    da_prediction_r       <= 1'b0;
    da_prediction_type_r  <= `npuarc_BR_TYPE_BITS'b0;
    da_error_branch_r     <= 1'b0;
    da_with_dslot_r       <= 1'b0;
    da_in_dslot_r         <= 1'b0;
    da_orphan_dslot_r     <= 1'b0;

    sa_is_predicted_r     <= 1'b0;
    sa_prediction_r       <= 1'b0;
    sa_prediction_type_r  <= `npuarc_BR_TYPE_BITS'b0;
    sa_error_branch_r     <= 1'b0;
    sa_with_dslot_r       <= 1'b0;
    sa_in_dslot_r         <= 1'b0;
    sa_orphan_dslot_r     <= 1'b0;

    x1_is_predicted_r     <= 1'b0;
    x1_prediction_r       <= 1'b0;
    x1_prediction_type_r  <= `npuarc_BR_TYPE_BITS'b0;
    x1_error_branch_r     <= 1'b0;
    x1_with_dslot_r       <= 1'b0;
    x1_in_dslot_r         <= 1'b0;
    x1_br_type_r          <= `npuarc_BR_TYPE_BITS'd0;
    x1_commit_size_r      <= 2'd0;
    x1_secondary_r        <= 1'b0;
    x1_predictable_r      <= 1'b0;
    x1_uop_predictable_r  <= 1'b0;
    x1_orphan_dslot_r     <= 1'b0;
    x1_pc_r               <= `npuarc_PC_BITS'b0;

    x2_is_predicted_r     <= 1'b0;
    x2_prediction_r       <= 1'b0;
    x2_prediction_type_r  <= `npuarc_BR_TYPE_BITS'b0;
    x2_error_branch_r     <= 1'b0;
    x2_fragged_r          <= 1'b0;
    x2_with_dslot_r       <= 1'b0;
    x2_in_dslot_r         <= 1'b0;
    x2_br_type_r          <= `npuarc_BR_TYPE_BITS'd0;
    x2_commit_size_r      <= 2'd0;
    x2_secondary_r        <= 1'b0;
    x2_br_outcome_r       <= 1'b0;
    x2_br_resolved_r      <= 1'b0;
    x2_late_pred_r        <= 1'b0;
    x2_predictable_r      <= 1'b0;
    x2_orphan_dslot_r     <= 1'b0;
  
    x3_is_predicted_r     <= 1'b0;
    x3_prediction_r       <= 1'b0;
    x3_prediction_type_r  <= `npuarc_BR_TYPE_BITS'b0;
    x3_error_branch_r     <= 1'b0;
    x3_late_pred_r        <= 1'b0;
    x3_fragged_r          <= 1'b0;
    x3_with_dslot_r       <= 1'b0;
    x3_in_dslot_r         <= 1'b0;
    x3_br_type_r          <= `npuarc_BR_TYPE_BITS'd0;
    x3_commit_size_r      <= 2'd0;
    x3_secondary_r        <= 1'b0;
    x3_br_outcome_r       <= 1'b0;
    x3_br_resolved_r      <= 1'b0;
    x3_predictable_r      <= 1'b0;
    x3_orphan_dslot_r     <= 1'b0;
    x3_early_mispred_outcome_r <= 1'b0;
    x3_early_mispred_bta_r <= 1'b0;

    ca_is_predicted_r     <= 1'b0;
    ca_prediction_r       <= 1'b0;
    ca_prediction_type_r  <= `npuarc_BR_TYPE_BITS'b0;
    ca_error_branch_r     <= 1'b0;
    ca_fragged_r          <= 1'b0;
    ca_with_dslot_r       <= 1'b0;
    ca_in_dslot_r         <= 1'b0;
    ca_br_type_r          <= `npuarc_BR_TYPE_BITS'd0;
    ca_commit_size_r      <= 2'd0;
    ca_secondary_r        <= 1'b0;
    ca_br_outcome_r       <= 1'b0;
    ca_br_resolved_r      <= 1'b0;
    ca_predictable_r      <= 1'b0;
    ca_orphan_dslot_r     <= 1'b0;
    ca_early_mispred_outcome_r <= 1'b0;
    ca_early_mispred_bta_r <= 1'b0;
    x2_bi_bta_mpd_r       <= 1'b0;
    x3_bi_bta_mpd_r       <= 1'b0;
    ca_bi_bta_mpd_r       <= 1'b0;
    sa_eslot_mpd_r        <= 1'b0;
    sa_is_eslot_r         <= 1'b0;
    x1_eslot_mpd_r        <= 1'b0;
    x1_is_eslot_r         <= 1'b0;
    x2_eslot_mpd_r        <= 1'b0;
    x3_eslot_mpd_r        <= 1'b0;
//    ca_eslot_mpd_r        <= 1'b0;
    x1_pg_xing_replay_r   <= 1'b0;
    x2_pg_xing_replay_r   <= 1'b0;
    x3_pg_xing_replay_r   <= 1'b0;
    ca_pg_xing_replay_r   <= 1'b0;
    sa_pg_xing_dslot_r    <= 1'b0;
    x1_pg_xing_dslot_r    <= 1'b0;
    x2_pg_xing_dslot_r    <= 1'b0;
    end
  else
    begin

    if (da_ctrl_cg0 == 1'b1)
      begin
      da_prediction_r       <= da_prediction_nxt;
      da_prediction_type_r  <= da_prediction_type_nxt;
      da_with_dslot_r       <= da_with_dslot_nxt;
      da_in_dslot_r         <= da_in_dslot_nxt;
      da_orphan_dslot_r     <= da_orphan_dslot_nxt;
      end

    if (da_err_br_cg0 == 1'b1)
      begin
      da_is_predicted_r     <= da_is_pred_nxt;
      da_error_branch_r     <= da_error_branch_nxt;
      end
      
    if (sa_ctrl_cg0 == 1'b1)
      begin
      sa_is_predicted_r     <= da_is_predicted_r & da_pass;
      sa_prediction_r       <= da_prediction_r;
      sa_prediction_type_r  <= da_prediction_type_r;
      sa_error_branch_r     <= da_error_branch_r & da_pass & (~fch_restart);
      sa_with_dslot_r       <= da_with_dslot_r;
      sa_in_dslot_r         <= da_in_dslot_r     & da_pass;
      sa_orphan_dslot_r     <= da_orphan_dslot_r & da_pass;
      sa_eslot_mpd_r        <= sa_eslot_mpd_nxt;
      sa_is_eslot_r         <= da_is_eslot       & da_pass;
      sa_pg_xing_dslot_r    <= sa_pg_xing_replay & da_pass;
      end

    if (x1_ctrl_cg0 == 1'b1)
      begin
      x1_is_predicted_r     <= sa_is_predicted_r & sa_pass;
      x1_prediction_r       <= sa_prediction_r;
      x1_prediction_type_r  <= sa_prediction_type_r;
      x1_error_branch_r     <= sa_error_branch   & sa_pass;
      x1_with_dslot_r       <= sa_with_dslot_r;
      x1_in_dslot_r         <= sa_in_dslot_r     & sa_pass;
      x1_br_type_r          <= sa_br_type;
      x1_commit_size_r      <= sa_commit_size;
      x1_secondary_r        <= sa_secondary;
      x1_predictable_r      <= sa_predictable;
      x1_uop_predictable_r  <= sa_uop_predictable_r;
      x1_orphan_dslot_r     <= sa_orphan_dslot_r & sa_pass;
      x1_pc_r               <= sa_pc;
      x1_eslot_mpd_r        <= sa_eslot_mpd_r    & sa_pass;
      x1_is_eslot_r         <= sa_is_eslot_r     & sa_pass;
      x1_pg_xing_replay_r   <= sa_pg_xing_replay  & sa_pass;
      x1_pg_xing_dslot_r    <= sa_pg_xing_dslot_r & sa_pass;
      end

    if (x2_ctrl_cg0 == 1'b1)
      begin
      x2_is_predicted_r     <= x1_is_predicted_r & x1_pass;
      x2_prediction_r       <= x1_prediction_r;
      x2_prediction_type_r  <= x1_prediction_type_r;
      x2_error_branch_r     <= x1_error_branch   & x1_pass; 
      x2_fragged_r          <= x1_error_branch;  
      x2_with_dslot_r       <= x1_with_dslot_r;
      x2_in_dslot_r         <= x1_in_dslot_r     & x1_pass;
      x2_br_type_r          <= x1_br_type_r;
      x2_commit_size_r      <= x1_commit_size_r;
      x2_secondary_r        <= x1_secondary_r;
      x2_br_outcome_r       <= x1_direction;
      x2_br_resolved_r      <= x2_br_resolved_nxt;
      x2_late_pred_r        <= x2_late_pred_nxt;
      x2_predictable_r      <= x1_predictable_r;
      x2_orphan_dslot_r     <= x1_orphan_dslot_r & x1_pass;
      x2_eslot_mpd_r        <= x1_eslot_mpd_r    & x1_pass;
      // BTA misprediction for BI/BI_H:
      // BI and BI_H wait for valid operands in SA.
      // BTA mispredict for BI and BI_H is
      // calculated in X1.
      // If the resolve of the BI is postponed till CA,
      // then that mispredict result is pipelined downstream
      // and used in CA.
      x2_bi_bta_mpd_r       <= x1_bi_bta_mpd & x1_pass;
      x2_pg_xing_replay_r   <= x1_pg_xing_replay_r & x1_pass;
      x2_pg_xing_dslot_r    <= x1_pg_xing_dslot_r  & x1_pass;
      end

    if (x3_ctrl_cg0 == 1'b1)
      begin
      x3_is_predicted_r     <= x2_is_predicted_r & x2_pass;
      x3_prediction_r       <= x2_prediction_r;
      x3_prediction_type_r  <= x2_prediction_type_r;
      x3_error_branch_r     <= x2_error_branch_r & x2_pass;
      x3_late_pred_r        <= x2_late_pred_r    & x2_pass;
      x3_fragged_r          <= x2_fragged_r      & x2_pass;
      x3_with_dslot_r       <= x2_with_dslot_r;
      x3_in_dslot_r         <= x2_in_dslot_r     & x2_pass;
      x3_br_type_r          <= x2_br_type_r;
      x3_commit_size_r      <= x2_commit_size_r;
      x3_secondary_r        <= x2_secondary_r;
      x3_br_outcome_r       <= x2_br_outcome_r;
      x3_br_resolved_r      <= x2_br_resolved_r;
      x3_predictable_r      <= x2_predictable_r;
      x3_orphan_dslot_r     <= x2_orphan_dslot_r & x2_pass;
      x3_eslot_mpd_r        <= x2_eslot_mpd_r    & x2_pass;
      x3_bi_bta_mpd_r       <= x2_bi_bta_mpd_r & x2_pass;
      x3_early_mispred_outcome_r <= mpd_early & mpd_mispred_outcome;
      x3_early_mispred_bta_r <= mpd_early & mpd_mispred_bta;
      x3_pg_xing_replay_r   <= x2_pg_xing_replay_r & x2_pass;
      end

    if (ca_ctrl_cg0 == 1'b1)
      begin
      ca_is_predicted_r     <= x3_is_predicted_r & x3_pass;
      ca_prediction_r       <= x3_prediction_r;
      ca_prediction_type_r  <= x3_prediction_type_r;
      ca_error_branch_r     <= x3_error_branch_r & x3_pass;
      ca_fragged_r          <= x3_fragged_r      & x3_pass;
      ca_with_dslot_r       <= x3_with_dslot_r;
      ca_in_dslot_r         <= x3_in_dslot_r     & x3_pass;
      ca_br_type_r          <= x3_br_type_r;
      ca_commit_size_r      <= x3_commit_size_r;
      ca_secondary_r        <= x3_secondary_r;
      ca_br_outcome_r       <= x3_br_outcome_r;
      ca_br_resolved_r      <= x3_br_resolved_r;
      ca_predictable_r      <= x3_predictable_r;
      ca_orphan_dslot_r     <= x3_orphan_dslot_r & x3_pass;
//      ca_eslot_mpd_r        <= x3_eslot_mpd_r    & x3_pass;
      ca_bi_bta_mpd_r       <= x3_bi_bta_mpd_r & x3_pass;
      ca_early_mispred_outcome_r <= x3_early_mispred_outcome_r;
      ca_early_mispred_bta_r <= x3_early_mispred_bta_r;
      ca_pg_xing_replay_r   <= x3_pg_xing_replay_r & x3_pass;
      end
    end

end // block: pred_ctrl_regs_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define state updates to prediction-data pipeline  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : pred_data_regs_PROC

  if (rst_a == 1'b1)
    begin
    da_pred_bta_r         <= `npuarc_PC_BITS'd0;
    da_branch_info_r      <= `npuarc_BR_INFO_SIZE'b0;
    sa_pred_bta_r         <= `npuarc_PC_BITS'd0;
    sa_branch_info_r      <= `npuarc_BR_INFO_SIZE'b0;
    x1_pred_bta_r         <= `npuarc_PC_BITS'd0;
    x1_branch_info_r      <= `npuarc_BR_INFO_SIZE'b0;
    x2_pred_bta_r         <= `npuarc_PC_BITS'd0;
    x2_branch_info_r      <= `npuarc_BR_INFO_SIZE'b0;
    x3_pred_bta_r         <= `npuarc_PC_BITS'd0;
    x3_branch_info_r      <= `npuarc_BR_INFO_SIZE'b0;
    ca_pred_bta_r         <= `npuarc_PC_BITS'd0;
    ca_branch_info_r      <= `npuarc_BR_INFO_SIZE'b0;
    end
  else
    begin
    if (da_info_cg0 == 1'b1)
      begin
      da_branch_info_r      <= al_branch_info;
      end

    if (da_pred_cg0 == 1'b1)
      begin
      da_pred_bta_r         <= al_predicted_bta;
      end

    if (sa_info_cg0 == 1'b1)
      begin
      sa_branch_info_r      <= da_branch_info_r;
      end

    if (sa_pred_cg0 == 1'b1)
      begin
      sa_pred_bta_r         <= sa_pred_bta_nxt;
      end

    if (x1_info_cg0 == 1'b1)
      begin
      x1_branch_info_r      <= sa_branch_info_r;
      end

    if (x1_pred_cg0 == 1'b1)
      begin
      x1_pred_bta_r         <= sa_pred_bta_r;
      end

    if (x2_info_cg0 == 1'b1)
      begin
      x2_branch_info_r      <= x1_branch_info_r;
      end

    if (x2_pred_cg0 == 1'b1)
      begin
      x2_pred_bta_r         <= x1_pred_bta_r;
      end

    if (x3_info_cg0 == 1'b1)
      begin
      x3_branch_info_r      <= x2_branch_info_r;
      end

     if (x3_pred_cg0 == 1'b1)
      begin
      x3_pred_bta_r         <= x2_pred_bta_r;
      end

   if (ca_info_cg0 == 1'b1)
      begin
      ca_branch_info_r      <= x3_branch_info_r;
      end

   if (ca_pred_cg0 == 1'b1)
      begin
      ca_pred_bta_r         <= x3_pred_bta_r;
      end

    end
end // block: pred_data_regs_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define early (X2) misprediction restart registers //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : x2_mpd_regs_PROC

  if (rst_a == 1'b1)
    begin
    x2_restart_r          <= 1'b0;
    x2_restart_pc_r       <= `npuarc_PC_BITS'd0;
    x2_mispred_r          <= 1'b0;
    end
  else if (x2_mpd_cg0 == 1'b1)
    begin
    x2_restart_r          <= x2_restart_nxt;
    x2_restart_pc_r       <= x1_restart_pc;
    x2_mispred_r          <= x1_mispredict;
    end

end // block: x2_mpd_regs_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define misprediction interface data registers     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : mpd_data_regs_PROC

  if (rst_a == 1'b1)
    begin
    mpd_mispred_r         <= 1'b0;
    mpd_direction_r       <= 1'b0;
    mpd_error_branch_r    <= 1'b0;
    mpd_is_predicted_r    <= 1'b0;
    mpd_mispred_outcome_r <= 1'b0;
    mpd_mispred_bta_r     <= 1'b0;
    mpd_branch_info_r     <= `npuarc_BR_INFO_SIZE'd0;
    mpd_dslot_r           <= 1'b0;
    mpd_type_r            <= `npuarc_BR_TYPE_BITS'd0;
    mpd_seq_next_pc_r     <= `npuarc_PC_BITS'd0;
    mpd_pc_r              <= `npuarc_PC_BITS'b0;
    mpd_early_r           <= 1'b0;
    mpd_tail_pc_3_r       <= 1'b0;
    mpd_commit_size_r     <= 2'd0;
    mpd_secondary_r       <= 1'b0;
    end
  else if (mpd_data_cg0 == 1'b1)
    begin
    mpd_mispred_r         <= mpd_mispred_nxt 
                           & (~ca_restart_without_mispredict) 
                           & (~ar_aux_debug_r[`npuarc_DEBUG_IS])
                           ;
    mpd_direction_r       <= mpd_direction_nxt;
    mpd_error_branch_r    <= mpd_error_branch_nxt;
    mpd_is_predicted_r    <= mpd_is_predicted_nxt;
    mpd_mispred_outcome_r <= mpd_mispred_outcome_nxt;
    mpd_mispred_bta_r     <= mpd_mispred_bta_nxt;
    mpd_branch_info_r     <= mpd_branch_info_nxt;
    mpd_dslot_r           <= mpd_dslot_nxt;
    mpd_type_r            <= mpd_type_nxt;
    mpd_seq_next_pc_r     <= mpd_seq_next_pc_nxt;
    mpd_pc_r              <= mpd_pc_nxt;
    mpd_early_r           <= mpd_early_nxt;
    mpd_tail_pc_3_r       <= mpd_tail_pc_3_nxt;
    mpd_commit_size_r     <= mpd_commit_size_nxt;
    mpd_secondary_r       <= mpd_secondary_nxt;
    end

end // block: mpd_data_regs_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define branch-commit data signal registers        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : brc_data_regs_PROC

  if (rst_a == 1'b1)
    begin
    wa_br_type_r          <= `npuarc_BR_TYPE_BITS'd0;
    wa_is_predicted_r     <= 1'b0;
    wa_target_r           <= `npuarc_PC_BITS'd0;
    wa_direction_r        <= 1'b0;
    wa_mispred_outcome_r  <= 1'b0;
    wa_mispred_bta_r      <= 1'b0;
    wa_secondary_r        <= 1'b0;
    end
  else if (brc_data_cg0 == 1'b1) 
    begin
    wa_br_type_r          <= ca_type;
    wa_is_predicted_r     <= ca_is_predicted_r | (x2_pg_xing_dslot_r & mpd_is_predicted_r);
    wa_target_r           <= ca_target;
    wa_direction_r        <= wa_direction_nxt;

    // Mispredict signals also need to be asserted for early mispredict.
    // That is achieved by remembering early mispredict in the pipeline with
    // ca_early_mispred_outcome_r and ca_early_mispred_bta_r.
    //
    wa_mispred_outcome_r  <= wa_mispred_outcome_nxt;
    wa_mispred_bta_r      <= wa_mispred_bta_nxt;
    wa_secondary_r        <= ca_secondary_r;
    end

end // brc_data_regs_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define branch-commit control signal registers     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
// Notes:
// 1. wa_dslot needs to be 0 for predicted uop instructions, i.e. LEAVE_S,
//   even when the uop seq contains a jump with delay slot.
//   With the current code it works out that way.
// 2. Logic in module alb_writeback makes sure that wa_pc and wa_pc_tail_3
//   are correct for the commit of a uop sequence.
//
// spyglass disable_block FlopEConst
// SMD: Enable pin is always high/low 
// SJ:  Done on purpose

always @(posedge clk or posedge rst_a)
begin : wa_ctrl_regs_PROC

  if (rst_a == 1'b1)
    begin
    wa_pass_r             <= 1'b0;
    wa_restart_r          <= 1'b0;
    wa_restart_kill_r     <= 1'b0;
    wa_stop_r             <= 1'b0;
    wa_pending_r          <= 1'b0;
    wa_iprot_replay_r     <= 1'b0;
    end
  else if (wa_enable == 1'b1) 
    begin
    wa_pass_r             <= wa_pass_nxt;
    wa_restart_r          <= ca_restart | ca_stop; 
    wa_restart_kill_r     <= ca_restart_kill_ca;
    wa_stop_r             <= ca_stop;
    wa_pending_r          <= wa_pending_nxt;
    wa_iprot_replay_r     <= ca_iprot_replay;
    end

end // wa_ctrl_regs_PROC
// spyglass enable_block FlopEConst
always @(posedge clk or posedge rst_a)
begin : br_commit_regs_PROC

  if (rst_a == 1'b1)
    begin
    wa_restart_pc_r       <= `npuarc_PC_BITS'd`npuarc_RESET_PC;
    wa_error_branch_r     <= 1'b0;
    wa_mispred_r          <= 1'b0;
    wa_commit_size_r      <= 2'd0;
    wa_branch_info_r      <= `npuarc_BR_INFO_SIZE'b0;
    end
  else if (brc_ctrl_cg0 == 1'b1) 
    begin
    // update wa_branch_info in sync with wa_pass
    // For every instruction committed as indicated by wa_pass
    // the corresponding wa_branch_info is provided.
    // If wa_pass is low for a restart without mispredict
    // then wa_branch_info remains frozen and indicates
    // the info of the last instruction committed.
    //
    if (wa_pass_nxt)
      wa_branch_info_r    <= x2_pg_xing_dslot_r
                           ? x2_branch_info_r
                           : ca_branch_info_r
                           ;

    wa_restart_pc_r       <= wa_restart_pc_nxt;
    
    wa_error_branch_r     <= (   ca_error_branch_r
                               | ca_detect_err_br
                               | x2_pg_xing_dslot_r
                             )
                           & (~wa_restart_r) & (~ca_flush)
                           ;
    
    wa_mispred_r          <= (ca_mispredict & (~ca_flush))
                           | (x2_pg_xing_dslot_r & mpd_mispred_r)
                           ;

    // If a predicted micro-op sequence is committed, it must be a LEAVE_S
    // and therefore wa_commit_size must be 16 bits (encoded as 0).
    // Otherwise wa_commit_size would be incorrectly set to the size of
    // the uop jump instruction.
    //
    wa_commit_size_r      <= ca_uop_predictable_r ? 2'd0 : ca_commit_size_r;   
    end

end // br_commit_regs_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Assignment of output wires                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign mpd_mispred            = mpd_mispred_r;
assign mpd_is_predicted       = mpd_is_predicted_r;
assign mpd_branch_info        = mpd_branch_info_r;
assign mpd_direction          = mpd_direction_r;
assign mpd_error_branch       = mpd_error_branch_r;
assign mpd_mispred_outcome    = mpd_mispred_outcome_r;
assign mpd_mispred_bta        = mpd_mispred_bta_r;
assign mpd_dslot              = mpd_dslot_r;
assign mpd_seq_next_pc        = mpd_seq_next_pc_r;
assign mpd_type               = mpd_type_r;

assign mpd_pc                 = mpd_pc_r;
assign mpd_early              = mpd_early_r;

assign mpd_tail_pc_3          = mpd_tail_pc_3_r;
assign mpd_commit_size        = mpd_commit_size_r;
assign mpd_secondary          = mpd_secondary_r;

assign wa_pass                = wa_pass_r;
assign wa_type                = wa_br_type_r;
assign wa_commit_size         = wa_commit_size_r;
assign wa_secondary           = wa_secondary_r;
assign wa_is_predicted        = wa_is_predicted_r;
assign wa_target              = wa_target_r;
assign wa_direction           = wa_direction_r;
assign wa_error_branch        = wa_error_branch_r;
assign wa_mispred_outcome     = wa_mispred_outcome_r;
assign wa_commit_mispred_bta  = wa_mispred_bta_r;
assign wa_branch_info         = wa_branch_info_r;

endmodule
