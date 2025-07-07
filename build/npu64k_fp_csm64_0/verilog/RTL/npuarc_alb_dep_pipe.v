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
//  #####   ######  #####           #####      #    #####   ######
//  #    #  #       #    #          #    #     #    #    #  #
//  #    #  #####   #    #          #    #     #    #    #  #####
//  #    #  #       #####           #####      #    #####   #
//  #    #  #       #               #          #    #       #
//  #####   ######  #      #######  #          #    #       ######
//
// ===========================================================================
// @f:opd_sel:
// Description:
// @p
//  The alb_dep_pipe module detects dependencies between the instruction at
//  the Decode stage and all pre-commit instructions in downstream stages
//  of the pipeline. It also tracks the evolution of those dependencies as
//  instructions progress through the pipeline. It provides outputs to the
//  datapath for each stage of the pipeline to allow them to select correct
//  forwarding values and to assert stalls as required.
// @e
// ===========================================================================


// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants.
//
`include "npuarc_ucode_const.v"

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pipeline registers holding dependency information                        //
//                                                                          //
// This module implements a dependency-checking pipeline, with one stage    //
// for each pipeline stage from Operand-select through to Commit.           //
// Each pipeline stage contains a 4-bit vector to represent the potential   //
// dependencies between lo/hi registers at source and destination.          //
//                                                                          //
// The four tracked dependencies, and the indices into the vector in which  //
// they are registered, are:                                                //
//                                                                          //
// 0  source register 0 depends on write port 0, vector index is `R0_W0     //
// 1  source register 0 depends on write port 1, vector index is `R0_W1     //
// 2. source register 1 depends on write port 0, vector index is `R1_W0     //
// 3. source register 1 depends on write port 1, vector index is `R1_W1     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dep_pipe (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,              // clock signal
  input                       rst_a,            // reset signal

  ////////// Control inputs from the Dispatch Pipeline ///////////////////////
  //
  // -------------------------------------------------------------------------
  input                       da_valid_r /* verilator public_flat */,       // valid insn at Decode stage
  input                       da_uop_busy_r,    // uop-seq is active
  input                       da_uop_is_excpn_r,// 'da' ins is for excpn (uop)
  input                       da_uop_prol_r,    // 'da' ins is uop prol
  input                       da_uop_is_sirq_r, // 'da' ins is for sirq (uop)
  input                       int_load_active,  // to stall DA non-prologue/epilogue instruction
  input                       da_rtie_op_r,
  input                       int_in_prologue,
  input                       da_eslot_stall,   // RAW hazard stall on BTA
  input                       da_ei_op,         // DA insn is an EI_S
  input                       da_ldi_src0,      // LDI insn at DA
  input                       da_jli_src0,      // LDI insn at DA
  input [`npuarc_ZNCV_RANGE]         da_zncv_wen,      //

  input                       da_rtt_stall_r,
  output reg                  sa_stall_r1  ,    //
  output                      sa_flag_stall,    //
  output reg                  sa_stall_r15,

  output reg                  sa_acc_raw   ,    //
  output reg                  ca_acc_waw   ,    //
  //
  // -------------------------------------------------------------------------
  input                       sa_valid_nxt,     // valid insn to Operand stage
  //     Operand-stage ucode
  input                       sa_opds_in_sa_r,  // insn requires opds at SA
  input                       sa_agu_uses_r0_r, // AGU uses reg0 as source
  input                       sa_agu_uses_r1_r, // AGU uses reg1 as source
  input                       sa_dslot_r,       // insn has a delay slot
  input                       sa_link_r,        // insn updates link reg
  input                       sa_store_r,       // ST insn at SA
  input                       sa_load_r,        // LD insn at SA
  input                       sa_dmb_op_r,      // DMB insn at SA
  input [2:0]                 sa_dmb_type_r,    // DMB type operand at SA
  input                       sa_dsync_op_r,    // DSYNC operand at SA
  output reg                  sa_dmb_stall,     // SA stall due to DMB
  input                       sa_ei_op_r,       // SA insn is an EI_S
  input                       sa_sr_op_r,       // SR insn at SA
  input                       sa_ldi_src0_r,    // LDI insn at SA
  input                       sa_jli_src0_r,    // LDI insn at SA
  input [`npuarc_ZNCV_RANGE]         sa_zncv_wen_r,    // ZNCV flag write-enable
  input [4:0]                 sa_q_field_r,     //
  input                       sa_with_carry_r,  // implicit use of Carry flag
  input                       sa_reads_acc_r,   // explicit ACC read at SA
  output reg                  sa_flags_ready,   // to EIA
  input                       sa_eia_hazard,    //
  input                       ca_dest_cr_is_ext_r,//
  output                      gb_dest_cr_is_ext,// to eia dep pipe
  input                       sa_eia_hold,      // blocking instr ahead
  input                       x2_eia_hold,      // src64 blocking in x2
  output reg                  ar0_rf_valid_r,
  output reg                  ar0_rf_wenb1_r,
  output reg [`npuarc_GRAD_ADDR_RANGE]   ar0_rf_wa1_r,
  output reg                  ar0_rf_wenb1_64_r,
  output reg                  ar0_dest_cr_is_ext,
  output reg                  ar1_rf_valid_r,
  output reg                  ar1_rf_wenb1_r,
  output reg [`npuarc_GRAD_ADDR_RANGE]   ar1_rf_wa1_r,
  output reg                  ar1_rf_wenb1_64_r,
  output reg                  ar1_dest_cr_is_ext,
  output reg                  ar2_rf_valid_r,
  output reg                  ar2_rf_wenb1_r,
  output reg [`npuarc_GRAD_ADDR_RANGE]   ar2_rf_wa1_r,
  output reg                  ar2_rf_wenb1_64_r,
  output reg                  ar2_dest_cr_is_ext,
  output reg                  ar3_rf_valid_r,
  output reg                  ar3_rf_wenb1_r,
  output reg [`npuarc_GRAD_ADDR_RANGE]   ar3_rf_wa1_r,
  output reg                  ar3_rf_wenb1_64_r,
  output reg                  ar3_dest_cr_is_ext,
  output reg                  ar4_rf_valid_r,
  output reg                  ar4_rf_wenb1_r,
  output reg [`npuarc_GRAD_ADDR_RANGE]   ar4_rf_wa1_r,
  output reg                  ar4_rf_wenb1_64_r,
  output reg                  ar4_dest_cr_is_ext,
  output reg                  ar5_rf_valid_r,
  output reg                  ar5_rf_wenb1_r,
  output reg [`npuarc_GRAD_ADDR_RANGE]   ar5_rf_wa1_r,
  output reg                  ar5_rf_wenb1_64_r,
  output reg                  ar5_dest_cr_is_ext,
  output reg                  ar6_rf_valid_r,
  output reg                  ar6_rf_wenb1_r,
  output reg [`npuarc_GRAD_ADDR_RANGE]   ar6_rf_wa1_r,
  output reg                  ar6_rf_wenb1_64_r,
  output reg                  ar6_dest_cr_is_ext,
  output reg                  ar7_rf_valid_r,
  output reg                  ar7_rf_wenb1_r,
  output reg [`npuarc_GRAD_ADDR_RANGE]   ar7_rf_wa1_r,
  output reg                  ar7_rf_wenb1_64_r,
  output reg                  ar7_dest_cr_is_ext,

  ////////// Dependency inputs from the Auxiliary Control Pipeline ///////////
  //
  input                       aux_x2_r4_sr,     // core region 4 SR at X2
  input                       aux_x3_r4_sr_r,   // core region 4 SR at X3
  input                       aux_ca_r4_sr_r,   // core region 4 SR at CA

  ////////// Control inputs from the Execute Pipeline ////////////////////////
  //
  // -------------------------------------------------------------------------
  input                       sa_is_predicted_r, // SA is predicted branch
  input                       sa_with_dslot_r,   // SA has predicted delay slot
  input                       sa_error_branch_r, // SA is fragged error branch
  input                       sa_zol_stall,     // stall at SA due to ZOL
  input                       x1_zol_stall,     // stall at X1 due to ZOL
  input                       x1_valid_nxt,     // valid insn to Exec1 stage
  //      Exec1-stage ucode
  input                       x1_load_r,        // insn at Exec1 is a Load
  input                       x1_store_r,       // insn at Exec1 is a Store
  input                       x1_fast_op_r,     // insn at Exec1 takes 1-cycle
  input                       x1_eia_op_r,      // eia insn at X1
  input                       ca_eia_op_r,      // eia insn at CA
  input                       x1_eia_fast_op_r, // eia insn at X1 is done
  input                       x1_eia_hold,      // multi-cycle blocking in x1
  input                       x1_slow_op_r,     // insn at Exec1 takes 1-cycle
  input     [`npuarc_ZNCV_RANGE]     x1_zncv_wen_r,    // insn at Exec1 ZNCV wen
  input                       x1_flag_op_r,     // insn at Exec1 is [k]flag
  input                       x1_brk_op_r,      // insn at Exec1 is brk
  input                       x1_sleep_op_r,    // insn at Exec1 is sleep
  input                       x1_cond,          // insn at Exec1 will eval.
  input     [4:0]             x1_q_field_r,     // insn at Exec1 q-field
  input                       x1_signed_op_r,   // insn at Exec1 is signed
  input                       x1_opds_in_sa_r,  // requires opds in SA at latest
  input                       x1_opds_in_x1_r,  // requires opds in X1 at latest
  input                       x1_agu_uses_r0_r, // AGU uses reg0 as source
  input                       x1_sr_op_r,       // SR insn at Exec1
  input                       x1_uop_commit_r,  // insn is terminal of uop-seq
  input                       x1_uop_prol_r,    // insn is terminal of prologue
  input                       x1_uop_epil_r,    // insn is terminal of epilogue
  input                       x1_with_carry_r,  // insn at X1 uses carry flag
  input                       x1_grab_src0,     // grab a WA bypass for src0
  input                       x1_grab_src1,     // grab a WA bypass for src1
  input                       x1_grab_src2,     // grab a WA bypass for src0
  input                       x1_grab_src3,     // grab a WA bypass for src1
  input                       x1_rgf_link_r,
  input                       x1_dmb_op_r,      // DMB insn at X1
  input     [2:0]             x1_dmb_type_r,    // DMB operand type at X1
  input                       x1_div_op_r,      // DIV or REM insn at X1
  input                       div_busy_r,       // Divider is busy
  //
  // -------------------------------------------------------------------------
  input                       x2_valid_nxt,     // valid insn to Exec2 stage
  //      Exec2-stage ZNCV state
  input     [`npuarc_ZNCV_RANGE]     x2_zncv_wen_r,    // insn at Exec2 ZNCV wen
  input                       x2_wevt_op,       // inst at Exec2 wevt
  input                       x2_brk_op_r,      // inst at Exec2 brk
  //      Exec2-stage ucode
  input                       x2_slow_op_r,     // insn at Exec2 takes 1-cycle
  input                       x2_flag_op_r,     // insn at Exec2 is flag
// leda NTL_CON13C off
// LMD: non driving bits 0-3
// LJ:  unused 4 bits of a 5-bit port
  input     [4:0]             x2_q_field_r,     // insn at Exec2 q-field
// leda NTL_CON13C on
  input                       x2_signed_op_r,   // insn at Exec2 is signed
  input                       x2_dslot_r,       // insn at Exec2 has delay slot
  input                       x2_sync_op_r,     // SYNC insn at X2
  input                       x2_load_r,        //
  input                       x2_store_r,       //
  input                       x2_excpn_stall,   // stall Exec2 on poss. excpn
  input                       x2_sc_stall,      // stall Exec2 on poss. SC
  output reg                  dp_x2_sp_r,       // SP dependency exists
  input                       x2_locked_r,      // LLOCK/SCOND at X2
  input                       x2_dmb_op_r,      // DMB insn at X2
  input     [2:0]             x2_dmb_type_r,    // DMB operand type at X2
  input                       x2_sr_op_r,       // SR insn at X2
  input                       x2_pg_xing_replay_r,

  output reg                  x2_exu_stall,     // EXU x2 stall
  //
  // -------------------------------------------------------------------------
  //
  input                       dmp_dc3_stall_r,
  input                       x3_valid_nxt,     // valid insn to Exec3 stage
  //      Exec3-stage ucode
  input     [`npuarc_ZNCV_RANGE]     x3_zncv_wen_r,    // insn at Exec3 ZNCV wen
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused x3 stage interface
  input                       x3_flag_op_r,     // insn at Exec3 is flag
  input     [4:0]             x3_q_field_r,     // insn at Exec3 q-field
  input                       x3_signed_op_r,   // insn at Exec3 is signed
// leda NTL_CON13C on
  input                       x3_sync_op_r,     // SYNC insn at X3
  input                       x3_trap_op_r,     // TRAP insn at X3
  input                       x3_brk_op_r,      // BRK insn at X3
  input                       x3_rtie_op_r,     // RTIE insn at X3
  input                       aux_x3_stall,     // RAW hazard from SR to LR
  input                       wdt_x3_stall,
  input                       x3_locked_r,      // LLOCK/SCOND at X3
  input                       x3_store_r,       // Store at X3 (e.g. SCOND)
  input                       x3_vector_op_r,   // SIMD operation at X3
  input                       x3_macu_r,        // MACU-bypassable op at X3
  input                       x3_dmb_op_r,      // DMB insn at X3
  input     [2:0]             x3_dmb_type_r,    // DMB operand type at X3
  input                       x3_load_r,        // Load insn at X3
  input                       x3_sr_op_r,       // SR insn at X3
  input                       x3_wevt_op,       // WEVT insn at X3
  //
  // -------------------------------------------------------------------------
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused ca stage interface
  input                       ca_valid_nxt,     // valid insn to Commit stage
  input                       ca_q_cond,        // predicate evaluated at CA
  //      Commit-stage ucode
  input                       ca_fast_op_r,     // insn at Commit takes 1-cycle
  input                       ca_load_r,        // insn at Commit is a Load
  input     [`npuarc_ADDR_RANGE]     ca_mem_addr_r,    // VA for graduating loads
  input                       ca_store_r,       // insn at Commit is a Store
  input     [`npuarc_ZNCV_RANGE]     ca_zncv_wen_r,    // insn at Commit ZNCV wen
  input                       ca_normal_evt,


  input                       ca_predicate_r,   // CA-stage insn predicate
  input                       ca_rtie_op_r,     // RTIE insn at CA
  input                       ca_div_op_r,      // DIV or REM insn at CA
//  input                       ca_sync_op_r,     // SYNC insn at CA
  input                       ca_mpy_op_r,      // MPY operation at CA
  input                       ca_vector_op_r,   // SIMD operation at CA
  input                       ca_macu_r,        // MACU-bypassable op at CA
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input     [4:0]             ca_q_field_r,     // CA instruction conditional
// spyglass enable_block W240
  input                       ca_with_carry_r,  // CA insn uses C-flag implicitly
  input                       ca_sr_op_r,       // SR insn at CA
  input                       ca_dmb_op_r,      // DMB insn at CA
  input     [2:0]             ca_dmb_type_r,    // DMB sub-type operand at CA
  input                       ca_sr_stall_rtie,
  input                       ca_pg_xing_replay_r,
// leda NTL_CON13C on
  //
  // -------------------------------------------------------------------------
  input                       wa_valid_nxt,     // valid insn to Writeback stage
  input                       wa_cmt_flag_evt_r,//
  input                       wa_store_r,       // ST instruction in Writeback
  input                       wa_load_r,        // Load insn at WA
  input                       wa_sr_op_r,       // SR insn at WA
  input                       wa_rf_wenb0_64_nxt,
  //
  ////////// Source register information from Decode stage ///////////////////
  //
  input     [`npuarc_RGF_ADDR_RANGE] da_rf_ra0_r,      // reg0 address at Decode
  input                       da_rf_renb0_r,    // reg0 at Decode is enabled
  input                       da_rf_renb0_64_r, // enable 64-bit read on reg0
  //
  input     [`npuarc_RGF_ADDR_RANGE] da_rf_ra1_r,      // reg1 address at Decode
  input                       da_rf_renb1_r,    // reg1 at Decode is enabled
  input                       da_rf_renb1_64_r, // enable 64-bit read on reg1
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  register information from downstream stages
  ////////// Source register information from downstream stages //////////////
  // (currently only use bit 0 from these register read address vectors)
  //
// leda NTL_CON37 off
// LMD: Signal/Net must read from the input port
// LJ:  subset of bits from input vectors are used
  input     [`npuarc_RGF_ADDR_RANGE] sa_rf_ra0_r,      // reg0 address at Operands
  input     [`npuarc_RGF_ADDR_RANGE] sa_rf_ra1_r,      // reg1 address at Operands
  input     [`npuarc_RGF_ADDR_RANGE] x1_rf_ra0_r,      // reg0 address at Exec1
  input     [`npuarc_RGF_ADDR_RANGE] x1_rf_ra1_r,      // reg1 address at Exec1
  input     [`npuarc_RGF_ADDR_RANGE] x2_rf_ra0_r,      // reg0 address at Exec2
  input     [`npuarc_RGF_ADDR_RANGE] x2_rf_ra1_r,      // reg1 address at Exec2
  input     [`npuarc_RGF_ADDR_RANGE] x3_rf_ra0_r,      // reg0 address at Exec3
  input     [`npuarc_RGF_ADDR_RANGE] x3_rf_ra1_r,      // reg1 address at Exec3
  input     [`npuarc_RGF_ADDR_RANGE] ca_rf_ra0_r,      // reg0 address at Commit
  input     [`npuarc_RGF_ADDR_RANGE] ca_rf_ra1_r,      // reg1 address at Commit
// leda NTL_CON37 on


  ////////// Destination register information from downstream stages /////////
  //
// leda NTL_CON13C on
  input                       sa_rf_renb0_64_r, // reg0+1 at Opd_Sel is read
  input     [`npuarc_RGF_ADDR_RANGE] sa_rf_wa0_r,      // reg0 address at Opd_Sel
  input                       sa_rf_wenb0_r,    // reg0 at Opd_Sel is written
  input                       sa_rf_wenb0_64_r, // enable 64-bit write 0
  //

  input                       sa_rf_renb1_64_r, // reg1+1 at Opd_Sel is read
  input     [`npuarc_RGF_ADDR_RANGE] sa_rf_wa1_r,      // reg1 address at Opd_Sel
  input                       sa_rf_wenb1_r,    // reg1 at Opd_Sel is enabled
  input                       sa_rf_wenb1_64_r, // enable 64-bit write 1
  // ------------------------------------------------------------------------
  input     [`npuarc_RGF_ADDR_RANGE] x1_rf_wa0_r,      // reg0 address at Exec1
  input                       x1_rf_wenb0_r,    // reg0 at Exec1 is enabled
  input                       x1_rf_wenb0_64_r, // enable 64-bit write 0
  //
  input     [`npuarc_RGF_ADDR_RANGE] x1_rf_wa1_r,      // reg1 address at Exec1
  input                       x1_rf_wenb1_r,    // reg1 at Exec1 is enabled
  input                       x1_rf_wenb1_64_r, // enable 64-bit write 1
  input                       x1_acc_wenb_r,    // X1 has implicit ACC write
  //
  input                       dc1_stall,        // DMP stalls at Exec1/DC1
  // --------------------------------------------------------------------------
  input     [`npuarc_RGF_ADDR_RANGE] x2_rf_wa0_r,      // reg0 address at Exec2
  input                       x2_rf_wenb0_r,    // reg0 at Exec2 is enabled
  input                       x2_rf_wenb0_64_r, // enable 64-bit write 0
  //
  input     [`npuarc_RGF_ADDR_RANGE] x2_rf_wa1_r,      // reg1 address at Exec2
  input                       x2_rf_wenb1_r,    // reg1 at Exec2 is enabled
  input                       x2_rf_wenb1_64_r, // enable 64-bit write 1
  input                       x2_acc_wenb_r,    // X2 has implicit ACC write
  input                       dc2_stall,        // DMP stalls at X2/DC2
  // -------------------------------------------------------------------------
  input     [`npuarc_RGF_ADDR_RANGE] x3_rf_wa0_r,      // reg0 address at Exec3
  input                       x3_rf_wenb0_r,    // reg0 at Exec3 is enabled
  input                       x3_rf_wenb0_64_r, // enable 64-bit write 0
  //
  input     [`npuarc_RGF_ADDR_RANGE] x3_rf_wa1_r,      // reg1 address at Exec3
  input                       x3_rf_wenb1_r,    // reg1 at Exec3 is enabled
  input                       x3_rf_wenb1_64_r, // enable 64-bit write 1
  input                       x3_acc_op_r,      // X3 implicitly reads ACC
  input                       x3_acc_wenb_r,    // X3 has implicit ACC write
  input                       dmp_dc3_fast_byp, // x3/dc3 fast load indicator
  // -------------------------------------------------------------------------
  input     [`npuarc_RGF_ADDR_RANGE] ca_rf_wa0_r,      // reg0 address at Commit
  input                       ca_rf_wenb0_r,    // reg0 at Commit is enabled
  input                       ca_rf_wenb0_64_r, // enable 64-bit write 0
  //
  input     [`npuarc_RGF_ADDR_RANGE] ca_rf_wa1_r,      // reg1 address at Commit
  input                       ca_rf_wenb1_r,    // reg1 at Commit is enabled
  input                       ca_rf_wenb1_64_r, // enable 64-bit write 1
  input                       ca_writes_acc_r,  // CA has explicit ACC write
  input                       ca_acc_wenb_r,    // CA has implicit ACC write
  input                       ca_locked_r,      // LLOCK or SCOND is at CA
  input                       ca_wlfc_op,       // WLFC insn at CA
  input                       dmp_dc4_fast_byp_r,// ca/dc4 fast load indicator
  input                       dmp_dc4_fast_miss_r,// ca/dc4 fast load miss
  input                       dmp_aux_pending_r,
  input                       dmp_wr_pending_r,
  input                       dc4_stall,        // DMP stalls at CA/DC4
  input                       dc4_replay,       // replay the instr at DC4
  input                       dc4_waw_replay_r, // replay if WAW hazard

  input                       ct_replay,        // post-commit replay
  input                       wa_cmt_isi_evt,   //
  input                       excpn_restart,    // Exception & interrupt kills CA
  input                       hlt_restart,      // Halt kills CA
  input                       aps_break,        // BP Halt kills CA
  input                       aps_halt,         // WP Halt kills CA
  input                       x3_aps_break_r,   // X3 APS BP
  input                       x3_aps_halt_r,    // X3 APS WP
  input                       wa_uopld_status32,
  // -------------------------------------------------------------------------
  input     [`npuarc_RGF_ADDR_RANGE] wa_rf_wa0_r,      // reg0 address at Writeback
  input                       wa_rf_wenb0_r,    // reg0 at Writeback is enabled
  input                       wa_rf_wenb0_64_r, // enable 64-bit write 0
  //
  input     [`npuarc_RGF_ADDR_RANGE] wa_rf_wa1_r,      // reg1 address at Writeback
  input                       wa_rf_wenb1_r,    // reg1 at Writeback is enabled
  input                       wa_rf_wenb1_64_r, // enable 64-bit write 1
  input                       wa_writes_acc_r,  // WA has explicit ACC write
  input                       wa_acc_wenb_r,    // WA has implicit ACC write
  // -------------------------------------------------------------------------
  input                       x1_rf_renb0_64_r, // X1 src reg #0 is 64-bit
  input                       x2_rf_renb0_64_r, // X2 src reg #0 is 64-bit
  input                       x3_rf_renb0_64_r, // X3 src reg #0 is 64-bit
  input                       ca_rf_renb0_64_r, // CA src reg #0 is 64-bit
  // -------------------------------------------------------------------------
  input                       x1_rf_renb1_64_r, // X1 src reg #1 is 64-bit
  input                       x2_rf_renb1_64_r, // X2 src reg #1 is 64-bit
  input                       x3_rf_renb1_64_r, // X3 src reg #1 is 64-bit
  input                       ca_rf_renb1_64_r, // CA src reg #1 is 64-bit

  ////////// Forwarding hazards 64-bit write port 0 //////////////////////////
  //
  input                       x1_cc_byp_64_haz_r, // X1 insn cannot bypass r0h
  input                       x2_cc_byp_64_haz_r, // X2 insn cannot bypass r0h
  input                       x3_cc_byp_64_haz_r, // X3 insn cannot bypass r0h
  input                       ca_cc_byp_64_haz_r, // CA insn cannot bypass r0h
  input                       wa_cc_byp_64_haz_r, // WA insn cannot bypass r0h

  ////////// Misprediction and restart interface /////////////////////////////
  //
  input                       da_in_dslot_r,    // DA inst is in a dslot
  input                       sa_in_dslot_r,    // SA inst is in a dslot
  input                       x1_in_dslot_r,    // X1 inst is in a dslot
  input                       x1_dslot_stall,   // X1 dslot error branch stall
  input                       x2_in_dslot_r,    // X2 inst is in a dslot
  input                       x3_in_dslot_r,    // X3 inst is in a dslot
  input                       ca_in_dslot_r,    // CA inst is in a dslot
  //
  input                       x2_restart_r,     // restart signal from Exec2
  input                       x2_mispred_r,     // early branch misprediction
  //
  // Note: the following fragged signals cover all forms of error-branch
  input                       holdup_excpn_r,
  input                       holdup_excpn_nxt,
  input                       x2_error_branch_r,// X2 insn has error-branch
  input                       x2_fragged_r,     // X2 insn was fragged on issue
  input                       x3_error_branch_r,// X3 insn has error-branch
  input                       ca_error_branch_r,// CA insn has error-branch
  input                       ca_fragged_r,     // CA insn was fragged on issue
  input                       wa_error_branch,  // late error branch report
  //
  input                       wa_restart,       // restart signal from W/back
  input                       excpn_in_prologue_r,// in an exception prologue

  input                       wa_mispred_r,     // late branch misprediction
  ////////// Graduation requests from the DMP ////////////////////////////////
  //
  input                       dc4_grad_req,     // DMP graduation request
  input    [`npuarc_GRAD_ADDR_RANGE] dc4_grad_rf_wa,   // DMP graduating register
  input                       dc4_grad_rf_64,   // 64-bit DMP graduation
  input                       dmp_idle_r,       // DMP is idle
  input                       dmp_retire_req,   // DMP requests a retirement

  ////////// Graduation requests from the Divide Unit ////////////////////////
  //
  input                       div_grad_req,     // DIV graduation request
  input     [`npuarc_RGF_ADDR_RANGE] div_grad_rf_wa,   // DIV graduating register

  ////////// Graduation requests from the Floating-point Unit ////////////////
  //
  input                       eia_grad_req,     // EIA graduation request
  input     [`npuarc_RGF_ADDR_RANGE] eia_grad_rf_wa,   // EIA graduating register
  input                       eia_grad_rf_64,   // 64-bit EIA graduation

  ////////// Graduation acknowledgements to all post-commit units ////////////
  //
  output reg                  ca_grad_req,      // any graduation request
  output                      ca_grad_ack,      // graduation acceptance
  output    [`npuarc_GRAD_TAG_RANGE] ca_grad_tag,      // tag of graduating context
  output reg                  ca_replay,        // replay CA stage instruction
  output reg                  ca_dc4_replay,    // replay CA stage instruction,
                                                // without the holdup exception
                                                // to remove combinational loop

  ////////// Retirement interface with Commit stage //////////////////////////
  //
  input                       ca_retire_req,    // retirement request
  input     [`npuarc_GRAD_TAG_RANGE] ca_retire_tag,    // tag of retiring context
  input                       ca_retire_ack,    // retirement acknowledged
  input                       ca_wa1_conflict,  // unable to retire on port 1
  input                       commit_inst,      // confirmed instruction commit
  output                      dp_retire_rf_64,  // 64-bit flag for retirement
  output                      dp_retire_rf_wenb,// reg-wenb for retiring tag
  output   [`npuarc_GRAD_ADDR_RANGE] dp_retire_rf_wa,  // reg-addr for retiring tag
  output    [`npuarc_ZNCV_RANGE]     dp_retire_zncv,   // retirement ZNCV write enables
  output reg                  ar_zncv_upt_r,    // ZNCV update pending in GB
  output                      dp_retire_scond,  // SCOND is retiring this cycle
  output                      dp_retire_writes_acc,
  output    [`npuarc_ADDR_RANGE]     dp_retire_ld_addr, // VA of retiring load
  output                      dp_retire_is_load, // Retiring is load

  ////////// Operands-stage bypass gating signals ////////////////////////////
  //
  output                      fwd_x1_sa0_lo,
  output                      fwd_x2_sa0_lo,
  output                      fwd_x3_sa0_lo,
  output                      fwd_ca0_lo_sa0_lo,
  output                      fwd_ca1_lo_sa0_lo,
  output                      fwd_wa0_lo_sa0_lo,
  output                      fwd_wa1_lo_sa0_lo,
  output                      fwd_ca0_hi_sa0_lo,
  output                      fwd_wa0_hi_sa0_lo,
  output                      fwd_ca1_hi_sa0_lo,
  output                      fwd_ca1_hi_sa1_lo,
  output                      fwd_wa1_hi_sa0_lo,
  output                      fwd_wa1_hi_sa1_lo,
  output                      fwd_wa0_hi_sa0_hi,
  output                      fwd_wa1_hi_sa0_hi,
  output                      fwd_x1_sa1_lo,
  output                      fwd_x2_sa1_lo,
  output                      fwd_x3_sa1_lo,
  output                      fwd_ca0_lo_sa1_lo,
  output                      fwd_ca1_lo_sa1_lo,
  output                      fwd_wa0_lo_sa1_lo,
  output                      fwd_wa1_lo_sa1_lo,
  output                      fwd_ca0_hi_sa1_lo,
  output                      fwd_wa0_hi_sa1_lo,
  output                      fwd_wa0_lo_sa0_hi,
  output                      fwd_wa1_lo_sa0_hi,
  output                      fwd_wa0_hi_sa1_hi,
  output                      fwd_wa0_lo_sa1_hi,
  output                      fwd_wa1_lo_sa1_hi,
  output                      fwd_wa1_hi_sa1_hi,

  ////////// Exec1-stage bypass gating signals ///////////////////////////////
  //
  output                      fwd_x1_r0_dmp_fast,   // load data for early bypass
  output                      fwd_x1_r1_dmp_fast,   // load data for early bypass
  //
  output                      fwd_x1_r0_wa_w0_lo,   // W/back w0 bypass value (lo)
  output                      fwd_x1_r1_wa_w0_lo,   // W/back w0 bypass value (lo)
  //
  output                      fwd_x1_r0_wa_w1_lo,   // W/back w1 bypass value (lo)
  output                      fwd_x1_r1_wa_w1_lo,   // W/back w1 bypass value (lo)
  //
  output                      fwd_x1_r0_ca_w1_hi,   // Commit w1 bypass value (hi)
  output                      fwd_x1_r1_ca_w1_hi,   // Commit w1 bypass value (hi)
  output                      fwd_x1_r0h_ca_w1_hi,  // Commit w1 bypass value (hi)
  output                      fwd_x1_r1h_ca_w1_hi,  // Commit w1 bypass value (hi)
  //
  output                      fwd_x1_r0_wa_w1_hi,   // W/back w1 bypass value (hi)
  output                      fwd_x1_r1_wa_w1_hi,   // W/back w1 bypass value (hi)
  output                      fwd_x1_r0h_wa_w1_hi,  // W/back w1 bypass value (hi)
  output                      fwd_x1_r1h_wa_w1_hi,  // W/back w1 bypass value (hi)
  output                      fwd_x1_r1h_wa_w0_lo,  // W/back w0 bypass value (lo)
  output                      fwd_x1_r1h_wa_w1_lo,  // W/back w1 bypass value (lo)
  //
  output                      fwd_x1_r0_x2_w0,      // Exec2 bypass value
  output                      fwd_x1_r1_x2_w0,      // Exec2 bypass value
  output                      fwd_x1_r0h_x2_w0,     // Exec2 bypass value
  output                      fwd_x1_r1h_x2_w0,     // Exec2 bypass value

  output                      fwd_x1_r0_x3_w0,      // Exec3 bypass value
  output                      fwd_x1_r1_x3_w0,      // Exec3 bypass value
  output                      fwd_x1_r0h_x3_w0,     // Exec3 bypass value
  output                      fwd_x1_r1h_x3_w0,     // Exec3 bypass value

  output                      fwd_x1_r0_ca_w0_lo,   // Commit w0 bypass value (lo)
  output                      fwd_x1_r1_ca_w0_lo,   // Commit w0 bypass value (lo)

  output                      fwd_x1_r0_ca_w1_lo,   // Commit w1 bypass value (lo)
  output                      fwd_x1_r1_ca_w1_lo,   // Commit w1 bypass value (lo)

  output                      fwd_x1_r0_ca_w0_hi,   // Commit w0 bypass value (hi)
  output                      fwd_x1_r1_ca_w0_hi,   // Commit w0 bypass value (hi)

  output                      fwd_x1_r0_wa_w0_hi,   // W/back w0 bypass value (hi)
  output                      fwd_x1_r1_wa_w0_hi,   // W/back w0 bypass value (hi)
  output                      fwd_x1_r0h_ca_w0_lo,  // Commit w0 bypass value (lo)
  output                      fwd_x1_r1h_ca_w0_lo,  // Commit w0 bypass value (lo)
  output                      fwd_x1_r0h_ca_w0_hi,  // Commit w0 bypass value (hi)
  output                      fwd_x1_r1h_ca_w0_hi,  // Commit w0 bypass value (hi)

  output                      fwd_x1_r0h_ca_w1_lo,  // Commit w1 bypass value (lo)
  output                      fwd_x1_r1h_ca_w1_lo,  // Commit w1 bypass value (lo)

  output                      fwd_x1_r0h_wa_w0_lo,  // W/back w0 bypass value (lo)
  output                      fwd_x1_r0h_wa_w0_hi,  // W/back w0 bypass value (hi)
  output                      fwd_x1_r0h_wa_w1_lo,  // W/back w1 bypass value (lo)
  output                      fwd_x1_r1h_wa_w0_hi,  // W/back w0 bypass value (hi)
  output reg [`npuarc_ZNCV_RANGE]    fwd_zncv_x1,          // fwd X1 ZNCV flags
  output reg [`npuarc_ZNCV_RANGE]    fwd_zncv_x1_x2,       // W/back X2 ZNCV flags
  output reg [`npuarc_ZNCV_RANGE]    fwd_zncv_x1_ca,       // W/back CA ZNCV flags
  output reg                  fwd_zncv_x1_ar,

  ////////// Exec2-stage bypass gating signals ///////////////////////////////
  //
  output                      fwd_x2_r0_wa_w0_lo,//
  output                      fwd_x2_r0_wa_w1_lo,//
  output                      fwd_x2_r1_wa_w0_lo,//
  output                      fwd_x2_r1_wa_w1_lo,//
  output                      fwd_x2_r0_wa_w0_hi,//
  output                      fwd_x2_r1_wa_w0_hi,//
  output                      fwd_x2_r0_wa_w1_hi,//
  output                      fwd_x2_r1_wa_w1_hi,//
  output                      fwd_x2_r1h_wa_w0_lo,  // 
  output                      fwd_x2_r1h_wa_w1_lo,  //
  output                      fwd_x2_r1h_wa_w0_hi,  //
  output                      fwd_x2_r1h_wa_w1_hi,  //

  ////////// Exec3-stage bypass gating signals ///////////////////////////////
  //
  output                      fwd_x3_r0_ca_w0_lo, //
  output                      fwd_x3_r0_ca_w1_lo, //
  output                      fwd_x3_r0_wa_w0_lo, //
  output                      fwd_x3_r0_wa_w1_lo, //
  //
  output                      fwd_x3_r1_ca_w0_lo, //
  output                      fwd_x3_r1_ca_w1_lo, //
  output                      fwd_x3_r1_wa_w0_lo, //
  output                      fwd_x3_r1_wa_w1_lo, //
  output                      fwd_x3_r0_ca_w0_hi, //
  output                      fwd_x3_r0_wa_w0_hi, //
  //
  output                      fwd_x3_r1_ca_w0_hi, //
  output                      fwd_x3_r1_wa_w0_hi, //
  output                      fwd_x3_r0_wa_w1_hi, //
  output                      fwd_x3_r1_wa_w1_hi, //
  output                      fwd_x3_r0_ca_w1_hi, //
  //
  output                      fwd_x3_r1_ca_w1_hi, //
  output                      fwd_x3_r1h_ca_w0_lo,
  output                      fwd_x3_r1h_ca_w1_lo,
  output                      fwd_x3_r1h_wa_w0_lo,
  output                      fwd_x3_r1h_wa_w1_lo,
  output                      fwd_x3_r1h_ca_w0_hi,
  output                      fwd_x3_r1h_wa_w0_hi,
  output                      fwd_x3_r1h_ca_w1_hi,
  output                      fwd_x3_r1h_wa_w1_hi,


  ////////// Commit-stage bypass gating signals //////////////////////////////
  //
  output                      fwd_ca_r0_wa_w0_lo, // 
  output                      fwd_ca_r0_wa_w1_lo, // 
  output                      fwd_ca_r1_wa_w0_lo, // 
  output                      fwd_ca_r1_wa_w1_lo, // 
  output                      fwd_ca_r0_wa_w0_hi, // 
  output                      fwd_ca_r1_wa_w0_hi, // 
  output                      fwd_ca_r0_wa_w1_hi, // 
  output                      fwd_ca_r1_wa_w1_hi, // 
  output                      fwd_ca_r1h_wa_w0_lo,
  output                      fwd_ca_r1h_wa_w1_lo,
  output                      fwd_ca_r1h_wa_w0_hi,
  output                      fwd_ca_r1h_wa_w1_hi,
//  output                      fwd_wa_d0l_dmp_lo,  //
//  output                      fwd_wa_d1l_dmp_lo,  //
//  output                      fwd_wa_d0h_dmp_lo,  //
 // output                      fwd_wa_d1h_dmp_lo,  //
//  output                      fwd_wa_d1h_dmp_hi,  //
//  output                      fwd_wa_d0h_dmp_hi,  //

  //////////  X1 branch resolution dependency conditions /////////////////////
  //
  output reg                  x1_cond_ready,    // X1 flag condition is ready
  output reg                  x1_bta_ready,     // X1 BTA value is ready
  output reg                  x1_no_eval,       // insn at X1 does not evaluate
  output reg                  x2_done_nxt,      //

  ////////// Pipeline stage control signals //////////////////////////////////
  //
  output reg                  da_holdup,        // EXU unable to take input
  output reg                  da_enable /* verilator public_flat */,        // Decode inputs are enabled
  output reg                  sa_enable /* verilator public_flat */,        // Operand inputs are enabled
  output reg                  x1_enable /* verilator public_flat */,        // Exec1 inputs are enabled
  output reg                  x2_enable /* verilator public_flat */,        // Exec2 inputs are enabled
  output reg                  x3_enable /* verilator public_flat */,        // Exec3 inputs are enabled
  output reg                  ca_enable /* verilator public_flat */,        // Commit inputs are enabled
  output reg                  wa_enable /* verilator public_flat */,        // Writeback inputs are enabled
  //
  output reg                  da_pass /* verilator public_flat */,          // Decode has valid insn to pass
  output reg                  sa_pass /* verilator public_flat */,          // Opds has valid insn to pass
  output reg                  x1_pass /* verilator public_flat */,          // Exec1 has valid insn to pass
  output reg                  x2_pass /* verilator public_flat */,          // Exec2 has valid insn to pass
  output reg                  x3_pass /* verilator public_flat */,          // Exec3 has valid insn to pass
  output reg                  ca_pass /* verilator public_flat */,          // Commit has valid insn to pass
  output reg                  ca_pass_no_hlt,   // Commit has valid insn to pass
                                                //  excluding a potential kill
                                                //  for a halt event.

  input                       ca_iprot_viol_r,  // ifetch prot viol at CA
  output reg                  ca_pass_no_iprot, // Commit will pass a valid
                                                //  valid insn to WA, ignoring
                                                //  any iprot violation
  output reg                  sa_valid_r,       // Operand stage has valid insn
  output reg                  x1_valid_r,       // Exec1 stage has valid insn
  output reg                  x2_valid_r,       // Exec2 stage has valid insn
  output reg                  x3_valid_r,       // Exec3 stage has valid insn
  output reg                  ca_valid_r,       // Commit stage has valid insn
  output reg                  wa_valid_r,       // Writeback has valid insn

  output reg                  da_kill,          // DA stage is to be killed
  output reg                  sa_kill,          // SA stage is to be killed
  output reg                  x1_kill,          // X1 stage is to be killed
  output reg                  x2_kill,          // X2 stage is to be killed
  output reg                  x3_kill,          // X3 stage is to be killed
  output reg                  ca_kill,          // CA stage is to be killed

  output reg                  x1_wa_dslot,      // X1 in DSLOT of WA
  output reg                  x2_wa_dslot,      // X2 in DSLOT of WA

  output reg                  x1_retain,        // X1 must retain its insn
  output reg                  x2_retain,        // X2 must retain its insn
  output reg                  x3_retain,        // X3 must retain its insn

  output reg                  ca_stall,         // CA stage is stalled

  output reg                  x2_read_r0_r,     // X2 insn is yet to read reg0
  output reg                  x2_read_r1_r,     // X2 insn is yet to read reg1
  output reg                  x3_read_r0_r,     // X3 insn is yet to read reg0
  output reg                  x3_read_r1_r,     // X3 insn is yet to read reg1


  ////////////////////////////////////////////////////////////////////////////
  //                                                                        //
  // Pipeline registers holding completion status of non-Load comptutations //
  // at stages x2, x3 and ca.                                               //
  //                                                                        //
  // If the instruction at stage XX computes in the current cycle, and then //
  // advances to stage YY, it will set YY_done_r on entry to stage YY.      //
  // Thereafter, as that instruction advances through the pipeline, all     //
  // subsequent ZZ_done_r signals will also get set to 1. This indicates    //
  // that the instruction has completed its non-Load computation.           //
  //                                                                        //
  ////////////////////////////////////////////////////////////////////////////
  //
  output reg                  x2_done_r,        // x2 stage has valid x2_res_r
  output reg                  x2_has_w0,        // x2 has valid x2_byp_data0
  output reg                  x3_done_r,        // x3 stage has valid x3_res_r
  output reg                  ca_done_r,        // ca stage has valid ca_res_r
  output reg                  ar_tags_empty_r   // ar stage is empty
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Decode-stage Read-After-Write dependency computations                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg   [`npuarc_PRE_RAW_RANGE]        dp_da_sa;           // da dependencies on sa
reg   [`npuarc_PRE_RAW_RANGE]        dp_da_x1;           // da dependencies on x1
reg   [`npuarc_PRE_RAW_RANGE]        dp_da_x2;           // da dependencies on x2
reg   [`npuarc_PRE_RAW_RANGE]        dp_da_x3;           // da dependencies on x3
reg   [`npuarc_PRE_RAW_RANGE]        dp_da_ca;           // da dependencies on ca
reg   [`npuarc_PRE_RAW_RANGE]        dp_da_wa;           // da dependencies on wa 
reg   [`npuarc_POST_RAW_RANGE]       dp_da_ar0;          // da dependencies on ar0
reg   [`npuarc_POST_RAW_RANGE]       dp_da_ar1;          // da dependencies on ar1
reg   [`npuarc_POST_RAW_RANGE]       dp_da_ar2;          // da dependencies on ar2
reg   [`npuarc_POST_RAW_RANGE]       dp_da_ar3;          // da dependencies on ar3
reg   [`npuarc_POST_RAW_RANGE]       dp_da_ar4;          // da dependencies on ar4
reg   [`npuarc_POST_RAW_RANGE]       dp_da_ar5;          // da dependencies on ar5
reg   [`npuarc_POST_RAW_RANGE]       dp_da_ar6;          // da dependencies on ar6
reg   [`npuarc_POST_RAW_RANGE]       dp_da_ar7;          // da dependencies on ar7

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Operand-stage Write-After-Write dependency computations                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_x1;           // sa kills x1 definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_x2;           // sa kills x2 definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_x3;           // sa kills x3 definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_ca;           // sa kills ca definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_wa;           // sa kills wa definitions 

reg   [`npuarc_DP_KILL_RANGE]        sa_kl_ar0;          // sa kills ar0 definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_ar1;          // sa kills ar1 definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_ar2;          // sa kills ar2 definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_ar3;          // sa kills ar3 definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_ar4;          // sa kills ar4 definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_ar5;          // sa kills ar5 definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_ar6;          // sa kills ar6 definitions
reg   [`npuarc_DP_KILL_RANGE]        sa_kl_ar7;          // sa kills ar7 definitions
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Operand-stage Read-After-Write dependency pipeline registers             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg   [`npuarc_PRE_RAW_RANGE]        dp_sa_x1_r;         // sa dependency on x1
reg   [`npuarc_PRE_RAW_RANGE]        dp_sa_x2_r;         // sa dependencies on x2
reg   [`npuarc_PRE_RAW_RANGE]        dp_sa_x3_r;         // sa dependencies on x3
reg   [`npuarc_PRE_RAW_RANGE]        dp_sa_ca_r;         // sa dependencies on ca
reg   [`npuarc_PRE_RAW_RANGE]        dp_sa_wa_r;         // sa dependencies on wa
reg   [`npuarc_POST_RAW_RANGE]       dp_sa_ar0_r;        // sa dependencies on ar0
reg   [`npuarc_POST_RAW_RANGE]       dp_sa_ar1_r;        // sa dependencies on ar1
reg   [`npuarc_POST_RAW_RANGE]       dp_sa_ar2_r;        // sa dependencies on ar2
reg   [`npuarc_POST_RAW_RANGE]       dp_sa_ar3_r;        // sa dependencies on ar3
reg   [`npuarc_POST_RAW_RANGE]       dp_sa_ar4_r;        // sa dependencies on ar4
reg   [`npuarc_POST_RAW_RANGE]       dp_sa_ar5_r;        // sa dependencies on ar5
reg   [`npuarc_POST_RAW_RANGE]       dp_sa_ar6_r;        // sa dependencies on ar6
reg   [`npuarc_POST_RAW_RANGE]       dp_sa_ar7_r;        // sa dependencies on ar7

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Exec1-stage Read-After-Write dependency pipeline registers               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg   [`npuarc_DP_PRE_RANGE]         dp_x1_x2_r;         // x1 dependencies on x2
reg   [`npuarc_DP_PRE_RANGE]         dp_x1_x3_r;         // x1 dependencies on x3
reg   [`npuarc_DP_PRE_RANGE]         dp_x1_ca_r;         // x1 dependencies on ca
reg   [`npuarc_DP_PRE_RANGE]         dp_x1_wa_r;         // x1 dependencies on wa
reg   [`npuarc_DP_POST_RANGE]        dp_x1_ar0_r;        // x1 dependencies on ar0
reg   [`npuarc_DP_POST_RANGE]        dp_x1_ar1_r;        // x1 dependencies on ar1
reg   [`npuarc_DP_POST_RANGE]        dp_x1_ar2_r;        // x1 dependencies on ar2
reg   [`npuarc_DP_POST_RANGE]        dp_x1_ar3_r;        // x1 dependencies on ar3
reg   [`npuarc_DP_POST_RANGE]        dp_x1_ar4_r;        // x1 dependencies on ar4
reg   [`npuarc_DP_POST_RANGE]        dp_x1_ar5_r;        // x1 dependencies on ar5
reg   [`npuarc_DP_POST_RANGE]        dp_x1_ar6_r;        // x1 dependencies on ar6
reg   [`npuarc_DP_POST_RANGE]        dp_x1_ar7_r;        // x1 dependencies on ar7

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Exec2-stage Read-After-Write dependency pipeline registers               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg   [`npuarc_DP_PRE_RANGE]         dp_x2_x3_r;         // x2 dependencies on x3
reg   [`npuarc_DP_PRE_RANGE]         dp_x2_ca_r;         // x2 dependencies on ca
reg   [`npuarc_DP_PRE_RANGE]         dp_x2_wa_r;         // x2 dependencies on wa
reg   [`npuarc_DP_POST_RANGE]        dp_x2_ar0_r;        // x2 dependencies on ar0
reg   [`npuarc_DP_POST_RANGE]        dp_x2_ar1_r;        // x2 dependencies on ar1
reg   [`npuarc_DP_POST_RANGE]        dp_x2_ar2_r;        // x2 dependencies on ar2
reg   [`npuarc_DP_POST_RANGE]        dp_x2_ar3_r;        // x2 dependencies on ar3
reg   [`npuarc_DP_POST_RANGE]        dp_x2_ar4_r;        // x2 dependencies on ar4
reg   [`npuarc_DP_POST_RANGE]        dp_x2_ar5_r;        // x2 dependencies on ar5
reg   [`npuarc_DP_POST_RANGE]        dp_x2_ar6_r;        // x2 dependencies on ar6
reg   [`npuarc_DP_POST_RANGE]        dp_x2_ar7_r;        // x2 dependencies on ar7
// leda NTL_CON32 on
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Exec3-stage Read-After-Write dependency pipeline registers               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg   [`npuarc_DP_PRE_RANGE]         dp_x3_ca_r;         // x3 dependencies on ca
reg   [`npuarc_DP_PRE_RANGE]         dp_x3_wa_r;         // x3 dependencies on wa
reg   [`npuarc_DP_POST_RANGE]        dp_x3_ar0_r;        // x3 dependencies on ar0
reg   [`npuarc_DP_POST_RANGE]        dp_x3_ar1_r;        // x3 dependencies on ar1
reg   [`npuarc_DP_POST_RANGE]        dp_x3_ar2_r;        // x3 dependencies on ar2
reg   [`npuarc_DP_POST_RANGE]        dp_x3_ar3_r;        // x3 dependencies on ar3
reg   [`npuarc_DP_POST_RANGE]        dp_x3_ar4_r;        // x3 dependencies on ar4
reg   [`npuarc_DP_POST_RANGE]        dp_x3_ar5_r;        // x3 dependencies on ar5
reg   [`npuarc_DP_POST_RANGE]        dp_x3_ar6_r;        // x3 dependencies on ar6
reg   [`npuarc_DP_POST_RANGE]        dp_x3_ar7_r;        // x3 dependencies on ar7

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Commit-stage Read-After-Write dependency pipeline registers              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg   [`npuarc_DP_PRE_RANGE]         dp_ca_wa_r;         // ca dependencies on wa
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar0_r;        // ca dependencies on ar0
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar0_nxt;      // next ca to ar0 deps
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar1_r;        // ca dependencies on ar1
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar1_nxt;      // next ca to ar1 deps
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar2_r;        // ca dependencies on ar2
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar2_nxt;      // next ca to ar2 deps
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar3_r;        // ca dependencies on ar3
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar3_nxt;      // next ca to ar3 deps
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar4_r;        // ca dependencies on ar4
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar4_nxt;      // next ca to ar4 deps
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar5_r;        // ca dependencies on ar5
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar5_nxt;      // next ca to ar5 deps
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar6_r;        // ca dependencies on ar6
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar6_nxt;      // next ca to ar6 deps
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar7_r;        // ca dependencies on ar7
reg   [`npuarc_DP_POST_RANGE]        dp_ca_ar7_nxt;      // next ca to ar7 deps
// leda NTL_CON32 on

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Context registers for post-commit retirement of instructions             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           ar0_rf_valid_nxt;

reg                           ar0_is_load_r;      // 1 => entry is for a load
reg                           ar0_is_load_nxt;
reg                           ar0_rf_wenb1_nxt;
reg   [`npuarc_GRAD_ADDR_RANGE]      ar0_rf_wa1_nxt;

reg                           ar0_rf_wenb1_64_nxt;
reg                           ar0_rf_wenbs;       // 1 => wenb1_r or wenb1_64_r

reg                           ar0_flag_wen_r;     // 1 => writes ZNCV flags
reg                           ar0_flag_wen_nxt;   // next flag-write

reg                           ar0_writes_acc_r;   // 1 => explicit ACC write
reg                           ar0_writes_acc_nxt; // 1 => explicit ACC write
reg                           ar0_exclusive_r;    // 1 => LLOCK or SCOND
reg                           ar0_exclusive_nxt;  // 1 => LLOCK or SCOND
reg   [`npuarc_ADDR_RANGE]           ar0_ld_addr_r;      // VA of graduating loads
reg                           ar1_rf_valid_nxt;

reg                           ar1_is_load_r;      // 1 => entry is for a load
reg                           ar1_is_load_nxt;
reg                           ar1_rf_wenb1_nxt;
reg   [`npuarc_GRAD_ADDR_RANGE]      ar1_rf_wa1_nxt;

reg                           ar1_rf_wenb1_64_nxt;
reg                           ar1_rf_wenbs;       // 1 => wenb1_r or wenb1_64_r

reg                           ar1_flag_wen_r;     // 1 => writes ZNCV flags
reg                           ar1_flag_wen_nxt;   // next flag-write

reg                           ar1_writes_acc_r;   // 1 => explicit ACC write
reg                           ar1_writes_acc_nxt; // 1 => explicit ACC write
reg                           ar1_exclusive_r;    // 1 => LLOCK or SCOND
reg                           ar1_exclusive_nxt;  // 1 => LLOCK or SCOND
reg   [`npuarc_ADDR_RANGE]           ar1_ld_addr_r;      // VA of graduating loads
reg                           ar2_rf_valid_nxt;

reg                           ar2_is_load_r;      // 1 => entry is for a load
reg                           ar2_is_load_nxt;
reg                           ar2_rf_wenb1_nxt;
reg   [`npuarc_GRAD_ADDR_RANGE]      ar2_rf_wa1_nxt;

reg                           ar2_rf_wenb1_64_nxt;
reg                           ar2_rf_wenbs;       // 1 => wenb1_r or wenb1_64_r

reg                           ar2_flag_wen_r;     // 1 => writes ZNCV flags
reg                           ar2_flag_wen_nxt;   // next flag-write

reg                           ar2_writes_acc_r;   // 1 => explicit ACC write
reg                           ar2_writes_acc_nxt; // 1 => explicit ACC write
reg                           ar2_exclusive_r;    // 1 => LLOCK or SCOND
reg                           ar2_exclusive_nxt;  // 1 => LLOCK or SCOND
reg   [`npuarc_ADDR_RANGE]           ar2_ld_addr_r;      // VA of graduating loads
reg                           ar3_rf_valid_nxt;

reg                           ar3_is_load_r;      // 1 => entry is for a load
reg                           ar3_is_load_nxt;
reg                           ar3_rf_wenb1_nxt;
reg   [`npuarc_GRAD_ADDR_RANGE]      ar3_rf_wa1_nxt;

reg                           ar3_rf_wenb1_64_nxt;
reg                           ar3_rf_wenbs;       // 1 => wenb1_r or wenb1_64_r

reg                           ar3_flag_wen_r;     // 1 => writes ZNCV flags
reg                           ar3_flag_wen_nxt;   // next flag-write

reg                           ar3_writes_acc_r;   // 1 => explicit ACC write
reg                           ar3_writes_acc_nxt; // 1 => explicit ACC write
reg                           ar3_exclusive_r;    // 1 => LLOCK or SCOND
reg                           ar3_exclusive_nxt;  // 1 => LLOCK or SCOND
reg   [`npuarc_ADDR_RANGE]           ar3_ld_addr_r;      // VA of graduating loads
reg                           ar4_rf_valid_nxt;

reg                           ar4_is_load_r;      // 1 => entry is for a load
reg                           ar4_is_load_nxt;
reg                           ar4_rf_wenb1_nxt;
reg   [`npuarc_GRAD_ADDR_RANGE]      ar4_rf_wa1_nxt;

reg                           ar4_rf_wenb1_64_nxt;
reg                           ar4_rf_wenbs;       // 1 => wenb1_r or wenb1_64_r

reg                           ar4_flag_wen_r;     // 1 => writes ZNCV flags
reg                           ar4_flag_wen_nxt;   // next flag-write

reg                           ar4_writes_acc_r;   // 1 => explicit ACC write
reg                           ar4_writes_acc_nxt; // 1 => explicit ACC write
reg                           ar4_exclusive_r;    // 1 => LLOCK or SCOND
reg                           ar4_exclusive_nxt;  // 1 => LLOCK or SCOND
reg   [`npuarc_ADDR_RANGE]           ar4_ld_addr_r;      // VA of graduating loads
reg                           ar5_rf_valid_nxt;

reg                           ar5_is_load_r;      // 1 => entry is for a load
reg                           ar5_is_load_nxt;
reg                           ar5_rf_wenb1_nxt;
reg   [`npuarc_GRAD_ADDR_RANGE]      ar5_rf_wa1_nxt;

reg                           ar5_rf_wenb1_64_nxt;
reg                           ar5_rf_wenbs;       // 1 => wenb1_r or wenb1_64_r

reg                           ar5_flag_wen_r;     // 1 => writes ZNCV flags
reg                           ar5_flag_wen_nxt;   // next flag-write

reg                           ar5_writes_acc_r;   // 1 => explicit ACC write
reg                           ar5_writes_acc_nxt; // 1 => explicit ACC write
reg                           ar5_exclusive_r;    // 1 => LLOCK or SCOND
reg                           ar5_exclusive_nxt;  // 1 => LLOCK or SCOND
reg   [`npuarc_ADDR_RANGE]           ar5_ld_addr_r;      // VA of graduating loads
reg                           ar6_rf_valid_nxt;

reg                           ar6_is_load_r;      // 1 => entry is for a load
reg                           ar6_is_load_nxt;
reg                           ar6_rf_wenb1_nxt;
reg   [`npuarc_GRAD_ADDR_RANGE]      ar6_rf_wa1_nxt;

reg                           ar6_rf_wenb1_64_nxt;
reg                           ar6_rf_wenbs;       // 1 => wenb1_r or wenb1_64_r

reg                           ar6_flag_wen_r;     // 1 => writes ZNCV flags
reg                           ar6_flag_wen_nxt;   // next flag-write

reg                           ar6_writes_acc_r;   // 1 => explicit ACC write
reg                           ar6_writes_acc_nxt; // 1 => explicit ACC write
reg                           ar6_exclusive_r;    // 1 => LLOCK or SCOND
reg                           ar6_exclusive_nxt;  // 1 => LLOCK or SCOND
reg   [`npuarc_ADDR_RANGE]           ar6_ld_addr_r;      // VA of graduating loads
reg                           ar7_rf_valid_nxt;

reg                           ar7_is_load_r;      // 1 => entry is for a load
reg                           ar7_is_load_nxt;
reg                           ar7_rf_wenb1_nxt;
reg   [`npuarc_GRAD_ADDR_RANGE]      ar7_rf_wa1_nxt;

reg                           ar7_rf_wenb1_64_nxt;
reg                           ar7_rf_wenbs;       // 1 => wenb1_r or wenb1_64_r

reg                           ar7_flag_wen_r;     // 1 => writes ZNCV flags
reg                           ar7_flag_wen_nxt;   // next flag-write

reg                           ar7_writes_acc_r;   // 1 => explicit ACC write
reg                           ar7_writes_acc_nxt; // 1 => explicit ACC write
reg                           ar7_exclusive_r;    // 1 => LLOCK or SCOND
reg                           ar7_exclusive_nxt;  // 1 => LLOCK or SCOND
reg   [`npuarc_ADDR_RANGE]           ar7_ld_addr_r;      // VA of graduating loads

assign gb_dest_cr_is_ext =   1'b0
                               | ar0_dest_cr_is_ext & ar0_rf_valid_r
                               | ar1_dest_cr_is_ext & ar1_rf_valid_r
                               | ar2_dest_cr_is_ext & ar2_rf_valid_r
                               | ar3_dest_cr_is_ext & ar3_rf_valid_r
                               | ar4_dest_cr_is_ext & ar4_rf_valid_r
                               | ar5_dest_cr_is_ext & ar5_rf_valid_r
                               | ar6_dest_cr_is_ext & ar6_rf_valid_r
                               | ar7_dest_cr_is_ext & ar7_rf_valid_r
                                 ;

reg                           ar_wenb_nxt;        // selected port 0 or 1 wenb
reg                           ar_tags_full_r;     // 1 => all tags allocated
reg                           ar_tags_full_nxt;   // next full status
reg [7:0]                 ar_tags_next_state; // tags next state
reg                           ar_full_en;         // enable for ar_tags_full_r
reg                           ar_tags_empty_nxt;  // next empty status
reg   [`npuarc_ZNCV_RANGE]           ar_zncv_wen_r;      // ZNCV flag write enables
reg   [`npuarc_ZNCV_RANGE]           ar_zncv_wen_nxt;    // next flag write enables
reg                           ar_zncv_upt_nxt;    // next ZNCV update status
reg                           x3_flag_haz;        // flag WAW hazard at X3
reg                           ca_uses_flags;      // CA insn uses ZNCV flags
reg                           ca_flag_haz;        // flag RAW hazard at CA

reg                           clear_deps_r;       // delayed wa_restart

reg                           uop_dep_stall;      // stall UOPs on grad buffer
reg                           ar_tags_empty_dly_r;// one cycle delayed to cover wa stage

//   Decode-stage stalls
reg                           da_stall_r0;

//   Operand-stage stalls
reg                           sa_stall_r2;
reg                           sa_stall_r3;
reg                           sa_stall_r4;
reg                           sa_stall_r5;
reg                           sa_stall_r6;
reg                           sa_stall_r14;
reg                           sa_stall_r17;
//   Exec1-stage stalls
reg                           x1_stall_r4;
reg                           x1_stall_r5;
reg                           x1_stall_r6;
reg                           x1_stall_r8;
reg                           x1_stall_r7;
reg                           x1_stall_r15;
reg                           x1_stall_r20;
reg                           x1_stall_r21;
//   Exec2-stage stalls
reg                           x2_stall_r18;
reg                           x2_stall_bld;
//   Exec3-stage stalls
reg                           x3_stall_r9;
reg                           x3_stall_r10;
reg                           x3_stall_r12;
reg                           x3_stall_r16;
reg                           x3_stall_scond;

//   Commit-stage stalls
reg                           ca_stall_r11;
reg                           ca_waw_haz_r;
reg                           ca_waw_haz_nxt;
reg                           ar_excl_pending;
reg                           ca_stall_r18;
reg                           ca_stall_bld;

// General pipeline stage controls from sa to wa
//
// -- per-stage stall signals --
reg                           da_stall;
reg                           sa_stall;
reg                           x1_stall;
reg                           x2_stall;
reg                           x3_stall;
// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  TB use this signal@@
reg                           wa_stall; // always 0
// leda NTL_CON13A on
//reg                           ar_stall_r12;

// -- `xx_yy_dslot' is asserted when stage xx has the delay-slot of stage yy
reg                           da_wa_dslot;
reg                           sa_x2_dslot;
reg                           sa_wa_dslot;
reg                           x1_x2_dslot;
reg                           x3_wa_dslot;
reg                           ca_wa_dslot;

// -- per-stage kill signals
reg                           wa_kills_x2;

// -- per-stage holdup signals
reg                           sa_holdup;
reg                           x1_holdup;
reg                           x2_holdup;
reg                           x3_holdup;
reg                           ca_holdup;

reg                           wa_holdup;

// -- per-stage delay signals (only da generates a delay signal)
reg                           da_delay;

// -- per-stage retain signals
reg                           da_retain /* verilator public_flat */;
reg                           sa_retain;
reg                           ca_retain;
reg                           wa_retain;

reg                           ca_kill_no_hlt;
reg                           ca_kill_no_iprot;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Code-density auxiliary register Read-After-Write dependency pipeline     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg                           sa_aux_haz_r;     // RAW from implicit aux use
reg                           sa_aux_haz_nxt;   // next sa_aux_haz_r
reg                           sa_aux_raw;       // SA insn has aux RAW
reg                           da_aux_raw;       // DA insn has aux RAW
reg                           da_uses_cd_aux;   // DA uses a CD aux reg
reg                           sa_uses_cd_aux;   // SA uses a CD aux reg
reg                           da_sr_cd_haz;     // DA hazard on SR at SA or X1
reg                           sa_sr_cd_haz;     // DA hazard on SR at SA or X1
reg                           aux_r4_haz;       // Region 4 SR in X2,X3,CA

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pipeline registers holding operand read-pending status and completion    //
// status of the operation at stages sa, x1, x2, x3, and ca.                //
//                                                                          //
// On entering the Operand stage, each sa_read_r0_r and sa_read_r1_r is set //
// to 1 if the corresponding da_rf_renb0_r or da_rf_renb1_r signal is set,  //
// and if there is a dependency through that register with any downstream   //
// instruction other than the instruction at the Writeback stage, which can //
// be bypassed in the current cycle as the instruction enters the Operand   //
// stage.                                                                   //
//                                                                          //
// As instructions advance from sa through to x3, the next value for each   //
// xx_read_rY_r state is updated according to whether the producing stage   //
// makes its result available.                                              //
//                                                                          //
// In general, instructions in the x3 stage are not permitted to advance to //
// the Commit stage with any pending register read. The only exception to   //
// this is a Store instruction with a pending read on a store data register //
// value. Such Store instructions are permitted to stall in the Commit      //
// stage and bypass from the Writeback stage W0 or W1 results into the DMP. //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           sa_read_r0_r;     // SA insn yet to read reg0 lo
reg                           sa_read_r1_r;     // SA insn yet to read reg1 lo
reg                           sa_read_r0_nxt;   // next value for sa_read_r0_r
reg                           sa_read_r1_nxt;   // next value for sa_read_r1_r

reg                           x1_read_r0_r;     // X1 insn yet to read reg0 lo
reg                           x1_read_r1_r;     // X1 insn yet to read reg1 lo
reg                           x1_read_r0_nxt;   // next value for x1_read_r0_r
reg                           x1_read_r1_nxt;   // next value for x1_read_r1_r
  // leda NTL_CON32 off
  // LMD: Change on net has no effect on any of the outputs
  // LJ:  Pipeline reg
reg                           x1_read_r2_r;     // X1 insn yet to read reg2
reg                           x1_read_r2_nxt;   // next value for x1_read_r2_r
  // leda NTL_CON32 on
reg                           x1_read_r3_r;     // X1 insn yet to read reg1 hi
reg                           x1_read_r3_nxt;   // next value for x1_read_r3_r
reg                           x1_r0_dmp_fast_r; // allow fast bypass to AGU r0

reg                           x2_read_r0_nxt;   // next value for x2_read_r0_r
reg                           x2_read_r1_nxt;   // next value for x2_read_r1_r

reg   [`npuarc_ZNCV_RANGE]           x2_zncv_valid_r;  // X2 flags useable from X1
reg   [`npuarc_ZNCV_RANGE]           x2_zncv_valid_nxt;// X2 flags useable from X1

reg                           x2_zncv_refil_r;    // X2 ZNCV needs resync with AR
reg                           x2_zncv_refil_nxt;  // X2 ZNCV needs resync with AR


reg                           x3_read_r0_nxt;   // next value for x3_read_r0_r
reg                           x3_read_r1_nxt;   // next value for x3_read_r1_r

reg                           wa_dp_wenb0_64_r; // 64-bit port 0 dst at WA

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Post-commit dependencies at each stage, multiplexed according to the tag //
// of the currently-retiring post-commit context. These dependency vectors  //
// are assigned to stage xx's dep_xx_wa_r when a retirement is scheduled,   //
// and this reinstates the dependency from stage xx to the Writeback stage  //
// just as the retiring value reaches the Writeback stage.                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  some bits are not used
reg  [`npuarc_DP_POST_RANGE]         dp_da_ar;         // sa dependence on retire tag
// leda NTL_CON13A on
reg  [`npuarc_POST_RAW_RANGE]        dp_sa1_ar;        // sa dep on retire tag for sa
reg  [`npuarc_DP_POST_RANGE]         dp_sa2_ar;        // sa dep on retire tag for x1
reg  [`npuarc_DP_POST_RANGE]         dp_x1_ar;         // x1 dependence on retire tag
reg  [`npuarc_DP_POST_RANGE]         dp_x2_ar;         // x2 dependence on retire tag
reg  [`npuarc_DP_POST_RANGE]         dp_x3_ar;         // x3 dependence on retire tag
reg  [`npuarc_DP_POST_RANGE]         dp_ca_ar;         // ca dependence on retire tag

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Signal vectors at second-stage of dependency pipeline, derived from the  //
// dependency pipeline registers during the cycle in which those signals    //
// are used to detect stalls and enable register bypass paths.              //
// These vectors are qualified by gating dependencies with write-enables    //
// where they may be modified since stage 1 of the dependency calculation.  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
//
reg   [`npuarc_PRE_RAW_RANGE]        qd_sa_x1;         // qualifed sa dep. on x1
reg   [`npuarc_PRE_RAW_RANGE]        qd_sa_x2;         // qualifed sa dep. on x2
reg   [`npuarc_PRE_RAW_RANGE]        qd_sa_x3;         // qualifed sa dep. on x3
reg   [`npuarc_PRE_RAW_RANGE]        qd_sa_ca;         // qualifed sa dep. on ca
reg   [`npuarc_PRE_RAW_RANGE]        qd_sa_wa;         // qualifed sa dep. on wa
reg   [`npuarc_POST_RAW_RANGE]       qd_sa_ar0;        // qualifed sa dep. on ar0
reg   [`npuarc_POST_RAW_RANGE]       qd_sa_ar1;        // qualifed sa dep. on ar1
reg   [`npuarc_POST_RAW_RANGE]       qd_sa_ar2;        // qualifed sa dep. on ar2
reg   [`npuarc_POST_RAW_RANGE]       qd_sa_ar3;        // qualifed sa dep. on ar3
reg   [`npuarc_POST_RAW_RANGE]       qd_sa_ar4;        // qualifed sa dep. on ar4
reg   [`npuarc_POST_RAW_RANGE]       qd_sa_ar5;        // qualifed sa dep. on ar5
reg   [`npuarc_POST_RAW_RANGE]       qd_sa_ar6;        // qualifed sa dep. on ar6
reg   [`npuarc_POST_RAW_RANGE]       qd_sa_ar7;        // qualifed sa dep. on ar7

reg   [`npuarc_PRE_RAW_RANGE]        qd_x1_x2;         // qualifed x1 dep. on x2
reg   [`npuarc_PRE_RAW_RANGE]        qd_x1_x3;         // qualifed x1 dep. on x3
reg   [`npuarc_PRE_RAW_RANGE]        qd_x1_ca;         // qualifed x1 dep. on ca
reg   [`npuarc_PRE_RAW_RANGE]        qd_x1_wa;         // qualifed x1 dep. on wa

reg   [`npuarc_PRE_RAW_RANGE]        qd_x2_x3;         // qualifed x2 dep. on x3
reg   [`npuarc_PRE_RAW_RANGE]        qd_x2_ca;         // qualifed x2 dep. on ca
reg   [`npuarc_PRE_RAW_RANGE]        qd_x2_wa;         // qualifed x2 dep. on wa

reg   [`npuarc_PRE_RAW_RANGE]        qd_x3_ca;         // qualifed x3 dep. on ca
reg   [`npuarc_PRE_RAW_RANGE]        qd_x3_wa;         // qualifed x3 dep. on wa

reg   [`npuarc_PRE_RAW_RANGE]        qd_ca_wa;         // qualifed ca dep. on wa

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Signal vectors at second-stage of dependency pipeline, derived from the  //
// dependency pipeline registers during the cycle in which those signals    //
// are used to detect stalls and enable register bypass paths.              //
// As 64-bit operands are supported, these vectors are expanded versions of //
// the dp_xx_yy_r pipelined vectors, representing the dependencies between  //
// all combinations of low and high 32-bit halves of each 64-bit operand.   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
//
// leda NTL_CON12A off
// LMD: undriven internal net Range:
// leda NTL_CON13A off
// LMD: non driving internal net Range: ...
// LJ:  some bits are not used
// spyglass disable_block W497
// SMD: non driving bits in signals
// SJ:  some bits are not used
reg   [`npuarc_S2_PRE_RANGE]         fd_sa_x1;         // full sa dependency on x1
reg   [`npuarc_S2_PRE_RANGE]         fd_sa_x2;         // full sa dependencies on x2
reg   [`npuarc_S2_PRE_RANGE]         fd_sa_x3;         // full sa dependencies on x3
reg   [`npuarc_S2_PRE_RANGE]         fd_sa_ca;         // full sa dependencies on ca
reg   [`npuarc_S2_PRE_RANGE]         fd_sa_wa;         // full sa dependencies on wa

reg   [`npuarc_S2_PRE_RANGE]         fd_x1_x2;         // full x1 dependencies on x2
reg   [`npuarc_S2_PRE_RANGE]         fd_x1_x3;         // full x1 dependencies on x3

reg   [`npuarc_S2_PRE_RANGE]         fd_x1_ca;         // full x1 dependencies on ca
reg   [`npuarc_S2_PRE_RANGE]         fd_x1_wa;         // full x1 dependencies on wa

reg   [`npuarc_S2_PRE_RANGE]         fd_x2_x3;         // full x2 dependencies on x3
reg   [`npuarc_S2_PRE_RANGE]         fd_x2_ca;         // full x2 dependencies on ca
reg   [`npuarc_S2_PRE_RANGE]         fd_x2_wa;         // full x2 dependencies on wa

reg   [`npuarc_S2_PRE_RANGE]         fd_x3_ca;         // full x3 dependencies on ca
reg   [`npuarc_S2_PRE_RANGE]         fd_x3_wa;         // full x3 dependencies on wa

reg   [`npuarc_S2_PRE_RANGE]         fd_ca_wa;         // full ca dependencies on wa
// leda NTL_CON13A on
// leda NTL_CON12A on
// spyglass enable_block W497
//////////////////////////////////////////////////////////////////////////////
// Conditional dependency kill signals                                       //
//////////////////////////////////////////////////////////////////////////////
//
reg   [`npuarc_DP_KILL_RANGE]        x1_kill_x2;       // x1 defs that kill x2 defs
reg   [`npuarc_DP_KILL_RANGE]        x1_kill_x3;       // x1 defs that kill x3 defs
reg   [`npuarc_DP_KILL_RANGE]        x1_kill_ca;       // x1 defs that kill ca defs
reg   [`npuarc_DP_KILL_RANGE]        x1_kill_wa;       // x1 defs that kill wa defs
reg   [`npuarc_KL_RANGE_HI]          x1_kill_ar0;      // x1 defs that kill ar0 defs
reg   [`npuarc_KL_RANGE_HI]          x1_kill_ar1;      // x1 defs that kill ar1 defs
reg   [`npuarc_KL_RANGE_HI]          x1_kill_ar2;      // x1 defs that kill ar2 defs
reg   [`npuarc_KL_RANGE_HI]          x1_kill_ar3;      // x1 defs that kill ar3 defs
reg   [`npuarc_KL_RANGE_HI]          x1_kill_ar4;      // x1 defs that kill ar4 defs
reg   [`npuarc_KL_RANGE_HI]          x1_kill_ar5;      // x1 defs that kill ar5 defs
reg   [`npuarc_KL_RANGE_HI]          x1_kill_ar6;      // x1 defs that kill ar6 defs
reg   [`npuarc_KL_RANGE_HI]          x1_kill_ar7;      // x1 defs that kill ar7 defs
//
reg   [`npuarc_DP_KILL_RANGE]        x2_kill_x3;       // x2 defs that kill x3 defs
reg   [`npuarc_DP_KILL_RANGE]        x2_kill_ca;       // x2 defs that kill ca defs
reg   [`npuarc_DP_KILL_RANGE]        x2_kill_wa;       // x2 defs that kill wa defs
reg   [`npuarc_KL_RANGE_HI]          x2_kill_ar0;      // x2 defs that kill ar0 defs
reg   [`npuarc_KL_RANGE_HI]          x2_kill_ar1;      // x2 defs that kill ar1 defs
reg   [`npuarc_KL_RANGE_HI]          x2_kill_ar2;      // x2 defs that kill ar2 defs
reg   [`npuarc_KL_RANGE_HI]          x2_kill_ar3;      // x2 defs that kill ar3 defs
reg   [`npuarc_KL_RANGE_HI]          x2_kill_ar4;      // x2 defs that kill ar4 defs
reg   [`npuarc_KL_RANGE_HI]          x2_kill_ar5;      // x2 defs that kill ar5 defs
reg   [`npuarc_KL_RANGE_HI]          x2_kill_ar6;      // x2 defs that kill ar6 defs
reg   [`npuarc_KL_RANGE_HI]          x2_kill_ar7;      // x2 defs that kill ar7 defs
//
reg   [`npuarc_DP_KILL_RANGE]        x3_kill_ca;       // x3 defs that kill ca defs
reg   [`npuarc_DP_KILL_RANGE]        x3_kill_wa;       // x3 defs that kill wa defs
reg   [`npuarc_KL_RANGE_HI]          x3_kill_ar0;      // x3 defs that kill ar0 defs
reg   [`npuarc_KL_RANGE_HI]          x3_kill_ar1;      // x3 defs that kill ar1 defs
reg   [`npuarc_KL_RANGE_HI]          x3_kill_ar2;      // x3 defs that kill ar2 defs
reg   [`npuarc_KL_RANGE_HI]          x3_kill_ar3;      // x3 defs that kill ar3 defs
reg   [`npuarc_KL_RANGE_HI]          x3_kill_ar4;      // x3 defs that kill ar4 defs
reg   [`npuarc_KL_RANGE_HI]          x3_kill_ar5;      // x3 defs that kill ar5 defs
reg   [`npuarc_KL_RANGE_HI]          x3_kill_ar6;      // x3 defs that kill ar6 defs
reg   [`npuarc_KL_RANGE_HI]          x3_kill_ar7;      // x3 defs that kill ar7 defs
//
reg   [`npuarc_DP_KILL_RANGE]        ca_kill_wa;       // ca defs that kill wa defs
reg   [`npuarc_KL_RANGE_HI]          ca_kill_ar0;      // ca defs that kill ar0 defs
reg   [`npuarc_KL_RANGE_HI]          ca_kill_ar1;      // ca defs that kill ar1 defs
reg   [`npuarc_KL_RANGE_HI]          ca_kill_ar2;      // ca defs that kill ar2 defs
reg   [`npuarc_KL_RANGE_HI]          ca_kill_ar3;      // ca defs that kill ar3 defs
reg   [`npuarc_KL_RANGE_HI]          ca_kill_ar4;      // ca defs that kill ar4 defs
reg   [`npuarc_KL_RANGE_HI]          ca_kill_ar5;      // ca defs that kill ar5 defs
reg   [`npuarc_KL_RANGE_HI]          ca_kill_ar6;      // ca defs that kill ar6 defs
reg   [`npuarc_KL_RANGE_HI]          ca_kill_ar7;      // ca defs that kill ar7 defs

//////////////////////////////////////////////////////////////////////////////
// Conditional reachability of downstream definitions at each stage         //
//////////////////////////////////////////////////////////////////////////////

// leda NTL_CON12A off
// leda NTL_CON13A off
// LMD: undriven internal net
// LJ: usage of signals is configuration-dependent, not all used in all cases
reg   [`npuarc_DP_KILL_RANGE]        sa_sees_x2;       // x2 defs will reach sa
reg   [`npuarc_DP_KILL_RANGE]        sa_sees_x3;       // x3 defs will reach sa
reg   [`npuarc_DP_KILL_RANGE]        sa_sees_ca;       // ca defs will reach sa
reg   [`npuarc_DP_KILL_RANGE]        sa_sees_wa;       // wa defs will reach sa 
reg   [`npuarc_KL_RANGE_HI]          sa_sees_ar0;      // ar0 defs will reach sa
reg   [`npuarc_KL_RANGE_HI]          sa_sees_ar1;      // ar1 defs will reach sa
reg   [`npuarc_KL_RANGE_HI]          sa_sees_ar2;      // ar2 defs will reach sa
reg   [`npuarc_KL_RANGE_HI]          sa_sees_ar3;      // ar3 defs will reach sa
reg   [`npuarc_KL_RANGE_HI]          sa_sees_ar4;      // ar4 defs will reach sa
reg   [`npuarc_KL_RANGE_HI]          sa_sees_ar5;      // ar5 defs will reach sa
reg   [`npuarc_KL_RANGE_HI]          sa_sees_ar6;      // ar6 defs will reach sa
reg   [`npuarc_KL_RANGE_HI]          sa_sees_ar7;      // ar7 defs will reach sa
// leda NTL_CON12A on
// leda NTL_CON13A on
//////////////////////////////////////////////////////////////////////////////
// Reaching dependency signals, uniquified and conditionalized              //
//////////////////////////////////////////////////////////////////////////////
//
reg   [`npuarc_PRE_RAW_RANGE]        rd_sa_x1;         // final sa dependency on x1
reg   [`npuarc_PRE_RAW_RANGE]        rd_sa_x2;         // final sa dependency on x2
reg   [`npuarc_PRE_RAW_RANGE]        rd_sa_x3;         // final sa dependency on x3
reg   [`npuarc_PRE_RAW_RANGE]        rd_sa_ca;         // final sa dependency on ca
reg   [`npuarc_PRE_RAW_RANGE]        rd_sa_wa;         // final sa dependency on wa
reg   [`npuarc_POST_RAW_RANGE]       rd_sa_ar0;        // final sa dependency on ar0
reg   [`npuarc_POST_RAW_RANGE]       rd_sa_ar1;        // final sa dependency on ar1
reg   [`npuarc_POST_RAW_RANGE]       rd_sa_ar2;        // final sa dependency on ar2
reg   [`npuarc_POST_RAW_RANGE]       rd_sa_ar3;        // final sa dependency on ar3
reg   [`npuarc_POST_RAW_RANGE]       rd_sa_ar4;        // final sa dependency on ar4
reg   [`npuarc_POST_RAW_RANGE]       rd_sa_ar5;        // final sa dependency on ar5
reg   [`npuarc_POST_RAW_RANGE]       rd_sa_ar6;        // final sa dependency on ar6
reg   [`npuarc_POST_RAW_RANGE]       rd_sa_ar7;        // final sa dependency on ar7

//////////////////////////////////////////////////////////////////////////////
// Memory barrier and memory synchronization state for DMB and DSYNC insns  //
//////////////////////////////////////////////////////////////////////////////
//
reg                           ar_load_r;        // committed load is pending
reg                           x1_dsync_hold_r;  // 1=>stall DSYNC at SA
reg   [2:0]                   x1_dmb_hold_r;    // vector of DMB hold states
reg   [2:0]                   ar_mbf_r;         // vector of DMB hold states
//
reg                           ar_load_nxt;
reg                           x1_dsync_hold_nxt;
reg   [2:0]                   x1_dmb_hold_nxt;

reg   [2:0]                   set_ar_mbf;
reg   [2:0]                   clr_ar_mbf;

//
reg   [2:0]                   sa_mbf_vec;       // {ctrl,wr,rd} vector at SA
reg   [2:0]                   x1_mbf_vec;       // {ctrl,wr,rd} vector at X1
reg   [2:0]                   x2_mbf_vec;       // {ctrl,wr,rd} vector at X2
reg   [2:0]                   x3_mbf_vec;       // {ctrl,wr,rd} vector at X3
reg   [2:0]                   ca_mbf_vec;       // {ctrl,wr,rd} vector at CA
reg   [2:0]                   ar_mbf_vec;       // graduated {ctrl,wr,rd} vector
reg   [2:0]                   wa_mbf_vec;       // {ctrl,wr,rd} vector at WA

reg   [2:0]                   sa_mbf_sum;       // sum of vectors at SA
reg   [2:0]                   x1_mbf_sum;       // sum of vectors at X1
reg   [2:0]                   x2_mbf_sum;       // sum of vectors at X2
reg   [2:0]                   x3_mbf_sum;       // sum of vectors at X3
reg   [2:0]                   ca_mbf_sum;       // sum of vectors at CA
reg   [2:0]                   wa_mbf_sum;       // sum of vectors at WA
reg   [2:0]                   ar_mbf_sum;       // sum of vectors at AR
reg                           sa_dsync_stall;   // SA stall due to DSYNC
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic for DSYNC and DMB hold-condition states              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : dmb_dsync_PROC

  //==========================================================================
  // Each <xx>_mbf_vec signal is a vector of 3 bits to indicate whether there
  // is a valid aux write, memory store or memory load at stage <xx>.
  //
  sa_mbf_vec        = { sa_sr_op_r,         sa_store_r,       sa_load_r };
  x1_mbf_vec        = { x1_sr_op_r,         x1_store_r,       x1_load_r };
  x2_mbf_vec        = { x2_sr_op_r,         x2_store_r,       x2_load_r };
  x3_mbf_vec        = { x3_sr_op_r,         x3_store_r,       x3_load_r };
  ca_mbf_vec        = { ca_sr_op_r,         ca_store_r,       ca_load_r };
  wa_mbf_vec        = { wa_sr_op_r,         wa_store_r,       wa_load_r };
  ar_mbf_vec        = { dmp_aux_pending_r,  dmp_wr_pending_r, ar_load_r };

  //==========================================================================
  // Each <xx>_mbf_sum signal is a vector of 3 bits to indicate whether there
  // will be a valid aux write, memory store or memory load at any stage that
  // is downstream of stage <xx>, in the next cycle.
  //
  ar_mbf_sum        = ar_mbf_r                     | ar_mbf_vec;
  wa_mbf_sum        = wa_mbf_vec                   | ar_mbf_sum;
  ca_mbf_sum        = ({3{~ca_kill}} & ca_mbf_vec) | wa_mbf_sum;
  x3_mbf_sum        = ({3{~x3_kill}} & x3_mbf_vec) | ca_mbf_sum;
  x2_mbf_sum        = ({3{~x2_kill}} & x2_mbf_vec) | x3_mbf_sum;
  x1_mbf_sum        = ({3{~x1_kill}} & x1_mbf_vec) | x2_mbf_sum;
  sa_mbf_sum        = ({3{ sa_pass}} & sa_mbf_vec) | x1_mbf_sum;

  //==========================================================================
  // x1_dsync_hold_nxt is set to 1 if there will be any valid aux write,
  // memory store or memory load at any stage from X1 to CA, or which has
  // graduated and not yet retired, in the next cycle. Otherwise, it is cleared.
  //
  x1_dsync_hold_nxt = |sa_mbf_sum;

  //==========================================================================
  // x1_dmb_hold_nxt is a vector of 3 bits, with each bit carrying DMB hold
  // information for valid aux write, memory store or memory load operations.
  // Each bit is set to 1 if, in the next cycle, there will be a corresponding
  // operation type downstream of a DMB instruction for which the bit for that
  // operation type is set to 1 in that dmb instruction's u3 operand field.
  //
  x1_dmb_hold_nxt   = ({3{sa_dmb_op_r &   sa_pass }} & sa_dmb_type_r & x1_mbf_sum)
                    | ({3{x1_dmb_op_r & (~x1_kill)}} & x1_dmb_type_r & x2_mbf_sum)
                    | ({3{x2_dmb_op_r & (~x2_kill)}} & x2_dmb_type_r & x3_mbf_sum)
                    | ({3{x3_dmb_op_r & (~x3_kill)}} & x3_dmb_type_r & ca_mbf_sum)
                    | ({3{ca_dmb_op_r & (~ca_kill)}} & ca_dmb_type_r & wa_mbf_sum)
                    | ar_mbf_r
                    ;

  set_ar_mbf        = (wa_mbf_vec | ar_mbf_vec)
                    & ca_dmb_type_r
                    & {3{ca_dmb_op_r & ca_pass}}
                    ;

  clr_ar_mbf        = ~ar_mbf_vec;

  sa_dsync_stall    = sa_dsync_op_r & x1_dsync_hold_r;

  sa_dmb_stall      = |(sa_mbf_vec & x1_dmb_hold_r);

end // dmb_dsync_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sequential process definining the flip-flops for DSYNC and DMB registers //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : dmb_dsync_regs_PROC

  if (rst_a == 1'b1)
    begin
    x1_dsync_hold_r <= 1'b0;
    x1_dmb_hold_r   <= 3'd0;
    ar_load_r       <= 1'b0;
    ar_mbf_r        <= 3'd0;
    end
  else
    begin
    ar_load_r       <= ar_load_nxt;
    x1_dsync_hold_r <= x1_dsync_hold_nxt;
    x1_dmb_hold_r   <= x1_dmb_hold_nxt;
    ar_mbf_r        <= set_ar_mbf | (ar_mbf_r & (~clr_ar_mbf));
    end

end // dmb_dsync_regs_PROC



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic for stage 2 of the dependency pipeline               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : s2_dep_PROC

  //==========================================================================
  // For each graduation buffer entry create a signal that indicates whether
  // its entry is enabled to write.
  //
  ar0_rf_wenbs = ar0_rf_wenb1_r | ar0_rf_wenb1_64_r;
  ar1_rf_wenbs = ar1_rf_wenb1_r | ar1_rf_wenb1_64_r;
  ar2_rf_wenbs = ar2_rf_wenb1_r | ar2_rf_wenb1_64_r;
  ar3_rf_wenbs = ar3_rf_wenb1_r | ar3_rf_wenb1_64_r;
  ar4_rf_wenbs = ar4_rf_wenb1_r | ar4_rf_wenb1_64_r;
  ar5_rf_wenbs = ar5_rf_wenb1_r | ar5_rf_wenb1_64_r;
  ar6_rf_wenbs = ar6_rf_wenb1_r | ar6_rf_wenb1_64_r;
  ar7_rf_wenbs = ar7_rf_wenb1_r | ar7_rf_wenb1_64_r;


  x1_kill_x2  = {dp_x1_x2_r[`npuarc_DP_KL_W1], dp_x1_x2_r[`npuarc_DP_KL_W0]};
  x1_kill_x3  = {dp_x1_x3_r[`npuarc_DP_KL_W1], dp_x1_x3_r[`npuarc_DP_KL_W0]};
  x1_kill_ca  = {dp_x1_ca_r[`npuarc_DP_KL_W1], dp_x1_ca_r[`npuarc_DP_KL_W0]};
  x1_kill_wa  = {dp_x1_wa_r[`npuarc_DP_KL_W1], dp_x1_wa_r[`npuarc_DP_KL_W0]};
  x1_kill_ar0 = {dp_x1_ar0_r[`npuarc_DP_KL_W1]};
  x1_kill_ar1 = {dp_x1_ar1_r[`npuarc_DP_KL_W1]};
  x1_kill_ar2 = {dp_x1_ar2_r[`npuarc_DP_KL_W1]};
  x1_kill_ar3 = {dp_x1_ar3_r[`npuarc_DP_KL_W1]};
  x1_kill_ar4 = {dp_x1_ar4_r[`npuarc_DP_KL_W1]};
  x1_kill_ar5 = {dp_x1_ar5_r[`npuarc_DP_KL_W1]};
  x1_kill_ar6 = {dp_x1_ar6_r[`npuarc_DP_KL_W1]};
  x1_kill_ar7 = {dp_x1_ar7_r[`npuarc_DP_KL_W1]};

  x2_kill_x3  = {dp_x2_x3_r[`npuarc_DP_KL_W1], dp_x2_x3_r[`npuarc_DP_KL_W0]};
  x2_kill_ca  = {dp_x2_ca_r[`npuarc_DP_KL_W1], dp_x2_ca_r[`npuarc_DP_KL_W0]};
  x2_kill_wa  = {dp_x2_wa_r[`npuarc_DP_KL_W1], dp_x2_wa_r[`npuarc_DP_KL_W0]};
  x2_kill_ar0 = {dp_x2_ar0_r[`npuarc_DP_KL_W1]};
  x2_kill_ar1 = {dp_x2_ar1_r[`npuarc_DP_KL_W1]};
  x2_kill_ar2 = {dp_x2_ar2_r[`npuarc_DP_KL_W1]};
  x2_kill_ar3 = {dp_x2_ar3_r[`npuarc_DP_KL_W1]};
  x2_kill_ar4 = {dp_x2_ar4_r[`npuarc_DP_KL_W1]};
  x2_kill_ar5 = {dp_x2_ar5_r[`npuarc_DP_KL_W1]};
  x2_kill_ar6 = {dp_x2_ar6_r[`npuarc_DP_KL_W1]};
  x2_kill_ar7 = {dp_x2_ar7_r[`npuarc_DP_KL_W1]};

  x3_kill_ca  = {dp_x3_ca_r[`npuarc_DP_KL_W1], dp_x3_ca_r[`npuarc_DP_KL_W0]};
  x3_kill_wa  = {dp_x3_wa_r[`npuarc_DP_KL_W1], dp_x3_wa_r[`npuarc_DP_KL_W0]};
  x3_kill_ar0 = {dp_x3_ar0_r[`npuarc_DP_KL_W1]};
  x3_kill_ar1 = {dp_x3_ar1_r[`npuarc_DP_KL_W1]};
  x3_kill_ar2 = {dp_x3_ar2_r[`npuarc_DP_KL_W1]};
  x3_kill_ar3 = {dp_x3_ar3_r[`npuarc_DP_KL_W1]};
  x3_kill_ar4 = {dp_x3_ar4_r[`npuarc_DP_KL_W1]};
  x3_kill_ar5 = {dp_x3_ar5_r[`npuarc_DP_KL_W1]};
  x3_kill_ar6 = {dp_x3_ar6_r[`npuarc_DP_KL_W1]};
  x3_kill_ar7 = {dp_x3_ar7_r[`npuarc_DP_KL_W1]};

  ca_kill_wa  = {dp_ca_wa_r[`npuarc_DP_KL_W1], dp_ca_wa_r[`npuarc_DP_KL_W0]};
  ca_kill_ar0 = {dp_ca_ar0_r[`npuarc_DP_KL_W1]};
  ca_kill_ar1 = {dp_ca_ar1_r[`npuarc_DP_KL_W1]};
  ca_kill_ar2 = {dp_ca_ar2_r[`npuarc_DP_KL_W1]};
  ca_kill_ar3 = {dp_ca_ar3_r[`npuarc_DP_KL_W1]};
  ca_kill_ar4 = {dp_ca_ar4_r[`npuarc_DP_KL_W1]};
  ca_kill_ar5 = {dp_ca_ar5_r[`npuarc_DP_KL_W1]};
  ca_kill_ar6 = {dp_ca_ar6_r[`npuarc_DP_KL_W1]};
  ca_kill_ar7 = {dp_ca_ar7_r[`npuarc_DP_KL_W1]};

  sa_sees_x2  = ~(x1_kill_x2);
  sa_sees_x3  = ~(x1_kill_x3  | x2_kill_x3);
  sa_sees_ca  = ~(x1_kill_ca  | x2_kill_ca  | x3_kill_ca);
  sa_sees_wa  = ~(x1_kill_wa  | x2_kill_wa  | x3_kill_wa  | ca_kill_wa);
  sa_sees_ar0 = ~(x1_kill_ar0 | x2_kill_ar0 | x3_kill_ar0 | ca_kill_ar0);
  sa_sees_ar1 = ~(x1_kill_ar1 | x2_kill_ar1 | x3_kill_ar1 | ca_kill_ar1);
  sa_sees_ar2 = ~(x1_kill_ar2 | x2_kill_ar2 | x3_kill_ar2 | ca_kill_ar2);
  sa_sees_ar3 = ~(x1_kill_ar3 | x2_kill_ar3 | x3_kill_ar3 | ca_kill_ar3);
  sa_sees_ar4 = ~(x1_kill_ar4 | x2_kill_ar4 | x3_kill_ar4 | ca_kill_ar4);
  sa_sees_ar5 = ~(x1_kill_ar5 | x2_kill_ar5 | x3_kill_ar5 | ca_kill_ar5);
  sa_sees_ar6 = ~(x1_kill_ar6 | x2_kill_ar6 | x3_kill_ar6 | ca_kill_ar6);
  sa_sees_ar7 = ~(x1_kill_ar7 | x2_kill_ar7 | x3_kill_ar7 | ca_kill_ar7);

  //==========================================================================
  // Compute the qualified dependency signals at the start of stage 2.
  //
  qd_sa_x1  = dp_sa_x1_r;
  qd_sa_x2  = dp_sa_x2_r;
  qd_sa_x3  = dp_sa_x3_r;
  qd_sa_ca  = dp_sa_ca_r;
  qd_sa_wa  = dp_sa_wa_r;
  qd_sa_ar0 = dp_sa_ar0_r & {`npuarc_POST_RAW_BITS{ar0_rf_wenbs}};
  qd_sa_ar1 = dp_sa_ar1_r & {`npuarc_POST_RAW_BITS{ar1_rf_wenbs}};
  qd_sa_ar2 = dp_sa_ar2_r & {`npuarc_POST_RAW_BITS{ar2_rf_wenbs}};
  qd_sa_ar3 = dp_sa_ar3_r & {`npuarc_POST_RAW_BITS{ar3_rf_wenbs}};
  qd_sa_ar4 = dp_sa_ar4_r & {`npuarc_POST_RAW_BITS{ar4_rf_wenbs}};
  qd_sa_ar5 = dp_sa_ar5_r & {`npuarc_POST_RAW_BITS{ar5_rf_wenbs}};
  qd_sa_ar6 = dp_sa_ar6_r & {`npuarc_POST_RAW_BITS{ar6_rf_wenbs}};
  qd_sa_ar7 = dp_sa_ar7_r & {`npuarc_POST_RAW_BITS{ar7_rf_wenbs}};

  qd_x1_x2  = dp_x1_x2_r[`npuarc_PRE_RAW_RANGE];
  qd_x1_x3  = dp_x1_x3_r[`npuarc_PRE_RAW_RANGE];
  qd_x1_ca  = dp_x1_ca_r[`npuarc_PRE_RAW_RANGE];
  qd_x1_wa  = dp_x1_wa_r[`npuarc_PRE_RAW_RANGE];

  qd_x2_x3  = dp_x2_x3_r[`npuarc_PRE_RAW_RANGE];
  qd_x2_ca  = dp_x2_ca_r[`npuarc_PRE_RAW_RANGE];
  qd_x2_wa  = dp_x2_wa_r[`npuarc_PRE_RAW_RANGE];

  qd_x3_ca  = dp_x3_ca_r[`npuarc_PRE_RAW_RANGE];
  qd_x3_wa  = dp_x3_wa_r[`npuarc_PRE_RAW_RANGE];

  qd_ca_wa  = dp_ca_wa_r[`npuarc_PRE_RAW_RANGE];

  //==========================================================================
  // Gate each actual dependence with its reachability from the point of
  // definition to the current point of reference. These rd_xx_yy vectors
  // represent fully-qualified read-after-write dependencies from stage yy
  // to stage xx.
  //
  rd_sa_x1[`npuarc_LR0_LW0] = qd_sa_x1[`npuarc_LR0_LW0];
  rd_sa_x1[`npuarc_LR0_LW1] = qd_sa_x1[`npuarc_LR0_LW1];
  rd_sa_x1[`npuarc_LR1_LW0] = qd_sa_x1[`npuarc_LR1_LW0];
  rd_sa_x1[`npuarc_LR1_LW1] = qd_sa_x1[`npuarc_LR1_LW1];

  rd_sa_x2[`npuarc_LR0_LW0] = qd_sa_x2[`npuarc_LR0_LW0] & sa_sees_x2[`npuarc_K_W0_LO];
  rd_sa_x2[`npuarc_LR0_LW1] = qd_sa_x2[`npuarc_LR0_LW1] & sa_sees_x2[`npuarc_K_W1_LO];
  rd_sa_x2[`npuarc_LR1_LW0] = qd_sa_x2[`npuarc_LR1_LW0] & sa_sees_x2[`npuarc_K_W0_LO];
  rd_sa_x2[`npuarc_LR1_LW1] = qd_sa_x2[`npuarc_LR1_LW1] & sa_sees_x2[`npuarc_K_W1_LO];

  rd_sa_x3[`npuarc_LR0_LW0] = qd_sa_x3[`npuarc_LR0_LW0] & sa_sees_x3[`npuarc_K_W0_LO];
  rd_sa_x3[`npuarc_LR0_LW1] = qd_sa_x3[`npuarc_LR0_LW1] & sa_sees_x3[`npuarc_K_W1_LO];
  rd_sa_x3[`npuarc_LR1_LW0] = qd_sa_x3[`npuarc_LR1_LW0] & sa_sees_x3[`npuarc_K_W0_LO];
  rd_sa_x3[`npuarc_LR1_LW1] = qd_sa_x3[`npuarc_LR1_LW1] & sa_sees_x3[`npuarc_K_W1_LO];

  rd_sa_ca[`npuarc_LR0_LW0] = qd_sa_ca[`npuarc_LR0_LW0] & sa_sees_ca[`npuarc_K_W0_LO];
  rd_sa_ca[`npuarc_LR0_LW1] = qd_sa_ca[`npuarc_LR0_LW1] & sa_sees_ca[`npuarc_K_W1_LO];
  rd_sa_ca[`npuarc_LR1_LW0] = qd_sa_ca[`npuarc_LR1_LW0] & sa_sees_ca[`npuarc_K_W0_LO];
  rd_sa_ca[`npuarc_LR1_LW1] = qd_sa_ca[`npuarc_LR1_LW1] & sa_sees_ca[`npuarc_K_W1_LO];

  rd_sa_wa[`npuarc_LR0_LW0] = qd_sa_wa[`npuarc_LR0_LW0] & sa_sees_wa[`npuarc_K_W0_LO];
  rd_sa_wa[`npuarc_LR0_LW1] = qd_sa_wa[`npuarc_LR0_LW1] & sa_sees_wa[`npuarc_K_W1_LO];
  rd_sa_wa[`npuarc_LR1_LW0] = qd_sa_wa[`npuarc_LR1_LW0] & sa_sees_wa[`npuarc_K_W0_LO];
  rd_sa_wa[`npuarc_LR1_LW1] = qd_sa_wa[`npuarc_LR1_LW1] & sa_sees_wa[`npuarc_K_W1_LO];

  rd_sa_ar0[`npuarc_LR0_LW1] = qd_sa_ar0[`npuarc_LR0_LW1] & sa_sees_ar0[`npuarc_K_W1_LO];
  rd_sa_ar0[`npuarc_LR1_LW1] = qd_sa_ar0[`npuarc_LR1_LW1] & sa_sees_ar0[`npuarc_K_W1_LO];

  rd_sa_ar1[`npuarc_LR0_LW1] = qd_sa_ar1[`npuarc_LR0_LW1] & sa_sees_ar1[`npuarc_K_W1_LO];
  rd_sa_ar1[`npuarc_LR1_LW1] = qd_sa_ar1[`npuarc_LR1_LW1] & sa_sees_ar1[`npuarc_K_W1_LO];

  rd_sa_ar2[`npuarc_LR0_LW1] = qd_sa_ar2[`npuarc_LR0_LW1] & sa_sees_ar2[`npuarc_K_W1_LO];
  rd_sa_ar2[`npuarc_LR1_LW1] = qd_sa_ar2[`npuarc_LR1_LW1] & sa_sees_ar2[`npuarc_K_W1_LO];

  rd_sa_ar3[`npuarc_LR0_LW1] = qd_sa_ar3[`npuarc_LR0_LW1] & sa_sees_ar3[`npuarc_K_W1_LO];
  rd_sa_ar3[`npuarc_LR1_LW1] = qd_sa_ar3[`npuarc_LR1_LW1] & sa_sees_ar3[`npuarc_K_W1_LO];

  rd_sa_ar4[`npuarc_LR0_LW1] = qd_sa_ar4[`npuarc_LR0_LW1] & sa_sees_ar4[`npuarc_K_W1_LO];
  rd_sa_ar4[`npuarc_LR1_LW1] = qd_sa_ar4[`npuarc_LR1_LW1] & sa_sees_ar4[`npuarc_K_W1_LO];

  rd_sa_ar5[`npuarc_LR0_LW1] = qd_sa_ar5[`npuarc_LR0_LW1] & sa_sees_ar5[`npuarc_K_W1_LO];
  rd_sa_ar5[`npuarc_LR1_LW1] = qd_sa_ar5[`npuarc_LR1_LW1] & sa_sees_ar5[`npuarc_K_W1_LO];

  rd_sa_ar6[`npuarc_LR0_LW1] = qd_sa_ar6[`npuarc_LR0_LW1] & sa_sees_ar6[`npuarc_K_W1_LO];
  rd_sa_ar6[`npuarc_LR1_LW1] = qd_sa_ar6[`npuarc_LR1_LW1] & sa_sees_ar6[`npuarc_K_W1_LO];

  rd_sa_ar7[`npuarc_LR0_LW1] = qd_sa_ar7[`npuarc_LR0_LW1] & sa_sees_ar7[`npuarc_K_W1_LO];
  rd_sa_ar7[`npuarc_LR1_LW1] = qd_sa_ar7[`npuarc_LR1_LW1] & sa_sees_ar7[`npuarc_K_W1_LO];


  //==========================================================================
  // Expand the dependency signals for each pipeline stage to track mixed
  // 32 and 64-bit source and destination register uses and definitions.
  //
  fd_sa_x1[`npuarc_LR0_LW0] = rd_sa_x1[`npuarc_R0_W0] & (sa_rf_ra0_r[0] == x1_rf_wa0_r[0]);
  fd_sa_x1[`npuarc_HR0_LW0] = rd_sa_x1[`npuarc_R0_W0] & x1_rf_wa0_r[0] & sa_rf_renb0_64_r;
  fd_sa_x1[`npuarc_LR0_HW0] = rd_sa_x1[`npuarc_R0_W0] & sa_rf_ra0_r[0] & x1_rf_wenb0_64_r;
  fd_sa_x1[`npuarc_HR0_HW0] = rd_sa_x1[`npuarc_R0_W0] & x1_rf_wenb0_64_r & sa_rf_renb0_64_r;
  fd_sa_x1[`npuarc_LR0_LW1] = rd_sa_x1[`npuarc_R0_W1] & (sa_rf_ra0_r[0] == x1_rf_wa1_r[0]);
  fd_sa_x1[`npuarc_HR0_LW1] = rd_sa_x1[`npuarc_R0_W1] & x1_rf_wa1_r[0] & sa_rf_renb0_64_r;
  fd_sa_x1[`npuarc_LR0_HW1] = rd_sa_x1[`npuarc_R0_W1] & sa_rf_ra0_r[0] & x1_rf_wenb1_64_r;
  fd_sa_x1[`npuarc_HR0_HW1] = rd_sa_x1[`npuarc_R0_W1] & x1_rf_wenb1_64_r & sa_rf_renb0_64_r;
  fd_sa_x1[`npuarc_LR1_LW0] = rd_sa_x1[`npuarc_R1_W0] & (sa_rf_ra1_r[0] == x1_rf_wa0_r[0]);
  fd_sa_x1[`npuarc_HR1_LW0] = rd_sa_x1[`npuarc_R1_W0] & x1_rf_wa0_r[0] & sa_rf_renb1_64_r;
  fd_sa_x1[`npuarc_LR1_HW0] = rd_sa_x1[`npuarc_R1_W0] & sa_rf_ra1_r[0] & x1_rf_wenb0_64_r;
  fd_sa_x1[`npuarc_HR1_HW0] = rd_sa_x1[`npuarc_R1_W0] & x1_rf_wenb0_64_r & sa_rf_renb1_64_r;
  fd_sa_x1[`npuarc_LR1_LW1] = rd_sa_x1[`npuarc_R1_W1] & (sa_rf_ra1_r[0] == x1_rf_wa1_r[0]);
  fd_sa_x1[`npuarc_HR1_LW1] = rd_sa_x1[`npuarc_R1_W1] & x1_rf_wa1_r[0] & sa_rf_renb1_64_r;
  fd_sa_x1[`npuarc_LR1_HW1] = rd_sa_x1[`npuarc_R1_W1] & sa_rf_ra1_r[0] & x1_rf_wenb1_64_r;
  fd_sa_x1[`npuarc_HR1_HW1] = rd_sa_x1[`npuarc_R1_W1] & x1_rf_wenb1_64_r & sa_rf_renb1_64_r;

  fd_sa_x2[`npuarc_LR0_LW0] = rd_sa_x2[`npuarc_R0_W0] & (sa_rf_ra0_r[0] == x2_rf_wa0_r[0]);
  fd_sa_x2[`npuarc_HR0_LW0] = rd_sa_x2[`npuarc_R0_W0] & x2_rf_wa0_r[0] & sa_rf_renb0_64_r;
  fd_sa_x2[`npuarc_LR0_HW0] = rd_sa_x2[`npuarc_R0_W0] & sa_rf_ra0_r[0] & x2_rf_wenb0_64_r;
  fd_sa_x2[`npuarc_HR0_HW0] = rd_sa_x2[`npuarc_R0_W0] & x2_rf_wenb0_64_r & sa_rf_renb0_64_r;
  fd_sa_x2[`npuarc_LR0_LW1] = rd_sa_x2[`npuarc_R0_W1] & (sa_rf_ra0_r[0] == x2_rf_wa1_r[0]);
  fd_sa_x2[`npuarc_HR0_LW1] = rd_sa_x2[`npuarc_R0_W1] & x2_rf_wa1_r[0] & sa_rf_renb0_64_r;
  fd_sa_x2[`npuarc_LR0_HW1] = rd_sa_x2[`npuarc_R0_W1] & sa_rf_ra0_r[0] & x2_rf_wenb1_64_r;
  fd_sa_x2[`npuarc_HR0_HW1] = rd_sa_x2[`npuarc_R0_W1] & x2_rf_wenb1_64_r & sa_rf_renb0_64_r;
  fd_sa_x2[`npuarc_LR1_LW0] = rd_sa_x2[`npuarc_R1_W0] & (sa_rf_ra1_r[0] == x2_rf_wa0_r[0]);
  fd_sa_x2[`npuarc_HR1_LW0] = rd_sa_x2[`npuarc_R1_W0] & x2_rf_wa0_r[0] & sa_rf_renb1_64_r;
  fd_sa_x2[`npuarc_LR1_HW0] = rd_sa_x2[`npuarc_R1_W0] & sa_rf_ra1_r[0] & x2_rf_wenb0_64_r;
  fd_sa_x2[`npuarc_HR1_HW0] = rd_sa_x2[`npuarc_R1_W0] & x2_rf_wenb0_64_r & sa_rf_renb1_64_r;
  fd_sa_x2[`npuarc_LR1_LW1] = rd_sa_x2[`npuarc_R1_W1] & (sa_rf_ra1_r[0] == x2_rf_wa1_r[0]);
  fd_sa_x2[`npuarc_HR1_LW1] = rd_sa_x2[`npuarc_R1_W1] & x2_rf_wa1_r[0] & sa_rf_renb1_64_r;
  fd_sa_x2[`npuarc_LR1_HW1] = rd_sa_x2[`npuarc_R1_W1] & sa_rf_ra1_r[0] & x2_rf_wenb1_64_r;
  fd_sa_x2[`npuarc_HR1_HW1] = rd_sa_x2[`npuarc_R1_W1] & x2_rf_wenb1_64_r & sa_rf_renb1_64_r;

  fd_sa_x3[`npuarc_LR0_LW0] = rd_sa_x3[`npuarc_R0_W0] & (sa_rf_ra0_r[0] == x3_rf_wa0_r[0]);
  fd_sa_x3[`npuarc_HR0_LW0] = rd_sa_x3[`npuarc_R0_W0] & x3_rf_wa0_r[0] & sa_rf_renb0_64_r;
  fd_sa_x3[`npuarc_LR0_HW0] = rd_sa_x3[`npuarc_R0_W0] & sa_rf_ra0_r[0] & x3_rf_wenb0_64_r;
  fd_sa_x3[`npuarc_HR0_HW0] = rd_sa_x3[`npuarc_R0_W0] & x3_rf_wenb0_64_r & sa_rf_renb0_64_r;
  fd_sa_x3[`npuarc_LR0_LW1] = rd_sa_x3[`npuarc_R0_W1] & (sa_rf_ra0_r[0] == x3_rf_wa1_r[0]);
  fd_sa_x3[`npuarc_HR0_LW1] = rd_sa_x3[`npuarc_R0_W1] & x3_rf_wa1_r[0] & sa_rf_renb0_64_r;
  fd_sa_x3[`npuarc_LR0_HW1] = rd_sa_x3[`npuarc_R0_W1] & sa_rf_ra0_r[0] & x3_rf_wenb1_64_r;
  fd_sa_x3[`npuarc_HR0_HW1] = rd_sa_x3[`npuarc_R0_W1] & x3_rf_wenb1_64_r & sa_rf_renb0_64_r;
  fd_sa_x3[`npuarc_LR1_LW0] = rd_sa_x3[`npuarc_R1_W0] & (sa_rf_ra1_r[0] == x3_rf_wa0_r[0]);
  fd_sa_x3[`npuarc_HR1_LW0] = rd_sa_x3[`npuarc_R1_W0] & x3_rf_wa0_r[0] & sa_rf_renb1_64_r;
  fd_sa_x3[`npuarc_LR1_HW0] = rd_sa_x3[`npuarc_R1_W0] & sa_rf_ra1_r[0] & x3_rf_wenb0_64_r;
  fd_sa_x3[`npuarc_HR1_HW0] = rd_sa_x3[`npuarc_R1_W0] & x3_rf_wenb0_64_r & sa_rf_renb1_64_r;
  fd_sa_x3[`npuarc_LR1_LW1] = rd_sa_x3[`npuarc_R1_W1] & (sa_rf_ra1_r[0] == x3_rf_wa1_r[0]);
  fd_sa_x3[`npuarc_HR1_LW1] = rd_sa_x3[`npuarc_R1_W1] & x3_rf_wa1_r[0] & sa_rf_renb1_64_r;
  fd_sa_x3[`npuarc_LR1_HW1] = rd_sa_x3[`npuarc_R1_W1] & sa_rf_ra1_r[0] & x3_rf_wenb1_64_r;
  fd_sa_x3[`npuarc_HR1_HW1] = rd_sa_x3[`npuarc_R1_W1] & x3_rf_wenb1_64_r & sa_rf_renb1_64_r;

  fd_sa_ca[`npuarc_LR0_LW0] = rd_sa_ca[`npuarc_R0_W0] & (sa_rf_ra0_r[0] == ca_rf_wa0_r[0]);
  fd_sa_ca[`npuarc_HR0_LW0] = rd_sa_ca[`npuarc_R0_W0] & ca_rf_wa0_r[0] & sa_rf_renb0_64_r;
  fd_sa_ca[`npuarc_LR0_HW0] = rd_sa_ca[`npuarc_R0_W0] & sa_rf_ra0_r[0] & ca_rf_wenb0_64_r;
  fd_sa_ca[`npuarc_HR0_HW0] = rd_sa_ca[`npuarc_R0_W0] & ca_rf_wenb0_64_r & sa_rf_renb0_64_r;
  fd_sa_ca[`npuarc_LR0_LW1] = rd_sa_ca[`npuarc_R0_W1] & (sa_rf_ra0_r[0] == ca_rf_wa1_r[0]);
  fd_sa_ca[`npuarc_HR0_LW1] = rd_sa_ca[`npuarc_R0_W1] & ca_rf_wa1_r[0] & sa_rf_renb0_64_r;
  fd_sa_ca[`npuarc_LR0_HW1] = rd_sa_ca[`npuarc_R0_W1] & sa_rf_ra0_r[0] & ca_rf_wenb1_64_r;
  fd_sa_ca[`npuarc_HR0_HW1] = rd_sa_ca[`npuarc_R0_W1] & ca_rf_wenb1_64_r & sa_rf_renb0_64_r;
  fd_sa_ca[`npuarc_LR1_LW0] = rd_sa_ca[`npuarc_R1_W0] & (sa_rf_ra1_r[0] == ca_rf_wa0_r[0]);
  fd_sa_ca[`npuarc_HR1_LW0] = rd_sa_ca[`npuarc_R1_W0] & ca_rf_wa0_r[0] & sa_rf_renb1_64_r;
  fd_sa_ca[`npuarc_LR1_HW0] = rd_sa_ca[`npuarc_R1_W0] & sa_rf_ra1_r[0] & ca_rf_wenb0_64_r;
  fd_sa_ca[`npuarc_HR1_HW0] = rd_sa_ca[`npuarc_R1_W0] & ca_rf_wenb0_64_r & sa_rf_renb1_64_r;
  fd_sa_ca[`npuarc_LR1_LW1] = rd_sa_ca[`npuarc_R1_W1] & (sa_rf_ra1_r[0] == ca_rf_wa1_r[0]);
  fd_sa_ca[`npuarc_HR1_LW1] = rd_sa_ca[`npuarc_R1_W1] & ca_rf_wa1_r[0] & sa_rf_renb1_64_r;
  fd_sa_ca[`npuarc_LR1_HW1] = rd_sa_ca[`npuarc_R1_W1] & sa_rf_ra1_r[0] & ca_rf_wenb1_64_r;
  fd_sa_ca[`npuarc_HR1_HW1] = rd_sa_ca[`npuarc_R1_W1] & ca_rf_wenb1_64_r & sa_rf_renb1_64_r;

  fd_sa_wa[`npuarc_LR0_LW0] = rd_sa_wa[`npuarc_R0_W0] & (sa_rf_ra0_r[0] == wa_rf_wa0_r[0]);
  fd_sa_wa[`npuarc_HR0_LW0] = rd_sa_wa[`npuarc_R0_W0] & wa_rf_wa0_r[0] & sa_rf_renb0_64_r;
  fd_sa_wa[`npuarc_LR0_HW0] = rd_sa_wa[`npuarc_R0_W0] & sa_rf_ra0_r[0] & wa_dp_wenb0_64_r;
  fd_sa_wa[`npuarc_HR0_HW0] = rd_sa_wa[`npuarc_R0_W0] & wa_dp_wenb0_64_r & sa_rf_renb0_64_r;
  fd_sa_wa[`npuarc_LR0_LW1] = rd_sa_wa[`npuarc_R0_W1] 
                     & (sa_rf_ra0_r[0] == wa_rf_wa1_r[0])
                     & wa_rf_wenb1_r
                     ;
  fd_sa_wa[`npuarc_HR0_LW1] = rd_sa_wa[`npuarc_R0_W1] & wa_rf_wa1_r[0] & sa_rf_renb0_64_r;
  fd_sa_wa[`npuarc_LR0_HW1] = rd_sa_wa[`npuarc_R0_W1] & sa_rf_ra0_r[0] & wa_rf_wenb1_64_r;
  fd_sa_wa[`npuarc_HR0_HW1] = rd_sa_wa[`npuarc_R0_W1] & wa_rf_wenb1_64_r & sa_rf_renb0_64_r;
  fd_sa_wa[`npuarc_LR1_LW0] = rd_sa_wa[`npuarc_R1_W0] & (sa_rf_ra1_r[0] == wa_rf_wa0_r[0]);
  fd_sa_wa[`npuarc_HR1_LW0] = rd_sa_wa[`npuarc_R1_W0] & wa_rf_wa0_r[0] & sa_rf_renb1_64_r;
  fd_sa_wa[`npuarc_LR1_HW0] = rd_sa_wa[`npuarc_R1_W0] & sa_rf_ra1_r[0] & wa_dp_wenb0_64_r;
  fd_sa_wa[`npuarc_HR1_HW0] = rd_sa_wa[`npuarc_R1_W0] & wa_dp_wenb0_64_r & sa_rf_renb1_64_r;
  fd_sa_wa[`npuarc_LR1_LW1] = rd_sa_wa[`npuarc_R1_W1] 
                     & (sa_rf_ra1_r[0] == wa_rf_wa1_r[0])
                     & wa_rf_wenb1_r
                     ;
  fd_sa_wa[`npuarc_HR1_LW1] = rd_sa_wa[`npuarc_R1_W1] & wa_rf_wa1_r[0] & sa_rf_renb1_64_r;
  fd_sa_wa[`npuarc_LR1_HW1] = rd_sa_wa[`npuarc_R1_W1] & sa_rf_ra1_r[0] & wa_rf_wenb1_64_r;
  fd_sa_wa[`npuarc_HR1_HW1] = rd_sa_wa[`npuarc_R1_W1] & wa_rf_wenb1_64_r & sa_rf_renb1_64_r;

  fd_x1_x2[`npuarc_LR0_LW0] = qd_x1_x2[`npuarc_R0_W0] & (x1_rf_ra0_r[0] == x2_rf_wa0_r[0]);
  fd_x1_x2[`npuarc_HR0_LW0] = qd_x1_x2[`npuarc_R0_W0] & x2_rf_wa0_r[0] & x1_rf_renb0_64_r;
  fd_x1_x2[`npuarc_LR0_HW0] = qd_x1_x2[`npuarc_R0_W0] & x1_rf_ra0_r[0] & x2_rf_wenb0_64_r;
  fd_x1_x2[`npuarc_HR0_HW0] = qd_x1_x2[`npuarc_R0_W0] & x2_rf_wenb0_64_r & x1_rf_renb0_64_r;
  fd_x1_x2[`npuarc_LR0_LW1] = qd_x1_x2[`npuarc_R0_W1] & (x1_rf_ra0_r[0] == x2_rf_wa1_r[0]);
  fd_x1_x2[`npuarc_HR0_LW1] = qd_x1_x2[`npuarc_R0_W1] & x2_rf_wa1_r[0] & x1_rf_renb0_64_r;
  fd_x1_x2[`npuarc_LR0_HW1] = qd_x1_x2[`npuarc_R0_W1] & x1_rf_ra0_r[0] & x2_rf_wenb1_64_r;
  fd_x1_x2[`npuarc_HR0_HW1] = qd_x1_x2[`npuarc_R0_W1] & x2_rf_wenb1_64_r & x1_rf_renb0_64_r;
  fd_x1_x2[`npuarc_LR1_LW0] = qd_x1_x2[`npuarc_R1_W0] & (x1_rf_ra1_r[0] == x2_rf_wa0_r[0]);
  fd_x1_x2[`npuarc_HR1_LW0] = qd_x1_x2[`npuarc_R1_W0] & x2_rf_wa0_r[0] & x1_rf_renb1_64_r;
  fd_x1_x2[`npuarc_LR1_HW0] = qd_x1_x2[`npuarc_R1_W0] & x1_rf_ra1_r[0] & x2_rf_wenb0_64_r;
  fd_x1_x2[`npuarc_HR1_HW0] = qd_x1_x2[`npuarc_R1_W0] & x2_rf_wenb0_64_r & x1_rf_renb1_64_r;
  fd_x1_x2[`npuarc_LR1_LW1] = qd_x1_x2[`npuarc_R1_W1] & (x1_rf_ra1_r[0] == x2_rf_wa1_r[0]);
  fd_x1_x2[`npuarc_HR1_LW1] = qd_x1_x2[`npuarc_R1_W1] & x2_rf_wa1_r[0] & x1_rf_renb1_64_r;
  fd_x1_x2[`npuarc_LR1_HW1] = qd_x1_x2[`npuarc_R1_W1] & x1_rf_ra1_r[0] & x2_rf_wenb1_64_r;
  fd_x1_x2[`npuarc_HR1_HW1] = qd_x1_x2[`npuarc_R1_W1] & x2_rf_wenb1_64_r & x1_rf_renb1_64_r;

  fd_x1_x3[`npuarc_LR0_LW0] = qd_x1_x3[`npuarc_R0_W0] & (x1_rf_ra0_r[0] == x3_rf_wa0_r[0]);
  fd_x1_x3[`npuarc_HR0_LW0] = qd_x1_x3[`npuarc_R0_W0] & x3_rf_wa0_r[0] & x1_rf_renb0_64_r;
  fd_x1_x3[`npuarc_LR0_HW0] = qd_x1_x3[`npuarc_R0_W0] & x1_rf_ra0_r[0] & x3_rf_wenb0_64_r;
  fd_x1_x3[`npuarc_HR0_HW0] = qd_x1_x3[`npuarc_R0_W0] & x3_rf_wenb0_64_r & x1_rf_renb0_64_r;
  fd_x1_x3[`npuarc_LR0_LW1] = qd_x1_x3[`npuarc_R0_W1] & (x1_rf_ra0_r[0] == x3_rf_wa1_r[0]);
  fd_x1_x3[`npuarc_HR0_LW1] = qd_x1_x3[`npuarc_R0_W1] & x3_rf_wa1_r[0] & x1_rf_renb0_64_r;
  fd_x1_x3[`npuarc_LR0_HW1] = qd_x1_x3[`npuarc_R0_W1] & x1_rf_ra0_r[0] & x3_rf_wenb1_64_r;
  fd_x1_x3[`npuarc_HR0_HW1] = qd_x1_x3[`npuarc_R0_W1] & x3_rf_wenb1_64_r & x1_rf_renb0_64_r;
  fd_x1_x3[`npuarc_LR1_LW0] = qd_x1_x3[`npuarc_R1_W0] & (x1_rf_ra1_r[0] == x3_rf_wa0_r[0]);
  fd_x1_x3[`npuarc_HR1_LW0] = qd_x1_x3[`npuarc_R1_W0] & x3_rf_wa0_r[0] & x1_rf_renb1_64_r;
  fd_x1_x3[`npuarc_LR1_HW0] = qd_x1_x3[`npuarc_R1_W0] & x1_rf_ra1_r[0] & x3_rf_wenb0_64_r;
  fd_x1_x3[`npuarc_HR1_HW0] = qd_x1_x3[`npuarc_R1_W0] & x3_rf_wenb0_64_r & x1_rf_renb1_64_r;
  fd_x1_x3[`npuarc_LR1_LW1] = qd_x1_x3[`npuarc_R1_W1] & (x1_rf_ra1_r[0] == x3_rf_wa1_r[0]);
  fd_x1_x3[`npuarc_HR1_LW1] = qd_x1_x3[`npuarc_R1_W1] & x3_rf_wa1_r[0] & x1_rf_renb1_64_r;
  fd_x1_x3[`npuarc_LR1_HW1] = qd_x1_x3[`npuarc_R1_W1] & x1_rf_ra1_r[0] & x3_rf_wenb1_64_r;
  fd_x1_x3[`npuarc_HR1_HW1] = qd_x1_x3[`npuarc_R1_W1] & x3_rf_wenb1_64_r & x1_rf_renb1_64_r;

  fd_x1_ca[`npuarc_LR0_LW0] = qd_x1_ca[`npuarc_R0_W0] & (x1_rf_ra0_r[0] == ca_rf_wa0_r[0]);
  fd_x1_ca[`npuarc_HR0_LW0] = qd_x1_ca[`npuarc_R0_W0] & ca_rf_wa0_r[0] & x1_rf_renb0_64_r;
  fd_x1_ca[`npuarc_LR0_HW0] = qd_x1_ca[`npuarc_R0_W0] & x1_rf_ra0_r[0] & ca_rf_wenb0_64_r;
  fd_x1_ca[`npuarc_HR0_HW0] = qd_x1_ca[`npuarc_R0_W0] & ca_rf_wenb0_64_r & x1_rf_renb0_64_r;
  fd_x1_ca[`npuarc_LR0_LW1] = qd_x1_ca[`npuarc_R0_W1] & (x1_rf_ra0_r[0] == ca_rf_wa1_r[0]);
  fd_x1_ca[`npuarc_HR0_LW1] = qd_x1_ca[`npuarc_R0_W1] & ca_rf_wa1_r[0] & x1_rf_renb0_64_r;
  fd_x1_ca[`npuarc_LR0_HW1] = qd_x1_ca[`npuarc_R0_W1] & x1_rf_ra0_r[0] & ca_rf_wenb1_64_r;
  fd_x1_ca[`npuarc_HR0_HW1] = qd_x1_ca[`npuarc_R0_W1] & ca_rf_wenb1_64_r & x1_rf_renb0_64_r;
  fd_x1_ca[`npuarc_LR1_LW0] = qd_x1_ca[`npuarc_R1_W0] & (x1_rf_ra1_r[0] == ca_rf_wa0_r[0]);
  fd_x1_ca[`npuarc_HR1_LW0] = qd_x1_ca[`npuarc_R1_W0] & ca_rf_wa0_r[0] & x1_rf_renb1_64_r;
  fd_x1_ca[`npuarc_LR1_HW0] = qd_x1_ca[`npuarc_R1_W0] & x1_rf_ra1_r[0] & ca_rf_wenb0_64_r;
  fd_x1_ca[`npuarc_HR1_HW0] = qd_x1_ca[`npuarc_R1_W0] & ca_rf_wenb0_64_r & x1_rf_renb1_64_r;
  fd_x1_ca[`npuarc_LR1_LW1] = qd_x1_ca[`npuarc_R1_W1] & (x1_rf_ra1_r[0] == ca_rf_wa1_r[0]);
  fd_x1_ca[`npuarc_HR1_LW1] = qd_x1_ca[`npuarc_R1_W1] & ca_rf_wa1_r[0] & x1_rf_renb1_64_r;
  fd_x1_ca[`npuarc_LR1_HW1] = qd_x1_ca[`npuarc_R1_W1] & x1_rf_ra1_r[0] & ca_rf_wenb1_64_r;
  fd_x1_ca[`npuarc_HR1_HW1] = qd_x1_ca[`npuarc_R1_W1] & ca_rf_wenb1_64_r & x1_rf_renb1_64_r;

  fd_x1_wa[`npuarc_LR0_LW0] = qd_x1_wa[`npuarc_R0_W0] & (x1_rf_ra0_r[0] == wa_rf_wa0_r[0]);
  fd_x1_wa[`npuarc_HR0_LW0] = qd_x1_wa[`npuarc_R0_W0] & wa_rf_wa0_r[0] & x1_rf_renb0_64_r;
  fd_x1_wa[`npuarc_LR0_HW0] = qd_x1_wa[`npuarc_R0_W0] & x1_rf_ra0_r[0] & wa_dp_wenb0_64_r;
  fd_x1_wa[`npuarc_HR0_HW0] = qd_x1_wa[`npuarc_R0_W0] & wa_dp_wenb0_64_r & x1_rf_renb0_64_r;
  fd_x1_wa[`npuarc_LR0_LW1] = qd_x1_wa[`npuarc_R0_W1] 
                     & (x1_rf_ra0_r[0] == wa_rf_wa1_r[0])
                     & wa_rf_wenb1_r
                     ;
  fd_x1_wa[`npuarc_HR0_LW1] = qd_x1_wa[`npuarc_R0_W1] & wa_rf_wa1_r[0] & x1_rf_renb0_64_r;
  fd_x1_wa[`npuarc_LR0_HW1] = qd_x1_wa[`npuarc_R0_W1] & x1_rf_ra0_r[0] & wa_rf_wenb1_64_r;
  fd_x1_wa[`npuarc_HR0_HW1] = qd_x1_wa[`npuarc_R0_W1] & wa_rf_wenb1_64_r & x1_rf_renb0_64_r;
  fd_x1_wa[`npuarc_LR1_LW0] = qd_x1_wa[`npuarc_R1_W0] & (x1_rf_ra1_r[0] == wa_rf_wa0_r[0]);
  fd_x1_wa[`npuarc_HR1_LW0] = qd_x1_wa[`npuarc_R1_W0] & wa_rf_wa0_r[0] & x1_rf_renb1_64_r;
  fd_x1_wa[`npuarc_LR1_HW0] = qd_x1_wa[`npuarc_R1_W0] & x1_rf_ra1_r[0] & wa_dp_wenb0_64_r;
  fd_x1_wa[`npuarc_HR1_HW0] = qd_x1_wa[`npuarc_R1_W0] & wa_dp_wenb0_64_r & x1_rf_renb1_64_r;
  fd_x1_wa[`npuarc_LR1_LW1] = qd_x1_wa[`npuarc_R1_W1] 
                     & (x1_rf_ra1_r[0] == wa_rf_wa1_r[0])
                     & wa_rf_wenb1_r
                     ;
  fd_x1_wa[`npuarc_HR1_LW1] = qd_x1_wa[`npuarc_R1_W1] & wa_rf_wa1_r[0] & x1_rf_renb1_64_r;
  fd_x1_wa[`npuarc_LR1_HW1] = qd_x1_wa[`npuarc_R1_W1] & x1_rf_ra1_r[0] & wa_rf_wenb1_64_r;
  fd_x1_wa[`npuarc_HR1_HW1] = qd_x1_wa[`npuarc_R1_W1] & wa_rf_wenb1_64_r & x1_rf_renb1_64_r;

  fd_x2_x3[`npuarc_LR0_LW0] = qd_x2_x3[`npuarc_R0_W0] & (x2_rf_ra0_r[0] == x3_rf_wa0_r[0]);
  fd_x2_x3[`npuarc_HR0_LW0] = qd_x2_x3[`npuarc_R0_W0] & x3_rf_wa0_r[0] & x2_rf_renb0_64_r;
  fd_x2_x3[`npuarc_LR0_HW0] = qd_x2_x3[`npuarc_R0_W0] & x2_rf_ra0_r[0] & x3_rf_wenb0_64_r;
  fd_x2_x3[`npuarc_HR0_HW0] = qd_x2_x3[`npuarc_R0_W0] & x3_rf_wenb0_64_r & x2_rf_renb0_64_r;
  fd_x2_x3[`npuarc_LR0_LW1] = qd_x2_x3[`npuarc_R0_W1] & (x2_rf_ra0_r[0] == x3_rf_wa1_r[0]);
  fd_x2_x3[`npuarc_HR0_LW1] = qd_x2_x3[`npuarc_R0_W1] & x3_rf_wa1_r[0] & x2_rf_renb0_64_r;
  fd_x2_x3[`npuarc_LR0_HW1] = qd_x2_x3[`npuarc_R0_W1] & x2_rf_ra0_r[0] & x3_rf_wenb1_64_r;
  fd_x2_x3[`npuarc_HR0_HW1] = qd_x2_x3[`npuarc_R0_W1] & x3_rf_wenb1_64_r & x2_rf_renb0_64_r;
  fd_x2_x3[`npuarc_LR1_LW0] = qd_x2_x3[`npuarc_R1_W0] & (x2_rf_ra1_r[0] == x3_rf_wa0_r[0]);
  fd_x2_x3[`npuarc_HR1_LW0] = qd_x2_x3[`npuarc_R1_W0] & x3_rf_wa0_r[0] & x2_rf_renb1_64_r;
  fd_x2_x3[`npuarc_LR1_HW0] = qd_x2_x3[`npuarc_R1_W0] & x2_rf_ra1_r[0] & x3_rf_wenb0_64_r;
  fd_x2_x3[`npuarc_HR1_HW0] = qd_x2_x3[`npuarc_R1_W0] & x3_rf_wenb0_64_r & x2_rf_renb1_64_r;
  fd_x2_x3[`npuarc_LR1_LW1] = qd_x2_x3[`npuarc_R1_W1] & (x2_rf_ra1_r[0] == x3_rf_wa1_r[0]);
  fd_x2_x3[`npuarc_HR1_LW1] = qd_x2_x3[`npuarc_R1_W1] & x3_rf_wa1_r[0] & x2_rf_renb1_64_r;
  fd_x2_x3[`npuarc_LR1_HW1] = qd_x2_x3[`npuarc_R1_W1] & x2_rf_ra1_r[0] & x3_rf_wenb1_64_r;
  fd_x2_x3[`npuarc_HR1_HW1] = qd_x2_x3[`npuarc_R1_W1] & x3_rf_wenb1_64_r & x2_rf_renb1_64_r;

  fd_x2_ca[`npuarc_LR0_LW0] = qd_x2_ca[`npuarc_R0_W0] & (x2_rf_ra0_r[0] == ca_rf_wa0_r[0]);
  fd_x2_ca[`npuarc_HR0_LW0] = qd_x2_ca[`npuarc_R0_W0] & ca_rf_wa0_r[0] & x2_rf_renb0_64_r;
  fd_x2_ca[`npuarc_LR0_HW0] = qd_x2_ca[`npuarc_R0_W0] & x2_rf_ra0_r[0] & ca_rf_wenb0_64_r;
  fd_x2_ca[`npuarc_HR0_HW0] = qd_x2_ca[`npuarc_R0_W0] & ca_rf_wenb0_64_r & x2_rf_renb0_64_r;
  fd_x2_ca[`npuarc_LR0_LW1] = qd_x2_ca[`npuarc_R0_W1] & (x2_rf_ra0_r[0] == ca_rf_wa1_r[0]);
  fd_x2_ca[`npuarc_HR0_LW1] = qd_x2_ca[`npuarc_R0_W1] & ca_rf_wa1_r[0] & x2_rf_renb0_64_r;
  fd_x2_ca[`npuarc_LR0_HW1] = qd_x2_ca[`npuarc_R0_W1] & x2_rf_ra0_r[0] & ca_rf_wenb1_64_r;
  fd_x2_ca[`npuarc_HR0_HW1] = qd_x2_ca[`npuarc_R0_W1] & ca_rf_wenb1_64_r & x2_rf_renb0_64_r;
  fd_x2_ca[`npuarc_LR1_LW0] = qd_x2_ca[`npuarc_R1_W0] & (x2_rf_ra1_r[0] == ca_rf_wa0_r[0]);
  fd_x2_ca[`npuarc_HR1_LW0] = qd_x2_ca[`npuarc_R1_W0] & ca_rf_wa0_r[0] & x2_rf_renb1_64_r;
  fd_x2_ca[`npuarc_LR1_HW0] = qd_x2_ca[`npuarc_R1_W0] & x2_rf_ra1_r[0] & ca_rf_wenb0_64_r;
  fd_x2_ca[`npuarc_HR1_HW0] = qd_x2_ca[`npuarc_R1_W0] & ca_rf_wenb0_64_r & x2_rf_renb1_64_r;
  fd_x2_ca[`npuarc_LR1_LW1] = qd_x2_ca[`npuarc_R1_W1] & (x2_rf_ra1_r[0] == ca_rf_wa1_r[0]);
  fd_x2_ca[`npuarc_HR1_LW1] = qd_x2_ca[`npuarc_R1_W1] & ca_rf_wa1_r[0] & x2_rf_renb1_64_r;
  fd_x2_ca[`npuarc_LR1_HW1] = qd_x2_ca[`npuarc_R1_W1] & x2_rf_ra1_r[0] & ca_rf_wenb1_64_r;
  fd_x2_ca[`npuarc_HR1_HW1] = qd_x2_ca[`npuarc_R1_W1] & ca_rf_wenb1_64_r & x2_rf_renb1_64_r;

  fd_x2_wa[`npuarc_LR0_LW0] = qd_x2_wa[`npuarc_R0_W0] & (x2_rf_ra0_r[0] == wa_rf_wa0_r[0]);
  fd_x2_wa[`npuarc_HR0_LW0] = qd_x2_wa[`npuarc_R0_W0] & wa_rf_wa0_r[0] & x2_rf_renb0_64_r;
  fd_x2_wa[`npuarc_LR0_HW0] = qd_x2_wa[`npuarc_R0_W0] & x2_rf_ra0_r[0] & wa_dp_wenb0_64_r;
  fd_x2_wa[`npuarc_HR0_HW0] = qd_x2_wa[`npuarc_R0_W0] & wa_dp_wenb0_64_r & x2_rf_renb0_64_r;
  fd_x2_wa[`npuarc_LR0_LW1] = qd_x2_wa[`npuarc_R0_W1] 
                     & (x2_rf_ra0_r[0] == wa_rf_wa1_r[0])
                     & wa_rf_wenb1_r
                     ;
  fd_x2_wa[`npuarc_HR0_LW1] = qd_x2_wa[`npuarc_R0_W1] & wa_rf_wa1_r[0] & x2_rf_renb0_64_r;
  fd_x2_wa[`npuarc_LR0_HW1] = qd_x2_wa[`npuarc_R0_W1] & x2_rf_ra0_r[0] & wa_rf_wenb1_64_r;
  fd_x2_wa[`npuarc_HR0_HW1] = qd_x2_wa[`npuarc_R0_W1] & wa_rf_wenb1_64_r & x2_rf_renb0_64_r;
  fd_x2_wa[`npuarc_LR1_LW0] = qd_x2_wa[`npuarc_R1_W0] & (x2_rf_ra1_r[0] == wa_rf_wa0_r[0]);
  fd_x2_wa[`npuarc_HR1_LW0] = qd_x2_wa[`npuarc_R1_W0] & wa_rf_wa0_r[0] & x2_rf_renb1_64_r;
  fd_x2_wa[`npuarc_LR1_HW0] = qd_x2_wa[`npuarc_R1_W0] & x2_rf_ra1_r[0] & wa_dp_wenb0_64_r;
  fd_x2_wa[`npuarc_HR1_HW0] = qd_x2_wa[`npuarc_R1_W0] & wa_dp_wenb0_64_r & x2_rf_renb1_64_r;
  fd_x2_wa[`npuarc_LR1_LW1] = qd_x2_wa[`npuarc_R1_W1] 
                     & (x2_rf_ra1_r[0] == wa_rf_wa1_r[0])
                     & wa_rf_wenb1_r
                     ;
  fd_x2_wa[`npuarc_HR1_LW1] = qd_x2_wa[`npuarc_R1_W1] & wa_rf_wa1_r[0] & x2_rf_renb1_64_r;
  fd_x2_wa[`npuarc_LR1_HW1] = qd_x2_wa[`npuarc_R1_W1] & x2_rf_ra1_r[0] & wa_rf_wenb1_64_r;
  fd_x2_wa[`npuarc_HR1_HW1] = qd_x2_wa[`npuarc_R1_W1] & wa_rf_wenb1_64_r & x2_rf_renb1_64_r;

  fd_x3_ca[`npuarc_LR0_LW0] = qd_x3_ca[`npuarc_R0_W0] & (x3_rf_ra0_r[0] == ca_rf_wa0_r[0]);
  fd_x3_ca[`npuarc_HR0_LW0] = qd_x3_ca[`npuarc_R0_W0] & ca_rf_wa0_r[0] & x3_rf_renb0_64_r;
  fd_x3_ca[`npuarc_LR0_HW0] = qd_x3_ca[`npuarc_R0_W0] & x3_rf_ra0_r[0] & ca_rf_wenb0_64_r;
  fd_x3_ca[`npuarc_HR0_HW0] = qd_x3_ca[`npuarc_R0_W0] & ca_rf_wenb0_64_r & x3_rf_renb0_64_r;
  fd_x3_ca[`npuarc_LR0_LW1] = qd_x3_ca[`npuarc_R0_W1] & (x3_rf_ra0_r[0] == ca_rf_wa1_r[0]);
  fd_x3_ca[`npuarc_HR0_LW1] = qd_x3_ca[`npuarc_R0_W1] & ca_rf_wa1_r[0] & x3_rf_renb0_64_r;
  fd_x3_ca[`npuarc_LR0_HW1] = qd_x3_ca[`npuarc_R0_W1] & x3_rf_ra0_r[0] & ca_rf_wenb1_64_r;
  fd_x3_ca[`npuarc_HR0_HW1] = qd_x3_ca[`npuarc_R0_W1] & ca_rf_wenb1_64_r & x3_rf_renb0_64_r;
  fd_x3_ca[`npuarc_LR1_LW0] = qd_x3_ca[`npuarc_R1_W0] & (x3_rf_ra1_r[0] == ca_rf_wa0_r[0]);
  fd_x3_ca[`npuarc_HR1_LW0] = qd_x3_ca[`npuarc_R1_W0] & ca_rf_wa0_r[0] & x3_rf_renb1_64_r;
  fd_x3_ca[`npuarc_LR1_HW0] = qd_x3_ca[`npuarc_R1_W0] & x3_rf_ra1_r[0] & ca_rf_wenb0_64_r;
  fd_x3_ca[`npuarc_HR1_HW0] = qd_x3_ca[`npuarc_R1_W0] & ca_rf_wenb0_64_r & x3_rf_renb1_64_r;
  fd_x3_ca[`npuarc_LR1_LW1] = qd_x3_ca[`npuarc_R1_W1] & (x3_rf_ra1_r[0] == ca_rf_wa1_r[0]);
  fd_x3_ca[`npuarc_HR1_LW1] = qd_x3_ca[`npuarc_R1_W1] & ca_rf_wa1_r[0] & x3_rf_renb1_64_r;
  fd_x3_ca[`npuarc_LR1_HW1] = qd_x3_ca[`npuarc_R1_W1] & x3_rf_ra1_r[0] & ca_rf_wenb1_64_r;
  fd_x3_ca[`npuarc_HR1_HW1] = qd_x3_ca[`npuarc_R1_W1] & ca_rf_wenb1_64_r & x3_rf_renb1_64_r;

  fd_x3_wa[`npuarc_LR0_LW0] = qd_x3_wa[`npuarc_R0_W0] & (x3_rf_ra0_r[0] == wa_rf_wa0_r[0]);
  fd_x3_wa[`npuarc_HR0_LW0] = qd_x3_wa[`npuarc_R0_W0] & wa_rf_wa0_r[0] & x3_rf_renb0_64_r;
  fd_x3_wa[`npuarc_LR0_HW0] = qd_x3_wa[`npuarc_R0_W0] & x3_rf_ra0_r[0] & wa_dp_wenb0_64_r;
  fd_x3_wa[`npuarc_HR0_HW0] = qd_x3_wa[`npuarc_R0_W0] & wa_dp_wenb0_64_r & x3_rf_renb0_64_r;
  fd_x3_wa[`npuarc_LR0_LW1] = qd_x3_wa[`npuarc_R0_W1] 
                     & (x3_rf_ra0_r[0] == wa_rf_wa1_r[0])
                     & wa_rf_wenb1_r
                     ;
  fd_x3_wa[`npuarc_HR0_LW1] = qd_x3_wa[`npuarc_R0_W1] & wa_rf_wa1_r[0] & x3_rf_renb0_64_r;
  fd_x3_wa[`npuarc_LR0_HW1] = qd_x3_wa[`npuarc_R0_W1] & x3_rf_ra0_r[0] & wa_rf_wenb1_64_r;
  fd_x3_wa[`npuarc_HR0_HW1] = qd_x3_wa[`npuarc_R0_W1] & wa_rf_wenb1_64_r & x3_rf_renb0_64_r;
  fd_x3_wa[`npuarc_LR1_LW0] = qd_x3_wa[`npuarc_R1_W0] & (x3_rf_ra1_r[0] == wa_rf_wa0_r[0]);
  fd_x3_wa[`npuarc_HR1_LW0] = qd_x3_wa[`npuarc_R1_W0] & wa_rf_wa0_r[0] & x3_rf_renb1_64_r;
  fd_x3_wa[`npuarc_LR1_HW0] = qd_x3_wa[`npuarc_R1_W0] & x3_rf_ra1_r[0] & wa_dp_wenb0_64_r;
  fd_x3_wa[`npuarc_HR1_HW0] = qd_x3_wa[`npuarc_R1_W0] & wa_dp_wenb0_64_r & x3_rf_renb1_64_r;
  fd_x3_wa[`npuarc_LR1_LW1] = qd_x3_wa[`npuarc_R1_W1] 
                     & (x3_rf_ra1_r[0] == wa_rf_wa1_r[0])
                     & wa_rf_wenb1_r
                     ;
  fd_x3_wa[`npuarc_HR1_LW1] = qd_x3_wa[`npuarc_R1_W1] & wa_rf_wa1_r[0] & x3_rf_renb1_64_r;
  fd_x3_wa[`npuarc_LR1_HW1] = qd_x3_wa[`npuarc_R1_W1] & x3_rf_ra1_r[0] & wa_rf_wenb1_64_r;
  fd_x3_wa[`npuarc_HR1_HW1] = qd_x3_wa[`npuarc_R1_W1] & wa_rf_wenb1_64_r & x3_rf_renb1_64_r;

  fd_ca_wa[`npuarc_LR0_LW0] = qd_ca_wa[`npuarc_R0_W0] & (ca_rf_ra0_r[0] == wa_rf_wa0_r[0]);
  fd_ca_wa[`npuarc_HR0_LW0] = qd_ca_wa[`npuarc_R0_W0] & wa_rf_wa0_r[0] & ca_rf_renb0_64_r;
  fd_ca_wa[`npuarc_LR0_HW0] = qd_ca_wa[`npuarc_R0_W0] & ca_rf_ra0_r[0] & wa_dp_wenb0_64_r;
  fd_ca_wa[`npuarc_HR0_HW0] = qd_ca_wa[`npuarc_R0_W0] & wa_dp_wenb0_64_r & ca_rf_renb0_64_r;
  fd_ca_wa[`npuarc_LR0_LW1] = qd_ca_wa[`npuarc_R0_W1] 
                     & (ca_rf_ra0_r[0] == wa_rf_wa1_r[0])
                     & wa_rf_wenb1_r
                     ;
  fd_ca_wa[`npuarc_HR0_LW1] = qd_ca_wa[`npuarc_R0_W1] & wa_rf_wa1_r[0] & ca_rf_renb0_64_r;
  fd_ca_wa[`npuarc_LR0_HW1] = qd_ca_wa[`npuarc_R0_W1] & ca_rf_ra0_r[0] & wa_rf_wenb1_64_r;
  fd_ca_wa[`npuarc_HR0_HW1] = qd_ca_wa[`npuarc_R0_W1] & wa_rf_wenb1_64_r & ca_rf_renb0_64_r;
  fd_ca_wa[`npuarc_LR1_LW0] = qd_ca_wa[`npuarc_R1_W0] & (ca_rf_ra1_r[0] == wa_rf_wa0_r[0]);
  fd_ca_wa[`npuarc_HR1_LW0] = qd_ca_wa[`npuarc_R1_W0] & wa_rf_wa0_r[0] & ca_rf_renb1_64_r;
  fd_ca_wa[`npuarc_LR1_HW0] = qd_ca_wa[`npuarc_R1_W0] & ca_rf_ra1_r[0] & wa_dp_wenb0_64_r;
  fd_ca_wa[`npuarc_HR1_HW0] = qd_ca_wa[`npuarc_R1_W0] & wa_dp_wenb0_64_r & ca_rf_renb1_64_r;
  fd_ca_wa[`npuarc_LR1_LW1] = qd_ca_wa[`npuarc_R1_W1] 
                     & (ca_rf_ra1_r[0] == wa_rf_wa1_r[0])
                     & wa_rf_wenb1_r
                     ;
  fd_ca_wa[`npuarc_HR1_LW1] = qd_ca_wa[`npuarc_R1_W1] & wa_rf_wa1_r[0] & ca_rf_renb1_64_r;
  fd_ca_wa[`npuarc_LR1_HW1] = qd_ca_wa[`npuarc_R1_W1] & ca_rf_ra1_r[0] & wa_rf_wenb1_64_r;
  fd_ca_wa[`npuarc_HR1_HW1] = qd_ca_wa[`npuarc_R1_W1] & wa_rf_wenb1_64_r & ca_rf_renb1_64_r;


end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pre-commit RAW dependence vectors at the Operand stage are concatenated  //
// with the kill signals generated at the Operand stage. These larger       //
// vectors are then propagated to the Exec1 stage and beyond.               //
//                                                                          //
// At the Operand stage we have only RAW dependencies, in the column of the //
// dependency matrix associated with the Operand stage (dp_sa_yy_r, where   //
// yy is any stage downstream of sa, or one of the graduation buffer rows). //
// These are prepended with the kill signals defined by sa_kl_yy vectors.   //
// Each sa_kl_yy vector indicates the set of write results at stage yy that //
// are killed (i.e. redefined) by the computation at the Operand stage.     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire  [`npuarc_DP_PRE_RANGE]   cn_sa_x1;               // concatenated sa_x1 vector
wire  [`npuarc_DP_PRE_RANGE]   cn_sa_x2;               // concatenated sa_x1 vector
wire  [`npuarc_DP_PRE_RANGE]   cn_sa_x3;               // concatenated sa_x1 vector
wire  [`npuarc_DP_PRE_RANGE]   cn_sa_ca;               // concatenated sa_x1 vector
wire  [`npuarc_DP_PRE_RANGE]   cn_sa_wa;               // concatenated sa_x1 vector
wire  [`npuarc_DP_POST_RANGE]  cn_sa_ar0;              // concatenated sa_ar0 vector
wire  [`npuarc_DP_POST_RANGE]  cn_sa_ar1;              // concatenated sa_ar1 vector
wire  [`npuarc_DP_POST_RANGE]  cn_sa_ar2;              // concatenated sa_ar2 vector
wire  [`npuarc_DP_POST_RANGE]  cn_sa_ar3;              // concatenated sa_ar3 vector
wire  [`npuarc_DP_POST_RANGE]  cn_sa_ar4;              // concatenated sa_ar4 vector
wire  [`npuarc_DP_POST_RANGE]  cn_sa_ar5;              // concatenated sa_ar5 vector
wire  [`npuarc_DP_POST_RANGE]  cn_sa_ar6;              // concatenated sa_ar6 vector
wire  [`npuarc_DP_POST_RANGE]  cn_sa_ar7;              // concatenated sa_ar7 vector

assign cn_sa_x1 = { sa_kl_x1[`npuarc_KL_RANGE_HI], rd_sa_x1, sa_kl_x1[`npuarc_KL_RANGE_LO]};
assign cn_sa_x2 = { sa_kl_x2[`npuarc_KL_RANGE_HI], rd_sa_x2, sa_kl_x2[`npuarc_KL_RANGE_LO]};
assign cn_sa_x3 = { sa_kl_x3[`npuarc_KL_RANGE_HI], rd_sa_x3, sa_kl_x3[`npuarc_KL_RANGE_LO]};
assign cn_sa_ca = { sa_kl_ca[`npuarc_KL_RANGE_HI], rd_sa_ca, sa_kl_ca[`npuarc_KL_RANGE_LO]};
assign cn_sa_wa = { sa_kl_wa[`npuarc_KL_RANGE_HI], rd_sa_wa, sa_kl_wa[`npuarc_KL_RANGE_LO]};

assign cn_sa_ar0 = { sa_kl_ar0[`npuarc_KL_RANGE_HI], rd_sa_ar0 };
assign cn_sa_ar1 = { sa_kl_ar1[`npuarc_KL_RANGE_HI], rd_sa_ar1 };
assign cn_sa_ar2 = { sa_kl_ar2[`npuarc_KL_RANGE_HI], rd_sa_ar2 };
assign cn_sa_ar3 = { sa_kl_ar3[`npuarc_KL_RANGE_HI], rd_sa_ar3 };
assign cn_sa_ar4 = { sa_kl_ar4[`npuarc_KL_RANGE_HI], rd_sa_ar4 };
assign cn_sa_ar5 = { sa_kl_ar5[`npuarc_KL_RANGE_HI], rd_sa_ar5 };
assign cn_sa_ar6 = { sa_kl_ar6[`npuarc_KL_RANGE_HI], rd_sa_ar6 };
assign cn_sa_ar7 = { sa_kl_ar7[`npuarc_KL_RANGE_HI], rd_sa_ar7 };

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pre-commit dependence vectors in which the W0 and W1 halves have been    //
// multiplexed according to the write channel requesting to graduate a      //
// post-commit result for out-of-order retirement. If the Commit-stage      //
// instruction is a Load, then W1 will be graduated, otherwise it is W0.    //
// These dependencies are assigned to post-commit graduation buffers when   //
// the Commit-stage instruction graduates without retiring the selected     //
// write-channel result.                                                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire  [`npuarc_POST_RAW_RANGE]    mg_da_ca;               // RAW only mux, dp_da_ca
wire  [`npuarc_POST_RAW_RANGE]    mg_sa_ca_h;             // RAW only mux, dp_sa_ca_r
wire  [`npuarc_DP_POST_RANGE]     mg_sa_ca_r;             // RAW+kill mux, dp_sa_ca_r
wire  [`npuarc_DP_POST_RANGE]     mg_x1_ca_r;             // RAW+kill mux, dp_x1_ca_r
wire  [`npuarc_DP_POST_RANGE]     mg_x2_ca_r;             // RAW+kill mux, dp_x2_ca_r
wire  [`npuarc_DP_POST_RANGE]     mg_x3_ca_r;             // RAW+kill mux, dp_x3_ca_r

assign mg_da_ca   = ca_load_r 
                  ? dp_da_ca[`npuarc_R1_W1:`npuarc_R0_W1]
                  : dp_da_ca[`npuarc_R1_W0:`npuarc_R0_W0]
                  ;
                            
assign mg_sa_ca_h = ca_load_r 
                  ? dp_sa_ca_r[`npuarc_R1_W1:`npuarc_R0_W1]
                  : dp_sa_ca_r[`npuarc_R1_W0:`npuarc_R0_W0]
                  ;

assign mg_sa_ca_r = ca_load_r 
                  ? cn_sa_ca[`npuarc_DP_W1]
                  : { cn_sa_ca[`npuarc_W0_HI], cn_sa_ca[`npuarc_W0_LO], cn_sa_ca[`npuarc_RAW_W0] }
                  ;

assign mg_x1_ca_r = ca_load_r 
                  ? dp_x1_ca_r[`npuarc_DP_W1]
                  : { dp_x1_ca_r[`npuarc_W0_HI], dp_x1_ca_r[`npuarc_W0_LO], dp_x1_ca_r[`npuarc_RAW_W0] }
                  ;

assign mg_x2_ca_r = ca_load_r
                  ? dp_x2_ca_r[`npuarc_DP_W1]
                  : { dp_x2_ca_r[`npuarc_W0_HI], dp_x2_ca_r[`npuarc_W0_LO], dp_x2_ca_r[`npuarc_RAW_W0] }
                  ;

assign mg_x3_ca_r = ca_load_r
                  ? dp_x3_ca_r[`npuarc_DP_W1]
                  : { dp_x3_ca_r[`npuarc_W0_HI], dp_x3_ca_r[`npuarc_W0_LO], dp_x3_ca_r[`npuarc_RAW_W0] }
                  ;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Each 'xx_adv' signal is asserted if, and only if, the instruction at     //
// stage xx will advance to the next stage in the current cycle.            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           da_adv;           // Decode stage advances
reg                           sa_adv;           // Operand stage advances
reg                           x1_adv;           // Exec1 stage advances
reg                           x2_adv;           // Exec2 stage advances
reg                           x3_adv;           // Exec3 stage advances
reg                           ca_adv;           // Commit stage advances
reg                           ca_to_ar;         // Commit insn graduates
reg                           ca_adv_w0;        // Commit writes W0 in-order
reg                           ca_adv_w1;        // Commit writes W1 in-order
reg                           ca_grad_w1;       // Commit graduates W1 channel
reg                           ca_grad_allowed;  // Graduation is permitted

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Each 'dp_xx_enb' signal is asserted if, and only if, pipeline stage xx   //
// is valid in the current cycle or will receive a valid instruction in     //
// the next cycle. These signals are used to clock-gate the per-stage       //
// columns of the dependency matrix.                                        //
//                                                                          //
// It is guaranteed that any column representing a stage that does not have //
// a valid instruction is guaranteed to contains all zero dependency        //
// vector elements. If that stage does not receive a valid instruction in   //
// the coming cycle, then it will remain all zeros, and hence does not need //
// to be clocked. In these circumstances the dp_xx_enb signal will not be   //
// asserted (to save dynamic power).                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           dp_sa_enb;        // Operand column enable
reg                           dp_x1_enb;        // Exec1 column enable
reg                           dp_x2_enb;        // Exec2 column enable
reg                           dp_x3_enb;        // Exec3 column enable
reg                           dp_ca_enb;        // Commit column enable

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Each 'XX_has_wY' signal is asserted if, and only if, the result of the   //
// instruction at stage XX is computed and available for bypass through     //
// channel wY (Y = 0 or 1). This signal indicates that either the result    //
// was computed in a previous stage, and is still available from stage XX,  //
// or that its computation completes in stage XX and therefore it is now    //
// available for bypass.                                                    //
//                                                                          //
// The W0 and W1 results are always available at Writeback.                 //
//                                                                          //
// The W1 result is never available at x1, x2 or x3.                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           x1_has_w0;        // Exec1 has W0 result
reg                           x3_has_w0;        // Exec3 has W0 result
reg                           ca_has_w0;        // Commit has W0 result
reg                           ca_has_w1;        // Commit has W1 result

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// An instruction present a X1 may not evaluate if the speculative          //
// flags retained by X2 are not up to date. Flags at X2 may become          //
// invalid if a flag-producing instruction is deferred until CA. In         //
// this case, we must therefore also defer any subsequent                   //
// instructions dependent upon the flags produced by the original           //
// instruction.                                                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// @dp_x2_flag_upt_PROC
//
reg                           x1_flags_ready;   // Exec1 has no ZNCV hazard.
reg                           x1_alu_exec;      // ALU exeutes insn at X1
reg                           x1_flags_done;    // Flags effectively done at X1
reg [`npuarc_ZNCV_RANGE]             x1_flag_use;
reg [`npuarc_ZNCV_RANGE]             x1_is_flag;
reg [`npuarc_ZNCV_RANGE]             x2_is_flag;
reg [`npuarc_ZNCV_RANGE]             x3_is_flag;
reg [`npuarc_ZNCV_RANGE]             flag_invalidate;

// @deferred_flag_update_PROC
//
reg                           pending_flag_upt_r;
reg                           pending_flag_upt_nxt;
reg                           pending_eia_cc;
reg                           flag_dependency_at_sa;
reg                           flag_flush_pipe;
reg                           update_flags_x2;
reg                           flag_producer_in_dslot;
reg                           pending_flag_upt_cg0;
reg                           sa_haz_on_zncv;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Signals for detecting data dependencies on first source register (reg0)  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           da0_is_sa_pair0;  // reg0 may match Opds data
reg                           da0_is_sa_pair1;  // reg0 may match Opds load
//
reg                           da0_is_x1_pair0;  // reg0 may match Exec1 data
reg                           da0_is_x1_pair1;  // reg0 may match Exec1 load
//
reg                           da0_is_x2_pair0;  // reg0 may match Exec2 data
reg                           da0_is_x2_pair1;  // reg0 may match Exec2 load
//
reg                           da0_is_x3_pair0;  // reg0 may match Exec3 data
reg                           da0_is_x3_pair1;  // reg0 may match Exec3 load
//
reg                           da0_is_ca_pair0;  // reg0 may match Commit data
reg                           da0_is_ca_pair1;  // reg0 may match Commit load
//
reg                           da0_is_wa_pair0;  // reg0 may match w/back data
reg                           da0_is_wa_pair1;  // reg0 may match w/back load
//
reg                           da0_is_ar0_pair1;  // reg0 may match ar0 context
reg                           da0_is_ar1_pair1;  // reg0 may match ar1 context
reg                           da0_is_ar2_pair1;  // reg0 may match ar2 context
reg                           da0_is_ar3_pair1;  // reg0 may match ar3 context
reg                           da0_is_ar4_pair1;  // reg0 may match ar4 context
reg                           da0_is_ar5_pair1;  // reg0 may match ar5 context
reg                           da0_is_ar6_pair1;  // reg0 may match ar6 context
reg                           da0_is_ar7_pair1;  // reg0 may match ar7 context

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Signals for detecting data dependencies on 2nd source register (reg1)    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           da1_is_sa_pair0;  // reg1 may match Opds data
reg                           da1_is_sa_pair1;  // reg1 may match Opds load
//
reg                           da1_is_x1_pair0;  // reg1 may match Exec1 data
reg                           da1_is_x1_pair1;  // reg1 may match Exec1 load
//
reg                           da1_is_x2_pair0;  // reg1 may match Exec2 data
reg                           da1_is_x2_pair1;  // reg1 may match Exec2 load
//
reg                           da1_is_x3_pair0;  // reg1 may match Exec3 data
reg                           da1_is_x3_pair1;  // reg1 may match Exec3 load
//
reg                           da1_is_ca_pair0;  // reg1 may match Commit data
reg                           da1_is_ca_pair1;  // reg1 may match Commit load
//
reg                           da1_is_wa_pair0;  // reg1 may match W/back data
reg                           da1_is_wa_pair1;  // reg1 may match W/back load
//
reg                           da1_is_ar0_pair1;  // reg1 may match ar0 context
reg                           da1_is_ar1_pair1;  // reg1 may match ar1 context
reg                           da1_is_ar2_pair1;  // reg1 may match ar2 context
reg                           da1_is_ar3_pair1;  // reg1 may match ar3 context
reg                           da1_is_ar4_pair1;  // reg1 may match ar4 context
reg                           da1_is_ar5_pair1;  // reg1 may match ar5 context
reg                           da1_is_ar6_pair1;  // reg1 may match ar6 context
reg                           da1_is_ar7_pair1;  // reg1 may match ar7 context


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Signals for managing the allocation and deallocation of post-commit      //
// retirement contexts, and for implementing the graduation and retirement  //
// interface logic beteen the dependency pipe and the main pipeline.        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg   [`npuarc_GRAD_ADDR_RANGE]      ca_grad_rf_wa;    // graduating register address
reg                           ca_grad_rf_64;    // 64-bit graduation request
reg                           grad_ack;         // graduation acceptance
reg   [`npuarc_GRAD_TAG_RANGE]       grad_tag;         // tag of graduating context
reg                           retire_ack;       // retirement acknowledge
reg                           retire_rf_64;     // 64-bit flag for retirement
reg                           retire_rf_wenb;   // reg-wenb for retiring tag
reg                           retire_flag_wen;  // retirement writes flags
reg   [`npuarc_GRAD_ADDR_RANGE]      retire_rf_wa;     // reg-addr for retiring tag
reg                           retire_writes_acc;// writes_acc for retirement
reg   [`npuarc_ADDR_RANGE]           retire_ld_addr;   // VA of retiring ld addr
reg                           retire_is_load;   // Retiring is load
reg                           retire_exclusive; // retiring LLOCK or SCOND
reg                           ca_tag_stall;     // stall waiting to graduate

reg   [7:0]                   ar_tags_valid;    // vector of tag valid bits
reg   [7:0]                   ar_alloc_hot;     // one-hot tag alloc vector
reg   [7:0]                   ar_dealloc_hot;   // one-hot tag dealloc vector
reg   [7:0]                   ar_tag_en;        // vector of tag enables

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// The following vectors each contain one element for each post-commit      //
// retirement context. They signify the following:                          //
//                                                                          //
// ar_a[t] is set to 1 when tag t is Allocated a new context this cycle.    //
//                                                                          //
// ar_d[t] is set to 1 when tag t is Deallocated (and retired) this cycle.  //
//                                                                          //
// ar_f[t] is set to 1 when tag t remains Fixed in its current state.       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg   [7:0]                   ar_a;             // tag allocation vector
reg   [7:0]                   ar_d;             // tag de-allocation vector
reg   [7:0]                   ar_f;             // no alloc/dealloc this cycle
reg   [7:0]                   ar_s;             // tag's wenb may be squashed
reg   [7:0]                   ar_v;             // tag dependence validity

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to compute the 'XX_has_wY' signals                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : dp_has_PROC

  //==========================================================================
  // X1 has the W0 result if it is a fast (1-cycle operation) that has no
  // outstanding operand read flags set. This signal is critical for sa_stall
  // and therefore does not depend on the x1_cond signal.
  // If the X1 operation is a STore, then x1_has_w0 is independent of the
  // current value of x1_read_r1_r (which is the Store data and does not
  // affect the completion of the address calculation in X1).
  //
  x1_has_w0     =   (x1_flags_ready | x1_eia_fast_op_r)
                  & (x1_fast_op_r   | x1_eia_fast_op_r)
                  & (~x1_read_r0_r)
                  & (x1_store_r | (~x1_read_r1_r))
                  ;


  //==========================================================================
  // We execute the current X1 instruction in the X1-stage ALU if is is
  // a fast (1-cycle operation) that has no outstanding operand read flags set.
  // We also consider it executed, if it has a false predicate and also has no
  // outstanding operand read flags set.
  // The second condition ensures that the results of a slow operation are
  // not evaluated again in X2 (e.g. for min, max and abs).
  //
  x1_alu_exec   =
                (
                  (   x1_flags_ready
                    & (   (    x1_fast_op_r
                            | ((~x1_cond) & (~x1_rf_wenb0_64_r))
                            | x1_eia_fast_op_r
                          )
                        & (~x1_read_r0_r)
                        & (~x1_read_r1_r)
                      )
                  )
                | (   x1_opds_in_x1_r
                    & (~x1_cond)
                    & (~x1_rf_wenb0_64_r)
                  )
                )
                ;

  //==========================================================================
  // The next value of x2_done_r is set to 1 if the current X1 instruction
  // evaluates in the X1 ALU (or extension ALU) or if it is a load or a store.
  // Load and Store operations have always completed their channel 0 address
  // calculation by the time they proceed to X2, so they always set
  // x2_done_nxt to 1.
  //
  x2_done_nxt   = x1_alu_exec
                   | x1_store_r
                   | x1_load_r
                ;

  //==========================================================================
  // The current X1 instruction will produce a flag result that is available
  // in X2 if its main ALU result is executed in X1 (x1_alu_exec), or if
  // the X1 instruction is a 'slow_op'. All slow-ops (MIN, MAX, ABS) are
  // permitted to enter X1 only when they have all source operands, and are
  // permitted to exit X1 only if all flag dependencies are satisfied.
  // Slow ops do not produce their final result in X1, but DO yield flag
  // results in X1.
  //
  x1_flags_done = x1_alu_exec
                | x1_slow_op_r
                ;

  //==========================================================================
  // A flag is valid at X2 if: (1) a bypass occurs into next X2 flags
  // from one of the permissible locations {X1,X2,CA}, or (2) on a restart
  // (where it is initialised with the true architectural flag values), or
  // (3) they have been recovered from a previously saved-from or
  // initialised-to state.
  // If a pipeline restart happens when a post-commit retirement of flags
  // is pending, then those flags that are pending a post-commit update will
  // not be made valid in the speculative X2 flags register on pipe flush.
  // All other flags get copied from the architectural state and become
  // valid on a pipeine flush.
  //
  if (wa_restart == 1'b1)
    x2_zncv_valid_nxt = ~(ar_zncv_wen_r & {4{ar_zncv_upt_r}})         // (2)
                      | (dp_retire_zncv & {`npuarc_ZNCV_BITS{retire_ack}})
                      ;
  else
    x2_zncv_valid_nxt = fwd_zncv_x1                                   // (1)
                      | (fwd_zncv_x1_x2 & x2_zncv_valid_r)
                      | fwd_zncv_x1_ca
                      | {`npuarc_ZNCV_BITS{   x1_uop_commit_r                // (3)
                                     & (x1_uop_epil_r | x1_uop_prol_r)
                                   }}
                      | {`npuarc_ZNCV_BITS{x2_zncv_refil_r}}
                      ;

  //==========================================================================
  //  If the Exec1-stage instruction must evaluate at Exec1, and it
  //  depends on the ZNCV flags to evaluate either its result or its
  //  predication outcome, and flags are uncertain without a downstream
  //  flag-defining instruction then the X2 flags need to resync'd with
  //  Architectural flags
  //
  x2_zncv_refil_nxt   = x1_stall_r6
                      & (~(1'b0
                          | x2_valid_r
                          | x3_valid_r
                          | ca_valid_r
                          | ar_zncv_upt_r
                        ))
                      ;



  //==========================================================================
  // Logic to determine whether the X1 branch/jump instruction can have
  // its prediction resolved in X1.
  //
  x1_bta_ready  = (~x1_read_r0_r) & (~x1_read_r1_r);

  x1_cond_ready = x1_flags_ready & x1_bta_ready;

  // X2 has W0 result
  //
  // Note: slow ops always eval in X1/X2, so read flags will always be 0
  //       at X2, and x2_has_w0 can be independent of read flags.
  //

  x2_has_w0     = x2_done_r
                | x2_slow_op_r
                ;

  // X3 has W0 result if it was computed already before entering X3.
  //
  x3_has_w0     = x3_done_r;

  // Commit has W0 result
  //
  ca_has_w0     =
                  ca_done_r
                | ((
                    ( ca_fast_op_r
                    )
                    | ca_mpy_op_r
                    | ca_vector_op_r
                   ) & (~ca_flag_haz))
                ;

  //==========================================================================
  // Commit stage has a bypassable in-order load result:
  //
  // An in-order load result is available in the current cycle iff:
  //
  //  (1) the CA instruction writes to port 1, and
  //  (2) there is no graduation request from the CA load instruction
  //  (3) there is no WAW hazard on the CA load instruction
  //  (4) there is no simultaneous retirement request from the DMP
  //  (5) the dmp_dc4_fast_byp_r signal is asserted when x1_r0_dmp_fast_r
  //      indicates that a fast bypass was predicted in the DC3 stage.
  //
  ca_has_w1     = ca_rf_wenb1_r                               // (1)
                & (~ca_grad_req)                              // (2)
                & (~ca_waw_haz_r)                             // (3)
                & (~dmp_retire_req)                           // (4)
                & (dmp_dc4_fast_byp_r | (~x1_r0_dmp_fast_r))    // (5)
                ;

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to compute the dependency pipeline register        //
// enable signals. These may be enabled when the corresponding stage is     //
// stalled, so they are derived purely to reduce power consumption.         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : pipe_enable_PROC

  dp_sa_enb = sa_valid_r | sa_valid_nxt | clear_deps_r | ca_retire_req;
  dp_x1_enb = x1_valid_r | x1_valid_nxt | clear_deps_r | ca_retire_req;
  dp_x2_enb = x2_valid_r | x2_valid_nxt | clear_deps_r | ca_retire_req;
  dp_x3_enb = x3_valid_r | x3_valid_nxt | clear_deps_r | ca_retire_req;
  dp_ca_enb = ca_valid_r | ca_valid_nxt | clear_deps_r | ca_retire_req;

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Code-density auxiliary register Read-After-Write dependency checks       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : dp_aux_raw_PROC

  da_uses_cd_aux  = da_valid_r & (da_jli_src0   | da_ldi_src0   | da_ei_op);
  sa_uses_cd_aux  = sa_valid_r & (sa_jli_src0_r | sa_ldi_src0_r | sa_ei_op_r);

  da_sr_cd_haz    = da_uses_cd_aux & (sa_sr_op_r | x1_sr_op_r);
  sa_sr_cd_haz    = sa_uses_cd_aux & x1_sr_op_r;

  aux_r4_haz      = (aux_x2_r4_sr | aux_x3_r4_sr_r | aux_ca_r4_sr_r);

  da_aux_raw      = da_sr_cd_haz | (da_uses_cd_aux & aux_r4_haz);
  sa_aux_raw      = sa_sr_cd_haz | (sa_uses_cd_aux & aux_r4_haz);

  sa_aux_haz_nxt  = (da_aux_raw & da_pass)
                  | sa_aux_raw
                  ;

end // dp_aux_raw_PROC


always @(posedge clk or posedge rst_a)
begin : dp_aux_haz_reg_PROC

  if (rst_a == 1'b1)
    sa_aux_haz_r  <= 1'b0;
  else
    sa_aux_haz_r  <= sa_aux_haz_nxt;

end // dp_aux_haz_reg_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Stall condition computations                                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : stall_cond_PROC

  //==========================================================================
  // DA stage delays SA stage if the SA stage has a dslot (1a) or eslot (1b) instruction
  // and the DA stage is currently empty. (1)
  // If there is a predicted branch with a delay slot, then the delay slot could
  // be a fragged error branch for which al_error_branch is asserted, that is only
  // relevant when the predicted branch itself is not an error_branch.
  // To be able to turn the predicted branch into an error branch when al_error_branch is
  // asserted for the delay slot, both must rendez-vous in SA/DA. (2)
  //
  //
  da_delay    = (~da_valid_r) & sa_valid_r         // (1)
              & (  sa_dslot_r                      // (1a)
                 | sa_ei_op_r                      // (1b)
                 | (sa_is_predicted_r & sa_with_dslot_r & ~sa_error_branch_r) // (2)
                );

  //==========================================================================
  // Rule 0:  No instruction is allowed to proceed beyond DA if there is
  //          an error branch instruction at X2, X3, CA or WA.
  //          This rule ensures that dependencies between a valid DA
  //          instruction and an incorrect downstream instruction are not
  //          allowed to enter the dependency pipeline. If the DA instruction
  //          will be killed by the error-branch restart, then the stall is
  //          irrelevant, but if the DA instruction is actually the re-fetched
  //          error-branch instruction, then it must not detect any dependence
  //          with downstream instructions until the error branch is both
  //          resolved and exited from the pipeline.
  //
  da_stall_r0 = da_valid_r
              & (   x2_error_branch_r
                  | x3_error_branch_r
                  | ca_error_branch_r
                  | wa_error_branch
                )
              ;

  //==========================================================================
  // uop_dep_stall holds up the DA stage in the following cases:
  //
  // 0. pending special register write is identified by graduation buffer empty
  //    signal ar_tags_empty_r. to cover the last write at wa stage we extend the
  //    period by one cycle (ar_tags_empty_dly_r)
  // 1. The DA instruction is the first instruction of an exception UOP prologue.
  //    In this case we must wait for the arithmetic flags (status32) to be
  //    fully updated by any pending flag updates in the graduation buffers.
  //    This is implemented by a simple solution based on the graduation buffer
  //    empty signal that guarantees no pending flag updates.
  //
  // 2. The DA instruction is the first instruction of an FIRQ prologue.
  //    In this case we must wait for when flags (status32) are fully updated,
  //    and there are no pending flag updates (similar to the exception case 1).
  //
  // 3. The DA instruction is the first instruction of an SIRQ special register
  //    store during an SIRQ prologue sequence. Note, for GPRs the normal
  //    dependency check handles dependencies, so we don't need to do anything
  //    for GPRs. However, for sepcial register (!gpr) we wait for  the
  //    graduation buffer to become empty.
  //
  // 4. The DA instruction is the first instruction of an SIRQ ISR.
  //    As the prologue sequence guarantees flag updates we don't need to do
  //    anything in addition to case (3).
  //
  // 5. The DA instruction is a regular instruction that must wait for stable
  //    flags due to flag restoration that took place during an SIRQ epilogue
  //    sequence. This is indicated by int_load_active .
  //    Note, when RGF_NUM_BANKS > 1, this condition also ensures that the
  //    bank ID has become stable.
  //
  // 6. Avoid fast RTIE being reached by interrupt service routine while
  //    prologue is not done.
  uop_dep_stall = (   da_valid_r
                    & (!(ar_tags_empty_r & (!ca_load_r) & ar_tags_empty_dly_r))  // (0)
                    & (   (da_uop_is_excpn_r & da_uop_prol_r)   // (1)
                        | (   da_uop_is_sirq_r
                            & da_uop_prol_r
                          )                                     // (3,4)
                      )
                  )
                | (   da_valid_r
                    & (!da_uop_is_excpn_r)
                    & (!da_uop_is_sirq_r)
                    & int_load_active                           // (5)
                  )
                | (   da_valid_r
                    & (int_in_prologue & da_rtie_op_r)          // (6)
                  )
                ;

  //==========================================================================
  // Rule 1:  If R0 or R1 is used as input to the AGU, when the instruction
  //          is at the Operand stage, and the producing Load instruction is
  //          at the X1 or X2 stage, or is in one of the graduation buffers
  //          then the SA-stage mem-op must stall.
  //          If R1 is used as an input to the AGU, under the same conditions,
  //          then SA-stage mem-op must also stall if the producing Load
  //          instruction is at the X3 stage, as there is no fast bypass
  //          into the second register source to the AGU from DC4.
  //
  sa_stall_r1 = (   sa_agu_uses_r0_r
                  & (   dp_sa_x1_r[`npuarc_R0_W1]
                      | dp_sa_x2_r[`npuarc_R0_W1]
                      | (dp_sa_ca_r[`npuarc_R0_W1] & (~ca_has_w1))
                      | dp_sa_ar0_r[`npuarc_R0_W1]
                      | dp_sa_ar1_r[`npuarc_R0_W1]
                      | dp_sa_ar2_r[`npuarc_R0_W1]
                      | dp_sa_ar3_r[`npuarc_R0_W1]
                      | dp_sa_ar4_r[`npuarc_R0_W1]
                      | dp_sa_ar5_r[`npuarc_R0_W1]
                      | dp_sa_ar6_r[`npuarc_R0_W1]
                      | dp_sa_ar7_r[`npuarc_R0_W1]
                    )
                )

              | (   sa_agu_uses_r1_r
                  & (   dp_sa_x1_r[`npuarc_R1_W1]
                      | dp_sa_x2_r[`npuarc_R1_W1]
                      | dp_sa_x3_r[`npuarc_R1_W1]
                      | (dp_sa_ca_r[`npuarc_R1_W1] & (~ca_has_w1))
                      | dp_sa_ar0_r[`npuarc_R1_W1]
                      | dp_sa_ar1_r[`npuarc_R1_W1]
                      | dp_sa_ar2_r[`npuarc_R1_W1]
                      | dp_sa_ar3_r[`npuarc_R1_W1]
                      | dp_sa_ar4_r[`npuarc_R1_W1]
                      | dp_sa_ar5_r[`npuarc_R1_W1]
                      | dp_sa_ar6_r[`npuarc_R1_W1]
                      | dp_sa_ar7_r[`npuarc_R1_W1]
                    )
                )
              ;

  //==========================================================================
  // Rule 2:  If R0 or R1 is used as input to the AGU, when the instruction
  //          is at the Operand stage, and the producing Load instruction is
  //          at the X3 stage, and the dmp_dc3_fast_byp signal is not
  //          asserted, then the SA-stage mem-op must stall.
  //          This stall is always applied if the producing Load instruction
  //          is a LDD, as bypass from the upper 32-bit half of and LDD is
  //          not supported.
  //
  sa_stall_r2 =  sa_agu_uses_r0_r
              &  dp_sa_x3_r[`npuarc_R0_W1]
              &  (x3_rf_wenb1_64_r | (~dmp_dc3_fast_byp))
              ;

  //==========================================================================
  // Rule 3:  If R0 or R1 is used as an input to the AGU, when the instruction
  //          is at the Operand stage, and the result of the producing non-Load
  //          operation is not available in the current cycle, then the
  //          Operand-stage mem-op must stall. The producing non-Load
  //          instruction could be at x1, x2, x3, ca, or one of the post-commit
  //          tags. Hence, the R0_W0 and R1_W0 dependence elements must be
  //          checked in dp_sa_x1_r, dp_sa_x2_r, dp_sa_x3_r, dp_sa_ca_r,
  //          and all dp_sa_arN_r for N covering all graduation buffers.
  //
  sa_stall_r3 = (   sa_agu_uses_r0_r
                  & (   (dp_sa_x1_r[`npuarc_R0_W0] & (~x1_has_w0))
                      | (dp_sa_x2_r[`npuarc_R0_W0] & (~x2_has_w0))
                      | (dp_sa_x3_r[`npuarc_R0_W0] & (~x3_has_w0))
                      | (dp_sa_ca_r[`npuarc_R0_W0] & (~ca_has_w0))
                    )
                )
              | (   sa_agu_uses_r1_r
                  & (   (dp_sa_x1_r[`npuarc_R1_W0] & (~x1_has_w0))
                      | (dp_sa_x2_r[`npuarc_R1_W0] & (~x2_has_w0))
                      | (dp_sa_x3_r[`npuarc_R1_W0] & (~x3_has_w0))
                      | (dp_sa_ca_r[`npuarc_R1_W0] & (~ca_has_w0))
                    )
                )
              ;

  //==========================================================================
  // Rule 4a: If R0 or R1 is dependent on any downstream W0 or W1, and the
  //          result for W0 or W1 is not available in the current cycle,
  //          and the instruction must obtain all operands in the SA stage.
  //          This constraint is indicated by the ucode bit sa_opds_in_sa_r.
  //
  sa_stall_r4 = sa_opds_in_sa_r
              & (   ((dp_sa_x1_r[`npuarc_R0_W0] | dp_sa_x1_r[`npuarc_R1_W0]) & (~x1_has_w0))
                  | ((dp_sa_x2_r[`npuarc_R0_W0] | dp_sa_x2_r[`npuarc_R1_W0]) & (~x2_has_w0))
                  | ((dp_sa_x3_r[`npuarc_R0_W0] | dp_sa_x3_r[`npuarc_R1_W0]) & (~x3_has_w0))
                  | ((dp_sa_ca_r[`npuarc_R0_W0] | dp_sa_ca_r[`npuarc_R1_W0]) & (~ca_has_w0))
                  | ( dp_sa_x1_r[`npuarc_R0_W1] | dp_sa_x1_r[`npuarc_R1_W1])
                  | ( dp_sa_x2_r[`npuarc_R0_W1] | dp_sa_x2_r[`npuarc_R1_W1])
                  | ( dp_sa_x3_r[`npuarc_R0_W1] | dp_sa_x3_r[`npuarc_R1_W1])
                  | ((dp_sa_ca_r[`npuarc_R0_W1] | dp_sa_ca_r[`npuarc_R1_W1]) & (~ca_has_w1))
                  | (dp_sa_ar0_r[`npuarc_R0_W1] | dp_sa_ar0_r[`npuarc_R1_W1])
                  | (dp_sa_ar1_r[`npuarc_R0_W1] | dp_sa_ar1_r[`npuarc_R1_W1])
                  | (dp_sa_ar2_r[`npuarc_R0_W1] | dp_sa_ar2_r[`npuarc_R1_W1])
                  | (dp_sa_ar3_r[`npuarc_R0_W1] | dp_sa_ar3_r[`npuarc_R1_W1])
                  | (dp_sa_ar4_r[`npuarc_R0_W1] | dp_sa_ar4_r[`npuarc_R1_W1])
                  | (dp_sa_ar5_r[`npuarc_R0_W1] | dp_sa_ar5_r[`npuarc_R1_W1])
                  | (dp_sa_ar6_r[`npuarc_R0_W1] | dp_sa_ar6_r[`npuarc_R1_W1])
                  | (dp_sa_ar7_r[`npuarc_R0_W1] | dp_sa_ar7_r[`npuarc_R1_W1])
              )
              ;

  //==========================================================================
  // Rule 5:  If the instruction at SA is dependent upon the speculative flags
  //          retained by X2 (either as a consumer or a producer), the instruction
  //          must stall until any outstanding flag producing instruction (in a
  //          prior D-slot) has committed.
  //
  sa_stall_r5 = flag_dependency_at_sa
              ;

  //==========================================================================
  // Rule 6:  If the instruction at SA requires a link address derived from
  //          the size of the instruction at DA, stall SA until a valid
  //          and instruction is present in DA, and it can be guaranteed that
  //          if the current SA instruction is not mispredicted then the
  //          DA instruction is also not mispredicted. The latter condition
  //          cannot be guaranteed if the SA instruction is in a delay slot
  //          and itself has a delay slot. In that case, its delay slot
  //          could have been mispredicted when fetching the previous branch.
  //          This hazard only occurs for a branch with delay slot that is
  //          also in a delay slot, and is overcome by stalling the SA stage
  //          until stages X1..CA have drained. This is a very rare corner case.
  //
  sa_stall_r6 = sa_dslot_r
              & sa_link_r
              & (   (~da_valid_r)
                  | (   sa_in_dslot_r
                      & (   x1_valid_r
                          | x2_valid_r
                          | x3_valid_r
                          | ca_valid_r
                        )
                    )
                )
              ;

  //==========================================================================
  // Rule 14: If the instruction at SA is potentially dependent on a 64-bit
  //          result from an instruction that has not yet written its result,
  //          and one of the results from that instruction is partially killed
  //          by a 32-bit result from an intervening instruction, then the
  //          SA instruction cannot advance. This is due to an imprecise
  //          dependency analysis, caused by the partial kill from the
  //          intervening instruction. Software can avoid these stalls by
  //          not reusing one of the destination registers from a 64-bit
  //          register pair result until 5 instructions after the first
  //          64-bit instruction.
  //
  sa_stall_r14    = 1'b0
                  | (   (dp_sa_x2_r[`npuarc_R0_W0] | dp_sa_x2_r[`npuarc_R1_W0]   )
                      & (dp_x1_x2_r[`npuarc_W0_HI]                        )
                    )
                  | (   (dp_sa_x3_r[`npuarc_R0_W0] | dp_sa_x3_r[`npuarc_R1_W0]   )
                      & (dp_x1_x3_r[`npuarc_W0_HI] | dp_x2_x3_r[`npuarc_W0_HI]   )
                    )
                  | (   (dp_sa_ca_r[`npuarc_R0_W0] | dp_sa_ca_r[`npuarc_R1_W0]   )
                      & (   dp_x1_ca_r[`npuarc_W0_HI] | dp_x2_ca_r[`npuarc_W0_HI]
                          | dp_x3_ca_r[`npuarc_W0_HI]
                        )
                    )
                  | (   (dp_sa_wa_r[`npuarc_R0_W0] | dp_sa_wa_r[`npuarc_R1_W0]   )
                      & (   dp_x1_wa_r[`npuarc_W0_HI] | dp_x2_wa_r[`npuarc_W0_HI]
                          | dp_x3_wa_r[`npuarc_W0_HI] | dp_ca_wa_r[`npuarc_W0_HI]
                        )
                    )
                  | (   (dp_sa_x2_r[`npuarc_R0_W1] | dp_sa_x2_r[`npuarc_R1_W1]   )
                      & (dp_x1_x2_r[`npuarc_W1_HI]                        )
                    )
                  | (   (dp_sa_x3_r[`npuarc_R0_W1] | dp_sa_x3_r[`npuarc_R1_W1]   )
                      & (dp_x1_x3_r[`npuarc_W1_HI] | dp_x2_x3_r[`npuarc_W1_HI]   )
                    )
                  | (   (dp_sa_ca_r[`npuarc_R0_W1] | dp_sa_ca_r[`npuarc_R1_W1]   )
                      & (   dp_x1_ca_r[`npuarc_W1_HI] | dp_x2_ca_r[`npuarc_W1_HI]
                          | dp_x3_ca_r[`npuarc_W1_HI]
                        )
                    )
                  | (   (dp_sa_wa_r[`npuarc_R0_W1] | dp_sa_wa_r[`npuarc_R1_W1]   )
                      & (   dp_x1_wa_r[`npuarc_W1_HI] | dp_x2_wa_r[`npuarc_W1_HI]
                          | dp_x3_wa_r[`npuarc_W1_HI] | dp_ca_wa_r[`npuarc_W1_HI]
                        )
                    )
                  | (   (dp_sa_ar0_r[`npuarc_R0_W1] | dp_sa_ar0_r[`npuarc_R1_W1] )
                      & (   dp_x1_ar0_r[`npuarc_W1_HI] | dp_x2_ar0_r[`npuarc_W1_HI]
                          | dp_x3_ar0_r[`npuarc_W1_HI] | dp_ca_ar0_r[`npuarc_W1_HI]
                        )
                    )
                  | (   (dp_sa_ar1_r[`npuarc_R0_W1] | dp_sa_ar1_r[`npuarc_R1_W1] )
                      & (   dp_x1_ar1_r[`npuarc_W1_HI] | dp_x2_ar1_r[`npuarc_W1_HI]
                          | dp_x3_ar1_r[`npuarc_W1_HI] | dp_ca_ar1_r[`npuarc_W1_HI]
                        )
                    )
                  | (   (dp_sa_ar2_r[`npuarc_R0_W1] | dp_sa_ar2_r[`npuarc_R1_W1] )
                      & (   dp_x1_ar2_r[`npuarc_W1_HI] | dp_x2_ar2_r[`npuarc_W1_HI]
                          | dp_x3_ar2_r[`npuarc_W1_HI] | dp_ca_ar2_r[`npuarc_W1_HI]
                        )
                    )
                  | (   (dp_sa_ar3_r[`npuarc_R0_W1] | dp_sa_ar3_r[`npuarc_R1_W1] )
                      & (   dp_x1_ar3_r[`npuarc_W1_HI] | dp_x2_ar3_r[`npuarc_W1_HI]
                          | dp_x3_ar3_r[`npuarc_W1_HI] | dp_ca_ar3_r[`npuarc_W1_HI]
                        )
                    )
                  | (   (dp_sa_ar4_r[`npuarc_R0_W1] | dp_sa_ar4_r[`npuarc_R1_W1] )
                      & (   dp_x1_ar4_r[`npuarc_W1_HI] | dp_x2_ar4_r[`npuarc_W1_HI]
                          | dp_x3_ar4_r[`npuarc_W1_HI] | dp_ca_ar4_r[`npuarc_W1_HI]
                        )
                    )
                  | (   (dp_sa_ar5_r[`npuarc_R0_W1] | dp_sa_ar5_r[`npuarc_R1_W1] )
                      & (   dp_x1_ar5_r[`npuarc_W1_HI] | dp_x2_ar5_r[`npuarc_W1_HI]
                          | dp_x3_ar5_r[`npuarc_W1_HI] | dp_ca_ar5_r[`npuarc_W1_HI]
                        )
                    )
                  | (   (dp_sa_ar6_r[`npuarc_R0_W1] | dp_sa_ar6_r[`npuarc_R1_W1] )
                      & (   dp_x1_ar6_r[`npuarc_W1_HI] | dp_x2_ar6_r[`npuarc_W1_HI]
                          | dp_x3_ar6_r[`npuarc_W1_HI] | dp_ca_ar6_r[`npuarc_W1_HI]
                        )
                    )
                  | (   (dp_sa_ar7_r[`npuarc_R0_W1] | dp_sa_ar7_r[`npuarc_R1_W1] )
                      & (   dp_x1_ar7_r[`npuarc_W1_HI] | dp_x2_ar7_r[`npuarc_W1_HI]
                          | dp_x3_ar7_r[`npuarc_W1_HI] | dp_ca_ar7_r[`npuarc_W1_HI]
                        )
                    )
                  ;

  //==========================================================================
  // Rule 5:  If R0 is used as input to the AGU, when the instruction is at
  //          the X1 stage, and the producing Load instruction has not yet
  //          advanced to the CA stage, then the X1-stage mem-op must stall.
  //          This rule covers the case where the SA instruction was given
  //          permission to advance to X1 due to assertion of dmp_dc3_fast_byp
  //          but when it advanced into X1, the producing LD instruction
  //          remained stalled at X3. The mem-op at X1 must stall in X1
  //          if the dependency matrix indicates (via dp_x1_x3_r[`R0_W1])
  //          that the producer of R0 is still in the X3 stage.
  //          This stall is retained through the cycle in which an LDD
  //          retires, as bypass from the high register of an LDD is not
  //          supported. During that cycle, the x1_src0_r register will
  //          capture the retiring value.
  //
  x1_stall_r5 = x1_agu_uses_r0_r
              & x1_read_r0_r
              & (   dp_x1_x3_r[`npuarc_R0_W1]
                  | (~(  (   dp_x1_ca_r[`npuarc_R0_W1]
                          & dmp_dc4_fast_byp_r
                          & (~dmp_dc4_fast_miss_r)
                        )
                      | (dp_x1_wa_r[`npuarc_R0_W1] & (~wa_rf_wenb1_64_r))
                     )
                   )
                 )
              ;

  //==========================================================================
  // Rule 4b: If R0 or R1 is dependent on any downstream W0 or W1, and the
  //          result for W0 or W1 is not available in the current cycle,
  //          and the instruction must obtain all operands in the X1 stage.
  //          This constraint is indicated by the ucode bit x1_opds_in_x1_r.
  //
  x1_stall_r4 = x1_opds_in_x1_r
              & (   ((dp_x1_x2_r[`npuarc_R0_W0] | dp_x1_x2_r[`npuarc_R1_W0]) & (~x2_has_w0))
                  | ((dp_x1_x3_r[`npuarc_R0_W0] | dp_x1_x3_r[`npuarc_R1_W0]) & (~x3_has_w0))
                  | ((dp_x1_ca_r[`npuarc_R0_W0] | dp_x1_ca_r[`npuarc_R1_W0]) & (~ca_has_w0))
                  | ( dp_x1_x2_r[`npuarc_R0_W1] | dp_x1_x2_r[`npuarc_R1_W1])
                  | ( dp_x1_x3_r[`npuarc_R0_W1] | dp_x1_x3_r[`npuarc_R1_W1])
                  | ((dp_x1_ca_r[`npuarc_R0_W1] | dp_x1_ca_r[`npuarc_R1_W1]) & (~ca_has_w1))
                  | (dp_x1_ar0_r[`npuarc_R0_W1] | dp_x1_ar0_r[`npuarc_R1_W1])
                  | (dp_x1_ar1_r[`npuarc_R0_W1] | dp_x1_ar1_r[`npuarc_R1_W1])
                  | (dp_x1_ar2_r[`npuarc_R0_W1] | dp_x1_ar2_r[`npuarc_R1_W1])
                  | (dp_x1_ar3_r[`npuarc_R0_W1] | dp_x1_ar3_r[`npuarc_R1_W1])
                  | (dp_x1_ar4_r[`npuarc_R0_W1] | dp_x1_ar4_r[`npuarc_R1_W1])
                  | (dp_x1_ar5_r[`npuarc_R0_W1] | dp_x1_ar5_r[`npuarc_R1_W1])
                  | (dp_x1_ar6_r[`npuarc_R0_W1] | dp_x1_ar6_r[`npuarc_R1_W1])
                  | (dp_x1_ar7_r[`npuarc_R0_W1] | dp_x1_ar7_r[`npuarc_R1_W1])
              )
              ;

  //==========================================================================
  // Detect a RAW dependency at the SA stage on the ACCL or ACCH registers
  // due to an explicit register read from r58 or r59 at the SA stage when
  // there exists a pending implicit accumulator update in any downstream
  // stage or in the graduation buffers.
  //
  sa_acc_raw    = sa_reads_acc_r
                & (   x1_acc_wenb_r
                    | x2_acc_wenb_r
                    | x3_acc_wenb_r
                    | ca_acc_wenb_r
                    | wa_acc_wenb_r
                    | ar0_writes_acc_r
                    | ar1_writes_acc_r
                    | ar2_writes_acc_r
                    | ar3_writes_acc_r
                    | ar4_writes_acc_r
                    | ar5_writes_acc_r
                    | ar6_writes_acc_r
                    | ar7_writes_acc_r
                  )
                ;


  //==========================================================================
  // Detect a RAW dependency at the SA stage against any downstream stage
  // that has the <xx>_cc_byp_64_haz_r bit set to 1. This signifies that
  // the matching downstream stage has a conditional definition of the
  // upper 32 bits of its destination result that is, or may be, predicated
  // false. In such cases, there is no forwarding of the false high result,
  // and the dependent SA instruction must wait until the instruction has
  // exited the pipeline.
  //
  sa_stall_r15  = (   (dp_sa_x1_r[`npuarc_R0_W0] | dp_sa_x1_r[`npuarc_R1_W0])
                    & x1_cc_byp_64_haz_r)
                | (   (dp_sa_x2_r[`npuarc_R0_W0] | dp_sa_x2_r[`npuarc_R1_W0])
                    & x2_cc_byp_64_haz_r)
                | (   (dp_sa_x3_r[`npuarc_R0_W0] | dp_sa_x3_r[`npuarc_R1_W0])
                    & x3_cc_byp_64_haz_r)
                | (   (dp_sa_ca_r[`npuarc_R0_W0] | dp_sa_ca_r[`npuarc_R1_W0])
                    & ca_cc_byp_64_haz_r)
                | (   (dp_sa_wa_r[`npuarc_R0_W0] | dp_sa_wa_r[`npuarc_R1_W0])
                    & wa_cc_byp_64_haz_r)
                ;

  //==========================================================================
  // If there is a valid instruction at X3 with a pending error branch
  // signal, then there is stale dependency information in the dependency
  // pipeline registers. This means that any valid SA instruction cannot
  // progress until the X3 instruction has moved into CA, or has been killed.
  //
  sa_stall_r17  = sa_valid_r & x3_valid_r & x3_error_branch_r;

  //==========================================================================
  // Rule 6:  If the Exec1-stage instruction must evaluate at Exec1, and it
  //          depends on the ZNCV flags to evaluate either its result or its
  //          predication outcome, and flags are uncertain due to a downstream
  //          flag-defining instruction that has not yet defined its flag
  //          result, then the Exec1-stage instruction must stall.
  //
  x1_stall_r6 = x1_no_eval & (x1_opds_in_sa_r | x1_opds_in_x1_r | x1_rgf_link_r)
              | (x1_valid_r & update_flags_x2)
              ;

  //==========================================================================
  // Rule 7:  If there is a structural hazard on dispatching the X1 instruction
  //          to any of the functional units that begins executing in X2,
  //          then stall the instruction at X1.
  //
  x1_stall_r7 = 1'b0
              | (x1_div_op_r & div_busy_r)      // unable to dispatch DIV/REM
              ;

  //==========================================================================
  // Rule 8:  If there is a mem-op at Exec1 and the dmp reports that it is
  //          busy (and cannot accept a new mem-op), then the Exec1-stage
  //          mem-op must stall. During this time, the Exec1 stage detects
  //          if any R0_W1 or R1_W1 dependency becomes resolved while the
  //          Exec1-stage mem-op is stalled. If this happens, the mem-op
  //          is poisoned and a Missed Dependency Replay will eventually
  //          happen. This is a rare case.
  //
  x1_stall_r8 = (x1_load_r | x1_store_r) & dc1_stall;

  //==========================================================================
  // Rule 15: If there is a mem-op at X1 and there is a SYNC or WEVT or BRK instruction
  //          at X2 or X3, then stall the mem-op in X1 to prevent a
  //          deadlock on mem-op at X2 when the write queue is draining
  //          under an x3_stall_r12 condition.
  //
  x1_stall_r15 = (x1_load_r    | x1_store_r   )
               & (x2_sync_op_r | x2_wevt_op | x2_brk_op_r | x2_flag_op_r |
                  x3_sync_op_r | x3_wevt_op | x3_brk_op_r | x3_flag_op_r)
               ;


  //==========================================================================
  // Rule 20: If there is a SYNC or WEVT or BRK instruction
  //          drain all the ahead of this instruction.
  //          This should ensure any after effects (exception/branches) are
  //          resolved and this instruction is free to proceed without
  //          any interference.
  //
  x1_stall_r20 = (x1_brk_op_r | x1_sleep_op_r)
               & (x2_valid_r | x3_valid_r | ca_valid_r | ~ar_tags_empty_r)
               ;

  //==========================================================================
  // Rule 21: If there is a pending Exception
  //          complete all the prior instructions to the exception.
  //          This should ensure any after effects (exception/branches) are
  //          resolved and this instruction is free to proceed without
  //          any interference.
  //
  x1_stall_r21   = (excpn_in_prologue_r)
                 & (~ar_tags_empty_r)
                 ;

  //==========================================================================
  // x2_stall_bld is required in builds with MMU so that a branch-and-link
  // instruction with the x2_pg_xing_replay_r attribute waits at X2 until
  // the downstream pipeline stages have drained completely. This is to ensure
  // that no downstream instruction can contend with this branch's delay-slot
  // when it requires access to the Branch Commit interface at the non-standard
  // X2 stage (so that it can commit the report an error branch before its
  // parent branch commits).
  //
  x2_stall_bld  = x2_pg_xing_replay_r
                & (   x3_valid_r
                    | ca_valid_r
                    | wa_store_r
                    | (~ar_tags_empty_r)
                    | (~dmp_idle_r)
                  )
                ;
  //==========================================================================
  // Rule 9:  If R0 or R1, for the Exec3-stage instruction, depends on W0 or W1
  //          at the Commit stage, and the relevant W0 or W1 does not make its
  //          result available in the current cycle, then the Exec3-stage
  //          instruction must stall.
  //
  x3_stall_r9 = ((dp_x3_ca_r[`npuarc_R0_W0] | dp_x3_ca_r[`npuarc_R1_W0]) & (~ca_has_w0))
              | ((dp_x3_ca_r[`npuarc_R0_W1] | dp_x3_ca_r[`npuarc_R1_W1]) & (~ca_has_w1))
              ;

  //==========================================================================
  // Rule 10: If the Exec3-stage instruction has a matching Rx_Wy dependency
  //          with any post-commit graduation buffer entry, then that Exec3-
  //          stage instruction must stall.
  //          The register definitions in the post-commit buffers that may
  //          trigger this dependency could be killed by an intervening
  //          redefinition at the Commit stage. However, in that case there
  //          would also be a WAW hazard between the redefinition at the
  //          Commit stage and the definition in the post-commit buffers.
  //          That will stall the Commit stage, and hence the x3 stage anyway
  //          so it does not matter if this stall rule also applies.
  //
  x3_stall_r10 = dp_x3_ar0_r[`npuarc_R0_W1] | dp_x3_ar0_r[`npuarc_R1_W1]
               | dp_x3_ar1_r[`npuarc_R0_W1] | dp_x3_ar1_r[`npuarc_R1_W1]
               | dp_x3_ar2_r[`npuarc_R0_W1] | dp_x3_ar2_r[`npuarc_R1_W1]
               | dp_x3_ar3_r[`npuarc_R0_W1] | dp_x3_ar3_r[`npuarc_R1_W1]
               | dp_x3_ar4_r[`npuarc_R0_W1] | dp_x3_ar4_r[`npuarc_R1_W1]
               | dp_x3_ar5_r[`npuarc_R0_W1] | dp_x3_ar5_r[`npuarc_R1_W1]
               | dp_x3_ar6_r[`npuarc_R0_W1] | dp_x3_ar6_r[`npuarc_R1_W1]
               | dp_x3_ar7_r[`npuarc_R0_W1] | dp_x3_ar7_r[`npuarc_R1_W1]
               ;

  //==========================================================================
  // Rule 12: If a SYNC instruction is present in X3, stall until all of the
  //          preceding instructions have committed and retired any result.
  //
  x3_stall_r12  = (   (x3_sync_op_r | x3_wevt_op | x3_brk_op_r | x3_flag_op_r)
                    & (~(   ar_tags_empty_r
                         & dmp_idle_r
                         & (~ca_valid_r)
                         & (~wa_store_r)
                       )
                      )
                  )
                | (    (  x3_trap_op_r
                        | x3_brk_op_r
                        | x3_rtie_op_r
                        | x3_flag_op_r
                        | (x3_aps_break_r & x3_valid_r)
                        | (x3_aps_halt_r & x3_valid_r)
                       )
                    & (~(   ar_tags_empty_r
                         & (~ca_valid_r)
                       )
                     )
                  )
                ;

  //==========================================================================
  // Rule 16: If an X3 instruction performs an implicit read of ACC, and
  //          there is an explicit definition of ACCL or ACCH in CA, WA,
  //          or any of the graduation buffers, then stall the X3 instruction.
  //          Also stall any accumulating operation in X3 if the CA insn
  //          writes to ACCL and/or ACCH, and these instructions don't match
  //          in terms of their vector/non-vector nature, or if the X3
  //          insn is a MACU.F and the CA insn is not also a MACU.F.
  //
  x3_stall_r16  = x3_acc_op_r
                & (   ca_writes_acc_r
                    | wa_writes_acc_r
                    | ar0_writes_acc_r
                    | ar1_writes_acc_r
                    | ar2_writes_acc_r
                    | ar3_writes_acc_r
                    | ar4_writes_acc_r
                    | ar5_writes_acc_r
                    | ar6_writes_acc_r
                    | ar7_writes_acc_r
                    | (   ca_acc_wenb_r
                        & (   (ca_vector_op_r != x3_vector_op_r)
                            | (   x3_macu_r
                                & x3_zncv_wen_r[`npuarc_V_FLAG]
                                & (!(ca_macu_r & ca_zncv_wen_r[`npuarc_V_FLAG]))
                              )
                          )
                      )
                  )
                ;

  //==========================================================================
  // Rule 17: An SCOND or any other ST instruction at X3 shall stall if there
  // is a LLOCK instruction currently at CA (including LLOCKD).
  // This conservatively stalls an X3 ST instruction, which may not in fact
  // touch the location locked by the LLOCK instruction at CA. However, in
  // practice most LLOCK instructions will not be followed by a ST instruction
  // and therefore this safety check is unlikely to be used often.
  //
  x3_stall_scond  = x3_store_r
                  & ca_locked_r & ca_load_r
                  ;

  //==========================================================================
  // Detect a WAW dependency at the CA stage on the ACCL or ACCH registers
  // due to a pending accumulator update in the graduation buffers and a
  // CA-stage accumulator update (whether explicit or implicit).
  //
  ca_acc_waw    = (ca_acc_wenb_r | ca_writes_acc_r)
                & (   ar0_writes_acc_r
                    | ar1_writes_acc_r
                    | ar2_writes_acc_r
                    | ar3_writes_acc_r
                    | ar4_writes_acc_r
                    | ar5_writes_acc_r
                    | ar6_writes_acc_r
                    | ar7_writes_acc_r
                  )
                ;

  //==========================================================================
  // Rule 11: If there is any WAW dependency active at the Commit stage,
  //          then the Commit-stage instruction must stall.
  //
  ca_stall_r11  = (   ca_waw_haz_r
                    | ca_acc_waw
                  );

  //==========================================================================
  // Rule 18: Any instruction that would modify the lock flag may not
  //          commit if there is a graduated exclusive operation that
  //          has not yet retired. This covers any LLOCK or SCOND
  //          operation at the Commit stage, when any ar*_exclusive_r bit
  //          is set to 1.
  //
  ar_excl_pending = ar0_exclusive_r
                  | ar1_exclusive_r
                  | ar2_exclusive_r
                  | ar3_exclusive_r
                  | ar4_exclusive_r
                  | ar5_exclusive_r
                  | ar6_exclusive_r
                  | ar7_exclusive_r
                  ;

  ca_stall_r18    = ar_excl_pending
                  & (   (ca_locked_r & (ca_load_r | ca_store_r))
                      | ca_wlfc_op
                    )
                  ;

  //==========================================================================
  // A branch-and-link instruction with delay slot insn may need to rendezvous
  // (again) with its delay-slot instruction when the branch-and-link is at CA.
  // This is required only when the ca_pg_xing_replay_r signal is asserted.
  // This rendezvous ensures that the delay-slot instruction reaches X3,
  // and has therefore signaled its error-branch status via a misprediction
  // on the Branch Commit interface, before the parent branch gets replayed
  // when it reaches CA.
  //
  ca_stall_bld    = ca_valid_r & ca_pg_xing_replay_r & (~x3_valid_r)
                  ;

  //==========================================================================
  // Combine stalling rules into stall signals for each stage that can stall.
  //==========================================================================

  // 1, The DA stage is stalled whenever there is an error-branch instruction
  //    at X2, X3, CA or WA, indicated by da_stall_r0.
  //
  // 2. An execution-slot instruction may stall at DA if there is a RAW hazard
  //    on the BTA register, which it requires in order to compute its return
  //    branch address. This address will be used to detect a mispredicted BTA
  //    for that instruction.
  //
  // 3. UOP sequence related stall -- see earlier comments for uop_dep_stall
  //
  // 4. bank swapping related stall --
  //    We need to make sure all registers are written with the correct bank ID
  //    before they can be used by following instructions
  //
  // 5. RTT freeze request
  //
  da_stall    = da_eslot_stall        // (2)
              | da_stall_r0           // (1)
              | uop_dep_stall         // (3)
              ;

  sa_stall    = sa_stall_r1
              | sa_stall_r2
              | sa_stall_r3
              | sa_stall_r4
              | sa_stall_r5
              | sa_stall_r6
              | sa_eia_hazard
              | sa_eia_hold           // blocking eia instr ahead
              | sa_aux_haz_r
              | sa_stall_r14
              | sa_stall_r15
              | sa_zol_stall
              | sa_acc_raw
              | sa_stall_r17
              | sa_dsync_stall
              | sa_dmb_stall
              | pending_eia_cc
              | holdup_excpn_r
              ;

  x1_stall    = x1_stall_r4
              | x1_stall_r5
              | x1_stall_r6
              | x1_stall_r7
              | x1_stall_r8
              | x1_stall_r15
              | x1_stall_r20
              | (   x1_valid_r
                  & da_rtt_stall_r    // Generic RTT Stall signal
                )
              | x1_dslot_stall
              | x1_eia_hold
              | x1_zol_stall
              ;

  x2_stall_r18 = (x3_rtie_op_r | ca_rtie_op_r)
               & (x2_load_r | x2_store_r)
               ;


  x2_stall    = dc2_stall
              | x2_excpn_stall
              | x2_stall_r18
              | x2_sc_stall
              | x2_eia_hold           // src64 blocking in x2
              | x2_stall_bld
              ;

  // EXU (and not DMP) x2_stall
  //
  x2_exu_stall = x2_excpn_stall
               | x2_stall_r18
               | x2_sc_stall
               | x2_stall_bld
               ;

  x3_stall    = x3_stall_r9
              | x3_stall_r10
              | x3_stall_r12

              | x3_stall_r16
              | wdt_x3_stall
              | aux_x3_stall
              | x3_flag_haz
              | x3_stall_scond
              | dmp_dc3_stall_r
              ;

  ca_stall    = dc4_stall
              | ca_tag_stall
              | ca_wa1_conflict
              | ca_stall_r11
              | ca_flag_haz
              | ca_sr_stall_rtie
              | ca_stall_r18
              | ca_stall_bld
              ;

   wa_stall    = 1'b0;

  ca_replay   = dc4_replay
              | (dc4_waw_replay_r & ca_stall_r11)
              | holdup_excpn_nxt
              ;

  ca_dc4_replay   = dc4_replay
              | (dc4_waw_replay_r & ca_stall_r11)
              ;

  //==========================================================================
  // The `xx_yy_dslot' signal is asserted if, and only if, the instruction
  // at stage xx is the delay-slot instruction of the branch/jump instruction
  // at stage yy.
  //
  da_wa_dslot = da_in_dslot_r // & wa_dslot
              & (~(   sa_valid_r
                   | x1_valid_r
                   | x2_valid_r
                   | x3_valid_r
                   | ca_valid_r
                   )
                 )
              ;

  //==========================================================================
  // SA insn is in the delay-slot of the X2 instruction if, and only if,
  // the X2 insn has the dslot attribute and there is no valid intervening
  // instruction at X1.
  //
  sa_x2_dslot = x2_dslot_r & (~(x1_valid_r));

  sa_wa_dslot = sa_in_dslot_r
              & (~(   x1_valid_r
                   | x2_valid_r
                   | x3_valid_r
                   | ca_valid_r
                  )
                 )
              ;

  //==========================================================================
  // X1 insn is in the delay-slot of the X1 instruction if, and only if,
  // the X2 insn has the dslot attribute. This is a static attribute,
  // that is used only to determine whether the X1 instruction should be
  // killed when an X2 misprediction takes place.
  //
  x1_x2_dslot = x2_dslot_r
              ;

  x1_wa_dslot = x1_in_dslot_r
              & (~(   x2_valid_r
                   | x3_valid_r
                   | ca_valid_r
                 )
                )
              ;

  x2_wa_dslot = x2_in_dslot_r
              & (~(   x3_valid_r
                   | ca_valid_r
                  )
                 )
              ;

  x3_wa_dslot = x3_in_dslot_r
              & (~(ca_valid_r))
              ;

  ca_wa_dslot = ca_in_dslot_r
              ;

  //==========================================================================
  // Define the conditions under which each pipeline stage is killed (flushed)
  // The rules for killing instructions are:
  //
  //  1. A pipeline flush originating from WA, due to exception, interrupt
  //     replay or error branch, will kill every EXU instruction from DA to CA.
  //     These are signaled with wa_restart_r == 1, and either
  //     wa_mispred_r == 0 or wa_error_branch_r == 1.
  //
  //  2. Branch misprediction flushes originating from WA, that are not
  //     error branches, will kill those instructions in stages DA thru
  //     CA that are not the delay slot of the mispredicted branch at WA.
  //     These are signaled with wa_restart_r == 1 and wa_mispred_r == 1
  //     and wa_error_branch_r == 0.
  //
  //  3. Branch misprediction flushes originating from X2 will always kill
  //     the instruction at DA, as this can never be the delay slot of the
  //     branch with delay-slot at X2 (the X1-SA dslot tie guarantees this).
  //     These are signaled with x2_restart_r == 1 and x2_mispred_r == 1.
  //
  //  4. Branch misprediction flushes originating from X2 will kill those
  //     instructions in stages SA or X1 that are not the delay slot of
  //     the mispredicted branch at X1. However, if the X2 misprediction
  //     is due to an error branch, then instructions in SA and X1 will
  //     always be killed.
  //     These are signaled with x2_restart_r == 1 and x2_mispred_r == 1.
  //
  da_kill     = x2_restart_r
              | (   wa_restart
                  & (~(wa_mispred_r & da_wa_dslot & (~wa_error_branch)))
                )
              ;

  sa_kill     = (   x2_restart_r
                  & (~(x2_mispred_r & sa_x2_dslot & (~x2_fragged_r)))
                )
              | (   wa_restart
                  & (~(wa_mispred_r & sa_wa_dslot & (~wa_error_branch)))
                )
              ;

  x1_kill     = (   x2_restart_r
                  & (~(x2_mispred_r & x1_x2_dslot & (~x2_fragged_r)))
                )
              | (   wa_restart
                  & (~(wa_mispred_r & x1_wa_dslot & (~wa_error_branch)))
                )
              ;

  wa_kills_x2 = wa_restart
              & (~(wa_mispred_r & x2_wa_dslot & (~wa_error_branch)))
              ;

  x2_kill     = wa_kills_x2
              ;

  x3_kill     = (   wa_restart
                  & (~(wa_mispred_r & x3_wa_dslot & (~wa_error_branch)))
                )
              ;

  ca_kill     = (   wa_restart
                  & (~(wa_mispred_r & ca_wa_dslot & (~wa_error_branch)))
                )
              | dc4_replay
              | wa_cmt_isi_evt
              | ct_replay
              | excpn_restart
              | hlt_restart
              | aps_break
              | aps_halt
              | ca_fragged_r
              | ca_error_branch_r
              | ca_pg_xing_replay_r
              | ca_iprot_viol_r
              | holdup_excpn_nxt
              ;

  ca_kill_no_iprot   = (   wa_restart
                  & (~(wa_mispred_r & ca_wa_dslot & (~wa_error_branch)))
                )
              | dc4_replay
              | wa_cmt_isi_evt
              | ct_replay
              | excpn_restart
              | hlt_restart
              | aps_break
              | aps_halt
              | ca_fragged_r
              | ca_error_branch_r
              | ca_pg_xing_replay_r
              ;

  // ca_kill_no_hlt is a ca_kill for any reason except a hlt_restart.
  // The hlt_restart after a BRK instruction needs to be prevented if there is
  // a ca_kill for any other reason that should kill that BRK instruction.

  ca_kill_no_hlt     = (   wa_restart
                  & (~(wa_mispred_r & ca_wa_dslot & (~wa_error_branch)))
                )
              | dc4_replay
              | ct_replay
              | excpn_restart
              | ca_fragged_r
              | ca_error_branch_r
              | ca_pg_xing_replay_r
              ;

  //==========================================================================
  // Define the stage control signals for the Writeback stage.
  //
  wa_holdup   = 1'b0;
  wa_retain   = 1'b0;
  wa_enable   = wa_restart | (~wa_retain);

  //==========================================================================
  // Define the stage control signals for the Commit stage.
  //
  ca_holdup   =  ca_valid_r & (wa_holdup | ca_stall);
  ca_retain   = ((ca_valid_r & wa_holdup) | ca_stall) & (~ca_kill);
  ca_enable   = ca_kill | (~ca_retain);
  ca_pass     = ca_valid_r & (~(ca_kill | ca_retain));
  ca_pass_no_hlt = ca_valid_r & (~(ca_kill_no_hlt | ca_retain));
  ca_pass_no_iprot = ca_valid_r & (~(ca_kill_no_iprot | ca_retain));

  //==========================================================================
  // Define the stage control signals for the Exec3 stage.
  //
  x3_holdup   =  x3_valid_r & (ca_holdup | x3_stall);
  x3_retain   = ((x3_valid_r & ca_holdup) | x3_stall) & (~x3_kill);
  x3_enable   = x3_kill | (~x3_retain);
  x3_pass     = x3_valid_r & (~(x3_kill | x3_retain));

  //==========================================================================
  // Define the stage control signals for the Exec2 stage.
  //
  x2_holdup   = x2_valid_r  & (x3_holdup | x2_stall);
  x2_retain   = ((x2_valid_r & x3_holdup) | x2_stall) & (~x2_kill);
  x2_enable   = x2_kill | (~x2_retain);
  x2_pass     = x2_valid_r & (~(x2_kill | x2_retain));

  //==========================================================================
  // Define the stage control signals for the Exec1 stage.
  //
  x1_holdup   = x1_valid_r  & (x2_holdup | x1_stall);
  x1_retain   = ((x1_valid_r & x2_holdup) | x1_stall) & (~x1_kill);
  x1_enable   = x1_kill | (~x1_retain);
  x1_pass     = x1_valid_r & (~(x1_kill | x1_retain));

  //==========================================================================
  // Define the stage control signals for the Operand stage.
  //
  sa_holdup   = sa_valid_r  & (x1_holdup | sa_stall);
  sa_retain   = ((sa_valid_r & (sa_stall | x1_holdup)) | da_delay) & (~sa_kill);
  sa_enable   = sa_kill | (~sa_retain);
  sa_pass     = sa_valid_r & (~(sa_kill | sa_retain));

  //==========================================================================
  // Define the stage control signals for the Decode stage.
  //
  da_holdup   = da_valid_r  & (sa_holdup | da_uop_busy_r | da_stall);
  da_retain   = ((da_valid_r & sa_holdup ) | da_stall) & (~da_kill);
  da_enable   = da_kill | (~da_retain);
  da_pass     = da_valid_r & (~(da_kill | da_retain));

  //==========================================================================
  // Each pipeline stage xx is considered to have advanced its instruction to
  // the subsequent pipeline stage yy if stage xx is ready to pass forward an
  // instruction (xx_pass == 1) and the next stage is enabled to receive a
  // new instruction (yy_enable == 1)).
  //
  da_adv  = da_pass & sa_enable;
  sa_adv  = sa_pass & x1_enable;
  x1_adv  = x1_pass & x2_enable;
  x2_adv  = x2_pass & x3_enable;
  x3_adv  = x3_pass & ca_enable;
  ca_adv  = ca_pass & wa_enable;

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Read-after-write dependency detection logic - at the Decode stage        //
//                                                                          //
// Signal dp_xx_yy[`R0_W0] indicates that a read-after-write dependency     //
// exists from the write-port 0 definition at stage yy to the register used //
// at stage xx as register operand 0 (the first register operand).          //
//                                                                          //
// Signal dp_xx_yy[`R0_W1] indicates that a read-after-write dependency     //
// exists from the write-port 1 definition at stage yy to the register used //
// at stage xx as register operand 0 (the first register operand).          //
//                                                                          //
// Signal dp_xx_yy[`R1_W0] indicates that a read-after-write dependency     //
// exists from the write-port 0 definition at stage yy to the register used //
// at stage xx as register operand 1 (the second register operand).         //
//                                                                          //
// Signal dp_xx_yy[`R1_W1] indicates that a read-after-write dependency     //
// exists from the write-port 1 definition at stage yy to the register used //
// at stage xx as register operand 1 (the second register operand).         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : da_raw_deps_PROC

  // -------------- dependencies from Operand stage instruction --------------

  da0_is_sa_pair0   = sa_rf_wenb0_r
                    & da_rf_renb0_r
                    & (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da0_is_sa_pair1   = sa_rf_wenb1_r
                    & da_rf_renb0_r
                    & (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_sa_pair0   = sa_rf_wenb0_r
                    & da_rf_renb1_r
                    & (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_sa_pair1   = sa_rf_wenb1_r
                    & da_rf_renb1_r
                    & (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_sa[`npuarc_R0_W0]  = da0_is_sa_pair0
                    & (   (da_rf_ra0_r[0] == sa_rf_wa0_r[0])
                        | da_rf_renb0_64_r
                        | sa_rf_wenb0_64_r
                      );

  dp_da_sa[`npuarc_R0_W1]  = da0_is_sa_pair1
                    & (   (da_rf_ra0_r[0] == sa_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | sa_rf_wenb1_64_r
                      );

  dp_da_sa[`npuarc_R1_W0]  = da1_is_sa_pair0
                    & (   (da_rf_ra1_r[0] == sa_rf_wa0_r[0])
                        | da_rf_renb1_64_r
                        | sa_rf_wenb0_64_r
                      );

  dp_da_sa[`npuarc_R1_W1]  = da1_is_sa_pair1
                    & (   (da_rf_ra1_r[0] == sa_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | sa_rf_wenb1_64_r
                      );

  // -------------- dependencies from Exec1 stage instruction ----------------

  da0_is_x1_pair0   = x1_rf_wenb0_r
                    & da_rf_renb0_r
                    & (    x1_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da0_is_x1_pair1   = x1_rf_wenb1_r
                    & da_rf_renb0_r
                    & (    x1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_x1_pair0   = x1_rf_wenb0_r
                    & da_rf_renb1_r
                    & (    x1_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_x1_pair1   = x1_rf_wenb1_r
                    & da_rf_renb1_r
                    & (    x1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_x1[`npuarc_R0_W0]  = da0_is_x1_pair0
                    & (   (da_rf_ra0_r[0] == x1_rf_wa0_r[0])
                        | da_rf_renb0_64_r
                        | x1_rf_wenb0_64_r
                      );

  dp_da_x1[`npuarc_R0_W1]  = da0_is_x1_pair1
                    & (   (da_rf_ra0_r[0] == x1_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | x1_rf_wenb1_64_r
                      );

  dp_da_x1[`npuarc_R1_W0]  = da1_is_x1_pair0
                    & (   (da_rf_ra1_r[0] == x1_rf_wa0_r[0])
                        | da_rf_renb1_64_r
                        | x1_rf_wenb0_64_r
                      );

  dp_da_x1[`npuarc_R1_W1]  = da1_is_x1_pair1
                    & (   (da_rf_ra1_r[0] == x1_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | x1_rf_wenb1_64_r
                      );

  // -------------- dependencies from Exec2 stage instruction ----------------

  da0_is_x2_pair0   = x2_rf_wenb0_r
                    & da_rf_renb0_r
                    & (    x2_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da0_is_x2_pair1   = x2_rf_wenb1_r
                    & da_rf_renb0_r
                    & (    x2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_x2_pair0   = x2_rf_wenb0_r
                    & da_rf_renb1_r
                    & (    x2_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_x2_pair1   = x2_rf_wenb1_r
                    & da_rf_renb1_r
                    & (    x2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_x2[`npuarc_R0_W0]  = da0_is_x2_pair0
                    & (   (da_rf_ra0_r[0] == x2_rf_wa0_r[0])
                        | da_rf_renb0_64_r
                        | x2_rf_wenb0_64_r
                      );

  dp_da_x2[`npuarc_R0_W1]  = da0_is_x2_pair1
                    & (   (da_rf_ra0_r[0] == x2_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | x2_rf_wenb1_64_r
                      );

  dp_da_x2[`npuarc_R1_W0]  = da1_is_x2_pair0
                    & (   (da_rf_ra1_r[0] == x2_rf_wa0_r[0])
                        | da_rf_renb1_64_r
                        | x2_rf_wenb0_64_r
                      );

  dp_da_x2[`npuarc_R1_W1]  = da1_is_x2_pair1
                    & (   (da_rf_ra1_r[0] == x2_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | x2_rf_wenb1_64_r
                      );

  // -------------- dependencies from Exec3 stage instruction ----------------

  da0_is_x3_pair0   = x3_rf_wenb0_r
                    & da_rf_renb0_r
                    & (    x3_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da0_is_x3_pair1   = x3_rf_wenb1_r
                    & da_rf_renb0_r
                    & (    x3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_x3_pair0   = x3_rf_wenb0_r
                    & da_rf_renb1_r
                    & (    x3_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_x3_pair1   = x3_rf_wenb1_r
                    & da_rf_renb1_r
                    & (    x3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_x3[`npuarc_R0_W0]  = da0_is_x3_pair0
                    & (   (da_rf_ra0_r[0] == x3_rf_wa0_r[0])
                        | da_rf_renb0_64_r
                        | x3_rf_wenb0_64_r
                      );

  dp_da_x3[`npuarc_R0_W1]  = da0_is_x3_pair1
                    & (   (da_rf_ra0_r[0] == x3_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | x3_rf_wenb1_64_r
                      );

  dp_da_x3[`npuarc_R1_W0]  = da1_is_x3_pair0
                    & (   (da_rf_ra1_r[0] == x3_rf_wa0_r[0])
                        | da_rf_renb1_64_r
                        | x3_rf_wenb0_64_r
                      );

  dp_da_x3[`npuarc_R1_W1]  = da1_is_x3_pair1
                    & (   (da_rf_ra1_r[0] == x3_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | x3_rf_wenb1_64_r
                      );

  // -------------- dependencies from Commit stage instruction ---------------

  da0_is_ca_pair0   = ca_rf_wenb0_r
                    & da_rf_renb0_r
                    & (    ca_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da0_is_ca_pair1   = ca_rf_wenb1_r
                    & da_rf_renb0_r
                    & (    ca_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_ca_pair0   = ca_rf_wenb0_r
                    & da_rf_renb1_r
                    & (    ca_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_ca_pair1   = ca_rf_wenb1_r
                    & da_rf_renb1_r
                    & (    ca_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_ca[`npuarc_R0_W0]  = da0_is_ca_pair0
                    & (   (da_rf_ra0_r[0] == ca_rf_wa0_r[0])
                        | da_rf_renb0_64_r
                        | ca_rf_wenb0_64_r
                      );

  dp_da_ca[`npuarc_R0_W1]  = da0_is_ca_pair1
                    & (   (da_rf_ra0_r[0] == ca_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | ca_rf_wenb1_64_r
                      );

  dp_da_ca[`npuarc_R1_W0]  = da1_is_ca_pair0
                    & (   (da_rf_ra1_r[0] == ca_rf_wa0_r[0])
                        | da_rf_renb1_64_r
                        | ca_rf_wenb0_64_r
                      );

  dp_da_ca[`npuarc_R1_W1]  = da1_is_ca_pair1
                    & (   (da_rf_ra1_r[0] == ca_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | ca_rf_wenb1_64_r
                      );

  // -------------- dependencies from Writeback stage instruction ------------

  da0_is_wa_pair0   = wa_rf_wenb0_r
                    & da_rf_renb0_r
                    & (    wa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da0_is_wa_pair1   = wa_rf_wenb1_r
                    & da_rf_renb0_r
                    & (    wa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_wa_pair0   = wa_rf_wenb0_r
                    & da_rf_renb1_r
                    & (    wa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_wa_pair1   = wa_rf_wenb1_r
                    & da_rf_renb1_r
                    & (    wa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_wa[`npuarc_R0_W0]  = da0_is_wa_pair0
                    & (   (da_rf_ra0_r[0] == wa_rf_wa0_r[0])
                        | da_rf_renb0_64_r
                        | wa_rf_wenb0_64_r
                      );

  dp_da_wa[`npuarc_R0_W1]  = da0_is_wa_pair1
                    & (   (da_rf_ra0_r[0] == wa_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | wa_rf_wenb1_64_r
                      );

  dp_da_wa[`npuarc_R1_W0]  = da1_is_wa_pair0
                    & (   (da_rf_ra1_r[0] == wa_rf_wa0_r[0])
                        | da_rf_renb1_64_r
                        | wa_rf_wenb0_64_r
                      );

  dp_da_wa[`npuarc_R1_W1]  = da1_is_wa_pair1
                    & (   (da_rf_ra1_r[0] == wa_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | wa_rf_wenb1_64_r
                      );

  // -------------- dependencies from post-commit context 8 ------------------

  da0_is_ar0_pair1   = ar0_rf_wenbs
                    & da_rf_renb0_r
                    & (    ar0_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_ar0_pair1   = ar0_rf_wenbs
                    & da_rf_renb1_r
                    & (    ar0_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_ar0[`npuarc_R0_W1]  = da0_is_ar0_pair1
                    & (   (da_rf_ra0_r[0] == ar0_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | ar0_rf_wenb1_64_r
                      );

  dp_da_ar0[`npuarc_R1_W1]  = da1_is_ar0_pair1
                    & (   (da_rf_ra1_r[0] == ar0_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | ar0_rf_wenb1_64_r
                      );

  da0_is_ar1_pair1   = ar1_rf_wenbs
                    & da_rf_renb0_r
                    & (    ar1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_ar1_pair1   = ar1_rf_wenbs
                    & da_rf_renb1_r
                    & (    ar1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_ar1[`npuarc_R0_W1]  = da0_is_ar1_pair1
                    & (   (da_rf_ra0_r[0] == ar1_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | ar1_rf_wenb1_64_r
                      );

  dp_da_ar1[`npuarc_R1_W1]  = da1_is_ar1_pair1
                    & (   (da_rf_ra1_r[0] == ar1_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | ar1_rf_wenb1_64_r
                      );

  da0_is_ar2_pair1   = ar2_rf_wenbs
                    & da_rf_renb0_r
                    & (    ar2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_ar2_pair1   = ar2_rf_wenbs
                    & da_rf_renb1_r
                    & (    ar2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_ar2[`npuarc_R0_W1]  = da0_is_ar2_pair1
                    & (   (da_rf_ra0_r[0] == ar2_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | ar2_rf_wenb1_64_r
                      );

  dp_da_ar2[`npuarc_R1_W1]  = da1_is_ar2_pair1
                    & (   (da_rf_ra1_r[0] == ar2_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | ar2_rf_wenb1_64_r
                      );

  da0_is_ar3_pair1   = ar3_rf_wenbs
                    & da_rf_renb0_r
                    & (    ar3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_ar3_pair1   = ar3_rf_wenbs
                    & da_rf_renb1_r
                    & (    ar3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_ar3[`npuarc_R0_W1]  = da0_is_ar3_pair1
                    & (   (da_rf_ra0_r[0] == ar3_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | ar3_rf_wenb1_64_r
                      );

  dp_da_ar3[`npuarc_R1_W1]  = da1_is_ar3_pair1
                    & (   (da_rf_ra1_r[0] == ar3_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | ar3_rf_wenb1_64_r
                      );

  da0_is_ar4_pair1   = ar4_rf_wenbs
                    & da_rf_renb0_r
                    & (    ar4_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_ar4_pair1   = ar4_rf_wenbs
                    & da_rf_renb1_r
                    & (    ar4_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_ar4[`npuarc_R0_W1]  = da0_is_ar4_pair1
                    & (   (da_rf_ra0_r[0] == ar4_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | ar4_rf_wenb1_64_r
                      );

  dp_da_ar4[`npuarc_R1_W1]  = da1_is_ar4_pair1
                    & (   (da_rf_ra1_r[0] == ar4_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | ar4_rf_wenb1_64_r
                      );

  da0_is_ar5_pair1   = ar5_rf_wenbs
                    & da_rf_renb0_r
                    & (    ar5_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_ar5_pair1   = ar5_rf_wenbs
                    & da_rf_renb1_r
                    & (    ar5_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_ar5[`npuarc_R0_W1]  = da0_is_ar5_pair1
                    & (   (da_rf_ra0_r[0] == ar5_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | ar5_rf_wenb1_64_r
                      );

  dp_da_ar5[`npuarc_R1_W1]  = da1_is_ar5_pair1
                    & (   (da_rf_ra1_r[0] == ar5_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | ar5_rf_wenb1_64_r
                      );

  da0_is_ar6_pair1   = ar6_rf_wenbs
                    & da_rf_renb0_r
                    & (    ar6_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_ar6_pair1   = ar6_rf_wenbs
                    & da_rf_renb1_r
                    & (    ar6_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_ar6[`npuarc_R0_W1]  = da0_is_ar6_pair1
                    & (   (da_rf_ra0_r[0] == ar6_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | ar6_rf_wenb1_64_r
                      );

  dp_da_ar6[`npuarc_R1_W1]  = da1_is_ar6_pair1
                    & (   (da_rf_ra1_r[0] == ar6_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | ar6_rf_wenb1_64_r
                      );

  da0_is_ar7_pair1   = ar7_rf_wenbs
                    & da_rf_renb0_r
                    & (    ar7_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra0_r[`npuarc_RGF_PAIR_RANGE]);

  da1_is_ar7_pair1   = ar7_rf_wenbs
                    & da_rf_renb1_r
                    & (    ar7_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                        == da_rf_ra1_r[`npuarc_RGF_PAIR_RANGE]);

  dp_da_ar7[`npuarc_R0_W1]  = da0_is_ar7_pair1
                    & (   (da_rf_ra0_r[0] == ar7_rf_wa1_r[0])
                        | da_rf_renb0_64_r
                        | ar7_rf_wenb1_64_r
                      );

  dp_da_ar7[`npuarc_R1_W1]  = da1_is_ar7_pair1
                    & (   (da_rf_ra1_r[0] == ar7_rf_wa1_r[0])
                        | da_rf_renb1_64_r
                        | ar7_rf_wenb1_64_r
                      );


  // -------------- next Operand-stage read-pending states -------------------

  sa_read_r0_nxt  =  dp_da_sa[`npuarc_R0_W0] | dp_da_sa[`npuarc_R0_W1]
                  |  dp_da_x1[`npuarc_R0_W0] | dp_da_x1[`npuarc_R0_W1]
                  |  dp_da_x2[`npuarc_R0_W0] | dp_da_x2[`npuarc_R0_W1]
                  |  dp_da_x3[`npuarc_R0_W0] | dp_da_x3[`npuarc_R0_W1]
                  |  dp_da_ca[`npuarc_R0_W0] | dp_da_ca[`npuarc_R0_W1]
                                      | dp_da_ar0[`npuarc_R0_W1]
                                      | dp_da_ar1[`npuarc_R0_W1]
                                      | dp_da_ar2[`npuarc_R0_W1]
                                      | dp_da_ar3[`npuarc_R0_W1]
                                      | dp_da_ar4[`npuarc_R0_W1]
                                      | dp_da_ar5[`npuarc_R0_W1]
                                      | dp_da_ar6[`npuarc_R0_W1]
                                      | dp_da_ar7[`npuarc_R0_W1]
                   ;

  sa_read_r1_nxt  =  dp_da_sa[`npuarc_R1_W0] | dp_da_sa[`npuarc_R1_W1]
                  |  dp_da_x1[`npuarc_R1_W0] | dp_da_x1[`npuarc_R1_W1]
                  |  dp_da_x2[`npuarc_R1_W0] | dp_da_x2[`npuarc_R1_W1]
                  |  dp_da_x3[`npuarc_R1_W0] | dp_da_x3[`npuarc_R1_W1]
                  |  dp_da_ca[`npuarc_R1_W0] | dp_da_ca[`npuarc_R1_W1]
                                      | dp_da_ar0[`npuarc_R1_W1]
                                      | dp_da_ar1[`npuarc_R1_W1]
                                      | dp_da_ar2[`npuarc_R1_W1]
                                      | dp_da_ar3[`npuarc_R1_W1]
                                      | dp_da_ar4[`npuarc_R1_W1]
                                      | dp_da_ar5[`npuarc_R1_W1]
                                      | dp_da_ar6[`npuarc_R1_W1]
                                      | dp_da_ar7[`npuarc_R1_W1]
                  ;

  // -------------- next Exec1-stage read-pending states -------------------

  x1_read_r0_nxt  = sa_adv
                  & (   (fwd_x1_sa0_lo     & (~x1_has_w0))
                      | (fwd_x2_sa0_lo     & (~x2_has_w0))
                      | (fwd_x3_sa0_lo     & (~x3_has_w0))
                      | (fwd_ca0_lo_sa0_lo & (~ca_has_w0))
                      | (fwd_ca1_lo_sa0_lo & (~ca_has_w1))
                      | (fwd_ca0_hi_sa0_lo & (~ca_has_w0))
                      | fd_sa_x1[`npuarc_LR0_HW0]
                      | fd_sa_x2[`npuarc_LR0_HW0]
                      | fd_sa_x3[`npuarc_LR0_HW0]
                      | (fwd_ca1_hi_sa0_lo & (~ca_has_w1))
                      | rd_sa_x1[`npuarc_R0_W1]
                      | rd_sa_x2[`npuarc_R0_W1]
                      | rd_sa_x3[`npuarc_R0_W1]
                      | rd_sa_ar0[`npuarc_R0_W1]
                      | rd_sa_ar1[`npuarc_R0_W1]
                      | rd_sa_ar2[`npuarc_R0_W1]
                      | rd_sa_ar3[`npuarc_R0_W1]
                      | rd_sa_ar4[`npuarc_R0_W1]
                      | rd_sa_ar5[`npuarc_R0_W1]
                      | rd_sa_ar6[`npuarc_R0_W1]
                      | rd_sa_ar7[`npuarc_R0_W1]
                    )
                  | (x1_read_r0_r & x1_retain & (~x1_grab_src0))
                  ;

  x1_read_r1_nxt  = sa_pass
                  & (   (fwd_x1_sa1_lo     & (~x1_has_w0))
                      | (fwd_x2_sa1_lo     & (~x2_has_w0))
                      | (fwd_x3_sa1_lo     & (~x3_has_w0))
                      | (fwd_ca0_lo_sa1_lo & (~ca_has_w0))
                      | (fwd_ca1_lo_sa1_lo & (~ca_has_w1))
                      | (fwd_ca0_hi_sa1_lo & (~ca_has_w0))
                      | fd_sa_x1[`npuarc_LR1_HW0]
                      | fd_sa_x2[`npuarc_LR1_HW0]
                      | fd_sa_x3[`npuarc_LR1_HW0]
                      | (fwd_ca1_hi_sa1_lo & (~ca_has_w1))
                      | rd_sa_x1[`npuarc_R1_W1]
                      | rd_sa_x2[`npuarc_R1_W1]
                      | rd_sa_x3[`npuarc_R1_W1]
                      | rd_sa_ar0[`npuarc_R1_W1]
                      | rd_sa_ar1[`npuarc_R1_W1]
                      | rd_sa_ar2[`npuarc_R1_W1]
                      | rd_sa_ar3[`npuarc_R1_W1]
                      | rd_sa_ar4[`npuarc_R1_W1]
                      | rd_sa_ar5[`npuarc_R1_W1]
                      | rd_sa_ar6[`npuarc_R1_W1]
                      | rd_sa_ar7[`npuarc_R1_W1]
                    )
                  | (x1_read_r1_r & x1_retain & (~x1_grab_src1))
                  ;

  x1_read_r2_nxt  = sa_adv
                  & (   rd_sa_x1[`npuarc_R0_W1]
                      | rd_sa_x2[`npuarc_R0_W1]
                      | rd_sa_x3[`npuarc_R0_W1]
                      | rd_sa_ar0[`npuarc_R0_W1]
                      | rd_sa_ar1[`npuarc_R0_W1]
                      | rd_sa_ar2[`npuarc_R0_W1]
                      | rd_sa_ar3[`npuarc_R0_W1]
                      | rd_sa_ar4[`npuarc_R0_W1]
                      | rd_sa_ar5[`npuarc_R0_W1]
                      | rd_sa_ar6[`npuarc_R0_W1]
                      | rd_sa_ar7[`npuarc_R0_W1]
                      | fd_sa_x1[`npuarc_HR0_LW0]
                      | fd_sa_x2[`npuarc_HR0_LW0]
                      | fd_sa_x3[`npuarc_HR0_LW0]
                      | fd_sa_ca[`npuarc_HR0_LW0]
                      | fd_sa_ca[`npuarc_HR0_LW1]
                      | fd_sa_ca[`npuarc_HR0_HW0]
                      | fd_sa_x1[`npuarc_HR0_HW0]
                      | fd_sa_x2[`npuarc_HR0_HW0]
                      | fd_sa_x3[`npuarc_HR0_HW0]
                      | fd_sa_ca[`npuarc_HR0_HW1]
                    )
                  | (x1_read_r2_r & x1_retain & (~x1_grab_src2))
                  ;

  x1_read_r3_nxt  = sa_adv
                  & (   fd_sa_x1[`npuarc_HR1_LW0]
                      | fd_sa_x2[`npuarc_HR1_LW0]
                      | fd_sa_x3[`npuarc_HR1_LW0]
                      | fd_sa_ca[`npuarc_HR1_LW0]
                      | fd_sa_ca[`npuarc_HR1_LW1]
                      | fd_sa_ca[`npuarc_HR1_HW0]
                      | fd_sa_x1[`npuarc_HR1_HW0]
                      | fd_sa_x2[`npuarc_HR1_HW0]
                      | fd_sa_x3[`npuarc_HR1_HW0]
                      | fd_sa_ca[`npuarc_HR1_HW1]
                      | rd_sa_x1[`npuarc_R1_W1]
                      | rd_sa_x2[`npuarc_R1_W1]
                      | rd_sa_x3[`npuarc_R1_W1]
                      | rd_sa_ar0[`npuarc_R1_W1]
                      | rd_sa_ar1[`npuarc_R1_W1]
                      | rd_sa_ar2[`npuarc_R1_W1]
                      | rd_sa_ar3[`npuarc_R1_W1]
                      | rd_sa_ar4[`npuarc_R1_W1]
                      | rd_sa_ar5[`npuarc_R1_W1]
                      | rd_sa_ar6[`npuarc_R1_W1]
                      | rd_sa_ar7[`npuarc_R1_W1]
                    )
                  | (x1_read_r3_r & x1_retain & (~x1_grab_src3))
                  ;

  // ----------------- next X2-stage read-pending states -------------------
  //
  // The next X2 read flags will be set for the current X1 instruction,
  // when it moves to X2, if there was a read flag set at the X1 stage
  // and there is no activated forwarding path for each operand.
  //
  // If the X1 instruction is computed in the current cycle, then the read
  // flag is never set when the instruction enters X2. This is indicated by
  // x2_done_nxt == 1 or x1_slow_op_r == 1. Note, `slow' 2-cycle operations
  // always begin execution in X1 and complete in X2. Therefore, they cannot
  // possibly have read flags set in X2.
  //
  // When functional units are configured that begin executing at X2, such
  // as the multiplier or the FPU, then values can be forwarded from port
  // 0 at X2, X3, CA and WA, and from port 1 at CA and WA. Any forwarding
  // value at WA is always available for use at X1.
  //
  x2_read_r0_nxt  = x1_pass
                  & x1_read_r0_r
                  & (~(  fd_x1_wa[`npuarc_LR0_LW0]
                      | fd_x1_wa[`npuarc_LR0_LW1]
                      | fd_x1_wa[`npuarc_LR0_HW0]
                      | fd_x1_wa[`npuarc_LR0_HW1]
                      | (fd_x1_ca[`npuarc_LR0_HW1] & ca_has_w1)
                      | (fd_x1_x2[`npuarc_LR0_LW0] & x2_has_w0)
                      | (fd_x1_x3[`npuarc_LR0_LW0] & x3_has_w0)
                      | (fd_x1_ca[`npuarc_LR0_LW0] & ca_has_w0)
                      | (fd_x1_ca[`npuarc_LR0_LW1] & ca_has_w1)
                      | (fd_x1_ca[`npuarc_LR0_HW0] & ca_has_w0)
                     )
                    )
                  ;

/*
  x2_read_r0h_nxt = x1_pass
                  & x1_read_r2_r
                  & (~(  fd_x1_wa[`npuarc_HR0_LW0]
                      | fd_x1_wa[`npuarc_HR0_LW1]
                      | fd_x1_wa[`npuarc_HR0_HW0]
                      | fd_x1_wa[`npuarc_HR0_HW1]
                      | (fd_x1_ca[`npuarc_HR0_HW1] & ca_has_w1)
                      | (fd_x1_x2[`npuarc_HR0_LW0] & x2_has_w0)
                      | (fd_x1_x3[`npuarc_HR0_LW0] & x3_has_w0)
                      | (fd_x1_ca[`npuarc_HR0_LW0] & ca_has_w0)
                      | (fd_x1_ca[`npuarc_HR0_LW1] & ca_has_w1)
                      | (fd_x1_ca[`npuarc_HR0_HW0] & ca_has_w0)
                    )
                   )
                  ;
*/
  x2_read_r1_nxt  = x1_pass
                  & x1_read_r1_r
                  & (~(  fd_x1_wa[`npuarc_LR1_LW0]
                      | fd_x1_wa[`npuarc_LR1_LW1]
                      | fd_x1_wa[`npuarc_LR1_HW0]
                      | fd_x1_wa[`npuarc_LR1_HW1]
                      | (fd_x1_ca[`npuarc_LR1_HW1] & ca_has_w1)
                      | (fd_x1_x2[`npuarc_LR1_LW0] & x2_has_w0)
                      | (fd_x1_x3[`npuarc_LR1_LW0] & x3_has_w0)
                      | (fd_x1_ca[`npuarc_LR1_LW0] & ca_has_w0)
                      | (fd_x1_ca[`npuarc_LR1_LW1] & ca_has_w1)
                      | (fd_x1_ca[`npuarc_LR1_HW0] & ca_has_w0)
                     )
                    )
                  ;

/*  x2_read_r1h_nxt = x1_pass
                  & x1_read_r3_r
                  & (~(  fd_x1_wa[`npuarc_HR1_LW0]
                      | fd_x1_wa[`npuarc_HR1_LW1]
                      | fd_x1_wa[`npuarc_HR1_HW0]
                      | fd_x1_wa[`npuarc_HR1_HW1]
                      | (fd_x1_ca[`npuarc_HR1_HW1] & ca_has_w1)
                      | (fd_x1_x2[`npuarc_HR1_LW0] & x2_has_w0)
                      | (fd_x1_x3[`npuarc_HR1_LW0] & x3_has_w0)
                      | (fd_x1_ca[`npuarc_HR1_LW0] & ca_has_w0)
                      | (fd_x1_ca[`npuarc_HR1_LW1] & ca_has_w1)
                      | (fd_x1_ca[`npuarc_HR1_HW0] & ca_has_w0)
                     )
                    )
                  ;
*/
  // ----------------- next X3-stage read-pending states -------------------
  //
  // The next X3 read flags will be set for the current X2 instruction,
  // when it moves to X3, if if there was a read flag set at the X2 stage
  // and there is no activated forwarding path for each operand.
  //
  x3_read_r0_nxt  = x2_pass
                  & x2_read_r0_r
                  & (~(  fd_x2_wa[`npuarc_LR0_LW0]
                      | fd_x2_wa[`npuarc_LR0_LW1]
                      | fd_x2_wa[`npuarc_LR0_HW0]
                      | fd_x2_wa[`npuarc_LR0_HW1]
                    ))
                  ;

/*  x3_read_r0h_nxt = x2_pass
                  & x2_read_r0h_r
                  & (~(  fd_x2_wa[`npuarc_HR0_LW0]
                      | fd_x2_wa[`npuarc_HR0_LW1]
                      | fd_x2_wa[`npuarc_HR0_HW0]
                      | fd_x2_wa[`npuarc_HR0_HW1]
                    ))
                  ;
*/
  x3_read_r1_nxt  = x2_pass
                  & x2_read_r1_r
                  & (~(  fd_x2_wa[`npuarc_LR1_LW0]
                      | fd_x2_wa[`npuarc_LR1_LW1]
                      | fd_x2_wa[`npuarc_LR1_HW0]
                      | fd_x2_wa[`npuarc_LR1_HW1]
                     ))
                  ;

/*  x3_read_r1h_nxt = x2_pass
                  & x2_read_r1h_r
                  & (~(  fd_x2_wa[`npuarc_HR1_LW0]
                      | fd_x2_wa[`npuarc_HR1_LW1]
                      | fd_x2_wa[`npuarc_HR1_HW0]
                      | fd_x2_wa[`npuarc_HR1_HW1]
                     ))
                  ;
*/
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Write-after-write dependency detection logic - at the Operand stage      //
//                                                                          //
// Signal xx_kl_yy indicates that a write-after-write dependency exists     //
// between a destination of the instruction at xx and a destination of the  //
// instruction at stage yy. This redefinition of a register result has two  //
// important consequences. Firstly, it may become a write-after-write (WAW) //
// hazard if the instruction at xx ever tries to retire a result before the //
// instruction at yy has done so. Secondly, any read of the register that   //
// is defined by both xx and yy, issued after xx, need only consider the    //
// dependency with xx.                                                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : sa_waw_deps_PROC


  // -------------- compute kill set for x1 from sa instruction --------------

  sa_kl_x1[`npuarc_K_W0_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == x1_rf_wa0_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & x1_rf_wenb0_r
                         & (   (sa_rf_wa0_r[0] == x1_rf_wa0_r[0])
                             | sa_rf_wenb0_64_r
                             | x1_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == x1_rf_wa0_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & x1_rf_wenb0_r
                         & (   (sa_rf_wa1_r[0] == x1_rf_wa0_r[0])
                             | sa_rf_wenb1_64_r
                             | x1_rf_wenb0_64_r
                           )
                        )
                      ;

  sa_kl_x1[`npuarc_K_W0_HI]  = (x1_rf_wenb0_64_r
                          & (  ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                   == x1_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                 )
                                 & sa_rf_wenb0_r & (~sa_rf_wenb0_64_r)
                               )
                             | ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                                   == x1_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                 )
                                 & sa_rf_wenb1_r
                                 & (~sa_rf_wenb1_64_r)
                               )
                            )
                               )
                      | (   sa_rf_wenb0_64_r
                          & (|sa_q_field_r)
                          & (   ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                    == x1_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                  )
                                  & x1_rf_wenb0_r
                                )
                              | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                    == x1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                                  )
                                  & x1_rf_wenb1_r
                                )
                            )
                                )
                      ;

  sa_kl_x1[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == x1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & x1_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == x1_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                             | x1_rf_wenb1_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == x1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & x1_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == x1_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | x1_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_x1[`npuarc_K_W1_HI]  = x1_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == x1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == x1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for x2 from sa instruction --------------

  sa_kl_x2[`npuarc_K_W0_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == x2_rf_wa0_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & x2_rf_wenb0_r
                         & (   (sa_rf_wa0_r[0] == x2_rf_wa0_r[0])
                             | sa_rf_wenb0_64_r
                             | x2_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == x2_rf_wa0_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & x2_rf_wenb0_r
                         & (   (sa_rf_wa1_r[0] == x2_rf_wa0_r[0])
                             | sa_rf_wenb1_64_r
                             | x2_rf_wenb0_64_r
                           )
                        )
                      ;

  sa_kl_x2[`npuarc_K_W0_HI]  = (x2_rf_wenb0_64_r
                          & (  ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                   == x2_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                 )
                                 & sa_rf_wenb0_r & (~sa_rf_wenb0_64_r)
                               )
                             | ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                                   == x2_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                 )
                                 & sa_rf_wenb1_r
                                 & (~sa_rf_wenb1_64_r)
                               )
                            )
                               )
                      | (   sa_rf_wenb0_64_r
                          & (|sa_q_field_r)
                          & (   ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                    == x2_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                  )
                                  & x2_rf_wenb0_r
                                )
                              | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                    == x2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                                  )
                                  & x2_rf_wenb1_r
                                )
                            )
                                )
                      ;

  sa_kl_x2[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == x2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & x2_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == x2_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                             | x2_rf_wenb1_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == x2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & x2_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == x2_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | x2_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_x2[`npuarc_K_W1_HI]  = x2_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == x2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == x2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for x3 from sa instruction --------------

  sa_kl_x3[`npuarc_K_W0_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == x3_rf_wa0_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & x3_rf_wenb0_r
                         & (   (sa_rf_wa0_r[0] == x3_rf_wa0_r[0])
                             | sa_rf_wenb0_64_r
                             | x3_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == x3_rf_wa0_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & x3_rf_wenb0_r
                         & (   (sa_rf_wa1_r[0] == x3_rf_wa0_r[0])
                             | sa_rf_wenb1_64_r
                             | x3_rf_wenb0_64_r
                           )
                        )
                      ;

  sa_kl_x3[`npuarc_K_W0_HI]  = (x3_rf_wenb0_64_r
                          & (  ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                   == x3_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                 )
                                 & sa_rf_wenb0_r & (~sa_rf_wenb0_64_r)
                               )
                             | ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                                   == x3_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                 )
                                 & sa_rf_wenb1_r
                                 & (~sa_rf_wenb1_64_r)
                               )
                            )
                               )
                      | (   sa_rf_wenb0_64_r
                          & (|sa_q_field_r)
                          & (   ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                    == x3_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                  )
                                  & x3_rf_wenb0_r
                                )
                              | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                    == x3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                                  )
                                  & x3_rf_wenb1_r
                                )
                            )
                                )
                      ;

  sa_kl_x3[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == x3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & x3_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == x3_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                             | x3_rf_wenb1_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == x3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & x3_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == x3_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | x3_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_x3[`npuarc_K_W1_HI]  = x3_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == x3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == x3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for ca from sa instruction --------------

  sa_kl_ca[`npuarc_K_W0_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == ca_rf_wa0_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & ca_rf_wenb0_r
                         & (   (sa_rf_wa0_r[0] == ca_rf_wa0_r[0])
                             | sa_rf_wenb0_64_r
                             | ca_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == ca_rf_wa0_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & ca_rf_wenb0_r
                         & (   (sa_rf_wa1_r[0] == ca_rf_wa0_r[0])
                             | sa_rf_wenb1_64_r
                             | ca_rf_wenb0_64_r
                           )
                        )
                      ;

  sa_kl_ca[`npuarc_K_W0_HI]  = (ca_rf_wenb0_64_r
                          & (  ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                   == ca_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                 )
                                 & sa_rf_wenb0_r & (~sa_rf_wenb0_64_r)
                               )
                             | ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                                   == ca_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                 )
                                 & sa_rf_wenb1_r
                                 & (~sa_rf_wenb1_64_r)
                               )
                            )
                               )
                      | (   sa_rf_wenb0_64_r
                          & (|sa_q_field_r)
                          & (   ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                    == ca_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                  )
                                  & ca_rf_wenb0_r
                                )
                              | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                    == ca_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                                  )
                                  & ca_rf_wenb1_r
                                )
                            )
                                )
                      ;

  sa_kl_ca[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == ca_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & ca_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == ca_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                             | ca_rf_wenb1_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == ca_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & ca_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == ca_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | ca_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_ca[`npuarc_K_W1_HI]  = ca_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == ca_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == ca_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for wa from sa instruction --------------

  sa_kl_wa[`npuarc_K_W0_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == wa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & wa_rf_wenb0_r
                         & (   (sa_rf_wa0_r[0] == wa_rf_wa0_r[0])
                             | sa_rf_wenb0_64_r
                             | wa_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == wa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & wa_rf_wenb0_r
                         & (   (sa_rf_wa1_r[0] == wa_rf_wa0_r[0])
                             | sa_rf_wenb1_64_r
                             | wa_rf_wenb0_64_r
                           )
                        )
                      ;

  sa_kl_wa[`npuarc_K_W0_HI]  = (wa_rf_wenb0_64_r
                          & (  ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                   == wa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                 )
                                 & sa_rf_wenb0_r & (~sa_rf_wenb0_64_r)
                               )
                             | ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                                   == wa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                 )
                                 & sa_rf_wenb1_r
                                 & (~sa_rf_wenb1_64_r)
                               )
                            )
                               )
                      | (   sa_rf_wenb0_64_r
                          & (|sa_q_field_r)
                          & (   ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                    == wa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                  )
                                  & wa_rf_wenb0_r
                                )
                              | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                                    == wa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                                  )
                                  & wa_rf_wenb1_r
                                )
                            )
                                )
                      ;

  sa_kl_wa[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == wa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & wa_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == wa_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                             | wa_rf_wenb1_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == wa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & wa_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == wa_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | wa_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_wa[`npuarc_K_W1_HI]  = wa_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == wa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == wa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for ar0 from sa instruction --------------

  sa_kl_ar0[`npuarc_K_W0_LO]  = 1'b0;
  sa_kl_ar0[`npuarc_K_W0_HI]  = 1'b0;

  sa_kl_ar0[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == ar0_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & ar0_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == ar0_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == ar0_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & ar0_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == ar0_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | ar0_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_ar0[`npuarc_K_W1_HI]  = ar0_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == ar0_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == ar0_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for ar1 from sa instruction --------------

  sa_kl_ar1[`npuarc_K_W0_LO]  = 1'b0;
  sa_kl_ar1[`npuarc_K_W0_HI]  = 1'b0;

  sa_kl_ar1[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == ar1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & ar1_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == ar1_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == ar1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & ar1_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == ar1_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | ar1_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_ar1[`npuarc_K_W1_HI]  = ar1_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == ar1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == ar1_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for ar2 from sa instruction --------------

  sa_kl_ar2[`npuarc_K_W0_LO]  = 1'b0;
  sa_kl_ar2[`npuarc_K_W0_HI]  = 1'b0;

  sa_kl_ar2[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == ar2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & ar2_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == ar2_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == ar2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & ar2_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == ar2_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | ar2_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_ar2[`npuarc_K_W1_HI]  = ar2_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == ar2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == ar2_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for ar3 from sa instruction --------------

  sa_kl_ar3[`npuarc_K_W0_LO]  = 1'b0;
  sa_kl_ar3[`npuarc_K_W0_HI]  = 1'b0;

  sa_kl_ar3[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == ar3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & ar3_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == ar3_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == ar3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & ar3_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == ar3_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | ar3_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_ar3[`npuarc_K_W1_HI]  = ar3_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == ar3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == ar3_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for ar4 from sa instruction --------------

  sa_kl_ar4[`npuarc_K_W0_LO]  = 1'b0;
  sa_kl_ar4[`npuarc_K_W0_HI]  = 1'b0;

  sa_kl_ar4[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == ar4_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & ar4_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == ar4_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == ar4_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & ar4_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == ar4_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | ar4_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_ar4[`npuarc_K_W1_HI]  = ar4_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == ar4_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == ar4_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for ar5 from sa instruction --------------

  sa_kl_ar5[`npuarc_K_W0_LO]  = 1'b0;
  sa_kl_ar5[`npuarc_K_W0_HI]  = 1'b0;

  sa_kl_ar5[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == ar5_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & ar5_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == ar5_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == ar5_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & ar5_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == ar5_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | ar5_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_ar5[`npuarc_K_W1_HI]  = ar5_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == ar5_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == ar5_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for ar6 from sa instruction --------------

  sa_kl_ar6[`npuarc_K_W0_LO]  = 1'b0;
  sa_kl_ar6[`npuarc_K_W0_HI]  = 1'b0;

  sa_kl_ar6[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == ar6_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & ar6_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == ar6_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == ar6_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & ar6_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == ar6_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | ar6_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_ar6[`npuarc_K_W1_HI]  = ar6_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == ar6_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == ar6_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

  // -------------- compute kill set for ar7 from sa instruction --------------

  sa_kl_ar7[`npuarc_K_W0_LO]  = 1'b0;
  sa_kl_ar7[`npuarc_K_W0_HI]  = 1'b0;

  sa_kl_ar7[`npuarc_K_W1_LO]  = (  (   sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                            == ar7_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb0_r
                         & ar7_rf_wenb1_r
                         & (   (sa_rf_wa0_r[0] == ar7_rf_wa1_r[0])
                             | sa_rf_wenb0_64_r
                           )
                        )
                      | (  (   sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                            == ar7_rf_wa1_r[`npuarc_RGF_PAIR_RANGE])
                         & sa_rf_wenb1_r
                         & ar7_rf_wenb1_r
                         & (   (sa_rf_wa1_r[0] == ar7_rf_wa1_r[0])
                             | sa_rf_wenb1_64_r
                             | ar7_rf_wenb1_64_r
                           )
                        )
                      ;

  sa_kl_ar7[`npuarc_K_W1_HI]  = ar7_rf_wenb1_64_r
                      & (  ( (    sa_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                               == ar7_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb1_r
                             & (~sa_rf_wenb1_64_r)
                           )
                         | ( (    sa_rf_wa0_r[`npuarc_RGF_PAIR_RANGE]
                               == ar7_rf_wa1_r[`npuarc_RGF_PAIR_RANGE]
                             )
                             & sa_rf_wenb0_r
                             & (~sa_rf_wenb0_64_r)
                           )
                             )
                      ;

end




//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Graduation tag management logic                                          //
//                                                                          //
// Each graduation tag has a valid bit. If the valid bit is 0, then the tag //
// can be selected for allocation when the next graduation request arrives. //
// If the valid bit is 1, then the tag is in-use and cannot be reallocated. //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : ar_mgmt_PROC


  //==========================================================================
  // Collate graduation requests from all possible sources
  //
  ca_grad_req   = dc4_grad_req
                | div_grad_req
                | eia_grad_req
                ;

  //==========================================================================
  // Group the valid bits from all tag contexts in a single vector, indexed
  // by tag ID.
  //
  ar_tags_valid = {
                    ar7_rf_valid_r,
                    ar6_rf_valid_r,
                    ar5_rf_valid_r,
                    ar4_rf_valid_r,
                    ar3_rf_valid_r,
                    ar2_rf_valid_r,
                    ar1_rf_valid_r,
                    ar0_rf_valid_r
                  };

  //==========================================================================
  // Determine whether a graduation request will be honored. A graduation
  // request from a DIV,REM operation with a div-by-zero status will not
  // be honored, nor will an instruction with a false predicate.
  //
  ca_grad_allowed   = ((1'b0
                    | (ca_div_op_r == 1'b1)
                    | (ca_eia_op_r == 1'b1)
                    )
                    ? (ca_predicate_r & ca_q_cond)
                    : ca_predicate_r
                    )
                    ;


  //==========================================================================
  // Determine the next graduation tag to be allocated, based on current
  // registered status.
  //
  ar_alloc_hot      = 8'd0;
  grad_tag          = 3'd0;

  casez (ar_tags_valid)
  8'b???????0:
    begin
    ar_alloc_hot[0] = ca_grad_req & ca_grad_allowed;
    grad_tag        = 3'd0;
    end
  8'b??????01:
    begin
    ar_alloc_hot[1] = ca_grad_req & ca_grad_allowed;
    grad_tag        = 3'd1;
    end
  8'b?????011:
    begin
    ar_alloc_hot[2] = ca_grad_req & ca_grad_allowed;
    grad_tag        = 3'd2;
    end
  8'b????0111:
    begin
    ar_alloc_hot[3] = ca_grad_req & ca_grad_allowed;
    grad_tag        = 3'd3;
    end
  8'b???01111:
    begin
    ar_alloc_hot[4] = ca_grad_req & ca_grad_allowed;
    grad_tag        = 3'd4;
    end
  8'b??011111:
    begin
    ar_alloc_hot[5] = ca_grad_req & ca_grad_allowed;
    grad_tag        = 3'd5;
    end
  8'b?0111111:
    begin
    ar_alloc_hot[6] = ca_grad_req & ca_grad_allowed;
    grad_tag        = 3'd6;
    end
  8'b01111111:
    begin
    ar_alloc_hot[7] = ca_grad_req & ca_grad_allowed;
    grad_tag        = 3'd7;
    end
  default:
    begin
    ar_alloc_hot    = 8'd0;
    grad_tag        = 3'd0;
    end
  endcase

  //==========================================================================
  // Perform binary to one-hot decoding of the retirement tag, and
  // select the chosen tag to return from this module back to
  // the commit stage. The retirement tag is also used to select
  // one row of the post-commit dependency matrix for re-assignment
  // back to the dep_xx_wa_r row of the pre-commit dependency
  // matrix when a retirement occurs.
  //
  ar_dealloc_hot  = 8'd0;
  retire_rf_64    = 1'b0;
  retire_rf_wenb  = 1'b0;
  retire_flag_wen = 1'b0;
  retire_rf_wa    = `npuarc_GRAD_ADDR_BITS'd0;
  retire_writes_acc = 1'b0;
  retire_ld_addr    = {`npuarc_ADDR_SIZE{1'b0}};
  retire_is_load    = {1{1'b0}};
  retire_exclusive = 1'b0;
  dp_da_ar        = `npuarc_DP_POST_BITS'd0;
  dp_sa1_ar       = `npuarc_POST_RAW_BITS'd0;
  dp_sa2_ar       = `npuarc_DP_POST_BITS'd0;
  dp_x1_ar        = `npuarc_DP_POST_BITS'd0;
  dp_x2_ar        = `npuarc_DP_POST_BITS'd0;
  dp_x3_ar        = `npuarc_DP_POST_BITS'd0;
  dp_ca_ar        = `npuarc_DP_POST_BITS'd0;

  case (ca_retire_tag)
  3'd0:
    begin
    ar_dealloc_hot[0] = ca_retire_ack;
    retire_rf_64      = ar0_rf_wenb1_64_r;
    retire_rf_wenb    = ar0_rf_wenb1_r;
    retire_rf_wa      = ar0_rf_wa1_r;
    retire_flag_wen   = ar0_flag_wen_r;
    retire_writes_acc = ar0_writes_acc_r;
    retire_ld_addr    = ar0_ld_addr_r;
    retire_is_load    = ar0_is_load_r;
    retire_exclusive  = ar0_exclusive_r;
    dp_da_ar          = {2'd0, dp_da_ar0};
    dp_sa1_ar         = qd_sa_ar0;
    dp_sa2_ar         = cn_sa_ar0;
    dp_x1_ar          = dp_x1_ar0_r;
    dp_x2_ar          = dp_x2_ar0_r;
    dp_x3_ar          = dp_x3_ar0_r;
    dp_ca_ar          = dp_ca_ar0_r;
    end
  3'd1:
    begin
    ar_dealloc_hot[1] = ca_retire_ack;
    retire_rf_64      = ar1_rf_wenb1_64_r;
    retire_rf_wenb    = ar1_rf_wenb1_r;
    retire_rf_wa      = ar1_rf_wa1_r;
    retire_flag_wen   = ar1_flag_wen_r;
    retire_writes_acc = ar1_writes_acc_r;
    retire_ld_addr    = ar1_ld_addr_r;
    retire_is_load    = ar1_is_load_r;
    retire_exclusive  = ar1_exclusive_r;
    dp_da_ar          = {2'd0, dp_da_ar1};
    dp_sa1_ar         = qd_sa_ar1;
    dp_sa2_ar         = cn_sa_ar1;
    dp_x1_ar          = dp_x1_ar1_r;
    dp_x2_ar          = dp_x2_ar1_r;
    dp_x3_ar          = dp_x3_ar1_r;
    dp_ca_ar          = dp_ca_ar1_r;
    end
  3'd2:
    begin
    ar_dealloc_hot[2] = ca_retire_ack;
    retire_rf_64      = ar2_rf_wenb1_64_r;
    retire_rf_wenb    = ar2_rf_wenb1_r;
    retire_rf_wa      = ar2_rf_wa1_r;
    retire_flag_wen   = ar2_flag_wen_r;
    retire_writes_acc = ar2_writes_acc_r;
    retire_ld_addr    = ar2_ld_addr_r;
    retire_is_load    = ar2_is_load_r;
    retire_exclusive  = ar2_exclusive_r;
    dp_da_ar          = {2'd0, dp_da_ar2};
    dp_sa1_ar         = qd_sa_ar2;
    dp_sa2_ar         = cn_sa_ar2;
    dp_x1_ar          = dp_x1_ar2_r;
    dp_x2_ar          = dp_x2_ar2_r;
    dp_x3_ar          = dp_x3_ar2_r;
    dp_ca_ar          = dp_ca_ar2_r;
    end
  3'd3:
    begin
    ar_dealloc_hot[3] = ca_retire_ack;
    retire_rf_64      = ar3_rf_wenb1_64_r;
    retire_rf_wenb    = ar3_rf_wenb1_r;
    retire_rf_wa      = ar3_rf_wa1_r;
    retire_flag_wen   = ar3_flag_wen_r;
    retire_writes_acc = ar3_writes_acc_r;
    retire_ld_addr    = ar3_ld_addr_r;
    retire_is_load    = ar3_is_load_r;
    retire_exclusive  = ar3_exclusive_r;
    dp_da_ar          = {2'd0, dp_da_ar3};
    dp_sa1_ar         = qd_sa_ar3;
    dp_sa2_ar         = cn_sa_ar3;
    dp_x1_ar          = dp_x1_ar3_r;
    dp_x2_ar          = dp_x2_ar3_r;
    dp_x3_ar          = dp_x3_ar3_r;
    dp_ca_ar          = dp_ca_ar3_r;
    end
  3'd4:
    begin
    ar_dealloc_hot[4] = ca_retire_ack;
    retire_rf_64      = ar4_rf_wenb1_64_r;
    retire_rf_wenb    = ar4_rf_wenb1_r;
    retire_rf_wa      = ar4_rf_wa1_r;
    retire_flag_wen   = ar4_flag_wen_r;
    retire_writes_acc = ar4_writes_acc_r;
    retire_ld_addr    = ar4_ld_addr_r;
    retire_is_load    = ar4_is_load_r;
    retire_exclusive  = ar4_exclusive_r;
    dp_da_ar          = {2'd0, dp_da_ar4};
    dp_sa1_ar         = qd_sa_ar4;
    dp_sa2_ar         = cn_sa_ar4;
    dp_x1_ar          = dp_x1_ar4_r;
    dp_x2_ar          = dp_x2_ar4_r;
    dp_x3_ar          = dp_x3_ar4_r;
    dp_ca_ar          = dp_ca_ar4_r;
    end
  3'd5:
    begin
    ar_dealloc_hot[5] = ca_retire_ack;
    retire_rf_64      = ar5_rf_wenb1_64_r;
    retire_rf_wenb    = ar5_rf_wenb1_r;
    retire_rf_wa      = ar5_rf_wa1_r;
    retire_flag_wen   = ar5_flag_wen_r;
    retire_writes_acc = ar5_writes_acc_r;
    retire_ld_addr    = ar5_ld_addr_r;
    retire_is_load    = ar5_is_load_r;
    retire_exclusive  = ar5_exclusive_r;
    dp_da_ar          = {2'd0, dp_da_ar5};
    dp_sa1_ar         = qd_sa_ar5;
    dp_sa2_ar         = cn_sa_ar5;
    dp_x1_ar          = dp_x1_ar5_r;
    dp_x2_ar          = dp_x2_ar5_r;
    dp_x3_ar          = dp_x3_ar5_r;
    dp_ca_ar          = dp_ca_ar5_r;
    end
  3'd6:
    begin
    ar_dealloc_hot[6] = ca_retire_ack;
    retire_rf_64      = ar6_rf_wenb1_64_r;
    retire_rf_wenb    = ar6_rf_wenb1_r;
    retire_rf_wa      = ar6_rf_wa1_r;
    retire_flag_wen   = ar6_flag_wen_r;
    retire_writes_acc = ar6_writes_acc_r;
    retire_ld_addr    = ar6_ld_addr_r;
    retire_is_load    = ar6_is_load_r;
    retire_exclusive  = ar6_exclusive_r;
    dp_da_ar          = {2'd0, dp_da_ar6};
    dp_sa1_ar         = qd_sa_ar6;
    dp_sa2_ar         = cn_sa_ar6;
    dp_x1_ar          = dp_x1_ar6_r;
    dp_x2_ar          = dp_x2_ar6_r;
    dp_x3_ar          = dp_x3_ar6_r;
    dp_ca_ar          = dp_ca_ar6_r;
    end
  3'd7:
    begin
    ar_dealloc_hot[7] = ca_retire_ack;
    retire_rf_64      = ar7_rf_wenb1_64_r;
    retire_rf_wenb    = ar7_rf_wenb1_r;
    retire_rf_wa      = ar7_rf_wa1_r;
    retire_flag_wen   = ar7_flag_wen_r;
    retire_writes_acc = ar7_writes_acc_r;
    retire_ld_addr    = ar7_ld_addr_r;
    retire_is_load    = ar7_is_load_r;
    retire_exclusive  = ar7_exclusive_r;
    dp_da_ar          = {2'd0, dp_da_ar7};
    dp_sa1_ar         = qd_sa_ar7;
    dp_sa2_ar         = cn_sa_ar7;
    dp_x1_ar          = dp_x1_ar7_r;
    dp_x2_ar          = dp_x2_ar7_r;
    dp_x3_ar          = dp_x3_ar7_r;
    dp_ca_ar          = dp_ca_ar7_r;
    end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept
  default: ;
// spyglass enable_block W193
  endcase

  //==========================================================================
  // Respond to graduation requests with a positive graduation acknowledgement
  // if at least one buffer location is free, otherwise withhold the ack.
  // This signal does not mean that a graduation will necessarily happen
  // in the current cycle, as that depends on ca_adv. This signal tells the
  // commit stage that a graduation request is not prevented by a full buffer.
  //
  grad_ack      = (~ar_tags_full_r) & ca_grad_allowed;

  //==========================================================================
  // Stall at CA if a graduation is requested but the graduation buffer is full.
  // (when CA is stalled, retirements are still enabled).
  //
  ca_tag_stall  = ca_grad_req & ca_grad_allowed & ar_tags_full_r;

  //==========================================================================
  // Select a graduation requests from one of the possible sources, which may
  // include: (1) DMP, (2) Vector Unit (3) DIV, (4) FPU, (5) EIA
  //
  if (dc4_grad_req)
    begin
    ca_grad_rf_wa   = dc4_grad_rf_wa;
    ca_grad_rf_64   = dc4_grad_rf_64;
    end
  else if (div_grad_req)
    begin
    ca_grad_rf_wa   = {1'b0, div_grad_rf_wa};
    ca_grad_rf_64   = 1'b0;
    end
  else if (eia_grad_req)
    begin
    ca_grad_rf_wa   = {1'b0, eia_grad_rf_wa};
    ca_grad_rf_64   = eia_grad_rf_64;
    end
  else
    begin
    ca_grad_rf_wa   = `npuarc_GRAD_ADDR_BITS'd0;
    ca_grad_rf_64   = 1'b0;
    end

  //==========================================================================
  // Commit-stage ca_retire_ack signal provides the retirement acknowledge
  // that drives the dependency and graduation buffer updates during
  // retirement.
  //
  retire_ack    = ca_retire_ack;

  //==========================================================================
  // ca_adv_w0 is asserted whenever a Commit-stage instruction advances
  // and transfers its W0 result (if any) to the Writeback stage without
  // graduating it into a post-commit retirement buffer. This will always
  // be the case if ca_grad_req is not asserted, or if the Commit-stage
  // instruction is a Load. Hence, any graduation request for a non-Load
  // instruction is assumed to graduate the W0 channel. This is also true
  // if an instruction makes a graduation request but its predicate is false.
  // In this case, the previous value of its destination register is
  // available from the Writeback stage in the next cycle.
  //
  ca_adv_w0   = ca_adv & ((~ca_grad_req) | (~ca_predicate_r) | ca_load_r);

  //==========================================================================
  // ca_adv_w1 is asserted whenever a Commit-stage instruction advances
  // and transfers its W1 result (if any) to the Writeback stage without
  // graduating it into a post-commit retirement buffer. This will be the
  // case only if the instruction is a Load and there is no graduation
  // request.
  //
  ca_adv_w1   = ca_adv & ((~ca_grad_req) & ca_load_r);

  //==========================================================================
  // ca_grad_w0 is asserted whenever a Commit-stage instruction advances
  // while making a graduation request for write channel W0. This is indicated
  // by the Commit-stage instruction not being a Load instruction, as all
  // non-Load instructions that retire an out-of-order result will do so
  // via W0. This signal is not asserted if the CA-stage predicate is false,
  // as no graduation will occur in this case.
  //

  //==========================================================================
  // ca_grad_w1 is asserted whenever a Commit-stage instruction advances
  // while making a graduation request for write channel W1. This is indicated
  // by the Commit-stage instruction being a Load, as all Load instructions
  // that retire an out-of-order result will do so only via W1. If present,
  // a valid W0 result from a Load instruction will always commit in-order.
  //
  ca_grad_w1  = ca_adv & grad_ack & ca_load_r;

  //==========================================================================
  // ar_load_nxt is the next registered value of ar_load_r.
  // The ar_load_r state bit indicates if there was a load in the graduation
  // buffers, or was entering the graduation buffers, in the previous cycle.
  // It therefore is 1 whenever a graduation buffer entry contains a valid
  // load context, or if a previously-graduated load is currently retiring
  // at the Writeback stage.
  //
  ar_load_nxt = ca_grad_w1
              | ar0_is_load_r
              | ar1_is_load_r
              | ar2_is_load_r
              | ar3_is_load_r
              | ar4_is_load_r
              | ar5_is_load_r
              | ar6_is_load_r
              | ar7_is_load_r
              ;

  //==========================================================================
  // ca_to_ar is asserted whenever a Commit-stage instruction graduates to
  // the Writeback stage and defers the retirement of its result.
  // This also indicates that the next post-commit tag to be allocated
  // will be assigned a new context.
  //
  ca_to_ar    = ca_adv & ca_grad_req & ca_grad_allowed;

  //==========================================================================
  // Determine the one-hot signals that indicate when each tag is being
  // allocated a new context in the current cycle.
  //
  ar_a        = (ar_alloc_hot   & {8{ca_to_ar}});

  ar_v        = ar_a & {8{ar_wenb_nxt}};

  //==========================================================================
  // Determine the one-hot signals that indicate when each tag is being
  // de-allocated, and hence retired, in the current cycle.
  //
  ar_d        = (ar_dealloc_hot & ar_tags_valid & {8{ca_retire_req}});

  //==========================================================================
  // Determine one-hot signals to indicate, for each tag t, that it is
  // neither allocated nor deallocated in the current cycle.
  //
  ar_f        = (~ar_a) & (~ar_d);

  //==========================================================================
  // Determine one-hot signals to indicate, for each tag t, if it could be
  // subject to squashing of one of its write-enables in the current cycle.
  // This happens if there is a WAW hazard between the current CA-stage
  // instruction and each graduation buffer entry. The squashing will only
  // take place if the CA-stage instruction commits an in-order write,
  // but we allow the ar_s vector elements to be asserted speculatively,
  // as their main purpose is dynamic power saving and they are not functionally
  // critical provided they are always asserted when a change is required to the
  // corresponding entry.
  //
  ar_s        = {
                    (ca_kill_ar7[`npuarc_K_W1_LO] | ca_kill_ar7[`npuarc_K_W1_HI]),
                    (ca_kill_ar6[`npuarc_K_W1_LO] | ca_kill_ar6[`npuarc_K_W1_HI]),
                    (ca_kill_ar5[`npuarc_K_W1_LO] | ca_kill_ar5[`npuarc_K_W1_HI]),
                    (ca_kill_ar4[`npuarc_K_W1_LO] | ca_kill_ar4[`npuarc_K_W1_HI]),
                    (ca_kill_ar3[`npuarc_K_W1_LO] | ca_kill_ar3[`npuarc_K_W1_HI]),
                    (ca_kill_ar2[`npuarc_K_W1_LO] | ca_kill_ar2[`npuarc_K_W1_HI]),
                    (ca_kill_ar1[`npuarc_K_W1_LO] | ca_kill_ar1[`npuarc_K_W1_HI]),
                    (ca_kill_ar0[`npuarc_K_W1_LO] | ca_kill_ar0[`npuarc_K_W1_HI])
                };

  //==========================================================================
  // Enable updates to each graduation buffer element (tags) if allocating
  // or deallocating that element. Allocation happens when a graduation
  // request is acknowledged, and the Commit stage advances. A deallocation
  // happens when a retirement request is made for the given ca_retire_tag
  // entry, and that entry is currently allocated.
  // Graduation buffer updates are also enabled if they are involved in a
  // WAW hazard with a CA-stage instruction. This may clear one or more
  // write-enable bit, in one or more entries, provided the CA-stage
  // instruction actually commits.
  //
  ar_tag_en   = ar_a | ar_d | ar_s;

  //==========================================================================
  // Derive the next (occupancy) state of the graduation buffer as a
  // function of whether any tags are currently being deallocated or
  // allocated in the current cycle.
  //
  ar_tags_next_state= (ar_tags_valid & (~ar_d)) | ar_a;

  //==========================================================================
  // Determine if the graduation buffer tags will be fully-allocated
  // in the next cycle. This is the case if the current ar_tags_valid bits,
  // with any deallocated bits removed and any allocated bits added,
  // are all set to 1.
  //
  ar_tags_full_nxt = &ar_tags_next_state;

  //==========================================================================
  // Determine if the graduation buffer will be empty in the next cycle.
  //
  ar_tags_empty_nxt = ~|ar_tags_next_state;

  //==========================================================================
  // Enable updates to ar_tags_full_r if any tag is updated. This is indicated
  // by any one of the entries being allocated or deallocated. Squashing a
  // write-enable within one of the entries will not affect the full status
  // of the graduation buffers and therefore ar_s is not included in the
  // update condition.
  //
  ar_full_en  = |(ar_a | ar_d);

  //==========================================================================
  // Compute the next value for the dependency matrix elements between the
  // CA stage and each of the graduation buffer entries. This is assigned
  // to the dependency matrix on the next cycle, if dp_ca_enb == 1, and
  // is also used to compute whether there will be a WAW hazard in CA
  // during the following cycle.
  //
  dp_ca_ar0_nxt = ({4{  x3_adv     &   ar_v[0] }} & mg_x3_ca_r )
                |  ({4{  x3_adv     &   ar_f[0] }} & dp_x3_ar0_r)
                |  ({4{(~ca_enable) & (~ar_d[0])}} & dp_ca_ar0_r);

  dp_ca_ar1_nxt = ({4{  x3_adv     &   ar_v[1] }} & mg_x3_ca_r )
                |  ({4{  x3_adv     &   ar_f[1] }} & dp_x3_ar1_r)
                |  ({4{(~ca_enable) & (~ar_d[1])}} & dp_ca_ar1_r);

  dp_ca_ar2_nxt = ({4{  x3_adv     &   ar_v[2] }} & mg_x3_ca_r )
                |  ({4{  x3_adv     &   ar_f[2] }} & dp_x3_ar2_r)
                |  ({4{(~ca_enable) & (~ar_d[2])}} & dp_ca_ar2_r);

  dp_ca_ar3_nxt = ({4{  x3_adv     &   ar_v[3] }} & mg_x3_ca_r )
                |  ({4{  x3_adv     &   ar_f[3] }} & dp_x3_ar3_r)
                |  ({4{(~ca_enable) & (~ar_d[3])}} & dp_ca_ar3_r);

  dp_ca_ar4_nxt = ({4{  x3_adv     &   ar_v[4] }} & mg_x3_ca_r )
                |  ({4{  x3_adv     &   ar_f[4] }} & dp_x3_ar4_r)
                |  ({4{(~ca_enable) & (~ar_d[4])}} & dp_ca_ar4_r);

  dp_ca_ar5_nxt = ({4{  x3_adv     &   ar_v[5] }} & mg_x3_ca_r )
                |  ({4{  x3_adv     &   ar_f[5] }} & dp_x3_ar5_r)
                |  ({4{(~ca_enable) & (~ar_d[5])}} & dp_ca_ar5_r);

  dp_ca_ar6_nxt = ({4{  x3_adv     &   ar_v[6] }} & mg_x3_ca_r )
                |  ({4{  x3_adv     &   ar_f[6] }} & dp_x3_ar6_r)
                |  ({4{(~ca_enable) & (~ar_d[6])}} & dp_ca_ar6_r);

  dp_ca_ar7_nxt = ({4{  x3_adv     &   ar_v[7] }} & mg_x3_ca_r )
                |  ({4{  x3_adv     &   ar_f[7] }} & dp_x3_ar7_r)
                |  ({4{(~ca_enable) & (~ar_d[7])}} & dp_ca_ar7_r);

end

always @*
begin : waw_nxt_PROC
  //==========================================================================
  // Detect if there will be a WAW dependency active at the CA stage during
  // the following cycle. By computing this in the cycle before the hazard,
  // and registering it in a flip-flop, we avoid critical timing issues when
  // using ca_waw_haz_r to define upstream stall conditions via ca_has_w1.
  //
  ca_waw_haz_nxt  = (dp_ca_ar0_nxt[`npuarc_W1_HI] | dp_ca_ar0_nxt[`npuarc_W1_LO])
                  | (dp_ca_ar1_nxt[`npuarc_W1_HI] | dp_ca_ar1_nxt[`npuarc_W1_LO])
                  | (dp_ca_ar2_nxt[`npuarc_W1_HI] | dp_ca_ar2_nxt[`npuarc_W1_LO])
                  | (dp_ca_ar3_nxt[`npuarc_W1_HI] | dp_ca_ar3_nxt[`npuarc_W1_LO])
                  | (dp_ca_ar4_nxt[`npuarc_W1_HI] | dp_ca_ar4_nxt[`npuarc_W1_LO])
                  | (dp_ca_ar5_nxt[`npuarc_W1_HI] | dp_ca_ar5_nxt[`npuarc_W1_LO])
                  | (dp_ca_ar6_nxt[`npuarc_W1_HI] | dp_ca_ar6_nxt[`npuarc_W1_LO])
                  | (dp_ca_ar7_nxt[`npuarc_W1_HI] | dp_ca_ar7_nxt[`npuarc_W1_LO])
                  ;
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// ZNCV flag pipeline - principles of operation                             //
//                                                                          //
// The HS pipeline maintains two copies of the ZNCV-flags: a                //
// speculative set at X2 and the true architectural set in WA. Each         //
// set of flags is produced by the preceeding ALU.                          //
//                                                                          //
// The flag pipeline is complicated somewhat by the ability of              //
// flag-producing instruction to be deferred to the later ALU in CA         //
// (typically as a consequence of an unresolve data-dependency). In         //
// doing this, we must account for any as yet unevaluated flag              //
// producing instruction downstream of X1 before we can consider            //
// whether to evaluate any flag-consumers. 'x1_flag_dep' is derived to      //
// maintain a mapping between the dependency of flags for the               //
// instruction in X1 versus the flags in X2 (x2_zncv_r), the validity       //
// of which is denoted by 'x2_zncv_valid_r'.                                //
//                                                                          //
// The forwarding network below is designed to track unresolved flag        //
// dependencies and to manage the update of the speculative flag set        //
// in response to instruction being evaluated at both X1 and CA.            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: dp_x2_flag_upt_PROC

  //==========================================================================
  // Determine the (sub)set of ZNCV flags used by the X1 instruction.
  //
  if (x1_eia_op_r & (|x1_zncv_wen_r))
             x1_flag_use = 4'b1111;
  else
  case (x1_q_field_r)
    5'h00:   x1_flag_use = 4'b0000;
    5'h01:   x1_flag_use = 4'b1000;
    5'h02:   x1_flag_use = 4'b1000;
    5'h03:   x1_flag_use = 4'b0100;
    5'h04:   x1_flag_use = 4'b0100;
    5'h05:   x1_flag_use = 4'b0010;
    5'h06:   x1_flag_use = 4'b0010;
    5'h07:   x1_flag_use = 4'b0001;
    5'h08:   x1_flag_use = 4'b0001;
    5'h09:   x1_flag_use = 4'b1101;
    5'h0a:   x1_flag_use = 4'b0101;
    5'h0b:   x1_flag_use = 4'b0101;
    5'h0c:   x1_flag_use = 4'b1101;
    5'h0d:   x1_flag_use = 4'b1010;
    5'h0e:   x1_flag_use = 4'b1010;
    5'h0f:   x1_flag_use = 4'b1100;
    default: x1_flag_use = 4'b0000;
  endcase

  // any instruction that relies on a carry-in must set x1_flag_use[`C_FLAG]
  //
  x1_flag_use[`npuarc_C_FLAG] = x1_flag_use[`npuarc_C_FLAG] | x1_with_carry_r;

  //==========================================================================
  // An instruction at X1 can evaluate only if there are no unresolved
  // dependencies on status flags that are to be produced by an as-yet
  // unevaluated instruction. The x2_zncv_valid_r vector indicates whether
  // there are any pending writes from instructions at X2 and beyond.
  // The x1_flag_use vector indicates the specific flags that the X1
  // instruction needs to use.
  // The x1_flags_ready signal is not asserted if the X1 instruction uses
  // any flags and there is an entry in the graduation buffers that is set
  // to modify flags.
  // Also ready if instruction at X1 is eia because its bflags input was
  // resolved prior to dispatch.
  //
  x1_flags_ready    = ~(|(x1_flag_use & (~x2_zncv_valid_r)))
                    & (~((|x1_flag_use) & ar_zncv_upt_r))
                    | (x1_eia_fast_op_r & (x1_flag_use == 4'h0))
                    ;

  //==========================================================================
  // Identify [k]flag instructions.
  //
  x1_is_flag     = {`npuarc_ZNCV_BITS{x1_flag_op_r & (~x1_signed_op_r)}};
  x2_is_flag     = {`npuarc_ZNCV_BITS{x2_flag_op_r & (~x2_signed_op_r)}};
  x3_is_flag     = {`npuarc_ZNCV_BITS{x3_flag_op_r & (~x3_signed_op_r)}};

  //==========================================================================
  // Logic for APEX instruction source bflags dependency
  // An APEX instruction at SA is free from any bflags dependency if the
  // flags are valid at X2 and there is no flag-modifying instruction in X1.
  //
  sa_flags_ready = (x2_zncv_valid_r == 4'hf)
                 & (!x1_valid_r | (!x1_flag_op_r & (x1_zncv_wen_r == 4'h0)));


  //==========================================================================
  // The instruction in X1 cannot be evaluated whenever there is an
  // unresolved flag dependency between the current and a downstream
  // instruction. This typically occurs when a flag-producing
  // instruction has been deferred (to evaluate in CA), and produces
  // flags upon which the current instruction in X1 depends.
  //
  x1_no_eval        = ~x1_flags_ready
                    ;

  //==========================================================================
  // Specific flags in the ZNCV vector are invalidated when a flag-modifying
  // instruction is in X1 and will not be evaluated in X1.
  //
  flag_invalidate   =  {`npuarc_ZNCV_BITS{(~x1_flags_done) & x1_pass}}
                    &  x1_zncv_wen_r
                    & (~x1_is_flag)
                    ;

  //==========================================================================
  // Forward new flags from X1 to the speculative register at X2 on
  // restart (where the register is being reset to a known good
  // value), OR when a [k]flag or flag-modifying instruction is
  // advancing into X2 and shall be evaluated.
  //
  fwd_zncv_x1       = (~flag_invalidate)
                    & {`npuarc_ZNCV_BITS{x1_adv & x1_cond}}
                    & (   x1_zncv_wen_r
                        | x1_is_flag
                      )
                    ;

  //==========================================================================
  // Forward new flags produced in CA when each specific flag will be
  // updated by the CA-stage instruction (ca_zncv_wen_r) and the CA-stage
  // instruction is being evaluated at that stage (~ca_done_r, and the
  // predication condition for the CA-stage instruction is true (ca_q_cond),
  // and the CA-stage instruction will advance to WA (ca_adv).
  //
  fwd_zncv_x1_ca    =  (   (ca_zncv_wen_r  & {`npuarc_ZNCV_BITS{   (   (~ca_done_r)
                                                              | (   ca_store_r
                                                                   & ca_locked_r
                                                                 )
                                                            )
                                                          & (~(ca_grad_req & ca_grad_allowed))
                                                          & (~ca_stall)
                                                          & (ca_normal_evt)

                                                        }})
                         | (dp_retire_zncv & {`npuarc_ZNCV_BITS{retire_ack}})
                       )
                    & (~(   (x3_is_flag | x3_zncv_wen_r)
                          & {`npuarc_ZNCV_BITS{   (~x3_done_r)
                                         | (x3_store_r & x3_locked_r)
                                       }}
                       ))
                    & (~(   (x2_is_flag | x2_zncv_wen_r)
                          & {`npuarc_ZNCV_BITS{   (~(x2_done_r | x2_slow_op_r))
                                         | (x2_store_r & x2_locked_r)
                                       }}
                       ))
                    & (~x2_zncv_valid_r)
                    & (~fwd_zncv_x1)
                    & (~flag_invalidate)
                    ;

  //==========================================================================
  // Forward ('fwd') the speculative ZNCV flags (retaining their
  // current value) whenever we know the current state of X1 is not
  // explicitly invalidating flags, or when new flags have been
  // computed in X1 or CA.
  //
  fwd_zncv_x1_x2    = ~flag_invalidate
                    & (~(   fwd_zncv_x1
                         | fwd_zncv_x1_ca
                       ))
                    ;

  //==========================================================================
  // Forward committed machine architectural flags to the speculative
  // X2 set on a pipeline flush, or on a pending flag update.
  //
  fwd_zncv_x1_ar    = flag_flush_pipe
                    | update_flags_x2
                    ;

  //==========================================================================
  // Determine whether the CA instruction uses flags as part of its evaluation
  // at the CA stage. This is true when the Q-field of the CA instruction is
  // non-zero, or if the with_carry ucode bit is set to 1 (ADC, SBC, RLC).
  //
  ca_uses_flags     = ca_with_carry_r | (|ca_q_field_r);

end // block: dp_x2_flag_upt_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @deferred_flag_update_PROC:                                              //
//                                                                          //
// Combinational process to identify a unresolve flag dependency on a       //
// mispredicted branch/jump instruction with a flag producing/setting       //
// instruction in its D-slot.                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: deferred_flag_update_PROC

  //==========================================================================
  //
  update_flags_x2        = pending_flag_upt_r
                         & wa_cmt_flag_evt_r
                         ;

  //==========================================================================
  // The associated D-Slot instruction of a post-committed branch/jump
  // instruction is present in the pipeline and shall modify the
  // machine flags on commit.
  //

  flag_producer_in_dslot = (da_wa_dslot & (|da_zncv_wen)   & (~da_kill))
                         | (sa_wa_dslot & (|sa_zncv_wen_r) & (~sa_kill))
                         | (x1_wa_dslot & (|x1_zncv_wen_r) & (~x1_kill))
                         | (x2_wa_dslot & (|x2_zncv_wen_r) & (~x2_kill))
                         | (x3_wa_dslot & (|x3_zncv_wen_r) & (~x3_kill))
                         | (ca_wa_dslot & (|ca_zncv_wen_r) & (~ca_kill))
                         ;

  //==========================================================================
  // Identify a pending flag update (1) on the misprediction of a CTI
  // with a flag producing D-slot instruction, and (2) retain until
  // the speculative flags at X2 have been updated or a pipeline flush
  // has occurred. Flags may be pending due to a pre-commit inst.f or a
  // post-commit inst.f in the graduation buffer. Retirement of either of
  // these two types of instruction will trigger update_flags_x2 if the
  // pending_flag_upt_r signal is set to 1. This should only clear the
  // pending_flag_upt_r flip-flop if the flag_producer_in_dslot status
  // has been rescinded. This covers the case where there is a graduated
  // flag-setting instruction and a flag-setting delay-slot instruction
  // in the pipeline simultaneously. The flag-setting GB entry always retires
  // first, and because we still have a flag_producer_in_dslot condition,
  // the pending_flag_upt_r status remains asserted.
  //
  pending_flag_upt_nxt   = (   wa_mispred_r                       // (1)
                             & flag_producer_in_dslot
                             & (~pending_flag_upt_r)
                           )
                         | (   ~(   (    update_flags_x2
                                      & (!flag_producer_in_dslot))  // (2)
                                  | wa_restart
                                )
                             & pending_flag_upt_r
                           )
                         ;
  pending_eia_cc =  sa_q_field_r[4] &
                   (  (|x1_zncv_wen_r) & x1_valid_r
                    | (|x2_zncv_wen_r) & x2_valid_r
                    | (|x3_zncv_wen_r) & x3_valid_r
                    | (|ca_zncv_wen_r) & ca_valid_r
                    | ar0_flag_wen_r
                    | ar1_flag_wen_r
                    | ar2_flag_wen_r
                    | ar3_flag_wen_r
                    | ar4_flag_wen_r
                    | ar5_flag_wen_r
                    | ar6_flag_wen_r
                    | ar7_flag_wen_r
                    )
                   | (|sa_zncv_wen_r) &
                   ( x1_q_field_r[4] & x1_valid_r |
                     x2_q_field_r[4] & x2_valid_r |
                     x3_q_field_r[4] & x3_valid_r |
                     ca_q_field_r[4] & ca_valid_r
                    );

  //==========================================================================
  // Enable flag update register on an initial misprediction and
  // retain until flag update.
  //
  pending_flag_upt_cg0   = wa_mispred_r
                         | pending_flag_upt_r
                         ;

  //==========================================================================
  // Instruction at SA is a (1,3) flag consuming or (2) flag producing,
  // instruction.
  //
  sa_haz_on_zncv         = sa_valid_r
                         & (   (|sa_q_field_r)                        // (1)
                             | (|sa_zncv_wen_r)                       // (2)
                             | sa_with_carry_r                        // (3)
                           )
                         ;

  //==========================================================================
  // A flag dependency exists when the instruction in SA is
  // flag-dependent and is not the D-Slot instruction of the committed
  // CTI and there is an outstanding flag update.
  //
  flag_dependency_at_sa  =  sa_haz_on_zncv
                         & (~(da_wa_dslot | sa_wa_dslot))
                         &  pending_flag_upt_r
                         ;

  //==========================================================================
  // Flush pipeline (thereby restoring speculative flag set to the
  // architectural state) on a WA restart when there are no flag
  // producing instruction in the D-Slot position.
  //
  flag_flush_pipe        = (wa_restart & (~flag_producer_in_dslot))
                         | (ct_replay)
                         | wa_uopld_status32
                         ;

end // block: deferred_flag_update_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sequential process to track the evolution of dependency states           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : dep_state_PROC
  if (rst_a == 1'b1)
    begin
    // ---- reset the Operands-stage dependency states
    //
    dp_sa_x1_r  <= `npuarc_PRE_RAW_BITS'd0;
    dp_sa_x2_r  <= `npuarc_PRE_RAW_BITS'd0;
    dp_sa_x3_r  <= `npuarc_PRE_RAW_BITS'd0;
    dp_sa_ca_r  <= `npuarc_PRE_RAW_BITS'd0;
    dp_sa_wa_r  <= `npuarc_PRE_RAW_BITS'd0;
    dp_sa_ar0_r <= `npuarc_POST_RAW_BITS'd0;
    dp_sa_ar1_r <= `npuarc_POST_RAW_BITS'd0;
    dp_sa_ar2_r <= `npuarc_POST_RAW_BITS'd0;
    dp_sa_ar3_r <= `npuarc_POST_RAW_BITS'd0;
    dp_sa_ar4_r <= `npuarc_POST_RAW_BITS'd0;
    dp_sa_ar5_r <= `npuarc_POST_RAW_BITS'd0;
    dp_sa_ar6_r <= `npuarc_POST_RAW_BITS'd0;
    dp_sa_ar7_r <= `npuarc_POST_RAW_BITS'd0;
    //
    // ---- reset the Exec1-stage dependency states
    //
    dp_x1_x2_r  <= `npuarc_DP_PRE_BITS'd0;
    dp_x1_x3_r  <= `npuarc_DP_PRE_BITS'd0;
    dp_x1_ca_r  <= `npuarc_DP_PRE_BITS'd0;
    dp_x1_wa_r  <= `npuarc_DP_PRE_BITS'd0;
    dp_x1_ar0_r <= `npuarc_DP_POST_BITS'd0;
    dp_x1_ar1_r <= `npuarc_DP_POST_BITS'd0;
    dp_x1_ar2_r <= `npuarc_DP_POST_BITS'd0;
    dp_x1_ar3_r <= `npuarc_DP_POST_BITS'd0;
    dp_x1_ar4_r <= `npuarc_DP_POST_BITS'd0;
    dp_x1_ar5_r <= `npuarc_DP_POST_BITS'd0;
    dp_x1_ar6_r <= `npuarc_DP_POST_BITS'd0;
    dp_x1_ar7_r <= `npuarc_DP_POST_BITS'd0;
    //
    // ---- reset the Exec2-stage dependency states
    //
    dp_x2_x3_r  <= `npuarc_DP_PRE_BITS'd0;
    dp_x2_ca_r  <= `npuarc_DP_PRE_BITS'd0;
    dp_x2_wa_r  <= `npuarc_DP_PRE_BITS'd0;
    dp_x2_ar0_r <= `npuarc_DP_POST_BITS'd0;
    dp_x2_ar1_r <= `npuarc_DP_POST_BITS'd0;
    dp_x2_ar2_r <= `npuarc_DP_POST_BITS'd0;
    dp_x2_ar3_r <= `npuarc_DP_POST_BITS'd0;
    dp_x2_ar4_r <= `npuarc_DP_POST_BITS'd0;
    dp_x2_ar5_r <= `npuarc_DP_POST_BITS'd0;
    dp_x2_ar6_r <= `npuarc_DP_POST_BITS'd0;
    dp_x2_ar7_r <= `npuarc_DP_POST_BITS'd0;
    //
    // ---- reset the Exec2-stage dependency states
    //
    dp_x3_ca_r  <= `npuarc_DP_PRE_BITS'd0;
    dp_x3_wa_r  <= `npuarc_DP_PRE_BITS'd0;
    dp_x3_ar0_r <= `npuarc_DP_POST_BITS'd0;
    dp_x3_ar1_r <= `npuarc_DP_POST_BITS'd0;
    dp_x3_ar2_r <= `npuarc_DP_POST_BITS'd0;
    dp_x3_ar3_r <= `npuarc_DP_POST_BITS'd0;
    dp_x3_ar4_r <= `npuarc_DP_POST_BITS'd0;
    dp_x3_ar5_r <= `npuarc_DP_POST_BITS'd0;
    dp_x3_ar6_r <= `npuarc_DP_POST_BITS'd0;
    dp_x3_ar7_r <= `npuarc_DP_POST_BITS'd0;
    //
    // ---- reset the Commit-stage dependency states
    //
    dp_ca_wa_r  <= `npuarc_DP_PRE_BITS'd0;
    dp_ca_ar0_r <= `npuarc_DP_POST_BITS'd0;
    dp_ca_ar1_r <= `npuarc_DP_POST_BITS'd0;
    dp_ca_ar2_r <= `npuarc_DP_POST_BITS'd0;
    dp_ca_ar3_r <= `npuarc_DP_POST_BITS'd0;
    dp_ca_ar4_r <= `npuarc_DP_POST_BITS'd0;
    dp_ca_ar5_r <= `npuarc_DP_POST_BITS'd0;
    dp_ca_ar6_r <= `npuarc_DP_POST_BITS'd0;
    dp_ca_ar7_r <= `npuarc_DP_POST_BITS'd0;
    ca_waw_haz_r  <= 1'b0;
    end
  else
    begin
    if (dp_sa_enb == 1'b1)
      begin
      // Progression of dependence vectors at Operands stage
      //
      dp_sa_x1_r   <= ({4{  da_adv  &   sa_adv }} & dp_da_sa  )
                    | ({4{  da_adv  & x1_retain}} & dp_da_x1  )
                    | ({4{sa_retain & x1_retain}} & qd_sa_x1  );

      dp_sa_x2_r   <= ({4{sa_retain &   x1_adv }} & qd_sa_x1  )
                    | ({4{  da_adv  &   x1_adv }} & dp_da_x1  )
                    | ({4{  da_adv  & x2_retain}} & dp_da_x2  )
                    | ({4{sa_retain & x2_retain}} & qd_sa_x2  );

      dp_sa_x3_r   <= ({4{sa_retain &   x2_adv }} & qd_sa_x2  )
                    | ({4{  da_adv  &   x2_adv }} & dp_da_x2  )
                    | ({4{  da_adv  & x3_retain}} & dp_da_x3  )
                    | ({4{sa_retain & x3_retain}} & qd_sa_x3  );
// spyglass disable_block Ac_conv01 
// SMD: syncs converge on combinational gate
// SJ:  safe, causes no issues
      dp_sa_ca_r   <= ({4{sa_retain &   x3_adv }} & qd_sa_x3  )
                    | ({4{  da_adv  &   x3_adv }} & dp_da_x3  )
                    | ({4{  da_adv  & ca_retain}} & dp_da_ca  )
                    | ({4{sa_retain & ca_retain}} & qd_sa_ca  );
// spyglass enable_block Ac_conv01 
      dp_sa_wa_r[`npuarc_RAW_W0] <= 
                  ({2{sa_retain & ca_adv_w0 }} & qd_sa_ca[`npuarc_RAW_W0])
                | ({2{  da_adv  & ca_adv_w0 }} & dp_da_ca[`npuarc_RAW_W0])
                | ({2{  da_adv  & wa_retain }} & dp_da_wa[`npuarc_RAW_W0])
                | ({2{sa_retain & wa_retain }} & qd_sa_wa[`npuarc_RAW_W0]);

      dp_sa_wa_r[`npuarc_RAW_W1] <= 
                  ({2{sa_retain & ca_adv_w1 }} & qd_sa_ca[`npuarc_RAW_W1])
                | ({2{  da_adv  & ca_adv_w1 }} & dp_da_ca[`npuarc_RAW_W1])
                | ({2{  da_adv  & wa_retain }} & dp_da_wa[`npuarc_RAW_W1])
                | ({2{sa_retain & wa_retain }} & qd_sa_wa[`npuarc_RAW_W1])
                | ({2{  da_adv  & retire_ack}} & dp_da_ar[`npuarc_RAW_W1])
                | ({2{sa_retain & retire_ack}} & dp_sa1_ar[`npuarc_RAW_W1]);

      dp_sa_ar0_r  <= ({2{sa_retain    &   ar_v[0] }} & mg_sa_ca_h )
                    | ({2{  da_adv     &   ar_v[0] }} & mg_da_ca   )
                    | ({2{  da_adv     &   ar_f[0] }} & dp_da_ar0  )
                    | ({2{(~sa_enable) & (~ar_d[0])}} & qd_sa_ar0 );

      dp_sa_ar1_r  <= ({2{sa_retain    &   ar_v[1] }} & mg_sa_ca_h )
                    | ({2{  da_adv     &   ar_v[1] }} & mg_da_ca   )
                    | ({2{  da_adv     &   ar_f[1] }} & dp_da_ar1  )
                    | ({2{(~sa_enable) & (~ar_d[1])}} & qd_sa_ar1 );

      dp_sa_ar2_r  <= ({2{sa_retain    &   ar_v[2] }} & mg_sa_ca_h )
                    | ({2{  da_adv     &   ar_v[2] }} & mg_da_ca   )
                    | ({2{  da_adv     &   ar_f[2] }} & dp_da_ar2  )
                    | ({2{(~sa_enable) & (~ar_d[2])}} & qd_sa_ar2 );

      dp_sa_ar3_r  <= ({2{sa_retain    &   ar_v[3] }} & mg_sa_ca_h )
                    | ({2{  da_adv     &   ar_v[3] }} & mg_da_ca   )
                    | ({2{  da_adv     &   ar_f[3] }} & dp_da_ar3  )
                    | ({2{(~sa_enable) & (~ar_d[3])}} & qd_sa_ar3 );

      dp_sa_ar4_r  <= ({2{sa_retain    &   ar_v[4] }} & mg_sa_ca_h )
                    | ({2{  da_adv     &   ar_v[4] }} & mg_da_ca   )
                    | ({2{  da_adv     &   ar_f[4] }} & dp_da_ar4  )
                    | ({2{(~sa_enable) & (~ar_d[4])}} & qd_sa_ar4 );

      dp_sa_ar5_r  <= ({2{sa_retain    &   ar_v[5] }} & mg_sa_ca_h )
                    | ({2{  da_adv     &   ar_v[5] }} & mg_da_ca   )
                    | ({2{  da_adv     &   ar_f[5] }} & dp_da_ar5  )
                    | ({2{(~sa_enable) & (~ar_d[5])}} & qd_sa_ar5 );

      dp_sa_ar6_r  <= ({2{sa_retain    &   ar_v[6] }} & mg_sa_ca_h )
                    | ({2{  da_adv     &   ar_v[6] }} & mg_da_ca   )
                    | ({2{  da_adv     &   ar_f[6] }} & dp_da_ar6  )
                    | ({2{(~sa_enable) & (~ar_d[6])}} & qd_sa_ar6 );

      dp_sa_ar7_r  <= ({2{sa_retain    &   ar_v[7] }} & mg_sa_ca_h )
                    | ({2{  da_adv     &   ar_v[7] }} & mg_da_ca   )
                    | ({2{  da_adv     &   ar_f[7] }} & dp_da_ar7  )
                    | ({2{(~sa_enable) & (~ar_d[7])}} & qd_sa_ar7 );

      end

    if (dp_x1_enb == 1'b1)
      begin
      // Progression of dependence vectors at Exec1 stage
      //
      dp_x1_x2_r   <= ({8{  sa_adv  &   x1_adv }} & cn_sa_x1  )
                    | ({8{  sa_adv  & x2_retain}} & cn_sa_x2  )
                    | ({8{x1_retain & x2_retain}} & dp_x1_x2_r);

      dp_x1_x3_r   <= ({8{x1_retain &   x2_adv }} & dp_x1_x2_r)
                    | ({8{  sa_adv  &   x2_adv }} & cn_sa_x2  )
                    | ({8{  sa_adv  & x3_retain}} & cn_sa_x3  )
                    | ({8{x1_retain & x3_retain}} & dp_x1_x3_r);

      dp_x1_ca_r   <= ({8{x1_retain &   x3_adv }} & dp_x1_x3_r)
                    | ({8{  sa_adv  &   x3_adv }} & cn_sa_x3  )
                    | ({8{  sa_adv  & ca_retain}} & cn_sa_ca  )
                    | ({8{x1_retain & ca_retain}} & dp_x1_ca_r);

      dp_x1_wa_r[`npuarc_DP_W0] <=
                  ({`npuarc_DP_W0_BITS{x1_retain & ca_adv_w0 }} & dp_x1_ca_r[`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{  sa_adv  & ca_adv_w0 }} & cn_sa_ca  [`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{  sa_adv  & wa_retain }} & cn_sa_wa  [`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{x1_retain & wa_retain }} & dp_x1_wa_r[`npuarc_DP_W0]);

      dp_x1_wa_r[`npuarc_DP_W1] <=
                  ({`npuarc_DP_W1_BITS{x1_retain & ca_adv_w1 }} & dp_x1_ca_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  sa_adv  & ca_adv_w1 }} & cn_sa_ca  [`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  sa_adv  & wa_retain }} & cn_sa_wa  [`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{x1_retain & wa_retain }} & dp_x1_wa_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  sa_adv  & retire_ack}} & dp_sa2_ar [`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{x1_retain & retire_ack}} & dp_x1_ar  [`npuarc_DP_W1]);

      dp_x1_ar0_r  <= ({4{x1_retain    &   ar_v[0] }} & mg_x1_ca_r )
                    | ({4{  sa_adv     &   ar_v[0] }} & mg_sa_ca_r )
                    | ({4{  sa_adv     &   ar_f[0] }} & cn_sa_ar0)
                    | ({4{(~x1_enable) & (~ar_d[0])}} & dp_x1_ar0_r);

      dp_x1_ar1_r  <= ({4{x1_retain    &   ar_v[1] }} & mg_x1_ca_r )
                    | ({4{  sa_adv     &   ar_v[1] }} & mg_sa_ca_r )
                    | ({4{  sa_adv     &   ar_f[1] }} & cn_sa_ar1)
                    | ({4{(~x1_enable) & (~ar_d[1])}} & dp_x1_ar1_r);

      dp_x1_ar2_r  <= ({4{x1_retain    &   ar_v[2] }} & mg_x1_ca_r )
                    | ({4{  sa_adv     &   ar_v[2] }} & mg_sa_ca_r )
                    | ({4{  sa_adv     &   ar_f[2] }} & cn_sa_ar2)
                    | ({4{(~x1_enable) & (~ar_d[2])}} & dp_x1_ar2_r);

      dp_x1_ar3_r  <= ({4{x1_retain    &   ar_v[3] }} & mg_x1_ca_r )
                    | ({4{  sa_adv     &   ar_v[3] }} & mg_sa_ca_r )
                    | ({4{  sa_adv     &   ar_f[3] }} & cn_sa_ar3)
                    | ({4{(~x1_enable) & (~ar_d[3])}} & dp_x1_ar3_r);

      dp_x1_ar4_r  <= ({4{x1_retain    &   ar_v[4] }} & mg_x1_ca_r )
                    | ({4{  sa_adv     &   ar_v[4] }} & mg_sa_ca_r )
                    | ({4{  sa_adv     &   ar_f[4] }} & cn_sa_ar4)
                    | ({4{(~x1_enable) & (~ar_d[4])}} & dp_x1_ar4_r);

      dp_x1_ar5_r  <= ({4{x1_retain    &   ar_v[5] }} & mg_x1_ca_r )
                    | ({4{  sa_adv     &   ar_v[5] }} & mg_sa_ca_r )
                    | ({4{  sa_adv     &   ar_f[5] }} & cn_sa_ar5)
                    | ({4{(~x1_enable) & (~ar_d[5])}} & dp_x1_ar5_r);

      dp_x1_ar6_r  <= ({4{x1_retain    &   ar_v[6] }} & mg_x1_ca_r )
                    | ({4{  sa_adv     &   ar_v[6] }} & mg_sa_ca_r )
                    | ({4{  sa_adv     &   ar_f[6] }} & cn_sa_ar6)
                    | ({4{(~x1_enable) & (~ar_d[6])}} & dp_x1_ar6_r);

      dp_x1_ar7_r  <= ({4{x1_retain    &   ar_v[7] }} & mg_x1_ca_r )
                    | ({4{  sa_adv     &   ar_v[7] }} & mg_sa_ca_r )
                    | ({4{  sa_adv     &   ar_f[7] }} & cn_sa_ar7)
                    | ({4{(~x1_enable) & (~ar_d[7])}} & dp_x1_ar7_r);

      end

    if (dp_x2_enb == 1'b1)
      begin
      // Progression of dependence vectors at Exec2 stage
      //
      dp_x2_x3_r   <= ({8{  x1_adv  &   x2_adv }} & dp_x1_x2_r)
                    | ({8{  x1_adv  & x3_retain}} & dp_x1_x3_r)
                    | ({8{x2_retain & x3_retain}} & dp_x2_x3_r);

      dp_x2_ca_r   <= ({8{x2_retain &   x3_adv }} & dp_x2_x3_r)
                    | ({8{  x1_adv  &   x3_adv }} & dp_x1_x3_r)
                    | ({8{  x1_adv  & ca_retain}} & dp_x1_ca_r)
                    | ({8{x2_retain & ca_retain}} & dp_x2_ca_r);

      dp_x2_wa_r[`npuarc_DP_W0] <=
                  ({`npuarc_DP_W0_BITS{x2_retain & ca_adv_w0 }} & dp_x2_ca_r[`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{  x1_adv  & ca_adv_w0 }} & dp_x1_ca_r[`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{  x1_adv  & wa_retain }} & dp_x1_wa_r[`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{x2_retain & wa_retain }} & dp_x2_wa_r[`npuarc_DP_W0]);

      dp_x2_wa_r[`npuarc_DP_W1] <=
                  ({`npuarc_DP_W1_BITS{x2_retain & ca_adv_w1 }} & dp_x2_ca_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  x1_adv  & ca_adv_w1 }} & dp_x1_ca_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  x1_adv  & wa_retain }} & dp_x1_wa_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{x2_retain & wa_retain }} & dp_x2_wa_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  x1_adv  & retire_ack}} & dp_x1_ar  [`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{x2_retain & retire_ack}} & dp_x2_ar  [`npuarc_DP_W1]);

      dp_x2_ar0_r  <= ({4{x2_retain    &   ar_v[0] }} & mg_x2_ca_r )
                    | ({4{  x1_adv     &   ar_v[0] }} & mg_x1_ca_r )
                    | ({4{  x1_adv     &   ar_f[0] }} & dp_x1_ar0_r)
                    | ({4{(~x2_enable) & (~ar_d[0])}} & dp_x2_ar0_r);

      dp_x2_ar1_r  <= ({4{x2_retain    &   ar_v[1] }} & mg_x2_ca_r )
                    | ({4{  x1_adv     &   ar_v[1] }} & mg_x1_ca_r )
                    | ({4{  x1_adv     &   ar_f[1] }} & dp_x1_ar1_r)
                    | ({4{(~x2_enable) & (~ar_d[1])}} & dp_x2_ar1_r);

      dp_x2_ar2_r  <= ({4{x2_retain    &   ar_v[2] }} & mg_x2_ca_r )
                    | ({4{  x1_adv     &   ar_v[2] }} & mg_x1_ca_r )
                    | ({4{  x1_adv     &   ar_f[2] }} & dp_x1_ar2_r)
                    | ({4{(~x2_enable) & (~ar_d[2])}} & dp_x2_ar2_r);

      dp_x2_ar3_r  <= ({4{x2_retain    &   ar_v[3] }} & mg_x2_ca_r )
                    | ({4{  x1_adv     &   ar_v[3] }} & mg_x1_ca_r )
                    | ({4{  x1_adv     &   ar_f[3] }} & dp_x1_ar3_r)
                    | ({4{(~x2_enable) & (~ar_d[3])}} & dp_x2_ar3_r);

      dp_x2_ar4_r  <= ({4{x2_retain    &   ar_v[4] }} & mg_x2_ca_r )
                    | ({4{  x1_adv     &   ar_v[4] }} & mg_x1_ca_r )
                    | ({4{  x1_adv     &   ar_f[4] }} & dp_x1_ar4_r)
                    | ({4{(~x2_enable) & (~ar_d[4])}} & dp_x2_ar4_r);

      dp_x2_ar5_r  <= ({4{x2_retain    &   ar_v[5] }} & mg_x2_ca_r )
                    | ({4{  x1_adv     &   ar_v[5] }} & mg_x1_ca_r )
                    | ({4{  x1_adv     &   ar_f[5] }} & dp_x1_ar5_r)
                    | ({4{(~x2_enable) & (~ar_d[5])}} & dp_x2_ar5_r);

      dp_x2_ar6_r  <= ({4{x2_retain    &   ar_v[6] }} & mg_x2_ca_r )
                    | ({4{  x1_adv     &   ar_v[6] }} & mg_x1_ca_r )
                    | ({4{  x1_adv     &   ar_f[6] }} & dp_x1_ar6_r)
                    | ({4{(~x2_enable) & (~ar_d[6])}} & dp_x2_ar6_r);

      dp_x2_ar7_r  <= ({4{x2_retain    &   ar_v[7] }} & mg_x2_ca_r )
                    | ({4{  x1_adv     &   ar_v[7] }} & mg_x1_ca_r )
                    | ({4{  x1_adv     &   ar_f[7] }} & dp_x1_ar7_r)
                    | ({4{(~x2_enable) & (~ar_d[7])}} & dp_x2_ar7_r);

      end

    if (dp_x3_enb == 1'b1)
      begin
      // Progression of dependence vectors at Exec3 stage
      //
      dp_x3_ca_r   <= ({8{  x2_adv  &   x3_adv }} & dp_x2_x3_r)
                    | ({8{  x2_adv  & ca_retain}} & dp_x2_ca_r)
                    | ({8{x3_retain & ca_retain}} & dp_x3_ca_r);

      dp_x3_wa_r[`npuarc_DP_W0] <=
                  ({`npuarc_DP_W0_BITS{x3_retain & ca_adv_w0 }} & dp_x3_ca_r[`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{  x2_adv  & ca_adv_w0 }} & dp_x2_ca_r[`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{  x2_adv  & wa_retain }} & dp_x2_wa_r[`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{x3_retain & wa_retain }} & dp_x3_wa_r[`npuarc_DP_W0]);

      dp_x3_wa_r[`npuarc_DP_W1] <=
                  ({`npuarc_DP_W1_BITS{x3_retain & ca_adv_w1 }} & dp_x3_ca_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  x2_adv  & ca_adv_w1 }} & dp_x2_ca_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  x2_adv  & wa_retain }} & dp_x2_wa_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{x3_retain & wa_retain }} & dp_x3_wa_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  x2_adv  & retire_ack}} & dp_x2_ar  [`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{x3_retain & retire_ack}} & dp_x3_ar  [`npuarc_DP_W1]);

      dp_x3_ar0_r  <= ({4{x3_retain    &   ar_v[0] }} & mg_x3_ca_r )
                    | ({4{  x2_adv     &   ar_v[0] }} & mg_x2_ca_r )
                    | ({4{  x2_adv     &   ar_f[0] }} & dp_x2_ar0_r)
                    | ({4{(~x3_enable) & (~ar_d[0])}} & dp_x3_ar0_r);

      dp_x3_ar1_r  <= ({4{x3_retain    &   ar_v[1] }} & mg_x3_ca_r )
                    | ({4{  x2_adv     &   ar_v[1] }} & mg_x2_ca_r )
                    | ({4{  x2_adv     &   ar_f[1] }} & dp_x2_ar1_r)
                    | ({4{(~x3_enable) & (~ar_d[1])}} & dp_x3_ar1_r);

      dp_x3_ar2_r  <= ({4{x3_retain    &   ar_v[2] }} & mg_x3_ca_r )
                    | ({4{  x2_adv     &   ar_v[2] }} & mg_x2_ca_r )
                    | ({4{  x2_adv     &   ar_f[2] }} & dp_x2_ar2_r)
                    | ({4{(~x3_enable) & (~ar_d[2])}} & dp_x3_ar2_r);

      dp_x3_ar3_r  <= ({4{x3_retain    &   ar_v[3] }} & mg_x3_ca_r )
                    | ({4{  x2_adv     &   ar_v[3] }} & mg_x2_ca_r )
                    | ({4{  x2_adv     &   ar_f[3] }} & dp_x2_ar3_r)
                    | ({4{(~x3_enable) & (~ar_d[3])}} & dp_x3_ar3_r);

      dp_x3_ar4_r  <= ({4{x3_retain    &   ar_v[4] }} & mg_x3_ca_r )
                    | ({4{  x2_adv     &   ar_v[4] }} & mg_x2_ca_r )
                    | ({4{  x2_adv     &   ar_f[4] }} & dp_x2_ar4_r)
                    | ({4{(~x3_enable) & (~ar_d[4])}} & dp_x3_ar4_r);

      dp_x3_ar5_r  <= ({4{x3_retain    &   ar_v[5] }} & mg_x3_ca_r )
                    | ({4{  x2_adv     &   ar_v[5] }} & mg_x2_ca_r )
                    | ({4{  x2_adv     &   ar_f[5] }} & dp_x2_ar5_r)
                    | ({4{(~x3_enable) & (~ar_d[5])}} & dp_x3_ar5_r);

      dp_x3_ar6_r  <= ({4{x3_retain    &   ar_v[6] }} & mg_x3_ca_r )
                    | ({4{  x2_adv     &   ar_v[6] }} & mg_x2_ca_r )
                    | ({4{  x2_adv     &   ar_f[6] }} & dp_x2_ar6_r)
                    | ({4{(~x3_enable) & (~ar_d[6])}} & dp_x3_ar6_r);

      dp_x3_ar7_r  <= ({4{x3_retain    &   ar_v[7] }} & mg_x3_ca_r )
                    | ({4{  x2_adv     &   ar_v[7] }} & mg_x2_ca_r )
                    | ({4{  x2_adv     &   ar_f[7] }} & dp_x2_ar7_r)
                    | ({4{(~x3_enable) & (~ar_d[7])}} & dp_x3_ar7_r);

      end

    if (dp_ca_enb == 1'b1)
      begin
      // Progression of dependence vectors at Commit stage
      //
      dp_ca_wa_r[`npuarc_DP_W0] <=
                  ({`npuarc_DP_W0_BITS{  x3_adv  & ca_adv_w0 }} & dp_x3_ca_r[`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{  x3_adv  & wa_retain }} & dp_x3_wa_r[`npuarc_DP_W0])
                | ({`npuarc_DP_W0_BITS{ca_retain & wa_retain }} & dp_ca_wa_r[`npuarc_DP_W0]);

      dp_ca_wa_r[`npuarc_DP_W1] <=
                  ({`npuarc_DP_W1_BITS{  x3_adv  & ca_adv_w1 }} & dp_x3_ca_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  x3_adv  & wa_retain }} & dp_x3_wa_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{ca_retain & wa_retain }} & dp_ca_wa_r[`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{  x3_adv  & retire_ack}} & dp_x3_ar  [`npuarc_DP_W1])
                | ({`npuarc_DP_W1_BITS{ca_retain & retire_ack}} & dp_ca_ar  [`npuarc_DP_W1]);

      dp_ca_ar0_r  <= dp_ca_ar0_nxt;

      dp_ca_ar1_r  <= dp_ca_ar1_nxt;

      dp_ca_ar2_r  <= dp_ca_ar2_nxt;

      dp_ca_ar3_r  <= dp_ca_ar3_nxt;

      dp_ca_ar4_r  <= dp_ca_ar4_nxt;

      dp_ca_ar5_r  <= dp_ca_ar5_nxt;

      dp_ca_ar6_r  <= dp_ca_ar6_nxt;

      dp_ca_ar7_r  <= dp_ca_ar7_nxt;

      ca_waw_haz_r      <= ca_waw_haz_nxt;
      end
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sequential process to implement the graduation buffer registers          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : next_tags_PROC

  //==========================================================================
  // Set the next value for the register address of each graduation buffer
  // entry from the selected graduating register. If allocating the entry
  // then set its next vallue to be ca_grad_rf_wa, otherwise retain its
  // current value. This allows these registers to be clock-gated using a
  // single common gating signal for all components of the same entry.
  //
  ar0_rf_wa1_nxt      = ar_alloc_hot[0] ? ca_grad_rf_wa : ar0_rf_wa1_r;
  ar1_rf_wa1_nxt      = ar_alloc_hot[1] ? ca_grad_rf_wa : ar1_rf_wa1_r;
  ar2_rf_wa1_nxt      = ar_alloc_hot[2] ? ca_grad_rf_wa : ar2_rf_wa1_r;
  ar3_rf_wa1_nxt      = ar_alloc_hot[3] ? ca_grad_rf_wa : ar3_rf_wa1_r;
  ar4_rf_wa1_nxt      = ar_alloc_hot[4] ? ca_grad_rf_wa : ar4_rf_wa1_r;
  ar5_rf_wa1_nxt      = ar_alloc_hot[5] ? ca_grad_rf_wa : ar5_rf_wa1_r;
  ar6_rf_wa1_nxt      = ar_alloc_hot[6] ? ca_grad_rf_wa : ar6_rf_wa1_r;
  ar7_rf_wa1_nxt      = ar_alloc_hot[7] ? ca_grad_rf_wa : ar7_rf_wa1_r;

  //==========================================================================
  // Set each entry to be valid when allocated and retain its validity
  // until deallocated.
  //
  ar0_rf_valid_nxt    = ar_alloc_hot[0]
                      | (ar0_rf_valid_r & (~ar_dealloc_hot[0]))
                      ;

  ar1_rf_valid_nxt    = ar_alloc_hot[1]
                      | (ar1_rf_valid_r & (~ar_dealloc_hot[1]))
                      ;

  ar2_rf_valid_nxt    = ar_alloc_hot[2]
                      | (ar2_rf_valid_r & (~ar_dealloc_hot[2]))
                      ;

  ar3_rf_valid_nxt    = ar_alloc_hot[3]
                      | (ar3_rf_valid_r & (~ar_dealloc_hot[3]))
                      ;

  ar4_rf_valid_nxt    = ar_alloc_hot[4]
                      | (ar4_rf_valid_r & (~ar_dealloc_hot[4]))
                      ;

  ar5_rf_valid_nxt    = ar_alloc_hot[5]
                      | (ar5_rf_valid_r & (~ar_dealloc_hot[5]))
                      ;

  ar6_rf_valid_nxt    = ar_alloc_hot[6]
                      | (ar6_rf_valid_r & (~ar_dealloc_hot[6]))
                      ;

  ar7_rf_valid_nxt    = ar_alloc_hot[7]
                      | (ar7_rf_valid_r & (~ar_dealloc_hot[7]))
                      ;


  //==========================================================================
  // Indicate which graduation buffer entries hold a LOAD operation.
  //
   ar0_is_load_nxt = (ar_alloc_hot[0] & ca_load_r)
                   | (!ar_dealloc_hot[0] & ar0_is_load_r)
                   ;
   ar1_is_load_nxt = (ar_alloc_hot[1] & ca_load_r)
                   | (!ar_dealloc_hot[1] & ar1_is_load_r)
                   ;
   ar2_is_load_nxt = (ar_alloc_hot[2] & ca_load_r)
                   | (!ar_dealloc_hot[2] & ar2_is_load_r)
                   ;
   ar3_is_load_nxt = (ar_alloc_hot[3] & ca_load_r)
                   | (!ar_dealloc_hot[3] & ar3_is_load_r)
                   ;
   ar4_is_load_nxt = (ar_alloc_hot[4] & ca_load_r)
                   | (!ar_dealloc_hot[4] & ar4_is_load_r)
                   ;
   ar5_is_load_nxt = (ar_alloc_hot[5] & ca_load_r)
                   | (!ar_dealloc_hot[5] & ar5_is_load_r)
                   ;
   ar6_is_load_nxt = (ar_alloc_hot[6] & ca_load_r)
                   | (!ar_dealloc_hot[6] & ar6_is_load_r)
                   ;
   ar7_is_load_nxt = (ar_alloc_hot[7] & ca_load_r)
                   | (!ar_dealloc_hot[7] & ar7_is_load_r)
                   ;

  //==========================================================================
  // Set each graduation buffer entry's wenb1 bit when allocating a graduating
  // instruction from the CA stage that has the appropriate ca_rf_wenb0_r or
  // ca_rf_wenb1_r set to 1. The choice depends on whether graduating a LD
  // or some other operation. LD results are carried on port 1 whereas all
  // other results are carries on port 0.
  // Keep the wenb1 bit set unless deallocating the entry or squashing the
  // write enable due to a WAW hazard with a committing CA instruction.
  //
  ar_wenb_nxt         = ca_load_r
                      ? ca_rf_wenb1_r
                          : ca_rf_wenb0_r
                      ;

  ar0_rf_wenb1_nxt    = (ar_alloc_hot[0] & ar_wenb_nxt)
                      | (   ar0_rf_wenb1_r
                          & (~(   ar_dealloc_hot[0]
                               | (   commit_inst
                                   & (  (   ca_kill_ar0[`npuarc_K_W1_LO]
                                          & (   (ca_rf_wa1_r[0] == ar0_rf_wa1_r[0])
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                     )
                                 )
                             )
                        ))
                      ;

  ar1_rf_wenb1_nxt    = (ar_alloc_hot[1] & ar_wenb_nxt)
                      | (   ar1_rf_wenb1_r
                          & (~(   ar_dealloc_hot[1]
                               | (   commit_inst
                                   & (  (   ca_kill_ar1[`npuarc_K_W1_LO]
                                          & (   (ca_rf_wa1_r[0] == ar1_rf_wa1_r[0])
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                     )
                                 )
                             )
                        ))
                      ;

  ar2_rf_wenb1_nxt    = (ar_alloc_hot[2] & ar_wenb_nxt)
                      | (   ar2_rf_wenb1_r
                          & (~(   ar_dealloc_hot[2]
                               | (   commit_inst
                                   & (  (   ca_kill_ar2[`npuarc_K_W1_LO]
                                          & (   (ca_rf_wa1_r[0] == ar2_rf_wa1_r[0])
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                     )
                                 )
                             )
                        ))
                      ;

  ar3_rf_wenb1_nxt    = (ar_alloc_hot[3] & ar_wenb_nxt)
                      | (   ar3_rf_wenb1_r
                          & (~(   ar_dealloc_hot[3]
                               | (   commit_inst
                                   & (  (   ca_kill_ar3[`npuarc_K_W1_LO]
                                          & (   (ca_rf_wa1_r[0] == ar3_rf_wa1_r[0])
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                     )
                                 )
                             )
                        ))
                      ;

  ar4_rf_wenb1_nxt    = (ar_alloc_hot[4] & ar_wenb_nxt)
                      | (   ar4_rf_wenb1_r
                          & (~(   ar_dealloc_hot[4]
                               | (   commit_inst
                                   & (  (   ca_kill_ar4[`npuarc_K_W1_LO]
                                          & (   (ca_rf_wa1_r[0] == ar4_rf_wa1_r[0])
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                     )
                                 )
                             )
                        ))
                      ;

  ar5_rf_wenb1_nxt    = (ar_alloc_hot[5] & ar_wenb_nxt)
                      | (   ar5_rf_wenb1_r
                          & (~(   ar_dealloc_hot[5]
                               | (   commit_inst
                                   & (  (   ca_kill_ar5[`npuarc_K_W1_LO]
                                          & (   (ca_rf_wa1_r[0] == ar5_rf_wa1_r[0])
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                     )
                                 )
                             )
                        ))
                      ;

  ar6_rf_wenb1_nxt    = (ar_alloc_hot[6] & ar_wenb_nxt)
                      | (   ar6_rf_wenb1_r
                          & (~(   ar_dealloc_hot[6]
                               | (   commit_inst
                                   & (  (   ca_kill_ar6[`npuarc_K_W1_LO]
                                          & (   (ca_rf_wa1_r[0] == ar6_rf_wa1_r[0])
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                     )
                                 )
                             )
                        ))
                      ;

  ar7_rf_wenb1_nxt    = (ar_alloc_hot[7] & ar_wenb_nxt)
                      | (   ar7_rf_wenb1_r
                          & (~(   ar_dealloc_hot[7]
                               | (   commit_inst
                                   & (  (   ca_kill_ar7[`npuarc_K_W1_LO]
                                          & (   (ca_rf_wa1_r[0] == ar7_rf_wa1_r[0])
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                     )
                                 )
                             )
                        ))
                      ;


  //==========================================================================
  // Set each graduation buffer entry's wenb1_64 bit when allocating a
  // graduating instruction from CA that has ca_rf_wenb1_64_r set to 1.
  // Keep the wenb1_64 bit set unless deallocating the entry or squashing
  // the write enable due to a WAW hazard with a committing CA instruction
  // that will over-write the high register defined by the graduating
  // buffer entry.
  //
  ar0_rf_wenb1_64_nxt = (ar_alloc_hot[0] & ca_grad_rf_64)
                      | (   ar0_rf_wenb1_64_r
                          & (~(   ar_dealloc_hot[0]
                               | (   commit_inst
                                   & (  (   ca_kill_ar0[`npuarc_K_W1_HI]
                                          & (   ca_rf_wa1_r[0]
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                      | (   ca_kill_ar0[`npuarc_K_W1_LO]
                                          & ca_rf_wenb1_64_r
                                        )
                                     )
                                 )
                            ) )
                        )
                      ;

  ar1_rf_wenb1_64_nxt = (ar_alloc_hot[1] & ca_grad_rf_64)
                      | (   ar1_rf_wenb1_64_r
                          & (~(   ar_dealloc_hot[1]
                               | (   commit_inst
                                   & (  (   ca_kill_ar1[`npuarc_K_W1_HI]
                                          & (   ca_rf_wa1_r[0]
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                      | (   ca_kill_ar1[`npuarc_K_W1_LO]
                                          & ca_rf_wenb1_64_r
                                        )
                                     )
                                 )
                            ) )
                        )
                      ;

  ar2_rf_wenb1_64_nxt = (ar_alloc_hot[2] & ca_grad_rf_64)
                      | (   ar2_rf_wenb1_64_r
                          & (~(   ar_dealloc_hot[2]
                               | (   commit_inst
                                   & (  (   ca_kill_ar2[`npuarc_K_W1_HI]
                                          & (   ca_rf_wa1_r[0]
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                      | (   ca_kill_ar2[`npuarc_K_W1_LO]
                                          & ca_rf_wenb1_64_r
                                        )
                                     )
                                 )
                            ) )
                        )
                      ;

  ar3_rf_wenb1_64_nxt = (ar_alloc_hot[3] & ca_grad_rf_64)
                      | (   ar3_rf_wenb1_64_r
                          & (~(   ar_dealloc_hot[3]
                               | (   commit_inst
                                   & (  (   ca_kill_ar3[`npuarc_K_W1_HI]
                                          & (   ca_rf_wa1_r[0]
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                      | (   ca_kill_ar3[`npuarc_K_W1_LO]
                                          & ca_rf_wenb1_64_r
                                        )
                                     )
                                 )
                            ) )
                        )
                      ;

  ar4_rf_wenb1_64_nxt = (ar_alloc_hot[4] & ca_grad_rf_64)
                      | (   ar4_rf_wenb1_64_r
                          & (~(   ar_dealloc_hot[4]
                               | (   commit_inst
                                   & (  (   ca_kill_ar4[`npuarc_K_W1_HI]
                                          & (   ca_rf_wa1_r[0]
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                      | (   ca_kill_ar4[`npuarc_K_W1_LO]
                                          & ca_rf_wenb1_64_r
                                        )
                                     )
                                 )
                            ) )
                        )
                      ;

  ar5_rf_wenb1_64_nxt = (ar_alloc_hot[5] & ca_grad_rf_64)
                      | (   ar5_rf_wenb1_64_r
                          & (~(   ar_dealloc_hot[5]
                               | (   commit_inst
                                   & (  (   ca_kill_ar5[`npuarc_K_W1_HI]
                                          & (   ca_rf_wa1_r[0]
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                      | (   ca_kill_ar5[`npuarc_K_W1_LO]
                                          & ca_rf_wenb1_64_r
                                        )
                                     )
                                 )
                            ) )
                        )
                      ;

  ar6_rf_wenb1_64_nxt = (ar_alloc_hot[6] & ca_grad_rf_64)
                      | (   ar6_rf_wenb1_64_r
                          & (~(   ar_dealloc_hot[6]
                               | (   commit_inst
                                   & (  (   ca_kill_ar6[`npuarc_K_W1_HI]
                                          & (   ca_rf_wa1_r[0]
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                      | (   ca_kill_ar6[`npuarc_K_W1_LO]
                                          & ca_rf_wenb1_64_r
                                        )
                                     )
                                 )
                            ) )
                        )
                      ;

  ar7_rf_wenb1_64_nxt = (ar_alloc_hot[7] & ca_grad_rf_64)
                      | (   ar7_rf_wenb1_64_r
                          & (~(   ar_dealloc_hot[7]
                               | (   commit_inst
                                   & (  (   ca_kill_ar7[`npuarc_K_W1_HI]
                                          & (   ca_rf_wa1_r[0]
                                              | ca_rf_wenb1_64_r
                                            )
                                        )
                                      | (   ca_kill_ar7[`npuarc_K_W1_LO]
                                          & ca_rf_wenb1_64_r
                                        )
                                     )
                                 )
                            ) )
                        )
                      ;


  //==========================================================================
  // Set each graduation buffer entry's flag-write bit when allocating a
  // graduating instruction from CA that has ca_<flag>_wen_r set to 1, for
  // any flag in the set {Z, N, C, V}.
  // Keep the flag-write bit set unless deallocating the entry or squashing
  // the write enable due to a WAW hazard with a committing CA instruction.
  //
  ar0_flag_wen_nxt = (ar_alloc_hot[0] & (|ca_zncv_wen_r) & commit_inst)
                      | (   ar0_flag_wen_r
                          & (~(   ar_dealloc_hot[0]
                               | (ca_kill_ar0[`npuarc_K_W1_LO] & commit_inst)
                             ))
                        )
                      ;

  ar1_flag_wen_nxt = (ar_alloc_hot[1] & (|ca_zncv_wen_r) & commit_inst)
                      | (   ar1_flag_wen_r
                          & (~(   ar_dealloc_hot[1]
                               | (ca_kill_ar1[`npuarc_K_W1_LO] & commit_inst)
                             ))
                        )
                      ;

  ar2_flag_wen_nxt = (ar_alloc_hot[2] & (|ca_zncv_wen_r) & commit_inst)
                      | (   ar2_flag_wen_r
                          & (~(   ar_dealloc_hot[2]
                               | (ca_kill_ar2[`npuarc_K_W1_LO] & commit_inst)
                             ))
                        )
                      ;

  ar3_flag_wen_nxt = (ar_alloc_hot[3] & (|ca_zncv_wen_r) & commit_inst)
                      | (   ar3_flag_wen_r
                          & (~(   ar_dealloc_hot[3]
                               | (ca_kill_ar3[`npuarc_K_W1_LO] & commit_inst)
                             ))
                        )
                      ;

  ar4_flag_wen_nxt = (ar_alloc_hot[4] & (|ca_zncv_wen_r) & commit_inst)
                      | (   ar4_flag_wen_r
                          & (~(   ar_dealloc_hot[4]
                               | (ca_kill_ar4[`npuarc_K_W1_LO] & commit_inst)
                             ))
                        )
                      ;

  ar5_flag_wen_nxt = (ar_alloc_hot[5] & (|ca_zncv_wen_r) & commit_inst)
                      | (   ar5_flag_wen_r
                          & (~(   ar_dealloc_hot[5]
                               | (ca_kill_ar5[`npuarc_K_W1_LO] & commit_inst)
                             ))
                        )
                      ;

  ar6_flag_wen_nxt = (ar_alloc_hot[6] & (|ca_zncv_wen_r) & commit_inst)
                      | (   ar6_flag_wen_r
                          & (~(   ar_dealloc_hot[6]
                               | (ca_kill_ar6[`npuarc_K_W1_LO] & commit_inst)
                             ))
                        )
                      ;

  ar7_flag_wen_nxt = (ar_alloc_hot[7] & (|ca_zncv_wen_r) & commit_inst)
                      | (   ar7_flag_wen_r
                          & (~(   ar_dealloc_hot[7]
                               | (ca_kill_ar7[`npuarc_K_W1_LO] & commit_inst)
                             ))
                        )
                      ;

  ar_zncv_wen_nxt     = ca_zncv_wen_r;

  //==========================================================================
  // Determine if the graduation buffer will contain a pending flag update
  // during the next cycle.
  //
  ar_zncv_upt_nxt     = ar0_flag_wen_nxt
                      | ar1_flag_wen_nxt
                      | ar2_flag_wen_nxt
                      | ar3_flag_wen_nxt
                      | ar4_flag_wen_nxt
                      | ar5_flag_wen_nxt
                      | ar6_flag_wen_nxt
                      | ar7_flag_wen_nxt
                      ;


  //==========================================================================
  // If there is a WAW dependency on the flags, between the X3 instruction
  // and any instruction in a graduation buffer, or with a graduating CA
  // instruction, then the X3 instruction must stall.
  // The x3_rtie_op_r is a special case. It's not itself but
  // its epilogue sequence who needs to update the status
  //
  x3_flag_haz         = (   ar_zncv_upt_r
                          | ((|ca_zncv_wen_r) & ca_grad_req)
                        )
                      & (((|x3_zncv_wen_r) | x3_rtie_op_r) & x3_valid_r)
                      ;

  //==========================================================================
  // If there is a RAW dependency on the flags, between the CA instruction
  // and any instruction in a graduation buffer then the CA instruction
  // must stall.
  //
  ca_flag_haz         = ar_zncv_upt_r
                      & (ca_uses_flags & ca_valid_r & (~ca_done_r))
                      ;

  //==========================================================================
  // Set each graduation buffer entry's accumulator write flags when
  // allocating a graduating instruction from CA that has ca_writes_acc_r
  // and/or ca_acc_wenb_r set to 1. Keep these bits set unless deallocating
  // the entry or squashing it due to a WAW hazard with a committing CA insn.
  //
  ar0_writes_acc_nxt = (ar_alloc_hot[0] & ca_writes_acc_r)
                        | (   ar0_writes_acc_r
                            & (~(   ar_dealloc_hot[0]
                                 | (ca_acc_waw & commit_inst)
                               ))
                          )
                        ;

  ar1_writes_acc_nxt = (ar_alloc_hot[1] & ca_writes_acc_r)
                        | (   ar1_writes_acc_r
                            & (~(   ar_dealloc_hot[1]
                                 | (ca_acc_waw & commit_inst)
                               ))
                          )
                        ;

  ar2_writes_acc_nxt = (ar_alloc_hot[2] & ca_writes_acc_r)
                        | (   ar2_writes_acc_r
                            & (~(   ar_dealloc_hot[2]
                                 | (ca_acc_waw & commit_inst)
                               ))
                          )
                        ;

  ar3_writes_acc_nxt = (ar_alloc_hot[3] & ca_writes_acc_r)
                        | (   ar3_writes_acc_r
                            & (~(   ar_dealloc_hot[3]
                                 | (ca_acc_waw & commit_inst)
                               ))
                          )
                        ;

  ar4_writes_acc_nxt = (ar_alloc_hot[4] & ca_writes_acc_r)
                        | (   ar4_writes_acc_r
                            & (~(   ar_dealloc_hot[4]
                                 | (ca_acc_waw & commit_inst)
                               ))
                          )
                        ;

  ar5_writes_acc_nxt = (ar_alloc_hot[5] & ca_writes_acc_r)
                        | (   ar5_writes_acc_r
                            & (~(   ar_dealloc_hot[5]
                                 | (ca_acc_waw & commit_inst)
                               ))
                          )
                        ;

  ar6_writes_acc_nxt = (ar_alloc_hot[6] & ca_writes_acc_r)
                        | (   ar6_writes_acc_r
                            & (~(   ar_dealloc_hot[6]
                                 | (ca_acc_waw & commit_inst)
                               ))
                          )
                        ;

  ar7_writes_acc_nxt = (ar_alloc_hot[7] & ca_writes_acc_r)
                        | (   ar7_writes_acc_r
                            & (~(   ar_dealloc_hot[7]
                                 | (ca_acc_waw & commit_inst)
                               ))
                          )
                        ;

  //==========================================================================
  // Set each graduation buffer entry's exclusive operation flag when
  // allocating a graduating an LLOCK or SCOND instruction from CA.
  // This is indicated by the ca_locked_r signal at the time of graduation.
  // Keep these bits set until the entry is deallocated.
  //
  ar0_exclusive_nxt  = (ar_alloc_hot[0] & ca_locked_r)
                        | (ar0_exclusive_r & (~(ar_dealloc_hot[0])))
                        ;

  ar1_exclusive_nxt  = (ar_alloc_hot[1] & ca_locked_r)
                        | (ar1_exclusive_r & (~(ar_dealloc_hot[1])))
                        ;

  ar2_exclusive_nxt  = (ar_alloc_hot[2] & ca_locked_r)
                        | (ar2_exclusive_r & (~(ar_dealloc_hot[2])))
                        ;

  ar3_exclusive_nxt  = (ar_alloc_hot[3] & ca_locked_r)
                        | (ar3_exclusive_r & (~(ar_dealloc_hot[3])))
                        ;

  ar4_exclusive_nxt  = (ar_alloc_hot[4] & ca_locked_r)
                        | (ar4_exclusive_r & (~(ar_dealloc_hot[4])))
                        ;

  ar5_exclusive_nxt  = (ar_alloc_hot[5] & ca_locked_r)
                        | (ar5_exclusive_r & (~(ar_dealloc_hot[5])))
                        ;

  ar6_exclusive_nxt  = (ar_alloc_hot[6] & ca_locked_r)
                        | (ar6_exclusive_r & (~(ar_dealloc_hot[6])))
                        ;

  ar7_exclusive_nxt  = (ar_alloc_hot[7] & ca_locked_r)
                        | (ar7_exclusive_r & (~(ar_dealloc_hot[7])))
                        ;

end

//////////////////////////////////////////////////////////////////////////////
//
// Synchronous processes
//
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : tag_regs_PROC
  if (rst_a == 1'b1)
    begin
      ar_tags_full_r       <= 1'b0;
      ar_tags_empty_r      <= 1'b1;
      ar_tags_empty_dly_r  <= 1'b1;
      ar_zncv_upt_r        <= 1'b0;
      ar_zncv_wen_r        <= 4'd0;

      ar0_rf_valid_r    <= 1'b0;
      ar0_is_load_r     <= 1'b0;
      ar0_rf_wenb1_r    <= 1'b0;
      ar0_rf_wa1_r      <= `npuarc_GRAD_ADDR_BITS'd0;
      ar0_rf_wenb1_64_r <= 1'b0;
      ar0_flag_wen_r    <= 1'b0;
      ar0_writes_acc_r  <= 1'b0;
      ar0_exclusive_r   <= 1'b0;
      ar0_dest_cr_is_ext <= 1'b0;

      ar1_rf_valid_r    <= 1'b0;
      ar1_is_load_r     <= 1'b0;
      ar1_rf_wenb1_r    <= 1'b0;
      ar1_rf_wa1_r      <= `npuarc_GRAD_ADDR_BITS'd0;
      ar1_rf_wenb1_64_r <= 1'b0;
      ar1_flag_wen_r    <= 1'b0;
      ar1_writes_acc_r  <= 1'b0;
      ar1_exclusive_r   <= 1'b0;
      ar1_dest_cr_is_ext <= 1'b0;

      ar2_rf_valid_r    <= 1'b0;
      ar2_is_load_r     <= 1'b0;
      ar2_rf_wenb1_r    <= 1'b0;
      ar2_rf_wa1_r      <= `npuarc_GRAD_ADDR_BITS'd0;
      ar2_rf_wenb1_64_r <= 1'b0;
      ar2_flag_wen_r    <= 1'b0;
      ar2_writes_acc_r  <= 1'b0;
      ar2_exclusive_r   <= 1'b0;
      ar2_dest_cr_is_ext <= 1'b0;

      ar3_rf_valid_r    <= 1'b0;
      ar3_is_load_r     <= 1'b0;
      ar3_rf_wenb1_r    <= 1'b0;
      ar3_rf_wa1_r      <= `npuarc_GRAD_ADDR_BITS'd0;
      ar3_rf_wenb1_64_r <= 1'b0;
      ar3_flag_wen_r    <= 1'b0;
      ar3_writes_acc_r  <= 1'b0;
      ar3_exclusive_r   <= 1'b0;
      ar3_dest_cr_is_ext <= 1'b0;

      ar4_rf_valid_r    <= 1'b0;
      ar4_is_load_r     <= 1'b0;
      ar4_rf_wenb1_r    <= 1'b0;
      ar4_rf_wa1_r      <= `npuarc_GRAD_ADDR_BITS'd0;
      ar4_rf_wenb1_64_r <= 1'b0;
      ar4_flag_wen_r    <= 1'b0;
      ar4_writes_acc_r  <= 1'b0;
      ar4_exclusive_r   <= 1'b0;
      ar4_dest_cr_is_ext <= 1'b0;

      ar5_rf_valid_r    <= 1'b0;
      ar5_is_load_r     <= 1'b0;
      ar5_rf_wenb1_r    <= 1'b0;
      ar5_rf_wa1_r      <= `npuarc_GRAD_ADDR_BITS'd0;
      ar5_rf_wenb1_64_r <= 1'b0;
      ar5_flag_wen_r    <= 1'b0;
      ar5_writes_acc_r  <= 1'b0;
      ar5_exclusive_r   <= 1'b0;
      ar5_dest_cr_is_ext <= 1'b0;

      ar6_rf_valid_r    <= 1'b0;
      ar6_is_load_r     <= 1'b0;
      ar6_rf_wenb1_r    <= 1'b0;
      ar6_rf_wa1_r      <= `npuarc_GRAD_ADDR_BITS'd0;
      ar6_rf_wenb1_64_r <= 1'b0;
      ar6_flag_wen_r    <= 1'b0;
      ar6_writes_acc_r  <= 1'b0;
      ar6_exclusive_r   <= 1'b0;
      ar6_dest_cr_is_ext <= 1'b0;

      ar7_rf_valid_r    <= 1'b0;
      ar7_is_load_r     <= 1'b0;
      ar7_rf_wenb1_r    <= 1'b0;
      ar7_rf_wa1_r      <= `npuarc_GRAD_ADDR_BITS'd0;
      ar7_rf_wenb1_64_r <= 1'b0;
      ar7_flag_wen_r    <= 1'b0;
      ar7_writes_acc_r  <= 1'b0;
      ar7_exclusive_r   <= 1'b0;
      ar7_dest_cr_is_ext <= 1'b0;

      ar0_ld_addr_r     <= {`npuarc_ADDR_SIZE{1'b0}};
      ar1_ld_addr_r     <= {`npuarc_ADDR_SIZE{1'b0}};
      ar2_ld_addr_r     <= {`npuarc_ADDR_SIZE{1'b0}};
      ar3_ld_addr_r     <= {`npuarc_ADDR_SIZE{1'b0}};
      ar4_ld_addr_r     <= {`npuarc_ADDR_SIZE{1'b0}};
      ar5_ld_addr_r     <= {`npuarc_ADDR_SIZE{1'b0}};
      ar6_ld_addr_r     <= {`npuarc_ADDR_SIZE{1'b0}};
      ar7_ld_addr_r     <= {`npuarc_ADDR_SIZE{1'b0}};
    end
  else
    begin
      if (ar_full_en == 1'b1)
      begin
        ar_tags_full_r  <=  ar_tags_full_nxt;
        ar_tags_empty_r <=  ar_tags_empty_nxt;
        ar_zncv_upt_r   <=  ar_zncv_upt_nxt;
        if ((ca_to_ar == 1'b1) && ((|ca_zncv_wen_r) == 1'b1))
          ar_zncv_wen_r <=  ar_zncv_wen_nxt;
      end
      ar_tags_empty_dly_r  <=  ar_tags_empty_r & (!ca_load_r);

      if (ar_tag_en[0] == 1'b1)
        begin
        ar0_rf_valid_r  <= ar0_rf_valid_nxt;
        ar0_is_load_r   <= ar0_is_load_nxt;
        ar0_rf_wa1_r    <= ar0_rf_wa1_nxt;
        ar0_rf_wenb1_r  <= ar0_rf_wenb1_nxt;
        ar0_rf_wenb1_64_r  <= ar0_rf_wenb1_64_nxt;
        ar0_flag_wen_r     <= ar0_flag_wen_nxt;
        ar0_dest_cr_is_ext <= ca_dest_cr_is_ext_r;
        ar0_writes_acc_r   <= ar0_writes_acc_nxt;
        ar0_exclusive_r    <= ar0_exclusive_nxt;
        if (ar_alloc_hot[0] == 1'b1)
          ar0_ld_addr_r    <= ca_mem_addr_r;
        end

      if (ar_tag_en[1] == 1'b1)
        begin
        ar1_rf_valid_r  <= ar1_rf_valid_nxt;
        ar1_is_load_r   <= ar1_is_load_nxt;
        ar1_rf_wa1_r    <= ar1_rf_wa1_nxt;
        ar1_rf_wenb1_r  <= ar1_rf_wenb1_nxt;
        ar1_rf_wenb1_64_r  <= ar1_rf_wenb1_64_nxt;
        ar1_flag_wen_r     <= ar1_flag_wen_nxt;
        ar1_dest_cr_is_ext <= ca_dest_cr_is_ext_r;
        ar1_writes_acc_r   <= ar1_writes_acc_nxt;
        ar1_exclusive_r    <= ar1_exclusive_nxt;
        if (ar_alloc_hot[1] == 1'b1)
          ar1_ld_addr_r    <= ca_mem_addr_r;
        end

      if (ar_tag_en[2] == 1'b1)
        begin
        ar2_rf_valid_r  <= ar2_rf_valid_nxt;
        ar2_is_load_r   <= ar2_is_load_nxt;
        ar2_rf_wa1_r    <= ar2_rf_wa1_nxt;
        ar2_rf_wenb1_r  <= ar2_rf_wenb1_nxt;
        ar2_rf_wenb1_64_r  <= ar2_rf_wenb1_64_nxt;
        ar2_flag_wen_r     <= ar2_flag_wen_nxt;
        ar2_dest_cr_is_ext <= ca_dest_cr_is_ext_r;
        ar2_writes_acc_r   <= ar2_writes_acc_nxt;
        ar2_exclusive_r    <= ar2_exclusive_nxt;
        if (ar_alloc_hot[2] == 1'b1)
          ar2_ld_addr_r    <= ca_mem_addr_r;
        end

      if (ar_tag_en[3] == 1'b1)
        begin
        ar3_rf_valid_r  <= ar3_rf_valid_nxt;
        ar3_is_load_r   <= ar3_is_load_nxt;
        ar3_rf_wa1_r    <= ar3_rf_wa1_nxt;
        ar3_rf_wenb1_r  <= ar3_rf_wenb1_nxt;
        ar3_rf_wenb1_64_r  <= ar3_rf_wenb1_64_nxt;
        ar3_flag_wen_r     <= ar3_flag_wen_nxt;
        ar3_dest_cr_is_ext <= ca_dest_cr_is_ext_r;
        ar3_writes_acc_r   <= ar3_writes_acc_nxt;
        ar3_exclusive_r    <= ar3_exclusive_nxt;
        if (ar_alloc_hot[3] == 1'b1)
          ar3_ld_addr_r    <= ca_mem_addr_r;
        end

      if (ar_tag_en[4] == 1'b1)
        begin
        ar4_rf_valid_r  <= ar4_rf_valid_nxt;
        ar4_is_load_r   <= ar4_is_load_nxt;
        ar4_rf_wa1_r    <= ar4_rf_wa1_nxt;
        ar4_rf_wenb1_r  <= ar4_rf_wenb1_nxt;
        ar4_rf_wenb1_64_r  <= ar4_rf_wenb1_64_nxt;
        ar4_flag_wen_r     <= ar4_flag_wen_nxt;
        ar4_dest_cr_is_ext <= ca_dest_cr_is_ext_r;
        ar4_writes_acc_r   <= ar4_writes_acc_nxt;
        ar4_exclusive_r    <= ar4_exclusive_nxt;
        if (ar_alloc_hot[4] == 1'b1)
          ar4_ld_addr_r    <= ca_mem_addr_r;
        end

      if (ar_tag_en[5] == 1'b1)
        begin
        ar5_rf_valid_r  <= ar5_rf_valid_nxt;
        ar5_is_load_r   <= ar5_is_load_nxt;
        ar5_rf_wa1_r    <= ar5_rf_wa1_nxt;
        ar5_rf_wenb1_r  <= ar5_rf_wenb1_nxt;
        ar5_rf_wenb1_64_r  <= ar5_rf_wenb1_64_nxt;
        ar5_flag_wen_r     <= ar5_flag_wen_nxt;
        ar5_dest_cr_is_ext <= ca_dest_cr_is_ext_r;
        ar5_writes_acc_r   <= ar5_writes_acc_nxt;
        ar5_exclusive_r    <= ar5_exclusive_nxt;
        if (ar_alloc_hot[5] == 1'b1)
          ar5_ld_addr_r    <= ca_mem_addr_r;
        end

      if (ar_tag_en[6] == 1'b1)
        begin
        ar6_rf_valid_r  <= ar6_rf_valid_nxt;
        ar6_is_load_r   <= ar6_is_load_nxt;
        ar6_rf_wa1_r    <= ar6_rf_wa1_nxt;
        ar6_rf_wenb1_r  <= ar6_rf_wenb1_nxt;
        ar6_rf_wenb1_64_r  <= ar6_rf_wenb1_64_nxt;
        ar6_flag_wen_r     <= ar6_flag_wen_nxt;
        ar6_dest_cr_is_ext <= ca_dest_cr_is_ext_r;
        ar6_writes_acc_r   <= ar6_writes_acc_nxt;
        ar6_exclusive_r    <= ar6_exclusive_nxt;
        if (ar_alloc_hot[6] == 1'b1)
          ar6_ld_addr_r    <= ca_mem_addr_r;
        end

      if (ar_tag_en[7] == 1'b1)
        begin
        ar7_rf_valid_r  <= ar7_rf_valid_nxt;
        ar7_is_load_r   <= ar7_is_load_nxt;
        ar7_rf_wa1_r    <= ar7_rf_wa1_nxt;
        ar7_rf_wenb1_r  <= ar7_rf_wenb1_nxt;
        ar7_rf_wenb1_64_r  <= ar7_rf_wenb1_64_nxt;
        ar7_flag_wen_r     <= ar7_flag_wen_nxt;
        ar7_dest_cr_is_ext <= ca_dest_cr_is_ext_r;
        ar7_writes_acc_r   <= ar7_writes_acc_nxt;
        ar7_exclusive_r    <= ar7_exclusive_nxt;
        if (ar_alloc_hot[7] == 1'b1)
          ar7_ld_addr_r    <= ca_mem_addr_r;
        end

    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sequential process to implement the pipeline of status bits to track     //
// whether operands have been read at each stage, and whether there is a    //
// defined result at each position where a result may exist, and whether    //
// the arithmetic flags (ZNCV) are redefined or pending a new definition    //
// at each stage from X2 onwards.                                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : dp_pipe_PROC
  if (rst_a == 1'b1)
    begin
    sa_valid_r      <= 1'b0;
    sa_read_r0_r    <= 1'b0;
    sa_read_r1_r    <= 1'b0;
    //
    x1_valid_r      <= 1'b0;
    x1_read_r0_r    <= 1'b0;
    x1_read_r1_r    <= 1'b0;
    x1_read_r2_r    <= 1'b0;
    x1_read_r3_r    <= 1'b0;
    //
    x2_valid_r      <= 1'b0;
    x2_read_r0_r    <= 1'b0;
    x2_read_r1_r    <= 1'b0;
    x2_done_r       <= 1'b0;
    x2_zncv_valid_r <= 4'hF;
    x2_zncv_refil_r <= 1'b0;
    //
    x3_valid_r      <= 1'b0;
    x3_read_r0_r    <= 1'b0;
    x3_read_r1_r    <= 1'b0;
    x3_done_r       <= 1'b0;
    //
    ca_valid_r      <= 1'b0;
    ca_done_r       <= 1'b0;
    //
    wa_valid_r      <= 1'b0;
    end
  else
    begin

    if (sa_enable == 1'b1)
      begin
      sa_valid_r      <= sa_valid_nxt;
      sa_read_r0_r    <= sa_read_r0_nxt;
      sa_read_r1_r    <= sa_read_r1_nxt;
      end

    x1_read_r0_r      <= x1_read_r0_nxt;
    x1_read_r1_r      <= x1_read_r1_nxt;
    x1_read_r2_r      <= x1_read_r2_nxt;
    x1_read_r3_r      <= x1_read_r3_nxt;

    if (x1_enable == 1'b1)
      begin
      x1_valid_r      <= x1_valid_nxt;
      end

    x2_zncv_valid_r   <= x2_zncv_valid_nxt;
// spyglass disable_block STARC-2.3.4.3
// SMD: Flip-flop has neither asynchronous set nor asynchronous reset
// SJ:  Flop state is not required immediately after reset
    x2_zncv_refil_r   <= x2_zncv_refil_nxt;
// spyglass enable_block  STARC-2.3.4.3

    if (x2_enable == 1'b1)
      begin
      x2_valid_r      <= x2_valid_nxt;
      x2_read_r0_r    <= x2_read_r0_nxt;
      x2_read_r1_r    <= x2_read_r1_nxt;
      x2_done_r       <= x2_done_nxt;
      end

    if (x3_enable == 1'b1)
      begin
      x3_valid_r      <= x3_valid_nxt;
      x3_read_r0_r    <= x3_read_r0_nxt;
      x3_read_r1_r    <= x3_read_r1_nxt;
      x3_done_r       <= x2_has_w0;
      end

    if (ca_enable == 1'b1)
      begin
      ca_valid_r      <= ca_valid_nxt;
      ca_done_r       <= x3_has_w0;
      end
// spyglass disable_block FlopEConst
// SMD: Enable pin is always high/low
// SJ:  Done on purpose
    if (wa_enable == 1'b1)
      begin
      wa_valid_r      <= wa_valid_nxt;
      end
// spyglass enable_block FlopEConst
    end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sequential process to implement a 1-cycle delayed version of wa_restart  //
// This is used to enable all depedency state variables in the cycle after  //
// a pipeline flush. This avoids any requirement to clear dependency bits   //
// in the cycle in which the flush occurs, which would complicate the next  //
// state logic. However, in the cycle after a flush, all valid bits and all //
// valid_nxt signals are clear, so the normal power-saving enables will be  //
// turned off.                                                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: clr_dep_reg_PROC

  if (rst_a == 1'b1)
    clear_deps_r <= 1'b0;
  else
    clear_deps_r <= wa_restart;

end


always @(posedge clk or posedge rst_a)
begin: deferred_flag_update_regs_PROC
  if (rst_a == 1'b1)
    pending_flag_upt_r   <= 1'b0;
  else if (pending_flag_upt_cg0 == 1'b1)
    pending_flag_upt_r   <= pending_flag_upt_nxt;
end // block: deferred_flag_update_regs_PROC

always @(posedge clk or posedge rst_a)
begin: wa0_64_regs_PROC

  if (rst_a == 1'b1)
    wa_dp_wenb0_64_r  <= 1'b0;
  else if (ca_adv == 1'b1)
    wa_dp_wenb0_64_r  <= wa_rf_wenb0_64_nxt
                      | (ca_rf_wenb0_64_r & (|ca_q_field_r) & ca_rf_renb0_64_r)
                      ;

end // block: wa0_64_regs_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to implement x1_r0_dmp_fast_nxt state              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg x1_r0_dmp_fast_nxt;

always @*
begin : x1_fast_nxt_PROC

  //==========================================================================
  // The x1_r0_dmp_fast_r state bit indicates when a fast bypass from DC4 to
  // X1 should take place. The next value for this control signal is set in
  // the previous cycle, according to the value of x1_r0_dmp_fast_nxt.
  // This depends on the presence of dependencies between instructions at the
  // SA and X1 stages, and LD instructions at X3 and CA. It also depends on
  // whether a potentially fast bypass will be possible from the DC3 load
  // when it reaches DC4, and on whether the SA, X1, X3 and CA instructions
  // involved in fast bypass dependencies advance to the next stage or else
  // remain in their current stage. There are four cases where a fast bypass
  // may be indicated in the following cycle:
  //
  // a. SA and X3 instructions have an LR0_LW1 dependency and both advance
  // b. X1 and X3 instructions have an LR0_LW1 dependency and X1 is retained
  //    and X3 advances.
  // c. X1 and CA instructions have an LR0_LW1 dependency and both are retained
  // d. SA and CA instructions have an LR0_LW1 dependency and SA advances
  //    but CA is retained.
  //
  // In each case, the availability of a fast bypass is indicated by either
  // the dmp_dc3_fast_byp signal (if X3 advances), or by dmp_dc4_fast_byp_r
  // (if SA advances and CA is retained), or by x1_r0_dmp_fast_r (if both X1
  // and CA instructions are retained).
  //
  x1_r0_dmp_fast_nxt  =
       (dmp_dc3_fast_byp   & rd_sa_x3[`npuarc_LR0_LW1]   & sa_adv    & x3_adv   ) // a
     | (dmp_dc3_fast_byp   & dp_x1_x3_r[`npuarc_LR0_LW1] & x1_retain & x3_adv   ) // b
     | (x1_r0_dmp_fast_r   & dp_x1_ca_r[`npuarc_LR0_LW1] & x1_retain & ca_retain) // c
     | (dmp_dc4_fast_byp_r & rd_sa_ca[`npuarc_LR0_LW1]   & sa_adv    & ca_retain) // d
     ;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Sequential process to implement x1_r0_dmp_fast_r flip-flop               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x1_fast_reg_PROC

  if (rst_a == 1'b1)
    x1_r0_dmp_fast_r  <= 1'b0;
  else
    x1_r0_dmp_fast_r  <= x1_r0_dmp_fast_nxt;

end

reg    dp_x2_sp_cg;
reg    dp_x2_sp_nxt;

always @*
begin: dp_x2_sp_PROC

  dp_x2_sp_cg  = dp_x2_sp_r
               | (x3_valid_r & x3_rf_wenb1_r)
               | (ca_valid_r & ca_rf_wenb1_r)
               | (wa_valid_r & wa_rf_wenb1_r)
               | (ar0_rf_valid_r & ar0_rf_wenb1_r)
               | (ar1_rf_valid_r & ar1_rf_wenb1_r)
               | (ar2_rf_valid_r & ar2_rf_wenb1_r)
               | (ar3_rf_valid_r & ar3_rf_wenb1_r)
               | (ar4_rf_valid_r & ar4_rf_wenb1_r)
               | (ar5_rf_valid_r & ar5_rf_wenb1_r)
               | (ar6_rf_valid_r & ar6_rf_wenb1_r)
               | (ar7_rf_valid_r & ar7_rf_wenb1_r)
               ;

  dp_x2_sp_nxt = 1'b0
               | (  (x3_rf_wa1_r == `npuarc_SP_REG)
                 & x3_rf_wenb1_r
                 & x3_valid_r)
               | (  (ca_rf_wa1_r == `npuarc_SP_REG)
                  & ca_rf_wenb1_r
                  & ca_valid_r)
               | (  (wa_rf_wa1_r == `npuarc_SP_REG)
                  & wa_rf_wenb1_r
                  & wa_valid_r)
               | (  (ar0_rf_wa1_r [`npuarc_RGF_ADDR_RANGE] == `npuarc_SP_REG)
                  & ar0_rf_wenb1_r
                  & ar0_rf_valid_r)
               | (  (ar1_rf_wa1_r [`npuarc_RGF_ADDR_RANGE] == `npuarc_SP_REG)
                  & ar1_rf_wenb1_r
                  & ar1_rf_valid_r)
               | (  (ar2_rf_wa1_r [`npuarc_RGF_ADDR_RANGE] == `npuarc_SP_REG)
                  & ar2_rf_wenb1_r
                  & ar2_rf_valid_r)
               | (  (ar3_rf_wa1_r [`npuarc_RGF_ADDR_RANGE] == `npuarc_SP_REG)
                  & ar3_rf_wenb1_r
                  & ar3_rf_valid_r)
               | (  (ar4_rf_wa1_r [`npuarc_RGF_ADDR_RANGE] == `npuarc_SP_REG)
                  & ar4_rf_wenb1_r
                  & ar4_rf_valid_r)
               | (  (ar5_rf_wa1_r [`npuarc_RGF_ADDR_RANGE] == `npuarc_SP_REG)
                  & ar5_rf_wenb1_r
                  & ar5_rf_valid_r)
               | (  (ar6_rf_wa1_r [`npuarc_RGF_ADDR_RANGE] == `npuarc_SP_REG)
                  & ar6_rf_wenb1_r
                  & ar6_rf_valid_r)
               | (  (ar7_rf_wa1_r [`npuarc_RGF_ADDR_RANGE] == `npuarc_SP_REG)
                  & ar7_rf_wenb1_r
                  & ar7_rf_valid_r)
               ;

end // block: dp_x2_sp_PROC

always @(posedge clk or posedge rst_a)
begin: dp_x2_sp_reg_PROC

  if (rst_a == 1'b1)
    dp_x2_sp_r <= 1'b0;
  else if (dp_x2_sp_cg == 1'b1)
    dp_x2_sp_r <= dp_x2_sp_nxt;

end // block: dp_x2_sp_reg_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign ca_grad_ack          = grad_ack;
assign ca_grad_tag          = grad_tag;
assign dp_retire_rf_64      = retire_rf_64;
assign dp_retire_rf_wenb    = retire_rf_wenb;
assign dp_retire_rf_wa      = retire_rf_wa;
assign dp_retire_zncv       = {4{retire_flag_wen}} & ar_zncv_wen_r;
assign dp_retire_writes_acc = retire_writes_acc;
assign dp_retire_ld_addr    = retire_ld_addr;
assign dp_retire_is_load    = retire_is_load;
assign dp_retire_scond      = ca_retire_ack & retire_exclusive & retire_flag_wen;

////////// Operands-stage bypass gating signals //////////////////////////////
//
assign fwd_x1_sa0_lo        = fd_sa_x1[`npuarc_LR0_LW0];
assign fwd_x2_sa0_lo        = fd_sa_x2[`npuarc_LR0_LW0];
assign fwd_x3_sa0_lo        = fd_sa_x3[`npuarc_LR0_LW0];
assign fwd_ca0_lo_sa0_lo    = fd_sa_ca[`npuarc_LR0_LW0];
assign fwd_ca1_lo_sa0_lo    = fd_sa_ca[`npuarc_LR0_LW1] & sa_read_r0_r;
assign fwd_wa0_lo_sa0_lo    = fd_sa_wa[`npuarc_LR0_LW0];
assign fwd_wa1_lo_sa0_lo    = fd_sa_wa[`npuarc_LR0_LW1];
assign fwd_ca0_hi_sa0_lo    = fd_sa_ca[`npuarc_LR0_HW0];
assign fwd_wa0_hi_sa0_lo    = fd_sa_wa[`npuarc_LR0_HW0];
assign fwd_ca1_hi_sa0_lo    = fd_sa_ca[`npuarc_LR0_HW1] & sa_read_r0_r;
assign fwd_ca1_hi_sa1_lo    = fd_sa_ca[`npuarc_LR1_HW1] & sa_read_r1_r;
assign fwd_wa1_hi_sa0_lo    = fd_sa_wa[`npuarc_LR0_HW1];
assign fwd_wa1_hi_sa1_lo    = fd_sa_wa[`npuarc_LR1_HW1];
assign fwd_wa0_hi_sa0_hi    = fd_sa_wa[`npuarc_HR0_HW0];
assign fwd_wa1_hi_sa0_hi    = fd_sa_wa[`npuarc_HR0_HW1];
assign fwd_x1_sa1_lo        = fd_sa_x1[`npuarc_LR1_LW0];
assign fwd_x2_sa1_lo        = fd_sa_x2[`npuarc_LR1_LW0];
assign fwd_x3_sa1_lo        = fd_sa_x3[`npuarc_LR1_LW0];
assign fwd_ca0_lo_sa1_lo    = fd_sa_ca[`npuarc_LR1_LW0];
assign fwd_ca1_lo_sa1_lo    = fd_sa_ca[`npuarc_LR1_LW1] & sa_read_r1_r;
assign fwd_wa0_lo_sa1_lo    = fd_sa_wa[`npuarc_LR1_LW0];
assign fwd_wa1_lo_sa1_lo    = fd_sa_wa[`npuarc_LR1_LW1];
assign fwd_ca0_hi_sa1_lo    = fd_sa_ca[`npuarc_LR1_HW0];
assign fwd_wa0_hi_sa1_lo    = fd_sa_wa[`npuarc_LR1_HW0];
assign fwd_wa0_lo_sa0_hi    = fd_sa_wa[`npuarc_HR0_LW0];
assign fwd_wa1_lo_sa0_hi    = fd_sa_wa[`npuarc_HR0_LW1];
assign fwd_wa0_hi_sa1_hi    = fd_sa_wa[`npuarc_HR1_HW0];
assign fwd_wa0_lo_sa1_hi    = fd_sa_wa[`npuarc_HR1_LW0];
assign fwd_wa1_lo_sa1_hi    = fd_sa_wa[`npuarc_HR1_LW1];
assign fwd_wa1_hi_sa1_hi    = fd_sa_wa[`npuarc_HR1_HW1];

////////// Exec1-stage bypass gating signals /////////////////////////////////
//
assign fwd_x1_r0_dmp_fast   = x1_r0_dmp_fast_r;     // fast DC4 load-AGU path
assign fwd_x1_r1_dmp_fast   = 1'b0;                 // no fast path to AGU r1
//
assign fwd_x1_r0_wa_w0_lo   = fd_x1_wa[`npuarc_LR0_LW0];   // W/back w0 bypass (lo)
assign fwd_x1_r1_wa_w0_lo   = fd_x1_wa[`npuarc_LR1_LW0];   // W/back w0 bypass (lo)
//
assign fwd_x1_r0_wa_w1_lo   = fd_x1_wa[`npuarc_LR0_LW1];   // W/back w1 bypass (lo)
assign fwd_x1_r1_wa_w1_lo   = fd_x1_wa[`npuarc_LR1_LW1];   // W/back w1 bypass (lo)
//
assign fwd_x1_r0_ca_w1_hi   = fd_x1_ca[`npuarc_LR0_HW1] & x1_read_r0_r;   // Commit w1 bypass (hi)
assign fwd_x1_r1_ca_w1_hi   = fd_x1_ca[`npuarc_LR1_HW1] & x1_read_r1_r;   // Commit w1 bypass (hi)
assign fwd_x1_r0h_ca_w1_hi  = fd_x1_ca[`npuarc_HR0_HW1] & x1_read_r2_r;  // Commit w1 bypass (hi)
assign fwd_x1_r1h_ca_w1_hi  = fd_x1_ca[`npuarc_HR1_HW1] & x1_read_r3_r;  // Commit w1 bypass (hi)
//
assign fwd_x1_r0_wa_w1_hi   = fd_x1_wa[`npuarc_LR0_HW1];   // W/back w1 bypass (hi)
assign fwd_x1_r1_wa_w1_hi   = fd_x1_wa[`npuarc_LR1_HW1];   // W/back w1 bypass (hi)
assign fwd_x1_r0h_wa_w1_hi  = fd_x1_wa[`npuarc_HR0_HW1];   // W/back w1 bypass (hi)
assign fwd_x1_r1h_wa_w1_hi  = fd_x1_wa[`npuarc_HR1_HW1];   // W/back w1 bypass (hi)
assign fwd_x1_r1h_wa_w0_lo  = fd_x1_wa[`npuarc_HR1_LW0];   // W/back w0 bypass (lo)
assign fwd_x1_r1h_wa_w1_lo  = fd_x1_wa[`npuarc_HR1_LW1];   // W/back w1 bypass (lo)
//
assign fwd_x1_r0_x2_w0      = fd_x1_x2[`npuarc_LR0_LW0];   // Exec2 bypass value
assign fwd_x1_r1_x2_w0      = fd_x1_x2[`npuarc_LR1_LW0];   // Exec2 bypass value
assign fwd_x1_r0h_x2_w0     = fd_x1_x2[`npuarc_HR0_LW0];   // Exec2 bypass value
assign fwd_x1_r1h_x2_w0     = fd_x1_x2[`npuarc_HR1_LW0];   // Exec2 bypass value

assign fwd_x1_r0_x3_w0      = fd_x1_x3[`npuarc_LR0_LW0];   // Exec3 bypass value
assign fwd_x1_r1_x3_w0      = fd_x1_x3[`npuarc_LR1_LW0];   // Exec3 bypass value
assign fwd_x1_r0h_x3_w0     = fd_x1_x3[`npuarc_HR0_LW0];   // Exec3 bypass value
assign fwd_x1_r1h_x3_w0     = fd_x1_x3[`npuarc_HR1_LW0];   // Exec3 bypass value

assign fwd_x1_r0_ca_w0_lo   = fd_x1_ca[`npuarc_LR0_LW0];   // Commit w0 bypass (lo)
assign fwd_x1_r1_ca_w0_lo   = fd_x1_ca[`npuarc_LR1_LW0];   // Commit w0 bypass (lo)

assign fwd_x1_r0_ca_w1_lo   = fd_x1_ca[`npuarc_LR0_LW1] & x1_read_r0_r;  // Commit w1 bypass (lo)
assign fwd_x1_r1_ca_w1_lo   = fd_x1_ca[`npuarc_LR1_LW1] & x1_read_r1_r;  // Commit w1 bypass (lo)

assign fwd_x1_r0_ca_w0_hi   = fd_x1_ca[`npuarc_LR0_HW0];   // Commit w0 bypass (hi)
assign fwd_x1_r1_ca_w0_hi   = fd_x1_ca[`npuarc_LR1_HW0];   // Commit w0 bypass (hi)

assign fwd_x1_r0_wa_w0_hi   = fd_x1_wa[`npuarc_LR0_HW0];   // W/back w0 bypass (hi)
assign fwd_x1_r1_wa_w0_hi   = fd_x1_wa[`npuarc_LR1_HW0];   // W/back w0 bypass (hi)
assign fwd_x1_r0h_ca_w0_lo  = fd_x1_ca[`npuarc_HR0_LW0];   // Commit w0 bypass (lo)
assign fwd_x1_r0h_ca_w0_hi  = fd_x1_ca[`npuarc_HR0_HW0];   // Commit w0 bypass (hi)
assign fwd_x1_r1h_ca_w0_lo  = fd_x1_ca[`npuarc_HR1_LW0];   // Commit w0 bypass (lo)
assign fwd_x1_r1h_ca_w0_hi  = fd_x1_ca[`npuarc_HR1_HW0];   // Commit w0 bypass (hi)

assign fwd_x1_r0h_ca_w1_lo  = fd_x1_ca[`npuarc_HR0_LW1] & x1_read_r2_r;   // Commit w1 bypass (lo)
assign fwd_x1_r1h_ca_w1_lo  = fd_x1_ca[`npuarc_HR1_LW1] & x1_read_r3_r;   // Commit w1 bypass (lo)

assign fwd_x1_r0h_wa_w0_lo  = fd_x1_wa[`npuarc_HR0_LW0];   // W/back w0 bypass (lo)
assign fwd_x1_r0h_wa_w0_hi  = fd_x1_wa[`npuarc_HR0_HW0];   // W/back w0 bypass (hi)
assign fwd_x1_r0h_wa_w1_lo  = fd_x1_wa[`npuarc_HR0_LW1];   // W/back w1 bypass (lo)
assign fwd_x1_r1h_wa_w0_hi  = fd_x1_wa[`npuarc_HR1_HW0];   // W/back w0 bypass (hi)

////////// Exec2-stage bypass gating signals /////////////////////////////////
//
assign fwd_x2_r0_wa_w0_lo   = fd_x2_wa[`npuarc_LR0_LW0];
assign fwd_x2_r0_wa_w1_lo   = fd_x2_wa[`npuarc_LR0_LW1];
assign fwd_x2_r1_wa_w0_lo   = fd_x2_wa[`npuarc_LR1_LW0];
assign fwd_x2_r1_wa_w1_lo   = fd_x2_wa[`npuarc_LR1_LW1];
assign fwd_x2_r0_wa_w0_hi   = fd_x2_wa[`npuarc_LR0_HW0];
assign fwd_x2_r1_wa_w0_hi   = fd_x2_wa[`npuarc_LR1_HW0];
assign fwd_x2_r0_wa_w1_hi   = fd_x2_wa[`npuarc_LR0_HW1];
assign fwd_x2_r1_wa_w1_hi   = fd_x2_wa[`npuarc_LR1_HW1];
assign fwd_x2_r1h_wa_w0_lo  = fd_x2_wa[`npuarc_HR1_LW0];
assign fwd_x2_r1h_wa_w1_lo  = fd_x2_wa[`npuarc_HR1_LW1];
assign fwd_x2_r1h_wa_w0_hi  = fd_x2_wa[`npuarc_HR1_HW0];
assign fwd_x2_r1h_wa_w1_hi  = fd_x2_wa[`npuarc_HR1_HW1];

////////// Exec3-stage bypass gating signals /////////////////////////////////
//
assign fwd_x3_r0_ca_w0_lo   = fd_x3_ca[`npuarc_LR0_LW0];
assign fwd_x3_r0_ca_w1_lo   = fd_x3_ca[`npuarc_LR0_LW1];
assign fwd_x3_r0_wa_w0_lo   = fd_x3_wa[`npuarc_LR0_LW0];
assign fwd_x3_r0_wa_w1_lo   = fd_x3_wa[`npuarc_LR0_LW1];
//
assign fwd_x3_r1_ca_w0_lo   = fd_x3_ca[`npuarc_LR1_LW0];
assign fwd_x3_r1_ca_w1_lo   = fd_x3_ca[`npuarc_LR1_LW1];
assign fwd_x3_r1_wa_w0_lo   = fd_x3_wa[`npuarc_LR1_LW0];
assign fwd_x3_r1_wa_w1_lo   = fd_x3_wa[`npuarc_LR1_LW1];
assign fwd_x3_r0_ca_w0_hi   = fd_x3_ca[`npuarc_LR0_HW0];
assign fwd_x3_r0_wa_w0_hi   = fd_x3_wa[`npuarc_LR0_HW0];
//
assign fwd_x3_r1_ca_w0_hi   = fd_x3_ca[`npuarc_LR1_HW0];
assign fwd_x3_r1_wa_w0_hi   = fd_x3_wa[`npuarc_LR1_HW0];
assign fwd_x3_r0_wa_w1_hi   = fd_x3_wa[`npuarc_LR0_HW1];
assign fwd_x3_r1_wa_w1_hi   = fd_x3_wa[`npuarc_LR1_HW1];
assign fwd_x3_r0_ca_w1_hi   = fd_x3_ca[`npuarc_LR0_HW1];
//
assign fwd_x3_r1_ca_w1_hi   = fd_x3_ca[`npuarc_LR1_HW1];
assign fwd_x3_r1h_ca_w0_lo  = fd_x3_ca[`npuarc_HR1_LW0];
assign fwd_x3_r1h_ca_w1_lo  = fd_x3_ca[`npuarc_HR1_LW1];
assign fwd_x3_r1h_wa_w0_lo  = fd_x3_wa[`npuarc_HR1_LW0];
assign fwd_x3_r1h_wa_w1_lo  = fd_x3_wa[`npuarc_HR1_LW1];
assign fwd_x3_r1h_ca_w0_hi  = fd_x3_ca[`npuarc_HR1_HW0];
assign fwd_x3_r1h_wa_w0_hi  = fd_x3_wa[`npuarc_HR1_HW0];
assign fwd_x3_r1h_ca_w1_hi  = fd_x3_ca[`npuarc_HR1_HW1];
assign fwd_x3_r1h_wa_w1_hi  = fd_x3_wa[`npuarc_HR1_HW1];

////////// Commit-stage bypass gating signals ////////////////////////////////
//
assign fwd_ca_r0_wa_w0_lo   = fd_ca_wa[`npuarc_LR0_LW0];
assign fwd_ca_r0_wa_w1_lo   = fd_ca_wa[`npuarc_LR0_LW1];
assign fwd_ca_r1_wa_w0_lo   = fd_ca_wa[`npuarc_LR1_LW0];
assign fwd_ca_r1_wa_w1_lo   = fd_ca_wa[`npuarc_LR1_LW1];
assign fwd_ca_r0_wa_w0_hi   = fd_ca_wa[`npuarc_LR0_HW0];
assign fwd_ca_r1_wa_w0_hi   = fd_ca_wa[`npuarc_LR1_HW0];
assign fwd_ca_r0_wa_w1_hi   = fd_ca_wa[`npuarc_LR0_HW1];
assign fwd_ca_r1_wa_w1_hi   = fd_ca_wa[`npuarc_LR1_HW1];
assign fwd_ca_r1h_wa_w0_lo  = fd_ca_wa[`npuarc_HR1_LW0];
assign fwd_ca_r1h_wa_w1_lo  = fd_ca_wa[`npuarc_HR1_LW1];
assign fwd_ca_r1h_wa_w0_hi  = fd_ca_wa[`npuarc_HR1_HW0];
assign fwd_ca_r1h_wa_w1_hi  = fd_ca_wa[`npuarc_HR1_HW1];
assign sa_flag_stall        = flag_dependency_at_sa;

endmodule // alb_dep_pipe
