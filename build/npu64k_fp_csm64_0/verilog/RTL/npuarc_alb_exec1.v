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
//  ####### #     # #######  #####     #
//  #        #   #  #       #     #   ##
//  #         # #   #       #        # #
//  #####      #    #####   #          #
//  #         # #   #       #          #
//  #        #   #  #       #     #    #
//  ####### #     # #######  #####   #####
//
//============================================================================
// @f:execute:
// Description:
// @p
//  This module implements the first execution stage of the Albacore pipeline.
//
//  This module implements a single-stage ALU incorporating an Adder,
//  an optional Barrel Shifter, a Logic-Move-Extend unit, an optional
//  byte-manipulation unit, and an optional normalization unit.
//  The optional units are included according to the build configuration.
//
//  Branch and Jump instructions may have been resolved in the previous
//  (Operand) stage, in which case their resolution is available in this stage.
//  If the resolution indicates a branch mis-prediction, then the Issue Pipe
//  is restarted from the correct PC.
//
//  Branch and Jumps instructions that are dependent on their immediate
//  predecessor instruction (e.g. CMP followed by BEQ) cannot be resolved
//  until they reach this stage. Their resolution is based on the arithmetic
//  status bits available early in the X2 stage.
//
//  Branch prediction state is not updated in this stage, as instructions
//  are still speculative at this point.
//
//  The module hierarchy, at and below this module, is:
//
//         alb_exec1
//            |
//            +-- alb_agu
//            |
//            +-- alb_alu
//                   |
//                   +-- alb_maskgen
//                   |
//                   +-- alb_adder
//                   |
//                   +-- alb_logic_unit
//                   |
//                   +-- alb_shifter
//                   |
//                   +-- alb_byte_unit
//                   |
//                   +-- alb_bitscan
//
//  This stage is aligned with the DC1 stage of the Data Memory Pipeline,
//  with the MP1 stage of the Multiplier Pipeline, and with the FP1 stage
//  of the FPU pipeline.
// @e
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants.
//
`include "npuarc_ucode_const.v"

// Definitions for all decode-related constants
//
`include "npuarc_decode_const.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_exec1 (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,              // clock signal
  input                       rst_a,            // reset signal
  input                       db_active,        // debug operation is active

  ////////// Machine Architectural state /////////////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input   [`npuarc_DATA_RANGE]       ar_aux_status32_r,// STATUS32 AUX. register
  input   [`npuarc_DATA_RANGE]       ar_aux_erstatus_r,// ERSTATUS AUX. register
// leda NTL_CON13C on
  input                       ar_aux_user_mode_r,// user mode before interrupt

  ////////// Input from the Operands stage ///////////////////////////////////
  //
  input   [`npuarc_DATA_RANGE]       x1_src0_nxt,      // src0 of next insn
  input   [`npuarc_DATA_RANGE]       x1_src1_nxt,      // src1 of next insn
  input   [`npuarc_DATA_RANGE]       x1_src2_nxt,      // src2[31:0] of next insn
  input   [`npuarc_DATA_RANGE]       x1_src3_nxt,      // src3[13:0] of next insn
  input   [`npuarc_PC_RANGE]         sa_restart_pc,    // restart PC for SA mispred
  //
  input                       sa_src0_pass,     // receive valid src0 operand
  input                       sa_src1_pass,     // receive valid src1 operand
  input                       sa_src2_pass,     // receive valid src2 operand
  input                       sa_src3_pass,     // receive valid src3 operand
  //
  input  [`npuarc_X1_CODE_WIDTH-1:0] x1_code_nxt,      // next ucode for Exec1 stage

  ////////// Inputs from Dependency Pipeline /////////////////////////////////
  //
  input                       sa_pass,          // SA ready to pass insn to X1
  input                       x1_valid_r,       // valid instruction at X1
  input                       x1_pass,          // DA has insn to pass on
  input                       x1_retain,        // X1 instruction is retained
  input                       x1_enable,        // X1 enabled to receive insn
  input                       x1_bta_ready,     // X1 BTA value is ready
  input                       x1_no_eval,       // insn at X1 does not evaluate
  input                       x2_done_nxt,      // insn evals at X1.

  ////////// Inputs from Prediction Pipeline /////////////////////////////////
  //
  input                       sa_error_branch_r,// SA has fragged insn
  input                       x1_predictable_r, // X1 has predictable branch
  input                       x1_error_branch_r,// X1 has error-branch
  input                       x1_is_eslot_r,    // X1 is in an eslot
  input   [`npuarc_PC_RANGE]         x1_pred_bta_r,    // X1 predicted BTA or EI retn
 // input                       x2_kill,          // X2 is killed
//  input                       x1_wa_dslot,      // X1 is in DSLOT of WA
//  input                       x2_wa_dslot,      // X2 is in DSLOT of WA

  ////////// Inputs from ZOL Pipeline ////////////////////////////////////////
  //
//  input                       x1_zol_lp_jmp,    // early ZOL loop-back

 ////////// Interface to eia early result bus ///////////////////////////////
  //
  input                       x1_eia_res_valid, // explicit result valid 
  input                       x1_eia_fast_op_r, // explicit result valid 
  input       [`npuarc_DATA_RANGE]   x1_eia_res_data,  // explicit result data  
  input       [`npuarc_ZNCV_RANGE]   x1_eia_res_flags, // explicit result bflags
  
  ////////// Outputs to index the Data Cache aliasing predictor ///////////////
  //
  output reg [`npuarc_ADDR_RANGE]    x1_addr_base,     // VA addr base  
  output reg [`npuarc_ADDR_RANGE]    x1_addr_offset,   // VA add offset 
 
  ////////// Inputs from the Exec2 stage /////////////////////////////////////
  //
//  input                       x2_valid_r,       // valid insn at Exec2 stage
//  input                       x2_dslot_r,       // Exec1 is in Exec2 dslot
  input   [`npuarc_ZNCV_RANGE]       x2_zncv_r,        // speculative Exec2 ZNCV flags

  ////////// Datapath bypass values going into Exec1 stage ///////////////////
  //
  input   [`npuarc_DATA_RANGE]       dmp_dc4_fast_data,// early load data
  input   [`npuarc_DATA_RANGE]       wa_rf_wdata0_lo,  // W/back w0 bypass value (lo)
  input   [`npuarc_DATA_RANGE]       wa_rf_wdata1_lo,  // W/back w1 bypass value (lo)
  //
  input   [`npuarc_DATA_RANGE]       ca_byp_data1_hi,  // Commit w1 bypass value (hi)
  input   [`npuarc_DATA_RANGE]       wa_rf_wdata1_hi,  // W/back w1 bypass value (hi)
  //
  input   [`npuarc_DATA_RANGE]       x2_byp_data0,     // Exec2 bypass value
  input   [`npuarc_DATA_RANGE]       x3_byp_data0,     // Exec3 bypass value
  input   [`npuarc_DATA_RANGE]       ca_byp_data0_lo,  // Commit w0 bypass value (lo)
  input   [`npuarc_DATA_RANGE]       ca_byp_data1_lo,  // Commit w1 bypass value (lo)
  input   [`npuarc_DATA_RANGE]       ca_byp_data0_hi,  // Commit w0 bypass value (hi)
//  `endif
//  `if ((`DST64_OPTION == 1) | (`LL64_OPTION == 1))
  input   [`npuarc_DATA_RANGE]       wa_rf_wdata0_hi,  // W/back w0 bypass value (hi)

  ////////// Exec1-stage bypass gating signals ///////////////////////////////
  //
  input                       fwd_x1_r0_dmp_fast,   // load data for early bypass
  input                       fwd_x1_r1_dmp_fast,   // load data for early bypass
  //
  input                       fwd_x1_r0_wa_w0_lo,   // W/back w0 bypass value (lo)
  input                       fwd_x1_r1_wa_w0_lo,   // W/back w0 bypass value (lo)
  //
  input                       fwd_x1_r0_wa_w1_lo,   // W/back w1 bypass value (lo)
  input                       fwd_x1_r1_wa_w1_lo,   // W/back w1 bypass value (lo)
  //
  input                       fwd_x1_r0_ca_w1_hi,   // Commit w1 bypass value (hi)
  input                       fwd_x1_r1_ca_w1_hi,   // Commit w1 bypass value (hi)
  input                       fwd_x1_r0h_ca_w1_hi,  // Commit w1 bypass value (hi)
  input                       fwd_x1_r1h_ca_w1_hi,  // Commit w1 bypass value (hi)
  //
  input                       fwd_x1_r0_wa_w1_hi,   // W/back w1 bypass value (hi)
  input                       fwd_x1_r1_wa_w1_hi,   // W/back w1 bypass value (hi)
  input                       fwd_x1_r0h_wa_w1_hi,  // W/back w1 bypass value (hi)
  input                       fwd_x1_r1h_wa_w1_hi,  // W/back w1 bypass value (hi)
  input                       fwd_x1_r1h_wa_w0_lo,  // W/back w0 bypass value (lo)
  input                       fwd_x1_r1h_wa_w1_lo,  // W/back w1 bypass value (lo)
  //
  input                       fwd_x1_r0_x2_w0,      // Exec2 bypass value
  input                       fwd_x1_r1_x2_w0,      // Exec2 bypass value
  input                       fwd_x1_r0h_x2_w0,     // Exec2 bypass value
  input                       fwd_x1_r1h_x2_w0,     // Exec2 bypass value

  input                       fwd_x1_r0_x3_w0,      // Exec3 bypass value
  input                       fwd_x1_r1_x3_w0,      // Exec3 bypass value
  input                       fwd_x1_r0h_x3_w0,     // Exec3 bypass value
  input                       fwd_x1_r1h_x3_w0,     // Exec3 bypass value

  input                       fwd_x1_r0_ca_w0_lo,   // Commit w0 bypass value (lo)
  input                       fwd_x1_r1_ca_w0_lo,   // Commit w0 bypass value (lo)

  input                       fwd_x1_r0_ca_w1_lo,   // Commit w1 bypass value (lo)
  input                       fwd_x1_r1_ca_w1_lo,   // Commit w1 bypass value (lo)

  input                       fwd_x1_r0_ca_w0_hi,   // Commit w0 bypass value (hi)
  input                       fwd_x1_r1_ca_w0_hi,   // Commit w0 bypass value (hi)

  input                       fwd_x1_r0_wa_w0_hi,   // W/back w0 bypass value (hi)
  input                       fwd_x1_r1_wa_w0_hi,   // W/back w0 bypass value (hi)
  input                       fwd_x1_r0h_ca_w0_lo,  // Commit w0 bypass value (lo)
  input                       fwd_x1_r0h_ca_w0_hi,  // Commit w0 bypass value (hi)
  input                       fwd_x1_r1h_ca_w0_lo,  // Commit w0 bypass value (lo)
  input                       fwd_x1_r1h_ca_w0_hi,  // Commit w0 bypass value (hi)

  input                       fwd_x1_r0h_ca_w1_lo,  // Commit w1 bypass value (lo)
  input                       fwd_x1_r1h_ca_w1_lo,  // Commit w1 bypass value (lo)

  input                       fwd_x1_r0h_wa_w0_lo,  // W/back w0 bypass value (lo)
  input                       fwd_x1_r0h_wa_w0_hi,  // W/back w0 bypass value (hi)
  input                       fwd_x1_r0h_wa_w1_lo,  // W/back w1 bypass value (hi)
  input                       fwd_x1_r1h_wa_w0_hi,  // W/back w0 bypass value (hi)
  input       [`npuarc_ZNCV_RANGE]   fwd_zncv_x1,          // Fwd X1 ZNCV flags to X2
  input       [`npuarc_ZNCV_RANGE]   fwd_zncv_x1_x2,       // Fwd X2 ZNCV flags to X1
  input       [`npuarc_ZNCV_RANGE]   fwd_zncv_x1_ca,       // Fwd CA ZNCV flags to X1
  input                       fwd_zncv_x1_ar,       //
  input       [`npuarc_ZNCV_RANGE]   dp_retire_zncv,   // retirement ZNCV write enables
  input       [`npuarc_ZNCV_RANGE]   ca_retire_flags,  // selected retirement flags

  ////////// Inputs from the Writeback stage /////////////////////////////////
  //

// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input       [`npuarc_PFLAG_RANGE]  wa_aux_status32_nxt,  // Commiting STATUS32 from CA
// leda NTL_CON13C on
  ////////// Outputs to the Exec2 stage //////////////////////////////////////
  //
  output reg  [`npuarc_DATA_RANGE]   x1_byp_data0,     // primary Exec1 result value
  output reg  [`npuarc_DATA_RANGE]   x2_src0_nxt,      // src0 for Exec2 stage
  output reg  [`npuarc_DATA_RANGE]   x2_src1_nxt,      // src1 for Exec2 stage
  output reg  [`npuarc_PC_RANGE]     x2_target_nxt,    // next branch target for X2
  output reg                  x1_res_pass,      // pass valid x1_byp_data0
  output reg                  x1_src0_pass,     // pass valid x2_src0_nxt
  output reg                  x1_src1_pass,     // pass valid x2_src1_nxt
  //
  output reg  [`npuarc_ZNCV_RANGE]   x2_zncv_nxt,      // next ZNCV flags
  output [`npuarc_X2_CODE_WIDTH-1:0] x2_code_nxt,      // next ucode for x2 stage
  output                      x2_lt_flag_nxt,   // next less-than flag
  
  ////////// Early branch resolution information from X1 stage ///////////////
  //
  output reg                  x1_br_taken,      // Branch or jump taken at X1
  output reg                  x1_br_direction,  // PC change direction at X1
  output reg [`npuarc_PC_RANGE]      x1_br_target,     // target or fall-thru at X1
  output reg [`npuarc_PC_RANGE]      x1_br_fall_thru,  // fall-thru address at X1
  output reg                  x1_bi_bta_mpd,    // BTA miss for BI, BIH insn
  output     [`npuarc_PC_RANGE]      x1_link_addr,     // link addr for BL, JL
  
  ////////// Outputs to Dep. Pipeline ////////////////////////////////////////
  //
  output [`npuarc_RGF_ADDR_RANGE]    x1_rf_ra0_r,       // reg-read address 0 at X1
  output [`npuarc_RGF_ADDR_RANGE]    x1_rf_ra1_r,       // reg-read address 1 at X1
  output [`npuarc_RGF_ADDR_RANGE]    x1_rf_wa0_r,       //
  output                      x1_rf_wenb0_r,     //
  output                      x1_rf_wenb0_64_r,  //
  output                      x1_cc_byp_64_haz_r,// X1 insn cannot bypass r0h
  output [`npuarc_RGF_ADDR_RANGE]    x1_rf_wa1_r,       //
  output                      x1_rf_wenb1_r,     //
  output                      x1_rf_wenb1_64_r,  //
  output                      x1_rf_renb0_64_r,  //
  output                      x1_rf_renb1_64_r,  //
  output                      x1_acc_wenb_r,     //
  // -- signals for determining flag dependencies
  output      [`npuarc_ZNCV_RANGE]   x1_zncv_wen_r,    // ZNCV flag write-enable
  output                      x1_flag_op_r,     // [k]flag insn.
  output                      x1_brk_op_r,      // brk insn
  output                      x1_sleep_op_r,    // sleep (any type) insn
  output reg                  x1_cond,          // insn shall evaluate on cc
  output      [4:0]           x1_q_field_r,     // insn. q-field
  output                      x1_signed_op_r,   //
  output                      x1_uop_commit_r,  // insn is terminal of uop-seq
  output                      x1_uop_prol_r,    // insn is terminal of prologue
  output                      x1_uop_epil_r,    // insn is terminal of epilogue
  output                      x1_with_carry_r,  // insn at X1 uses carry flag
  output                      x1_rgf_link,
  output                      x1_dmb_op_r,      // DMB insn at X1
  output     [2:0]            x1_dmb_type_r,    // DMB u3 operand at X1

 ////////// Inputs from the DMP /////////////////////////////////////////////
  //

  ////////// Outputs to the Prediction pipeline //////////////////////////////
  //
  output                      x1_uop_inst_r,    // X1 insn is part of uop seq
  
  ////////// Outputs to the ZOL pipeline /////////////////////////////////////
  //
  output                      x1_wa0_lpc_r,
  output                      x1_loop_op_r,
  

  ////////// Outputs to Dependency Pipeline //////////////////////////////////
  //
  output reg                  x1_valid_nxt,     //
  output                      x1_fast_op_r,     //
  output                      x1_slow_op_r,     //
  output                      x1_dslot_r,       // X1 has dslot insn
  output                      x1_sr_op_r,       //
  output                      x1_ei_op_r,       //
  output                      x1_btab_op_r,     //
  output                      x1_opds_in_sa_r,  //
  output                      x1_opds_in_x1_r,  //
  output                      x1_agu_uses_r0_r, //
  //
  output reg                  x1_grab_src0,     // grab a WA bypass for src0
  output reg                  x1_grab_src1,     // grab a WA bypass for src1
  output reg                  x1_grab_src2,     // grab a WA bypass for src0
  output reg                  x1_grab_src3,     // grab a WA bypass for src1

  ////////// Control outputs to Multiplier Pipeline //////////////////////////
  //
  output                      x1_mpy_op_r,      // mpy op is decoded in X1
  output                      x1_half_size_r,   // mpy data size is 16 bits
  output                      x1_dual_op_r,     // dual SIMD operation
  output                      x1_vector_op_r,   // independent channels
  output                      x1_quad_op_r,     // quad SIMD operation

  ////////// Operand values for Multiplier and/or FPU ////////////////////////
  //
  output reg [`npuarc_DATA_RANGE]    mp1_src0_nxt,     // 1st src opd (lsb 32 bits)
  output reg [`npuarc_DATA_RANGE]    mp1_src1_nxt,     // 2nd src oped (lsb 32 bits)
  output reg [`npuarc_DATA_RANGE]    mp1_src2_nxt,     // 1st src opd (lsb 32 bits)
  output reg [`npuarc_DATA_RANGE]    mp1_src3_nxt,     // 2nd src opd (lsb 32 bits)
  ////////// Outputs to Divide unit //////////////////////////////////////////
  //
  output                      x1_div_op_r,      // DIV, REM ucode bit
  output                      x1_div_kind_r,    // 0 => div/u, 1 => rem/u

  output                      x2_predicate_nxt, // X1 Evaluated predicate
  ////////// Outputs to Memory Protection Unit ///////////////////////////////
  //
  output                      x1_iprot_viol_r,  // disallow AP match if viol
  ////////// handshake to eia logic //////////////////////////////////////////
  //
  output                      x1_dest_cr_is_ext_r,  // to eia dep logic
  input                       eia_ext_cond,     // EIA extension condition
  ////////// Outputs to the DMP //////////////////////////////////////////////
  //
  output reg                  x1_addr_pass,     // passing valid mem addr to X2
  output reg  [1:0]           x1_size_r,        // LD/ST insn size in Execute
  output                      x1_load_r,        // Load insn in Execute
  output                      x1_store_r,       // Store insns in Execute
  output                      x1_pref_r,        // Pref ucode bit
  output                      x1_cache_byp_r,   // enable cache bypass
  output reg  [`npuarc_ADDR_RANGE]   x1_mem_addr0,     // computed memory address
  output      [`npuarc_ADDR_RANGE]   x1_mem_addr1,     // memory address plus 4 or 8
  output      [1:0]           x1_bank_sel_lo,   // memory bank lo
  output      [1:0]           x1_bank_sel_hi    // memory bank hi
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pipeline registers at the input to the X1 stage                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg   [`npuarc_DATA_RANGE]         x1_src0_r;        // first source operand [31:0]
reg   [`npuarc_DATA_RANGE]         x1_src1_r;        // second source operand [31:0]
reg   [`npuarc_DATA_RANGE]         x1_src2_r;        // third source operand
reg   [`npuarc_DATA_RANGE]         x1_src3_r;        // fourth source operand
reg   [`npuarc_PC_RANGE]           x1_restart_pc_r;  // needed for error-branch mpd
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg   [`npuarc_X1_CODE_WIDTH-1:0]  x1_code_r;        // Execute-stage ucode vector
// leda NTL_CON32 on


wire                        x1_double_size_r;
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Wires and regs for local non-registered signals                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// Assign each microcode field to a named wire or wire-vector
//
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

assign x1_rf_wa0_r  = x1_code_r[`npuarc_RF_WA0_RANGE];  // generated code
assign x1_rf_wenb0_r  = x1_code_r[`npuarc_RF_WENB0_RANGE];  // generated code
assign x1_rf_wenb0_64_r  = x1_code_r[`npuarc_RF_WENB0_64_RANGE];  // generated code
assign x1_cc_byp_64_haz_r  = x1_code_r[`npuarc_CC_BYP_64_HAZ_RANGE];  // generated code
wire   x1_has_limm_r;  // generated code
assign x1_has_limm_r  = x1_code_r[`npuarc_HAS_LIMM_RANGE];  // generated code
wire   x1_is_16bit_r;  // generated code
assign x1_is_16bit_r  = x1_code_r[`npuarc_IS_16BIT_RANGE];  // generated code
assign x1_sr_op_r   = x1_code_r[`npuarc_SR_OP_RANGE];  // generated code
assign x1_loop_op_r  = x1_code_r[`npuarc_LOOP_OP_RANGE];  // generated code
wire   x1_locked_r;  // generated code
assign x1_locked_r  = x1_code_r[`npuarc_LOCKED_RANGE];  // generated code
assign x1_wa0_lpc_r  = x1_code_r[`npuarc_WA0_LPC_RANGE];  // generated code
assign x1_dslot_r   = x1_code_r[`npuarc_DSLOT_RANGE];  // generated code
assign x1_sleep_op_r  = x1_code_r[`npuarc_SLEEP_OP_RANGE];  // generated code
assign x1_acc_wenb_r  = x1_code_r[`npuarc_ACC_WENB_RANGE];  // generated code
wire   x1_writes_acc_r;  // generated code
assign x1_writes_acc_r  = x1_code_r[`npuarc_WRITES_ACC_RANGE];  // generated code
assign x1_lr_op_r   = x1_code_r[`npuarc_LR_OP_RANGE];  // generated code
wire   x1_jump_r;  // generated code
assign x1_jump_r  = x1_code_r[`npuarc_JUMP_RANGE];  // generated code
assign x1_load_r    = x1_code_r[`npuarc_LOAD_RANGE];  // generated code
assign x1_pref_r    = x1_code_r[`npuarc_PREF_RANGE];  // generated code
assign x1_store_r   = x1_code_r[`npuarc_STORE_RANGE];  // generated code
assign x1_uop_prol_r  = x1_code_r[`npuarc_UOP_PROL_RANGE];  // generated code
assign x1_rf_wa1_r  = x1_code_r[`npuarc_RF_WA1_RANGE];  // generated code
assign x1_rf_wenb1_r  = x1_code_r[`npuarc_RF_WENB1_RANGE];  // generated code
assign x1_rf_wenb1_64_r  = x1_code_r[`npuarc_RF_WENB1_64_RANGE];  // generated code
assign x1_signed_op_r  = x1_code_r[`npuarc_SIGNED_OP_RANGE];  // generated code
assign x1_double_size_r  = x1_code_r[`npuarc_DOUBLE_SIZE_RANGE];  // generated code
assign x1_half_size_r  = x1_code_r[`npuarc_HALF_SIZE_RANGE];  // generated code
wire   x1_byte_size_r;  // generated code
assign x1_byte_size_r  = x1_code_r[`npuarc_BYTE_SIZE_RANGE];  // generated code
wire   x1_rtie_op_r;  // generated code
assign x1_rtie_op_r  = x1_code_r[`npuarc_RTIE_OP_RANGE];  // generated code
wire   x1_enter_op_r;  // generated code
assign x1_enter_op_r  = x1_code_r[`npuarc_ENTER_OP_RANGE];  // generated code
wire   x1_leave_op_r;  // generated code
assign x1_leave_op_r  = x1_code_r[`npuarc_LEAVE_OP_RANGE];  // generated code
wire   x1_trap_op_r;  // generated code
assign x1_trap_op_r  = x1_code_r[`npuarc_TRAP_OP_RANGE];  // generated code
wire   x1_sync_op_r;  // generated code
assign x1_sync_op_r  = x1_code_r[`npuarc_SYNC_OP_RANGE];  // generated code
assign x1_brk_op_r  = x1_code_r[`npuarc_BRK_OP_RANGE];  // generated code
wire   x1_invalid_instr_r;  // generated code
assign x1_invalid_instr_r  = x1_code_r[`npuarc_INVALID_INSTR_RANGE];  // generated code
wire   x1_rgf_link_r;  // generated code
assign x1_rgf_link_r  = x1_code_r[`npuarc_RGF_LINK_RANGE];  // generated code
wire   x1_prod_sign_r;  // generated code
assign x1_prod_sign_r  = x1_code_r[`npuarc_PROD_SIGN_RANGE];  // generated code
wire   x1_macu_r;  // generated code
assign x1_macu_r  = x1_code_r[`npuarc_MACU_RANGE];  // generated code
assign x1_quad_op_r  = x1_code_r[`npuarc_QUAD_OP_RANGE];  // generated code
wire   x1_acc_op_r;  // generated code
assign x1_acc_op_r  = x1_code_r[`npuarc_ACC_OP_RANGE];  // generated code
assign x1_vector_op_r  = x1_code_r[`npuarc_VECTOR_OP_RANGE];  // generated code
assign x1_dual_op_r  = x1_code_r[`npuarc_DUAL_OP_RANGE];  // generated code
assign x1_mpy_op_r  = x1_code_r[`npuarc_MPY_OP_RANGE];  // generated code
wire   x1_z_wen_r;  // generated code
assign x1_z_wen_r  = x1_code_r[`npuarc_Z_WEN_RANGE];  // generated code
wire   x1_n_wen_r;  // generated code
assign x1_n_wen_r  = x1_code_r[`npuarc_N_WEN_RANGE];  // generated code
wire   x1_c_wen_r;  // generated code
assign x1_c_wen_r  = x1_code_r[`npuarc_C_WEN_RANGE];  // generated code
wire   x1_v_wen_r;  // generated code
assign x1_v_wen_r  = x1_code_r[`npuarc_V_WEN_RANGE];  // generated code
wire   x1_kernel_op_r;  // generated code
assign x1_kernel_op_r  = x1_code_r[`npuarc_KERNEL_OP_RANGE];  // generated code
assign x1_flag_op_r  = x1_code_r[`npuarc_FLAG_OP_RANGE];  // generated code
wire   x1_bcc_r;  // generated code
assign x1_bcc_r  = x1_code_r[`npuarc_BCC_RANGE];  // generated code
wire   x1_link_r;  // generated code
assign x1_link_r  = x1_code_r[`npuarc_LINK_RANGE];  // generated code
wire   x1_brcc_bbit_r;  // generated code
assign x1_brcc_bbit_r  = x1_code_r[`npuarc_BRCC_BBIT_RANGE];  // generated code
assign x1_cache_byp_r  = x1_code_r[`npuarc_CACHE_BYP_RANGE];  // generated code
assign x1_slow_op_r  = x1_code_r[`npuarc_SLOW_OP_RANGE];  // generated code
assign x1_fast_op_r  = x1_code_r[`npuarc_FAST_OP_RANGE];  // generated code
assign x1_div_op_r  = x1_code_r[`npuarc_DIV_OP_RANGE];  // generated code
assign x1_btab_op_r  = x1_code_r[`npuarc_BTAB_OP_RANGE];  // generated code
assign x1_ei_op_r   = x1_code_r[`npuarc_EI_OP_RANGE];  // generated code
wire   x1_in_eslot_r;  // generated code
assign x1_in_eslot_r  = x1_code_r[`npuarc_IN_ESLOT_RANGE];  // generated code
wire   x1_rel_branch_r;  // generated code
assign x1_rel_branch_r  = x1_code_r[`npuarc_REL_BRANCH_RANGE];  // generated code
wire   x1_illegal_operand_r;  // generated code
assign x1_illegal_operand_r  = x1_code_r[`npuarc_ILLEGAL_OPERAND_RANGE];  // generated code
wire   x1_swap_op_r;  // generated code
assign x1_swap_op_r  = x1_code_r[`npuarc_SWAP_OP_RANGE];  // generated code
wire   x1_setcc_op_r;  // generated code
assign x1_setcc_op_r  = x1_code_r[`npuarc_SETCC_OP_RANGE];  // generated code
wire [2:0]  x1_cc_field_r;  // generated code
assign x1_cc_field_r  = x1_code_r[`npuarc_CC_FIELD_RANGE];  // generated code
assign x1_q_field_r  = x1_code_r[`npuarc_Q_FIELD_RANGE];  // generated code
assign x1_dest_cr_is_ext_r  = x1_code_r[`npuarc_DEST_CR_IS_EXT_RANGE];  // generated code
wire   x1_add_op_r;  // generated code
assign x1_add_op_r  = x1_code_r[`npuarc_ADD_OP_RANGE];  // generated code
wire   x1_and_op_r;  // generated code
assign x1_and_op_r  = x1_code_r[`npuarc_AND_OP_RANGE];  // generated code
wire   x1_or_op_r;  // generated code
assign x1_or_op_r  = x1_code_r[`npuarc_OR_OP_RANGE];  // generated code
wire   x1_xor_op_r;  // generated code
assign x1_xor_op_r  = x1_code_r[`npuarc_XOR_OP_RANGE];  // generated code
wire   x1_mov_op_r;  // generated code
assign x1_mov_op_r  = x1_code_r[`npuarc_MOV_OP_RANGE];  // generated code
assign x1_with_carry_r  = x1_code_r[`npuarc_WITH_CARRY_RANGE];  // generated code
wire   x1_simple_shift_op_r;  // generated code
assign x1_simple_shift_op_r  = x1_code_r[`npuarc_SIMPLE_SHIFT_OP_RANGE];  // generated code
wire   x1_left_shift_r;  // generated code
assign x1_left_shift_r  = x1_code_r[`npuarc_LEFT_SHIFT_RANGE];  // generated code
wire   x1_rotate_op_r;  // generated code
assign x1_rotate_op_r  = x1_code_r[`npuarc_ROTATE_OP_RANGE];  // generated code
wire   x1_inv_src1_r;  // generated code
assign x1_inv_src1_r  = x1_code_r[`npuarc_INV_SRC1_RANGE];  // generated code
wire   x1_inv_src2_r;  // generated code
assign x1_inv_src2_r  = x1_code_r[`npuarc_INV_SRC2_RANGE];  // generated code
wire   x1_bit_op_r;  // generated code
assign x1_bit_op_r  = x1_code_r[`npuarc_BIT_OP_RANGE];  // generated code
wire   x1_mask_op_r;  // generated code
assign x1_mask_op_r  = x1_code_r[`npuarc_MASK_OP_RANGE];  // generated code
wire   x1_src2_mask_sel_r;  // generated code
assign x1_src2_mask_sel_r  = x1_code_r[`npuarc_SRC2_MASK_SEL_RANGE];  // generated code
assign x1_uop_commit_r  = x1_code_r[`npuarc_UOP_COMMIT_RANGE];  // generated code
assign x1_uop_epil_r  = x1_code_r[`npuarc_UOP_EPIL_RANGE];  // generated code
wire   x1_uop_excpn_r;  // generated code
assign x1_uop_excpn_r  = x1_code_r[`npuarc_UOP_EXCPN_RANGE];  // generated code
wire   x1_predicate_r;  // generated code
assign x1_predicate_r  = x1_code_r[`npuarc_PREDICATE_RANGE];  // generated code
wire   x1_rf_renb0_r;  // generated code
assign x1_rf_renb0_r  = x1_code_r[`npuarc_RF_RENB0_RANGE];  // generated code
wire   x1_rf_renb1_r;  // generated code
assign x1_rf_renb1_r  = x1_code_r[`npuarc_RF_RENB1_RANGE];  // generated code
assign x1_rf_renb0_64_r  = x1_code_r[`npuarc_RF_RENB0_64_RANGE];  // generated code
assign x1_rf_renb1_64_r  = x1_code_r[`npuarc_RF_RENB1_64_RANGE];  // generated code
assign x1_rf_ra0_r  = x1_code_r[`npuarc_RF_RA0_RANGE];  // generated code
assign x1_rf_ra1_r  = x1_code_r[`npuarc_RF_RA1_RANGE];  // generated code
wire   x1_jli_src0_r;  // generated code
assign x1_jli_src0_r  = x1_code_r[`npuarc_JLI_SRC0_RANGE];  // generated code
assign x1_uop_inst_r  = x1_code_r[`npuarc_UOP_INST_RANGE];  // generated code
wire   x1_vec_shimm_r;  // generated code
assign x1_vec_shimm_r  = x1_code_r[`npuarc_VEC_SHIMM_RANGE];  // generated code
assign x1_iprot_viol_r  = x1_code_r[`npuarc_IPROT_VIOL_RANGE];  // generated code
assign x1_dmb_op_r  = x1_code_r[`npuarc_DMB_OP_RANGE];  // generated code
assign x1_dmb_type_r  = x1_code_r[`npuarc_DMB_TYPE_RANGE];  // generated code
wire   x1_force_cin_r;  // generated code
assign x1_force_cin_r  = x1_code_r[`npuarc_FORCE_CIN_RANGE];  // generated code
wire   x1_opd3_sel_r;  // generated code
assign x1_opd3_sel_r  = x1_code_r[`npuarc_OPD3_SEL_RANGE];  // generated code
wire   x1_multi_op_r;  // generated code
assign x1_multi_op_r  = x1_code_r[`npuarc_MULTI_OP_RANGE];  // generated code
wire   x1_abs_op_r;  // generated code
assign x1_abs_op_r  = x1_code_r[`npuarc_ABS_OP_RANGE];  // generated code
wire   x1_min_op_r;  // generated code
assign x1_min_op_r  = x1_code_r[`npuarc_MIN_OP_RANGE];  // generated code
wire   x1_max_op_r;  // generated code
assign x1_max_op_r  = x1_code_r[`npuarc_MAX_OP_RANGE];  // generated code
wire   x1_norm_op_r;  // generated code
assign x1_norm_op_r  = x1_code_r[`npuarc_NORM_OP_RANGE];  // generated code
wire   x1_ldi_src0_r;  // generated code
assign x1_ldi_src0_r  = x1_code_r[`npuarc_LDI_SRC0_RANGE];  // generated code
wire   x1_pre_addr_r;  // generated code
assign x1_pre_addr_r  = x1_code_r[`npuarc_PRE_ADDR_RANGE];  // generated code
wire   x1_stimm_op_r;  // generated code
assign x1_stimm_op_r  = x1_code_r[`npuarc_STIMM_OP_RANGE];  // generated code
wire   x1_src2_sh1_r;  // generated code
assign x1_src2_sh1_r  = x1_code_r[`npuarc_SRC2_SH1_RANGE];  // generated code
wire   x1_src2_sh2_r;  // generated code
assign x1_src2_sh2_r  = x1_code_r[`npuarc_SRC2_SH2_RANGE];  // generated code
wire   x1_src2_sh3_r;  // generated code
assign x1_src2_sh3_r  = x1_code_r[`npuarc_SRC2_SH3_RANGE];  // generated code
wire   x1_barrel_shift_op_r;  // generated code
assign x1_barrel_shift_op_r  = x1_code_r[`npuarc_BARREL_SHIFT_OP_RANGE];  // generated code
assign x1_opds_in_x1_r  = x1_code_r[`npuarc_OPDS_IN_X1_RANGE];  // generated code
assign x1_agu_uses_r0_r  = x1_code_r[`npuarc_AGU_USES_R0_RANGE];  // generated code
assign x1_opds_in_sa_r  = x1_code_r[`npuarc_OPDS_IN_SA_RANGE];  // generated code
wire   x1_limm0_64_r;  // generated code
assign x1_limm0_64_r  = x1_code_r[`npuarc_LIMM0_64_RANGE];  // generated code
wire   x1_limm1_64_r;  // generated code
assign x1_limm1_64_r  = x1_code_r[`npuarc_LIMM1_64_RANGE];  // generated code

// leda NTL_CON13A on
wire  [`npuarc_DATA_RANGE]         x1_alu_result;    // X1 ALU result value


wire                        adder_lessthan;   // X1 ALU less-than condition
wire                        alu_brcc_cond;    // X1 BRcc test outcome
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  not used lower bit
wire  [`npuarc_DATA_RANGE]         alu_sum_no_cin;   // src1+src2 with no carry-in
// leda NTL_CON13A on
wire  [`npuarc_DATA_RANGE]         alu_shift_src2;   // optionally-shifted src2

wire  [`npuarc_ZNCV_RANGE]         alu_zncv;         // ALU flags
reg   [`npuarc_ZNCV_RANGE]         x1_alu_zncv_sel;  // ALU/EIA flags
reg   [`npuarc_ZNCV_RANGE]         x1_zncv;          // X1 flags


// @x1_ctrl_PROC
reg                         x1_code_cg0;
reg                         x1_src0_cg0;      // enable the x1_src0_r register
reg                         x1_src1_cg0;      // enable the x1_src1_r register
reg                         x1_src2_cg0;      // enable the x1_src2_r register
reg                         x1_src3_cg0;      // enable the x1_src3_r register

reg   [`npuarc_ADDR_RANGE]         agu_src1;         // source 1 for AGU module
reg   [`npuarc_ADDR_RANGE]         agu_src2;         // source 2 for AGU module
wire  [`npuarc_ADDR_RANGE]         agu_addr0;        // agu_src1 + (scaled)agu_src2
reg   [`npuarc_ADDR_RANGE]         x1_base_addr;     // source 1 or 2 (pre-addr, EX)
reg   [`npuarc_DATA_RANGE]         agu_address;      // DATA_SIZEd AGU result 

reg   [`npuarc_X2_CODE_WIDTH-1:0]  ucode_out;        // output ucode for next stage

reg                         x1_is_branch;     // insn is a branch
reg                         x1_is_mem_op;     // insn is a LD or ST
reg                         x1_is_aux_op;     // insn is an LR or SR
reg                         x1_needs_src2;    // insn is FLAG,SLEEP or TRAP
reg                         x1_sel_src2;      // x2_src0_nxt gets x1_src2_r
//reg                         x1_sel_alu;       // select alu output as X1 res
reg   [`npuarc_DATA_RANGE]         x1_false_res;     // X1 result if cond is false
reg   [`npuarc_DATA_RANGE]         x1_cond_res;      // conditional X1 result
reg   [`npuarc_DATA_RANGE]         x1_false_res_hi;  // pass-thru hi result

// Define registers for Exec1-stage result bypassing from downstream
//
// @x1_bypass_PROC
reg                         r0_no_agu_byp;    // No AGU early bypass for reg0
reg                         r0_lo_wa_byp;     // reg0 lo gets bypass from WA
reg                         r0_lo_no_byp;     // No bypass for reg0 lo
reg   [`npuarc_DATA_RANGE]         x1_r0_lo_byp_wa;  // Bypassed reg0 lo value from WA
reg   [`npuarc_DATA_RANGE]         x1_byp_reg0_lo;   // Bypassed reg0 lo value
reg   [`npuarc_DATA_RANGE]         x1_next_src0;     // next value for x1_src0_r

reg                         r1_lo_wa_byp;     // reg1 lo gets bypass from WA
reg                         r1_lo_no_byp;     // No bypass for reg1 lo
reg   [`npuarc_DATA_RANGE]         x1_r1_lo_byp_wa;  // Bypassed reg1 lo value from WA
reg   [`npuarc_DATA_RANGE]         x1_byp_reg1_lo;   // Bypassed reg1 lo value
reg   [`npuarc_DATA_RANGE]         x1_next_src1;     // next value for x1_src1_r

reg   [`npuarc_DATA_RANGE]         x1_next_src2;     // next value for x1_src2_r
reg                         r0_hi_wa_byp;     // reg0 hi gets bypass from WA
reg                         r0_hi_no_byp;     // No bypass for reg0 hi
reg   [`npuarc_DATA_RANGE]         x1_r0_hi_byp_wa;  // Bypassed reg0 hi value from WA
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  bypass reg
reg   [`npuarc_DATA_RANGE]         x1_byp_reg0_hi;   // Bypassed reg0 hi value
// leda NTL_CON13A on

reg   [`npuarc_DATA_RANGE]         x1_next_src3;     // next value for x1_src3_r
reg                         r1_hi_wa_byp;     // reg1 hi gets bypass from WA
reg                         r1_hi_no_byp;     // No bypass for reg1 hi
reg   [`npuarc_DATA_RANGE]         x1_r1_hi_byp_wa;  // Bypassed reg1 hi value from WA
reg   [`npuarc_DATA_RANGE]         x1_byp_reg1_hi;   // Bypassed src1 hi value
reg                         r1h_is_wa0_hi;    // Bypass wa0 hi to X1 r1h
reg                         r1h_is_wa1_hi;    // Bypass wa1 hi to X1 r1h
reg                         i_prod_sign;      // product sign, used by MAC ops
  

// Define registers for Exec1-stage condition evaluation
//
// @x1_cond_PROC
reg                         q_cond;           // Predicate value at X1
reg                         v_flag;           // oVerflow flag at X1
reg                         c_flag;           // Carry flag at X1
reg                         n_flag;           // sigN flag at X1
reg                         z_flag;           // Zero flag at X1

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to implement the bypass network at the X1 stage    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block STARC05-1.3.1.3
// SMD: Asynchronous reset signal not used as intended
// SJ:  Is used as asynchronous reset signal
always @*
begin : x1_bypass_PROC

  //==========================================================================
  // Each of the two AGU source operands may be bypassed from the speculative
  // load data available early in the Commit stage (dmp_dc4_fast_data).
  // The Dependency Pipe determines which of the inputs will deliver the
  // most up-to-date value for the required source operand, and sets the
  // corresponding selection control signals. These are registered at the
  // input interface to the Exec1 stage.
  //
  r0_no_agu_byp   = !(  fwd_x1_r0_dmp_fast
                      | fwd_x1_r0_wa_w1_lo
                     )
                  ;

  agu_src1        = ( {`npuarc_DATA_SIZE{r0_no_agu_byp}}      & x1_src0_r         )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_dmp_fast}} & dmp_dc4_fast_data )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_wa_w1_lo}} & wa_rf_wdata1_lo   )
                  ;

  //==========================================================================
  // r0_lo_wa_byp is asserted whenever the LR0 read channel should receive
  // a bypassed results from WA.
  //
  r0_lo_wa_byp    = fwd_x1_r0_wa_w0_lo
                  | fwd_x1_r0_wa_w1_lo
                  | fwd_x1_r0_wa_w1_hi
                  | fwd_x1_r0_wa_w0_hi
                  ;
                  
  //==========================================================================
  // r0_lo_no_byp is asserted whenever the LR0 read channel is not required
  // to receive a bypassed value from any legal bypass point. In this case,
  // the current x1_src0_r operand value is valid, and should be forwarded
  // to the X2 stage through x1_byp_reg0_lo.
  //
  r0_lo_no_byp    = !(  r0_lo_wa_byp
                      | fwd_x1_r0_ca_w1_hi
                      | fwd_x1_r0_x2_w0
                      | fwd_x1_r0_x3_w0
                      | fwd_x1_r0_ca_w0_lo
                      | fwd_x1_r0_ca_w1_lo
                      | fwd_x1_r0_ca_w0_hi
                    )
                  ;

  //==========================================================================
  // x1_r0_lo_byp_wa carries all current bypass values from the WA stage to
  // the reg0 lo read channel at X1.
  //
  x1_r0_lo_byp_wa = ( {`npuarc_DATA_SIZE{fwd_x1_r0_wa_w0_lo}} & wa_rf_wdata0_lo   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_wa_w1_lo}} & wa_rf_wdata1_lo   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_wa_w1_hi}} & wa_rf_wdata1_hi   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_wa_w0_hi}} & wa_rf_wdata0_hi   )
                  ;
  
  //==========================================================================
  // x1_byp_reg0_lo carries all current bypass values from all stages to
  // the reg0 lo read channel at X1.
  //
  x1_byp_reg0_lo  = x1_r0_lo_byp_wa
                  | ( {`npuarc_DATA_SIZE{r0_lo_no_byp}}       & x1_src0_r         )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_ca_w1_hi}} & ca_byp_data1_hi   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_x2_w0}}    & x2_byp_data0      )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_x3_w0}}    & x3_byp_data0      )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_ca_w0_lo}} & ca_byp_data0_lo   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_ca_w1_lo}} & ca_byp_data1_lo   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0_ca_w0_hi}} & ca_byp_data0_hi   )
                  ;

  agu_src2        = x1_src1_r;

  //==========================================================================
  // r1_lo_wa_byp is asserted whenever the LR1 read channel should receive
  // a bypassed results from WA.
  //
  r1_lo_wa_byp    = fwd_x1_r1_wa_w0_lo
                  | fwd_x1_r1_wa_w1_lo
                  | fwd_x1_r1_wa_w1_hi
                  | fwd_x1_r1_wa_w0_hi
                  ;

  //==========================================================================
  // r1_lo_no_byp is asserted whenever the LR1 read channel is not required
  // to receive a bypassed value from any legal bypass point. In this case,
  // the current LR1 operand value is valid, and should be forwarded
  // to the X2 stage.
  //
  r1_lo_no_byp    = !(  r1_lo_wa_byp
                      | fwd_x1_r1_dmp_fast
                      | fwd_x1_r1_ca_w1_hi
                      | fwd_x1_r1_x2_w0
                      | fwd_x1_r1_x3_w0
                      | fwd_x1_r1_ca_w0_lo
                      | fwd_x1_r1_ca_w1_lo
                      | fwd_x1_r1_ca_w0_hi
                    )
                  ;

  //==========================================================================
  // x1_r1_lo_byp_wa carries all current bypass values from the WA stage to
  // the reg1 lo read channel at X1.
  //
  x1_r1_lo_byp_wa = ( {`npuarc_DATA_SIZE{fwd_x1_r1_wa_w0_lo}} & wa_rf_wdata0_lo   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1_wa_w1_lo}} & wa_rf_wdata1_lo   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1_wa_w1_hi}} & wa_rf_wdata1_hi   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1_wa_w0_hi}} & wa_rf_wdata0_hi   )
                  ;

  //==========================================================================
  // x1_byp_reg1_lo carries all current bypass values from all stages to
  // the reg1 lo read channel at X1.
  //
  x1_byp_reg1_lo  = x1_r1_lo_byp_wa
                  | ( {`npuarc_DATA_SIZE{r1_lo_no_byp}}       & alu_shift_src2    )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1_ca_w1_hi}} & ca_byp_data1_hi   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1_x2_w0}}    & x2_byp_data0      )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1_x3_w0}}    & x3_byp_data0      )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1_ca_w0_lo}} & ca_byp_data0_lo   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1_ca_w1_lo}} & ca_byp_data1_lo   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1_ca_w0_hi}} & ca_byp_data0_hi   )
                  ;

  //==========================================================================
  // r0_hi_wa_byp is asserted whenever the HR0 read channel should receive
  // a bypassed result from WA.
  //
  r0_hi_wa_byp    = fwd_x1_r0h_wa_w0_lo
                  | fwd_x1_r0h_wa_w0_hi
                  | fwd_x1_r0h_wa_w1_lo
                  | fwd_x1_r0h_wa_w1_hi
                  ;
  
  //==========================================================================
  // r0_hi_no_byp is asserted whenever the HR0 read channel is not required
  // to receive a bypassed value from any legal bypass point. In this case,
  // the current HR0 operand value is valid, and should be forwarded
  // to the X2 stage.
  //
  r0_hi_no_byp    = !(  r0_hi_wa_byp
                      | fwd_x1_r0h_x2_w0
                      | fwd_x1_r0h_x3_w0
                      | fwd_x1_r0h_ca_w0_lo
                      | fwd_x1_r0h_ca_w0_hi
                      | fwd_x1_r0h_ca_w1_lo
                      | fwd_x1_r0h_ca_w1_hi
                    )
                  ;

  //==========================================================================
  // x1_r0_hi_byp_wa carries all current bypass values from the WA stage to
  // the reg0 hi read channel at X1.
  //
  x1_r0_hi_byp_wa = `npuarc_DATA_SIZE'h0
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0h_wa_w0_lo
                                | fwd_x1_r0h_wa_w0_hi}} & wa_rf_wdata0_hi   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0h_wa_w1_lo
                                | fwd_x1_r0h_wa_w1_hi}} & wa_rf_wdata1_hi   )
                  ;

  //==========================================================================
  // x1_byp_reg0_hi carries all current bypass values from all stages to
  // the reg0 hi read channel at X1.
  //
  x1_byp_reg0_hi  = x1_r0_hi_byp_wa
                  | ( {`npuarc_DATA_SIZE{r0_hi_no_byp}}        & x1_src2_r         )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0h_x2_w0}}    & x2_byp_data0      )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0h_x3_w0}}    & x3_byp_data0      )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0h_ca_w0_lo
                                | fwd_x1_r0h_ca_w0_hi}} & ca_byp_data0_hi   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r0h_ca_w1_lo
                                | fwd_x1_r0h_ca_w1_hi}} & ca_byp_data1_hi   )
                  ;

  //==========================================================================
  // r1_hi_wa_byp is asserted whenever the HR1 read channel should receive
  // a bypassed result from WA.
  //
  r1_hi_wa_byp    = fwd_x1_r1h_wa_w0_lo
                  | fwd_x1_r1h_wa_w1_lo
                  | fwd_x1_r1h_wa_w0_hi
                  | fwd_x1_r1h_wa_w1_hi
                  ;

  //==========================================================================
  // r1_hi_no_byp is asserted whenever the HR1 read channel is not required
  // to receive a bypassed value from any legal bypass point. In this case,
  // the current HR1 operand value is valid, and should be forwarded
  // to the X2 stage.
  //
  r1_hi_no_byp    = !(  r1_hi_wa_byp 
                      | fwd_x1_r1h_ca_w1_hi
                      | fwd_x1_r1h_x2_w0
                      | fwd_x1_r1h_x3_w0
                      | fwd_x1_r1h_ca_w0_lo
                      | fwd_x1_r1h_ca_w0_hi
                      | fwd_x1_r1h_ca_w1_lo
                    )
                  ;

  //==========================================================================
  // x1_r1_hi_byp_wa carries all current bypass values from the WA stage to
  // the reg1 hi read channel at X1. Any value forwarded to r1h, that is due
  // to a dependency with the low half of a 64-bit write port, is always
  // available on both the upper and lower 32-bit halves of the port. 
  // That allows this bypass network to avoid the separate inclusion of
  // both lower and upper halves of such 64-bit write ports, when configured.
  // 
  //
  r1h_is_wa0_hi   = fwd_x1_r1h_wa_w0_lo | fwd_x1_r1h_wa_w0_hi;
  r1h_is_wa1_hi   = fwd_x1_r1h_wa_w1_lo | fwd_x1_r1h_wa_w1_hi;
  
  x1_r1_hi_byp_wa = `npuarc_DATA_SIZE'd0
                  | ( {`npuarc_DATA_SIZE{r1h_is_wa0_hi}}       & wa_rf_wdata0_hi   )
                  | ( {`npuarc_DATA_SIZE{r1h_is_wa1_hi}}       & wa_rf_wdata1_hi   )
                  ;

  //==========================================================================
  // x1_byp_reg1_hi carries all current bypass values from all stages to
  // the reg1 hi read channel at X1.
  //
  x1_byp_reg1_hi  = x1_r1_hi_byp_wa
                  | ( {`npuarc_DATA_SIZE{r1_hi_no_byp}}        & x1_src3_r         )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1h_x2_w0}}    & x2_byp_data0      )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1h_x3_w0}}    & x3_byp_data0      )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1h_ca_w0_lo
                                | fwd_x1_r1h_ca_w0_hi}} & ca_byp_data0_hi   )
                  | ( {`npuarc_DATA_SIZE{fwd_x1_r1h_ca_w1_lo
                                | fwd_x1_r1h_ca_w1_hi}} & ca_byp_data1_hi   )
                  ;




  //==========================================================================
  
  x1_next_src0    = (x1_retain & x1_rf_renb0_r)
                  ? x1_r0_lo_byp_wa
                  : x1_src0_nxt
                  ;

  x1_next_src1    = (x1_retain & x1_rf_renb1_r)
                  ? x1_r1_lo_byp_wa
                  : x1_src1_nxt
                  ;
  
  x1_next_src2    = (x1_retain & (x1_store_r | x1_rf_renb0_64_r))
                  ? (   x1_store_r
                      ? x1_r1_lo_byp_wa
                      : x1_r0_hi_byp_wa
                    )
                  : x1_src2_nxt
                  ;

  x1_next_src3    = (x1_retain & x1_rf_renb1_64_r)
                  ? x1_r1_hi_byp_wa
                  : x1_src3_nxt
                  ;
  
  //==========================================================================
  // Select the operand inputs for the MP1 stage of the multiplier pipeline
  // or the FPU pipeline, where configured.
  //
  mp1_src0_nxt    = x1_byp_reg0_lo;
  mp1_src1_nxt    = x1_byp_reg1_lo;
  mp1_src2_nxt    = x1_rf_renb0_64_r ? x1_byp_reg0_hi : x1_byp_reg0_lo;
///        `else
///   mp1_src2_nxt    = x1_byp_reg0_lo;
  mp1_src3_nxt    = x1_rf_renb1_64_r ? x1_byp_reg1_hi : x1_byp_reg1_lo;
///         `else
///   mp1_src3_nxt    = x1_byp_reg1_lo;

  //==========================================================================
  // pre-compute the exected sign of the 32x32 multiplier product as this is 
  // needed in CA to determine whether overflow occurred.
  //
  i_prod_sign = mp1_src0_nxt[31] ^ mp1_src1_nxt[31];

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the Arithmetic and Logic Unit (ALU)                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_alu u_alb_alu (

  ////////// Input values for the ALU operation //////////////
  //
  .alu_src1             (x1_src0_r            ),
  .alu_src2             (x1_src1_r            ),
  .carry_in             (x2_zncv_r[`npuarc_C_FLAG]   ),
  .x1_link_addr_r       (x1_src3_r            ),

  ////////// Microcode control signals for the ALU ///////////
  //
  .x1_add_op_r          (x1_add_op_r          ),
  .x1_mov_op_r          (x1_mov_op_r          ),
  .x1_or_op_r           (x1_or_op_r           ),
  .x1_and_op_r          (x1_and_op_r          ),
  .x1_xor_op_r          (x1_xor_op_r          ),

  .x1_min_op_r          (x1_min_op_r          ),
  .x1_max_op_r          (x1_max_op_r          ),
  .x1_abs_op_r          (x1_abs_op_r          ),

  .x1_simple_shift_op_r (x1_simple_shift_op_r ),
  .x1_barrel_shift_op_r (x1_barrel_shift_op_r ),
  .x1_with_carry_r      (x1_with_carry_r      ),
  .x1_force_cin_r       (x1_force_cin_r       ),
  .x1_inv_src1_r        (x1_inv_src1_r        ),
  .x1_inv_src2_r        (x1_inv_src2_r        ),
  .x1_bit_op_r          (x1_bit_op_r          ),
  .x1_mask_op_r         (x1_mask_op_r         ),
  .x1_src2_mask_sel_r   (x1_src2_mask_sel_r   ),
  .x1_signed_op_r       (x1_signed_op_r       ),
  .x1_half_size_r       (x1_half_size_r       ),
  .x1_byte_size_r       (x1_byte_size_r       ),
  .x1_left_shift_r      (x1_left_shift_r      ),
  .x1_rotate_op_r       (x1_rotate_op_r       ),
  .x1_src2_sh1_r        (x1_src2_sh1_r        ),
  .x1_src2_sh2_r        (x1_src2_sh2_r        ),
  .x1_src2_sh3_r        (x1_src2_sh3_r        ),
  .x1_norm_op_r         (x1_norm_op_r         ),
  .x1_swap_op_r         (x1_swap_op_r         ),
  .x1_setcc_op_r        (x1_setcc_op_r        ),
  .x1_link_r            (x1_link_r            ),
  .x1_dslot_r           (x1_dslot_r           ),
  .x1_cc_field_r        (x1_cc_field_r[2:0]   ),

  ////////// Result outputs from the ALU operation ///////////
  //
  .alu_shift_src2       (alu_shift_src2       ),
  .alu_sum_no_cin       (alu_sum_no_cin       ),
  .alu_result           (x1_alu_result        ),
  .alu_z_out            (alu_zncv[`npuarc_Z_FLAG]    ),
  .alu_n_out            (alu_zncv[`npuarc_N_FLAG]    ),
  .alu_c_out            (alu_zncv[`npuarc_C_FLAG]    ),
  .alu_v_out            (alu_zncv[`npuarc_V_FLAG]    ),
  .adder_lessthan       (adder_lessthan       ),
  .alu_brcc_cond        (alu_brcc_cond        )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the Address Generator Unit (agu) module                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_agu u_alb_agu (
  ////////// Input values for the AGU operation //////////////////////////////
  //
  .agu_src1             (agu_src1             ),
  .agu_src2             (agu_src2             ),

  ////////// Microcode control signals for the AGU ///////////////////////////
  //
  .x1_src2_sh1_r        (x1_src2_sh1_r        ),
  .x1_src2_sh2_r        (x1_src2_sh2_r        ),
  .x1_pre_addr_r        (x1_pre_addr_r        ),
  .x1_mov_op_r          (x1_mov_op_r          ),

  ////////// Control signals for the AGU bank sel ///////////////////////////
  //
  .x1_byte_size_r      (x1_byte_size_r        ), 
  .x1_half_size_r      (x1_half_size_r        ), 
  .x1_double_size_r    (x1_double_size_r      ),
  ////////// Address output from the AGU /////////////////////////////////////
  //
  .agu_addr0            (agu_addr0            ),
  .agu_addr1            (x1_mem_addr1         ),
  
  ////////// Memory bank output from the AGU //////////////////////////////////
  //
  .agu_bank_sel_lo      (x1_bank_sel_lo       ),
  .agu_bank_sel_hi      (x1_bank_sel_hi       )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Logic for the non-ALU data-path in the Exec1 stage                       //
//                                                                          //
//  In this process the x2_src0_nxt and x2_src1_nxt result outputs are      //
//  defined, and the validity of the three Execute-stage data outputs is    //
//  determined by x1_src0_pass, x1_src1_pass and x1_addr_pass.              //
//  There are several cases to consider:                                    //
//                                                                          //
//   (a). Passing x1_src0_r to x2_src0_nxt, when needed as the first        //
//        operand of a MIN, MAX or ABS instruction.                         //
//                                                                          //
//   (b). Passing the write data value from x1_src2_r to the x2_src0_nxt    //
//        output, for ST and EX instructions.                               //
//                                                                          //
//   (c). Passing the write data value from x1_src3_r to the x2_src1_nxt    //
//        output, for 64-bit ST instructions.                               //
//                                                                          //
//   (d). Passing the branch or jump target from x1_src2_r to the           //
//        x2_src0_nxt output. This is needed in order to set the BTA        //
//        register correctly if the current branch/jump has a delay slot    //
//        instruction.                                                      //
//                                                                          //
//   (e). Passing the target of an LPcc instruction, held in x1_src2_r, to  //
//        the x2_src0_nxt output, in order to later set LP_END if the LPcc  //
//        condition is true, or to set BTA if the condition is false.       //
//                                                                          //
//   (f). Passing a link address to x2_res_r, when needed as the            //
//        fall-thru target of a conditional branch or jump instruction,     //
//        or when needed as the next LP_START value resulting from the      //
//        current LPcc instruction. The fall-thru address of every branch,  //
//        jump or LPcc instruction is passed to X1 via the x1_src3_nxt      //
//        input to this module.                                             //
//                                                                          //
//   (g). Passing the auxiliary address from x1_src0_r to x2_src0_nxt       //
//        when an LR or SR instruction is taking place. At the same time,   //
//        the auxiliary address will also be present in x1_aux_addr_r, from //
//        where it will be routed directly to the aux_regs module.          //
//                                                                          //
//   (h). Passing the AGU address to x1_byp_data0 for all memory operations //
//        that specify an address-register update in their addressing mode. //
//                                                                          //
//   (i). Passing SR write data from the x1_src1_r to x2_src1_nxt, for      //
//        subsequent use further down the pipeline.                         //
//                                                                          //
//   (j). Passing x1_src1_r to x2_src1_nxt, when needed as the second       //
//        operand of a MIN, MAX or ABS instruction, or as the operand for   //
//        FLAG, TRAP, and SLEEP instructions.                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : res_sel_PROC

  //==========================================================================
  // Decode the conditions under which each source data value is required at
  // each of the data outputs of the Execute stage.
  //
  x1_is_branch  = x1_loop_op_r
                | x1_bcc_r
                | x1_jump_r
                | x1_brcc_bbit_r
                | x1_rtie_op_r
                | x1_btab_op_r
                ;

  x1_is_mem_op  = x1_load_r
                | x1_store_r
                ;

  x1_is_aux_op  = x1_sr_op_r
                | x1_lr_op_r
                ;

  x1_needs_src2 = x1_flag_op_r
                | x1_sleep_op_r
                | x1_trap_op_r
                ;

  //==========================================================================
  // The x1_sel_src2 signal determines whether the x1_src2_r value should 
  // be selected as the store data, or whether the bypassed reg1 (lo) value
  // should be selected. The x1_src2_r value is selected only if there is no
  // bypass through the reg1 channel, as this then represents the most 
  // up-to-date store data value. 
  //
  x1_sel_src2   = x1_store_r & r1_lo_no_byp
                ;

  //==========================================================================
  // Select the next values for x2_src0_nxt
  //
  x2_src0_nxt   = (!x1_sr_op_r & x1_lr_op_r)
                ? x1_src3_r 
                : (   (x1_store_r & x1_double_size_r)
                    ? x1_byp_reg1_hi 
                    : x1_byp_reg0_lo
                  )
                ;

  //==========================================================================
  // Select the next values for x2_src1_nxt. This is provided by x1_src2_r
  // when performing an LPcc, branch, jump, or store instructions. Otherwise,
  // it is provided by the bypassed src1 operand, unless the X1 instruction
  // defines a 64-bit result and has a false predicate. In that case, the
  // upper 32 bits of the false-result must be passed to x2_src1_nxt.
  //
  x1_false_res_hi = x1_rf_renb0_64_r ? x1_byp_reg0_hi : x1_byp_reg1_hi;
  x2_src1_nxt     = x1_sel_src2
                  ? x1_src2_r
                  : (   (x1_rf_wenb0_64_r & (~q_cond))
                      ? x1_false_res_hi
                      : x1_byp_reg1_lo
                    )
                  ;
/*
  //==========================================================================
  // Select the alu_result as the result of X1 when the condition of
  // the instruction has evaluated to be true, or when the instruction
  // requires the calculation of link (derived from X1_LINK_ADDR_R in
  // the X1 ALU) or when fast eia instruction.
  //
  x1_sel_alu    = q_cond | (x1_link_r & (~x2_done_nxt)) | x1_eia_fast_op_r;
*/
  //==========================================================================
  // Select the next conditional result for an ALU.<cc> instruction
  // This is done in two parts; firstly, the bypassed src0 or src1 is 
  // selected as the potential result value (depending on whether there is
  // a first source operand or not). Secondly, this result value is selected
  // over the ALU result if the conditional result is false.
  //
  x1_false_res  = x1_rf_renb0_r ? x1_byp_reg0_lo : x1_byp_reg1_lo;
  x1_cond_res   = 
                  x1_eia_res_valid && q_cond ?
                                                 x1_eia_res_data : 
                  (q_cond | (x1_link_r & (~x2_done_nxt))) ?
                                                 x1_alu_result   :
                  x1_false_res;

  //==========================================================================
  // Select the next values for x1_byp_data0
  //
  agu_address              = `npuarc_DATA_SIZE'd0;
  agu_address[`npuarc_ADDR_RANGE] = agu_addr0;
  x1_byp_data0             = x1_is_mem_op ? agu_address : x1_cond_res;

  //==========================================================================
  // Select the x1_mem_addr0 output to the DMP. This depends on the addressing
  // mode, and shall be the computed AGU result agu_addr0 unless a pre-update
  // addressing mode is used, in which case agu_src1 shall be used.
  // Furthermore, when performing an EX instruction, the memory address is
  // given by the second source operand (this is indicated by the ucode bit
  // x1_mov_op_r being set). Thus, x1_base_addr is first selected from the
  // two AGU source values, and then the memory address is selected from 
  // either the base address or the computed address.
  //
  x1_base_addr  = x1_is_branch 
                ? x1_src3_r
                : (x1_mov_op_r   ? agu_src2     : agu_src1)
                ;
                
  x1_mem_addr0  = (x1_pre_addr_r | x1_is_branch) ? x1_base_addr : agu_addr0;

  //==========================================================================
  // Those are the components of the x1 mem addr uesd in the DMP aliasing 
  // predictor
  //

  x1_addr_base     = agu_src1;
  x1_addr_offset   = x1_pre_addr_r ? {`npuarc_ADDR_SIZE{1'b0}} : agu_src2;
  
  //==========================================================================
  // The following three signals define when the outgoing x1_byp_data0,
  // x2_src0_nxt and x2_src1_nxt busses contain valid new data.
  // These are used in the Exec2 stage to gate the updates to x2_res_r,
  // x2_src0_r and x2_src1_r respectively.
  //
  x1_res_pass   = (x1_pass & (x1_rf_wenb0_r | x1_dslot_r))
                | db_active
                ;

  //==========================================================================
  // x1_src0_pass determines whether a relavant value is passed from X1 to X2
  // in relation to the x2_src0_nxt operand.
  //
  x1_src0_pass  = x1_pass
                & (   (~x1_opds_in_sa_r)    // possible late-evaluating insn
                    | x1_slow_op_r
                    | x1_is_mem_op
                    | x1_is_aux_op
                    | x1_is_branch
                    | x1_cc_byp_64_haz_r
                    | db_active
                  )
                ;

  //==========================================================================
  // x1_src1_pass determines whether a relavant value is passed from X1 to X2
  // in relation to the x2_src1_nxt operand.
  //
  x1_src1_pass  = x1_pass
                & (   (~x1_opds_in_sa_r)    // possible late-evaluating insn
                    | x1_slow_op_r 
                    | x1_is_mem_op
                    | x1_is_aux_op
                    | x1_is_branch
                    | x1_needs_src2
                    | db_active
                    | x1_rf_wenb0_64_r
                  )
                ;

  x1_addr_pass  = x1_pass & (x1_is_mem_op | x1_is_branch);

  //==========================================================================
  // X1 provides the re-encoded memory operand size field <zz> from the
  // current instruction, for use by the DMP. (00-b, 01-h, 10-w, 11-dw)
  //
  // Logically this is equivalent to:
  //
  //   x1_size_r     = { ((~x1_half_size_r) & (~x1_byte_size_r)),
  //                     (x1_half_size_r | x1_double_size_r)
  //                   };
  //
  casez ({   x1_half_size_r
           , x1_byte_size_r
           , x1_double_size_r
         })
    3'b1??:  x1_size_r = 2'b01; // 16-bit operation
    3'b01?:  x1_size_r = 2'b00; //  8-bit operation
    3'b001:  x1_size_r = 2'b11; // 64-bit operation
    3'b000:  x1_size_r = 2'b10; // 32-bit operation
    default: x1_size_r = 2'b10; // 32-bit operation
  endcase

end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process for handling conditional operations.                //
//                                                                          //
// The Z, N, C and V flags are derived from the speculative Exec2-stage     //
// flag register x2_zncv, corresponding to the flag result of the most      //
// recently executed instruction. The 'x1_cond' reg contains 1'b1 if this   //
// instruction should commit (if predicated), or branch/jump if it is a     //
// conditional control-transfer instruction.                                //
//                                                                          //
// Logic to resolve the outcome of a Bcc, Jcc or LPcc instruction.          //
//                                                                          //
// It also handles the RTIE instruction, which basically is a jump to a     //
// previously saved address.                                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


always @*
begin : x1_cond_PROC

  z_flag = x2_zncv_r[`npuarc_Z_FLAG];
  n_flag = x2_zncv_r[`npuarc_N_FLAG];
  c_flag = x2_zncv_r[`npuarc_C_FLAG];
  v_flag = x2_zncv_r[`npuarc_V_FLAG];

  q_cond = 1'b1;                                     // Default is unconditional

  //==========================================================================
  // Decode the condition code field for Bcc, Jcc and predication
  //
  case ( x1_q_field_r )
    5'h00: q_cond = 1'b1;                            // Always (default)
    5'h01: q_cond = z_flag;                          // Zero
    5'h02: q_cond = ~z_flag;                         // Non-Zero
    5'h03: q_cond = ~n_flag;                         // Positive
    5'h04: q_cond = n_flag;                          // Negative
    5'h05: q_cond = c_flag;                          // Carry set
    5'h06: q_cond = ~c_flag;                         // Carry clear
    5'h07: q_cond = v_flag;                          // Overflow set
    5'h08: q_cond = ~v_flag;                         // Overflow clear
    5'h09: q_cond = (n_flag & v_flag & (~z_flag))
              | ((~n_flag) & (~v_flag) & (~z_flag)); // > signed
    5'h0a: q_cond = (n_flag == v_flag);              // >= signed
    5'h0b: q_cond = (n_flag != v_flag);              // < signed
    5'h0c: q_cond = z_flag | (n_flag != v_flag);     // <= signed
    5'h0d: q_cond = (~c_flag) & (~z_flag);           // > unsigned
    5'h0e: q_cond = c_flag | z_flag;                 // <= unsigned
    5'h0f: q_cond = (~n_flag) & (~z_flag);           // Positive non-zero
    default: q_cond = eia_ext_cond;                  // EIA extension condition
  endcase

  //==========================================================================
  // Determine whether a branch should be taken or not-taken at X1.
  // A branch is taken under any of the following conditions:
  //
  //  (a). a true condition for Bcc, Jcc, BLcc or JLcc; or a JLI_S or EI_S.
  //  (b). a false condition for LPcc, instructions;
  //  (c). an RTIE instruction;
  //  (d). a true condition for BRcc or BBITn.
  //  (e). the X1 instruction is in an execution slot of an EI_S instruction
  //  (f). a BI or BIH instruction (which is unconditional)
  //  (g). there is a ZOL loop back to LP_START
  //
  // The outcome of a BRcc or BBITn instruction is indicated by the
  // 'alu_brcc_cond' signal, produced by the ALU.
  //
  // The x1_br_direction signal is derived speculatively, and may not be
  // used unless all relevant flag dependencies are resolved already
  // in the X1 stage.
  //
  x1_br_taken     = (   (q_cond    & (x1_bcc_r | x1_jump_r))  // (a) Bcc,Jcc,EI
                      | ((~q_cond) & x1_loop_op_r)            // (b) LPcc false
                      | x1_rtie_op_r                          // (c) RTIE
                      | (alu_brcc_cond & x1_brcc_bbit_r)      // (d) BRcc
                      | x1_in_eslot_r                         // (e) in EI slot
                      | x1_btab_op_r                          // (f) BI,BIH
                    );

  //==========================================================================
  // Determine the branch direction at X1, as used in the misprediction
  // interface to indicate taken versus not-taken outcomes. 
  // This signal is set under either of two conditions:
  // 
  // (a). a branch, jump, rtie or eslot instruction is at X1 and is taken
  // (b). a zero-overhead loop-back condition was true at X1.
  //
  x1_br_direction = x1_br_taken                               // (a) br or jmp
//                  | x1_zol_lp_jmp                             // (b) ZOL jump; ZOL is postponed to CA
                  ;
                  
  //==========================================================================
  // The conditional predicate of the X1 instruction is true if the 
  // instruction is valid and the q_cond result is 1.
  //
  x1_cond         = q_cond & x1_valid_r;
  
  //==========================================================================
  // Determine the branch or jump target, for use in BTA misprediction logic. 
  // This should be the target if X1 has any kind of predictable branch
  // or jump operation, otherwise it should be the fall-through address
  // given by x1_src3_r.
  // The x1_br_target expression does not include the target of a BI or BIH
  // instruction, as the misprediction detection for those instructions is 
  // based on a comparison of jump index and a precomputed expected index.
  // That actual jump target of BI and BIH is produced by alu_sum_no_cin,
  // and is included in the logic for x2_target_nxt, after x1_br_target.
  // However, for BI and BIH instructions, the x1_br_target value will be
  // always sourced from x1_src2_r. This is the predicted scaled index of
  // the BI,BIH instruction. This value is relied up on later in the pipeline
  // in case of a late BI,BIH misprediction in the Commit stage. The
  // predicted scaled index is passed down the pipeline via the x2_target_r,
  // x3_target_r, and ca_target_r pipeline registers, for BI,BIH instructions.
  //
  x1_br_target    = (x1_predictable_r == 1'b0)
                  ? x1_src3_r[`npuarc_PC_RANGE]
                  : (   x1_jump_r
                      ? (   x1_opd3_sel_r
                          ? x1_src1_r[`npuarc_PC_RANGE]
                          : x1_src0_r[`npuarc_PC_RANGE]
                        )
                      : x1_src2_r[`npuarc_PC_RANGE]
                    )
                  ;

  //==========================================================================
  // Determine whether the scaled BI, BIH index register has the same value
  // as the index value required for a correct BTA prediction of the X1-stage 
  // BI, BIH instruction. The x1_src2_r input register will contain the
  // value (x1_pred_bta_r - x1_restart_pc_r), which was pre-computed in SA.
  // If this is equal to the scaled index register value in x1_src1_r, then
  // the predicted BTA was correct. If not, then a BTA misprediction occurred.
  //
  x1_bi_bta_mpd   = x1_btab_op_r
                  & (x1_src2_r[`npuarc_PC_RANGE] != alu_shift_src2[`npuarc_PC_RANGE])
                  ;

  //==========================================================================
  // Determine the actual branch or jump target for use in determining
  // the restart address in case of a misprediction. 
  // For BI, BIH instructions that have their index register available in
  // X1, the target will be the result of adding the next PC with the scaled
  // index register, which is available in alu_sum_no_cin.
  // For all other cases, the x2_target_nxt value is given by the x1_br_target
  // value obtained above. This includes the case where a BI, BIH instruction
  // cannot resolve its BTA prediction in X1. For this case we must pass the
  // predicted scaled index from x1_src2_r, via x1_br_target, to x2_target_nxt.
  //
  x2_target_nxt   = x1_br_taken
                  ? (   (x1_btab_op_r & x1_bta_ready)
                      ? alu_sum_no_cin[`npuarc_PC_RANGE]
                      : (x1_is_eslot_r ? x1_pred_bta_r : x1_br_target)
                    )
                  : x1_br_target
                  ;

  x1_br_fall_thru = x1_restart_pc_r;

end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process to calculate the next value of the X2 ZNCV register //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg [`npuarc_ZNCV_RANGE]        zncv_nxt;
reg                      is_flag_op;
reg [`npuarc_ZNCV_RANGE]        ar_zncv_nxt;


always @*
begin: x1_zncv_PROC

  //==========================================================================
  // Identify [k]flag instruction at X1. The 'signed_op' ucode bit is
  // used to identify the seti/clri flag-modifying instruction
  // sub-class that does not apply in this instance.
  //
  is_flag_op        = (x1_flag_op_r & q_cond & (~x1_signed_op_r))
                    ;

  //==========================================================================
  // Mux flag producers to generate definitive X1 flag set.
  //

  x1_alu_zncv_sel   = 
                      x1_eia_fast_op_r ? x1_eia_res_flags :
                      alu_zncv;

  x1_zncv           = (x1_alu_zncv_sel        & {`npuarc_ZNCV_BITS{~is_flag_op}})
                    | (x1_src1_r[`npuarc_ZNCV_RANGE] & {`npuarc_ZNCV_BITS{ is_flag_op}})
                    ;


  //==========================================================================
  // The state of speculative flags retained by X2 are calculated as a
  // composite of the current flag producing instruction, versus the
  // forwarding of downstream CA stage flag producing updates, versus
  // the retention of the current flag values.
  //
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  Functionally independent signals
  zncv_nxt          = (x1_zncv                           & fwd_zncv_x1   )
                    | (wa_aux_status32_nxt[`npuarc_P_ZNCV_FLAG] & fwd_zncv_x1_ca)
                    | (x2_zncv_r                         & fwd_zncv_x1_x2)
                    ;
// spyglass enable_block Ac_conv01
  //==========================================================================
  // When fwd_zncv_x1_ar is asserted, the x2_zncv_nxt flags will be defined
  // by the architectural committed flags. This allows speculative flags 
  // to be rolled-back to their committed values when a pipeline flush occurs.
  // If any flag has a pending retirement update, then the ar_zncv_nxt
  // signal for that flag should take its value from ca_retire_flags.
  // This will ensure, that the x2_zncv_r bits are updated with the
  // retiring flag value if the retirement coincides with a pipeline flush, 
  //
  ar_zncv_nxt       = ( dp_retire_zncv & ca_retire_flags                )
                    | (~dp_retire_zncv & ar_aux_status32_r[`npuarc_ZNCV_RANGE] )
                    ; 
  
  //==========================================================================
  // The value of the next flags at X2 are derived by:
  //
  //   (1) On flush, the new flag values are set to the known
  //       architectural values, unless the instruction present in X1
  //       or X2 is a (potentially flag-modifying) dslot instruction
  //       of the restart initiating instruction in WA.
  //
  //   (2) On entry to an interrupt or exception prologue, the flags
  //       are set to {user_mode_r, arch. ncv} before interrupt.
  //
  //   (3) In the tail of an exception epilogue the flag values are
  //       set to the prior (pre-exception) architectural as retained
  //       by ERSTATUS.
  //
  //   (4) Otherwise, the new flag values as calculated by the
  //       X1-/CA-stage ALU.
  //
  casez ({   fwd_zncv_x1_ar
           , x1_uop_commit_r
           , x1_uop_prol_r
           , x1_uop_epil_r
           , x1_uop_excpn_r
         })
    5'b1????: x2_zncv_nxt  = ar_zncv_nxt;                           // (1)
    5'b0110?: x2_zncv_nxt  = {ar_aux_user_mode_r, 
                              ar_aux_status32_r[`npuarc_N_FLAG: `npuarc_V_FLAG]}; // (2)
    5'b01011: x2_zncv_nxt  = ar_aux_erstatus_r[`npuarc_ZNCV_RANGE];        // (3)
// spyglass disable_block Ac_conv01
// SMD: Multiple synchronizers converging on flop
// SJ:  Signals are independent 
    default:  x2_zncv_nxt  = zncv_nxt;                              // (4)
// spyglass enable_block Ac_conv01
  endcase

end // block: x1_zncv_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process for controlling the update of X1 input registers    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : x1_ctrl_PROC

  //==========================================================================
  // x1_valid_nxt:  1 => X1 stage receives a valid instruction
  //  This is asserted when the SA stage asserts sa_pass, to indicate that
  //  an instruction is available and is not going to be squashed.
  //
  x1_valid_nxt  = sa_pass;

  //==========================================================================
  // x1_code_cg0 enables the update of x1_code_r
  //
  // x1_code_cg0 is asserted when:
  //
  //  (a). the X1 stage is enabled to receive new input, and
  //  (b). either x1_valid_r or x1_valid_nxt
  //
  // Condition (b) ensures that the X1 ucode vector is updated whenever a
  // new instruction arrives or an exising instruction leaves. It does not
  // clock the ucode vector when it is already empty and nothing is arriving.
  //
  x1_code_cg0     = x1_enable
                  & (   x1_valid_r
                      | x1_valid_nxt
                      | sa_error_branch_r
                    )
                  ;

  //==========================================================================
  // x1_grab_src<n> enables the update of x1_src<n>_r when the X1 instruction
  // is retained in the X1 stage. This is necessary to allow bypassed values
  // from WA to be captured by the X1-stage input registers when the X1-stage
  // instruction is stalled.
  //
  // x1_src0_r must capture WA bypass whenever r0_lo_wa_byp is asserted,
  // as any register operand in src0 is always from channel LR0. 
  //
  x1_grab_src0    = x1_retain & r0_lo_wa_byp;
                  
  // x1_src1_r must capture WA bypass whenever a non-Store instruction
  // asserts r1_lo_wa_byp. Store instructions never have a bypassable
  // regiser operand in x1_src1_r, as it contains a literal address offset.
  //
  x1_grab_src1    = x1_retain & r1_lo_wa_byp & (~x1_store_r);

  // x1_src2_r must capture WA bypass under two distinct conditions, and in
  // each case it accepts bypass from up to two different register bypass
  // channels (depending on configuration).
  // 
  //  (a). Store instructions at X1 take WA bypass into x1_src2_r from the
  //       LR1 channel when r1_lo_wa_byp is asserted.
  //
  //  (b). Non-store instructions at X1 taken WA bypass into x1_src2_r from
  //       the HR0 channel when r0_hi_wa_byp is asserted.
  //
  x1_grab_src2    = x1_retain 
                  & (   (r1_lo_wa_byp &   x1_store_r )
                      | (r0_hi_wa_byp & (~x1_store_r))
                    )
                  ;
                  
  // x1_src3_r must capture WA bypass when 64-bit input operands are configured
  // and there is a valid bypass from WA through the HR1 register channel.
  //
  x1_grab_src3    = x1_retain & r1_hi_wa_byp;

  //==========================================================================
  // x1_src<n>_cg0 enables the update of x1_src<n>_r
  //
  // x1_src<n>_cg0 is asserted when:
  //
  //  (a). the X1 stage is enabled to receive new input, and the SA stage 
  //       indicates there is a relevant value on x1_src<n>_nxt, or
  // 
  //  (b). the X1-stage instruction is retained, and the WA-stage has the
  //       bypass value required by that sourc input of the stalled instruction.
  //       This specific condition is indicated by x1_grab_src<n>.
  //
  x1_src0_cg0     = (x1_enable & sa_src0_pass)          // (a)
                  | x1_grab_src0                        // (b)
                  ;
  
  x1_src1_cg0     = (x1_enable & sa_src1_pass)          // (a)
                  | x1_grab_src1                        // (b)
                  ;
  
  x1_src2_cg0     = (x1_enable & sa_src2_pass)          // (a)
                  | x1_grab_src2                        // (b)
                  ;
  
  x1_src3_cg0     = (x1_enable & sa_src3_pass)          // (a)
                  | x1_grab_src3                        // (b)
                  ;

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process to define the ucode sent to the X2 stage            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : x1_ucode_PROC

  //==========================================================================
  // Start by copying the X1-stage microcode to the microcode
  // output wires. Unless we further modify these signals within this
  // block they will be forwarded intact to the X2 stage.
  //
  ucode_out               = x1_code_r[`npuarc_X2_CODE_WIDTH-1:0];

  //==========================================================================
  // Defeat the predicate microcode bit if x1_cond is false and the X1 
  // instruction cannot evalaute in X1 due to an unresolved flag dependency.
  // 
  ucode_out[`npuarc_PREDICATE_RANGE] = x1_predicate_r & (x1_cond | x1_no_eval);
  
  //==========================================================================
  // Retain the outgoing cc_byp_64_haz microcode bit in the active state
  // if, and only if, the X1 condition is false.
  //
  ucode_out[`npuarc_CC_BYP_64_HAZ_RANGE] = x1_cc_byp_64_haz_r & (~q_cond);
  
  //==========================================================================
  // Define the outgoing prod_sign microcode bit, for use by 32x32 MAC
  // instructions at the Commit stage.
  //
  ucode_out[`npuarc_PROD_SIGN_RANGE] = i_prod_sign;


  //==========================================================================
  // If there is an error branch, then set the outgoing ucode signals for
  // all register write enables to 0. This is to prevent the error branch
  // instruction becoming the source of a RAW or WAW dependency with itself
  // when reissued, or with any other subsequent instruction.
  //
  if (x1_error_branch_r == 1'b1)
  begin
    ucode_out[`npuarc_RF_WENB0_RANGE]        = 1'b0;
    ucode_out[`npuarc_RF_WENB1_RANGE]        = 1'b0;
    ucode_out[`npuarc_RF_WENB0_64_RANGE]     = 1'b0;
    ucode_out[`npuarc_RF_WENB1_64_RANGE]     = 1'b0;
  end

  //==========================================================================
  // Kill the control subset of microcode bits if the X1-stage
  // instruction is not being passed on to the X2 stage.
  //
  if (x1_pass == 1'b0)
  begin
`include "npuarc_ucode_kill_x2.v"
  end

  //==========================================================================
  // The invalid_instr microcode bit is special, as is must be cleared
  // when not passing forward a new instruction (x1_pass == 1'b0), but
  // must not be cleared when an instruction is simply disabled by
  // x1_cond (i.e., when x1_cond is 1'b0).
  //
  if (x1_pass == 1'b0)
  begin
    ucode_out[`npuarc_INVALID_INSTR_RANGE] = 1'b0;
    ucode_out[`npuarc_RGF_LINK_RANGE]      = 1'b0;
  end

end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous blocks defining X1 stage pipeline input registers            //
//                                                                          //
// Pipeline registers for incoming data, updated whenever a new instruction //
// is received from the Dispatch Pipe.                                      //
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Input registers associated with source operand 0 are updated when the    //
// x1_src0_cg0 signal is asserted.                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x1_src0_reg_PROC
  if (rst_a == 1'b1)
    begin
      x1_src0_r       <= `npuarc_DATA_SIZE'd0;
    end
  else if (x1_src0_cg0 == 1'b1)
    begin
      x1_src0_r       <= x1_next_src0;
    end
end

// spyglass enable_block STARC05-1.3.1.3 
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Input registers associated with source operand 1 are updated when the    //
// x1_src0_cg1 signal is asserted.                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x1_src1_reg_PROC
  if (rst_a == 1'b1)
    begin
      x1_src1_r       <= `npuarc_DATA_SIZE'd0;
    end
  else if (x1_src1_cg0 == 1'b1)
    begin
      x1_src1_r       <= x1_next_src1;
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// The x1_src2_r pipeline register is updated only for store instructions   //
// or branch, jump and LPcc instructions. It is therefore enabled when both //
// x1_enable and sa_src2_pass are asserted. This 32-bit register is enabled //
// independently of other operand registers to save dynamic power.          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x1_src2_reg_PROC
  if (rst_a == 1'b1)
    begin
      x1_src2_r       <= `npuarc_DATA_SIZE'd0;
    end
  else if (x1_src2_cg0 == 1'b1)
    begin
      x1_src2_r       <= x1_next_src2;
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// The x1_src3_r pipeline register is updated only for store instructions   //
// or branch, jump and LPcc instructions. It is therefore enabled when both //
// x1_enable and sa_src3_pass are asserted. This 32-bit register is enabled //
// independently of other operand registers to save dynamic power.          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x1_src3_reg_PROC
  if (rst_a == 1'b1)
    begin
      x1_src3_r       <= `npuarc_DATA_SIZE'd0;
    end
  else if (x1_src3_cg0 == 1'b1)
    begin
      x1_src3_r       <= x1_next_src3;
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pipeline registers for incoming control information are updated whenever //
// the existing Execute-stage instruction exits the Execute stage.          //
// It may be replaced by a new instruction or a pipeline bubble,            //
// indicated by x1_valid_r <= 1'b0.                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x1_ctrl_regs_PROC
  if (rst_a == 1'b1)
    begin
      x1_code_r       <= `npuarc_X1_CODE_WIDTH'd0;
      x1_restart_pc_r <= `npuarc_PC_BITS'd0;
    end
  else if (x1_code_cg0 == 1'b1)
    begin
      x1_code_r       <= x1_code_nxt;
      x1_restart_pc_r <= sa_restart_pc;
    end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
assign  x2_code_nxt     =  ucode_out;
assign  x1_zncv_wen_r   = { x1_z_wen_r, x1_n_wen_r, x1_c_wen_r, x1_v_wen_r };
assign  x2_lt_flag_nxt  = adder_lessthan;
assign  x1_link_addr    = x1_src3_r[`npuarc_PC_RANGE];
assign  x1_div_kind_r   = x1_byte_size_r;    // 0 => div/u, 1 => rem/u
assign  x1_rgf_link     = x1_rgf_link_r;
assign  x2_predicate_nxt = x1_predicate_r & (x1_cond | x1_no_eval);


endmodule // alb_execute
