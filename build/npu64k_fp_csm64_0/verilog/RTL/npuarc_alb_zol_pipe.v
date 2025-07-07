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
//  ######   ####   #               #####      #    #####   ######
//      #   #    #  #               #    #     #    #    #  #
//     #    #    #  #               #    #     #    #    #  #####
//    #     #    #  #               #####      #    #####   #
//   #      #    #  #               #          #    #       #
//  ######   ####   ###### #######  #          #    #       ######

//
// ===========================================================================
//
// Description:
//
//  This module is responsible for implementing the zero-overhead loop (ZOL)
//  mechanism, and for implementing the LP_COUNT register (r60) within the
//  Albacore processor.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_zol_pipe (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,              // clock signal
  input                       rst_a,            // reset signal
  input                       db_active,        // debug unit is active

  ////////// Architectural machine state /////////////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_DATA_RANGE]    ar_aux_status32_r,// committed STATUS32 aux reg
  input      [`npuarc_DATA_RANGE]    ar_aux_lp_start_r,// LP_START aux reg
  input      [`npuarc_DATA_RANGE]    ar_aux_lp_end_r,  // LP_START aux reg 
// leda NTL_CON13C on
  ////////// Prediction information attached to SA-stage instruction /////////
  //
  input                       sa_error_branch,      // error branch at SA
  
  ////////// Prediction information attached to CA-stage instruction /////////
  //
  input                       ca_is_predicted_r,    // CA insn was predicted
  input                       ca_prediction_r,      // prediction for CA insn
  input     [`npuarc_PC_RANGE]       ca_pred_bta_r,        // predicted BTA at CA
  
  ////////// Control inputs from Dependency Pipeline /////////////////////////
  //
  input                       da_pass,          // DA instruction ready to go
  input                       sa_enable,        // SA is able to receive input
  input                       sa_pass,          // SA instruction ready to go
  input                       sa_in_dslot_r,    // SA insn was issued in dslot
  input                       x1_in_dslot_r,    // X1 insn was issued in dslot
  input                       x1_enable,        // X1 is able to receive input
  input                       x1_pass,          // X1 instruction ready to go
  input                       x2_enable,        // X2 is able to receive input
  input                       x2_pass,          // X2 instruction ready to go
  input                       x3_enable,        // X3 is able to receive input
  input                       x3_pass,          // X3 instruction ready to go
  input                       ca_enable,        // CA is able to receive input
  input                       wa_enable,        // WA is able to receive input

  ////////// Microcode inputs from each state /////////////////////////////////
  //
  input                       sa_branch_or_jump, // SA insn is a br or jump
  input                       sa_multi_op_r,    // SA is ENTER_S/LEAVE_S/RTIE
  input                       wa_wa0_lpc_r,     // WA writes to LP_COUNT
  input                       x1_loop_op_r,     // LPcc insn is at X1
  input                       x2_loop_op_r,     // LPcc insn is at X2
  input                       x3_loop_op_r,     // LPcc insn is at X3
  input                       ca_loop_op_r,     // LPcc insn is at CA
  input                       wa_loop_op_r,     // LPcc insn is at WA
  input                       ca_uop_commit_r,  // CA insn cmts multi-op
  input                       ca_uop_inprol_r,  // CA insn cmts prol
  input                       ca_cmt_brk_evt,   // CA brk commited
 
  input                       wa_uopld_lp_count,//stack pop to lp_count
  input [`npuarc_DATA_RANGE]         wa_uopld_data,    //stack data for restore 

  ////////// Indication of valid instructions at each EXU pipeline stage /////
  //
  input                       x2_valid_r,       // Exec2 stage has valid insn
  input                       x3_valid_r,       // Exec3 stage has valid insn
  input                       ca_valid_r,       // Commit stage has valid insn

  input                       x2_error_branch_r,
  input                       x3_error_branch_r,

  ////////// Instruction context from the Decode stage ///////////////////////
  //
  input     [`npuarc_RGF_ADDR_RANGE] da_rf_ra0_r,      // reg0 address at Decode
  input                       da_rf_renb0_r,    // reg0 at Decode is enabled
  //
  input     [`npuarc_RGF_ADDR_RANGE] da_rf_ra1_r,      // reg1 address at Decode
  input                       da_rf_renb1_r,    // reg1 at Decode is enabled
  input     [`npuarc_PC_RANGE]       sa_seq_pc_nxt,    // next seq PC at DA stage

  ////////// Instruction context from the Operands stage /////////////////////
  //
  input     [`npuarc_PC_RANGE]       sa_seq_pc_r,      // next seq PC at SA stage
  
  ////////// Instruction commit info from the Commit stage ///////////////////
  //
  input     [`npuarc_PC_RANGE]       ca_seq_pc_nxt,       // next seq PC at CA 
  input                       wa_cmt_norm_evt_nxt, // commit normal inst
  input                       ca_branch_evt,       // branch or jump at CA
  input                       ca_uop_inst,         // uop inst at CA
  input                       ca_error_branch_r,   // error br at CA
  ////////// Port 0 result info from the Writeback stage /////////////////////
  //
  input     [`npuarc_DATA_RANGE]     wa_rf_wdata0_lo_r,// port #0 write data
  
  ////////// Control outputs to the ZOL pipeline /////////////////////////////
  //
  output reg                  sa_zol_stall,     // SA hazard due to ZOL
  output reg                  sa_hit_lp_end,    // SA insn is at loop-end
  output reg                  sa_zol_hazard,    // ZOL creates hazard in SA

  ////////// commited LP_COUNT for stack push ////////////////////////////////
  //
  output reg [`npuarc_LPC_RANGE]     ar_lp_count_r,    // committed LP_COUNT reg

  ////////// Speculative LP_COUNT for SA stage use ///////////////////////////
  //
  output     [`npuarc_LPC_RANGE]     sa_lp_count_r,    // speculative LP_COUNT reg
   //////////////////For pct/////////////////////////////////////////////////
  output                      zol_depend_stall,

  ////////// Early misprediction outputs from the ZOL pipeline ///////////////
  //
  output reg                  x1_zol_stall,     // X1 hazard due to ZOL
  output                      x1_zol_mpd_dir,   // early ZOL mispred dir
  output reg                  x1_zol_hazard_r,  // ZOL creates hazard
  output reg                  x1_early_pred_r,  // X1 has early ZOL prediction

  ////////// Exception-raising outputs from the ZOL pipeline /////////////////
  //
  output reg                  x2_zol_ill_seq_r, // illegal inst sequence (ZOL)
  
  ////////// Late misprediction outputs from the ZOL pipeline ////////////////
  //
  output reg                  ca_hit_lp_end,    // CA insn is at loop-end
  output reg                  ca_zol_mpd_dir,   // late ZOL mispred dir
  output reg                  ca_zol_mpd_bta,   // late ZOL mispred BTA
  output reg                  ca_zol_lp_jmp,    // late ZOL loop-back
  output reg                  ca_zol_branch     
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// ZOL pipeline register declarations                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//------ SA stage ------------------------------------------------------------
//
reg                         sa_decr_lpc_r;      // decrement LP_COUNT at SA
reg                         sa_reads_lpc_r;     // SA insn reads LP_COUNT
reg                         sa_zol_maybe_ill;   // a potential illegal insn
                                                // in the last position of 
                                                // a ZOL body
reg                         sa_zol_illegal_stall;
reg                         sa_hit_lp_end_int;
reg                         sa_lpc_unclear_r;   // LP_COUNT unclear at SA

//------ X1 stage ------------------------------------------------------------
//
reg                         x1_decr_lpc_r;      // decrement LP_COUNT at X1
reg                         x1_zol_ill_seq_r;   // exception condition
reg                         x1_hit_lp_end_r;    
reg                         x1_ill_dslot;
reg                         x1_pipe_empty;
reg                         x1_lpc_unclear_r;   // LP_COUNT unclear at X1

//------ X2 stage ------------------------------------------------------------
//
reg                         x2_decr_lpc_r;      // decrement LP_COUNT at X2
reg                         x2_lpc_unclear_r;   // LP_COUNT unclear at X2

//------ X3 stage ------------------------------------------------------------
//
reg                         x3_decr_lpc_r;      // decrement LP_COUNT at X3
reg                         x3_lpc_unclear_r;   // LP_COUNT unclear at X3

//------ CA stage ------------------------------------------------------------
//
reg                         ca_decr_lpc_r;      // decrement LP_COUNT at CA
reg                         ca_lpc_unclear_r;   // LP_COUNT unclear at CA

//------ WA stage ------------------------------------------------------------
//
reg                         wa_decr_lpc_r;      // decrement LP_COUNT at WA

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Enable signals for ZOL pipeline registers                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// @zol_pipe_PROC
//
reg                         sa_decrement;       // speculatively decr LP_COUNT
reg                         ar_lpc_cg0;         // enable committed LP_COUNT

reg                         sa_ctrl_cg0;        // enable SA ctrl info
reg                         x1_ctrl_cg0;        // enable X1 ctrl info
reg                         x2_ctrl_cg0;        // enable X2 ctrl info
reg                         x3_ctrl_cg0;        // enable X3 ctrl info
reg                         ca_ctrl_cg0;        // enable CA ctrl info
reg                         wa_ctrl_cg0;        // enable WA ctrl info

reg                         sa_decr_lpc_nxt;    // next LPC decrement at SA
reg                         x1_decr_lpc_nxt;    // next LPC decrement at X1
reg                         x2_decr_lpc_nxt;    // next LPC decrement at X2
reg                         x3_decr_lpc_nxt;    // next LPC decrement at X3
reg                         ca_decr_lpc_nxt;    // next LPC decrement at CA
reg                         wa_decr_lpc_nxt;    // next LPC decrement at WA

reg                         sa_lpc_unclear_nxt; // next LPC unclear at SA
reg                         x1_lpc_unclear_nxt; // next LPC unclear at X1
reg                         x2_lpc_unclear_nxt; // next LPC unclear at X2
reg                         x3_lpc_unclear_nxt; // next LPC unclear at X3
reg                         ca_lpc_unclear_nxt; // next LPC unclear at CA


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Nets for performing ZOL calculations                                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// @zol_next_lpc_PROC
//
reg   [`npuarc_LPC_RANGE]          ar_lp_count_nxt;    // next architectural LP_COUNT


// @zol_sa_detect_PROC
//
reg                         sa_reads_lpc_nxt;   // DA insn reads LP_COUNT


// @zol_sa_mispred_PROC
//
reg                         ar_lp_end_stale;    // LP_END is stale at SA

//
reg                         x1_zol_hazard_nxt;  // ZOL creates hazard for X1
reg                         x1_zol_ill_seq_nxt; // Inst. Seq. exception

// @zol_ca_mispred_PROC
//
reg                         ca_iterates;        // ZOL loop-back at CA stage

wire  [`npuarc_PC_RANGE]           ar_lp_start_r;      // PC_RANGE version of LP_START
wire  [`npuarc_PC_RANGE]           ar_lp_end_r;        // PC_RANGE version of LP_END

assign ar_lp_start_r  = ar_aux_lp_start_r[`npuarc_PC_RANGE];
assign ar_lp_end_r    = ar_aux_lp_end_r[`npuarc_PC_RANGE];


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to define the next ZOL pipeline states and         //
// register enable signals.                                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : zol_pipe_PROC


  sa_decrement      = ( sa_seq_pc_r                == ar_lp_end_r )
                    & ( ar_aux_status32_r[`npuarc_L_FLAG] == 1'b0        )
                    & (~sa_error_branch)
                    ;

  
  //==========================================================================
  // Derive the register enables for each register of the ZOL pipeline.
  // The loop-back prediction mechanism must be disabled during debug
  // operations, and this is achieved by disabling sa_ctrl_cg0 when the
  // db_active signal is asserted. This prevents new prediction information
  // entering (and therefore propagating) down the ZOL pipeline.
  //
  sa_ctrl_cg0       = sa_enable 
                    & (~db_active)
                    ;
  x1_ctrl_cg0       = x1_enable;
  x2_ctrl_cg0       = x2_enable;
  x3_ctrl_cg0       = x3_enable;
  ca_ctrl_cg0       = ca_enable;
  wa_ctrl_cg0       = wa_enable;
  
  //==========================================================================
  // If there is a predicted jump to LP_START when sa_seq_pc_nxt is pointing
  // at LP_END, and the STATUS32.L bit is clear, then the current DA-stage
  // instruction would auto-decrement LP_COUNT.
  //
  sa_decr_lpc_nxt   = ( sa_seq_pc_nxt              == ar_lp_end_r )
                    & ( ar_aux_status32_r[`npuarc_L_FLAG] == 1'b0        )
                    & ( da_pass                    == 1'b1        )
                    ;
  
  x1_decr_lpc_nxt   = sa_decrement  & sa_pass;
  x2_decr_lpc_nxt   = x1_decr_lpc_r & x1_pass;
  x3_decr_lpc_nxt   = x2_decr_lpc_r & x2_pass;
  ca_decr_lpc_nxt   = x3_decr_lpc_r & x3_pass;

  //==========================================================================
  // If ar_lp_end_stale is asserted when an instruction is at SA, then the
  // correct detection of sa_decr_lpc_nxt cannot be guaranteed, and thhe next
  // value of sa_decr_lpc_r is unclear. The LP_COUNT hazard detection logic 
  // must be conservative about potential decrements to LP_COUNT at each of
  // the stages SA thru CA, when it is unclear whether a decrement should
  // actually take place in that stage.
  // The sa_lpc_unclear_nxt signal detects the lack of clarity in the 
  // sa_decr_lpc_nxt signal, and this propagates down the pipeline to CA.
  //
  sa_lpc_unclear_nxt  = ar_lp_end_stale  & da_pass;
  x1_lpc_unclear_nxt  = sa_lpc_unclear_r & sa_pass;
  x2_lpc_unclear_nxt  = x1_lpc_unclear_r & x1_pass;
  x3_lpc_unclear_nxt  = x2_lpc_unclear_r & x2_pass;
  ca_lpc_unclear_nxt  = x3_lpc_unclear_r & x3_pass;
  
  //==========================================================================
  // Determine whether the next WA instruction would decrement the LP_COUNT
  // register through the ZOL end-of-loop semantics. This is not a predicted
  // or speculative condition, but a definitive indicator. This condition is
  // true when the CA-stage instruction is at the last instruction position
  // of a ZOL, indicated by ca_hit_lp_end, and a regular instruction commits
  // during this cycle. This must exclude debug instructions and on the commit
  // of multi-ops.
  // LP_COUNT is decremented when the next PC hits LP_END.
  // There is no exclusion for branch events, including E-slots.
  // If there is a branch event in the last position of a ZOL, incl E-slot,
  // the branch event takes precedence and there is no ZOL jump, but
  // still LP_COUNT is decremented.
  //
  wa_decr_lpc_nxt   = ca_hit_lp_end
                    & wa_cmt_norm_evt_nxt
                    & (~ca_uop_commit_r)
                    & (~ca_uop_inprol_r)
                    & (~ca_cmt_brk_evt)
                    ;
  
  //==========================================================================
  // Derive the register enable for the committed LP_COUNT register.
  // The architectural LP_COUNT register must be updated under any of the 
  // following conditions:
  //
  //  (a). a committed write to LP_COUNT, indicated by wa_wa0_lpc_r
  //  (d). an instruction exits the WA stage when the wa_decr_lpc_r bit
  //       is set.
  //
  ar_lpc_cg0        = (   wa_enable
                        & (wa_wa0_lpc_r | wa_decr_lpc_r)
                      )
                    | wa_uopld_lp_count 
                    ;
  
end // block: zol_pipe_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to define stall on read of speculative LP_COUNT    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg sa_lpc_read_stall;
reg sa_lpc_uncertain;
reg sa_lpc_hazard;

always @*
begin: zol_stall_PROC

  //==========================================================================
  // If the potential to decrement LP_COUNT at X1, X2, X3 or CA is unclear,
  // then the sa_lpc_uncertain signal is asserted. This stalls any read of
  // LP_COUNT, as a regular source operand, at the SA stage. 
  // This uncertainty may happen if LP_COUNT is read during the first iteration
  // of a ZOL, before the LP instruction has updated the architectural state
  // of LP_START, LP_END and STATUS32.L.
  //
  sa_lpc_uncertain  = x1_lpc_unclear_r
                    | x2_lpc_unclear_r
                    | x3_lpc_unclear_r
                    | ca_lpc_unclear_r
                    ;

  //==========================================================================
  // If the STATUS32.L flag is clear, and there is an implicit decrement of
  // LP_COUNT at X1, X2, X3, CA or WA, then there is a definite hazard on
  // reading LP_COUNT at SA. In this case, the sa_lpc_hazard signal is asserted
  // and any attempt to read LP_COUNT as a regular operand in SA will stall 
  // until this condition has been resolved.
  //
  sa_lpc_hazard     = (     (ar_aux_status32_r[`npuarc_L_FLAG] == 1'b0)
                         && (   x1_decr_lpc_r
                              | x2_decr_lpc_r
                              | x3_decr_lpc_r
                              | ca_decr_lpc_r                   
                              | wa_decr_lpc_r
                            )
                      )
                    ;                

  //==========================================================================
  // The sa_lpc_read_stall signal is asserted whenever there is a RAW hazard
  // on LP_COUNT due to a downstream implicit modification of LP_COUNT.
  // LP_COUNT can be modified under several possible conditions:
  //
  // (A).  Writing to LP_COUNT as an explicit destination of an instruction
  //       These hazards are detected separately by the alb_dep_pipe module.
  //
  // (B).  Implicit decrements of LP_COUNT at the end of a ZOL.
  //       To detect implicit decrements, three cases must be considered:
  //
  //  (1). There is an LP instruction at X1, X2, X3 or CA, and therefore
  //       the value of LP_END and STATUS32.L are stale. This is indicated
  //       by the ar_lp_end_stale signal.
  //
  //  (2). There is a known decrement of LP_COUNT at X1, X2, X3, CA or WA,
  //       meaning that the architecturally-committed LP_COUNT register is
  //       not up to date. This condition arises for instructions that
  //       read LP_COUNT as a source operand within a few instructions of
  //       the loop end.
  //
  //  (3). At least one of the instructions at X1, X2, X3 or CA entered
  //       the X1 stage at a time when there was an LP instruction at
  //       X1, X2, X3 or CA, and therefore the values of LP_END and STATUS32.L
  //       were stale. This meant that the potential to decrement LP_COUNT
  //       downstream of SA exists, but cannot be known for certain.
  //       This is indicated by the sa_lpc_uncertain signal.
  //
  sa_lpc_read_stall = sa_reads_lpc_r
                    & (   ar_lp_end_stale   // (1)
                        | sa_lpc_hazard     // (2)
                        | sa_lpc_uncertain  // (3)
                      )
                    ;

end



always @*
begin : zol_sa_detect_PROC

  //==========================================================================
  // Detect whether there is a WAW hazard between an implicit decrement
  // of LP_COUNT by the current SA instruction (i.e. when it is at the end
  // of the loop) and any downstream instruction that has not yet updated
  // the speculative copy of LP_COUNT at sa_lp_count_r.
  //==========================================================================
  // Detect whether the next SA instruction (currently in DA) reads
  // LP_COUNT as a source register.
  //
  sa_reads_lpc_nxt  = (da_rf_renb0_r & (da_rf_ra0_r == `npuarc_LP_COUNT_REG))
                    | (da_rf_renb1_r & (da_rf_ra1_r == `npuarc_LP_COUNT_REG))
                    ;
  
  //==========================================================================
  // A ZOL-related stall is required at the SA stage if the SA-stage
  // instruction needs to read LP_COUNT as an instruction operand, and
  // there is a pending down-stream modification to LP_COUNT.
  //   
  sa_zol_stall = sa_lpc_read_stall
               | sa_zol_illegal_stall
               ;

end // block: zol_sa_detect_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to define next LP_COUNT values at SA and WA        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : zol_next_lpc_PROC

  //==========================================================================
  // Define the next committed LP_COUNT value. This is specified such that it 
  // always represents the next value for LP_COUNT, even if LP_COUNT would
  // not be updated in the current cycle. This allows ar_lp_count_nxt to be
  // used to set the speculative sa_lp_count_r value when wa_restart_r is
  // asserted (for whatever reason).
  //
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction
// leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  ar_lp_count_nxt must wrap around when decremented. Carry-out is ignored.
  casez ({
           wa_uopld_lp_count
         , wa_wa0_lpc_r
         , 1'b0 
         , wa_decr_lpc_r
        })
  4'b1???:  ar_lp_count_nxt = wa_uopld_data;
  4'b01??:  ar_lp_count_nxt = wa_rf_wdata0_lo_r;
  4'b0001:  ar_lp_count_nxt = ar_lp_count_r - 1;
  default:  ar_lp_count_nxt = ar_lp_count_r;
  endcase

// leda BTTF_D002 on
// leda W484 on 

end // block: zol_next_lpc_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to detect ZOL mispredictions at SA                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : zol_sa_mispred_PROC

  //==========================================================================
  // Detect when the SA instruction is at the loop-end position.
  // This is indicated by an equivalence between the next sequential PC 
  // at the SA stage and the architectural LP_END auxiliary register,
  // when the STATUS32.L flag is set to 0.
  //
  sa_hit_lp_end_int   = ( sa_seq_pc_r                == ar_lp_end_r )
                      & ( ar_aux_status32_r[`npuarc_L_FLAG] == 1'b0        )
                      & ( db_active                  == 1'b0        )
                      ;

  // sa_hit_lp_end_int is sa_hit_lp_end used internally in this module
  // sa_hit_lp_end is sa_hit_lp_end exported to SA.
  //
  sa_hit_lp_end       = 1'b0;
 
  //==========================================================================
  // An early loop-back prediction, at X2, can only be made if the speculative
  // LP_END and/or LP_START auxiliary registers are not rendered potentially
  // stale by a downstream LPcc instruction or SR instruction (which may
  // modify LP_END or LP_START). Sometimes this condition will prevent early
  // prediction when LP_START and LP_END are not modified, but it will never
  // give a false positive result.
  //
  // Auxiliary register writes to LP_END and LP_START are serialized so we 
  // don't need to include them in ar_lp_end_stale.
  //
  ar_lp_end_stale     = x1_loop_op_r 
                      | x2_loop_op_r 
                      | x3_loop_op_r 
                      | ca_loop_op_r 
                      | wa_loop_op_r
                      ;

  //==========================================================================
  // ZOL hazards for branch resolution:
  // The following hazards are used to prevent early error branches in SA and 
  // branch resolution in X1.
  // The hazard occurs when:
  //
  //  (1) a branch is in the last position of a ZOL body, or
  //
  //  (2) when lp_end is stale, and therefore we don't know if we're at the 
  //      last position of a ZOL.
  //
  sa_zol_hazard       = sa_hit_lp_end_int                         // (1)
                      | ( ar_lp_end_stale                         // (2)
                          & ( ar_aux_status32_r[`npuarc_L_FLAG] == 1'b0 )
                        )
                      ;

  x1_zol_hazard_nxt   = sa_zol_hazard
                      & (~sa_error_branch)
                      & (sa_pass)
                      ;

  //==========================================================================
  // Determine whether an early prediction (or misprediction) of the ZOL
  // loop-back can be made at the X2 stage. This is possible only when both
  // the speculative LP_COUNT register and the architectural LP_START and
  // LP_END auxiliary registers are not rendered stale by downstream insns.
  //
  //==========================================================================
  // Detect the Illegal Instruction Sequence that occurs when the last 
  // position of a zero-overhead loop is occupied by a an instruction that
  // is not permitted in that position.
  //
  // This includes the following illegal cases:
  //  (a). a branch or jump, with or without a delay-slot, and taken or 
  //       not taken, including: Bcc, BLcc, BRcc, Jcc, JLcc, BBIT0, BBIT1,
  //       BI, BIH, etc
  //  (b). an EI_S instruction (optional)
  //  (c). a JLI_S instruction (optional)
  //  (d). a LPcc instruction
  //  (e). an E-slot (EI_S target instruction).
  //  (f). a delay slot of a taken branch or jump insn
  //  (g). a micro-op insn: ENTER_S/LEAVE_S/RTIE
  //
  sa_zol_maybe_ill    = sa_branch_or_jump    // (a), (b), (c), (d), (e)
                      | sa_multi_op_r        // (g)
                      ;

  //==========================================================================
  // Signal x1_pipe_empty indicates if the pipe is drained downstream from X1.
  //
  x1_pipe_empty    = ~( (x2_valid_r & (~x2_error_branch_r))
                      | (x3_valid_r & (~x3_error_branch_r))
                      | (ca_valid_r & (~ca_error_branch_r))
                      );

  //==========================================================================
  // Stalls related to illegal instruction sequences:
  // It is illegal to have certain instructions in the last position of a 
  // ZOL body. To check if we're in the last position we need to compare the 
  // next sequential PC with LOOP_END. We do that already in SA with 
  // sa_hit_lp_end_int. If lp_end is stale, then we take stall cycles and 
  // wait until sa_hit_lp_end_int is valid. That is only necessary in case 
  // of a potential illegal instruction.
  // A delay slot of a taken branch is not allowed at the end of a ZOL,
  // so that is one of the cases for which we need to stall in case of
  // a stale LOOP_END.
  //
  sa_zol_illegal_stall = ar_lp_end_stale 
                       & (sa_zol_maybe_ill | sa_in_dslot_r) 
                       & ( ar_aux_status32_r[`npuarc_L_FLAG] == 1'b0 )
                       ;

  x1_zol_stall = x1_hit_lp_end_r & x1_in_dslot_r & (~x1_pipe_empty);

  x1_ill_dslot = x1_hit_lp_end_r & x1_in_dslot_r & x1_pipe_empty & ar_aux_status32_r[`npuarc_DE_FLAG];

  //==========================================================================
  // Check for instructions that are illegal at the last position of a ZOL
  // coinciding with the SA instruction being at the end of the loop.
  //
  x1_zol_ill_seq_nxt  = sa_hit_lp_end_int
                      & sa_zol_maybe_ill
                      & (~ca_uop_inprol_r)
                      ;

end // block: zol_sa_mispred_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to detect ZOL mispredictions at CA                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : zol_ca_mispred_PROC

  //==========================================================================
  // Detect when the CA instruction is at the loop-end position.
  // This is indicated by an equivalence between the next sequential PC 
  // at the SA stage and the architectural LP_END auxiliary register,
  // when the STATUS32.L flag is set to 0.
  //
  ca_hit_lp_end     = ( ca_seq_pc_nxt              == ar_lp_end_r )
                    & ( ar_aux_status32_r[`npuarc_L_FLAG] == 1'b0        )
                    & ( db_active                  == 1'b0        )
                    ;
  
  //==========================================================================
  // Detect when the LP_COUNT register value at the CA stage is not equal to 1,
  // thereby indicating that another loop iteration will be required when
  // the PC reaches the loop-end position. There are three cases to consider:
  // 
  // (a). LP_COUNT is the destination of write port #0 at the WA stage
  //      - in this case CA iterates if the value written is not equal to 1.
  // 
  // (b). LP_COUNT is decremented by a loop-end condition on the WA-stage
  //      instruction, and it is not written by the WA-stage instruction.
  //      - in this case CA iterates if LP_COUNT is not equal to 2 before
  //      the decrement takes place.
  // 
  // (c). LP_COUNT is not modified by the instruction at the WA stage, either
  //      explicitly or implicitly.
  //      - in this case CA iterates if LP_COUNT is not equal to 1.
  //
  casez ( {wa_wa0_lpc_r, wa_decr_lpc_r} )
  2'b1?:   ca_iterates = (wa_rf_wdata0_lo_r != `npuarc_DATA_SIZE'd1);    // (a)
  2'b01:   ca_iterates = (ar_lp_count_r     != `npuarc_LPC_SIZE'd2);     // (b)
  default: ca_iterates = (ar_lp_count_r     != `npuarc_LPC_SIZE'd1);     // (c)
  endcase

  //==========================================================================
  // Detect late mispredictions for a ZOL loop-back, in the CA stage.
  // ZOL loop-back predictions are of branch type BR_CONDITIONAL.
  //
  // There are two forms of misprediction that we must detect:
  //  
  //  (a). An incorrect prediction of the loop termination condition, which
  //       typically occurs when the LP_COUNT value reaches 1 but the IFU
  //       does not predict that correctly.
  //
  //  (b). An incorrect branch target address when a ZOL loop-back is
  //       correctly predicted to be taken. This typically occurs when
  //       branch aliasing occurs, or if LP_START has changed since the
  //       last prediction of a loop-closing branch at the current ar_pc_r
  //       location.
  
  //==========================================================================
  // A late ZOL branch outcome misprediction is asserted if the current
  // CA instruction is at the last position of a ZOL, and it was predicted
  // incorrectly by the BPU, or if there was no prediction and the loop-back
  // should take place.
  // 
  ca_zol_mpd_dir      = ca_hit_lp_end                               // (a)
                      & (~ca_branch_evt)
                      & (~ca_uop_inst)
                      & (   (ca_prediction_r != ca_iterates)
                          | (~ca_is_predicted_r)
                        )
                      ;

  //==========================================================================
  // A late ZOL branch target misprediction is asserted if the current
  // CA instruction is at the last position of a ZOL, and it was predicted
  // by the BPU, and the loop jump was predicted taken, but the predicted
  // target was predicted incorrectly.
  //
  ca_zol_mpd_bta      = ca_hit_lp_end                               // (b)
                      & ca_iterates
                      & (~ca_branch_evt)
                      & (~ca_uop_inst)
                      & ca_is_predicted_r
                      & ca_prediction_r
                      & (ca_pred_bta_r != ar_lp_start_r)
                      ;
                      
  //==========================================================================
  // Define the direction of outcome for any late ZOL pseudo-branch, for onward
  // transmission to the prediction pipeline and the Misprediction Interface.
  //
  ca_zol_lp_jmp       = ca_iterates
                      & ca_hit_lp_end
                      & (~ca_branch_evt) // (1) disable lp_jmp if another branch
                      & (~ca_uop_inst)
                      & (~ca_error_branch_r)
                      ;

  //==========================================================================
  // Signal ca_zol_branch indicates if there is a ZOL phantom branch, 
  // taken or not taken. This is used to commit the ZOL phantom branch.
  // That commit must occur both when the branch is taken or not taken.
  // Suppress ZOL if there is another taken branch in the last position of the
  // ZOL body.
  //
  ca_zol_branch       = ca_hit_lp_end
                      & (~ca_branch_evt)
                      & (~ca_uop_inst)
                      ;
                      
end // block: zol_ca_mispred_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define state updates to pipelined control signals //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : zol_ctrl_regs_PROC

  if (rst_a == 1'b1)
    begin
    sa_decr_lpc_r     <= 1'b0;
    x1_decr_lpc_r     <= 1'b0;
    x2_decr_lpc_r     <= 1'b0;
    x3_decr_lpc_r     <= 1'b0;
    ca_decr_lpc_r     <= 1'b0;
    sa_lpc_unclear_r  <= 1'b0;
    x1_lpc_unclear_r  <= 1'b0;
    x2_lpc_unclear_r  <= 1'b0;
    x3_lpc_unclear_r  <= 1'b0;
    ca_lpc_unclear_r  <= 1'b0;
    x1_zol_ill_seq_r  <= 1'b0;
    x1_hit_lp_end_r   <= 1'b0;
    x2_zol_ill_seq_r  <= 1'b0;
    x1_zol_hazard_r   <= 1'b0;
    sa_reads_lpc_r    <= 1'b0;
    wa_decr_lpc_r     <= 1'b0;
    x1_early_pred_r   <= 1'b0;
    end
  else
    begin

    if (sa_ctrl_cg0 == 1'b1)
      begin
      sa_decr_lpc_r     <= sa_decr_lpc_nxt;
      sa_reads_lpc_r    <= sa_reads_lpc_nxt;
      sa_lpc_unclear_r  <= sa_lpc_unclear_nxt;
      end

    if (x1_ctrl_cg0 == 1'b1)
      begin
      x1_decr_lpc_r     <= x1_decr_lpc_nxt;
      x1_lpc_unclear_r  <= x1_lpc_unclear_nxt;
      x1_zol_ill_seq_r  <= x1_zol_ill_seq_nxt;
      x1_zol_hazard_r   <= x1_zol_hazard_nxt;
      x1_hit_lp_end_r   <= sa_hit_lp_end_int;
      x1_early_pred_r   <= 1'b1;
      end

    if (x2_ctrl_cg0 == 1'b1)
      begin
      x2_decr_lpc_r     <= x2_decr_lpc_nxt;
      x2_lpc_unclear_r  <= x2_lpc_unclear_nxt;
      x2_zol_ill_seq_r  <= x1_zol_ill_seq_r | x1_ill_dslot;
      end

    if (x3_ctrl_cg0 == 1'b1)
      begin
      x3_decr_lpc_r     <= x3_decr_lpc_nxt;
      x3_lpc_unclear_r  <= x3_lpc_unclear_nxt;
      end

    if (ca_ctrl_cg0 == 1'b1)
      begin
      ca_decr_lpc_r     <= ca_decr_lpc_nxt;
      ca_lpc_unclear_r  <= ca_lpc_unclear_nxt;
      end

// spyglass disable_block FlopEConst
// SMD: Enable pin is always high/low 
// SJ:  Done on purpose

    if (wa_ctrl_cg0 == 1'b1)
      begin
      wa_decr_lpc_r     <= wa_decr_lpc_nxt;
      end
    end
// spyglass enable_block FlopEConst
end // block: zol_ctrl_regs_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define committed LP_COUNT register at AR          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : ar_lp_count_reg_PROC

  if (rst_a == 1'b1)
    ar_lp_count_r         <= `npuarc_LPC_SIZE'd0;
  else if (ar_lpc_cg0 == 1'b1)
    ar_lp_count_r         <= ar_lp_count_nxt;

end // block: ar_lp_count_reg_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Assignment of output wires                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign x1_zol_mpd_dir   = 1'b0;
assign sa_lp_count_r    = `npuarc_LPC_SIZE'd0;

//////////////////////For pct//////////////////////////////////////
assign zol_depend_stall = 1'b0
                        | sa_lpc_read_stall
                        ;

endmodule
