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

module npuarc_alb_status32 (
  ////////// Machine Architectural State /////////////////////////////////////
  //
 // leda NTL_CON37 off
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_DATA_RANGE]    ar_aux_status32_r,  //

  input      [`npuarc_DATA_RANGE]    ar_aux_erstatus_r,  //

  input                       ar_aux_user_mode_r, //
 // leda NTL_CON13C on 
 // leda NTL_CON37 on

  ////////// General inputs from the Commit-Stage ////////////////////////////
  //
  input                       ca_valid_r,         // CA stage is valid
  input                       ca_pass,            // CA commit
  input                       ca_stall,           // CA stage is stalled


// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_DATA_RANGE]    ca_src1_r,          //
  input                       ca_uop_active_r,
// leda NTL_CON13C on 
  input      [`npuarc_ZNCV_RANGE]    ca_zncv_r,          //
  input      [`npuarc_ZNCV_RANGE]    alu_result_zncv,    //
  input                       ca_br_delayed,      //
  input                       commit_normal_evt,  // Commit Normal Insn
  input                       commit_uop_evt,     // Commit Multi-Op Insn

  input                       ca_cmt_brk_evt,     // Commit of BRK insn.
  input                       ca_triple_fault_set, // Triple fault event
  input                       ca_cmt_sleep_evt,   // Commit of SLEEP insn.
  input                       ca_cond,            // CA instruction predicate
  input                       ca_cmt_isi_evt,     // Instruction Step
  input                       db_active_r,        //

  input                       single_step_active_r, // DEBUG register IS bit
  input                       ar_tags_empty_r,
  output reg                  ca_finish_sgl_step,

  input                       ca_async_halt_evt,  //
  input                       ca_async_run_evt,   //
  input                       ca_done_r,          // insn was executed at X1
  input                       ca_predicate_r,     // evaluated predicate
  input                       ca_q_cond,          // CA-derived predicate
  input                       ca_flag_op_r,       //
  input                       ca_byte_size_r,     //
  input                       ca_signed_op_r,     //
  input                       ca_cache_byp_r,     //
  input                       ca_loop_op_r,       //
  input                       ca_trap_op_r,       //
  input                       ca_z_wen_r,         //
  input                       ca_n_wen_r,         //
  input                       ca_c_wen_r,         //
  input                       ca_v_wen_r,         //
  input                       ca_ei_op_r,         //
  input                       ca_0_grad_flags,    //
  input                       ca_grad_req,        //
  input     [`npuarc_ZNCV_RANGE]     ca_retire_flags,    //
  input     [`npuarc_ZNCV_RANGE]     dp_retire_zncv,     //
  input                       ca_retire_ack,      //

  //
  input                       ca_scond,           //

  ////////// AUX SR Interface ////////////////////////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input     [`npuarc_DATA_RANGE]     wa_sr_data_r,       // AUX WA wdata
// leda NTL_CON13C on 
  input                       wa_status32_wen,    // AUX WA sel. STATUS32

  ////////// UOP load Interface ////////////////////////////////////////////////
  //
  input      [`npuarc_DATA_RANGE]    wa_rf_wdata1_lo_nxt,   //
  input                       wa_uopld_status32_nxt, //
  input                       wa_debug_wen,       // AUX WA sel. DEBUG

  ////////// Exception Interface /////////////////////////////////////////////
  //
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  unused port range
  input      [`npuarc_INTEVT_RANGE]  excpn_evts,         // Excpn. Events
  input      [`npuarc_INTEVT_RANGE]  int_evts,           // Interrupts Events

// leda NTL_CON13C on
// leda NTL_CON37 on
  ////////// Instruction status to CA ////////////////////////////////////////
  //
  output                      ca_kflag_op,        // CA insn is FLAG
  output                      ca_is_flag,         // CA KFLAG is enabled
  
  ////////// STATUS32 update to WA ///////////////////////////////////////////
  //
  output reg                  ca_flag_upt,        // insn would update flags
  output                      ca_in_kflag,        // Kernel Flag update
  output     [`npuarc_PFLAG_RANGE]   wa_aux_status32_nxt,// new STATUS32 value
  output                      wa_aux_uop_flag_pass,// pass flag for leave instruction
  output                      wa_aux_flags_pass,  //
  output                      wa_aux_status32_pass// pass new STATUS32
);

// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems

// @sm_h_PROC:
//
reg                           halt_machine;   //
reg                           unhalt_machine; //
reg                           ca_h_sm;        //

// @sm_PROC:
//
reg [`npuarc_ZNCV_RANGE]             zncv_wen;       // bit-wise flag writes at CA
reg                           ca_early_flag;  // flag update in CA from X1 ALU
reg                           ca_late_flag;   // flag update in CA from CA ALU
reg [`npuarc_ZNCV_RANGE]             x1_zncv_wen;    // early ALU bit-wise flag writes
reg [`npuarc_ZNCV_RANGE]             ca_zncv_wen;    // late ALU  bit-wise flag writes
reg [`npuarc_ZNCV_RANGE]             pre_ca_zncv;    // flags computed before CA stage
reg [`npuarc_ZNCV_RANGE]             act_ca_zncv;    // actual new flags for CA insn
reg [`npuarc_E_FLAG]                 ca_e_sm;        //
reg                           ca_ae_sm;       //
reg                           ca_de_sm;       //
reg                           ca_u_sm;        //
reg [`npuarc_ZNCV_RANGE]             ca_zncv_sm;     //
reg                           ca_l_sm;        //
reg                           ca_dz_sm;       //
reg                           ca_sc_sm;       //
reg                           ca_eih_sm;       //
reg                           ca_es_sm;       //
reg                           ca_ad_sm;       //
reg                           ca_us_sm;       //
reg                           ca_ie_sm;       //

// @wa_aux_status32_PROC
//
reg [`npuarc_PFLAG_RANGE]            status32_nxt;   //
reg [1:0]                     status32_pass_vec;
reg                           flags_pass;     //

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @is_PROC: Combinatorial process to identify relevant flag-modifying      //
// instruction types that are potential alias'.                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                 kill_ca_insn;
reg                 in_kernel_mode;
reg                 sleep_kernel_mode;
reg                 is_flag;
reg                 kflag_op;
reg                 is_kflag;
reg                 is_sleep;
reg                 is_seti;
reg                 is_clri;
reg                 is_sr;
reg                 is_swi;
//reg                 is_trap;
reg                 is_loop;

always @*
begin: is_PROC

  // Signal indicating whether the instruction in CA should not be
  // allowed to update STATUS32 because of some asserting event. This
  // should be derived similar to CA_RESTART, but hopefully somewhat
  // faster.
  //
  kill_ca_insn      = ca_cmt_isi_evt
//                    | ca_cmt_brk_evt
                    ;


  // The machine is operating in kernel-mode
  //
  in_kernel_mode    = ~ar_aux_status32_r[`npuarc_U_FLAG]
                    ;


  // SLEEP, WEVT and WLFC are operating in kernel-mode
  //
  sleep_kernel_mode = in_kernel_mode | ar_aux_status32_r[`npuarc_US_FLAG]
                    ;
  // CA-stage instruction is a FLAG
  //
  is_flag           = ca_valid_r
                    & ca_flag_op_r
                    & ca_cond
                    & (~ca_signed_op_r)
                    & (~ca_cache_byp_r)
                    & (~kill_ca_insn)
                    ;

  // CA-stage instruction is a KFLAG, regardless of predicate condition
  //
  kflag_op          = ca_valid_r
                    & ca_flag_op_r
                    & (~ca_signed_op_r)
                    & ca_cache_byp_r
                    & (~kill_ca_insn)
                    ;
                    
  // CA-stage KFLAG is decoded, and has true condition
  //
  is_kflag          = kflag_op
                    & ca_cond
                    & (~kill_ca_insn)
                    ;

  // CA-stage Sleep EVT needs to update Interrupt status
  //
  is_sleep          = ca_cmt_sleep_evt
                    & ca_src1_r[4]              // 
                    & (~kill_ca_insn)
                    ;
  // CA-stage instruction is a SETI
  //
  is_seti           = ca_valid_r
                    & ca_flag_op_r
                    & ca_signed_op_r
                    & ca_cache_byp_r
                    & (~kill_ca_insn)
                    ;

  // CA-stage instruction is a CLRI
  //
  is_clri           = ca_valid_r
                    & ca_flag_op_r
                    & ca_signed_op_r
                    & (~ca_cache_byp_r)
                    & (~kill_ca_insn)
                    ;

  // CA-stage LPcc is decoded, and has true condition
  //
  is_loop           = ca_valid_r
                    & ca_loop_op_r
                    & ca_cond
                    & (~kill_ca_insn)
                    ;

  // From PRM, Section 3.3.21 STATUS32: "The STATUS32 register cannot
  // be written by a regular SR instruction regardless of the
  // operating mode."
  //
  is_sr             = wa_status32_wen
                    & db_active_r
                    ;

  // Current instruction is SWI, which causes a pre-commit exception.
  //
  is_swi            =  ca_valid_r
                    &  ca_trap_op_r
                    & (~ca_byte_size_r)
                    & (~kill_ca_insn)
                    ;
/*
  //
  //
  is_trap           = ca_valid_r
                    & ca_trap_op_r
                    & ca_byte_size_r
                    & (~kill_ca_insn)
                    ;
*/
  // Assert ca_flag_upt if the ZNCV flags will be updated by the current
  // CA instruction if it commits without graduating for later retirement.
  //
  ca_flag_upt       = is_sr
                    | (    ca_valid_r
                         & (    (ca_flag_op_r & (~ca_signed_op_r))
                              | ca_z_wen_r
                              | ca_n_wen_r
                              | ca_c_wen_r
                              | ca_v_wen_r
                           )
                       )
                    ;
                    
end // block: is_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @sm_h_PROC: Combinatorial process to derive state updates to STATUS32.H  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: sm_h_PROC


  // =========================================================================
  // A single stepping instruciton is finished when
  // 1. Single stepping instruction is committed & Tags are empty
  // 2. Single stepping is active & UOP has finished with 
  //    any pending graduated instructions are retired
  // 
  ca_finish_sgl_step = 
                      (ca_cmt_isi_evt & ar_tags_empty_r)
                    | (  single_step_active_r & (!ca_uop_active_r)
                       & ca_retire_ack
                      )
                    ;

  // =========================================================================
  // Non-architectural/Non-programmatic invoked machine halt
  // conditions to override any further updates to STATUS32.H
  //
  halt_machine      = ca_cmt_brk_evt
                    | ca_triple_fault_set
                    | ca_async_halt_evt
                    | ca_finish_sgl_step
                    ;



  unhalt_machine    = ca_async_run_evt
                    & ar_aux_status32_r[`npuarc_H_FLAG]
                    ;

  // =========================================================================
  // -- STATUS32.H - SR (debug), kFLAG, FLAG
  //
  casez ({   halt_machine
           , unhalt_machine
           , is_sr
           , (is_flag | is_kflag) & in_kernel_mode
           ,   1'b0
             | wa_debug_wen
         })
    5'b1????: ca_h_sm    = 1'b1;
    5'b01???: ca_h_sm    = 1'b0;
    5'b001??: ca_h_sm    = wa_sr_data_r[`npuarc_H_FLAG];
    5'b0001?: ca_h_sm    = ca_src1_r[`npuarc_H_FLAG];
    5'b00001: ca_h_sm    = (   ar_aux_status32_r[`npuarc_H_FLAG]
                             & (~wa_sr_data_r[`npuarc_DEBUG_IS]))
                         | wa_sr_data_r[`npuarc_DEBUG_FH]
                         ;
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
    default: ca_h_sm     = ar_aux_status32_r[`npuarc_H_FLAG];
// spyglass enable_block Ac_conv01
  endcase

end // block: sm_h_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @sm_PROC: Combinatorial process to calculate the next value of flag      //
// instructions.                                                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: sm_PROC

  // =========================================================================
  // -- STATUS32.E - SR (debug), kFLAG, SETI, CLRI
  //
  casez ({   ca_h_sm
           , is_sr
           , (  ((is_flag | is_kflag) & in_kernel_mode)
              | (is_sleep & sleep_kernel_mode))
           ,   1'b0
             | (is_seti & (|ca_src1_r[5:4]))
         })
    4'b?_1??: ca_e_sm    = wa_sr_data_r[`npuarc_E_FLAG];
    4'b0_01?: ca_e_sm    = (is_sleep == 1'b1)
                         ? ca_src1_r[3:0]
                         : ca_src1_r[`npuarc_E_FLAG]
                         ;
    4'b0_001: ca_e_sm    = ca_src1_r[3:0];
    default:  ca_e_sm    = ar_aux_status32_r[`npuarc_E_FLAG];
  endcase

  // =========================================================================
  // -- STATUS32.AE - SR (debug), kFLAG
  //
  casez ({   ca_h_sm
           , is_sr
           , is_kflag & in_kernel_mode
         })
    3'b?_1?:  ca_ae_sm    = wa_sr_data_r[`npuarc_AE_FLAG];
    3'b0_01:  ca_ae_sm    = ca_src1_r[`npuarc_AE_FLAG];
    default:  ca_ae_sm    = ar_aux_status32_r[`npuarc_AE_FLAG];
  endcase

  // =========================================================================
  // -- STATUS32.DE
  //
  casez ({   ca_h_sm
           , is_sr
           ,   commit_normal_evt
             | commit_uop_evt
         })
    3'b?_1?: ca_de_sm    = wa_sr_data_r[`npuarc_DE_FLAG];
    3'b0_01: ca_de_sm    = ca_br_delayed & (~ar_aux_status32_r[`npuarc_DE_FLAG]);
    default: ca_de_sm    = ar_aux_status32_r[`npuarc_DE_FLAG];
  endcase

  // =========================================================================
  // -- STATUS32.U
  //
  casez ({
             is_sr
         })
    1'b1:    ca_u_sm     = wa_sr_data_r[`npuarc_U_FLAG];
    default: ca_u_sm     = ar_aux_user_mode_r;
  endcase

  // =========================================================================
  // -- STATUS32.{Z,N,C,V}
  //
  //--------------------------------------------------------------------------
  // zncv_wen is a vector that indicates whether the current CA-stage insn 
  // would write to each of the ZNCV flags, as a flag-setting side-effect,
  // if the instruction commits. This excludes updates due to FLAG, KFLAG, 
  // or debug SR operations to STATUS32.
  //
  zncv_wen      = {ca_z_wen_r, ca_n_wen_r, ca_c_wen_r, ca_v_wen_r};
  
  //--------------------------------------------------------------------------
  // x1_zncv_wen is a vector that indicates whether the current CA-stage insn
  // would write to each of the ZNCV flags, as a flag-setting side-effect,
  // based on the early evaluation of a flag-setting ALU operation in X1.
  // It is created by gating zncv_wen with ca_early_flag. 
  // If graduation of flag-setting instructions is supported, then 
  // x1_zncv_wen bits are disabled by bits that may be set in dp_retire_zncv
  // when a retirement is acknowledged.
  //
  ca_early_flag = ca_done_r         // CA instruction was evaluated in X1
                & ca_predicate_r    // predicate is true
                & (~ca_stall)       // CA instruction is not stalled
                & (~ca_grad_req)    // CA instruction does not graduate
                ;
   
  x1_zncv_wen   = zncv_wen 
                & {`npuarc_ZNCV_BITS{ca_early_flag}}
                & (~dp_retire_zncv)
                ;

  //--------------------------------------------------------------------------
  // ca_zncv_wen is a vector that indicates whether the current CA-stage insn
  // would write to each of the ZNCV flags, as a flag-setting side-effect,
  // based on the late evaluation of a flag-setting ALU operation in CA.
  // It is created by gating zncv_wen with ca_late_flag.
  //
  ca_late_flag  = (!ca_done_r | ca_scond)   // CA flag was not produced at X1
                & ca_q_cond                 // CA predicate is true
                & (~ca_stall)               // CA insn is not stalled
                & (~ca_grad_req)            // CA insn does not graduate
                ;
                
  ca_zncv_wen   = zncv_wen 
                & {`npuarc_ZNCV_BITS{ca_late_flag}} 
                & (~dp_retire_zncv)
                ;

  //--------------------------------------------------------------------------
  // 'pre_ca_zncv' is a vector of ZNCV values obtained by merging the
  // the early speculative flags, computed by the early ALU when the 
  // CA-stage instruction was at the X1 stage, with the committed flags.
  // This vector of ZNCV values is not timing-critical.
  //
  pre_ca_zncv   = (ca_zncv_r                      & x1_zncv_wen   )
                | (ar_aux_status32_r[`npuarc_ZNCV_RANGE] & (~(x1_zncv_wen | dp_retire_zncv)))
                | (ca_retire_flags                & dp_retire_zncv)
                ;

  //--------------------------------------------------------------------------
  // 'act_ca_zncv' is a vector of ZNCV values obtained by merging the
  // late speculative flags, computed in the current cycle by the late ALU
  // at the CA stage, with the pre_ca_zncv values.
  // This vector of ZNCV values *is* timing-critical, as it includes the
  // ALU status results from the current ALU operation at the CA stage.
  //
  act_ca_zncv   = (pre_ca_zncv       & (~ca_zncv_wen) )
                | (alu_result_zncv   & ca_zncv_wen    )
                ;
                
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on mux
// SJ:  functionally independent signals
  casez ({   ca_h_sm
           , is_sr
           , (is_flag | is_kflag)
           , (|dp_retire_zncv)
           , (|zncv_wen & commit_normal_evt)
         })
    5'b?_1???: ca_zncv_sm = wa_sr_data_r[`npuarc_ZNCV_RANGE];
    5'b0_01??: ca_zncv_sm = ca_src1_r[`npuarc_ZNCV_RANGE];
    5'b?_001?: ca_zncv_sm = act_ca_zncv;
    5'b?_0001: ca_zncv_sm = act_ca_zncv;
    default:   ca_zncv_sm = ar_aux_status32_r[`npuarc_ZNCV_RANGE];
  endcase
// spyglass enable_block Ac_conv01

  // =========================================================================
  // -- STATUS32.L - SR (debug)
  //
  casez ({   ca_h_sm
           , is_sr
           , is_loop
         })
    3'b?_1?:  ca_l_sm    = wa_sr_data_r[`npuarc_L_FLAG];
    3'b0_01:  ca_l_sm    = 1'b0;
    default:  ca_l_sm    = ar_aux_status32_r[`npuarc_L_FLAG];
  endcase

  // =========================================================================
  // -- STATUS32.DZ - SR (debug), kFLAG, FLAG (kernel)
  //
  casez ({   ca_h_sm
           , is_sr
           , (is_flag | is_kflag) & in_kernel_mode
         })
    3'b?_1?: ca_dz_sm    = wa_sr_data_r[`npuarc_DZ_FLAG];
    3'b0_01: ca_dz_sm    = ca_src1_r[`npuarc_DZ_FLAG];
    default: ca_dz_sm    = ar_aux_status32_r[`npuarc_DZ_FLAG];
  endcase

  // =========================================================================
  // -- STATUS32.SC - SR (debug), kFLAG, FLAG (kernel)
  //
  casez ({   ca_h_sm
           , is_sr
           , (is_flag | is_kflag) & in_kernel_mode
         })
    3'b?_1?: ca_sc_sm    = wa_sr_data_r[`npuarc_SC_FLAG];
    3'b0_01: ca_sc_sm    = ca_src1_r[`npuarc_SC_FLAG];
    default: ca_sc_sm    = ar_aux_status32_r[`npuarc_SC_FLAG];
  endcase

  // =========================================================================
  // -- STATUS32.ES
  // 2. Update flag on SR
  // 3a. Set on EI op (only valid in Pipe A/0)
  // 3b. Rescind on EI slot commit
  //
  casez ({   ca_h_sm
           , is_sr
           , commit_normal_evt
         })
    3'b?_1?: ca_es_sm    = wa_sr_data_r[`npuarc_ES_FLAG];
    3'b0_01: ca_es_sm    = ca_ei_op_r & (~ar_aux_status32_r[`npuarc_ES_FLAG]);
    default: ca_es_sm    = ar_aux_status32_r[`npuarc_ES_FLAG];
  endcase

  // =========================================================================
  // -- STATUS32.AD - SR (debug), kFLAG, FLAG (kernel)
  //
  casez ({   ca_h_sm
           , is_sr
           , (is_flag | is_kflag) & in_kernel_mode
         })
    3'b?_1?: ca_ad_sm    = wa_sr_data_r[`npuarc_AD_FLAG];
    3'b0_01: ca_ad_sm    = ca_src1_r[`npuarc_AD_FLAG];
    default: ca_ad_sm    = ar_aux_status32_r[`npuarc_AD_FLAG];
  endcase

  // =========================================================================
  // -- STATUS32.US - SR (debug), kFLAG, FLAG (kernel)
  //
  casez ({   ca_h_sm
           , is_sr
           , (is_flag | is_kflag) & in_kernel_mode
         })
    3'b?_1?: ca_us_sm    = wa_sr_data_r[`npuarc_US_FLAG];
    3'b0_01: ca_us_sm    = ca_src1_r[`npuarc_US_FLAG];
    default: ca_us_sm    = ar_aux_status32_r[`npuarc_US_FLAG];
  endcase

  // =========================================================================
  // -- STATUS32.EIH - SR (debug), kFLAG, FLAG (kernel)
  //
  casez ({   ca_h_sm
           , is_sr
           , (is_flag | is_kflag) & in_kernel_mode
         })
    3'b?_1?: ca_eih_sm    = wa_sr_data_r[`npuarc_EIH_FLAG];
    3'b0_01: ca_eih_sm    = ca_src1_r[`npuarc_EIH_FLAG];
    default: ca_eih_sm    = ar_aux_status32_r[`npuarc_EIH_FLAG];
  endcase

  // =========================================================================
  // -- STATUS32.IE - SR (debug), kFLAG, SETI, CLRI
  //
  casez ({   ca_h_sm
           , is_sr
           , (  (is_kflag & in_kernel_mode)
              | (is_sleep & sleep_kernel_mode))
           , (is_seti | is_clri)
         })
    4'b?_1??: ca_ie_sm   = wa_sr_data_r[`npuarc_IE_FLAG];
    4'b0_01?: ca_ie_sm   = (is_sleep == 1'b1)
                         ? ca_src1_r[4]
                         : ca_src1_r[`npuarc_IE_FLAG]
                         ;
    4'b0_001: ca_ie_sm   = is_seti & (~ca_src1_r[5]|ca_src1_r[4]);
    default:  ca_ie_sm   = ar_aux_status32_r[`npuarc_IE_FLAG];
  endcase

end // block: sm_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinatorial process to derive the value of updates to STATUS32.        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: wa_aux_status32_PROC


  status32_nxt           = `npuarc_PFLAG_BITS'd0;

  // Derive next value of the packed architectural status32 register
  // (maintained in the writeback stage).
  //
  // leda W226 off
  // LMD: Case select expression is constant
  // LJ:  A constant select expression is required in this case
  // leda W225 off
  // LMD: Case item expression is not constant
  // LJ:  A non-constant case-itme expression is required in this case
  //
 
  case (1'b1)

    // Update to STATUS32 on entry to an exception handler (upon commit of
    // the exception prologue multi-op sequence).
    //
    (  (is_swi & ca_pass)
     | excpn_evts[`npuarc_INTEVT_ENTER]
    ): begin
      status32_nxt[`npuarc_P_H_FLAG]      = (ca_triple_fault_set == 1'b1) ? ca_h_sm : 1'b0;
      status32_nxt[`npuarc_P_IE_FLAG]     = 1'b0;                        
      status32_nxt[`npuarc_P_E_FLAG]      = ar_aux_status32_r[`npuarc_E_FLAG];  
      status32_nxt[`npuarc_P_L_FLAG]      = 1'b1;
      status32_nxt[`npuarc_P_AE_FLAG]     = 1'b1;
      status32_nxt[`npuarc_P_AD_FLAG]     = ar_aux_status32_r[`npuarc_AD_FLAG];
      status32_nxt[`npuarc_P_US_FLAG]     = ar_aux_status32_r[`npuarc_US_FLAG];
      status32_nxt[`npuarc_P_SC_FLAG]     = 1'b0;
      status32_nxt[`npuarc_P_DZ_FLAG]     = 1'b0;
      status32_nxt[`npuarc_P_EIH_FLAG]    = ar_aux_status32_r[`npuarc_EIH_FLAG];
      status32_nxt[`npuarc_P_ZNCV_FLAG]   = {   ar_aux_user_mode_r
                                       , ar_aux_status32_r[`npuarc_N_FLAG:`npuarc_V_FLAG]
                                     }
                                   ;
    end

    // Update to STATUS32 on exit of an exception handler (upon commit of
    // the exception epilogue multi-op sequence).
    //
    excpn_evts[`npuarc_INTEVT_EXIT]: begin
     status32_nxt                = `npuarc_PFLAG_BITS'd0;
     status32_nxt[`npuarc_P_E_FLAG]     = ar_aux_erstatus_r[`npuarc_E_FLAG];
     status32_nxt[`npuarc_P_AE_FLAG]    = ar_aux_erstatus_r[`npuarc_AE_FLAG];
     status32_nxt[`npuarc_P_DE_FLAG]    = ar_aux_erstatus_r[`npuarc_DE_FLAG];
     status32_nxt[`npuarc_P_U_FLAG]     = ar_aux_erstatus_r[`npuarc_U_FLAG]; 
     status32_nxt[`npuarc_P_ZNCV_FLAG]  = ar_aux_erstatus_r[`npuarc_ZNCV_RANGE];
     status32_nxt[`npuarc_P_L_FLAG]     = ar_aux_erstatus_r[`npuarc_L_FLAG];    
     status32_nxt[`npuarc_P_DZ_FLAG]    = ar_aux_erstatus_r[`npuarc_DZ_FLAG];
     status32_nxt[`npuarc_P_SC_FLAG]    = ar_aux_erstatus_r[`npuarc_SC_FLAG];
     status32_nxt[`npuarc_P_ES_FLAG]    = ar_aux_erstatus_r[`npuarc_ES_FLAG];
     status32_nxt[`npuarc_P_AD_FLAG]    = ar_aux_erstatus_r[`npuarc_AD_FLAG];
     status32_nxt[`npuarc_P_US_FLAG]    = ar_aux_erstatus_r[`npuarc_US_FLAG];
     status32_nxt[`npuarc_P_EIH_FLAG]   = ar_aux_erstatus_r[`npuarc_EIH_FLAG];
     status32_nxt[`npuarc_P_IE_FLAG]    = ar_aux_erstatus_r[`npuarc_IE_FLAG];
    end

    // Update to STATUS32 on entry to interrupt handler
    // we need to disable ZOL for the ISR
    //
    int_evts[`npuarc_INTEVT_ENTER]: begin
      status32_nxt[`npuarc_P_L_FLAG]      = 1'b1;
      status32_nxt[`npuarc_P_IE_FLAG]     = ar_aux_status32_r[`npuarc_IE_FLAG];
      status32_nxt[`npuarc_P_EIH_FLAG]    = ar_aux_status32_r[`npuarc_EIH_FLAG];
      status32_nxt[`npuarc_P_E_FLAG]      = ar_aux_status32_r[`npuarc_E_FLAG];
      status32_nxt[`npuarc_P_AD_FLAG]     = ar_aux_status32_r[`npuarc_AD_FLAG];
      status32_nxt[`npuarc_P_US_FLAG]     = ar_aux_status32_r[`npuarc_US_FLAG];
      status32_nxt[`npuarc_P_SC_FLAG]     = ar_aux_status32_r[`npuarc_SC_FLAG];
      status32_nxt[`npuarc_P_DZ_FLAG]     = 1'b0;
      status32_nxt[`npuarc_P_EIH_FLAG]    = ar_aux_status32_r[`npuarc_EIH_FLAG];
      status32_nxt[`npuarc_P_ZNCV_FLAG]   = {   ar_aux_user_mode_r
                                       , ar_aux_status32_r[`npuarc_N_FLAG:`npuarc_V_FLAG]
                                     };

    end

    // Update to STATUS32 on exit of an interrupt handler (upon the commit of
    // the interrupt epiliogue multi-op sequence).
    //
    int_evts[`npuarc_INTEVT_EXIT]: begin
     status32_nxt                = `npuarc_PFLAG_BITS'd0;
     status32_nxt[`npuarc_P_E_FLAG]     = ar_aux_status32_r[`npuarc_E_FLAG];
     status32_nxt[`npuarc_P_AE_FLAG]    = ar_aux_status32_r[`npuarc_AE_FLAG];
     status32_nxt[`npuarc_P_DE_FLAG]    = ar_aux_status32_r[`npuarc_DE_FLAG];
     status32_nxt[`npuarc_P_U_FLAG]     = ar_aux_status32_r[`npuarc_U_FLAG]; 
     status32_nxt[`npuarc_P_ZNCV_FLAG]  = ar_aux_status32_r[`npuarc_ZNCV_RANGE];
     status32_nxt[`npuarc_P_L_FLAG]     = ar_aux_status32_r[`npuarc_L_FLAG];    
     status32_nxt[`npuarc_P_DZ_FLAG]    = ar_aux_status32_r[`npuarc_DZ_FLAG];
     status32_nxt[`npuarc_P_SC_FLAG]    = ar_aux_status32_r[`npuarc_SC_FLAG];
     status32_nxt[`npuarc_P_ES_FLAG]    = ar_aux_status32_r[`npuarc_ES_FLAG];
     status32_nxt[`npuarc_P_AD_FLAG]    = ar_aux_status32_r[`npuarc_AD_FLAG];
     status32_nxt[`npuarc_P_US_FLAG]    = ar_aux_status32_r[`npuarc_US_FLAG];
     status32_nxt[`npuarc_P_EIH_FLAG]   = ar_aux_status32_r[`npuarc_EIH_FLAG];
     status32_nxt[`npuarc_P_IE_FLAG]    = ar_aux_status32_r[`npuarc_IE_FLAG];
      status32_nxt[`npuarc_P_U_FLAG]            = ar_aux_user_mode_r;

    end


    default: begin
      // For non-exceptional events, derive the appropriate update to
      // machine flags as a function of the current instruction being
      // committed.
      //
      status32_nxt[`npuarc_P_H_FLAG]      = ca_h_sm;
      status32_nxt[`npuarc_P_E_FLAG]      = ca_e_sm;
      status32_nxt[`npuarc_P_AE_FLAG]     = ca_ae_sm;
      status32_nxt[`npuarc_P_DE_FLAG]     = ca_de_sm;
      status32_nxt[`npuarc_P_U_FLAG]      = ca_u_sm;
      status32_nxt[`npuarc_P_ZNCV_FLAG]   = ca_zncv_sm;
      status32_nxt[`npuarc_P_L_FLAG]      = ca_l_sm;
      status32_nxt[`npuarc_P_DZ_FLAG]     = ca_dz_sm;
      status32_nxt[`npuarc_P_SC_FLAG]     = ca_sc_sm;
      status32_nxt[`npuarc_P_ES_FLAG]     = ca_es_sm;
      status32_nxt[`npuarc_P_AD_FLAG]     = ca_ad_sm;
      status32_nxt[`npuarc_P_US_FLAG]     = ca_us_sm;
      status32_nxt[`npuarc_P_EIH_FLAG]    = ca_eih_sm;
      status32_nxt[`npuarc_P_IE_FLAG]     = ca_ie_sm;
    end
  endcase // case (1'b1)

  // leda W226 on
  // leda W225 on


  // overwrite status32 by load instruction
  if (wa_uopld_status32_nxt ) begin
     status32_nxt                = `npuarc_PFLAG_BITS'd0;
     status32_nxt[`npuarc_P_H_FLAG]     = ca_h_sm; // If Halt & UOP load race

     status32_nxt[`npuarc_P_E_FLAG]     = wa_rf_wdata1_lo_nxt[`npuarc_E_FLAG];
     status32_nxt[`npuarc_P_AE_FLAG]    = wa_rf_wdata1_lo_nxt[`npuarc_AE_FLAG];
     status32_nxt[`npuarc_P_DE_FLAG]    = wa_rf_wdata1_lo_nxt[`npuarc_DE_FLAG];
     status32_nxt[`npuarc_P_U_FLAG]     = wa_rf_wdata1_lo_nxt[`npuarc_U_FLAG]; 
     status32_nxt[`npuarc_P_ZNCV_FLAG]  = wa_rf_wdata1_lo_nxt[`npuarc_ZNCV_RANGE];
     status32_nxt[`npuarc_P_L_FLAG]     = wa_rf_wdata1_lo_nxt[`npuarc_L_FLAG];    
     status32_nxt[`npuarc_P_DZ_FLAG]    = wa_rf_wdata1_lo_nxt[`npuarc_DZ_FLAG];
     status32_nxt[`npuarc_P_SC_FLAG]    = wa_rf_wdata1_lo_nxt[`npuarc_SC_FLAG];
     status32_nxt[`npuarc_P_ES_FLAG]    = wa_rf_wdata1_lo_nxt[`npuarc_ES_FLAG];
     status32_nxt[`npuarc_P_AD_FLAG]    = wa_rf_wdata1_lo_nxt[`npuarc_AD_FLAG];
     status32_nxt[`npuarc_P_US_FLAG]    = wa_rf_wdata1_lo_nxt[`npuarc_US_FLAG];
     status32_nxt[`npuarc_P_EIH_FLAG]   = wa_rf_wdata1_lo_nxt[`npuarc_EIH_FLAG];
     status32_nxt[`npuarc_P_IE_FLAG]    = wa_rf_wdata1_lo_nxt[`npuarc_IE_FLAG];
  end

  // Update architectural state of STATUS32 to be retained in WA.
  //
// spyglass disable_block Ac_conv02
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
  status32_pass_vec     = 2'b00
                        |  {2{commit_normal_evt}}
                        
                        | {2{excpn_evts[`npuarc_INTEVT_ENTER]
                            | int_evts[`npuarc_INTEVT_ENTER]
                            | wa_uopld_status32_nxt
                            | wa_status32_wen
                            | wa_debug_wen
                            | halt_machine
                            | unhalt_machine
                           }}
                        ;
// spyglass enable_block Ac_conv02
  flags_pass            = |(  status32_pass_vec
                           & ~{1'b0, ca_0_grad_flags}
                           )
                        | (ca_retire_ack & (|dp_retire_zncv))
                        ;


end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output Assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign ca_in_kflag            = (is_flag & in_kernel_mode) | is_kflag;
assign ca_is_flag             = is_flag;
assign ca_kflag_op            = kflag_op;
assign wa_aux_status32_nxt    = status32_nxt;
assign wa_aux_status32_pass   = (|status32_pass_vec);
assign wa_aux_flags_pass      = flags_pass;
assign wa_aux_uop_flag_pass   = commit_uop_evt;
// spyglass enable_block W193

endmodule // alb_status32
