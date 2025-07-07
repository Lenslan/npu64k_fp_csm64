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
// #  #    # ##### ###### #####   #####  #    # #####  #####  ####
// #  ##   #   #   #      #    #  #    # #    # #    #   #   #
// #  # #  #   #   #####  #    #  #    # #    # #    #   #    ####
// #  #  # #   #   #      #####   #####  #    # #####    #        #
// #  #   ##   #   #      #   #   #   #  #    # #        #   #    #
// #  #    #   #   ###### #    #  #    #  ####  #        #    ####
//
//----------------------------------------------------------------------------
//
// @f:interrupts
//
// Description:
// @p
//     This module implements the logic used to manage the processing of
//   external interrupt requests.
// @e
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o interrupts.vpp
//
// ===========================================================================

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


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_interrupts (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,                // Global clock
  input                       rst_a,              // Asynchronous reset signal

  ////////// Machine Architectural state /////////////////////////////////////
  //
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Not all bits used
  input      [`npuarc_DATA_RANGE]    ar_aux_irq_act_r,   // (arch.) IRQ_ACT_AUX
  input      [`npuarc_DATA_RANGE]    ar_aux_status32_r,  // (arch.) STATUS32_AUX
  input      [`npuarc_DATA_RANGE]    sp_aux_status32_r,  // (spec.) STATUS32_AUX
  // leda NTL_CON13C on
  input                       ar_aux_user_mode_r, // (arch.) user mode

  input      [`npuarc_INT_NUM_RANGE] irq_num_r,          // current IRQ number
  input                       ar_tags_empty_r,    // grad buffer is empty
  input                       ca_load_r,          // ca inst is load

  ////////// Debug Unit signals //////////////////////////////////////////////
  //
  input                       db_active,          // Insn. is DEBUG

  ////////// MMU related signals /////////////////////////////////////////////
  //
  input                       ca_replay,          // DC4 request replay

  ////////// Commit Stage UOP signals ////////////////////////////////////////
  //
  input                       ca_rtie_op_r,       // CA Insn is RTIE
  input                       ca_uop_commit_r,    // Insn terminates UOP seq
  input                       ca_uop_active_r,    // UOP module is active
  input                       ca_cmt_norm_evt,    // Commit Insn
  input                       ca_cmt_uop_evt,     // Commit UOP Insn

  ////////// Exceptions module to ints ///////////////////////////////////////
  //
  input                       take_int,           //take interrupt  



  ////////// Post-Commit state ///////////////////////////////////////////////
  //
  output reg                  ct_rtie_nopp_r,     // RTIE invokes NOPP
  output reg [7:0]            irq_num_nopp_r,     // irq_num for NOPP
  output reg [`npuarc_IRQLGN_RANGE]  irq_w_nopp_r,       // irq_w for NOPP

  ////////// Interface between interrupt module and irq_unit (requests) //////
  //
  input                       irq_req,            // Enabled, active IRQ exists
  input      [7:0]            irq_num,            // ID of preempted irq input
  input      [`npuarc_IRQLGN_RANGE]  irq_w,              // Priority ('W') value
  input                       irq_preempts,       // Winning IRQ will preempt
  input      [`npuarc_IRQLGN_RANGE]  irq_ack_w_r,        // Interrupt acknowledge ('W')

  ////////// Interface between interrupt module and irq_unit (acknowledgment)
  //
  output reg [`npuarc_IRQN_RANGE]    cpu_accept_irq,     // CPU-accepted IRQ priorities
  output reg                  irq_ack,            // Interrupt acknowledge
  output reg [7:0]            irq_ack_num,        // Interrupt acknowledge ('N')

  ////////// Exception State Events //////////////////////////////////////////
  //
  // leda NTL_CON13C off
  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  input      [`npuarc_INTEVT_RANGE]  excpn_evts,         // Exception events
  // leda NTL_CON13C on
  // leda NTL_CON37 on

  input                       ca_pkill_evt,       // int prologue is killed by exception

  ////////// Interrupt State Events //////////////////////////////////////////
  //
  output reg [`npuarc_INTEVT_RANGE]  int_evts,           // Interrupts Events
  output                      int_ilink_evt,      // Updt ILINK with PC
  input                       int_rtie_replay_r,  // Exception events
  
  ////////// Interrupt State to Commit ///////////////////////////////////////
  //
  output reg                  int_preempt,        // Preempt current state
  output reg [`npuarc_DATA_RANGE]    int_act_nxt         // Next value of IRQ_ACT_AUX
  );
reg                           int_nopp;
// nopreempt_PROC
//
reg                           int_nopreempt;

// preempt_PROC
//
reg                           ints_enabled;
reg [`npuarc_IRQ_ACT_ACT_RANGE]      aux_stat32_e_ury;
reg [`npuarc_IRQ_ACT_ACT_RANGE]      irq_act_enables;

reg [`npuarc_IRQ_ACT_ACT_RANGE]      irq_w_1h;
reg [`npuarc_IRQ_ACT_ACT_RANGE]      act_p_1h;

// nopush_pop_PROC
//
  // leda NTL_CON13A off
  // LMD: non driving internal reg
  // LJ:  Not all bits of bus used
reg [`npuarc_IRQ_ACT_ACT_RANGE]      act_q_1h;
  // leda NTL_CON13A on
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used
reg                           int_nopp_nxt;
// leda NTL_CON13A on
reg                           int_nopp_en;

// int_misc_PROC
//

// aux_irq_act_PROC
//
reg [`npuarc_IRQ_ACT_ACT_RANGE]      act_act_nxt;
reg                           act_u_nxt;

// int_prologue_evt_PROC
//
reg                           int_prologue_evt;
reg                           int_enter_evt;

// int_prologue_PROC
//
reg                           in_int_prologue_nxt;

// int_epilogue_evt_PROC
//
reg                           int_epilogue_evt;
reg                           int_exit_evt;

// int_epilogue_PROC
//
reg                           in_int_epilogue_nxt;

// irq_ack_PROC
//
reg [`npuarc_IRQN_RANGE]             act_ack_1h;

// ct_rtie_nopp_PROC
//
reg                           ct_rtie_nopp_nxt;

// int_reg_PROC
//
reg                           in_int_prologue_r;

// int_nopp_reg_PROC
//
reg                           int_nopp_r;

reg                           in_int_epilogue_r;

// ct_rtie_nopp_reg_PROC
//

// leda W225 off - allow non-constant case expressions
// LMD: case item expression is not constant
// LJ:  requirement of one-hot decoder case statement
// leda W226 off - allow constant case-select expression (1'b1)
// LMD: case select expression is constant
// LJ:  "case (1'b1)" is used for a one-hot decoder

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @nopreempt_PROC:                                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: nopreempt_PROC

  // Disallow preemption during the following conditions:
  //
  //   (1) Whenever a uop_seq is currently active in the pipeline.
  //
  //   (2) When the machine is operating in an exception context.
  //
  //   (3) During an exception prologue sequence (unlike 2, the machine
  //       state is not updated until the completion of the uop sequence).
  //
  //   (4) During an interrupt prologue or epilogue.
  //
  int_nopreempt         = ca_uop_active_r                // ---- (1)
                        | sp_aux_status32_r[`npuarc_AE_FLAG]    // ---- (2)
                        | excpn_evts[`npuarc_INTEVT_INPROL]     // ---- (3)
                        | in_int_prologue_r              // -+-- (4)
                        | in_int_epilogue_r              // -+
                        | int_rtie_replay_r              // -+
                        ;

end // block: nopreempt_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @preempt_PROC:                                                         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: preempt_PROC

  // Assert the ints_enabled signal if an enabled interrupt, of a
  // sufficient priority, can be taken. This does not take into
  // account the presence of active uops or active interrupt or exception
  // prologue or epilogue sequences. They are handled by the int_nopreempt
  // signal, which temporarily disables the taking of an interrupt until
  // those sequences are completed.
  //
  ints_enabled      =  sp_aux_status32_r[`npuarc_IE_FLAG]
                    & (!sp_aux_status32_r[`npuarc_AE_FLAG])
                    & (!sp_aux_status32_r[`npuarc_H_FLAG])
                    ;

  // Derive a NUMBER_OF_LEVELS bit-vector, where each bit denotes
  // whether the corresponding level is enabled for the current value
  // of STATUS32.E. All bits are cleared if the core is not preemptible,
  // as indicated by the ints_enabled signal.
  //
  aux_stat32_e_ury  = `npuarc_NUMBER_OF_LEVELS'd0;
  case (sp_aux_status32_r[`npuarc_E_FLAG])
   4'd0: aux_stat32_e_ury[0:0] = {1{ints_enabled}};
   4'd1: aux_stat32_e_ury[1:0] = {2{ints_enabled}};
   4'd2: aux_stat32_e_ury[2:0] = {3{ints_enabled}};
   4'd3: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd4: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd5: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd6: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd7: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd8: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd9: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd10: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd11: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd12: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd13: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd14: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
   4'd15: aux_stat32_e_ury       = {`npuarc_NUMBER_OF_LEVELS{ints_enabled}};
  endcase

  // Derive a NUMBER_OF_LEVELS bit-vector, where each bit denotes
  // whether the corresponding level is enabled for the current value
  // of AUX_IRQ_ACT.ACTIVE. This is a priority encoder, which detects
  // the least-significant bit set (if any) in ar_aux_irq_act_r, and
  // sets all lower-numbered bits in the irq_act_enables vector to
  // to 1. All other bits are set to 0. Therefore, if the least-significant
  // bit in ar_aux_irq_act_r is bit 4, then bits [3:0] would be set to 1
  // and bits [NUMBER_OF_LEVELS-1:4] would be set to 0.
  //
  irq_act_enables   = {`npuarc_NUMBER_OF_LEVELS{1'b1}};

  // leda W71 off
  // LMD: case block missing a default
  // LJ:  default term is covered prior to the case block
  case (1'b1)
    ar_aux_irq_act_r[0]: irq_act_enables = {3{1'b0}};
    ar_aux_irq_act_r[1]: irq_act_enables = {{2{1'b0}}, {1{1'b1}}};
    ar_aux_irq_act_r[2]: irq_act_enables = {{1{1'b0}}, {2{1'b1}}};
  endcase
  // leda W71 on

  // Combine the priority-level enable signals from aux_stat32_e_ury
  // with irq_act_enables, and with the ints_enabled signal.
  // Only priority levels that have a 1 in the corresponding bits of
  // BOTH enabling vectors are actually enabled when ints_enabled
  // is asserted. All bits are cleared if ints_enabled is not asserted.
  //
  cpu_accept_irq    = aux_stat32_e_ury
                    & irq_act_enables
                    ;

  // Convert the incoming priority level to one-hot for further
  // processing.
  //
  irq_w_1h          = `npuarc_IRQ_N'b0;
  // leda W71 off - allow case statement without default clause
  // LMD: case block missing a default
  // leda DFT_022 off
  // LMD: Incomplete case statement
  // LJ:  default term is covered prior to the case block
  case (irq_w)
    `npuarc_IRQLGN_BITS'd0:
      irq_w_1h[0]  = (aux_stat32_e_ury[0] & irq_req);
    `npuarc_IRQLGN_BITS'd1:
      irq_w_1h[1]  = (aux_stat32_e_ury[1] & irq_req);
    `npuarc_IRQLGN_BITS'd2:
      irq_w_1h[2]  = (aux_stat32_e_ury[2] & irq_req);
  endcase
  // leda DFT_022 on
  // leda W71 on

  // Derive the current operating level from IRQ_ACT by selecting
  // the highest priority bit.
  //
  act_p_1h          = `npuarc_NUMBER_OF_LEVELS'd0;

  // leda W71 off - allow case statement without default clause
  // LMD: case block missing a default
  // leda DFT_022 off
  // LMD: Incomplete case statement
  // LJ:  default term is covered prior to the case block
  case (1'b1)
    ar_aux_irq_act_r[0]: act_p_1h[0] = 1'b1;
    ar_aux_irq_act_r[1]: act_p_1h[1] = 1'b1;
    ar_aux_irq_act_r[2]: act_p_1h[2] = 1'b1;
  endcase
  // leda DFT_022 on
  // leda W71 on

  // Determine whether the incoming interrupt level preempts the
  // current operating state. Iterate over each level in order of
  // priority and pick the first for which an interrupt is
  // asserted. If the level corresponds to the current operating level
  // preemption does not occur. Similarly, if the level corresponds to
  // the incoming level and that level is enabled preemption occurs.
  //
  int_preempt = irq_preempts & (!int_nopreempt);

end // block: preempt_PROC

                                                                        

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @nopp_PROC:                                                            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: nopp_PROC

  // Derive the return-to priority level by masking out the current
  // operating level 'P' and by selecting the next highest
  // priority. The return-to priority is the next highest priority in
  // the active interrupt stack.
  //
  act_q_1h         = `npuarc_NUMBER_OF_LEVELS'd0;

  // leda W71 off - allow case statement without default clause
  // LMD: case block missing a default
  // leda DFT_022 off
  // LMD: Incomplete case statement
  // LJ:  default term is covered prior to the case block
  case (1'b1)
    (ar_aux_irq_act_r[0] & (~act_p_1h[0])): begin
      act_q_1h[0] = (irq_w_1h[0] | ar_aux_irq_act_r[0]);
    end
    (ar_aux_irq_act_r[1] & (~act_p_1h[1])): begin
      act_q_1h[1] = (irq_w_1h[1] | ar_aux_irq_act_r[1]);
    end
    (ar_aux_irq_act_r[2] & (~act_p_1h[2])): begin
      act_q_1h[2] = (irq_w_1h[2] | ar_aux_irq_act_r[2]);
    end
  endcase
  // leda DFT_022 on
  // leda W71 on

  // In the non-preemptive case, calculate whether the return-to
  // priority 'Q' corresponds to the current value at the irq_unit
  // ('W'). If it does (implying that the irq_unit is operating at a
  // higher priority than the current next priority on the active
  // stack, but lower than the current operating priority 'P'), the
  // push/pop operation can be avoided and the new interrupt
  // entered immediately.
  //
  int_nopp_nxt           = 1'b0;
  // leda W71 off - allow case statement without default clause
  // LMD: case block missing a default
  // leda DFT_022 off
  // LMD: Incomplete case statement
  // LJ:  default term is covered prior to the case block
  case (1'b1)
    ((~int_preempt & irq_w_1h[0]) | act_q_1h[0]):
      int_nopp_nxt       = (irq_w_1h[0] & (~act_q_1h[0]))
                         ;
    ((~int_preempt & irq_w_1h[1]) | act_q_1h[1]):
      int_nopp_nxt       = (irq_w_1h[1] & (~act_q_1h[1]))
                         ;
    ((~int_preempt & irq_w_1h[2]) | act_q_1h[2]):
      int_nopp_nxt       = (irq_w_1h[2] & (~act_q_1h[2]))
                         ;
  endcase
  // leda DFT_022 on
  // leda W71 on

  // After the transition to an interrupt prologue or epilogue, retain
  // the value of the NOPP state on entry to the sequence so as to
  // correctly update IRQ_ACT_AUX on the commit of the sequence.
  //
  int_nopp_en           = (~in_int_prologue_r)
                        & (~in_int_epilogue_r)
                        ;

  // The 'nopush_pop' registered value is defeated iff an incoming
  // interrupt preempts the current operating level at a time when an
  // RTIE would otherwise transition into the ISR at the current
  // operating level.
  //
  int_nopp               = int_nopp_r
                         & (~int_preempt)
                         & (~int_rtie_replay_r)
                         ;

end // block: nopp_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @int_act_nxt_PROC:                                                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: int_act_nxt_PROC

  // Derive the 1-hot encoding of the IRQ_ACK_W (the priority of the
  // interrupt currently being acknowledged).
  //
  act_ack_1h   = `npuarc_IRQ_N'b0;
  // leda W71 off - allow case statement without default clause
  // LMD: case block missing a default
  // leda DFT_022 off
  // LMD: Incomplete case statement
  // LJ:  default term is covered prior to the case block
  case (irq_ack_w_r)
    `npuarc_IRQLGN_BITS'd0:
      act_ack_1h[0]     = 1'b1;
    `npuarc_IRQLGN_BITS'd1:
      act_ack_1h[1]     = 1'b1;
    `npuarc_IRQLGN_BITS'd2:
      act_ack_1h[2]     = 1'b1;
  endcase
  // leda DFT_022 on
  // leda W71 on

  // Derive the next value of IRQ_ACT_AUX.ACT, as follows:
  //
  // On the transition into a interrupt context, the next value
  // of IRQ_ACT_AUX.ACT is derived using:
  //
  //   (1) The current value of IRQ_ACT_AUX.ACT OR'd with the
  //       one-hot encoding of the priority of the interrupt into
  //       which we are transitioning.
  //   (2) AND'd with, the one-cold mask denoting the current
  //       priority level when replaying a NOPP sequence.
  //
  // Otherwise, during the transition out of an interrupt:
  //
  //   (3) The value of IRQ_ACT_AUX.ACT with the current operating
  //       level cleared.
  //
  act_act_nxt  = (int_enter_evt == 1'b1)
               ? (   act_ack_1h                               // (1)
                   | (   ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]
                       & (   {`npuarc_IRQ_N{~int_nopp_r}}            // (2)
                           | (   {`npuarc_IRQ_N{int_nopp_r}}
                               & (~act_p_1h)
                             )
                         )
                     )
                 )
               : (   ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE]     // (3)
                   & (~act_p_1h)
                 )
               ;

  // Set the 'U'-bit of IRQ_ACT to arch. user mode when
  // entering the interrupt chain
  // Clear the 'U' bit when exiting the interrupt chain 
  //
  // leda W563 off
  // LMD: reduction of single bit expression is redundant
  // LJ:  configurable field may be a single bit
  act_u_nxt    =   ar_aux_user_mode_r
               &   (|act_act_nxt[`npuarc_IRQ_ACT_ACT_RANGE])
               ;
  // leda W563 on

  // Consolidate and assign output
  //
  int_act_nxt  = {   act_u_nxt
                   , 28'd0
                   , act_act_nxt
                 }
               ;

end // block: int_act_nxt_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @int_prologue_evt_PROC                                                 //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: int_prologue_evt_PROC


  // An interrupt prologue event occurs when an interrupt has been
  // detected that preempted the current operating state. 
  // It forces flushes to discard instructions in the pipeline
  // and restart from the interrupt vector
  //
  int_prologue_evt  = take_int;

  // The interrupt is considered taken on the commit of the interrupt
  // prologue sequence. We detect this by the assertion of the
  // uop_commit (2) signal and the fact that we are currently executing in
  // an prologue sequence(3).
  // The instruction is commited (by ca_pass) and includes the last instruction of UOP (1) 
  //
  int_enter_evt     = ca_cmt_norm_evt   // (1) 
                    & ca_uop_commit_r   // (2)
                    & in_int_prologue_r // (3)
                    & (~( ar_aux_status32_r [`npuarc_AE_FLAG]
                       | excpn_evts[`npuarc_INTEVT_ENTER] 
                       ))
                    ;

end // block: int_prologue_evt_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @int_ilink_PROC:                                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// On the transition into an interrupt prologue, the value of the
// interrupted PC is retained in ILINK for the period until it can
// be pushed to the stack (from ILINK). Hold-off update if grad buf
// is not empty as potentially could overwrite ilink (r29)
//
reg int_ilink_evt_nxt;
reg int_ilink_wait_nxt;
reg int_ilink_wait_r;
always @(*)
begin: int_ilink_sm_PROC
  int_ilink_evt_nxt  = 1'b0;
  int_ilink_wait_nxt = int_ilink_wait_r;
  case (int_ilink_wait_r)
    1'b0: begin
      if (int_evts[`npuarc_INTEVT_PROLOGUE]) begin
        if (ar_tags_empty_r & (!ca_load_r)) begin
          int_ilink_evt_nxt  = 1'b1;
        end
        else begin
          int_ilink_wait_nxt = 1'b1;
        end
      end
    end
    1'b1: begin
      if (ar_tags_empty_r & (!ca_load_r)) begin
        int_ilink_evt_nxt  = 1'b1;
        int_ilink_wait_nxt = 1'b0;
      end
    end
  endcase
end
 
always @(posedge clk or posedge rst_a)
begin: int_ilink_r_PROC
  if (rst_a == 1'b1) begin
    int_ilink_wait_r <= 1'b0;
  end
  else begin
    int_ilink_wait_r <= int_ilink_wait_nxt;
  end
end

//we use the signal aligned with prologue event
//to make the ilink register available one cycle sooner 
//so that we can start the prologue instruction earlier
//
assign int_ilink_evt = int_ilink_evt_nxt;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @int_prologue_PROC:                                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: int_prologue_PROC

  // The 'nxt' state derivation of in_int_prologue.
  //
  // The wire is asserted on the transition into an interrput prologue
  // sequence (1) and remains so until the sequence is committed
  // (2). An exception due to prologue instructions will terminate the 
  // interrupt (3) 
  //
  in_int_prologue_nxt = 
                      (   (    int_evts[`npuarc_INTEVT_PROLOGUE]       // (1)
                              & (~in_int_prologue_r)
                          )
                          | ( (~( int_evts[`npuarc_INTEVT_ENTER]     // (2)
                                | ca_pkill_evt                // (3)
                                | ca_replay                   // (4)
                                )
                              )
                            & in_int_prologue_r
                            )
                      )
                      ;

end // block: int_prologue_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @int_epilogue_evt_PROC:                                                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: int_epilogue_evt_PROC

  // The interrupt epilogue event is triggered by the pass of an RTIE
  // instruction to the commit stage. 
  // We specifically distinguish between RTIEs associated with interrupts
  // and exceptions by allowing the assertion to be defeated by the
  // asserted of exception active flag (the AE flag) (1)
  // We have to make sure there is interrupt being serviced (2), Otherwise 
  // the RTIE would be from an exception or user program 
  // Similarly, the signal is defeated if the RTIE is causing an exception 
  // to be entered (for example, when asserting a priviledge exception on 
  // the attempted commit of an RTIE in user-mode) (3).
  // An nopp condition will also defeat the epilogue (4). Actually it will kill
  // the epilogue sequence after this RTIE before it enters commit stage.
  // During debug there is no epilogue allowed in the pipeline (5)
  //
  // leda W563 off
  // LMD: reduction of single bit expression is redundant
  // LJ:  configurable field may be a single bit
  int_epilogue_evt  = ca_cmt_uop_evt
                    & ca_rtie_op_r
                    & (~sp_aux_status32_r[`npuarc_AE_FLAG])            // (1)
                    & (|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE])   // (2)
                    & (~excpn_evts[`npuarc_INTEVT_PROLOGUE])           // (3)
                    & (~int_nopp)                               // (4)
                    & (~db_active)                              // (5)
                   ;
  // leda W563 on

  // Event denoting the final cycle of the interrupt epilogue.
  // when the last epilogue instruction is commited and accepted
  //
  int_exit_evt      = ca_cmt_norm_evt
                    & ca_uop_commit_r
                    & in_int_epilogue_r
                    ;

  // Interrupt Epilogue Replay (int_ereplay), if an RTIE is present in
  // the commit stage, and will initiate a nopush_pop sequence, we
  // need to be doubly sure that the interrupt request remains
  // asserted. If not, the incoming interrupt priority and level may
  // be invalid and, if acted upon, will corrupt the machine state. By
  // replaying the RTIE, we cancel the nopush_pop sequence (which is
  // initiated in the commit stage), and instead by virtue of the
  // restart, we instead replay a normal epilogue sequence (initiated
  // in the execute stage).
  // This case is handled by registering the irq signals and proceed
  // on the irq service -- even the IRQ disappears after decision is made 
  // proceed with the service
  // In the IRQ_OUTPUT_REG case, this event acts doubly to ensure that
  // the new irq_unit has propogated to the boundary before acting
  // on the output. Should the irq_req signal be rescinded shortly
  // before the assertion of nopp.
  //

end // block: int_epilogue_evt_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @int_epilogue_PROC:                                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: int_epilogue_PROC

  // The 'nxt' state derivation of in_int_epilogue.
  //
  in_int_epilogue_nxt = ~excpn_evts[`npuarc_INTEVT_PROLOGUE]
                      & (   (    int_evts[`npuarc_INTEVT_EPILOGUE]
                              & (~in_int_epilogue_r)
                            )
                          | (   ~( int_evts[`npuarc_INTEVT_EXIT]
                                 | ca_replay
                                 )
                              & in_int_epilogue_r
                            )
                        )
                      ;

end // block: int_epilogue_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @irq_ack_PROC:                                                         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: irq_ack_PROC

  // Acknowledge the interrupt on 'int_enter_evt', the event which
  // denoted the completion/commit of the interrupt prologue sequence.
  //
  irq_ack           = int_enter_evt
                    ;

  irq_ack_num       = irq_num_r;

end // block: irq_ack_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @ct_rtie_nopp_PROC:                                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: ct_rtie_nopp_PROC

  // RTIE/NOPP Deferred is asserted the cycle after the commit of an
  // RTIE that will initiate a no-push-pop interrupt prologue
  // sequence. We do this because the initiation of a prologue would
  // kill the commit of the RTIE which is incorrect. We additionally
  // retain the value until the interrupt has been acknolwedged, in
  // case the outstanding interrupt is held-up.
  // A preempted interrupt overwrites the nopp interrupt if both are happening. 
  // 
  //
  //ca_rtie_op_r should be qulified by |ar_aux_irq_act_r[`IRQ_ACT_ACT_RANGE]
  // and by ~sp_aux_status32_r[`AE_FLAG]
  //to make sure the rtie is for interrupt instead of exception
  //
  // leda W563 off
  // LMD: reduction of single bit expression is redundant
  // LJ:  configurable field IRQ_ACT_ACT_RANGE may be a single bit
  ct_rtie_nopp_nxt  = (   ca_cmt_uop_evt
                        & ca_rtie_op_r
                        & (|ar_aux_irq_act_r[`npuarc_IRQ_ACT_ACT_RANGE])
                        & (~sp_aux_status32_r[`npuarc_AE_FLAG])
                        & int_nopp
                        & (~ct_rtie_nopp_r)
                      )
                    ;
  //leda W563 on
end // block: ct_rtie_nopp_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @int_evts_PROC:                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin: int_evts_PROC

  // The following vector consolidate the various state variables used
  // to track the relative location of the machine within interrupt
  // prologue/epilogue sequences. The following signals should be used
  // by external consumers of interrupts events.
  //
  int_evts                    = `npuarc_INTEVT_BITS'd0
                              ;


  // The event which denotes the cycle in which the machine transitions
  // into an interrupt prologue event.
  //
  int_evts[`npuarc_INTEVT_PROLOGUE]  = int_prologue_evt
                              ;

  // Asserted over the period in which an interrupt prologue sequence
  // is being replayed (asserted on cycle after the int_prologue_evt).
  //
  int_evts[`npuarc_INTEVT_INPROL]    = in_int_prologue_r
                              ;

  // The event which denotes the cycle in which the interrupt prologue
  // is committed/completed.
  //
  int_evts[`npuarc_INTEVT_ENTER]     = int_enter_evt
                              ;

  // The event which denotes the cycle in which the machine
  // transitions into an interrupt epilogue (on the commit of the
  // initiating RTIE instruction).
  //
  int_evts[`npuarc_INTEVT_EPILOGUE]  = int_epilogue_evt
                              ;

  // Asserted over the period in which an interrupt epilogue sequence
  // is being replayed (asserted one cycle after int_epilogue_evt).
  //
  int_evts[`npuarc_INTEVT_INEPIL]    = in_int_epilogue_r
                              ;

  // The event which denotes the cycle in which the interrupt epilogue
  // is committed/completed.
  //
  int_evts[`npuarc_INTEVT_EXIT]      = int_exit_evt
                              ;

end // block: int_evts_PROC

// leda W225 on - check for non-constant case expressions
// leda W226 on - check for constant case-select expression (1'b1)

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @int_reg_PROC:                                                         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: int_reg_PROC
  if (rst_a == 1'b1) begin
    in_int_prologue_r  <= 1'b0;
    in_int_epilogue_r  <= 1'b0;
  end
  else begin
    in_int_prologue_r  <= in_int_prologue_nxt;
    in_int_epilogue_r  <= in_int_epilogue_nxt;
  end
end // block: int_reg_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @int_nopp_reg_PROC:                                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: int_nopp_reg_PROC
  if (rst_a == 1'b1) begin
    int_nopp_r      <= 1'b0;
  end
  else if (int_nopp_en == 1'b1) begin
    int_nopp_r    <= int_nopp_nxt;
  end
end // block: int_nopp_reg_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// @ct_rtie_nop_reg_PROC:                                                 //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//We retain the nopp interrupt information as are triggered one cycle later
//after the irq that may disappear in this delayed cycle
//
always @(posedge clk or posedge rst_a)
begin: ct_rtie_nopp_reg_PROC
  if (rst_a == 1'b1) begin
    ct_rtie_nopp_r  <= 1'b0;
  end
  else begin
    ct_rtie_nopp_r  <= ct_rtie_nopp_nxt;
  end
end // block: ct_rtie_nopp_reg_PROC

always @(posedge clk or posedge rst_a)
begin: irq_reg_PROC
  if (rst_a == 1'b1) begin
    irq_num_nopp_r  <= 8'b0;
    irq_w_nopp_r    <= `npuarc_IRQLGN_BITS'd0; 
  end
  else if (ct_rtie_nopp_nxt) begin
    irq_num_nopp_r  <= irq_num;
    irq_w_nopp_r    <= irq_w;
  end
end // block: ct_rtie_nopp_reg_PROC

endmodule // alb_interrupts
