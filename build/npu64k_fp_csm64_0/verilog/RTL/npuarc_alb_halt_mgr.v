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


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_halt_mgr (
// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,                // system clock
  input                       rst_a,              // system reset

  ////////// Machine Architectural state /////////////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  standard aux interface
  input      [`npuarc_DATA_RANGE]    ar_aux_status32_r,  // (arch) STATUS32
  input      [`npuarc_DATA_RANGE]    ar_aux_debug_r,     // (arch) aux. DEBUG
// leda NTL_CON13C on
  input                       dbg_we_r,           // waiting for event
  input                       dbg_wf_r,           // waiting for LF to clear

  ////////// Debug Halt Request Interface ////////////////////////////////////
  //
  input                       db_request,         // Debug halt request
  input                       ca_cmt_dbg_evt,     // CA commits DBG Insn.

  output reg                  hlt_debug_evt,      // Debug 'Event'
  output                      db_active_r,        // Debug is active

  ////////// Breakpoint Interface ////////////////////////////////////////////
  //
  input                       ca_cmt_brk_evt,     // CA cmts. BRK insn.
  input                       ca_cmt_isi_evt,     // Instruction Step

  ////////// Breakpoint Interface ////////////////////////////////////////////
  //
  input                       int_preempt,        // preempted interrupt to wake up 

  ////////// Sleep Interface /////////////////////////////////////////////////
  //
  input                       ca_sleep_evt,       // Commit sleep insn
  output                      sleep_hlt_wake,     // Wake up from sleep
  input                       arc_event_r,        // external wakeup event
  output                      wevt_wakeup_r,      // Wake up from wevt
  input                       wa_lock_flag_r,     // lock flag state
  output reg                  wlfc_wakeup,        // Wake up from wevt
  output reg                  wake_from_wait,     // re-enable clock after wait

  ////////// Pipeline Interface //////////////////////////////////////////////
  //
  input                       ar_tags_empty_r,    // Grad. buffer empty
  input                       ca_uop_active,      // UOP sequencer is active
  input                       wa_restart_r,       // Pipeline flush
  input                       wa_restart_kill_r,  // 
  input                       fch_stop_r,         // EXU requests IFU halt
  input                       excpn_restart,      // Exception flush
  input                       ct_replay,          // Aux Replay
  input                       excpn_hld_halt,     //
  input                       wa_aux_pc_wen,      // Debug write enable for PC
  input                       ca_finish_sgl_step, // commit or retire sgl step

  output                      hlt_stop,           // Request. Stop restart
  output                      hlt_restart_r,      // Request. Halt restart
  output reg                  hlt_issue_reset,    // Halt issues reset.
  output reg                  hlt_do_halt,        //
  output reg                  hlt_do_unhalt,      //
  output reg                  pipe_block_ints,    //
  output reg                  hlt_wait_idle,      // Halt waiting units to idle
  
  ///////////bist test/////////////////////////////

  ////////// Sub-System Interface ////////////////////////////////////////////
  //
  input                       ifu_idle_r,         // IFU is idle
  input                       dmp_idle_r,         // DMP is idle
  input                       dmp_idle1_r,        // DMP is idle (ignore dmp excpn)
  input                       biu_idle_r,         // BIU are idle

  ////////// Global Machine State ////////////////////////////////////////////
  //
  input                       gb_sys_reset_done_r,// Machine has finshed reset

  ////////// Machine Global Halt/Run request Interface ///////////////////////
  //
  input                       gb_sys_run_req_r,   // Machine run request
  input                       gb_sys_halt_req_r,  // Machine halt request

  output                      gb_sys_run_ack_r,   // Machine run acknowledge
  output                      gb_sys_halt_ack_r,  // Machine halt acknowledge

  //////////  clock control block //////////////////////////////////////////
  //
  output                      hor_clock_enable_nxt, // Arch. Clock Enable

  ////////// Machine Global Run State ////////////////////////////////////////
  //
  output reg                  gb_sys_halt_r,      // Machine is Halted
  output reg                  gb_sys_sleep_r      // Machine is Sleeping
);

parameter   FSM_WAIT_RESET        = 6'b10_1111;
parameter   FSM_RUN               = 6'b00_0000;
parameter   FSM_WAIT_RUN          = 6'b00_0010;
parameter   FSM_UNHALT            = 6'b10_0001;
parameter   FSM_HOR_INIT          = 6'b00_0001;
parameter   FSM_HALT_EMIT_STOP    = 6'b10_1001;
parameter   FSM_HALT_WAIT_PRE     = 6'b10_1000;
parameter   FSM_HALT_WAIT_IDLE    = 6'b10_1010;
parameter   FSM_HALT_HALTED       = 6'b10_1011;
parameter   FSM_DB_EMIT_STOP      = 6'b10_1001;
parameter   FSM_DB_WAIT_PRE       = 6'b11_1000;
parameter   FSM_DB_WAIT_IDLE      = 6'b11_1010;
parameter   FSM_DB_HALTED         = 6'b11_1011;
parameter   FSM_DB_RETIRE         = 6'b11_1100;

parameter    HALT_DB_BIT          = 4;

// @halt_PROC:
//
reg                           hold_halt;
reg                           ca_sgl_step_finished;
reg                           ca_sgl_step_finished_r;
reg                           do_halt;
reg                           do_halt_r;
reg                           do_unhalt;
reg                           do_wakeup;
reg                           gb_sys_halt_nxt;
reg                           gb_sys_sleep_nxt;
reg                           sys_run_ack_nxt;
reg                           sys_halt_ack_nxt;
reg                           halted_on_rst_nxt;
wire                          halted_on_rst_next;
reg                           sync_halt;
reg                           sys_run_ack_r;
reg                           sys_halt_ack_r;
reg                           sys_reset_done;

// @fsm_halt_nxt_PROC:
//
reg [5:0]                     fsm_halt_nxt;
wire[5:0]                     fsm_halt_next;
reg                           stop_nxt;
reg                           stop_r;
wire                          i_wevt_wake_nxt;

reg                           issue_restart_r;
reg                           issue_restart_nxt;

// @fsm_halt_reg_PROC:
//
reg                           halted_on_rst_r;
reg [5:0]                     fsm_halt_r;

reg                           wlfc_wakeup_req;    // Wake up from wevt

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @halt_PROC                                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: halt_PROC

  // Retain state to denote the period in which the machine is halted
  // because of an initial HALT_ON_RESET.
  //
  halted_on_rst_nxt      = halted_on_rst_r & (fsm_halt_nxt != FSM_RUN)
                         & (~wa_aux_pc_wen)
                         ;

  // A synchronous halt is performed when:
  //
  //  (1) On the presence of a BRK(_S) instruction in the commit stage.
  //
  //  (2) The post-commit of normal instruction.
  //
  //  (3) triple fault halt req
  //
  //  (4) The commit of a sleep instruction
  
  sync_halt              = ca_cmt_brk_evt                   // (1)
                         | ca_cmt_isi_evt                   // (2)
                         | ar_aux_debug_r[`npuarc_DEBUG_TF]        // (3)
                         | ( ca_sleep_evt                   // (4)
                           & (~ar_aux_debug_r[`npuarc_DEBUG_IS]))
                         ;

  // Prevent (asynchronous) machine halts until the following
  // conditions have been attained:
  //
  hold_halt              = (~sync_halt)
                         & (   ca_uop_active
                             | ct_replay
                             | excpn_restart
                             | (excpn_hld_halt & (!ar_aux_status32_r[`npuarc_H_FLAG]))
                             | wa_restart_r
                             | wa_restart_kill_r
                           )
                         ;

  ca_sgl_step_finished = ca_finish_sgl_step
                       | ca_sgl_step_finished_r;


  // Initiate the halt process when:
  //
  do_halt                = biu_idle_r
                         & ifu_idle_r
                         & (ar_tags_empty_r & 
                             (  dmp_idle_r
                              | (dmp_idle1_r & ca_sgl_step_finished)
                             )
                           )
                         & (~excpn_hld_halt | ar_aux_status32_r[`npuarc_H_FLAG])
                         ;

  //
  //
  do_unhalt              = ~ar_aux_status32_r[`npuarc_H_FLAG] &  gb_sys_halt_r
                         ;

  // Assert global halted state on transition to halted state.
  //
  gb_sys_halt_nxt        = ar_aux_status32_r[`npuarc_H_FLAG]
                         & ( (fsm_halt_nxt == FSM_HALT_HALTED)
                           | (fsm_halt_r   == FSM_HOR_INIT)
                           | (fsm_halt_nxt == FSM_HOR_INIT)
                           | (fsm_halt_nxt == FSM_DB_WAIT_PRE)
                           | (fsm_halt_nxt == FSM_DB_WAIT_IDLE)
                           | (fsm_halt_nxt == FSM_DB_HALTED)
                           | (fsm_halt_nxt == FSM_DB_RETIRE)
                           | (fsm_halt_nxt == FSM_UNHALT)
                           )
                         ;

  // Assert global sleep state on transition to sleeping state.
  //
  gb_sys_sleep_nxt       = ar_aux_debug_r[`npuarc_DEBUG_ZZ]
                         & ( (fsm_halt_nxt == FSM_HALT_HALTED)
                           | (fsm_halt_nxt == FSM_DB_WAIT_PRE)
                           | (fsm_halt_nxt == FSM_DB_WAIT_IDLE)
                           | (fsm_halt_nxt == FSM_DB_HALTED)
                           | (fsm_halt_nxt == FSM_DB_RETIRE)
                           | (fsm_halt_nxt == FSM_UNHALT)
                           )
                         ;

  // Acknowledge an external run request on the transition out of the halted
  // state.
  //
  sys_run_ack_nxt        = (gb_sys_run_req_r == 1'b1)
                         & (fsm_halt_r   != FSM_HALT_HALTED)
                         ;

  // Acknowledge an external halt request on the transition into the
  // halted state.
  //
  sys_halt_ack_nxt       = (gb_sys_halt_req_r == 1'b1)
                         & (fsm_halt_nxt == FSM_HALT_HALTED)
                         ;


  //
  //
  hlt_do_halt            = sys_halt_ack_nxt
                         ;

  //
  //
  hlt_do_unhalt          = sys_run_ack_nxt
                         ;


  // Identify when reset procedure is finished
  //
  sys_reset_done         = gb_sys_reset_done_r; 

  // WLFC wakeup request (sticky)
  //
  wlfc_wakeup_req        = dbg_wf_r 
                         & (!wa_lock_flag_r)
                         ;



end // block: halt_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// @fsm_halt_nxt_PROC:                                                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: fsm_halt_nxt_PROC

  // Assign default state transition
  //
  stop_nxt          = 1'b0;
  issue_restart_nxt = 1'b0;
  pipe_block_ints   = 1'b1;
  do_wakeup         = 1'b0;
  wake_from_wait    = 1'b0;

  hlt_debug_evt     = 1'b0;
  hlt_issue_reset   = 1'b0;
  
  hlt_wait_idle     = 1'b0;
  
  fsm_halt_nxt      = fsm_halt_r;

  wlfc_wakeup       = 1'b0;

  case (fsm_halt_r)

  // FSM_HOR_INIT:
  // Wait for Cache Initialization before proceeding to
  // Halted State
  //
  FSM_HOR_INIT: 
  begin
    pipe_block_ints = 1'b0;
    if (do_halt)
      fsm_halt_nxt          = FSM_HALT_HALTED;

  end // state : FSM_HOR_INIT

   // FSM_WAIT_RESET: Wait until the various sub-systems (typically
   // cache tag macros have been appropriately initialised before
   // attempting to respond to any halt requests).
   //
   FSM_WAIT_RESET: 
   begin
      pipe_block_ints = 1'b0;
      if ( (sys_reset_done == 1'b1)
         )
        fsm_halt_nxt          = FSM_RUN;
   end

   // FSM_RUN:
   //
   FSM_RUN: 
   begin
    pipe_block_ints = 1'b0;

    if ( sync_halt )
    begin
      stop_nxt            = 1'b1;
      issue_restart_nxt   = 1'b1;
      fsm_halt_nxt        = FSM_HALT_WAIT_PRE;
    end
    else if (   gb_sys_halt_req_r
             || ar_aux_status32_r[`npuarc_H_FLAG])
    begin
      fsm_halt_nxt        = FSM_HALT_EMIT_STOP;
    end
    else if ( db_request )
    begin
      fsm_halt_nxt        = FSM_DB_EMIT_STOP;
    end  
  end

  // FSM_*_EMIT_STOP:
  //
  FSM_HALT_EMIT_STOP: 
  begin
    if (hold_halt == 1'b0)
    begin
      stop_nxt               = 1'b1;
      issue_restart_nxt      = 1'b1;

      fsm_halt_nxt           = FSM_HALT_WAIT_PRE;
    end
  end

  // FSM_*_WAIT_PRE:
  //
  FSM_DB_WAIT_PRE,
  FSM_HALT_WAIT_PRE: 
  begin
    // Wait till Restart is issued for hlt_restart
    if (wa_restart_r == 1'b1)
    begin
      fsm_halt_nxt           =  FSM_HALT_WAIT_IDLE;
    end
  end // FSM_*_WAIT_PRE

   // FSM_*_WAIT_IDLE:
   //
  FSM_DB_WAIT_IDLE,
  FSM_HALT_WAIT_IDLE: 
  begin
     hlt_wait_idle = 1'b1;
     
       // If Replay (2nd Restart) issued before Hold process is completed
       // Need to restart the Halt process
       // This can occur if a replay is applied after hlt_restart
       if (wa_restart_r && !fch_stop_r)
       begin
         // A restart issued after an earlier stop; Mostly likely DC4 exception
         // Need to restart the Halt process
         fsm_halt_nxt        = FSM_HALT_EMIT_STOP;
       end
       else if (do_halt_r == 1'b1)
       begin
         fsm_halt_nxt           = (db_request)
                                ? FSM_DB_HALTED
                                : FSM_HALT_HALTED
                              ;
         hlt_debug_evt          = db_request;
       end
   end

  // FSM_DB_HALTED
  //
  FSM_DB_HALTED: 
  begin
    if (ca_cmt_dbg_evt == 1'b1)
      fsm_halt_nxt            = FSM_DB_RETIRE;
  end

  // FSM_DB_RETIRE
  //
  FSM_DB_RETIRE: 
  begin
    hlt_debug_evt             = 1'b1;

    // After the retirement of a debug instruction, return to the
    // halted state to process further debug requests or to wait for
    // an unhalt request.
    //
    fsm_halt_nxt              = FSM_HALT_HALTED;
  end

  // FSM_HALT_HALTED
  //
  FSM_HALT_HALTED: 
  begin

    // On a debug request, in the halted state, replay the original FSM
    // sequence (post-halt), to revert back to the halted state upon
    // completion.
    //
    // 1. On Debug request service Debug & return
    // 2. No External Halt Request
    // 2.1 Run Request when Halted
    // 2.2 Wakeup from Sleep or Halted
    // 2.3 Wake from Sleep due to:
    // 2.3.1  external event after WEVT
    // 2.3.2  lock-flag clear after WLFC
    // 2.3.3  interrupt preemption, already qualified with STATUS32.IE
    //
    if ((db_request == 1'b1)                              // 1
       )
      fsm_halt_nxt           = FSM_DB_WAIT_IDLE;
    else if (gb_sys_halt_req_r == 1'b0)                  // 2
    begin    
      if ( (   (ar_aux_status32_r[`npuarc_H_FLAG] == 1'b1)      // 2.1
             & (gb_sys_run_req_r == 1'b1))
         | (   (ar_aux_status32_r[`npuarc_H_FLAG] == 1'b0)      // 2.2
             & (ar_aux_debug_r[`npuarc_DEBUG_ZZ]  == 1'b0))     
         | (   (ar_aux_status32_r[`npuarc_H_FLAG] == 1'b0)      // 2.3
             & (ar_aux_debug_r[`npuarc_DEBUG_ZZ]  == 1'b1)
             & (  i_wevt_wake_nxt                        // 2.3.1
                | wlfc_wakeup_req                        // 2.3.2
                | int_preempt                            // 2.3.3
             )
           )
         )
      begin
        fsm_halt_nxt           = FSM_UNHALT;
        do_wakeup              = 1'b1;
        wake_from_wait         = i_wevt_wake_nxt
                               | wlfc_wakeup_req
                               ;
        wlfc_wakeup            = wlfc_wakeup_req;

      end // No Ext Halt Req
    end // 
  end // FSM_HALT_HALTED

  // FSM_UNHALT
  //
  FSM_UNHALT:
  begin
    if ( (ar_aux_status32_r[`npuarc_H_FLAG] == 1'b0)
       & (ar_aux_debug_r[`npuarc_DEBUG_ZZ]  == 1'b0))
    begin
    // On an attempt to unhalt from the initial reset state, issue the
    // reset sequence from the uop_seq module and stall further debug
    // transaction until the sequence has committed.
    //
      hlt_issue_reset          =  halted_on_rst_r;
      issue_restart_nxt        = ~halted_on_rst_r;

      fsm_halt_nxt             = (halted_on_rst_r == 1'b1)
                               ? FSM_WAIT_RESET
                               : FSM_WAIT_RUN
                               ;
    end
  end
  
  FSM_WAIT_RUN:
  begin
    if (wa_restart_r)
    begin
      fsm_halt_nxt             = FSM_RUN;
    end      
  
  end
  default:;
  endcase // case (fsm_halt_r)

  
end // block: fsm_halt_nxt_PROC

assign i_wevt_wake_nxt  = dbg_we_r & arc_event_r;


assign fsm_halt_next = 
                        fsm_halt_nxt;

assign halted_on_rst_next =
                           halted_on_rst_nxt;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Halt Manager State                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: fsm_halt_reg_PROC
  if (rst_a == 1'b1) begin
    halted_on_rst_r <= 1'b1;
    fsm_halt_r      <= FSM_HOR_INIT;
  end
  else begin
    halted_on_rst_r <= halted_on_rst_next;
    fsm_halt_r      <= fsm_halt_next;
  end
end // block: fsm_halt_reg_PROC

always @(posedge clk or posedge rst_a)
begin : issue_restart_reg_PROC
  if (rst_a == 1'b1) begin
    do_halt_r       <= 1'b0;
    issue_restart_r <= 1'b0;
    stop_r          <= 1'b0;
    ca_sgl_step_finished_r <= 1'b0;
  end
  else begin
    do_halt_r       <= do_halt;
    issue_restart_r <= issue_restart_nxt;
    stop_r          <= stop_nxt;
    ca_sgl_step_finished_r <= (  ca_finish_sgl_step
                               | ca_sgl_step_finished_r
                              )
                            & (!do_halt);

  end
end

always @(posedge clk or posedge rst_a)
begin: sys_halt_regs_PROC
  if (rst_a == 1'b1) begin
    gb_sys_halt_r        <= 1'b1;
    gb_sys_sleep_r       <= 1'b0;
    sys_run_ack_r        <= 1'b0;
    sys_halt_ack_r       <= 1'b0;
  end
  else begin
    gb_sys_halt_r        <= gb_sys_halt_nxt;
    gb_sys_sleep_r       <= gb_sys_sleep_nxt;
    sys_run_ack_r        <= sys_run_ack_nxt;
    sys_halt_ack_r       <= sys_halt_ack_nxt;
  end
end // block: sys_halt_regs_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output Assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign db_active_r       = fsm_halt_r[HALT_DB_BIT];
assign hlt_stop          = stop_r;         
assign hlt_restart_r     = issue_restart_r;
assign gb_sys_run_ack_r  = sys_run_ack_r;
assign gb_sys_halt_ack_r = sys_halt_ack_r;
assign sleep_hlt_wake    = do_unhalt 
                         | do_wakeup
                         ;
assign hor_clock_enable_nxt = (fsm_halt_r == FSM_HOR_INIT) 
                            ? 1'b1
                            : 1'b0
                            ;

assign wevt_wakeup_r    = dbg_we_r & arc_event_r & wake_from_wait;
// spyglass enable_block W193

endmodule // alb_halt_mgr
