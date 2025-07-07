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
//
//
//
//
//
// ===========================================================================
// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"
//
// Description:
//
//  This module instantiates, and connects together, the ancillary pipeline
//  control modules of the Execution Unit.
//
//  The module hierarchy, at and below this module, is:
//
//         alb_exex_ctrl
//            |
//            |
//            +-- alb_irq_unit
//            |
//            |
//            +-- alb_smart
//
// ===========================================================================

// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//
`include "npuarc_ucode_const.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_exec_ctrl (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,              // clock signal
  input                       smt_unit_clk,     // SMT arch. clock gate
  input                       rst_a,            // reset signal
  input                       l1_clock_active,  //


  ////////// Machine Architectural state /////////////////////////////////////
  //
  input  [`npuarc_DATA_RANGE]        ar_aux_status32_r,// aux. STATUS32
  input  [`npuarc_DATA_RANGE]        ar_aux_debug_r,   // aux. DEBUG
  input                       dbg_we_r,         // waiting for event
  input                       dbg_wf_r,         // waiting for LF to clear

  ////////// Global Machine State ////////////////////////////////////////////
  //
  input                       gb_sys_reset_done_r,//
  ////////// BVCI Debug Command Interface ////////////////////////////////////
  //
  input                       dbg_cmdval,       // |cmdval| from JTAG
  output                      dbg_cmdack,       // BVCI |cmd| acknowledge
  input  [`npuarc_DBG_ADDR_RANGE]    dbg_address,      // |addres|s from JTAG
  input  [`npuarc_DBG_BE_RANGE]      dbg_be,           // |be| from JTAG
  input  [`npuarc_DBG_CMD_RANGE]     dbg_cmd,          // |cmd| from JTAG
  input  [`npuarc_DBG_DATA_RANGE]    dbg_wdata,        // |wdata| from JTAG
  input                       dbg_rspack,       // |rspack| from JTAG
  output                      dbg_rspval,       // BVCI response valid
  output [`npuarc_DBG_DATA_RANGE]    dbg_rdata,        // BVCI response EOP
  output                      dbg_reop,         // BVCI response error
  output                      dbg_rerr,         // BVCI data to Debug host

  ////////// APB debug interface /////////////////////////////////////////////

  input                       dbg_prot_sel,

  input                       pclkdbg_en,
  input                     presetdbgn,
  input [31:2]                paddrdbg,
  input                       pseldbg,
  input                       penabledbg,
  input                       pwritedbg,
  input [31:0]                pwdatadbg,

  output                      preadydbg,
  output [31:0]               prdatadbg,
  output                      pslverrdbg,

  input   [7:0]               arcnum,
  input                       dbgen,
  input                       niden,


  ////////// Debug/Pipeline Interface ////////////////////////////////////////
  //
  output                      db_valid,         //
  output                      db_active,        //
  output                      db_active_r,      //
  output [`npuarc_DATA_RANGE]        db_inst,          //
  output [`npuarc_DATA_RANGE]        db_limm,          //
  output [`npuarc_DATA_RANGE]        db_data,          //
  output                      db_sel_limm0,     //
  output                      db_sel_limm1,     //
  output                      debug_reset,
  input                       db_restart,       // Debug is restarted
  input                       ca_cmt_dbg_evt,   // CA commits DBG Insn.
  input                       ca_db_exception_r, // CA exception on DBG

  //////////  clock control block //////////////////////////////////////////
  //
  output                      db_clock_enable_nxt, // Clock needs to be enb
  input                       ar_clock_enable_r,   // 

  ////////// Retirement Interface ////////////////////////////////////////////
  //
  input  [`npuarc_DATA_RANGE]        wa_rf_wdata0_lo_r,//
  input  [`npuarc_DATA_RANGE]        wa_rf_wdata1_lo_r,//


  ////////// Halt Interface to EXEC_PIPE /////////////////////////////////////
  //
  input                       ca_cmt_brk_evt,   // Commit of BRK insn.
  input                       ca_cmt_isi_evt,   // Instruction-Step evt.
  input                       ca_sleep_evt,     // Commit sleep insn
  input                       arc_event_r,      // external wakeup event
  output                      sleep_hlt_wake,   // Sleep Halt Wake
  output                      wevt_wakeup_r,    // WEVT wakeup event
  input                       wa_lock_flag_r,   // lock flag value
  output                      wlfc_wakeup,      // WLFC wakeup event
  output                      wake_from_wait,   // re-enable clock after wait
  input                       ca_pass_eslot,    // commit return from eslot
  input [`npuarc_PC_RANGE]           ca_pc_jump,       // for smart jump instr address
  input [`npuarc_PC_RANGE]           aux_eret_addr,    // for smart exception return addr
  output                      smt_cap_rst_vec,
  input [`npuarc_PC_RANGE]           ar_pc_save_r,
  input                       aux_read,
  input                       aux_write,


  ////////// Interrupt/Exception Interface ///////////////////////////////////
  //
  input [`npuarc_IRQM_RANGE]         timer0_irq_1h,


  input [`npuarc_IRQM_RANGE]         wdt_int_timeout_1h_r,
  input  [`npuarc_IRQM_RANGE]         pct_int_overflow_r,
  input [`npuarc_IRQE_RANGE]         irq_r,          // synchronous output

 // input                       clk_resync,
 // output                      irq_sync_req_a,

  input                      irq_clk_en_r,        //multi-cycle clock enable for irq inputs

  input                       int_preempt,        //interrupt preempted to wake up from sleep
 
  ////////// Interrupt/Exception Interface ///////////////////////////////////
  //
  input   [`npuarc_IRQN_RANGE]       cpu_accept_irq,     //
  input                       irq_ack,            //
  input   [7:0]               irq_ack_num,        //

  output                      irq_req,            //
  output  [7:0]               irq_num,            //
  output  [`npuarc_IRQLGN_RANGE]     irq_w,              //
  output                      irq_preempts,       //
  output                      irq_preempts_nxt,   //
  input   [`npuarc_IRQLGN_RANGE]     irq_ack_w_r,        //

  input       [`npuarc_DATA_RANGE]   aux_wdata, 
  input                       aux_irq_ren_r,        //  (X3) Aux     Enable
  input       [11:0]          aux_irq_raddr_r,      //  (X3) Aux Address
  input                       aux_irq_wen_r,        //  (WA) Aux     Enable
  input       [11:0]          aux_irq_waddr_r,      //  (WA) Aux Address
  output      [`npuarc_DATA_RANGE]   irq_aux_rdata,        //  (X3) LR read data
  output                      irq_aux_illegal,      //  (X3) SR/LR illegal
  output                      irq_aux_k_rd,         //  (X3) needs Kernel Read
  output                      irq_aux_k_wr,         //  (X3) needs Kernel W perm
  output                      irq_aux_unimpl,       //  (X3) Invalid
  output                      irq_aux_serial_sr,    //  (X3) SR group flush pipe
  output                      irq_aux_strict_sr,    //  (X3) SR flush pipe

  output    [`npuarc_DATA_RANGE]     ar_aux_icause0_r,  // from alb_irq_unit)
  output    [`npuarc_DATA_RANGE]     ar_aux_icause1_r,  // from alb_irq_unit)
  output    [`npuarc_DATA_RANGE]     ar_aux_icause2_r,  // from alb_irq_unit)
  input     [`npuarc_DATA_RANGE]     ar_aux_irq_act_r,     //


  //////////bist   test////////////////////////////////////////////////////

  ////////// Halt Interface to EXEC_PIPE /////////////////////////////////////
  //
  input                       ar_tags_empty_r,    // Grad. Buf empty
  input                       ca_uop_active,      // UOP sequencer is active
  input                       wa_restart_r,       // Pipeline flush
  input                       wa_restart_kill_r,  //
  input                       fch_stop_r,         // EXU requests IFU halt
  input                       excpn_restart,      //
  input                       ct_replay,          // Aux Replay
  input                       excpn_hld_halt,     //
  input                       wa_aux_pc_wen,      // Debug write enable for PC
  input                       ca_finish_sgl_step,

  output                      hlt_stop,           // Halt. reqs. IFU stop
  output                      hlt_restart_r,      // Halt. reqs. pipe flush
  output                      hlt_issue_reset,    //
  output                      hor_clock_enable_nxt, // Arch. Clock Enable
  output                      hlt_do_halt,        //
  output                      hlt_do_unhalt,      //
  output                      pipe_block_ints,    //
  output                      hlt_wait_idle,      //
  input   [`npuarc_DATA_RANGE]       wa_sr_data_r,       // aux write data
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Not all bits used
  input   [`npuarc_INTEVT_RANGE]     int_evts,
  // leda NTL_CON13C on  

  ////////// Auxiliary interface for (SMT) SR/LR instructions ////////////
  //
  input                       aux_smt_active,       //  AUX smart is active
  input                       aux_smt_ren_r,        //  (X3) Aux     Enable
  input                       aux_smt_raddr_r,      //  (X3) Aux Address
  input                       aux_smt_wen_r,        //  (WA) Aux     Enable
  input                       aux_smt_waddr_r,      //  (WA) Aux Address
  output      [`npuarc_DATA_RANGE]   smt_aux_rdata,        //  (X3) LR read data
  output                      smt_aux_illegal,      //  (X3) SR/LR illegal
  output                      smt_aux_k_rd,         //  (X3) need Kernel Read
  output                      smt_aux_k_wr,         //  (X3) need Kernel Write
  output                      smt_aux_unimpl,       //  (X3) Invalid    
  output                      smt_aux_serial_sr,    //  (X3) SR group flush pipe
  output                      smt_aux_strict_sr,    //  (X3) SR flush pipe
  output                      smt_unit_enable,       //  
  
  input                       ca_br_evt,

  input                       ca_pass,
  input                       ca_trap_op_r,

  input       [`npuarc_PC_RANGE]     ar_pc_r,

  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Bit0 is not used in addr bus

  input       [`npuarc_DATA_RANGE]   ar_aux_lp_end_r,      // LP_END aux register
  // LJ:  Not used in all config
  input       [`npuarc_PC_RANGE]     ar_pc_nxt, 
  input       [`npuarc_PFLAG_RANGE]  wa_aux_status32_nxt,
  // leda NTL_CON13C on

  // leda NTL_CON13C off
  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  Not all bits used
  input       [`npuarc_INTEVT_RANGE] excpn_evts,
  // leda NTL_CON13C on
  // leda NTL_CON37 on
  input                       ca_zol_lp_jmp,
  input       [`npuarc_PC_RANGE]     wa_pc_r,

  ////////// IFU/DMP Halt Interface //////////////////////////////////////////
  //
  input                       ifu_idle_r,         // IFU is idle
  input                       dmp_idle_r,         // DMP is idle
  input                       dmp_idle1_r,        // DMP is idle (ignore dmp excpn)
  input                       biu_idle_r,         // BIU is idle
  
  ////////// External Halt Interface /////////////////////////////////////////
  //
  input                       gb_sys_halt_req_r,  // Sync. halt req.
  output                      gb_sys_halt_ack_r,  // Sync. halt ack.
  output                      sys_halt_ack_r,     // Sync. halt ack pulse.

  input                       gb_sys_run_req_r,   // Sync. run req.
  output                      gb_sys_run_ack_r,   // Sync. run ack.

  output                      gb_sys_halt_r,      // System halted state
  output                      gb_sys_sleep_r      // System sleeping state
);

// Outputs of u_alb_debug
//
wire                          db_request;

// Outputs of u_alb_halt_mgr
//
wire                          hlt_debug_evt;



wire                          dbg_ra_r;
assign dbg_ra_r = ar_aux_debug_r[`npuarc_DEBUG_RA];

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// alb_debug: Debug Unit Instantiation                                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_debug u_alb_debug(
  .clk                   (clk                ),
  .rst_a                 (rst_a              ),
  .l1_clock_active       (l1_clock_active    ),  //
  .hlt_debug_evt         (hlt_debug_evt      ),
  .wa_rf_wdata0_lo_r     (wa_rf_wdata0_lo_r  ), //
  .wa_rf_wdata1_lo_r     (wa_rf_wdata1_lo_r  ), //
  .gb_sys_halt_r         (gb_sys_halt_r      ),

  .wa_commit_dbg         (ca_cmt_dbg_evt     ),
  .wa_invalid_instr_r    (ca_db_exception_r  ),

  .dbg_ra_r              (dbg_ra_r           ),
  .dbg_cmdval            (dbg_cmdval         ),
  .dbg_cmdack            (dbg_cmdack         ),
  .dbg_address           (dbg_address        ),
  .dbg_be                (dbg_be             ),
  .dbg_cmd               (dbg_cmd            ),
  .dbg_wdata             (dbg_wdata          ),
  .dbg_rspack            (dbg_rspack         ),
  .dbg_rspval            (dbg_rspval         ),
  .dbg_rdata             (dbg_rdata          ),
  .dbg_reop              (dbg_reop           ),
  .dbg_rerr              (dbg_rerr           ),

  .dbg_prot_sel          (dbg_prot_sel       ),
  .pclkdbg_en            (pclkdbg_en         ),
  .presetdbgn (presetdbgn),
  .paddrdbg               (paddrdbg             ),
  .pseldbg                (pseldbg              ),
  .penabledbg             (penabledbg           ),
  .pwritedbg              (pwritedbg            ),
  .pwdatadbg              (pwdatadbg            ),
  .preadydbg              (preadydbg            ),
  .prdatadbg              (prdatadbg            ),
  .pslverrdbg             (pslverrdbg           ),
  .dbgen                  (dbgen                ),
  .niden                  (niden                ),
  .arcnum                 (arcnum),

  .db_request            (db_request         ),
  .db_valid              (db_valid           ),
  .db_active             (db_active          ), //
  .db_inst               (db_inst            ),
  .db_limm               (db_limm            ),
  .db_data               (db_data            ),
  .db_sel_limm0          (db_sel_limm0       ),
  .db_sel_limm1          (db_sel_limm1       ),
  .debug_reset           (debug_reset        ),
  .db_restart            (db_restart         ),
  .db_clock_enable_nxt   (db_clock_enable_nxt ),
  .ar_clock_enable_r     (ar_clock_enable_r  )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// alb_halt: Halt/Low-Power State Management Logic                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_halt_mgr u_alb_halt_mgr(
  .clk                   (clk                ),
  .rst_a                 (rst_a              ),
  .ar_aux_status32_r     (ar_aux_status32_r  ),
  .ar_aux_debug_r        (ar_aux_debug_r     ),
  .dbg_we_r              (dbg_we_r           ),
  .dbg_wf_r              (dbg_wf_r           ),
  .db_request            (db_request         ),
  .ca_cmt_dbg_evt        (ca_cmt_dbg_evt     ),
  .hlt_debug_evt         (hlt_debug_evt      ),
  .db_active_r           (db_active_r        ),
  .ca_cmt_brk_evt        (ca_cmt_brk_evt     ),
  .ca_cmt_isi_evt        (ca_cmt_isi_evt     ),
  .ca_sleep_evt          (ca_sleep_evt       ),
  .sleep_hlt_wake        (sleep_hlt_wake     ),
  .arc_event_r           (arc_event_r        ),
  .wevt_wakeup_r         (wevt_wakeup_r      ),
  .wa_lock_flag_r        (wa_lock_flag_r     ),
  .wlfc_wakeup           (wlfc_wakeup        ),
  .wake_from_wait        (wake_from_wait     ),
  .ar_tags_empty_r       (ar_tags_empty_r    ),
  .ca_uop_active         (ca_uop_active      ),
  .wa_restart_r          (wa_restart_r       ),
  .wa_restart_kill_r     (wa_restart_kill_r  ),
  .fch_stop_r            (fch_stop_r         ),
  .excpn_restart         (excpn_restart      ),
  .ct_replay             (ct_replay          ),
  .excpn_hld_halt        (excpn_hld_halt     ),
  .wa_aux_pc_wen         (wa_aux_pc_wen      ),
  .ca_finish_sgl_step    (ca_finish_sgl_step ),
  .hlt_stop              (hlt_stop           ),
  .hlt_restart_r         (hlt_restart_r      ),
  .hlt_issue_reset       (hlt_issue_reset    ),
  .hor_clock_enable_nxt  (hor_clock_enable_nxt),
  .int_preempt           (int_preempt        ),

  .hlt_do_halt           (hlt_do_halt        ),
  .hlt_do_unhalt         (hlt_do_unhalt      ),
  .pipe_block_ints       (pipe_block_ints    ),
  .hlt_wait_idle         (hlt_wait_idle      ),
  .ifu_idle_r            (ifu_idle_r         ),
  .dmp_idle_r            (dmp_idle_r         ),
  .dmp_idle1_r           (dmp_idle1_r        ),
  .biu_idle_r            (biu_idle_r         ),
  .gb_sys_reset_done_r   (gb_sys_reset_done_r),
  .gb_sys_run_req_r      (gb_sys_run_req_r   ),
  .gb_sys_halt_req_r     (gb_sys_halt_req_r  ),
  .gb_sys_run_ack_r      (gb_sys_run_ack_r   ),
  .gb_sys_halt_ack_r     (gb_sys_halt_ack_r  ),
  .gb_sys_halt_r         (gb_sys_halt_r      ),
  .gb_sys_sleep_r        (gb_sys_sleep_r     )
);



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// alb_irq_unit: Interrupt detection and prioritisation logic               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//`if (`IRQ_E > 0)
//wire [`IRQE_RANGE] irq_r; 
//`endif

//`define TIMER0_INT_SANITY_CHK

npuarc_alb_irq_unit u_alb_irq_unit(
  .aux_write             (aux_write          ),
  .aux_read              (aux_read           ),
  .aux_wdata             (aux_wdata          ),
  .aux_irq_ren_r         (aux_irq_ren_r      ),
  .aux_irq_raddr_r       (aux_irq_raddr_r    ),
  .aux_irq_wen_r         (aux_irq_wen_r      ),
  .aux_irq_waddr_r       (aux_irq_waddr_r    ),
  .irq_aux_rdata         (irq_aux_rdata      ),
  .irq_aux_illegal       (irq_aux_illegal    ),
  .irq_aux_k_rd          (irq_aux_k_rd       ), 
  .irq_aux_k_wr          (irq_aux_k_wr       ),
  .irq_aux_unimpl        (irq_aux_unimpl     ),
  .irq_aux_serial_sr     (irq_aux_serial_sr  ),
  .irq_aux_strict_sr     (irq_aux_strict_sr  ),
  .cpu_accept_irq        (cpu_accept_irq     ),
  .irq_req               (irq_req            ),
  .irq_num               (irq_num            ),
  .irq_w                 (irq_w              ),
  .irq_preempts          (irq_preempts       ),
  .irq_preempts_nxt      (irq_preempts_nxt   ),
  .irq_ack               (irq_ack            ),
  .irq_ack_num           (irq_ack_num        ),
  .irq_ack_w_r           (irq_ack_w_r        ),
  .ar_aux_icause0_r   (ar_aux_icause0_r),
  .ar_aux_icause1_r   (ar_aux_icause1_r),
  .ar_aux_icause2_r   (ar_aux_icause2_r),

  .ar_aux_irq_act_r      (ar_aux_irq_act_r   ),

  .irq_r                 (irq_r              ),
  .timer0_irq_1h         (timer0_irq_1h      ),
  .wdt_int_timeout_1h_r    (wdt_int_timeout_1h_r ),
  .pct_int_overflow_r          (pct_int_overflow_r   ),
  .irq_clk_en_r          (irq_clk_en_r       ),
  .clk                   (clk                ),
  .rst_a                 (rst_a              )
);


//`if ((`HAS_INTERRUPTS == 1) && (`IRQ_E > 0))

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// alb_irq_resync_in: Interrupt asynchronous input resynchronisation logic. //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//alb_irq_resync_in u_alb_irq_resync_in(

  //.irq_r                 (irq_r              ), 

//`if (`IRQ_OUTPUT_REG > 0)
  //.irq_clk_en_r          (irq_clk_en_r       ),
//`endif

 // `if (`IRQ_GATED_SYNC == 1)  
 // .clk                   (clk_resync         ), 
 // .irq_sync_req_a        (irq_sync_req_a     ), 
  //`else
  //.clk                   (clk                ), 
  //`endif
  //.rst_a                 (rst_a              )  
  //);
//`endif //`if ((`HAS_INTERRUPTS == 1) && (`IRQ_E > 0))

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire    ca_pass_jump;
assign  ca_pass_jump = ca_pass;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Smart module: Small Real-Time trace                                      //
//                                                                          //
//   The Smart module captures non-sequential instruction trace points.     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_smart u_smart (
  .clk                 (smt_unit_clk       ),
  .rst_a               (rst_a              ),

  // WA stage
  .aux_smt_wen_r       (aux_smt_wen_r      ),
  .aux_smt_waddr_r     (aux_smt_waddr_r    ),
  .wa_sr_data_r        (wa_sr_data_r       ),

  // X3 stage
  .aux_smt_active      (aux_smt_active     ),
  .aux_write           (aux_write          ),
  .aux_read            (aux_read           ),
  .aux_smt_ren_r       (aux_smt_ren_r      ),
  .aux_smt_raddr_r     (aux_smt_raddr_r    ),

  .smt_aux_rdata       (smt_aux_rdata      ),
  .smt_aux_illegal     (smt_aux_illegal    ),
  .smt_aux_k_rd        (smt_aux_k_rd       ),
  .smt_aux_k_wr        (smt_aux_k_wr       ),
  .smt_aux_unimpl      (smt_aux_unimpl     ),
  .smt_aux_serial_sr   (smt_aux_serial_sr  ),
  .smt_aux_strict_sr   (smt_aux_strict_sr  ),

  .ca_pass             (ca_pass_jump       ),
  .ca_pass_eslot       (ca_pass_eslot      ),
  .ca_pc_jump          (ca_pc_jump         ),
  .aux_eret_addr       (aux_eret_addr      ),
  .ca_br_evt           (ca_br_evt          ),
  .ca_trap_op_r        (ca_trap_op_r       ),
  .ar_pc_r             (ar_pc_r            ),
  .ar_pc_nxt           (ar_pc_nxt          ),
  .wa_pc_r             (wa_pc_r            ),

  .ar_aux_lp_end_r     (ar_aux_lp_end_r[`npuarc_PC_RANGE]),
  .ca_user_mode_nxt    (wa_aux_status32_nxt[`npuarc_P_U_FLAG]),
  
  .ca_excpn_prol_evt   (excpn_evts[`npuarc_INTEVT_PROLOGUE]),
  .ca_excpn_enter_evt  (excpn_evts[`npuarc_INTEVT_ENTER]),

  .ca_int_prologue_evt (int_evts[`npuarc_INTEVT_PROLOGUE]),
  .ca_int_enter_evt    (int_evts[`npuarc_INTEVT_ENTER]),
  .ca_int_epilogue_evt (int_evts[`npuarc_INTEVT_EPILOGUE]),
  .smt_cap_rst_vec       (smt_cap_rst_vec      ),
  .ar_pc_save_r          (ar_pc_save_r         ),

  
  
  .smt_unit_enable     (smt_unit_enable    ),
  .ca_lp_jmp_r         (ca_zol_lp_jmp      )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////



assign sys_halt_ack_r = gb_sys_halt_ack_r;


endmodule // alb_exec_ctrl
