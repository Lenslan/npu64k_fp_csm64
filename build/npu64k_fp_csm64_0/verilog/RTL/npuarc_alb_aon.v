// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2017 Synopsys, Inc. All rights reserved.
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
//    #     #       #####             ##     ####   #    #
//   #  #   #       #   #            #  #   #    #  ##   #
//  #    #  #       #####           #    #  #    #  # #  #
//  #### #  #       #    #          ######  #    #  #  # #
//  #    #  #       #    #          #    #  #    #  #   ##
//  #    #  #####   ###### #######  #    #   ####   #    #
//
// ===========================================================================
//
// Description:
//  The alb_aon module instantiates all modules under the always-on-power
//  domain.  This is a purely structural Verilog module,
//  containing no actual logic.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_aon (

  output                         ar_save_clk,
  input                         ar_save_en_r,
  input                     clk_ungated,

  ////////// External Event Interface ////////////////////////////////////////
  //
  input                       arc_event_a,      // Async. event signal

  input                       db_active,
  input                       dbg_cache_rst_disable,  // cache behavior at reset
  input                       dccm_dmi_priority,      // DCCM DMI priority
  ////////// External Halt Request Interface /////////////////////////////////
  //
  input                       arc_halt_req_a,   // Async. halt req.
  input                       arc_run_req_a,    // Async. run req.
  output                      arc_halt_ack,     //
  output                      arc_run_ack,      //

  ////////// Interrupt signals ///////////////////////////////////////////////
  //
  input                       irq17_a, // Async. IRQ input
  input                       irq19_a, // Async. IRQ input
  input                       irq21_a, // Async. IRQ input
  input                       irq22_a, // Async. IRQ input
  input                       irq23_a, // Async. IRQ input
  input                       irq24_a, // Async. IRQ input
  input                       irq25_a, // Async. IRQ input
  input                       irq26_a, // Async. IRQ input
  input                       irq27_a, // Async. IRQ input
  input                       irq28_a, // Async. IRQ input
  input                       irq29_a, // Async. IRQ input
  input                       irq30_a, // Async. IRQ input
  input                       irq31_a, // Async. IRQ input
  input                       irq32_a, // Async. IRQ input
  input                       irq33_a, // Async. IRQ input
  input                       irq34_a, // Async. IRQ input
  input                       irq35_a, // Async. IRQ input
  input                       irq36_a, // Async. IRQ input
  input                       irq37_a, // Async. IRQ input
  input                       irq38_a, // Async. IRQ input
  input                       irq39_a, // Async. IRQ input
  input                       irq40_a, // Async. IRQ input
  input                       irq41_a, // Async. IRQ input
  input                       irq42_a, // Async. IRQ input
  input                       irq43_a, // Async. IRQ input
  input                       irq44_a, // Async. IRQ input
  input                       irq45_a, // Async. IRQ input
  input                       irq46_a, // Async. IRQ input
  input                       irq47_a, // Async. IRQ input
  input                       irq48_a, // Async. IRQ input
  input                       irq49_a, // Async. IRQ input
  input                       irq50_a, // Async. IRQ input
  input                       irq51_a, // Async. IRQ input
  input                       irq52_a, // Async. IRQ input
  input                       irq53_a, // Async. IRQ input
  input                       irq54_a, // Async. IRQ input
  output  [`npuarc_IRQE_RANGE]       irq_r,


  ////////// Machine Halt Interface //////////////////////////////////////////
  //
  output                     gb_sys_halt_req_r,    // Sync. halt req
  output                     gb_sys_run_req_r,     // Sync run req
  
  input                      core_sys_halt_r,       //
  input                      core_sys_sleep_r,      //
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input [`npuarc_EXT_SMODE_RANGE]   core_sys_sleep_mode_r,
// spyglass enable_block W240
  input                      core_sys_halt_ack_r,
  input                      core_sys_run_ack_r,
  

////////// SRAM memory modules enables and selects ////////////////////////
  //



    input ic_data_cen0,
    input ic_data_cen1,
    input ic_tag_cen0,
    input ic_tag_cen1,
    input ic_tag_cen2,
    input ic_tag_cen3,



    input dc_tag_even_cs_w0,
    input dc_tag_odd_cs_w0,
    input dc_tag_even_cs_w1,
    input dc_tag_odd_cs_w1,
  input dc_data_even_cs_lo,
  input dc_data_even_cs_hi,
  input dc_data_odd_cs_lo,
  input dc_data_odd_cs_hi,

      input dccm_bank0_cs_lo,
      input dccm_bank0_cs_hi,
      input dccm_bank1_cs_lo,
      input dccm_bank1_cs_hi,


  input ntlb_pd0_ce,
  input ntlb_pd1_ce,

  input bc_me0,
  input gs_me0,
  input bc_me1,
  input gs_me1,
  
  //////////// Inputs for clock control module  //////////////////////////////
  //
  input                       dmp_idle_r,
  input                       ifu_idle_r,
  input                       hor_clock_enable_nxt, 
  input                       biu_dmi_clk_en_req,
  input                       db_clock_enable_nxt,
  input                       irq_preempts_nxt,

  ////////// Unit-level clock gating control outputs to clock_ctrl ///////////
  //
  input                       mpy_unit_enable,      // clk ctrl for multiplier
  input                       div_unit_enable,      // clk ctrl for divider
  input                       smt_unit_enable,      // clk ctrl for smart
  input                       dmp_unit_enable,      // clk ctrl for DMP
  input                       dmp_dmu_unit_enable,  // clk ctrl for DMP dmu
  input                       dmp_lq_unit_enable,  // clk ctrl for DMP lq
  input                       ap_unit_enable,
  input                       aux_aps_active,       //
  input                       pct_unit_enable,
  input                       aux_timer_active,
  input                       wake_from_wait,       // wakeup from WEVT, WLFC
  
  //////////// Outputs from clock control module  ////////////////////////////
  //
  output                      ar_clock_enable_r,
  ///////// interrupt sample clock control ///////////////////////////////////
  //
  output                      irq_clk_en_r, 


  output                      cpu_clk_enable,
  input                       cpu_l1_cg_dis,      
  input                       cpu_l1_accept_en,  
  
  output                      l1_clock_active, 
  output                      clk_gated,
  ////////// Unit-level clock gating control outputs from clock_ctrl ///////////
  //
  output                      mpy_unit_clk,         // clk      for multiplier
  output                      div_unit_clk,         // clk      for divider
  output                      smt_unit_clk,         // clk      for EIA
  output                      rtt_unit_clk,
  output                      dmp_unit_clk,         // clk      for DMP
  output                      dmp_dmu_unit_clk,     // clk      for DMP dmu
  output                      dmp_lq_unit_clk,     // clk      for DMP lq
  output                      ap_unit_clk,          // clk      for AP
  output                      ap_aux_clk,           // clk for AP Aux
  output                      pct_unit_clk,        // clk      for PCT

  output                      arc_event_r,         // Sync. evt signal
  output                      dbg_cache_rst_disable_r, 
  output                      dccm_dmi_priority_r,      
  
  // leda NTL_CON13C off
  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  ////////// Interface to the Debug module (BVCI target) /////////////////////
  //

  output                      dbg_cmdack, // BVCI cmd acknowledge
  output                      dbg_rspval, // BVCI response valid
  output  [`npuarc_DBG_DATA_RANGE]   dbg_rdata,  // BVCI response EOP
  output                      dbg_reop,   // BVCI response error
  output                      dbg_rerr,   // BVCI data to Debug host

  // leda NTL_CON13C on
  // leda NTL_CON37 on
 
  input                       core_dbg_cmdack, // BVCI cmd acknowledge
  input                       core_dbg_rspval, // BVCI response valid
  input  [`npuarc_DBG_DATA_RANGE]    core_dbg_rdata,  // BVCI response EOP
  input                       core_dbg_reop,   // BVCI response error
  input                       core_dbg_rerr,   // BVCI data to Debug host
  
  input                       presetdbgn,

  output                      apb_rst,
  
// spyglass disable_block W240
// SMD: input declared but not used
// SJ:  unused in some configs
  input                       rtt_prod_sel,    // enable RTT interf clk (from rtt)
// spyglass enable_block W240
  input                       aux_rtt_active,  // enable RTT interf clk (for aux op)
// spyglass disable_block W240
// SMD: input declared but not used
// SJ:  unused in some configs
  input                       dbg_bh_r,           // break halt
  input                       dbg_sh_r,           // self_halt
  input                       dbg_ah_r,           // actionpoint halt
// spyglass enable_block W240

  ////////// Test interface //////////////////////////////////////////////////
  //
  input                       test_mode,

  input                       wdt_clk,
  //////////// Watchdog timer ////////////////////////////////////////////////
  //
  input                       wdt_ext_timeout_ack_r,   // External timeout acknowledge
  output                      wdt_ext_timeout_r,       // External timeout signal
  output                      wdt_reset,               // Reset timeout signal
  output                      wdt_reset2,              // Reset timeout signal from wdt clk
  output                      wdt_x3_stall,
  input                       x3_kill,

  ////////// Timers aux interface ////////////////////////////////////////////
  //
  input                      aux_tm0_ren_r,
  input      [1:0]           aux_tm0_raddr_r,
  input                      aux_tm0_wen_r,
  input      [1:0]           aux_tm0_waddr_r,
  output     [`npuarc_DATA_RANGE]   tm0_aux_rdata,
  output                     tm0_aux_illegal,
  output                     tm0_aux_k_rd,
  output                     tm0_aux_k_wr,
  output                     tm0_aux_unimpl,
  output                     tm0_aux_serial_sr,
  output  [`npuarc_IRQM_RANGE]      timer0_irq_1h, 

  ////////// Watchdog reset output signals ///////////////////////////////////
  //
  output                     watchdog_reset,     // Assert Watchdog reset

  input                      aux_wdt_ren_r,    // Aux region select for Read
  input      [3:0]           aux_wdt_raddr_r,  // Aux address for Read
  input                      aux_wdt_wen_r,    // Aux region select for Write
  input      [3:0]           aux_wdt_waddr_r,  // Aux address for Write

  output  [`npuarc_DATA_RANGE]      wdt_aux_rdata,     // LR read data
  output                     wdt_aux_illegal,   // SR/LR operation is illegal
  output                     wdt_aux_k_rd,      // op needs Kernel R perm
  output                     wdt_aux_k_wr,      // op needs Kernel W perm
  output                     wdt_aux_unimpl,    // LR/SR reg is not present
  output                     wdt_aux_serial_sr, // SR needs Serialization
  output                     wdt_aux_strict_sr, // SR must Serialize

  ////////// Interface to the IRQ unit ///////////////////////////////////////
  //
  //
  output  [`npuarc_IRQM_RANGE]      wdt_int_timeout_1h_r,    // Interrupt timeout signal

  ////////// Real time counter ///////////////////////////////////////////////
  //
  //
  input                      aux_rtc_ren_r,    // Aux region select for Read
  input      [2:0]           aux_rtc_raddr_r,  // Aux address for Read
  input                      aux_rtc_wen_r,    // Aux region select for Write
  input      [2:0]           aux_rtc_waddr_r,  // Aux address for Write

  output  [`npuarc_DATA_RANGE]      rtc_aux_rdata,     // LR read data
  output                     rtc_aux_illegal,   // SR/LR operation is illegal
  output                     rtc_aux_k_rd,      // op needs Kernel R perm
  output                     rtc_aux_k_wr,      // op needs Kernel W perm
  output                     rtc_aux_unimpl,    // LR/SR reg is not present
  output                     rtc_aux_serial_sr, // SR needs Serialization
  output                     rtc_aux_strict_sr, // SR must Serialize

  input                      rtc_na,            // RTC Non-atomic

  //////////// Common aux bus interface //////////////////////////////////////
  //
  input                       aux_read,
  input                       aux_write,

  input [`npuarc_DATA_RANGE]         wa_sr_data_r,

  ////////// General  signals ////////////////////////////////////////////////
  //
  input                       clk,                // Processor clock

  output                      rst,               // Sync. reset
  input                       rst_a               // Asynchronous reset
);

// Local declarations
//
wire clk_wdt_gated;
wire wdt_unit_en_r;

wire                        timer_unit_enable;


//////////////////////////////////////////////////////////////////////////////
// Wires for clock control module
////////////////////////////////////////////////////////////////////////////////
wire                        clk_timer;
wire                        clk_rtc;
wire                        clk_watchdog;
wire                        clk_resync;
wire                        cpu_resync_clk_enable;  // level 1 clk req
wire rst2_a;
//////////////////////////////////////////////////////////////////////////////
// Wires for resync_in
////////////////////////////////////////////////////////////////////////////////
wire                        irq_sync_req;             //
wire                        irq_sync_req_a;
wire                        arc_halt_req;        //
wire                        arc_run_req;         //

//////////////////////////////////////////////////////////////////////////////
// Wires for irq_resync_in
////////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Modules instantiation                        
//                                                                          //
//////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////
//
// Module instantiation - Clock Control
//
////////////////////////////////////////////////////////////////////////////
wire [`npuarc_EXT_SMODE_RANGE] sys_sleep_mode_r     = core_sys_sleep_mode_r;
npuarc_alb_clock_ctrl u_alb_clock_ctrl (

  .ar_save_clk    (ar_save_clk  ),
  .ar_save_en_r   (ar_save_en_r ),

  .clk_ungated           (clk_ungated          ),
  .cpu_resync_clk_enable (cpu_resync_clk_enable),
  .cpu_clk_enable        (cpu_clk_enable       ),
  .cpu_l1_cg_dis         (cpu_l1_cg_dis        ),    
  .cpu_l1_accept_en      (cpu_l1_accept_en     ), 
  .l1_clock_active       (l1_clock_active      ),
  .sys_sleep_mode_r      (sys_sleep_mode_r     ),
  .sys_sleep_r           (core_sys_sleep_r     ),
  .sys_halt_r            (core_sys_halt_r      ),
  .arc_halt_req          (gb_sys_halt_req_r   ),
  .arc_halt_ack          (core_sys_halt_ack_r ), 
  .arc_run_req           (gb_sys_run_req_r    ),
  .arc_run_ack           (core_sys_run_ack_r  ), 
// SRAM memory modules enables and select signals to LS logic



    .ic_data_cen0        (ic_data_cen0        ),
    .ic_data_cen1        (ic_data_cen1        ),
    .ic_tag_cen0         (ic_tag_cen0         ),
    .ic_tag_cen1         (ic_tag_cen1         ),
    .ic_tag_cen2         (ic_tag_cen2         ),
    .ic_tag_cen3         (ic_tag_cen3         ),



    .dc_tag_even_cs_w0     (dc_tag_even_cs_w0     ),
    .dc_tag_odd_cs_w0      (dc_tag_odd_cs_w0      ),
    .dc_tag_even_cs_w1     (dc_tag_even_cs_w1     ),
    .dc_tag_odd_cs_w1      (dc_tag_odd_cs_w1      ),
  .dc_data_even_cs_lo     (dc_data_even_cs_lo     ),
  .dc_data_even_cs_hi     (dc_data_even_cs_hi     ),
  .dc_data_odd_cs_lo      (dc_data_odd_cs_lo      ),
  .dc_data_odd_cs_hi      (dc_data_odd_cs_hi      ),

      .dccm_bank0_cs_lo     (dccm_bank0_cs_lo  ),
      .dccm_bank0_cs_hi     (dccm_bank0_cs_hi  ),
      .dccm_bank1_cs_lo     (dccm_bank1_cs_lo  ),
      .dccm_bank1_cs_hi     (dccm_bank1_cs_hi  ),


  .ntlb_pd0_ce           (ntlb_pd0_ce),
  .ntlb_pd1_ce           (ntlb_pd1_ce),

.bc_me0                  (bc_me0              ),
.gs_me0                  (gs_me0              ),
  .bc_me1                  (bc_me1              ),
  .gs_me1                  (gs_me1              ),

  .dmp_idle_r            (dmp_idle_r          ),
  .ifu_idle_r            (ifu_idle_r          ),
  .ar_clock_enable_r     (ar_clock_enable_r   ),

  .hor_clock_enable_nxt  (hor_clock_enable_nxt),
  .biu_dmi_clk_en_req    (biu_dmi_clk_en_req),
  .db_clock_enable_nxt   (db_clock_enable_nxt ),
  .irq_sync_req          (irq_sync_req        ),
  .irq_preempts_nxt      (irq_preempts_nxt    ),
  .irq_clk_en_r          (irq_clk_en_r        ),


  .clk_timer             (clk_timer           ),
  .clk_rtc               (clk_rtc             ),
  .wdt_clk               (wdt_clk             ),
  .rst2_a                (rst2_a              ),
  .clk_watchdog          (clk_watchdog        ),
  .clk_resync            (clk_resync          ),
  .clk_gated             (clk_gated           ),
  .mpy_unit_enable      (mpy_unit_enable      ),
  .mpy_unit_clk         (mpy_unit_clk         ),
  .div_unit_enable      (div_unit_enable      ),
  .div_unit_clk         (div_unit_clk         ),
  .smt_unit_enable      (smt_unit_enable      ),
  .smt_unit_clk         (smt_unit_clk         ),
  .rtt_unit_enable      (rtt_prod_sel         ), // name chg
  .aux_rtt_active       (aux_rtt_active       ),
  .rtt_unit_clk         (rtt_unit_clk         ),
  .dmp_unit_enable      (dmp_unit_enable      ),
  .dmp_dmu_unit_enable  (dmp_dmu_unit_enable  ),
  .dmp_lq_unit_enable   (dmp_lq_unit_enable   ),
  .dmp_unit_clk         (dmp_unit_clk         ),
  .dmp_dmu_unit_clk     (dmp_dmu_unit_clk     ),
  .dmp_lq_unit_clk      (dmp_lq_unit_clk      ),
  .ap_unit_enable       (ap_unit_enable       ),
  .ap_unit_clk          (ap_unit_clk          ),
  .aux_aps_active       (aux_aps_active           ),
  .ap_aux_clk           (ap_aux_clk           ),
  .pct_unit_enable      (pct_unit_enable      ),
  .pct_unit_clk         (pct_unit_clk         ),
  .timer_unit_enable    (timer_unit_enable    ),
  .wdt_unit_en_r        (wdt_unit_en_r        ),
  .wake_from_wait       (wake_from_wait       ),
  .clk                   (clk                 ),
  .clk_wdt_gated (clk_wdt_gated),

  .rst_a                 (rst                 )
);

//////////////////////////////////////////////////////////////////////////////
// Module instantiation - reset_ctrl                                        //
//
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_reset_ctrl u_alb_reset_ctrl(
  .clk                (clk            ),
  .rst_a              (rst_a          ),
  .test_mode          (test_mode      ),

  .rst                (rst            )
);

//////////////////////////////////////////////////////////////////////////////
// Module instantiation - apb_rst_ctrl                                        //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_apb_rst_ctrl u_apb_reset_ctrl(
  .clk                (clk            ),
  .rst_a              (rst            ),
  .rst_in             (presetdbgn     ),
  .test_mode          (test_mode      ),
  .rst_out            (apb_rst        )
);



//////////////////////////////////////////////////////////////////////////////
// Module instantiation - asynchronous input synchronization                //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_resync_in u_alb_resync_in (
  .clk                (clk                  ),
  .rst_a              (rst                  ),

  .arc_halt_req_a     (arc_halt_req_a       ),
  .arc_run_req_a      (arc_run_req_a        ),
  .presetdbgn         (presetdbgn           ),
  .irq_sync_req_a     (irq_sync_req_a       ),
  .arc_event_a        (arc_event_a          ),
  .dbg_cache_rst_disable (dbg_cache_rst_disable), 
  .dccm_dmi_priority     (dccm_dmi_priority),     

  .cpu_resync_clk_enable (cpu_resync_clk_enable), // level 1 clk req

  .irq_sync_req       (irq_sync_req         ),
  .arc_halt_req       (arc_halt_req         ),
  .arc_run_req        (arc_run_req          ),
  .dbg_cache_rst_disable_r (dbg_cache_rst_disable_r), 
  .dccm_dmi_priority_r     (dccm_dmi_priority_r),     
  .arc_event_r        (arc_event_r          )
);


///////////////////////////////////////////////////////////////////////////////////
// exu  alb_irq_resync_in: Interrupt asynchronous input resynchronisation logic. //
///////////////////////////////////////////////////////////////////////////////////
npuarc_alb_irq_resync_in u_alb_irq_resync_in(
  .irq17_a (irq17_a),
  .irq19_a (irq19_a),
  .irq21_a (irq21_a),
  .irq22_a (irq22_a),
  .irq23_a (irq23_a),
  .irq24_a (irq24_a),
  .irq25_a (irq25_a),
  .irq26_a (irq26_a),
  .irq27_a (irq27_a),
  .irq28_a (irq28_a),
  .irq29_a (irq29_a),
  .irq30_a (irq30_a),
  .irq31_a (irq31_a),
  .irq32_a (irq32_a),
  .irq33_a (irq33_a),
  .irq34_a (irq34_a),
  .irq35_a (irq35_a),
  .irq36_a (irq36_a),
  .irq37_a (irq37_a),
  .irq38_a (irq38_a),
  .irq39_a (irq39_a),
  .irq40_a (irq40_a),
  .irq41_a (irq41_a),
  .irq42_a (irq42_a),
  .irq43_a (irq43_a),
  .irq44_a (irq44_a),
  .irq45_a (irq45_a),
  .irq46_a (irq46_a),
  .irq47_a (irq47_a),
  .irq48_a (irq48_a),
  .irq49_a (irq49_a),
  .irq50_a (irq50_a),
  .irq51_a (irq51_a),
  .irq52_a (irq52_a),
  .irq53_a (irq53_a),
  .irq54_a (irq54_a),

  .irq_r                 (irq_r              ),

  .irq_clk_en_r          (irq_clk_en_r       ),

  .clk                   (clk_resync         ),
// spyglass disable_block Ac_conv02
// SMD: irq cdc syncs converging on combinational gate
// SJ:  cdc syncs are independing, chances of glitch is low
  .irq_sync_req_a        (irq_sync_req_a     ),
// spyglass enable_block Ac_conv02
  .rst_a                 (rst                )
  );

////////////////////////////////////////////////////////////////////////////
// Module instantiation - Timers                                          //
////////////////////////////////////////////////////////////////////////////

npuarc_alb_timers u_alb_timers (
  .clk                (clk_timer          ),
  .rst_a              (rst                ),
  .timer_unit_enable  (timer_unit_enable  ),
  .db_active          (db_active          ),
  .sys_halt_r         (core_sys_halt_r    ),

  .wa_sr_data_r       (wa_sr_data_r       ),

  .aux_timer_active       (aux_timer_active       ),    

  .aux_tm0_ren_r      (aux_tm0_ren_r      ),
  .aux_tm0_raddr_r    (aux_tm0_raddr_r    ),
  .aux_tm0_wen_r      (aux_tm0_wen_r      ),
  .aux_tm0_waddr_r    (aux_tm0_waddr_r    ),

  .tm0_aux_rdata      (tm0_aux_rdata      ),
  .tm0_aux_illegal    (tm0_aux_illegal    ),
  .tm0_aux_k_rd       (tm0_aux_k_rd       ),
  .tm0_aux_k_wr       (tm0_aux_k_wr       ),
  .tm0_aux_unimpl     (tm0_aux_unimpl     ),
  .tm0_aux_serial_sr  (tm0_aux_serial_sr  ),

  .timer0_irq_1h      (timer0_irq_1h      ),
  .irq_clk_en_r       (irq_clk_en_r       ),

  .watchdog_reset     (watchdog_reset     )
);

////////////////////////////////////////////////////////////////////////////
// Module instantiation - watchdog timer                                  //
////////////////////////////////////////////////////////////////////////////
npuarc_alb_watchdog u_alb_watchdog (
  .clk                (clk_wdt_gated      ),
  .clk2               (clk_watchdog       ),
  .rst2_a                (rst2_a              ),
   .irq_clk_en_r      (irq_clk_en_r       ), 
  .rst_a              (rst                ),
  
  .db_active          (db_active          ),     
  
  .sys_halt_r       (core_sys_halt_r    ),

  .wa_sr_data_r       (wa_sr_data_r       ),

  .aux_read           (aux_read           ),
  .aux_write          (aux_write          ),

  .aux_wdt_ren_r      (aux_wdt_ren_r      ),
  .aux_wdt_raddr_r    (aux_wdt_raddr_r    ),
  .aux_wdt_wen_r      (aux_wdt_wen_r      ),
  .aux_wdt_waddr_r    (aux_wdt_waddr_r    ),

  .wdt_aux_rdata      (wdt_aux_rdata      ),
  .wdt_aux_illegal    (wdt_aux_illegal    ),
  .wdt_aux_k_rd       (wdt_aux_k_rd       ),
  .wdt_aux_k_wr       (wdt_aux_k_wr       ),
  .wdt_aux_unimpl     (wdt_aux_unimpl     ),
  .wdt_aux_serial_sr  (wdt_aux_serial_sr  ),
  .wdt_aux_strict_sr  (wdt_aux_strict_sr  ),
  .x3_kill            (x3_kill            ),
  .wdt_x3_stall       (wdt_x3_stall       ),
  .wdt_int_timeout_1h_r   (wdt_int_timeout_1h_r),
  .wdt_unit_en_r          (wdt_unit_en_r       ),
////////// Watchdog output signals /////////////////////////////////


  .wdt_ext_timeout_ack_r  (wdt_ext_timeout_ack_r),
  .wdt_ext_timeout_r      (wdt_ext_timeout_r),
  .wdt_reset2           (wdt_reset2           ),
  .wdt_reset              (wdt_reset)
);

//////////////////////////////////////////////////////////////////////////////
// Module instantiation - alb_wdt_rst_ctrl                                        //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_wdt_reset_ctrl u_wdt_reset_ctrl(
  .clk                (clk_watchdog   ),
  .rst_a              (rst            ),
  .test_mode          (test_mode      ),
  .rst                (rst2_a         )
);

////////////////////////////////////////////////////////////////////////////
// Module instantiation - Real Time Counter                               //
////////////////////////////////////////////////////////////////////////////
npuarc_alb_rtc u_alb_rtc (
  .clk                (clk_rtc            ),
  .rst_a              (rst                ),
  .wa_sr_data_r       (wa_sr_data_r       ),

  .aux_read           (aux_read           ),
  .aux_write          (aux_write          ),

  .aux_rtc_ren_r      (aux_rtc_ren_r      ),
  .aux_rtc_raddr_r    (aux_rtc_raddr_r    ),
  .aux_rtc_wen_r      (aux_rtc_wen_r      ),
  .aux_rtc_waddr_r    (aux_rtc_waddr_r    ),

  .rtc_aux_rdata      (rtc_aux_rdata      ),
  .rtc_aux_illegal    (rtc_aux_illegal    ),
  .rtc_aux_k_rd       (rtc_aux_k_rd       ),
  .rtc_aux_k_wr       (rtc_aux_k_wr       ),
  .rtc_aux_unimpl     (rtc_aux_unimpl     ),
  .rtc_aux_serial_sr  (rtc_aux_serial_sr  ),
  .rtc_aux_strict_sr  (rtc_aux_strict_sr  ),

  .rtc_na             (rtc_na             )
);


npuarc_alb_cpu_glue  u_glue_logic (
// Glue logic has registers 0
  .arc_halt_req      (arc_halt_req),
  .arc_run_req       (arc_run_req),
  .gb_sys_halt_req_r (gb_sys_halt_req_r),
  .gb_sys_run_req_r  (gb_sys_run_req_r)
);

assign  dbg_cmdack = core_dbg_cmdack;   
assign  dbg_rspval = core_dbg_rspval;    
assign  dbg_rdata  = core_dbg_rdata;    
assign  dbg_reop   = core_dbg_reop;     
assign  dbg_rerr   = core_dbg_rerr;      

assign  arc_run_ack  = core_sys_run_ack_r;
assign  arc_halt_ack = core_sys_halt_ack_r;



endmodule // alb_aon
