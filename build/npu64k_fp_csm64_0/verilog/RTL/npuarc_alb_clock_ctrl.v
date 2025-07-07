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
//   ####   #       ####    ####   #    #         ####    #####  #####   #
//  #    #  #      #    #  #    #  #   #         #    #     #    #    #  #
//  #       #      #    #  #       ####          #          #    #    #  #
//  #       #      #    #  #       #  #          #          #    #####   #
//  #    #  #      #    #  #    #  #   #         #    #     #    #   #   #
//   ####   #####   ####    ####   #    # #####   ####      #    #    #  #####
//
// ===========================================================================
//
// @f:clock_ctrl
//
// Description:
// @p
//  The |clock_ctrl| module instantiates the architectural clock gates, which 
//  gates off clocks as necessary, when in sleep/halt mode
// @e
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o alb_clock_ctrl.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_clock_ctrl (

  output                        ar_save_clk,
  input                         ar_save_en_r,
  ////////// State of the core ///////////////////////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  core state interface
  input                       clk_ungated,
  input                       cpu_resync_clk_enable, // ext async evts clk en
  output                      cpu_clk_enable,     // req to level 1 clk gate
  input                       cpu_l1_cg_dis,      // GLOBAL_L1_CLK_DIS aux bit
  input                       cpu_l1_accept_en,   // L1 clock ative

  output reg                  l1_clock_active,
  input                       sys_sleep_r,        // sleeping (arch_sleep_r)
  input [`npuarc_EXT_SMODE_RANGE]    sys_sleep_mode_r,   // sleep mode
  input                       sys_halt_r,         // halted
  input                       arc_halt_req,       // synchr halt req

  input                       arc_halt_ack,       // synchr halt ack
// leda NTL_CON13C on
  input                       arc_run_req,        // synchr run req
  input                       arc_run_ack,        // synchr run ack




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

  ////////// DMP status ////////////////////////////////////////////////////
  //
  input                       dmp_idle_r,

  ////////// IFU status ////////////////////////////////////////////////////
  //
  input                       ifu_idle_r,

  ////////// arch clk enable signal //////////////////////////////////////////   
  //
  output reg                  ar_clock_enable_r,

  input                       hor_clock_enable_nxt, // HOR=halt_on_reset
  ////////// DMI enable signal from external BIU ///////////////////////////////////////////////  
  //
  input                       biu_dmi_clk_en_req,
  ////////// Debug enable signal /////////////////////////////////////////////
  //
  input                       db_clock_enable_nxt,

  ////////// IRQ resync enable signal ////////////////////////////////////////
  //
  input                       irq_sync_req,
  ////////// IRQ preemption signal (to wake up a sleeping core ///////////////
  //
  input                       irq_preempts_nxt,

  ///////// interrupt sample clock control //////////////////////////////
  //
  output reg                  irq_clk_en_r, 


  ///////// Outputs of the architectural clock gates /////////////////////////
  //
  output                      clk_timer,
  output                      clk_rtc,
  input                       wdt_clk,
// spyglass disable_block W240
// SMD: An input has been declared but is not read
// SJ:  not used in some config
  input                       rst2_a,
// spyglass enable_block W240
  output                      clk_watchdog,
  output                      clk_resync,
  output                      clk_gated,


  ////////// Unit-level clock gating control outputs to clock_ctrl ///////////
  //
  input                       mpy_unit_enable,      // clk ctrl for multiplier
  output                      mpy_unit_clk,         // clk      for multiplier
  input                       div_unit_enable,      // clk ctrl for divider
  output                      div_unit_clk,         // clk      for divider
  input                       smt_unit_enable,      // clk ctrl for SMT
  output                      smt_unit_clk,         // clk      for SMT
  input                       rtt_unit_enable,      // clk ctrl for RTT
  input                       aux_rtt_active,       // enable RTT interf clk (for aux op)
  output                      rtt_unit_clk,         // clk      for RTT
  input                       dmp_unit_enable,      // clk ctrl for DMP
  input                       dmp_dmu_unit_enable,  // clk ctrl for DMP
  input                       dmp_lq_unit_enable,  // clk ctrl for DMP
  output                      dmp_unit_clk,         // clk      for DMP
  output                      dmp_dmu_unit_clk,     // clk      for DMP dmu
  output                      dmp_lq_unit_clk,     // clk      for DMP lq
  input                       ap_unit_enable,
  output                      ap_unit_clk,
  input                       aux_aps_active,       //
  output                      ap_aux_clk,           // clk for AP Aux
  input                       pct_unit_enable,
  output                      pct_unit_clk,
  input                       timer_unit_enable,

  input                       wdt_unit_en_r,
  input                       wake_from_wait,       // wakeup from WEVT, WLFC

  ////////// General input signals ///////////////////////////////////////////
  //

  output                      clk_wdt_gated, // processor clock gated for watchdog
  input                       clk,               // Processor clock
  input                       rst_a              // Asynchronous reset
);

// Local Declarations

reg                     cpu_l1_cg_dis_r;
reg                     db_clock_enable_r;
reg                     ar_clock_enable_nxt;

reg                     ar_clock_enable_timer_r;      
reg                     ar_clock_enable_timer_nxt;      

reg                     ar_clock_enable_watchdog_nxt;      
reg                     clock_enable_watchdog_r;
reg                     ar_clock_enable_watchdog_r;  
reg                     ar_clock_enable_watchdog_r_r;      
reg                     ar_clock_enable_rtc_r;
reg                     ar_clock_enable_rtc_nxt;

reg                     ar_clock_enable_resync_r;
reg                     ar_clock_enable_resync_nxt;



reg                     mpy_unit_enable_r;
reg                     div_unit_enable_r;
reg                     rtt_unit_enable_r;
reg                     smt_unit_enable_r;
reg                     dmp_dmu_unit_enable_r;
reg                     dmp_dmu_unit_enable_nxt;
reg                     dmp_lq_unit_enable_r;
reg                     dmp_lq_unit_enable_nxt;
reg                     dmp_unit_enable_nxt;
reg                     dmp_unit_enable_r;
reg                     pct_unit_enable_r;

reg irq_preempts_r;



wire        cpu_clk_enable_ext_a;
reg         cpu_clk_enable_ext_r0;
wire         cpu_clk_enable_ext_r1;
reg         cpu_clk_enable_ext_r2;
reg         cpu_clk_enable_ext_r3;

wire        cpu_clk_enable_int_a;
reg         cpu_clk_enable_int_r0;
wire         cpu_clk_enable_int_r1;

wire        cpu_clk_enable_r1;
 

// Core External Units : Core Clock Enable
assign cpu_clk_enable_ext_a =  1'b0
                            | cpu_resync_clk_enable // ext async evts (halt, irq, etc.)
                            ;
                         

// spyglass disable_block Ac_unsync01 Ac_glitch04
// SMD: Ac_unsync01 unsynchronized clock domain crossing for scalar signals
// SJ: Issues caused by unsynchronized inputs are resolved down the pipe

// spyglass disable_block Ar_resetcross01
// SMD: Unsynchronized reset crossing detected 
// SJ: Issues caused by unsynchronized inputs are resolved down the pipe (Same as Ac_unsync01 above)

always @(posedge clk or posedge rst_a)
begin : cpu_clk_enable_ext_r0_PROC
  if (rst_a == 1'b1) begin
    cpu_clk_enable_ext_r0 <= 1'b1;
  end 
  else begin
// spyglass disable_block Reset_check04
// SMD: asynchronous reset used sychronously
// SJ:  rst_a must be used to asynchronously to request L1 clock and also a synchronized version 
//      (component of cpu_clk_enable_r1) must be used for the L1 idle/busy FSM
    cpu_clk_enable_ext_r0 <= cpu_clk_enable_ext_a;
// spyglass enable_block Reset_check04
  end
end

// spyglass enable_block Ar_resetcross01
// spyglass enable_block Ac_unsync01 Ac_glitch04
wire cpu_clk_enable_ext_r1n;
// spyglass disable_block Reset_check04
// SMD: Reset signals that are used asynchronously as well as synchronously for different flip-flops
// SJ:  presetdbgn, atresetn are used as data & not as synchronous resets
npuarc_cdc_sync u_cdc_sync_ext (
  .clk        (clk),
  .rst_a      (rst_a),
  .din        (~cpu_clk_enable_ext_a),
  .dout       (cpu_clk_enable_ext_r1n)
);
// spyglass enable_block Reset_check04
assign cpu_clk_enable_ext_r1 = ~cpu_clk_enable_ext_r1n;

always @(posedge clk or posedge rst_a)
begin : cpu_clk_enable_ext_r_PROC
  if (rst_a == 1'b1) begin
    cpu_clk_enable_ext_r2 <= 1'b1;
    cpu_clk_enable_ext_r3 <= 1'b1;
  end 
  else begin
    cpu_clk_enable_ext_r2 <= cpu_clk_enable_ext_r1;
    // Exclude pulse glitches
    cpu_clk_enable_ext_r3 <= cpu_clk_enable_ext_r2 & cpu_clk_enable_ext_r1;
  end
end

// spyglass disable_block Ac_conv01
// SMD: cdc sync signals converging on combinational gate
// SJ:  cdc syncs are independent and chance of glitch is very low
// Core Internal Units : Core Clock Enable
assign cpu_clk_enable_int_a = (cpu_l1_cg_dis_r == 1'b1)
                            | ar_clock_enable_r     // running
                            | ar_clock_enable_nxt   // wake up ...
                            | dmp_unit_enable_nxt
                            | timer_unit_enable
                            | wdt_unit_en_r
                            ;
// spyglass enable_block Ac_conv01
                         
always @(posedge clk or posedge rst_a)
begin : cpu_clk_enable_int_r_PROC
  if (rst_a == 1'b1) begin
    cpu_clk_enable_int_r0 <= 1'b1;
  end 
  else begin
    cpu_clk_enable_int_r0 <= cpu_clk_enable_int_a;
  end
end
wire cpu_clk_enable_int_r1n;
npuarc_cdc_sync u_cdc_sync_int (
  .clk        (clk),
  .rst_a      (rst_a),
  .din        (~cpu_clk_enable_int_a),
  .dout       (cpu_clk_enable_int_r1n)
);
assign cpu_clk_enable_int_r1 = ~cpu_clk_enable_int_r1n;

// spyglass disable_block Ac_conv01 Ac_conv02 Ac_conv03
// SMD: cdc sync signals converging on combinational gate
// SJ:  cdc syncs are independent and chance of glitch is very low
assign cpu_clk_enable = 1'b0
                      | cpu_clk_enable_ext_a | cpu_clk_enable_ext_r0 | cpu_clk_enable_ext_r1
                      | cpu_clk_enable_int_a | cpu_clk_enable_int_r0 | cpu_clk_enable_int_r1
                      ;
// spyglass enable_block Ac_conv01 Ac_conv02 Ac_conv03

assign cpu_clk_enable_r1 = cpu_clk_enable_ext_r3 | cpu_clk_enable_int_r1;


// Module Definition
// Instantiate a clock gate wrapper so that the synthesis flow can replace it 
// with the proper clkgate cell of the target library
//

npuarc_clkgate u_clkgate0 (
  .clk_in            (clk),
  .clock_enable      (ar_clock_enable_r),
  .clk_out           (clk_gated)
);


// SRAM memory modules enables and select logic to gate with ls
////// WB_PER0 //////////////////////////////

////// WB_PER1 //////////////////////////////

////// WB_MEM //////////////////////////////

////// ICACHE //////////////////////////////
reg ic_data_cen0_r;
reg ic_data_cen1_r;
reg ic_tag_cen0_r;
reg ic_tag_cen1_r;
reg ic_tag_cen2_r;
reg ic_tag_cen3_r;

////// ICCM0 ///////////////////////////////

////// ICCM1 ///////////////////////////////

////// DCACHE //////////////////////////////
    reg dc_tag_even_cs_w0_r;
    reg dc_tag_odd_cs_w0_r;
    reg dc_tag_even_cs_w1_r;
    reg dc_tag_odd_cs_w1_r;
  reg dc_data_even_cs_lo_r;
  reg dc_data_even_cs_hi_r;
  reg dc_data_odd_cs_lo_r;
  reg dc_data_odd_cs_hi_r;

////// DCCM ////////////////////////////////
      reg dccm_bank0_cs_lo_r;
      reg dccm_bank0_cs_hi_r;
      reg dccm_bank1_cs_lo_r;
      reg dccm_bank1_cs_hi_r;

////// SMART ///////////////////////////////

////// MMU /////////////////////////////////
  reg ntlb_pd0_ce_r;
  reg ntlb_pd1_ce_r;

////// BC GS ///////////////////////////////
  reg bc_me0_r;
  reg gs_me0_r;
  reg bc_me1_r;
  reg gs_me1_r;

////// assignment of SRAM registered enables and selects 
always @(posedge clk or posedge rst_a)
begin: sram_ce_cs_r_PROC // {
  if (rst_a)
  begin // {



    ic_data_cen0_r <= 0;
    ic_data_cen1_r <= 0;
    ic_tag_cen0_r <= 0;
    ic_tag_cen1_r <= 0;
    ic_tag_cen2_r <= 0;
    ic_tag_cen3_r <= 0;



    dc_tag_even_cs_w0_r  <= 0;
    dc_tag_odd_cs_w0_r  <= 0;
    dc_tag_even_cs_w1_r  <= 0;
    dc_tag_odd_cs_w1_r  <= 0;
    dc_data_even_cs_lo_r  <= 0;
    dc_data_even_cs_hi_r  <= 0;
    dc_data_odd_cs_lo_r  <= 0;
    dc_data_odd_cs_hi_r  <= 0;

    dccm_bank0_cs_lo_r  <= 0;
    dccm_bank0_cs_hi_r <= 0;
    dccm_bank1_cs_lo_r  <= 0;
    dccm_bank1_cs_hi_r <= 0;


    ntlb_pd0_ce_r  <= 0;
    ntlb_pd1_ce_r  <= 0;

    bc_me0_r  <= 0;
    gs_me0_r  <= 0;
    bc_me1_r  <= 0;
    gs_me1_r  <= 0;
  end  // }
  else begin // { 



    ic_data_cen0_r <= ic_data_cen0;
    ic_data_cen1_r <= ic_data_cen1;
    ic_tag_cen0_r <= ic_tag_cen0;
    ic_tag_cen1_r <= ic_tag_cen1;
    ic_tag_cen2_r <= ic_tag_cen2;
    ic_tag_cen3_r <= ic_tag_cen3;



    dc_tag_even_cs_w0_r  <= dc_tag_even_cs_w0;
    dc_tag_odd_cs_w0_r  <= dc_tag_odd_cs_w0;
    dc_tag_even_cs_w1_r  <= dc_tag_even_cs_w1;
    dc_tag_odd_cs_w1_r  <= dc_tag_odd_cs_w1;
    dc_data_even_cs_lo_r  <= dc_data_even_cs_lo;
    dc_data_even_cs_hi_r  <= dc_data_even_cs_hi;
    dc_data_odd_cs_lo_r  <= dc_data_odd_cs_lo;
    dc_data_odd_cs_hi_r  <= dc_data_odd_cs_hi;

    dccm_bank0_cs_lo_r  <= dccm_bank0_cs_lo;
    dccm_bank0_cs_hi_r <= dccm_bank0_cs_hi;
    dccm_bank1_cs_lo_r  <= dccm_bank1_cs_lo;
    dccm_bank1_cs_hi_r <= dccm_bank1_cs_hi;


    ntlb_pd0_ce_r  <= ntlb_pd0_ce;
    ntlb_pd1_ce_r  <= ntlb_pd1_ce;

    bc_me0_r  <= bc_me0;
    gs_me0_r  <= gs_me0;
    bc_me1_r  <= bc_me1;
    gs_me1_r  <= gs_me1;
  end // }
end // }

// Memory setup-falling constraint on "ls" i.e. de-assertion of low leakage state, is more critical that setup-rising
// Hence use registered edge of the clock enable for assertion and the unregistered edge for de-assertion. 
// Allow 2-cycle setup for falling edge of "ls". 


npuarc_clkgate u_clkgate1 (
  .clk_in            (clk),
  .clock_enable      (ar_clock_enable_timer_r),
  .clk_out           (clk_timer)
);

npuarc_clkgate u_clkgate2 (
  .clk_in            (clk),
  .clock_enable      (ar_clock_enable_rtc_r),
  .clk_out           (clk_rtc)
);

npuarc_clkgate u_clkgate5 (
  .clk_in            (clk),
  .clock_enable      (clock_enable_watchdog_r),
  .clk_out           (clk_wdt_gated)
);
 
npuarc_clkgate u_clkgate4 (
  .clk_in            (wdt_clk),
  .clock_enable      (ar_clock_enable_watchdog_r_r),
  .clk_out           (clk_watchdog)
);

npuarc_clkgate u_clkgate3 (
  .clk_in            (clk),
  .clock_enable      (ar_clock_enable_resync_r),
  .clk_out           (clk_resync)
);


//
npuarc_clkgate u_clkgate_ar_save (
  .clk_in            (clk                  ),
  .clock_enable      (ar_save_en_r         ),
  .clk_out           (ar_save_clk          )
);




  ////////// Unit-level clock gating control outputs to clock_ctrl ///////////
  //
//
npuarc_clkgate u_clkgate_mpy (
  .clk_in            (clk),
  .clock_enable      (mpy_unit_enable_r),
  .clk_out           (mpy_unit_clk)
);
//
npuarc_clkgate u_clkgate_div (
  .clk_in            (clk),
  .clock_enable      (div_unit_enable_r),
  .clk_out           (div_unit_clk)
);
//
npuarc_clkgate u_clkgate_rtt (
  .clk_in            (clk),
  .clock_enable      (rtt_unit_enable_r),
  .clk_out           (rtt_unit_clk)
);
//
npuarc_clkgate u_clkgate_smt (
  .clk_in            (clk),
  .clock_enable      (smt_unit_enable_r),
  .clk_out           (smt_unit_clk)
);
//

npuarc_clkgate u_clkgate_dmp (
  .clk_in            (clk),
  .clock_enable      (dmp_unit_enable_r),
  .clk_out           (dmp_unit_clk)
);
npuarc_clkgate u_clkgate_dmp_dmu (
  .clk_in            (clk),
  .clock_enable      (dmp_dmu_unit_enable_r),
  .clk_out           (dmp_dmu_unit_clk)
);
npuarc_clkgate u_clkgate_dmp_lq (
  .clk_in            (clk),
  .clock_enable      (dmp_lq_unit_enable_r),
  .clk_out           (dmp_lq_unit_clk)
);

npuarc_clkgate u_clkgate_aps (
  .clk_in            (clk),
  .clock_enable      (ap_unit_enable),
  .clk_out           (ap_unit_clk)
);
npuarc_clkgate u_clkgate_apaux (
  .clk_in            (clk),
  .clock_enable      (aux_aps_active),
  .clk_out           (ap_aux_clk)
);



npuarc_clkgate u_clkgate_pct (
  .clk_in            (clk),
  .clock_enable      (pct_unit_enable_r),
  .clk_out           (pct_unit_clk)
);



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process to determine next value for the architectural       //
// clock gate enable                                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : ar_clock_en_PROC
  if (sys_sleep_r | sys_halt_r)   
  begin
    // The core is in a low power state (sleeping or halted). By default the
    // core clock will be disabled. However, the clock needs to be enabled 
    // for the following events:
    //
    // 1. A fully-qualified and enabled interrupt request is asserted, 
    //    guaranteeing that at least one asserted interrupt should be taken 
    //    by the core. This event will bring the core out of a sleeping state.
    //
    // 2. A snoop intervention transaction is to take place, requiring temporary
    //  enablement of the core clock.
    //
    // 3. A DMI transaction is to take place, requiring temporary enablement
    //    of the core clock.
    //
    // 4. A debug transaction is to take place, requiring temporary enablement
    //    of the core clock.
    //
    // 5. there is a posted DMP write, which remains active until the write
    //    data reaches its destination.
    //
    // 6/7. servicing a halt/run req/ack in sleep mode
    // 
    // 8. The core wakes up from sleep due to a WEVT or WLFC instruction
    //
    // 9. The uDMA DMI transaction is to take place, requiring temporary enablement
    //    of the core clock.
    //
    // 10. The uDMA access APEX aux regs transaction is to take place, requiring temporary enablement
    //    of the core clock.
    //
    // 11. when the write buffer PER0 is busy, need to the clock to be enabled
    //
    // 12. when the write buffer PER1 is busy, need to the clock to be enabled
    //
    // 13. when the write buffer MEM  is busy, need to the clock to be enabled
    //
    ar_clock_enable_nxt   = (1'b0
                          | hor_clock_enable_nxt
                          | irq_preempts_r                                // (1)
                          | biu_dmi_clk_en_req                          // (3) 


                          | (   db_clock_enable_nxt                     // (4)
                              | db_clock_enable_r
                            )
                          | (~dmp_idle_r)                               // (5)
                          | (~ifu_idle_r)
                          | arc_halt_req  | arc_halt_ack                // (6)
                          | arc_run_req   | arc_run_ack                 // (7)
                          | wake_from_wait                              // (8)               

                          ) 
                          ;
  end
  else
  begin
    // The core is running, and the clock must remain enabled.
    //
    // spyglass disable_block Ac_conv01 Ac_conv02 Ac_conv03
    // SMD: Combinational Convergence of same domain synchronized signals
    // SJ:  sys_sleep_r & sys_halt_r belong to cpu clock domain
    // SMD: multiple synchronizers converge on combinational gate
    // SJ:  jtag wakeup signal 1st sync'd to core clk
    //      
    ar_clock_enable_nxt   = 1'b1
                          ;
  end
    
  // Enable the IRQ resynchronizer clock when any of the following
  // conditions is true:
  //
  // 1. The core clock will be running in the next cycle
  //
  // 2. The irq_resync_in module detects a changing interrupt that
  //    requires to be synchronized.
  //
  ar_clock_enable_resync_nxt  = ar_clock_enable_nxt                     // (1)
                              | irq_sync_req                            // (2)
                              ;
  
    // spyglass enable_block Ac_conv01 Ac_conv02 Ac_conv03
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Level-1 idle FSM    
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg [1:0]  l1_state_r;
reg [1:0]  l1_state_nxt;
wire [1:0]  l1_state_next;

localparam CPU_ACTIVE      = 2'b00;
localparam CPU_GOING_IDLE  = 2'b01;
localparam CPU_IDLE        = 2'b10;

always @*
begin : cpu_l1_fsm_PROC
  
  l1_clock_active = 1'b0;
// spyglass disable_block Ac_conv01
// SMD: cdc sync signals converging on mux
// SJ:  cdc syncs are independent and chance of glitch is very low
  l1_state_nxt    = l1_state_r;
// spyglass enable_block Ac_conv01
  case (l1_state_r)
  CPU_ACTIVE:
  begin
    l1_clock_active = cpu_clk_enable_r1;
    
    if (cpu_clk_enable_r1 == 1'b0)
    begin
      // This takes into account the AUX chicken-bit
      //
      l1_state_nxt = CPU_GOING_IDLE;
    end
  end
  
  CPU_GOING_IDLE:
  begin
    if (  (cpu_l1_accept_en == 1'b0)
        | (cpu_clk_enable_r1 == 1'b1))
    begin
      // We are going idle...
      //
      l1_state_nxt = CPU_IDLE;
    end
  end

  default: // CPU_IDLE
  begin
    if (cpu_l1_accept_en == 1'b1)
    begin
      // Let's go active again.
      //
      l1_state_nxt = CPU_ACTIVE;
    end
  end
  endcase
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process to determine next value for the architectural       //
// clock gate enable for the timers                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
reg timer_off;
always @*
begin : timer_clk_en_PROC
  // The timers architectural clock enabled is only active when the cpu
  // is in SLEEP_MODE_0 or SLEP_MODE_2. It is disabled otherwise.
  //
  timer_off                 = (  (   sys_sleep_r
                                   & (   (sys_sleep_mode_r != `npuarc_SLEEP_MODE_0)
                                       & (sys_sleep_mode_r != `npuarc_SLEEP_MODE_2))
                                 )
                               | (~timer_unit_enable)
                              )
                              ;  
  
  ar_clock_enable_timer_nxt = (~timer_off);
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process to determine next value for the architectural       //
// clock gate enable for the watchdog                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : watchdog_clk_en_PROC
  // The watchdog architectural clock enabled is only active when the cpu
  // is in SLEEP_MODE_0 or SLEP_MODE_2. It is disabled otherwise.
  //
  ar_clock_enable_watchdog_nxt = ~(   sys_sleep_r
                                & (  (sys_sleep_mode_r != `npuarc_SLEEP_MODE_0)
                                   & (sys_sleep_mode_r != `npuarc_SLEEP_MODE_2))

                                );
end
  
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process to determine next value for the architectural       //
// clock gate enable for the RTC.                                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : rtc_clk_en_PROC
  // The timers architectural clock enabled is only active when the cpu
  // is in SLEEP_MODE_0 or SLEP_MODE_1. It is disabled otherwise.
  //
  ar_clock_enable_rtc_nxt =  ~(   sys_sleep_r
                               & (  (sys_sleep_mode_r != `npuarc_SLEEP_MODE_0)
                                  & (sys_sleep_mode_r != `npuarc_SLEEP_MODE_1))
                               );
end
  

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asynchronous process to determine next value for the dmp unit clock      
//                                                                          
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dmp_unit_enable_nxt_PROC
  dmp_unit_enable_nxt =  dmp_unit_enable
                       | biu_dmi_clk_en_req
                       ;
  dmp_dmu_unit_enable_nxt = dmp_dmu_unit_enable
                          | biu_dmi_clk_en_req

                          ;

  dmp_lq_unit_enable_nxt = dmp_lq_unit_enable
                          ;
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous processes to register the incoming debug enable              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// When the debug unit turns on the clock, it needs to remain one for
// at least two cycles. This is needed so that the clock is enabled while
// there are debug instructions moving through the pipeline
//

always @(posedge clk or posedge rst_a)
begin : db_clk_en_PROC
  if (rst_a == 1'b1) begin
    db_clock_enable_r  <= 1'b1;
  end
  else begin
    db_clock_enable_r  <= db_clock_enable_nxt; 
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define the registered architectural clock enable  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : ar_clk_en_reg_PROC
  if (rst_a == 1'b1) begin
    ar_clock_enable_r  <= 1'b1;
  end
  else begin
    ar_clock_enable_r  <= ar_clock_enable_nxt; 
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define the registered architectural clock enable  //
// for the timers                                                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : timer_clk_en_reg_PROC
  if (rst_a == 1'b1) begin
    ar_clock_enable_timer_r  <= 1'b1;
  end
  else begin
    ar_clock_enable_timer_r  <= ar_clock_enable_timer_nxt; 
  end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define the registered architectural clock enable  //
// for the watchdog                                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : wdt_clk_en_reg_PROC
  if (rst_a == 1'b1) begin
    clock_enable_watchdog_r  <= 1'b1;
  end
  else begin
    clock_enable_watchdog_r  <= ar_clock_enable_watchdog_nxt; 
  end
end

always @(posedge wdt_clk or posedge rst2_a)
begin : wdt_clk_en_reg2_PROC
  if (rst2_a == 1'b1) begin
    ar_clock_enable_watchdog_r   <= 1'b1;
    ar_clock_enable_watchdog_r_r  <= 1'b1;
  end
  else begin
    ar_clock_enable_watchdog_r  <= clock_enable_watchdog_r; 
    ar_clock_enable_watchdog_r_r <= ar_clock_enable_watchdog_r;
  end 
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define the registered architectural clock enable  //
// for the RTC                                                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : rtc_clk_en_reg_PROC
  if (rst_a == 1'b1) begin
    ar_clock_enable_rtc_r  <= 1'b1;
  end
  else begin
    ar_clock_enable_rtc_r  <= ar_clock_enable_rtc_nxt; 
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process to define the registered architectural clock enable  //
// for the IRQ resync module                                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : irq_resync_en_reg_PROC
  if (rst_a == 1'b1) begin
    ar_clock_enable_resync_r  <= 1'b1;
  end
  else begin
    ar_clock_enable_resync_r  <= ar_clock_enable_resync_nxt; 
  end
end

always @(posedge clk or posedge rst_a)
begin : mpy_unit_clock_enable_reg_PROC
  if (rst_a == 1'b1) begin
    mpy_unit_enable_r  <= 1'b1;
  end
  else begin
    mpy_unit_enable_r  <= mpy_unit_enable; 
  end
end // block : mpy_unit_clock_enable_reg_PROC
always @(posedge clk or posedge rst_a)
begin : div_unit_clock_enable_reg_PROC
  if (rst_a == 1'b1) begin
    div_unit_enable_r  <= 1'b1;
  end
  else begin
    div_unit_enable_r  <= div_unit_enable; 
  end
end // block : div_unit_clock_enable_reg_PROC
always @(posedge clk or posedge rst_a)
begin : rtt_unit_clock_enable_reg_PROC
  if (rst_a == 1'b1) begin
    rtt_unit_enable_r  <= 1'b1;
  end
  else begin
    rtt_unit_enable_r  <= rtt_unit_enable | aux_rtt_active; 
  end
end // block : rtt_unit_clock_enable_reg_PROC
always @(posedge clk or posedge rst_a)
begin : smt_unit_clock_enable_reg_PROC
  if (rst_a == 1'b1) begin
    smt_unit_enable_r  <= 1'b1;
  end
  else begin
    smt_unit_enable_r  <= smt_unit_enable & ar_clock_enable_nxt; 
  end
end // block : rtt_unit_clock_enable_reg_PROC
 
always @(posedge clk or posedge rst_a)
begin : dmp_unit_clock_enable_reg_PROC
  if (rst_a == 1'b1) begin
    dmp_unit_enable_r  <= 1'b1;
  end
  else begin
    dmp_unit_enable_r  <= dmp_unit_enable_nxt; 
  end
end // block : dmp_unit_clock_enable_reg_PROC
always @(posedge clk or posedge rst_a)
begin : dmp_dmu_unit_clock_enable_reg_PROC
  if (rst_a == 1'b1) begin
    dmp_dmu_unit_enable_r  <= 1'b1;
  end
  else begin
    dmp_dmu_unit_enable_r  <= dmp_dmu_unit_enable_nxt; 
  end
end // block : dmp_unit_clock_enable_reg_PROC
always @(posedge clk or posedge rst_a)
begin : dmp_lq_unit_clock_enable_reg_PROC
  if (rst_a == 1'b1) begin
    dmp_lq_unit_enable_r  <= 1'b1;
  end
  else begin
    dmp_lq_unit_enable_r  <= dmp_lq_unit_enable_nxt; 
  end
end // block : dmp_unit_clock_enable_reg_PROC

always @(posedge clk or posedge rst_a)
begin : pct_unit_clock_enable_reg_PROC
  if (rst_a == 1'b1) begin
    pct_unit_enable_r  <= 1'b1;
  end
  else begin
    pct_unit_enable_r  <= pct_unit_enable & ar_clock_enable_nxt; 
  end
end 

always @(posedge clk_ungated or posedge rst_a)
begin: irq_clk_en_PROC
  if (rst_a == 1'b1) begin
    irq_clk_en_r <= 1'b0;
  end
  else begin
    irq_clk_en_r <= ~irq_clk_en_r;
  end
end


always @(posedge clk_ungated or posedge rst_a)
begin: irq_preempt_PROC
  if (rst_a == 1'b1) begin
    irq_preempts_r <= 1'b0;
  end
  else if (irq_clk_en_r) begin
      irq_preempts_r <= irq_preempts_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : l1_cg_dis_reg_PROC
  if (rst_a == 1'b1) begin
    cpu_l1_cg_dis_r  <= 1'b1;
  end
  else begin
    cpu_l1_cg_dis_r  <= cpu_l1_cg_dis;
  end
end 

assign l1_state_next = 
                        l1_state_nxt;

// spyglass disable_block Reset_check10
// SMD: Reset_check10 Asynchronous reset signal is reaching to data  
// SJ: async resets are part of L1 cpu_clk_enable, which affects l1_state
// SJ: this may cause minor loss in test cov due to excl of these state FFs
always @(posedge clk or posedge rst_a)
begin : l1_fsm_reg_PROC
  if (rst_a == 1'b1) begin
    l1_state_r <= CPU_ACTIVE;
  end
  else begin
    l1_state_r <= l1_state_next;
  end
end 
// spyglass enable_block Reset_check10
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output assignment                                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////





endmodule // alb_clock_ctrl


