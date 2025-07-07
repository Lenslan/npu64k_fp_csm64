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
//  #####   ######   #     #         #######  #######  ######
// #     #  #     #  #     #            #     #     #  #     #
// #        #     #  #     #            #     #     #  #     #
// #        ######   #     #            #     #     #  ######
// #        #        #     #            #     #     #  #
// #     #  #        #     #            #     #     #  #
//  #####   #         #####   #####     #     #######  #
//
// ===========================================================================
//
// @f:alb_cpu_top
//
// Description:
// @p
//  The |cpu_top| module instantiates the CPU and connects it to the local
//  RAM modules required by caches and CCMs.
// @e
//
// ===========================================================================

// Configuration-dependent macro definitions
//
// Set simulation timescale
//
// synopsys translate_off

///////////////////////////////////////////////////////////////////////////
// Common Verilog definitions
///////////////////////////////////////////////////////////////////////////

// Verilog simulator timescale definition for all modules
//
`timescale 1 ns / 10 ps

// synopsys translate_on

module npuarc_alb_cpu_top (

  ////////// External Event Interface /////////////////////////////////////////
  //
  input                       arc_event_a,      // Async. event signal

  ////////// External Halt Request Interface /////////////////////////////////
  //
  input                       arc_halt_req_a,    // Async Req to Halt core
  input                       arc_run_req_a,     // Async Req to unHalt core
  //
  output                      arc_halt_ack,      // Core has Halted cleanly
  output                      arc_run_ack,      // Core has unHalted
  //



  ////////// EIA user extension external input signals ///////////////////////
  //
  input   [95:0]  EventManager_evm_event_a,
  input           EventManager_evm_sleep,

  ////////// EIA user extension external output signals //////////////////////
  //
  output          EventManager_evm_wakeup,
  output  [63:0]  EventManager_evm_send,
  output  [31:0]  EventManager_vm_grp0_sid,
  output  [31:0]  EventManager_vm_grp0_ssid,
  output  [31:0]  EventManager_vm_grp1_sid,
  output  [31:0]  EventManager_vm_grp1_ssid,
  output  [31:0]  EventManager_vm_grp2_sid,
  output  [31:0]  EventManager_vm_grp3_sid,
  output  [31:0]  EventManager_vm_grp2_ssid,
  output  [31:0]  EventManager_vm_grp3_ssid,
  output          EventManager_evt_vm_irq,
  output  [3:0]  EventManager_evt_vm_sel,
// spyglass disable_block SDC_02
// SMD: Pin: "*" specified in constraint file not found in design:

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
// spyglass enable_block SDC_02


  input [21:0]                      intvbase_in, // for external interrupt vector base configuring


  input                             biu_dmi_clk_en_req,

  
  ////////// Auxiliary interface for common aux register accesses ////////////
  //
  output                      aux_rs_valid,         //  CCAUX valid rd request
  output [0:0]   aux_rs_region,        //  CCAUX region identity
  output [11:0]  aux_rs_addr,          //  CCAUX region offset
  output                      aux_rs_read,          //  CCAUX read enable
  output                      aux_rs_write,         //  CCAUX write enable
  input  [31:0]        aux_rs_data,          //  CCAUX LR data
  input  [5:0]  aux_rs_status,        //  CCAUX credintials
  input                       aux_rs_accept,        //  CCAUX response read

  output                      aux_wr_valid,         //  CCAux wr valid
  output [0:0]   aux_wr_region,        //  CCAux wr region
  output [11:0]  aux_wr_addr,          //  CCAux wr Address
  output [31:0]        aux_wr_data,          //  CCAux wr data
  input                       aux_wr_allow,         //  CCAux new write allowed
  output                      aux_cm_phase,         //  CCAux in commit phase
  output                      aux_cm_valid,         //  CCAux commit is valid


  // leda NTL_CON13C off
  // leda NTL_CON37 off
  // LMD: non driving port
  // LJ:  Not all bits of bus used
  ////////// Interface to the Debug module (BVCI target) /////////////////////
  //
  input                       dbg_cmdval,         // cmdval from JTAG
// spyglass disable_block W240
// SMD: inputs declared but not read
// SJ:  kept for debug interface
  input                       dbg_eop,            // eop from JTAG
// spyglass enable_block W240
  input   [31:0]   dbg_address,        // address from JTAG
  input   [3:0]     dbg_be,             // be from JTAG
  input   [1:0]    dbg_cmd,            // cmd from JTAG
  input   [31:0]   dbg_wdata,          // wdata from JTAG
  input                       dbg_rspack,         // rspack from JTAG

  output                      dbg_cmdack,         // BVCI cmd acknowledge
  output                      dbg_rspval,         // BVCI response valid
  output  [31:0]   dbg_rdata,          // BVCI response EOP
  output                      dbg_reop,           // BVCI response error
  output                      dbg_rerr,           // BVCI data to Debug host
  ////////// Interface to the Debug module for host control of system reset //
  //
  output                      debug_reset,        // Reset from debug host
  // leda NTL_CON13C on
  // leda NTL_CON37 on
  input                       dbg_prot_sel,

  input                       pclkdbg_en,
  output                      preadydbg,
  output [31:0]               prdatadbg,
  output                      pslverrdbg,
  input                       presetdbgn,
  input [31:2]                paddrdbg,
  input                       pseldbg,
  input                       penabledbg,
  input                       pwritedbg,
  input [31:0]                pwdatadbg,
  input                       dbgen,
  input                       niden,

//      `if ((1 == 1) && (1 == 1) && (1 == 1)) // {
//        `if ((1 == 1) && (8 > 0)) // {
  output [7:0]                cti_ap_status,
//        `endif // }
//      `endif // }
//      `if ((1 == 1) && (1 == 1) && (1 == 1)) // {
//        `if (((0 == 1) || (1 == 1)) && (8 > 0)) // {
  output                      cti_ap_hit,
//        `endif // }
//      `endif // }
  output                      cti_halt,
//    `if ((1 == 1) && (1 == 1)) // {
//      `if ((0 == 1) || (1 == 1)) // {
  output                      cti_break,
//      `endif // }
//    `endif // }
  output                      cti_sleep,


  //
  input                       dbg_cache_rst_disable, // cache behavior at reset

  input                       dccm_dmi_priority,    // DCCM DMI priority


  ////////// Watchdog reset output signals /////////////////////////////////
  //
  output                      watchdog_reset,     // Assert Watchdog reset


  ////////// RTT Programming interface ///////////////////////////////////
  //
  output                    rtt_read_a,  // RTT read pulse
  output                    rtt_write_a, // RTT write pulse
  output [31:0]  rtt_addr_r,  // RTT Pgm Address
  input  [31:0]      rtt_drd_r,   // RTT read data
  output [31:0]      rtt_dwr_r,   // RTT write data


  input                     rtt_prod_sel,

  ///////// RTT Pipeline tracking outputs ////////////////////////////////
  //
  output              rtt_inst_commit,   // instruction has committed
  output [31:1]  rtt_inst_addr,     // instruction address (pc)
  output              rtt_cond_valid,    // commit inst was conditional
  output              rtt_cond_pass,     // condition code test passed

  output              rtt_branch,        // instruction was a branch
  output              rtt_branch_indir,  // branch was indirect
  output [31:1]  rtt_branch_taddr,  // Target address of branch/exc
  output              rtt_dslot,         // Branch has delay slot
  output              rtt_in_deslot,     // in d or e slot
  output              rtt_in_eslot,      // in e slot
  output              rtt_uop_is_leave,  // ca has leave_s gen'd uop instr
  output              rtt_exception,     // exception has been taken
  output              rtt_exception_rtn, // exception RTIE executed
  output              rtt_interrupt,     // interrupt has been taken
  output              rtt_zd_loop,       // zero-delay loop has been taken

  output    [7:0]     rtt_process_id,    // Current value of PID register
  output              rtt_pid_wr_en,     // Write enable for PID register

  output              rtt_ss_halt,
  output              rtt_hw_bp,         // hardware breakpoint hit
  output              rtt_hw_exc,        // hardware error (memory error)
  output              rtt_sleep_mode,
  output              rtt_dbg_halt,
  output              rtt_rst_applied,

  // Actionpoints
  output              rtt_wp_hit,        // actionpoint has been hit
  output    [7:0]     rtt_wp_val,        // which actionpoints triggered
  output              rtt_sw_bp,         // software breakpoint hit


  output wire  [32:0] rtt_swe_data,    // SWE Trace data to RTT
  output wire         rtt_swe_val,     // SWE Trace data valid to RTT

  ////////// Freeze/restart interface ////////////////////////////////////
  //
  input               rtt_freeze,        //
  input [7:0]         rtt_src_num,

//  output                      pct_interrupt       ,
  ////////// Machine Halt / Sleep Status//////////////////////////////////////
  //
  output                      sys_halt_r /* verilator public_flat */,
  output                      sys_tf_halt_r,  // triple fault, ISA Align
  output                      sys_sleep_r,
  output  [2:0]  sys_sleep_mode_r,


  //////////// IFU IBP interface    /////////////////////////////////////////
  //
// leda NTL_CON37 off
// LMD: Signal/Net must read from the input port
// LJ: Signals are defined as part of the internal bus protocol, readibility
  output                     ifu_ibus_cmd_valid,      // command valid
  input                      ifu_ibus_cmd_accept,     // command accept
  output   [40-1:0] ifu_ibus_cmd_addr,       // command address (LSBs need to be tied to 0)
  output                     ifu_ibus_cmd_wrap,       // if true then critical word first
  output   [3:0]             ifu_ibus_cmd_cache,
  output   [3:0]             ifu_ibus_cmd_burst_size, // length of burst in number of data elements -1
  output   [1:0]             ifu_ibus_cmd_prot,       // if true then kernel mode, else user

  input                      ifu_ibus_rd_valid,       // read data valid
  input                      ifu_ibus_err_rd,         // read error
  output                     ifu_ibus_rd_accept,      // read data accept
  input  [64-1:0]            ifu_ibus_rd_data,        // read data
  input                      ifu_ibus_rd_last,        // read last
// leda NTL_CON37 on


  output                         lqwq_mem_cmd_valid,
  output                         lqwq_mem_cmd_cache,
  output                         lqwq_mem_cmd_burst_size,
  output                         lqwq_mem_cmd_read,
  input                          lqwq_mem_cmd_accept,
  output      [39:0]     lqwq_mem_cmd_addr,
  output                         lqwq_mem_cmd_lock,
  output                         lqwq_mem_cmd_excl,
  output      [2:0]              lqwq_mem_cmd_data_size,
  output      [1:0]              lqwq_mem_cmd_prot,

  output                         lqwq_mem_wr_valid,
  output                         lqwq_mem_wr_last,
  input                          lqwq_mem_wr_accept,
  output      [7:0] lqwq_mem_wr_mask,
  output      [63:0]    lqwq_mem_wr_data,

  input                          lqwq_mem_rd_valid,
  input                          lqwq_mem_err_rd,
  input                          lqwq_mem_rd_excl_ok,
  input                          lqwq_mem_rd_last,
  output                         lqwq_mem_rd_accept,
  input       [63:0]    lqwq_mem_rd_data,

  input                          lqwq_mem_wr_done,
  input                          lqwq_mem_wr_excl_done,
  input                          lqwq_mem_err_wr,
  output                         lqwq_mem_wr_resp_accept,


  ////////// RF IBP interface ///////////////////////////////////////////
  //
  output                         rf_cmd_valid,
  output                         rf_cmd_excl,
  input                          rf_cmd_accept,
  output                         rf_cmd_read,
  output  [39:0]         rf_cmd_addr,
  output  [1:0]                  rf_cmd_prot,
  output                         rf_cmd_wrap,
  output  [3:0]                  rf_cmd_burst_size,
  output  [3:0]                  rf_cmd_cache,
  output                         rf_cmd_lock,
  output  [2:0]                  rf_cmd_data_size,

  input                          rf_rd_valid,
  input                          rf_rd_last,
  input                          rf_err_rd,
  input [127:0]      rf_rd_data,
  output                         rf_rd_accept,

  ////////// CB IBP interface ///////////////////////////////////////////
  //
  output                         cb_cmd_valid,
  input                          cb_cmd_accept,
  output                         cb_cmd_read,
  output  [39:0]         cb_cmd_addr,
  output  [1:0]                  cb_cmd_prot,
  output                         cb_cmd_wrap,
  output  [3:0]                  cb_cmd_burst_size,
  output  [3:0]                  cb_cmd_cache,
  output                         cb_cmd_excl,
  output                         cb_cmd_lock,
  output  [2:0]                  cb_cmd_data_size,

  output                         cb_wr_valid,
  input                          cb_wr_accept,
  output                         cb_wr_last,
  output  [127:0]    cb_wr_data,
  output  [15:0]    cb_wr_mask,
  input                          cb_wr_done,
  input                          cb_err_wr,
  output                         cb_wr_resp_accept,


  /////// DCCM DMI IBP interface /////////////////////////////////////////////
  //
  // leda NTL_CON37 off
  // LMD: non driving port range
  // LJ:  Not all bits of bus used
  input                      dccm_dmi_cmd_valid,
  output                     dccm_dmi_cmd_accept,
  input                      dccm_dmi_cmd_read,
  input [24-1:3]        dccm_dmi_cmd_addr,

  output                     dccm_dmi_rd_valid,
  output                     dccm_dmi_err_rd,
  input                      dccm_dmi_rd_accept,
  output [63:0]     dccm_dmi_rd_data,

  input                      dccm_dmi_wr_valid,
  output                     dccm_dmi_wr_accept,
  input  [63:0]     dccm_dmi_wr_data,
  input  [7:0]  dccm_dmi_wr_mask,
  output                     dccm_dmi_wr_done,
  output                     dccm_dmi_err_wr,
  // leda NTL_CON37 on




  ////////// General input signals ///////////////////////////////////////////
  //
  input                      test_mode,

  input   [7:0]              arcnum /* verilator public_flat */,
  input   [7:0]              core_clusternum,

  //////////// Watchdog timer ////////////////////////////////////////////////
  //
  input                       wdt_clk,
  output                      wdt_reset_wdt_clk,       // Reset timeout signal from wdt clk
  input                       wdt_ext_timeout_ack_r,   // External timeout ack
  output                      wdt_ext_timeout_r,       // External timeout signal
  output                      wdt_reset,               // Reset timeout signal  



//`if 0 // {
 


  output                      fs_ic_tag_ecc_sb_error_r,
  output                      fs_ic_tag_ecc_db_error_r,
  output                      fs_ic_data_ecc_sb_error_r,
  output                      fs_ic_data_ecc_db_error_r,


  output                      fs_dccm_ecc_sb_error_r,
  output                      fs_dccm_ecc_db_error_r,

  output                      fs_dc_data_ecc_sb_error_r,
  output                      fs_dc_data_ecc_db_error_r,
  output                      fs_dc_tag_ecc_sb_error_r,
  output                      fs_dc_tag_ecc_db_error_r,
  output                      fs_itlb_ecc_sb_error_r,
  output                      fs_itlb_ecc_db_error_r,
  output                      fs_dtlb_ecc_sb_error_r,
  output                      fs_dtlb_ecc_db_error_r,
//`endif          // }   // HAS_SAFETY



// spyglass disable_block W240
// SMD: Signal declared but not read
// SJ:  ungated clk is unused in some configs
   input mem_ds,
   input mem_sd,
// spyglass enable_block W240




  // leda NTL_CLK03 off
  // LMD: Use only one edge of the clock
  // LJ:  Negative edge of clk used for optimizing internal memory timing
  //
  output                      cpu_clk_enable,     // level 1 clock request
  input                       l1_cg_dis,          // GLOBAL_L1_CLK_DIS aux bit
  input                       l1_accept_en,       // level 1 clock active
  input                       clk,                // Processor clock
  input                       clk_ungated,
  input                       rst_a               // Asynchronous reset

);


  
wire [5:0]    fs_ic_tag_bank0_syndrome_r;
wire                      fs_ic_tag_bank0_ecc_sb_error_r;
wire                      fs_ic_tag_bank0_ecc_db_error_r;
wire [5:0]    fs_ic_tag_bank1_syndrome_r;
wire                      fs_ic_tag_bank1_ecc_sb_error_r;
wire                      fs_ic_tag_bank1_ecc_db_error_r;
wire [5:0]    fs_ic_tag_bank2_syndrome_r;
wire                      fs_ic_tag_bank2_ecc_sb_error_r;
wire                      fs_ic_tag_bank2_ecc_db_error_r;
wire [5:0]    fs_ic_tag_bank3_syndrome_r;
wire                      fs_ic_tag_bank3_ecc_sb_error_r;
wire                      fs_ic_tag_bank3_ecc_db_error_r;
wire [5:0]    fs_ic_data_bank00_syndrome_r;
wire                      fs_ic_data_bank00_ecc_sb_error_r;
wire                      fs_ic_data_bank00_ecc_db_error_r;
wire [5:0]    fs_ic_data_bank01_syndrome_r;
wire                      fs_ic_data_bank01_ecc_sb_error_r;
wire                      fs_ic_data_bank01_ecc_db_error_r;
wire [5:0]    fs_ic_data_bank10_syndrome_r;
wire                      fs_ic_data_bank10_ecc_sb_error_r;
wire                      fs_ic_data_bank10_ecc_db_error_r;
wire [5:0]    fs_ic_data_bank11_syndrome_r;
wire                      fs_ic_data_bank11_ecc_sb_error_r;
wire                      fs_ic_data_bank11_ecc_db_error_r;
assign fs_ic_tag_ecc_sb_error_r = 1'b0 
                        | fs_ic_tag_bank0_ecc_sb_error_r
                        | fs_ic_tag_bank1_ecc_sb_error_r
                        | fs_ic_tag_bank2_ecc_sb_error_r
                        | fs_ic_tag_bank3_ecc_sb_error_r
                                       ;
assign fs_ic_tag_ecc_db_error_r = 1'b0 
                        | fs_ic_tag_bank0_ecc_db_error_r
                        | fs_ic_tag_bank1_ecc_db_error_r
                        | fs_ic_tag_bank2_ecc_db_error_r
                        | fs_ic_tag_bank3_ecc_db_error_r
                                       ;
assign fs_ic_data_ecc_sb_error_r = 1'b0 
                        | fs_ic_data_bank00_ecc_sb_error_r
                        | fs_ic_data_bank01_ecc_sb_error_r
                        | fs_ic_data_bank10_ecc_sb_error_r
                        | fs_ic_data_bank11_ecc_sb_error_r
                                       ;
assign fs_ic_data_ecc_db_error_r = 1'b0 
                        | fs_ic_data_bank00_ecc_db_error_r
                        | fs_ic_data_bank01_ecc_db_error_r
                        | fs_ic_data_bank10_ecc_db_error_r
                        | fs_ic_data_bank11_ecc_db_error_r
                                       ;

wire [5:0]    fs_dccm_bank0_syndrome_r;
wire [5:0]    fs_dccm_bank1_syndrome_r;
wire [5:0]    fs_dccm_bank2_syndrome_r;
wire [5:0]    fs_dccm_bank3_syndrome_r;
wire                      fs_dccm_bank0_ecc_sb_error_r;
wire                      fs_dccm_bank1_ecc_sb_error_r;
wire                      fs_dccm_bank2_ecc_sb_error_r;
wire                      fs_dccm_bank3_ecc_sb_error_r;
wire                      fs_dccm_bank0_ecc_db_error_r;
wire                      fs_dccm_bank1_ecc_db_error_r;
wire                      fs_dccm_bank2_ecc_db_error_r;
wire                      fs_dccm_bank3_ecc_db_error_r;
assign fs_dccm_ecc_sb_error_r = 1'b0 
                                 | fs_dccm_bank0_ecc_sb_error_r
                                 | fs_dccm_bank1_ecc_sb_error_r
                                 | fs_dccm_bank2_ecc_sb_error_r
                                 | fs_dccm_bank3_ecc_sb_error_r
                                       ;
assign fs_dccm_ecc_db_error_r = 1'b0 
                                 | fs_dccm_bank0_ecc_db_error_r
                                 | fs_dccm_bank1_ecc_db_error_r
                                 | fs_dccm_bank2_ecc_db_error_r
                                 | fs_dccm_bank3_ecc_db_error_r
                                       ;

wire [5:0]    fs_dc_tag_bank0_syndrome_r;
wire [5:0]    fs_dc_tag_bank1_syndrome_r;
wire [5:0]    fs_dc_tag_bank2_syndrome_r;
wire [5:0]    fs_dc_tag_bank3_syndrome_r;
	    

wire [5:0]    fs_dc_data_bank0_syndrome_r;
wire [5:0]    fs_dc_data_bank1_syndrome_r;
wire [5:0]    fs_dc_data_bank2_syndrome_r;
wire [5:0]    fs_dc_data_bank3_syndrome_r;
wire                      fs_dc_data_bank0_ecc_sb_error_r;
wire                      fs_dc_data_bank1_ecc_sb_error_r;
wire                      fs_dc_data_bank2_ecc_sb_error_r;
wire                      fs_dc_data_bank3_ecc_sb_error_r;
wire                      fs_dc_data_bank0_ecc_db_error_r;
wire                      fs_dc_data_bank1_ecc_db_error_r;
wire                      fs_dc_data_bank2_ecc_db_error_r;
wire                      fs_dc_data_bank3_ecc_db_error_r;
wire                      fs_dc_tag_bank0_ecc_sb_error_r;
wire                      fs_dc_tag_bank1_ecc_sb_error_r;
wire                      fs_dc_tag_bank2_ecc_sb_error_r;
wire                      fs_dc_tag_bank3_ecc_sb_error_r;
wire                      fs_dc_tag_bank0_ecc_db_error_r;
wire                      fs_dc_tag_bank1_ecc_db_error_r;
wire                      fs_dc_tag_bank2_ecc_db_error_r;
wire                      fs_dc_tag_bank3_ecc_db_error_r;
assign fs_dc_tag_ecc_sb_error_r = 1'b0 
                                 | fs_dc_tag_bank0_ecc_sb_error_r
                                 | fs_dc_tag_bank1_ecc_sb_error_r
                                 | fs_dc_tag_bank2_ecc_sb_error_r
                                 | fs_dc_tag_bank3_ecc_sb_error_r
                                       ;
assign fs_dc_tag_ecc_db_error_r = 1'b0 
                                 | fs_dc_tag_bank0_ecc_db_error_r
                                 | fs_dc_tag_bank1_ecc_db_error_r
                                 | fs_dc_tag_bank2_ecc_db_error_r
                                 | fs_dc_tag_bank3_ecc_db_error_r
                                       ;
assign fs_dc_data_ecc_sb_error_r = 1'b0 
                                 | fs_dc_data_bank0_ecc_sb_error_r
                                 | fs_dc_data_bank1_ecc_sb_error_r
                                 | fs_dc_data_bank2_ecc_sb_error_r
                                 | fs_dc_data_bank3_ecc_sb_error_r
                                       ;
assign fs_dc_data_ecc_db_error_r = 1'b0 
                                 | fs_dc_data_bank0_ecc_db_error_r
                                 | fs_dc_data_bank1_ecc_db_error_r
                                 | fs_dc_data_bank2_ecc_db_error_r
                                 | fs_dc_data_bank3_ecc_db_error_r
                                       ;

wire [5:0]    fs_itlb_bank0_syndrome_r;
wire [5:0]    fs_itlb_bank1_syndrome_r;
wire [5:0]    fs_itlb_bank2_syndrome_r;
wire [5:0]    fs_itlb_bank3_syndrome_r;
wire [5:0]    fs_itlb_bank4_syndrome_r;

wire [5:0]    fs_dtlb_bank0_syndrome_r;
wire [5:0]    fs_dtlb_bank1_syndrome_r;
wire [5:0]    fs_dtlb_bank2_syndrome_r;
wire [5:0]    fs_dtlb_bank3_syndrome_r;
wire [5:0]    fs_dtlb_bank4_syndrome_r;
wire                      fs_itlb_bank0_ecc_sb_error_r;
wire                      fs_itlb_bank1_ecc_sb_error_r;
wire                      fs_itlb_bank2_ecc_sb_error_r;
wire                      fs_itlb_bank3_ecc_sb_error_r;
wire                      fs_itlb_bank4_ecc_sb_error_r;
wire                      fs_itlb_bank0_ecc_db_error_r;
wire                      fs_itlb_bank1_ecc_db_error_r;
wire                      fs_itlb_bank2_ecc_db_error_r;
wire                      fs_itlb_bank3_ecc_db_error_r;
wire                      fs_itlb_bank4_ecc_db_error_r;
wire                      fs_dtlb_bank0_ecc_sb_error_r;
wire                      fs_dtlb_bank1_ecc_sb_error_r;
wire                      fs_dtlb_bank2_ecc_sb_error_r;
wire                      fs_dtlb_bank3_ecc_sb_error_r;
wire                      fs_dtlb_bank4_ecc_sb_error_r;
wire                      fs_dtlb_bank0_ecc_db_error_r;
wire                      fs_dtlb_bank1_ecc_db_error_r;
wire                      fs_dtlb_bank2_ecc_db_error_r;
wire                      fs_dtlb_bank3_ecc_db_error_r;
wire                      fs_dtlb_bank4_ecc_db_error_r;
assign fs_itlb_ecc_sb_error_r = 1'b0 
                                 | fs_itlb_bank0_ecc_sb_error_r
                                 | fs_itlb_bank1_ecc_sb_error_r
                                 | fs_itlb_bank2_ecc_sb_error_r
                                 | fs_itlb_bank3_ecc_sb_error_r
                                 | fs_itlb_bank4_ecc_sb_error_r
                                       ;
assign fs_itlb_ecc_db_error_r = 1'b0 
                                 | fs_itlb_bank0_ecc_db_error_r
                                 | fs_itlb_bank1_ecc_db_error_r
                                 | fs_itlb_bank2_ecc_db_error_r
                                 | fs_itlb_bank3_ecc_db_error_r
                                 | fs_itlb_bank4_ecc_db_error_r
                                       ;
assign fs_dtlb_ecc_sb_error_r = 1'b0 
                                 | fs_dtlb_bank0_ecc_sb_error_r
                                 | fs_dtlb_bank1_ecc_sb_error_r
                                 | fs_dtlb_bank2_ecc_sb_error_r
                                 | fs_dtlb_bank3_ecc_sb_error_r
                                 | fs_dtlb_bank4_ecc_sb_error_r
                                       ;
assign fs_dtlb_ecc_db_error_r = 1'b0 
                                 | fs_dtlb_bank0_ecc_db_error_r
                                 | fs_dtlb_bank1_ecc_db_error_r
                                 | fs_dtlb_bank2_ecc_db_error_r
                                 | fs_dtlb_bank3_ecc_db_error_r
                                 | fs_dtlb_bank4_ecc_db_error_r
                                       ;


`ifdef VERILATOR  // {
wire                             i_test_mode = 1'b0;
`else  // } {
wire                             i_test_mode = test_mode;
`endif // }

wire            ltest_mode;
   assign ltest_mode = i_test_mode;

   
wire                         rst;             // Re-synchronized reset

wire                         ls;                     // light sleep
wire                         gb_sys_halt_r;          // Global System Halt
wire                         gb_sys_tf_halt_r;       // Global System TF Halt
wire                         gb_sys_sleep_r;         // Global System Sleep
wire [2:0]      gb_sys_sleep_mode_r;
//wire                         imem_clk;

//////////////////////////////////////////////////////////////////////////////
/// Connectivity signals between cpu and srams                              //
//////////////////////////////////////////////////////////////////////////////
  // Instruction cache
  wire                        ic_data_bank0_clk;
  wire                        ic_data_ce0;
  wire [10:0]        ic_data_addr0;
  wire [78-1:0]   ic_data_din0;
  wire                        ic_data_we0;
  wire [10-1:0]ic_data_wem0;
  wire [78-1:0]   ic_data_dout0;
  wire                        ic_data_bank1_clk;
  wire                        ic_data_ce1;
  wire [10:0]        ic_data_addr1;
  wire [78-1:0]   ic_data_din1;
  wire                        ic_data_we1;
  wire [10-1:0]ic_data_wem1;
  wire [78-1:0]   ic_data_dout1;
  wire                        ic_tag_way0_clk;
  wire                        ic_tag_ce0;
  wire [12:6]        ic_tag_addr0;
  wire [36:0]       ic_tag_din0;
  wire                        ic_tag_we0;
  wire [36:0]  ic_tag_wem0;
  wire [36:0]       ic_tag_dout0;
  wire                        ic_tag_way1_clk;
  wire                        ic_tag_ce1;
  wire [12:6]        ic_tag_addr1;
  wire [36:0]       ic_tag_din1;
  wire                        ic_tag_we1;
  wire [36:0]  ic_tag_wem1;
  wire [36:0]       ic_tag_dout1;
  wire                        ic_tag_way2_clk;
  wire                        ic_tag_ce2;
  wire [12:6]        ic_tag_addr2;
  wire [36:0]       ic_tag_din2;
  wire                        ic_tag_we2;
  wire [36:0]  ic_tag_wem2;
  wire [36:0]       ic_tag_dout2;
  wire                        ic_tag_way3_clk;
  wire                        ic_tag_ce3;
  wire [12:6]        ic_tag_addr3;
  wire [36:0]       ic_tag_din3;
  wire                        ic_tag_we3;
  wire [36:0]  ic_tag_wem3;
  wire [36:0]       ic_tag_dout3;
  // Data cache
  wire                        clk_tag_even_w0;
  wire                        dc_tag_even_cs_w0;
  wire                        dc_tag_even_we_w0;
  wire [33:0]       dc_tag_even_wem_w0;
  wire [13:7]        dc_tag_even_addr_w0;
  wire [33:0]       dc_tag_even_din_w0;
  wire [33:0]       dc_tag_even_dout_w0;
  wire                        clk_tag_odd_w0;
  wire                        dc_tag_odd_cs_w0;
  wire                        dc_tag_odd_we_w0;
  wire [33:0]       dc_tag_odd_wem_w0;
  wire [13:7]        dc_tag_odd_addr_w0;
  wire [33:0]       dc_tag_odd_din_w0;
  wire [33:0]       dc_tag_odd_dout_w0;
  wire                        clk_tag_even_w1;
  wire                        dc_tag_even_cs_w1;
  wire                        dc_tag_even_we_w1;
  wire [33:0]       dc_tag_even_wem_w1;
  wire [13:7]        dc_tag_even_addr_w1;
  wire [33:0]       dc_tag_even_din_w1;
  wire [33:0]       dc_tag_even_dout_w1;
  wire                        clk_tag_odd_w1;
  wire                        dc_tag_odd_cs_w1;
  wire                        dc_tag_odd_we_w1;
  wire [33:0]       dc_tag_odd_wem_w1;
  wire [13:7]        dc_tag_odd_addr_w1;
  wire [33:0]       dc_tag_odd_din_w1;
  wire [33:0]       dc_tag_odd_dout_w1;
  wire                        clk_data_even_lo;
  wire                        dc_data_even_cs_lo;
  wire                        dc_data_even_we_lo;
  wire [9:0]     dc_data_even_wem_lo;
  wire [13:4]        dc_data_even_addr_lo;
  wire [77:0]       dc_data_even_din_lo;
  wire [77:0]       dc_data_even_dout_lo;
  wire                        clk_data_even_hi;
  wire                        dc_data_even_cs_hi;
  wire                        dc_data_even_we_hi;
  wire [9:0]     dc_data_even_wem_hi;
  wire [13:4]        dc_data_even_addr_hi;
  wire [77:0]       dc_data_even_din_hi;
  wire [77:0]       dc_data_even_dout_hi;
  wire                        clk_data_odd_lo;
  wire                        dc_data_odd_cs_lo;
  wire                        dc_data_odd_we_lo;
  wire [9:0]     dc_data_odd_wem_lo;
  wire [13:4]        dc_data_odd_addr_lo;
  wire [77:0]       dc_data_odd_din_lo;
  wire [77:0]       dc_data_odd_dout_lo;
  wire                        clk_data_odd_hi;
  wire                        dc_data_odd_cs_hi;
  wire                        dc_data_odd_we_hi;
  wire [9:0]     dc_data_odd_wem_hi;
  wire [13:4]        dc_data_odd_addr_hi;
  wire [77:0]       dc_data_odd_din_hi;
  wire [77:0]       dc_data_odd_dout_hi;
  // NTLB PD0 (tag) ram interface
  wire                        ntlb_pd0_clk;
  wire                        ntlb_pd0_ce;
  wire                        ntlb_pd0_we;
  wire [(4+4)-1:0]ntlb_pd0_wem;
  wire [5:0] ntlb_pd0_addr;
  wire [131:0] ntlb_pd0_wdata;
  wire [131:0] ntlb_pd0_rdata;
  // NTLB PD1 (data) ram interface
  wire                        ntlb_pd1_clk;
  wire                        ntlb_pd1_ce;
  wire                        ntlb_pd1_we;
  wire [7:0] ntlb_pd1_addr;
  wire [44:0] ntlb_pd1_wdata;
  wire [44:0] ntlb_pd1_rdata;
  // DCCM
  wire                        clk_dccm_bank0_lo;
  wire                        clk_dccm_bank0_hi;
  wire                        dccm_bank0_cs_lo;
  wire                        dccm_bank0_cs_hi;
  wire [14:4]      dccm_bank0_addr_lo;
  wire [14:4]      dccm_bank0_addr_hi;
  wire                        dccm_bank0_we_lo;
  wire                        dccm_bank0_we_hi;
  wire [77:0]      dccm_bank0_din;
  wire [9:0]   dccm_bank0_wem;
  wire [77:0]      dccm_bank0_dout;
  wire                        clk_dccm_bank1_lo;
  wire                        clk_dccm_bank1_hi;
  wire                        dccm_bank1_cs_lo;
  wire                        dccm_bank1_cs_hi;
  wire [14:4]      dccm_bank1_addr_lo;
  wire [14:4]      dccm_bank1_addr_hi;
  wire                        dccm_bank1_we_lo;
  wire                        dccm_bank1_we_hi;
  wire [77:0]      dccm_bank1_din;
  wire [9:0]   dccm_bank1_wem;
  wire [77:0]      dccm_bank1_dout;
  // I/O ports to BPU RAMS
  wire [67:0]    bc_din0;
  wire [11:4]     bc_addr0;
  wire                        bc_me0;
  wire                        bc_we0;
  wire [67:0]    bc_wem0;
  wire [67:0]    bc_dout0;
  wire [7:0]    gs_din0;
  wire [13:4]         gs_addr0;
  wire                        gs_me0;
  wire                        gs_we0;
  wire [7:0]    gs_wem0;
  wire [7:0]    gs_dout0;
  wire                        bc_ram0_clk;
  wire                        pt_ram0_clk;
  wire [67:0]    bc_din1;
  wire [11:4]     bc_addr1;
  wire                        bc_me1;
  wire                        bc_we1;
  wire [67:0]    bc_wem1;
  wire [67:0]    bc_dout1;
  wire [7:0]    gs_din1;
  wire [13:4]         gs_addr1;
  wire                        gs_me1;
  wire                        gs_we1;
  wire [7:0]    gs_wem1;
  wire [7:0]    gs_dout1;
  wire                        bc_ram1_clk;
  wire                        pt_ram1_clk;


//wire                          clk_gated;







//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Module instantiation - cpu                                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_cpu u_alb_cpu (




  .intvbase_in            (intvbase_in          ),

  ////////// External Event Interface /////////////////////////////////////////
  //
  .arc_event_a          (arc_event_a           ),

  .dbg_cache_rst_disable (dbg_cache_rst_disable), 
  .dccm_dmi_priority     (dccm_dmi_priority),   
  ////////// External Halt Request Interface /////////////////////////////////
  //
  .arc_halt_req_a       (arc_halt_req_a       ),
  .arc_run_req_a        (arc_run_req_a        ),
  .arc_halt_ack         (arc_halt_ack         ),
  .arc_run_ack          (arc_run_ack          ),



  ////////// EIA user extension external input signals ///////////////////////
  //
  .EventManager_evm_event_a (EventManager_evm_event_a),
  .EventManager_evm_sleep (EventManager_evm_sleep),

  ////////// EIA user extension external output signals //////////////////////
  //
  .EventManager_evm_wakeup (EventManager_evm_wakeup),
  .EventManager_evm_send (EventManager_evm_send),
  .EventManager_vm_grp0_sid (EventManager_vm_grp0_sid),
  .EventManager_vm_grp0_ssid (EventManager_vm_grp0_ssid),
  .EventManager_vm_grp1_sid (EventManager_vm_grp1_sid),
  .EventManager_vm_grp1_ssid (EventManager_vm_grp1_ssid),
  .EventManager_vm_grp2_sid (EventManager_vm_grp2_sid),
  .EventManager_vm_grp3_sid (EventManager_vm_grp3_sid),
  .EventManager_vm_grp2_ssid (EventManager_vm_grp2_ssid),
  .EventManager_vm_grp3_ssid (EventManager_vm_grp3_ssid),
  .EventManager_evt_vm_irq (EventManager_evt_vm_irq),
  .EventManager_evt_vm_sel (EventManager_evt_vm_sel),
   .clk_ungated         (clk_ungated          ),
// RAM interface for icache tags and data
  .ic_tag_way0_clk   (ic_tag_way0_clk   ),
  .ic_tag_din0         (ic_tag_din0         ),
  .ic_tag_dout0        (ic_tag_dout0        ),
  .ic_tag_addr0        (ic_tag_addr0        ),
  .ic_tag_wem0         (ic_tag_wem0         ),    
  .ic_tag_cen0         (ic_tag_ce0          ),
  .ic_tag_wen0         (ic_tag_we0          ) ,
  .ic_tag_way1_clk   (ic_tag_way1_clk   ),
  .ic_tag_din1         (ic_tag_din1         ),
  .ic_tag_dout1        (ic_tag_dout1        ),
  .ic_tag_addr1        (ic_tag_addr1        ),
  .ic_tag_wem1         (ic_tag_wem1         ),    
  .ic_tag_cen1         (ic_tag_ce1          ),
  .ic_tag_wen1         (ic_tag_we1          ) ,
  .ic_tag_way2_clk   (ic_tag_way2_clk   ),
  .ic_tag_din2         (ic_tag_din2         ),
  .ic_tag_dout2        (ic_tag_dout2        ),
  .ic_tag_addr2        (ic_tag_addr2        ),
  .ic_tag_wem2         (ic_tag_wem2         ),    
  .ic_tag_cen2         (ic_tag_ce2          ),
  .ic_tag_wen2         (ic_tag_we2          ) ,
  .ic_tag_way3_clk   (ic_tag_way3_clk   ),
  .ic_tag_din3         (ic_tag_din3         ),
  .ic_tag_dout3        (ic_tag_dout3        ),
  .ic_tag_addr3        (ic_tag_addr3        ),
  .ic_tag_wem3         (ic_tag_wem3         ),    
  .ic_tag_cen3         (ic_tag_ce3          ),
  .ic_tag_wen3         (ic_tag_we3          ) ,

  .ic_data_bank0_clk (ic_data_bank0_clk ),
  .ic_data_din0        (ic_data_din0        ),
  .ic_data_dout0       (ic_data_dout0       ),
  .ic_data_addr0       (ic_data_addr0       ),
  .ic_data_cen0        (ic_data_ce0         ),
  .ic_data_wen0        (ic_data_we0         ),
  .ic_data_wem0        (ic_data_wem0        ),
  .ic_data_bank1_clk (ic_data_bank1_clk ),
  .ic_data_din1        (ic_data_din1        ),
  .ic_data_dout1       (ic_data_dout1       ),
  .ic_data_addr1       (ic_data_addr1       ),
  .ic_data_cen1        (ic_data_ce1         ),
  .ic_data_wen1        (ic_data_we1         ),
  .ic_data_wem1        (ic_data_wem1        ),

  .fs_dccm_bank0_syndrome_r    (fs_dccm_bank0_syndrome_r),
  .fs_dccm_bank1_syndrome_r    (fs_dccm_bank1_syndrome_r),
  .fs_dccm_bank2_syndrome_r    (fs_dccm_bank2_syndrome_r),
  .fs_dccm_bank3_syndrome_r    (fs_dccm_bank3_syndrome_r),

  .fs_dccm_bank0_ecc_sb_error_r(fs_dccm_bank0_ecc_sb_error_r),
  .fs_dccm_bank1_ecc_sb_error_r(fs_dccm_bank1_ecc_sb_error_r),
  .fs_dccm_bank2_ecc_sb_error_r(fs_dccm_bank2_ecc_sb_error_r),
  .fs_dccm_bank3_ecc_sb_error_r(fs_dccm_bank3_ecc_sb_error_r),

  .fs_dccm_bank0_ecc_db_error_r(fs_dccm_bank0_ecc_db_error_r),
  .fs_dccm_bank1_ecc_db_error_r(fs_dccm_bank1_ecc_db_error_r),
  .fs_dccm_bank2_ecc_db_error_r(fs_dccm_bank2_ecc_db_error_r),
  .fs_dccm_bank3_ecc_db_error_r(fs_dccm_bank3_ecc_db_error_r),


  .clk_dccm_bank0_lo    (clk_dccm_bank0_lo ),
  .clk_dccm_bank0_hi    (clk_dccm_bank0_hi ),
  .dccm_bank0_cs_lo     (dccm_bank0_cs_lo  ),
  .dccm_bank0_cs_hi     (dccm_bank0_cs_hi  ),
  .dccm_bank0_addr_lo   (dccm_bank0_addr_lo),
  .dccm_bank0_addr_hi   (dccm_bank0_addr_hi),
  .dccm_bank0_we_lo     (dccm_bank0_we_lo  ),
  .dccm_bank0_we_hi     (dccm_bank0_we_hi  ),
  .dccm_bank0_wem       (dccm_bank0_wem    ),
  .dccm_bank0_din       (dccm_bank0_din    ),

  .dccm_bank0_dout      (dccm_bank0_dout   ),

  .clk_dccm_bank1_lo    (clk_dccm_bank1_lo ),
  .clk_dccm_bank1_hi    (clk_dccm_bank1_hi ),
  .dccm_bank1_cs_lo     (dccm_bank1_cs_lo  ),
  .dccm_bank1_cs_hi     (dccm_bank1_cs_hi  ),
  .dccm_bank1_addr_lo   (dccm_bank1_addr_lo),
  .dccm_bank1_addr_hi   (dccm_bank1_addr_hi),
  .dccm_bank1_we_lo     (dccm_bank1_we_lo  ),
  .dccm_bank1_we_hi     (dccm_bank1_we_hi  ),
  .dccm_bank1_wem       (dccm_bank1_wem    ),
  .dccm_bank1_din       (dccm_bank1_din    ),

  .dccm_bank1_dout      (dccm_bank1_dout   ),


  .dccm_dmi_cmd_valid      (dccm_dmi_cmd_valid ),
  .dccm_dmi_cmd_accept     (dccm_dmi_cmd_accept),
  .dccm_dmi_cmd_read       (dccm_dmi_cmd_read  ),
  .dccm_dmi_cmd_addr       (dccm_dmi_cmd_addr  ),

  .dccm_dmi_rd_valid       (dccm_dmi_rd_valid  ),
  .dccm_dmi_err_rd         (dccm_dmi_err_rd    ),
  .dccm_dmi_rd_accept      (dccm_dmi_rd_accept ),
  .dccm_dmi_rd_data        (dccm_dmi_rd_data   ),

  .dccm_dmi_wr_valid       (dccm_dmi_wr_valid  ),
  .dccm_dmi_wr_accept      (dccm_dmi_wr_accept ),
  .dccm_dmi_wr_data        (dccm_dmi_wr_data   ),
  .dccm_dmi_wr_mask        (dccm_dmi_wr_mask   ),
  .dccm_dmi_wr_done        (dccm_dmi_wr_done   ),
  .dccm_dmi_err_wr         (dccm_dmi_err_wr    ),
  .fs_dc_tag_bank0_syndrome_r     (fs_dc_tag_bank0_syndrome_r),
  .fs_dc_tag_bank1_syndrome_r     (fs_dc_tag_bank1_syndrome_r),
  .fs_dc_tag_bank2_syndrome_r     (fs_dc_tag_bank2_syndrome_r),
  .fs_dc_tag_bank3_syndrome_r     (fs_dc_tag_bank3_syndrome_r),

  .fs_dc_tag_bank0_ecc_sb_error_r (fs_dc_tag_bank0_ecc_sb_error_r),
  .fs_dc_tag_bank1_ecc_sb_error_r (fs_dc_tag_bank1_ecc_sb_error_r),
  .fs_dc_tag_bank2_ecc_sb_error_r (fs_dc_tag_bank2_ecc_sb_error_r),
  .fs_dc_tag_bank3_ecc_sb_error_r (fs_dc_tag_bank3_ecc_sb_error_r),

  .fs_dc_tag_bank0_ecc_db_error_r (fs_dc_tag_bank0_ecc_db_error_r),
  .fs_dc_tag_bank1_ecc_db_error_r (fs_dc_tag_bank1_ecc_db_error_r),
  .fs_dc_tag_bank2_ecc_db_error_r (fs_dc_tag_bank2_ecc_db_error_r),
  .fs_dc_tag_bank3_ecc_db_error_r (fs_dc_tag_bank3_ecc_db_error_r),

  .fs_dc_data_bank0_syndrome_r    (fs_dc_data_bank0_syndrome_r),
  .fs_dc_data_bank1_syndrome_r    (fs_dc_data_bank1_syndrome_r),
  .fs_dc_data_bank2_syndrome_r    (fs_dc_data_bank2_syndrome_r),
  .fs_dc_data_bank3_syndrome_r    (fs_dc_data_bank3_syndrome_r),

  .fs_dc_data_bank0_ecc_sb_error_r(fs_dc_data_bank0_ecc_sb_error_r),
  .fs_dc_data_bank1_ecc_sb_error_r(fs_dc_data_bank1_ecc_sb_error_r),
  .fs_dc_data_bank2_ecc_sb_error_r(fs_dc_data_bank2_ecc_sb_error_r),
  .fs_dc_data_bank3_ecc_sb_error_r(fs_dc_data_bank3_ecc_sb_error_r),

  .fs_dc_data_bank0_ecc_db_error_r(fs_dc_data_bank0_ecc_db_error_r),
  .fs_dc_data_bank1_ecc_db_error_r(fs_dc_data_bank1_ecc_db_error_r),
  .fs_dc_data_bank2_ecc_db_error_r(fs_dc_data_bank2_ecc_db_error_r),
  .fs_dc_data_bank3_ecc_db_error_r(fs_dc_data_bank3_ecc_db_error_r),


  .clk_tag_even_w0       (clk_tag_even_w0       ),
  .dc_tag_even_cs_w0     (dc_tag_even_cs_w0     ),
  .dc_tag_even_we_w0     (dc_tag_even_we_w0     ),
  .dc_tag_even_wem_w0    (dc_tag_even_wem_w0    ),
  .dc_tag_even_addr_w0   (dc_tag_even_addr_w0   ),
  .dc_tag_even_din_w0    (dc_tag_even_din_w0    ),
  .dc_tag_even_dout_w0   (dc_tag_even_dout_w0   ),

  .clk_tag_odd_w0        (clk_tag_odd_w0        ),
  .dc_tag_odd_cs_w0      (dc_tag_odd_cs_w0      ),
  .dc_tag_odd_we_w0      (dc_tag_odd_we_w0      ),
  .dc_tag_odd_wem_w0     (dc_tag_odd_wem_w0     ),
  .dc_tag_odd_addr_w0    (dc_tag_odd_addr_w0    ),
  .dc_tag_odd_din_w0     (dc_tag_odd_din_w0     ),
  .dc_tag_odd_dout_w0    (dc_tag_odd_dout_w0    ),

  .clk_tag_even_w1       (clk_tag_even_w1       ),
  .dc_tag_even_cs_w1     (dc_tag_even_cs_w1     ),
  .dc_tag_even_we_w1     (dc_tag_even_we_w1     ),
  .dc_tag_even_wem_w1    (dc_tag_even_wem_w1    ),
  .dc_tag_even_addr_w1   (dc_tag_even_addr_w1   ),
  .dc_tag_even_din_w1    (dc_tag_even_din_w1    ),
  .dc_tag_even_dout_w1   (dc_tag_even_dout_w1   ),

  .clk_tag_odd_w1        (clk_tag_odd_w1        ),
  .dc_tag_odd_cs_w1      (dc_tag_odd_cs_w1      ),
  .dc_tag_odd_we_w1      (dc_tag_odd_we_w1      ),
  .dc_tag_odd_wem_w1     (dc_tag_odd_wem_w1     ),
  .dc_tag_odd_addr_w1    (dc_tag_odd_addr_w1    ),
  .dc_tag_odd_din_w1     (dc_tag_odd_din_w1     ),
  .dc_tag_odd_dout_w1    (dc_tag_odd_dout_w1    ),

  .clk_data_even_lo       (clk_data_even_lo       ),
  .dc_data_even_cs_lo     (dc_data_even_cs_lo     ),
  .dc_data_even_we_lo     (dc_data_even_we_lo     ),
  .dc_data_even_wem_lo    (dc_data_even_wem_lo    ),
  .dc_data_even_addr_lo   (dc_data_even_addr_lo   ),
  .dc_data_even_din_lo    (dc_data_even_din_lo    ),
  .dc_data_even_dout_lo   (dc_data_even_dout_lo   ),

  .clk_data_even_hi       (clk_data_even_hi       ),
  .dc_data_even_cs_hi     (dc_data_even_cs_hi     ),
  .dc_data_even_we_hi     (dc_data_even_we_hi     ),
  .dc_data_even_wem_hi    (dc_data_even_wem_hi    ),
  .dc_data_even_addr_hi   (dc_data_even_addr_hi   ),
  .dc_data_even_din_hi    (dc_data_even_din_hi    ),
  .dc_data_even_dout_hi   (dc_data_even_dout_hi   ),

  .clk_data_odd_lo        (clk_data_odd_lo        ),
  .dc_data_odd_cs_lo      (dc_data_odd_cs_lo      ),
  .dc_data_odd_we_lo      (dc_data_odd_we_lo      ),
  .dc_data_odd_wem_lo     (dc_data_odd_wem_lo     ),
  .dc_data_odd_addr_lo    (dc_data_odd_addr_lo    ),
  .dc_data_odd_din_lo     (dc_data_odd_din_lo     ),
  .dc_data_odd_dout_lo    (dc_data_odd_dout_lo    ),

  .clk_data_odd_hi        (clk_data_odd_hi        ),
  .dc_data_odd_cs_hi      (dc_data_odd_cs_hi      ),
  .dc_data_odd_we_hi      (dc_data_odd_we_hi      ),
  .dc_data_odd_wem_hi     (dc_data_odd_wem_hi     ),
  .dc_data_odd_addr_hi    (dc_data_odd_addr_hi    ),
  .dc_data_odd_din_hi     (dc_data_odd_din_hi     ),
  .dc_data_odd_dout_hi    (dc_data_odd_dout_hi    ),



  ////////// Interrupt signals ///////////////////////////////////////////////
  //
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



  .biu_dmi_clk_en_req     (biu_dmi_clk_en_req         ),

  // No BIU
  //
  .ifu_ibus_cmd_valid      (ifu_ibus_cmd_valid    ),
  .ifu_ibus_cmd_accept     (ifu_ibus_cmd_accept   ),
  .ifu_ibus_cmd_addr       (ifu_ibus_cmd_addr     ),
  .ifu_ibus_cmd_wrap       (ifu_ibus_cmd_wrap     ),
  .ifu_ibus_cmd_cache      (ifu_ibus_cmd_cache    ),
  .ifu_ibus_cmd_burst_size (ifu_ibus_cmd_burst_size),
  .ifu_ibus_cmd_prot       (ifu_ibus_cmd_prot     ),
  .ifu_ibus_rd_valid       (ifu_ibus_rd_valid     ),
  .ifu_ibus_err_rd         (ifu_ibus_err_rd       ),
  .ifu_ibus_rd_accept      (ifu_ibus_rd_accept    ),
  .ifu_ibus_rd_data        (ifu_ibus_rd_data      ),
  .ifu_ibus_rd_last        (ifu_ibus_rd_last      ),




  // No internal BIU
  //



  .lqwq_mem_cmd_valid       (lqwq_mem_cmd_valid     ),
  .lqwq_mem_cmd_cache       (lqwq_mem_cmd_cache     ),
  .lqwq_mem_cmd_burst_size  (lqwq_mem_cmd_burst_size),
  .lqwq_mem_cmd_read        (lqwq_mem_cmd_read      ),
  .lqwq_mem_cmd_accept      (lqwq_mem_cmd_accept    ),
  .lqwq_mem_cmd_addr        (lqwq_mem_cmd_addr      ),
  .lqwq_mem_cmd_lock        (lqwq_mem_cmd_lock      ),
  .lqwq_mem_cmd_excl        (lqwq_mem_cmd_excl      ),
  .lqwq_mem_cmd_data_size   (lqwq_mem_cmd_data_size ),
  .lqwq_mem_cmd_prot        (lqwq_mem_cmd_prot      ),

  .lqwq_mem_wr_valid        (lqwq_mem_wr_valid      ),
  .lqwq_mem_wr_last         (lqwq_mem_wr_last       ),
  .lqwq_mem_wr_accept       (lqwq_mem_wr_accept     ),
  .lqwq_mem_wr_mask         (lqwq_mem_wr_mask       ),
  .lqwq_mem_wr_data         (lqwq_mem_wr_data       ),

  .lqwq_mem_rd_valid        (lqwq_mem_rd_valid      ),
  .lqwq_mem_err_rd          (lqwq_mem_err_rd        ),
  .lqwq_mem_rd_excl_ok      (lqwq_mem_rd_excl_ok    ),
  .lqwq_mem_rd_last         (lqwq_mem_rd_last       ),
  .lqwq_mem_rd_accept       (lqwq_mem_rd_accept     ),
  .lqwq_mem_rd_data         (lqwq_mem_rd_data       ),

  .lqwq_mem_wr_done         (lqwq_mem_wr_done       ),
  .lqwq_mem_wr_excl_done    (lqwq_mem_wr_excl_done  ),
  .lqwq_mem_err_wr          (lqwq_mem_err_wr        ),
  .lqwq_mem_wr_resp_accept  (lqwq_mem_wr_resp_accept),


  // DCACHE IBP
  //
  .rf_cmd_valid           (rf_cmd_valid         ),
  .rf_cmd_cache           (rf_cmd_cache         ),
  .rf_cmd_excl            (rf_cmd_excl          ),
  .rf_cmd_data_size       (rf_cmd_data_size     ),
  .rf_cmd_accept          (rf_cmd_accept        ),
  .rf_cmd_read            (rf_cmd_read          ),
  .rf_cmd_addr            (rf_cmd_addr          ),
  .rf_cmd_lock            (rf_cmd_lock          ),
  .rf_cmd_prot            (rf_cmd_prot          ),
  .rf_cmd_wrap            (rf_cmd_wrap          ),
  .rf_cmd_burst_size      (rf_cmd_burst_size    ),

  .rf_rd_valid            (rf_rd_valid          ),
  .rf_rd_last             (rf_rd_last           ),
  .rf_err_rd              (rf_err_rd            ),
  .rf_rd_data             (rf_rd_data           ),
  .rf_rd_accept           (rf_rd_accept         ),

  .cb_cmd_valid           (cb_cmd_valid         ),
  .cb_cmd_cache           (cb_cmd_cache         ),
  .cb_cmd_excl            (cb_cmd_excl          ),
  .cb_cmd_data_size       (cb_cmd_data_size     ),
  .cb_cmd_accept          (cb_cmd_accept        ),
  .cb_cmd_read            (cb_cmd_read          ),
  .cb_cmd_addr            (cb_cmd_addr          ),
  .cb_cmd_lock            (cb_cmd_lock          ),
  .cb_cmd_prot            (cb_cmd_prot          ),
  .cb_cmd_wrap            (cb_cmd_wrap          ),
  .cb_cmd_burst_size      (cb_cmd_burst_size    ),

  .cb_wr_valid            (cb_wr_valid          ),
  .cb_wr_accept           (cb_wr_accept         ),
  .cb_wr_last             (cb_wr_last           ),
  .cb_wr_data             (cb_wr_data           ),
  .cb_wr_mask             (cb_wr_mask           ),
  .cb_wr_done             (cb_wr_done           ),
  .cb_err_wr              (cb_err_wr            ),
  .cb_wr_resp_accept      (cb_wr_resp_accept    ),




  ////////// Inputs to the debug target interface ////////////////////////////
  //
  .dbg_cmdval           (dbg_cmdval          ),
  .dbg_address          (dbg_address         ),
  .dbg_be               (dbg_be              ),
  .dbg_cmd              (dbg_cmd             ),
  .dbg_wdata            (dbg_wdata           ),
  .dbg_rspack           (dbg_rspack          ),

  ////////// Outputs from the debug target interface /////////////////////////
  //
  .dbg_cmdack           (dbg_cmdack          ),
  .dbg_rspval           (dbg_rspval          ),
  .dbg_rdata            (dbg_rdata           ),
  .dbg_reop             (dbg_reop            ),
  .dbg_rerr             (dbg_rerr            ),
  .debug_reset          (debug_reset         ),

  ////////// APB debug interface /////////////////////////////////////////////

  .dbg_prot_sel         (dbg_prot_sel        ),
  .pclkdbg_en           (pclkdbg_en          ),
  .presetdbgn           (presetdbgn          ),
  .paddrdbg             (paddrdbg            ),
  .pseldbg              (pseldbg             ),
  .penabledbg           (penabledbg          ),
  .pwritedbg            (pwritedbg           ),
  .pwdatadbg            (pwdatadbg           ),
  .preadydbg            (preadydbg           ),
  .prdatadbg            (prdatadbg           ),
  .pslverrdbg           (pslverrdbg          ),
  .dbgen                (dbgen               ),
  .niden                (niden               ),
  .cti_ap_status        (cti_ap_status       ),
  .cti_ap_hit           (cti_ap_hit          ),
  .cti_halt             (cti_halt            ),
  .cti_break            (cti_break           ),
  .cti_sleep            (cti_sleep           ),



  .fs_itlb_bank0_syndrome_r     (fs_itlb_bank0_syndrome_r),
  .fs_itlb_bank1_syndrome_r     (fs_itlb_bank1_syndrome_r),
  .fs_itlb_bank2_syndrome_r     (fs_itlb_bank2_syndrome_r),
  .fs_itlb_bank3_syndrome_r     (fs_itlb_bank3_syndrome_r),
  .fs_itlb_bank4_syndrome_r     (fs_itlb_bank4_syndrome_r),

  .fs_itlb_bank0_ecc_sb_error_r (fs_itlb_bank0_ecc_sb_error_r),
  .fs_itlb_bank1_ecc_sb_error_r (fs_itlb_bank1_ecc_sb_error_r),
  .fs_itlb_bank2_ecc_sb_error_r (fs_itlb_bank2_ecc_sb_error_r),
  .fs_itlb_bank3_ecc_sb_error_r (fs_itlb_bank3_ecc_sb_error_r),
  .fs_itlb_bank4_ecc_sb_error_r (fs_itlb_bank4_ecc_sb_error_r),

  .fs_itlb_bank0_ecc_db_error_r (fs_itlb_bank0_ecc_db_error_r),
  .fs_itlb_bank1_ecc_db_error_r (fs_itlb_bank1_ecc_db_error_r),
  .fs_itlb_bank2_ecc_db_error_r (fs_itlb_bank2_ecc_db_error_r),
  .fs_itlb_bank3_ecc_db_error_r (fs_itlb_bank3_ecc_db_error_r),
  .fs_itlb_bank4_ecc_db_error_r (fs_itlb_bank4_ecc_db_error_r),

  .fs_dtlb_bank0_syndrome_r     (fs_dtlb_bank0_syndrome_r),
  .fs_dtlb_bank1_syndrome_r     (fs_dtlb_bank1_syndrome_r),
  .fs_dtlb_bank2_syndrome_r     (fs_dtlb_bank2_syndrome_r),
  .fs_dtlb_bank3_syndrome_r     (fs_dtlb_bank3_syndrome_r),
  .fs_dtlb_bank4_syndrome_r     (fs_dtlb_bank4_syndrome_r),

  .fs_dtlb_bank0_ecc_sb_error_r (fs_dtlb_bank0_ecc_sb_error_r),
  .fs_dtlb_bank1_ecc_sb_error_r (fs_dtlb_bank1_ecc_sb_error_r),
  .fs_dtlb_bank2_ecc_sb_error_r (fs_dtlb_bank2_ecc_sb_error_r),
  .fs_dtlb_bank3_ecc_sb_error_r (fs_dtlb_bank3_ecc_sb_error_r),
  .fs_dtlb_bank4_ecc_sb_error_r (fs_dtlb_bank4_ecc_sb_error_r),

  .fs_dtlb_bank0_ecc_db_error_r (fs_dtlb_bank0_ecc_db_error_r),
  .fs_dtlb_bank1_ecc_db_error_r (fs_dtlb_bank1_ecc_db_error_r),
  .fs_dtlb_bank2_ecc_db_error_r (fs_dtlb_bank2_ecc_db_error_r),
  .fs_dtlb_bank3_ecc_db_error_r (fs_dtlb_bank3_ecc_db_error_r),
  .fs_dtlb_bank4_ecc_db_error_r (fs_dtlb_bank4_ecc_db_error_r),



// NTLB PD0 (tag) ram interface
  .ntlb_pd0_clk         (ntlb_pd0_clk),
  .ntlb_pd0_ce          (ntlb_pd0_ce),
  .ntlb_pd0_we          (ntlb_pd0_we),
  .ntlb_pd0_wem         (ntlb_pd0_wem),
  .ntlb_pd0_addr        (ntlb_pd0_addr),
  .ntlb_pd0_wdata       (ntlb_pd0_wdata),
  .ntlb_pd0_rdata       (ntlb_pd0_rdata),

// NTLB PD1 (data) ram interface
  .ntlb_pd1_clk         (ntlb_pd1_clk),
  .ntlb_pd1_ce          (ntlb_pd1_ce),
  .ntlb_pd1_we          (ntlb_pd1_we),
  .ntlb_pd1_addr        (ntlb_pd1_addr),
  .ntlb_pd1_wdata       (ntlb_pd1_wdata),
  .ntlb_pd1_rdata       (ntlb_pd1_rdata),

  //////////  RTT interface (ext pins) ///////////////////////////////////////
  //
  .rtt_read_a          (rtt_read_a         ),
  .rtt_write_a         (rtt_write_a        ),
  .rtt_addr_r          (rtt_addr_r         ),
  .rtt_dwr_r           (rtt_dwr_r          ),
  .rtt_drd_r           (rtt_drd_r          ),

  .rtt_prod_sel        (rtt_prod_sel       ),
 
  .rtt_inst_commit     (rtt_inst_commit    ),
  .rtt_inst_addr       (rtt_inst_addr      ),
  .rtt_cond_valid      (rtt_cond_valid     ),
  .rtt_cond_pass       (rtt_cond_pass      ),
  .rtt_branch          (rtt_branch         ),
  .rtt_branch_indir    (rtt_branch_indir   ),
  .rtt_branch_taddr    (rtt_branch_taddr   ),
  .rtt_dslot           (rtt_dslot          ),
  .rtt_in_deslot       (rtt_in_deslot      ),
  .rtt_in_eslot        (rtt_in_eslot       ),
  .rtt_uop_is_leave    (rtt_uop_is_leave   ),
  .rtt_exception       (rtt_exception      ),
  .rtt_exception_rtn   (rtt_exception_rtn  ),
  .rtt_interrupt       (rtt_interrupt      ),
  .rtt_zd_loop         (rtt_zd_loop        ),

  .rtt_process_id      (rtt_process_id     ),
  .rtt_pid_wr_en       (rtt_pid_wr_en      ),

  .rtt_ss_halt         (rtt_ss_halt        ),
  .rtt_hw_bp           (rtt_hw_bp          ),
  .rtt_hw_exc          (rtt_hw_exc         ),
  .rtt_sleep_mode      (rtt_sleep_mode     ),
  .rtt_dbg_halt        (rtt_dbg_halt       ),
  .rtt_rst_applied     (rtt_rst_applied    ),

  .rtt_wp_hit          (rtt_wp_hit         ),
  .rtt_wp_val          (rtt_wp_val         ),
  .rtt_sw_bp           (rtt_sw_bp          ),

  .rtt_swe_data        (rtt_swe_data       ),
  .rtt_swe_val         (rtt_swe_val        ),
  .rtt_freeze          (rtt_freeze         ),
  .rtt_src_num         (rtt_src_num        ),

//  .pct_interrupt        (pct_interrupt       ),
  .bc_din0              (bc_din0             ),
  .bc_addr0             (bc_addr0            ),
  .bc_me0               (bc_me0              ),
  .bc_we0               (bc_we0              ),
  .bc_wem0              (bc_wem0             ),
  .bc_dout0             (bc_dout0            ),
  .gs_din0              (gs_din0             ),
  .gs_addr0             (gs_addr0            ),
  .gs_me0               (gs_me0              ),
  .gs_we0               (gs_we0              ),
  .gs_wem0              (gs_wem0             ),
  .gs_dout0             (gs_dout0            ),
  .bc_ram0_clk          (bc_ram0_clk         ),
  .pt_ram0_clk          (pt_ram0_clk         ),
  .bc_ram0_clk_en       (bc_ram0_clk_en      ),
  .pt_ram0_clk_en       (pt_ram0_clk_en      ),

  .bc_din1              (bc_din1             ),
  .bc_addr1             (bc_addr1            ),
  .bc_me1               (bc_me1              ),
  .bc_we1               (bc_we1              ),
  .bc_wem1              (bc_wem1             ),
  .bc_dout1             (bc_dout1            ),
  .gs_din1              (gs_din1             ),
  .gs_addr1             (gs_addr1            ),
  .gs_me1               (gs_me1              ),
  .gs_we1               (gs_we1              ),
  .gs_wem1              (gs_wem1             ),
  .gs_dout1             (gs_dout1            ),
  .bc_ram1_clk          (bc_ram1_clk         ),
  .pt_ram1_clk          (pt_ram1_clk         ),
  .bc_ram1_clk_en       (bc_ram1_clk_en      ),
  .pt_ram1_clk_en       (pt_ram1_clk_en      ),

//  .imem_clk             (imem_clk            ),
  .aux_rs_valid           (aux_rs_valid          ), //
  .aux_rs_region          (aux_rs_region         ), //
  .aux_rs_addr            (aux_rs_addr           ), //
  .aux_rs_read            (aux_rs_read           ), //
  .aux_rs_write           (aux_rs_write          ), //
  .aux_rs_data            (aux_rs_data           ), //
  .aux_rs_status          (aux_rs_status         ), //
  .aux_rs_accept          (aux_rs_accept         ), //

  .aux_wr_valid           (aux_wr_valid          ), //
  .aux_wr_region          (aux_wr_region         ), //
  .aux_wr_addr            (aux_wr_addr           ), //
  .aux_wr_data            (aux_wr_data           ), //
  .aux_wr_allow           (aux_wr_allow          ), //
  .aux_cm_phase           (aux_cm_phase          ), //
  .aux_cm_valid           (aux_cm_valid          ), //
  ////////// Outputs from the CPU to /////////////////////////////////////////
  //
  .test_mode            (ltest_mode          ), //
  .arcnum               (arcnum              ), //
  .clusternum           (core_clusternum     ),
  .watchdog_reset       (watchdog_reset      ), //

  ////////// Machine Halt Interface //////////////////////////////////////////
  //
  .gb_sys_halt_r        (gb_sys_halt_r       ), //
  .gb_sys_tf_halt_r     (gb_sys_tf_halt_r    ), //
  .gb_sys_sleep_r       (gb_sys_sleep_r      ), //
  .gb_sys_sleep_mode_r  (gb_sys_sleep_mode_r ), //

  ////////// MMB bus signals for memory BIST ////////////////////////////////
  //

   .wdt_clk             (wdt_clk              ),
  .wdt_reset2             (wdt_reset_wdt_clk    ),
  .wdt_ext_timeout_ack_r(wdt_ext_timeout_ack_r),
  .wdt_ext_timeout_r    (wdt_ext_timeout_r    ),
  .wdt_reset            (wdt_reset            ),
  
  
  




//     `if (0 == 1) // {

  .fs_ic_tag_bank0_syndrome_r      (fs_ic_tag_bank0_syndrome_r    ),
  .fs_ic_tag_bank0_ecc_sb_error_r  (fs_ic_tag_bank0_ecc_sb_error_r   ),
  .fs_ic_tag_bank0_ecc_db_error_r  (fs_ic_tag_bank0_ecc_db_error_r   ),
  .fs_ic_tag_bank1_syndrome_r      (fs_ic_tag_bank1_syndrome_r    ),
  .fs_ic_tag_bank1_ecc_sb_error_r  (fs_ic_tag_bank1_ecc_sb_error_r   ),
  .fs_ic_tag_bank1_ecc_db_error_r  (fs_ic_tag_bank1_ecc_db_error_r   ),
  .fs_ic_tag_bank2_syndrome_r      (fs_ic_tag_bank2_syndrome_r    ),
  .fs_ic_tag_bank2_ecc_sb_error_r  (fs_ic_tag_bank2_ecc_sb_error_r   ),
  .fs_ic_tag_bank2_ecc_db_error_r  (fs_ic_tag_bank2_ecc_db_error_r   ),
  .fs_ic_tag_bank3_syndrome_r      (fs_ic_tag_bank3_syndrome_r    ),
  .fs_ic_tag_bank3_ecc_sb_error_r  (fs_ic_tag_bank3_ecc_sb_error_r   ),
  .fs_ic_tag_bank3_ecc_db_error_r  (fs_ic_tag_bank3_ecc_db_error_r   ),
  .fs_ic_data_bank00_ecc_sb_error_r (fs_ic_data_bank00_ecc_sb_error_r),
  .fs_ic_data_bank00_ecc_db_error_r (fs_ic_data_bank00_ecc_db_error_r),
  .fs_ic_data_bank00_syndrome_r  (fs_ic_data_bank00_syndrome_r     ),
  .fs_ic_data_bank01_ecc_sb_error_r (fs_ic_data_bank01_ecc_sb_error_r),
  .fs_ic_data_bank01_ecc_db_error_r (fs_ic_data_bank01_ecc_db_error_r),
  .fs_ic_data_bank01_syndrome_r  (fs_ic_data_bank01_syndrome_r     ),
  .fs_ic_data_bank10_ecc_sb_error_r (fs_ic_data_bank10_ecc_sb_error_r),
  .fs_ic_data_bank10_ecc_db_error_r (fs_ic_data_bank10_ecc_db_error_r),
  .fs_ic_data_bank10_syndrome_r  (fs_ic_data_bank10_syndrome_r     ),
  .fs_ic_data_bank11_ecc_sb_error_r (fs_ic_data_bank11_ecc_sb_error_r),
  .fs_ic_data_bank11_ecc_db_error_r (fs_ic_data_bank11_ecc_db_error_r),
  .fs_ic_data_bank11_syndrome_r  (fs_ic_data_bank11_syndrome_r     ),

//     `endif               // }




/////////// Glue logic signals to alb_cpu_top /////////////////////
  
  

////////// SAFETY signals ///////////////////////////////////////////
  //

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////             
  ////////// General input signals ///////////////////////////////////////////
  //
  .cpu_clk_enable       (cpu_clk_enable      ),        // level 1 clk req
  .cpu_l1_cg_dis        (l1_cg_dis           ),
  .cpu_l1_accept_en     (l1_accept_en        ),
  .clk                  (clk                 ),
// spyglass disable_block Ac_conv01
// SMD: Ac_conv01 Convergence  
// SJ: These signals are independent which is not need to be cared  
// spyglass enable_block Ac_conv01  
  .rst                  (rst                 ),
  .rst_a                (rst_a               )
);

assign ls = 1'b0;


///////////////////////////////////////////////////////////////////////////////
// SRAMS                                                                     //
///////////////////////////////////////////////////////////////////////////////
npuarc_alb_srams u_alb_srams (

  // Instruction cache
  .ic_data_bank0_clk          (ic_data_bank0_clk),
  .ic_data_ce0                (ic_data_ce0),
  .ic_data_addr0              (ic_data_addr0),
  .ic_data_din0               (ic_data_din0),
  .ic_data_we0                (ic_data_we0),
  .ic_data_wem0               (ic_data_wem0),
  .ic_data_ds0                (mem_ds),
  .ic_data_sd0                (mem_sd),
  .ic_data_dout0              (ic_data_dout0),
  .ic_data_bank1_clk          (ic_data_bank1_clk),
  .ic_data_ce1                (ic_data_ce1),
  .ic_data_addr1              (ic_data_addr1),
  .ic_data_din1               (ic_data_din1),
  .ic_data_we1                (ic_data_we1),
  .ic_data_wem1               (ic_data_wem1),
  .ic_data_ds1                (mem_ds),
  .ic_data_sd1                (mem_sd),
  .ic_data_dout1              (ic_data_dout1),
  .ic_tag_way0_clk            (ic_tag_way0_clk),
  .ic_tag_ce0                 (ic_tag_ce0),
  .ic_tag_addr0               (ic_tag_addr0),
  .ic_tag_din0                (ic_tag_din0),
  .ic_tag_we0                 (ic_tag_we0),
  .ic_tag_wem0                (ic_tag_wem0),
  .ic_tag_ds0                 (mem_ds),
  .ic_tag_sd0                 (mem_sd),
  .ic_tag_dout0               (ic_tag_dout0),
  .ic_tag_way1_clk            (ic_tag_way1_clk),
  .ic_tag_ce1                 (ic_tag_ce1),
  .ic_tag_addr1               (ic_tag_addr1),
  .ic_tag_din1                (ic_tag_din1),
  .ic_tag_we1                 (ic_tag_we1),
  .ic_tag_wem1                (ic_tag_wem1),
  .ic_tag_ds1                 (mem_ds),
  .ic_tag_sd1                 (mem_sd),
  .ic_tag_dout1               (ic_tag_dout1),
  .ic_tag_way2_clk            (ic_tag_way2_clk),
  .ic_tag_ce2                 (ic_tag_ce2),
  .ic_tag_addr2               (ic_tag_addr2),
  .ic_tag_din2                (ic_tag_din2),
  .ic_tag_we2                 (ic_tag_we2),
  .ic_tag_wem2                (ic_tag_wem2),
  .ic_tag_ds2                 (mem_ds),
  .ic_tag_sd2                 (mem_sd),
  .ic_tag_dout2               (ic_tag_dout2),
  .ic_tag_way3_clk            (ic_tag_way3_clk),
  .ic_tag_ce3                 (ic_tag_ce3),
  .ic_tag_addr3               (ic_tag_addr3),
  .ic_tag_din3                (ic_tag_din3),
  .ic_tag_we3                 (ic_tag_we3),
  .ic_tag_wem3                (ic_tag_wem3),
  .ic_tag_ds3                 (mem_ds),
  .ic_tag_sd3                 (mem_sd),
  .ic_tag_dout3               (ic_tag_dout3),
  // Data cache
  .clk_tag_even_w0            (clk_tag_even_w0),
  .dc_tag_even_cs_w0          (dc_tag_even_cs_w0),
  .dc_tag_even_we_w0          (dc_tag_even_we_w0),
  .dc_tag_even_wem_w0         (dc_tag_even_wem_w0),
  .dc_tag_even_addr_w0        (dc_tag_even_addr_w0),
  .dc_tag_even_din_w0         (dc_tag_even_din_w0),
  .dc_tag_even_ds_w0          (mem_ds),
  .dc_tag_even_sd_w0          (mem_sd),
  .dc_tag_even_dout_w0        (dc_tag_even_dout_w0),
  .clk_tag_odd_w0             (clk_tag_odd_w0),
  .dc_tag_odd_cs_w0           (dc_tag_odd_cs_w0),
  .dc_tag_odd_we_w0           (dc_tag_odd_we_w0),
  .dc_tag_odd_wem_w0          (dc_tag_odd_wem_w0),
  .dc_tag_odd_addr_w0         (dc_tag_odd_addr_w0),
  .dc_tag_odd_din_w0          (dc_tag_odd_din_w0),
  .dc_tag_odd_ds_w0           (mem_ds),
  .dc_tag_odd_sd_w0           (mem_sd),
  .dc_tag_odd_dout_w0         (dc_tag_odd_dout_w0),
  .clk_tag_even_w1            (clk_tag_even_w1),
  .dc_tag_even_cs_w1          (dc_tag_even_cs_w1),
  .dc_tag_even_we_w1          (dc_tag_even_we_w1),
  .dc_tag_even_wem_w1         (dc_tag_even_wem_w1),
  .dc_tag_even_addr_w1        (dc_tag_even_addr_w1),
  .dc_tag_even_din_w1         (dc_tag_even_din_w1),
  .dc_tag_even_ds_w1          (mem_ds),
  .dc_tag_even_sd_w1          (mem_sd),
  .dc_tag_even_dout_w1        (dc_tag_even_dout_w1),
  .clk_tag_odd_w1             (clk_tag_odd_w1),
  .dc_tag_odd_cs_w1           (dc_tag_odd_cs_w1),
  .dc_tag_odd_we_w1           (dc_tag_odd_we_w1),
  .dc_tag_odd_wem_w1          (dc_tag_odd_wem_w1),
  .dc_tag_odd_addr_w1         (dc_tag_odd_addr_w1),
  .dc_tag_odd_din_w1          (dc_tag_odd_din_w1),
  .dc_tag_odd_ds_w1           (mem_ds),
  .dc_tag_odd_sd_w1           (mem_sd),
  .dc_tag_odd_dout_w1         (dc_tag_odd_dout_w1),
  .clk_data_even_lo           (clk_data_even_lo),
  .dc_data_even_cs_lo         (dc_data_even_cs_lo),
  .dc_data_even_we_lo         (dc_data_even_we_lo),
  .dc_data_even_wem_lo        (dc_data_even_wem_lo),
  .dc_data_even_addr_lo       (dc_data_even_addr_lo),
  .dc_data_even_din_lo        (dc_data_even_din_lo),
  .dc_data_even_ds_lo         (mem_ds),
  .dc_data_even_sd_lo         (mem_sd),
  .dc_data_even_dout_lo       (dc_data_even_dout_lo),
  .clk_data_even_hi           (clk_data_even_hi),
  .dc_data_even_cs_hi         (dc_data_even_cs_hi),
  .dc_data_even_we_hi         (dc_data_even_we_hi),
  .dc_data_even_wem_hi        (dc_data_even_wem_hi),
  .dc_data_even_addr_hi       (dc_data_even_addr_hi),
  .dc_data_even_din_hi        (dc_data_even_din_hi),
  .dc_data_even_ds_hi         (mem_ds),
  .dc_data_even_sd_hi         (mem_sd),
  .dc_data_even_dout_hi       (dc_data_even_dout_hi),
  .clk_data_odd_lo            (clk_data_odd_lo),
  .dc_data_odd_cs_lo          (dc_data_odd_cs_lo),
  .dc_data_odd_we_lo          (dc_data_odd_we_lo),
  .dc_data_odd_wem_lo         (dc_data_odd_wem_lo),
  .dc_data_odd_addr_lo        (dc_data_odd_addr_lo),
  .dc_data_odd_din_lo         (dc_data_odd_din_lo),
  .dc_data_odd_ds_lo          (mem_ds),
  .dc_data_odd_sd_lo          (mem_sd),
  .dc_data_odd_dout_lo        (dc_data_odd_dout_lo),
  .clk_data_odd_hi            (clk_data_odd_hi),
  .dc_data_odd_cs_hi          (dc_data_odd_cs_hi),
  .dc_data_odd_we_hi          (dc_data_odd_we_hi),
  .dc_data_odd_wem_hi         (dc_data_odd_wem_hi),
  .dc_data_odd_addr_hi        (dc_data_odd_addr_hi),
  .dc_data_odd_din_hi         (dc_data_odd_din_hi),
  .dc_data_odd_ds_hi          (mem_ds),
  .dc_data_odd_sd_hi          (mem_sd),
  .dc_data_odd_dout_hi        (dc_data_odd_dout_hi),
  // NTLB PD0 (tag) ram interface
  .ntlb_pd0_clk               (ntlb_pd0_clk),
  .ntlb_pd0_ce                (ntlb_pd0_ce),
  .ntlb_pd0_we                (ntlb_pd0_we),
  .ntlb_pd0_wem               (ntlb_pd0_wem),
  .ntlb_pd0_addr              (ntlb_pd0_addr),
  .ntlb_pd0_wdata             (ntlb_pd0_wdata),
  .ntlb_pd0_rdata             (ntlb_pd0_rdata),
  .ntlb_pd0_ds                (mem_ds),
  .ntlb_pd0_sd                (mem_sd),
  .ntlb_pd1_ds                (mem_ds),
  .ntlb_pd1_sd                (mem_sd),
  // NTLB PD1 (data) ram interface
  .ntlb_pd1_clk               (ntlb_pd1_clk),
  .ntlb_pd1_ce                (ntlb_pd1_ce),
  .ntlb_pd1_we                (ntlb_pd1_we),
  .ntlb_pd1_addr              (ntlb_pd1_addr),
  .ntlb_pd1_wdata             (ntlb_pd1_wdata),
  .ntlb_pd1_rdata             (ntlb_pd1_rdata),
  // DCCM
  .clk_dccm_bank0_lo          (clk_dccm_bank0_lo),
  .clk_dccm_bank0_hi          (clk_dccm_bank0_hi),
  .dccm_bank0_cs_lo           (dccm_bank0_cs_lo),
  .dccm_bank0_cs_hi           (dccm_bank0_cs_hi),
  .dccm_bank0_addr_lo         (dccm_bank0_addr_lo),
  .dccm_bank0_addr_hi         (dccm_bank0_addr_hi),
  .dccm_bank0_we_lo           (dccm_bank0_we_lo),
  .dccm_bank0_we_hi           (dccm_bank0_we_hi),
  .dccm_bank0_din             (dccm_bank0_din),
  .dccm_bank0_wem             (dccm_bank0_wem),
  .dccm_bank0_ds              (mem_ds),
  .dccm_bank0_sd              (mem_sd),
  .dccm_bank0_dout            (dccm_bank0_dout),
  .clk_dccm_bank1_lo          (clk_dccm_bank1_lo),
  .clk_dccm_bank1_hi          (clk_dccm_bank1_hi),
  .dccm_bank1_cs_lo           (dccm_bank1_cs_lo),
  .dccm_bank1_cs_hi           (dccm_bank1_cs_hi),
  .dccm_bank1_addr_lo         (dccm_bank1_addr_lo),
  .dccm_bank1_addr_hi         (dccm_bank1_addr_hi),
  .dccm_bank1_we_lo           (dccm_bank1_we_lo),
  .dccm_bank1_we_hi           (dccm_bank1_we_hi),
  .dccm_bank1_din             (dccm_bank1_din),
  .dccm_bank1_wem             (dccm_bank1_wem),
  .dccm_bank1_ds              (mem_ds),
  .dccm_bank1_sd              (mem_sd),
  .dccm_bank1_dout            (dccm_bank1_dout),
  // I/O ports to BPU RAMS
  .bc_din0                    (bc_din0),
  .bc_addr0                   (bc_addr0),
  .bc_me0                     (bc_me0),
  .bc_we0                     (bc_we0),
  .bc_wem0                    (bc_wem0),
  .bc_ds0                     (mem_ds),
  .bc_sd0                     (mem_sd),
  .bc_dout0                   (bc_dout0),
  .gs_din0                    (gs_din0),
  .gs_addr0                   (gs_addr0),
  .gs_me0                     (gs_me0),
  .gs_we0                     (gs_we0),
  .gs_wem0                    (gs_wem0),
  .gs_ds0                     (mem_ds),
  .gs_sd0                     (mem_sd),
  .gs_dout0                   (gs_dout0),
  .bc_ram0_clk                (bc_ram0_clk),
  .pt_ram0_clk                (pt_ram0_clk),
  .bc_din1                    (bc_din1),
  .bc_addr1                   (bc_addr1),
  .bc_me1                     (bc_me1),
  .bc_we1                     (bc_we1),
  .bc_wem1                    (bc_wem1),
  .bc_ds1                     (mem_ds),
  .bc_sd1                     (mem_sd),
  .bc_dout1                   (bc_dout1),
  .gs_din1                    (gs_din1),
  .gs_addr1                   (gs_addr1),
  .gs_me1                     (gs_me1),
  .gs_we1                     (gs_we1),
  .gs_wem1                    (gs_wem1),
  .gs_ds1                     (mem_ds),
  .gs_sd1                     (mem_sd),
  .gs_dout1                   (gs_dout1),
  .bc_ram1_clk                (bc_ram1_clk),
  .pt_ram1_clk                (pt_ram1_clk),
  .rst                        (rst),
  .clk                        (clk),
  .ls                         (ls),
  .test_mode                  (test_mode)


 );



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// External to Internal signal renaming                                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// status
assign sys_halt_r        = gb_sys_halt_r;
assign sys_tf_halt_r     = gb_sys_tf_halt_r;
assign sys_sleep_r       = gb_sys_sleep_r;
assign sys_sleep_mode_r  = gb_sys_sleep_mode_r;



/////////////////////////////////////////////////////




endmodule // cpu_top
