// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2013 Synopsys, Inc. All rights reserved.
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
//   ####    ####   #####   ######
//  #    #  #    #  #    #  #
//  #       #    #  #    #  #####
//  #       #    #  #####   #
//  #    #  #    #  #   #   #
//   ####    ####   #    #  ######
//
// ===========================================================================
//
// Description:
//  The core module instantiates and connects up the major subsystems within
//  the CPU.
//  This is a purely structural Verilog module, containing no actual logic.
//
// ===========================================================================

`include "npuarc_defines.v"

`define TRACE_BRANCH_COMMIT 0

module npuarc_alb_core (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                             test_mode,     // DfT Test mode
  input                             l1_clock_active,
  input                             clk,           // Processor clock
  input                             rst_a,         // Asynchronous reset
  input  [7:0] arcnum /* verilator public_flat */, // processor id
  input  [7:0]                      clusternum,    // for cluster_id register

  input                             biu_idle,
  input                             clk_ungated,
// Library ARCv2HS-3.5.999999999



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


  ////////// Debug Interface /////////////////////////////////////////////////
  //
  input                            dbg_cmdval,        // |cmdval| from JTAG
  output                           dbg_cmdack,        // BVCI |cmd| acknowledge
  input  [`npuarc_DBG_ADDR_RANGE]         dbg_address,       // |addres|s from JTAG
  input  [`npuarc_DBG_BE_RANGE]           dbg_be,            // |be| from JTAG
  input  [`npuarc_DBG_CMD_RANGE]          dbg_cmd,           // |cmd| from JTAG
  input  [`npuarc_DBG_DATA_RANGE]         dbg_wdata,         // |wdata| from JTAG
  //
  input                            dbg_rspack,        // |rspack| from JTAG
  output                           dbg_rspval,        // BVCI response valid
  output [`npuarc_DBG_DATA_RANGE]         dbg_rdata,         // BVCI response EOP
  output                           dbg_reop,          // BVCI response error
  output                           dbg_rerr,          // BVCI data to Debug host

  output                           db_clock_enable_nxt, // Debug unit needs clk
  input                            ar_clock_enable_r,  //

  ////////// APB debug interface /////////////////////////////////////////////

  input                            dbg_prot_sel,
  input                       pclkdbg_en,
  input                            presetdbgn,
  input [31:2]                     paddrdbg,
  input                            pseldbg,
  input                            penabledbg,
  input                            pwritedbg,
  input [31:0]                     pwdatadbg,

  output                           preadydbg,
  output [31:0]                    prdatadbg,
  output                           pslverrdbg,

  input                            dbgen,
  input                            niden,

  //////////  clock control block //////////////////////////////////////////
  //
  output                           hor_clock_enable_nxt, // Arch. Clock Enable


  output [`npuarc_SYNDROME_MSB:0]          fs_dccm_bank0_syndrome_r,
  output [`npuarc_SYNDROME_MSB:0]          fs_dccm_bank1_syndrome_r,
  output [`npuarc_SYNDROME_MSB:0]          fs_dccm_bank2_syndrome_r,
  output [`npuarc_SYNDROME_MSB:0]          fs_dccm_bank3_syndrome_r,

  output                            fs_dccm_bank0_ecc_sb_error_r,
  output                            fs_dccm_bank1_ecc_sb_error_r,
  output                            fs_dccm_bank2_ecc_sb_error_r,
  output                            fs_dccm_bank3_ecc_sb_error_r,

  output                            fs_dccm_bank0_ecc_db_error_r,
  output                            fs_dccm_bank1_ecc_db_error_r,
  output                            fs_dccm_bank2_ecc_db_error_r,
  output                            fs_dccm_bank3_ecc_db_error_r,

  ////////// Interface with DCCM SRAMS////////////////////////////////////////
  //

  output                            clk_dccm_bank0_lo,
  output                            clk_dccm_bank0_hi,
  output                            dccm_bank0_cs_lo,
  output                            dccm_bank0_cs_hi,
  output [`npuarc_DCCM_ADDR_RANGE]         dccm_bank0_addr_lo,
  output [`npuarc_DCCM_ADDR_RANGE]         dccm_bank0_addr_hi,
  output                            dccm_bank0_we_lo,
  output                            dccm_bank0_we_hi,
  output [`npuarc_DBL_DCCM_BE_RANGE]       dccm_bank0_wem,
  output [`npuarc_DBL_DCCM_RANGE]          dccm_bank0_din,
  input  [`npuarc_DBL_DCCM_RANGE]          dccm_bank0_dout,

  output                            clk_dccm_bank1_lo,
  output                            clk_dccm_bank1_hi,
  output                            dccm_bank1_cs_lo,
  output                            dccm_bank1_cs_hi,
  output [`npuarc_DCCM_ADDR_RANGE]         dccm_bank1_addr_lo,
  output [`npuarc_DCCM_ADDR_RANGE]         dccm_bank1_addr_hi,
  output                            dccm_bank1_we_lo,
  output                            dccm_bank1_we_hi,
  output [`npuarc_DBL_DCCM_BE_RANGE]       dccm_bank1_wem,
  output [`npuarc_DBL_DCCM_RANGE]          dccm_bank1_din,
  input  [`npuarc_DBL_DCCM_RANGE]          dccm_bank1_dout,

  /////// DCCM DMI IBP interface /////////////////////////////////////////////
  //
  // leda NTL_CON37 off
  // LMD: non driving port range
  // LJ:  Not all bits of bus used
  input                             dccm_dmi_cmd_valid,
  output                            dccm_dmi_cmd_accept,
  input                             dccm_dmi_cmd_read,
  input [`npuarc_CCM_AW-1:3]               dccm_dmi_cmd_addr,

  output                            dccm_dmi_rd_valid,
  output                            dccm_dmi_err_rd,
  input                             dccm_dmi_rd_accept,
  output [`npuarc_DOUBLE_RANGE]            dccm_dmi_rd_data,

  input                             dccm_dmi_wr_valid,
  output                            dccm_dmi_wr_accept,
  input  [`npuarc_DOUBLE_RANGE]            dccm_dmi_wr_data,
  input  [`npuarc_DOUBLE_BE_RANGE]         dccm_dmi_wr_mask,
  output                            dccm_dmi_wr_done,
  output                            dccm_dmi_err_wr,
   // leda NTL_CON37 on

  ////////// Interface with I-Cache SRAMS ///////////////////////////////////
  //
  output                            ic_tag_way0_clk,
  input   [`npuarc_IC_TRAM_RANGE]          ic_tag_dout0,
  output  [`npuarc_IC_TRAM_RANGE]          ic_tag_din0,
  output  [`npuarc_IC_IDX_RANGE]           ic_tag_addr0,
  output  [`npuarc_IC_TRAM_MASK_RANGE]     ic_tag_wem0,    
  output                            ic_tag_cen0,
  output                            ic_tag_wen0,
  output                            ic_tag_way1_clk,
  input   [`npuarc_IC_TRAM_RANGE]          ic_tag_dout1,
  output  [`npuarc_IC_TRAM_RANGE]          ic_tag_din1,
  output  [`npuarc_IC_IDX_RANGE]           ic_tag_addr1,
  output  [`npuarc_IC_TRAM_MASK_RANGE]     ic_tag_wem1,    
  output                            ic_tag_cen1,
  output                            ic_tag_wen1,
  output                            ic_tag_way2_clk,
  input   [`npuarc_IC_TRAM_RANGE]          ic_tag_dout2,
  output  [`npuarc_IC_TRAM_RANGE]          ic_tag_din2,
  output  [`npuarc_IC_IDX_RANGE]           ic_tag_addr2,
  output  [`npuarc_IC_TRAM_MASK_RANGE]     ic_tag_wem2,    
  output                            ic_tag_cen2,
  output                            ic_tag_wen2,
  output                            ic_tag_way3_clk,
  input   [`npuarc_IC_TRAM_RANGE]          ic_tag_dout3,
  output  [`npuarc_IC_TRAM_RANGE]          ic_tag_din3,
  output  [`npuarc_IC_IDX_RANGE]           ic_tag_addr3,
  output  [`npuarc_IC_TRAM_MASK_RANGE]     ic_tag_wem3,    
  output                            ic_tag_cen3,
  output                            ic_tag_wen3,

  output                            ic_data_bank0_clk,
  input   [`npuarc_IC_BANK_WIDTH-1:0]      ic_data_dout0,
  output  [`npuarc_IC_ADR_RANGE]           ic_data_addr0,
  output  [`npuarc_IC_BANK_WIDTH-1:0]      ic_data_din0,
  output                            ic_data_cen0,
  output                            ic_data_wen0,
  output  [`npuarc_IC_BANK_BYTE_SIZE-1:0]  ic_data_wem0,
  output                            ic_data_bank1_clk,
  input   [`npuarc_IC_BANK_WIDTH-1:0]      ic_data_dout1,
  output  [`npuarc_IC_ADR_RANGE]           ic_data_addr1,
  output  [`npuarc_IC_BANK_WIDTH-1:0]      ic_data_din1,
  output                            ic_data_cen1,
  output                            ic_data_wen1,
  output  [`npuarc_IC_BANK_BYTE_SIZE-1:0]  ic_data_wem1,
  ////////// Interface with Branch Cache SRAMS ////////////////////////////////
  //
  output [`npuarc_BR_BC_DATA_RANGE]        bc_din0,
  output [`npuarc_BR_BC_IDX_RANGE]         bc_addr0,
  output                            bc_me0,
  output                            bc_we0,
  output [`npuarc_BR_BC_DATA_RANGE]        bc_wem0,
  input  [`npuarc_BR_BC_DATA_RANGE]        bc_dout0,

  ////////// Interface with predicion table SRAMS /////////////////////////////
  //
  output [`npuarc_BR_PT_DATA_RANGE]        gs_din0,
  output [`npuarc_BR_PT_RANGE]             gs_addr0,
  output                            gs_me0,
  output                            gs_we0,
  output [`npuarc_BR_PT_DATA_RANGE]        gs_wem0,
  input  [`npuarc_BR_PT_DATA_RANGE]        gs_dout0,
  output                            bc_ram0_clk,
  output                            pt_ram0_clk,
  output                            bc_ram0_clk_en,
  output                            pt_ram0_clk_en,

  output [`npuarc_BR_BC_DATA_RANGE]        bc_din1,
  output [`npuarc_BR_BC_IDX_RANGE]         bc_addr1,
  output                            bc_me1,
  output                            bc_we1,
  output [`npuarc_BR_BC_DATA_RANGE]        bc_wem1,
  input  [`npuarc_BR_BC_DATA_RANGE]        bc_dout1,

  output [`npuarc_BR_PT_DATA_RANGE]        gs_din1,
  output [`npuarc_BR_PT_RANGE]             gs_addr1,
  output                            gs_me1,
  output                            gs_we1,
  output [`npuarc_BR_PT_DATA_RANGE]        gs_wem1,
  input  [`npuarc_BR_PT_DATA_RANGE]        gs_dout1,
  output                            bc_ram1_clk,
  output                            pt_ram1_clk,
  output                            bc_ram1_clk_en,
  output                            pt_ram1_clk_en,


  output [`npuarc_DC_TAG_SYNDROME_MSB:0]      fs_dc_tag_bank0_syndrome_r,
  output [`npuarc_DC_TAG_SYNDROME_MSB:0]      fs_dc_tag_bank1_syndrome_r,
  output [`npuarc_DC_TAG_SYNDROME_MSB:0]      fs_dc_tag_bank2_syndrome_r,
  output [`npuarc_DC_TAG_SYNDROME_MSB:0]      fs_dc_tag_bank3_syndrome_r,

  output                        fs_dc_tag_bank0_ecc_sb_error_r,
  output                        fs_dc_tag_bank1_ecc_sb_error_r,
  output                        fs_dc_tag_bank2_ecc_sb_error_r,
  output                        fs_dc_tag_bank3_ecc_sb_error_r,

  output                        fs_dc_tag_bank0_ecc_db_error_r,
  output                        fs_dc_tag_bank1_ecc_db_error_r,
  output                        fs_dc_tag_bank2_ecc_db_error_r,
  output                        fs_dc_tag_bank3_ecc_db_error_r,


  output [`npuarc_SYNDROME_MSB:0]      fs_dc_data_bank0_syndrome_r,
  output [`npuarc_SYNDROME_MSB:0]      fs_dc_data_bank1_syndrome_r,
  output [`npuarc_SYNDROME_MSB:0]      fs_dc_data_bank2_syndrome_r,
  output [`npuarc_SYNDROME_MSB:0]      fs_dc_data_bank3_syndrome_r,

  output                        fs_dc_data_bank0_ecc_sb_error_r,
  output                        fs_dc_data_bank1_ecc_sb_error_r,
  output                        fs_dc_data_bank2_ecc_sb_error_r,
  output                        fs_dc_data_bank3_ecc_sb_error_r,

  output                        fs_dc_data_bank0_ecc_db_error_r,
  output                        fs_dc_data_bank1_ecc_db_error_r,
  output                        fs_dc_data_bank2_ecc_db_error_r,
  output                        fs_dc_data_bank3_ecc_db_error_r,

  ////////// Interface with DTAG SRAMS////////////////////////////////////////
  //
  output                        clk_tag_even_w0,
  output                        dc_tag_even_cs_w0,
  output                        dc_tag_even_we_w0,
  output [`npuarc_DC_TRAM_RANGE]       dc_tag_even_wem_w0,
  output [`npuarc_DC_IDX_RANGE]        dc_tag_even_addr_w0,
  output [`npuarc_DC_TRAM_RANGE]       dc_tag_even_din_w0,
  input  [`npuarc_DC_TRAM_RANGE]       dc_tag_even_dout_w0,

  output                        clk_tag_odd_w0,
  output                        dc_tag_odd_cs_w0,
  output                        dc_tag_odd_we_w0,
  output [`npuarc_DC_TRAM_RANGE]       dc_tag_odd_wem_w0,
  output [`npuarc_DC_IDX_RANGE]        dc_tag_odd_addr_w0,
  output [`npuarc_DC_TRAM_RANGE]       dc_tag_odd_din_w0,
  input  [`npuarc_DC_TRAM_RANGE]       dc_tag_odd_dout_w0,

  output                        clk_tag_even_w1,
  output                        dc_tag_even_cs_w1,
  output                        dc_tag_even_we_w1,
  output [`npuarc_DC_TRAM_RANGE]       dc_tag_even_wem_w1,
  output [`npuarc_DC_IDX_RANGE]        dc_tag_even_addr_w1,
  output [`npuarc_DC_TRAM_RANGE]       dc_tag_even_din_w1,
  input  [`npuarc_DC_TRAM_RANGE]       dc_tag_even_dout_w1,

  output                        clk_tag_odd_w1,
  output                        dc_tag_odd_cs_w1,
  output                        dc_tag_odd_we_w1,
  output [`npuarc_DC_TRAM_RANGE]       dc_tag_odd_wem_w1,
  output [`npuarc_DC_IDX_RANGE]        dc_tag_odd_addr_w1,
  output [`npuarc_DC_TRAM_RANGE]       dc_tag_odd_din_w1,
  input  [`npuarc_DC_TRAM_RANGE]       dc_tag_odd_dout_w1,

  ////////// Interface with DDATA SRAMS////////////////////////////////////////
  //
  output                        clk_data_even_lo,
  output                        dc_data_even_cs_lo,
  output                        dc_data_even_we_lo,
  output  [`npuarc_DC_DBL_BE_RANGE]    dc_data_even_wem_lo,
  output  [`npuarc_DC_ADR_RANGE]       dc_data_even_addr_lo,
  output  [`npuarc_DC_DRAM_RANGE]      dc_data_even_din_lo,
  input [`npuarc_DC_DRAM_RANGE]        dc_data_even_dout_lo,

  output                        clk_data_even_hi,
  output                        dc_data_even_cs_hi,
  output                        dc_data_even_we_hi,
  output  [`npuarc_DC_DBL_BE_RANGE]    dc_data_even_wem_hi,
  output  [`npuarc_DC_ADR_RANGE]       dc_data_even_addr_hi,
  output  [`npuarc_DC_DRAM_RANGE]      dc_data_even_din_hi,
  input [`npuarc_DC_DRAM_RANGE]        dc_data_even_dout_hi,

  output                        clk_data_odd_lo,
  output                        dc_data_odd_cs_lo,
  output                        dc_data_odd_we_lo,
  output  [`npuarc_DC_DBL_BE_RANGE]    dc_data_odd_wem_lo,
  output  [`npuarc_DC_ADR_RANGE]       dc_data_odd_addr_lo,
  output  [`npuarc_DC_DRAM_RANGE]      dc_data_odd_din_lo,
  input [`npuarc_DC_DRAM_RANGE]        dc_data_odd_dout_lo,

  output                        clk_data_odd_hi,
  output                        dc_data_odd_cs_hi,
  output                        dc_data_odd_we_hi,
  output  [`npuarc_DC_DBL_BE_RANGE]    dc_data_odd_wem_hi,
  output  [`npuarc_DC_ADR_RANGE]       dc_data_odd_addr_hi,
  output  [`npuarc_DC_DRAM_RANGE]      dc_data_odd_din_hi,
  input [`npuarc_DC_DRAM_RANGE]        dc_data_odd_dout_hi,


///////////////////////////////////////////////
//  End of connections for vector unit
///////////////////////////////////////////////

  ////////////////////
  // RTT Interface
  output                           rtt_ca_pref,
  output                           rtt_wa_spl_ld,      //
  output                           rtt_wa_store,       // WA Store for Trace
  output                           rtt_dmp_retire,     // DMP retire for Trace
  output                           rtt_dmp_null_ret,   // DMP null retire rpt for Trace


  ////////// Interface to the Debug module for host control of system reset //
  //
  output                            debug_reset,    // Reset from debug host

  ////////// Debug unit to the clock control /////////////////////////////////
  //

  output                            db_active,      // Debug op in progress

  output [`npuarc_DATA_RANGE]              wa_sr_data_r,   // aux write data


  ////////// Interrupt signals ///////////////////////////////////////////////
  //

  input [`npuarc_IRQM_RANGE]               timer0_irq_1h,


  input [`npuarc_IRQM_RANGE]               wdt_int_timeout_1h_r,

  input [`npuarc_IRQE_RANGE]               irq_r,          // synchronous output

  input [21:0]                      intvbase_in, // for external interrupt vector base configuring
  input                             irq_clk_en_r,

  output                            irq_preempts_nxt,

  //input                           clk_resync,
 // output                          irq_sync_req_a,



  ////////// Auxiliary interface for (Timer) SR/LR instructions ////////////
  //

  output                      aux_tm0_ren_r,
  output      [1:0]           aux_tm0_raddr_r,
  output                      aux_tm0_wen_r,
  output      [1:0]           aux_tm0_waddr_r,
  input       [`npuarc_DATA_RANGE]   tm0_aux_rdata,
  input                       tm0_aux_illegal,
  input                       tm0_aux_k_rd,
  input                       tm0_aux_k_wr,
  input                       tm0_aux_unimpl,
  input                       tm0_aux_serial_sr,
  output                      aux_timer_active,    //  timer SR is active   
  output                      aux_read,
  output                      aux_write,
  output                      aux_wdt_ren_r,
  output      [3:0]           aux_wdt_raddr_r,
  output                      aux_wdt_wen_r,
  output      [3:0]           aux_wdt_waddr_r,

  input       [`npuarc_DATA_RANGE]   wdt_aux_rdata,
  input                       wdt_aux_illegal,
  input                       wdt_aux_k_rd,
  input                       wdt_aux_k_wr,
  input                       wdt_aux_unimpl,
  input                       wdt_aux_serial_sr,
  input                       wdt_aux_strict_sr,
  input                       wdt_x3_stall,
  output                      x3_kill,
  output                      aux_rtc_ren_r,
  output      [2:0]           aux_rtc_raddr_r,
  output                      aux_rtc_wen_r,
  output      [2:0]           aux_rtc_waddr_r,

  input       [`npuarc_DATA_RANGE]   rtc_aux_rdata,
  input                       rtc_aux_illegal,
  input                       rtc_aux_k_rd,
  input                       rtc_aux_k_wr,
  input                       rtc_aux_unimpl,
  input                       rtc_aux_serial_sr,
  input                       rtc_aux_strict_sr,

  output                      rtc_na,

  ////////// Auxiliary interface for common aux register accesses ////////////
  //
  output                      aux_rs_valid,         //  CCAUX valid rd request
  output [`npuarc_CCAUX_RGN_RANGE]   aux_rs_region,        //  CCAUX region identity
  output [`npuarc_CCAUX_ADDR_RANGE]  aux_rs_addr,          //  CCAUX region offset
  output                      aux_rs_read,          //  CCAUX read enable
  output                      aux_rs_write,         //  CCAUX write enable
  input  [`npuarc_DATA_RANGE]        aux_rs_data,          //  CCAUX LR data
  input  [`npuarc_CCAUX_STAT_RANGE]  aux_rs_status,        //  CCAUX credintials
  input                       aux_rs_accept,        //  CCAUX response read

  output                      aux_wr_valid,         //  CCAux wr valid
  output [`npuarc_CCAUX_RGN_RANGE]   aux_wr_region,        //  CCAux wr region
  output [`npuarc_CCAUX_ADDR_RANGE]  aux_wr_addr,          //  CCAux wr Address
  output [`npuarc_DATA_RANGE]        aux_wr_data,          //  CCAux wr data
  input                       aux_wr_allow,         //  CCAux new write allowed
  output                      aux_cm_phase,         //  CCAux in commit phase
  output                      aux_cm_valid,         //  CCAux commit is valid


  input                       ar_save_clk,
  output                      ar_save_en_r,

 
  output [`npuarc_MMU_PD0_SYNDROME_MSB:0]    fs_itlb_bank0_syndrome_r,
  output [`npuarc_MMU_PD0_SYNDROME_MSB:0]    fs_itlb_bank1_syndrome_r,
  output [`npuarc_MMU_PD0_SYNDROME_MSB:0]    fs_itlb_bank2_syndrome_r,
  output [`npuarc_MMU_PD0_SYNDROME_MSB:0]    fs_itlb_bank3_syndrome_r,
  output [`npuarc_MMU_PD1_SYNDROME_MSB:0]    fs_itlb_bank4_syndrome_r,

  output                      fs_itlb_bank0_ecc_sb_error_r,
  output                      fs_itlb_bank1_ecc_sb_error_r,
  output                      fs_itlb_bank2_ecc_sb_error_r,
  output                      fs_itlb_bank3_ecc_sb_error_r,
  output                      fs_itlb_bank4_ecc_sb_error_r,
 
  output                      fs_itlb_bank0_ecc_db_error_r,
  output                      fs_itlb_bank1_ecc_db_error_r,
  output                      fs_itlb_bank2_ecc_db_error_r,
  output                      fs_itlb_bank3_ecc_db_error_r,
  output                      fs_itlb_bank4_ecc_db_error_r,

  output [`npuarc_MMU_PD0_SYNDROME_MSB:0]    fs_dtlb_bank0_syndrome_r,
  output [`npuarc_MMU_PD0_SYNDROME_MSB:0]    fs_dtlb_bank1_syndrome_r,
  output [`npuarc_MMU_PD0_SYNDROME_MSB:0]    fs_dtlb_bank2_syndrome_r,
  output [`npuarc_MMU_PD0_SYNDROME_MSB:0]    fs_dtlb_bank3_syndrome_r,
  output [`npuarc_MMU_PD1_SYNDROME_MSB:0]    fs_dtlb_bank4_syndrome_r,

  output                      fs_dtlb_bank0_ecc_sb_error_r,
  output                      fs_dtlb_bank1_ecc_sb_error_r,
  output                      fs_dtlb_bank2_ecc_sb_error_r,
  output                      fs_dtlb_bank3_ecc_sb_error_r,
  output                      fs_dtlb_bank4_ecc_sb_error_r,

  output                      fs_dtlb_bank0_ecc_db_error_r,
  output                      fs_dtlb_bank1_ecc_db_error_r,
  output                      fs_dtlb_bank2_ecc_db_error_r,
  output                      fs_dtlb_bank3_ecc_db_error_r,
  output                      fs_dtlb_bank4_ecc_db_error_r,


  ////////// MMU NTLB RAMs //////////////////////////////////////////////////
  //
  // NTLB PD0 (tag) ram interface
  output                           ntlb_pd0_clk,
  output                           ntlb_pd0_ce,
  output                           ntlb_pd0_we,
  output [`npuarc_NTLB_NUM_WAYS_ECC-1:0]  ntlb_pd0_wem,
  output [`npuarc_NTLB_PD0_ADDR_MSB:0]    ntlb_pd0_addr,
  output [`npuarc_NTLB_PD0_DATA_MSB:0]    ntlb_pd0_wdata,
  input  [`npuarc_NTLB_PD0_DATA_MSB:0]    ntlb_pd0_rdata,

  // NTLB PD1 (data) ram interface
  output                           ntlb_pd1_clk,
  output                           ntlb_pd1_ce,
  output                           ntlb_pd1_we,
  output [`npuarc_NTLB_PD1_ADDR_MSB:0]    ntlb_pd1_addr,
  output [`npuarc_NTLB_PD1_DATA_MSB:0]    ntlb_pd1_wdata,
  input  [`npuarc_NTLB_PD1_DATA_MSB:0]    ntlb_pd1_rdata,


  // halt status
  output                      dbg_bh_r,           // break halt
  output                      dbg_sh_r,           // self_halt
  output                      dbg_eh_r,           // external halt
  output                      dbg_ah_r,           // actionpoint halt


//  output                      imem_clk,

  ////////// Unit-level clock gating control outputs to clock_ctrl ///////////
  //
  output                      mpy_unit_enable,      // clk ctrl for multiplier
  input                       mpy_unit_clk,         // clk clk  for multiplier
  output                      div_unit_enable,      // clk ctrl for divider
  input                       div_unit_clk,         // clk clk  for divider
  output                      smt_unit_enable,      // clk ctrl for smart
  input                       smt_unit_clk,         // clk clk  for smart
  output                      dmp_unit_enable,      // clk ctrl for DMP
  output                      dmp_dmu_unit_enable,  // clk ctrl for DMU (dcache backend)
  output                      dmp_lq_unit_enable,   // clk ctrl for LQ
  input                       dmp_unit_clk,         // clk clk  for DMP
  input                       dmp_dmu_unit_clk,     // clk clk  for DMP dmu
  input                       dmp_lq_unit_clk,      // clk clk  for DMP LQ
  output                      ap_unit_enable,
  input                       ap_unit_clk,          // clk for AP
  output                      aux_aps_active,       //
  input                       ap_aux_clk,           // clk for AP Aux
  output                      pct_unit_enable,
  input                       pct_unit_clk,       // clk   for PCT

  output  [`npuarc_PC_RANGE]         ar_pc_r,

  output [`npuarc_MMU_PID_ASID_RANGE]  asid_r,          // Current pid.asid
  output                        asid_wr_en,      // pid update

  input [7:0]                 rtt_src_num,

  ////////// Auxiliary interface for (RTT) SR/LR instructions ////////////
  //
  output                      aux_rtt_active,       // enable RTT interf clk
  output                      aux_rtt_ren_r,        //  (X3) Aux     Enable
  output  [3:0]               aux_rtt_raddr_r,      //  (X3) Aux Address
  output                      aux_rtt_wen_r,        //  (WA) Aux     Enable
  output  [3:0]               aux_rtt_waddr_r,      //  (WA) Aux Address
  input   [`npuarc_DATA_RANGE]       rtt_aux_rdata,        //  (X3) LR read data
  input                       rtt_aux_illegal,      //  (X3) SR/LR illegal
  input                       rtt_aux_k_rd,         //  (X3) need Kernel Read
  input                       rtt_aux_k_wr,         //  (X3) need Kernel Write
  input                       rtt_aux_unimpl,       //  (X3) Invalid
  input                       rtt_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       rtt_aux_strict_sr,    //  (X3) SR flush pipe

  output [`npuarc_INTEVT_RANGE]      int_evts,
  output  [`npuarc_PC_RANGE]         ar_pc_nxt,
  output  [`npuarc_PFLAG_RANGE]      wa_aux_status32_nxt,
  output  [`npuarc_INTEVT_RANGE]     excpn_evts,
  output                      excpn_exit_evt,
  output                      ca_zol_lp_jmp,        // late ZOL loop-back

  output                      commit_normal_evt,
  output                      ca_cond_inst,
  output                      ca_cond_met,

  output                      ca_cmt_dbg_evt,

  output                      ca_br_or_jmp_all,
  output                      ca_indir_br,
  output                      ca_dslot_r,
  output                      ca_in_deslot,
  output                      ca_in_eslot_r,
  output                      rtt_leave_uop_cmt,
  output                      ca_cmt_brk_inst,    // Commit Break inst
  output                      ca_cmt_isi_evt,
  output                      dbg_halt_r,
  output [`npuarc_DATA_RANGE]        ar_aux_ecr_r,

  input                       da_rtt_stall_r,
  output                      dbg_ra_r,           // 'reset applied' bit


  output      [`npuarc_APNUM_RANGE]  aps_active,      // Identity of active hit
  output                      aps_halt,    // Halt due to AP match
  output                      aps_break,   // Break due to AP match
  output      [`npuarc_APS_RANGE]    aps_status,       // All triggered Actionpoints
  output                      aps_excpn,   // Excpn due to AP match

  // AUX register read/write monitoring
  output                      wa_lr_op_r,
  output                      wa_sr_op_r,
  output [`npuarc_AUX_REG_RANGE]     wa_aux_addr_r,

  // Core register write monitoring
  output [`npuarc_RGF_ADDR_RANGE]    wa_rf_wa0_r,
  output                      wa_rf_wenb0_r,
  output [`npuarc_RGF_ADDR_RANGE]    wa_rf_wa1_r,
  output                      wa_rf_wenb1_r,

  output [`npuarc_DATA_RANGE]        wa_rf_wdata0_lo_r,
  output [`npuarc_DATA_RANGE]        wa_rf_wdata1_lo_r,

  output [`npuarc_DATA_RANGE]        wa_rf_wdata0_hi_r,
  output                      wa_rf_wenb0_64_r,
  output [`npuarc_DATA_RANGE]        wa_rf_wdata1_hi_r,
  output                      wa_rf_wenb1_64_r,

  // Load/store monitoring
  output                      ca_pass,              // CA passing on inst
  output                      ca_load_r,            // CA load
  output                      ca_grad_req,          // CA grad buffer req
  output                      ca_store_r,           // CA store
  output [1:0]                ca_size_r,            // 00-b, 01-h, 10-w, 11-dw
  output [`npuarc_ADDR_RANGE]        ca_mem_addr_r,
  output [`npuarc_DMP_DATA_RANGE]    ca_wr_data_r,         // CA write data
  output [`npuarc_ADDR_RANGE]        dmp_retire_va_addr,   // VA Address of retiring LD
//`if ((`RTT_IMPL_MEDIUM == 1) || (`RTT_IMPL_FULL == 1)) //{ 
// spyglass disable_block W241
// SMD: output declared but not driven
// SJ:  unused in some configs
  output [`npuarc_ADDR_RANGE]        dmp_retire_mem_addr,  // PA Address of retirin LD
  output [`npuarc_DMP_DATA_RANGE]    dmp_retire_mem_data,  // DATA of retirin LD
  output [1:0]                dmp_retire_mem_size,  // Size of retireing load
// spyglass enable_block W241
//`endif  //  }


  output                      ap_tkn,



//  output                      pct_interrupt       ,
  ////////// External Event Interface /////////////////////////////////////////
  //
  input                       arc_event_r,          //
  output                      wake_from_wait,       // re-enable clock after wait

  input                       dbg_cache_rst_disable_r,
  input                       dccm_dmi_priority_r,      

  ////////// External Halt Request Interface /////////////////////////////////
  //
  input                       gb_sys_halt_req_r,    // Sync. halt req.
  output                      gb_sys_halt_ack_r,    // Sync. halt ack.
  //
  input                       gb_sys_run_req_r,     // Sync. run req.
  output                      gb_sys_run_ack_r,     // Sync. run ack.

  //////////// IFU IBP interface    /////////////////////////////////////////
  //
// leda NTL_CON37 off
// LMD: Signal/Net must read from the input port
// LJ: Signals are defined as part of the internal bus protocol, readibility

  output  wire                   ifu_ibus_cmd_valid,      // command valid
  input wire                     ifu_ibus_cmd_accept,     // command accept
  output  wire [`npuarc_PADDR_SIZE-1:0] ifu_ibus_cmd_addr,       // command address (LSBs need to be tied to 0)
  output  wire                   ifu_ibus_cmd_wrap,       // if true then critical word first
  output  wire [3:0]             ifu_ibus_cmd_cache,
  output  wire [3:0]             ifu_ibus_cmd_burst_size, // length of burst in number of data elements -1
  output  wire [1:0]             ifu_ibus_cmd_prot,       // if true then kernel mode, else user

  input wire                     ifu_ibus_rd_valid,       // read data valid
  input wire                     ifu_ibus_err_rd,         // read error
  output wire                    ifu_ibus_rd_accept,      // read data accept
  input wire [64-1:0]            ifu_ibus_rd_data,        // read data
  input wire                     ifu_ibus_rd_last,        // read last
// leda NTL_CON37 on




  output                        lqwq_mem_cmd_valid,
  output                        lqwq_mem_cmd_cache,
  output                        lqwq_mem_cmd_burst_size,
  output                        lqwq_mem_cmd_read,
  input                         lqwq_mem_cmd_accept,
  output [`npuarc_PADDR_RANGE]         lqwq_mem_cmd_addr,
  output                        lqwq_mem_cmd_lock,
  output                        lqwq_mem_cmd_excl,
  output [2:0]                  lqwq_mem_cmd_data_size,
  output [1:0]                  lqwq_mem_cmd_prot,

  output                        lqwq_mem_wr_valid,
  output                        lqwq_mem_wr_last,
  input                         lqwq_mem_wr_accept,
  output [`npuarc_DOUBLE_BE_RANGE]     lqwq_mem_wr_mask,
  output [`npuarc_DOUBLE_RANGE]        lqwq_mem_wr_data,

  input                         lqwq_mem_rd_valid,
  input                         lqwq_mem_err_rd,
  input                         lqwq_mem_rd_excl_ok,
  input                         lqwq_mem_rd_last,
  output                        lqwq_mem_rd_accept,
  input  [`npuarc_DOUBLE_RANGE]        lqwq_mem_rd_data,

  input                         lqwq_mem_wr_done,
  input                         lqwq_mem_wr_excl_done,
  input                         lqwq_mem_err_wr,
  output                        lqwq_mem_wr_resp_accept,
  ////////// RF IBP interface ///////////////////////////////////////////
  //
  output                         rf_cmd_valid,
  output [3:0]                   rf_cmd_cache,       
  output                         rf_cmd_excl, 
  output [2:0]                   rf_cmd_data_size, 
  input                          rf_cmd_accept,      
  output                         rf_cmd_read,        
  output  [`npuarc_PADDR_RANGE]         rf_cmd_addr,
  output                         rf_cmd_lock,        
  output  [1:0]                  rf_cmd_prot,        
  output                         rf_cmd_wrap,        
  output  [3:0]                  rf_cmd_burst_size,  

  input                          rf_rd_valid,
  input                          rf_rd_last,
  input                          rf_err_rd,
  input [`npuarc_RF_CB_DATA_RANGE]      rf_rd_data,
  output                         rf_rd_accept,
  ////////// CB IBP interface ///////////////////////////////////////////
  //
  output                         cb_cmd_valid, 
  output [3:0]                   cb_cmd_cache,  
  output                         cb_cmd_excl,  
  output [2:0]                   cb_cmd_data_size,
  input                          cb_cmd_accept,    
  output                         cb_cmd_read,      
  output  [`npuarc_PADDR_RANGE]         cb_cmd_addr,  
  output                         cb_cmd_lock,    
  output  [1:0]                  cb_cmd_prot,      
  output                         cb_cmd_wrap,      
  output  [3:0]                  cb_cmd_burst_size,

  output                         cb_wr_valid,      
  input                          cb_wr_accept,     
  output                         cb_wr_last,       
  output  [`npuarc_RF_CB_DATA_RANGE]    cb_wr_data,       
  output  [`npuarc_RF_CB_MASK_RANGE]    cb_wr_mask,       
  input                          cb_wr_done,       
  input                          cb_err_wr,    
  output                         cb_wr_resp_accept,   


//`if (`HAS_SAFETY == 1) // {
 


//   `if (`HAS_SAFETY == 1) // {
  output                    fs_ic_tag_bank0_ecc_sb_error_r,
  output                    fs_ic_tag_bank0_ecc_db_error_r,
  output [`npuarc_IC_TAG_SYNDROME_MSB:0]  fs_ic_tag_bank0_syndrome_r,
  output                    fs_ic_tag_bank1_ecc_sb_error_r,
  output                    fs_ic_tag_bank1_ecc_db_error_r,
  output [`npuarc_IC_TAG_SYNDROME_MSB:0]  fs_ic_tag_bank1_syndrome_r,
  output                    fs_ic_tag_bank2_ecc_sb_error_r,
  output                    fs_ic_tag_bank2_ecc_db_error_r,
  output [`npuarc_IC_TAG_SYNDROME_MSB:0]  fs_ic_tag_bank2_syndrome_r,
  output                    fs_ic_tag_bank3_ecc_sb_error_r,
  output                    fs_ic_tag_bank3_ecc_db_error_r,
  output [`npuarc_IC_TAG_SYNDROME_MSB:0]  fs_ic_tag_bank3_syndrome_r,
  output                      fs_ic_data_bank00_ecc_sb_error_r,
  output                      fs_ic_data_bank00_ecc_db_error_r,
  output [`npuarc_SYNDROME_MSB:0]    fs_ic_data_bank00_syndrome_r,
  output                      fs_ic_data_bank01_ecc_sb_error_r,
  output                      fs_ic_data_bank01_ecc_db_error_r,
  output [`npuarc_SYNDROME_MSB:0]    fs_ic_data_bank01_syndrome_r,
  output                      fs_ic_data_bank10_ecc_sb_error_r,
  output                      fs_ic_data_bank10_ecc_db_error_r,
  output [`npuarc_SYNDROME_MSB:0]    fs_ic_data_bank10_syndrome_r,
  output                      fs_ic_data_bank11_ecc_sb_error_r,
  output                      fs_ic_data_bank11_ecc_db_error_r,
  output [`npuarc_SYNDROME_MSB:0]    fs_ic_data_bank11_syndrome_r,
//    `endif // }

//`endif               // }   // HAS_SAFETY







  ////////// Machine Halt Interface //////////////////////////////////////////
  //
  output                         ifu_idle_r,           //
  output                         dmp_idle_r,           //
  output                         gb_sys_halt_r,        //
  output                         gb_sys_tf_halt_r,     //
  output                         gb_sys_sleep_r,       //
  output [`npuarc_EXT_SMODE_RANGE]      gb_sys_sleep_mode_r

 );

wire                             dmp_queue_empty;

  wire                           da_uop_busy_r;
 






wire [3:0]                  ecc_dccm_sbe_count_r; // Single bit error count
wire [3:0]                  ecc_dc_tag_sbe_count_r;  // Single bit error count on tag
wire [3:0]                  ecc_dc_data_sbe_count_r; // Single bit error count on data
wire [3:0]                  ecc_mmu_sbe_count_r;     // Single bit error count on mmu
wire [`npuarc_SYNDROME_MSB:0]      itlb_syndrome_r;
wire [`npuarc_SYNDROME_MSB:0]      dtlb_syndrome_r;


wire [3:0]                  ic_data_ecc_sbe_cnt;
wire [3:0]                  ic_tag_ecc_sbe_cnt;


//  ERP AUX interface siganls
wire [7:0]         ecc_sbe_clr; 
wire               ecc_sbe_dmp_clr; 
wire [`npuarc_DATA_RANGE] ecc_sbe_count_r;

wire       mmu_ecc_sbe_clr;
wire       dc_tag_ecc_sbe_clr;
wire       dc_data_ecc_sbe_clr;
wire       ic_tag_ecc_sbe_clr;
wire       ic_data_ecc_sbe_clr;
wire       iccm1_ecc_sbe_clr;
wire       dccm_ecc_sbe_clr;
wire       iccm0_ecc_sbe_clr;

assign {
        mmu_ecc_sbe_clr,
        dc_tag_ecc_sbe_clr,
        dc_data_ecc_sbe_clr,
        ic_tag_ecc_sbe_clr,
        ic_data_ecc_sbe_clr,
        iccm1_ecc_sbe_clr,
        dccm_ecc_sbe_clr,
        iccm0_ecc_sbe_clr
        } = ecc_sbe_clr;
         
assign ecc_sbe_count_r = {
                              ecc_mmu_sbe_count_r,
                              ecc_dc_tag_sbe_count_r,
                              ecc_dc_data_sbe_count_r,
                              ic_tag_ecc_sbe_cnt,
                              ic_data_ecc_sbe_cnt,
                              4'b0000,
                              ecc_dccm_sbe_count_r,
                              4'b0000
                             };



///////////// MPU interface FOR IFU ///////////////////////////////////////////
//
wire [`npuarc_PC_RGN_RANGE]        ifetch_addr_mpu;
wire                        ifetch_viol;

////////// Interface for auxiliary register accesses from EXU ////////////////
//
wire                        al_with_dslot;
wire                        wa_tail_pc_3;


////////// MPU Interface between IFU and EXU /////////////////////////////////
//
//wire                        ifu_fetch_r;          // instr fetch signal to MPU
//wire [`PC_RANGE]            ifu_pc_r;             // instruction fetch address
//
//wire                        mpu_ifu_protv;        // MPU protection violation
//wire [`MPU_ECR_MR_RANGE]    mpu_ifu_mr;           // MPU exception region

////////// Performance monitoring signals from the IFU ///////////////////////
//
wire                       ifu_issue_stall_r   ;

wire                       ifu_icache_miss_r   ;
wire                       ifu_icache_hit_r      ;
wire                       ifu_icache_disabled ;
wire                       ifu_way_pred_miss_r ;
wire                       ifu_brch_mispred_r  ;
wire                       ifu_late_br_mispred ;
wire                       ifu_cond_mispred_r  ;
wire                       ifu_bta_mispred_r   ;
wire                       ifu_missing_pred_r  ;
wire                       ifu_error_branch_r  ;
wire                       ifu_branch_cache_miss;

wire                       ifu_bit_error_r     ;
wire                       ca_lp_lpcc_evt         ;
wire                       ca_br_taken         ;
wire                       ca_has_limm_r       ;
wire                       ca_is_16bit_r       ;

wire                       ca_br_jmp_op        ;
wire                       ca_lr_op_r          ;
wire                       ca_sr_op_r          ;
wire                       ca_jump_r           ;
wire                       ca_bcc_r            ;
wire                       ca_brcc_bbit_r      ;
wire                       ca_zol_branch       ;
wire                       dc4_pref_r          ; 
wire [4:0]                 ca_q_field_r        ;
wire                       ca_byte_size_r      ;
wire                       ca_hit_lp_end       ;
wire [`npuarc_DATA_RANGE]         ar_aux_lp_start_r   ;

wire                       zol_depend_stall    ;




wire                       icm                 ;
wire                       icll                ;
wire                       icoff               ;
wire                       ifu_ivic            ;
wire                       ifu_ivil            ;
wire                       icwpm               ;
wire                       da_eslot_stall      ;
wire                       da_uop_stall        ;
wire                       x1_dslot_stall      ;
wire                       sa_flag_stall       ;

wire                       sa_stall_r15        ;

wire                       sa_stall_r1         ;
wire                       sa_acc_raw          ;
wire                       ca_acc_waw          ;
wire                       dc_pct_dcm          ; // Data Cache miss
wire                       dc_pct_dclm         ; // Data Cache load miss
wire                       dc_pct_dcsm         ; // Data Cache store miss
wire                       dc_pct_dcpm         ; // Data Cache predict miss
wire                       dc_pct_dcbc         ; // Data Cache bank conflicts
wire                       dc_pct_ivdc         ;
wire                       dc_pct_ivdl         ;
wire                       dc_pct_flsh         ;
wire                       dc_pct_fldl         ;
wire                       dccm_pct_dcbc       ; // DCCM bank conflicts
wire [`npuarc_DMP_TARGET_RANGE]   dc4_target_r        ;
wire                       do_aux_replay_r     ;

wire                       bauxflsh            ;


assign                     icm  = ifu_icache_miss_r;
assign                     icll = ifu_icache_hit_r;
assign                     icoff = ifu_icache_disabled;
assign                     icwpm = ifu_way_pred_miss_r;



wire  [`npuarc_IRQM_RANGE]         pct_int_overflow_r;

wire                        ca_sleep_evt;

wire                        ca_trap_op_r;
wire  [`npuarc_DATA_RANGE]         ar_aux_lp_end_r;



////////// Interface between EXU and DMP /////////////////////////////////////
//
// -- Interface to the SA stage
wire                        sa_load_r;            // SA insn is a Load
wire                        sa_store_r;           // SA insn is a Store
wire                        dmp_aux_sr_op;        // CA, WA insn is DMP SR

//
wire [7:0]        aux_memseg_r;
//  -- Interface to the X1 stage
//
wire                        x1_valid_r;           // X1 has valid instruction
wire                        x1_pass;              // X1  passing on ints
wire                        x1_load_r;            // X1 load
wire                        x1_store_r;           // X1 store
wire                        x1_pref_r;            // X1 pref ucode bit
wire                        x1_cache_byp_r;       // X1 .di instruction
wire [1:0]                  x1_size_r;            // 00-b; 01-h; 10-w; 11-dw
wire [`npuarc_ADDR_RANGE]          x1_mem_addr0;         // X1 mem addr0
wire [`npuarc_ADDR_RANGE]          x1_mem_addr1;         // X1 mem addr1
wire [`npuarc_ADDR_RANGE]          x1_addr_base;         // X1 addr base
wire [`npuarc_ADDR_RANGE]          x1_addr_offset;       // X1 addr offset
wire [1:0]                  x1_bank_sel_lo;       // X1 bank sel0
wire [1:0]                  x1_bank_sel_hi;       // X1 bank sel0

wire                        x1_uop_inst_r;        // X1 insn. is multi-op
wire                        dc1_stall;            // X1 stall from DMP
//
// -- Interface to the X2 stage
//
wire                        x2_valid_r;           // X2 has valid instruction
wire                        x2_pass;              // X2 passing on instt
wire                        x2_enable;            // X2 accepts new instruction
wire                        x2_load_r;            // X2 load
wire                        x2_store_r;           // X2 store
wire                        x2_locked_r;          // X2 LLOCK/SCOND
wire                        x2_pref_r;            // X2 prefetch
wire [1:0]                  x2_size_r;            // X2 size
wire                        x2_cache_byp_r;       // X2 .di instruction
wire                        x2_mpu_data_flt;      // 
wire                        dc2_stall;            // X2 stall from DMP
//
// -- Interface to the X3 stage
//
wire                        x3_valid_r;           // X3 has valid instruction
wire                        x3_pass;              // X3 passing on instt
wire                        x3_enable;            // X3 accepts new instruction
wire                        x3_load_r;            // X3 load
//wire                        x3_pre_alloc_r;       // X3 pre-alloc
wire                        x3_store_r;           // X3 store
wire                        x3_locked_r;          // X3 LLOCK/SCOND
wire                        x3_pref;              // PREFETCH into L1
wire                        x3_pref_l2;           // PREFETCH into L2
wire                        x3_prefw;             // PREFETCHW
wire                        x3_pre_alloc;         // PREALLOC
wire [1:0]                  x3_size_r;            // 00-b; 01-h; 10-w; 11-dw
wire                        x3_sex_r;             // X3 load sign extension

// -- Interface to the CA stage
//
wire                        ca_valid_r;           // CA has valid instruction
//wire                        ca_pref_r;            // CA pref
wire                        ca_enable;            // CA accepts new instruction
wire                        ca_sex_r;             // CA load sign extension
wire                        ca_cache_byp_r;       // CA cache byp
wire                        ca_pref;              // PREFETCH into L1
wire                        ca_pref_l2;           // PREFETCH into L2
wire                        ca_prefw;             // PREFETCHW
wire                        ca_pre_alloc;         // PREALLOC
wire [`npuarc_PADDR_RANGE]         ca_phys_addr_r;       // CA physical memory address
wire                        dc4_stall_r;          // DC4 structural hazard
wire                        dc4_waw_replay_r;     // DC4 WAW stall not allowed
//
// -- Interface to the WA stage
//
wire                        wa_restart_r;         // WB pipeline flush
wire                        wa_restart_kill_r;    // WB flush kills CA
wire                        wa_hlt_restart_r;
wire                        mem_excpn_ack_r;      // bus error excpn ack
// pct_event for sync/dsync/dmb stall
wire                        sync_dsync_dmb_stall;
assign bauxflsh = do_aux_replay_r & wa_restart_r;

//
// -- Interface for returning load data and status
//
wire [`npuarc_DMP_DATA_RANGE]      dmp_rf_wdata;         // aligned and sign extended
//
// -- Interface for returning SCOND success/failure
//
wire                        dmp_scond_zflag;     // indicate SCOND sucs/fail
wire                        dmp_clear_lf;        // External write to LPA
wire                        rtt_dc4_scond_go;  // scond will be success
//
// -- Exception and replay interface
//
wire                        dc3_excpn;           // DMP precise memory err exc
wire [`npuarc_DMP_EXCPN_RANGE]     dc3_excpn_type;      // exception type
wire [7:0]                  dc3_excpn_code;      // cause code

wire                        dc4_replay;           // replay instruction in DC4
wire                        dc4_excpn;            // DMP excpn
wire                        dc4_excpn_user_mode_r;// DMP excpn privilege
wire [`npuarc_PADDR_RANGE]         dc4_excpn_mem_addr;   // Address of the faulting
//                                                   inst; may be imprecise
wire [`npuarc_DMP_EXCPN_RANGE]     dc4_excpn_type;       // exception type
//wire [7:0]                  dc4_excpn_code;       // exception cause code
//
// -- Graduation Interface
//
wire                        dc4_grad_req;         // req to grad, no retirement
wire                        ca_grad_ack;          // grad ack
wire [`npuarc_GRAD_TAG_RANGE]      ca_grad_tag;          // tag of graduating context
//
// -- Post Commit Retirement Interface
//
wire                        dmp_retire_req;       // retirement request
wire                        dmp_retire_ack;       // retirement acknowledge
wire [`npuarc_GRAD_TAG_RANGE]      dmp_retire_tag;       // tag of retiring context
wire                        wa_lock_flag_r;       // LF reg from EXU to DMP
wire                        wa_lock_double_r;     // LF size to DMP
wire [`npuarc_PADDR_RANGE]         wa_lpa_r;             // LPA reg from EXU to DMP
wire                        ca_locked_r;          // Indicates LLOCK or SCOND

//
// -- Post Commit status
//
wire                       dmp_wr_pending_r;      // post-commit store
wire                       dmp_aux_pending_r;     // post-commit cache instr
wire                       dmp_idle1_r;

// IFU ECC fault signals
wire                       ecc_ifu_disable;
wire                       ecc_ifu_expn_disable;
wire                       ecc_dmp_disable;
wire                       ecc_dmp_expn_disable;
wire                       ecc_mmu_disable;
wire                       ecc_mmu_expn_disable;
wire                       ic_tag_ecc_err;
wire                       al_icache_ecc_err;

wire                       dc4_dc_dt_ecc_db_error;
wire                       dc4_dc_dd_ecc_db_error;

wire [`npuarc_SYNDROME_MSB:0]     dc_tag_syndrome_r;
wire [`npuarc_SYNDROME_MSB:0]     dc_data_syndrome_r;

wire                       dc4_dccm_ecc_db_error;

wire [`npuarc_SYNDROME_MSB:0]     dccm_syndrome_r; 
wire                       x3_store_may_grad;
wire  [1:0]                ca_store_grad_swap;
wire  [1:0]                ca_store_grad;
//`if ((`DUAL_ISSUE == 1) || (`HAS_DSP == 1))  // {
wire  [`npuarc_GRAD_TAG_RANGE]    ca_store_grad_tag_lo;
wire  [`npuarc_GRAD_TAG_RANGE]    ca_store_grad_tag_hi;
wire                       wa_retire1_valid;
wire  [`npuarc_GRAD_TAG_RANGE]    wa_retire1_tag;
//  `if (`DUAL_ISSUE == 1) // {
wire                       wa_retire0_valid;
wire  [`npuarc_GRAD_TAG_RANGE]    wa_retire0_tag;
//  `endif               // }
//`endif               // }


wire                       ca_store_grad_r;
wire [`npuarc_DMP_GRAD_TAG_RANGE] ca_store_grad_tag;

wire                       dmp_st_retire0;
wire [`npuarc_DMP_GRAD_TAG_RANGE] dmp_st_retire0_tag;
wire [`npuarc_DMP_DATA_RANGE]     dmp_st_retire0_data;

wire                       dmp_st_retire1;
wire [`npuarc_DMP_GRAD_TAG_RANGE] dmp_st_retire1_tag;
wire [`npuarc_DMP_DATA_RANGE]     dmp_st_retire1_data;









////////// Interface between IFU and EXU ///////////////////////////////////
//
// -- Fetch-Restart Interface
//
wire                        fch_restart;
wire                        fch_stop_r;
wire [`npuarc_PC_RANGE]            fch_target;
wire                        fch_restart_vec;
wire [`npuarc_IM_LINE_BITS:3]      fch_target_successor;
wire                        fch_iprot_replay;
//
// -- Instruction Issue Interface
//


wire                        al_pass;

wire [`npuarc_DATA_RANGE]          al_inst;
wire [`npuarc_DATA_RANGE]          al_limm;


wire                        al_exception;
wire [`npuarc_FCH_EXCPN_RANGE]     al_excpn_type;
wire [`npuarc_FCH_EINFO_RANGE]     al_excpn_info;
wire                        al_ifu_err_nxtpg;
wire                        al_iprot_viol;

wire                        al_is_predicted;
wire                        al_prediction;
wire [`npuarc_PC_RANGE]            al_predicted_bta;
wire [`npuarc_BR_TYPE_RANGE]       al_prediction_type;
wire                        al_error_branch;
wire [`npuarc_BR_INFO_RANGE]       al_branch_info;


//
//
// -- Misprediction Interface
//
wire                        mpd_mispred;
wire                        mpd_direction;
wire                        mpd_error_branch;
wire                        mpd_is_predicted;
wire                        mpd_mispred_outcome;
wire                        mpd_mispred_bta;
wire [`npuarc_BR_INFO_RANGE]       mpd_branch_info;
wire [`npuarc_BR_TYPE_RANGE]       mpd_type;
wire [`npuarc_PC_RANGE]            mpd_seq_next_pc;
wire                        mpd_dslot;
wire [`npuarc_PC_RANGE]            mpd_pc;
wire                        mpd_tail_pc_3;
wire [`npuarc_ISIZE_RANGE]         mpd_commit_size;
wire                        mpd_secondary;
wire                        mpd_early;

//
// --  Branch Commit Interface
//
wire                        wa_pass /* verilator public_flat */;
wire [`npuarc_BR_TYPE_RANGE]       wa_type /* verilator public_flat */;
wire                        wa_secondary;
wire [`npuarc_PC_RANGE]            wa_pc;
wire                        wa_dslot;
wire [`npuarc_PC_RANGE]            wa_target /* verilator public_flat */;
wire [`npuarc_ISIZE_RANGE]         wa_commit_size;
wire                        wa_direction;
wire                        wa_error_branch;
wire                        wa_is_predicted;
wire                        wa_mispred_outcome;
wire                        wa_commit_mispred_bta;
wire [`npuarc_BR_INFO_RANGE]       wa_branch_info;
wire                        ar_user_mode_r;

//////////Performance counter branch prediction conditions////////////////
assign  ifu_missing_pred_r =  ifu_brch_mispred_r
                           & ((wa_type == `npuarc_BR_COND_RETURN) || (wa_type == `npuarc_BR_RETURN))
                           ;

assign  ifu_brch_mispred_r = (wa_type != 0)
                      & (wa_commit_mispred_bta | wa_error_branch | wa_mispred_outcome | ((!wa_is_predicted) & wa_direction))
                      & wa_pass
                      ;
assign  ifu_late_br_mispred = ifu_brch_mispred_r
                            & mpd_mispred
                            & (~mpd_early) ;
assign  ifu_cond_mispred_r = wa_mispred_outcome
                           & wa_pass
                           & ((wa_type == `npuarc_BR_CONDITIONAL) || (wa_type == `npuarc_BR_COND_CALL) || (wa_type == `npuarc_BR_COND_RETURN))
                           ;
assign  ifu_bta_mispred_r  =  (wa_type != 0)
                           & wa_pass
                           & wa_commit_mispred_bta
                           ;
assign  ifu_error_branch_r =  (wa_type != 0)
                           & wa_pass
                           & wa_error_branch
                           ;
assign  ifu_branch_cache_miss = (wa_type != 0)
                              & wa_pass
                              & (!wa_is_predicted)
                              & wa_direction
                              ;


////////// EXU interface to the DMP //////////////////////////////////////////
//
wire                        sa_dsync_op_r;
wire                        sa_dmb_op_r;
wire                        sa_dmb_dmp_stall;
wire [`npuarc_ADDR_RANGE]          x2_mem_addr_r;
wire                        x2_uop_inst_r;
wire                        x2_exu_stall;
wire [`npuarc_ADDR_RANGE]          x3_mem_addr_r;
wire                        x3_uop_inst_r;
wire                        dmp_dc3_stall_r;
wire                        ca_uop_inst_r;
wire                        db_active_r;
wire                        x3_sync_op_r;
wire                        x3_brk_op_r;
wire [`npuarc_ADDR_RANGE]          dc3_dtlb_efa;
wire                        dmp_dc3_fast_byp;
wire                        dmp_dc4_fast_byp_r;
wire                        dmp_dc4_fast_miss_r;
wire                        x3_cache_byp_r;
wire [`npuarc_DATA_RANGE]          dmp_dc4_fast_data;

wire                        hlt_wait_idle;

////////// Client interfaces for auxiliary registers access //////////////////
//

// -- DMP AUX. Interface
//
//wire                        dmp_aux_unimpl_r;
//wire                        dmp_aux_illegal_r;
//wire                        dmp_aux_k_rd_r;
//wire                        dmp_aux_k_wr_r;
//wire                        dmp_aux_serial_sr_r;
//wire                        dmp_aux_strict_sr_r;
//wire                        dmp_aux_stall_x3_r;
//wire [`DATA_RANGE]          dmp_aux_lr_data_r;

//wire                        gb_sys_halt_ack;
//wire                        ifu_idle_ack;
//wire                        dmp_idle_ack;
//wire                        hlt_idle_req;
//wire                        hlt_pipe_stop;

////////// Inputs from the Debug Target (CPU) ////////////////////////////
//
//wire                        wa_commit_dbg;        // 1 iff writeback commits
//wire [`DATA_RANGE]          wa_rf_wdata0_r;       // writeback data (port 0)
//`if (`RGF_WR_PORTS > 1)
//wire [`DATA_RANGE]          wa_rf_wdata1_r;       // writeback data (port 1)
//`endif
//wire                        debug_evt;            // acknowledges |db_request|
//wire                        wa_invalid_instr_r;   // illegal_instr => failure
//wire                        sys_halt_r;           // CPU is halted (STATUS32.H)

wire                          x3_1_db_exception;
wire                          ca_db_exception;

////////// Outputs to the Debug target (CPU) /////////////////////////////
//


///////// Clean Halt Interface ///////////////////////////////////////////
//




wire                        aux_dccm_ren_r;       //  (X3) Aux Reg Enable
wire                        aux_dccm_wen_r;       //  (WA) Aux Reg Enable
wire  [`npuarc_DATA_RANGE]         dccm_aux_rdata;       //  (X3) LR read data
wire                        dccm_aux_illegal;     //  (X3) SR/LR illegal
wire                        dccm_aux_k_rd;        //  (X3) needs Kernel Read
wire                        dccm_aux_k_wr;        //  (X3) needs Kernel Write
wire                        dccm_aux_unimpl;      //  (X3) Invalid Reg
wire                        dccm_aux_serial_sr;   //  (X3) SR group flush pipe
wire                        dccm_aux_strict_sr;   //  (X3) SR flush pipe
wire [3:0]                  dccm_base_r;
wire                        aux_dper_ren_r;       //  (X3) Aux Reg Enable
wire                        aux_dper_raddr_r;
wire                        aux_dper_wen_r;       //  (WA) Aux Reg Enable
wire                        aux_dper_waddr_r;
wire  [`npuarc_DATA_RANGE]         dper_aux_rdata;       //  (X3) LR read data
wire                        dper_aux_illegal;     //  (X3) SR/LR illegal
wire                        dper_aux_k_rd;        //  (X3) need Kernel Read
wire                        dper_aux_k_wr;        //  (X3) needs Kernel W perm
wire                        dper_aux_unimpl;      //  (X3) Invalid Reg
wire                        dper_aux_serial_sr;   //  (X3) SR group flush pipe
wire                        dper_aux_strict_sr;   //  (X3) SR flush pipe
wire [3:0]                  aux_dmp_per0_base_r;
wire [3:0]                  aux_dmp_per0_limit_r;

////////// Auxiliary interface for (DC) SR/LR instructions ////////////
//
wire                        aux_dc_ren_r;         //  (X3) Aux read enable
wire  [4:0]                 aux_dc_raddr_r;       //  (X3) Aux Address
wire                        aux_dc_wen_r;         //  (WA) Aux write enable
wire  [4:0]                 aux_dc_waddr_r;       //  (WA) Aux Address
wire  [`npuarc_DATA_RANGE]         dc_aux_rdata;         //  (X3) LR read data
wire                        dc_aux_illegal;       //  (X3) SR/LR illegal
wire                        dc_aux_k_rd;          //  (X3) need Kernel Rd
wire                        dc_aux_k_wr;          //  (X3) need Kernel Wr
wire                        dc_aux_unimpl;        //  (X3) Invalid Reg
wire                        dc_aux_serial_sr;     //  (X3) SR group flush
wire                        dc_aux_strict_sr;     //  (X3) SR single flus  h
wire                        dc_aux_busy;          //  Structural hazard
wire                        dc2_addr_pass;
wire  [`npuarc_ADDR_RANGE]         dc2_aux_addr;
wire                        aux_ic_ren_r;        //  (X3) Aux     Enable
wire  [3:0]                 aux_ic_raddr_r;      //  (X3) Aux Address
wire                        aux_ic_wen_r;        //  (WA) Aux     Enable
wire  [3:0]                 aux_ic_waddr_r;      //  (WA) Aux Address
wire  [`npuarc_DATA_RANGE]         ic_aux_rdata;        //  (X3) LR read data
wire                        ic_aux_illegal;      //  (X3) SR/LR illegal
wire                        ic_aux_k_rd;         //  (X3) need Kernel Read
wire                        ic_aux_k_wr;         //  (X3) need Kernel Write
wire                        ic_aux_unimpl;       //  (X3) Invalid
wire                        ic_aux_serial_sr;    //  (X3) SR group flush pipe
wire                        ic_aux_strict_sr;    //  (X3) SR flush pipe

// BPU aux regs module -> AUX
wire                        aux_bpu_ren_r;       //
wire   [3:0]                aux_bpu_raddr_r;     //
wire                        aux_bpu_wen_r;       //
wire   [3:0]                aux_bpu_waddr_r;     //
wire   [`npuarc_DATA_RANGE]        bpu_aux_rdata;       //
wire                        bpu_aux_illegal;     //
wire                        bpu_aux_k_rd;        //
wire                        bpu_aux_k_wr;        //
wire                        bpu_aux_unimpl;      //
wire                        bpu_aux_serial_sr;   //
wire                        bpu_aux_strict_sr;   //

wire                        aux_pct_active;       //
wire                        aux_pct_ren_r;        //  (X3) Aux     Enable
wire        [5:0]           aux_pct_raddr_r;      //  (X3) Aux Address
wire                        aux_pct_wen_r;        //  (WA) Aux     Enable
wire        [5:0]           aux_pct_waddr_r;      //  (WA) Aux Address
wire  [`npuarc_DATA_RANGE]         pct_aux_rdata;        //  (X3) LR read data
wire                        pct_aux_illegal;      //  (X3) SR/LR illegal
wire                        pct_aux_k_rd;         //  (X3) needs Kernel Rd
wire                        pct_aux_k_wr;         //  (X3) needs Kernel Wr
wire                        pct_aux_unimpl;       //  (X3) Invalid
wire                        pct_aux_serial_sr;    //  (X3) SR group flush
wire                        pct_aux_strict_sr;    //  (X3) SR single flush
wire [`npuarc_DATA_RANGE]         ar_aux_debug_r;
wire [`npuarc_DATA_RANGE]         ar_aux_status32_r;     //  Status32
wire [`npuarc_DATA_RANGE]         ar_aux_irq_act_r;      //  IRQ ACT

////////// General input signals ///////////////////////////////////////////
//
wire                        mmu_ready;       // Clear on reset, set when
                                             // mmu ready for operation
                                             // (finished reset sequence)
wire                        mmu_en_r;        // Enable TLB lookups
wire                        mpu_en_r;
wire                        x2_da0_transl;

wire                        mmu_clock_req_r;
wire                        mmu_cmd_active;
// Access type: user/kernel mode, pid shared bit (common to all req ports)
wire                        kernel_mode;     // has Kernel mode privileges
wire                        shared_en_r;     // Shared lib enable (PID)
wire [`npuarc_SASID_RANGE]         sasid_r;         // Current pid slib membership
wire [`npuarc_MMU_PID_ASID_RANGE]  asid_rr;         // Current pid.asid (2cyc)

////////// AUX interface //////////////////////////////////////////////////
//
wire                        aux_mmu_ren_r;        //  (X3) Aux     Enable
wire [4:0]                  aux_mmu_raddr_r;      //  (X3) Aux Address
wire                        aux_mmu_wen_r;        //  (WA) Aux     Enable
wire [4:0]                  aux_mmu_waddr_r;      //  (WA) Aux Address
wire [`npuarc_DATA_RANGE]          mmu_aux_rdata;        //  (X3) LR read data
wire                        mmu_aux_illegal;      //  (X3) SR/LR illegal
wire                        mmu_aux_k_rd;         //  (X3) needs Kernel Read
wire                        mmu_aux_k_wr;         //  (X3) needs Kernel W perm
wire                        mmu_aux_unimpl;       //  (X3) Invalid
wire                        mmu_aux_serial_sr;    //  (X3) SR group flush pipe
wire                        mmu_aux_strict_sr;    //  (X3) SR flush pipe
wire                        mmu_aux_index_ecc_e;

////////// Interface to itlb //////////////////////////////////////////////
//
// itlb update request (on miss)
wire                        ifu_clk2_en;
wire                        itlb_update_req;     // late (unreg) outputs
wire [`npuarc_PD0_VPN_RANGE]       itlb_update_req_vpn;

// jtlb response to itlb update request
wire                        jrsp_itlb_update_nxt;
wire                        jrsp_itlb_update;
wire                        jrsp_itlb_update_hit;
wire                        jrsp_itlb_multi_hit;
wire                        jrsp_itlb_tlb_err;
wire                        jrsp_itlb_tlb_err_evt;
wire                        jrsp_itlb_tlb_err_excpn;

// insert / delete / Inval (aux) operations from jtlb
wire [`npuarc_JCMD_RANGE]          jtlb_itlb_cmd_r;   // command from jtlb (aux)
wire [`npuarc_ITLB_INDEX_RANGE]    jtlb_itlb_index_r; // Aux addr for read/write

// Interface to read utlb entries
//
wire                        itlb_rd_val;   // rd data reg in jtlb
wire [`npuarc_UTLB_ENTRY_RANGE]    itlb_rd_data;  // LR read data (entry)
//wire                        al_ifu_err_nxtpg;

////////// Interface to dtlb //////////////////////////////////////////////
//
// Consolidated dtlb update request (on miss(es))
wire                        dtlb_update_req;     // late (unreg) outputs
wire [`npuarc_PD0_VPN_RANGE]       dtlb_update_req_vpn;

// jtlb response to dtlb update request
wire                        jrsp_dtlb_update;
wire                        jrsp_dtlb_update_hit;
wire                        jrsp_dtlb_multi_hit;
wire                        jrsp_dtlb_tlb_err;
wire                        jrsp_dtlb_tlb_err_evt;
wire                        jrsp_dtlb_tlb_err_excpn;

// insert / delete / Inval (aux) operations from jtlb
wire [`npuarc_JCMD_RANGE]          jtlb_dtlb_cmd_r;    // command from jtlb (aux)
wire [`npuarc_DTLB_INDEX_RANGE]    jtlb_dtlb_index_r;  // Aux addr for read/write

// Interface to read utlb entries
//
wire                        dtlb_rd_val;   // rd data reg in jtlb
wire [`npuarc_UTLB_ENTRY_RANGE]    dtlb_rd_data;  // LR read data (entry)

////////// Shared bus to uTLBs ////////////////////////////////////////////
//
// Entry data for update from jtlb; also used for lookups and write by jtlb
wire [`npuarc_UTLB_ENTRY_RANGE]    jtlb_update_data;

wire                        wa_jtlb_lookup_start_r;
wire                        wa_jtlb_cancel;

wire                        dtlb_update_pend_r;
wire   [1:0]                dc4_dtlb_miss_r;
wire                        dc3_dtlb_miss_excpn_r;
wire                        dc3_dtlb_ovrlp_excpn_r;
wire                        dc3_dtlb_protv_excpn_r;
wire                        dc3_dtlb_ecc_excpn_r;
wire                        ca_tlb_miss_excpn;
wire   [`npuarc_PD0_VPN_RANGE]     ca_tlb_miss_efa;
wire                        ca_m_chk_excpn;

assign kernel_mode = ~ar_user_mode_r;


//////////////////////////////////////////////////////////////////////////////
// Wires for ECC Interface
//
wire [15:0]                 ecc_flt_status;       //
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used
wire [`npuarc_DATA_RANGE]          ar_aux_ecc_ctrl_r;    //
// leda NTL_CON13A on




wire                    iexcpn_discarded;
wire                    holdup_excpn_r;
wire                    st_instrs_discarded;

// qualify tlb result signals with result valid (update to utlb)
assign  jrsp_itlb_tlb_err_evt = (jrsp_itlb_tlb_err && jrsp_itlb_update)| mmu_aux_index_ecc_e;
assign  jrsp_dtlb_tlb_err_evt = jrsp_dtlb_tlb_err && jrsp_dtlb_update;

assign ecc_flt_status = {
                        (jrsp_itlb_tlb_err_evt),
                        (jrsp_dtlb_tlb_err_evt),
                        dc4_dc_dt_ecc_db_error,     // D$ Tag Error
                        dc4_dc_dd_ecc_db_error,     // D$ Data error
                        2'b00,
                        ic_tag_ecc_err,
                        al_icache_ecc_err,
                        2'b00,
                        dc4_dccm_ecc_db_error,      // DCCM error
                        1'b0,
                        4'b0000
                        };

assign ecc_ifu_disable        =   ar_aux_ecc_ctrl_r[0];

assign ecc_ifu_expn_disable   =   ar_aux_ecc_ctrl_r[2];

assign ecc_dmp_disable        =   ar_aux_ecc_ctrl_r[1];

assign ecc_dmp_expn_disable   =   ar_aux_ecc_ctrl_r[3];

assign ecc_mmu_disable        =   ar_aux_ecc_ctrl_r[4];

assign ecc_mmu_expn_disable   =   ar_aux_ecc_ctrl_r[5];


assign jrsp_dtlb_tlb_err_excpn = jrsp_dtlb_tlb_err & (~ecc_mmu_expn_disable);
assign jrsp_itlb_tlb_err_excpn = jrsp_itlb_tlb_err & (~ecc_mmu_expn_disable);

assign ca_store_grad_r = (|ca_store_grad);




//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Module instantiation: Instruction Fetch Unit                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_ifu u_alb_ifu (
  .clk                    (clk                    ),
  .l1_clock_active        (l1_clock_active        ),

  .rst_a                  (rst_a                  ),

  .dbg_cache_rst_disable_r (dbg_cache_rst_disable_r),


//   .imem_clk               (imem_clk               ),

  .ic_tag_way0_clk     (ic_tag_way0_clk     ),
  .ic_tag_dout0          (ic_tag_dout0          ),
  .ic_tag_din0           (ic_tag_din0           ),
  .ic_tag_addr0          (ic_tag_addr0          ),
  .ic_tag_wem0           (ic_tag_wem0           ),    
  .ic_tag_cen0           (ic_tag_cen0           ),
  .ic_tag_wen0           (ic_tag_wen0           ),
  .ic_tag_way1_clk     (ic_tag_way1_clk     ),
  .ic_tag_dout1          (ic_tag_dout1          ),
  .ic_tag_din1           (ic_tag_din1           ),
  .ic_tag_addr1          (ic_tag_addr1          ),
  .ic_tag_wem1           (ic_tag_wem1           ),    
  .ic_tag_cen1           (ic_tag_cen1           ),
  .ic_tag_wen1           (ic_tag_wen1           ),
  .ic_tag_way2_clk     (ic_tag_way2_clk     ),
  .ic_tag_dout2          (ic_tag_dout2          ),
  .ic_tag_din2           (ic_tag_din2           ),
  .ic_tag_addr2          (ic_tag_addr2          ),
  .ic_tag_wem2           (ic_tag_wem2           ),    
  .ic_tag_cen2           (ic_tag_cen2           ),
  .ic_tag_wen2           (ic_tag_wen2           ),
  .ic_tag_way3_clk     (ic_tag_way3_clk     ),
  .ic_tag_dout3          (ic_tag_dout3          ),
  .ic_tag_din3           (ic_tag_din3           ),
  .ic_tag_addr3          (ic_tag_addr3          ),
  .ic_tag_wem3           (ic_tag_wem3           ),    
  .ic_tag_cen3           (ic_tag_cen3           ),
  .ic_tag_wen3           (ic_tag_wen3           ),

  .ic_data_bank0_clk   (ic_data_bank0_clk   ),
  .ic_data_dout0         (ic_data_dout0         ),
  .ic_data_addr0         (ic_data_addr0         ),
  .ic_data_din0          (ic_data_din0          ),
  .ic_data_cen0          (ic_data_cen0           ),
  .ic_data_wen0          (ic_data_wen0           ),
  .ic_data_wem0          (ic_data_wem0           ),
  .ic_data_bank1_clk   (ic_data_bank1_clk   ),
  .ic_data_dout1         (ic_data_dout1         ),
  .ic_data_addr1         (ic_data_addr1         ),
  .ic_data_din1          (ic_data_din1          ),
  .ic_data_cen1          (ic_data_cen1           ),
  .ic_data_wen1          (ic_data_wen1           ),
  .ic_data_wem1          (ic_data_wem1           ),

  // MPU interface
  .ifetch_addr_mpu        (ifetch_addr_mpu        ),
  .ifetch_viol            (ifetch_viol            ),
  .ifetch_unc             (1'b0                   ), 

  .ifu_ibus_cmd_valid     (ifu_ibus_cmd_valid     ),
  .ifu_ibus_cmd_prot      (ifu_ibus_cmd_prot[0]   ),
  .ifu_ibus_cmd_accept    (ifu_ibus_cmd_accept    ),
  .ifu_ibus_cmd_addr      (ifu_ibus_cmd_addr      ),
  .ifu_ibus_cmd_wrap      (ifu_ibus_cmd_wrap      ),
  .ifu_ibus_cmd_cache     (ifu_ibus_cmd_cache[2]  ),
  .ifu_ibus_cmd_burst_size(ifu_ibus_cmd_burst_size),
  .ifu_ibus_rd_valid      (ifu_ibus_rd_valid      ),
  .ifu_ibus_rd_accept     (ifu_ibus_rd_accept     ),
  .ifu_ibus_rd_data       (ifu_ibus_rd_data       ),
  .ifu_ibus_rd_last       (ifu_ibus_rd_last       ),
  .ifu_ibus_err_rd        (ifu_ibus_err_rd        ),





  .ecc_ifu_disable        (ecc_ifu_disable      ),
  .ecc_ifu_expn_disable   (ecc_ifu_expn_disable ),
  .ic_tag_ecc_err         (ic_tag_ecc_err       ),
  .al_icache_ecc_err      (al_icache_ecc_err    ),
  .ic_tag_ecc_sbe_clr     (ic_tag_ecc_sbe_clr   ),
  .ic_tag_ecc_sbe_cnt     (ic_tag_ecc_sbe_cnt   ),

  .ic_data_ecc_sbe_clr    (ic_data_ecc_sbe_clr  ),
  .ic_data_ecc_sbe_cnt    (ic_data_ecc_sbe_cnt  ),
//     `if (`HAS_SAFETY == 1)
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

//     `endif




  .ifu_ivic                (ifu_ivic           ),
  .ifu_ivil                (ifu_ivil           ),

  .aux_read               (aux_read             ), //
  .aux_write              (aux_write            ), //
  .aux_wdata              (wa_sr_data_r         ), //
  .aux_ic_ren_r           (aux_ic_ren_r         ),
  .aux_ic_raddr_r         (aux_ic_raddr_r       ),
  .aux_ic_wen_r           (aux_ic_wen_r         ),
  .aux_ic_waddr_r         (aux_ic_waddr_r       ),
  .ic_aux_unimpl          (ic_aux_unimpl        ),
  .ic_aux_illegal         (ic_aux_illegal       ),
  .ic_aux_k_rd            (ic_aux_k_rd          ),
  .ic_aux_k_wr            (ic_aux_k_wr          ),
  .ic_aux_serial_sr       (ic_aux_serial_sr     ),
  .ic_aux_strict_sr       (ic_aux_strict_sr     ),
  .ic_aux_rdata           (ic_aux_rdata         ),
  .aux_bpu_ren_r          (aux_bpu_ren_r        ),
  .aux_bpu_raddr_r        (aux_bpu_raddr_r      ),
  .aux_bpu_wen_r          (aux_bpu_wen_r        ),
  .aux_bpu_waddr_r        (aux_bpu_waddr_r      ),
  .bpu_aux_unimpl         (bpu_aux_unimpl       ),
  .bpu_aux_illegal        (bpu_aux_illegal      ),
  .bpu_aux_k_rd           (bpu_aux_k_rd         ),
  .bpu_aux_k_wr           (bpu_aux_k_wr         ),
  .bpu_aux_serial_sr      (bpu_aux_serial_sr    ),
  .bpu_aux_strict_sr      (bpu_aux_strict_sr    ),
  .bpu_aux_rdata          (bpu_aux_rdata        ),

  // Fetch Restart Interface/////////////////////////////////////////////////
  //
  .fch_restart            (fch_restart            ),
  .fch_restart_vec        (fch_restart_vec        ),
  .fch_target             (fch_target             ),
  .fch_target_successor   (fch_target_successor   ),
  .fch_iprot_replay       (fch_iprot_replay       ),
  .ar_user_mode_r         (ar_user_mode_r         ),

  ///////// Predecode output /////////////////////////////////////////////////
  //
  .al_pass                (al_pass                ),
  .al_inst                (al_inst                ),
  .al_limm                (al_limm                ),
  .da_holdup              (da_holdup              ),

  .al_exception           (al_exception           ),
  .al_excpn_type          (al_excpn_type          ),
  .al_excpn_info          (al_excpn_info          ),
  .al_ifu_err_nxtpg       (al_ifu_err_nxtpg      ),
  .al_iprot_viol          (al_iprot_viol          ),

  .al_is_predicted        (al_is_predicted        ),
  .al_prediction          (al_prediction          ),
  .al_predicted_bta       (al_predicted_bta       ),
  .al_prediction_type     (al_prediction_type     ),
  .al_error_branch        (al_error_branch        ),
  .al_branch_info         (al_branch_info         ),
  .al_with_dslot          (al_with_dslot          ),



  ////////// Misprediction Interface /////////////////////////////////////////
  //
  .mpd_mispred            (mpd_mispred            ),
  .mpd_direction          (mpd_direction          ),
  .mpd_error_branch       (mpd_error_branch       ),
  .mpd_is_predicted       (mpd_is_predicted       ),
  .mpd_mispred_outcome    (mpd_mispred_outcome    ),
  .mpd_mispred_bta        (mpd_mispred_bta        ),
  .mpd_branch_info        (mpd_branch_info        ),
  .mpd_dslot              (mpd_dslot              ),
  .mpd_seq_next_pc        (mpd_seq_next_pc        ),
  .mpd_type               (mpd_type               ),

  .mpd_pc                 (mpd_pc                 ),
  .mpd_tail_pc_3          (mpd_tail_pc_3          ),
  .mpd_commit_size        (mpd_commit_size        ),
  .mpd_secondary          (mpd_secondary          ),
  .mpd_early              (mpd_early              ),

  .wa_pass                (wa_pass                ),
  .wa_type                (wa_type                ),
  .wa_secondary           (wa_secondary           ),
  .wa_pc                  (wa_pc                  ),
  .wa_tail_pc_3           (wa_tail_pc_3           ),
  .wa_dslot               (wa_dslot               ),
  .wa_target              (wa_target              ),
  .wa_commit_size         (wa_commit_size         ),
  .wa_direction           (wa_direction           ),
  .wa_error_branch        (wa_error_branch        ),
  .wa_is_predicted        (wa_is_predicted        ),
  .wa_mispred_outcome     (wa_mispred_outcome     ),
  .wa_commit_mispred_bta  (wa_commit_mispred_bta  ),
  .wa_branch_info         (wa_branch_info         ),

  .bc_din0                (bc_din0                ),
  .bc_addr0               (bc_addr0               ),
  .bc_me0                 (bc_me0                 ),
  .bc_we0                 (bc_we0                 ),
  .bc_wem0                (bc_wem0                ),
  .bc_dout0               (bc_dout0               ),
  .gs_din0                (gs_din0                ),
  .gs_addr0               (gs_addr0               ),
  .gs_me0                 (gs_me0                 ),
  .gs_we0                 (gs_we0                 ),
  .gs_wem0                (gs_wem0                ),
  .gs_dout0               (gs_dout0               ),
  .bc_ram0_clk            (bc_ram0_clk            ),
  .pt_ram0_clk            (pt_ram0_clk            ),
  .bc_ram0_clk_en         (bc_ram0_clk_en         ),
  .pt_ram0_clk_en         (pt_ram0_clk_en         ),

  .bc_din1                (bc_din1                ),
  .bc_addr1               (bc_addr1               ),
  .bc_me1                 (bc_me1                 ),
  .bc_we1                 (bc_we1                 ),
  .bc_wem1                (bc_wem1                ),
  .bc_dout1               (bc_dout1               ),
  .gs_din1                (gs_din1                ),
  .gs_addr1               (gs_addr1               ),
  .gs_me1                 (gs_me1                 ),
  .gs_we1                 (gs_we1                 ),
  .gs_wem1                (gs_wem1                ),
  .gs_dout1               (gs_dout1               ),
  .bc_ram1_clk            (bc_ram1_clk            ),
  .pt_ram1_clk            (pt_ram1_clk            ),
  .bc_ram1_clk_en         (bc_ram1_clk_en         ),
  .pt_ram1_clk_en         (pt_ram1_clk_en         ),

  .ifu_icache_miss_r      (ifu_icache_miss_r      ),
  .ifu_icache_hit_r       (ifu_icache_hit_r       ),
  .ifu_icache_disabled    (ifu_icache_disabled    ),
  .ifu_way_pred_miss_r    (ifu_way_pred_miss_r    ),
  .ifu_issue_stall_r      (ifu_issue_stall_r      ),



  .ifu_bit_error_r        (ifu_bit_error_r        ),

  ////////// Interface to itlb //////////////////////////////////////////////
  //
  .mmu_en_r               (mmu_en_r),         // Enable TLB lookups
  .mpu_en_r               (mpu_en_r),

  .mmu_ready              (mmu_ready),
  .mmu_clock_req_r        (mmu_clock_req_r),
  .mmu_cmd_active         (mmu_cmd_active),

  .shared_en_r            (shared_en_r),      // Shared lib enable (PID)
  .sasid_r                (sasid_r),          // Current pid slib membership
  .asid_r                 (asid_rr),          // Current pid.asid (2cyc)

  .db_active_r            (db_active_r),

  // itlb update request (on miss)
  .ifu_clk2_en            (ifu_clk2_en),
  .itlb_update_req        (itlb_update_req),     // late (unreg) outputs
  .itlb_update_req_vpn    (itlb_update_req_vpn),

  // jtlb response to itlb update request
  .jrsp_itlb_update_nxt   (jrsp_itlb_update_nxt),
  .jrsp_itlb_update       (jrsp_itlb_update),
  .jrsp_itlb_update_hit   (jrsp_itlb_update_hit),
  .jrsp_itlb_multi_hit    (jrsp_itlb_multi_hit),
  .jrsp_itlb_tlb_err      (jrsp_itlb_tlb_err_excpn),

  // insert / delete / Inval (aux) operations from jtlb
  .jtlb_itlb_cmd_r        (jtlb_itlb_cmd_r),   // command from jtlb (aux)
  .jtlb_itlb_index_r      (jtlb_itlb_index_r), // Aux addr for read/write

  // Interface to read utlb entries
  //
  .itlb_rd_val            (itlb_rd_val),   // rd data reg in jtlb
  .itlb_rd_data           (itlb_rd_data),  // LR read data (entry)

  ////////// Shared bus to uTLBs ////////////////////////////////////////////
  //
  // Entry data for update from jtlb; also used for lookups and write by jtlb
  .jtlb_update_data       (jtlb_update_data),

  .fch_stop_r             (fch_stop_r             ),
  .ifu_idle_r             (ifu_idle_r             )
);


assign ifu_ibus_cmd_cache[3] = 1'b1;
assign ifu_ibus_cmd_cache[1] = ifu_ibus_cmd_cache[2];
assign ifu_ibus_cmd_cache[0] = ifu_ibus_cmd_cache[2];


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Module instantiation: Data Memory Pipeline                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_dmp u_alb_dmp (
  .iexcpn_discarded         (iexcpn_discarded       ),
  .holdup_excpn_r           (holdup_excpn_r         ),
  .st_instrs_discarded      (st_instrs_discarded    ),
  .st_instrs_discarded_r    (ar_aux_ecr_r[25]       ),
  .sa_dsync_op_r            (sa_dsync_op_r          ),
  .sa_dmb_op_r              (sa_dmb_op_r            ),
  .sa_dmb_stall             (sa_dmb_dmp_stall       ),

  .sa_load_r                (sa_load_r              ),
  .sa_store_r               (sa_store_r             ),
  .ca_dmp_aux_sr_op         (dmp_aux_sr_op          ),



  .x1_valid_r               (x1_valid_r             ),
  .x1_pass                  (x1_pass                ),
  .x1_load_r                (x1_load_r              ),
  .x1_store_r               (x1_store_r             ),
  .x1_pref_r                (x1_pref_r              ),
  .x1_cache_byp_r           (x1_cache_byp_r         ),
  .x1_size_r                (x1_size_r              ),
  .x1_mem_addr0             (x1_mem_addr0           ),
  .x1_mem_addr1             (x1_mem_addr1           ),
  .x1_addr_base             (x1_addr_base           ),
  .x1_addr_offset           (x1_addr_offset         ),
  .x1_bank_sel_lo           (x1_bank_sel_lo         ),
  .x1_bank_sel_hi           (x1_bank_sel_hi         ),
  .x1_uop_inst_r            (x1_uop_inst_r          ),
  .dc1_stall                (dc1_stall              ),

  .x2_valid_r               (x2_valid_r             ),
  .x2_pass                  (x2_pass                ),
  .x2_enable                (x2_enable              ),
  .x2_load_r                (x2_load_r              ),
  .x2_store_r               (x2_store_r             ),
  .x2_locked_r              (x2_locked_r            ),
  .x2_pref_r                (x2_pref_r              ),
  .x2_size_r                (x2_size_r              ),
  .x2_cache_byp_r           (x2_cache_byp_r         ),
  .x2_mpu_data_flt          (x2_mpu_data_flt        ),
  .x2_mpu_data_unc          (1'b0                   ),
  .x2_uop_inst_r            (x2_uop_inst_r          ),
  .x2_mem_addr0_r           (x2_mem_addr_r          ),
  .x2_exu_stall             (x2_exu_stall           ),
  .dc2_stall                (dc2_stall              ),

  .x3_valid_r               (x3_valid_r             ),
  .x3_pass                  (x3_pass                ),
  .x3_1_enable              (x3_enable              ),
  .x3_load_r                (x3_load_r              ),
  .x3_pref_r                (x3_pref                ),
  .x3_pref_l2_r             (x3_pref_l2             ),
  .x3_prefw_r               (x3_prefw               ),
  .x3_pre_alloc_r           (x3_pre_alloc           ),
  .x3_store_r               (x3_store_r             ),
  .x3_store_may_grad        (x3_store_may_grad      ),
  .x3_locked_r              (x3_locked_r            ),
  .x3_cache_byp_r           (x3_cache_byp_r         ),
  .x3_size_r                (x3_size_r              ),
  .x3_sex_r                 (x3_sex_r               ),
  .x3_mem_addr0_r           (x3_mem_addr_r          ),
  .x3_uop_inst_r            (x3_uop_inst_r          ),
  .dmp_dc3_stall_r          (dmp_dc3_stall_r        ),
  .x3_sync_op_r             (x3_sync_op_r           ),
  .x3_brk_op_r              (x3_brk_op_r            ),
  .dc3_dtlb_efa             (dc3_dtlb_efa           ),
  .dc3_fast_byp             (dmp_dc3_fast_byp       ),
  .dc4_fast_byp_r           (dmp_dc4_fast_byp_r     ),
  .dc4_fast_byp_miss_r      (dmp_dc4_fast_miss_r    ),

  .ca_valid_r               (ca_valid_r             ),
  .ca_pass                  (ca_pass                ),
  .ca_enable                (ca_enable              ),
  .ca_load_r                (ca_load_r              ),
  .ca_pref_r                (ca_pref                ),
  .ca_pref_l2_r             (ca_pref_l2             ),
  .ca_prefw_r               (ca_prefw               ),
  .ca_pre_alloc_r           (ca_pre_alloc           ),
  .ca_store_r               (ca_store_r             ),
//`if ((`RTT_IMPL_MEDIUM == 1) || (`RTT_IMPL_FULL == 1)) //{
  .ca_store_grad_r          (ca_store_grad          ),
//`endif // }
  .ca_store_grad_swap_r     (ca_store_grad_swap     ),
  .ca_store_grad_tag_lo_r   (ca_store_grad_tag_lo   ),
  .ca_store_grad_tag_hi_r   (ca_store_grad_tag_hi   ),

  .ca_locked_r              (ca_locked_r            ),
  .ca_size_r                (ca_size_r              ),
  .ca_sex_r                 (ca_sex_r               ),
  .ca_mem_addr0_r           (ca_mem_addr_r          ),
  .ca_phys_addr_r           (ca_phys_addr_r         ),
  .ca_uop_inst_r            (ca_uop_inst_r          ),
  .ca_wr_data_r             (ca_wr_data_r           ),
  .dc4_stall_r              (dc4_stall_r            ),

  .ecc_dccm_sbe_count_r     (ecc_dccm_sbe_count_r   ),
  .dccm_ecc_sbe_clr         (dccm_ecc_sbe_clr       ),
  .ecc_dc_tag_sbe_count_r   (ecc_dc_tag_sbe_count_r ),
  .dc_tag_ecc_sbe_clr       (dc_tag_ecc_sbe_clr     ),
  .ecc_dc_data_sbe_count_r  (ecc_dc_data_sbe_count_r),
  .dc_data_ecc_sbe_clr      (dc_data_ecc_sbe_clr    ),
  .ecc_sbe_dmp_clr          (ecc_sbe_dmp_clr        ),

  .dc4_waw_replay_r         (dc4_waw_replay_r       ),
  .dc4_pref_r               (dc4_pref_r             ),

  .wa_lpa_r                 (wa_lpa_r               ),
  .wa_lock_flag_r           (wa_lock_flag_r         ),
  .wa_lock_double_r         (wa_lock_double_r       ),

  .wa_restart_r             (wa_restart_r           ),
  .wa_restart_kill_r        (wa_restart_kill_r      ),
  .wa_hlt_restart_r         (wa_hlt_restart_r       ),
  .mem_excpn_ack_r          (mem_excpn_ack_r        ),

  .wa_retire1_valid         (wa_retire1_valid       ),
  .wa_retire1_tag           (wa_retire1_tag         ),
  .wa_retire1_data          ({wa_rf_wdata1_hi_r,
                              wa_rf_wdata1_lo_r}    ),


//`if ((`RTT_IMPL_MEDIUM == 1) || (`RTT_IMPL_FULL == 1)) //{
  .ca_store_grad_tag        (ca_store_grad_tag      ),
  .dmp_st_retire0           (dmp_st_retire0         ),
  .dmp_st_retire0_tag       (dmp_st_retire0_tag     ),
  .dmp_st_retire0_data      (dmp_st_retire0_data    ),

  .dmp_st_retire1           (dmp_st_retire1         ),
  .dmp_st_retire1_tag       (dmp_st_retire1_tag     ),
  .dmp_st_retire1_data      (dmp_st_retire1_data    ),

//`endif               // }

  .ar_user_mode_r           (ar_user_mode_r         ),

  .dc4_fast_data            (dmp_dc4_fast_data      ),
  .dmp_rf_wdata             (dmp_rf_wdata           ),
  .dmp_scond_zflag          (dmp_scond_zflag        ),
  .dmp_clear_lf             (dmp_clear_lf           ),
  .rtt_dc4_scond_go         (rtt_dc4_scond_go       ),  // scond will be success

  .dc3_excpn                (dc3_excpn              ),
  .dc3_excpn_type           (dc3_excpn_type         ),
  .dc3_excpn_code           (dc3_excpn_code         ),

  .dc4_replay               (dc4_replay             ),
  .dc4_excpn                (dc4_excpn              ),
  .dc4_excpn_user_mode_r    (dc4_excpn_user_mode_r  ),
  .dc4_excpn_mem_addr       (dc4_excpn_mem_addr     ),
  .dc4_excpn_type           (dc4_excpn_type         ),
//  .dc4_excpn_code           (dc4_excpn_code         ),

  .ecc_dmp_disable          (ecc_dmp_disable       ),
  .ecc_dmp_expn_disable     (ecc_dmp_expn_disable  ),
  .fs_dc_tag_bank0_syndrome_r    (fs_dc_tag_bank0_syndrome_r),
  .fs_dc_tag_bank1_syndrome_r    (fs_dc_tag_bank1_syndrome_r),
  .fs_dc_tag_bank2_syndrome_r    (fs_dc_tag_bank2_syndrome_r),
  .fs_dc_tag_bank3_syndrome_r    (fs_dc_tag_bank3_syndrome_r),

  .fs_dc_tag_bank0_ecc_sb_error_r(fs_dc_tag_bank0_ecc_sb_error_r),
  .fs_dc_tag_bank1_ecc_sb_error_r(fs_dc_tag_bank1_ecc_sb_error_r),
  .fs_dc_tag_bank2_ecc_sb_error_r(fs_dc_tag_bank2_ecc_sb_error_r),
  .fs_dc_tag_bank3_ecc_sb_error_r(fs_dc_tag_bank3_ecc_sb_error_r),

  .fs_dc_tag_bank0_ecc_db_error_r(fs_dc_tag_bank0_ecc_db_error_r),
  .fs_dc_tag_bank1_ecc_db_error_r(fs_dc_tag_bank1_ecc_db_error_r),
  .fs_dc_tag_bank2_ecc_db_error_r(fs_dc_tag_bank2_ecc_db_error_r),
  .fs_dc_tag_bank3_ecc_db_error_r(fs_dc_tag_bank3_ecc_db_error_r),

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

//  `endif
  .dc4_dc_dt_ecc_db_error  (dc4_dc_dt_ecc_db_error  ),
  .dc4_dc_dd_ecc_db_error  (dc4_dc_dd_ecc_db_error  ),
  .dc4_dccm_ecc_db_error   (dc4_dccm_ecc_db_error   ),
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

//  `endif
  .dc4_grad_req             (dc4_grad_req           ),
  .ca_grad_ack              (ca_grad_ack            ),
  .ca_grad_tag              (ca_grad_tag            ),

  .dmp_retire_req           (dmp_retire_req         ),
  .dmp_retire_tag           (dmp_retire_tag         ),
  .retire_ack               (dmp_retire_ack         ),


  .clk_bank0_lo         (clk_dccm_bank0_lo    ),
  .clk_bank0_hi         (clk_dccm_bank0_hi    ),
  .dccm_bank0_cs_lo     (dccm_bank0_cs_lo     ),
  .dccm_bank0_cs_hi     (dccm_bank0_cs_hi     ),
  .dccm_bank0_addr_lo   (dccm_bank0_addr_lo   ),
  .dccm_bank0_addr_hi   (dccm_bank0_addr_hi   ),
  .dccm_bank0_we_lo     (dccm_bank0_we_lo     ),
  .dccm_bank0_we_hi     (dccm_bank0_we_hi     ),
  .dccm_bank0_din       (dccm_bank0_din       ),
  .dccm_bank0_wem       (dccm_bank0_wem       ),
  .dccm_bank0_dout      (dccm_bank0_dout      ),

  .clk_bank1_lo         (clk_dccm_bank1_lo    ),
  .clk_bank1_hi         (clk_dccm_bank1_hi    ),
  .dccm_bank1_cs_lo     (dccm_bank1_cs_lo     ),
  .dccm_bank1_cs_hi     (dccm_bank1_cs_hi     ),
  .dccm_bank1_addr_lo   (dccm_bank1_addr_lo   ),
  .dccm_bank1_addr_hi   (dccm_bank1_addr_hi   ),
  .dccm_bank1_we_lo     (dccm_bank1_we_lo     ),
  .dccm_bank1_we_hi     (dccm_bank1_we_hi     ),
  .dccm_bank1_din       (dccm_bank1_din       ),
  .dccm_bank1_wem       (dccm_bank1_wem       ),
  .dccm_bank1_dout      (dccm_bank1_dout      ),


  .dmi_cmd_valid_r         (dccm_dmi_cmd_valid      ),
  .dmi_cmd_accept          (dccm_dmi_cmd_accept     ),
  .dmi_cmd_read_r          (dccm_dmi_cmd_read       ),
  .dmi_cmd_addr_r          (dccm_dmi_cmd_addr       ),

  .dmi_rd_valid            (dccm_dmi_rd_valid       ),
  .dmi_rd_accept_r         (dccm_dmi_rd_accept      ),
  .dmi_rd_data             (dccm_dmi_rd_data        ),
  .dmi_rd_err              (dccm_dmi_err_rd         ),

  .dmi_wr_valid_r          (dccm_dmi_wr_valid       ),
  .dmi_wr_accept           (dccm_dmi_wr_accept      ),
  .dmi_wr_data_r           (dccm_dmi_wr_data        ),
  .dmi_wr_mask_r           (dccm_dmi_wr_mask        ),
  .dmi_wr_done_r           (dccm_dmi_wr_done        ),
  .dmi_err_wr              (dccm_dmi_err_wr         ),

  .clk_tag_even_w0        (clk_tag_even_w0       ),
  .dc_tag_even_cs_w0      (dc_tag_even_cs_w0     ),
  .dc_tag_even_we_w0      (dc_tag_even_we_w0     ),
  .dc_tag_even_wem_w0     (dc_tag_even_wem_w0    ),
  .dc_tag_even_addr_w0    (dc_tag_even_addr_w0   ),
  .dc_tag_even_din_w0     (dc_tag_even_din_w0    ),
  .dc_tag_even_dout_w0    (dc_tag_even_dout_w0   ),

  .clk_tag_odd_w0         (clk_tag_odd_w0        ),
  .dc_tag_odd_cs_w0       (dc_tag_odd_cs_w0      ),
  .dc_tag_odd_we_w0       (dc_tag_odd_we_w0      ),
  .dc_tag_odd_wem_w0      (dc_tag_odd_wem_w0     ),
  .dc_tag_odd_addr_w0     (dc_tag_odd_addr_w0    ),
  .dc_tag_odd_din_w0      (dc_tag_odd_din_w0     ),
  .dc_tag_odd_dout_w0     (dc_tag_odd_dout_w0    ),

  .clk_tag_even_w1        (clk_tag_even_w1       ),
  .dc_tag_even_cs_w1      (dc_tag_even_cs_w1     ),
  .dc_tag_even_we_w1      (dc_tag_even_we_w1     ),
  .dc_tag_even_wem_w1     (dc_tag_even_wem_w1    ),
  .dc_tag_even_addr_w1    (dc_tag_even_addr_w1   ),
  .dc_tag_even_din_w1     (dc_tag_even_din_w1    ),
  .dc_tag_even_dout_w1    (dc_tag_even_dout_w1   ),

  .clk_tag_odd_w1         (clk_tag_odd_w1        ),
  .dc_tag_odd_cs_w1       (dc_tag_odd_cs_w1      ),
  .dc_tag_odd_we_w1       (dc_tag_odd_we_w1      ),
  .dc_tag_odd_wem_w1      (dc_tag_odd_wem_w1     ),
  .dc_tag_odd_addr_w1     (dc_tag_odd_addr_w1    ),
  .dc_tag_odd_din_w1      (dc_tag_odd_din_w1     ),
  .dc_tag_odd_dout_w1     (dc_tag_odd_dout_w1    ),

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




  .rf_cmd_valid           (rf_cmd_valid         ),
  .rf_cmd_cache           (rf_cmd_cache         ),
  .rf_cmd_excl            (rf_cmd_excl          ),
  .rf_cmd_data_size       (rf_cmd_data_size     ),
  .rf_cmd_accept          (rf_cmd_accept        ),
  .rf_cmd_read            (rf_cmd_read          ),
  .rf_cmd_addr            (rf_cmd_addr          ),
  .rf_cmd_lock            (rf_cmd_lock          ),
  .rf_cmd_prot            (rf_cmd_prot[0]       ),
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
  .cb_cmd_prot            (cb_cmd_prot[0]       ),
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
  .dccm_pct_dcbc          (dccm_pct_dcbc         ),
  .dc4_target_r           (dc4_target_r          ),
  .dc_pct_dcm             (dc_pct_dcm            ),
  .dc_pct_dclm            (dc_pct_dclm           ),
  .dc_pct_dcsm            (dc_pct_dcsm           ),
  .dc_pct_dcpm            (dc_pct_dcpm           ),
  .dc_pct_dcbc            (dc_pct_dcbc           ),
  .dc_pct_ivdc            (dc_pct_ivdc           ),
  .dc_pct_ivdl            (dc_pct_ivdl           ),
  .dc_pct_flsh            (dc_pct_flsh           ),
  .dc_pct_fldl            (dc_pct_fldl           ),
  .dc_pct_bdcmstall       (dc_pct_bdcmstall      ),

  .aux_read               (aux_read              ),  // common
  .aux_write              (aux_write             ),  // common
  .aux_wdata_r            (wa_sr_data_r          ),  // common
  .aux_dc_ren_r           (aux_dc_ren_r          ),
  .aux_dc_raddr_r         (aux_dc_raddr_r        ),
  .aux_dc_wen_r           (aux_dc_wen_r          ),
  .aux_dc_waddr_r         (aux_dc_waddr_r        ),

  .aux_dc_rdata           (dc_aux_rdata          ),
  .aux_dc_illegal         (dc_aux_illegal        ),
  .aux_dc_k_rd            (dc_aux_k_rd           ),
  .aux_dc_k_wr            (dc_aux_k_wr           ),
  .aux_dc_unimpl          (dc_aux_unimpl         ),
  .aux_dc_serial_sr       (dc_aux_serial_sr      ),
  .aux_dc_strict_sr       (dc_aux_strict_sr      ),
  .aux_dc_busy            (dc_aux_busy           ),


  .aux_dc_x2_addr_pass    (dc2_addr_pass         ),
  .aux_dc_x2_addr         (dc2_aux_addr          ),

  .aux_dccm_ren_r         (aux_dccm_ren_r        ),
  .aux_dccm_wen_r         (aux_dccm_wen_r        ),

  .aux_dccm_rdata         (dccm_aux_rdata        ),
  .aux_dccm_illegal       (dccm_aux_illegal      ),
  .aux_dccm_k_rd          (dccm_aux_k_rd         ),
  .aux_dccm_k_wr          (dccm_aux_k_wr         ),
  .aux_dccm_unimpl        (dccm_aux_unimpl       ),
  .aux_dccm_serial_sr     (dccm_aux_serial_sr    ),
  .aux_dccm_strict_sr     (dccm_aux_strict_sr    ),

  .aux_dccm_r             (dccm_base_r           ),
  .aux_dper_ren_r         (aux_dper_ren_r        ),
  .aux_dper_raddr_r       (aux_dper_raddr_r      ),
  .aux_dper_wen_r         (aux_dper_wen_r        ),
  .aux_dper_waddr_r       (aux_dper_waddr_r      ),

  .aux_dper_rdata         (dper_aux_rdata        ),
  .aux_dper_illegal       (dper_aux_illegal      ),
  .aux_dper_k_rd          (dper_aux_k_rd         ),
  .aux_dper_k_wr          (dper_aux_k_wr         ),
  .aux_dper_unimpl        (dper_aux_unimpl       ),
  .aux_dper_serial_sr     (dper_aux_serial_sr    ),
  .aux_dper_strict_sr     (dper_aux_strict_sr    ),


  .idle_req               (hlt_wait_idle         ),
  .dmp_idle_r             (dmp_idle_r            ),
  .dmp_idle1_r            (dmp_idle1_r           ),
  .dmp_queue_empty        (dmp_queue_empty       ),
  .dmp_wr_pending_r       (dmp_wr_pending_r      ),
  .dmp_aux_pending_r      (dmp_aux_pending_r     ),

  .dmp_unit_enable        (dmp_unit_enable       ),
  .dmp_dmu_unit_enable    (dmp_dmu_unit_enable   ),
  .dmp_lq_unit_enable     (dmp_lq_unit_enable    ),

  .x3_db_exception        (x3_1_db_exception     ),
  .db_active_r            (db_active_r           ),
  .db_exception_r         (ca_db_exception       ),


  ////////// Interface to dtlb //////////////////////////////////////////////
  //
  .mmu_en_r               (mmu_en_r),         // Enable TLB lookups
  .mpu_en_r               (mpu_en_r),
  .mmu_clock_req_r        (mmu_clock_req_r),
  .shared_en_r            (shared_en_r),      // Shared lib enable (PID)
  .sasid_r                (sasid_r),          // Current pid slib membership
  .asid_r                 (asid_rr),          // Current pid.asid (2cyc)

  .x2_da0_transl          (x2_da0_transl       ),

  // Consolidated dtlb update request (on miss(es))
  .dtlb_update_req        (dtlb_update_req),     // late (unreg) outputs
  .dtlb_update_req_vpn    (dtlb_update_req_vpn),

  // jtlb response to dtlb update request
  .jrsp_dtlb_update       (jrsp_dtlb_update),
  .jrsp_dtlb_update_hit   (jrsp_dtlb_update_hit),
  .jrsp_dtlb_multi_hit    (jrsp_dtlb_multi_hit),
  .jrsp_dtlb_tlb_err      (jrsp_dtlb_tlb_err_excpn),

  // insert / delete / Inval (aux) operations from jtlb
  .jtlb_dtlb_cmd_r        (jtlb_dtlb_cmd_r),    // command from jtlb (aux)
  .jtlb_dtlb_index_r      (jtlb_dtlb_index_r),  // Aux addr for read/write
  .aux_memseg_r           (aux_memseg_r         ),

  // Interface to read utlb entries
  //
  .dtlb_rd_val            (dtlb_rd_val),   // rd data reg in jtlb
  .dtlb_rd_data           (dtlb_rd_data),  // LR read data (entry)

  ////////// Shared bus to uTLBs ////////////////////////////////////////////
  //
  // Entry data for update from jtlb; also used for lookups and write by jtlb
  .jtlb_update_data       (jtlb_update_data      ),
  .wa_jtlb_lookup_start_r (wa_jtlb_lookup_start_r),
  .wa_jtlb_cancel         (wa_jtlb_cancel        ),
  .dtlb_update_pend_r     (dtlb_update_pend_r    ),
  .dc4_dtlb_miss_r        (dc4_dtlb_miss_r       ),
  .dc3_dtlb_miss_excpn_r  (dc3_dtlb_miss_excpn_r ),
  .dc3_dtlb_ovrlp_excpn_r (dc3_dtlb_ovrlp_excpn_r),
  .dc3_dtlb_protv_excpn_r (dc3_dtlb_protv_excpn_r),
  .dc3_dtlb_ecc_excpn_r   (dc3_dtlb_ecc_excpn_r  ),


  .test_mode              (test_mode              ),
  .l1_clock_active        (l1_clock_active        ),
  
  .clk                    (dmp_unit_clk           ),
  .clk_dmu                (dmp_dmu_unit_clk       ),
  .clk_lq                 (dmp_lq_unit_clk        ),
  .dbg_cache_rst_disable_r (dbg_cache_rst_disable_r),
  .dccm_dmi_priority      (dccm_dmi_priority_r    ),
  .rst_a                  (rst_a                  )

);






//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Module instantiation: Execution Unit                                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_exu u_alb_exu (

  ////////// General input signals ///////////////////////////////////////////
  //
  .clk                    (clk                    ),
  .rst_a                  (rst_a                  ),
  .l1_clock_active        (l1_clock_active        ), 
  .arcnum                 (arcnum                 ),
  .clusternum             (clusternum             ),
  .dmp_queue_empty        (dmp_queue_empty        ),
  .iexcpn_discarded       (iexcpn_discarded       ),
  .holdup_excpn_r         (holdup_excpn_r         ),
  .st_instrs_discarded    (st_instrs_discarded    ),

  .rtt_ca_pref            (rtt_ca_pref            ), // load with null dest for trace
  .rtt_wa_spl_ld          (rtt_wa_spl_ld          ), // Auxiliary load for trace
  .rtt_wa_store           (rtt_wa_store           ),
  .rtt_dmp_retire         (rtt_dmp_retire         ), // DMP retire for trace
  .rtt_dmp_null_ret       (rtt_dmp_null_ret       ),

  .wa_jtlb_lookup_start_r (wa_jtlb_lookup_start_r),
  .wa_jtlb_cancel         (wa_jtlb_cancel        ),
  .dc4_dtlb_miss_r        (dc4_dtlb_miss_r       ),
  .dc3_dtlb_miss_excpn_r  (dc3_dtlb_miss_excpn_r ),
  .dc3_dtlb_ovrlp_excpn_r (dc3_dtlb_ovrlp_excpn_r),
  .dc3_dtlb_protv_excpn_r (dc3_dtlb_protv_excpn_r),
  .dc3_dtlb_ecc_excpn_r   (dc3_dtlb_ecc_excpn_r  ),
  .ca_tlb_miss_excpn      (ca_tlb_miss_excpn     ),
  .ca_tlb_miss_efa        (ca_tlb_miss_efa       ),
  .ca_m_chk_excpn         (ca_m_chk_excpn        ),
  .mmu_en_r               (mmu_en_r              ),
  .mpu_en_r               (mpu_en_r              ), 
  .x2_da0_transl          (x2_da0_transl         ),
  .clk_ungated            (clk_ungated           ),  
// Library ARCv2HS-3.5.999999999


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

  ////////// Fetch-Restart Interface /////////////////////////////////////////
  //
  .fch_restart            (fch_restart            ),
  .fch_restart_vec        (fch_restart_vec        ),
  .fch_target             (fch_target             ),
  .fch_target_successor   (fch_target_successor   ),
  .fch_stop_r             (fch_stop_r             ),
  .fch_iprot_replay       (fch_iprot_replay       ),

  ////////// Instruction Issue Interface /////////////////////////////////////
  //
  .al_pass                (al_pass                ),
  .al_inst                (al_inst                ),
  .al_limm                (al_limm                ),

  .al_exception           (al_exception           ),
  .al_excpn_type          (al_excpn_type          ),
  .al_excpn_info          (al_excpn_info          ),
  .al_ifu_err_nxtpg       (al_ifu_err_nxtpg       ),
  .al_iprot_viol          (al_iprot_viol          ),
  .al_is_predicted        (al_is_predicted        ),
  .al_prediction          (al_prediction          ),
  .al_predicted_bta       (al_predicted_bta       ),
  .al_prediction_type     (al_prediction_type     ),
  .al_error_branch        (al_error_branch        ),
  .al_branch_info         (al_branch_info         ),
  .al_with_dslot          (al_with_dslot          ),

  .da_holdup              (da_holdup              ),



  .wa_rf_wenb0_r          (wa_rf_wenb0_r          ),
  ////////// Misprediction Interface /////////////////////////////////////////
  //
  .mpd_mispred            (mpd_mispred            ),
  .mpd_direction          (mpd_direction          ),
  .mpd_error_branch       (mpd_error_branch       ),
  .mpd_is_predicted       (mpd_is_predicted       ),
  .mpd_mispred_outcome    (mpd_mispred_outcome    ),
  .mpd_mispred_bta        (mpd_mispred_bta        ),
  .mpd_branch_info        (mpd_branch_info        ),
  .mpd_dslot              (mpd_dslot              ),
  .mpd_seq_next_pc        (mpd_seq_next_pc        ),
  .mpd_type               (mpd_type               ),

  .mpd_pc                 (mpd_pc                 ),
  .mpd_tail_pc_3          (mpd_tail_pc_3          ),
  .mpd_commit_size        (mpd_commit_size        ),
  .mpd_secondary          (mpd_secondary          ),
  .mpd_early              (mpd_early              ),

  ////////// Branch Commit Interface /////////////////////////////////////////
  //
  .wa_pass                (wa_pass                ),
  .wa_type                (wa_type                ),
  .wa_secondary           (wa_secondary           ),
  .wa_pc                  (wa_pc                  ),
  .wa_tail_pc_3           (wa_tail_pc_3           ),
  .wa_dslot               (wa_dslot               ),
  .wa_target              (wa_target              ),
  .wa_commit_size         (wa_commit_size         ),
  .wa_direction           (wa_direction           ),
  .wa_error_branch        (wa_error_branch        ),
  .wa_is_predicted        (wa_is_predicted        ),
  .wa_mispred_outcome     (wa_mispred_outcome     ),
  .wa_commit_mispred_bta  (wa_commit_mispred_bta  ),
  .wa_branch_info         (wa_branch_info         ),
  .wa_restart_r           (wa_restart_r           ),
  .wa_hlt_restart_r       (wa_hlt_restart_r       ),
  .wa_restart_kill_r      (wa_restart_kill_r      ),

//  .da_pass                (da_pass                ),
//  .da_kill                (da_kill                ),
//  .da_enable              (da_enable              ),
  .zol_depend_stall       (zol_depend_stall       ),

  // MPU interface for IFU
  .ifetch_addr_mpu        (ifetch_addr_mpu        ),
  .ifetch_viol            (ifetch_viol            ),

  ////////// EXU interface to DMP ////////////////////////////////////////////
  //
  .sa_dsync_op_r          (sa_dsync_op_r         ),
  .sa_dmb_op_r            (sa_dmb_op_r           ),
  .sa_dmb_dmp_stall       (sa_dmb_dmp_stall      ),
  // SA
  .sa_load_r              (sa_load_r              ),
  .sa_store_r             (sa_store_r             ),
  .dmp_aux_sr_op          (dmp_aux_sr_op          ),
  .aux_memseg_r           (aux_memseg_r           ),

  // X1
  .dc1_stall              (dc1_stall              ),
  .x1_valid_r             (x1_valid_r             ),
  .x1_pass                (x1_pass                ),
  .x1_load_r              (x1_load_r              ),
  .x1_store_r             (x1_store_r             ),
  .x1_pref_r              (x1_pref_r              ),
  .x1_cache_byp_r         (x1_cache_byp_r         ),
  .x1_size_r              (x1_size_r              ),
  .x1_mem_addr0           (x1_mem_addr0           ),
  .x1_mem_addr1           (x1_mem_addr1           ),
  .x1_addr_base           (x1_addr_base           ),
  .x1_addr_offset         (x1_addr_offset         ),
  .x1_bank_sel_lo         (x1_bank_sel_lo         ),
  .x1_bank_sel_hi         (x1_bank_sel_hi         ),
  .x1_uop_inst_r          (x1_uop_inst_r          ),
  // X2
  .dc2_stall              (dc2_stall              ),
  .dc2_addr_pass          (dc2_addr_pass          ),
  .dc2_aux_addr           (dc2_aux_addr           ),
  .x2_valid_r             (x2_valid_r             ),
  .x2_pass                (x2_pass                ),
  .x2_enable              (x2_enable              ),
  .x2_load_r              (x2_load_r              ),
  .x2_store_r             (x2_store_r             ),
  .x2_locked_r            (x2_locked_r            ),
  .x2_pref_r              (x2_pref_r              ),
  .x2_size_r              (x2_size_r              ),
  .x2_cache_byp_r         (x2_cache_byp_r         ),
  .x2_mpu_data_flt        (x2_mpu_data_flt        ),
  .x2_mem_addr_r          (x2_mem_addr_r          ),
  .x2_uop_inst_r          (x2_uop_inst_r          ),
  .x2_exu_stall           (x2_exu_stall           ),
  // X3
  .dmp_dc3_dtlb_efa       (dc3_dtlb_efa           ),
  .dmp_dc3_stall_r        (dmp_dc3_stall_r        ),
  .dmp_dc3_fast_byp       (dmp_dc3_fast_byp       ),
  .x3_valid_r             (x3_valid_r             ),
  .x3_pass                (x3_pass                ),
  .x3_enable              (x3_enable              ),
  .x3_load_r              (x3_load_r              ),
  .x3_store_r             (x3_store_r             ),
  .x3_locked_r            (x3_locked_r            ),
  .x3_pref                (x3_pref                ),
  .x3_pref_l2             (x3_pref_l2             ),
  .x3_prefw               (x3_prefw               ),
  .x3_pre_alloc           (x3_pre_alloc           ),
  .x3_cache_byp_r         (x3_cache_byp_r         ),
  .x3_size_r              (x3_size_r              ),
  .x3_sex_r               (x3_sex_r               ),
  .x3_mem_addr_r          (x3_mem_addr_r          ),
  .x3_uop_inst_r          (x3_uop_inst_r          ),
  .x3_sync_op_r           (x3_sync_op_r           ),
  .x3_brk_op_r            (x3_brk_op_r            ),
  .dc3_excpn              (dc3_excpn              ),
  .dc3_excpn_type         (dc3_excpn_type         ),
  .dc3_excpn_code         (dc3_excpn_code         ),
  // CA
  .dmp_dc4_fast_data      (dmp_dc4_fast_data      ),
  .dmp_dc4_fast_byp_r     (dmp_dc4_fast_byp_r     ),
  .dmp_dc4_fast_miss_r    (dmp_dc4_fast_miss_r    ),
  .dmp_dc4_rf_wdata_lo    (dmp_rf_wdata[`npuarc_DBL_LO_RANGE]),
  .dc4_waw_replay_r       (dc4_waw_replay_r       ),
  .dmp_dc4_stall          (dc4_stall_r            ),
  .x3_store_may_grad      (x3_store_may_grad      ),
  .ca_store_grad          (ca_store_grad          ),
  .ca_store_grad_swap     (ca_store_grad_swap     ),
  .ca_store_grad_tag_lo   (ca_store_grad_tag_lo   ),
  .ca_store_grad_tag_hi   (ca_store_grad_tag_hi   ),
  .wa_retire1_valid       (wa_retire1_valid       ),
  .wa_retire1_tag         (wa_retire1_tag         ),


  .ca_valid_r             (ca_valid_r             ),
  .ca_pass                (ca_pass                ),
  .ca_enable              (ca_enable              ),
  .ca_load_r              (ca_load_r              ),
//  .ca_pref_r              (ca_pref_r              ),
  .ca_grad_req            (ca_grad_req            ),
  .ca_store_r             (ca_store_r             ),
  .ca_size_r              (ca_size_r              ),
  .ca_sex_r               (ca_sex_r               ),
  .ca_cache_byp_r         (ca_cache_byp_r         ),
  .ca_pref                (ca_pref                ),
  .ca_pref_l2             (ca_pref_l2             ),
  .ca_prefw               (ca_prefw               ),
  .ca_pre_alloc           (ca_pre_alloc           ),
  .ca_mem_addr_r          (ca_mem_addr_r          ),
  .ca_phys_addr_r         (ca_phys_addr_r         ),
  .ca_uop_inst_r          (ca_uop_inst_r          ),
  .db_active_r            (db_active_r            ),
  .dc4_write_data_lo      (ca_wr_data_r[`npuarc_DBL_LO_RANGE]),
  .dmp_dc4_rf_wdata_hi    (dmp_rf_wdata[`npuarc_DBL_HI_RANGE]),
  .dc4_write_data_hi      (ca_wr_data_r[`npuarc_DBL_HI_RANGE]),
  // DMP replay and exceptions
  .dc4_replay             (dc4_replay             ),
  .dc4_excpn              (dc4_excpn              ),
  .dc4_excpn_user_mode_r  (dc4_excpn_user_mode_r  ),
  .dc4_excpn_mem_addr     (dc4_excpn_mem_addr     ),
  .dc4_excpn_type         (dc4_excpn_type         ),
  // DMP graduation and retirement interface
  //
  .dc4_grad_req           (dc4_grad_req           ),
  .dmp_retire_req         (dmp_retire_req         ),
  .dmp_retire_tag         (dmp_retire_tag         ),
  .ca_locked_r            (ca_locked_r            ),
  .wa_lock_flag_r         (wa_lock_flag_r         ),
  .wa_lock_double_r       (wa_lock_double_r       ),
  .wa_lpa_r               (wa_lpa_r               ),
  .dmp_scond_zflag        (dmp_scond_zflag        ),
  .dmp_clear_lf           (dmp_clear_lf           ),
  .dmp_retire_ack         (dmp_retire_ack         ),
  .rtt_dc4_scond_go       (rtt_dc4_scond_go       ),  // scond will be success
  .dmp_retire_ld_addr     (dmp_retire_va_addr     ),

  // Pending post-commit operations
  //
  .dmp_wr_pending_r       (dmp_wr_pending_r       ),
  .dmp_aux_pending_r      (dmp_aux_pending_r      ),

  ////////// Common graduation interface /////////////////////////////////////
  //
  .ca_grad_ack            (ca_grad_ack            ),
  .ca_grad_tag            (ca_grad_tag            ),

  ////////// Bus error exception acknowledgement /////////////////////////////
  //
  .mem_excpn_ack_r        (mem_excpn_ack_r        ),


  ////////// Exception exit /////////////////////////////////////////////////
  //
  .excpn_exit_evt        (excpn_exit_evt          ),

  .wdt_x3_stall           ( wdt_x3_stall         ),
  .x3_kill                ( x3_kill              ),

  ////////// EXU AUX. Interface //////////////////////////////////////////////
  //

  .aux_read           (aux_read            ),
  .aux_write          (aux_write           ),
  .wa_sr_data_r       (wa_sr_data_r        ),

  .intvbase_in        (intvbase_in         ),


  
  .do_aux_replay_r    (do_aux_replay_r     ),
  .aux_dccm_ren_r     (aux_dccm_ren_r     ),
  .aux_dccm_wen_r     (aux_dccm_wen_r     ),
  .dccm_aux_rdata     (dccm_aux_rdata     ),
  .dccm_aux_illegal   (dccm_aux_illegal   ),
  .dccm_aux_k_rd      (dccm_aux_k_rd      ),
  .dccm_aux_k_wr      (dccm_aux_k_wr      ),
  .dccm_aux_unimpl    (dccm_aux_unimpl    ),
  .dccm_aux_serial_sr (dccm_aux_serial_sr ),
  .dccm_aux_strict_sr (dccm_aux_strict_sr ),

  .aux_dper_ren_r     (aux_dper_ren_r     ),
  .aux_dper_raddr_r   (aux_dper_raddr_r   ),
  .aux_dper_wen_r     (aux_dper_wen_r     ),
  .aux_dper_waddr_r   (aux_dper_waddr_r   ),
  .dper_aux_rdata     (dper_aux_rdata     ),
  .dper_aux_illegal   (dper_aux_illegal   ),
  .dper_aux_k_rd      (dper_aux_k_rd      ),
  .dper_aux_k_wr      (dper_aux_k_wr      ),
  .dper_aux_unimpl    (dper_aux_unimpl    ),
  .dper_aux_serial_sr (dper_aux_serial_sr ),
  .dper_aux_strict_sr (dper_aux_strict_sr ),

  .aux_dc_ren_r       (aux_dc_ren_r       ),
  .aux_dc_raddr_r     (aux_dc_raddr_r     ),
  .aux_dc_wen_r       (aux_dc_wen_r       ),
  .aux_dc_waddr_r     (aux_dc_waddr_r     ),
  .dc_aux_rdata       (dc_aux_rdata       ),
  .dc_aux_illegal     (dc_aux_illegal     ),
  .dc_aux_k_rd        (dc_aux_k_rd        ),
  .dc_aux_k_wr        (dc_aux_k_wr        ),
  .dc_aux_unimpl      (dc_aux_unimpl      ),
  .dc_aux_serial_sr   (dc_aux_serial_sr   ),
  .dc_aux_strict_sr   (dc_aux_strict_sr   ),
  .dc_aux_busy        (dc_aux_busy        ),

  .aux_ic_ren_r       (aux_ic_ren_r       ),
  .aux_ic_raddr_r     (aux_ic_raddr_r     ),
  .aux_ic_wen_r       (aux_ic_wen_r       ),
  .aux_ic_waddr_r     (aux_ic_waddr_r     ),
  .ic_aux_rdata       (ic_aux_rdata       ),
  .ic_aux_illegal     (ic_aux_illegal     ),
  .ic_aux_k_rd        (ic_aux_k_rd        ),
  .ic_aux_k_wr        (ic_aux_k_wr        ),
  .ic_aux_unimpl      (ic_aux_unimpl      ),
  .ic_aux_serial_sr   (ic_aux_serial_sr   ),
  .ic_aux_strict_sr   (ic_aux_strict_sr   ),

  .aux_bpu_ren_r      (aux_bpu_ren_r      ),
  .aux_bpu_raddr_r    (aux_bpu_raddr_r    ),
  .aux_bpu_wen_r      (aux_bpu_wen_r      ),
  .aux_bpu_waddr_r    (aux_bpu_waddr_r    ),
  .bpu_aux_rdata      (bpu_aux_rdata      ),
  .bpu_aux_illegal    (bpu_aux_illegal    ),
  .bpu_aux_k_rd       (bpu_aux_k_rd       ),
  .bpu_aux_k_wr       (bpu_aux_k_wr       ),
  .bpu_aux_unimpl     (bpu_aux_unimpl     ),
  .bpu_aux_serial_sr  (bpu_aux_serial_sr  ),
  .bpu_aux_strict_sr  (bpu_aux_strict_sr  ),

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

  .aux_timer_active   (aux_timer_active   ),    
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
  .rtc_na             (rtc_na             ),

  .aux_pct_active     (aux_pct_active     ),      
  .aux_pct_ren_r      (aux_pct_ren_r      ),
  .aux_pct_raddr_r    (aux_pct_raddr_r    ),
  .aux_pct_wen_r      (aux_pct_wen_r      ),
  .aux_pct_waddr_r    (aux_pct_waddr_r    ),
  .pct_aux_rdata      (pct_aux_rdata      ),
  .pct_aux_illegal    (pct_aux_illegal    ),
  .pct_aux_k_rd       (pct_aux_k_rd       ),
  .pct_aux_k_wr       (pct_aux_k_wr       ),
  .pct_aux_unimpl     (pct_aux_unimpl     ),
  .pct_aux_serial_sr  (pct_aux_serial_sr  ),
  .pct_aux_strict_sr  (pct_aux_strict_sr  ),

  .aux_mmu_ren_r      (aux_mmu_ren_r      ),
  .aux_mmu_raddr_r    (aux_mmu_raddr_r    ),
  .aux_mmu_wen_r      (aux_mmu_wen_r      ),
  .aux_mmu_waddr_r    (aux_mmu_waddr_r    ),
  .mmu_aux_rdata      (mmu_aux_rdata      ),
  .mmu_aux_illegal    (mmu_aux_illegal    ),
  .mmu_aux_k_rd       (mmu_aux_k_rd       ),
  .mmu_aux_k_wr       (mmu_aux_k_wr       ),
  .mmu_aux_unimpl     (mmu_aux_unimpl     ),
  .mmu_aux_serial_sr  (mmu_aux_serial_sr  ),
  .mmu_aux_strict_sr  (mmu_aux_strict_sr  ),

  .ar_save_clk    (ar_save_clk  ),
  .ar_save_en_r   (ar_save_en_r ),

  .ar_aux_debug_r     (ar_aux_debug_r        ),
  .ar_aux_status32_r  (ar_aux_status32_r     ),
  .ar_aux_irq_act_r   (ar_aux_irq_act_r      ),
  .ar_aux_lp_start_r  (ar_aux_lp_start_r     ),

  .da_eslot_stall     (da_eslot_stall        ),
  .da_uop_stall       (da_uop_stall          ),
  .x1_dslot_stall     (x1_dslot_stall        ),
  .sa_flag_stall      (sa_flag_stall         ),
  .sa_stall_r15          ( sa_stall_r15        ),
  .sa_stall_r1        (sa_stall_r1           ),
  .sa_acc_raw         (sa_acc_raw            ),
  .ca_acc_waw         (ca_acc_waw            ),
  .dep_bdcmstall      (dep_bdcmstall         ),

  .ca_lp_lpcc_evt     (ca_lp_lpcc_evt        ),
  .ca_br_taken        (ca_br_taken           ),
  .ca_lr_op_r         (ca_lr_op_r            ),
  .ca_sr_op_r         (ca_sr_op_r            ),
  .ca_q_field_r       (ca_q_field_r          ),
  .ca_byte_size_r     (ca_byte_size_r        ),
  .ca_hit_lp_end      (ca_hit_lp_end         ),
  .ca_has_limm_r      (ca_has_limm_r         ),
  .ca_is_16bit_r      (ca_is_16bit_r         ),

  .ca_br_jmp_op       (ca_br_jmp_op          ),
  .ca_jump_r          (ca_jump_r             ),
  .ca_bcc_r           (ca_bcc_r              ),
  .ca_brcc_bbit_r     (ca_brcc_bbit_r        ),
  .ca_zol_branch      (ca_zol_branch         ),
  .ca_sleep_evt       (ca_sleep_evt          ),
  .ar_pc_r              (ar_pc_r             ),
  .commit_normal_evt    (commit_normal_evt   ),
  .ca_dslot_r           (ca_dslot_r          ),
  .excpn_evts           (excpn_evts          ),
  .int_evts             (int_evts            ),

  .ar_aux_lp_end_r      (ar_aux_lp_end_r     ),
  .ca_trap_op_r         (ca_trap_op_r        ),
  .ar_aux_ecr_r         (ar_aux_ecr_r        ),

  .ca_cmt_dbg_evt       (ca_cmt_dbg_evt      ),
  .ca_zol_lp_jmp        (ca_zol_lp_jmp       ),
  .rtt_src_num          (rtt_src_num         ),
  .ar_pc_nxt            (ar_pc_nxt           ),
  .wa_aux_status32_nxt  (wa_aux_status32_nxt ),
  .ca_cond_inst         (ca_cond_inst        ),
  .ca_cond_met          (ca_cond_met         ),

  .aux_rtt_active       (aux_rtt_active      ),
  .aux_rtt_ren_r        (aux_rtt_ren_r       ),
  .aux_rtt_raddr_r      (aux_rtt_raddr_r     ),
  .aux_rtt_wen_r        (aux_rtt_wen_r       ),
  .aux_rtt_waddr_r      (aux_rtt_waddr_r     ),
  .rtt_aux_rdata        (rtt_aux_rdata       ),
  .rtt_aux_illegal      (rtt_aux_illegal     ),
  .rtt_aux_k_rd         (rtt_aux_k_rd        ),
  .rtt_aux_k_wr         (rtt_aux_k_wr        ),
  .rtt_aux_unimpl       (rtt_aux_unimpl      ),
  .rtt_aux_serial_sr    (rtt_aux_serial_sr   ),
  .rtt_aux_strict_sr    (rtt_aux_strict_sr   ),

  .ca_br_or_jmp_all     (ca_br_or_jmp_all    ),
  .ca_indir_br          (ca_indir_br         ),
  .ca_in_deslot         (ca_in_deslot        ),
  .ca_in_eslot_r        (ca_in_eslot_r       ),
  .rtt_leave_uop_cmt      (rtt_leave_uop_cmt     ),
  .ca_cmt_brk_inst      (ca_cmt_brk_inst     ),
  .ca_cmt_isi_evt       (ca_cmt_isi_evt      ),
  .dbg_halt_r           (dbg_halt_r          ),

  .da_rtt_stall_r       (da_rtt_stall_r      ),

  .aps_status           (aps_status          ),
  .aps_excpn            (aps_excpn           ),
  .aps_active      (aps_active      ),
  .aps_halt        (aps_halt       ),
  .aps_break       (aps_break      ),
  .wa_lr_op_r           (wa_lr_op_r          ),
  .wa_sr_op_r           (wa_sr_op_r          ),
  .wa_aux_addr_r        (wa_aux_addr_r       ),

  .wa_rf_wa0_r          (wa_rf_wa0_r         ),
  .wa_rf_wa1_r          (wa_rf_wa1_r         ),
  .wa_rf_wenb1_r        (wa_rf_wenb1_r       ),

  .wa_rf_wenb0_64_r     (wa_rf_wenb0_64_r    ),
  .wa_rf_wenb1_64_r     (wa_rf_wenb1_64_r    ),


  .ap_tkn          (ap_tkn         ),

  .wa_rf_wdata0_lo_r    (wa_rf_wdata0_lo_r   ),
  .wa_rf_wdata0_hi_r    (wa_rf_wdata0_hi_r   ),
  .wa_rf_wdata1_lo_r    (wa_rf_wdata1_lo_r   ),
  .wa_rf_wdata1_hi_r    (wa_rf_wdata1_hi_r   ),


  .aux_rs_valid          (aux_rs_valid          ), //
  .aux_rs_region         (aux_rs_region         ), //
  .aux_rs_addr           (aux_rs_addr           ), //
  .aux_rs_read           (aux_rs_read           ), //
  .aux_rs_write          (aux_rs_write          ), //
  .aux_rs_data           (aux_rs_data           ), //
  .aux_rs_status         (aux_rs_status         ), //
  .aux_rs_accept         (aux_rs_accept         ), //

  .aux_wr_valid          (aux_wr_valid          ), //
  .aux_wr_region         (aux_wr_region         ), //
  .aux_wr_addr           (aux_wr_addr           ), //
  .aux_wr_data           (aux_wr_data           ), //
  .aux_wr_allow          (aux_wr_allow          ), //
  .aux_cm_phase          (aux_cm_phase          ), //
  .aux_cm_valid          (aux_cm_valid          ), //


  // halt status
  .dbg_bh_r             (dbg_bh_r            ),
  .dbg_sh_r             (dbg_sh_r            ),
  .dbg_eh_r             (dbg_eh_r            ),
  .dbg_ah_r             (dbg_ah_r            ),
  .dbg_ra_r             (dbg_ra_r            ),

  .ecc_flt_status     (ecc_flt_status      ),  // ECC
  .ar_aux_ecc_ctrl_r  (ar_aux_ecc_ctrl_r   ),  // ECC
  .ecc_sbe_count_r    (ecc_sbe_count_r     ), // ECC single bit error count
  .ecc_sbe_clr        (ecc_sbe_clr         ),
  .ecc_sbe_dmp_clr    (ecc_sbe_dmp_clr     ),
  .ar_user_mode_r     (ar_user_mode_r      ),  //

  ////////// Interrupt signals ///////////////////////////////////////////////
  //
  .timer0_irq_1h      (timer0_irq_1h       ),

  .wdt_int_timeout_1h_r      (wdt_int_timeout_1h_r  ),

  .pct_int_overflow_r        (pct_int_overflow_r    ),
  .irq_clk_en_r          (irq_clk_en_r            ),



  .irq_r                 (irq_r              ),

  .irq_preempts_nxt      (irq_preempts_nxt        ),

  //.clk_resync            (clk_resync              ),
 // .irq_sync_req_a        (irq_sync_req_a          ),


  .db_active             (db_active               ),

  ////////// Debug Interface /////////////////////////////////////////////////
  //
  .dbg_cmdval            (dbg_cmdval              ),
  .dbg_cmdack            (dbg_cmdack              ),
  .dbg_address           (dbg_address             ),
  .dbg_be                (dbg_be                  ),
  .dbg_cmd               (dbg_cmd                 ),
  .dbg_wdata             (dbg_wdata               ),
  .dbg_rspack            (dbg_rspack              ),
  .dbg_rspval            (dbg_rspval              ),
  .dbg_rdata             (dbg_rdata               ),
  .dbg_reop              (dbg_reop                ),
  .dbg_rerr              (dbg_rerr                ),
  ////////// APB debug interface /////////////////////////////////////////////

  .dbg_prot_sel          (dbg_prot_sel            ),
  .pclkdbg_en            (pclkdbg_en              ),
  .presetdbgn            (presetdbgn              ),
  .paddrdbg              (paddrdbg                ),
  .pseldbg               (pseldbg                 ),
  .penabledbg            (penabledbg              ),
  .pwritedbg             (pwritedbg               ),
  .pwdatadbg             (pwdatadbg               ),
  .preadydbg             (preadydbg               ),
  .prdatadbg             (prdatadbg               ),
  .pslverrdbg            (pslverrdbg              ),

  .dbgen                 (dbgen                   ),
  .niden                 (niden                   ),

  .debug_reset           (debug_reset             ),
  .db_clock_enable_nxt   (db_clock_enable_nxt     ),
  .ar_clock_enable_r     (ar_clock_enable_r       ),
  .x3_1_db_exception     (x3_1_db_exception       ),
  .ca_db_exception       (ca_db_exception         ),


  ////////// Unit-level clock gating control outputs to clock_ctrl ///////////
  //
  .mpy_unit_enable       (mpy_unit_enable         ),
  .mpy_unit_clk          (mpy_unit_clk            ),
  .div_unit_enable       (div_unit_enable         ),
  .div_unit_clk          (div_unit_clk            ),
  .smt_unit_enable       (smt_unit_enable         ),  
  .smt_unit_clk          (smt_unit_clk            ),  
  .ap_unit_enable        (ap_unit_enable          ),
  .ap_unit_clk           (ap_unit_clk             ),
  .aux_aps_active        (aux_aps_active           ),
  .ap_aux_clk            (ap_aux_clk               ),

  ////////// IFU/DMP/BIU Halt Interface //////////////////////////////////////
  //
  .hlt_wait_idle         (hlt_wait_idle           ),

  .ifu_idle_r            (ifu_idle_r              ),
  .dmp_idle_r            (dmp_idle_r              ),
  .dmp_idle1_r           (dmp_idle1_r             ),
  .biu_idle_r            (biu_idle                ),

  .hor_clock_enable_nxt (hor_clock_enable_nxt     ),  //


  ////////// External Event Interface /////////////////////////////////////////
  //
  .arc_event_r           (arc_event_r             ),
  .wake_from_wait        (wake_from_wait          ),




  ////////// External Halt Interface /////////////////////////////////////////
  //
  .gb_sys_halt_req_r     (gb_sys_halt_req_r       ),
  .gb_sys_halt_ack_r     (gb_sys_halt_ack_r       ),
  //
  .gb_sys_run_req_r      (gb_sys_run_req_r        ),
  .gb_sys_run_ack_r      (gb_sys_run_ack_r        ),
  //
  .gb_sys_halt_r         (gb_sys_halt_r           ),
  .gb_sys_tf_halt_r      (gb_sys_tf_halt_r        ),
  .gb_sys_sleep_r        (gb_sys_sleep_r          ),

  .sync_dsync_dmb_stall  (sync_dsync_dmb_stall    ),

  .gb_sys_sleep_mode_r   (gb_sys_sleep_mode_r     )

); // instance : u_alb_exu





// Tie unused signals
//
assign ifu_ibus_cmd_prot[1]      = 1'b1;

assign rf_cmd_prot[1]            = 1'b0;
assign cb_cmd_prot[1]            = 1'b0;







////////////////////////////////////////////////////////////////////////////
// Module instantiation - PCT                                             //
////////////////////////////////////////////////////////////////////////////

wire any_store_grad;
assign any_store_grad = (|ca_store_grad);

npuarc_alb_pct         u_alb_pct (
  .clk                  (pct_unit_clk         ),
  .pct_unit_enable      (pct_unit_enable      ),
  .rst_a                (rst_a                ),
  .irq_clk_en_r         (irq_clk_en_r         ),
  // pct envent for sync/dsync/dmb stall
  .sync_dsync_dmb_stall (sync_dsync_dmb_stall ),
  .icm                  (icm                  ),
  .icll                 (icll                 ),
  .icoff                (icoff                ),
  .ivic                 (ifu_ivic             ),
  .ivil                 (ifu_ivil             ),
  .icwpm                (icwpm                ),
  .ifu_issue_stall_r    (ifu_issue_stall_r    ),
  .ifu_brch_mispred_r   (ifu_brch_mispred_r   ),
  .ifu_cond_mispred_r   (ifu_cond_mispred_r   ),
  .ifu_bta_mispred_r    (ifu_bta_mispred_r    ),
  .ifu_missing_pred_r   (ifu_missing_pred_r   ),
  .ifu_late_br_mispred  (ifu_late_br_mispred  ),
  .ifu_error_branch_r   (ifu_error_branch_r   ),
  .ifu_branch_cache_miss (ifu_branch_cache_miss),
  .ifu_bit_error_r      (ifu_bit_error_r      ),
  .icm_stall            (1'b0                 ),
  .ar_aux_ecr_r         (ar_aux_ecr_r         ),
  .dccmbc               (dccm_pct_dcbc        ),
  .dcm                  (dc_pct_dcm           ),
  .dclm                 (dc_pct_dclm          ),
  .dcsm                 (dc_pct_dcsm          ),
  .dcpm                 (dc_pct_dcpm          ),
  .dcbc                 (dc_pct_dcbc          ),
  .ivdc                 (dc_pct_ivdc          ),
  .ivdl                 (dc_pct_ivdl          ),
  .flsh                 (dc_pct_flsh          ),
  .fldl                 (dc_pct_fldl          ),
  .dc_bdcmstall         (dc_pct_bdcmstall     ),
  .dep_bdcmstall        (dep_bdcmstall        ),
  .da_eslot_stall       (da_eslot_stall       ),
  .da_uop_stall         (da_uop_stall         ),
  .db_active_r          (db_active_r          ),
  .dc1_stall            (dc1_stall            ),
  .dc2_stall            (dc2_stall            ),
  .dc4_stall_r          (dc4_stall_r          ),
  .bzolcnt              (zol_depend_stall     ),

  .bauxflsh             (bauxflsh             ),



  .sa_flag_stall        (sa_flag_stall        ),
  .sa_stall_r15          ( sa_stall_r15        ),
  .sa_stall_r1          (sa_stall_r1          ),
  .sa_acc_raw           (sa_acc_raw           ),

  .x1_dslot_stall       (x1_dslot_stall       ),



  .ca_pass              (ca_pass              ),
  .ca_normal_evt        (commit_normal_evt    ),
  .ca_sleep_evt         (ca_sleep_evt         ),
  .ca_lp_lpcc_evt       (ca_lp_lpcc_evt          ),
  .ca_br_taken          (ca_br_taken          ),
  .ca_acc_waw           (ca_acc_waw           ),
  .ca_dslot_r           (ca_dslot_r           ),
  .ca_trap_op_r         (ca_trap_op_r         ),
  .ca_load_r            (ca_load_r            ),
  .ca_store_r           (ca_store_r           ),
  .dc4_pref_r           (dc4_pref_r           ),
  .ca_target_r          (dc4_target_r         ),
  .ca_lr_op_r           (ca_lr_op_r           ),
  .ca_sr_op_r           (ca_sr_op_r           ),
  .ca_has_limm_r        (ca_has_limm_r        ),
  .ca_is_16bit_r        (ca_is_16bit_r        ),
  .ca_br_jmp_op         (ca_br_jmp_op         ),
  .ca_jump_r            (ca_jump_r            ),
  .ca_bcc_r             (ca_bcc_r             ),
  .ca_brcc_bbit_r       (ca_brcc_bbit_r       ),
  .ca_zol_branch        (ca_zol_branch        ),
  .ca_q_field_r         (ca_q_field_r         ),
  .ca_byte_size_r       (ca_byte_size_r       ),
  .ca_hit_lp_end        (ca_hit_lp_end        ),
  .ca_locked_r          (ca_locked_r          ),

  .wa_restart_r         (wa_restart_r         ),

  .ar_aux_lp_start_r    (ar_aux_lp_start_r    ),
  .ar_aux_lp_end_r      (ar_aux_lp_end_r      ),

  .excpn_evts           (excpn_evts           ),
  .int_evts             (int_evts             ),

  .ar_pc_r               (ar_pc_r             ),
  .ar_aux_status32_r     (ar_aux_status32_r   ),
  .ar_aux_debug_r        (ar_aux_debug_r      ),
  .ar_aux_irq_act_r      (ar_aux_irq_act_r    ),
  .pct_int_overflow_r    (pct_int_overflow_r  ),
  
  .aux_pct_active        (aux_pct_active      ),
  .aux_pct_ren_r         (aux_pct_ren_r       ),
  .aux_pct_raddr_r       (aux_pct_raddr_r     ),
  .aux_read              (aux_read            ),
  .aux_write             (aux_write           ),
  .aux_pct_wen_r         (aux_pct_wen_r       ),
  .aux_pct_waddr_r       (aux_pct_waddr_r     ),
  .wa_sr_data_r          (wa_sr_data_r        ),
  .pct_aux_rdata         (pct_aux_rdata       ),
  .pct_aux_illegal       (pct_aux_illegal     ),
  .pct_aux_k_rd          (pct_aux_k_rd        ),
  .pct_aux_k_wr          (pct_aux_k_wr        ),
  .pct_aux_unimpl        (pct_aux_unimpl      ),
  .pct_aux_serial_sr     (pct_aux_serial_sr   ),
  .pct_aux_strict_sr     (pct_aux_strict_sr   )
); // alb_pct

////////////////////////////////////////////////////////////////////////////
// Module instantiation - MMU                                             //
////////////////////////////////////////////////////////////////////////////

npuarc_jtlb u_jtlb (

  ////////// General input signals ///////////////////////////////////////////
  //
  .clk                          (clk),              // Processor clock
  .rst_a                        (rst_a),            // Global reset
  .rst_init_disable_r           (dbg_cache_rst_disable_r),
  .mmu_ready                    (mmu_ready),        // Clear on reset, set when
                                                    // mmu ready for operation
  .mmu_en_r                     (mmu_en_r),         // Enable TLB lookups
  .mmu_clock_req_r              (mmu_clock_req_r),  // MMU clock request
  .mmu_cmd_active               (mmu_cmd_active),
  // Access type: user/kernel mode, pid shared bit (common to all req ports)
  .debug_op                     (db_active_r),      // ld/st originated from debug
  .kernel_mode                  (kernel_mode),      // has Kernel mode privileges

  .shared_en_r                  (shared_en_r),      // Shared lib enable (PID)
  .sasid_r                      (sasid_r),          // Current pid slib membership
  .asid_rr                      (asid_rr),          // Current pid.asid (2cyc)
  .asid_r                       (asid_r),           // Current pid.asid
  .asid_wr_en                   (asid_wr_en),       // pid update

  // NTLB PD0 (tag) ram interface
  .ntlb_pd0_clk                 (ntlb_pd0_clk),
  .ntlb_pd0_ram_ce              (ntlb_pd0_ce),
  .ntlb_pd0_ram_we              (ntlb_pd0_we),
  .ntlb_pd0_ram_wem             (ntlb_pd0_wem),
  .ntlb_pd0_ram_addr            (ntlb_pd0_addr),
  .ntlb_pd0_ram_wdata           (ntlb_pd0_wdata),
  .ntlb_pd0_ram_rdata           (ntlb_pd0_rdata),

  // NTLB PD1 (data) ram interface
  .ntlb_pd1_clk                 (ntlb_pd1_clk),
  .ntlb_pd1_ram_ce              (ntlb_pd1_ce),
  .ntlb_pd1_ram_we              (ntlb_pd1_we),
  .ntlb_pd1_ram_addr            (ntlb_pd1_addr),
  .ntlb_pd1_ram_wdata           (ntlb_pd1_wdata),
  .ntlb_pd1_ram_rdata           (ntlb_pd1_rdata),

 ////////////////Bist interface /////////////////////////////////////////////


  ////////// AUX interface //////////////////////////////////////////////////
  //
  ////////// Interface for SR instructions to write aux regs ////////////////
  //                    (WA stage)
  .aux_mmu_wen_r                (aux_mmu_wen_r),    // (WA) Aux write enable
  .aux_mmu_waddr_r              (aux_mmu_waddr_r),  // (WA) Aux write Address
  .aux_wdata                    (wa_sr_data_r),     // (WA) Aux write data

  ////////// Interface for aux address / perm checks and aux read ///////////
  //                    (X3 stage)
  .aux_write                    (aux_write),        // (X3) Aux write operation
  .aux_read                     (aux_read),         // (X3) Aux read operation
  .aux_mmu_ren_r                (aux_mmu_ren_r),    // (X3) Aux unit select
  .aux_mmu_raddr_r              (aux_mmu_raddr_r),  // (X3) Aux address (rd/wr)

  .mmu_aux_rdata                (mmu_aux_rdata),    // (X3) LR read data
  .mmu_aux_illegal              (mmu_aux_illegal),  // (X3) SR/LR op is illegal
  .mmu_aux_k_rd                 (mmu_aux_k_rd),     // (X3) op needs Kernel R perm
  .mmu_aux_k_wr                 (mmu_aux_k_wr),     // (X3) op needs Kernel W perm
  .mmu_aux_unimpl               (mmu_aux_unimpl),   // (X3) LR/SR reg is not present
  .mmu_aux_serial_sr            (mmu_aux_serial_sr),// (X3) SR group flush
  .mmu_aux_strict_sr            (mmu_aux_strict_sr),// (X3) SR single flush
  .mmu_aux_index_ecc_e          (mmu_aux_index_ecc_e),

  ////////// Interface to itlb //////////////////////////////////////////////
  //
  // itlb update request (on miss)
  .ifu_clk2_en                  (ifu_clk2_en),
  .itlb_update_req              (itlb_update_req),     // late (unreg) outputs
  .itlb_update_req_vpn          (itlb_update_req_vpn),

  // jtlb response to itlb update request
  .jrsp_itlb_update_nxt         (jrsp_itlb_update_nxt),
  .jrsp_itlb_update             (jrsp_itlb_update),
  .jrsp_itlb_update_hit         (jrsp_itlb_update_hit),
  .jrsp_itlb_multi_hit          (jrsp_itlb_multi_hit),
  .jrsp_itlb_tlb_err            (jrsp_itlb_tlb_err),

  // insert / delete / Inval (aux) operations from jtlb
  .jtlb_itlb_cmd_r              (jtlb_itlb_cmd_r),   // command from jtlb (aux)
  .jtlb_itlb_index_r            (jtlb_itlb_index_r), // Aux addr for read/write

  // Interface to read utlb entries
  //
  .itlb_rd_val                  (itlb_rd_val),   // rd data reg in jtlb
  .itlb_rd_data                 (itlb_rd_data),  // LR read data (entry)

  ////////// Interface to dtlb //////////////////////////////////////////////
  //
  // Consolidated dtlb update request (on miss(es))
  .dtlb_update_req              (dtlb_update_req),     // late (unreg) outputs
  .dtlb_update_req_vpn          (dtlb_update_req_vpn),

  // jtlb response to dtlb update request
  .jrsp_dtlb_update             (jrsp_dtlb_update),
  .jrsp_dtlb_update_hit         (jrsp_dtlb_update_hit),
  .jrsp_dtlb_multi_hit          (jrsp_dtlb_multi_hit),
  .jrsp_dtlb_tlb_err            (jrsp_dtlb_tlb_err),

  // insert / delete / Inval (aux) operations from jtlb
  .jtlb_dtlb_cmd_r              (jtlb_dtlb_cmd_r),    // command from jtlb (aux)
  .jtlb_dtlb_index_r            (jtlb_dtlb_index_r),  // Aux addr for read/write

  // Interface to read utlb entries
  //
  .dtlb_rd_val                  (dtlb_rd_val),   // rd data reg in jtlb
  .dtlb_rd_data                 (dtlb_rd_data),  // LR read data (entry)

  ////////// Shared bus to uTLBs ////////////////////////////////////////////
  //
  .ecc_mmu_disable              (ecc_mmu_disable       ),
  .ecc_mmu_sbe_count_r          (ecc_mmu_sbe_count_r   ),
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


  .mmu_ecc_sbe_clr              (mmu_ecc_sbe_clr       ),
  
  
  
  // Entry data for update from jtlb; also used for lookups and write by jtlb
  .jtlb_update_data             (jtlb_update_data      ),

  .wa_jtlb_lookup_start_r       (wa_jtlb_lookup_start_r),
  .wa_restart_r                 (wa_restart_r          ),
  .wa_jtlb_cancel               (wa_jtlb_cancel        ),
  .dtlb_update_pend_r           (dtlb_update_pend_r    ),

  .ca_tlb_miss_excpn            (ca_tlb_miss_excpn     ),
  .ca_tlb_miss_efa              (ca_tlb_miss_efa       ),
  .ca_m_chk_excpn               (ca_m_chk_excpn        )
);






endmodule // alb_core
