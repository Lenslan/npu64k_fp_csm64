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
//  ###   ####   #   #
// #   #  #   #  #   #
// #      #   #  #   #
// #      ####   #   #
// #      #      #   #
// #   #  #      #   #
//  ###   #       ###
//
// ===========================================================================
//
// @f:cpu
//
// Description:
// @p
//  The |cpu| module instantiates and connects up the major subsystems within
//  the CPU. This includes the main integer pipeline (|pipe|) and the data
//  memory pipeline (|dmp|). This is a purely structural Verilog module,
//  containing no actual logic.
// @e
//
// ===========================================================================

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

module npuarc_alb_cpu (




  ////////// External Event Interface /////////////////////////////////////////
  //
  input                       arc_event_a,            // Async. event signal
  input                       dccm_dmi_priority,      // DCCM DMI priority
  input                       dbg_cache_rst_disable, // cache behavior at reset
  ////////// External Halt Request Interface /////////////////////////////////
  //
  input                       arc_halt_req_a,    // Async. halt req.
  input                       arc_run_req_a,     // Async. run req.
  //
  output                      arc_halt_ack,      // Sync. halt ack.
  output                      arc_run_ack,       // Sync. halt ack.



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

  input                       clk_ungated,  //to pull in ungated clock for APEX

  ////////////////////////// Interface to the I-cache RAM macros /////////////
  //
  output                      ic_tag_way0_clk,
  input   [`npuarc_IC_TRAM_RANGE]    ic_tag_dout0,     // Data from I-tag RAM0
  output  [`npuarc_IC_TRAM_RANGE]    ic_tag_din0,      // Data to I-tag RAM0
  output  [`npuarc_IC_IDX_RANGE]     ic_tag_addr0,     // Addr to I-tag RAM0
  output  [`npuarc_IC_TRAM_MASK_RANGE] ic_tag_wem0,    
  output                      ic_tag_cen0,      // CE to I-tag RAM0
  output                      ic_tag_wen0,      // WE to I-tag RAM0
  output                      ic_tag_way1_clk,
  input   [`npuarc_IC_TRAM_RANGE]    ic_tag_dout1,     // Data from I-tag RAM1
  output  [`npuarc_IC_TRAM_RANGE]    ic_tag_din1,      // Data to I-tag RAM1
  output  [`npuarc_IC_IDX_RANGE]     ic_tag_addr1,     // Addr to I-tag RAM1
  output  [`npuarc_IC_TRAM_MASK_RANGE] ic_tag_wem1,    
  output                      ic_tag_cen1,      // CE to I-tag RAM1
  output                      ic_tag_wen1,      // WE to I-tag RAM1
  output                      ic_tag_way2_clk,
  input   [`npuarc_IC_TRAM_RANGE]    ic_tag_dout2,     // Data from I-tag RAM2
  output  [`npuarc_IC_TRAM_RANGE]    ic_tag_din2,      // Data to I-tag RAM2
  output  [`npuarc_IC_IDX_RANGE]     ic_tag_addr2,     // Addr to I-tag RAM2
  output  [`npuarc_IC_TRAM_MASK_RANGE] ic_tag_wem2,    
  output                      ic_tag_cen2,      // CE to I-tag RAM2
  output                      ic_tag_wen2,      // WE to I-tag RAM2
  output                      ic_tag_way3_clk,
  input   [`npuarc_IC_TRAM_RANGE]    ic_tag_dout3,     // Data from I-tag RAM3
  output  [`npuarc_IC_TRAM_RANGE]    ic_tag_din3,      // Data to I-tag RAM3
  output  [`npuarc_IC_IDX_RANGE]     ic_tag_addr3,     // Addr to I-tag RAM3
  output  [`npuarc_IC_TRAM_MASK_RANGE] ic_tag_wem3,    
  output                      ic_tag_cen3,      // CE to I-tag RAM3
  output                      ic_tag_wen3,      // WE to I-tag RAM3
  output                        ic_data_bank0_clk, // I$ data ram clock
  input   [`npuarc_IC_BANK_WIDTH-1:0]  ic_data_dout0,  // Data from I-data RAM0
  output  [`npuarc_IC_BANK_WIDTH-1:0]  ic_data_din0,   // Data to I-data RAM0
  output  [`npuarc_IC_ADR_RANGE]       ic_data_addr0,  // Addr to I-data RAM0
  output                        ic_data_cen0,   // CE to I-data RAM0
  output                        ic_data_wen0,   // WE to I-data RAM0
  output  [`npuarc_IC_BANK_BYTE_SIZE-1:0] ic_data_wem0,
  output                        ic_data_bank1_clk, // I$ data ram clock
  input   [`npuarc_IC_BANK_WIDTH-1:0]  ic_data_dout1,  // Data from I-data RAM1
  output  [`npuarc_IC_BANK_WIDTH-1:0]  ic_data_din1,   // Data to I-data RAM1
  output  [`npuarc_IC_ADR_RANGE]       ic_data_addr1,  // Addr to I-data RAM1
  output                        ic_data_cen1,   // CE to I-data RAM1
  output                        ic_data_wen1,   // WE to I-data RAM1
  output  [`npuarc_IC_BANK_BYTE_SIZE-1:0] ic_data_wem1,


//  `if ((`HAS_SAFETY == 1) && (`ECC_SYNDROME_OPTION == 1))
  output [`npuarc_SYNDROME_MSB:0]        fs_dccm_bank0_syndrome_r,
  output [`npuarc_SYNDROME_MSB:0]       fs_dccm_bank1_syndrome_r,
  output [`npuarc_SYNDROME_MSB:0]       fs_dccm_bank2_syndrome_r,
  output [`npuarc_SYNDROME_MSB:0]       fs_dccm_bank3_syndrome_r,

  output                         fs_dccm_bank0_ecc_sb_error_r,
  output                         fs_dccm_bank1_ecc_sb_error_r,
  output                         fs_dccm_bank2_ecc_sb_error_r,
  output                         fs_dccm_bank3_ecc_sb_error_r,

  output                          fs_dccm_bank0_ecc_db_error_r,
  output                          fs_dccm_bank1_ecc_db_error_r,
  output                          fs_dccm_bank2_ecc_db_error_r,
  output                          fs_dccm_bank3_ecc_db_error_r,


  ////////// Interface with DCCM SRAMS////////////////////////////////////////
  //

  output                        clk_dccm_bank0_lo,
  output                        clk_dccm_bank0_hi,
  output                        dccm_bank0_cs_lo,
  output                        dccm_bank0_cs_hi,
  output [`npuarc_DCCM_ADDR_RANGE]     dccm_bank0_addr_lo,
  output [`npuarc_DCCM_ADDR_RANGE]     dccm_bank0_addr_hi,
  output                        dccm_bank0_we_lo,
  output                        dccm_bank0_we_hi,
  output [`npuarc_DBL_DCCM_BE_RANGE]   dccm_bank0_wem,
  output [`npuarc_DBL_DCCM_RANGE]      dccm_bank0_din,
  input  [`npuarc_DBL_DCCM_RANGE]      dccm_bank0_dout,

  output                        clk_dccm_bank1_lo,
  output                        clk_dccm_bank1_hi,
  output                        dccm_bank1_cs_lo,
  output                        dccm_bank1_cs_hi,
  output [`npuarc_DCCM_ADDR_RANGE]     dccm_bank1_addr_lo,
  output [`npuarc_DCCM_ADDR_RANGE]     dccm_bank1_addr_hi,
  output                        dccm_bank1_we_lo,
  output                        dccm_bank1_we_hi,
  output [`npuarc_DBL_DCCM_BE_RANGE]   dccm_bank1_wem,
  output [`npuarc_DBL_DCCM_RANGE]      dccm_bank1_din,
  input  [`npuarc_DBL_DCCM_RANGE]      dccm_bank1_dout,


  /////// DCCM DMI IBP interface /////////////////////////////////////////////
  //
  // leda NTL_CON37 off
  // LMD: non driving port range
  // LJ:  Not all bits of bus used
  input                         dccm_dmi_cmd_valid,
  output                        dccm_dmi_cmd_accept,
  input                         dccm_dmi_cmd_read,
  input [`npuarc_CCM_AW-1:3]           dccm_dmi_cmd_addr,

  output                        dccm_dmi_rd_valid,
  output                        dccm_dmi_err_rd,
  input                         dccm_dmi_rd_accept,
  output [`npuarc_DOUBLE_RANGE]        dccm_dmi_rd_data,

  input                         dccm_dmi_wr_valid,
  output                        dccm_dmi_wr_accept,
  input  [`npuarc_DOUBLE_RANGE]        dccm_dmi_wr_data,
  input  [`npuarc_DOUBLE_BE_RANGE]     dccm_dmi_wr_mask,
  output                        dccm_dmi_wr_done,
  output                        dccm_dmi_err_wr,
  // leda NTL_CON37 on

//  `if ((`HAS_SAFETY == 1) && (`ECC_SYNDROME_OPTION == 1))
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


  // interface to branch cache RAMs
  output [`npuarc_BR_BC_DATA_RANGE]    bc_din0,
  output [`npuarc_BR_BC_IDX_RANGE]     bc_addr0,
  output                        bc_me0,
  output                        bc_we0,
  output [`npuarc_BR_BC_DATA_RANGE]    bc_wem0,
  input  [`npuarc_BR_BC_DATA_RANGE]    bc_dout0,

  // interface to prediction table RAMs
  output [`npuarc_BR_PT_DATA_RANGE]    gs_din0,
  output [`npuarc_BR_PT_RANGE]         gs_addr0,
  output                        gs_me0,
  output                        gs_we0,
  output [`npuarc_BR_PT_DATA_RANGE]    gs_wem0,
  input  [`npuarc_BR_PT_DATA_RANGE]    gs_dout0,
  output                        bc_ram0_clk,
  output                        pt_ram0_clk,
  output                        bc_ram0_clk_en,
  output                        pt_ram0_clk_en,
  

  output [`npuarc_BR_BC_DATA_RANGE]    bc_din1,
  output [`npuarc_BR_BC_IDX_RANGE]     bc_addr1,
  output                        bc_me1,
  output                        bc_we1,
  output [`npuarc_BR_BC_DATA_RANGE]    bc_wem1,
  input  [`npuarc_BR_BC_DATA_RANGE]    bc_dout1,

  output [`npuarc_BR_PT_DATA_RANGE]    gs_din1,
  output [`npuarc_BR_PT_RANGE]         gs_addr1,
  output                        gs_me1,
  output                        gs_we1,
  output [`npuarc_BR_PT_DATA_RANGE]    gs_wem1,
  input  [`npuarc_BR_PT_DATA_RANGE]    gs_dout1,
  output                        bc_ram1_clk,
  output                        pt_ram1_clk,
  output                        bc_ram1_clk_en,
  output                        pt_ram1_clk_en,
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


  input [21:0]                intvbase_in, // for external interrupt vector base configuring




  input                                biu_dmi_clk_en_req,



  ////////// Interface to the Debug module (BVCI target) /////////////////////
  //
  input                       dbg_cmdval,  // cmdval from JTAG
  input   [`npuarc_DBG_ADDR_RANGE]   dbg_address, // address from JTAG
  input   [`npuarc_DBG_BE_RANGE]     dbg_be,      // be from JTAG
  input   [`npuarc_DBG_CMD_RANGE]    dbg_cmd,     // cmd from JTAG
  input   [`npuarc_DBG_DATA_RANGE]   dbg_wdata,   // wdata from JTAG
  input                       dbg_rspack,  // rspack from JTAG

  output                      dbg_cmdack,   // BVCI cmd acknowledge
  output                      dbg_rspval,   // BVCI response valid
  output  [`npuarc_DBG_DATA_RANGE]   dbg_rdata,    // BVCI response EOP
  output                      dbg_reop,     // BVCI response error
  output                      dbg_rerr,     // BVCI data to Debug host

  ////////// Interface to the Debug module for host control of system reset //
  //
  output                      debug_reset,    // Reset from debug host

  input                       dbg_prot_sel,

  input                       pclkdbg_en,
  input                       presetdbgn,
  input [31:2]                paddrdbg,
  input                       pseldbg,
  input                       penabledbg,
  input                       pwritedbg,
  input [31:0]                pwdatadbg,

  output                      preadydbg,
  output [31:0]               prdatadbg,
  output                      pslverrdbg,

  input                       dbgen,
  input                       niden,

  output [7:0]                cti_ap_status,
  output                      cti_ap_hit,
  output                      cti_halt,
  output                      cti_break,
  output                      cti_sleep,

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


//  `if ((`HAS_SAFETY == 1) && (`ECC_SYNDROME_OPTION == 1))
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


  input                       test_mode,
  input  [7:0]                arcnum,
  input  [7:0]                clusternum,             // for cluster_id register

//  output                      imem_clk,

  ////////// Watchdog reset output signals /////////////////////////////////
  //
  output                      watchdog_reset,     // Assert Watchdog reset

  ////////// Machine Halt Interface //////////////////////////////////////////
  //
  output                      gb_sys_halt_r,    //
  output                      gb_sys_tf_halt_r, //
  output                      gb_sys_sleep_r,   //
  output [`npuarc_EXT_SMODE_RANGE]   gb_sys_sleep_mode_r,


  ////////// RTT Programming interface ///////////////////////////////////
  //
  output                    rtt_read_a,  // RTT read pulse
  output                    rtt_write_a, // RTT write pulse
  output [`npuarc_RTT_ADDR_RANGE]  rtt_addr_r,  // RTT Pgm Address
  input  [`npuarc_DATA_RANGE]      rtt_drd_r,   // RTT read data
  output [`npuarc_DATA_RANGE]      rtt_dwr_r,   // RTT write data

  input                     rtt_prod_sel, // RTT Producer enable

  ///////// RTT Pipeline tracking outputs ////////////////////////////////
  //
  output              rtt_inst_commit,   // instruction has committed
  output [`npuarc_PC_RANGE]  rtt_inst_addr,     // instruction address (pc)
  output              rtt_cond_valid,    // commit inst was conditional
  output              rtt_cond_pass,     // condition code test passed

  output              rtt_branch,        // instruction was a branch
  output              rtt_branch_indir,  // branch was indirect
  output [`npuarc_PC_RANGE]  rtt_branch_taddr,  // Target address of branch/exc
  output              rtt_dslot,         // Branch has delay slot
  output              rtt_in_deslot,     // in d or e slot
  output              rtt_in_eslot,      // in e slot
  output              rtt_uop_is_leave,  // ca has leave_s gen'd uop instr
  output              rtt_exception,     // exception has been taken
  output              rtt_exception_rtn, // exception exit
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
  input               rtt_freeze,
  input [7:0]         rtt_src_num,


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
  output  wire                   ifu_ibus_rd_accept,      // read data accept
  input wire [64-1:0]            ifu_ibus_rd_data,        // read data
  input wire                     ifu_ibus_rd_last,        // read last
// leda NTL_CON37 on






  output wire                    lqwq_mem_cmd_valid,
  output wire                    lqwq_mem_cmd_cache,
  output wire                    lqwq_mem_cmd_burst_size,
  output wire                    lqwq_mem_cmd_read,
  input  wire                    lqwq_mem_cmd_accept,
  output wire [`npuarc_PADDR_RANGE]     lqwq_mem_cmd_addr,
  output wire                    lqwq_mem_cmd_lock,
  output wire                    lqwq_mem_cmd_excl,
  output wire [2:0]              lqwq_mem_cmd_data_size,
  output wire [1:0]              lqwq_mem_cmd_prot,

  output wire                    lqwq_mem_wr_valid,
  output wire                    lqwq_mem_wr_last,
  input  wire                    lqwq_mem_wr_accept,
  output wire [`npuarc_DOUBLE_BE_RANGE] lqwq_mem_wr_mask,
  output wire [`npuarc_DOUBLE_RANGE]    lqwq_mem_wr_data,

  input  wire                    lqwq_mem_rd_valid,
  input  wire                    lqwq_mem_err_rd,
  input  wire                    lqwq_mem_rd_excl_ok,
  input  wire                    lqwq_mem_rd_last,
  output wire                    lqwq_mem_rd_accept,
  input  wire [`npuarc_DOUBLE_RANGE]    lqwq_mem_rd_data,

  input  wire                    lqwq_mem_wr_done,
  input  wire                    lqwq_mem_wr_excl_done,
  input  wire                    lqwq_mem_err_wr,
  output wire                    lqwq_mem_wr_resp_accept,
// leda NTL_CON37 on
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


  //////////// Watchdog timer /////////////////////////////////////////////////
  //
  input                       wdt_clk,
  input                       wdt_ext_timeout_ack_r,   // External timeout acknowledge
  output                      wdt_ext_timeout_r,       // External timeout signal
  output                      wdt_reset,               // Reset timeout signal
  output                      wdt_reset2,              // Reset timeout signal from wdt clk




//  `if (`HAS_SAFETY == 1) // {
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




  output                      rst               , // not an output of alb_core


  ////////// General input signals ///////////////////////////////////////////
  //
  output                      cpu_clk_enable,     // level 1 clock request
  input                       cpu_l1_cg_dis,      // GLOBAL_L1_CLK_DIS aux bit
  input                       cpu_l1_accept_en,   // level 1 clock active
  input                       clk,                // Processor clock
  input                       rst_a               // Asynchronous reset

);


///////////////////////////////////////////////////////////////////////////////
// Local Signal Declarations
//




wire                       core_dbg_cmdack;
wire                       core_dbg_rspval;
wire [`npuarc_DBG_DATA_RANGE]     core_dbg_rdata;
wire                       core_dbg_reop;
wire                       core_dbg_rerr;

// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  These signals are used for MCIP relevant configurations, may non driving in corner configurations which is harmless
// spyglass disable_block W528
// SMD: signal set but not read
// SJ:  These signals are used for MCIP relevant configurations, may be non driving in corner configurations which is harmless
wire                       dbg_bh_r;           // break halt
wire                       dbg_sh_r;           // self_halt
wire                       dbg_eh_r;           // external halt (cur unused)

wire                       dbg_ah_r;           // actionpoint halt
// spyglass enable_block W528
// leda NTL_CON13A on


//////////////////////////////////////////////////////////////////////////////
// Wires for clock control module
//
wire                        dmp_idle_r;
wire                        ifu_idle_r;
wire                        ar_clock_enable_r;
wire                        db_clock_enable_nxt;
wire                        db_active;          // Debug op in progress
wire                        irq_preempts_nxt;
wire                        irq_clk_en_r;

wire                        clk_gated;
wire                        hor_clock_enable_nxt;

wire                        mpy_unit_enable;
wire                        mpy_unit_clk;
wire                        div_unit_enable;
wire                        div_unit_clk;
wire                        smt_unit_enable;
wire                        smt_unit_clk;
wire                        rtt_unit_clk;
wire                        dmp_unit_enable;
wire                        dmp_dmu_unit_enable;
wire                        dmp_lq_unit_enable;
wire                        dmp_unit_clk;
wire                        dmp_dmu_unit_clk;
wire                        dmp_lq_unit_clk;
wire                        ap_unit_enable;
wire                        ap_unit_clk;
wire                        aux_aps_active;
wire                        ap_aux_clk;
wire                        pct_unit_enable;
wire                        pct_unit_clk;
wire                        aux_timer_active; 

wire                        wake_from_wait;

//////////////////////////////////////////////////////////////////////////////
// Wires for resync_in
//
wire                        arc_event_r;
wire                        irq_sync_req;             //
wire                        dbg_cache_rst_disable_r;
wire                        dccm_dmi_priority_r;      

//////////////////////////////////////////////////////////////////////////////
//wire for irq_resync_in
//
wire  [`npuarc_IRQE_RANGE]         irq_r;

//////////////////////////////////////////////////////////////////////////////
// Wires for Auxiliary
//
//
wire                        aux_read;             //
wire                        aux_write;            //
wire  [`npuarc_DATA_RANGE]         wa_sr_data_r;         // Aux Write data

wire                         wdt_x3_stall;
wire                         x3_kill;

wire                      aux_rtt_active;  // enable RTT interf clk


//////////////////////////////////////////////////////////////////////////////
// Wires for RTC
//
//
wire                        aux_wdt_ren_r;        //
wire  [3:0]                 aux_wdt_raddr_r;      //
wire                        aux_wdt_wen_r;        //
wire  [3:0]                 aux_wdt_waddr_r;      //
//
wire  [`npuarc_DATA_RANGE]         wdt_aux_rdata;        //
wire                        wdt_aux_illegal;      //
wire                        wdt_aux_k_rd;         //
wire                        wdt_aux_k_wr;         //
wire                        wdt_aux_unimpl;       //
wire                        wdt_aux_serial_sr;    //
wire                        wdt_aux_strict_sr;    //
wire  [`npuarc_IRQM_RANGE]         wdt_int_timeout_1h_r; // Interrupt timeout signal
//////////////////////////////////////////////////////////////////////////////
// Wires for RTC
//
//
wire                        aux_rtc_ren_r;        //
wire  [2:0]                 aux_rtc_raddr_r;      //
wire                        aux_rtc_wen_r;        //
wire  [2:0]                 aux_rtc_waddr_r;      //
//
wire  [`npuarc_DATA_RANGE]         rtc_aux_rdata;        //
wire                        rtc_aux_illegal;      //
wire                        rtc_aux_k_rd;         //
wire                        rtc_aux_k_wr;         //
wire                        rtc_aux_unimpl;       //
wire                        rtc_aux_serial_sr;    //
wire                        rtc_aux_strict_sr;    //
//
wire                        rtc_na;               //

//////////////////////////////////////////////////////////////////////////////
//
// Timers wires
//
//////////////////////////////////////////////////////////////////////////////
wire                        aux_tm0_ren_r;
wire  [1:0]                 aux_tm0_raddr_r;
wire                        aux_tm0_wen_r;
wire  [1:0]                 aux_tm0_waddr_r;
//
wire  [`npuarc_DATA_RANGE]         tm0_aux_rdata;
wire                        tm0_aux_illegal;
wire                        tm0_aux_k_rd;
wire                        tm0_aux_k_wr;
wire                        tm0_aux_unimpl;
wire                        tm0_aux_serial_sr;
//
wire  [`npuarc_IRQM_RANGE]         timer0_irq_1h;




wire                      core_sys_halt_r;
wire                      core_sys_sleep_r;
wire   [`npuarc_EXT_SMODE_RANGE] core_sys_sleep_mode_r;




wire                      gb_sys_halt_req_r   ;
wire                      gb_sys_run_req_r    ;
wire                      core_sys_tf_halt_r  ;
wire                      core_sys_halt_ack_r ;
wire                      core_sys_run_ack_r  ;

wire                      l1_clock_active;


wire                      ar_save_clk;
wire                      ar_save_en_r;

////////////////////////////////////////////////////////////////////////////
//
// Module instantiation - aon
//
////////////////////////////////////////////////////////////////////////////
npuarc_alb_aon u_aon (

  .ar_save_clk    (ar_save_clk  ),
  .ar_save_en_r   (ar_save_en_r ),

  .arc_event_a(arc_event_a),
  .db_active(db_active),
  .dbg_cache_rst_disable(dbg_cache_rst_disable), 
  .dccm_dmi_priority(dccm_dmi_priority),
  .arc_halt_req_a(arc_halt_req_a),
  .arc_run_req_a(arc_run_req_a),
  .arc_halt_ack(arc_halt_ack),
  .arc_run_ack(arc_run_ack),

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
  .irq_r(irq_r),
  .gb_sys_halt_req_r(gb_sys_halt_req_r),
  .gb_sys_run_req_r(gb_sys_run_req_r),

  .core_sys_halt_r(core_sys_halt_r),
  .core_sys_sleep_r(core_sys_sleep_r),
  .core_sys_sleep_mode_r(core_sys_sleep_mode_r),

  .core_sys_halt_ack_r(core_sys_halt_ack_r),
  .core_sys_run_ack_r(core_sys_run_ack_r),


  .x3_kill            (x3_kill            ),
  .wdt_x3_stall       (wdt_x3_stall       ),

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

  .dmp_idle_r(dmp_idle_r),
  .ifu_idle_r(ifu_idle_r),
  .hor_clock_enable_nxt(hor_clock_enable_nxt),
  .biu_dmi_clk_en_req(biu_dmi_clk_en_req),
  .db_clock_enable_nxt(db_clock_enable_nxt),
  .irq_preempts_nxt(irq_preempts_nxt),

  .mpy_unit_enable(mpy_unit_enable),
  .div_unit_enable(div_unit_enable),
  .smt_unit_enable(smt_unit_enable),
  .dmp_unit_enable(dmp_unit_enable),
  .dmp_dmu_unit_enable(dmp_dmu_unit_enable),
  .dmp_lq_unit_enable(dmp_lq_unit_enable),
  .ap_unit_enable       (ap_unit_enable           ),
  .aux_aps_active       (aux_aps_active           ),
  .pct_unit_enable(pct_unit_enable),
  .aux_timer_active(aux_timer_active),
  .wake_from_wait(wake_from_wait),

  //////////// Outputs from clock control module  /////////////////////////////
  //
  .cpu_clk_enable(cpu_clk_enable),        // level 1 clk req
  .cpu_l1_cg_dis(cpu_l1_cg_dis),  
  .cpu_l1_accept_en(cpu_l1_accept_en),
  .l1_clock_active(l1_clock_active),
  .ar_clock_enable_r(ar_clock_enable_r),
  .irq_clk_en_r(irq_clk_en_r),

  .clk_gated(clk_gated),
  .mpy_unit_clk(mpy_unit_clk),
  .div_unit_clk(div_unit_clk),
  .smt_unit_clk(smt_unit_clk),
  .rtt_unit_clk(rtt_unit_clk),
  .dmp_unit_clk(dmp_unit_clk),
  .dmp_dmu_unit_clk(dmp_dmu_unit_clk),
  .dmp_lq_unit_clk(dmp_lq_unit_clk),
  .ap_unit_clk          (ap_unit_clk          ),
  .ap_aux_clk           (ap_aux_clk           ),
  .pct_unit_clk(pct_unit_clk),


  .arc_event_r(arc_event_r),
  .dbg_cache_rst_disable_r(dbg_cache_rst_disable_r),
  .dccm_dmi_priority_r(dccm_dmi_priority_r),    


  .dbg_cmdack(dbg_cmdack),
  .dbg_rspval(dbg_rspval),
  .dbg_rdata(dbg_rdata),
  .dbg_reop(dbg_reop),
  .dbg_rerr(dbg_rerr),


  .core_dbg_cmdack(core_dbg_cmdack),
  .core_dbg_rspval(core_dbg_rspval),
  .core_dbg_rdata(core_dbg_rdata),
  .core_dbg_reop(core_dbg_reop),
  .core_dbg_rerr(core_dbg_rerr),

  .apb_rst(apb_rst),
  .presetdbgn(presetdbgn),

  .rtt_prod_sel(rtt_prod_sel),
  .aux_rtt_active(aux_rtt_active),

  .dbg_bh_r(dbg_bh_r),
  .dbg_sh_r(dbg_sh_r),
  .dbg_ah_r(dbg_ah_r),


  .test_mode(test_mode),

  .wdt_clk                   (wdt_clk),
  .wdt_ext_timeout_ack_r(wdt_ext_timeout_ack_r),
  .wdt_ext_timeout_r(wdt_ext_timeout_r),
  .wdt_reset(wdt_reset),
  .wdt_reset2           (wdt_reset2           ),

  //if (`SAFETY_HAS_PMODE == 1)
//  input                       perf_mode,
  //endif



  .aux_tm0_ren_r(aux_tm0_ren_r),
  .aux_tm0_raddr_r(aux_tm0_raddr_r),
  .aux_tm0_wen_r(aux_tm0_wen_r),
  .aux_tm0_waddr_r(aux_tm0_waddr_r),
  .tm0_aux_rdata(tm0_aux_rdata),
  .tm0_aux_illegal(tm0_aux_illegal),
  .tm0_aux_k_rd(tm0_aux_k_rd),
  .tm0_aux_k_wr(tm0_aux_k_wr),
  .tm0_aux_unimpl(tm0_aux_unimpl),
  .tm0_aux_serial_sr(tm0_aux_serial_sr),
  .timer0_irq_1h(timer0_irq_1h),

  .watchdog_reset(watchdog_reset),     // Assert Watchdog reset
  .aux_wdt_ren_r(aux_wdt_ren_r),
  .aux_wdt_raddr_r(aux_wdt_raddr_r),
  .aux_wdt_wen_r(aux_wdt_wen_r),
  .aux_wdt_waddr_r(aux_wdt_waddr_r),

  .wdt_aux_rdata(wdt_aux_rdata),
  .wdt_aux_illegal(wdt_aux_illegal),
  .wdt_aux_k_rd(wdt_aux_k_rd),
  .wdt_aux_k_wr(wdt_aux_k_wr),
  .wdt_aux_unimpl(wdt_aux_unimpl),
  .wdt_aux_serial_sr(wdt_aux_serial_sr),
  .wdt_aux_strict_sr(wdt_aux_strict_sr),

  .wdt_int_timeout_1h_r(wdt_int_timeout_1h_r),

  .aux_rtc_ren_r(aux_rtc_ren_r),
  .aux_rtc_raddr_r(aux_rtc_raddr_r),
  .aux_rtc_wen_r(aux_rtc_wen_r),
  .aux_rtc_waddr_r(aux_rtc_waddr_r),

  .rtc_aux_rdata(rtc_aux_rdata),
  .rtc_aux_illegal(rtc_aux_illegal),
  .rtc_aux_k_rd(rtc_aux_k_rd),
  .rtc_aux_k_wr(rtc_aux_k_wr),
  .rtc_aux_unimpl(rtc_aux_unimpl),
  .rtc_aux_serial_sr(rtc_aux_serial_sr),
  .rtc_aux_strict_sr(rtc_aux_strict_sr),
  .rtc_na(rtc_na),

  .aux_read(aux_read),
  .aux_write(aux_write),
  .wa_sr_data_r(wa_sr_data_r),
  .clk(clk),
  .clk_ungated          (clk_ungated	      ),
  .rst(rst),
  .rst_a(rst_a)
);

////////////////////////////////////////////////////////////////////////////
//
// Module instantiation - pd1
//
////////////////////////////////////////////////////////////////////////////
npuarc_alb_pd1 u_alb_pd1 (
  .ar_save_clk    (ar_save_clk  ),
  .ar_save_en_r   (ar_save_en_r ),





  .intvbase_in            (intvbase_in          ),

  .x3_kill                (x3_kill              ),
  .wdt_x3_stall           (wdt_x3_stall         ),
  ////////// Machine Halt Interface //////////////////////////////////////////
  //
  .gb_sys_halt_req_r      (gb_sys_halt_req_r    ),   // Sync. halt req.
  .gb_sys_run_req_r       (gb_sys_run_req_r     ),   // Sync. run req.

  .core_sys_halt_r        (core_sys_halt_r      ),
  .core_sys_tf_halt_r     (core_sys_tf_halt_r   ),
  .core_sys_sleep_r       (core_sys_sleep_r     ),
  .core_sys_sleep_mode_r  (core_sys_sleep_mode_r),

  .core_sys_halt_ack_r    (core_sys_halt_ack_r  ),    // Sync. halt ack.
  .core_sys_run_ack_r     (core_sys_run_ack_r   ),    // Sync. halt ack.


  //////////// Inputs from clock control module  /////////////////////////////
  //
  .ar_clock_enable_r       (ar_clock_enable_r),
  ///////// interrupt sample clock control ///////////////////////////////////
  //
  .irq_clk_en_r            (irq_clk_en_r),

  .clk_gated               (clk_gated),

  ////////// Unit-level clock gating control outputs to clock_ctrl ///////////
  //
  .mpy_unit_clk             (mpy_unit_clk),
  .div_unit_clk             (div_unit_clk),
  .smt_unit_clk             (smt_unit_clk),
  .rtt_unit_clk             (rtt_unit_clk),
  .dmp_unit_clk             (dmp_unit_clk),
  .dmp_dmu_unit_clk         (dmp_dmu_unit_clk),
  .dmp_lq_unit_clk         (dmp_lq_unit_clk),
  .ap_unit_clk             (ap_unit_clk       ),
  .ap_aux_clk              (ap_aux_clk        ),
  .pct_unit_clk             (pct_unit_clk),

  //////////// Outputs to clock control module  /////////////////////////////
  //
  .dmp_idle_r               (dmp_idle_r),
  .ifu_idle_r               (ifu_idle_r),
  .hor_clock_enable_nxt     (hor_clock_enable_nxt),
  .db_clock_enable_nxt      (db_clock_enable_nxt),
  .irq_preempts_nxt         (irq_preempts_nxt),

  ////////// Unit-level clock gating control outputs to clock_ctrl ///////////
  //
  .mpy_unit_enable      (mpy_unit_enable),
  .div_unit_enable      (div_unit_enable),
  .smt_unit_enable      (smt_unit_enable),
// spyglass disable_block Ac_conv01
// SMD: Convergence
// SJ:  two accessing path is independent path    
  .dmp_unit_enable      (dmp_unit_enable),
// spyglass enable_block Ac_conv01  
  .dmp_dmu_unit_enable  (dmp_dmu_unit_enable),
  .dmp_lq_unit_enable   (dmp_lq_unit_enable),
  .ap_unit_enable       (ap_unit_enable           ),
  .aux_aps_active       (aux_aps_active           ),
  .pct_unit_enable      (pct_unit_enable),
  .aux_timer_active(aux_timer_active), 
  .wake_from_wait       (wake_from_wait),
  .dbg_cmdval           (dbg_cmdval          ),
  .dbg_address          (dbg_address         ),
  .dbg_be               (dbg_be              ),
  .dbg_cmd              (dbg_cmd             ),
  .dbg_wdata            (dbg_wdata           ),
  .dbg_rspack           (dbg_rspack          ),

  .core_dbg_cmdack      (core_dbg_cmdack     ),
  .core_dbg_rspval      (core_dbg_rspval     ),
  .core_dbg_rdata       (core_dbg_rdata      ),
  .core_dbg_reop        (core_dbg_reop       ),
  .core_dbg_rerr        (core_dbg_rerr       ),

  .debug_reset          (debug_reset         ),

  ////////// APB debug interface /////////////////////////////////////////////

  .dbg_prot_sel         (dbg_prot_sel        ),

  .pclkdbg_en           (pclkdbg_en          ),
  .apb_rst              (apb_rst             ),
  .paddrdbg             (paddrdbg            ),
  .pseldbg              (pseldbg             ),
  .penabledbg           (penabledbg          ),
  .pwritedbg            (pwritedbg           ),
  .pwdatadbg            (pwdatadbg           ),
  .dbgen                (dbgen               ),
  .niden                (niden               ),

  .preadydbg            (preadydbg           ),
  .prdatadbg            (prdatadbg           ),
  .pslverrdbg           (pslverrdbg          ),

  .cti_ap_status        (cti_ap_status       ),
  .cti_ap_hit           (cti_ap_hit          ),
  .cti_halt             (cti_halt            ),
  .cti_break            (cti_break           ),
  .cti_sleep            (cti_sleep           ),

  .dbg_bh_r             (dbg_bh_r            ),
  .dbg_sh_r             (dbg_sh_r            ),
  .dbg_eh_r             (dbg_eh_r            ),

  .dbg_ah_r             (dbg_ah_r            ),
  // ALB_RESYNC_IN
  //
  .arc_event_r           (arc_event_r), // Sync. evt signal
  .dbg_cache_rst_disable_r (dbg_cache_rst_disable_r),
  .dccm_dmi_priority_r     (dccm_dmi_priority_r),


  // ALB_IRQ_RESYNC_IN
  //
  .irq_r                (irq_r), // Sync. interrupts



  .clk_ungated            (clk_ungated          ),


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


// RAM interface for icache tags and data
  .ic_tag_way0_clk   (ic_tag_way0_clk   ),
  .ic_tag_din0         (ic_tag_din0         ),
  .ic_tag_dout0        (ic_tag_dout0        ),
  .ic_tag_addr0        (ic_tag_addr0        ),
  .ic_tag_wem0         (ic_tag_wem0         ),    
  .ic_tag_cen0         (ic_tag_cen0         ),
  .ic_tag_wen0         (ic_tag_wen0         ),
  .ic_tag_way1_clk   (ic_tag_way1_clk   ),
  .ic_tag_din1         (ic_tag_din1         ),
  .ic_tag_dout1        (ic_tag_dout1        ),
  .ic_tag_addr1        (ic_tag_addr1        ),
  .ic_tag_wem1         (ic_tag_wem1         ),    
  .ic_tag_cen1         (ic_tag_cen1         ),
  .ic_tag_wen1         (ic_tag_wen1         ),
  .ic_tag_way2_clk   (ic_tag_way2_clk   ),
  .ic_tag_din2         (ic_tag_din2         ),
  .ic_tag_dout2        (ic_tag_dout2        ),
  .ic_tag_addr2        (ic_tag_addr2        ),
  .ic_tag_wem2         (ic_tag_wem2         ),    
  .ic_tag_cen2         (ic_tag_cen2         ),
  .ic_tag_wen2         (ic_tag_wen2         ),
  .ic_tag_way3_clk   (ic_tag_way3_clk   ),
  .ic_tag_din3         (ic_tag_din3         ),
  .ic_tag_dout3        (ic_tag_dout3        ),
  .ic_tag_addr3        (ic_tag_addr3        ),
  .ic_tag_wem3         (ic_tag_wem3         ),    
  .ic_tag_cen3         (ic_tag_cen3         ),
  .ic_tag_wen3         (ic_tag_wen3         ),

  .ic_data_bank0_clk (ic_data_bank0_clk ),
  .ic_data_din0        (ic_data_din0        ),
  .ic_data_dout0       (ic_data_dout0       ),
  .ic_data_addr0       (ic_data_addr0       ),
  .ic_data_cen0        (ic_data_cen0        ),
  .ic_data_wen0        (ic_data_wen0        ),
  .ic_data_wem0        (ic_data_wem0        ),
  .ic_data_bank1_clk (ic_data_bank1_clk ),
  .ic_data_din1        (ic_data_din1        ),
  .ic_data_dout1       (ic_data_dout1       ),
  .ic_data_addr1       (ic_data_addr1       ),
  .ic_data_cen1        (ic_data_cen1        ),
  .ic_data_wen1        (ic_data_wen1        ),
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


  .db_active             (db_active          ),

  ////////// Timers aux interface /////////////////////////////////////////
  //
  .aux_tm0_ren_r           (aux_tm0_ren_r    ),
  .aux_tm0_raddr_r         (aux_tm0_raddr_r  ),
  .aux_tm0_wen_r           (aux_tm0_wen_r    ),
  .aux_tm0_waddr_r         (aux_tm0_waddr_r  ),
  .tm0_aux_rdata           (tm0_aux_rdata    ),
  .tm0_aux_illegal         (tm0_aux_illegal  ),
  .tm0_aux_k_rd            (tm0_aux_k_rd     ),
  .tm0_aux_k_wr            (tm0_aux_k_wr     ),
  .tm0_aux_unimpl          (tm0_aux_unimpl   ),
  .tm0_aux_serial_sr       (tm0_aux_serial_sr),
  .timer0_irq_1h           (timer0_irq_1h    ),



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
  .wdt_int_timeout_1h_r (wdt_int_timeout_1h_r),


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



  .aux_rs_valid            (aux_rs_valid           ), //
  .aux_rs_region           (aux_rs_region          ), //
  .aux_rs_addr             (aux_rs_addr            ), //
  .aux_rs_read             (aux_rs_read            ), //
  .aux_rs_write            (aux_rs_write           ), //
  .aux_rs_data             (aux_rs_data            ), //
  .aux_rs_status           (aux_rs_status          ), //
  .aux_rs_accept           (aux_rs_accept          ), //

  .aux_wr_valid            (aux_wr_valid           ), //
  .aux_wr_region           (aux_wr_region          ), //
  .aux_wr_addr             (aux_wr_addr            ), //
  .aux_wr_data             (aux_wr_data            ), //
  .aux_wr_allow            (aux_wr_allow           ), //
  .aux_cm_phase            (aux_cm_phase           ), //
  .aux_cm_valid            (aux_cm_valid           ), //
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
  .ntlb_pd0_clk          (ntlb_pd0_clk),
  .ntlb_pd0_ce           (ntlb_pd0_ce),
  .ntlb_pd0_we           (ntlb_pd0_we),
  .ntlb_pd0_wem          (ntlb_pd0_wem),
  .ntlb_pd0_addr         (ntlb_pd0_addr),
  .ntlb_pd0_wdata        (ntlb_pd0_wdata),
  .ntlb_pd0_rdata        (ntlb_pd0_rdata),

  // NTLB PD1 (data) ram interface
  .ntlb_pd1_clk          (ntlb_pd1_clk),
  .ntlb_pd1_ce           (ntlb_pd1_ce),
  .ntlb_pd1_we           (ntlb_pd1_we),
  .ntlb_pd1_addr         (ntlb_pd1_addr),
  .ntlb_pd1_wdata        (ntlb_pd1_wdata),
  .ntlb_pd1_rdata        (ntlb_pd1_rdata),


  .test_mode            (test_mode          ),
  .arcnum               (arcnum             ),
  .clusternum           (clusternum         ),

//`if (`HAS_SAFETY == 1) // {


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





  .aux_rtt_active      (aux_rtt_active     ),
  .rtt_read_a          (rtt_read_a         ),
  .rtt_write_a         (rtt_write_a        ),
  .rtt_addr_r          (rtt_addr_r         ),
  .rtt_dwr_r           (rtt_dwr_r          ),
  .rtt_drd_r           (rtt_drd_r          ),


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


  .ifu_ibus_cmd_valid      (ifu_ibus_cmd_valid    ),
  .ifu_ibus_cmd_accept     (ifu_ibus_cmd_accept   ),
  .ifu_ibus_cmd_addr       (ifu_ibus_cmd_addr     ),
  .ifu_ibus_cmd_wrap       (ifu_ibus_cmd_wrap     ),
  .ifu_ibus_cmd_cache      (ifu_ibus_cmd_cache     ),
  .ifu_ibus_cmd_burst_size (ifu_ibus_cmd_burst_size),
  .ifu_ibus_cmd_prot       (ifu_ibus_cmd_prot     ),
  .ifu_ibus_rd_valid       (ifu_ibus_rd_valid     ),
  .ifu_ibus_err_rd         (ifu_ibus_err_rd       ),
  .ifu_ibus_rd_accept      (ifu_ibus_rd_accept    ),
  .ifu_ibus_rd_data        (ifu_ibus_rd_data      ),
  .ifu_ibus_rd_last        (ifu_ibus_rd_last      ),

  .aux_read                (aux_read            ), // Aux read op
  .aux_write               (aux_write           ), // Aux write op
  .wa_sr_data_r            (wa_sr_data_r        ), // aux write data

  .lqwq_mem_cmd_valid        (lqwq_mem_cmd_valid     ),
  .lqwq_mem_cmd_cache        (lqwq_mem_cmd_cache     ),
  .lqwq_mem_cmd_burst_size   (lqwq_mem_cmd_burst_size),
  .lqwq_mem_cmd_read         (lqwq_mem_cmd_read      ),
  .lqwq_mem_cmd_accept       (lqwq_mem_cmd_accept    ),
  .lqwq_mem_cmd_addr         (lqwq_mem_cmd_addr      ),
  .lqwq_mem_cmd_lock         (lqwq_mem_cmd_lock      ),
  .lqwq_mem_cmd_excl         (lqwq_mem_cmd_excl      ),
  .lqwq_mem_cmd_data_size    (lqwq_mem_cmd_data_size ),
  .lqwq_mem_cmd_prot         (lqwq_mem_cmd_prot      ),

  .lqwq_mem_wr_valid         (lqwq_mem_wr_valid      ),
  .lqwq_mem_wr_last          (lqwq_mem_wr_last       ),
  .lqwq_mem_wr_accept        (lqwq_mem_wr_accept     ),
  .lqwq_mem_wr_mask          (lqwq_mem_wr_mask       ),
  .lqwq_mem_wr_data          (lqwq_mem_wr_data       ),

  .lqwq_mem_rd_valid         (lqwq_mem_rd_valid      ),
  .lqwq_mem_err_rd           (lqwq_mem_err_rd        ),
  .lqwq_mem_rd_excl_ok       (lqwq_mem_rd_excl_ok    ),
  .lqwq_mem_rd_last          (lqwq_mem_rd_last       ),
  .lqwq_mem_rd_accept        (lqwq_mem_rd_accept     ),
  .lqwq_mem_rd_data          (lqwq_mem_rd_data       ),

  .lqwq_mem_wr_done          (lqwq_mem_wr_done       ),
  .lqwq_mem_wr_excl_done     (lqwq_mem_wr_excl_done  ),
  .lqwq_mem_err_wr           (lqwq_mem_err_wr        ),
  .lqwq_mem_wr_resp_accept   (lqwq_mem_wr_resp_accept),

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







  .l1_clock_active     (l1_clock_active       ),
  .clk                 (clk),
  .rst_a               (rst),
  .rst                 (rst)
);


assign gb_sys_sleep_r        = core_sys_sleep_r     ;
assign gb_sys_sleep_mode_r   = core_sys_sleep_mode_r;
assign gb_sys_halt_r         = core_sys_halt_r      ;
assign gb_sys_tf_halt_r      = core_sys_tf_halt_r   ;

endmodule // module : alb_cpu
