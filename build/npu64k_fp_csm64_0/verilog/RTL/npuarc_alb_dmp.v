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
//   #####   #     #  ####                   
//    #   #  ##   ##  #   #                  
//    #   #  # # # #  #   #                  
//    #   #  #  #  #  ####                   
//    #   #  #     #  #                      
//   #####   #     #  #                      
//
// ===========================================================================
//
// Description:
//  This module implements the Data Memory pipeline.
//  It is a dmp top module that instantiates all the dmp sub modules.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o dmp.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some inputs are not used in certain configurations
  ////////// Interface to the SA stage //////////////////////////////////////
  //
  input                         sa_dsync_op_r,        // SA is a DSYNC insn.
  input                         sa_dmb_op_r,          // SA is a DMB insn.
  input                         sa_dmb_stall,         // SA stall due to DMB

  ////////// Interface to the SA stage //////////////////////////////////////
  //
  input                         sa_load_r,
  input                         sa_store_r,
  input                         ca_dmp_aux_sr_op,

  ////////// Interface to the X1 stage //////////////////////////////////////
  //
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input                         x1_valid_r,     // X1 has valid instruction
// spyglass enable_block W240
  input                         x1_pass,        // X1  passing on ints
  input                         x1_load_r,      // X1 load
  input                         x1_store_r,     // X1 store
  input                         x1_pref_r,      // X1 pref ucode bit
  input                         x1_cache_byp_r, // X1 .di instruction
  input  [1:0]                  x1_size_r,      // 00-b, 01-h, 10-w, 11-dw
  input  [`npuarc_ADDR_RANGE]          x1_mem_addr0,   // X1 mem addr0
  input  [`npuarc_ADDR_RANGE]          x1_mem_addr1,   // X1 mem addr1
  input  [`npuarc_ADDR_RANGE]          x1_addr_base,   // X1 addr base
  input  [`npuarc_ADDR_RANGE]          x1_addr_offset, // X1 addr  offset
  input  [1:0]                  x1_bank_sel_lo, // X1 bank sel 
  input  [1:0]                  x1_bank_sel_hi, // X1 bank sel
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                         x1_uop_inst_r,  // X1 uop signal
// spyglass enable_block W240
  output                        dc1_stall,        // X1 stall
  
  ////////// Interface to the X2 stage ///////////////////////////////
  //
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                         x2_valid_r,     // X2 has valid instruction
// spyglass enable_block W240
  input                         x2_pass,        // X2 passing on instt
  input                         x2_enable,      // X2 accepts new instruction
  input                         x2_load_r,      // X2 load  
  input                         x2_store_r,     // X2 store 
  input                         x2_locked_r,    // X2 LLOCK/SCOND
  input                         x2_pref_r,      // X2 Prefetch
  input [1:0]                   x2_size_r,      // X2 size  
  input                         x2_cache_byp_r, // X2 .di instruction
  input                         x2_mpu_data_unc,// X2 unc MPU region     
  input                         x2_mpu_data_flt,      // 
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                         x2_uop_inst_r,  // X2 uop signal
// spyglass enable_block W240
  input [`npuarc_ADDR_RANGE]           x2_mem_addr0_r, // X2 mem addr
  input                         x2_exu_stall,   // X2 EXU stall
  output                        dc2_stall,      // DC2 stall
  
  ////////// Interface to the X3 stage ///////////////////////////////
  //
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input                         x3_valid_r,     // X3 has valid instruction 
// spyglass enable_block W240
  input                         x3_pass,        // X3 passing on instt
  input                         x3_1_enable,    // X3 accepts new instruction
  input                         x3_load_r,      // X3 load  
  input                         x3_pref_r,      // X3 pref  
  input                         x3_pref_l2_r,   // X3 pref l2  
  input                         x3_prefw_r,     // X3 pref with intention to write  
  input                         x3_pre_alloc_r, // X3 pre-alloc instruction  
  input                         x3_store_r,     // X3 store
  input                         x3_store_may_grad, // 
  input                         x3_locked_r,    // X3 LLOCK/SCOND
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                         x3_cache_byp_r, // X3 .di instruction
// spyglass enable_block W240
  input  [1:0]                  x3_size_r,      // 00-b, 01-h, 10-w, 11-dw
  input                         x3_sex_r,       // X3 load sign extension
  input [`npuarc_ADDR_RANGE]           x3_mem_addr0_r, // X3 memory address
  input                         x3_uop_inst_r,
  output                        dmp_dc3_stall_r,
  input                         x3_sync_op_r,   // X3 SYNC instr
  input                         x3_brk_op_r,    // X3 BRK instr
  output [`npuarc_ADDR_RANGE]          dc3_dtlb_efa,   // DC3 Effective fault address
  output                        dc3_fast_byp,   // DC3 speculative fast byp
  output                        dc4_fast_byp_r, // DC4 fast byp
  output                        dc4_fast_byp_miss_r, // LD miss
  
  ////////// Interface to the CA stage /////////////////////////////
  //
  input                         ca_valid_r,     // CA has valid instruction 
  input                         ca_pass,        // CA passing on inst
  input                         ca_enable,      // CA accepts new instruction
  input                         ca_load_r,      // CA load

// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input                         ca_pref_r,      // CA pref L1
  input                         ca_pref_l2_r,   // CA pref L2  
  input                         ca_prefw_r,     // CA pref with intention to write  
  input                         ca_pre_alloc_r, // CA pre_alloc
// spyglass enable_block W240
  input                         ca_store_r,     // CA store  
  input [1:0]                   ca_store_grad_r,// CA Store Graduation
  input [1:0]                   ca_store_grad_swap_r, // Indicates where data is expected
  input [`npuarc_GRAD_TAG_RANGE]       ca_store_grad_tag_lo_r,// CA store grad tag
  input [`npuarc_GRAD_TAG_RANGE]       ca_store_grad_tag_hi_r,// CA store grad tag
  input                         ca_locked_r,    // CA LLOCK/SCOND
  input [1:0]                   ca_size_r,      // 00-b, 01-h, 10-w, 11-dw
  input                         ca_sex_r,       // CA load sign extension
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input [`npuarc_ADDR_RANGE]           ca_mem_addr0_r, // CA memory address
// spyglass enable_block W240
  output [`npuarc_PADDR_RANGE]         ca_phys_addr_r, // CA physical memory address
  input                         ca_uop_inst_r,  // CA uop
  input [`npuarc_DMP_DATA_RANGE]       ca_wr_data_r,   // CA write data
  
  output                        dc4_stall_r,     // DC4 structural hazard
  output [3:0]                  ecc_dccm_sbe_count_r, // Single bit error count         
  input                         dccm_ecc_sbe_clr,
  output [3:0]                  ecc_dc_tag_sbe_count_r,  // Single bit error count tag
  input                         dc_tag_ecc_sbe_clr,
  output [3:0]                  ecc_dc_data_sbe_count_r, // Single bit error count data
  input                         dc_data_ecc_sbe_clr,
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                         ecc_sbe_dmp_clr,
// spyglass enable_block W240

  output                        dc4_waw_replay_r, // CA not stall on WAW
  output                        dc4_pref_r,
  ////////// Interface to the WA stage /////////////////////////////////////
  //
  input [`npuarc_PADDR_RANGE]          wa_lpa_r,          // LPA reg 
  input                         wa_lock_flag_r,    // LF  reg value 
  input                         wa_lock_double_r,  // LF  size
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input                         wa_restart_r,      // WB pipe flush kills CA
  input                         wa_restart_kill_r, // WB pipe flush kills CA
  input                         wa_hlt_restart_r,  // WB pipe flush kills CA
// spyglass enable_block W240
  input                         mem_excpn_ack_r,   // bus error excpn ack

  input                         wa_retire1_valid,   // WA1 retire valid
  input [`npuarc_GRAD_TAG_RANGE]       wa_retire1_tag,     // WA1 retire Tag
  input [`npuarc_DOUBLE_RANGE]         wa_retire1_data,    // WA1 retire data


  
  ////////// Interface to RTT /////////////////////////////////////
  //
  output [1:0]                  ca_store_grad_tag,
 
  output                        dmp_st_retire0,
  output [1:0]                  dmp_st_retire0_tag,
  output [`npuarc_DMP_DATA_RANGE]      dmp_st_retire0_data,


  output                        dmp_st_retire1,
  output [1:0]                  dmp_st_retire1_tag,
  output [`npuarc_DMP_DATA_RANGE]      dmp_st_retire1_data,

  ////////// Privilege mode ////////////////////////////////////////////////
  //
  input                         ar_user_mode_r,
  
  ////////// Result Interface //////////////////////////////////////////////
  //
  output [`npuarc_DATA_RANGE]          dc4_fast_data,     // DC4 fast bypass data
  output [`npuarc_DMP_DATA_RANGE]      dmp_rf_wdata,      // aligned and sign extended
  output                        dmp_scond_zflag,   // indicate SCOND sucs/fail

  ////////// DMP SCOND monitor interface ////////////////////////////////////
  //
  output                        dmp_clear_lf,      // External write to LPA
  output                        rtt_dc4_scond_go,  // scond will be success

  ////////// X3 Exception Interface ///////////////////////////////////////////
  //
  output                        dc3_excpn,           // DMP excpn 
  output [`npuarc_DMP_EXCPN_RANGE]     dc3_excpn_type,      // exception type
  output [7:0]                  dc3_excpn_code,      // cause code

  ////////// Exception Interface //////////////////////////////////////////////
  //
  input                         holdup_excpn_r,
  output                        st_instrs_discarded,
  input                         st_instrs_discarded_r,
  output                        iexcpn_discarded,
  output                        dc4_replay,           // replay instr in DC4
  output                        dc4_excpn,            // DMP excpn
  output                        dc4_excpn_user_mode_r,// DMP excpn privilege
  output [`npuarc_PADDR_RANGE]         dc4_excpn_mem_addr,   // Addr of faulting inst
  output [7:0]                  dc4_excpn_type,       // exception type
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input                         ecc_dmp_disable,     // Disable all 1b and 2b errors
  input                         ecc_dmp_expn_disable,// Disable 2b error excpn
// spyglass enable_block W240
  output                        dc4_dc_dt_ecc_db_error,
  output                        dc4_dc_dd_ecc_db_error,
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
//    `endif 
  output                        dc4_dccm_ecc_db_error,
  output [`npuarc_SYNDROME_MSB:0]      fs_dccm_bank0_syndrome_r, 
  output [`npuarc_SYNDROME_MSB:0]      fs_dccm_bank1_syndrome_r, 
  output [`npuarc_SYNDROME_MSB:0]      fs_dccm_bank2_syndrome_r, 
  output [`npuarc_SYNDROME_MSB:0]      fs_dccm_bank3_syndrome_r, 

  output                        fs_dccm_bank0_ecc_sb_error_r,                   
  output                        fs_dccm_bank1_ecc_sb_error_r,                   
  output                        fs_dccm_bank2_ecc_sb_error_r,                   
  output                        fs_dccm_bank3_ecc_sb_error_r,                   

  output                        fs_dccm_bank0_ecc_db_error_r,          
  output                        fs_dccm_bank1_ecc_db_error_r,            
  output                        fs_dccm_bank2_ecc_db_error_r,              
  output                        fs_dccm_bank3_ecc_db_error_r,

//  `endif 
  ////////// Graduation Interface /////////////////////////////
  //
  output                        dc4_grad_req,      // grad without retirement req 
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                         ca_grad_ack,       // grad ack                     
// spyglass enable_block W240
  input [`npuarc_GRAD_TAG_RANGE]       ca_grad_tag,       // tag of graduating context  

  ////////// Post Commit Retirement Interface /////////////////////////////
  //
  output                        dmp_retire_req,    // retirement request          
  output [`npuarc_GRAD_TAG_RANGE]      dmp_retire_tag,    // tag of retiring context     
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                         retire_ack,        // retirement acknowledge      
// spyglass enable_block W240

  ////////// Interface with DCCM SRAMS////////////////////////////////////////
  //

  output                        clk_bank0_lo,   
  output                        clk_bank0_hi,   
  output                        dccm_bank0_cs_lo,  
  output                        dccm_bank0_cs_hi,  
  output [`npuarc_DCCM_ADDR_RANGE]     dccm_bank0_addr_lo,
  output [`npuarc_DCCM_ADDR_RANGE]     dccm_bank0_addr_hi,
  output                        dccm_bank0_we_lo,  
  output                        dccm_bank0_we_hi,  
  output [`npuarc_DBL_DCCM_BE_RANGE]   dccm_bank0_wem, 
  output [`npuarc_DBL_DCCM_RANGE]      dccm_bank0_din, 
  input  [`npuarc_DBL_DCCM_RANGE]      dccm_bank0_dout,
  
  output                        clk_bank1_lo,   
  output                        clk_bank1_hi,   
  output                        dccm_bank1_cs_lo,  
  output                        dccm_bank1_cs_hi,  
  output [`npuarc_DCCM_ADDR_RANGE]     dccm_bank1_addr_lo,
  output [`npuarc_DCCM_ADDR_RANGE]     dccm_bank1_addr_hi,
  output                        dccm_bank1_we_lo,  
  output                        dccm_bank1_we_hi,  
  output [`npuarc_DBL_DCCM_BE_RANGE]   dccm_bank1_wem, 
  output [`npuarc_DBL_DCCM_RANGE]      dccm_bank1_din, 
  input  [`npuarc_DBL_DCCM_RANGE]      dccm_bank1_dout,
  
  
  //////////  DMI interface (internal protocol) /////////////////////////////
  //
  input                         dmi_cmd_valid_r,
  output                        dmi_cmd_accept,             
  input                         dmi_cmd_read_r,
  input [`npuarc_CCM_AW-1:3]           dmi_cmd_addr_r,
  
  output                        dmi_rd_valid,
  output [`npuarc_DOUBLE_RANGE]        dmi_rd_data,
  output                        dmi_rd_err,
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                         dmi_rd_accept_r,
  input                         dmi_wr_valid_r,
// spyglass enable_block W240
  output                        dmi_wr_accept,
  input  [`npuarc_DOUBLE_RANGE]        dmi_wr_data_r,
  input  [`npuarc_DOUBLE_BE_RANGE]     dmi_wr_mask_r,
  output                        dmi_wr_done_r,
  output                        dmi_err_wr,
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



  ////////// Unified LQ/WQ Memory interface ///////////////////////////////////
  //
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





  ////////// Refill IBP Interace  //////////////////////////////////////////////////
  //
  output                        rf_cmd_valid,
  output [3:0]                  rf_cmd_cache,       
  output                        rf_cmd_excl, 
  output [2:0]                  rf_cmd_data_size, 
  input                         rf_cmd_accept,      
  output                        rf_cmd_read,        
  output  [`npuarc_PADDR_RANGE]        rf_cmd_addr,
  output                        rf_cmd_lock,        
  output                        rf_cmd_prot,        
  output                        rf_cmd_wrap,        
  output  [3:0]                 rf_cmd_burst_size,  

  input                         rf_rd_valid,        
  input                         rf_rd_last,         
  input                         rf_err_rd,          
  input [`npuarc_RF_CB_DATA_RANGE]     rf_rd_data,         
  output                        rf_rd_accept,       
  ////////// Copy back IBP interface ///////////////////////////////////////////
  //
  output                        cb_cmd_valid, 
  output [3:0]                  cb_cmd_cache,  
  output                        cb_cmd_excl,  
  output [2:0]                  cb_cmd_data_size,
  input                         cb_cmd_accept,    
  output                        cb_cmd_read,      
  output  [`npuarc_PADDR_RANGE]        cb_cmd_addr,  
  output                        cb_cmd_lock,    
  output                        cb_cmd_prot,      
  output                        cb_cmd_wrap,      
  output  [3:0]                 cb_cmd_burst_size,

  output                        cb_wr_valid,      
  input                         cb_wr_accept,     
  output                        cb_wr_last,       
  output  [`npuarc_RF_CB_DATA_RANGE]   cb_wr_data,       
  output  [`npuarc_RF_CB_MASK_RANGE]   cb_wr_mask,       
  input                         cb_wr_done,       
  input                         cb_err_wr,    
  output                        cb_wr_resp_accept,   

  output                        dccm_pct_dcbc,  // DCCM bank conflict
  ////////// Interface with PCT     ///////////////////////////////////////////
  //
  output                        dc_pct_dcm,      // Data Cache miss
  output                        dc_pct_dclm,     // Data Cache load miss
  output                        dc_pct_dcsm,     // Data Cache store miss
  output                        dc_pct_dcpm,     // Data Cache predictor miss
  output                        dc_pct_dcbc,     // Data Cache bank conflict
  output                        dc_pct_ivdc,     // Invalidate Data Cache 
  output                        dc_pct_ivdl,     // Invalidate Data Line  
  output                        dc_pct_flsh,     // Flush entire cache    
  output                        dc_pct_fldl,     // Flush data line       
  output                        dc_pct_bdcmstall, // Flush data line   
    
  
  output [`npuarc_DMP_TARGET_RANGE]    dc4_target_r,    // DC4 memory target
 
  ////////// Interface with aux ctl ///////////////////////////////////////////
  //
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                         aux_read,          //  (X3) Aux region read
  input                         aux_write,         //  (x3) Aux reagion write
  input [`npuarc_DATA_RANGE]           aux_wdata_r,       //  (WA) Aux write data
  input                         aux_dc_ren_r,      //  (X3) Aux region select
  input [4:0]                   aux_dc_raddr_r,    //  (X3) Aux region addr
  input                         aux_dc_wen_r,      //  (WA) Aux region select
  input [4:0]                   aux_dc_waddr_r,    //  (WA) Aux write addr
// spyglass enable_block W240
  
  output [`npuarc_DATA_RANGE]          aux_dc_rdata,      //  (X3) LR read data
  output                        aux_dc_illegal,    //  (X3) SR/LR illegal
  output                        aux_dc_k_rd,       //  (X3) needs Kernel Read
  output                        aux_dc_k_wr,       //  (X3) needs Kernel Write
  output                        aux_dc_unimpl,     //  (X3) Invalid Reg
  output                        aux_dc_serial_sr,  //  (X3) SR group flush pipe
  output                        aux_dc_strict_sr,  //  (X3) SR flush pipe
  output                        aux_dc_busy,

  ////////// Interface with EXU ///////////////////////////////////////////////
  //
  output                        aux_dc_x2_addr_pass,
  output [`npuarc_ADDR_RANGE]          aux_dc_x2_addr,
  input                         aux_dccm_ren_r,      //  (X3) Aux region select
  input                         aux_dccm_wen_r,      //  (WA) Aux region select
  
  output [`npuarc_DATA_RANGE]          aux_dccm_rdata,      //  (X3) LR read data
  output                        aux_dccm_illegal,    //  (X3) SR/LR illegal
  output                        aux_dccm_k_rd,       //  (X3) needs Kernel Read
  output                        aux_dccm_k_wr,       //  (X3) needs Kernel Write
  output                        aux_dccm_unimpl,     //  (X3) Invalid Reg
  output                        aux_dccm_serial_sr,  //  (X3) SR group flush pipe
  output                        aux_dccm_strict_sr,  //  (X3) SR flush pipe
  

  output [3:0]                  aux_dccm_r,           // DCCM base addres

  input                         aux_dper_ren_r,      //  (X3) Aux region select
  input                         aux_dper_raddr_r,    // 
  input                         aux_dper_wen_r,      //  (WA) Aux region select
  input                         aux_dper_waddr_r,    // 
  
  output [`npuarc_DATA_RANGE]          aux_dper_rdata,      //  (X3) LR read data
  output                        aux_dper_illegal,    //  (X3) SR/LR illegal
  output                        aux_dper_k_rd,       //  (X3) needs Kernel Read
  output                        aux_dper_k_wr,       //  (X3) needs Kernel Write
  output                        aux_dper_unimpl,     //  (X3) Invalid Reg
  output                        aux_dper_serial_sr,  //  (X3) SR group flush pipe
  output                        aux_dper_strict_sr,  //  (X3) SR flush pipe


  // Access type: user/kernel mode, pid shared bit (common to all req ports)
  input                         mmu_en_r,       // Enable TLB lookups
  input                         mmu_clock_req_r,// MMU clock request
  input                         mpu_en_r,  
  output                        x2_da0_transl,
  input                         shared_en_r,    // Shared lib enable (PID)
  input  [`npuarc_SASID_RANGE]         sasid_r,        // Current pid slib membership
  input  [`npuarc_MMU_PID_ASID_RANGE]  asid_r,         // Current pid.asid
                
  ////////// Interface to dtlb //////////////////////////////////////////////
  //
  // Consolidated dtlb update request (on miss(es))
  output                        dtlb_update_req,     // late (unreg) outputs
  output  [`npuarc_PD0_VPN_RANGE]      dtlb_update_req_vpn,

  // jtlb response to dtlb update request
  input                         jrsp_dtlb_update, 
  input                         jrsp_dtlb_update_hit,
  input                         jrsp_dtlb_multi_hit,
  input                         jrsp_dtlb_tlb_err,

  // insert / delete / Inval (aux) operations from jtlb
  input  [`npuarc_JCMD_RANGE]          jtlb_dtlb_cmd_r,    // command from jtlb (aux)
  input  [`npuarc_DTLB_INDEX_RANGE]    jtlb_dtlb_index_r,  // Aux addr for read/write
  input [7:0]         aux_memseg_r,
 
  // Interface to read utlb entries
  //
  output                        dtlb_rd_val,   // rd data reg in jtlb
  output [`npuarc_UTLB_ENTRY_RANGE]    dtlb_rd_data,  // LR read data (entry)

  ////////// Shared bus to uTLBs ////////////////////////////////////////////
  //
  // Entry data for update from jtlb; also used for lookups and write by jtlb
  input  [`npuarc_UTLB_ENTRY_RANGE]    jtlb_update_data,

  input                         wa_jtlb_lookup_start_r,
  input                         wa_jtlb_cancel,
  input                         dtlb_update_pend_r,
  output [1:0]                  dc4_dtlb_miss_r,
  output                        dc3_dtlb_miss_excpn_r,
  output                        dc3_dtlb_ovrlp_excpn_r,
  output                        dc3_dtlb_protv_excpn_r,
  output                        dc3_dtlb_ecc_excpn_r,
  ////////// Idle Status /////////////////////////////////////////////////////
  //
  input                         idle_req,
  
  output                        dmp_idle_r,
  output                        dmp_idle1_r,
  output                        dmp_queue_empty,
  output                        dmp_wr_pending_r,
  output                        dmp_aux_pending_r,
 
  ////////// Interface with clock ctrl //////////////////////////////////////
  //
  output                       dmp_unit_enable,
  output                       dmp_dmu_unit_enable,
  output                       dmp_lq_unit_enable,
  ////////// General input signals ///////////////////////////////////////////
  //
  input                         db_active_r,     // debug initiated
  input                         x3_db_exception, // X3 debug exception
  input                         db_exception_r,  // CA signal 
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input                         test_mode,             
// spyglass enable_block W240
  input                         l1_clock_active,
  input                         clk,             
  input                         clk_dmu,
  input                         clk_lq,
  input                         dbg_cache_rst_disable_r,
  input                         dccm_dmi_priority,
  input                         rst_a          
// leda NTL_CON37 on
// leda NTL_CON13C on
);

// wires
wire                         dc4_dt_miss_r;



// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variabled are not used in certain configurations

wire [3:0]                wq_dccm_top_bank_req_mask;
wire [3:0]                wq_dccm_sec_bank_req_mask;
wire                      wq_req_even_lo;  
wire  [`npuarc_DCCM_ADR_RANGE]   wq_addr_even_lo; 
wire  [`npuarc_DATA_RANGE]       wq_din_even_lo;  
wire  [3:0]               wq_wem_even_lo;  

wire                      wq_req_even_hi;  
wire  [`npuarc_DCCM_ADR_RANGE]   wq_addr_even_hi; 
wire  [`npuarc_DATA_RANGE]       wq_din_even_hi;  
wire  [3:0]               wq_wem_even_hi;  

wire                      wq_req_odd_lo;  
wire  [`npuarc_DCCM_ADR_RANGE]   wq_addr_odd_lo; 
wire  [`npuarc_DATA_RANGE]       wq_din_odd_lo;  
wire  [3:0]               wq_wem_odd_lo;  

wire                      wq_req_odd_hi;  
wire  [`npuarc_DCCM_ADR_RANGE]   wq_addr_odd_hi; 
wire  [`npuarc_DATA_RANGE]       wq_din_odd_hi;  
wire  [3:0]               wq_wem_odd_hi;  

wire                      wq_dccm_read_one;
wire                      wq_dccm_read_two;

wire                     dc4_dccm_ecc_excpn_r;
wire                     wq_req_dd_even_lo; 
wire [`npuarc_DC_ADR_RANGE]     wq_dd_addr_even_lo;
wire [`npuarc_DATA_RANGE]       wq_dd_din_even_lo; 
wire [`npuarc_DC_BE_RANGE]      wq_dd_wem_even_lo; 

wire                     wq_req_dd_even_hi; 
wire [`npuarc_DC_ADR_RANGE]     wq_dd_addr_even_hi;
wire [`npuarc_DATA_RANGE]       wq_dd_din_even_hi; 
wire [`npuarc_DC_BE_RANGE]      wq_dd_wem_even_hi; 

wire                     wq_req_dd_odd_lo;  
wire [`npuarc_DC_ADR_RANGE]     wq_dd_addr_odd_lo; 
wire [`npuarc_DATA_RANGE]       wq_dd_din_odd_lo;  
wire [`npuarc_DC_BE_RANGE]      wq_dd_wem_odd_lo;  

wire                     wq_req_dd_odd_hi;  
wire [`npuarc_DC_ADR_RANGE]     wq_dd_addr_odd_hi; 
wire [`npuarc_DATA_RANGE]       wq_dd_din_odd_hi;  
wire [`npuarc_DC_BE_RANGE]      wq_dd_wem_odd_hi; 

wire [`npuarc_DC_WAY_RANGE]     wq_dd_way_hot;    

wire                       dccm_rb_req;
wire [`npuarc_DBL_DCCM_LO_RANGE]  dccm_rb_data0_lo_r;
wire [`npuarc_DBL_DCCM_LO_RANGE]  dccm_rb_data0_hi_r;
wire [`npuarc_DBL_DCCM_LO_RANGE]  dccm_rb_data1_lo_r; 
wire [`npuarc_DBL_DCCM_LO_RANGE]  dccm_rb_data1_hi_r;  

wire [3:0]               dc4_dccm_ecc_sb_error_r;
wire                     dc4_dmi_scrubbing_conflict;
wire [`npuarc_DATA_RANGE]       dc4_ecc_data_even_lo;
wire [`npuarc_DATA_RANGE]       dc4_ecc_data_even_hi;
wire [`npuarc_DATA_RANGE]       dc4_ecc_data_odd_lo;
wire [`npuarc_DATA_RANGE]       dc4_ecc_data_odd_hi;

wire                     dc4_dc_ecc_db_error_r;


wire                           dc_rb_req;     
wire                           dc_dt_hit;     
wire [3:0]                     dc4_dccm_ecc_skid_sb_error_r;
wire [3:0]                     dc4_dccm_ecc_skid_db_error_r;
wire [3:0]                     dc4_dc_ecc_skid_sb_error_r;
wire [3:0]                     dc4_dc_ecc_skid_db_error_r;
wire [`npuarc_SYNDROME_MSB:0]         dc_skid_bank0_syndrome_r;
wire [`npuarc_SYNDROME_MSB:0]         dc_skid_bank1_syndrome_r;
wire [`npuarc_SYNDROME_MSB:0]         dc_skid_bank2_syndrome_r;
wire [`npuarc_SYNDROME_MSB:0]         dc_skid_bank3_syndrome_r;
   
wire [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc3_dd_data_even_lo;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc3_dd_data_even_hi;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc3_dd_data_odd_lo;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc3_dd_data_odd_hi;
wire [`npuarc_DC_TRAM_RANGE]          dc3_dt_even_w0;
wire [`npuarc_DC_TRAM_RANGE]          dc3_dt_even_w1;
wire [`npuarc_DC_TRAM_RANGE]          dc3_dt_odd_w0;
wire [`npuarc_DC_TRAM_RANGE]          dc3_dt_odd_w1;
wire [`npuarc_DCCM_DATA_ECC_RANGE]    dc3_dccm_data_even_lo;
wire [`npuarc_DCCM_DATA_ECC_RANGE]    dc3_dccm_data_even_hi;
wire [`npuarc_DCCM_DATA_ECC_RANGE]    dc3_dccm_data_odd_lo;
wire [`npuarc_DCCM_DATA_ECC_RANGE]    dc3_dccm_data_odd_hi;
wire                           dc3_even_way0_hit;
wire                           dc3_odd_way0_hit;

wire [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc_rb_bank0_lo_r;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc_rb_bank0_hi_r;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc_rb_bank1_lo_r;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE]  dc_rb_bank1_hi_r;

wire                     mq_rb_req;                       
wire                     mq_rb_err;  
wire                     mq_rb_user_mode;                     
wire [`npuarc_GRAD_TAG_RANGE]   mq_rb_tag;       
wire                     mq_rb_ack;                     
wire                     mq_sex;                       
wire [1:0]               mq_size;       
wire [3:0]               mq_bank_sel;                     
wire [`npuarc_PADDR_RANGE]      mq_rb_addr;                     
wire [`npuarc_DC_DATA_RANGE]    mq_rb_data;
wire                     mq_wr_err; 
wire                     mq_flush_err_req;
wire [`npuarc_DC_LBUF_RANGE]    mq_flush_err_addr;
wire                     mq_flush_err_ack;  
wire                     rf_err_req;
wire [`npuarc_DC_LBUF_RANGE]    rf_err_addr;    
wire [`npuarc_DC_DATA_RANGE]    rb_aln_data;                    

wire                     wq_err_r;        
wire                     wq_err_user_mode_r;        
wire  [`npuarc_PADDR_RANGE]     wq_err_addr_r;     
wire                     wq_err_ack;      
wire                     wq_dc_read;
wire                     wq_fwd_replay;
wire  [3:0]              wq_fwd_bank;
wire  [`npuarc_DATA_RANGE]      wq_fwd_data_bank0_lo;
wire  [`npuarc_DATA_RANGE]      wq_fwd_data_bank0_hi;
wire  [`npuarc_DATA_RANGE]      wq_fwd_data_bank1_lo;
wire  [`npuarc_DATA_RANGE]      wq_fwd_data_bank1_hi;
wire  [3:0]              wq_fwd_bank_r;
wire  [`npuarc_DATA_RANGE]      wq_fwd_data_bank0_lo_r;
wire  [`npuarc_DATA_RANGE]      wq_fwd_data_bank0_hi_r;
wire  [`npuarc_DATA_RANGE]      wq_fwd_data_bank1_lo_r;
wire  [`npuarc_DATA_RANGE]      wq_fwd_data_bank1_hi_r;

wire [15:0]              wq_skid_ctrl_mask;

wire                     lq_rb_req;  
wire                     lq_rb_err;  
wire                     lq_rb_user_mode;   
wire [`npuarc_GRAD_TAG_RANGE]   lq_rb_tag;       
wire                     lq_rb_sex;         
wire [1:0]               lq_rb_size;        
wire [`npuarc_PADDR_RANGE]      lq_rb_addr; 
wire                     lq_rb_ack;     
wire  [`npuarc_DOUBLE_RANGE]    lq_rb_data_even_r;               
wire  [`npuarc_DOUBLE_RANGE]    lq_rb_data_odd_r;               
wire                     rb_stall_r;
wire                      core_bank0_cs_lo_r;  
wire                      core_bank0_cs_hi_r;  
wire [`npuarc_DCCM_ADDR_RANGE]   core_bank0_addr_lo_r; 
wire [`npuarc_DCCM_ADDR_RANGE]   core_bank0_addr_hi_r; 
wire                      core_bank0_we_lo_r; 
wire                      core_bank0_we_hi_r; 
wire [`npuarc_DBL_DCCM_BE_RANGE] core_bank0_wem_r; 
wire [`npuarc_DBL_DCCM_RANGE]    core_bank0_din_r;
wire [`npuarc_DBL_DCCM_RANGE]    core_bank0_dout;
wire                      dccm_bank0_wait_lo;
wire                      dccm_bank0_wait_hi;
wire                      core_bank0_busy_lo_nxt;
wire                      core_bank0_busy_hi_nxt;
wire                      core_bank1_cs_lo_r;  
wire                      core_bank1_cs_hi_r;  
wire [`npuarc_DCCM_ADDR_RANGE]   core_bank1_addr_lo_r; 
wire [`npuarc_DCCM_ADDR_RANGE]   core_bank1_addr_hi_r; 
wire                      core_bank1_we_lo_r; 
wire                      core_bank1_we_hi_r; 
wire [`npuarc_DBL_DCCM_BE_RANGE] core_bank1_wem_r; 
wire [`npuarc_DBL_DCCM_RANGE]    core_bank1_din_r;
wire [`npuarc_DBL_DCCM_RANGE]    core_bank1_dout;
wire                      dccm_bank1_wait_lo;
wire                      dccm_bank1_wait_hi;
wire                      core_bank1_busy_lo_nxt;
wire                      core_bank1_busy_hi_nxt;
wire [`npuarc_DCCM_ADR_RANGE]   dc1_dccm_addr0;
wire [`npuarc_DCCM_ADR_RANGE]   dc1_dccm_addr1;
wire                     dc1_dccm_stall;
wire                     dc1_dccm_bank_conflict;
wire                     dc2_dccm_stall;
wire [3:0]               dc1_rmw;
wire [3:0]               dc2_rmw;
wire [3:0]               dc3_rmw_r;
wire [3:0]               dc4_rmw_r;
wire                     dc2_volatile_region0;
wire                     dc2_volatile_region1;
wire                     dc2_stuck;
wire                     dc4_dccm_ecc_replay;
wire                     dc4_dc_ecc_replay_r;
wire                     dc4_wq_skid_replay_r;
wire                     dc1_dc_stall;
wire                     dc2_cft_stall_r;
wire                     dc2_dc_uop_stall;
wire                     dc1_dt_line_cross;
wire [1:0]               dc1_dt_bank_sel;
wire [`npuarc_DC_IDX_RANGE]     dc1_dt_addr0;
wire [`npuarc_DC_IDX_RANGE]     dc1_dt_addr1;
wire [`npuarc_DC_ADR_RANGE]     dc1_dd_addr0;
wire [`npuarc_DC_ADR_RANGE]     dc1_dd_addr1;
wire                     dc3_dccm_poisoned;
wire                     dmu_evict_rd;
wire                     dc3_dc_poisoned;
wire [`npuarc_DC_WAY_RANGE]     dc3_dt_even_hit_way_hot_prel;
wire [`npuarc_DC_WAY_RANGE]     dc3_dt_even_hit_way_hot;
wire [`npuarc_DC_WAY_RANGE]     dc3_dt_odd_hit_way_hot_prel;
wire [`npuarc_DC_WAY_RANGE]     dc3_dt_odd_hit_way_hot;
wire                     dc3_dt_line_cross_r;
wire [1:0]               dc3_dt_bank_sel_r;
wire                     dc3_enable;

wire                     dc4_dt_line_cross_r;
wire [1:0]               dc4_dt_bank_sel_r;
wire                     dc3_dt_any_hit;
wire                     dc3_dt_hit;
wire                     dc3_dt_miss;
wire                     dc3_dt_miss_fast;
wire [`npuarc_PADDR_RANGE]      dc3_mem_addr_even; 
wire [`npuarc_PADDR_RANGE]      dc3_mem_addr_odd; 
wire                     dc3_pref;

wire [`npuarc_ADDR_RANGE]       dc2_mem_addr1_r;  
wire [2:0]               dc3_size0_r;  
wire [2:0]               dc3_size1_r;  
wire [`npuarc_PADDR_RANGE]      dc3_mem_addr1_r; 
wire                     dc3_fwd_allowed_r;
wire [2:0]               dc4_size0_r;  
wire [2:0]               dc4_size1_r;  
wire [`npuarc_PADDR_RANGE]      dc4_mem_addr1_r; 
wire [`npuarc_DMP_DATA_RANGE]   dc4_wr_data;   // CA write data

wire [`npuarc_DMP_TARGET_RANGE] dc1_target;
wire [`npuarc_DMP_TARGET_RANGE] dc2_target_r;
wire [`npuarc_DMP_TARGET_RANGE] dc3_target_r;
wire                     dc4_volatile_r;
wire                     dc4_strict_order_r;
wire [3:0]               dc4_data_mem_attr_r;

wire [3:0]               dc2_data_bank_sel_r;
wire [1:0]               dc2_data_bank_sel_lo_r;
wire [1:0]               dc2_data_bank_sel_hi_r;
wire [1:0]               dc3_data_bank_sel_lo_r;
wire [1:0]               dc3_data_bank_sel_hi_r;
wire [1:0]               dc4_data_bank_sel_lo_r;
wire [1:0]               dc4_data_bank_sel_hi_r;
wire                     dc3_partial_or_multi_conflict;
wire [`npuarc_DC_WAY_RANGE]     dc4_hit_even_way_hot_r;
wire [`npuarc_DC_WAY_RANGE]     dc4_hit_odd_way_hot_r; 
wire                     dc4_dt_hit_r;
wire                     dc4_cache_byp_r;
wire                     dc4_wq_ovf_replay_r;
wire                     dc4_wq_order_replay_r;
wire                     wq_dc4_fwd_replay_r;

wire                     dc3_fwd_req;

wire [`npuarc_DMP_FIFO_RANGE]   lq_order_ptr_1h;        
wire                     dc4_war_hazard; 
wire                     lq_cmd_read;    
wire [`npuarc_LQ_PTR_RANGE]     lq_cmd_rd_ptr;  
wire                     lq_data_retire; 
wire [`npuarc_LQ_PTR_RANGE]     lq_data_rd_ptr; 
wire                     lq_empty_r;     
wire                     lq_full_nxt;

wire                     rb_empty;

wire                     wa_replay_r;

wire                     wq_dc_entry;
wire                     wq_scond_entry;
wire                     wq_target_dc;        
wire                     wq_dmu_set_conflict;        
wire                     dc_skid_active;
wire                     wq_non_dc_entry;        
wire                     wq_retire;
wire                     wq_empty;    
wire                     wq_more_than_one_empty;    
wire                     dc4_wq_full;     
wire                     dc4_wq_one_empty;        
wire [`npuarc_DMP_FIFO_RANGE]   wq_order_ptr_1h;      
wire                     dc4_raw_hazard;       
wire                     wq_mem_per_iccm_read; 
wire [`npuarc_WQ_PTR_RANGE]     wq_rdentry0;          
wire                     wq_mem_retire;        
wire [`npuarc_WQ_PTR_RANGE]     wq_mem_entry_id;      

wire [3:0]               dc3_ecc_data_bank_sel; 
  
wire                     dmu_empty; 
wire                     mq_one_or_less_entry; 
wire [`npuarc_DC_SET_RANGE]     dmu_set_addr;    
wire                     dmu_mq_full; 
wire                     dmu_lsmq_full; 
wire                     lsmq_two_empty; 
wire                     dc4_lsmq_nomatch_replay; 
wire                     dmu_wr_pending;
wire                     dc4_mq_replay_r;
wire                     dc4_lsmq_replay_r;
wire                     aux_cache_off;
 
wire [3:0]               aux_dmp_dcache_attr_r;
wire                     aux_dmp_mem_attr_r;

wire  [3:0]              aux_volatile_base_r;
wire  [3:0]              aux_volatile_limit_r;
wire                     aux_volatile_strict_r;
wire                     aux_volatile_dis_r;



// leda NTL_CON13A on

wire                        lq_mem_cmd_valid; 
wire                        lq_mem_cmd_burst_size;                   
wire                        lq_mem_cmd_read;                  
wire                        lq_mem_cmd_accept;                
wire [`npuarc_PADDR_RANGE]         lq_mem_cmd_addr;                  
wire                        lq_mem_cmd_lock;                  
wire                        lq_mem_cmd_excl;
wire [1:0]                  lq_mem_cmd_data_size;                  
wire                        lq_mem_cmd_prot;                  

wire                        lq_mem_rd_valid;                  
wire                        lq_mem_err_rd;                  
wire                        lq_mem_rd_excl_ok;
wire                        lq_mem_rd_last;                   
wire                        lq_mem_rd_accept;                 
wire  [`npuarc_DOUBLE_RANGE]       lq_mem_rd_data;     

wire                        wq_mem_cmd_valid;   
wire                        wq_mem_cmd_cache;   
wire                        wq_mem_cmd_burst_size;   
wire                        wq_mem_cmd_accept;  
wire [`npuarc_PADDR_RANGE]         wq_mem_cmd_addr;    
wire [1:0]                  wq_mem_cmd_data_size;    
wire                        wq_mem_cmd_lock;                  
wire                        wq_mem_cmd_excl;
wire                        wq_mem_cmd_prot;                  

wire                        wq_mem_wr_valid;    
wire                        wq_mem_wr_last;    
wire                        wq_mem_wr_accept;   
wire [`npuarc_DOUBLE_BE_RANGE]     wq_mem_wr_mask;         
wire [`npuarc_DOUBLE_RANGE]        wq_mem_wr_data;    

wire                        wq_mem_wr_done;
wire                        wq_mem_wr_excl_done;
wire                        wq_mem_err_wr;
wire                        wq_mem_wr_resp_accept;



///////////////////////////////////////////////////////////////////////////
///// Lookup Interface (to dtlb) //////////////////////////////////////////
//
// Request bus 0 for uTLB lookup ---------------------------------------------
//
wire                           dtlb_lookup0_valid;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variable are not used in certain configurations
wire       [`npuarc_PADDR_RANGE]      dtlb_rslt0_paddr;
wire       [`npuarc_PD1_UA_RANGE]     dtlb_rslt0_user_attr;
wire                           dtlb_rslt0_wr_thru;
wire                           dtlb_rslt0_cached;

// Request bus 1 for uTLB lookup ---------------------------------------------
//
wire                           dtlb_lookup1_valid;

// Lookup result 1
wire       [`npuarc_PADDR_RANGE]      dtlb_rslt1_paddr;
wire       [`npuarc_PD1_UA_RANGE]     dtlb_rslt1_user_attr;
wire                           dtlb_rslt1_wr_thru;
wire                           dtlb_rslt1_cached;
// leda NTL_CON13A on
// dtlb exceptions
wire       [1:0]               dc2_dtlb_efa_mux;           
wire       [1:0]               dc2_dtlb_miss;
wire                           dc2_dtlb_miss_excpn;
wire                           dc2_dtlb_ovrlp_excpn;
wire                           dc2_dtlb_protv_excpn;
wire                           dc2_dtlb_ecc_error;
wire                           dc2_lkup1_npage_cross_r;
wire [`npuarc_DC_PRED_BIT_RANGE]      dc2_pred0_r;
wire [`npuarc_DC_PRED_BIT_RANGE]      dc2_pred1_r;
wire                           dc3_mispred;
wire                           dc4_mispred;

//wire [1:0]                     dc3_dtlb_miss_r;
wire                           dc3_lkup1_page_cross_r;

wire                           dc3_dtlb_ecc_error_r;
wire [1:0]                     dc3_dtlb_miss_r;

wire [`npuarc_PADDR_RANGE]            dc3_mem_addr0_r; // X3 memory address
wire                           dc4_pref_bad_r;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variabled are not used in certain configurations
wire                           dtlb_active;
// leda NTL_CON13A on

wire                           dc4_scond_go;
wire                           wq_scond_rb_req;     
wire  [`npuarc_GRAD_TAG_RANGE]        wq_scond_rb_tag;     
wire                           wq_scond_rb_flag;    
wire                           wq_scond_rb_ack;     
wire [7:0]                     aux_dc_x2_addr_hi;

wire [`npuarc_DATA_RANGE]             aux_dc_aux_rdata;     
wire                           aux_dc_aux_illegal;   
wire                           aux_dc_aux_k_rd;      
wire                           aux_dc_aux_k_wr;      
wire                           aux_dc_aux_unimpl;    
wire                           aux_dc_aux_serial_sr; 
wire                           aux_dc_aux_strict_sr; 
wire                           aux_dc_aux_busy;      





wire [3:0]                     dc3_skid_ecc_valid;

wire                          ecc0_even_sel;
wire                          ecc0_odd_sel;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_even_lo ;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_even_hi ;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_odd_lo  ;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_odd_hi  ;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_even_lo ;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_even_hi ;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_odd_lo  ;
wire [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_odd_hi  ;

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: DTLB                            
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_dtlb u_dtlb (

  ////////// General input signals ///////////////////////////////////////////
  //
  .clk                  (clk),            // Processor clock
  .rst                  (rst_a),          // Global reset

  .rst_init_disable_r   (dbg_cache_rst_disable_r),

  // Enable uTLB
  .utlb_en_r            (mmu_en_r),       // Enable TLB lookups (pid.t)
  .mpu_en_r             (mpu_en_r),  
  .x2_da0_transl        (x2_da0_transl       ),
  .mmu_clock_req_r      (mmu_clock_req_r),
  .utlb_active          (dtlb_active),
  .wa_restart_r         (wa_jtlb_cancel),
  .wa_jtlb_lookup_start_r (wa_jtlb_lookup_start_r), // flush/replay due to utlb miss
  .wa_hlt_restart_r     (wa_hlt_restart_r),


  .debug_op             (db_active_r),    // ld/st originated from debug
  .kernel_mode          (~ar_user_mode_r), // in Kernel mode
  .access_type_inst     (1'b0),           // instr or data access
  .access_type_rd       (x2_load_r),      // lkup for load (or ex) op
  .access_type_wr       (x2_store_r),     // lkup for store (or ex) op

  .shared_en_r          (shared_en_r),    // Shared lib enable (PID)
  .sasid_r              (sasid_r),        // Current pid slib membership

  ////////// Interface to translation client(s): fetch or dmp ///////////////
  //
  // Request bus 0 for uTLB lookup ---------------------------------------------
  // late inputs
  .lkup0_valid_r        (dtlb_lookup0_valid),
  .lkup0_vaddr_r        (x2_mem_addr0_r),
  .lkup0_asid_r         (asid_r),

  // Lookup result 
  .rslt0_paddr          (dtlb_rslt0_paddr),
  .rslt0_user_attr      (dtlb_rslt0_user_attr),
  .rslt0_wr_thru        (dtlb_rslt0_wr_thru),
  .rslt0_cached         (dtlb_rslt0_cached),

  .x2_pass              (x2_pass             ),
  .x2_size_r            (x2_size_r           ),
  .x2_pref_r            (x2_pref_r           ), 
  .dc2_dtlb_efa_mux     (dc2_dtlb_efa_mux    ),
  .dc2_dtlb_miss        (dc2_dtlb_miss       ),
  .dc2_dtlb_miss_excpn  (dc2_dtlb_miss_excpn ),
  .dc2_dtlb_ovrlp_excpn (dc2_dtlb_ovrlp_excpn),
  .dc2_dtlb_protv_excpn (dc2_dtlb_protv_excpn),
  .dc2_dtlb_ecc_error   (dc2_dtlb_ecc_error  ),
  // Request bus 1 for uTLB lookup ---------------------------------------------
  // late inputs
  .lkup1_valid_r        (dtlb_lookup1_valid),
  .lkup1_vaddr_r        (dc2_mem_addr1_r),
  .lkup1_asid_r         (asid_r),

  // Lookup result 
  .rslt1_paddr          (dtlb_rslt1_paddr),
  .rslt1_user_attr      (dtlb_rslt1_user_attr),
  .rslt1_wr_thru        (dtlb_rslt1_wr_thru),
  .rslt1_cached         (dtlb_rslt1_cached),

  ////////// Interface to jtlb //////////////////////////////////////////////
  //
  // Consolidated jtlb update request
  .jtlb_update_req      (dtlb_update_req),
  .jtlb_update_req_vpn  (dtlb_update_req_vpn),

  // jtlb response to update request
  .jrsp_update          (jrsp_dtlb_update), 
  .jrsp_update_hit      (jrsp_dtlb_update_hit),
  .jrsp_multi_hit       (jrsp_dtlb_multi_hit),
  .jrsp_tlb_err         (jrsp_dtlb_tlb_err),

  // Entry data for update from jtlb; also used for lookups by jtlb
  .entry_update_data    (jtlb_update_data), // new entry from jtlb
             
  // Inval / insert / update operations from jtlb
  .jtlb_cmd_r           (jtlb_dtlb_cmd_r),    // command from jtlb
  .jtlb_index_r         (jtlb_dtlb_index_r),  // Index for read/write
  .aux_memseg_r         (aux_memseg_r     ),
       
  // Interface to read utlb entries
  .entry_rd_val         (dtlb_rd_val),   // rd data valid
  .entry_rd_data        (dtlb_rd_data)   // LR read data (entry)
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: ALIAS_PRED                            
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_alias_pred   u_alb_dmp_alias_pred (
  .clk                  (clk                   ),
  .rst_a                (rst_a                 ),

  .mmu_en_r             (mmu_en_r              ),
  .db_active_r          (db_active_r           ),
  
  .x1_load_r            (x1_load_r             ),    
  .x1_store_r           (x1_store_r            ),    
  .x1_pass              (x1_pass               ),     
  .x1_uop_inst_r        (x1_uop_inst_r         ),
  .x1_addr_base         (x1_addr_base          ),
  .x1_addr_offset       (x1_addr_offset        ),
  .x1_mem_addr0         (x1_mem_addr0          ),
  .x1_mem_addr1         (x1_mem_addr1          ),

  .x2_load_r            (x2_load_r             ),    
  .x2_store_r           (x2_store_r            ),    
  .x2_pass              (x2_pass               ),        
  .x2_enable            (x2_enable             ),        
  .x2_uop_inst_r        (x2_uop_inst_r         ),        
  .dc2_pred0_r          (dc2_pred0_r           ),
  .dc2_pred1_r          (dc2_pred1_r           ),
  
  .x3_load_r            (x3_load_r             ),    
  .x3_store_r           (x3_store_r            ),    
  .x3_pass              (x3_pass               ),        
  .x3_enable            (x3_1_enable           ),
  .x3_uop_inst_r        (x3_uop_inst_r         ), 
  .dc3_dtlb_miss_r      (dc3_dtlb_miss_r       ), 
  .dc3_page_cross       (dc3_lkup1_page_cross_r),
  .dc3_mem_addr0_r      (dc3_mem_addr0_r       ),
  .dc3_mem_addr1_r      (dc3_mem_addr1_r       ),
  .dc3_target_r         (dc3_target_r          ),
  .dc3_mispred          (dc3_mispred           ),

  .ca_pass              (ca_pass               ),
  .ca_enable            (ca_enable             ),
  .ca_uop_inst_r        (ca_uop_inst_r         ),
  .dc4_dtlb_miss_r      (dc4_dtlb_miss_r       ),

  .wa_restart_r         (wa_restart_kill_r     ),
  .wa_replay_r          (wa_replay_r           ),
     
  .dc_pct_dcpm          (dc_pct_dcpm           ),

  .jrsp_dtlb_update     (jrsp_dtlb_update      ),
  .jrsp_dtlb_update_hit (jrsp_dtlb_update_hit  ),
  .jrsp_dtlb_multi_hit  (jrsp_dtlb_multi_hit   ),
  .jtlb_update_data     (jtlb_update_data      )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: Bank sel                             
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_bank_sel u_alb_dmp_bank_sel (
  .x1_size_r                (x1_size_r           ),
  .x1_cache_byp_r           (x1_cache_byp_r      ),
  .x1_pref_r                (x1_pref_r           ),
  .x1_mem_addr0             (x1_mem_addr0        ),   
  .x1_mem_addr1             (x1_mem_addr1        ),   
  
  .db_active_r              (db_active_r         ),
  .aux_dccm_r               (aux_dccm_r          ),

  .dc1_dccm_addr0           (dc1_dccm_addr0      ),
  .dc1_dccm_addr1           (dc1_dccm_addr1      ),
  .dc1_dt_bank_sel          (dc1_dt_bank_sel     ),
  .dc1_dt_line_cross        (dc1_dt_line_cross   ),
  .dc1_dt_addr0             (dc1_dt_addr0        ),
  .dc1_dt_addr1             (dc1_dt_addr1        ),
  .dc1_dd_addr0             (dc1_dd_addr0        ),
  .dc1_dd_addr1             (dc1_dd_addr1        ),
  .dc1_target               (dc1_target          )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: Staging of DMP specific information 
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_staging u_alb_dmp_staging (
  .clk                          (clk                   ), 
  .rst_a                        (rst_a                 ), 
  .db_active_r                  (db_active_r           ),
  .x1_pass                      (x1_pass               ), 
  .x1_load_r                    (x1_load_r             ), 
  .x1_store_r                   (x1_store_r            ), 
  .x1_size_r                    (x1_size_r             ), 
  .x1_cache_byp_r               (x1_cache_byp_r        ),
  .x1_mem_addr0                 (x1_mem_addr0          ),
  .x1_mem_addr1                 (x1_mem_addr1          ),
  .dc1_target                   (dc1_target            ), 
  .dc1_data_bank_sel_lo         (x1_bank_sel_lo        ), 
  .dc1_data_bank_sel_hi         (x1_bank_sel_hi        ), 
  .dc1_dt_bank_sel              (dc1_dt_bank_sel       ), 
  .dc1_dt_line_cross            (dc1_dt_line_cross     ),
  .aux_cache_off                (aux_cache_off         ),      
  .aux_volatile_base_r          (aux_volatile_base_r   ),
  .aux_volatile_limit_r         (aux_volatile_limit_r  ),
  .aux_volatile_strict_r        (aux_volatile_strict_r ),
  .aux_volatile_dis_r           (aux_volatile_dis_r    ),
  .aux_dmp_dcache_attr_r        (aux_dmp_dcache_attr_r ),     
  .aux_dmp_mem_attr_r           (aux_dmp_mem_attr_r    ),        
  .aux_dccm_r                   (aux_dccm_r            ),       
  .aux_memseg_r                 (aux_memseg_r          ),       
  .ecc_dmp_disable              (ecc_dmp_disable       ),
  .dc1_rmw                      (dc1_rmw               ),
  .x2_pass                      (x2_pass               ), 
  .x2_load_r                    (x2_load_r             ), 
  .x2_store_r                   (x2_store_r            ), 
  .x2_exu_stall                 (x2_exu_stall          ),
  .x2_cache_byp_r               (x2_cache_byp_r        ),
  .x2_mpu_data_flt              (x2_mpu_data_flt       ),
  .x2_mpu_data_unc              (x2_mpu_data_unc       ),
  .x2_locked_r                  (x2_locked_r           ),
  .x2_enable                    (x2_enable             ), 
  .x2_mem_addr0_r               (x2_mem_addr0_r        ),
  .dc2_dtlb_efa_mux             (dc2_dtlb_efa_mux      ),
  .dc2_dtlb_miss                (dc2_dtlb_miss         ),
  .dc2_dtlb_miss_excpn          (dc2_dtlb_miss_excpn   ),
  .dc2_dtlb_ovrlp_excpn         (dc2_dtlb_ovrlp_excpn  ),
  .dc2_dtlb_protv_excpn         (dc2_dtlb_protv_excpn  ),
  .dc2_dtlb_ecc_error           (dc2_dtlb_ecc_error    ),
  .dtlb_rslt0_paddr             (dtlb_rslt0_paddr      ),
  .dtlb_rslt1_paddr             (dtlb_rslt1_paddr      ),
  .dtlb_lookup0_valid           (dtlb_lookup0_valid    ),
  .dtlb_lookup1_valid           (dtlb_lookup1_valid    ),
  .dtlb_rslt0_cached            (dtlb_rslt0_cached     ),
  .dc2_lkup1_npage_cross_r      (dc2_lkup1_npage_cross_r),
  .dc2_aux_pass                 (aux_dc_x2_addr_pass   ),
  .dc2_aux_addr                 (aux_dc_x2_addr        ),
  .dc2_aux_addr_hi              (aux_dc_x2_addr_hi     ),
  .dc2_aux_bank                 (aux_dc_x2_addr[`npuarc_DC_TAG_BANK_ID]),
  .dc2_mem_addr1_r              (dc2_mem_addr1_r       ),
  .dc2_data_bank_sel_lo_r       (dc2_data_bank_sel_lo_r), 
  .dc2_data_bank_sel_hi_r       (dc2_data_bank_sel_hi_r), 
  .dc2_target_r                 (dc2_target_r          ),
  .dc2_data_bank_sel_r          (dc2_data_bank_sel_r   ),  
  .dc2_rmw                      (dc2_rmw               ),
  .dc2_volatile_region0         (dc2_volatile_region0  ),
  .dc2_volatile_region1         (dc2_volatile_region1  ),
  .dc2_stuck                    (dc2_stuck             ),
  .x3_pass                      (x3_pass               ), 
  .x3_load_r                    (x3_load_r             ), 
  .x3_store_r                   (x3_store_r            ), 
  .x3_pref_r                    (x3_pref_r             ), 
  .x3_pref_l2_r                 (x3_pref_l2_r          ), 
  .x3_prefw_r                   (x3_prefw_r            ), 
  .x3_pre_alloc_r               (x3_pre_alloc_r        ), 
  
  .x3_locked_r                  (x3_locked_r           ),
  .x3_enable                    (x3_1_enable           ),
  .dc3_dtlb_efa                 (dc3_dtlb_efa          ),
  .dc3_mem_addr0_r              (dc3_mem_addr0_r       ),
  .x3_mem_addr0_r               (x3_mem_addr0_r        ),

  .dc3_pref                     (dc3_pref              ),
  .dc3_target_r                 (dc3_target_r          ), 
  .dc3_size0_r                  (dc3_size0_r           ),   
  .dc3_size1_r                  (dc3_size1_r           ),   
  .dc3_mem_addr1_r              (dc3_mem_addr1_r       ),
  .dc3_data_bank_sel_lo_r       (dc3_data_bank_sel_lo_r),
  .dc3_data_bank_sel_hi_r       (dc3_data_bank_sel_hi_r),
  .dc3_rmw_r                    (dc3_rmw_r             ), 
  .dc3_fwd_allowed_r            (dc3_fwd_allowed_r     ), 
  .dc3_dtlb_ecc_error_r         (dc3_dtlb_ecc_error_r  ), 
  .dc3_dtlb_miss_r              (dc3_dtlb_miss_r       ), 
  .dc3_lkup1_page_cross_r       (dc3_lkup1_page_cross_r),
  .dc3_dtlb_miss_excpn          (dc3_dtlb_miss_excpn_r ),
  .dc3_dtlb_ovrlp_excpn         (dc3_dtlb_ovrlp_excpn_r),
  .dc3_dtlb_protv_excpn         (dc3_dtlb_protv_excpn_r),
  .dc3_dtlb_ecc_excpn           (dc3_dtlb_ecc_excpn_r  ),
  .dc3_mem_addr_even            (dc3_mem_addr_even     ),
  .dc3_mem_addr_odd             (dc3_mem_addr_odd      ),
  .dc3_dt_bank_sel_r            (dc3_dt_bank_sel_r     ),
  .dc3_dt_line_cross_r          (dc3_dt_line_cross_r   ),
  .dc3_enable                   (dc3_enable            ),
  .dc3_mispred                  (dc3_mispred           ),
  .ca_load_r                    (ca_load_r             ),
  .ca_store_r                   (ca_store_r            ),
  .ca_size_r                    (ca_size_r             ),
  .ca_wr_data_r                 (ca_wr_data_r          ),
  .ca_enable                    (ca_enable             ),
  .ca_locked_r                  (ca_locked_r           ),
  .dc4_dt_miss_r                (dc4_dt_miss_r         ),  
  .wa_lpa_r                     (wa_lpa_r              ),
  .wa_lock_flag_r               (wa_lock_flag_r        ),
  .wa_lock_double_r             (wa_lock_double_r      ),

  .dc4_dt_line_cross_r          (dc4_dt_line_cross_r   ),
  .dc4_dt_bank_sel_r            (dc4_dt_bank_sel_r     ),
  .dc4_scond_go                 (dc4_scond_go          ),
  .dmp_clear_lf                 (dmp_clear_lf          ),
  .dc4_dtlb_miss                (dc4_dtlb_miss_r       ),
  .dc4_mispred                  (dc4_mispred           ),
  .dc4_wr_data                  (dc4_wr_data           ),
  .dc4_pref_r                   (dc4_pref_r            ),
  .dc4_pref_bad_r               (dc4_pref_bad_r        ),  
  .dc4_cache_byp_r              (dc4_cache_byp_r       ),
  .dc4_target_r                 (dc4_target_r          ),
  .dc4_volatile_r               (dc4_volatile_r        ),
  .dc4_strict_order_r           (dc4_strict_order_r    ),
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Outputs connected to floating net
// SJ: Not all bits of data mem attributes used in this design
  .dc4_data_mem_attr_r          (dc4_data_mem_attr_r   ),
// spyglass enable_block UnloadedOutTerm-ML
  .dc4_size0_r                  (dc4_size0_r           ),
  .dc4_size1_r                  (dc4_size1_r           ),
  .dc4_mem_addr0_r              (ca_phys_addr_r        ),
  .dc4_mem_addr1_r              (dc4_mem_addr1_r       ),
  .dc4_rmw_r                    (dc4_rmw_r             ),
  .wa_restart_r                 (wa_restart_r          ),
  .wa_restart_kill_r            (wa_restart_kill_r     ),
  .wa_hlt_restart_r             (wa_hlt_restart_r      ), 

  .dc4_data_bank_sel_lo_r       (dc4_data_bank_sel_lo_r),
  .dc4_data_bank_sel_hi_r       (dc4_data_bank_sel_hi_r)

);

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: Stall control
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_stall_ctrl u_alb_dmp_stall_ctrl (
  .clk                      (clk                ),    
  .rst_a                    (rst_a              ),   
  .x1_load_r                (x1_load_r          ),
  .x1_store_r               (x1_store_r         ),
  .dc1_dccm_stall           (dc1_dccm_stall     ),
  .dc1_dc_stall             (dc1_dc_stall       ),
  .dtlb_update_pend_r       (dtlb_update_pend_r ),
  
  .x2_store_r               (x2_store_r         ),
  .x2_uop_inst_r            (x2_uop_inst_r      ),
  .x2_mem_addr0_r           (x2_mem_addr0_r[1:0]),
  .x2_locked_r              (x2_locked_r        ),
  .dc2_dccm_stall_r         (dc2_dccm_stall     ),
  .dc2_cft_stall_r          (dc2_cft_stall_r    ),
  .dc2_target_r             (dc2_target_r       ),
  .dc2_dc_uop_stall         (dc2_dc_uop_stall   ),
  
  .x3_pass                  (x3_pass            ),    
  .x3_load_r                (x3_load_r          ),
  .x3_pref_r                (dc3_pref           ),
  .x3_store_r               (x3_store_r         ),   
  .x3_locked_r              (x3_locked_r        ),   
  .dc3_rmw_r                (dc3_rmw_r          ),
  .x3_uop_inst_r            (x3_uop_inst_r      ),   
  .dc3_target_r             (dc3_target_r       ),
  .dc3_bank_sel_r           ({dc3_data_bank_sel_hi_r[1],
                              dc3_data_bank_sel_lo_r[1],          
                              dc3_data_bank_sel_hi_r[0],          
                              dc3_data_bank_sel_lo_r[0]}),   
  .dc3_dc_poisoned          (dc3_dc_poisoned    ),  
  
  .ca_load_r                (ca_load_r          ),
  .ca_store_r               (ca_store_r         ),
  .ca_locked_r              (ca_locked_r        ),   
  .dc4_rmw_r                (dc4_rmw_r          ),
  .ca_uop_inst_r            (ca_uop_inst_r      ),   
  .ca_pass                  (ca_pass            ), 
  .dc4_bank_sel_r           ({dc4_data_bank_sel_hi_r[1],
                              dc4_data_bank_sel_lo_r[1],
                              dc4_data_bank_sel_hi_r[0],
                              dc4_data_bank_sel_lo_r[0]}),
  .dc4_target_r             (dc4_target_r       ),
  .dc4_dt_bank_sel_r        (dc4_dt_bank_sel_r   ),
  .wa_restart_r             (wa_restart_kill_r  ), 

  .dc4_dccm_ecc_replay      (dc4_dccm_ecc_replay ),
  .dc4_dc_ecc_replay_r      (dc4_dc_ecc_replay_r ),
  .dc4_wq_ovf_replay_r      (dc4_wq_ovf_replay_r ),
  .dc4_wq_order_replay_r    (dc4_wq_order_replay_r),
  .wq_dc4_fwd_replay_r      (wq_dc4_fwd_replay_r),
  .dc4_wq_skid_replay_r     (dc4_wq_skid_replay_r),
  .dc4_dtlb_miss_r          (dc4_dtlb_miss_r    ),
  .dc4_mispred              (dc4_mispred        ),
 
  .wa_replay_r              (wa_replay_r        ),
  
  .lq_empty_r               (lq_empty_r         ),
  .lq_full_nxt              (lq_full_nxt        ),

  .dc4_wq_full              (dc4_wq_full        ),
  .dc4_wq_one_empty         (dc4_wq_one_empty   ),
  .wq_dc_entry              (wq_dc_entry        ),
  .wq_scond_entry           (wq_scond_entry    ),
  .wq_non_dc_entry          (wq_non_dc_entry    ),
  .wq_retire                (wq_retire          ),
  .wq_empty                 (wq_empty           ),
  .wq_more_than_one_empty   (wq_more_than_one_empty),

  .dc3_dt_hit               (dc3_dt_hit         ),
  .dc3_dt_miss              (dc3_dt_miss        ),
  .dc4_dt_hit_r             (dc4_dt_hit_r       ),
  .dc4_dt_miss_r            (dc4_dt_miss_r      ),
  .dmu_empty                (dmu_empty          ),
  .mq_one_or_less_entry     (mq_one_or_less_entry),
  .dmu_mq_full              (dmu_mq_full        ),
  .dmu_lsmq_full            (dmu_lsmq_full      ),
  .lsmq_two_empty           (lsmq_two_empty     ),
  .dc4_lsmq_nomatch_replay  (dc4_lsmq_nomatch_replay),
  .dc4_mq_replay_r          (dc4_mq_replay_r    ),
  .dc4_lsmq_replay_r        (dc4_lsmq_replay_r  ),
  .rb_stall_r               (rb_stall_r         ), 
  .dc1_stall                (dc1_stall          ),
  .dc2_stall                (dc2_stall          ),
  .dc4_stall                (dc4_stall_r        ),
  .dc4_replay               (dc4_replay         )    
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: DCCM                             
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_dccm u_alb_dmp_dccm (
  .l1_clock_active                  (l1_clock_active           ),
  .clk                              (clk                       ),  
  .rst_a                            (rst_a                     ),

  .dccm_dmi_priority                (dccm_dmi_priority         ),
  .core_bank0_cs_lo_r            (core_bank0_cs_lo_r     ),   
  .core_bank0_cs_hi_r            (core_bank0_cs_hi_r     ), 
  .core_bank0_addr_lo_r          (core_bank0_addr_lo_r   ), 
  .core_bank0_addr_hi_r          (core_bank0_addr_hi_r   ), 
  .core_bank0_we_lo_r            (core_bank0_we_lo_r     ),   
  .core_bank0_we_hi_r            (core_bank0_we_hi_r     ),   
  .core_bank0_wem_r              (core_bank0_wem_r       ),  
  .core_bank0_din_r              (core_bank0_din_r       ),
  
  .core_bank0_busy_lo_nxt        (core_bank0_busy_lo_nxt ), 
  .core_bank0_busy_hi_nxt        (core_bank0_busy_hi_nxt ), 
    
  .dccm_bank0_wait_lo            (dccm_bank0_wait_lo     ),
  .dccm_bank0_wait_hi            (dccm_bank0_wait_hi     ),
 
  .dccm_bank0_dout               (dccm_bank0_dout        ),

  .core_bank1_cs_lo_r            (core_bank1_cs_lo_r     ),   
  .core_bank1_cs_hi_r            (core_bank1_cs_hi_r     ), 
  .core_bank1_addr_lo_r          (core_bank1_addr_lo_r   ), 
  .core_bank1_addr_hi_r          (core_bank1_addr_hi_r   ), 
  .core_bank1_we_lo_r            (core_bank1_we_lo_r     ),   
  .core_bank1_we_hi_r            (core_bank1_we_hi_r     ),   
  .core_bank1_wem_r              (core_bank1_wem_r       ),  
  .core_bank1_din_r              (core_bank1_din_r       ),
  
  .core_bank1_busy_lo_nxt        (core_bank1_busy_lo_nxt ), 
  .core_bank1_busy_hi_nxt        (core_bank1_busy_hi_nxt ), 
    
  .dccm_bank1_wait_lo            (dccm_bank1_wait_lo     ),
  .dccm_bank1_wait_hi            (dccm_bank1_wait_hi     ),
 
  .dccm_bank1_dout               (dccm_bank1_dout        ),

  .x1_valid_r                       (x1_valid_r                ),  
  .x1_pass                          (x1_pass                   ),  
  .x1_load_r                        (x1_load_r                 ),  
  .x1_store_r                       (x1_store_r                ),  
  .dc1_target                       (dc1_target                ),
  .dc1_data_bank_sel_lo             (x1_bank_sel_lo            ),
  .dc1_data_bank_sel_hi             (x1_bank_sel_hi            ),
  .dc1_dccm_addr0                   (dc1_dccm_addr0            ),
  .dc1_dccm_addr1                   (dc1_dccm_addr1            ),
  .dc1_rmw                          (dc1_rmw                   ),
  .dc1_bank_conflict                (dc1_dccm_bank_conflict    ),  
  .dc1_stall                        (dc1_dccm_stall            ),

  .x2_valid_r                       (x2_valid_r                ), 
  .x2_pass                          (x2_pass                   ), 
  .x2_enable                        (x2_enable                 ),
  .x2_exu_stall                     (x2_exu_stall              ),
  .x2_load_r                        (x2_load_r                 ), 
  .x2_store_r                       (x2_store_r                ),
  .dc2_target_r                     (dc2_target_r              ),
  .dc2_data_bank_sel_r              (dc2_data_bank_sel_r       ),
  .dc2_stuck                        (dc2_stuck                 ),
  .dc2_rmw                          (dc2_rmw                   ),
  .dc2_cft_stall                    (dc2_cft_stall_r           ),
  .dc2_stall                        (dc2_dccm_stall            ),

  .x3_mem_addr0_r                   (x3_mem_addr0_r[`npuarc_DCCM_ADR_RANGE] ),
  .dc3_mem_addr1_r                  (dc3_mem_addr1_r[`npuarc_DCCM_ADR_RANGE]),
  .x3_valid_r                       (x3_valid_r                ),   
  .x3_pass                          (x3_pass                   ), 

  .x3_load_r                        (x3_load_r                 ),
  .x3_store_r                       (x3_store_r                ), 
  .dc3_target_r                     (dc3_target_r              ),
  .dc3_stall_r                      (dmp_dc3_stall_r           ),
  .dc3_partial_or_multi_conflict    (dc3_partial_or_multi_conflict),
  .dc3_bank_sel_r                   ({dc3_data_bank_sel_hi_r[1],
                                      dc3_data_bank_sel_lo_r[1],          
                                      dc3_data_bank_sel_hi_r[0],
                                      dc3_data_bank_sel_lo_r[0]}),
  .dc3_rmw_r                        (dc3_rmw_r                 ),
  .dc3_dccm_poisoned                (dc3_dccm_poisoned         ),
  .dc3_dccm_data_even_lo            (dc3_dccm_data_even_lo     ),
  .dc3_dccm_data_even_hi            (dc3_dccm_data_even_hi     ),
  .dc3_dccm_data_odd_lo             (dc3_dccm_data_odd_lo      ),
  .dc3_dccm_data_odd_hi             (dc3_dccm_data_odd_hi      ),
  .dc3_enable                       (dc3_enable                ),
  .dc3_skid_ecc_valid               (dc3_skid_ecc_valid        ),
  .dc3_excpn                        (dc3_excpn                 ),
  .ca_mem_addr0_r                   (ca_mem_addr0_r            ),
  .dc4_mem_addr1_r                  (dc4_mem_addr1_r           ),
  .ca_valid_r                       (ca_valid_r                ),
  .ca_load_r                        (ca_load_r                 ),
  .ca_store_r                       (ca_store_r                ),
  .ca_uop_inst_r                    (ca_uop_inst_r             ),
  .ca_enable                        (ca_enable                 ),
  .ca_pass                          (ca_pass                   ),
  .dc4_target_r                     (dc4_target_r              ),
  .dc4_stall_r                      (dc4_stall_r               ),
  .dc4_rmw_r                        (dc4_rmw_r                 ),

  .dc4_bank_sel_r                   ({dc4_data_bank_sel_hi_r[1],
                                      dc4_data_bank_sel_lo_r[1],
                                      dc4_data_bank_sel_hi_r[0],
                                      dc4_data_bank_sel_lo_r[0]}),
  
  .dc4_ecc_skid_sb_error_r          (dc4_dccm_ecc_skid_sb_error_r),   
  .dc4_ecc_skid_db_error_r          (dc4_dccm_ecc_skid_db_error_r),
  .dc_skid_bank0_syndrome_r         (dc_skid_bank0_syndrome_r    ),
  .dc_skid_bank1_syndrome_r         (dc_skid_bank1_syndrome_r    ),
  .dc_skid_bank2_syndrome_r         (dc_skid_bank2_syndrome_r    ),
  .dc_skid_bank3_syndrome_r         (dc_skid_bank3_syndrome_r    ),

  .wa_restart_r                     (wa_restart_kill_r         ),
         
  .wq_top_bank_req_mask             (wq_dccm_top_bank_req_mask ),
  .wq_sec_bank_req_mask             (wq_dccm_sec_bank_req_mask ),
 
  .wq_req_even_lo                   (wq_req_even_lo            ),  
  .wq_addr_even_lo                  (wq_addr_even_lo           ), 
  .wq_din_even_lo                   (wq_din_even_lo            ),  
  .wq_wem_even_lo                   (wq_wem_even_lo            ),  
  
  .wq_req_even_hi                   (wq_req_even_hi            ),  
  .wq_addr_even_hi                  (wq_addr_even_hi           ), 
  .wq_din_even_hi                   (wq_din_even_hi            ),  
  .wq_wem_even_hi                   (wq_wem_even_hi            ),  
  
  .wq_req_odd_lo                    (wq_req_odd_lo             ),  
  .wq_addr_odd_lo                   (wq_addr_odd_lo            ), 
  .wq_din_odd_lo                    (wq_din_odd_lo             ),  
  .wq_wem_odd_lo                    (wq_wem_odd_lo             ),  
  
  .wq_req_odd_hi                    (wq_req_odd_hi             ),  
  .wq_addr_odd_hi                   (wq_addr_odd_hi            ), 
  .wq_din_odd_hi                    (wq_din_odd_hi             ),  
  .wq_wem_odd_hi                    (wq_wem_odd_hi             ),  

  .wq_dc_entry                      (wq_dc_entry               ),
  .wq_empty                         (wq_empty                  ),

  .wq_dccm_read_one                 (wq_dccm_read_one          ),
  .wq_dccm_read_two                 (wq_dccm_read_two          ),
  .dmu_empty                        (dmu_empty                 ),
  .lq_empty_r                       (lq_empty_r                ), 
  .dmi_cmd_valid_r                  (dmi_cmd_valid_r           ),    
  .dmi_cmd_accept                   (dmi_cmd_accept            ),    
  .dmi_cmd_read_r                   (dmi_cmd_read_r            ),    
  .dmi_cmd_addr_r                   (dmi_cmd_addr_r            ),    
  
  .dmi_rd_valid                     (dmi_rd_valid              ),    
  .dmi_rd_data                      (dmi_rd_data               ),    
  .dmi_rd_err                       (dmi_rd_err                ),

  .dmi_wr_valid_r                   (dmi_wr_valid_r            ),    
  .dmi_wr_accept                    (dmi_wr_accept             ),    
  .dmi_wr_data_r                    (dmi_wr_data_r             ),    
  .dmi_wr_mask_r                    (dmi_wr_mask_r             ),    
  .dmi_wr_done_r                    (dmi_wr_done_r             ),    
  .dmi_err_wr_r                     (dmi_err_wr                ),
  
  .dccm_rb_req                      (dccm_rb_req               ),    
  .dccm_rb_data0_lo_r               (dccm_rb_data0_lo_r        ),
  .dccm_rb_data0_hi_r               (dccm_rb_data0_hi_r        ),
  .dccm_rb_data1_lo_r               (dccm_rb_data1_lo_r        ),
  .dccm_rb_data1_hi_r               (dccm_rb_data1_hi_r        ),
 
  .dc4_dccm_ecc_sb_error            (dc4_dccm_ecc_sb_error_r   ),
  .dc4_dmi_scrubbing_conflict       (dc4_dmi_scrubbing_conflict),
  .ecc_dmp_disable                  (ecc_dmp_disable           ),
  .ecc_dmp_expn_disable             (ecc_dmp_expn_disable      ),

  .dc4_dccm_ecc_db_error            (dc4_dccm_ecc_db_error     ),
  .fs_dccm_bank0_syndrome_r         (fs_dccm_bank0_syndrome_r  ), 
  .fs_dccm_bank1_syndrome_r         (fs_dccm_bank1_syndrome_r  ), 
  .fs_dccm_bank2_syndrome_r         (fs_dccm_bank2_syndrome_r  ), 
  .fs_dccm_bank3_syndrome_r         (fs_dccm_bank3_syndrome_r  ), 

  .fs_dccm_bank0_ecc_sb_error_r     (fs_dccm_bank0_ecc_sb_error_r), 
  .fs_dccm_bank1_ecc_sb_error_r     (fs_dccm_bank1_ecc_sb_error_r), 
  .fs_dccm_bank2_ecc_sb_error_r     (fs_dccm_bank2_ecc_sb_error_r), 
  .fs_dccm_bank3_ecc_sb_error_r     (fs_dccm_bank3_ecc_sb_error_r), 

  .fs_dccm_bank0_ecc_db_error_r     (fs_dccm_bank0_ecc_db_error_r),   
  .fs_dccm_bank1_ecc_db_error_r     (fs_dccm_bank1_ecc_db_error_r),     
  .fs_dccm_bank2_ecc_db_error_r     (fs_dccm_bank2_ecc_db_error_r),       
  .fs_dccm_bank3_ecc_db_error_r     (fs_dccm_bank3_ecc_db_error_r),
//  `endif
  .dc4_dccm_ecc_excpn_r             (dc4_dccm_ecc_excpn_r      ),
  .dc4_ecc_data_even_lo             (dc4_ecc_data_even_lo      ),
  .dc4_ecc_data_even_hi             (dc4_ecc_data_even_hi      ),
  .dc4_ecc_data_odd_lo              (dc4_ecc_data_odd_lo       ),
  .dc4_ecc_data_odd_hi              (dc4_ecc_data_odd_hi       ),

  .dc4_dccm_ecc_replay              (dc4_dccm_ecc_replay       ),

  .dccm_pct_dcbc                    (dccm_pct_dcbc             ),

  .aux_ren_r                        (aux_dccm_ren_r            ),  
  .aux_wen_r                        (aux_dccm_wen_r            ),  
  .aux_wdata_r                      (aux_wdata_r               ),  
  
  .aux_rdata                        (aux_dccm_rdata            ),  
  .aux_illegal                      (aux_dccm_illegal          ),  
  .aux_k_rd                         (aux_dccm_k_rd             ),  
  .aux_k_wr                         (aux_dccm_k_wr             ),  
  .aux_unimpl                       (aux_dccm_unimpl           ),  
  .aux_serial_sr                    (aux_dccm_serial_sr        ), 
  .aux_strict_sr                    (aux_dccm_strict_sr        ),
  
  .aux_dccm_r                       (aux_dccm_r                )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: DCCM if. This can be shared in a multi-core
// implementation  with shared DCCM                           
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dccm_if u_alb_dccm_if(
  .core0_bank0_cs_lo_r            (core_bank0_cs_lo_r      ),   
  .core0_bank0_cs_hi_r            (core_bank0_cs_hi_r      ),   
  .core0_bank0_addr_lo_r          (core_bank0_addr_lo_r    ), 
  .core0_bank0_addr_hi_r          (core_bank0_addr_hi_r    ), 
  .core0_bank0_we_lo_r            (core_bank0_we_lo_r      ),   
  .core0_bank0_we_hi_r            (core_bank0_we_hi_r      ),   
  .core0_bank0_wem_r              (core_bank0_wem_r        ),  
  .core0_bank0_din_r              (core_bank0_din_r        ),

  .core0_bank0_busy_lo_nxt        (core_bank0_busy_lo_nxt  ),   
  .core0_bank0_busy_hi_nxt        (core_bank0_busy_hi_nxt),   
      
  .core0_bank0_dout               (core_bank0_dout         ),
  .dccm_core0_bank0_wait_lo       (dccm_bank0_wait_lo      ),
  .dccm_core0_bank0_wait_hi       (dccm_bank0_wait_hi      ),
  .core0_bank1_cs_lo_r            (core_bank1_cs_lo_r      ),   
  .core0_bank1_cs_hi_r            (core_bank1_cs_hi_r      ),   
  .core0_bank1_addr_lo_r          (core_bank1_addr_lo_r    ), 
  .core0_bank1_addr_hi_r          (core_bank1_addr_hi_r    ), 
  .core0_bank1_we_lo_r            (core_bank1_we_lo_r      ),   
  .core0_bank1_we_hi_r            (core_bank1_we_hi_r      ),   
  .core0_bank1_wem_r              (core_bank1_wem_r        ),  
  .core0_bank1_din_r              (core_bank1_din_r        ),

  .core0_bank1_busy_lo_nxt        (core_bank1_busy_lo_nxt  ),   
  .core0_bank1_busy_hi_nxt        (core_bank1_busy_hi_nxt),   
      
  .core0_bank1_dout               (core_bank1_dout         ),
  .dccm_core0_bank1_wait_lo       (dccm_bank1_wait_lo      ),
  .dccm_core0_bank1_wait_hi       (dccm_bank1_wait_hi      ),
  
  .clk_bank0_lo                   (clk_bank0_lo           ),  
  .clk_bank0_hi                   (clk_bank0_hi           ),  
  .dccm_bank0_cs_lo               (dccm_bank0_cs_lo       ),  
  .dccm_bank0_cs_hi               (dccm_bank0_cs_hi       ),  
  .dccm_bank0_addr_lo             (dccm_bank0_addr_lo     ), 
  .dccm_bank0_addr_hi             (dccm_bank0_addr_hi     ), 
  .dccm_bank0_we_lo               (dccm_bank0_we_lo       ),  
  .dccm_bank0_we_hi               (dccm_bank0_we_hi       ),  
  .dccm_bank0_wem                 (dccm_bank0_wem         ),  
  .dccm_bank0_din                 (dccm_bank0_din         ),
  
  .dccm_bank0_dout                (dccm_bank0_dout        ),  
                    
  .clk_bank1_lo                   (clk_bank1_lo           ),  
  .clk_bank1_hi                   (clk_bank1_hi           ),  
  .dccm_bank1_cs_lo               (dccm_bank1_cs_lo       ),  
  .dccm_bank1_cs_hi               (dccm_bank1_cs_hi       ),  
  .dccm_bank1_addr_lo             (dccm_bank1_addr_lo     ), 
  .dccm_bank1_addr_hi             (dccm_bank1_addr_hi     ), 
  .dccm_bank1_we_lo               (dccm_bank1_we_lo       ),  
  .dccm_bank1_we_hi               (dccm_bank1_we_hi       ),  
  .dccm_bank1_wem                 (dccm_bank1_wem         ),  
  .dccm_bank1_din                 (dccm_bank1_din         ),
  
  .dccm_bank1_dout                (dccm_bank1_dout        ),  
                    
  .clk                               (clk                       ),
  .rst_a                             (rst_a                     )
);

//////////////////////////////////////////////////////////////////////////////
//
// Module instantiation: SKID BUFFER
//
/////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_skid_buffer u_alb_dmp_skid_buffer (
  .clk                            (clk                           ),
  .rst_a                          (rst_a                         ),
  .ecc0_even_sel                  (ecc0_even_sel                 ),
  .ecc0_odd_sel                   (ecc0_odd_sel                  ),
  .dc3_dd_data_ecc0_even_lo       (dc3_dd_data_ecc0_even_lo      ),
  .dc3_dd_data_ecc0_even_hi       (dc3_dd_data_ecc0_even_hi      ),
  .dc3_dd_data_ecc0_odd_lo        (dc3_dd_data_ecc0_odd_lo       ),
  .dc3_dd_data_ecc0_odd_hi        (dc3_dd_data_ecc0_odd_hi       ),
  .dc3_dd_data_ecc1_even_lo       (dc3_dd_data_ecc1_even_lo      ),
  .dc3_dd_data_ecc1_even_hi       (dc3_dd_data_ecc1_even_hi      ),
  .dc3_dd_data_ecc1_odd_lo        (dc3_dd_data_ecc1_odd_lo       ),
  .dc3_dd_data_ecc1_odd_hi        (dc3_dd_data_ecc1_odd_hi       ),
  .ecc_dmp_disable                (ecc_dmp_disable               ),
//`if ( (`DC_ECC == 1) || (`DC_PARITY == 1) || (`DCCM_ECC == 1) || (`DCCM_PARITY == 1))
  .dc3_bank_sel_r                ({dc3_data_bank_sel_hi_r[1],
                                   dc3_data_bank_sel_lo_r[1],
                                   dc3_data_bank_sel_hi_r[0],
                                   dc3_data_bank_sel_lo_r[0]}    ),
//`endif
  .x3_load_r                      (x3_load_r                     ),
  .x3_store_r                     (x3_store_r                    ),
  .x3_pass                        (x3_pass                       ),
  .dc3_target_r                   (dc3_target_r                  ),
  .dc3_stall_r                    (dmp_dc3_stall_r               ),
  .dc3_rmw_r                      (dc3_rmw_r                     ),
  .dc3_skid_ecc_valid             (dc3_skid_ecc_valid            ),
  .dc3_pref                       (dc3_pref                      ),
  .dc3_dt_bank_sel_r              (dc3_dt_bank_sel_r             ),
  .ca_enable                      (ca_enable                     ),
  
  .dc_data_even_dout_lo           (dc_data_even_dout_lo          ),
  .dc_data_even_dout_hi           (dc_data_even_dout_hi          ),
  .dc_data_odd_dout_lo            (dc_data_odd_dout_lo           ),
  .dc_data_odd_dout_hi            (dc_data_odd_dout_hi           ),
  .dc_tag_even_dout_w0           (dc_tag_even_dout_w0          ),    
  .dc_tag_odd_dout_w0            (dc_tag_odd_dout_w0           ),
  .dc_tag_even_dout_w1           (dc_tag_even_dout_w1          ),    
  .dc_tag_odd_dout_w1            (dc_tag_odd_dout_w1           ),
  .bank0_dout                     (core_bank0_dout               ), 
  .bank1_dout                     (core_bank1_dout               ), 
  .dc3_even_way0_hit              (dc3_even_way0_hit             ),
  .dc3_odd_way0_hit               (dc3_odd_way0_hit              ),
  .dmu_evict_rd                   (dmu_evict_rd                  ),
  .dc3_dc_poisoned                (dc3_dc_poisoned               ),
  .dc3_dt_even_hit_way_hot_prel   (dc3_dt_even_hit_way_hot_prel  ),
  .dc3_dt_odd_hit_way_hot_prel    (dc3_dt_odd_hit_way_hot_prel   ),

  .dc3_ecc_data_bank_sel          (dc3_ecc_data_bank_sel         ),

  .wa_restart_r                   (wa_restart_kill_r             ),
  .wq_fwd_bank                    (wq_fwd_bank                   ),
  .wq_fwd_replay                  (wq_fwd_replay                 ),
  .wq_ctrl_mask                   (wq_skid_ctrl_mask             ),
  .wq_dc_data_even_lo             (wq_din_even_lo), 
  .wq_dc_data_even_hi             (wq_din_even_hi), 
  .wq_dc_data_odd_lo              (wq_din_odd_lo), 
  .wq_dc_data_odd_hi              (wq_din_odd_hi), 

  .dc3_dt_even_hit_way_hot        (dc3_dt_even_hit_way_hot       ),
  .dc3_dt_odd_hit_way_hot         (dc3_dt_odd_hit_way_hot        ),
  .dc3_dd_data_even_lo            (dc3_dd_data_even_lo           ),
  .dc3_dd_data_even_hi            (dc3_dd_data_even_hi           ),
  .dc3_dd_data_odd_lo             (dc3_dd_data_odd_lo            ),
  .dc3_dd_data_odd_hi             (dc3_dd_data_odd_hi            ),
  .dc3_dt_even_w0                 (dc3_dt_even_w0                ),
  .dc3_dt_even_w1                 (dc3_dt_even_w1                ),
  .dc3_dt_odd_w0                  (dc3_dt_odd_w0                 ),
  .dc3_dt_odd_w1                  (dc3_dt_odd_w1                 ),
  .dc3_dccm_data_even_lo          (dc3_dccm_data_even_lo         ),
  .dc3_dccm_data_even_hi          (dc3_dccm_data_even_hi         ),
  .dc3_dccm_data_odd_lo           (dc3_dccm_data_odd_lo          ),
  .dc3_dccm_data_odd_hi           (dc3_dccm_data_odd_hi          ),


  .dc4_wq_skid_replay_r           (dc4_wq_skid_replay_r          ),

  .dc4_dccm_ecc_skid_sb_error_r   (dc4_dccm_ecc_skid_sb_error_r  ),
  .dc4_dccm_ecc_skid_db_error_r   (dc4_dccm_ecc_skid_db_error_r  ),
  .dc4_dc_ecc_skid_sb_error_r     (dc4_dc_ecc_skid_sb_error_r    ),   
  .dc4_dc_ecc_skid_db_error_r     (dc4_dc_ecc_skid_db_error_r    ),   

  .dc_skid_bank0_syndrome_r       (dc_skid_bank0_syndrome_r      ),
  .dc_skid_bank1_syndrome_r       (dc_skid_bank1_syndrome_r      ),
  .dc_skid_bank2_syndrome_r       (dc_skid_bank2_syndrome_r      ),
  .dc_skid_bank3_syndrome_r       (dc_skid_bank3_syndrome_r      ),

     
  .dc_skid_active                 (dc_skid_active                )
);  

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: DCACHE                             
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_dcache u_alb_dmp_dcache (
  

  .ecc0_even_sel                  (ecc0_even_sel                 ),
  .ecc0_odd_sel                   (ecc0_odd_sel                  ),
  .dc3_dd_data_ecc0_even_lo       (dc3_dd_data_ecc0_even_lo      ),
  .dc3_dd_data_ecc0_even_hi       (dc3_dd_data_ecc0_even_hi      ),
  .dc3_dd_data_ecc0_odd_lo        (dc3_dd_data_ecc0_odd_lo       ),
  .dc3_dd_data_ecc0_odd_hi        (dc3_dd_data_ecc0_odd_hi       ),
  .dc3_dd_data_ecc1_even_lo       (dc3_dd_data_ecc1_even_lo      ),
  .dc3_dd_data_ecc1_even_hi       (dc3_dd_data_ecc1_even_hi      ),
  .dc3_dd_data_ecc1_odd_lo        (dc3_dd_data_ecc1_odd_lo       ),
  .dc3_dd_data_ecc1_odd_hi        (dc3_dd_data_ecc1_odd_hi       ),
  .x1_valid_r             (x1_valid_r          ),  
  .x1_pass                (x1_pass             ),  
  .x1_load_r              (x1_load_r           ),  
  .x1_store_r             (x1_store_r          ),  
  .x1_pref_r              (x1_pref_r           ),  
  .x1_cache_byp_r         (x1_cache_byp_r      ), 
  .x1_uop_inst_r          (x1_uop_inst_r       ),  

  .dc1_data_bank_sel_lo   (x1_bank_sel_lo      ),
  .dc1_data_bank_sel_hi   (x1_bank_sel_hi      ),

  .dc1_dt_bank_sel        (dc1_dt_bank_sel     ),   
  .dc1_dt_addr0           (dc1_dt_addr0        ),   
  .dc1_dt_addr1           (dc1_dt_addr1        ),   
  .dc1_target             (dc1_target          ),

  .dc1_dd_addr0           (dc1_dd_addr0        ),  
  .dc1_dd_addr1           (dc1_dd_addr1        ),  
  .dc1_rmw                (dc1_rmw             ),
  .dc1_dccm_bank_conflict (dc1_dccm_bank_conflict),
  .dc1_stall              (dc1_dc_stall        ),  

  .x2_pass                (x2_pass             ),   
  .x2_enable              (x2_enable           ),  
  .x2_exu_stall           (x2_exu_stall        ),  
  .x2_load_r              (x2_load_r           ),  
  .x2_store_r             (x2_store_r          ),  
  .x2_mem_addr0_r         (x2_mem_addr0_r      ),
  .dc2_pred0_r            (dc2_pred0_r         ),
  .dc2_pred1_r            (dc2_pred1_r         ),
  .dc2_lkup1_page_cross   (dc2_lkup1_npage_cross_r),
  .dc2_target_r           (dc2_target_r        ), 
  .dc2_data_bank_sel_r    (dc2_data_bank_sel_r ),
  .dc2_stuck              (dc2_stuck           ),
  .dc2_rmw                (dc2_rmw             ),
  .dc2_cft_stall          (dc2_cft_stall_r     ), 

  .x3_valid_r             (x3_valid_r          ),  
  .x3_pass                (x3_pass             ),   
  .x3_enable              (x3_1_enable         ),
  .x3_load_r              (x3_load_r           ),  
  .x3_store_r             (x3_store_r          ), 
  .x3_locked_r            (x3_locked_r         ),  
  .x3_uop_inst_r          (x3_uop_inst_r       ), 
  .x3_size_r              (x3_size_r           ),  
  .x3_mem_addr0_r         (dc3_mem_addr0_r     ),
  .dc3_mem_addr1_r        (dc3_mem_addr1_r     ),
  .dc3_stall_r            (dmp_dc3_stall_r     ),    
  .dc3_partial_or_multi_conflict (dc3_partial_or_multi_conflict),
  .dc3_rmw_r              (dc3_rmw_r           ),
  .dc3_dtlb_ecc_error_r   (dc3_dtlb_ecc_error_r),
  .dc3_dtlb_miss_r        (dc3_dtlb_miss_r     ),
  .dc3_mispred            (dc3_mispred         ),

  .dc3_enable             (dc3_enable          ),
  .dc3_skid_ecc_valid     (dc3_skid_ecc_valid  ),
      
  .dc3_dccm_poisoned      (dc3_dccm_poisoned   ),
  .dc3_dt_line_cross_r    (dc3_dt_line_cross_r ),
  .dc3_dt_bank_sel_r      (dc3_dt_bank_sel_r   ),
  .dc3_target_r           (dc3_target_r        ),
  .dc3_mem_addr_even      (dc3_mem_addr_even   ), 
  .dc3_mem_addr_odd       (dc3_mem_addr_odd    ), 
  
  .dc3_dc_poisoned        (dc3_dc_poisoned     ),
  .dc3_dt_any_hit         (dc3_dt_any_hit      ),
  .dc3_dt_hit             (dc3_dt_hit          ),
  .dc3_dt_miss            (dc3_dt_miss         ),
  .dc3_dt_miss_fast       (dc3_dt_miss_fast    ),
 
  .dc3_ecc_data_bank_sel  (dc3_ecc_data_bank_sel),

  .dc4_dt_hit_r           (dc4_dt_hit_r        ),
  .dc4_dt_miss_r          (dc4_dt_miss_r       ),
  .dmu_mq_full            (dmu_mq_full         ),
  .dmu_lsmq_full          (dmu_lsmq_full       ),
  .lsmq_two_empty         (lsmq_two_empty      ),
  .dc4_lsmq_nomatch_replay(dc4_lsmq_nomatch_replay),
  .dmu_wr_pending         (dmu_wr_pending      ),

  .ecc_dc_tag_sbe_count_r (ecc_dc_tag_sbe_count_r ),  
  .dc_tag_ecc_sbe_clr     (dc_tag_ecc_sbe_clr     ), 
  .ecc_dc_data_sbe_count_r(ecc_dc_data_sbe_count_r),
  .dc_data_ecc_sbe_clr    (dc_data_ecc_sbe_clr    ),

  .ca_enable              (ca_enable           ),      
  .ca_valid_r             (ca_valid_r          ),  
  .ca_pass                (ca_pass             ),   
  .ca_load_r              (ca_load_r           ),  
  .ca_pref_r              (ca_pref_r           ),  
  .ca_pref_l2_r           (ca_pref_l2_r        ),  
  .ca_prefw_r             (ca_prefw_r          ),  
  .ca_pre_alloc_r         (ca_pre_alloc_r      ),  
  .dc4_pref_bad_r         (dc4_pref_bad_r      ),  
  .ca_store_r             (ca_store_r          ), 
  .ca_locked_r            (ca_locked_r         ),
  .ca_uop_inst_r          (ca_uop_inst_r       ), 
  .ca_size_r              (ca_size_r           ),  
  .ca_sex_r               (ca_sex_r            ),  
  .ca_userm_r             (ar_user_mode_r      ),  
  .ca_grad_tag            (ca_grad_tag         ),
  .ca_mem_addr0_r         (ca_phys_addr_r      ),
  .dc4_mem_addr1_r        (dc4_mem_addr1_r     ), 
  .dc4_ecc_skid_sb_error_r (dc4_dc_ecc_skid_sb_error_r),   
  .dc4_ecc_skid_db_error_r (dc4_dc_ecc_skid_db_error_r),   
  .dc_skid_bank0_syndrome_r(dc_skid_bank0_syndrome_r),
  .dc_skid_bank1_syndrome_r(dc_skid_bank1_syndrome_r),
  .dc_skid_bank2_syndrome_r(dc_skid_bank2_syndrome_r),
  .dc_skid_bank3_syndrome_r(dc_skid_bank3_syndrome_r),

  .ca_wr_data_r           (dc4_wr_data         ),  
  .dc4_dt_line_cross_r    (dc4_dt_line_cross_r ),
  .dc4_scond_go           (dc4_scond_go        ),
  .dc4_target_r           (dc4_target_r        ),
  .dc4_stall_r            (dc4_stall_r         ), 
  .dc4_mq_replay_r        (dc4_mq_replay_r     ),
  .dc4_lsmq_replay_r      (dc4_lsmq_replay_r   ),
  .dc4_wq_order_replay_r  (dc4_wq_order_replay_r),
  .dc4_rmw_r              (dc4_rmw_r           ),
  .dc4_dc_ecc_db_error    (dc4_dc_ecc_db_error_r    ), 

  .ecc_dmp_disable        (ecc_dmp_disable          ),
  .ecc_dmp_expn_disable   (ecc_dmp_expn_disable     ),

  .dc4_dc_dt_ecc_db_error  (dc4_dc_dt_ecc_db_error  ), 
  .dc4_dc_dd_ecc_db_error  (dc4_dc_dd_ecc_db_error  ), 
  .fs_dc_tag_bank0_syndrome_r(fs_dc_tag_bank0_syndrome_r),
  .fs_dc_tag_bank1_syndrome_r(fs_dc_tag_bank1_syndrome_r),
  .fs_dc_tag_bank2_syndrome_r(fs_dc_tag_bank2_syndrome_r),
  .fs_dc_tag_bank3_syndrome_r(fs_dc_tag_bank3_syndrome_r),

  .fs_dc_tag_bank0_ecc_sb_error_r(fs_dc_tag_bank0_ecc_sb_error_r),
  .fs_dc_tag_bank1_ecc_sb_error_r(fs_dc_tag_bank1_ecc_sb_error_r),
  .fs_dc_tag_bank2_ecc_sb_error_r(fs_dc_tag_bank2_ecc_sb_error_r),
  .fs_dc_tag_bank3_ecc_sb_error_r(fs_dc_tag_bank3_ecc_sb_error_r),

  .fs_dc_tag_bank0_ecc_db_error_r(fs_dc_tag_bank0_ecc_db_error_r),
  .fs_dc_tag_bank1_ecc_db_error_r(fs_dc_tag_bank1_ecc_db_error_r),
  .fs_dc_tag_bank2_ecc_db_error_r(fs_dc_tag_bank2_ecc_db_error_r),
  .fs_dc_tag_bank3_ecc_db_error_r(fs_dc_tag_bank3_ecc_db_error_r),

  .fs_dc_data_bank0_syndrome_r(fs_dc_data_bank0_syndrome_r), 
  .fs_dc_data_bank1_syndrome_r(fs_dc_data_bank1_syndrome_r), 
  .fs_dc_data_bank2_syndrome_r(fs_dc_data_bank2_syndrome_r), 
  .fs_dc_data_bank3_syndrome_r(fs_dc_data_bank3_syndrome_r), 

  .fs_dc_data_bank0_ecc_sb_error_r(fs_dc_data_bank0_ecc_sb_error_r),
  .fs_dc_data_bank1_ecc_sb_error_r(fs_dc_data_bank1_ecc_sb_error_r),
  .fs_dc_data_bank2_ecc_sb_error_r(fs_dc_data_bank2_ecc_sb_error_r),
  .fs_dc_data_bank3_ecc_sb_error_r(fs_dc_data_bank3_ecc_sb_error_r),

  .fs_dc_data_bank0_ecc_db_error_r(fs_dc_data_bank0_ecc_db_error_r),
  .fs_dc_data_bank1_ecc_db_error_r(fs_dc_data_bank1_ecc_db_error_r),
  .fs_dc_data_bank2_ecc_db_error_r(fs_dc_data_bank2_ecc_db_error_r),
  .fs_dc_data_bank3_ecc_db_error_r(fs_dc_data_bank3_ecc_db_error_r),

//   `endif
  .dc4_hit_even_way_hot_r (dc4_hit_even_way_hot_r),
  .dc4_hit_odd_way_hot_r  (dc4_hit_odd_way_hot_r ),
  .dc4_waw_replay_r       (dc4_waw_replay_r      ),
  
  .lq_empty_r             (lq_empty_r          ),     
  .wa_restart_r           (wa_restart_kill_r   ), 
  .wa_replay_r            (wa_replay_r         ),  
  .wq_req_dd_even_lo      (wq_req_dd_even_lo   ),  
  .wq_dd_addr_even_lo     (wq_dd_addr_even_lo  ),  
  .wq_dd_din_even_lo      (wq_dd_din_even_lo   ),  
  .wq_dd_wem_even_lo      (wq_dd_wem_even_lo   ),  
  
  .wq_req_dd_even_hi      (wq_req_dd_even_hi   ),  
  .wq_dd_addr_even_hi     (wq_dd_addr_even_hi  ),  
  .wq_dd_din_even_hi      (wq_dd_din_even_hi   ),  
  .wq_dd_wem_even_hi      (wq_dd_wem_even_hi   ),  
  
  .wq_req_dd_odd_lo       (wq_req_dd_odd_lo    ),  
  .wq_dd_addr_odd_lo      (wq_dd_addr_odd_lo   ),  
  .wq_dd_din_odd_lo       (wq_dd_din_odd_lo    ),  
  .wq_dd_wem_odd_lo       (wq_dd_wem_odd_lo    ),  
  
  .wq_req_dd_odd_hi       (wq_req_dd_odd_hi    ),  
  .wq_dd_addr_odd_hi      (wq_dd_addr_odd_hi   ),  
  .wq_dd_din_odd_hi       (wq_dd_din_odd_hi    ),  
  .wq_dd_wem_odd_hi       (wq_dd_wem_odd_hi    ),  
  
  .wq_dd_way_hot          (wq_dd_way_hot       ),  
    
  .wq_empty               (wq_empty            ),

  .wq_dc_entry            (wq_target_dc        ),
  .wq_dmu_set_conflict    (wq_dmu_set_conflict ),
  .wq_scond_entry         (wq_scond_entry      ),
  
  .wq_read_one            (wq_dc_read          ),  
  .dmu_evict_rd           (dmu_evict_rd        ),
  .dc3_even_way0_hit      (dc3_even_way0_hit   ),
  .dc3_odd_way0_hit       (dc3_odd_way0_hit    ),
  .dc3_dt_even_hit_way_hot_prel   (dc3_dt_even_hit_way_hot_prel  ),
  .dc3_dt_odd_hit_way_hot_prel    (dc3_dt_odd_hit_way_hot_prel   ),
  .dc3_dt_even_hit_way_hot        (dc3_dt_even_hit_way_hot       ),
  .dc3_dt_odd_hit_way_hot         (dc3_dt_odd_hit_way_hot        ),
  .dc4_wq_skid_replay_r   (dc4_wq_skid_replay_r),
  .dc3_dd_data_even_lo    (dc3_dd_data_even_lo ),
  .dc3_dd_data_even_hi    (dc3_dd_data_even_hi ),
  .dc3_dd_data_odd_lo     (dc3_dd_data_odd_lo  ),
  .dc3_dd_data_odd_hi     (dc3_dd_data_odd_hi  ),

  .dc3_dt_even_w0         (dc3_dt_even_w0      ),
  .dc3_dt_even_w1         (dc3_dt_even_w1      ),
  .dc3_dt_odd_w0          (dc3_dt_odd_w0       ),
  .dc3_dt_odd_w1          (dc3_dt_odd_w1       ),
  
  .clk_tag_even_w0       (clk_tag_even_w0          ),
  .dc_tag_even_cs_w0     (dc_tag_even_cs_w0        ), 
  .dc_tag_even_we_w0     (dc_tag_even_we_w0        ), 
  .dc_tag_even_wem_w0    (dc_tag_even_wem_w0       ), 
  .dc_tag_even_addr_w0   (dc_tag_even_addr_w0      ),
  .dc_tag_even_din_w0    (dc_tag_even_din_w0       ), 
  .dc_tag_even_dout_w0   (dc_tag_even_dout_w0      ),

  .clk_tag_odd_w0        (clk_tag_odd_w0           ),
  .dc_tag_odd_cs_w0      (dc_tag_odd_cs_w0         ), 
  .dc_tag_odd_we_w0      (dc_tag_odd_we_w0         ), 
  .dc_tag_odd_wem_w0     (dc_tag_odd_wem_w0        ), 
  .dc_tag_odd_addr_w0    (dc_tag_odd_addr_w0       ),
  .dc_tag_odd_din_w0     (dc_tag_odd_din_w0        ), 
  .dc_tag_odd_dout_w0    (dc_tag_odd_dout_w0      ),

  .clk_tag_even_w1       (clk_tag_even_w1          ),
  .dc_tag_even_cs_w1     (dc_tag_even_cs_w1        ), 
  .dc_tag_even_we_w1     (dc_tag_even_we_w1        ), 
  .dc_tag_even_wem_w1    (dc_tag_even_wem_w1       ), 
  .dc_tag_even_addr_w1   (dc_tag_even_addr_w1      ),
  .dc_tag_even_din_w1    (dc_tag_even_din_w1       ), 
  .dc_tag_even_dout_w1   (dc_tag_even_dout_w1      ),

  .clk_tag_odd_w1        (clk_tag_odd_w1           ),
  .dc_tag_odd_cs_w1      (dc_tag_odd_cs_w1         ), 
  .dc_tag_odd_we_w1      (dc_tag_odd_we_w1         ), 
  .dc_tag_odd_wem_w1     (dc_tag_odd_wem_w1        ), 
  .dc_tag_odd_addr_w1    (dc_tag_odd_addr_w1       ),
  .dc_tag_odd_din_w1     (dc_tag_odd_din_w1        ), 
  .dc_tag_odd_dout_w1    (dc_tag_odd_dout_w1      ),

  .clk_data_even_lo       (clk_data_even_lo    ),
  .dc_data_even_cs_lo     (dc_data_even_cs_lo  ),  
  .dc_data_even_we_lo     (dc_data_even_we_lo  ),  
  .dc_data_even_wem_lo    (dc_data_even_wem_lo ),  
  .dc_data_even_addr_lo   (dc_data_even_addr_lo),  
  .dc_data_even_din_lo    (dc_data_even_din_lo ),

  .clk_data_even_hi       (clk_data_even_hi    ),
  .dc_data_even_cs_hi     (dc_data_even_cs_hi  ),  
  .dc_data_even_we_hi     (dc_data_even_we_hi  ),  
  .dc_data_even_wem_hi    (dc_data_even_wem_hi ),  
  .dc_data_even_addr_hi   (dc_data_even_addr_hi),  
  .dc_data_even_din_hi    (dc_data_even_din_hi ),

  .clk_data_odd_lo        (clk_data_odd_lo     ),
  .dc_data_odd_cs_lo      (dc_data_odd_cs_lo   ),  
  .dc_data_odd_we_lo      (dc_data_odd_we_lo   ),  
  .dc_data_odd_wem_lo     (dc_data_odd_wem_lo  ),  
  .dc_data_odd_addr_lo    (dc_data_odd_addr_lo ),  
  .dc_data_odd_din_lo     (dc_data_odd_din_lo  ),

  .clk_data_odd_hi        (clk_data_odd_hi     ),
  .dc_data_odd_cs_hi      (dc_data_odd_cs_hi   ),  
  .dc_data_odd_we_hi      (dc_data_odd_we_hi   ),  
  .dc_data_odd_wem_hi     (dc_data_odd_wem_hi  ),  
  .dc_data_odd_addr_hi    (dc_data_odd_addr_hi ),  
  .dc_data_odd_din_hi     (dc_data_odd_din_hi  ),

  .dc_rb_req              (dc_rb_req           ),
  .dc_dt_hit              (dc_dt_hit           ),

  .dc_rb_bank0_lo_r       (dc_rb_bank0_lo_r    ),
  .dc_rb_bank0_hi_r       (dc_rb_bank0_hi_r    ),
  .dc_rb_bank1_lo_r       (dc_rb_bank1_lo_r    ),
  .dc_rb_bank1_hi_r       (dc_rb_bank1_hi_r    ),
  .dc4_dc_ecc_replay_r   (dc4_dc_ecc_replay_r  ),
  .mq_rb_ack              (mq_rb_ack           ),
  .mq_rb_tag              (mq_rb_tag           ),
  .mq_rb_req              (mq_rb_req           ),
  .mq_rb_err              (mq_rb_err           ),
  .mq_userm               (mq_rb_user_mode     ),  

  .mq_sex                 (mq_sex              ),
  .mq_size                (mq_size             ),
  .mq_bank_sel            (mq_bank_sel         ),
  .mq_rb_data             (mq_rb_data          ),
  .mq_rb_addr             (mq_rb_addr          ),
  .mq_wr_err              (mq_wr_err           ),
  .rb_aln_data            (rb_aln_data         ),  

  .mq_flush_err_req       (mq_flush_err_req    ),
  .mq_flush_err_addr      (mq_flush_err_addr   ),
  .mq_flush_err_ack       (mq_flush_err_ack    ),
  
  .rf_err_req             (rf_err_req          ),
  .rf_err_addr            (rf_err_addr         ),

  
  .rf_cmd_valid           (rf_cmd_valid        ), 
  .rf_cmd_excl            (rf_cmd_excl         ),
  .rf_cmd_accept          (rf_cmd_accept       ),
  .rf_cmd_read            (rf_cmd_read         ), 
  .rf_cmd_addr            (rf_cmd_addr         ), 
  .rf_cmd_prot            (rf_cmd_prot         ), 
  .rf_cmd_wrap            (rf_cmd_wrap         ), 
  .rf_cmd_burst_size      (rf_cmd_burst_size   ),
  
  .rf_rd_valid            (rf_rd_valid         ),   
  .rf_rd_last             (rf_rd_last          ), 
  .rf_err_rd              (rf_err_rd           ),   
  .rf_rd_accept           (rf_rd_accept        ),   
  .rf_rd_data             (rf_rd_data          ),  

  .cb_cmd_valid           (cb_cmd_valid        ), 
  .cb_cmd_accept          (cb_cmd_accept       ),
  .cb_cmd_read            (cb_cmd_read         ), 
  .cb_cmd_addr            (cb_cmd_addr         ), 
  .cb_cmd_prot            (cb_cmd_prot         ), 
  .cb_cmd_wrap            (cb_cmd_wrap         ), 
  .cb_cmd_burst_size      (cb_cmd_burst_size   ),
  
  .cb_wr_valid            (cb_wr_valid         ),   
  .cb_wr_last             (cb_wr_last          ),   
  .cb_wr_accept           (cb_wr_accept        ),  
  .cb_wr_mask             (cb_wr_mask          ),   
  .cb_wr_data             (cb_wr_data          ), 
  .cb_wr_done             (cb_wr_done          ), 
  .cb_err_wr              (cb_err_wr           ), 


  .aux_read               (aux_read            ),  
  .aux_write              (aux_write           ),  
  .aux_ren_r              (aux_dc_ren_r        ),  
  .aux_raddr_r            (aux_dc_raddr_r      ),  
  .aux_wen_r              (aux_dc_wen_r        ),  
  .aux_waddr_r            (aux_dc_waddr_r      ),  
  .aux_wdata_r            (aux_wdata_r         ),  
  
  .aux_rdata              (aux_dc_aux_rdata    ),  
  .aux_illegal            (aux_dc_aux_illegal  ),  
  .aux_k_rd               (aux_dc_aux_k_rd     ),  
  .aux_k_wr               (aux_dc_aux_k_wr     ),  
  .aux_unimpl             (aux_dc_aux_unimpl   ),  
  .aux_serial_sr          (aux_dc_aux_serial_sr), 
  .aux_strict_sr          (aux_dc_aux_strict_sr), 
  .aux_busy               (aux_dc_aux_busy     ),
  
  .aux_x2_addr_pass       (aux_dc_x2_addr_pass ),
  .aux_x2_addr            (aux_dc_x2_addr      ),
  .aux_x2_addr_hi         (aux_dc_x2_addr_hi   ),
  
  .dc_pct_dcm             (dc_pct_dcm          ), 
  .dc_pct_dclm            (dc_pct_dclm         ), 
  .dc_pct_dcsm            (dc_pct_dcsm         ), 
  .dc_pct_dcbc            (dc_pct_dcbc         ), 
  .dc_pct_ivdc            (dc_pct_ivdc         ),
  .dc_pct_ivdl            (dc_pct_ivdl         ),
  .dc_pct_flsh            (dc_pct_flsh         ),
  .dc_pct_fldl            (dc_pct_fldl         ),
  .dc_pct_bdcmstall       (dc_pct_bdcmstall    ),


  .dmu_empty              (dmu_empty           ),
  .mq_one_or_less_entry   (mq_one_or_less_entry),
  .dmu_set_addr           (dmu_set_addr        ),
  .aux_cache_off          (aux_cache_off       ),
  

  .clk                    (clk                 ), 
  .clk_dmu                (clk_dmu             ), 
  .dbg_cache_rst_disable_r (dbg_cache_rst_disable_r),

  .rst_cache_a            (rst_a               ),
  .rst_a                  (rst_a               )
);



///////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: Write  Queue                               
//                                                                         
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_wq u_alb_dmp_wq (
  .clk                       (clk                   ),        
  .rst_a                     (rst_a                 ),

  .holdup_excpn_r            (holdup_excpn_r        ),
  .st_instrs_discarded       (st_instrs_discarded   ),
  .st_instrs_discarded_r     (st_instrs_discarded_r ),

  .ecc_dmp_disable           (ecc_dmp_disable       ),

  .sa_dsync_op_r             (sa_dsync_op_r         ), 
  .sa_dmb_op_r               (sa_dmb_op_r           ),   
  .sa_dmb_stall              (sa_dmb_stall          ),   
  .x2_mem_addr0_r            (x2_mem_addr0_r        ),
  .x2_load_r                 (x2_load_r             ),
  .x2_size_r                 (x2_size_r             ),
  .x2_pass                   (x2_pass               ),
  .dc2_rmw_r                 (dc2_rmw               ),
  .dc2_data_bank_sel_r       (dc2_data_bank_sel_r   ),
  .dc2_mem_addr1_r           (dc2_mem_addr1_r       ),
  .dc2_dc_uop_stall          (dc2_dc_uop_stall      ),   
  .x3_pass                   (x3_pass               ), 
  .x3_load_r                 (x3_load_r             ),
  .x3_store_r                (x3_store_r            ),
  .x3_store_may_grad         (x3_store_may_grad     ),
  .x3_mem_addr0_r            (dc3_mem_addr0_r       ),
  .x3_mem_addr1_r            (dc3_mem_addr1_r       ),  
  .x3_uop_inst_r             (x3_uop_inst_r         ),
  .dmp_dc3_stall_r           (dmp_dc3_stall_r       ),
  .dc3_partial_or_multi_conflict (dc3_partial_or_multi_conflict), 
  .x3_sync_op_r              (x3_sync_op_r          ),
  .x3_brk_op_r               (x3_brk_op_r           ),
  .dc3_size0_r               (dc3_size0_r           ),   
  .dc3_size1_r               (dc3_size1_r           ),   
  .dc3_bank_sel_r            ({dc3_data_bank_sel_hi_r[1], 
                               dc3_data_bank_sel_lo_r[1],
                               dc3_data_bank_sel_hi_r[0],
                               dc3_data_bank_sel_lo_r[0]}),
  .dc3_target_r              (dc3_target_r          ),
  .dc3_dt_any_hit            (dc3_dt_any_hit        ),
  .dc3_rmw_r                 (dc3_rmw_r             ),
  .dc3_fwd_allowed_r         (dc3_fwd_allowed_r     ),

  .wq_fwd_replay             (wq_fwd_replay         ),
  .wq_fwd_bank               (wq_fwd_bank           ),
  .wq_fwd_data_bank0_lo      (wq_fwd_data_bank0_lo  ),
  .wq_fwd_data_bank0_hi      (wq_fwd_data_bank0_hi  ),
  .wq_fwd_data_bank1_lo      (wq_fwd_data_bank1_lo  ),
  .wq_fwd_data_bank1_hi      (wq_fwd_data_bank1_hi  ),
  
  .wq_skid_ctrl_mask         (wq_skid_ctrl_mask     ),
  
  .db_active_r               (db_active_r           ),
  .db_exception_r            (db_exception_r        ),
  
  .ca_enable                 (ca_enable             ),       
  .ca_pass_prel              (ca_pass               ),        
  .ca_store_r                (ca_store_r            ),        
  .ca_load_r                 (ca_load_r             ),   
  .ca_locked_r               (ca_locked_r           ),
  .ca_scond_go               (dc4_scond_go          ),
  .ca_grad_tag               (ca_grad_tag           ),
  .ca_size_r                 (ca_size_r             ),        
  .ca_user_mode_r            (ar_user_mode_r        ),    
  .ca_cache_byp_r            (dc4_cache_byp_r       ),       
  .ca_mem_addr0_r            (ca_phys_addr_r        ),
  .ca_wr_data_r              (dc4_wr_data           ),        
  .ca_store_grad_r           (ca_store_grad_r       ),
  .ca_store_grad_swap_r      (ca_store_grad_swap_r  ),
  .ca_store_grad_tag_lo_r    (ca_store_grad_tag_lo_r),
  .ca_store_grad_tag_hi_r    (ca_store_grad_tag_hi_r),
  .dc4_grad_req              (dc4_grad_req          ),
  .dc4_size0_r               (dc4_size0_r           ),
  .dc4_size1_r               (dc4_size1_r           ),
  .dc4_mem_addr1_r           (dc4_mem_addr1_r       ),
  .dc4_target_r              (dc4_target_r          ), 
  .dc4_volatile_r            (dc4_volatile_r        ),
  .dc4_strict_order_r        (dc4_strict_order_r    ), 
  .dc4_data_mem_attr_r       (dc4_data_mem_attr_r[0]), 
  .dc4_data_bank_sel_lo_r    (dc4_data_bank_sel_lo_r),
  .dc4_data_bank_sel_hi_r    (dc4_data_bank_sel_hi_r),
  .dc4_rmw_r                 (dc4_rmw_r             ),    
  .dc4_data_even_lo_r        (dccm_rb_data0_lo_r    ),
  .dc4_data_even_hi_r        (dccm_rb_data0_hi_r    ),
  .dc4_data_odd_lo_r         (dccm_rb_data1_lo_r    ),
  .dc4_data_odd_hi_r         (dccm_rb_data1_hi_r    ),
  .dc4_dccm_ecc_sb_error_r   (dc4_dccm_ecc_sb_error_r), 
  .dc4_ecc_skid_sb_error_r   (dc4_dccm_ecc_skid_sb_error_r),
  .dc4_dccm_ecc_db_error_r   (dc4_dccm_ecc_excpn_r   ),
  .dc4_dmi_scrubbing_conflict(dc4_dmi_scrubbing_conflict),
  .dc4_ecc_data_even_lo      (dc4_ecc_data_even_lo   ),
  .dc4_ecc_data_even_hi      (dc4_ecc_data_even_hi   ),
  .dc4_ecc_data_odd_lo       (dc4_ecc_data_odd_lo    ),
  .dc4_ecc_data_odd_hi       (dc4_ecc_data_odd_hi    ),

  .dc4_dd_data_even_lo_r     (dc_rb_bank0_lo_r      ),
  .dc4_dd_data_even_hi_r     (dc_rb_bank0_hi_r      ),
  .dc4_dd_data_odd_lo_r      (dc_rb_bank1_lo_r      ),
  .dc4_dd_data_odd_hi_r      (dc_rb_bank1_hi_r      ), 
  .wq_fwd_bank_r             (wq_fwd_bank_r         ),
  .wq_fwd_data_bank0_lo_r    (wq_fwd_data_bank0_lo_r),
  .wq_fwd_data_bank0_hi_r    (wq_fwd_data_bank0_hi_r),
  .wq_fwd_data_bank1_lo_r    (wq_fwd_data_bank1_lo_r),
  .wq_fwd_data_bank1_hi_r    (wq_fwd_data_bank1_hi_r),
  .dc4_dt_line_cross_r       (dc4_dt_line_cross_r   ),
  .dc4_dt_bank_sel_r         (dc4_dt_bank_sel_r     ),
  .dc4_hit_even_way_hot_r    (dc4_hit_even_way_hot_r),
  .dc4_hit_odd_way_hot_r     (dc4_hit_odd_way_hot_r ),
  .dc4_stall_r               (dc4_stall_r            ),

  .ecc_dccm_sbe_count_r      (ecc_dccm_sbe_count_r  ), 
  .dccm_ecc_sbe_clr          (dccm_ecc_sbe_clr      ),

  .wq_scond_rb_req           (wq_scond_rb_req       ), 
  .wq_scond_rb_tag           (wq_scond_rb_tag       ), 
  .wq_scond_rb_flag          (wq_scond_rb_flag      ), 
  
  .wq_scond_rb_ack           (wq_scond_rb_ack       ), 

  .dc4_wq_ovf_replay_r       (dc4_wq_ovf_replay_r    ),
  .dc4_wq_order_replay_r     (dc4_wq_order_replay_r  ),
  .wq_dc4_fwd_replay_r       (wq_dc4_fwd_replay_r   ),
 

  .wa_retire1_valid          (wa_retire1_valid      ),
  .wa_retire1_garbage        (1'b0                  ),
  .wa_retire1_tag            (wa_retire1_tag        ),
  .wa_retire1_data           (wa_retire1_data       ),

  .ca_store_grad_tag         (ca_store_grad_tag     ),
  .dmp_st_retire0            (dmp_st_retire0        ),
  .dmp_st_retire0_tag        (dmp_st_retire0_tag    ),
  .dmp_st_retire0_data       (dmp_st_retire0_data   ),


  .dmp_st_retire1            (dmp_st_retire1        ),
  .dmp_st_retire1_tag        (dmp_st_retire1_tag    ),
  .dmp_st_retire1_data       (dmp_st_retire1_data   ),



  .wa_restart_r              (wa_restart_kill_r     ),
  .wa_hlt_restart_r          (wa_hlt_restart_r      ),
        

  .wq_req_even_lo            (wq_req_even_lo        ),  
  .wq_addr_even_lo           (wq_addr_even_lo       ), 
  .wq_din_even_lo            (wq_din_even_lo        ),  
  .wq_wem_even_lo            (wq_wem_even_lo        ),  
  
  .wq_req_even_hi            (wq_req_even_hi        ),  
  .wq_addr_even_hi           (wq_addr_even_hi       ), 
  .wq_din_even_hi            (wq_din_even_hi        ),  
  .wq_wem_even_hi            (wq_wem_even_hi        ),  
  
  .wq_req_odd_lo             (wq_req_odd_lo         ),  
  .wq_addr_odd_lo            (wq_addr_odd_lo        ), 
  .wq_din_odd_lo             (wq_din_odd_lo         ),  
  .wq_wem_odd_lo             (wq_wem_odd_lo         ),  
  
  .wq_req_odd_hi             (wq_req_odd_hi         ),  
  .wq_addr_odd_hi            (wq_addr_odd_hi        ), 
  .wq_din_odd_hi             (wq_din_odd_hi         ),  
  .wq_wem_odd_hi             (wq_wem_odd_hi         ),  
  
  .wq_dccm_read_one          (wq_dccm_read_one      ),
  .wq_dccm_read_two          (wq_dccm_read_two      ),
 
  .wq_dccm_top_bank_req_mask (wq_dccm_top_bank_req_mask),
  .wq_dccm_sec_bank_req_mask (wq_dccm_sec_bank_req_mask),

  .wq_mem_cmd_valid          (wq_mem_cmd_valid      ),        
  .wq_mem_cmd_cache          (wq_mem_cmd_cache      ),  
  .wq_mem_cmd_burst_size     (wq_mem_cmd_burst_size ),        
  .wq_mem_cmd_accept         (wq_mem_cmd_accept     ),        
  .wq_mem_cmd_addr           (wq_mem_cmd_addr       ),        
  .wq_mem_cmd_data_size      (wq_mem_cmd_data_size  ), 
  .wq_mem_cmd_lock           (wq_mem_cmd_lock       ),        
  .wq_mem_cmd_excl           (wq_mem_cmd_excl       ),
  .wq_mem_cmd_prot           (wq_mem_cmd_prot       ),        
  
  .wq_mem_wr_valid           (wq_mem_wr_valid       ),        
  .wq_mem_wr_last            (wq_mem_wr_last        ),        
  .wq_mem_wr_accept          (wq_mem_wr_accept      ),        
  .wq_mem_wr_mask            (wq_mem_wr_mask        ),        
  .wq_mem_wr_data            (wq_mem_wr_data        ),  
  
  .wq_mem_wr_done            (wq_mem_wr_done        ),
  .wq_mem_wr_excl_done       (wq_mem_wr_excl_done   ),
  .wq_mem_err_wr             (wq_mem_err_wr         ),
  .wq_mem_wr_resp_accept     (wq_mem_wr_resp_accept ),



 
  .wq_req_dd_even_lo         (wq_req_dd_even_lo     ),  
  .wq_dd_addr_even_lo        (wq_dd_addr_even_lo    ),  
  .wq_dd_din_even_lo         (wq_dd_din_even_lo     ),  
  .wq_dd_wem_even_lo         (wq_dd_wem_even_lo     ),  
  
  .wq_req_dd_even_hi         (wq_req_dd_even_hi     ),  
  .wq_dd_addr_even_hi        (wq_dd_addr_even_hi    ),  
  .wq_dd_din_even_hi         (wq_dd_din_even_hi     ),  
  .wq_dd_wem_even_hi         (wq_dd_wem_even_hi     ),  
  
  .wq_req_dd_odd_lo          (wq_req_dd_odd_lo      ),  
  .wq_dd_addr_odd_lo         (wq_dd_addr_odd_lo     ),  
  .wq_dd_din_odd_lo          (wq_dd_din_odd_lo      ),  
  .wq_dd_wem_odd_lo          (wq_dd_wem_odd_lo      ),  
  
  .wq_req_dd_odd_hi          (wq_req_dd_odd_hi      ),  
  .wq_dd_addr_odd_hi         (wq_dd_addr_odd_hi     ),  
  .wq_dd_din_odd_hi          (wq_dd_din_odd_hi      ),  
  .wq_dd_wem_odd_hi          (wq_dd_wem_odd_hi      ),  
  
  .wq_dd_way_hot             (wq_dd_way_hot         ),    
  
  .wq_dc_read                (wq_dc_read            ),  
  .dc3_fwd_req               (dc3_fwd_req           ),
  
  .dmu_empty                 (dmu_empty             ),
  .dmu_set_addr              (dmu_set_addr          ),
  .wq_err_r                  (wq_err_r              ),
  .wq_err_user_mode_r        (wq_err_user_mode_r    ), 
  .wq_err_addr_r             (wq_err_addr_r         ), 
  .wq_err_ack                (wq_err_ack            ), 
  
  .wq_order_ptr_1h           (wq_order_ptr_1h       ), 
  .dc4_raw_hazard            (dc4_raw_hazard        ),
  .wq_mem_per_iccm_read      (wq_mem_per_iccm_read  ), 
  .wq_rdentry0               (wq_rdentry0           ),    
  .wq_mem_retire             (wq_mem_retire         ),  
  .wq_mem_entry_id           (wq_mem_entry_id       ), 
  
  .lq_order_ptr_1h           (lq_order_ptr_1h       ), 
  .dc4_war_hazard            (dc4_war_hazard        ),
  .lq_cmd_read               (lq_cmd_read           ),     
  .lq_cmd_rd_ptr             (lq_cmd_rd_ptr         ),    
  .lq_data_retire            (lq_data_retire        ),     
  .lq_data_err               (lq_rb_err             ),
  .lq_data_rd_ptr            (lq_data_rd_ptr        ),    

  .wq_dc_entry               (wq_dc_entry           ),
  .wq_scond_entry            (wq_scond_entry        ),
  .wq_target_dc              (wq_target_dc          ),
  .wq_dmu_set_conflict       (wq_dmu_set_conflict   ),
  .dc4_wq_full               (dc4_wq_full           ),
  .dc4_wq_one_empty          (dc4_wq_one_empty      ),
  .wq_non_dc_entry           (wq_non_dc_entry       ),
  .wq_retire                 (wq_retire             ),
  .wq_empty                  (wq_empty              ),        
  .wq_more_than_one_empty    (wq_more_than_one_empty)        
);                      

//////////////////////////////////////////////////////////////////////////////
// 
// Module instantiation: Load Queue 
//
///////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_lq u_alb_dmp_lq (
  .clk                            (clk_lq                ),
  .rst_a                          (rst_a                 ),


  .x3_store_r                     (x3_store_r            ),
  .x3_pass                        (x3_pass               ),
  .x3_mem_addr0_r                 (dc3_mem_addr0_r       ),
  .x3_mem_addr1_r                 (dc3_mem_addr1_r       ),
  .dc3_target_r                   (dc3_target_r          ),
  .dc3_bank_sel_r                 ({dc3_data_bank_sel_hi_r[1],
                                    dc3_data_bank_sel_lo_r[1],     
                                    dc3_data_bank_sel_hi_r[0],     
                                    dc3_data_bank_sel_lo_r[0]}),     

  .ca_valid_r                     (ca_valid_r            ), 
  .ca_pass                        (ca_pass               ),
  .ca_load_r                      (ca_load_r             ),
  .ca_store_r                     (ca_store_r            ),
  .ca_locked_r                    (ca_locked_r           ),
  .ca_volatile_r                  (dc4_volatile_r        ), 
  .ca_strict_order_r              (dc4_strict_order_r    ), 
  .ca_size_r                      (ca_size_r             ),
  .ca_sex_r                       (ca_sex_r              ),    
  .ca_user_mode_r                 (ar_user_mode_r        ),  
  .ca_mem_addr0_r                 (ca_phys_addr_r        ),
  .ca_mem_addr1_r                 (dc4_mem_addr1_r       ),
  .ca_grad_tag                    (ca_grad_tag           ),


  .dc4_grad_req                   (dc4_grad_req          ),
  .dc4_target_r                   (dc4_target_r          ),
  .dc4_data_bank_sel_lo_r         (dc4_data_bank_sel_lo_r),
  .dc4_data_bank_sel_hi_r         (dc4_data_bank_sel_hi_r),
                                    
  .lq_rb_req                      (lq_rb_req             ),
  .lq_rb_err                      (lq_rb_err             ),
  .lq_rb_user_mode                (lq_rb_user_mode       ),
  .lq_rb_tag                      (lq_rb_tag             ),
  .lq_rb_sex                      (lq_rb_sex             ), 
  .lq_rb_size                     (lq_rb_size            ), 
  .lq_rb_addr                     (lq_rb_addr            ), 
 
  .lq_rb_ack                      (lq_rb_ack             ),  
  
  .lq_rb_data_even_r              (lq_rb_data_even_r     ),
  .lq_rb_data_odd_r               (lq_rb_data_odd_r      ),
                                       
  .lq_mem_cmd_valid               (lq_mem_cmd_valid      ), 
  .lq_mem_cmd_burst_size          (lq_mem_cmd_burst_size ), 
  .lq_mem_cmd_read                (lq_mem_cmd_read       ),
  .lq_mem_cmd_accept              (lq_mem_cmd_accept     ), 
  .lq_mem_cmd_addr                (lq_mem_cmd_addr       ),
  .lq_mem_cmd_lock                (lq_mem_cmd_lock       ),
  .lq_mem_cmd_excl                (lq_mem_cmd_excl       ),
  .lq_mem_cmd_data_size           (lq_mem_cmd_data_size  ), 
  .lq_mem_cmd_prot                (lq_mem_cmd_prot       ), 
  
  .lq_mem_rd_valid                (lq_mem_rd_valid       ), 
  .lq_mem_err_rd                  (lq_mem_err_rd         ), 
  .lq_mem_rd_excl_ok              (lq_mem_rd_excl_ok     ),
  .lq_mem_rd_accept               (lq_mem_rd_accept      ), 
  .lq_mem_rd_data                 (lq_mem_rd_data        ),

  .lq_order_ptr_1h                (lq_order_ptr_1h       ),
  .dc4_war_hazard                 (dc4_war_hazard        ), 
  
  .lq_cmd_read                    (lq_cmd_read           ),    
  .lq_cmd_rd_ptr                  (lq_cmd_rd_ptr         ),  
  .lq_data_retire                 (lq_data_retire        ),
  .lq_data_rd_ptr                 (lq_data_rd_ptr        ),
  
  .wq_order_ptr_1h                (wq_order_ptr_1h       ), 
  .dc4_raw_hazard                 (dc4_raw_hazard        ), 
  .wq_mem_per_iccm_read           (wq_mem_per_iccm_read  ), 
  .wq_rdentry0                    (wq_rdentry0           ), 
  .wq_mem_retire                  (wq_mem_retire         ), 
  .wq_mem_entry_id                (wq_mem_entry_id       ), 
  
  .lq_empty_r                     (lq_empty_r            ),
  .lq_full_nxt                    (lq_full_nxt           )
);                                
    
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Unified LQ/WQ interface                         
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_lqwq_if u0_alb_dmp_lqwq_if (
  .i0_cmd_valid      (lq_mem_cmd_valid       ), 
  .i0_cmd_burst_size (lq_mem_cmd_burst_size  ),                 
  .i0_cmd_read       (lq_mem_cmd_read        ),                
  .i0_cmd_accept     (lq_mem_cmd_accept      ),              
  .i0_cmd_addr       (lq_mem_cmd_addr        ),              
  .i0_cmd_lock       (lq_mem_cmd_lock        ),              
  .i0_cmd_excl       (lq_mem_cmd_excl        ),
  .i0_cmd_data_size  ({1'b0, lq_mem_cmd_data_size}),                
  .i0_cmd_prot       ({1'b0, lq_mem_cmd_prot}),                

  .i0_rd_valid       (lq_mem_rd_valid        ),                
  .i0_err_rd         (lq_mem_err_rd          ),                
  .i0_rd_excl_ok     (lq_mem_rd_excl_ok      ),
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Output connected to floating net
// SJ: Output  unused in this design
  .i0_rd_last        (lq_mem_rd_last         ),   
// spyglass enable_block UnloadedOutTerm-ML
  .i0_rd_accept      (lq_mem_rd_accept       ),               
  .i0_rd_data        (lq_mem_rd_data         ),   
  
  .i1_cmd_valid      (wq_mem_cmd_valid       ),   
  .i1_cmd_cache      (wq_mem_cmd_cache       ),   
  .i1_cmd_burst_size (wq_mem_cmd_burst_size  ),   
  .i1_cmd_accept     (wq_mem_cmd_accept      ),  
  .i1_cmd_addr       (wq_mem_cmd_addr        ),   
  .i1_cmd_data_size  ({1'b0, wq_mem_cmd_data_size}),   
  .i1_cmd_lock       (wq_mem_cmd_lock        ),              
  .i1_cmd_excl       (wq_mem_cmd_excl        ),
  .i1_cmd_prot       ({1'b0, wq_mem_cmd_prot}),              
  
  .i1_wr_valid       (wq_mem_wr_valid        ),   
  .i1_wr_last        (wq_mem_wr_last         ),   
  .i1_wr_accept      (wq_mem_wr_accept       ),   
  .i1_wr_mask        (wq_mem_wr_mask         ),       
  .i1_wr_data        (wq_mem_wr_data         ),   
  
  .i1_wr_done        (wq_mem_wr_done         ),
  .i1_wr_excl_done   (wq_mem_wr_excl_done    ),
  .i1_err_wr         (wq_mem_err_wr          ),
  .i1_wr_resp_accept (wq_mem_wr_resp_accept  ),

  .o_cmd_valid       (lqwq_mem_cmd_valid     ), 
  .o_cmd_cache       (lqwq_mem_cmd_cache     ), 
  .o_cmd_burst_size  (lqwq_mem_cmd_burst_size),              
  .o_cmd_read        (lqwq_mem_cmd_read      ),             
  .o_cmd_accept      (lqwq_mem_cmd_accept    ),           
  .o_cmd_addr        (lqwq_mem_cmd_addr      ),         
  .o_cmd_lock        (lqwq_mem_cmd_lock      ),         
  .o_cmd_excl        (lqwq_mem_cmd_excl      ),
  .o_cmd_data_size   (lqwq_mem_cmd_data_size ),             
  .o_cmd_prot        (lqwq_mem_cmd_prot      ),             

  .o_wr_valid        (lqwq_mem_wr_valid      ), 
  .o_wr_last         (lqwq_mem_wr_last       ), 
  .o_wr_accept       (lqwq_mem_wr_accept     ), 
  .o_wr_mask         (lqwq_mem_wr_mask       ),    
  .o_wr_data         (lqwq_mem_wr_data       ), 
  
  .o_rd_valid        (lqwq_mem_rd_valid      ),             
  .o_err_rd          (lqwq_mem_err_rd        ),             
  .o_rd_excl_ok      (lqwq_mem_rd_excl_ok    ),
  .o_rd_last         (lqwq_mem_rd_last       ),              
  .o_rd_accept       (lqwq_mem_rd_accept     ),            
  .o_rd_data         (lqwq_mem_rd_data       ), 
  
  .o_wr_done         (lqwq_mem_wr_done       ),
  .o_wr_excl_done    (lqwq_mem_wr_excl_done  ),
  .o_err_wr          (lqwq_mem_err_wr        ),
  .o_wr_resp_accept  (lqwq_mem_wr_resp_accept),
  
  .clk               (clk                    ),
  .rst_a             (rst_a                  )
);
  

                           
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: Graduation                               
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_grad u_alb_dmp_grad (
  .clk                    (clk                  ),  
  .rst_a                  (rst_a                ),  

  .db_active_r            (db_active_r          ),
  .x3_db_exception        (x3_db_exception      ),
  
  .x3_load_r              (x3_load_r            ),  
  .x3_pref_r              (dc3_pref             ),  
  .x3_store_r             (x3_store_r           ), 
  .x3_locked_r            (x3_locked_r          ), 
  .x3_pass                (x3_pass              ),  
  .dc3_fwd_req            (dc3_fwd_req          ),  
  .dc3_target_r           (dc3_target_r         ),  
  
  .ca_load_r              (ca_load_r            ),
  .ca_pref_r              (dc4_pref_r           ),
  .ca_enable              (ca_enable            ), 
  .dc4_scond_go           (dc4_scond_go         ),
  .dc4_dt_miss_r          (dc4_dt_miss_r        ),  
  .dc4_mq_replay_r        (dc4_mq_replay_r      ),  
  .dc4_lsmq_replay_r      (dc4_lsmq_replay_r    ),  
  .dc4_grad_req           (dc4_grad_req         )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: Result Bus                                
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_result_bus u_alb_dmp_result_bus (
  .clk                         (clk                   ),   
  .rst_a                       (rst_a                 ),
                                   
  .x3_pass                     (x3_pass               ),
  .x3_load_r                   (x3_load_r             ),
  .x3_store_r                  (x3_store_r            ),
  .x3_size_r                   (x3_size_r             ),
  .x3_sex_r                    (x3_sex_r              ),
  .x3_addr_3_to_0_r            (dc3_mem_addr0_r[3:0]   ),
  .dc3_data_bank_sel_lo_r      (dc3_data_bank_sel_lo_r),
  .dc3_data_bank_sel_hi_r      (dc3_data_bank_sel_hi_r),
  .dc3_target_r                (dc3_target_r          ),
  .dc3_dt_miss                 (dc3_dt_miss           ),   
  .dc3_rmw_r                   (dc3_rmw_r             ),
  .dc3_fwd_req                 (dc3_fwd_req           ),
  
  .ca_enable                   (ca_enable             ), 
  .ca_valid_r                  (ca_valid_r            ), 
  .ca_load_r                   (ca_load_r             ),
  .ca_size_r                   (ca_size_r             ),
  .ca_sex_r                    (ca_sex_r              ),    
  .ca_addr_3_to_0_r            (ca_phys_addr_r[3:0]   ),
  .dc4_target_r                (dc4_target_r          ),
  .wq_fwd_bank_r              (wq_fwd_bank_r         ),        
  .rb_fwd_data_bank0_lo_r     (wq_fwd_data_bank0_lo_r),
  .rb_fwd_data_bank0_hi_r     (wq_fwd_data_bank0_hi_r),
  .rb_fwd_data_bank1_lo_r     (wq_fwd_data_bank1_lo_r),
  .rb_fwd_data_bank1_hi_r     (wq_fwd_data_bank1_hi_r),
     
  .wq_fwd_bank                 (wq_fwd_bank           ),
  .wq_fwd_data_bank0_lo        (wq_fwd_data_bank0_lo  ),
  .wq_fwd_data_bank0_hi        (wq_fwd_data_bank0_hi  ),
  .wq_fwd_data_bank1_lo        (wq_fwd_data_bank1_lo  ),
  .wq_fwd_data_bank1_hi        (wq_fwd_data_bank1_hi  ),
                                      
  .dccm_rb_req                 (dccm_rb_req           ),
  .dccm_rb_bank0_lo_r          (dccm_rb_data0_lo_r    ),
  .dccm_rb_bank0_hi_r          (dccm_rb_data0_hi_r    ),
  .dccm_rb_bank1_lo_r          (dccm_rb_data1_lo_r    ),
  .dccm_rb_bank1_hi_r          (dccm_rb_data1_hi_r    ),
  
  .dc_rb_req                   (dc_rb_req             ), 
  .dc_dt_hit                   (dc_dt_hit             ),
  .dc_rb_bank0_lo_r            (dc_rb_bank0_lo_r      ),
  .dc_rb_bank0_hi_r            (dc_rb_bank0_hi_r      ),
  .dc_rb_bank1_lo_r            (dc_rb_bank1_lo_r      ),
  .dc_rb_bank1_hi_r            (dc_rb_bank1_hi_r      ),
    
  .lq_rb_req                   (lq_rb_req             ),
  .lq_rb_err                   (lq_rb_err             ),
  .lq_rb_tag                   (lq_rb_tag             ),  
  .lq_rb_sex                   (lq_rb_sex             ),  
  .lq_rb_size                  (lq_rb_size            ),  
  .lq_rb_addr                  (lq_rb_addr            ),  
  .lq_rb_ack                   (lq_rb_ack             ), 
  .lq_rb_data_even_r           (lq_rb_data_even_r     ),  
  .lq_rb_data_odd_r            (lq_rb_data_odd_r      ),  

  .mq_rb_req                   (mq_rb_req             ), 
  .mq_rb_err                   (mq_rb_err             ), 
  .mq_rb_tag                   (mq_rb_tag             ),
  .mq_rb_addr                  (mq_rb_addr            ),
  .mq_bank_sel                 (mq_bank_sel           ),
  .mq_sex                      (mq_sex                ),
  .mq_size                     (mq_size               ),
  .mq_rb_ack                   (mq_rb_ack             ),
  .mq_rb_data                  (mq_rb_data            ),  
  .rb_aln_data                 (rb_aln_data           ),  
  
  .wq_scond_rb_req             (wq_scond_rb_req       ), 
  .wq_scond_rb_tag             (wq_scond_rb_tag       ), 
  .wq_scond_rb_flag            (wq_scond_rb_flag      ), 
  .wq_scond_rb_ack             (wq_scond_rb_ack       ), 
  
  .dc4_scond_go                (dc4_scond_go          ), 
 
  .rb_retire_req_r             (dmp_retire_req        ),
  .rb_retire_err_r             (dmp_retire_err        ),
  .rb_retire_tag_r             (dmp_retire_tag        ),
  
  .rb_empty                    (rb_empty              ),
  
  .dc3_fast_byp                (dc3_fast_byp          ),
  .dc4_fast_byp_r              (dc4_fast_byp_r        ),
  .dc4_fast_byp_miss_r         (dc4_fast_byp_miss_r   ),
  .rb_fast_data                (dc4_fast_data         ),      
  .rb_scond_zflag              (dmp_scond_zflag       ),      
  .rb_stall_r                  (rb_stall_r            ), 
  .rb_rf_wdata                 (dmp_rf_wdata          )       
);                             
         
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation: DMP auxiliary registers or interface to CCAUX copies
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_aux u_alb_dmp_aux (

  .clk                           (clk                         ),  
  .rst_a                         (rst_a                       ),
  
  .aux_busy                      (aux_dc_busy                 ),
  .aux_dc_aux_busy               (aux_dc_aux_busy             ),

  .aux_wdata_r                   (aux_wdata_r                 ),  

  .aux_ren_r                     (aux_dc_ren_r                ),
  .aux_raddr_r                   (aux_dc_raddr_r              ),                              
  .aux_wen_r                     (aux_dc_wen_r                ), 
  .aux_waddr_r                   (aux_dc_waddr_r              ),

  .aux_rdata                     (aux_dc_rdata                ),   
  .aux_illegal                   (aux_dc_illegal              ),   
  .aux_k_rd                      (aux_dc_k_rd                 ),   
  .aux_k_wr                      (aux_dc_k_wr                 ),   
  .aux_unimpl                    (aux_dc_unimpl               ),   
  .aux_serial_sr                 (aux_dc_serial_sr            ),   
  .aux_strict_sr                 (aux_dc_strict_sr            ), 

  .aux_dper_ren_r                (aux_dper_ren_r              ), 
  .aux_dper_raddr_r              (aux_dper_raddr_r            ),
  .aux_dper_wen_r                (aux_dper_wen_r              ), 
  .aux_dper_waddr_r              (aux_dper_waddr_r            ),
  .aux_dper_rdata                (aux_dper_rdata              ), 
  .aux_dper_illegal              (aux_dper_illegal            ), 
  .aux_dper_k_rd                 (aux_dper_k_rd               ),  
  .aux_dper_k_wr                 (aux_dper_k_wr               ),  
  .aux_dper_unimpl               (aux_dper_unimpl             ), 
  .aux_dper_serial_sr            (aux_dper_serial_sr          ), 
  .aux_dper_strict_sr            (aux_dper_strict_sr          ), 

  .aux_dc_aux_rdata              (aux_dc_aux_rdata            ),  
  .aux_dc_aux_illegal            (aux_dc_aux_illegal          ),  
  .aux_dc_aux_k_rd               (aux_dc_aux_k_rd             ),  
  .aux_dc_aux_k_wr               (aux_dc_aux_k_wr             ),  
  .aux_dc_aux_unimpl             (aux_dc_aux_unimpl           ),  
  .aux_dc_aux_serial_sr          (aux_dc_aux_serial_sr        ),  
  .aux_dc_aux_strict_sr          (aux_dc_aux_strict_sr        ),  
  .aux_dmp_dcache_attr           (aux_dmp_dcache_attr_r       ),
  .aux_dmp_mem_attr              (aux_dmp_mem_attr_r          ),
  .aux_volatile_base_r           (aux_volatile_base_r         ),
  .aux_volatile_limit_r          (aux_volatile_limit_r        ),
  .aux_volatile_strict_r         (aux_volatile_strict_r       ),
  .aux_volatile_dis_r            (aux_volatile_dis_r          ) 
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation:  alb_dmp_idle_mgr                            
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_idle_mgr u_alb_dmp_idle_mgr (
  .clk                         (clk              ), 
  .rst_a                       (rst_a            ), 
 
  .wq_empty                    (wq_empty         ),
  .lq_empty                    (lq_empty_r       ),
  .rb_empty                    (rb_empty         ),
  
  .dmu_empty                   (dmu_empty        ), 
  .dmu_wr_pending              (dmu_wr_pending   ), 
  .aux_dc_busy                 (aux_dc_busy      ),
  .dmp_idle_r                  (dmp_idle_r       ),
  .dmp_idle1_r                 (dmp_idle1_r      ),
  .dmp_queue_empty             (dmp_queue_empty  ),
  .dmp_wr_pending_r            (dmp_wr_pending_r ),
  .dmp_aux_pending_r           (dmp_aux_pending_r)  
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation:  alb_dmp_clock_ctrl                          
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_clock_ctrl u_alb_dmp_clock_ctrl (
  .sa_load_r            (sa_load_r           ),
  .sa_store_r           (sa_store_r          ),
  
  .x1_load_r            (x1_load_r           ),
  .x1_store_r           (x1_store_r          ),
  
  .x2_load_r            (x2_load_r           ),
  .x2_store_r           (x2_store_r          ),
  .dc2_target_r         (dc2_target_r        ),
  .dc2_stall            (dc2_stall           ),

  .x3_load_r            (x3_load_r           ),
  .x3_store_r           (x3_store_r          ),
  .dc3_target_r         (dc3_target_r        ),
  .dc3_dt_miss_fast     (dc3_dt_miss_fast    ),
  
  .ca_load_r            (ca_load_r           ),
  .ca_store_r           (ca_store_r          ),
  .ca_dmp_aux_sr_op     (ca_dmp_aux_sr_op    ),
  .dc4_target_r         (dc4_target_r        ),
  .dc4_dt_miss_r        (dc4_dt_miss_r       ),
   
  .wq_empty             (wq_empty            ),
  .wq_err_r             (wq_err_r            ),
  .lq_empty_r           (lq_empty_r          ),
  .rb_empty             (rb_empty            ),
  .lq_err               (lq_rb_err           ),
  .dmu_empty            (dmu_empty           ),
  .dc_skid_active       (dc_skid_active  ),
  .mq_rd_err            (mq_rb_err           ),
  .mq_wr_err            (mq_wr_err           ),
  .aux_dc_busy          (aux_dc_busy         ),
  .dtlb_active          (dtlb_active         ),

  .ecc_sbe_dmp_clr      (ecc_sbe_dmp_clr     ),
  .dc4_excpn            (dc4_excpn           ),
  
  .dmp_dmu_unit_enable  (dmp_dmu_unit_enable ),
  .dmp_lq_unit_enable   (dmp_lq_unit_enable  ),
  

  .dmp_unit_enable      (dmp_unit_enable     )
);
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Module instantiation:  alb_dmp_excpn                           
//                                                                          
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_excpn u_alb_dmp_excpn (
  .clk                           (clk                        ), 
  .rst_a                         (rst_a                      ), 
  .db_active_r                   (db_active_r                ),
  .idle_req                      (idle_req                   ), 

  .x2_pass                       (x2_pass                    ), 
  .x2_load_r                     (x2_load_r                  ), 
  .x2_store_r                    (x2_store_r                 ), 
  .x2_mem_addr0_r                (x2_mem_addr0_r             ), 
  .x2_mem_addr1_r                (dc2_mem_addr1_r            ), 
  .dc2_bank_sel_r                ({dc2_data_bank_sel_hi_r[1],
                                   dc2_data_bank_sel_lo_r[1],    
                                   dc2_data_bank_sel_hi_r[0],    
                                   dc2_data_bank_sel_lo_r[0]}),  
  .dc2_target0_r                 (dc2_target_r               ), 
  .dc2_volatile_region0          (dc2_volatile_region0       ),
  .dc2_volatile_region1          (dc2_volatile_region1       ),
  .x2_cache_byp_r                (x2_cache_byp_r             ),
  .dtlb_rslt0_cached             (dtlb_rslt0_cached          ),


  .dtlb_rslt1_cached             (dtlb_rslt1_cached          ),
  .dc2_dtlb_miss                 (dc2_dtlb_miss              ),
  .dc2_lkup1_page_cross          (dc2_lkup1_npage_cross_r    ),
  .x3_enable                     (x3_1_enable                ),
  .x3_load_r                     (x3_load_r                  ), 
  .x3_store_r                    (x3_store_r                 ), 
  .dc3_pref                      (dc3_pref                   ),

  .wa_restart_r                  (wa_restart_kill_r          ),
  .mem_excpn_ack_r               (mem_excpn_ack_r            ),


  .aux_dccm_r                    (aux_dccm_r                 ), 
  .aux_memseg_r                  (aux_memseg_r              ),  
  .aux_volatile_dis_r            (aux_volatile_dis_r        ),
  .dc3_excpn                     (dc3_excpn                 ),  
  .dc3_excpn_type                (dc3_excpn_type            ),  
  .dc3_excpn_code                (dc3_excpn_code            ),  

  .lq_err                        (lq_rb_err                 ), 
  .lq_rb_ack                     (lq_rb_ack                 ), 
  .lq_err_user_mode              (lq_rb_user_mode           ), 
  .lq_err_addr                   (lq_rb_addr                ), 
  
  .wq_err_r                      (wq_err_r                  ), 
  .wq_err_user_mode_r            (wq_err_user_mode_r        ), 
  .wq_err_addr_r                 (wq_err_addr_r             ), 
  .wq_err_ack                    (wq_err_ack                ),
  
  .mq_rd_err                     (mq_rb_err                 ),
  .mq_wr_err                     (mq_wr_err                 ),
  .mq_rb_ack                     (mq_rb_ack                 ),
  .mq_err_user_mode              (mq_rb_user_mode           ),
  .mq_err_addr                   (mq_rb_addr                ),
  
  .mq_flush_err                  (mq_flush_err_req          ),
  .mq_flush_err_ack              (mq_flush_err_ack          ),
  .mq_flush_err_addr             (mq_flush_err_addr         ),
  
  .rf_err_req                    (rf_err_req                ),
  .rf_err_addr                   (rf_err_addr               ),
  .dc4_dccm_ecc_db_error_r       (dc4_dccm_ecc_excpn_r      ),   
  .dc4_dc_ecc_db_error_r         (dc4_dc_ecc_db_error_r     ),   


   

  .iexcpn_discarded              (iexcpn_discarded          ),
  .dc4_excpn                     (dc4_excpn                 ),   
  .dc4_excpn_user_mode_r         (dc4_excpn_user_mode_r     ),   
  .dc4_excpn_addr_r              (dc4_excpn_mem_addr        ),   
  .dc4_excpn_type                (dc4_excpn_type            )    
);


//////////////////////////////////////////////////////////////////////////////
//  Output assignments                                                    
//                                                                 
//////////////////////////////////////////////////////////////////////////////
assign rf_cmd_cache      = {aux_dmp_dcache_attr_r[0],
                            aux_dmp_dcache_attr_r[1], 
                            aux_dmp_dcache_attr_r[2],  
                            aux_dmp_dcache_attr_r[3]
                           }; 
assign rf_cmd_lock       = 1'b0;
assign rf_cmd_data_size  = 3'b100;

assign cb_cmd_cache      = {aux_dmp_dcache_attr_r[0],
                            aux_dmp_dcache_attr_r[1], 
                            aux_dmp_dcache_attr_r[2],  
                            aux_dmp_dcache_attr_r[3]
                           }; 
assign cb_cmd_excl       = 1'b0;
assign cb_cmd_lock       = 1'b0;
assign cb_cmd_data_size  = 3'b100;
assign cb_wr_resp_accept = 1'b1;

assign rtt_dc4_scond_go = dc4_scond_go;

endmodule // alb_dmp           
                               
                               
