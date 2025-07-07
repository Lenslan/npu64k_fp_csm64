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
//   ALB_DMP_DCACHE                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Data Memory pipeline.
//  It is a structural module which instantiates the data cache module and
//  connects it with the integer pipeline and higher-levels in the module
//  hierarchy.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_dcache.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


      

//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_dmp_dmu_edc_err" }
//D: error_signal { name: "alb_dmp_status_edc_err" }
//D: error_signal { name: "alb_dmp_dcache_aux_edc_err" }

module npuarc_alb_dmp_dcache (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
 
  
  ////////// Interface to the X1 stage /////////////////////////////////
  //
  input                        x1_valid_r,     // X1 has valid instruction
  input                        x1_pass,        // X1  passing on ints
  input                        x1_load_r,      // X1 load
  input                        x1_store_r,     // X1 store
  input                        x1_pref_r,      // X1 pref ucode bit
  input                        x1_cache_byp_r, // X1 .di instruction
  input                        x1_uop_inst_r,  // X1 uop signal

  input [`npuarc_DC_BANK_RANGE]       dc1_data_bank_sel_lo, // X1 DC bank select 
  input [`npuarc_DC_BANK_RANGE]       dc1_data_bank_sel_hi, // X1 DC bank select 
  input  [`npuarc_DMP_TARGET_RANGE]   dc1_target,           // DC1 target
  
  input [1:0]                  dc1_dt_bank_sel,      // DC1 even/odd tag sel
  input [`npuarc_DC_IDX_RANGE]        dc1_dt_addr0,         // DC1 tag addr0
  input [`npuarc_DC_IDX_RANGE]        dc1_dt_addr1,         // DC1 tag addr1
  
  input [`npuarc_DC_ADR_RANGE]        dc1_dd_addr0,        //
  input [`npuarc_DC_ADR_RANGE]        dc1_dd_addr1,        //
  input [3:0]                  dc1_rmw,             // DC1 RMW
  input                        dc1_dccm_bank_conflict,
  output reg                   dc1_stall,           // DC1 stall
  
  ////////// Interface to the X2 stage /////////////////////////////////
  //
  input                        x2_pass,              // X2 passing on instruction
  input                        x2_enable,            // X2 accepts new instruction
  input                        x2_exu_stall,         // X2 EXU stall
  input                        x2_load_r,            // X2 load  
  input                        x2_store_r,           // X2 store  
  input [`npuarc_ADDR_RANGE]          x2_mem_addr0_r,
  input [`npuarc_DC_PRED_BIT_RANGE]   dc2_pred0_r,          // DC2 alias predictor
  input [`npuarc_DC_PRED_BIT_RANGE]   dc2_pred1_r,          // DC2 alias predictor
  input                        dc2_lkup1_page_cross, // Page cross information
  input [`npuarc_DMP_TARGET_RANGE]    dc2_target_r,         // DC2 target
  input [3:0]                  dc2_data_bank_sel_r,  // DC2 data bank info 
  input                        dc2_stuck, 
  input [3:0]                  dc2_rmw,              // DC2 RMW
  output reg                   dc2_cft_stall,        // DC2 bank conflict stall 

  ////////// Interface to the X3 stage /////////////////////////////////
  //
  input                        x3_valid_r,     // X3 has valid instruction 
  input                        x3_pass,        // X3 passing on instruction
  input                        x3_enable,      // X3 accepts new instruction
  input                        x3_load_r,      // X3 load  
  input [`npuarc_PADDR_RANGE]         x3_mem_addr0_r,
  input [1:0]                  x3_size_r,
  input                        x3_store_r,
  input                        x3_locked_r,
  input                        x3_uop_inst_r,
 
  input                        dc3_dt_line_cross_r, 
  input [1:0]                  dc3_dt_bank_sel_r,
  input [`npuarc_DMP_TARGET_RANGE]    dc3_target_r,        // DC3 target
  input [`npuarc_PADDR_RANGE]         dc3_mem_addr_even,   // ppn=tag comparison, index=lru
  input [`npuarc_PADDR_RANGE]         dc3_mem_addr_odd,    // ppn for tag comparison
  input [`npuarc_PADDR_RANGE]         dc3_mem_addr1_r,
  input                        dc3_stall_r,   
  input                        dc3_partial_or_multi_conflict,
  input [3:0]                  dc3_rmw_r,           // DC3 RMW
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                        dc3_dtlb_ecc_error_r,
  input [1:0]                  dc3_dtlb_miss_r,
// spyglass enable_block W240
  input                        dc3_mispred,
  input                        dc3_enable,
  input [3:0]                  dc3_skid_ecc_valid, 
  ////////// Status ///////////////////////////////////////////
  //
  output                       dc3_dc_poisoned,
  output reg                   dc3_dccm_poisoned,    
  output reg                   dc3_dt_any_hit,
  output                       dc3_dt_hit,
  output                       dc3_dt_miss,
  output                       dc3_dt_miss_fast,
  output reg [3:0]             dc3_ecc_data_bank_sel,
  output reg                   dc4_dt_hit_r,
  output reg                   dc4_dt_miss_r,
  output                       dmu_mq_full,        
  output                       dmu_lsmq_full,
  output                       lsmq_two_empty,
  output                       dc4_lsmq_nomatch_replay,
  output                       dmu_wr_pending,   
  output [3:0]                 ecc_dc_tag_sbe_count_r,
  input                        dc_tag_ecc_sbe_clr,
  output [3:0]                 ecc_dc_data_sbe_count_r,
  input                        dc_data_ecc_sbe_clr,
  ////////// Interface to the CA stage //////////////////////////////////
  //
  input                        ca_enable,      // CA accepts new instruction
  input                        ca_load_r,
  input                        ca_pref_r,
  input                        ca_pref_l2_r,
  input                        ca_prefw_r,
  input                        ca_pre_alloc_r,
  input                        dc4_pref_bad_r,  
  input                        ca_store_r,
  input                        ca_locked_r,
  input                        ca_uop_inst_r, 
  input                        ca_pass,
  input                        ca_sex_r,
  input [1:0]                  ca_size_r,
  input                        ca_userm_r,
  input [`npuarc_GRAD_TAG_RANGE]      ca_grad_tag,              
  input                        ca_valid_r,
  input [`npuarc_PADDR_RANGE]         ca_mem_addr0_r,  
  input [`npuarc_PADDR_RANGE]         dc4_mem_addr1_r, 

  input [`npuarc_DMP_DATA_RANGE]      ca_wr_data_r,
  input                        dc4_dt_line_cross_r,  // addr1 is valid
  input                        dc4_scond_go,         // scond go ahead
  input  [`npuarc_DMP_TARGET_RANGE]   dc4_target_r,         // DC4 target
  input                        dc4_stall_r, 
  input                        dc4_mq_replay_r,      // MQ full replay
  input                        dc4_lsmq_replay_r,    // LSMQ full replay
  input                        dc4_wq_order_replay_r,// WQ order replay
// spyglass disable_block W240
// SMD: input declared but not used
// SJ:  unused in some configs
  input [3:0]                  dc4_rmw_r,            // DC4 RMW
// spyglass enable_block W240
  output reg                   dc4_dc_ecc_db_error,   // 2B error reporting
  input                        ecc_dmp_disable,       // Disable 1b and 2b errors
  input                        ecc_dmp_expn_disable,  // Disable 2b error excpn
  output reg                   dc4_dc_dt_ecc_db_error,// 2B error reporting
  output reg                   dc4_dc_dd_ecc_db_error,// 2B error reporting
  output reg [`npuarc_DC_TAG_SYNDROME_MSB:0]  fs_dc_tag_bank0_syndrome_r,
  output reg [`npuarc_DC_TAG_SYNDROME_MSB:0]  fs_dc_tag_bank1_syndrome_r,
  output reg [`npuarc_DC_TAG_SYNDROME_MSB:0]  fs_dc_tag_bank2_syndrome_r,
  output reg [`npuarc_DC_TAG_SYNDROME_MSB:0]  fs_dc_tag_bank3_syndrome_r,

  output reg                    fs_dc_tag_bank0_ecc_sb_error_r,
  output reg                    fs_dc_tag_bank1_ecc_sb_error_r,
  output reg                    fs_dc_tag_bank2_ecc_sb_error_r,
  output reg                    fs_dc_tag_bank3_ecc_sb_error_r,

  output reg                    fs_dc_tag_bank0_ecc_db_error_r,
  output reg                    fs_dc_tag_bank1_ecc_db_error_r,
  output reg                    fs_dc_tag_bank2_ecc_db_error_r,
  output reg                    fs_dc_tag_bank3_ecc_db_error_r,
    

  output reg [`npuarc_SYNDROME_MSB:0]  fs_dc_data_bank0_syndrome_r,  
  output reg [`npuarc_SYNDROME_MSB:0]  fs_dc_data_bank1_syndrome_r,  
  output reg [`npuarc_SYNDROME_MSB:0]  fs_dc_data_bank2_syndrome_r,  
  output reg [`npuarc_SYNDROME_MSB:0]  fs_dc_data_bank3_syndrome_r,  

  output reg                    fs_dc_data_bank0_ecc_sb_error_r,
  output reg                    fs_dc_data_bank1_ecc_sb_error_r,
  output reg                    fs_dc_data_bank2_ecc_sb_error_r,
  output reg                    fs_dc_data_bank3_ecc_sb_error_r,

  output reg                    fs_dc_data_bank0_ecc_db_error_r,
  output reg                    fs_dc_data_bank1_ecc_db_error_r,
  output reg                    fs_dc_data_bank2_ecc_db_error_r,
  output reg                    fs_dc_data_bank3_ecc_db_error_r,

//  `endif
  output reg [`npuarc_DC_WAY_RANGE]   dc4_hit_even_way_hot_r,
  output reg [`npuarc_DC_WAY_RANGE]   dc4_hit_odd_way_hot_r, 
  output reg                   dc4_waw_replay_r,
  ////////// Interface to the writeback stage ///////////////////////
  //
  input                        lq_empty_r,     // uncached loads pending
           
  input                        wa_restart_r,   // WB restart the pipeline
  input                        wa_replay_r,    // WB restart from DMP
  
  ////////// Write queue interface ////////////////////////////////////////
  //
  input                        wq_req_dd_even_lo,
  input [`npuarc_DC_ADR_RANGE]        wq_dd_addr_even_lo,
  input [`npuarc_DATA_RANGE]          wq_dd_din_even_lo,
  input [`npuarc_DC_BE_RANGE]         wq_dd_wem_even_lo,
  
  input                        wq_req_dd_even_hi,
  input [`npuarc_DC_ADR_RANGE]        wq_dd_addr_even_hi,
  input [`npuarc_DATA_RANGE]          wq_dd_din_even_hi,
  input [`npuarc_DC_BE_RANGE]         wq_dd_wem_even_hi,
  
  input                        wq_req_dd_odd_lo,
  input [`npuarc_DC_ADR_RANGE]        wq_dd_addr_odd_lo,
  input [`npuarc_DATA_RANGE]          wq_dd_din_odd_lo,
  input [`npuarc_DC_BE_RANGE]         wq_dd_wem_odd_lo,
  
  input                        wq_req_dd_odd_hi,
  input [`npuarc_DC_ADR_RANGE]        wq_dd_addr_odd_hi,
  input [`npuarc_DATA_RANGE]          wq_dd_din_odd_hi,
  input [`npuarc_DC_BE_RANGE]         wq_dd_wem_odd_hi,  
  input [`npuarc_DC_WAY_RANGE]        wq_dd_way_hot, 
  
  input                        wq_empty,

  input                        wq_dc_entry,
  input                        wq_dmu_set_conflict,
  input                        wq_scond_entry,
  output reg                   wq_read_one,
  ////////// SKID BUFFER INTERFACE ////////////////////////////////////
  //
  output                       dmu_evict_rd,

  output reg                   dc3_even_way0_hit,
  output reg                   dc3_odd_way0_hit,
  output reg [`npuarc_DC_WAY_RANGE]   dc3_dt_even_hit_way_hot_prel,
  output reg [`npuarc_DC_WAY_RANGE]   dc3_dt_odd_hit_way_hot_prel,
  input [`npuarc_DC_WAY_RANGE]        dc3_dt_even_hit_way_hot,
  input [`npuarc_DC_WAY_RANGE]        dc3_dt_odd_hit_way_hot,
  input                        dc4_wq_skid_replay_r,
  input [3:0]                  dc4_ecc_skid_sb_error_r,
  input [3:0]                  dc4_ecc_skid_db_error_r,
  input [`npuarc_SYNDROME_MSB:0]      dc_skid_bank0_syndrome_r,  
  input [`npuarc_SYNDROME_MSB:0]      dc_skid_bank1_syndrome_r,  
  input [`npuarc_SYNDROME_MSB:0]      dc_skid_bank2_syndrome_r,  
  input [`npuarc_SYNDROME_MSB:0]      dc_skid_bank3_syndrome_r,  
  
  
  input                           ecc0_even_sel,
  input                           ecc0_odd_sel,
  input  [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_even_lo ,
  input  [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_even_hi ,
  input  [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_odd_lo  ,
  input  [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc0_odd_hi  ,
  input  [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_even_lo ,
  input  [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_even_hi ,
  input  [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_odd_lo  ,
  input  [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_ecc1_odd_hi  ,

  input [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_even_lo,
  input [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_even_hi,
  input [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_odd_lo,
  input [`npuarc_DC_WAY_DATA_ECC_RANGE] dc3_dd_data_odd_hi,

  
  input [`npuarc_DC_TRAM_RANGE]         dc3_dt_even_w0,
  input [`npuarc_DC_TRAM_RANGE]         dc3_dt_even_w1,
  input [`npuarc_DC_TRAM_RANGE]         dc3_dt_odd_w0,
  input [`npuarc_DC_TRAM_RANGE]         dc3_dt_odd_w1,
  ////////// DTAG SRAM interface /////////////////////////////////////////
  //
  output                       clk_tag_even_w0,
  output reg                   dc_tag_even_cs_w0,  
  output reg                   dc_tag_even_we_w0,  
  output reg [`npuarc_DC_TRAM_RANGE]  dc_tag_even_wem_w0, 
  output reg [`npuarc_DC_IDX_RANGE]   dc_tag_even_addr_w0,
  output reg [`npuarc_DC_TRAM_RANGE]  dc_tag_even_din_w0, 
  input [`npuarc_DC_TRAM_RANGE]       dc_tag_even_dout_w0, 
                    
  output                       clk_tag_odd_w0,
  output reg                   dc_tag_odd_cs_w0,  
  output reg                   dc_tag_odd_we_w0,  
  output reg [`npuarc_DC_TRAM_RANGE]  dc_tag_odd_wem_w0, 
  output reg [`npuarc_DC_IDX_RANGE]   dc_tag_odd_addr_w0,
  output reg [`npuarc_DC_TRAM_RANGE]  dc_tag_odd_din_w0, 
  input [`npuarc_DC_TRAM_RANGE]       dc_tag_odd_dout_w0, 
  
  output                       clk_tag_even_w1,
  output reg                   dc_tag_even_cs_w1,  
  output reg                   dc_tag_even_we_w1,  
  output reg [`npuarc_DC_TRAM_RANGE]  dc_tag_even_wem_w1, 
  output reg [`npuarc_DC_IDX_RANGE]   dc_tag_even_addr_w1,
  output reg [`npuarc_DC_TRAM_RANGE]  dc_tag_even_din_w1, 
  input [`npuarc_DC_TRAM_RANGE]       dc_tag_even_dout_w1, 
                    
  output                       clk_tag_odd_w1,
  output reg                   dc_tag_odd_cs_w1,  
  output reg                   dc_tag_odd_we_w1,  
  output reg [`npuarc_DC_TRAM_RANGE]  dc_tag_odd_wem_w1, 
  output reg [`npuarc_DC_IDX_RANGE]   dc_tag_odd_addr_w1,
  output reg [`npuarc_DC_TRAM_RANGE]  dc_tag_odd_din_w1, 
  input [`npuarc_DC_TRAM_RANGE]       dc_tag_odd_dout_w1, 
  
  ////////// DDATA SRAM interface ///////////////////////////////////////////
  //
  output                        clk_data_even_lo,
  output reg                    dc_data_even_cs_lo,  
  output reg                    dc_data_even_we_lo,  
  output reg [`npuarc_DC_DBL_BE_RANGE] dc_data_even_wem_lo,  
  output reg [`npuarc_DC_ADR_RANGE]    dc_data_even_addr_lo, 
  output reg [`npuarc_DC_DRAM_RANGE]   dc_data_even_din_lo,

  output                        clk_data_even_hi,
  output reg                    dc_data_even_cs_hi,  
  output reg                    dc_data_even_we_hi,  
  output reg [`npuarc_DC_DBL_BE_RANGE] dc_data_even_wem_hi,  
  output reg [`npuarc_DC_ADR_RANGE]    dc_data_even_addr_hi,  
  output reg [`npuarc_DC_DRAM_RANGE]   dc_data_even_din_hi,

  output                        clk_data_odd_lo,
  output reg                    dc_data_odd_cs_lo,  
  output reg                    dc_data_odd_we_lo,  
  output reg [`npuarc_DC_DBL_BE_RANGE] dc_data_odd_wem_lo,  
  output reg [`npuarc_DC_ADR_RANGE]    dc_data_odd_addr_lo,  
  output reg [`npuarc_DC_DRAM_RANGE]   dc_data_odd_din_lo,

  output                        clk_data_odd_hi,
  output reg                    dc_data_odd_cs_hi,  
  output reg                    dc_data_odd_we_hi,  
  output reg [`npuarc_DC_DBL_BE_RANGE] dc_data_odd_wem_hi,  
  output reg [`npuarc_DC_ADR_RANGE]    dc_data_odd_addr_hi,  
  output reg [`npuarc_DC_DRAM_RANGE]   dc_data_odd_din_hi,

  ////////// Interface to the dmp_result bus (dc3 info) ///////////////////////
  //
  output reg                          dc_rb_req,
  output reg                          dc_dt_hit,

  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc_rb_bank0_lo_r,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc_rb_bank0_hi_r,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc_rb_bank1_lo_r,
  output reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc_rb_bank1_hi_r,
  ////////// ECC Interface to the DC4 stage (dc3 info) ///////////////////////
  //
  output reg                   dc4_dc_ecc_replay_r,
  input                        mq_rb_ack,       
  output [`npuarc_GRAD_TAG_RANGE]     mq_rb_tag,       
  output                       mq_rb_req,              
  output                       mq_rb_err,              
  output                       mq_userm,       
  output                       mq_sex,              
  output [1:0]                 mq_size,              
  output [3:0]                 mq_bank_sel,              
  output [`npuarc_PADDR_RANGE]        mq_rb_addr,              
  output [`npuarc_DC_DATA_RANGE]      mq_rb_data, 
  output                       mq_wr_err,             
  input  [`npuarc_DC_DATA_RANGE]      rb_aln_data,              

  output                       mq_flush_err_req,
  output [`npuarc_DC_LBUF_RANGE]      mq_flush_err_addr, 
  input                        mq_flush_err_ack,
  
  output                       rf_err_req,       
  output [`npuarc_DC_LBUF_RANGE]      rf_err_addr,      
  
  ////////// Refill interface to external memory //////////////////////////
  //
  output                       rf_cmd_valid, 
  output                       rf_cmd_excl, 
  input                        rf_cmd_accept,
  output                       rf_cmd_read,  
  output [`npuarc_PADDR_RANGE]        rf_cmd_addr,  
  output                       rf_cmd_prot,  
  output                       rf_cmd_wrap,  
  output [3:0]                 rf_cmd_burst_size,
  
  input                        rf_rd_valid,           
  input                        rf_rd_last, 
  input                        rf_err_rd,          
  output                       rf_rd_accept,           
  input  [`npuarc_RF_CB_DATA_RANGE]   rf_rd_data,   

  ////////// Copy back interface to external memory //////////////////////////
  //
  output                       cb_cmd_valid, 
  input                        cb_cmd_accept,
  output                       cb_cmd_read,  
  output [`npuarc_PADDR_RANGE]        cb_cmd_addr,  
  output                       cb_cmd_prot,  
  output                       cb_cmd_wrap,  
  output [3:0]                 cb_cmd_burst_size,
  
  output                       cb_wr_valid,    
  output                       cb_wr_last,    
  input                        cb_wr_accept,   
  output [`npuarc_RF_CB_MASK_RANGE]   cb_wr_mask,         
  output [`npuarc_RF_CB_DATA_RANGE]   cb_wr_data,  
  input                        cb_wr_done, 
  input                        cb_err_wr, 


  ////////// Interface with aux ctl ///////////////////////////////////////////
  //
  input                        aux_read,        //  (X3) Aux region read
  input                        aux_write,       //  (x3) Aux reagion write
  input                        aux_ren_r,       //  (X3) Aux region select
  input [4:0]                  aux_raddr_r,     //  (X3) Aux region addr
  input                        aux_wen_r,       //  (WA) Aux region select
  input [4:0]                  aux_waddr_r,     //  (WA) Aux write addr 
  input  [`npuarc_DATA_RANGE]         aux_wdata_r,     //  (WA) Aux write data
  
  output [`npuarc_ADDR_RANGE]         aux_rdata,       //  (X3) LR read data
  output                       aux_illegal,     //  (X3) SR/LR illegal
  output                       aux_k_rd,        //  (X3) needs Kernel Read
  output                       aux_k_wr,        //  (X3) needs Kernel Write
  output                       aux_unimpl,      //  (X3) Invalid Reg
  output                       aux_serial_sr,   //  (X3) SR group flush pipe
  output                       aux_strict_sr,   //  (X3) SR flush pipe
  output                       aux_busy,
  
  ////////// Interface with EXU  ///////////////////////////////////////////
  //
  output                       aux_x2_addr_pass,
  output  [`npuarc_ADDR_RANGE]        aux_x2_addr,
  output  [7:0]                aux_x2_addr_hi,

  ////////// Performance counters ///////////////////////////////////////////
  //
  output                       dc_pct_dcm,    // Data Cache miss
  output                       dc_pct_dclm,   // Data Cache load miss
  output                       dc_pct_dcsm,   // Data Cache store miss
  output reg                   dc_pct_dcbc,   // Data Cache bank conflicts
  output                       dc_pct_ivdc,   // Invalidate Data Cache
  output                       dc_pct_ivdl,   // Invalidate Data Line
  output                       dc_pct_flsh,   // Flush entire cache
  output                       dc_pct_fldl,   // Flush data line
  output reg                   dc_pct_bdcmstall,

  
  ////////// Status reporting /////////////////////////////////////////////
  //
  output                       dmu_empty,
  output                       mq_one_or_less_entry,
  output [`npuarc_DC_SET_RANGE]       dmu_set_addr,
  output                       aux_cache_off,
  



  ////////// General input signals ///////////////////////////////////////////
  //
  input                        clk,            // clock
  input                        clk_dmu, 
  input                        dbg_cache_rst_disable_r,

  input                        rst_cache_a,  
  input                        rst_a           // reset
// leda NTL_CON37 on 
// leda NTL_CON13C on 
);

// leda W175 off
// LMD: A parameter has been defined but is not used.
// LJ:  Code more readable; 

// Local declarations

reg                   dc1_load_valid;
reg                   dc1_store_valid;
reg                   dc1_cache_byp;
reg                   dc1_load_store_valid;
reg                   dc1_load_store_di;
reg                   dc1_load_store_uop;
reg                   dc1_req_dt_even;
reg                   dc1_req_dt_odd;

reg [1:0]             dc1_state_r;
reg [1:0]             dc1_state_nxt;

reg                   dc2_req_cg0;
reg                   dc2_kill;
reg                   dc2_req_dt_even_r;
reg                   dc2_req_dt_odd_r;
reg                   dc2_req_dd_even_lo_r;
reg                   dc2_req_dd_even_hi_r;
reg                   dc2_req_dd_odd_lo_r;
reg                   dc2_req_dd_odd_hi_r;
reg                   dc2_pref_r;
reg [`npuarc_DC_IDX_RANGE]   dc2_dt_addr0;
reg [`npuarc_DC_IDX_RANGE]   dc2_dt_addr1;
reg [`npuarc_DC_ADR_RANGE]   dc2_dd_addr0;
reg [`npuarc_DC_ADR_RANGE]   dc2_dd_addr1;


reg [`npuarc_DC_ADR_RANGE]   dc2_dd_addr0_qual;
reg [`npuarc_DC_ADR_RANGE]   dc2_dd_addr1_qual;


reg                   dc1_target_dc;
reg                   dc1_ld_target_dc;

reg                   dc2_req_dt_even;
reg                   dc2_req_dt_odd;
reg                   dc2_lost_ownership_to_dmu;  
reg                   dc2_lost_ownership_to_wq;  

reg                   dc2_target_dc;
reg                   dc2_ld_target_dc;
reg                   dc3_target_dc;
reg                   dc3_target_dccm;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variable are not used in certain configurations
reg                   dc3_ld_target_dc; 
reg                   dc3_st_target_dc; 
reg                   dc4_ld_target_dc; 
reg                   dc4_target_dc; 
reg                   dc4_st_target_dc; 
reg                   dc3_set_match0; 
reg                   dc3_set_match1; 
reg                   dc3_set_match; 
reg                   dc4_set_match0; 
reg                   dc4_set_match1; 
reg                   dc4_set_match; 
reg                   dc3_dmu_set_conflict;
reg                   dc4_dmu_set_conflict;
// leda NTL_CON13A on

reg                   dc1_uop_stall;
reg                   dc_pipe_empty;

wire [1:0]            aux_sg_off;
reg                   aux_ack_dt_even;
reg                   dmu_ack_dt_even;
reg                   dc2_ack_dt_even;
reg                   dc1_ack_dt_even;

reg                   aux_ack_dt_odd;
reg                   dmu_ack_dt_odd;
reg                   dc2_ack_dt_odd;
reg                   dc1_ack_dt_odd;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: some variable are not used in certain configurations
reg                      dc_pipe_ack_dt_even_r;
reg                      dc_pipe_ack_dt_odd_r;
// leda NTL_CON13A on
reg [`npuarc_DC_PRED_BIT_RANGE] dc2_pred0;
reg [`npuarc_DC_PRED_BIT_RANGE] dc2_pred1;
reg [`npuarc_DC_PRED_BIT_RANGE] dc3_dt_pred0_r;
reg [`npuarc_DC_PRED_BIT_RANGE] dc4_dd_pred0_r;

reg [`npuarc_DC_PRED_BIT_RANGE] dc3_dt_pred1_r;
reg [`npuarc_DC_PRED_BIT_RANGE] dc4_dd_pred1_r;
reg [`npuarc_DC_PRED_BIT_RANGE] dc3_pred0_r;
reg [`npuarc_DC_PRED_BIT_RANGE] dc3_pred1_r;
    

reg                   dmu_ack_ds;
reg                   aux_ack_ds; 

reg                   dc1_req_dd_even_lo;
reg                   dc1_req_dd_even_hi;
reg                   dc1_req_dd_odd_lo; 
reg                   dc1_req_dd_odd_hi; 

reg                   dc2_req_dd_even_lo;  
reg                   dc2_req_dd_even_hi;  
reg                   dc2_req_dd_odd_lo;   
reg                   dc2_req_dd_odd_hi;   

reg                   dc_pipe_ack_dd_even_lo_r;
reg                   dc_pipe_ack_dd_even_hi_r;
reg                   dc_pipe_ack_dd_odd_lo_r;
reg                   dc_pipe_ack_dd_odd_hi_r;

reg [3:0]             dc2_data_mem_valid_r;
reg [3:0]             dc3_data_mem_valid_r;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [1:0]             dc3_tag_mem_valid_r;
// leda NTL_CON32 on



reg                   dc4_dt_miss_even_r; 
reg                   dc4_dt_miss_odd_r;  
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc4_dd_data_even_lo_r;
reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc4_dd_data_even_hi_r;
reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc4_dd_data_odd_lo_r; 
reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc4_dd_data_odd_hi_r; 

reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc4_dd_data_even_lo_nxt;
reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc4_dd_data_even_hi_nxt;
reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc4_dd_data_odd_lo_nxt; 
reg [`npuarc_DC_WAY_DATA_ECC_RANGE] dc4_dd_data_odd_hi_nxt; 
// leda NTL_CON32 on
reg                   dmu_ack_dd_even_lo; 
reg                   dc1_ack_dd_even_lo; 
reg                   dc2_ack_dd_even_lo; 
reg                   wq_ack_dd_even_lo;  
reg                   aux_ack_dd_even_lo;

reg                   dmu_ack_dd_even_hi; 
reg                   dc1_ack_dd_even_hi; 
reg                   dc2_ack_dd_even_hi; 
reg                   wq_ack_dd_even_hi;  
reg                   aux_ack_dd_even_hi;

reg                   dmu_ack_dd_odd_lo; 
reg                   dc1_ack_dd_odd_lo; 
reg                   dc2_ack_dd_odd_lo; 
reg                   wq_ack_dd_odd_lo;  
reg                   aux_ack_dd_odd_lo;

reg                   dmu_ack_dd_odd_hi; 
reg                   dc1_ack_dd_odd_hi; 
reg                   dc2_ack_dd_odd_hi; 
reg                   wq_ack_dd_odd_hi;  
reg                   aux_ack_dd_odd_hi;

reg                   dc2_data_mem_valid_cg0;

reg [`npuarc_DC_BANK_RANGE]  dd_bank_busy_lo_r; 
reg [`npuarc_DC_BANK_RANGE]  dd_bank_busy_hi_r; 
wire [`npuarc_DC_BANK_RANGE] dd_bank_busy_lo_nxt; 
wire [`npuarc_DC_BANK_RANGE] dd_bank_busy_hi_nxt; 

reg                   dmu_block_dc_r;
reg                   dmu_block_dc_nxt;
reg                   dmu_block_dc_next;
reg                   dmu_data_sel_r;
reg                   dmu_data_sel_nxt;
reg                   dmu_data_sel_next;

reg                   dmu_has_dc_r;
reg                   dmu_has_dc_nxt;
wire                  dmu_has_dc_next;

reg [`npuarc_DC_WAY_RANGE]   dc_tag_even_cs_nxt;           
reg [`npuarc_DC_WAY_RANGE]   dc_tag_even_cs_next;           
reg [`npuarc_DC_IDX_RANGE]   dc_tag_even_addr_nxt;         
reg [`npuarc_DC_IDX_RANGE]   dc_tag_even_addr_next;         
reg                   dc_tag_even_we_nxt;           
reg                   dc_tag_even_we_next;           
reg [2:0]             dc_tag_even_wem_nxt;         
reg [2:0]             dc_tag_even_wem_next;         
reg                   dc_tag_even_valid_w0_nxt;        
reg                   dc_tag_even_valid_w0_next;        
reg [`npuarc_DC_TAG_RANGE]   dc_tag_even_tag_w0_nxt;          
reg [`npuarc_DC_TAG_RANGE]   dc_tag_even_tag_w0_next;          
reg                   dc_tag_even_valid_w1_nxt;        
reg                   dc_tag_even_valid_w1_next;        
reg [`npuarc_DC_TAG_RANGE]   dc_tag_even_tag_w1_nxt;          
reg [`npuarc_DC_TAG_RANGE]   dc_tag_even_tag_w1_next;          
                        
reg [`npuarc_DC_WAY_RANGE]   dc_tag_odd_cs_nxt;           
reg [`npuarc_DC_WAY_RANGE]   dc_tag_odd_cs_next;           
reg [`npuarc_DC_IDX_RANGE]   dc_tag_odd_addr_nxt;         
reg [`npuarc_DC_IDX_RANGE]   dc_tag_odd_addr_next;         
reg                   dc_tag_odd_we_nxt;           
reg                   dc_tag_odd_we_next;           
reg [2:0]             dc_tag_odd_wem_nxt;           
reg [2:0]             dc_tag_odd_wem_next;           
reg                   dc_tag_odd_valid_w0_nxt;        
reg                   dc_tag_odd_valid_w0_next;        
reg [`npuarc_DC_TAG_RANGE]   dc_tag_odd_tag_w0_nxt;          
reg [`npuarc_DC_TAG_RANGE]   dc_tag_odd_tag_w0_next;          
reg                   dc_tag_odd_valid_w1_nxt;        
reg                   dc_tag_odd_valid_w1_next;        
reg [`npuarc_DC_TAG_RANGE]   dc_tag_odd_tag_w1_nxt;          
reg [`npuarc_DC_TAG_RANGE]   dc_tag_odd_tag_w1_next;          
                        
// Clock enables
//
reg                   dc_tag_even_ctl_cg0;     
reg                   dc_tag_even_tag_ctl_cg0; 
reg                   dc_tag_even_tag_data_cg0;

reg                   dc_tag_odd_ctl_cg0;     
reg                   dc_tag_odd_tag_ctl_cg0; 
reg                   dc_tag_odd_tag_data_cg0;

reg [`npuarc_DC_WAY_RANGE]   dc3_dt_even_valid_way_hot;
reg [`npuarc_DC_WAY_RANGE]   dc3_dt_odd_valid_way_hot;

reg [`npuarc_DC_WAY_RANGE]   dc3_dt_even_tag_match_way_hot;
reg [`npuarc_DC_WAY_RANGE]   dc3_dt_odd_tag_match_way_hot;


wire                  dc3_stuck;

reg [`npuarc_DC_WAY_RANGE]   dc_tag_even_cs_r;           
reg [`npuarc_DC_IDX_RANGE]   dc_tag_even_addr_r;         
reg                   dc_tag_even_we_r;           
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [2:0]             dc_tag_even_wem_r;    // exclusive, valid, tag       
reg                   dc_tag_even_valid_w0_r;        
reg                   dc_tag_even_valid_w1_r;        
reg [`npuarc_DC_TAG_RANGE]   dc_tag_even_tag_w0_r;          
reg [`npuarc_DC_TAG_RANGE]   dc_tag_even_tag_w1_r;          

reg [`npuarc_DC_WAY_RANGE]   dc_tag_odd_cs_r;           
reg [`npuarc_DC_IDX_RANGE]   dc_tag_odd_addr_r;         
reg                   dc_tag_odd_we_r;           
reg [2:0]             dc_tag_odd_wem_r;    // exclusive, valid, tag        
// leda NTL_CON32 on
reg                   dc_tag_odd_valid_w0_r;        
reg                   dc_tag_odd_valid_w1_r;        
reg [`npuarc_DC_TAG_RANGE]   dc_tag_odd_tag_w0_r;          
reg [`npuarc_DC_TAG_RANGE]   dc_tag_odd_tag_w1_r;          
     
reg                   dc_data_even_din_lo_cg0; 
reg                   dc_data_even_din_hi_cg0; 
reg                   dc_data_odd_din_lo_cg0;  
reg                   dc_data_odd_din_hi_cg0;  

reg                   dc_data_even_addr_lo_cg0; 
reg                   dc_data_even_addr_hi_cg0; 
reg                   dc_data_odd_addr_lo_cg0;  
reg                   dc_data_odd_addr_hi_cg0;  

reg                            dc_data_even_cs_lo_nxt;    
reg                            dc_data_even_cs_lo_next;    
reg [`npuarc_DC_ADR_RANGE]            dc_data_even_addr_lo_nxt;  
reg [`npuarc_DC_ADR_RANGE]            dc_data_even_addr_lo_next;  
reg                            dc_data_even_we_lo_nxt;    
reg                            dc_data_even_we_lo_next;    
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_even_wem_lo_nxt;   
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_even_wem_lo_next;   
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_even_din_lo_nxt;
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_even_din_lo_next;

reg                            dc_data_even_cs_hi_nxt;    
reg                            dc_data_even_cs_hi_next;    
reg [`npuarc_DC_ADR_RANGE]            dc_data_even_addr_hi_nxt;  
reg [`npuarc_DC_ADR_RANGE]            dc_data_even_addr_hi_next;  
reg                            dc_data_even_we_hi_nxt;    
reg                            dc_data_even_we_hi_next;    
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_even_wem_hi_nxt;   
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_even_wem_hi_next;   
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_even_din_hi_nxt;
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_even_din_hi_next;

reg                            dc_data_odd_cs_lo_nxt;    
reg                            dc_data_odd_cs_lo_next;    
reg [`npuarc_DC_ADR_RANGE]            dc_data_odd_addr_lo_nxt;  
reg [`npuarc_DC_ADR_RANGE]            dc_data_odd_addr_lo_next;  
reg                            dc_data_odd_we_lo_nxt;    
reg                            dc_data_odd_we_lo_next;    
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_odd_wem_lo_nxt;   
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_odd_wem_lo_next;   
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_odd_din_lo_nxt; 
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_odd_din_lo_next; 

reg                            dc_data_odd_cs_hi_nxt;    
reg                            dc_data_odd_cs_hi_next;    
reg [`npuarc_DC_ADR_RANGE]            dc_data_odd_addr_hi_nxt;  
reg [`npuarc_DC_ADR_RANGE]            dc_data_odd_addr_hi_next;  
reg                            dc_data_odd_we_hi_nxt;    
reg                            dc_data_odd_we_hi_next;    
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_odd_wem_hi_nxt;   
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_odd_wem_hi_next;   
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_odd_din_hi_nxt; 
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_odd_din_hi_next; 

reg                            dc_data_even_cs_lo_r;    
reg [`npuarc_DC_ADR_RANGE]            dc_data_even_addr_lo_r;  
reg                            dc_data_even_we_lo_r;    
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_even_wem_lo_r;   
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_even_din_lo_r;

reg                            dc_data_even_cs_hi_r;    
reg [`npuarc_DC_ADR_RANGE]            dc_data_even_addr_hi_r;  
reg                            dc_data_even_we_hi_r;    
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_even_wem_hi_r;   
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_even_din_hi_r;

reg                            dc_data_odd_cs_lo_r;    
reg [`npuarc_DC_ADR_RANGE]            dc_data_odd_addr_lo_r;  
reg                            dc_data_odd_we_lo_r;    
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_odd_wem_lo_r;   
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_odd_din_lo_r; 

reg                            dc_data_odd_cs_hi_r;    
reg [`npuarc_DC_ADR_RANGE]            dc_data_odd_addr_hi_r;  
reg                            dc_data_odd_we_hi_r;    
reg [`npuarc_DC_DBL_BE_LO_RANGE]      dc_data_odd_wem_hi_r;   
reg [`npuarc_DC_WAY_DATA_ECC_RANGE]   dc_data_odd_din_hi_r; 

reg                            dc_data_way_hot_cg0;
reg [`npuarc_DC_WAY_RANGE]            dc_data_way_hot_nxt;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [`npuarc_DC_WAY_RANGE]            dc_data_way_hot_r;
// leda NTL_CON32 on


reg [3:0]              dc1_bank_req_mask;
reg [3:0]              dc2_bank_req_mask;
reg [3:0]              wq_top_bank_req_mask;
reg [3:0]              wq_sec_bank_req_mask;


reg [3:0]              dc1_bank_ack_mask;
reg [3:0]              dc1_bank_not_ack;
reg [3:0]              dc1_dc2_bank_common;
reg                    dc1_dc2_bank_common_set_cg0;
reg                    dc1_dc2_bank_common_clr_cg0;
reg [3:0]              dc1_dc2_bank_common_r;
reg [3:0]              dc1_dc2_bank_common_nxt;
reg [3:0]              dc2_bank_ack_mask;
reg [3:0]              dc2_bank_not_ack_r;
reg [3:0]              wq_bank_ack_mask;
reg [3:0]              dmu_bank_ack_mask;
reg                    dd_busy_nxt;

reg                    dc1_full_ack_dd;   
reg                    dc2_full_ack_dd;  
reg                    dc2_full_ack_dt; 
reg                    wq_top_full_ack_dd;
reg                    wq_sec_full_ack_dd;
reg                    dmu_full_ack;         


reg                    dmu_full_ack_dd;

reg                    aux_full_ack_dd;         

// wires
//
reg                   dc2_stuck_r;

wire                  aux_init_r;
wire                  aux_req_dt_even;
wire                  aux_req_dt_odd;
wire [`npuarc_DC_WAY_RANGE]  aux_dt_way_hot;
wire [`npuarc_DC_IDX_RANGE]  aux_dt_addr;
wire                  aux_dt_we;
wire [2:0]            aux_dt_wem;
wire                  aux_dt_valid;
wire [`npuarc_DC_TAG_RANGE]  aux_dt_tag;

wire                  dmu_req_dt_even;
wire                  dmu_req_dt_odd;
wire                  dmu_dt_odd_sel;
wire [`npuarc_DC_WAY_RANGE]  dmu_dt_way_hot;
wire [`npuarc_DC_IDX_RANGE]  dmu_dt_addr;
wire                  dmu_dt_we;
wire [2:0]            dmu_dt_wem;
wire                  dmu_dt_valid;
wire [`npuarc_DC_TAG_RANGE]  dmu_dt_tag;

wire                  aux_req_ds;
wire [`npuarc_DC_IDX_RANGE]  aux_ds_addr;
wire                  aux_ds_odd_sel;
wire                  aux_ds_we;
wire [2:0]            aux_ds_wem;
wire [`npuarc_DC_WAY_RANGE]  aux_ds_way_hot;
wire                  aux_ds_lock;
wire                  aux_ds_dirty;
wire                  aux_ds_lru;



wire                  aux_req_dd_even_lo;
wire                  aux_req_dd_even_hi;
wire                  aux_req_dd_odd_lo;
wire                  aux_req_dd_odd_hi;
wire [`npuarc_DC_ADR_RANGE]  aux_dd_addr;
wire [`npuarc_DC_WAY_RANGE]  aux_dd_way_hot; 
wire                  aux_dd_we;
wire [127:0]          aux_dd_din;
wire                  aux_dd_data_read;
wire                  aux_dd_direct_read;
wire [1:0]            aux_dd_data_bank;
reg  [31:0]           dc_dd_data;
reg  [31:0]           dc_dd_data_r;


wire                  aux_mq_write;
wire                  aux_mq_flush;
wire                  aux_mq_purge;
wire                  aux_mq_refill;
wire                  aux_mq_way;
wire [`npuarc_DC_LBUF_RANGE] aux_mq_addr;
wire                  aux_mq_lru_dirty;
wire                  lb_err_r;
wire                  mq_empty;
wire                  cb_full;

wire                  dmu_req_ds;
wire [`npuarc_DC_IDX_RANGE]  dmu_ds_addr;
wire                  dmu_ds_odd_sel;
wire                  dmu_ds_we;
wire [2:0]            dmu_ds_wem;
wire [`npuarc_DC_WAY_RANGE]  dmu_ds_way_hot;
wire                  dmu_ds_lock;
wire                  dmu_ds_dirty;
wire                  dmu_ds_lru;

wire                  dmu_req_dd;
wire [`npuarc_DC_ADR_RANGE]  dmu_dd_addr;
wire                  dmu_dd_we;
wire [`npuarc_DC_WAY_RANGE]  dmu_dd_way_hot; 
wire                  dmu_poison_stuck;
wire                  dmu_dc_idle;
wire [`npuarc_DC_DATA_RANGE] lbuf_rd_data;
wire [`npuarc_DC_DATA_RANGE] lbuf_rd_data_nxt;
wire [`npuarc_DC_LBUF_RANGE] dmu_line_addr;
wire [`npuarc_PADDR_RANGE]   mq_addr;
wire                  mq_valid;
wire                  dmu_dc_start;
wire                  dmu_dc_ready;
wire                  dmu_dc_read;
wire                  dmu_dc_done;

reg                   dc_pipe_enable_r;
reg                   dc_pipe_busy;

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: Not used in certain configurations
//wire                  dc3_dt_hit;
// leda NTL_CON13A on

// Input from Interface signals with DMU
wire                    mq_addr_even_hit;
wire                    mq_addr_odd_hit;
wire                    dmu_evict_hit;

reg                     dmu_ack_state_nxt;
wire                    dmu_ack_state_next;
reg                     dmu_ack_state_r;
reg                     dmu_dc_stall_r;
reg                     dmu_dc_stall_nxt;
reg                     dmu_dc_stall_next;
reg                     dmu_ack_ok;

// Output to Interface signals with DMU
reg [`npuarc_DC_TAG_RANGE]     dc3_dt_tag;
reg                     dc3_dt_val;
reg                     dc3_ds_lru;
reg [`npuarc_DC_WAY_RANGE]     dc3_ds_lock;
reg [`npuarc_DC_WAY_RANGE]     dc3_ds_dirty;
wire [`npuarc_DC_DATA_RANGE]   dc4_dd_data;
reg                     dc3_mq_addr_match;
reg                     dc4_mq_addr_match;
reg                     dc4_mq_set_match;
wire [`npuarc_DC_DATA_RANGE]   dc_rd_data;
wire [`npuarc_DC_DATA_RANGE]   dc_rd_data_nxt;
   

// Status array
//
reg                     dc_status0_write_even;
reg [`npuarc_DC_IDX_RANGE]     dc_status0_even_addr;
reg [2:0]               dc_status0_even_wem;
reg [`npuarc_DC_WAY_RANGE]     dc_status0_even_way_hot;
reg                     dc_status0_even_dirty;
reg                     dc_status0_even_lru;

reg                     dc_status0_write_odd;
reg [`npuarc_DC_IDX_RANGE]     dc_status0_odd_addr;
reg [2:0]               dc_status0_odd_wem;
reg [`npuarc_DC_WAY_RANGE]     dc_status0_odd_way_hot;
reg                     dc_status0_odd_dirty;
reg                     dc_status0_odd_lru;

reg                     dc_status1_read;
reg                     dc_status1_write;
reg  [`npuarc_DC_IDX_RANGE]    dc_status1_addr;
reg                     dc_status1_odd;
reg  [2:0]              dc_status1_wem;    
reg [`npuarc_DC_WAY_RANGE]     dc_status1_way_hot;
reg                     dc_status1_lock;
reg                     dc_status1_dirty;
reg                     dc_status1_lru;
wire                    status1_lru_even;
wire                    status1_lock_even;
wire [`npuarc_DC_WAY_RANGE]    status1_dirty_even;
wire                    status1_lru_odd;
wire                    status1_lock_odd;
wire [`npuarc_DC_WAY_RANGE]    status1_dirty_odd;



// leda NTL_CON13A off
// LMD: non driving internal net
// LJ: Not used in certain configurations

reg                     dmu_aux_dd_read;   
reg [`npuarc_DC_WAY_RANGE]     dmu_aux_dd_way_hot;
// leda NTL_CON13A on

reg                     dc2_tag_mem_valid;

reg                     dc3_tag_mem_valid;

reg                     dc3_set_poisoned;       
reg                     dc3_reset_poisoned;     
reg                     dc3_dc_poisoned_prel_r; 
reg                     dc3_dc_poisoned_prel_nxt; 

reg                     aux_busy_stall;

reg                     dc1_wq_order_block_r;
reg                     dc1_wq_order_block_nxt;
reg                     dc1_wq_order_state_r;
reg                     dc1_wq_order_state_nxt;
reg                     dc1_ecc_block_nxt;
reg                     dc1_ecc_block_r;
reg                     dc1_ecc_state_nxt;
reg                     dc1_ecc_state_r;
reg [3:0]               dc4_dd_ecc_sb_error;
reg [3:0]               dc4_dd_ecc_db_error;
reg                     dt_ecc_scrub;
reg                     dd_ecc_scrub;
reg                     dc4_dt_ecc_scrub_start;
reg                     dc4_dd_ecc_scrub_start;
reg                     aux_ecc_scrub_in_progress_r;
reg                     aux_ecc_scrub_in_progress_nxt;
wire                    aux_ecc_scrub_in_progress_next;
reg                     wa_dt_ecc_scrub_start_r;
reg                     wa_dd_ecc_scrub_start_r;
//reg                     dc4_dc_dd_ecc_db_error;
//reg                     dc4_dc_dt_ecc_db_error;
wire                    aux_dt_read;

wire [3:0]              dc_tag_read;
wire [3:0]              dc_tag_active;
reg  [3:0]              dc_tag_read_r;
reg  [3:0]              dc_tag_active_r;
wire [3:0]              dc_data_read;
reg  [3:0]              dc_data_read_r;
reg                     dmu_aux_dc_data_read_r;
reg  [3:0]              dmu_aux_dc_tag_read_r;

assign dc_tag_read  =   {dc_tag_odd_cs_r, dc_tag_even_cs_r}
                      & (~{{2{dc_tag_odd_we_r}}, {2{dc_tag_even_we_r}}})
                      & dmu_aux_dc_tag_read_r;

assign dc_tag_active =  {dc_tag_odd_cs_r, dc_tag_even_cs_r}
                      & dmu_aux_dc_tag_read_r;

assign dc_data_read =   (({   dc_data_odd_cs_hi_r, dc_data_odd_cs_lo_r,
                              dc_data_even_cs_hi_r,dc_data_even_cs_lo_r }))
                      & (~(({   dc_data_odd_we_hi_r, dc_data_odd_we_lo_r,
                                dc_data_even_we_hi_r, dc_data_even_we_lo_r})))
                      & {4{dmu_aux_dc_data_read_r}};
wire                    aux_ecc_done_r;



reg                     dc3_addr_match0;
reg                     dc3_addr_match1;
reg                     dc4_addr_match0; 
reg                     dc4_addr_match1;
reg                     dc4_st_no_grad_cg0;
reg  [3:0]              dc2_dc3_bank_common_match;

wire [1:0]              dc4_lsmq_write;
wire                    lsmq_match0;
wire                    lsmq_match1;
reg [3:0]               dc4_skid_ecc_valid_r;
reg                     wa_restart_rr;
reg                     wq_dmu_empty_r;


wire                    dmu_evict_rd_r;
assign dmu_evict_rd_r = 1'b0;




//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asynchronous block defining a valid dc1 instruction
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_load_store_PROC
  // Indicates uncached. Note the pref instructions are encoded overloading 
  // the pref ucode bit
  //
  dc1_cache_byp = x1_cache_byp_r & (~x1_pref_r);
  
  // The 'dc1_valid' signal is asserted whenever there is a load or store
  // instruction X1 targeting the Data Cache
  //
  dc1_load_valid  =   (  x1_load_r  
                       | ((|dc1_rmw) & x1_store_r)
                      ) 
                    & (x1_valid_r)
                    & (~dc1_cache_byp);
  
  dc1_store_valid =    x1_valid_r  
                    & (x1_store_r)
                    & (~dc1_cache_byp);

  dc1_load_store_valid = x1_valid_r
                       & (x1_load_r | x1_store_r)   
                       & (~dc1_cache_byp);

  dc1_load_store_di    =  (x1_load_r | x1_store_r)   
                        & (dc1_cache_byp);
                        
  dc1_load_store_uop   =   (x1_load_r | x1_store_r)  
                         & x1_uop_inst_r;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asynchronous block defining the dc1 logic for the dt pipeline accesses
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_req_dt_PROC
  // Tag requests from the pipeline
  //
  ////////////////////////////////////////////////////////////////////////////
  //                 Bank even                     Bank odd
  //   ________________________________________________________________
  //  |       bank_         bank_     |       bank_         bank_      |
  //  |     dd_even_hi     dd_even_lo |     dd_odd_hi     dd_odd_lo    |
  //  |    _________      _________   |   _________       _________    |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |<------->|    |<------->|  |  |<------->|     |<------->|   |
  //  |   |   32B   |    |   32B   |  |  |   32B   |     |   32B   |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |_________|    |_________|  |  |_________|     |_________|   |
  //  |                               |                                |
  //  |                               |                                |
  //  |_______________________________|________________________________|
  //  
  dc1_req_dt_even = (dc1_load_valid | dc1_store_valid) 
                   & dc1_dt_bank_sel[0]
                   & x1_pass;
  
  dc1_req_dt_odd  = (dc1_load_valid | dc1_store_valid) 
                   & dc1_dt_bank_sel[1]
                   & x1_pass;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asynchronous block defining the dc1 logic for the dd pipeline accesses
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_req_dd_PROC
  // Data requests from the pipeline.
  //
  dc1_req_dd_even_lo =  dc1_load_valid 
                      & dc1_data_bank_sel_lo[0]
                      & (~x1_pref_r)
                      & x1_pass;
  
  dc1_req_dd_even_hi =  dc1_load_valid 
                      & dc1_data_bank_sel_hi[0]
                      & (~x1_pref_r)
                      & x1_pass;

  dc1_req_dd_odd_lo  =  dc1_load_valid 
                      & dc1_data_bank_sel_lo[1]
                      & (~x1_pref_r)
                      & x1_pass;
  
  dc1_req_dd_odd_hi  =  dc1_load_valid 
                      & dc1_data_bank_sel_hi[1]
                      & (~x1_pref_r)
                      & x1_pass;

end


//////////////////////////////////////////////////////////////////////////////
// DC1 stall FSM 
//                                                                           
//////////////////////////////////////////////////////////////////////////////
parameter DC1_DEFAULT    = 2'b00;
parameter DC1_SMP_BLOCK  = 2'b01;
parameter DC1_FULL_BLOCK = 2'b10;


wire  dc4_agu_smp_replay;

assign dc4_agu_smp_replay =  1'b0
                          ;

always @*
begin : dc1_stall_fsm_PROC
  dc1_stall           =   (dc1_load_store_valid & dmu_block_dc_r)  
                        | (dc1_load_store_valid & dmu_dc_stall_r)  
                        | (dc1_load_store_valid & aux_busy_stall)  
                        | (dc1_load_store_uop   & dc1_uop_stall)  
                        | (dc1_load_store_di    & aux_busy_stall)  
                        | (aux_init_r)
                        | (dc1_wq_order_block_r)
                        | (dc1_load_store_valid & dc1_ecc_block_r)
                        ;
  
  dmu_block_dc_nxt        = dmu_block_dc_r;
 
  dc1_state_nxt           = dc1_state_r;
  dmu_data_sel_nxt        = dmu_evict_rd;
  
  case (dc1_state_r)
  DC1_DEFAULT:
  begin
    dmu_block_dc_nxt    =    dc4_mq_replay_r
                           | dc4_lsmq_replay_r 
                           | dc4_agu_smp_replay
                           ;
    
    casez ({
            dc4_agu_smp_replay,
            dc4_mq_replay_r,
            dc4_lsmq_replay_r
            })
// spyglass disable_block STARC05-2.8.1.3
// SMD: case label overlaps with another clase label
// SJ:  Done on purpose to cover multiple cases except 3'b000
    3'b01?,
    3'b0?1:  dc1_state_nxt = DC1_FULL_BLOCK;
// spyglass enable_block STARC05-2.8.1.3
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
    default:;
    endcase
// spyglass enable_block W193    
  end
  
  
  default: // DC1_FULL_BLOCK
  begin
    // The DMP pipeline is blocked
    //
    if ( ~(dmu_mq_full | dmu_lsmq_full))
    begin
      // Wait until the line buffer writes the line into the cache
      //
      dmu_block_dc_nxt    = 1'b0;
      dc1_state_nxt       = DC1_DEFAULT;
    end
  end 
  endcase
end

always @*
begin : dmu_has_dc_nxt_PROC
  dmu_has_dc_nxt = dmu_has_dc_r;
  
  if (dmu_dc_start & dmu_ack_ok)
  begin
    dmu_has_dc_nxt = 1'b1;
  end
  else if (dmu_dc_done)
  begin
    dmu_has_dc_nxt = 1'b0;
  end
end

//////////////////////////////////////////////////////////////////////////////
// DC1 WQ ORDER REPLAY BLOCK
//
//////////////////////////////////////////////////////////////////////////////
parameter DC1_WQ_ORDER_DEFAULT = 1'b0;
parameter DC1_WQ_ORDER_BLOCK   = 1'b1;

always @*
begin : dc1_wq_order_fsm_PROC
  dc1_wq_order_state_nxt   = dc1_wq_order_state_r;
  dc1_wq_order_block_nxt   = dc1_wq_order_block_r;
     
  case (dc1_wq_order_state_r)
  DC1_WQ_ORDER_DEFAULT:
  begin
    if (dc4_wq_order_replay_r)
    begin
      dc1_wq_order_state_nxt   = 1'b1;
      dc1_wq_order_block_nxt   = DC1_WQ_ORDER_BLOCK;
    end
  end

  default:
  begin
    // When WQ become empty
    // DMU might not be empty due to snoop interventions
    //
    if (wq_empty)// & dmu_empty)
    begin
      dc1_wq_order_state_nxt   = 1'b0;
      dc1_wq_order_block_nxt   = DC1_WQ_ORDER_DEFAULT;
    end
  end
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// DC1 ECC
//                                                                           
//////////////////////////////////////////////////////////////////////////////
parameter DC1_ECC_DEFAULT = 1'b0;
parameter DC1_ECC_BLOCK   = 1'b1;

wire   dc4_ecc_replay;
assign dc4_ecc_replay   = 1'b0
                           | dc4_dc_ecc_replay_r
                           ;     
always @*
begin : dc1_ecc_fsm_PROC
  dc1_ecc_state_nxt   = dc1_ecc_state_r;
  dc1_ecc_block_nxt   = dc1_ecc_block_r;
 
  case (dc1_ecc_state_r)
  DC1_ECC_DEFAULT:
  begin
    if (dc4_ecc_replay)
    begin
      dc1_ecc_block_nxt  = 1'b1; 
      dc1_ecc_state_nxt  = DC1_ECC_BLOCK;
    end
  end
  default:  //  DC1_ECC_BLOCK
  begin
    // When WQ become empty
    // DMU might not be empty due to snoop interventions
    //
    if (wq_empty & dmu_empty)
    begin
      dc1_ecc_block_nxt  = 1'b0;
      dc1_ecc_state_nxt  = DC1_ECC_DEFAULT;
    end
  end
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// DC2 PREDICTION ADDRESS
//  
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc2_pred_address_PROC
  // The following three cases
  //
  casez ({x2_mem_addr0_r[`npuarc_DC_TAG_BANK_ID], dc2_lkup1_page_cross})
  2'b?0:
  begin
    // No page cross
    //
    dc2_pred0 = dc2_pred0_r;
    dc2_pred1 = dc2_pred0_r;
  end
  2'b01: 
  begin
    // There is a page cross and the requested address0 is an even addr
    //
    dc2_pred0 = dc2_pred0_r;
    dc2_pred1 = dc2_pred1_r;
  end 
  2'b11: 
  begin
    // There is a page cross and the requested address0 is an odd addr
    //
    dc2_pred0 = dc2_pred1_r;
    dc2_pred1 = dc2_pred0_r;
  end
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
  default:
    ;
// spyglass enable_block W193   
  endcase  
end

always @*
begin : dc2_kill_PROC
  //
  //
  dc2_kill                   =   wa_restart_r
                             | (~(x2_load_r | x2_store_r));
end     


always @*
begin : dc2_req_cg0_PROC
  // dc2 request clock gate
  //
  dc2_req_cg0     = (dc1_load_store_valid & x1_pass)
//                  | (dc2_target_dc & x2_pass)
                  ;  
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Data tag arbiter: even 
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : data_tag_arbiter_even_PROC
  // Arbitration - Priorities:
  //   1. DMU request (refill/ copyback)
  //   2. dc2 request 
  //   3. dc1 request 
  //   4. Aux request 
  //
  dmu_ack_dt_even  = 1'b0;
  aux_ack_dt_even  = 1'b0;
  dc2_ack_dt_even  = 1'b0;
  dc1_ack_dt_even  = 1'b0;
 
  
  casez ({dmu_req_dt_even,
          dc2_req_dt_even,
          dc1_req_dt_even,
          aux_req_dt_even})
  
  4'b1???: dmu_ack_dt_even = 1'b1;
  4'b01??: dc2_ack_dt_even = ~dmu_has_dc_r;
  4'b001?: dc1_ack_dt_even = ~dmu_has_dc_r;
  4'b0001: aux_ack_dt_even = 1'b1;
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
  default:
    ;
// spyglass enable_block W193   
  endcase  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Data tag even flops (nxt values)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
//
// spyglass disable_block STARC05-2.8.1.3
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
always @*
begin : tag_even_PROC
  // cs per way
  //
  dc_tag_even_cs_nxt       = {`npuarc_DC_WAYS{1'b0}};

  // Common accross ways
  //
  dc_tag_even_addr_nxt     = {`npuarc_DC_IDX_BITS{1'b0}};
  
  dc_tag_even_we_nxt       = 1'b0;
  dc_tag_even_wem_nxt      = 3'b000;  // exclusive, valid, tag
  
  
  dc_tag_even_valid_w0_nxt = 1'b0;
  dc_tag_even_tag_w0_nxt   = {`npuarc_DC_TAG_BITS{1'b0}};
  
  dc_tag_even_valid_w1_nxt = 1'b0;
  dc_tag_even_tag_w1_nxt   = {`npuarc_DC_TAG_BITS{1'b0}};
                          
  // Clock enables
  //
  dc_tag_even_ctl_cg0      =  aux_ack_dt_even
                            | dmu_ack_dt_even
                            | dc2_ack_dt_even
                            | dc1_ack_dt_even
                            | aux_init_r
                            ;

  dc_tag_even_tag_ctl_cg0  = 1'b0;
  dc_tag_even_tag_data_cg0 = 1'b0;
   
  casez ({
          1'b0,
          dmu_ack_dt_even,
          dc2_ack_dt_even,
          dc1_ack_dt_even,
          aux_ack_dt_even})
  

  5'b01???:
  begin
    // Data Cache Miss Unit (dmu) ack
    //
    dc_tag_even_cs_nxt        = dmu_dt_way_hot;
    dc_tag_even_we_nxt        = dmu_dt_we;
    dc_tag_even_wem_nxt       = dmu_dt_wem;

    dc_tag_even_addr_nxt      = dmu_dt_addr;
    
    
    dc_tag_even_valid_w0_nxt  = dmu_dt_valid;
    dc_tag_even_tag_w0_nxt    = dmu_dt_tag;

    dc_tag_even_valid_w1_nxt  = dmu_dt_valid;
    dc_tag_even_tag_w1_nxt    = dmu_dt_tag;
    
    dc_tag_even_tag_ctl_cg0   = (| dmu_dt_wem);
    dc_tag_even_tag_data_cg0  = dmu_dt_wem[`npuarc_DC_TAG_MASK];
  end
  
  5'b0?1??:
  begin
    // Regular pipeline requests coming from dc2 ack
    // dc2_ack_dt_even
    //
    // We only do reads from DC2
    //
    dc_tag_even_cs_nxt         = {(dc2_target_r == `npuarc_DMP_TARGET_DC),
                                  (dc2_target_r == `npuarc_DMP_TARGET_DC)};
    dc_tag_even_addr_nxt       = dc2_dt_addr0; 
  end
  
  5'b0??1?:
  begin
    // Regular pipeline requests coming from dc1 ack
    // dc1_ack_dt_even
    //
    // We only do reads from DC1
    //
    dc_tag_even_cs_nxt         = {(dc1_target == `npuarc_DMP_TARGET_DC),
                                  (dc1_target == `npuarc_DMP_TARGET_DC)};
    dc_tag_even_addr_nxt       = dc1_dt_addr0;
  end
  
  5'b0???1:
  begin
    // Cache instructions ack:
    // aux_ack_dt_even
    //
    dc_tag_even_cs_nxt        = aux_dt_way_hot;
    dc_tag_even_we_nxt        = aux_dt_we;
    dc_tag_even_wem_nxt       = aux_dt_wem;

    dc_tag_even_addr_nxt      = aux_dt_addr;
    
    
    dc_tag_even_valid_w0_nxt  = aux_dt_valid;
    dc_tag_even_tag_w0_nxt    = aux_dt_tag;

    dc_tag_even_valid_w1_nxt  = aux_dt_valid;
    dc_tag_even_tag_w1_nxt    = aux_dt_tag;
    
    dc_tag_even_tag_ctl_cg0   = (| aux_dt_wem);
    dc_tag_even_tag_data_cg0  = aux_dt_wem[`npuarc_DC_TAG_MASK];
  end
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept  
  default:
    ;
// spyglass enable_block W193   
  endcase
   
end
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
// leda W547 on
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Data tag arbiter: odd 
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : data_tag_arbiter_odd_PROC
  // Arbitration - Priorities:
  //   1. DMU request (refill/ copyback)
  //   2. dc2 request 
  //   3. dc1 request 
  //   4. Aux request 
  //
  dmu_ack_dt_odd  = 1'b0;
  aux_ack_dt_odd  = 1'b0;
  dc2_ack_dt_odd  = 1'b0;
  dc1_ack_dt_odd  = 1'b0;
 
  
  casez ({dmu_req_dt_odd,
          dc2_req_dt_odd,
          dc1_req_dt_odd,
          aux_req_dt_odd})
  
  4'b1???: dmu_ack_dt_odd = 1'b1;
  4'b01??: dc2_ack_dt_odd = ~dmu_has_dc_r;
  4'b001?: dc1_ack_dt_odd = ~dmu_has_dc_r;
  4'b0001: aux_ack_dt_odd = 1'b1;
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
  default:
    ;
// spyglass enable_block W193   
  endcase  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Data tag odd flops (nxt values)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
//
// spyglass disable_block STARC05-2.8.1.3
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.

always @*
begin : tag_odd_PROC
  // cs per way
  //
  dc_tag_odd_cs_nxt       = {`npuarc_DC_WAYS{1'b0}};

  // Common accross ways
  //
  dc_tag_odd_addr_nxt     = {`npuarc_DC_IDX_BITS{1'b0}};
  
  dc_tag_odd_we_nxt       = 1'b0;
  dc_tag_odd_wem_nxt      = 3'b000;  // exclusive, valid, tag
  

  dc_tag_odd_valid_w0_nxt = 1'b0;
  dc_tag_odd_tag_w0_nxt   = {`npuarc_DC_TAG_BITS{1'b0}};
  
  dc_tag_odd_valid_w1_nxt = 1'b0;
  dc_tag_odd_tag_w1_nxt   = {`npuarc_DC_TAG_BITS{1'b0}};
                          
  // Clock enables
  //
  dc_tag_odd_ctl_cg0      =   aux_ack_dt_odd
                            | dmu_ack_dt_odd
                            | dc2_ack_dt_odd
                            | dc1_ack_dt_odd
                            | aux_init_r
                            ;

  dc_tag_odd_tag_ctl_cg0  = 1'b0;
  dc_tag_odd_tag_data_cg0 = 1'b0;
   
  casez ({
          1'b0,
          dmu_ack_dt_odd,
          dc2_ack_dt_odd,
          dc1_ack_dt_odd,
          aux_ack_dt_odd})
  
  
  
  5'b01???:
  begin
    // Data Cache Miss Unit (dmu) ack
    //
    dc_tag_odd_cs_nxt        = dmu_dt_way_hot;
    dc_tag_odd_we_nxt        = dmu_dt_we;
    dc_tag_odd_wem_nxt       = dmu_dt_wem;

    dc_tag_odd_addr_nxt      = dmu_dt_addr;
    

    dc_tag_odd_valid_w0_nxt  = dmu_dt_valid;
    dc_tag_odd_tag_w0_nxt    = dmu_dt_tag;

    dc_tag_odd_valid_w1_nxt  = dmu_dt_valid;
    dc_tag_odd_tag_w1_nxt    = dmu_dt_tag;
    
    dc_tag_odd_tag_ctl_cg0   = (| dmu_dt_wem);
    dc_tag_odd_tag_data_cg0  = dmu_dt_wem[`npuarc_DC_TAG_MASK];
  end
  
  5'b0?1??:
  begin
    // Regular pipeline requests coming from dc2 ack
    // dc2_ack_dt_odd
    //
    // We only do reads from DC2
    //
    dc_tag_odd_cs_nxt         = {(dc2_target_r == `npuarc_DMP_TARGET_DC),
                                 (dc2_target_r == `npuarc_DMP_TARGET_DC)};
    dc_tag_odd_addr_nxt       = dc2_dt_addr1; 
  end
  
  5'b0??1?:
  begin
    // Regular pipeline requests coming from dc1 ack
    // dc1_ack_dt_odd
    //
    // We only do reads from DC1
    //
    dc_tag_odd_cs_nxt         = {(dc1_target == `npuarc_DMP_TARGET_DC),
                                 (dc1_target == `npuarc_DMP_TARGET_DC)};
    dc_tag_odd_addr_nxt       = dc1_dt_addr1;
  end
  
  5'b0???1:
  begin
    // Cache instructions/IO coherency ack:
    // aux_ack_dt_odd
    //
    dc_tag_odd_cs_nxt        = aux_dt_way_hot;
    dc_tag_odd_we_nxt        = aux_dt_we;
    dc_tag_odd_wem_nxt       = aux_dt_wem;

    dc_tag_odd_addr_nxt      = aux_dt_addr;
    

    dc_tag_odd_valid_w0_nxt  = aux_dt_valid;
    dc_tag_odd_tag_w0_nxt    = aux_dt_tag;

    dc_tag_odd_valid_w1_nxt  = aux_dt_valid;
    dc_tag_odd_tag_w1_nxt    = aux_dt_tag;
    
    dc_tag_odd_tag_ctl_cg0   = (| aux_dt_wem);
    dc_tag_odd_tag_data_cg0  = aux_dt_wem[`npuarc_DC_TAG_MASK];
  end
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
  default:
    ;
// spyglass enable_block W193   
  endcase
   
end
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
// leda W547 on

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Data data arbiter: even
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : data_data_arbiter_even_PROC
  dmu_ack_dd_even_lo            = 1'b0;
  dc2_ack_dd_even_lo            = 1'b0; 
  dc1_ack_dd_even_lo            = 1'b0;
  wq_ack_dd_even_lo             = 1'b0;
  aux_ack_dd_even_lo            = 1'b0;
  
  // We dont give the dd bank to DC1 when there was a DC2 instruction stuck
  // in DC2. This prevents the DC1 instruction from accessing the DD bank
  // that may have its output holding the data for the DC2 instruction
  //
 
  // (1) the bank busy might not work in case of 3 back to back loads to same address
  // because, first load would have kept the bank busy and second load wouldn't have requested
  // the bank, but instead would have re-used the data from earlier Load, when the third load arrives
  // it does not see bank busy (since second LD have not requested the banks) and get the ack
  // This would corrupt the data for the second load. hence use the bank common match to give ack to dc1
  //
  
  // (1) when there is a dc1 dc2 bank common, WQ can wait
  //   

  // lo arbiter
  //
  casez ({dmu_req_dd,
          dc2_req_dd_even_lo,
          dc1_req_dd_even_lo,
          wq_req_dd_even_lo,
          aux_req_dd_even_lo})
  
  5'b1????: dmu_ack_dd_even_lo = !dd_bank_busy_lo_r[0];
  5'b01???: dc2_ack_dd_even_lo = !dd_bank_busy_lo_r[0] & (~dmu_has_dc_r);
  5'b001??: dc1_ack_dd_even_lo = !dd_bank_busy_lo_r[0] & (~dc2_stuck_r)  & (~dmu_has_dc_r) & (~dc2_dc3_bank_common_match[0]); // (1)
  5'b0001?: wq_ack_dd_even_lo  = !dd_bank_busy_lo_r[0] & (~dmu_has_dc_r) & (~dc1_dc2_bank_common_r[0]);
  5'b00001: aux_ack_dd_even_lo = !dd_bank_busy_lo_r[0];
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
  default:
    ;
// spyglass enable_block W193   
  endcase
  
  // ============================================================
  //
  
  dmu_ack_dd_even_hi            = 1'b0;
  dc2_ack_dd_even_hi            = 1'b0; 
  dc1_ack_dd_even_hi            = 1'b0;
  wq_ack_dd_even_hi             = 1'b0;
  aux_ack_dd_even_hi            = 1'b0;
  
  // We dont give the dd bank to DC1 when there was a DC2 instruction stuck
  // in DC2. This prevents the DC1 instruction from accessing the DD bank
  // that may have its output holding the data for the DC2 instruction
  //
  
  // (1) when there is a dc1 dc2 bank common, WQ can wait
  //   

  // hi arbiter
  //
  casez ({dmu_req_dd,
          dc2_req_dd_even_hi,
          dc1_req_dd_even_hi,
          wq_req_dd_even_hi,
          aux_req_dd_even_hi})
  
  5'b1????: dmu_ack_dd_even_hi = !dd_bank_busy_hi_r[0];
  5'b01???: dc2_ack_dd_even_hi = !dd_bank_busy_hi_r[0] & (~dmu_has_dc_r);
  5'b001??: dc1_ack_dd_even_hi = !dd_bank_busy_hi_r[0] & (~dc2_stuck_r) & (~dmu_has_dc_r) & (~dc2_dc3_bank_common_match[1]);
  5'b0001?: wq_ack_dd_even_hi  = !dd_bank_busy_hi_r[0] & (~dmu_has_dc_r)& (~dc1_dc2_bank_common_r[1]);
  5'b00001: aux_ack_dd_even_hi = !dd_bank_busy_hi_r[0];
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
  default:
    ;
// spyglass enable_block W193   
  endcase

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Data data arbiter: odd
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : data_data_arbiter_odd_PROC
  dmu_ack_dd_odd_lo            = 1'b0;
  dc2_ack_dd_odd_lo            = 1'b0; 
  dc1_ack_dd_odd_lo            = 1'b0;
  wq_ack_dd_odd_lo             = 1'b0;
  aux_ack_dd_odd_lo            = 1'b0;
  
  // We dont give the dd bank to DC1 when there was a DC2 instruction stuck
  // in DC2. This prevents the DC1 instruction from accessing the DD bank
  // that may have its output holding the data for the DC2 instruction
  //
  
  // (1) when there is a dc1 dc2 bank common, WQ can wait
  //   

  // lo arbiter
  //
  casez ({dmu_req_dd,
          dc2_req_dd_odd_lo,
          dc1_req_dd_odd_lo,
          wq_req_dd_odd_lo,
          aux_req_dd_odd_lo})
  
  5'b1????: dmu_ack_dd_odd_lo = !dd_bank_busy_lo_r[1];
  5'b01???: dc2_ack_dd_odd_lo = !dd_bank_busy_lo_r[1] & (~dmu_has_dc_r);
  5'b001??: dc1_ack_dd_odd_lo = !dd_bank_busy_lo_r[1] & (~dc2_stuck_r) & (~dmu_has_dc_r) & (~dc2_dc3_bank_common_match[2]);
  5'b0001?: wq_ack_dd_odd_lo  = !dd_bank_busy_lo_r[1] & (~dmu_has_dc_r)& (~dc1_dc2_bank_common_r[2]);
  5'b00001: aux_ack_dd_odd_lo = !dd_bank_busy_lo_r[1];
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
  default:
    ;
// spyglass enable_block W193   
  endcase

  
  // =====================================================
  
  dmu_ack_dd_odd_hi            = 1'b0;
  dc2_ack_dd_odd_hi            = 1'b0; 
  dc1_ack_dd_odd_hi            = 1'b0;
  wq_ack_dd_odd_hi             = 1'b0;
  aux_ack_dd_odd_hi            = 1'b0;
  
  // We dont give the dd bank to DC1 when there was a DC2 instruction stuck
  // in DC2. This prevents the DC1 instruction from accessing the DD bank
  // that may have its output holding the data for the DC2 instruction
  //
  
  // (1) when there is a dc1 dc2 bank common, WQ can wait
  //   

  // hi arbiter
  //
  casez ({dmu_req_dd,
          dc2_req_dd_odd_hi,
          dc1_req_dd_odd_hi,
          wq_req_dd_odd_hi,
          aux_req_dd_odd_hi})
  
  5'b1????: dmu_ack_dd_odd_hi = !dd_bank_busy_hi_r[1];
  5'b01???: dc2_ack_dd_odd_hi = !dd_bank_busy_hi_r[1] & (~dmu_has_dc_r);
  5'b001??: dc1_ack_dd_odd_hi = !dd_bank_busy_hi_r[1] & (~dc2_stuck_r) & (~dmu_has_dc_r) & (~dc2_dc3_bank_common_match[3]);
  5'b0001?: wq_ack_dd_odd_hi  = !dd_bank_busy_hi_r[1] & (~dmu_has_dc_r)& (~dc1_dc2_bank_common_r[3]);
  5'b00001: aux_ack_dd_odd_hi = !dd_bank_busy_hi_r[1];
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
  default:
    ;
// spyglass enable_block W193   
  endcase

end

///////////////////////////////////////////////////////////////////////////////
//                                                                           
// set conflicts          
//                                                                           
//////////////////////////////////////////////////////////////////////////////
assign dmu_set_addr = dmu_line_addr[`npuarc_DC_SET_RANGE];


always @*
begin : set_conflict_detection_PROC

  dc1_target_dc     =   (dc1_target == `npuarc_DMP_TARGET_DC); 
  
  dc1_ld_target_dc  =  ( x1_load_r 
                        | ((|dc1_rmw) & x1_store_r)
                       )
                     & x1_pass                           
                     & (~dc1_cache_byp);                  
  
  dc2_target_dc    =   (x2_load_r | x2_store_r)          
                     & (dc2_target_r == `npuarc_DMP_TARGET_DC); 
  
  dc2_ld_target_dc  =  ( x2_load_r
                        | ((|dc2_rmw) & x2_store_r)
                       )
                     & (dc2_target_r == `npuarc_DMP_TARGET_DC);
  
  dc3_target_dc    =   (x3_load_r | x3_store_r)          
                     & (dc3_target_r == `npuarc_DMP_TARGET_DC);
                     
  dc3_target_dccm  =   (x3_load_r | x3_store_r)          
                     & (dc3_target_r == `npuarc_DMP_TARGET_DCCM);
  
  dc3_ld_target_dc =   ( x3_load_r
                        | ((|dc3_rmw_r) & x3_store_r)
                       )
                     & (dc3_target_r == `npuarc_DMP_TARGET_DC)
                     & (~dc3_dc_poisoned); 
                     
  dc3_st_target_dc =    x3_store_r        
                     & (dc3_target_r == `npuarc_DMP_TARGET_DC);
    
  dc4_ld_target_dc =   ( ca_load_r
                        | ((|dc4_rmw_r) & ca_store_r)
                       )
                     & (dc4_target_r == `npuarc_DMP_TARGET_DC);
  dc4_target_dc    =   (ca_load_r | ca_store_r)
                     & (dc4_target_r == `npuarc_DMP_TARGET_DC);
  
  dc4_st_target_dc =   ca_store_r
                     & (dc4_target_r == `npuarc_DMP_TARGET_DC);
  
  dc3_set_match0 = 
       (x3_mem_addr0_r[`npuarc_DC_SET_RANGE]      == dmu_set_addr[`npuarc_DC_SET_RANGE]);
  
  dc3_set_match1 = 
           (dc3_mem_addr1_r[`npuarc_DC_SET_RANGE] == dmu_set_addr[`npuarc_DC_SET_RANGE]) 
         & dc3_dt_line_cross_r;
  
  dc3_set_match = dc3_set_match0 | dc3_set_match1;
  
  dc4_set_match0 = 
      (ca_mem_addr0_r[`npuarc_DC_SET_RANGE]       == dmu_set_addr[`npuarc_DC_SET_RANGE]);
  
  dc4_set_match1 = 
           (dc4_mem_addr1_r[`npuarc_DC_SET_RANGE] == dmu_set_addr[`npuarc_DC_SET_RANGE]) 
         & dc4_dt_line_cross_r;
  
  dc4_set_match = dc4_set_match0 | dc4_set_match1;
  
  
  dc3_dmu_set_conflict =   dc3_target_dc  
                         & dc3_set_match
                         & (~dc3_mq_addr_match);
  
  dc4_dmu_set_conflict =   dc4_target_dc
                         & dc4_set_match
                         & (~dc4_mq_addr_match);
end

/////////////////////////////////////////////////////////////////////////////
//  Allowing DMU to access the cache
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc_pipe_busy_PROC
  // Prevents the DMU from coming in when there is something valid at X2
  // and the pipe is not stalled
  //
  dc_pipe_busy = (x2_load_r | x2_store_r) & dc_pipe_enable_r;
end

parameter DMU_ACK_DEFAULT = 1'b0;
parameter DMU_ACK_WAIT_WQ = 1'b1;

always @*
begin : dmu_ack_PROC
  
  dmu_ack_ok        = 1'b0;
  dmu_dc_stall_nxt  = dmu_dc_stall_r;
  dmu_ack_state_nxt = dmu_ack_state_r;
  
  case (dmu_ack_state_r)
  DMU_ACK_DEFAULT:
  begin
    casez ({dmu_dc_start, dmu_dc_read, dc3_stuck, dc3_dc_poisoned})          
    4'b1100:                                                              
    begin                                                                
      // Copy back with pipe flowing and no poisoning. The DMU gets
      // access to the data cache when
      // (1). There is no set match in DC3
      // (2). There is no set match in DC4
      // (3). There is no set match the WQ
      //
      dmu_ack_ok        = ~(  dc3_dmu_set_conflict // (1)
                            | dc4_dmu_set_conflict // (2)
                            | wq_dmu_set_conflict  // (3)  
                            | aux_ecc_scrub_in_progress_r // in case of ecc scrub
                           );       
      dmu_ack_state_nxt = (aux_ecc_scrub_in_progress_r) 
                        ? DMU_ACK_WAIT_WQ 
                        : dmu_ack_state_r;                   
    
      // Prevent a potential livelock created when  load/store instructions 
      // conflicting with the dmu keep coming, preventing the dmu to access 
      // the cache
      //
      dmu_dc_stall_nxt  =  dc3_dmu_set_conflict
                         | dc4_dmu_set_conflict
                         | wq_dmu_set_conflict;
      
      if (  wq_dmu_set_conflict
          & (~dc3_dmu_set_conflict)
          & (~dc4_dmu_set_conflict)
         )
      begin
        dmu_dc_stall_nxt  = 1'b1;
        dmu_ack_state_nxt = DMU_ACK_WAIT_WQ; 
      end
    end 
    
    4'b1110:
    begin
      //
      // The instruction is stuck in X3
      // The X3 address (miss) is matching with DC4 and MQ. then do not poison
      // the instruction.
      //
      dmu_ack_ok        = ~(  dc3_dmu_set_conflict // (1)
                            | dc4_dmu_set_conflict // (2)      
                            | wq_dmu_set_conflict  // (3)
                            | aux_ecc_scrub_in_progress_r // in case of ecc scrub
                           );
  
      dmu_dc_stall_nxt  =  dc3_dmu_set_conflict
                         | dc4_dmu_set_conflict 
                         | wq_dmu_set_conflict;
    
      dmu_ack_state_nxt = (aux_ecc_scrub_in_progress_r) ? DMU_ACK_WAIT_WQ : dmu_ack_state_r;
     
      if (  wq_dmu_set_conflict
          & (~dc3_dmu_set_conflict)
          & (~dc4_dmu_set_conflict)
         )
      begin
        dmu_dc_stall_nxt  = 1'b1;
        dmu_ack_state_nxt = DMU_ACK_WAIT_WQ;
      end   
    end  

  
    4'b11?1:                                                              
    begin                                                                
      // Copy back with dc3 poisoned. Should not give ack straight away  
      //                                                                 
      dmu_ack_ok        = ~(  dc4_dmu_set_conflict // (1)
                            | wq_dmu_set_conflict  // (3)
                            | aux_ecc_scrub_in_progress_r // in case of ecc scrub
                           );

      dmu_dc_stall_nxt  =  dc4_dmu_set_conflict
                         | wq_dmu_set_conflict;
   
      dmu_ack_state_nxt = (aux_ecc_scrub_in_progress_r) 
                        ? DMU_ACK_WAIT_WQ 
                        : dmu_ack_state_r;

      if (  wq_dmu_set_conflict
          & (~dc4_dmu_set_conflict)
         )
      begin
        dmu_dc_stall_nxt  = 1'b1;
        dmu_ack_state_nxt = DMU_ACK_WAIT_WQ;
      end 

    end                                                                  
                                                                         
    4'b1000:
    begin
      // Refill. Not stuck, not poisoned                                      
      //                                                                 
      dmu_ack_ok        = dmu_dc_ready
                        & ~(   dc3_addr_match0
                             | dc3_addr_match1      
                             | dc4_addr_match0 
                             | dc4_addr_match1 
                             | aux_ecc_scrub_in_progress_r // in case of ecc scrub
                            )
                            ;       
      dmu_ack_state_nxt = (aux_ecc_scrub_in_progress_r) 
                        ? DMU_ACK_WAIT_WQ 
                        : dmu_ack_state_r;                   
    
      // Prevent a potential livelock created when  load/store instructions 
      // conflicting with the dmu keep coming, preventing the dmu to access 
      // the cache
      //
      dmu_dc_stall_nxt  =  dc3_addr_match0
                         | dc3_addr_match1
                         | dc4_addr_match0
                         | dc4_addr_match1;
      
    end
    
    4'b10?1:
    begin
      // Refill. Poisoned                                     
      //                                                                 
      dmu_ack_ok        = dmu_dc_ready
                        & ~(  dc4_addr_match0 
                            | dc4_addr_match1 
                            | aux_ecc_scrub_in_progress_r // in case of ecc scrub
                           );       
      dmu_ack_state_nxt = (aux_ecc_scrub_in_progress_r) 
                        ? DMU_ACK_WAIT_WQ 
                        : dmu_ack_state_r;                   
    
      // Prevent a potential livelock created when  load/store instructions 
      // conflicting with the dmu keep coming, preventing the dmu to access 
      // the cache
      //
      dmu_dc_stall_nxt  =  dc4_addr_match0
                         | dc4_addr_match1;
      
    end
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept    
    default:     
      ;
// spyglass enable_block W193                                                           
    endcase                                                              
  end

  default: // DMU_ACK_WAIT_WQ
  begin
    // Copy back shouldnt come in if there is a dc4/wq conflict. Refill is ok
    //
    if (  (wq_dc_entry == 1'b0) 
        | (dmu_dc_read == 1'b0)) 
    begin
      dmu_dc_stall_nxt  = 1'b0;
      dmu_ack_ok        = dmu_dc_read
                        ? ~aux_ecc_scrub_in_progress_r                      // CB
                        : (dmu_dc_ready & (~aux_ecc_scrub_in_progress_r));  // RF
                        
      dmu_ack_state_nxt = (aux_ecc_scrub_in_progress_r) 
                        ? DMU_ACK_WAIT_WQ 
                        : DMU_ACK_DEFAULT;
    end
  end
  endcase
end

/////////////////////////////////////////////////////////////////////////////
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc23_dccm_poisoned_PROC
  dc3_dccm_poisoned =  dc3_dc_poisoned_prel_r;
end


/////////////////////////////////////////////////////////////////////////////
//  Allowing x1 store uop to proceed
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_uop_stall_PROC 
  dc1_uop_stall = ~dmu_empty
                 | (dc3_target_dc & (~x3_uop_inst_r))
                 | (dc4_target_dc & (~ca_uop_inst_r))
                 ;
end

/////////////////////////////////////////////////////////////////////////////
//  Allowing x1 instructions to proceed
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_busy_stall_PROC 
  aux_busy_stall =  aux_busy 
                  ;
end
/////////////////////////////////////////////////////////////////////////////
//  Allowing AUX to access the cache
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc_pipe_empty_PROC
  // Dont let the AUX to come through when we have LD/ST instructions in flight
  // The AUX needs to access the dt and ds memories. When there are stalls, the
  // output of these memories needs to remain stable
  //
  dc_pipe_empty =   ~dc2_target_dc
                  & (~dc3_target_dc)
                  & (~dc4_target_dc);
end

/////////////////////////////////////////////////////////////////////////////
//                                                                           
//  Poisoning of instrutions       
//                                                                           
//////////////////////////////////////////////////////////////////////////////

wire dc3_evict_addr_hit;

// When there is a hit in the evict address, the DC3 ld/st is poisoned
// so that when it comes back, it will see a miss in the cache and it will
// go to LSMQ. 
//
assign dc3_evict_addr_hit =  dmu_evict_hit;

// Collect all sources of dc3 poisoning:
// DMU poisoning (1) 
// Hit in the  eviction address (2)
//
assign dc3_dc_poisoned =  dc3_dc_poisoned_prel_r  // (1)
                        | dc3_evict_addr_hit;     // (2)


assign dc3_stuck =    (   dc3_target_dc 
                       | dc3_target_dccm
                       )  
                       & (~(x3_pass & ca_enable))
                       ;

always @*
begin : dc3_poisoning_PROC
  // Set the DC3 poisoning bit when the DMU wants to start the refill/eviction
  // process but there is a DC3 instruction that can not proceed because CA
  // is not enabled or there is a x3 stall. 
  //
  // Assume, there can be an address A that misses in cache and got stuck in X3,
  // there might not be a copy back happening and address A is in Miss Queue,
  // We need to poison the x3.
  //
  // (1) When there is a dc3 addr match with top of MQ and there is no DC4 addr match
  //     then poison the DC3 in order to avoid the live lock
  //
  dc3_set_poisoned   = (   dmu_dc_start 
                          & (  dmu_poison_stuck
                             | (~lq_empty_r)
                             | (~wq_empty)
                             | x3_load_r
                             | ((|dc3_rmw_r) & x3_store_r)
                             | x3_locked_r
                             )
                          & (~(dc3_mq_addr_match & dc4_mq_addr_match)) // (1) 
                          & dc3_stuck)
                      | dmu_evict_hit
                      ; 
   
  
  dc3_reset_poisoned = wa_restart_r | wa_replay_r;
  
end



/////////////////////////////////////////////////////////////////////////////
//                                                                           
// Data Status arbiter            
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : data_status_arbiter_PROC
  // Arbitration for port1
  //
  dmu_ack_ds     = 1'b0;
  aux_ack_ds     = 1'b0;
   
  casez ({dmu_req_ds,
          aux_req_ds})
  2'b1?:  dmu_ack_ds = 1'b1;
  2'b01:  aux_ack_ds = 1'b1;
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
  default:
    ;
// spyglass enable_block W193   
  endcase
  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Status flops (Lock, Dirty, LRU) 
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc_status_PROC
  // Port0 is for CA/WA (only write. Unaligned accesses)
  //
  dc_status0_write_even   =   dc4_target_dc 
                            & ( | dc4_hit_even_way_hot_r)
                            & ca_pass;
  dc_status0_even_wem     = {1'b0,                                // lock
                             ca_store_r,                          // dirty
                             1'b1};                               // lru
  dc_status0_even_way_hot = dc4_hit_even_way_hot_r;
  dc_status0_even_dirty   = 1'b1;
  dc_status0_even_lru     = dc4_hit_even_way_hot_r[0];

  dc_status0_write_odd    =   dc4_target_dc 
                            & ( | dc4_hit_odd_way_hot_r)
                            & ca_pass;
  dc_status0_odd_wem      = {1'b0,                               // lock
                             ca_store_r,                          // dirty
                             1'b1};                               // lru
  dc_status0_odd_way_hot  = dc4_hit_odd_way_hot_r;
  dc_status0_odd_dirty    = 1'b1;
  dc_status0_odd_lru      = dc4_hit_odd_way_hot_r[0];
  
  if (ca_mem_addr0_r[`npuarc_DC_TAG_BANK_ID] == 1'b0)
  begin
    dc_status0_even_addr  = ca_mem_addr0_r[`npuarc_DC_IDX_RANGE];
    dc_status0_odd_addr   = dc4_mem_addr1_r[`npuarc_DC_IDX_RANGE];
  end
  else
  begin
    dc_status0_even_addr  = dc4_mem_addr1_r[`npuarc_DC_IDX_RANGE]; 
    dc_status0_odd_addr   = ca_mem_addr0_r[`npuarc_DC_IDX_RANGE]; 
  end
  
  // Port1 (read, write. Aligned accesses only). Shared between DMU and AUX
  //
  dc_status1_read      = 1'b0;
  dc_status1_write     = 1'b0;
  dc_status1_addr      = dmu_ds_addr;
  dc_status1_odd       = dmu_ds_odd_sel;
  dc_status1_wem       = dmu_ds_wem;        
  dc_status1_way_hot   = dmu_ds_way_hot;
  dc_status1_lock      = dmu_ds_lock;
  dc_status1_dirty     = dmu_ds_dirty;
  dc_status1_lru       = dmu_ds_lru;     
  
  if (dmu_ack_ds)
  begin
    dc_status1_read    = ~dmu_ds_we;
    dc_status1_write   = dmu_ds_we;
    dc_status1_addr    = dmu_ds_addr;
    dc_status1_odd     = dmu_ds_odd_sel;
    dc_status1_wem     = dmu_ds_wem;        
    dc_status1_way_hot = dmu_ds_way_hot;
    dc_status1_lock    = dmu_ds_lock;
    dc_status1_dirty   = dmu_ds_dirty;
    dc_status1_lru     = dmu_ds_lru;     
  end
  else if (aux_ack_ds)
  begin
    dc_status1_read    = ~aux_ds_we;
    dc_status1_write   = aux_ds_we;
    dc_status1_addr    = aux_ds_addr;
    dc_status1_odd     = aux_ds_odd_sel;
    dc_status1_wem     = aux_ds_wem;    
    dc_status1_way_hot = aux_ds_way_hot;
    dc_status1_lock    = aux_ds_lock;
    dc_status1_dirty   = aux_ds_dirty;
    dc_status1_lru     = aux_ds_lru; 
  end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asynchronous block defining DC1 bank conflict 
//                                                                           
//////////////////////////////////////////////////////////////////////////////
reg       dc1_dd_conflict;
reg       dc1_dt_conflict;
reg       dc1_dc_dccm_bank_conflict;
reg       dc1_bank_conflict;
reg       dc1_wq_conflict;
reg [3:0] dc1_ack_dd_qual; // qualified ack;

always @*
begin : dc1_bank_conflict_PROC
  // DC1 doesn't get access to DD
  //
  dc1_dd_conflict   = (   {dc1_req_dd_odd_hi,  dc1_req_dd_odd_lo,
                           dc1_req_dd_even_hi, dc1_req_dd_even_lo}
                       != {dc1_ack_dd_odd_hi,  dc1_ack_dd_odd_lo,
                           dc1_ack_dd_even_hi, dc1_ack_dd_even_lo});
  
  // DC1 doesn't get access to DT
  //
  dc1_dt_conflict   = (   {dc1_req_dt_odd,  dc1_req_dt_even}
                       != {dc1_ack_dt_odd,  dc1_ack_dt_even});
  
  // DC1 accessing banks that have been given to the write queue the previous
  // cycle
  //
  dc1_wq_conflict = (dc1_bank_req_mask[0] & dc_data_even_cs_lo & dc_data_even_we_lo)
                  | (dc1_bank_req_mask[1] & dc_data_even_cs_hi & dc_data_even_we_hi)
                  | (dc1_bank_req_mask[2] & dc_data_odd_cs_lo  & dc_data_odd_we_lo)
                  | (dc1_bank_req_mask[3] & dc_data_odd_cs_hi  & dc_data_odd_we_hi)
                  ;
  
  // We only fire partial acked memory banks when the DC1 load doesn't 
  // experience a bank conflict with a bank that has been just written
  //
  dc1_ack_dd_qual = {(dc1_ack_dd_odd_hi  & (~dc1_wq_conflict)),
                     (dc1_ack_dd_odd_lo  & (~dc1_wq_conflict)),
                     (dc1_ack_dd_even_hi & (~dc1_wq_conflict)),
                     (dc1_ack_dd_even_lo & (~dc1_wq_conflict))};
  
  // The DC1 instruction needs to be stalled in DC2 if it doesnt access to 
  // either DD or DT memories
  //
  dc1_bank_conflict =   dc1_dd_conflict
                      | dc1_dt_conflict
                      ;
  
  dc1_dc_dccm_bank_conflict = (   dc1_bank_conflict
                                | dc1_dccm_bank_conflict
                               )
                             ;  
end

reg                 dc3_data_mem_valid_cg0;

always @*
begin : dc3_data_mem_valid_cg0_PROC
  //
  //
  // DC3 Data clock gates
  //
  dc3_data_mem_valid_cg0      = (dc2_target_dc & x2_pass)
                              | wa_restart_r
                              ;      
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Bank conflict optmization
//                                                                           
//////////////////////////////////////////////////////////////////////////////
reg [3:0]           dc2_dc3_bank_common;
reg [3:0]           dc2_dc3_bank_match;
reg [3:0]           dc2_ignore_bank_vector;
reg                 dc2_ignore_bank_conflict;
reg [3:0]           dc2_bank_sel_not_fired;
//reg [3:0]           dc2_dc3_bank_common_match;              

reg [3:0]           dc3_bank_addr_cg0;
reg [`npuarc_DC_ADR_RANGE] dc3_bank0_addr_r;
reg [`npuarc_DC_ADR_RANGE] dc3_bank1_addr_r;
reg [`npuarc_DC_ADR_RANGE] dc3_bank2_addr_r;
reg [`npuarc_DC_ADR_RANGE] dc3_bank3_addr_r;

reg [`npuarc_DC_ADR_RANGE] dc3_addr0_nxt;
reg [`npuarc_DC_ADR_RANGE] dc3_addr1_nxt;

reg [3:0]           dc3_data_bank_valid_cg0;    
reg [3:0]           dc3_data_bank_valid_nxt;    
reg [3:0]           dc3_data_bank_valid_r;


wire [3:0]          dc2_active_cs_nxt;
reg  [3:0]          dc2_active_cs_r;
wire [3:0]          dc3_active_we_nxt;


assign dc2_active_cs_nxt = {(dc_data_odd_cs_hi_nxt  & (~dc_data_odd_we_hi_nxt)),
                            (dc_data_odd_cs_lo_nxt  & (~dc_data_odd_we_lo_nxt)),
                            (dc_data_even_cs_hi_nxt & (~dc_data_even_we_hi_nxt)) ,
                            (dc_data_even_cs_lo_nxt & (~dc_data_even_we_lo_nxt))};

assign dc3_active_we_nxt  = {(dc_data_odd_cs_hi_r  & dc_data_odd_we_hi_r),
                             (dc_data_odd_cs_lo_r  & dc_data_odd_we_lo_r),
                             (dc_data_even_cs_hi_r & dc_data_even_we_hi_r) ,
                             (dc_data_even_cs_lo_r & dc_data_even_we_lo_r)};
always @*
begin : dc3_addr0_nxt_PROC
  //
  //
  dc3_addr0_nxt                     = dc2_dd_addr0[`npuarc_DC_ADR_RANGE];
  dc3_addr0_nxt[`npuarc_DC_PRED_BIT_RANGE] = dc2_pred0; 

  dc3_addr1_nxt                     = dc2_dd_addr1[`npuarc_DC_ADR_RANGE];  
  dc3_addr1_nxt[`npuarc_DC_PRED_BIT_RANGE] = dc2_pred1;
end

always @*
begin : dc2_bank_conflict_opt_PROC
  // Compare dd bank addresses between dc2 and dc3. Back to back LD instructions
  // using the same memory bank(s) address dont need to stall, as the memory
  // output of the first load can be re-used for the second load.
  //
 
  // Clock gates for enabling the update of the dc3 bank addr registers
  //
  dc3_bank_addr_cg0[0] = dc2_target_dc & dc2_data_bank_sel_r[0] & x2_pass;
  dc3_bank_addr_cg0[1] = dc2_target_dc & dc2_data_bank_sel_r[1] & x2_pass;
  dc3_bank_addr_cg0[2] = dc2_target_dc & dc2_data_bank_sel_r[2] & x2_pass;
  dc3_bank_addr_cg0[3] = dc2_target_dc & dc2_data_bank_sel_r[3] & x2_pass;

  // Clock gates: enable when the memory banks are accessed
  // (1) The access can be due to WQ or DMU
  // (2) The access can be due to DC2
  //
  dc3_data_bank_valid_cg0[0] = (dc2_ld_target_dc & x2_pass)
                             | ( ~dc2_ld_target_dc)
                             | dc3_active_we_nxt[0]    
                             | wa_restart_r
                             ;     
  dc3_data_bank_valid_cg0[1] = (dc2_ld_target_dc & x2_pass)
                             | ( ~dc2_ld_target_dc)
                             | dc3_active_we_nxt[1]    
                             | wa_restart_r
                             ;     
  dc3_data_bank_valid_cg0[2] = (dc2_ld_target_dc & x2_pass)
                             | ( ~dc2_ld_target_dc)
                             | dc3_active_we_nxt[2]    
                             | wa_restart_r
                             ;     
  dc3_data_bank_valid_cg0[3] = (dc2_ld_target_dc & x2_pass)
                             | ( ~dc2_ld_target_dc)
                             | dc3_active_we_nxt[3]    
                             | wa_restart_r
                             ;     

  // The dc3_data_bank_valid_r registers record  the fact that a bank was last 
  // accessed by a read operation and therefore the bank output can be re-used
  //

  dc3_data_bank_valid_nxt = dc3_data_bank_valid_r;

  if (dc3_data_bank_valid_cg0[0])
  begin 
    dc3_data_bank_valid_nxt[0] = 1'b1
                               & dc2_data_bank_sel_r[0]
                               & (~dc2_pref_r)     
                               & dc2_ld_target_dc
                               & (~dc3_active_we_nxt[0])
                               & (~dc2_kill)     
                               ; 
  end
 
  if (dc3_data_bank_valid_cg0[1])
  begin 
    dc3_data_bank_valid_nxt[1] = 1'b1
                               & dc2_data_bank_sel_r[1] 
                               & (~dc2_pref_r)     
                               & dc2_ld_target_dc 
                               & (~dc3_active_we_nxt[1])
                               & (~dc2_kill)     
                               ;
  end
 
  if (dc3_data_bank_valid_cg0[2])
  begin 
    dc3_data_bank_valid_nxt[2] = 1'b1
                               & dc2_data_bank_sel_r[2] 
                               & (~dc2_pref_r)     
                               & dc2_ld_target_dc
                               & (~dc3_active_we_nxt[2])
                               & (~dc2_kill)     
                               ;
  end

  if (dc3_data_bank_valid_cg0[3])
  begin 
    dc3_data_bank_valid_nxt[3] = 1'b1
                               & dc2_data_bank_sel_r[3] 
                               & (~dc2_pref_r)     
                               & dc2_ld_target_dc  
                               & (~dc3_active_we_nxt[3])
                               & (~dc2_kill)     
                               ;
  end
  // In case of aliasing configurations, use the aliasing address bit
  //
  dc2_dd_addr0_qual                     = dc2_dd_addr0;
  dc2_dd_addr0_qual[`npuarc_DC_PRED_BIT_RANGE] = dc2_pred0;

  dc2_dd_addr1_qual                     = dc2_dd_addr1;
  dc2_dd_addr1_qual[`npuarc_DC_PRED_BIT_RANGE] = dc2_pred1;

  // Set of four comparators.
  //
  dc2_dc3_bank_match[0]  = dc2_dd_addr0_qual  == dc3_bank0_addr_r;
  dc2_dc3_bank_match[1]  = dc2_dd_addr0_qual  == dc3_bank1_addr_r;
  dc2_dc3_bank_match[2]  = dc2_dd_addr1_qual  == dc3_bank2_addr_r;
  dc2_dc3_bank_match[3]  = dc2_dd_addr1_qual  == dc3_bank3_addr_r;
  
  // Set of four bank masks. The dc3_data_bank_valid_r registers record 
  // the fact that a bank was last accessed by a read operation and therefore
  // the bank output can be re-used
  //
  dc2_dc3_bank_common[0] = dc2_data_bank_sel_r[0] & dc3_data_bank_valid_r[0] & (~dc3_mispred);
  dc2_dc3_bank_common[1] = dc2_data_bank_sel_r[1] & dc3_data_bank_valid_r[1] & (~dc3_mispred);
  dc2_dc3_bank_common[2] = dc2_data_bank_sel_r[2] & dc3_data_bank_valid_r[2] & (~dc3_mispred);
  dc2_dc3_bank_common[3] = dc2_data_bank_sel_r[3] & dc3_data_bank_valid_r[3] & (~dc3_mispred);

  // This expression records banks needed by the DC2 instruction that 
  // have not been fired/activated. We can't ignore a bank conflict stall 
  // if there is any bank that is not re-used from a previous load *and* 
  // has not been fired.
  //
  dc2_bank_sel_not_fired = (dc2_data_bank_sel_r ^ (dc2_data_bank_sel_r & dc2_active_cs_r)); 

  
  // Conditions to ignore the DC2 bank request: When DC1 and DC2 have bank addr match
  // then DC2 should not make a request in DC2
  //
  dc2_dc3_bank_common_match = (dc2_dc3_bank_common & dc2_dc3_bank_match);
  
  // Conditions to ignore bank conflict: memory bank outputs is valid (i.e.:
  // memory read) in DC3 and the DC2 load instruction is accessing the same
  // memory bank address
  //
  dc2_ignore_bank_vector = (dc2_dc3_bank_common_match)
                         | ((~dc2_dc3_bank_common) & (~dc2_bank_sel_not_fired))
                         ;

  dc2_ignore_bank_conflict = (& dc2_ignore_bank_vector) & (|dc2_dc3_bank_common_match);
  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// DC2 conflict stall
//                                                                           
//////////////////////////////////////////////////////////////////////////////
wire      dc2_bank_conflict_nxt;

reg       dc2_cft_state_cg0;
reg [2:0] dc2_cft_state_r;
reg [2:0] dc2_cft_state_nxt;

reg [3:0] dc2_keep_bank_busy;
reg       dc2_full_ack_dd_prev_r;

wire      dc2_lost_ownership;

assign dc2_lost_ownership = dc2_lost_ownership_to_dmu | dc2_lost_ownership_to_wq;

assign dc2_bank_conflict_nxt =   dc1_bank_conflict
                               & x2_enable;


parameter DC2_CFT_DEFAULT                = 3'b000;
parameter DC2_CFT_WAIT_DMU               = 3'b001;
parameter DC2_CFT_WAIT_WQ                = 3'b010;
parameter DC2_CFT_DD_ACCESS              = 3'b011;
parameter DC2_CFT_DD_DT_ACCESS           = 3'b100;


always @*
begin : dc2_cft_stall_PROC
  
  dc2_lost_ownership_to_dmu  =   (dmu_dc_start  | dmu_has_dc_r)
                               & (dc2_target_dc);    

  dc2_lost_ownership_to_wq   =   (  wq_dc_entry
                                  | (dc4_st_target_dc & ca_pass)
                                 )
                               & dc2_ld_target_dc
                               & (  (~dmu_empty) 
                                  | (~lq_empty_r)
                                  | (dc3_stall_r & dc3_partial_or_multi_conflict)   // when dc3 is stalling
                                  | dc4_stall_r                                     // when dc4 is stalling
                                 )   
                               & dc2_stuck;
  
  
  dc2_cft_stall              = 1'b0;
  
  dc2_req_dd_even_lo         = 1'b0;
  dc2_req_dd_even_hi         = 1'b0;  
  dc2_req_dd_odd_lo          = 1'b0; 
  dc2_req_dd_odd_hi          = 1'b0; 
  
  dc2_keep_bank_busy         = 4'h0;
  
  dc2_req_dt_even            = 1'b0;
  dc2_req_dt_odd             = 1'b0;

  dc_pct_dcbc                = 1'b0; 

  dc2_cft_state_cg0          = 1'b1;            
  dc2_cft_state_nxt          = dc2_cft_state_r; 
  
  case (dc2_cft_state_r)
  DC2_CFT_DEFAULT:
  begin
    dc2_cft_state_cg0        =   dc2_lost_ownership_to_dmu
                               | dc2_stuck
                               | dc2_bank_conflict_nxt
                               ;
    
    dc2_cft_stall            = dc2_lost_ownership_to_dmu;
   
    if (dc2_lost_ownership_to_wq)
    begin
      //  WQ accessing DD during a DC2 stall.
      //
      dc2_cft_state_nxt = DC2_CFT_WAIT_WQ;
    end   
    else if (dc2_lost_ownership_to_dmu)
    begin
      // The DMU comes in when we have a valid load/store in DC2.
      //
      dc2_cft_state_nxt = DC2_CFT_WAIT_DMU;
    end
    else if (  dc2_bank_conflict_nxt
             & dc1_target_dc)
    begin
      // The DC1 instruction didnt get access  to dd/dt when moving to DC2
      // 
      dc2_cft_state_nxt =    dc1_dt_conflict 
                          ?  DC2_CFT_DD_DT_ACCESS
                          :  DC2_CFT_DD_ACCESS; 
 
    end
  end
  
  DC2_CFT_WAIT_WQ:
  begin
    dc2_cft_stall       = 1'b1;  
    
    // when this is set, this will make sure that WQ gets the ACk and it completes
    //
    dc2_lost_ownership_to_wq = 1'b1;
   
  if (dc2_kill)
    begin
      dc2_cft_state_nxt = DC2_CFT_DEFAULT;
    end
    else if (~wq_dc_entry)
    begin
      dc2_cft_state_nxt = dc2_lost_ownership_to_dmu ? DC2_CFT_WAIT_DMU : DC2_CFT_DD_DT_ACCESS;
    end
  end
  
  DC2_CFT_WAIT_DMU:
  begin
    dc2_cft_stall       = 1'b1;
    
    if (dc2_kill)
    begin
      dc2_cft_state_nxt = DC2_CFT_DEFAULT;
    end
    else if (  (dmu_dc_done | (~dmu_has_dc_r))
             & (~dmu_dc_start))
    begin
      dc2_cft_state_nxt = DC2_CFT_DD_DT_ACCESS;
    end
  end
  
  DC2_CFT_DD_ACCESS:
  begin
    dc2_cft_stall       = (~dc2_ignore_bank_conflict)
                        | dc2_lost_ownership_to_dmu
                        ; //1'b1;  
   
   dc_pct_dcbc          = ~dc2_ignore_bank_conflict;

    dc2_req_dd_even_lo  = dc2_bank_not_ack_r[0] & (~dc2_dc3_bank_common_match[0]);  
    dc2_req_dd_even_hi  = dc2_bank_not_ack_r[1] & (~dc2_dc3_bank_common_match[1]);  
    dc2_req_dd_odd_lo   = dc2_bank_not_ack_r[2] & (~dc2_dc3_bank_common_match[2]);  
    dc2_req_dd_odd_hi   = dc2_bank_not_ack_r[3] & (~dc2_dc3_bank_common_match[3]);  

    // (1) In case of DC1 and DC2 have a bank addr common, then DC1 would not have requested
    //     for the bank that had it common with DC2, hence, in order to prevent the WQ from stealing
    //     the common bank (DC1-DC2). DC2 should keep that bank as well busy
    //
    
    // Only the banks that were acked by the DC1 arbiter are kept busy
    //
    dc2_keep_bank_busy  = {dc2_req_dd_odd_hi_r,
                           dc2_req_dd_odd_lo_r,
                           dc2_req_dd_even_hi_r,
                           dc2_req_dd_even_lo_r}
                         & (  (~dc2_bank_not_ack_r)
                            | dc2_dc3_bank_common_match)   // (1)
                         ;

    if (  dmu_dc_start
        | (dmu_has_dc_r & (~dmu_dc_done)))
    begin
      dc2_keep_bank_busy = 4'h0;
      dc2_cft_state_nxt  = DC2_CFT_WAIT_DMU;
      dc_pct_dcbc        = 1'b0; 
    end
    else if (dc2_lost_ownership_to_wq)
    begin
      dc2_keep_bank_busy = 4'h0;
      dc2_cft_state_nxt  = DC2_CFT_WAIT_WQ;
      dc_pct_dcbc        = 1'b0; 
    end
    else if (  dc1_bank_conflict
             & dc1_target_dc
             & x1_pass)
    begin
      // stay here
      //
      dc2_keep_bank_busy = 4'h0;  


      // The DC1 instruction didnt get access  to dd/dt when moving to DC2
      // 
      dc2_cft_state_nxt =    dc1_dt_conflict
                        ?  DC2_CFT_DD_DT_ACCESS
                        :  DC2_CFT_DD_ACCESS; 
 
//      dc2_cft_state_nxt  = DC2_CFT_DD_ACCESS;
    end
    else if (  (  dc3_enable 
//                & (~x2_exu_stall)
                & ( dc2_full_ack_dd 
                  | dc2_ignore_bank_conflict
                  | dc2_full_ack_dd_prev_r)  // this prevents re-access
                                             // when DC2 gets held-up
                )
             | (~dc2_target_dc)
             | dc2_kill
            )
    begin
      // After X3 is enabled, and after receiving dc2_full_ack, keep requesting the all bank
      // so that dc1 or WQ does not steal the banks during transistion
      //
      dc2_keep_bank_busy =  {dc2_req_dd_odd_hi_r,
                             dc2_req_dd_odd_lo_r,
                             dc2_req_dd_even_hi_r,
                             dc2_req_dd_even_lo_r};

      dc2_cft_state_nxt  = DC2_CFT_DEFAULT;
    end
  end
  
  DC2_CFT_DD_DT_ACCESS:
  begin
    dc2_cft_stall       = 1'b1; 
    
    dc2_req_dd_even_lo  = dc2_req_dd_even_lo_r;
    dc2_req_dd_even_hi  = dc2_req_dd_even_hi_r;  
    dc2_req_dd_odd_lo   = dc2_req_dd_odd_lo_r;  
    dc2_req_dd_odd_hi   = dc2_req_dd_odd_hi_r;  
  
    dc2_req_dt_even     = dc2_req_dt_even_r;
    dc2_req_dt_odd      = dc2_req_dt_odd_r;
    
    if (  dmu_dc_start
        | (dmu_has_dc_r & (~dmu_dc_done)))
    begin
      dc2_cft_state_nxt = DC2_CFT_WAIT_DMU;
    end
    else if (dc2_lost_ownership_to_wq)
    begin
      dc2_cft_state_nxt = DC2_CFT_WAIT_WQ;
    end
    else if (  (  dc3_enable 
                & (~x2_exu_stall)
                & dc2_full_ack_dd
                & dc2_full_ack_dt
                )
             | (dc2_target_r != `npuarc_DMP_TARGET_DC)
             | dc2_kill
            )
    begin
      // After X3 is enabled, we keep requesting the bank until
      // we get the dc2_full_ack_dd
      //
      dc2_cft_state_nxt = DC2_CFT_DEFAULT;
    end
  end
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept  
  default:;
// spyglass enable_block W193   
  endcase
  
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          
// DD full ack
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dd_full_ack_PROC
  // Handy vectors (req)
  //
  dc1_bank_req_mask     = {(dc1_data_bank_sel_hi[1] & dc1_load_valid), 
                           (dc1_data_bank_sel_lo[1] & dc1_load_valid),
                           (dc1_data_bank_sel_hi[0] & dc1_load_valid), 
                           (dc1_data_bank_sel_lo[0] & dc1_load_valid)}; 
                   
  dc2_bank_req_mask     = {dc2_req_dd_odd_hi,  dc2_req_dd_odd_lo,
                           dc2_req_dd_even_hi, dc2_req_dd_even_lo};
  
  wq_top_bank_req_mask  = { wq_req_dd_odd_hi, wq_req_dd_odd_lo,
                            wq_req_dd_even_hi, wq_req_dd_even_lo}; 

  wq_sec_bank_req_mask  = 4'b0000;               
  
  
  // Handy vectors (ack)
  //
  dc1_bank_ack_mask     = {dc1_ack_dd_odd_hi,  dc1_ack_dd_odd_lo,
                           dc1_ack_dd_even_hi, dc1_ack_dd_even_lo};

  dc1_bank_not_ack      = dc1_wq_conflict 
                        ? dc1_bank_req_mask
                        : (dc1_bank_ack_mask ^ dc1_bank_req_mask);

  // Banks that DC1 and DC2 require are not given to WQ.
  // Lets assume a scenario where there is a bank match between two
  // instructions, (dc1 would not have requested the bank, it just uses the bank activated by DC2)
  // then dc2_keep_bank_busy comes in to play after the instruction moves to DC2
  // during this transistion from DC1 to DC2, the following dc1_dc2_bank_common makes sures that WQ does not come in 
  // and steal the banks
  //
  // This could have been handled by dc2_keep_bank_busy, but that would have an impact on the pipeline LD's
  // Hence we do that in wq ack, so that it does not affect the pipeline LD's  
  // 
  // In case of lost ownership, there is no bank common
  //
  
  dc1_dc2_bank_common   = (dc1_bank_req_mask | dc2_data_bank_sel_r)
                        & {4{(dc1_ld_target_dc | dc2_ld_target_dc)}}
                        & {4{(~dc2_lost_ownership)}};

  // (1) Make sure that the WQ does not steal the banks that are required by DC2
  //     after the dc2_stall goes away
  //
  dc1_dc2_bank_common_set_cg0 = (dc1_load_valid & x1_pass)
                              | (dc2_full_ack_dd & dc3_enable);  // (1)

  dc1_dc2_bank_common_clr_cg0 = (|dc1_dc2_bank_common_r)
                              & (  (dc2_ld_target_dc & x2_pass)
                                 | (~dc2_ld_target_dc)      
                                 | dc2_kill
                                 | dc2_lost_ownership);
  
  dc2_bank_ack_mask     = {dc2_ack_dd_odd_hi,  dc2_ack_dd_odd_lo,
                           dc2_ack_dd_even_hi, dc2_ack_dd_even_lo};
  
  wq_bank_ack_mask      = {wq_ack_dd_odd_hi,  wq_ack_dd_odd_lo,
                           wq_ack_dd_even_hi, wq_ack_dd_even_lo};
  
  dmu_bank_ack_mask     = {dmu_ack_dd_odd_hi,  dmu_ack_dd_odd_lo,
                           dmu_ack_dd_even_hi, dmu_ack_dd_even_lo};
                            
  
  dd_busy_nxt           =   (| dc1_bank_ack_mask)
                          | (| wq_bank_ack_mask);
  
end

always @*
begin : dc2_full_ack_dd_PROC
  //
  // A full ack indicates the client was granted all the banks it have requested
  // On a full ack, the client is 'ready' to proceed. We do not fire a memory
  // bank on a partial ack!
  //
  
  dc1_full_ack_dd    =   (dc1_bank_req_mask == dc1_bank_ack_mask)
                       & x1_pass
                       ;
                       
  dc2_full_ack_dd    = (dc2_bank_req_mask == dc2_bank_ack_mask);
  
  dc2_full_ack_dt    =  (dc2_req_dt_odd  == dc2_ack_dt_odd)
                      & (dc2_req_dt_even == dc2_ack_dt_even);
  
                      
  // Give DD & DS to the WQ when:
  //
  wq_top_full_ack_dd =  (   (wq_top_bank_req_mask & wq_bank_ack_mask) 
                           == wq_top_bank_req_mask) 
                       ;

  wq_sec_full_ack_dd =   wq_top_full_ack_dd
                       & (  (wq_sec_bank_req_mask & wq_bank_ack_mask) 
                          == wq_sec_bank_req_mask);
  
  dmu_full_ack       = (   (& dmu_bank_ack_mask) 
                        &  (dmu_ack_dt_even |  dmu_ack_dt_odd));
  dmu_full_ack_dd    = & dmu_bank_ack_mask;
  
  // The AUX only access a single bank
  //
  aux_full_ack_dd    =   aux_ack_dd_even_lo 
                       | aux_ack_dd_even_hi
                       | aux_ack_dd_odd_lo
                       | aux_ack_dd_odd_hi;


end


//////////////////////////////////////////////////////////////////////////////
//                                                                          
// DD  ctl memory flops (nxt values of cs and we)
//                                                                           
//////////////////////////////////////////////////////////////////////////////

reg   dc_data_even_cs_lo_cg0;
reg   dc_data_even_cs_hi_cg0;
reg   dc_data_odd_cs_lo_cg0; 
reg   dc_data_odd_cs_hi_cg0;

always @*
begin : dc_data_cs_PROC
  // Clock enables
  //
  dc_data_even_cs_lo_cg0 =   dd_bank_busy_lo_r[0]
                           | dc1_ack_dd_even_lo
                           | dc2_ack_dd_even_lo
                           | wq_ack_dd_even_lo
                           | dmu_ack_dd_even_lo
                           | aux_ack_dd_even_lo
                           | dmu_has_dc_r
                             ;
  
  dc_data_even_cs_hi_cg0 =   dd_bank_busy_hi_r[0]
                           | dc1_ack_dd_even_hi
                           | dc2_ack_dd_even_hi
                           | wq_ack_dd_even_hi
                           | dmu_ack_dd_even_hi
                           | aux_ack_dd_even_hi
                           | dmu_has_dc_r
                             ;
  
  dc_data_odd_cs_lo_cg0 =   dd_bank_busy_lo_r[1]
                          | dc1_ack_dd_odd_lo
                          | dc2_ack_dd_odd_lo
                          | wq_ack_dd_odd_lo
                          | dmu_ack_dd_odd_lo
                          | aux_ack_dd_odd_lo
                          | dmu_has_dc_r
                             ;
  
  dc_data_odd_cs_hi_cg0 =   dd_bank_busy_hi_r[1]
                          | dc1_ack_dd_odd_hi
                          | dc2_ack_dd_odd_hi
                          | wq_ack_dd_odd_hi
                          | dmu_ack_dd_odd_hi
                          | aux_ack_dd_odd_hi
                          | dmu_has_dc_r
                             ;
  
  // The chip select is set whenever client(s) have full access to the 
  // dd memory
  //
  dc_data_even_cs_lo_nxt =  
         (dc1_ack_dd_qual[0] & dc1_target_dc)                        // dc1
       | (dc2_full_ack_dd    & dc2_bank_req_mask[0] & dc2_target_dc) // dc2
       | (wq_top_full_ack_dd & wq_top_bank_req_mask[0])              // wq_top
       | (wq_sec_full_ack_dd & wq_sec_bank_req_mask[0])              // wq_sec
       | (aux_ack_dd_even_lo)
       | (dmu_full_ack_dd)
         ;
  
  dc_data_even_cs_hi_nxt =  
         (dc1_ack_dd_qual[1] & dc1_target_dc)                        // dc1
       | (dc2_full_ack_dd    & dc2_bank_req_mask[1] & dc2_target_dc) // dc2
       | (wq_top_full_ack_dd & wq_top_bank_req_mask[1])              // wq_top
       | (wq_sec_full_ack_dd & wq_sec_bank_req_mask[1])              // wq_sec
       | (aux_ack_dd_even_hi)
       | (dmu_full_ack_dd)
         ;
 
  
  dc_data_odd_cs_lo_nxt =  
         (dc1_ack_dd_qual[2] & dc1_target_dc)                        // dc1
       | (dc2_full_ack_dd    & dc2_bank_req_mask[2] & dc2_target_dc) // dc2
       | (wq_top_full_ack_dd & wq_top_bank_req_mask[2])              // wq_top
       | (wq_sec_full_ack_dd & wq_sec_bank_req_mask[2])              // wq_sec
       | (aux_ack_dd_odd_lo)
       | (dmu_full_ack_dd)
         ;
  
  dc_data_odd_cs_hi_nxt =  
         (dc1_ack_dd_qual[3] & dc1_target_dc)                        // dc1
       | (dc2_full_ack_dd    & dc2_bank_req_mask[3] & dc2_target_dc) // dc2
       | (wq_top_full_ack_dd & wq_top_bank_req_mask[3])              // wq_top
       | (wq_sec_full_ack_dd & wq_sec_bank_req_mask[3])              // wq_sec
       | (aux_ack_dd_odd_hi)
       | (dmu_full_ack_dd)
         ;
  
  // The we is only set for clients doing a write opetation
  //
  dc_data_even_we_lo_nxt = 
         (wq_top_full_ack_dd & wq_top_bank_req_mask[0]) // wq_top
       | (wq_sec_full_ack_dd & wq_sec_bank_req_mask[0]) // wq_sec
       | (aux_ack_dd_even_lo & aux_dd_we)
       | (dmu_full_ack_dd    & dmu_dd_we)
         ;
   
  dc_data_even_we_hi_nxt = 
         (wq_top_full_ack_dd & wq_top_bank_req_mask[1]) // wq_top
       | (wq_sec_full_ack_dd & wq_sec_bank_req_mask[1]) // wq_sec
       | (aux_ack_dd_even_hi & aux_dd_we)
       | (dmu_full_ack_dd    & dmu_dd_we)
         ;
  
  dc_data_odd_we_lo_nxt = 
         (wq_top_full_ack_dd & wq_top_bank_req_mask[2]) // wq_top
       | (wq_sec_full_ack_dd & wq_sec_bank_req_mask[2]) // wq_sec
       | (aux_ack_dd_odd_lo  & aux_dd_we)
       | (dmu_full_ack_dd    & dmu_dd_we)
         ;
  
  dc_data_odd_we_hi_nxt = 
         (wq_top_full_ack_dd & wq_top_bank_req_mask[3]) // wq_top
       | (wq_sec_full_ack_dd & wq_sec_bank_req_mask[3]) // wq_sec
       | (aux_ack_dd_odd_hi  & aux_dd_we)
       | (dmu_full_ack_dd    & dmu_dd_we)
         ;
end

//////////////////////////////////////////////////////////////////////////////
//
// Mux that selects the input from BIST/AUX/WQ/LineBuffer to write in to DC 
//
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DATA_RANGE]   dc_data_even_lo;  
reg [`npuarc_DATA_RANGE]   dc_data_even_hi;  
reg [`npuarc_DATA_RANGE]   dc_data_odd_lo;  
reg [`npuarc_DATA_RANGE]   dc_data_odd_hi;  

wire [`npuarc_ECC_CODE_MSB:0]          dc_ecc_even_lo;
wire [`npuarc_ECC_CODE_MSB:0]          dc_ecc_even_hi;
wire [`npuarc_ECC_CODE_MSB:0]          dc_ecc_odd_lo;
wire [`npuarc_ECC_CODE_MSB:0]          dc_ecc_odd_hi;
wire [`npuarc_DATA_RANGE]  dc4_ecc_data_even_lo; // ECC Corrected data
wire [`npuarc_DATA_RANGE]  dc4_ecc_data_even_hi; // ECC Corrected data
wire [`npuarc_DATA_RANGE]  dc4_ecc_data_odd_lo;  // ECC Corrected data
wire [`npuarc_DATA_RANGE]  dc4_ecc_data_odd_hi;  // ECC Corrected data

reg  [`npuarc_DATA_RANGE]  wa_ecc_data_even_lo; // ECC Corrected data
reg  [`npuarc_DATA_RANGE]  wa_ecc_data_even_hi; // ECC Corrected data
reg  [`npuarc_DATA_RANGE]  wa_ecc_data_odd_lo;  // ECC Corrected data
reg  [`npuarc_DATA_RANGE]  wa_ecc_data_odd_hi;  // ECC Corrected data
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer
// spyglass disable_block STARC05-2.8.1.3
always @*
begin : mux_dc_data_PROC
  casez ({dmu_full_ack_dd, aux_full_ack_dd})
  2'b1?:
  begin
    // DMU
    //
    dc_data_even_lo = lbuf_rd_data_nxt[`npuarc_WORD0_RANGE];
    dc_data_even_hi = lbuf_rd_data_nxt[`npuarc_WORD1_RANGE];
    dc_data_odd_lo  = lbuf_rd_data_nxt[`npuarc_WORD2_RANGE];
    dc_data_odd_hi  = lbuf_rd_data_nxt[`npuarc_WORD3_RANGE];
  end
  2'b?1:
  begin
    // AUX
    //
    dc_data_even_lo = aux_dd_din[`npuarc_WORD0_RANGE];
    dc_data_even_hi = aux_dd_din[`npuarc_WORD1_RANGE];
    dc_data_odd_lo  = aux_dd_din[`npuarc_WORD2_RANGE];
    dc_data_odd_hi  = aux_dd_din[`npuarc_WORD3_RANGE];
  end
  default:
  begin
    // WQ
    //
    dc_data_even_lo = wq_dd_din_even_lo;
    dc_data_even_hi = wq_dd_din_even_hi;
    dc_data_odd_lo  = wq_dd_din_odd_lo;
    dc_data_odd_hi  = wq_dd_din_odd_hi;
  end
  endcase
end
// leda W547 on
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3


npuarc_alb_ecc_gen_32 u_alb_dmp_ecc_gen32_even_lo (
  .data_in        (dc_data_even_lo),
  .ecc_code       (dc_ecc_even_lo )
);

npuarc_alb_ecc_gen_32 u_alb_dmp_ecc_gen32_even_hi (
  .data_in        (dc_data_even_hi),
  .ecc_code       (dc_ecc_even_hi )
);

npuarc_alb_ecc_gen_32 u_alb_dmp_ecc_gen32_odd_lo (
  .data_in        (dc_data_odd_lo),
  .ecc_code       (dc_ecc_odd_lo )
);

npuarc_alb_ecc_gen_32 u_alb_dmp_ecc_gen32_odd_hi (
  .data_in        (dc_data_odd_hi),
  .ecc_code       (dc_ecc_odd_hi )
);

 
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// DD  data memory flops (nxt values of wem and din)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
// spyglass disable_block STARC05-2.8.1.3
always @*
begin : dd_data_din_wem_PROC
  // wq info (inputs to this module)
  //
  // Clock enables: only toggles on wq_ack. The dmu din and wem info
  // will be muxed in in DC2
  //
  
  dc_data_even_din_lo_cg0 = (  wq_ack_dd_even_lo 
                             | (dmu_full_ack_dd    & dmu_dd_we)
                             | (aux_ack_dd_even_lo & aux_dd_we))
                               ;
  dc_data_even_din_hi_cg0 = (  wq_ack_dd_even_hi
                             | (dmu_full_ack_dd    & dmu_dd_we)
                             | (aux_ack_dd_even_hi & aux_dd_we))
                               ;
  
  dc_data_odd_din_lo_cg0  = (  wq_ack_dd_odd_lo
                             | (dmu_full_ack_dd   & dmu_dd_we)
                             | (aux_ack_dd_odd_lo & aux_dd_we))
                               ;
  dc_data_odd_din_hi_cg0  = (  wq_ack_dd_odd_hi
                             | (dmu_full_ack_dd   & dmu_dd_we)
                             | (aux_ack_dd_odd_hi & aux_dd_we))
                               ;
  
  casez ({
          1'b0,
          dmu_full_ack_dd, aux_full_ack_dd})
  
  3'b01?:
  begin
    // DMU
    //
    // The write mask
    //
    dc_data_even_wem_lo_nxt = 5'b11111;
    dc_data_even_wem_hi_nxt = 5'b11111;
    dc_data_odd_wem_lo_nxt  = 5'b11111;
    dc_data_odd_wem_hi_nxt  = 5'b11111;

    dc_data_even_wem_lo_nxt = 5'b11111;
    dc_data_even_din_lo_nxt = {dc_ecc_even_lo, dc_data_even_lo};
 
    dc_data_even_wem_hi_nxt = 5'b11111;
    dc_data_even_din_hi_nxt = {dc_ecc_even_hi, dc_data_even_hi};

    dc_data_odd_wem_lo_nxt  = 5'b11111;
    dc_data_odd_din_lo_nxt  = {dc_ecc_odd_lo, dc_data_odd_lo};

    dc_data_odd_wem_hi_nxt  = 5'b11111;
    dc_data_odd_din_hi_nxt  = {dc_ecc_odd_hi, dc_data_odd_hi};
  end
  
  3'b0?1:
  begin
    // AUX
    //
    dc_data_even_wem_lo_nxt = {{~ecc_dmp_disable},4'b1111};
    dc_data_even_din_lo_nxt = {dc_ecc_even_lo, dc_data_even_lo};
    dc_data_even_wem_hi_nxt = {{~ecc_dmp_disable},4'b1111};
    dc_data_even_din_hi_nxt = {dc_ecc_even_hi, dc_data_even_hi};
   
    
    dc_data_odd_wem_lo_nxt  = {{~ecc_dmp_disable},4'b1111};
    dc_data_odd_din_lo_nxt  = {dc_ecc_odd_lo, dc_data_odd_lo};
    dc_data_odd_wem_hi_nxt  = {{~ecc_dmp_disable},4'b1111};
    dc_data_odd_din_hi_nxt  = {dc_ecc_odd_hi, dc_data_odd_hi};
  end
  
  default:
  begin
    // WQ
    //
    dc_data_even_wem_lo_nxt = {{~ecc_dmp_disable & (|wq_dd_wem_even_lo)},
                                 wq_dd_wem_even_lo};
    dc_data_even_din_lo_nxt = {dc_ecc_even_lo, dc_data_even_lo};

    dc_data_even_wem_hi_nxt = {{~ecc_dmp_disable & (|wq_dd_wem_even_hi)},
                                 wq_dd_wem_even_hi};    
    dc_data_even_din_hi_nxt = {dc_ecc_even_hi, dc_data_even_hi};

    dc_data_odd_wem_lo_nxt  = {{~ecc_dmp_disable & (|wq_dd_wem_odd_lo)},
                                 wq_dd_wem_odd_lo};
    dc_data_odd_din_lo_nxt  = {dc_ecc_odd_lo, dc_data_odd_lo};
   
    dc_data_odd_wem_hi_nxt  = {{~ecc_dmp_disable & (|wq_dd_wem_odd_hi)},
                                 wq_dd_wem_odd_hi}; 
    dc_data_odd_din_hi_nxt  = {dc_ecc_odd_hi, dc_data_odd_hi};
  end
  endcase
  
end
// leda W547 on
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block defining bank busy           
//                                                                           
//////////////////////////////////////////////////////////////////////////////
//
// Since individual banks are fired, irrespective of full ack, keep the bank busy for
// X1 instructions that move to X2
//
// Even lo
//
assign  dd_bank_busy_lo_nxt[0] = dc_data_even_cs_lo_nxt | dc2_keep_bank_busy[0];
// Odd lo
//
assign  dd_bank_busy_lo_nxt[1] = dc_data_odd_cs_lo_nxt  | dc2_keep_bank_busy[2];
// Even hi
//
assign  dd_bank_busy_hi_nxt[0] = dc_data_even_cs_hi_nxt | dc2_keep_bank_busy[1];
// Odd hi
//
assign  dd_bank_busy_hi_nxt[1] = dc_data_odd_cs_hi_nxt  | dc2_keep_bank_busy[3];
//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block to respond to the wq              
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_read_one_two_PROC
  // DC ack the WQ when the WQ is req a bank and it gets a full ack
  //
  wq_read_one =     wq_top_full_ack_dd 
                & (| wq_top_bank_req_mask);
  
//  wq_read_two = 1'b0;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// DD  data addr flops (nxt values of addr)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
// spyglass disable_block STARC05-2.8.1.3
always @*
begin : dc_data_addr_PROC
  dc_data_even_addr_lo_cg0 =   dc1_req_dd_even_lo
                             | dc2_req_dd_even_lo
                             | wq_ack_dd_even_lo
                             | dmu_ack_dd_even_lo
                             | aux_ack_dd_even_lo
                             | dmu_has_dc_r
                               ;
  
  casez ({wq_ack_dd_even_lo, 
          aux_ack_dd_even_lo, 
          dmu_has_dc_r, 
          dc2_ack_dd_even_lo})
  4'b???1:  dc_data_even_addr_lo_nxt  = dc2_dd_addr0;
  4'b??1?:  dc_data_even_addr_lo_nxt  = dmu_dd_addr;
  4'b?1??:  dc_data_even_addr_lo_nxt  = aux_dd_addr;
  4'b1???:  dc_data_even_addr_lo_nxt  = wq_dd_addr_even_lo;
  default:  dc_data_even_addr_lo_nxt  = dc1_dd_addr0;
  endcase  
   
  dc_data_even_addr_hi_cg0 =   dc1_req_dd_even_hi
                             | dc2_req_dd_even_hi
                             | wq_ack_dd_even_hi
                             | dmu_ack_dd_even_hi
                             | aux_ack_dd_even_hi
                             | dmu_has_dc_r
                             ;
  
  casez ({wq_ack_dd_even_hi, 
          aux_ack_dd_even_hi, 
          dmu_has_dc_r, 
          dc2_ack_dd_even_hi})
  4'b???1:  dc_data_even_addr_hi_nxt  = dc2_dd_addr0;
  4'b??1?:  dc_data_even_addr_hi_nxt  = dmu_dd_addr;
  4'b?1??:  dc_data_even_addr_hi_nxt  = aux_dd_addr;
  4'b1???:  dc_data_even_addr_hi_nxt  = wq_dd_addr_even_hi;
  default:  dc_data_even_addr_hi_nxt  = dc1_dd_addr0;
  endcase  
  
  dc_data_odd_addr_lo_cg0 =    dc1_req_dd_odd_lo
                             | dc2_req_dd_odd_lo
                             | wq_ack_dd_odd_lo
                             | dmu_ack_dd_odd_lo
                             | aux_ack_dd_odd_lo
                             | dmu_has_dc_r
                             ;
  
  casez ({wq_ack_dd_odd_lo, 
          aux_ack_dd_odd_lo, 
          dmu_has_dc_r, 
          dc2_ack_dd_odd_lo})
  4'b???1:  dc_data_odd_addr_lo_nxt  = dc2_dd_addr1;
  4'b??1?:  dc_data_odd_addr_lo_nxt  = dmu_dd_addr;
  4'b?1??:  dc_data_odd_addr_lo_nxt  = aux_dd_addr;
  4'b1???:  dc_data_odd_addr_lo_nxt  = wq_dd_addr_odd_lo;
  default:  dc_data_odd_addr_lo_nxt  = dc1_dd_addr1;
  endcase  
  
  dc_data_odd_addr_hi_cg0 =    dc1_req_dd_odd_hi
                             | dc2_req_dd_odd_hi
                             | wq_ack_dd_odd_hi
                             | dmu_ack_dd_odd_hi
                             | aux_ack_dd_odd_hi
                             | dmu_has_dc_r
                               ;
  
  casez ({wq_ack_dd_odd_hi, 
          aux_ack_dd_odd_hi, 
          dmu_has_dc_r, 
          dc2_ack_dd_odd_hi})
  4'b???1:  dc_data_odd_addr_hi_nxt  = dc2_dd_addr1;
  4'b??1?:  dc_data_odd_addr_hi_nxt  = dmu_dd_addr;
  4'b?1??:  dc_data_odd_addr_hi_nxt  = aux_dd_addr;
  4'b1???:  dc_data_odd_addr_hi_nxt  = wq_dd_addr_odd_hi;
  default:  dc_data_odd_addr_hi_nxt  = dc1_dd_addr1;
  endcase  
end
// spyglass enable_block W398
// leda W547 on
// spyglass enable_block STARC05-2.8.1.3
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// DD way information (nxt value of way)
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
//
// spyglass disable_block STARC05-2.8.1.3
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
always @*
begin : dc_way_hot_PROC
  dc_data_way_hot_cg0  =  dmu_full_ack_dd
                        | (| wq_bank_ack_mask)
                        | aux_full_ack_dd;
  
  casez ({dmu_full_ack_dd, aux_full_ack_dd})
  2'b1?:   dc_data_way_hot_nxt = dmu_dd_way_hot;
  2'b?1:   dc_data_way_hot_nxt = aux_dd_way_hot;
  default: dc_data_way_hot_nxt = wq_dd_way_hot;
  endcase
  
end
// leda W547 on
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
//////////////////////////////////////////////////////////////////////////////
//                                                                           
// DC3 tag comparison      
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_dt_valid_PROC
  // One hot encoded way valid information
  //
  dc3_dt_even_valid_way_hot[0] = dc_tag_even_dout_w0[`npuarc_DC_TAG_VALID_BIT];
  dc3_dt_even_valid_way_hot[1] = dc_tag_even_dout_w1[`npuarc_DC_TAG_VALID_BIT];

  dc3_dt_odd_valid_way_hot[0]  = dc_tag_odd_dout_w0[`npuarc_DC_TAG_VALID_BIT];
  dc3_dt_odd_valid_way_hot[1]  = dc_tag_odd_dout_w1[`npuarc_DC_TAG_VALID_BIT];
end



always @*
begin : dc3_dt_tag_match_PROC
  // One hot encoded tag match information
  //
  dc3_dt_even_tag_match_way_hot[0] = (   dc_tag_even_dout_w0[`npuarc_DC_TAG_TAG_RANGE]
                                      == dc3_mem_addr_even[`npuarc_DC_TAG_RANGE]); 
  dc3_dt_even_tag_match_way_hot[1] = (   dc_tag_even_dout_w1[`npuarc_DC_TAG_TAG_RANGE]
                                      == dc3_mem_addr_even[`npuarc_DC_TAG_RANGE]); 

  dc3_dt_odd_tag_match_way_hot[0]  = (   dc_tag_odd_dout_w0[`npuarc_DC_TAG_TAG_RANGE]
                                      == dc3_mem_addr_odd[`npuarc_DC_TAG_RANGE]); 
  dc3_dt_odd_tag_match_way_hot[1]  = (   dc_tag_odd_dout_w1[`npuarc_DC_TAG_TAG_RANGE]
                                      == dc3_mem_addr_odd[`npuarc_DC_TAG_RANGE]); 
end

always @*
begin : dc3_dt_way_hot_prel_PROC
  // One hot encoded 'hit' information
  //
  dc3_dt_even_hit_way_hot_prel[0] =   dc3_dt_even_valid_way_hot[0] 
                                    & dc3_dt_even_tag_match_way_hot[0];
  dc3_dt_even_hit_way_hot_prel[1] =   dc3_dt_even_valid_way_hot[1]
                                    & dc3_dt_even_tag_match_way_hot[1];
  
  dc3_dt_odd_hit_way_hot_prel[0] =   dc3_dt_odd_valid_way_hot[0]
                                   & dc3_dt_odd_tag_match_way_hot[0];
  dc3_dt_odd_hit_way_hot_prel[1] =   dc3_dt_odd_valid_way_hot[1]
                                   & dc3_dt_odd_tag_match_way_hot[1];
end


//////////////////////////////////////////////////////////////////////////////
//  DC3 hit information                                                                         
//                                                                           
//////////////////////////////////////////////////////////////////////////////
assign dc3_dt_even_hit  = (| dc3_dt_even_hit_way_hot) & dc3_dt_bank_sel_r[0];
assign dc3_dt_odd_hit   = (| dc3_dt_odd_hit_way_hot)  & dc3_dt_bank_sel_r[1];
assign dc3_dt_hit       = dc3_dt_even_hit | dc3_dt_odd_hit;

assign dc3_dt_even_miss = ~(| dc3_dt_even_hit_way_hot) & dc3_dt_bank_sel_r[0];
assign dc3_dt_odd_miss  = ~(| dc3_dt_odd_hit_way_hot)  & dc3_dt_bank_sel_r[1];

// This is to check the address matching among the dc3 and dc4 with MQ
// so in case of a dc3_ld matches with dc4_st, we treat it as a cache miss
//
// When there is a dc3_ld and dc4_ld is also a load, but its data is not yet available in line buffer, then treat this load as a miss too
//
// (1) When there is a match in lsmq, that means some entry is waiting for the data to get retired, hence treat the dc3 as miss too, hence it enters the LSMQ
//     and retires
//
wire   dc3_dc4_addr_match;
assign dc3_dc4_addr_match = ( (dc3_addr_match0 | dc3_addr_match1) & x3_load_r)
                          & ( (dc4_addr_match0 | dc4_addr_match1) & ( (|dc4_lsmq_write) | lsmq_match0 | lsmq_match1)); // (1)
 
// In case of stores, assert dc3_dt_miss, eventhough they hit in line buffer, because all the stores 
// will happen through the LSMQ
//
assign dc3_dt_miss      = (  (dc3_dt_even_miss & ( (~(mq_addr_even_hit)) | (mq_addr_even_hit & (dc3_st_target_dc | dc3_dc4_addr_match))))
                           | (dc3_dt_odd_miss  & ( (~(mq_addr_odd_hit )) | (mq_addr_odd_hit  & (dc3_st_target_dc | dc3_dc4_addr_match)))));

// This is the fast signal used for dmu clock control
//
assign dc3_dt_miss_fast = dc3_dt_even_miss | dc3_dt_odd_miss;

// In case of stores, do not assert hit, because the store is still treated as a miss
// and enters the LSMQ
//
assign addr_even_hit    = dc3_dt_even_hit | (mq_addr_even_hit & (~(dc3_st_target_dc | dc3_dc4_addr_match)));
assign addr_odd_hit     = dc3_dt_odd_hit  | (mq_addr_odd_hit  & (~(dc3_st_target_dc | dc3_dc4_addr_match)));


//////////////////////////////////////////////////////////////////////////////
//                                                                           
//                                                                           
//////////////////////////////////////////////////////////////////////////////
reg  dc4_waw_replay_nxt;
always @*
begin : dc4_waw_replay_nxt_PROC
  // This indicates a hit in the line buffer. This is used in the EXU
  // convert a possible WAW stall into replay
  //
  case (dc3_dt_bank_sel_r)
  2'b01:   dc4_waw_replay_nxt = mq_addr_even_hit;
  2'b10:   dc4_waw_replay_nxt = mq_addr_odd_hit;
  default: dc4_waw_replay_nxt = mq_addr_even_hit | mq_addr_odd_hit;
  endcase
end


//////////////////////////////////////////////////////////////////////////////
//                                                                           
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dmu_aux_dd_PROC
  dmu_aux_dd_read    = dmu_evict_rd | aux_dd_direct_read;
  dmu_aux_dd_way_hot = aux_dd_direct_read ? aux_dd_way_hot : dmu_dd_way_hot;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
//   
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
always @*
begin : dc3_way0_hit_PROC
  dc3_even_way0_hit = 1'b0;
  dc3_odd_way0_hit  = 1'b0;
  
  casez ({dmu_aux_dd_read, dc3_dt_bank_sel_r, dc3_data_mem_valid_r})
  7'b1_??_????:
  begin
    // Doing an eviction or a aux read
    //
    dc3_even_way0_hit = dmu_aux_dd_way_hot[0];
    dc3_odd_way0_hit  = dmu_aux_dd_way_hot[0];
  end
  
  7'b0_01_????:
  begin
    // This access only needs the even tag
    //
    dc3_even_way0_hit = dc3_dt_even_hit_way_hot[0];
    dc3_odd_way0_hit  = dc3_dt_even_hit_way_hot[0];
  end
  
  7'b0_10_????:
  begin
    // This access only needs the odd tag
    //
    dc3_even_way0_hit = dc3_dt_odd_hit_way_hot[0];
    dc3_odd_way0_hit  = dc3_dt_odd_hit_way_hot[0];
  end
  
  7'b0_11_1??1:
  begin
    // Crossing cache lines: both tags. Data bank odd hi to even lo crossing
    //
    if (x3_mem_addr0_r[`npuarc_DC_TAG_BANK_ID])
    begin
      // Odd to even tag crossing 
      //
      dc3_even_way0_hit = dc3_dt_even_hit_way_hot[0];
      dc3_odd_way0_hit  = dc3_dt_odd_hit_way_hot[0];
    end
    else
    begin
      // Even to odd tag crossing 
      //
      dc3_even_way0_hit = dc3_dt_odd_hit_way_hot[0];
      dc3_odd_way0_hit  = dc3_dt_even_hit_way_hot[0];
    end
  end
// spyglass disable_block W193
// SMD: Empty statement
// SJ:  Empty default statements kept
  default:
    ;
// spyglass enable_block W193   
  endcase  
end
// leda W547 on

always @*
begin : dc3_dt_any_hit_PROC
  case (dc3_dt_bank_sel_r)
  2'b01:  
    dc3_dt_any_hit =    (dc3_dt_even_hit | mq_addr_even_hit) 
                      & (~dc3_dc_poisoned);
  2'b10:  
    dc3_dt_any_hit =   (dc3_dt_odd_hit  | mq_addr_odd_hit) 
                      & (~dc3_dc_poisoned);
  2'b11:  
    dc3_dt_any_hit =  (   (dc3_dt_even_hit | mq_addr_even_hit) 
                       |  (dc3_dt_odd_hit  | mq_addr_odd_hit))
                      & (~dc3_dc_poisoned);
  default:
    dc3_dt_any_hit = 1'b0;
  endcase
end
   
//////////////////////////////////////////////////////////////////////////////
// @ DC3 Tag information for the DMU
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
always @*
begin : dc3_dt_tag_val_PROC
  // Read tag for eviction.
  //
  casez ({dmu_dt_odd_sel, dmu_dt_way_hot[1:0]})
  3'b0_?1:  dc3_dt_tag = dc_tag_even_dout_w0[`npuarc_DC_TAG_TAG_RANGE]; // even
  3'b0_10:  dc3_dt_tag = dc_tag_even_dout_w1[`npuarc_DC_TAG_TAG_RANGE]; // even
  3'b1_?1:  dc3_dt_tag = dc_tag_odd_dout_w0[`npuarc_DC_TAG_TAG_RANGE];  // odd
  3'b1_10:  dc3_dt_tag = dc_tag_odd_dout_w1[`npuarc_DC_TAG_TAG_RANGE];  // odd
  default:  dc3_dt_tag = dc_tag_even_dout_w0[`npuarc_DC_TAG_TAG_RANGE];
  endcase
  
  casez ({dmu_dt_odd_sel, dmu_dt_way_hot[1:0]})
  3'b0_?1:  dc3_dt_val = dc_tag_even_dout_w0[`npuarc_DC_TAG_VALID_BIT]; // even
  3'b0_10:  dc3_dt_val = dc_tag_even_dout_w1[`npuarc_DC_TAG_VALID_BIT]; // even
  3'b1_?1:  dc3_dt_val = dc_tag_odd_dout_w0[`npuarc_DC_TAG_VALID_BIT];  // odd
  3'b1_10:  dc3_dt_val = dc_tag_odd_dout_w1[`npuarc_DC_TAG_VALID_BIT];  // odd
  default:  dc3_dt_val = dc_tag_even_dout_w0[`npuarc_DC_TAG_VALID_BIT];
  endcase
end
// leda W547 on
//////////////////////////////////////////////////////////////////////////////
//                                                                           
// DC3 status information for the DMU  
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_ds_PROC
  if (dmu_ds_odd_sel)
  begin
    // Odd
    //
    dc3_ds_lock  =  {1'b0, status1_lock_odd}
                  ;
    dc3_ds_dirty = status1_dirty_odd;
    dc3_ds_lru   = status1_lru_odd;  
  end
  else
  begin
    // Even
    //
    dc3_ds_lock  =  {1'b0, status1_lock_even}
                  ;
    dc3_ds_dirty = status1_dirty_even;
    dc3_ds_lru   = status1_lru_even;  
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Data Tag SRAM interface           
//                                                                           
//////////////////////////////////////////////////////////////////////////////

wire [`npuarc_DC_TAG_ECC_CODE_MSB:0]   dc_tag_ecc_even_w0;
wire [`npuarc_DC_TAG_ECC_CODE_MSB:0]   dc_tag_ecc_even_w1;
wire [`npuarc_DC_TAG_ECC_CODE_MSB:0]   dc_tag_ecc_odd_w0;
wire [`npuarc_DC_TAG_ECC_CODE_MSB:0]   dc_tag_ecc_odd_w1;

npuarc_dc_tag_ecc_encoder u_dc_tag_ecc_encoder_even_lo (
  .data_in        ({dc_tag_even_valid_w0_r, dc_tag_even_tag_w0_r}),
  .ecc            (dc_tag_ecc_even_w0)
);

npuarc_dc_tag_ecc_encoder u_dc_tag_ecc_encoder_even_hi (
  .data_in        ({dc_tag_even_valid_w1_r, dc_tag_even_tag_w1_r}),
  .ecc            (dc_tag_ecc_even_w1)
);

npuarc_dc_tag_ecc_encoder u_dc_tag_ecc_encoder_odd_lo (
  .data_in        ({dc_tag_odd_valid_w0_r, dc_tag_odd_tag_w0_r}),
  .ecc            (dc_tag_ecc_odd_w0)
);

npuarc_dc_tag_ecc_encoder u_dc_tag_ecc_encoder_odd_hi (
  .data_in        ({dc_tag_odd_valid_w1_r, dc_tag_odd_tag_w1_r}),
  .ecc            (dc_tag_ecc_odd_w1)
);



always @*
begin : dc_tag_srams_PROC
  dc_tag_even_cs_w0     = dc_tag_even_cs_r[0];
  dc_tag_even_we_w0     = dc_tag_even_we_r;
  dc_tag_even_addr_w0   = dc_tag_even_addr_r;
  dc_tag_even_addr_w0[`npuarc_DC_PRED_BIT_RANGE] =   dc_pipe_ack_dt_even_r
                                             ? dc2_pred0
                                             : dc_tag_even_addr_r[`npuarc_DC_PRED_BIT_RANGE];
    dc_tag_even_wem_w0  = { {`npuarc_DC_TR_ECC_BITS{(~ecc_dmp_disable & dc_tag_even_wem_r[1])}}, 
                             dc_tag_even_wem_r[1], {`npuarc_DC_TAG_BITS{dc_tag_even_wem_r[1]}}};
    dc_tag_even_din_w0  = {
                            dc_tag_ecc_even_w0,
                            dc_tag_even_valid_w0_r,                
                            dc_tag_even_tag_w0_r};

  dc_tag_odd_cs_w0      = dc_tag_odd_cs_r[0];
  dc_tag_odd_we_w0      = dc_tag_odd_we_r;
  dc_tag_odd_addr_w0    = dc_tag_odd_addr_r;
  dc_tag_odd_addr_w0[`npuarc_DC_PRED_BIT_RANGE] =   dc_pipe_ack_dt_odd_r
                                            ? dc2_pred1
                                            : dc_tag_odd_addr_r[`npuarc_DC_PRED_BIT_RANGE];
    dc_tag_odd_wem_w0  = { {`npuarc_DC_TR_ECC_BITS{(~ecc_dmp_disable & dc_tag_odd_wem_r[1])}},
                            dc_tag_odd_wem_r[1], {`npuarc_DC_TAG_BITS{dc_tag_odd_wem_r[1]}}};
    dc_tag_odd_din_w0  = {
                           dc_tag_ecc_odd_w0,
                           dc_tag_odd_valid_w0_r,
                           dc_tag_odd_tag_w0_r};

  dc_tag_even_cs_w1     = dc_tag_even_cs_r[1];
  dc_tag_even_we_w1     = dc_tag_even_we_r;
  dc_tag_even_addr_w1   = dc_tag_even_addr_r;
  dc_tag_even_addr_w1[`npuarc_DC_PRED_BIT_RANGE] =   dc_pipe_ack_dt_even_r
                                             ? dc2_pred0
                                             : dc_tag_even_addr_r[`npuarc_DC_PRED_BIT_RANGE];
    dc_tag_even_wem_w1  = { {`npuarc_DC_TR_ECC_BITS{(~ecc_dmp_disable & dc_tag_even_wem_r[1])}}, 
                             dc_tag_even_wem_r[1], {`npuarc_DC_TAG_BITS{dc_tag_even_wem_r[1]}}};
    dc_tag_even_din_w1  = {
                            dc_tag_ecc_even_w1,
                            dc_tag_even_valid_w1_r,                
                            dc_tag_even_tag_w1_r};

  dc_tag_odd_cs_w1      = dc_tag_odd_cs_r[1];
  dc_tag_odd_we_w1      = dc_tag_odd_we_r;
  dc_tag_odd_addr_w1    = dc_tag_odd_addr_r;
  dc_tag_odd_addr_w1[`npuarc_DC_PRED_BIT_RANGE] =   dc_pipe_ack_dt_odd_r
                                            ? dc2_pred1
                                            : dc_tag_odd_addr_r[`npuarc_DC_PRED_BIT_RANGE];
    dc_tag_odd_wem_w1  = { {`npuarc_DC_TR_ECC_BITS{(~ecc_dmp_disable & dc_tag_odd_wem_r[1])}},
                            dc_tag_odd_wem_r[1], {`npuarc_DC_TAG_BITS{dc_tag_odd_wem_r[1]}}};
    dc_tag_odd_din_w1  = {
                           dc_tag_ecc_odd_w1,
                           dc_tag_odd_valid_w1_r,
                           dc_tag_odd_tag_w1_r};

end


//////////////////////////////////////////////////////////////////////////////
// Received data is little endian:
//    - To DC: change to big endian
//    - To result bus: no change
//    - From DC: change to little endian
//////////////////////////////////////////////////////////////////////////////
// 
  assign lbuf_rd_data_nxt = lbuf_rd_data;
  assign dc_rd_data  = dc_rd_data_nxt;

  assign dc4_dd_data = dmu_data_sel_r ? dc_rd_data : rb_aln_data;

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Data Data SRAM interface           
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc_data_din_wem_PROC
  dc_data_even_din_lo  = {dc_data_even_din_lo_r, dc_data_even_din_lo_r};
  dc_data_even_din_hi  = {dc_data_even_din_hi_r, dc_data_even_din_hi_r};
  dc_data_odd_din_lo  = {dc_data_odd_din_lo_r, dc_data_odd_din_lo_r};
  dc_data_odd_din_hi  = {dc_data_odd_din_hi_r, dc_data_odd_din_hi_r};

  dc_data_even_wem_lo  =  &dc_data_way_hot_r
                       ? {dc_data_even_wem_lo_r,dc_data_even_wem_lo_r}
                       : (  dc_data_way_hot_r[0]
                          ? {5'b00000, dc_data_even_wem_lo_r}
                          : {dc_data_even_wem_lo_r, 5'b00000});
  dc_data_even_wem_hi  =  &dc_data_way_hot_r
                       ?  {dc_data_even_wem_hi_r,dc_data_even_wem_hi_r}  
                       :  (  dc_data_way_hot_r[0]
                           ? {5'b00000, dc_data_even_wem_hi_r}
                           : {dc_data_even_wem_hi_r, 5'b00000});
  dc_data_odd_wem_lo  =  &dc_data_way_hot_r
                      ?  {dc_data_odd_wem_lo_r,dc_data_odd_wem_lo_r} 
                      :  (  dc_data_way_hot_r[0]
                          ? {5'b00000, dc_data_odd_wem_lo_r}
                          : {dc_data_odd_wem_lo_r, 5'b00000});
  dc_data_odd_wem_hi  =  &dc_data_way_hot_r
                      ?  {dc_data_odd_wem_hi_r,dc_data_odd_wem_hi_r} 
                      :  (  dc_data_way_hot_r[0]
                          ? {5'b00000, dc_data_odd_wem_hi_r}
                          : {dc_data_odd_wem_hi_r, 5'b00000});
  
  dc_data_even_cs_lo                         = dc_data_even_cs_lo_r;
  dc_data_even_we_lo                         = dc_data_even_we_lo_r;
  dc_data_even_addr_lo                       = dc_data_even_addr_lo_r; 
  dc_data_even_addr_lo[`npuarc_DC_PRED_BIT_RANGE]   =  dc_pipe_ack_dd_even_lo_r
                                              ? dc2_pred0
                                              : dc_data_even_addr_lo_r[`npuarc_DC_PRED_BIT_RANGE]; 
  
  
  dc_data_even_cs_hi                       = dc_data_even_cs_hi_r;
  dc_data_even_we_hi                       = dc_data_even_we_hi_r;
  dc_data_even_addr_hi                     = dc_data_even_addr_hi_r; 
  dc_data_even_addr_hi[`npuarc_DC_PRED_BIT_RANGE] =  dc_pipe_ack_dd_even_hi_r
                                            ? dc2_pred0
                                            : dc_data_even_addr_hi_r[`npuarc_DC_PRED_BIT_RANGE]; 

  dc_data_odd_cs_lo                       = dc_data_odd_cs_lo_r;    
  dc_data_odd_we_lo                       = dc_data_odd_we_lo_r;    
  dc_data_odd_addr_lo                     = dc_data_odd_addr_lo_r;  
  dc_data_odd_addr_lo[`npuarc_DC_PRED_BIT_RANGE] =  dc_pipe_ack_dd_odd_lo_r
                                            ? dc2_pred1
                                            : dc_data_odd_addr_lo_r[`npuarc_DC_PRED_BIT_RANGE]; 

  dc_data_odd_cs_hi                       = dc_data_odd_cs_hi_r;
  dc_data_odd_we_hi                       = dc_data_odd_we_hi_r;
  dc_data_odd_addr_hi                     = dc_data_odd_addr_hi_r; 
  dc_data_odd_addr_hi[`npuarc_DC_PRED_BIT_RANGE] =  dc_pipe_ack_dd_odd_hi_r
                                            ? dc2_pred1
                                            : dc_data_odd_addr_hi_r[`npuarc_DC_PRED_BIT_RANGE]; 
end



//////////////////////////////////////////////////////////////////////////////
//
// Module Instantiation: Detection of single and double bit errors in Tag tag
//
/////////////////////////////////////////////////////////////////////////////

// wire declarations for the Tag part
//

wire                           dc4_dt_ecc_sb_error_even_lo;
wire                           dc4_dt_ecc_sb_error_even_hi;
wire                           dc4_dt_ecc_sb_error_odd_lo;
wire                           dc4_dt_ecc_sb_error_odd_hi;

wire                           dc4_dt_ecc_db_error_even_lo;
wire                           dc4_dt_ecc_db_error_even_hi;
wire                           dc4_dt_ecc_db_error_odd_lo;
wire                           dc4_dt_ecc_db_error_odd_hi;

wire [`npuarc_DC_TAG_TAG_DATA_RANGE]             dc4_dt_ecc_corrected_even_w0;
wire [`npuarc_DC_TAG_TAG_DATA_RANGE]             dc4_dt_ecc_corrected_even_w1;
wire [`npuarc_DC_TAG_TAG_DATA_RANGE]             dc4_dt_ecc_corrected_odd_w0;
wire [`npuarc_DC_TAG_TAG_DATA_RANGE]             dc4_dt_ecc_corrected_odd_w1;

reg  [`npuarc_DC_TRAM_RANGE]          dc4_dt_ecc_tag_even_w0_r;
reg  [`npuarc_DC_TRAM_RANGE]          dc4_dt_ecc_tag_even_w1_r;
reg  [`npuarc_DC_TRAM_RANGE]          dc4_dt_ecc_tag_odd_w0_r;
reg  [`npuarc_DC_TRAM_RANGE]          dc4_dt_ecc_tag_odd_w1_r;
reg  [`npuarc_DC_IDX_RANGE]           dc4_ecc_tag_addr_odd_r;    
reg  [`npuarc_DC_IDX_RANGE]           dc4_ecc_tag_addr_even_r;  

reg                           dc4_dt_ecc_error_cg0;
reg                           dc4_dt_ecc_error_valid_cg0;

wire [`npuarc_DC_TAG_SYNDROME_MSB:0]         syndrome_dt_0;
wire [`npuarc_DC_TAG_SYNDROME_MSB:0]         syndrome_dt_1;
wire [`npuarc_DC_TAG_SYNDROME_MSB:0]         syndrome_dt_2;
wire [`npuarc_DC_TAG_SYNDROME_MSB:0]         syndrome_dt_3;

reg [`npuarc_DC_IDX_RANGE]            dc3_ecc_tag_addr_odd;
reg [`npuarc_DC_IDX_RANGE]            dc3_ecc_tag_addr_even;
reg [3:0]                      dc4_dt_ecc_valid_r;

wire dc_tag_ecc_decoder_en_0;
wire dc_tag_ecc_decoder_en_1;
wire dc_tag_ecc_decoder_en_2;
wire dc_tag_ecc_decoder_en_3;
wire [`npuarc_DC_TAG_ECC_CODE_MSB:0] dc4_dt_corrected_ecc_even_w0;
wire [`npuarc_DC_TAG_ECC_CODE_MSB:0] dc4_dt_corrected_ecc_even_w1;
wire [`npuarc_DC_TAG_ECC_CODE_MSB:0] dc4_dt_corrected_ecc_odd_w0;
wire [`npuarc_DC_TAG_ECC_CODE_MSB:0] dc4_dt_corrected_ecc_odd_w1;
wire dc4_dt_double_error_even_lo;
wire dc4_dt_unknown_error_even_lo;
wire dc4_dt_double_error_even_hi;
wire dc4_dt_unknown_error_even_hi;
wire dc4_dt_double_error_odd_lo;
wire dc4_dt_unknown_error_odd_lo;
wire dc4_dt_double_error_odd_hi;
wire dc4_dt_unknown_error_odd_hi;


assign dc_tag_ecc_decoder_en_0 = !(~dc4_dt_ecc_valid_r[0] | ecc_dmp_disable | ((wa_restart_r | wa_restart_rr) & (~(aux_busy | dmu_evict_rd | dmu_evict_rd_r | aux_ecc_scrub_in_progress_r))));
assign dc4_dt_ecc_db_error_even_lo = dc4_dt_double_error_even_lo 
                                   | dc4_dt_unknown_error_even_lo 
								   ;
assign dc_tag_ecc_decoder_en_1 = !(~dc4_dt_ecc_valid_r[1] | ecc_dmp_disable | ((wa_restart_r | wa_restart_rr) & (~(aux_busy | dmu_evict_rd | dmu_evict_rd_r | aux_ecc_scrub_in_progress_r))));
assign dc4_dt_ecc_db_error_even_hi = dc4_dt_double_error_even_hi 
                                   | dc4_dt_unknown_error_even_hi
								   ;
assign dc_tag_ecc_decoder_en_2 = !(~dc4_dt_ecc_valid_r[2] | ecc_dmp_disable | ((wa_restart_r | wa_restart_rr) & (~(aux_busy | dmu_evict_rd | dmu_evict_rd_r | aux_ecc_scrub_in_progress_r))));
assign dc4_dt_ecc_db_error_odd_lo = dc4_dt_double_error_odd_lo 
                                  | dc4_dt_unknown_error_odd_lo
								  ;
assign dc_tag_ecc_decoder_en_3 = !(~dc4_dt_ecc_valid_r[3] | ecc_dmp_disable | ((wa_restart_r | wa_restart_rr) & (~(aux_busy | dmu_evict_rd | dmu_evict_rd_r | aux_ecc_scrub_in_progress_r))));
assign dc4_dt_ecc_db_error_odd_hi = dc4_dt_double_error_odd_hi 
                                  | dc4_dt_unknown_error_odd_hi
								  ;

npuarc_dc_tag_ecc_decoder u_dc_tag_ecc_decoder_0 (
  .clk                        (clk),
  .rst_a                      (rst_a),
  .enable                     (dc_tag_ecc_decoder_en_0),
  .data_in                    (dc3_dt_even_w0[`npuarc_DC_TAG_TAG_DATA_RANGE]),
  .data_in_r                  (dc4_dt_ecc_tag_even_w0_r[`npuarc_DC_TAG_TAG_DATA_RANGE]),
  .ecc_in                     (dc3_dt_even_w0[`npuarc_DC_TAG_TAG_ECC_RANGE]),
  .ecc_in_r                   (dc4_dt_ecc_tag_even_w0_r[`npuarc_DC_TAG_TAG_ECC_RANGE]),
  .ecc_error_cg               (dc4_dt_ecc_error_cg0),

  .syndrome_out               (syndrome_dt_0),
  .single_err                 (dc4_dt_ecc_sb_error_even_lo),
  .double_err                 (dc4_dt_double_error_even_lo),
  .unknown_err                (dc4_dt_unknown_error_even_lo),
  .ecc_out                    (dc4_dt_corrected_ecc_even_w0),
  .data_out                   (dc4_dt_ecc_corrected_even_w0[`npuarc_DC_TAG_TAG_DATA_RANGE])
);

npuarc_dc_tag_ecc_decoder u_dc_tag_ecc_decoder_1 (
  .clk                        (clk),
  .rst_a                      (rst_a),
  .enable                     (dc_tag_ecc_decoder_en_1),
  .data_in                    (dc3_dt_even_w1[`npuarc_DC_TAG_TAG_DATA_RANGE]),
  .data_in_r                  (dc4_dt_ecc_tag_even_w1_r[`npuarc_DC_TAG_TAG_DATA_RANGE]),
  .ecc_in                     (dc3_dt_even_w1[`npuarc_DC_TAG_TAG_ECC_RANGE]),
  .ecc_in_r                   (dc4_dt_ecc_tag_even_w1_r[`npuarc_DC_TAG_TAG_ECC_RANGE]),
  .ecc_error_cg               (dc4_dt_ecc_error_cg0),

  .syndrome_out               (syndrome_dt_1),
  .single_err                 (dc4_dt_ecc_sb_error_even_hi),
  .double_err                 (dc4_dt_double_error_even_hi),
  .unknown_err                (dc4_dt_unknown_error_even_hi),
  .ecc_out                    (dc4_dt_corrected_ecc_even_w1),
  .data_out                   (dc4_dt_ecc_corrected_even_w1[`npuarc_DC_TAG_TAG_DATA_RANGE])
);

npuarc_dc_tag_ecc_decoder u_dc_tag_ecc_decoder_2 (
  .clk                        (clk),
  .rst_a                      (rst_a),
  .enable                     (dc_tag_ecc_decoder_en_2),
  .data_in                    (dc3_dt_odd_w0[`npuarc_DC_TAG_TAG_DATA_RANGE]),
  .data_in_r                  (dc4_dt_ecc_tag_odd_w0_r[`npuarc_DC_TAG_TAG_DATA_RANGE]),
  .ecc_in                     (dc3_dt_odd_w0[`npuarc_DC_TAG_TAG_ECC_RANGE]),
  .ecc_in_r                   (dc4_dt_ecc_tag_odd_w0_r[`npuarc_DC_TAG_TAG_ECC_RANGE]),
  .ecc_error_cg               (dc4_dt_ecc_error_cg0),

  .syndrome_out               (syndrome_dt_2),
  .single_err                 (dc4_dt_ecc_sb_error_odd_lo),
  .double_err                 (dc4_dt_double_error_odd_lo),
  .unknown_err                (dc4_dt_unknown_error_odd_lo),
  .ecc_out                    (dc4_dt_corrected_ecc_odd_w0),
  .data_out                   (dc4_dt_ecc_corrected_odd_w0[`npuarc_DC_TAG_TAG_DATA_RANGE])
);

npuarc_dc_tag_ecc_decoder u_dc_tag_ecc_decoder_3 (
  .clk                        (clk),
  .rst_a                      (rst_a),
  .enable                     (dc_tag_ecc_decoder_en_3),
  .data_in                    (dc3_dt_odd_w1[`npuarc_DC_TAG_TAG_DATA_RANGE]),
  .data_in_r                  (dc4_dt_ecc_tag_odd_w1_r[`npuarc_DC_TAG_TAG_DATA_RANGE]),
  .ecc_in                     (dc3_dt_odd_w1[`npuarc_DC_TAG_TAG_ECC_RANGE]),
  .ecc_in_r                   (dc4_dt_ecc_tag_odd_w1_r[`npuarc_DC_TAG_TAG_ECC_RANGE]),
  .ecc_error_cg               (dc4_dt_ecc_error_cg0),

  .syndrome_out               (syndrome_dt_3),
  .single_err                 (dc4_dt_ecc_sb_error_odd_hi),
  .double_err                 (dc4_dt_double_error_odd_hi),
  .unknown_err                (dc4_dt_unknown_error_odd_hi),
  .ecc_out                    (dc4_dt_corrected_ecc_odd_w1),
  .data_out                   (dc4_dt_ecc_corrected_odd_w1[`npuarc_DC_TAG_TAG_DATA_RANGE])
);


//////////////////////////////////////////////////////////////////////////////////////////////
// 
// DC3 ecc single bit and double bit error indication and replay generation
//
//////////////////////////////////////////////////////////////////////////////////////////////
reg [3:0]                     dc4_dt_ecc_sb_error;
reg                           dc4_dt_ecc_sb_error_cg0;
reg [3:0]                     dc4_dt_ecc_sb_error_r;
reg [3:0]                     dc4_dt_ecc_db_error;

reg                           dc4_dt_ecc_replay;
reg                           dc4_dd_ecc_replay;
reg [3:0]                     dc3_dt_ecc_valid;


// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [`npuarc_DC_ADR_RANGE]           wa_dd_ecc_addr_r;
reg [3:0]                     dc4_data_mem_valid_r;
// leda NTL_CON32 on
reg [3:0]                     dc3_dt_ecc_bank_sel;

always @*
begin : dc3_dt_ecc_valid_PROC
  //
  // Capture the dc3 information required for validating the ecc error detected in DC4 or next cycle
  //
  dc3_dt_ecc_valid          =   ( ( { {2{dc3_dt_bank_sel_r[1]}}, {2{dc3_dt_bank_sel_r[0]}} }
                                    & {4{(dc3_ld_target_dc | dc3_st_target_dc)}}
                                    & {4{~(dmu_evict_rd | aux_dt_read)}}
                                    & {4{~(dc4_dt_ecc_replay | dc4_dd_ecc_replay)}}
                                    & {4{~(wa_restart_r)}}
                                    & {4{~dc3_mispred}}
                                    & {4{~(|dc3_dtlb_miss_r)}}
                                    & {4{~dc3_dtlb_ecc_error_r}}
                                    & {4{~dc3_dc_poisoned}}))
                              | (  ({4{(dmu_evict_rd | aux_dt_read)}} & dc_tag_read_r)
                                 & dc3_dt_ecc_bank_sel);

end


always @*
begin : dc4_dt_ecc_sb_error_PROC
  // ECC error detection and validation for Tag tag
  //
  dc4_dt_ecc_sb_error    = {dc4_dt_ecc_sb_error_odd_hi, dc4_dt_ecc_sb_error_odd_lo,
                            dc4_dt_ecc_sb_error_even_hi,dc4_dt_ecc_sb_error_even_lo }
                         ;
  
  dc4_dt_ecc_db_error    = {dc4_dt_ecc_db_error_odd_hi, dc4_dt_ecc_db_error_odd_lo,
                            dc4_dt_ecc_db_error_even_hi,dc4_dt_ecc_db_error_even_lo }
                         & {4{~aux_ecc_scrub_in_progress_r}}    
                         ; 

  dc3_ecc_tag_addr_even     =   dc3_mem_addr_even[`npuarc_DC_IDX_RANGE];
 
  dc3_ecc_tag_addr_odd      =   dc3_mem_addr_odd[`npuarc_DC_IDX_RANGE];
 
  dc3_ecc_tag_addr_even[`npuarc_DC_PRED_BIT_RANGE]  = dc3_dt_pred0_r;
  dc3_ecc_tag_addr_odd[`npuarc_DC_PRED_BIT_RANGE]   = dc3_dt_pred1_r;

  dc4_dt_ecc_replay      =   (|dc4_dt_ecc_sb_error          )
                           & (~(|dc4_dt_ecc_db_error      ) )
                           & (ca_load_r | ca_store_r        )
                           & (~(  (dmu_evict_rd & (|dc_tag_read_r))
                                | aux_dt_read))
                           & (dc4_target_r == `npuarc_DMP_TARGET_DC)
                           & (~wa_restart_r                 )
                           ;

  dc4_dt_ecc_error_cg0   =   (  dc3_target_dc
                              & x3_pass                              // Set
                              & (~dc4_dt_ecc_replay))
                         | (  ~(dc3_target_dc)
                             & dc4_target_dc
                             & ca_pass)                             // Clear
                         |  (wa_restart_r & (~(wa_dt_ecc_scrub_start_r | wa_dd_ecc_scrub_start_r | aux_ecc_scrub_in_progress_r | dmu_evict_rd | aux_busy))) 
                         |  ( ~(|dc4_dt_ecc_db_error)
                             & (  (dmu_evict_rd & (|dc_tag_read_r)) // For eviction
                                | aux_dt_read                       // For direct tag read
                               )
                            );  

  dc4_dt_ecc_error_valid_cg0   =   (  dc3_target_dc
                                    & x3_pass                              // Set
                                    & (~dc4_dc_ecc_replay_r))
                               | (  ~(dc3_target_dc)
                                   & dc4_target_dc
                                   & ca_pass)                             // Clear
                               |  (wa_restart_r & (~(wa_dt_ecc_scrub_start_r | wa_dd_ecc_scrub_start_r | aux_ecc_scrub_in_progress_r | dmu_evict_rd | aux_busy))) 
                               |  ( ~(|dc4_dt_ecc_db_error)
                                   & (  (dmu_evict_rd & (|dc_tag_read_r)) // For eviction
                                      | aux_dt_read                       // For direct tag read
                                     )
                                  )
                               | (~dc3_target_dc & (~dc4_target_dc) & (~dmu_evict_rd) & (~aux_dt_read) & wq_dmu_empty_r & (~(|dc4_dt_ecc_sb_error & (~aux_ecc_scrub_in_progress_r) )) & (~(wa_dt_ecc_scrub_start_r | wa_restart_rr | wa_dd_ecc_scrub_start_r)))  //Clear
                               ;

end

///////////////////////////////////////////////////////////////////////////////
//
// Flop the tag output for error correction
//
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DC_TAG_TAG_DATA_RANGE] dc4_dt_ecc_tag;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
// leda NTL_CON32 on
reg [1:0]                    dc4_dt_ecc_way_hot;
reg [3:0]                    dc4_dt_ecc_mem_valid;
//reg [3:0]                    dc3_dt_ecc_bank_sel;
reg [3:0]                    dc4_dt_ecc_bank_sel_r;
reg [3:0]                    dc4_dt_ecc_bank_sel;
reg                          dc4_dt_ecc_bank_sel_cg0;
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
//
// spyglass disable_block STARC05-2.8.1.3
// spyglass disable_block W398 
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, optimized by synthesizer.

always @*
begin : dc3_ecc_tag_PROC

  // To select from the incomming dc3 ld/st or from evict tag
  //
  dc3_dt_ecc_bank_sel =   (dmu_evict_rd)                          // Incase of Eviction
                        ? ( ((|dc_tag_active) & (~(|dc_tag_read)))        // in case of invalidation use the correct tag 
                           ? dc_tag_active 
                           : dc_tag_active_r)
                        : (   (aux_dt_read)           // Incase of Aux direct tag read 
                            ? (4'b1111)
                            : {{2{dc3_dt_bank_sel_r[1]}}, {2{dc3_dt_bank_sel_r[0]}}}  
                          )   
                        ;

  dc4_dt_ecc_sb_error_cg0 = dc4_dt_ecc_scrub_start
                          & (~(wa_dt_ecc_scrub_start_r | aux_ecc_scrub_in_progress_r));
 
  dc4_dt_ecc_bank_sel = (|dc4_dt_ecc_sb_error) ? (dc4_dt_ecc_bank_sel_r & dc4_dt_ecc_sb_error) : dc4_dt_ecc_bank_sel_r;


  dc4_dt_ecc_bank_sel_cg0 =  (  dc3_target_dc
                              & x3_pass
                              & (~dc4_dt_ecc_replay))
                          | (dmu_evict_rd & (|dc_tag_read_r))
                          | (dmu_evict_rd & (|dc_tag_active) & (~(|(dc_tag_read | dc_tag_read_r)))) // For eviction with invalidation
                          |  aux_dt_read
                          ;

  casez (dc4_dt_ecc_bank_sel)
  4'b???1:
  begin
    dc4_dt_ecc_tag         = ecc_dmp_disable ? dc4_dt_ecc_tag_even_w0_r[`npuarc_DC_TAG_TAG_DATA_RANGE] : dc4_dt_ecc_corrected_even_w0[`npuarc_DC_TAG_TAG_DATA_RANGE]; 
    dc4_dt_ecc_way_hot     = 2'b01;                        // Way 0
    dc4_dt_ecc_mem_valid   = 4'b0001;                      // Even
  end
  4'b??1?:
  begin
    dc4_dt_ecc_tag         = ecc_dmp_disable ? dc4_dt_ecc_tag_even_w1_r[`npuarc_DC_TAG_TAG_DATA_RANGE] : dc4_dt_ecc_corrected_even_w1[`npuarc_DC_TAG_TAG_DATA_RANGE];
    dc4_dt_ecc_way_hot     = 2'b10;                        // Way 1
    dc4_dt_ecc_mem_valid   = 4'b0001;                      // Even
  end  
  4'b?1??:
  begin
    dc4_dt_ecc_tag         = ecc_dmp_disable ? dc4_dt_ecc_tag_odd_w0_r[`npuarc_DC_TAG_TAG_DATA_RANGE] : dc4_dt_ecc_corrected_odd_w0[`npuarc_DC_TAG_TAG_DATA_RANGE];
    dc4_dt_ecc_way_hot     = 2'b01;                        // Way 0
    dc4_dt_ecc_mem_valid   = 4'b0010;                      // Odd
  end
  4'b1???:
  begin
    dc4_dt_ecc_tag         = ecc_dmp_disable ? dc4_dt_ecc_tag_odd_w1_r[`npuarc_DC_TAG_TAG_DATA_RANGE] : dc4_dt_ecc_corrected_odd_w1[`npuarc_DC_TAG_TAG_DATA_RANGE];
    dc4_dt_ecc_way_hot     = 2'b10;                        // Way 1
    dc4_dt_ecc_mem_valid   = 4'b0010;                      // Odd
  end 
  default:
  begin
    dc4_dt_ecc_tag         = ecc_dmp_disable ? dc4_dt_ecc_tag_even_w1_r[`npuarc_DC_TAG_TAG_DATA_RANGE] : dc4_dt_ecc_corrected_even_w1[`npuarc_DC_TAG_TAG_DATA_RANGE];
    dc4_dt_ecc_way_hot     = 2'b00;
    dc4_dt_ecc_mem_valid   = 4'b0000;  
  end
  endcase
end
// leda W547 on
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
//////////////////////////////////////////////////////////////////////////////
//
// Module instantiation: ECC Error Correction for Tag tag
//
/////////////////////////////////////////////////////////////////////////////
 

//////////////////////////////////////////////////////////////////////////////
//
// Module Instantiation: Detection of Single or Double Bit errors in Data data 
//
/////////////////////////////////////////////////////////////////////////////

wire                           dc4_dd_ecc_sb_error_even_lo;
wire                           dc4_dd_ecc_sb_error_even_hi;
wire                           dc4_dd_ecc_sb_error_odd_lo;
wire                           dc4_dd_ecc_sb_error_odd_hi;

wire                           dc4_dd_ecc_db_error_even_lo;
wire                           dc4_dd_ecc_db_error_even_hi;
wire                           dc4_dd_ecc_db_error_odd_lo;
wire                           dc4_dd_ecc_db_error_odd_hi;
reg [3:0]                      dc4_dd_ecc_valid_r;
wire[3:0]                      ecc_valid;
//wire [3:0]                     dc4_dt_sb;

wire                           i_parity_dd_00;
wire                           i_parity_dd_10;
reg                            i_parity_dd_0_r;
reg                            i_parity_dd_0_nxt;

wire [`npuarc_SYNDROME_MSB:0]         syndrome_dd_00;
wire [`npuarc_SYNDROME_MSB:0]         syndrome_dd_10;

reg  [`npuarc_SYNDROME_MSB:0]         syndrome_dd_0_r;
reg  [`npuarc_SYNDROME_MSB:0]         syndrome_dd_0_nxt;

wire                           i_parity_dd_01;
wire                           i_parity_dd_11;
reg                            i_parity_dd_1_r;
reg                            i_parity_dd_1_nxt;

wire [`npuarc_SYNDROME_MSB:0]         syndrome_dd_01;
wire [`npuarc_SYNDROME_MSB:0]         syndrome_dd_11;

reg  [`npuarc_SYNDROME_MSB:0]         syndrome_dd_1_r;
reg  [`npuarc_SYNDROME_MSB:0]         syndrome_dd_1_nxt;

wire                           i_parity_dd_02;
wire                           i_parity_dd_12;
reg                            i_parity_dd_2_r;
reg                            i_parity_dd_2_nxt;

wire [`npuarc_SYNDROME_MSB:0]         syndrome_dd_02;
wire [`npuarc_SYNDROME_MSB:0]         syndrome_dd_12;

reg  [`npuarc_SYNDROME_MSB:0]         syndrome_dd_2_r;
reg  [`npuarc_SYNDROME_MSB:0]         syndrome_dd_2_nxt;

wire                           i_parity_dd_03;
wire                           i_parity_dd_13;
reg                            i_parity_dd_3_r;
reg                            i_parity_dd_3_nxt;

wire [`npuarc_SYNDROME_MSB:0]         syndrome_dd_03;
wire [`npuarc_SYNDROME_MSB:0]         syndrome_dd_13;

reg  [`npuarc_SYNDROME_MSB:0]         syndrome_dd_3_r;
reg  [`npuarc_SYNDROME_MSB:0]         syndrome_dd_3_nxt;


assign ecc_valid = dc4_dd_ecc_valid_r & dc4_skid_ecc_valid_r;// & (~dc4_dt_sb);


npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_dd_00 (
  .data_in                       (dc3_dd_data_ecc0_even_lo[`npuarc_DATA_RANGE]),
  .ecc_code_in                   (dc3_dd_data_ecc0_even_lo[`npuarc_DC_WAY0_ECC_RANGE]),
  .i_parity                      (i_parity_dd_00                          ),  // SB error
  .syndrome                      (syndrome_dd_00                          )  // DB error
);

npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_dd_01 (
  .data_in                       (dc3_dd_data_ecc0_even_hi[`npuarc_DATA_RANGE]),
  .ecc_code_in                   (dc3_dd_data_ecc0_even_hi[`npuarc_DC_WAY0_ECC_RANGE]),
  .i_parity                      (i_parity_dd_01                          ),  // SB error
  .syndrome                      (syndrome_dd_01                          )  // DB error
);

npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_dd_02 (
  .data_in                       (dc3_dd_data_ecc0_odd_lo[`npuarc_DATA_RANGE]),
  .ecc_code_in                   (dc3_dd_data_ecc0_odd_lo[`npuarc_DC_WAY0_ECC_RANGE]),
  .i_parity                      (i_parity_dd_02                          ),  // SB error
  .syndrome                      (syndrome_dd_02                          )  // DB error
);
 
npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_dd_03 (
  .data_in                       (dc3_dd_data_ecc0_odd_hi[`npuarc_DATA_RANGE]),
  .ecc_code_in                   (dc3_dd_data_ecc0_odd_hi[`npuarc_DC_WAY0_ECC_RANGE]),
  .i_parity                      (i_parity_dd_03                          ),  // SB error
  .syndrome                      (syndrome_dd_03                          )  // DB error
);



npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_dd_10 (
  .data_in                       (dc3_dd_data_ecc1_even_lo[`npuarc_DATA_RANGE]),
  .ecc_code_in                   (dc3_dd_data_ecc1_even_lo[`npuarc_DC_WAY0_ECC_RANGE]),
  .i_parity                      (i_parity_dd_10                          ),  // SB error
  .syndrome                      (syndrome_dd_10                          )  // DB error
);

npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_dd_11 (
  .data_in                       (dc3_dd_data_ecc1_even_hi[`npuarc_DATA_RANGE]),
  .ecc_code_in                   (dc3_dd_data_ecc1_even_hi[`npuarc_DC_WAY0_ECC_RANGE]),
  .i_parity                      (i_parity_dd_11                          ),  // SB error
  .syndrome                      (syndrome_dd_11                          )  // DB error
);

npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_dd_12 (
  .data_in                       (dc3_dd_data_ecc1_odd_lo[`npuarc_DATA_RANGE]),
  .ecc_code_in                   (dc3_dd_data_ecc1_odd_lo[`npuarc_DC_WAY0_ECC_RANGE]),
  .i_parity                      (i_parity_dd_12                          ),  // SB error
  .syndrome                      (syndrome_dd_12                          )  // DB error
);
 
npuarc_alb_dmp_ecc_combined_a u_alb_dmp_ecc_combined_a_dd_13 (
  .data_in                       (dc3_dd_data_ecc1_odd_hi[`npuarc_DATA_RANGE]),
  .ecc_code_in                   (dc3_dd_data_ecc1_odd_hi[`npuarc_DC_WAY0_ECC_RANGE]),
  .i_parity                      (i_parity_dd_13                          ),  // SB error
  .syndrome                      (syndrome_dd_13                          )  // DB error
);

npuarc_alb_dmp_ecc_combined_b u_alb_dmp_ecc_combined_b_dd_0 (
  .data_in                        (dc4_dd_data_even_lo_r[`npuarc_DATA_RANGE]),  // Data bits
  .ecc_code_in                    (dc4_dd_data_even_lo_r[`npuarc_DC_WAY0_ECC_RANGE]),  //  ECC  bits
  .i_parity                       (i_parity_dd_0_r            ),  // SB error
  .syndrome                       (syndrome_dd_0_r            ),  // DB error
  .ecc_dmp_disable                (~ecc_valid[0] | ecc_dmp_disable | ((wa_restart_r | wa_restart_rr) & (~(aux_busy | dmu_evict_rd | dmu_evict_rd_r | aux_ecc_scrub_in_progress_r)))),  // ECC Disabled
  .sb_error                       (dc4_dd_ecc_sb_error_even_lo),  // SB error
  .db_error                       (dc4_dd_ecc_db_error_even_lo),  // DB error
  .data_out                       (dc4_ecc_data_even_lo       )   // Syndrome
);

npuarc_alb_dmp_ecc_combined_b u_alb_dmp_ecc_combined_b_dd_1 (
  .data_in                        (dc4_dd_data_even_hi_r[`npuarc_DATA_RANGE]),  // Data bits
  .ecc_code_in                    (dc4_dd_data_even_hi_r[`npuarc_DC_WAY0_ECC_RANGE]),  //  ECC  bits
  .i_parity                       (i_parity_dd_1_r            ),  // SB error
  .syndrome                       (syndrome_dd_1_r            ),  // DB error
  .ecc_dmp_disable                (~ecc_valid[1] | ecc_dmp_disable | ((wa_restart_r | wa_restart_rr) & (~(aux_busy | dmu_evict_rd | dmu_evict_rd_r | aux_ecc_scrub_in_progress_r)))),  // ECC Disabled
  .sb_error                       (dc4_dd_ecc_sb_error_even_hi),  // SB error
  .db_error                       (dc4_dd_ecc_db_error_even_hi),  // DB error
  .data_out                       (dc4_ecc_data_even_hi       )   // Syndrome
);

npuarc_alb_dmp_ecc_combined_b u_alb_dmp_ecc_combined_b_dd_2 (
  .data_in                        (dc4_dd_data_odd_lo_r[`npuarc_DATA_RANGE]),  // Data bits
  .ecc_code_in                    (dc4_dd_data_odd_lo_r[`npuarc_DC_WAY0_ECC_RANGE]),  //  ECC  bits
  .i_parity                       (i_parity_dd_2_r           ),  // SB error
  .syndrome                       (syndrome_dd_2_r           ),  // DB error
  .ecc_dmp_disable                (~ecc_valid[2] | ecc_dmp_disable | ((wa_restart_r | wa_restart_rr) & (~(aux_busy | dmu_evict_rd | dmu_evict_rd_r | aux_ecc_scrub_in_progress_r)))),  // ECC Disabled
  .sb_error                       (dc4_dd_ecc_sb_error_odd_lo),  // SB error
  .db_error                       (dc4_dd_ecc_db_error_odd_lo),  // DB error
  .data_out                       (dc4_ecc_data_odd_lo       )   // Syndrome
);

npuarc_alb_dmp_ecc_combined_b u_alb_dmp_ecc_combined_b_dd_3 (
  .data_in                        (dc4_dd_data_odd_hi_r[`npuarc_DATA_RANGE]),  // Data bits
  .ecc_code_in                    (dc4_dd_data_odd_hi_r[`npuarc_DC_WAY0_ECC_RANGE]),  //  ECC  bits
  .i_parity                       (i_parity_dd_3_r           ),  // SB error
  .syndrome                       (syndrome_dd_3_r           ),  // DB error
  .ecc_dmp_disable                (~ecc_valid[3] | ecc_dmp_disable | ((wa_restart_r | wa_restart_rr) & (~(aux_busy | dmu_evict_rd | dmu_evict_rd_r | aux_ecc_scrub_in_progress_r)))),  // ECC Disabled
  .sb_error                       (dc4_dd_ecc_sb_error_odd_hi),  // SB error
  .db_error                       (dc4_dd_ecc_db_error_odd_hi),  // DB error
  .data_out                       (dc4_ecc_data_odd_hi       )   // Syndrome
);

/*
alb_dmp_ecc_combined u_alb_dmp_ecc_combined_dd_0 (
  .data_in                       (dc4_dd_data_even_lo_r[`npuarc_DATA_RANGE]),
  .ecc_code_in                   (dc4_dd_data_even_lo_r[`npuarc_DC_WAY0_ECC_RANGE]),
  .ecc_dmp_disable               (~ecc_valid[0] | ecc_dmp_disable ),
  .sb_error                      (dc4_dd_ecc_sb_error_even_lo       ),
  .db_error                      (dc4_dd_ecc_db_error_even_lo       ),
  .data_out                      (dc4_ecc_data_even_lo              )
);

alb_dmp_ecc_combined u_alb_dmp_ecc_combined_dd_1 (
  .data_in                       (dc4_dd_data_even_hi_r[`npuarc_DATA_RANGE]),
  .ecc_code_in                   (dc4_dd_data_even_hi_r[`npuarc_DC_WAY0_ECC_RANGE]),
  .ecc_dmp_disable               (~ecc_valid[1] | ecc_dmp_disable ),
  .sb_error                      (dc4_dd_ecc_sb_error_even_hi       ),
  .db_error                      (dc4_dd_ecc_db_error_even_hi       ),
  .data_out                      (dc4_ecc_data_even_hi              )
);

alb_dmp_ecc_combined u_alb_dmp_ecc_combined_dd_2 (
  .data_in                       (dc4_dd_data_odd_lo_r[`npuarc_DATA_RANGE] ),
  .ecc_code_in                   (dc4_dd_data_odd_lo_r[`npuarc_DC_WAY0_ECC_RANGE]),
  .ecc_dmp_disable               (~ecc_valid[2] | ecc_dmp_disable),
  .sb_error                      (dc4_dd_ecc_sb_error_odd_lo        ),
  .db_error                      (dc4_dd_ecc_db_error_odd_lo        ),
  .data_out                      (dc4_ecc_data_odd_lo               )
);
 
alb_dmp_ecc_combined u_alb_dmp_ecc_combined_dd_3 (
  .data_in                       (dc4_dd_data_odd_hi_r[`npuarc_DATA_RANGE] ),
  .ecc_code_in                   (dc4_dd_data_odd_hi_r[`npuarc_DC_WAY0_ECC_RANGE]),
  .ecc_dmp_disable               (~ecc_valid[3] | ecc_dmp_disable),
  .sb_error                      (dc4_dd_ecc_sb_error_odd_hi        ),
  .db_error                      (dc4_dd_ecc_db_error_odd_hi        ),
  .data_out                      (dc4_ecc_data_odd_hi               )
);

*/

////////////////////////////////////////////////////////////////////////////////////////////
//
// Data bank selection based on hits or partial hits when there is a line cross
//
///////////////////////////////////////////////////////////////////////////////////////////

wire                                   dc3_dt_line_cross_and_hit;
wire                                   dc3_dt_no_line_cross_and_hit;
wire                                   dc3_even_addr_cross;
wire                                   dc3_odd_addr_cross;

assign dc3_dt_line_cross_and_hit    =  dc3_dt_line_cross_r & dc3_dt_hit;
assign dc3_dt_no_line_cross_and_hit = ~dc3_dt_line_cross_r & dc3_dt_hit;
assign dc3_even_addr_cross          =  (x3_mem_addr0_r[`npuarc_DC_TAG_BANK_ID] == 1'b0)
                                      & dc3_dt_bank_sel_r[0];
assign dc3_odd_addr_cross           =  (x3_mem_addr0_r[`npuarc_DC_TAG_BANK_ID] == 1'b1)
                                      & dc3_dt_bank_sel_r[0];

// Incase of partial hits, the ecc data data corretion should happen only for the 
// portion of the data that hits in the cache
//
// leda W547 off    
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
//
// spyglass disable_block STARC05-2.8.1.3
// spyglass disable_block W398 
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, optimized by synthesizer.
always @*
begin : dc3_ecc_data_bank_information_PROC
  // Incase of a hit in dc3, the data banks should be selected base on the full hits
  // or partial hits when there is no dt_line_cross
  //
  casez ({dc3_dt_line_cross_and_hit, dc3_dt_no_line_cross_and_hit})
  2'b1?:
  begin
    // When there is a hit and there is a line cross, check if both cache lines are in 
    // the cache (1)
    // 
    // If not above, then check whether they have a hit in either data bank odd (lo-hi) (2)
    // 
    // If not above, then check whether they have a hit in either data bank even(lo-hi) (3)
    //
    dc3_ecc_data_bank_sel =   ((|dc3_dt_even_hit_way_hot) & (|dc3_dt_odd_hit_way_hot))
                            ? (4'b1111)                                                // (1)
                            : (   (  (dc3_even_addr_cross & (|dc3_dt_even_hit_way_hot)) 
                                   | (dc3_odd_addr_cross  & (|dc3_dt_odd_hit_way_hot)))
                                ? (4'b1100)                                            // (2)
                                : (4'b0011)                                            // (3)
                              );
  end
  2'b?1:
  begin
    // When there is a hit and no line cross 
    //
    dc3_ecc_data_bank_sel = 4'b1111;
  end
  default:
  begin
    dc3_ecc_data_bank_sel = 4'b0000;
  end
  endcase
end
// leda W547 on
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
//////////////////////////////////////////////////////////////////////////////////////////////
//
// DC3 ecc single bit and double bit error indication and replay generation
//
//////////////////////////////////////////////////////////////////////////////////////////////

reg                               dc4_dd_ecc_error_cg0;
reg                               dc4_dd_ecc_error_valid_cg0;
reg [3:0]                         dc3_dd_ecc_valid;


//assign dc4_dt_sb = (dmu_evict_rd | dmu_evict_rd_r | aux_busy)
//                 ? 4'b0000
//                 : {4{(|dc4_dt_ecc_sb_error)}};

always @*
begin : dc3_dd_ecc_error_PROC
  // In case of a single bit error detected in X3, a dc3_dc_ecc_replay signal gets 
  // asserted, dc4_ecc_replay_cg0 is enabled and the dc3_dc_ecc_replay information
  // is available in dc4 as a flop (dc4_dd_ecc_replay_r)
  //
  // The dc3_ecc_error is generated by receiving the ecc_error_odd/even_lo/hi
  // signals from alb_dmp_ecc_detection module and they are qualified with
  // x3_load_r or partial store(dc3_rmw_r). Since error detection is done on
  // all the data banks(even_lo, even_hi, odd_lo, odd_high), some of the banks
  // dout might be XX(since they are not accessed). Hence this is qualified with
  // dc3_data_mem_valid_r signal. Thus only the required banks are selected,
  // similarly the error signals
  //

  dc4_dd_ecc_sb_error    =  (  (  {dc4_dd_ecc_sb_error_odd_hi,  dc4_dd_ecc_sb_error_odd_lo,
                                   dc4_dd_ecc_sb_error_even_hi, dc4_dd_ecc_sb_error_even_lo}
                               )
                             |  dc4_ecc_skid_sb_error_r)
                          ;

  dc4_dd_ecc_db_error    =  (  (  {dc4_dd_ecc_db_error_odd_hi,  dc4_dd_ecc_db_error_odd_lo,
                                   dc4_dd_ecc_db_error_even_hi, dc4_dd_ecc_db_error_even_lo}
                               )
                             |  dc4_ecc_skid_db_error_r)     
                         & {4{~aux_ecc_scrub_in_progress_r}}
//                           & (~dc4_dt_sb)    
                          ;

  dc4_dd_ecc_replay      =   (|dc4_dd_ecc_sb_error                   )
                           & (~(|dc4_dd_ecc_db_error)                )
                           & (dc4_ld_target_dc                       )
                           & (~wa_restart_r                          )
                           & (~(dmu_evict_rd | aux_dd_data_read))
                           & (~(dc4_dt_ecc_replay | (|dc4_dt_ecc_db_error)))
                           ;
  
  dc3_dd_ecc_valid       =  ( ({4{(dmu_evict_rd | aux_dd_data_read)}} & dc_data_read_r)
                              |(  ({4{dc3_ld_target_dc}}) 
                                & {4{dc3_dt_hit}}
                                & dc3_ecc_data_bank_sel
                                & {4{~(dmu_evict_rd | aux_dd_data_read)}}
                                & {4{~(dc4_dt_ecc_replay | dc4_dd_ecc_replay)}}
                                & dc3_data_mem_valid_r
                                & {4{~dc3_dc_poisoned}}
                                & {4{~dc3_mispred}}
                                & {4{~(|dc3_dtlb_miss_r)}}
                                & {4{~dc3_dtlb_ecc_error_r}}
                                & ({4{~wa_restart_r}})));

  dc4_dd_ecc_replay      =   (|dc4_dd_ecc_sb_error                   )
                           & (~(|dc4_dd_ecc_db_error)                )
                           & (dc4_ld_target_dc                       )
                           & (~wa_restart_r                          )
                           & (~(dmu_evict_rd | dmu_evict_rd_r | aux_busy))
                           & (~(dc4_dt_ecc_replay | (|dc4_dt_ecc_db_error)))
                           ;


  dc4_dd_ecc_error_cg0   =   (  dc3_target_dc
                              & x3_pass                              // for the incoming load/partial store
                              & (~dc4_dd_ecc_replay))                                       
                          | (  ~(dc3_target_dc)
                              & dc4_target_dc
                              & ca_pass)                             // Clear
                         |  (wa_restart_r & (~(wa_dt_ecc_scrub_start_r | wa_dd_ecc_scrub_start_r | aux_ecc_scrub_in_progress_r | dmu_evict_rd | aux_busy))) 
                         |  ( ~(|dc4_dd_ecc_db_error)
                             & (  (dmu_evict_rd | dmu_evict_rd_r)   // For eviction
                                | aux_busy              // For Aux read
                               )
                            ); 

  dc4_dd_ecc_error_valid_cg0   =   (  dc3_target_dc
                                    & x3_pass                              // for the incoming load/partial store
                                    & (~dc4_dc_ecc_replay_r))    
                               | (  ~(dc3_target_dc)
                                   & dc4_target_dc
                                   & ca_pass)                             // Clear
                               |  (wa_restart_r & (~(wa_dt_ecc_scrub_start_r | wa_dd_ecc_scrub_start_r | aux_ecc_scrub_in_progress_r | dmu_evict_rd | aux_busy))) 
                               |  ( ~(|dc4_dd_ecc_db_error)
                                   & (  (dmu_evict_rd | dmu_evict_rd_r)   // For eviction
                                      | aux_busy      // For Aux read
                                     )
                                  )
                               | (~dc3_target_dc & (~dc4_target_dc) & (~dmu_evict_rd) & (~aux_dt_read) & (~(wa_dt_ecc_scrub_start_r | wa_restart_rr | wa_dd_ecc_scrub_start_r)))  //Clear
                               ;

end

/////////////////////////////////////////////////////////////////////////////////////////////////
//
// DC4 information used to set up the data data scrubbing through aux interface
//
////////////////////////////////////////////////////////////////////////////////////////////////

reg [`npuarc_DC_ADR_RANGE]dc4_dd_ecc_addr;
reg [1:0]          dc4_dd_ecc_way_hot;
reg [1:0]          wa_dd_ecc_way_hot_r;
reg [3:0]          dc4_dd_ecc_mem_valid;
reg [3:0]          wa_dd_ecc_mem_valid_r;
reg                wa_dd_ecc_mem_valid_cg0;
reg [1:0]          dc4_dt_even_hit_way_hot_r;
reg [1:0]          dc4_dt_odd_hit_way_hot_r;

assign dc4_data_bank_cross =   dc4_data_mem_valid_r[3]
                             & dc4_data_mem_valid_r[0];

always @*
begin : dc4_dd_aux_information_PROC
  // Setting up the aux address, way and data bank information for scrubbing the data
  //
  dc4_dd_ecc_addr         = {`npuarc_DC_ADDR_BITS{1'b0}};
  dc4_dd_ecc_way_hot      = 2'b00;
  dc4_dd_ecc_mem_valid    = 4'b0000;
// spyglass disable_block W415a
// SMD: signal assigned multiple times in the same always block
// SJ:  overwriting default assignments
  if (    dc4_data_bank_cross & dc4_dt_hit_r
       & (dc4_dd_ecc_sb_error[3] | dc4_dd_ecc_sb_error[2]) )
  begin
    // There is a line cross, and an error in the bank1,
    // then use ca_mem_addr0_r
    //
    dc4_dd_ecc_addr      =    ca_mem_addr0_r[`npuarc_DC_ADR_RANGE];
    dc4_dd_ecc_way_hot   =   (ca_mem_addr0_r[`npuarc_DC_TAG_BANK_ID] == 1'b0)
                           ?  dc4_dt_even_hit_way_hot_r
                           :  dc4_dt_odd_hit_way_hot_r
                           ;
    dc4_dd_ecc_mem_valid = dc4_dd_ecc_sb_error & 4'b1100;
  end
  else if (    dc4_data_bank_cross & dc4_dt_hit_r  
        & (dc4_dd_ecc_sb_error[0] | dc4_dd_ecc_sb_error[1]) )
  begin
    // There is a line cross, and an error in the bank0,
    // then use ca_mem_addr1_r
    //
    dc4_dd_ecc_addr      =    dc4_mem_addr1_r[`npuarc_DC_ADR_RANGE];
    dc4_dd_ecc_way_hot   =   (dc4_mem_addr1_r[`npuarc_DC_TAG_BANK_ID] == 1'b0)
                           ?  dc4_dt_even_hit_way_hot_r
                           :  dc4_dt_odd_hit_way_hot_r
                           ;
    dc4_dd_ecc_mem_valid = dc4_dd_ecc_sb_error & 4'b0011; 
  end
  else if ((~dc4_data_bank_cross) & dc4_dt_hit_r)
  begin
    // There is no line cross, and an error in the bank0 or bank1,
    // then use ca_mem_addr0_r
    //
    dc4_dd_ecc_addr      =    ca_mem_addr0_r[`npuarc_DC_ADR_RANGE];
    dc4_dd_ecc_way_hot   =   (ca_mem_addr0_r[`npuarc_DC_TAG_BANK_ID] == 1'b0)
                           ?  dc4_dt_even_hit_way_hot_r
                           :  dc4_dt_odd_hit_way_hot_r
                           ;
    dc4_dd_ecc_mem_valid = dc4_dd_ecc_sb_error & 4'b1111;
  end

  dc4_dd_ecc_addr[`npuarc_DC_PRED_BIT_RANGE] =  (|dc4_dd_ecc_sb_error[3:2])
                                       ? dc4_dd_pred1_r
                                       : dc4_dd_pred0_r;     
// spyglass enable_block W415a  
  // dc4 cgo for dc4_aux_ecc_addr, dc4_ecc_data_way_hot and dc4_ecc_data_mem_valid
  //
  wa_dd_ecc_mem_valid_cg0 = dc4_dd_ecc_replay
                          & (~wa_restart_r); 
end


// Incase of ECC, always the corrected data goes gout to DMU
//
assign dc_rd_data_nxt = ecc_dmp_disable 
                      ? {dc4_dd_data_odd_hi_r[`npuarc_DATA_RANGE],
                         dc4_dd_data_odd_lo_r[`npuarc_DATA_RANGE],
                         dc4_dd_data_even_hi_r[`npuarc_DATA_RANGE],
                         dc4_dd_data_even_lo_r[`npuarc_DATA_RANGE]}
                      : {dc4_ecc_data_odd_hi,
                         dc4_ecc_data_odd_lo,
                         dc4_ecc_data_even_hi,
                         dc4_ecc_data_even_lo};
  
/////////////////////////////////////////////////////////////////////////////////////////////////
//
// DC4 Aux information that is used to scrub tag tag or data data
//
////////////////////////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DC_ADR_RANGE]           aux_ecc_addr;
reg [`npuarc_DC_TAG_TAG_DATA_RANGE]  aux_ecc_tag;
reg [1:0]                     aux_ecc_dt_way_hot;
reg [3:0]                     aux_ecc_data_mem_valid;

reg                           aux_dt_ecc_bank_sel;
reg                           aux_dt_ecc_bank_sel_r;
reg                           wa_dc_ecc_error_cg0;

always @*
begin : dc4_aux_information_PROC
  // First we have to make sure that the tag has no error.
  // Hence any error in Tag should be scrubbed before going to data data
  //
  aux_dt_ecc_bank_sel  =   (  (|dc4_dt_ecc_sb_error) 
                            & (~wa_dd_ecc_scrub_start_r))
                         | aux_dt_read;
   
  wa_dc_ecc_error_cg0  =   dc4_dc_ecc_replay_r
                         | aux_dt_read;

  case (aux_dt_ecc_bank_sel_r)
  1'b1:
  begin
    aux_ecc_addr           = (|dc4_dt_ecc_sb_error[1:0]) ? {dc4_ecc_tag_addr_even_r, {3{1'b0}}} : {dc4_ecc_tag_addr_odd_r, {3{1'b0}}};
    aux_ecc_tag            = dc4_dt_ecc_tag[`npuarc_DC_TAG_TAG_DATA_RANGE];
    aux_ecc_dt_way_hot     = dc4_dt_ecc_way_hot;
    aux_ecc_data_mem_valid = dc4_dt_ecc_mem_valid;
  end
  default:
  begin
    aux_ecc_addr           = wa_dd_ecc_addr_r;
    aux_ecc_tag            = dc4_dt_ecc_tag[`npuarc_DC_TAG_TAG_DATA_RANGE]; 
    aux_ecc_dt_way_hot     = wa_dd_ecc_way_hot_r;
    aux_ecc_data_mem_valid = wa_dd_ecc_mem_valid_r;
  end
  endcase 
end
    
////////////////////////////////////////////////////////////////////////////////////////
//
// Initiating the Scrubbing
//
///////////////////////////////////////////////////////////////////////////////////////
wire                           dc4_dt_wq_dmu_empty;
wire                           dc4_dd_wq_dmu_empty;
assign dc4_dt_wq_dmu_empty =   ( (  (dmu_empty & wq_empty)  // in case of uop 
                                   |(ca_uop_inst_r & dmu_empty & (~wq_empty)))
                                 & (~(dc_tag_odd_we_r | dc_tag_even_we_r)) )
                             ; 

assign dc4_dd_wq_dmu_empty =   ( (  (dmu_empty & wq_empty)  // in case of uop
                                   |(ca_uop_inst_r & dmu_empty & (~wq_empty)))
                                 & (~(  dc_data_odd_we_hi_r  | dc_data_odd_we_lo_r
                                      | dc_data_even_we_hi_r | dc_data_even_we_lo_r)))
                              ;
   
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
//
// spyglass disable_block STARC05-2.8.1.3
// spyglass disable_block W398 
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, optimized by synthesizer.
always @*
begin : dc4_dc_ecc_scrub_start_PROC
  // Only initiate an AUX instruction when the following condition is satisfied
  // This makes sure that the error line is in the cache and no pending WQ or DMU
  // transactions. (1)
  // WQ and DMU empty signal should be checked in DC3 and DC4 
  // Since we already accessed the memories, in DC3 check for wq and dmu empty signals,
  // When doing so there may be a pending load or store might be in CA, hence check for 
  // the empty signals in DC3 and DC4
  // Do not initiate the scrub when there is a wa_restart_r (2)
  //

  dt_ecc_scrub =   (  (    dc4_dt_ecc_replay
                       &   dc4_dt_wq_dmu_empty        // (1)
                       &   (~dc4_wq_skid_replay_r)     
                       & (~wa_restart_r)))            // (2)
                 & (~wa_dt_ecc_scrub_start_r)        
                 ;

  dd_ecc_scrub =     dc4_dd_ecc_replay
                  & (~(|dc4_ecc_skid_sb_error_r))
                  &  (~dc4_wq_skid_replay_r)
                  &  dc4_dd_wq_dmu_empty              // (1)
                  & (~wa_restart_r)                   // (2)
                  & (~wa_dt_ecc_scrub_start_r)
                  & (~wa_dd_ecc_scrub_start_r)
                  ;
   
  // Lets set the priority, Scrub the tag tag first before scrubbing the data data
  // 
  casez ({dt_ecc_scrub, dd_ecc_scrub})
  2'b1?:
  begin
    dc4_dt_ecc_scrub_start = 1'b1;
    dc4_dd_ecc_scrub_start = 1'b0;
  end
  2'b?1:
  begin
    dc4_dt_ecc_scrub_start = 1'b0;
    dc4_dd_ecc_scrub_start = 1'b1;
  end
  default:
  begin
    dc4_dt_ecc_scrub_start = 1'b0;
    dc4_dd_ecc_scrub_start = 1'b0;
  end
  endcase
end
// leda W547 on
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
always @*
begin : dc4_dc_ecc_replay_PROC

  dc4_dc_ecc_replay_r =    dc4_dt_ecc_replay 
                         | dc4_dd_ecc_replay
                         ;
end

always @*
begin : dc4_dc_ecc_db_error_PROC
  dc4_dc_ecc_db_error   =   ( (|dc4_dd_ecc_db_error) | (|dc4_dt_ecc_db_error))
                          & (~(dmu_evict_rd | dmu_evict_rd_r | aux_dd_data_read | aux_dt_read))
                          & dc4_target_dc
//                          & (~dc4_dc_ecc_replay_r)
                          & (~wa_replay_r)
                          & (~ecc_dmp_disable & (~ecc_dmp_expn_disable))  
                          ;
  dc4_dc_dt_ecc_db_error   =  (   1'b0
                               | (|dc4_dt_ecc_db_error)
                              ) 
                            & (~ecc_dmp_disable)
                            ;

  dc4_dc_dd_ecc_db_error   =  (   1'b0
                               | (|dc4_dd_ecc_db_error)
                              )
                            & (~ecc_dmp_disable)   
                            ;
end
//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Result bus interface     
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc_rb_req_PROC
  // Request the result bus in DC3
  //
  dc_rb_req      =  x3_load_r 
                  & x3_pass 
                  & ca_enable 
                  & (dc3_target_r == `npuarc_DMP_TARGET_DC);
       
  
  dc_rb_bank0_lo_r = dc4_dd_data_even_lo_r;
  dc_rb_bank0_hi_r = dc4_dd_data_even_hi_r;
  
  dc_rb_bank1_lo_r = dc4_dd_data_odd_lo_r;
  dc_rb_bank1_hi_r = dc4_dd_data_odd_hi_r;
end

//////////////////////////////////////////////////////////////////////////////
// @ Asynchronous process defining hit information for the fast byp ctl
//                                                                           
//////////////////////////////////////////////////////////////////////////////
reg dc_dt_hit_prel;

always @*
begin : dc_dt_hit_PROC
  // This only includes hit in the data tag. Hit in the MQ is not included.
  // The fast byp data always come from the data memory
  //
  dc_dt_hit_prel = (  (dc3_dt_bank_sel_r[0] & (| dc3_dt_even_hit_way_hot))
                    | (dc3_dt_bank_sel_r[1] & (| dc3_dt_odd_hit_way_hot)))
                   & (~dc3_mispred)
                   ;
  dc_dt_hit      = dc_dt_hit_prel & (~dc3_dc_poisoned);                 
end

always @*
begin : dc3_mq_addr_match_PROC
  //
  //
  // Look for addr match with DC3 and MQ
  //
  // This is to make sure that the instruction in DC3 and DC4 and top of MQ are
  // pointing to the same cache line, so that we do not have to poison or replay the
  // DC3 instruction.
  //
  dc3_addr_match0  = (x3_mem_addr0_r[`npuarc_DC_LBUF_RANGE]   == mq_addr[`npuarc_DC_LBUF_RANGE])
                   & dc3_target_dc;
  dc3_addr_match1  = (dc3_mem_addr1_r[`npuarc_DC_LBUF_RANGE]  == mq_addr[`npuarc_DC_LBUF_RANGE])
                   & dc3_dt_line_cross_r
                   & dc3_target_dc;


  dc3_mq_addr_match  = (x3_load_r | x3_store_r)
                     & (~dmu_empty)
                     & mq_valid
                     & (  dc3_addr_match0
                        | dc3_addr_match1)
                     & (dc3_target_r == `npuarc_DMP_TARGET_DC)
                     & dc3_dt_miss
                     & (~dc3_dc_poisoned)       
                     & (~dc3_dt_hit);
end

     
always @*
begin : dc4_mq_addr_match_PROC
  //
  //
  // Look for addr match with DC4 and MQ
  //
  dc4_addr_match0  = (ca_mem_addr0_r[`npuarc_DC_LBUF_RANGE]   == mq_addr[`npuarc_DC_LBUF_RANGE])
                   & dc4_target_dc; 
  dc4_addr_match1  = (dc4_mem_addr1_r[`npuarc_DC_LBUF_RANGE]  == mq_addr[`npuarc_DC_LBUF_RANGE])
                   & dc4_dt_line_cross_r
                   & dc4_target_dc; 

  dc4_mq_addr_match  = (ca_load_r | ca_store_r)
                     & (~dmu_empty)
                     & mq_valid
                     & (  dc4_addr_match0
                        | dc4_addr_match1)
                     & (dc4_target_r == `npuarc_DMP_TARGET_DC)
                     & (~dc4_dt_hit_r)
                     & dc4_dt_miss_r;

  // Look for set match with DC4 and DMU
  //
  dc4_mq_set_match  = (ca_load_r | ca_store_r)
                    & (~dmu_empty)
                    & dmu_dc_read
                    & dc4_set_match
                    & (~( dc4_addr_match0
                         | (dc4_addr_match1 & dc4_dt_line_cross_r)))
                    & (dc4_target_r == `npuarc_DMP_TARGET_DC)
                    & dc4_dt_miss_r;
end  


//////////////////////////////////////////////////////////////////////////////
//                                                                           
//  Module instantiation: clockgates 
//                                                                           
//////////////////////////////////////////////////////////////////////////////

npuarc_clkgate u_clkgate_tag_even_w0 (
  .clk_in            (clk              ),
  .clock_enable      (dc_tag_even_cs_r[0]),
  .clk_out           (clk_tag_even_w0)
);

npuarc_clkgate u_clkgate_tag_odd_w0 (
  .clk_in            (clk              ),
  .clock_enable      (dc_tag_odd_cs_r[0]),
  .clk_out           (clk_tag_odd_w0)
);  


npuarc_clkgate u_clkgate_tag_even_w1 (
  .clk_in            (clk              ),
  .clock_enable      (dc_tag_even_cs_r[1]),
  .clk_out           (clk_tag_even_w1)
);

npuarc_clkgate u_clkgate_tag_odd_w1 (
  .clk_in            (clk              ),
  .clock_enable      (dc_tag_odd_cs_r[1]),
  .clk_out           (clk_tag_odd_w1)
);  


npuarc_clkgate u_clkgate_data_even_lo (
  .clk_in            (clk              ),
  .clock_enable      (dc_data_even_cs_lo_r),
  .clk_out           (clk_data_even_lo)
);

npuarc_clkgate u_clkgate_data_even_hi (
  .clk_in            (clk              ),
  .clock_enable      (dc_data_even_cs_hi_r),
  .clk_out           (clk_data_even_hi)
);

npuarc_clkgate u_clkgate_data_odd_lo (
  .clk_in            (clk              ),
  .clock_enable      (dc_data_odd_cs_lo_r),
  .clk_out           (clk_data_odd_lo    )
);

npuarc_clkgate u_clkgate_data_odd_hi (
  .clk_in            (clk              ),
  .clock_enable      (dc_data_odd_cs_hi_r),
  .clk_out           (clk_data_odd_hi    )
);


npuarc_alb_dmp_status u_alb_dmp_status (
  .dc_status0_write_even    (dc_status0_write_even  ),   
  .dc_status0_even_addr     (dc_status0_even_addr   ),    
  .dc_status0_even_wem      (dc_status0_even_wem    ),     
  .dc_status0_even_way_hot  (dc_status0_even_way_hot), 
  .dc_status0_even_dirty    (dc_status0_even_dirty  ),   
  .dc_status0_even_lru      (dc_status0_even_lru    ),     

  .dc_status0_write_odd     (dc_status0_write_odd   ),    
  .dc_status0_odd_addr      (dc_status0_odd_addr    ),     
  .dc_status0_odd_wem       (dc_status0_odd_wem     ),      
  .dc_status0_odd_way_hot   (dc_status0_odd_way_hot ),  
  .dc_status0_odd_dirty     (dc_status0_odd_dirty   ),    
  .dc_status0_odd_lru       (dc_status0_odd_lru     ),      

  .dc_status1_read          (dc_status1_read        ), 
  .dc_status1_write         (dc_status1_write       ),
  .dc_status1_addr          (dc_status1_addr        ), 
  .dc_status1_odd           (dc_status1_odd         ),  
  .dc_status1_wem           (dc_status1_wem         ),  
  .dc_status1_way_hot       (dc_status1_way_hot     ),      
  .dc_status1_lock          (dc_status1_lock        ), 
  .dc_status1_dirty         (dc_status1_dirty       ),
  .dc_status1_lru           (dc_status1_lru         ),  

  .status1_lru_even_r       (status1_lru_even       ),
  .status1_lock_even_r      (status1_lock_even      ),  
  .status1_dirty_even_r     (status1_dirty_even     ),  

  .status1_lru_odd_r        (status1_lru_odd        ), 
  .status1_lock_odd_r       (status1_lock_odd       ),
  .status1_dirty_odd_r      (status1_dirty_odd      ),       

  .clk                      (clk                    ),             
  .rst_a                    (rst_a                  )             
);


//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Module instantiation: DMU         
//                                                                           
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_dmu u_alb_dmp_dmu (

  .clk                    (clk_dmu             ),    
  .rst_a                  (rst_a               ),    

  .ecc_dmp_disable        (ecc_dmp_disable     ), 

  .dc3_dt_line_cross_r    (dc3_dt_line_cross_r ),  
  .dc4_dt_line_cross_r    (dc4_dt_line_cross_r ),  

  .dc3_target_r           (dc3_target_r        ),
  .dc4_target_r           (dc4_target_r        ),

  .x3_valid_r             (x3_valid_r          ),     
  .x3_pass                (x3_pass             ),     
  .x3_load_r              (x3_load_r           ),     
  .x3_store_r             (x3_store_r          ),     
  .x3_size_r              (x3_size_r           ),     
  .x3_mem_addr0_r         (x3_mem_addr0_r      ),  
  .dc3_mem_addr1_r        (dc3_mem_addr1_r     ), 
  
  .mq_addr_even_hit       (mq_addr_even_hit    ),
  .mq_addr_odd_hit        (mq_addr_odd_hit     ), 
  .dmu_evict_hit          (dmu_evict_hit       ),

  .ca_valid_r             (ca_valid_r          ), 
  .ca_pass                (ca_pass             ), 
  .ca_enable              (ca_enable           ), 
  .ca_load_r              (ca_load_r           ), 
  .ca_pref_r              (ca_pref_r           ), 
  .ca_pref_l2_r           (ca_pref_l2_r        ), 
  .ca_prefw_r             (ca_prefw_r          ), 
  .ca_pre_alloc_r         (ca_pre_alloc_r      ),
  .dc4_pref_bad_r         (dc4_pref_bad_r      ),  
  .ca_store_r             (ca_store_r          ), 
  .ca_locked_r            (ca_locked_r         ),
  .ca_sex_r               (ca_sex_r            ), 
  .ca_userm_r             (ca_userm_r          ), 
  .ca_size_r              (ca_size_r           ), 
  .ca_mem_addr0_r         (ca_mem_addr0_r      ), 
  .dc4_mem_addr1_r        (dc4_mem_addr1_r     ), 
  .ca_wr_data_r           (ca_wr_data_r        ), 
  .dc4_hit_even_way_hot_r (dc4_hit_even_way_hot_r),    
  .dc4_hit_odd_way_hot_r  (dc4_hit_odd_way_hot_r),  
  .dc4_dt_miss_even_r     (dc4_dt_miss_even_r   ),
  .dc4_dt_miss_odd_r      (dc4_dt_miss_odd_r    ),
  .dc4_dt_miss_r          (dc4_dt_miss_r        ),

  .dc4_scond_go           (dc4_scond_go         ),
  .wq_scond_entry         (wq_scond_entry       ),
  
  .dmu_empty              (dmu_empty           ),
  .mq_one_or_less_entry   (mq_one_or_less_entry),
  .dmu_dc_idle            (dmu_dc_idle         ),        
  .dmu_poison_stuck       (dmu_poison_stuck    ), 
  .dmu_mq_full            (dmu_mq_full         ),      
  .dmu_lsmq_full          (dmu_lsmq_full       ),
  .lsmq_two_empty         (lsmq_two_empty      ),
  .dc4_lsmq_write         (dc4_lsmq_write      ),
  .dc4_lsmq_nomatch_replay(dc4_lsmq_nomatch_replay),
  .lsmq_match0            (lsmq_match0         ),
  .lsmq_match1            (lsmq_match1         ),
  .dmu_wr_pending         (dmu_wr_pending      ),    
   
  .dd_busy_nxt            (dd_busy_nxt         ),
  .dc_pipe_busy           (dc_pipe_busy        ),
  
  .dmu_req_dt_even        (dmu_req_dt_even     ), 
  .dmu_req_dt_odd         (dmu_req_dt_odd      ), 
  .dmu_dt_odd_sel         (dmu_dt_odd_sel      ), 
  .dmu_dt_way_hot         (dmu_dt_way_hot      ), 
  .dmu_dt_we              (dmu_dt_we           ),      
  .dmu_dt_wem             (dmu_dt_wem          ),    
  .dmu_dt_addr            (dmu_dt_addr         ),    
  .dmu_dt_valid           (dmu_dt_valid        ),   
  .dmu_dt_tag             (dmu_dt_tag          ),     
  
  .dmu_req_ds             (dmu_req_ds          ),     
  .dmu_ds_odd_sel         (dmu_ds_odd_sel      ),  
  .dmu_ds_we              (dmu_ds_we           ),      
  .dmu_ds_wem             (dmu_ds_wem          ),     
  .dmu_ds_way_hot         (dmu_ds_way_hot      ), 
  .dmu_ds_dirty           (dmu_ds_dirty        ), 
  .dmu_ds_lock            (dmu_ds_lock         ), 
  .dmu_ds_lru             (dmu_ds_lru          ),  
  .dmu_ds_addr            (dmu_ds_addr         ), 
  
  .dc3_ds_lru             (dc3_ds_lru          ), 
  .dc3_ds_lock            (dc3_ds_lock         ), 
  .dc3_ds_dirty           (dc3_ds_dirty        ), 
  
  .dmu_req_dd             (dmu_req_dd          ),    
  .dmu_evict_rd           (dmu_evict_rd        ),   
  .dmu_dd_way_hot         (dmu_dd_way_hot      ), 
  .dmu_dd_we              (dmu_dd_we           ),  
  .dmu_dd_addr            (dmu_dd_addr         ),  

  .dc3_dt_tag             (dc3_dt_tag          ),
  .dc3_dt_val             (dc3_dt_val          ),
  .dc4_dt_ecc_corrected   (dc4_dt_ecc_tag     ),
  .dc4_dc_dt_ecc_db_error (dc4_dc_dt_ecc_db_error), 
  .dc4_dc_dd_ecc_db_error (dc4_dc_dd_ecc_db_error), 
  .dc4_dd_data            (dc4_dd_data          ),  
  .dc3_mq_addr_match      (dc3_mq_addr_match    ),
  .dc4_mq_addr_match      (dc4_mq_addr_match    ),
  .dc4_mq_set_match       (dc4_mq_set_match     ),
  .lbuf_rd_data           (lbuf_rd_data         ), 
  .dmu_dc_start           (dmu_dc_start         ),
  .dmu_dc_ready           (dmu_dc_ready         ),
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Outputs connected to floating net
// SJ: Not all bits of address used in this design
  .mq_addr                (mq_addr              ), 
// spyglass enable_block UnloadedOutTerm-ML
  .mq_valid               (mq_valid             ),
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Outputs connected to floating net
// SJ: Not all bits of address used in this design
  .dmu_line_addr          (dmu_line_addr        ),
// spyglass enable_block UnloadedOutTerm-ML
  .dmu_dc_read            (dmu_dc_read          ), 
  .dmu_dc_done            (dmu_dc_done          ),  
  
  .dmu_ack_ok             (dmu_ack_ok           ),   
  
  
  .cb_cmd_valid           (cb_cmd_valid         ),    
  .cb_cmd_accept          (cb_cmd_accept        ),   
  .cb_cmd_read            (cb_cmd_read          ),    
  .cb_cmd_addr            (cb_cmd_addr          ),    
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
  
  .rf_cmd_valid           (rf_cmd_valid         ), 
  .rf_cmd_excl            (rf_cmd_excl          ),
  .rf_cmd_accept          (rf_cmd_accept        ), 
  .rf_cmd_read            (rf_cmd_read          ),   
  .rf_cmd_addr            (rf_cmd_addr          ),   
  .rf_cmd_prot            (rf_cmd_prot          ),   
  .rf_cmd_wrap            (rf_cmd_wrap          ),   
  .rf_cmd_burst_size      (rf_cmd_burst_size    ),

  .rf_rd_valid            (rf_rd_valid          ), 
  .rf_rd_last             (rf_rd_last           ), 
  .rf_err_rd              (rf_err_rd            ), 
  .rf_rd_data             (rf_rd_data           ), 
  .rf_rd_accept           (rf_rd_accept         ),

  .dc_pct_dcm             (dc_pct_dcm           ),  
  .dc_pct_dclm            (dc_pct_dclm          ),  
  .dc_pct_dcsm            (dc_pct_dcsm          ),  

   
  .mq_rb_req              (mq_rb_req            ), 
  .mq_rb_err              (mq_rb_err            ), 
  .ca_grad_tag            (ca_grad_tag          ),
  .mq_rb_ack              (mq_rb_ack            ),
  
  .mq_bank_sel            (mq_bank_sel          ), 
  .mq_rb_tag              (mq_rb_tag            ), 
  .mq_rb_addr             (mq_rb_addr           ), 
  .mq_sex                 (mq_sex               ), 
  .mq_size                (mq_size              ), 
  .mq_userm               (mq_userm             ), 
  .mq_rb_data             (mq_rb_data           ), 
  .mq_wr_err              (mq_wr_err            ), 
  
  .mq_flush_err_req       (mq_flush_err_req     ), 
  .mq_flush_err_addr      (mq_flush_err_addr    ), 
  .mq_flush_err_ack       (mq_flush_err_ack     ), 

  .rf_err_req             (rf_err_req          ),        
  .rf_err_addr            (rf_err_addr         ),       

  .aux_mq_write           (aux_mq_write        ), 
  .aux_mq_flush           (aux_mq_flush        ), 
  .aux_mq_purge           (aux_mq_purge        ), 
  .aux_mq_refill          (aux_mq_refill       ), 
  .aux_mq_way             (aux_mq_way          ), 
  .aux_mq_addr            (aux_mq_addr         ),
  .aux_mq_lru_dirty       (aux_mq_lru_dirty    ),
  .lb_err_r               (lb_err_r            ),
  .mq_empty               (mq_empty            ), 
  .cb_full                (cb_full             )
);

npuarc_alb_dmp_dcache_aux u_alb_dmp_dcache_aux (

  .clk                      (clk              ),    
  .rst_a                    (rst_cache_a      ),  
  .dbg_cache_rst_disable_r  (dbg_cache_rst_disable_r),

  .aux_read                 (aux_read         ),  
  .aux_write                (aux_write        ),  
  .aux_ren_r                (aux_ren_r        ),  
  .aux_raddr_r              (aux_raddr_r      ),  
  .aux_wen_r                (aux_wen_r        ),  
  .aux_waddr_r              (aux_waddr_r      ),  
  .aux_wdata_r              (aux_wdata_r      ),  
  
  .aux_rdata                (aux_rdata        ),  
  .aux_illegal              (aux_illegal      ),  
  .aux_k_rd                 (aux_k_rd         ),  
  .aux_k_wr                 (aux_k_wr         ),  
  .aux_unimpl               (aux_unimpl       ),  
  .aux_serial_sr            (aux_serial_sr    ), 
  .aux_strict_sr            (aux_strict_sr    ),
  
  .aux_x2_addr_pass         (aux_x2_addr_pass ), 
  .aux_x2_addr              (aux_x2_addr      ), 
  .aux_x2_addr_hi           (aux_x2_addr_hi   ),

  .aux_init_r               (aux_init_r       ),        
  .aux_busy                 (aux_busy         ),        
  .aux_cache_off            (aux_cache_off    ),        
  .aux_sg_off               (aux_sg_off       ),        

  .aux_ecc_scrub_in_progress_r (aux_ecc_scrub_in_progress_r),
  .aux_ecc_addr_r           (aux_ecc_addr            ),
  .aux_ecc_tag_r            (aux_ecc_tag             ),
  .aux_ecc_dt_way_hot_r     (aux_ecc_dt_way_hot      ),
  .aux_ecc_data_mem_valid_r (aux_ecc_data_mem_valid  ),
  .dc4_dt_ecc_sb_error      (dc4_dt_ecc_sb_error     ),
  .dc4_dd_ecc_sb_error      (dc4_dd_ecc_sb_error     ),
  .dc4_dt_ecc_db_error      (dc4_dt_ecc_db_error     ),
  .dc4_dt_ecc_scrub_start   (dc4_dt_ecc_scrub_start  ),
  .dc4_dd_ecc_scrub_start   (dc4_dd_ecc_scrub_start  ),
  .aux_dc_dt_scrub_start_r  (wa_dt_ecc_scrub_start_r ),
  .aux_dc_dd_scrub_start_r  (wa_dd_ecc_scrub_start_r ),
  .dc4_ecc_data_odd_hi      (wa_ecc_data_odd_hi      ),
  .dc4_ecc_data_odd_lo      (wa_ecc_data_odd_lo      ),
  .dc4_ecc_data_even_hi     (wa_ecc_data_even_hi     ),
  .dc4_ecc_data_even_lo     (wa_ecc_data_even_lo     ),
  .aux_dt_read              (aux_dt_read             ),
  .aux_ecc_done_r           (aux_ecc_done_r          ),

  .ecc_dc_tag_sbe_count_r   (ecc_dc_tag_sbe_count_r  ),
  .dc_tag_ecc_sbe_clr       (dc_tag_ecc_sbe_clr      ),
  .ecc_dc_data_sbe_count_r  (ecc_dc_data_sbe_count_r ),
  .dc_data_ecc_sbe_clr      (dc_data_ecc_sbe_clr     ),

  .aux_req_dt_even          (aux_req_dt_even  ),
//  .aux_ack_dt_even          (aux_ack_dt_even  ),
  .aux_req_dt_odd           (aux_req_dt_odd   ),
//  .aux_ack_dt_odd           (aux_ack_dt_odd   ),
  .aux_dt_way_hot           (aux_dt_way_hot   ),
  .aux_dt_addr              (aux_dt_addr      ),
  .aux_dt_we                (aux_dt_we        ),
  .aux_dt_wem               (aux_dt_wem       ),
  .aux_dt_valid             (aux_dt_valid     ),
  .aux_dt_tag               (aux_dt_tag       ),

  .aux_req_ds               (aux_req_ds       ),
//  .aux_ack_ds               (aux_ack_ds       ),
  .aux_ds_addr              (aux_ds_addr      ),
  .aux_ds_odd_sel           (aux_ds_odd_sel   ),
  .aux_ds_we                (aux_ds_we        ),
  .aux_ds_wem               (aux_ds_wem       ),
  .aux_ds_lock              (aux_ds_lock      ),
  .aux_ds_dirty             (aux_ds_dirty     ),
  .aux_ds_lru               (aux_ds_lru       ),
  .aux_ds_way_hot           (aux_ds_way_hot   ),
 
  .aux_req_dd_even_lo       (aux_req_dd_even_lo),
  .aux_req_dd_even_hi       (aux_req_dd_even_hi),
  .aux_req_dd_odd_lo        (aux_req_dd_odd_lo ),
  .aux_req_dd_odd_hi        (aux_req_dd_odd_hi ),
  .aux_dd_addr              (aux_dd_addr       ),
  .aux_dd_way_hot           (aux_dd_way_hot    ), 
  .aux_dd_we                (aux_dd_we         ),
  .aux_dd_din               (aux_dd_din        ),
  .aux_dd_data_read         (aux_dd_data_read  ),
  .aux_dd_direct_read       (aux_dd_direct_read),
  .aux_dd_data_bank         (aux_dd_data_bank  ),
  .dc_dd_data               (dc_dd_data_r      ),
  .dc3_dt_even_hit_way_hot  (dc3_dt_even_hit_way_hot  ),
  .dc3_dt_even_valid_hot    (dc3_dt_even_valid_way_hot),
  .dc3_ds_even_dirty_hot    (status1_dirty_even       ),
  .dc3_ds_even_lock_hot     ({1'b0, status1_lock_even}),
  
  .dc3_dt_odd_hit_way_hot   (dc3_dt_odd_hit_way_hot   ),
  .dc3_dt_odd_valid_hot     (dc3_dt_odd_valid_way_hot ),
  .dc3_ds_odd_dirty_hot     (status1_dirty_odd        ),
  .dc3_ds_odd_lock_hot      ({1'b0, status1_lock_odd} ),
  
  .dc3_dt_even_tag_w0      (dc_tag_even_dout_w0[`npuarc_DC_TAG_TAG_RANGE]),
  .dc3_dt_odd_tag_w0       (dc_tag_odd_dout_w0[`npuarc_DC_TAG_TAG_RANGE]),
  .dc3_dt_even_tag_w1      (dc_tag_even_dout_w1[`npuarc_DC_TAG_TAG_RANGE]),
  .dc3_dt_odd_tag_w1       (dc_tag_odd_dout_w1[`npuarc_DC_TAG_TAG_RANGE]),
  
  .aux_mq_write             (aux_mq_write     ), 
  .aux_mq_flush             (aux_mq_flush     ), 
  .aux_mq_purge             (aux_mq_purge     ), 
  .aux_mq_refill            (aux_mq_refill    ), 
  .aux_mq_way               (aux_mq_way       ),
  .aux_mq_addr              (aux_mq_addr      ), 
  .aux_mq_lru_dirty         (aux_mq_lru_dirty ),
  .lb_err_r                 (lb_err_r         ),
  .mq_empty                 (mq_empty         ),
  .cb_full                  (cb_full          ),
//  .cb_wr_done               (cb_wr_done       ),
  .cb_err_wr                (cb_err_wr        ),

  .dc_pct_ivdc              (dc_pct_ivdc      ),
  .dc_pct_ivdl              (dc_pct_ivdl      ),
  .dc_pct_flsh              (dc_pct_flsh      ),
  .dc_pct_fldl              (dc_pct_fldl      ),
  
  .dc_pipe_empty            (dc_pipe_empty    ),
  .wq_empty                 (wq_empty         ),
  .dmu_empty                (dmu_empty        ),  
  .dmu_dc_idle              (dmu_dc_idle      )  
);


//////////////////////////////////////////////////////////////////////////////
//                                                                           
//////////////////////////////////////////////////////////////////////////////

reg [1:0]             dc2_tag_mem_valid_r;  // DC2 tag memory being read

always @*
begin : dc2_dc3_tag_data_mem_valid_PROC
  dc2_tag_mem_valid   = (| dc2_tag_mem_valid_r);
  dc3_tag_mem_valid   = (| dc3_tag_mem_valid_r);
  
end

//////////////////////////////////////////////////////////////////////////////
//  Asynchronous processes that determines the enabling of dc4_data registers    
//  In case of a dc4_stall, the dc3 data is stored in dc4 data registers
//  and the dc2 data stays in the memory output      
//                                                                           
//////////////////////////////////////////////////////////////////////////////

reg  dc3_tag_mem_valid_cg0; 
reg  dc4_tag_mem_valid_cg0; 
reg  dc4_waw_replay_cg0;

reg  dc4_dd_data_even_lo_cg0;
reg  dc4_dd_data_even_hi_cg0;
reg  dc4_dd_data_odd_lo_cg0; 
reg  dc4_dd_data_odd_hi_cg0;

always @*
begin : dc2_dc3_data_mem_valid_PROC
  // DC2 Data clock gates
  //
  dc2_data_mem_valid_cg0     =  dc1_ld_target_dc;
  
  // DC3 Tag clock gates
  //
  dc3_tag_mem_valid_cg0       =   dc2_tag_mem_valid
                                | dc3_tag_mem_valid; 
  
  // DC4 Tag clock gates
  //
  dc4_tag_mem_valid_cg0       =  dc3_target_dc & x3_pass   // set
                              | (dc4_target_dc & ca_pass)  // clear
                              ;

  
  // DC4 WAW replay clock gate 
  //
  dc4_waw_replay_cg0          = dc4_tag_mem_valid_cg0 | dc4_waw_replay_r;

  // DC4 Data clock gates
  //
  dc4_dd_data_even_lo_cg0     = (  dc3_ld_target_dc 
                                 & dc3_data_mem_valid_r[0]
                                 & x3_pass)
                               | dmu_evict_rd
                               | aux_dd_data_read
                                 ;
  dc4_dd_data_even_hi_cg0     = (  dc3_ld_target_dc 
                                 & dc3_data_mem_valid_r[1]
                                 & x3_pass)
                               | dmu_evict_rd
                               | aux_dd_data_read
                                 ;
  dc4_dd_data_odd_lo_cg0      = (  dc3_ld_target_dc 
                                 & dc3_data_mem_valid_r[2]
                                 & x3_pass)
                               | dmu_evict_rd
                               | aux_dd_data_read
                                 ;
  dc4_dd_data_odd_hi_cg0      = (  dc3_ld_target_dc 
                                 & dc3_data_mem_valid_r[3]
                                 & x3_pass)
                               | dmu_evict_rd 
                               | aux_dd_data_read
                                 ;
  
  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous process to align the dd data to the AUX module           
//                                                                           
//////////////////////////////////////////////////////////////////////////////
reg [1:0] dc_data_bank;

always @*
begin : dc_data_bank_PROC
  // When an EX instruction graduates, it may need the data it read from the 
  // data cache.
  //
  dc_data_bank =  (ca_load_r & ca_store_r)
                ?  ca_mem_addr0_r[3:2]
                :  aux_dd_data_bank
                ;
end

always @*
begin : dc_dd_data_PROC
  case (dc_data_bank)
  2'b00:   dc_dd_data = dc4_ecc_data_even_lo;
  2'b01:   dc_dd_data = dc4_ecc_data_even_hi;
  2'b10:   dc_dd_data = dc4_ecc_data_odd_lo;
  default: dc_dd_data = dc4_ecc_data_odd_hi;
  endcase
  
end


always @*
begin : dc1_dc2_bank_common_nxt_PROC
  //
  // Default Value
  dc1_dc2_bank_common_nxt = dc1_dc2_bank_common_r;
  
  if (dc1_dc2_bank_common_set_cg0)
  begin
    dc1_dc2_bank_common_nxt  = dc1_dc2_bank_common;
  end
  else if (dc1_dc2_bank_common_clr_cg0)
  begin
    dc1_dc2_bank_common_nxt  = 4'b0000;
  end
end

always @*
begin : aux_ecc_scrub_in_progress_nxt_PROC
  //
  // Default value
  aux_ecc_scrub_in_progress_nxt = aux_ecc_scrub_in_progress_r;
  
  if ( (~aux_busy) & (wa_dt_ecc_scrub_start_r | wa_dd_ecc_scrub_start_r))
  begin
    aux_ecc_scrub_in_progress_nxt  = 1'b1;
  end
  else if (aux_ecc_done_r)
  begin
    aux_ecc_scrub_in_progress_nxt  = 1'b0;
  end  
end  


always @*
begin : dc4_dd_data_nxt_PROC
  //
  // Default value
  dc4_dd_data_even_lo_nxt = dc4_dd_data_even_lo_r;
  dc4_dd_data_even_hi_nxt = dc4_dd_data_even_hi_r;
  dc4_dd_data_odd_lo_nxt  = dc4_dd_data_odd_lo_r;
  dc4_dd_data_odd_hi_nxt  = dc4_dd_data_odd_hi_r;

  i_parity_dd_0_nxt       = i_parity_dd_0_r;
  syndrome_dd_0_nxt       = syndrome_dd_0_r;
  i_parity_dd_1_nxt       = i_parity_dd_1_r;
  syndrome_dd_1_nxt       = syndrome_dd_1_r;
  i_parity_dd_2_nxt       = i_parity_dd_2_r;
  syndrome_dd_2_nxt       = syndrome_dd_2_r;
  i_parity_dd_3_nxt       = i_parity_dd_3_r;
  syndrome_dd_3_nxt       = syndrome_dd_3_r;
  if (dc4_dd_data_even_lo_cg0)
  begin
    dc4_dd_data_even_lo_nxt  =  dc3_dd_data_even_lo; //dc3_even_way0_hit
    i_parity_dd_0_nxt        = ecc0_even_sel ? i_parity_dd_00 : i_parity_dd_10;
    syndrome_dd_0_nxt        = ecc0_even_sel ? syndrome_dd_00 : syndrome_dd_10;
  end
    
  if (dc4_dd_data_even_hi_cg0)
  begin
    dc4_dd_data_even_hi_nxt  =  dc3_dd_data_even_hi; //!dc3_even_way0_hit
    i_parity_dd_1_nxt        = ecc0_even_sel ? i_parity_dd_01 : i_parity_dd_11;
    syndrome_dd_1_nxt        = ecc0_even_sel ? syndrome_dd_01 : syndrome_dd_11;
  end
       
  if (dc4_dd_data_odd_lo_cg0)
  begin
    dc4_dd_data_odd_lo_nxt   =  dc3_dd_data_odd_lo; //dc3_odd_way0_hit
    i_parity_dd_2_nxt        = ecc0_odd_sel ? i_parity_dd_02 : i_parity_dd_12;
    syndrome_dd_2_nxt        = ecc0_odd_sel ? syndrome_dd_02 : syndrome_dd_12;
  end

  if (dc4_dd_data_odd_hi_cg0)
  begin
    dc4_dd_data_odd_hi_nxt   =   dc3_dd_data_odd_hi; //!dc3_odd_way0_hit
    i_parity_dd_3_nxt        = ecc0_odd_sel ? i_parity_dd_03 : i_parity_dd_13;
    syndrome_dd_3_nxt        = ecc0_odd_sel ? syndrome_dd_03 : syndrome_dd_13;
  end
end


always @*
begin : dc3_dc_poisoned_nxt_PROC
  //
  // Default value
  dc3_dc_poisoned_prel_nxt = dc3_dc_poisoned_prel_r; 
  
  if (dc3_reset_poisoned)
  begin
    dc3_dc_poisoned_prel_nxt = 1'b0;
  end
  else if (dc3_set_poisoned)
  begin
    dc3_dc_poisoned_prel_nxt = 1'b1;
  end
end


always @*
begin : dc_tag_even_ctl_cg0_nxt_PROC
  //
  // Default Value
  dc_tag_even_addr_next     = dc_tag_even_addr_r;
  dc_tag_even_tag_w0_next   = dc_tag_even_tag_w0_r;
  dc_tag_even_tag_w1_next   = dc_tag_even_tag_w1_r;
  dc_tag_even_wem_next      = dc_tag_even_wem_r;  
  dc_tag_even_cs_next       = dc_tag_even_cs_nxt;  
  dc_tag_even_we_next       = dc_tag_even_we_nxt;  
  dc_tag_even_valid_w0_next = dc_tag_even_valid_w0_r;
  dc_tag_even_valid_w1_next = dc_tag_even_valid_w1_r;

  if (dc_tag_even_ctl_cg0)
  begin
    dc_tag_even_addr_next   = dc_tag_even_addr_nxt; 
  end
  
  if (dc_tag_even_tag_data_cg0)
  begin
    // Only enabled for tag writes 
    //
    dc_tag_even_tag_w0_next   = dc_tag_even_tag_w0_nxt;
    dc_tag_even_tag_w1_next   = dc_tag_even_tag_w1_nxt;
  end
  
  if (dc_tag_even_tag_ctl_cg0)
  begin
    // Only enabled for setting/resetting the valid bit
    //
    dc_tag_even_wem_next      = dc_tag_even_wem_nxt;  
    dc_tag_even_valid_w0_next = dc_tag_even_valid_w0_nxt;
    dc_tag_even_valid_w1_next = dc_tag_even_valid_w1_nxt;
  end
end

always @*
begin : dc_tag_odd_ctl_cg0_nxt_PROC
  //
  // Default Value
  dc_tag_odd_addr_next     = dc_tag_odd_addr_r;
  dc_tag_odd_tag_w0_next   = dc_tag_odd_tag_w0_r;
  dc_tag_odd_tag_w1_next   = dc_tag_odd_tag_w1_r;
  dc_tag_odd_wem_next      = dc_tag_odd_wem_r;  
  dc_tag_odd_cs_next       = dc_tag_odd_cs_nxt;  
  dc_tag_odd_we_next       = dc_tag_odd_we_nxt;  
  dc_tag_odd_valid_w0_next = dc_tag_odd_valid_w0_r;
  dc_tag_odd_valid_w1_next = dc_tag_odd_valid_w1_r;

  if (dc_tag_odd_ctl_cg0)
  begin
    dc_tag_odd_addr_next   = dc_tag_odd_addr_nxt; 
  end
  
  if (dc_tag_odd_tag_data_cg0)
  begin
    // Only enabled for tag writes 
    //
    dc_tag_odd_tag_w0_next   = dc_tag_odd_tag_w0_nxt;
    dc_tag_odd_tag_w1_next   = dc_tag_odd_tag_w1_nxt;
  end
  
  if (dc_tag_odd_tag_ctl_cg0)
  begin
    // Only enabled for setting/resetting the valid bit
    //
    dc_tag_odd_wem_next      = dc_tag_odd_wem_nxt;  
    dc_tag_odd_valid_w0_next = dc_tag_odd_valid_w0_nxt;
    dc_tag_odd_valid_w1_next = dc_tag_odd_valid_w1_nxt;
  end
end


always @*
begin : dc_data_cs_we_nxt_PROC
  //
  // Default Value
  dc_data_even_cs_lo_next = dc_data_even_cs_lo_r;
  dc_data_even_we_lo_next = dc_data_even_we_lo_r;
  dc_data_even_cs_hi_next = dc_data_even_cs_hi_r;
  dc_data_even_we_hi_next = dc_data_even_we_hi_r;

  dc_data_odd_cs_lo_next  = dc_data_odd_cs_lo_r;
  dc_data_odd_we_lo_next  = dc_data_odd_we_lo_r;
  dc_data_odd_cs_hi_next  = dc_data_odd_cs_hi_r;
  dc_data_odd_we_hi_next  = dc_data_odd_we_hi_r;

  if (dc_data_even_cs_lo_cg0)
  begin
    dc_data_even_cs_lo_next  = dc_data_even_cs_lo_nxt;  
    dc_data_even_we_lo_next  = dc_data_even_we_lo_nxt;  
  end
    
  if (dc_data_even_cs_hi_cg0)
  begin
    dc_data_even_cs_hi_next  = dc_data_even_cs_hi_nxt; 
    dc_data_even_we_hi_next  = dc_data_even_we_hi_nxt; 
  end
    
  if (dc_data_odd_cs_lo_cg0)
  begin
    dc_data_odd_cs_lo_next   = dc_data_odd_cs_lo_nxt;
    dc_data_odd_we_lo_next   = dc_data_odd_we_lo_nxt;
  end
    
  if (dc_data_odd_cs_hi_cg0)
  begin
    dc_data_odd_cs_hi_next   = dc_data_odd_cs_hi_nxt;
    dc_data_odd_we_hi_next   = dc_data_odd_we_hi_nxt;
  end
end  


always @*
begin : dc_data_din_wem_nxt_PROC
  //
  // Default values
  dc_data_even_wem_lo_next = dc_data_even_wem_lo_r;
  dc_data_even_din_lo_next = dc_data_even_din_lo_r;
  dc_data_even_wem_hi_next = dc_data_even_wem_hi_r;
  dc_data_even_din_hi_next = dc_data_even_din_hi_r;

  dc_data_odd_wem_lo_next  = dc_data_odd_wem_lo_r;
  dc_data_odd_din_lo_next  = dc_data_odd_din_lo_r;
  dc_data_odd_wem_hi_next  = dc_data_odd_wem_hi_r;
  dc_data_odd_din_hi_next  = dc_data_odd_din_hi_r;  
  
  if (dc_data_even_din_lo_cg0)
  begin
    dc_data_even_wem_lo_next = dc_data_even_wem_lo_nxt;
    dc_data_even_din_lo_next = dc_data_even_din_lo_nxt;
  end
  
  if (dc_data_even_din_hi_cg0)
  begin
    dc_data_even_wem_hi_next = dc_data_even_wem_hi_nxt;
    dc_data_even_din_hi_next = dc_data_even_din_hi_nxt;
  end
 
  if (dc_data_odd_din_lo_cg0)
  begin
    dc_data_odd_wem_lo_next = dc_data_odd_wem_lo_nxt;
    dc_data_odd_din_lo_next = dc_data_odd_din_lo_nxt;
  end
  
  if (dc_data_odd_din_hi_cg0)
  begin
    dc_data_odd_wem_hi_next = dc_data_odd_wem_hi_nxt; 
    dc_data_odd_din_hi_next = dc_data_odd_din_hi_nxt;
  end
end


always @*
begin : dc_data_addr_nxt_PROC
  //
  // Default Values
  dc_data_even_addr_lo_next = dc_data_even_addr_lo_r;
  dc_data_even_addr_hi_next = dc_data_even_addr_hi_r;
  dc_data_odd_addr_lo_next  = dc_data_odd_addr_lo_r;
  dc_data_odd_addr_hi_next  = dc_data_odd_addr_hi_r;
  
  if (dc_data_even_addr_lo_cg0)
  begin
// spyglass disable_block Reset_sync04
// SMD: Async reset signal is synchronized at least twice
// SJ:  other resync spot in alb_reset_ctrl already waived
    dc_data_even_addr_lo_next  = dc_data_even_addr_lo_nxt;
// spyglass enable_block Reset_sync04
  end
    
  if (dc_data_even_addr_hi_cg0)
  begin
    dc_data_even_addr_hi_next  = dc_data_even_addr_hi_nxt;
  end
  
  if (dc_data_odd_addr_lo_cg0)
  begin
    dc_data_odd_addr_lo_next  = dc_data_odd_addr_lo_nxt;
  end
  
  if (dc_data_odd_addr_hi_cg0)
  begin
    dc_data_odd_addr_hi_next  = dc_data_odd_addr_hi_nxt; 
  end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Synchronous processes            
//                                                                           
//////////////////////////////////////////////////////////////////////////////

// DC1 state
//
always @(posedge clk or posedge rst_a)
begin : dc1_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc1_state_r  <= DC1_DEFAULT;
  end
  else
  begin
    dc1_state_r <= dc1_state_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc1_ecc_block_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc1_ecc_state_r  <= 1'b0;
    dc1_ecc_block_r  <= 1'b0;
  end
  else
  begin
    dc1_ecc_state_r  <= dc1_ecc_state_nxt;
    dc1_ecc_block_r  <= dc1_ecc_block_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc2_req_dt_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_dt_addr0           <= {`npuarc_DC_IDX_BITS{1'b0}};
    dc2_dt_addr1           <= {`npuarc_DC_IDX_BITS{1'b0}};
    dc2_dd_addr0           <= {`npuarc_DC_ADR_BITS{1'b0}};
    dc2_dd_addr1           <= {`npuarc_DC_ADR_BITS{1'b0}};   
    dc2_bank_not_ack_r     <= 4'b0000;
    dc2_active_cs_r        <= 4'b0000;
    dc2_req_dt_even_r      <= 1'b0;
    dc2_req_dt_odd_r       <= 1'b0;         
    dc2_req_dd_even_lo_r   <= 1'b0;
    dc2_req_dd_even_hi_r   <= 1'b0;
    dc2_req_dd_odd_lo_r    <= 1'b0;
    dc2_req_dd_odd_hi_r    <= 1'b0;
    dc2_pref_r             <= 1'b0;
  end
  else if (dc2_req_cg0)  
  begin
    dc2_dt_addr0         <= dc1_dt_addr0;
    dc2_dt_addr1         <= dc1_dt_addr1;
    dc2_dd_addr0         <= dc1_dd_addr0;
    dc2_dd_addr1         <= dc1_dd_addr1;
    dc2_bank_not_ack_r   <= dc1_bank_not_ack;
    dc2_active_cs_r      <= dc2_active_cs_nxt;
    dc2_req_dt_even_r    <= dc1_req_dt_even;
    dc2_req_dt_odd_r     <= dc1_req_dt_odd;
    dc2_req_dd_even_lo_r <= dc1_bank_req_mask[0];
    dc2_req_dd_even_hi_r <= dc1_bank_req_mask[1];
    dc2_req_dd_odd_lo_r  <= dc1_bank_req_mask[2];
    dc2_req_dd_odd_hi_r  <= dc1_bank_req_mask[3];
    dc2_pref_r           <= x1_pref_r;
   end
end
// DC2 stall
//
always @(posedge clk or posedge rst_a)
begin : dc2_stuck_PROC
  if (rst_a == 1'b1)
  begin
    dc2_stuck_r            <= 1'b0; 
  end
  else
  begin
    dc2_stuck_r            <= dc2_stuck & dc2_ld_target_dc; 
  end
end

always @(posedge clk or posedge rst_a)
begin : dc1_dc2_bank_common_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc1_dc2_bank_common_r    <= 4'b0000;
  end
  else
  begin
    dc1_dc2_bank_common_r    <= dc1_dc2_bank_common_nxt;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc2_cft_stall_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_cft_state_r        <= DC2_CFT_DEFAULT;
    dc2_full_ack_dd_prev_r <= 1'b0;
  end
  else if (dc2_cft_state_cg0)
  begin
    dc2_cft_state_r        <= dc2_cft_state_nxt;
    dc2_full_ack_dd_prev_r <= dc2_ld_target_dc & dc2_full_ack_dd & dc2_stuck;
  end
end

    

// DC2 DD information
//
always @(posedge clk or posedge rst_a)
begin : dc2_data_mem_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_data_mem_valid_r   <= 4'b0000;
  end
  else if (dc2_data_mem_valid_cg0)
  begin
   dc2_data_mem_valid_r  <=   { dc1_data_bank_sel_hi[1],
                                dc1_data_bank_sel_lo[1],
                                dc1_data_bank_sel_hi[0],
                                dc1_data_bank_sel_lo[0]}
                           |  { aux_ack_dd_odd_hi,
                                aux_ack_dd_odd_lo,
                                aux_ack_dd_even_hi,
                                aux_ack_dd_even_lo}; 
  end
end

// DC2 DT information
//
always @(posedge clk or posedge rst_a)
begin : dc2_tag_mem_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_tag_mem_valid_r <= 2'b00;
  end
  else
  begin

    dc2_tag_mem_valid_r <= {dc1_ack_dt_even 
                            | aux_init_r
                            ,
                            dc1_ack_dt_odd  
                            | aux_init_r  
                           } ;
  end
end

// DC3 DD information
//
always @(posedge clk or posedge rst_a)
begin : dc3_data_mem_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_data_mem_valid_r       <= 4'b0000;
   end
  else if (dc3_data_mem_valid_cg0)
  begin
    dc3_data_mem_valid_r     <= ( dc2_data_mem_valid_r
                                )
                              &  {4{~dc2_pref_r}}
                              ;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_data_read_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_data_read_r         <= 4'b0000;
    dc_tag_read_r          <= 4'b0000;
    dc_tag_active_r        <= 4'b0000;
    dmu_aux_dc_data_read_r <= 1'b0;
    dmu_aux_dc_tag_read_r  <= 4'b0000;
  end
  else
  begin
    dc_data_read_r         <= dc_data_read;
    dc_tag_read_r          <= dc_tag_read;
    dc_tag_active_r        <= dc_tag_active;
    dmu_aux_dc_data_read_r <= (aux_full_ack_dd | dmu_full_ack_dd);
    dmu_aux_dc_tag_read_r  <= dmu_evict_rd
                            ? (   (dmu_dt_odd_sel == 1'b0)
                                ? ({2'b00,{dmu_dt_way_hot[1:0]}})
                                : ({{dmu_dt_way_hot[1:0]},2'b00})
                              )
                            : ({{2{aux_ack_dt_odd}},{2{aux_ack_dt_even}}})
                            ;  
  end
end


// DC3 DT information
//
always @(posedge clk or posedge rst_a)
begin : dc3_tag_mem_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_tag_mem_valid_r      <= 2'b00;
  end
  else if (dc3_tag_mem_valid_cg0)
  begin
    dc3_tag_mem_valid_r <= dc2_tag_mem_valid_r;
  end
end

// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ: 
// DC4 DT information
//
always @(posedge clk or posedge rst_a)
begin : dc4_tag_mem_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_dt_miss_even_r         <= 1'b0;
    dc4_dt_miss_odd_r          <= 1'b0;
    dc4_hit_even_way_hot_r     <= 2'b00;
    dc4_hit_odd_way_hot_r      <= 2'b00;
    dc4_dt_hit_r               <= 1'b0;
    dc4_dt_miss_r              <= 1'b0;
  end
  else if (dc4_tag_mem_valid_cg0)
  begin
    dc4_dt_miss_even_r         <= (~addr_even_hit & (~dc3_dc_poisoned));
    dc4_dt_miss_odd_r          <= (~addr_odd_hit & (~dc3_dc_poisoned));
    dc4_hit_even_way_hot_r     <=    dc3_dt_even_hit_way_hot  
                                  &  {`npuarc_DC_WAYS{dc3_dt_bank_sel_r[0]}}
                                  & (~{`npuarc_DC_WAYS{dc3_dc_poisoned}});
    dc4_hit_odd_way_hot_r      <=    dc3_dt_odd_hit_way_hot  
                                  &  {`npuarc_DC_WAYS{dc3_dt_bank_sel_r[1]}}
                                  & (~{`npuarc_DC_WAYS{dc3_dc_poisoned}});
    dc4_dt_hit_r               <=   dc3_dt_hit
                                  & dc3_target_dc    
                                  & (~dc3_dc_poisoned);    
    dc4_dt_miss_r              <= (  dc3_dt_miss 
                                  )
                                  & dc3_target_dc    
                                  & (~dc3_dc_poisoned); 

  end
end


// leda TEST_975 on

always @(posedge clk or posedge rst_a)
begin : dc4_waw_replay_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_waw_replay_r <= 1'b0;
  end
  else if (dc4_waw_replay_cg0)
  begin
    dc4_waw_replay_r <= dc4_waw_replay_nxt;
  end
end


// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:
always @(posedge clk or posedge rst_a)
begin : dc4_ecc_data_reg_PROC
  if (rst_a == 1'b1) 
  begin
    dc4_dt_even_hit_way_hot_r       <= 2'd0;
    dc4_dt_odd_hit_way_hot_r        <= 2'd0;
    dc4_data_mem_valid_r            <= 4'b0000; 
  end
  else if (dc4_dd_ecc_error_cg0)
  begin
    dc4_dt_even_hit_way_hot_r     <= dc3_dt_even_hit_way_hot;
    dc4_dt_odd_hit_way_hot_r      <= dc3_dt_odd_hit_way_hot;
    dc4_data_mem_valid_r          <= dc3_data_mem_valid_r;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_dd_ecc_valid_reg_PROC
  if (rst_a == 1'b1) 
  begin
    dc4_dd_ecc_valid_r            <= 4'd0;
  end
  else if (dc4_dd_ecc_error_valid_cg0)
  begin
    dc4_dd_ecc_valid_r            <= dc3_dd_ecc_valid;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_ecc_tag_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_ecc_tag_addr_even_r        <= {`npuarc_DC_IDX_BITS{1'b0}};
    dc4_ecc_tag_addr_odd_r         <= {`npuarc_DC_IDX_BITS{1'b0}};


    dc4_dt_ecc_tag_even_w0_r       <= {`npuarc_DC_TRAM_BITS{1'b0}}; 
    dc4_dt_ecc_tag_even_w1_r       <= {`npuarc_DC_TRAM_BITS{1'b0}}; 
    dc4_dt_ecc_tag_odd_w0_r        <= {`npuarc_DC_TRAM_BITS{1'b0}}; 
    dc4_dt_ecc_tag_odd_w1_r        <= {`npuarc_DC_TRAM_BITS{1'b0}}; 

  end
  else if (dc4_dt_ecc_error_cg0)
  begin
    dc4_ecc_tag_addr_even_r      <= dc3_ecc_tag_addr_even;
    dc4_ecc_tag_addr_odd_r       <= dc3_ecc_tag_addr_odd;

    dc4_dt_ecc_tag_even_w0_r     <= dc3_dt_even_w0;              
    dc4_dt_ecc_tag_even_w1_r     <= dc3_dt_even_w1;              
    dc4_dt_ecc_tag_odd_w0_r      <= dc3_dt_odd_w0;              
    dc4_dt_ecc_tag_odd_w1_r      <= dc3_dt_odd_w1;              

  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_dt_ecc_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_dt_ecc_valid_r             <= 4'd0;
  end
  else if (dc4_dt_ecc_error_valid_cg0)
  begin
    dc4_dt_ecc_valid_r           <= dc3_dt_ecc_valid;  
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_dt_ecc_bank_sel_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_dt_ecc_bank_sel_r          <= 4'd0;
  end
  else if (dc4_dt_ecc_bank_sel_cg0)
  begin
    dc4_dt_ecc_bank_sel_r        <= dc3_dt_ecc_bank_sel;
  end
end
// leda TEST_975 on

always @(posedge clk or posedge rst_a)
begin : wa_ecc_tag_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_dt_ecc_bank_sel_r        <= 1'b0;
  end
  else if (wa_dc_ecc_error_cg0)
  begin
    aux_dt_ecc_bank_sel_r        <= aux_dt_ecc_bank_sel;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_ecc_data_mem_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    wa_dd_ecc_addr_r       <= {`npuarc_DC_ADDR_BITS{1'b0}};
    wa_dd_ecc_way_hot_r    <= 2'b00;
    wa_dd_ecc_mem_valid_r  <= 4'b0000;
  end
  else if (wa_dd_ecc_mem_valid_cg0)
  begin
    wa_dd_ecc_addr_r     <= dc4_dd_ecc_addr;
    wa_dd_ecc_way_hot_r  <= dc4_dd_ecc_way_hot;
    wa_dd_ecc_mem_valid_r<= dc4_dd_ecc_mem_valid;
  end  
end

always @(posedge clk or posedge rst_a)
begin : wa_dd_ecc_scrub_start_reg_PROC
  if (rst_a == 1'b1)
  begin
    wa_dt_ecc_scrub_start_r       <=  1'b0;
    wa_dd_ecc_scrub_start_r       <=  1'b0;
  end
  else
  begin
    wa_dt_ecc_scrub_start_r       <= dc4_dt_ecc_scrub_start;
    wa_dd_ecc_scrub_start_r       <= dc4_dd_ecc_scrub_start;
  end
end  

assign aux_ecc_scrub_in_progress_next =
                        aux_ecc_scrub_in_progress_nxt;

always @(posedge clk or posedge rst_a)
begin : aux_ecc_scrub_in_progress_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_ecc_scrub_in_progress_r    <=  1'b0;
  end
  else
  begin
    aux_ecc_scrub_in_progress_r    <= aux_ecc_scrub_in_progress_next;
  end
end  

always @ (posedge clk or posedge rst_a)
begin : wa_ecc_data_reg_PROC
  if (rst_a == 1'b1)
  begin
    wa_ecc_data_even_lo   <= {`npuarc_DATA_SIZE{1'b0}};
    wa_ecc_data_even_hi   <= {`npuarc_DATA_SIZE{1'b0}};
    wa_ecc_data_odd_lo    <= {`npuarc_DATA_SIZE{1'b0}};
    wa_ecc_data_odd_hi    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (dc4_dd_ecc_replay)
  begin
    wa_ecc_data_even_lo <= dc4_ecc_data_even_lo;
    wa_ecc_data_even_hi <= dc4_ecc_data_even_hi;
    wa_ecc_data_odd_lo  <= dc4_ecc_data_odd_lo;
    wa_ecc_data_odd_hi  <= dc4_ecc_data_odd_hi;
  end
end  

// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked by the trailing edge of the same clock
// LJ:  
// DC4 DD data
//
always @(posedge clk or posedge rst_a)
begin : dc4_dd_data_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_dd_data_even_lo_r  <= {`npuarc_DC_WAY_DATA_ECC_SIZE{1'b0}};
    dc4_dd_data_even_hi_r  <= {`npuarc_DC_WAY_DATA_ECC_SIZE{1'b0}};
    dc4_dd_data_odd_lo_r   <= {`npuarc_DC_WAY_DATA_ECC_SIZE{1'b0}};
    dc4_dd_data_odd_hi_r   <= {`npuarc_DC_WAY_DATA_ECC_SIZE{1'b0}};
    i_parity_dd_0_r        <= 1'b0;
    i_parity_dd_1_r        <= 1'b0;
    i_parity_dd_2_r        <= 1'b0;
    i_parity_dd_3_r        <= 1'b0;
    
    syndrome_dd_0_r        <= 6'd0;
    syndrome_dd_1_r        <= 6'd0;
    syndrome_dd_2_r        <= 6'd0;
    syndrome_dd_3_r        <= 6'd0;
  end
  else
  begin
    dc4_dd_data_even_lo_r  <= dc4_dd_data_even_lo_nxt;
    dc4_dd_data_even_hi_r  <= dc4_dd_data_even_hi_nxt;
    dc4_dd_data_odd_lo_r   <= dc4_dd_data_odd_lo_nxt;
    dc4_dd_data_odd_hi_r   <= dc4_dd_data_odd_hi_nxt;
    i_parity_dd_0_r        <= i_parity_dd_0_nxt;
    syndrome_dd_0_r        <= syndrome_dd_0_nxt;
    i_parity_dd_1_r        <= i_parity_dd_1_nxt;
    syndrome_dd_1_r        <= syndrome_dd_1_nxt;
    i_parity_dd_2_r        <= i_parity_dd_2_nxt;
    syndrome_dd_2_r        <= syndrome_dd_2_nxt;
    i_parity_dd_3_r        <= i_parity_dd_3_nxt;
    syndrome_dd_3_r        <= syndrome_dd_3_nxt;
  end
end  
// leda TEST_975 on


always @(posedge clk or posedge rst_a)
begin : dc1_wq_order_block_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc1_wq_order_block_r <= 1'b0;
    dc1_wq_order_state_r <= DC1_WQ_ORDER_DEFAULT; 
  end
  else
  begin
    dc1_wq_order_block_r <= dc1_wq_order_block_nxt;
    dc1_wq_order_state_r <= dc1_wq_order_state_nxt;
  end
end

assign dmu_has_dc_next =
                        dmu_has_dc_nxt;
always @(posedge clk or posedge rst_a)
begin : dmu_has_dc_reg_PROC
  if (rst_a == 1'b1)
  begin
    dmu_has_dc_r         <= 1'b0;
  end
  else
  begin
    dmu_has_dc_r         <= dmu_has_dc_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_pipe_enable_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_pipe_enable_r    <= 1'b1;
  end
  else
  begin
    dc_pipe_enable_r    <= (x2_enable & x3_enable);
  end
end

always @*
begin
    dmu_block_dc_next       = dmu_block_dc_nxt;
    dmu_data_sel_next       = dmu_data_sel_nxt;
    dmu_dc_stall_next       = dmu_dc_stall_nxt;
end
  
always @(posedge clk or posedge rst_a)
begin : dmu_block_dc_reg_PROC
  if (rst_a == 1'b1)
  begin
    dmu_block_dc_r       <= 1'b0;
    dmu_data_sel_r       <= 1'b0;
    dmu_dc_stall_r       <= 1'b0;
  end
  else
  begin
    dmu_block_dc_r       <= dmu_block_dc_next;
    dmu_data_sel_r       <= dmu_data_sel_next;
    dmu_dc_stall_r       <= dmu_dc_stall_next;
  end  
end

assign dmu_ack_state_next =
                        dmu_ack_state_nxt;
always @(posedge clk or posedge rst_a)
begin : dmu_ack_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    dmu_ack_state_r <= DMU_ACK_DEFAULT;
  end
  else
  begin
    dmu_ack_state_r <= dmu_ack_state_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc3_dc_poisoned_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_dc_poisoned_prel_r <= 1'b0;
  end
  else
  begin
    dc3_dc_poisoned_prel_r <= dc3_dc_poisoned_prel_nxt;
  end    
end


// Bank busy information
//
always @(posedge clk or posedge rst_a)
begin : dd_bank_busy_reg_PROC
  if (rst_a == 1'b1)
  begin
    dd_bank_busy_lo_r <= 2'b00;
    dd_bank_busy_hi_r <= 2'b00;
  end
  else
  begin
    dd_bank_busy_lo_r <= dd_bank_busy_lo_nxt;
    dd_bank_busy_hi_r <= dd_bank_busy_hi_nxt;
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Synchronous processes: DTAG            
//                                                                           
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : dc_tag_even_ctl_cg0_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_tag_even_cs_r       <= {`npuarc_DC_WAYS{1'b0}};
    dc_tag_even_we_r       <= 1'b0;
    dc_tag_even_wem_r      <= 3'b000;
    dc_tag_even_addr_r     <= {`npuarc_DC_IDX_BITS{1'b0}}; 
    dc_tag_even_valid_w0_r <= 1'b0; 
    dc_tag_even_valid_w1_r <= 1'b0; 
    dc_tag_even_tag_w0_r   <= {`npuarc_DC_TAG_BITS{1'b0}};
    dc_tag_even_tag_w1_r   <= {`npuarc_DC_TAG_BITS{1'b0}};
  end
  else
  begin
    dc_tag_even_cs_r       <= dc_tag_even_cs_next;
    dc_tag_even_we_r       <= dc_tag_even_we_next;
    
    dc_tag_even_addr_r     <= dc_tag_even_addr_next; 

    
    dc_tag_even_tag_w0_r   <= dc_tag_even_tag_w0_next;   
    dc_tag_even_tag_w1_r   <= dc_tag_even_tag_w1_next;   
    
    
    dc_tag_even_wem_r      <= dc_tag_even_wem_next;  
    dc_tag_even_valid_w0_r <= dc_tag_even_valid_w0_next;
    dc_tag_even_valid_w1_r <= dc_tag_even_valid_w1_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_tag_odd_ctl_cg0_reg_PROC 
  if (rst_a == 1'b1)
  begin
    dc_tag_odd_cs_r       <= {`npuarc_DC_WAYS{1'b0}};
    dc_tag_odd_we_r       <= 1'b0;
    dc_tag_odd_wem_r      <= 3'b000;
    dc_tag_odd_addr_r     <= {`npuarc_DC_IDX_BITS{1'b0}}; 
    dc_tag_odd_valid_w0_r <= 1'b0; 
    dc_tag_odd_valid_w1_r <= 1'b0; 
    dc_tag_odd_tag_w0_r   <= {`npuarc_DC_TAG_BITS{1'b0}};
    dc_tag_odd_tag_w1_r   <= {`npuarc_DC_TAG_BITS{1'b0}};
  end
  else
  begin
    dc_tag_odd_cs_r       <= dc_tag_odd_cs_nxt;
    dc_tag_odd_we_r       <= dc_tag_odd_we_nxt;

    dc_tag_odd_addr_r     <= dc_tag_odd_addr_next; 

    
    dc_tag_odd_tag_w0_r   <= dc_tag_odd_tag_w0_next;   
    dc_tag_odd_tag_w1_r   <= dc_tag_odd_tag_w1_next;   

    
    dc_tag_odd_wem_r      <= dc_tag_odd_wem_next;  
    dc_tag_odd_valid_w0_r <= dc_tag_odd_valid_w0_next;
    dc_tag_odd_valid_w1_r <= dc_tag_odd_valid_w1_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_pipe_ack_reg_PROC 
  if (rst_a == 1'b1)
  begin
    dc_pipe_ack_dt_even_r <= 1'b0;
    dc_pipe_ack_dt_odd_r  <= 1'b0;
  end
  else
  begin
    dc_pipe_ack_dt_even_r <= dc1_ack_dt_even | dc2_ack_dt_even;
    dc_pipe_ack_dt_odd_r  <= dc1_ack_dt_odd  | dc2_ack_dt_odd;
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Synchronous processes: DDATA            
//                                                                           
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : dc_data_cs_we_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_data_even_cs_lo_r     <= 1'b0;
    dc_data_even_we_lo_r     <= 1'b0; 
    
    dc_data_even_cs_hi_r     <= 1'b0;
    dc_data_even_we_hi_r     <= 1'b0; 
    
    dc_data_odd_cs_lo_r      <= 1'b0;
    dc_data_odd_we_lo_r      <= 1'b0; 
    
    dc_data_odd_cs_hi_r      <= 1'b0;
    dc_data_odd_we_hi_r      <= 1'b0; 
  end
  else
  begin
    dc_data_even_cs_lo_r     <= dc_data_even_cs_lo_next;
    dc_data_even_we_lo_r     <= dc_data_even_we_lo_next;  
    dc_data_even_cs_hi_r     <= dc_data_even_cs_hi_next;
    dc_data_even_we_hi_r     <= dc_data_even_we_hi_next;  

    dc_data_odd_cs_lo_r      <= dc_data_odd_cs_lo_next;
    dc_data_odd_we_lo_r      <= dc_data_odd_we_lo_next;  
    dc_data_odd_cs_hi_r      <= dc_data_odd_cs_hi_next;
    dc_data_odd_we_hi_r      <= dc_data_odd_we_hi_next;  
     
  end
end  

always @(posedge clk or posedge rst_a)
begin : dc_data_even_lo_din_wem_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_data_even_wem_lo_r <= {`npuarc_DC_BE_ECC_SIZE{1'b0}};
    dc_data_even_din_lo_r <= {`npuarc_DC_WAY_DATA_ECC_SIZE{1'b0}};
  end
  else if (dc_data_even_din_lo_cg0)
  begin
    dc_data_even_wem_lo_r <= dc_data_even_wem_lo_next;
    dc_data_even_din_lo_r <= dc_data_even_din_lo_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_data_even_hi_din_wem_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_data_even_wem_hi_r <= {`npuarc_DC_BE_ECC_SIZE{1'b0}};
    dc_data_even_din_hi_r <= {`npuarc_DC_WAY_DATA_ECC_SIZE{1'b0}};
  end
  else if (dc_data_even_din_hi_cg0)
  begin
    dc_data_even_wem_hi_r <= dc_data_even_wem_hi_next;
    dc_data_even_din_hi_r <= dc_data_even_din_hi_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_data_odd_lo_din_wem_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_data_odd_wem_lo_r <= {`npuarc_DC_BE_ECC_SIZE{1'b0}};  
    dc_data_odd_din_lo_r <= {`npuarc_DC_WAY_DATA_ECC_SIZE{1'b0}}; 
  end
  else if (dc_data_odd_din_lo_cg0)
  begin
    dc_data_odd_wem_lo_r <= dc_data_odd_wem_lo_next;
    dc_data_odd_din_lo_r <= dc_data_odd_din_lo_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_data_odd_hi_din_wem_reg_PROC
  if (rst_a == 1'b1)
  begin  
    dc_data_odd_wem_hi_r <= {`npuarc_DC_BE_ECC_SIZE{1'b0}};
    dc_data_odd_din_hi_r <= {`npuarc_DC_WAY_DATA_ECC_SIZE{1'b0}};
  end
  else if (dc_data_odd_din_hi_cg0)
  begin
    dc_data_odd_wem_hi_r <= dc_data_odd_wem_hi_next; 
    dc_data_odd_din_hi_r <= dc_data_odd_din_hi_next;
  end
end


always @(posedge clk or posedge rst_a)
begin : dc_data_even_addr_lo_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_data_even_addr_lo_r  <= {`npuarc_DC_ADR_BITS{1'b0}};
  end
  else if (dc_data_even_addr_lo_cg0)
  begin
// spyglass disable_block Reset_sync04
// SMD: Async reset signal is synchronized at least twice
// SJ:  other resync spot in alb_reset_ctrl already waived
    dc_data_even_addr_lo_r  <= dc_data_even_addr_lo_next;
// spyglass enable_block Reset_sync04
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_data_even_addr_hi_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_data_even_addr_hi_r  <= {`npuarc_DC_ADR_BITS{1'b0}};
  end
  else if (dc_data_even_addr_hi_cg0)
  begin
    dc_data_even_addr_hi_r  <= dc_data_even_addr_hi_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_data_odd_addr_lo_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_data_odd_addr_lo_r   <= {`npuarc_DC_ADR_BITS{1'b0}};
  end
  else if (dc_data_odd_addr_lo_cg0)
  begin
    dc_data_odd_addr_lo_r  <= dc_data_odd_addr_lo_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_data_odd_addr_hi_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_data_odd_addr_hi_r   <= {`npuarc_DC_ADR_BITS{1'b0}};
  end
  else if (dc_data_odd_addr_hi_cg0)
  begin
    dc_data_odd_addr_hi_r  <= dc_data_odd_addr_hi_next; 
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_data_way_hot_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_data_way_hot_r <= 2'b00;
  end
  else
  begin
    if (dc_data_way_hot_cg0)
    begin
      dc_data_way_hot_r <= dc_data_way_hot_nxt;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : dc_pipe_ack_dd_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_pipe_ack_dd_even_lo_r <= 1'b0;
    dc_pipe_ack_dd_even_hi_r <= 1'b0;
    dc_pipe_ack_dd_odd_lo_r  <= 1'b0;
    dc_pipe_ack_dd_odd_hi_r  <= 1'b0;
  end
  else
  begin
    dc_pipe_ack_dd_even_lo_r <= dc1_ack_dd_even_lo | dc2_ack_dd_even_lo;
    dc_pipe_ack_dd_even_hi_r <= dc1_ack_dd_even_hi | dc2_ack_dd_even_hi;
    dc_pipe_ack_dd_odd_lo_r  <= dc1_ack_dd_odd_lo  | dc2_ack_dd_odd_lo;
    dc_pipe_ack_dd_odd_hi_r  <= dc1_ack_dd_odd_hi  | dc2_ack_dd_odd_hi;
  end
end


always @ (posedge clk or posedge rst_a)
begin : dc3_dt_pred0_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_dt_pred0_r   <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
    dc3_dt_pred1_r   <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
  end
  else if (dc2_target_dc & x2_pass)
  begin
    dc3_dt_pred0_r <= dc2_pred0;  
    dc3_dt_pred1_r <= dc2_pred1;  
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc3_dd_pred0_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_pred0_r   <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
    dc3_pred1_r   <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
  end
  else if (dc2_target_dc & x2_pass)
  begin
    dc3_pred0_r <= dc2_pred0;  
    dc3_pred1_r <= dc2_pred1;  
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc4_dd_pred0_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_dd_pred0_r   <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
    dc4_dd_pred1_r   <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
  end
  else if (dc3_target_dc & x3_pass)
  begin
    dc4_dd_pred0_r <= dc3_pred0_r;
    dc4_dd_pred1_r <= dc3_pred1_r;
  end
end





always @ (posedge clk or posedge rst_a)
begin : dc3_data_bank_valid_reg_PROC
  if (rst_a == 1'b1)
    dc3_data_bank_valid_r <= 4'd0;  
  else
    dc3_data_bank_valid_r <= dc3_data_bank_valid_nxt;
end

always @ (posedge clk or posedge rst_a)
begin : dc3_bank0_reg_PROC
  integer e;
  if (rst_a == 1'b1)
  begin
    dc3_bank0_addr_r      <= {`npuarc_DC_ADR_BITS{1'b0}};
  end
  else if (dc3_data_bank_valid_cg0[0] == 1'b1)
  begin
    dc3_bank0_addr_r <= dc3_addr0_nxt[`npuarc_DC_ADR_RANGE];
  end
end
always @ (posedge clk or posedge rst_a)
begin : dc3_bank1_reg_PROC
  integer e;
  if (rst_a == 1'b1)
  begin
    dc3_bank1_addr_r      <= {`npuarc_DC_ADR_BITS{1'b0}};
  end
  else if (dc3_data_bank_valid_cg0[1] == 1'b1)
  begin
    dc3_bank1_addr_r <= dc3_addr0_nxt[`npuarc_DC_ADR_RANGE];
  end
end
always @ (posedge clk or posedge rst_a)
begin : dc3_bank2_reg_PROC
  integer e;
  if (rst_a == 1'b1)
  begin
    dc3_bank2_addr_r      <= {`npuarc_DC_ADR_BITS{1'b0}};
  end
  else if (dc3_data_bank_valid_cg0[2] == 1'b1)
  begin
    dc3_bank2_addr_r <= dc3_addr1_nxt[`npuarc_DC_ADR_RANGE];
  end
end
always @ (posedge clk or posedge rst_a)
begin : dc3_bank3_reg_PROC
  integer e;
  if (rst_a == 1'b1)
  begin
    dc3_bank3_addr_r      <= {`npuarc_DC_ADR_BITS{1'b0}};
  end
  else if (dc3_data_bank_valid_cg0[3] == 1'b1)
  begin
    dc3_bank3_addr_r <= dc3_addr1_nxt[`npuarc_DC_ADR_RANGE];
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc_dd_data_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc_dd_data_r <= 32'd0;
  end
  else if (|ecc_valid)
  begin
    dc_dd_data_r <= dc_dd_data;    
  end
end

always @ (posedge clk or posedge rst_a)
begin : dc4_skid_ecc_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_skid_ecc_valid_r   <= 4'b0000; 
  end
  else if (dc4_dd_ecc_error_valid_cg0)
  begin
    dc4_skid_ecc_valid_r <= dc3_skid_ecc_valid
                          | ({4{(dmu_evict_rd | aux_dd_data_read)}} & dc_data_read_r)   
                          ; 
  end
end

always @ (posedge clk or posedge rst_a)
begin : wa_restart_rr_reg_PROC
  if (rst_a == 1'b1)
  begin
    wa_restart_rr   <= 1'b0;
    wq_dmu_empty_r  <= 1'b0;
  end
  else
  begin
    wa_restart_rr   <= wa_restart_r;
    wq_dmu_empty_r  <= wq_empty & dmu_empty;
  end
end  


always @ (posedge clk or posedge rst_a)
begin : dc4_dt_ecc_sb_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_dt_ecc_sb_error_r <= 4'b0000;
  end
  else if (dc4_dt_ecc_sb_error_cg0)
  begin
    dc4_dt_ecc_sb_error_r <= dc4_dt_ecc_sb_error;
  end
end  


always @*
begin : bdcmstall_PROC
  dc_pct_bdcmstall = ( (dc4_dt_miss_r 
                         & (~dc4_dt_hit_r)
                         & dc4_stall_r 
                         & (dc4_target_r[2:0]== `npuarc_DMP_TARGET_DC))
                      | (dc1_load_store_valid & dmu_dc_stall_r));
end


//`if (`HAS_SAFETY == 1)
always @ (posedge clk or posedge rst_a)
begin : dc_tag_syndrome_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_dc_tag_bank0_syndrome_r <= {`npuarc_DC_TAG_SYNDROME_MSB+1{1'b0}};
    fs_dc_tag_bank1_syndrome_r <= {`npuarc_DC_TAG_SYNDROME_MSB+1{1'b0}};
    fs_dc_tag_bank2_syndrome_r <= {`npuarc_DC_TAG_SYNDROME_MSB+1{1'b0}};
    fs_dc_tag_bank3_syndrome_r <= {`npuarc_DC_TAG_SYNDROME_MSB+1{1'b0}};
  end
  else
  begin
    fs_dc_tag_bank0_syndrome_r <= syndrome_dt_0;
    fs_dc_tag_bank1_syndrome_r <= syndrome_dt_1;
    fs_dc_tag_bank2_syndrome_r <= syndrome_dt_2;
    fs_dc_tag_bank3_syndrome_r <= syndrome_dt_3;
  end  
end

always @ (posedge clk or posedge rst_a)
begin : fs_dc_tag_bank0_ecc_sb_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_dc_tag_bank0_ecc_sb_error_r  <= 1'b0;
    fs_dc_tag_bank1_ecc_sb_error_r  <= 1'b0;
    fs_dc_tag_bank2_ecc_sb_error_r  <= 1'b0;
    fs_dc_tag_bank3_ecc_sb_error_r  <= 1'b0;
  end
  else
  begin
    fs_dc_tag_bank0_ecc_sb_error_r  <= dc4_dt_ecc_sb_error[0];
    fs_dc_tag_bank1_ecc_sb_error_r  <= dc4_dt_ecc_sb_error[1];
    fs_dc_tag_bank2_ecc_sb_error_r  <= dc4_dt_ecc_sb_error[2];
    fs_dc_tag_bank3_ecc_sb_error_r  <= dc4_dt_ecc_sb_error[3];
  end  
end

always @ (posedge clk or posedge rst_a)
begin : fs_dc_tag_bank0_ecc_db_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_dc_tag_bank0_ecc_db_error_r  <= 1'b0;
    fs_dc_tag_bank1_ecc_db_error_r  <= 1'b0;
    fs_dc_tag_bank2_ecc_db_error_r  <= 1'b0;
    fs_dc_tag_bank3_ecc_db_error_r  <= 1'b0;
  end
  else
  begin
    fs_dc_tag_bank0_ecc_db_error_r  <= dc4_dt_ecc_db_error[0];
    fs_dc_tag_bank1_ecc_db_error_r  <= dc4_dt_ecc_db_error[1];
    fs_dc_tag_bank2_ecc_db_error_r  <= dc4_dt_ecc_db_error[2];
    fs_dc_tag_bank3_ecc_db_error_r  <= dc4_dt_ecc_db_error[3];
  end
end


always @ (posedge clk or posedge rst_a)
begin : dc_data_syndrome_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_dc_data_bank0_syndrome_r   <= {`npuarc_SYNDROME_MSB+1{1'b0}};
    fs_dc_data_bank1_syndrome_r   <= {`npuarc_SYNDROME_MSB+1{1'b0}};
    fs_dc_data_bank2_syndrome_r   <= {`npuarc_SYNDROME_MSB+1{1'b0}};
    fs_dc_data_bank3_syndrome_r   <= {`npuarc_SYNDROME_MSB+1{1'b0}};
  end
  else
  begin
   fs_dc_data_bank0_syndrome_r    <= dc4_ecc_skid_sb_error_r[0] ? dc_skid_bank0_syndrome_r : syndrome_dd_0_r;
   fs_dc_data_bank1_syndrome_r    <= dc4_ecc_skid_sb_error_r[1] ? dc_skid_bank1_syndrome_r : syndrome_dd_1_r;
   fs_dc_data_bank2_syndrome_r    <= dc4_ecc_skid_sb_error_r[2] ? dc_skid_bank2_syndrome_r : syndrome_dd_2_r;
   fs_dc_data_bank3_syndrome_r    <= dc4_ecc_skid_sb_error_r[3] ? dc_skid_bank3_syndrome_r : syndrome_dd_3_r;
  end  
end

always @ (posedge clk or posedge rst_a)
begin : fs_dc_data_bank0_ecc_sb_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_dc_data_bank0_ecc_sb_error_r  <= 1'b0;
    fs_dc_data_bank1_ecc_sb_error_r  <= 1'b0;
    fs_dc_data_bank2_ecc_sb_error_r  <= 1'b0;
    fs_dc_data_bank3_ecc_sb_error_r  <= 1'b0;
  end
  else
  begin
    fs_dc_data_bank0_ecc_sb_error_r  <= dc4_dd_ecc_sb_error[0];
    fs_dc_data_bank1_ecc_sb_error_r  <= dc4_dd_ecc_sb_error[1];
    fs_dc_data_bank2_ecc_sb_error_r  <= dc4_dd_ecc_sb_error[2];
    fs_dc_data_bank3_ecc_sb_error_r  <= dc4_dd_ecc_sb_error[3];
  end
end

always @ (posedge clk or posedge rst_a)
begin : fs_dc_data_bank0_ecc_db_error_reg_PROC
  if (rst_a == 1'b1)
  begin
    fs_dc_data_bank0_ecc_db_error_r  <= 1'b0;
    fs_dc_data_bank1_ecc_db_error_r  <= 1'b0;
    fs_dc_data_bank2_ecc_db_error_r  <= 1'b0;
    fs_dc_data_bank3_ecc_db_error_r  <= 1'b0;
  end
  else
  begin
    fs_dc_data_bank0_ecc_db_error_r  <= dc4_dd_ecc_db_error[0];
    fs_dc_data_bank1_ecc_db_error_r  <= dc4_dd_ecc_db_error[1];
    fs_dc_data_bank2_ecc_db_error_r  <= dc4_dd_ecc_db_error[2];
    fs_dc_data_bank3_ecc_db_error_r  <= dc4_dd_ecc_db_error[3];
  end
end

//    `endif

// leda W175 on


endmodule // alb_dmp_dcache

