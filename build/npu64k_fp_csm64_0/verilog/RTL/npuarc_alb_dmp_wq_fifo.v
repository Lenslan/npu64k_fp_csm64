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
//   ALB_DMP_WQ_FIFO                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Write Queue Fifo.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_wq_fifo.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"



//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

//D: error_signal { name: "alb_dmp_wq_bfifo_0_edc_err" }

module npuarc_alb_dmp_wq_fifo (
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some inputs are not used in certain configurations
  
  ////////// General input signals ///////////////////////////////////////////
  //
  input                         clk,                 // clock
  input                         rst_a,               // reset

  input                         ecc_dmp_disable,     // ECC disable
    
  input                         holdup_excpn_r,
  output reg                    st_instrs_discarded,
  input                         st_instrs_discarded_r,
  ////////// Entry of the FIFO ///////////////////////////////////////////////
  //
  input                         ca_pass,
  input                         ca_store_r,
  input                         ca_load_r,
  input                         ca_locked_r,

  input [`npuarc_PADDR_RANGE]          ca_mem_addr0_r,      // CA memory address
  input [`npuarc_PADDR_RANGE]          dc4_mem_addr1_r,
  input [2:0]                   dc4_size0_r,
  input [2:0]                   dc4_size1_r,
  input [`npuarc_DMP_DATA_RANGE]       ca_wr_data_r, 
  input [1:0]                   ca_size_r,
  input                         ca_user_mode_r,
  input [3:0]                   ca_data_bank_sel_r,
  input                         ca_volatile_r,
  input                         ca_strict_order_r,
  input                         ca_data_mem_attr_r,
  input                         ca_dmi_scrubbing_conflict, // avoids scrubbing

  input [1:0]                   ca_store_grad_r,
  input [1:0]                   ca_store_grad_swap_r,
  input [`npuarc_GRAD_TAG_RANGE]       ca_store_grad_tag_lo_r,
  input [`npuarc_GRAD_TAG_RANGE]       ca_store_grad_tag_hi_r,

  input                         wa_retire1_valid,
  input                         wa_retire1_garbage,
  input [`npuarc_GRAD_TAG_RANGE]       wa_retire1_tag,
  input [`npuarc_DOUBLE_RANGE]         wa_retire1_data,


  output reg [1:0]              ca_store_grad_tag,

  output reg                    dmp_st_retire0_r,
  output reg [1:0]              dmp_st_retire0_tag_r,
  output reg [`npuarc_DMP_DATA_RANGE]  dmp_st_retire0_data_r,

  output reg                    dmp_st_retire1_r,
  output reg [1:0]              dmp_st_retire1_tag_r,
  output reg [`npuarc_DMP_DATA_RANGE]  dmp_st_retire1_data_r,
  

  input                         db_active_r,
  input                         wa_restart_r,
  
  input                         dmp_wq_write0,        // store instr enters wq
  input [`npuarc_DMP_DATA_RANGE]       dmp_wq_data0,         // write data
  input [2:0]                   dmp_wq_size0,         // write size
  input [`npuarc_PADDR_RANGE]          dmp_wq_addr0,         // address
  input [`npuarc_DMP_TARGET_RANGE]     dmp_wq_target0,       // internal or ext memories
  input [1:0]                   dmp_wq_bank_lo0,      // bank sel
  input [1:0]                   dmp_wq_bank_hi0,      // bank sel
  input [`npuarc_DC_WAY_RANGE]         dmp_wq_way_hot0,      // way info

  input [`npuarc_DMP_BE_RANGE]         dmp_wq_ecc_data_mask0, // ecc mask for partial grad stores
  input                         dmp_wq_write1,        // store instr enters wq
  input [`npuarc_DMP_DATA_RANGE]       dmp_wq_data1,         // write data
  input [2:0]                   dmp_wq_size1,         // write size
  input [`npuarc_PADDR_RANGE]          dmp_wq_addr1,         // address
  input [`npuarc_DMP_TARGET_RANGE]     dmp_wq_target1,       // internal or ext memories
  input [1:0]                   dmp_wq_bank_lo1,      // bank sel
  input [1:0]                   dmp_wq_bank_hi1,      // bank sel
  input [`npuarc_DC_WAY_RANGE]         dmp_wq_way_hot1,      // way info

  input [`npuarc_DMP_BE_RANGE]         dmp_wq_ecc_data_mask1, // ecc mask for partial grad stores
  ////////// Interface to the SA stage //////////////////////////////////////
  //
  input                         sa_dsync_op_r,        // SA is a DSYNC insn.
  input                         sa_dmb_op_r,          // SA is a DMB insn.
  input                         sa_dmb_stall,         // SA stall due to DMB

  input  [`npuarc_ADDR_RANGE]          x2_mem_addr0_r,
  input                         x2_load_r,
  input  [1:0]                  x2_size_r,
  input                         x2_pass,
  input  [3:0]                  dc2_rmw_r,
  input  [3:0]                  dc2_data_bank_sel_r,
  input  [`npuarc_ADDR_RANGE]          dc2_mem_addr1_r,
  
  ////////// Interface to X2 /////////////////////////////////////////////
  //
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                         dc2_dc_uop_stall,    // X2 uop stall
  ////////// DMU interface //////////////////////////////////////////////
  //
  input                         dmu_empty,
// spyglass enable_block W240
  input [`npuarc_DC_SET_RANGE]         dmu_set_addr,        // set addr, top of MQ

  ////////// Conflict detection with DC3 loads ////////////////////////////////
  //
  input                         x3_load_r,           // X3 load  
  input                         x3_store_r,          // X3 store 
  input                         x3_store_may_grad,
  input                         x3_pass,           
  output reg                    dc3_stall_r,
  output reg                    dc3_partial_or_multi_conflict,
  input                         x3_sync_op_r, 
  input                         x3_brk_op_r, 
  input [`npuarc_PADDR_RANGE]          x3_mem_addr0_r,      // X3 memory address
  input [`npuarc_PADDR_RANGE]          x3_mem_addr1_r,      // X3 memory address
  input [2:0]                   dc3_size0_r,         //
  input [2:0]                   dc3_size1_r,         //
  input [3:0]                   dc3_bank_sel_r,
  input [`npuarc_DMP_TARGET_RANGE]     dc3_target_r,        // DC3 target
  input [3:0]                   dc3_rmw_r,
  input                         dc3_fwd_allowed_r,   // store to ld fwd allowed
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                         dc4_stall_r,
// spyglass enable_block W240
  input [`npuarc_DMP_TARGET_RANGE]     dc4_target_r,

  input                         dc4_ecc_sb_error_r,
  output reg                    wq_fwd_replay,
  output reg [3:0]              wq_fwd_bank,
  output reg [`npuarc_DATA_RANGE]      wq_fwd_data_bank0_lo,
  output reg [`npuarc_DATA_RANGE]      wq_fwd_data_bank0_hi,
  output reg [`npuarc_DATA_RANGE]      wq_fwd_data_bank1_lo,
  output reg [`npuarc_DATA_RANGE]      wq_fwd_data_bank1_hi,
// spyglass disable_block UndrivenOutPort-ML W241
// SMD: undriven output
// SJ:  unused when undriven
  output reg [15:0]             wq_skid_ctrl_mask,    // byte mask ctrl to skid 
// spyglass enable_block UndrivenOutPort-ML W241
  ////////// Removal from the FIFO /////////////////////////////////////////////
  //
  input                         wq_mem_read,          // entry processed
  input                         wq_mem_wr_done,       // entry retired
  input                         wq_mem_wr_excl_done,  // entry retired
  input                         wq_mem_err_wr,        // entry retired
  input                         wq_dc_read,       // entry processed & retired
  input                         wq_dccm_read_one, // entry processed & retired
  input                         wq_dccm_read_two, // entries processed & retired

  output reg                    wq_dc_retire_one,
  output reg                    wq_dc_retire_two,
  output reg                    wq_retire,
  
  ////////// External Entry to be processed //////////////////////////////////////////////
  //
  output reg                      wq_ext_valid,
  output reg                      wq_ext_bufferable,
  output reg [`npuarc_DOUBLE_RANGE]      wq_ext_data_bank0,   
  output reg [`npuarc_DOUBLE_RANGE]      wq_ext_data_bank1,   
  output reg [`npuarc_DOUBLE_BE_RANGE]   wq_ext_mask_bank0,   
  output reg [`npuarc_DOUBLE_BE_RANGE]   wq_ext_mask_bank1,   
  output reg [`npuarc_PADDR_RANGE]       wq_ext_addr,   
  output reg [1:0]                wq_ext_size,   
  output reg                      wq_ext_user_mode,   
  output reg [`npuarc_DMP_TARGET_RANGE]  wq_ext_target, 
  output reg [3:0]                wq_ext_top_bank_req_mask,
  output reg                      wq_ext_scond,
  ////////// Internal Entry to be processed //////////////////////////////////////////////
  //
// spyglass disable_block W241
// SMD: output declared but not set
// SJ:  unused in some configs
  output reg                      wq_dc_valid,
// spyglass enable_block W241
  output reg [`npuarc_DC_WAY_RANGE]      wq_way_hot,
// spyglass disable_block W241
// SMD: output declared but not set
// SJ:  unused in some configs
  output reg [`npuarc_DOUBLE_RANGE]      wq_dc_data_bank0,   
  output reg [`npuarc_DOUBLE_RANGE]      wq_dc_data_bank1,   
  output reg [`npuarc_DOUBLE_BE_RANGE]   wq_dc_mask_bank0,   
  output reg [`npuarc_DOUBLE_BE_RANGE]   wq_dc_mask_bank1,   

  output reg [`npuarc_PADDR_RANGE]       wq_dc_addr,   
  output reg [`npuarc_DMP_TARGET_RANGE]  wq_dc_target, 
  output reg [3:0]                wq_dc_top_bank_req_mask,
// spyglass enable_block W241

  output reg [3:0]                wq_dccm_top_bank_req_mask,
  output reg [3:0]                wq_dccm_sec_bank_req_mask,

  ////////// Sec entry to be processed //////////////////////////////////////////////
  //
  output reg                     wq_sec_valid,
  output reg [`npuarc_DMP_TARGET_RANGE] wq_sec_target,
  output reg [3:0]               wq_sec_bank_req_mask,
  output reg [`npuarc_PADDR_RANGE]      wq_sec_addr,
  output reg [`npuarc_DOUBLE_BE_RANGE]  wq_sec_mask_bank0,
  output reg [`npuarc_DOUBLE_BE_RANGE]  wq_sec_mask_bank1,

  output reg [`npuarc_DOUBLE_RANGE]     wq_sec_data_bank0,
  output reg [`npuarc_DOUBLE_RANGE]     wq_sec_data_bank1,

  
 
  output reg                     wq_mem_scond,


  ////////// WQ forwarding ////////////////////////////////////////////////
  //
  output reg                     dc3_fwd_req,
  

  ////////// Error reporting /////////////////////////////////////////////
  //
  output                        wq_err_r,
  output                        wq_err_user_mode_r,
  output [`npuarc_PADDR_RANGE]         wq_err_addr_r,       
  input                         wq_err_ack,        

  //////////  Outputs to LQ synchronization //////////////////////////////////
  // 
  output reg [`npuarc_DMP_FIFO_RANGE]  wq_order_ptr_1h,      // WQ most recent external entry
  output reg                    dc4_raw_hazard,       // RAW hazard
  
  output reg                    wq_mem_per_iccm_read, // WQ entry processed
  output reg [`npuarc_WQ_PTR_RANGE]    wq_ext_rdentry0,      // WQ processed entry
 
  output reg                    wq_mem_retire,        // WQ mem entry retired
  output [`npuarc_WQ_PTR_RANGE]        wq_mem_entry_id,      // WQ retired  entry
 
 

  
  //////////  Inputs for WQ  synchronization /////////////////////////////////
  //
  input [`npuarc_DMP_FIFO_RANGE]       lq_order_ptr_1h,      // LQ most recent entry
  input                         dc4_war_hazard,       // RAW hazard
  
  input                         lq_cmd_read,         // LQ command  popped
  input [`npuarc_LQ_PTR_RANGE]         lq_cmd_rd_ptr,       // LQ command read pointer

  input                         lq_data_retire,      // LQ data retired
  input                         lq_data_err,         // LQ data retired with an error
  input [`npuarc_LQ_PTR_RANGE]         lq_data_rd_ptr,      // LQ data read pointer
  
  ////////// FIFO status ////////////////////////////////////////////////////
  //
  output reg                    wq_dc_entry,
  output reg                    wq_scond_entry,

  output reg                    wq_target_dc,
  output reg                    wq_dmu_set_conflict,
  output reg                    wq_non_dc_entry,
  output reg                    wq_ex_non_dc_entry,
  output reg [`npuarc_DMP_FIFO_RANGE]  wq_valid_r
// leda NTL_CON13C on
);
  
// Local Declarations
//



reg                        wq_dc_scond;

reg [`npuarc_DC_WAY_RANGE]        wq_sec_way_hot;

reg                        wq_merge_write;

reg  [`npuarc_DMP_DATA_RANGE]     wq_data0;       
reg  [2:0]                 wq_size0;       
reg  [`npuarc_PADDR_RANGE]        wq_addr0;       
reg  [3:0]                 wq_bank_mask0;  
reg  [`npuarc_DMP_TARGET_RANGE]   wq_target0;     
reg  [`npuarc_DC_WAY_RANGE]       wq_way_hot0;    
reg  [`npuarc_DMP_BE_RANGE]       wq_ecc_mask0;
reg  [`npuarc_DMP_BE_RANGE]       wq_ecc_mask1;

reg  [`npuarc_DMP_BE_RANGE]       wq_data_mask0;
reg  [`npuarc_DMP_BE_RANGE]       wq_data_mask1;

reg  [`npuarc_DMP_DATA_RANGE]     wq_data1;       
reg  [2:0]                 wq_size1;      
reg  [`npuarc_PADDR_RANGE]        wq_addr1;       
reg  [3:0]                 wq_bank_mask1; 
reg  [`npuarc_DMP_TARGET_RANGE]   wq_target1;  
reg  [`npuarc_DC_WAY_RANGE]       wq_way_hot1;    

wire                       wq_addr_cg1;
wire                       wq_data_cg1;

// leda NTL_CON12A off
// LMD: undriven internal net 
// LJ:  not all variables used in some congigurations

reg                        wq0_data_cg0;
reg                        wq0_addr_cg0;
reg                        wq0_ctl_cg0;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//    
reg  [`npuarc_DMP_DATA_RANGE]     wq0_data_nxt;  
// leda NTL_CON32 on
reg  [2:0]                 wq0_size_nxt;  

reg  [`npuarc_DMP_BE_RANGE]       wq0_ecc_mask_nxt;
reg  [`npuarc_DMP_BE_RANGE]       wq0_ecc_mask_r;
reg  [2:0]                 wq0_ecc_addr_r;
reg  [2:0]                 wq0_ecc_addr_nxt;

reg  [`npuarc_DMP_BE_RANGE]       wq0_data_mask_nxt;
reg  [`npuarc_DMP_BE_RANGE]       wq0_data_mask_r;

reg  [`npuarc_GRAD_TAG_RANGE]     wq0_grad_tag_lo_nxt;
reg  [`npuarc_GRAD_TAG_RANGE]     wq0_grad_tag_hi_nxt;
reg  [`npuarc_GRAD_TAG_RANGE]     wq0_grad_tag_lo_r;
reg  [`npuarc_GRAD_TAG_RANGE]     wq0_grad_tag_hi_r;
reg  [1:0]                 wq0_grad_nxt;
reg  [1:0]                 wq0_grad_r;
reg  [1:0]                 wq0_grad_data_src_nxt;
reg  [1:0]                 wq0_grad_data_src_r;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg                        wq0_user_mode_nxt;  
reg                        wq0_debug_nxt;  
// leda NTL_CON32 on
reg  [`npuarc_PADDR_RANGE]        wq0_addr_nxt;   
reg  [`npuarc_DMP_TARGET_RANGE]   wq0_target_nxt;  
reg  [3:0]                 wq0_bank_mask_nxt;
reg                        wq0_external_ex_nxt;
reg                        wq0_scond_nxt;  
reg  [`npuarc_DC_WAY_RANGE]       wq0_way_hot_nxt; 
reg  [`npuarc_DMP_FIFO_RANGE]     wq0_dep_nxt;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [`npuarc_DMP_DATA_RANGE]     wq0_data_r;   
reg  [`npuarc_DMP_DATA_RANGE]     wq0_rtt_grad_data_r;
reg  [`npuarc_DMP_DATA_RANGE]     wq0_rtt_grad_data_nxt;
// leda NTL_CON32 on
reg  [2:0]                 wq0_size_r;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg                        wq0_user_mode_r;  
reg                        wq0_debug_r;  
// leda NTL_CON32 on
reg  [`npuarc_PADDR_RANGE]        wq0_addr_r;   
reg  [`npuarc_DMP_TARGET_RANGE]   wq0_target_r;   
reg  [3:0]                 wq0_bank_mask_r;  
reg                        wq0_external_ex_r;
reg                        wq0_store_grad_match1_lo;
reg                        wq0_store_grad_match1_hi;
wire                       wq0_store_grad_match1;
reg                        wq0_store_grad_match1_lo_garbage;
reg                        wq0_store_grad_match1_hi_garbage;
wire                       wq0_store_grad_match1_garbage;
reg                        wq0_scond_r;  
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [`npuarc_DC_WAY_RANGE]       wq0_way_hot_r; 
// leda NTL_CON32 on
reg  [`npuarc_DMP_FIFO_RANGE]     wq0_dep_r;

reg                        wr0_0;
reg                        wr0_1;
reg                        wr0_merge;
reg                        wq1_data_cg0;
reg                        wq1_addr_cg0;
reg                        wq1_ctl_cg0;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//    
reg  [`npuarc_DMP_DATA_RANGE]     wq1_data_nxt;  
// leda NTL_CON32 on
reg  [2:0]                 wq1_size_nxt;  

reg  [`npuarc_DMP_BE_RANGE]       wq1_ecc_mask_nxt;
reg  [`npuarc_DMP_BE_RANGE]       wq1_ecc_mask_r;
reg  [2:0]                 wq1_ecc_addr_r;
reg  [2:0]                 wq1_ecc_addr_nxt;

reg  [`npuarc_DMP_BE_RANGE]       wq1_data_mask_nxt;
reg  [`npuarc_DMP_BE_RANGE]       wq1_data_mask_r;

reg  [`npuarc_GRAD_TAG_RANGE]     wq1_grad_tag_lo_nxt;
reg  [`npuarc_GRAD_TAG_RANGE]     wq1_grad_tag_hi_nxt;
reg  [`npuarc_GRAD_TAG_RANGE]     wq1_grad_tag_lo_r;
reg  [`npuarc_GRAD_TAG_RANGE]     wq1_grad_tag_hi_r;
reg  [1:0]                 wq1_grad_nxt;
reg  [1:0]                 wq1_grad_r;
reg  [1:0]                 wq1_grad_data_src_nxt;
reg  [1:0]                 wq1_grad_data_src_r;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg                        wq1_user_mode_nxt;  
reg                        wq1_debug_nxt;  
// leda NTL_CON32 on
reg  [`npuarc_PADDR_RANGE]        wq1_addr_nxt;   
reg  [`npuarc_DMP_TARGET_RANGE]   wq1_target_nxt;  
reg  [3:0]                 wq1_bank_mask_nxt;
reg                        wq1_external_ex_nxt;
reg                        wq1_scond_nxt;  
reg  [`npuarc_DC_WAY_RANGE]       wq1_way_hot_nxt; 
reg  [`npuarc_DMP_FIFO_RANGE]     wq1_dep_nxt;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [`npuarc_DMP_DATA_RANGE]     wq1_data_r;   
reg  [`npuarc_DMP_DATA_RANGE]     wq1_rtt_grad_data_r;
reg  [`npuarc_DMP_DATA_RANGE]     wq1_rtt_grad_data_nxt;
// leda NTL_CON32 on
reg  [2:0]                 wq1_size_r;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg                        wq1_user_mode_r;  
reg                        wq1_debug_r;  
// leda NTL_CON32 on
reg  [`npuarc_PADDR_RANGE]        wq1_addr_r;   
reg  [`npuarc_DMP_TARGET_RANGE]   wq1_target_r;   
reg  [3:0]                 wq1_bank_mask_r;  
reg                        wq1_external_ex_r;
reg                        wq1_store_grad_match1_lo;
reg                        wq1_store_grad_match1_hi;
wire                       wq1_store_grad_match1;
reg                        wq1_store_grad_match1_lo_garbage;
reg                        wq1_store_grad_match1_hi_garbage;
wire                       wq1_store_grad_match1_garbage;
reg                        wq1_scond_r;  
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [`npuarc_DC_WAY_RANGE]       wq1_way_hot_r; 
// leda NTL_CON32 on
reg  [`npuarc_DMP_FIFO_RANGE]     wq1_dep_r;

reg                        wr1_0;
reg                        wr1_1;
reg                        wr1_merge;
reg                        wq2_data_cg0;
reg                        wq2_addr_cg0;
reg                        wq2_ctl_cg0;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//    
reg  [`npuarc_DMP_DATA_RANGE]     wq2_data_nxt;  
// leda NTL_CON32 on
reg  [2:0]                 wq2_size_nxt;  

reg  [`npuarc_DMP_BE_RANGE]       wq2_ecc_mask_nxt;
reg  [`npuarc_DMP_BE_RANGE]       wq2_ecc_mask_r;
reg  [2:0]                 wq2_ecc_addr_r;
reg  [2:0]                 wq2_ecc_addr_nxt;

reg  [`npuarc_DMP_BE_RANGE]       wq2_data_mask_nxt;
reg  [`npuarc_DMP_BE_RANGE]       wq2_data_mask_r;

reg  [`npuarc_GRAD_TAG_RANGE]     wq2_grad_tag_lo_nxt;
reg  [`npuarc_GRAD_TAG_RANGE]     wq2_grad_tag_hi_nxt;
reg  [`npuarc_GRAD_TAG_RANGE]     wq2_grad_tag_lo_r;
reg  [`npuarc_GRAD_TAG_RANGE]     wq2_grad_tag_hi_r;
reg  [1:0]                 wq2_grad_nxt;
reg  [1:0]                 wq2_grad_r;
reg  [1:0]                 wq2_grad_data_src_nxt;
reg  [1:0]                 wq2_grad_data_src_r;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg                        wq2_user_mode_nxt;  
reg                        wq2_debug_nxt;  
// leda NTL_CON32 on
reg  [`npuarc_PADDR_RANGE]        wq2_addr_nxt;   
reg  [`npuarc_DMP_TARGET_RANGE]   wq2_target_nxt;  
reg  [3:0]                 wq2_bank_mask_nxt;
reg                        wq2_external_ex_nxt;
reg                        wq2_scond_nxt;  
reg  [`npuarc_DC_WAY_RANGE]       wq2_way_hot_nxt; 
reg  [`npuarc_DMP_FIFO_RANGE]     wq2_dep_nxt;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [`npuarc_DMP_DATA_RANGE]     wq2_data_r;   
reg  [`npuarc_DMP_DATA_RANGE]     wq2_rtt_grad_data_r;
reg  [`npuarc_DMP_DATA_RANGE]     wq2_rtt_grad_data_nxt;
// leda NTL_CON32 on
reg  [2:0]                 wq2_size_r;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg                        wq2_user_mode_r;  
reg                        wq2_debug_r;  
// leda NTL_CON32 on
reg  [`npuarc_PADDR_RANGE]        wq2_addr_r;   
reg  [`npuarc_DMP_TARGET_RANGE]   wq2_target_r;   
reg  [3:0]                 wq2_bank_mask_r;  
reg                        wq2_external_ex_r;
reg                        wq2_store_grad_match1_lo;
reg                        wq2_store_grad_match1_hi;
wire                       wq2_store_grad_match1;
reg                        wq2_store_grad_match1_lo_garbage;
reg                        wq2_store_grad_match1_hi_garbage;
wire                       wq2_store_grad_match1_garbage;
reg                        wq2_scond_r;  
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [`npuarc_DC_WAY_RANGE]       wq2_way_hot_r; 
// leda NTL_CON32 on
reg  [`npuarc_DMP_FIFO_RANGE]     wq2_dep_r;

reg                        wr2_0;
reg                        wr2_1;
reg                        wr2_merge;
reg                        wq3_data_cg0;
reg                        wq3_addr_cg0;
reg                        wq3_ctl_cg0;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//    
reg  [`npuarc_DMP_DATA_RANGE]     wq3_data_nxt;  
// leda NTL_CON32 on
reg  [2:0]                 wq3_size_nxt;  

reg  [`npuarc_DMP_BE_RANGE]       wq3_ecc_mask_nxt;
reg  [`npuarc_DMP_BE_RANGE]       wq3_ecc_mask_r;
reg  [2:0]                 wq3_ecc_addr_r;
reg  [2:0]                 wq3_ecc_addr_nxt;

reg  [`npuarc_DMP_BE_RANGE]       wq3_data_mask_nxt;
reg  [`npuarc_DMP_BE_RANGE]       wq3_data_mask_r;

reg  [`npuarc_GRAD_TAG_RANGE]     wq3_grad_tag_lo_nxt;
reg  [`npuarc_GRAD_TAG_RANGE]     wq3_grad_tag_hi_nxt;
reg  [`npuarc_GRAD_TAG_RANGE]     wq3_grad_tag_lo_r;
reg  [`npuarc_GRAD_TAG_RANGE]     wq3_grad_tag_hi_r;
reg  [1:0]                 wq3_grad_nxt;
reg  [1:0]                 wq3_grad_r;
reg  [1:0]                 wq3_grad_data_src_nxt;
reg  [1:0]                 wq3_grad_data_src_r;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg                        wq3_user_mode_nxt;  
reg                        wq3_debug_nxt;  
// leda NTL_CON32 on
reg  [`npuarc_PADDR_RANGE]        wq3_addr_nxt;   
reg  [`npuarc_DMP_TARGET_RANGE]   wq3_target_nxt;  
reg  [3:0]                 wq3_bank_mask_nxt;
reg                        wq3_external_ex_nxt;
reg                        wq3_scond_nxt;  
reg  [`npuarc_DC_WAY_RANGE]       wq3_way_hot_nxt; 
reg  [`npuarc_DMP_FIFO_RANGE]     wq3_dep_nxt;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [`npuarc_DMP_DATA_RANGE]     wq3_data_r;   
reg  [`npuarc_DMP_DATA_RANGE]     wq3_rtt_grad_data_r;
reg  [`npuarc_DMP_DATA_RANGE]     wq3_rtt_grad_data_nxt;
// leda NTL_CON32 on
reg  [2:0]                 wq3_size_r;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg                        wq3_user_mode_r;  
reg                        wq3_debug_r;  
// leda NTL_CON32 on
reg  [`npuarc_PADDR_RANGE]        wq3_addr_r;   
reg  [`npuarc_DMP_TARGET_RANGE]   wq3_target_r;   
reg  [3:0]                 wq3_bank_mask_r;  
reg                        wq3_external_ex_r;
reg                        wq3_store_grad_match1_lo;
reg                        wq3_store_grad_match1_hi;
wire                       wq3_store_grad_match1;
reg                        wq3_store_grad_match1_lo_garbage;
reg                        wq3_store_grad_match1_hi_garbage;
wire                       wq3_store_grad_match1_garbage;
reg                        wq3_scond_r;  
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg  [`npuarc_DC_WAY_RANGE]       wq3_way_hot_r; 
// leda NTL_CON32 on
reg  [`npuarc_DMP_FIFO_RANGE]     wq3_dep_r;

reg                        wr3_0;
reg                        wr3_1;
reg                        wr3_merge;

reg [`npuarc_DMP_FIFO_RANGE]      wq_strict_order_r;
reg [`npuarc_DMP_FIFO_RANGE]      wq_data_mem_attr_r;
reg [`npuarc_DMP_FIFO_RANGE]      wq0_lq_dep_r;
reg [`npuarc_DMP_FIFO_RANGE]      wq1_lq_dep_r;
reg [`npuarc_DMP_FIFO_RANGE]      wq2_lq_dep_r;
reg [`npuarc_DMP_FIFO_RANGE]      wq3_lq_dep_r;

reg [`npuarc_DMP_FIFO_RANGE]      wq_grad_st_rtt_r;

reg [`npuarc_DMP_FIFO_RANGE]      wq_recent_wr_r;
reg [`npuarc_DMP_FIFO_RANGE]      wq_recent_external_wr_r;
reg [`npuarc_DMP_FIFO_RANGE]      wq_volatile_r;
reg [`npuarc_DMP_FIFO_RANGE]      wq_external_entries;
reg [`npuarc_DMP_FIFO_RANGE]      wq_internal_entries;

reg [`npuarc_DMP_FIFO_RANGE]      wq_out_r;
reg [`npuarc_DMP_FIFO_RANGE]      wq_garbage_r;
reg [`npuarc_DMP_FIFO_RANGE]      wq_strict_garbage;
reg [`npuarc_DMP_FIFO_RANGE]      wq_order_garbage;
reg [`npuarc_DMP_FIFO_RANGE]      wq_grad_garbage;
reg [`npuarc_DMP_FIFO_RANGE]      wq_set_garbage;
reg [`npuarc_DMP_FIFO_RANGE]      lq_retire_error;

reg                        dc30_dc40_mask_conflict;
reg                        dc30_dc40_addr_conflict;
reg                        dc30_dc41_mask_conflict;
reg                        dc30_dc41_addr_conflict;
reg                        dc31_dc40_mask_conflict;
reg                        dc31_dc40_addr_conflict;
reg                        dc30_wq0_mask_conflict; 
reg                        dc30_wq0_addr_conflict; 
reg                        dc31_wq0_mask_conflict; 
reg                        dc31_wq0_addr_conflict; 
reg                        dc30_wq1_mask_conflict; 
reg                        dc30_wq1_addr_conflict; 
reg                        dc31_wq1_mask_conflict; 
reg                        dc31_wq1_addr_conflict; 
reg                        dc30_wq2_mask_conflict; 
reg                        dc30_wq2_addr_conflict; 
reg                        dc31_wq2_mask_conflict; 
reg                        dc31_wq2_addr_conflict; 
reg                        dc30_wq3_mask_conflict; 
reg                        dc30_wq3_addr_conflict; 
reg                        dc31_wq3_mask_conflict; 
reg                        dc31_wq3_addr_conflict; 
reg                        dc3_addr_conflict;
reg                        dc3_dc4_conflict;
//reg                        dc3_partial_or_multi_conflict;
reg [3:0]                  dc3_wq_conflict;

reg                        dc40_addr0_match;
reg                        dc41_addr0_match;
reg                        dc40_addr1_match;
reg                        dc41_addr1_match;
reg                        dc40_addr0_match_qual;
reg                        dc41_addr0_match_qual;
reg                        dc40_addr1_match_qual;
reg                        dc41_addr1_match_qual;

reg                        wq0_addr0_match;   
reg                        wq0_addr1_match;   
reg                        wq0_addr0_match_qual;   
reg                        wq0_addr1_match_qual;   
reg                        wq1_addr0_match;   
reg                        wq1_addr1_match;   
reg                        wq1_addr0_match_qual;   
reg                        wq1_addr1_match_qual;   
reg                        wq2_addr0_match;   
reg                        wq2_addr1_match;   
reg                        wq2_addr0_match_qual;   
reg                        wq2_addr1_match_qual;   
reg                        wq3_addr0_match;   
reg                        wq3_addr1_match;   
reg                        wq3_addr0_match_qual;   
reg                        wq3_addr1_match_qual;   
// leda NTL_CON12A on


// leda NTL_CON12A off
// leda NTL_CON13A off
// LMD: undriven internal net
// LJ:  These are wires that are declared bu not used
wire                       match0_dc40_bank1_hi;
wire                       match0_dc41_bank1_hi;
wire                       match0_wq0_bank0_lo;           
wire                       match0_wq1_bank0_lo;           
wire                       match0_wq2_bank0_lo;           
wire                       match0_wq3_bank0_lo;           
wire                       match0_wq0_bank0_hi;
wire                       match0_wq1_bank0_hi;
wire                       match0_wq2_bank0_hi;
wire                       match0_wq3_bank0_hi;
wire                       match0_wq0_bank1_lo;
wire                       match0_wq1_bank1_lo;
wire                       match0_wq2_bank1_lo;
wire                       match0_wq3_bank1_lo;
wire                       match0_wq0_bank1_hi;
wire                       match0_wq1_bank1_hi;
wire                       match0_wq2_bank1_hi;
wire                       match0_wq3_bank1_hi;
wire                       match1_wq0_bank0_lo;           
wire                       match1_wq1_bank0_lo;           
wire                       match1_wq2_bank0_lo;           
wire                       match1_wq3_bank0_lo;           
wire                       match1_wq0_bank0_hi;
wire                       match1_wq1_bank0_hi;
wire                       match1_wq2_bank0_hi;
wire                       match1_wq3_bank0_hi;
wire                       match1_wq0_bank1_lo;
wire                       match1_wq1_bank1_lo;
wire                       match1_wq2_bank1_lo;
wire                       match1_wq3_bank1_lo;
wire                       match1_wq0_bank1_hi;
wire                       match1_wq1_bank1_hi;
wire                       match1_wq2_bank1_hi;
wire                       match1_wq3_bank1_hi;
wire                       match2_wq0_bank0_lo;           
wire                       match2_wq1_bank0_lo;           
wire                       match2_wq2_bank0_lo;           
wire                       match2_wq3_bank0_lo;           
wire                       match2_wq0_bank0_hi;
wire                       match2_wq1_bank0_hi;
wire                       match2_wq2_bank0_hi;
wire                       match2_wq3_bank0_hi;
wire                       match2_wq0_bank1_lo;
wire                       match2_wq1_bank1_lo;
wire                       match2_wq2_bank1_lo;
wire                       match2_wq3_bank1_lo;
wire                       match2_wq0_bank1_hi;
wire                       match2_wq1_bank1_hi;
wire                       match2_wq2_bank1_hi;
wire                       match2_wq3_bank1_hi;
wire                       match3_wq0_bank0_lo;           
wire                       match3_wq1_bank0_lo;           
wire                       match3_wq2_bank0_lo;           
wire                       match3_wq3_bank0_lo;           
wire                       match3_wq0_bank0_hi;
wire                       match3_wq1_bank0_hi;
wire                       match3_wq2_bank0_hi;
wire                       match3_wq3_bank0_hi;
wire                       match3_wq0_bank1_lo;
wire                       match3_wq1_bank1_lo;
wire                       match3_wq2_bank1_lo;
wire                       match3_wq3_bank1_lo;
wire                       match3_wq0_bank1_hi;
wire                       match3_wq1_bank1_hi;
wire                       match3_wq2_bank1_hi;
wire                       match3_wq3_bank1_hi;

reg                        match_wq0_bank0_lo;
reg                        match_wq0_bank0_hi;
reg                        match_wq0_bank1_lo;
reg                        match_wq0_bank1_hi;
reg                        match_wq1_bank0_lo;
reg                        match_wq1_bank0_hi;
reg                        match_wq1_bank1_lo;
reg                        match_wq1_bank1_hi;
reg                        match_wq2_bank0_lo;
reg                        match_wq2_bank0_hi;
reg                        match_wq2_bank1_lo;
reg                        match_wq2_bank1_hi;
reg                        match_wq3_bank0_lo;
reg                        match_wq3_bank0_hi;
reg                        match_wq3_bank1_lo;
reg                        match_wq3_bank1_hi;

wire                       match0_dc40_bank0_lo;
wire                       match0_dc41_bank0_lo;
wire                       match1_dc40_bank0_lo;
wire                       match1_dc41_bank0_lo;
wire                       match0_dc40_bank0_hi;
wire                       match0_dc41_bank0_hi;
wire                       match1_dc40_bank0_hi;
wire                       match1_dc41_bank0_hi;
wire                       match0_dc40_bank1_lo;
wire                       match0_dc41_bank1_lo;

wire                       match1_dc40_bank1_hi;
wire                       match1_dc41_bank1_hi;

wire [7:0]                 dc30_mask_bank0;
wire [7:0]                 dc31_mask_bank0;
wire [7:0]                 dc30_mask_bank1;
wire [7:0]                 dc31_mask_bank1;

wire [7:0]                 dc40_mask_bank0;
wire [7:0]                 dc40_mask_bank1;
wire [7:0]                 dc41_mask_bank0;
wire [7:0]                 dc41_mask_bank1;
wire [7:0]                 wq0_aln_mask_bank0;
wire [7:0]                 wq0_aln_mask_bank1;

wire [`npuarc_DMP_DATA_RANGE]      wq0_wr_data0;
wire [1:0]                  wq0_grad_prel;
wire [7:0]                 wq1_aln_mask_bank0;
wire [7:0]                 wq1_aln_mask_bank1;

wire [`npuarc_DMP_DATA_RANGE]      wq1_wr_data0;
wire [1:0]                  wq1_grad_prel;
wire [7:0]                 wq2_aln_mask_bank0;
wire [7:0]                 wq2_aln_mask_bank1;

wire [`npuarc_DMP_DATA_RANGE]      wq2_wr_data0;
wire [1:0]                  wq2_grad_prel;
wire [7:0]                 wq3_aln_mask_bank0;
wire [7:0]                 wq3_aln_mask_bank1;

wire [`npuarc_DMP_DATA_RANGE]      wq3_wr_data0;
wire [1:0]                  wq3_grad_prel;

wire [`npuarc_DOUBLE_RANGE]       dc40_aln_data_bank0;
wire [`npuarc_DOUBLE_RANGE]       dc41_aln_data_bank0;
wire [`npuarc_DOUBLE_RANGE]       dc40_aln_data_bank1;
wire [`npuarc_DOUBLE_RANGE]       dc41_aln_data_bank1;
wire [`npuarc_DOUBLE_RANGE]       wq0_aln_data_bank0;
wire [`npuarc_DOUBLE_RANGE]       wq0_aln_data_bank1;
wire [`npuarc_DOUBLE_RANGE]       wq1_aln_data_bank0;
wire [`npuarc_DOUBLE_RANGE]       wq1_aln_data_bank1;
wire [`npuarc_DOUBLE_RANGE]       wq2_aln_data_bank0;
wire [`npuarc_DOUBLE_RANGE]       wq2_aln_data_bank1;
wire [`npuarc_DOUBLE_RANGE]       wq3_aln_data_bank0;
wire [`npuarc_DOUBLE_RANGE]       wq3_aln_data_bank1;

// leda NTL_CON12A on
// leda NTL_CON13A on

wire                       replay0_bank0_lo;    
wire                       replay1_bank0_lo;    
wire                       replay0_bank0_hi;   
wire                       replay1_bank0_hi;   
wire                       replay0_bank1_lo;  
 
wire                       replay0_bank1_hi;    
   

wire                       fwd_enable0_bank0_lo;
wire                       fwd_enable1_bank0_lo;
wire                       fwd_enable0_bank0_hi;
wire                       fwd_enable1_bank0_hi;
wire                       fwd_enable0_bank1_lo;

wire                       fwd_enable0_bank1_hi;

// Write merging stuff
//

reg                        wr_merge_hot_cg0;
reg [`npuarc_DMP_FIFO_RANGE]      wr_merge_hot_r;
reg [`npuarc_DMP_FIFO_RANGE]      wr_merge_hot_nxt;

wire                       dmp_wq_mem_write0;
wire                       dmp_wq_mem_write1;
wire                       dmp_wq_non_mem;
wire                       wq_bank30_crossing;
wire [3:0]                 dmp_wq_bank_mask0;
wire                       ca_store_byte;  
wire                       ca_store_half;
wire                       ca_store_word;
wire                       ca_store_double;

reg [3:0]                  addr0_inc;
reg [3:0]                  addr1_inc;

reg                        mem_merge;
reg                        mem_non_merge;
reg                        merge_broken;

reg                        wq_merge_start;
reg [`npuarc_WQ_PTR_RANGE]        wq_merge_start_ptr;
reg                        wq_merge_inc;
reg                        wq_merge_done;

reg                        wq_merge_state_r;
reg                        wq_merge_state_nxt;
wire                       wq_merge_state_next;

reg                        wq_merge_counter_cg0;
reg [7:0]                  wq_merge_counter_r;
reg [7:0]                  wq_merge_counter_nxt;
reg                        wq_merge_counter_expired_r;
reg                        wq_merge_counter_expired_nxt;

reg                        wq_merge_addr_cg0;
reg  [`npuarc_PADDR_RANGE]        wq_merge_addr_r;
reg  [`npuarc_PADDR_RANGE]        wq_merge_addr_nxt;

reg [`npuarc_DOUBLE_RANGE]        wq_merge_data;
reg [3:0]                  wq_merge_mask;
reg [2:0]                  wq_merge_size;
reg [2:0]                  wq_merging_size;
reg                        wq_merge_ovf;

reg                        wq_write_one; 
reg                        wq_write_two;

reg [`npuarc_WQ_PTR_RANGE]        wq_one_wrentry0; 

reg [`npuarc_WQ_PTR_RANGE]        wq_two_wrentry0; 
reg [`npuarc_WQ_PTR_RANGE]        wq_two_wrentry1; 

reg                        dc3_ca_raw_hazard;

reg                        wq_fwd_replay_prel;
reg                        wq_full_fwd;
reg                        dc4_grad_store_match;
reg [1:0]                  ca_grad_data_src_prel;


//////////////////////////////////////////////////////////////////////////////
//
// Consolidating writes into the WQ FIFO
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_write_PROC
  wq_write_one = (  (dmp_wq_write0 & (~wq_merge_write))
                  | dmp_wq_write1)
                 & ca_pass;                 
  wq_write_two =  (dmp_wq_write0 & dmp_wq_write1)
                 & (~wq_merge_write) 
                 & ca_pass;
end


//////////////////////////////////////////////////////////////////////////////
//
// Find one empty
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_one_wrentry_PROC
  casez (wq_valid_r)
  4'b???0: wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] = 2'd0;
  4'b??01: wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] = 2'd1;
  4'b?011: wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] = 2'd2;
  default: wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] = 2'd3;
  endcase
end

//////////////////////////////////////////////////////////////////////////////
//
// Find two empty
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_two_wrentry_PROC
  casez (wq_valid_r)
  4'b??00: 
  begin
    wq_two_wrentry0[`npuarc_WQ_PTR_RANGE] = 2'd0;
    wq_two_wrentry1[`npuarc_WQ_PTR_RANGE] = 2'd1;
  end  
  
  4'b?010: 
  begin
    wq_two_wrentry0[`npuarc_WQ_PTR_RANGE] = 2'd0;
    wq_two_wrentry1[`npuarc_WQ_PTR_RANGE] = 2'd2;
  end  
  
  4'b0110: 
  begin
    wq_two_wrentry0[`npuarc_WQ_PTR_RANGE] = 2'd0;
    wq_two_wrentry1[`npuarc_WQ_PTR_RANGE] = 2'd3;
  end  
  
  4'b?001: 
  begin
    wq_two_wrentry0[`npuarc_WQ_PTR_RANGE] = 2'd1;
    wq_two_wrentry1[`npuarc_WQ_PTR_RANGE] = 2'd2;
  end  
  
  4'b0101: 
  begin
    wq_two_wrentry0[`npuarc_WQ_PTR_RANGE] = 2'd1;
    wq_two_wrentry1[`npuarc_WQ_PTR_RANGE] = 2'd3;
  end  
  
  default: 
  begin
    wq_two_wrentry0[`npuarc_WQ_PTR_RANGE] = 2'd2;
    wq_two_wrentry1[`npuarc_WQ_PTR_RANGE] = 2'd3;
  end    
  endcase
end

reg [`npuarc_WQ_PTR_RANGE]    wq_wrentry0;
reg [`npuarc_WQ_PTR_RANGE]    wq_wrentry1;
//////////////////////////////////////////////////////////////////////////////
//
// Select entries to write
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_wrentry_PROC
  wq_wrentry0   = wq_one_wrentry0;
  wq_wrentry1   = wq_one_wrentry0;
  
  if (dmp_wq_write0 & dmp_wq_write1)
  begin
    wq_wrentry0 = wq_two_wrentry0;
    wq_wrentry1 = wq_two_wrentry1;
  end
end

//////////////////////////////////////////////////////////////////////////////
// Handy vectors
//
////////////////////////////////////////////////////////////////////////////// 

reg [`npuarc_DMP_FIFO_RANGE] wq_dep_r;
reg [`npuarc_DMP_FIFO_RANGE] wq_grad_r;
reg [`npuarc_DMP_DATA_RANGE] wq_data_r[`npuarc_DMP_FIFO_RANGE];

always @*
begin : wq_dep_handy_PROC
  // This is the row of the dependency matrix
  //
  wq_dep_r[0]  = | (wq0_dep_r & wq_valid_r);
  wq_grad_r[0] =   (|wq0_grad_r) & wq_valid_r[0];
  wq_data_r[0] =   wq0_data_r;
  wq_dep_r[1]  = | (wq1_dep_r & wq_valid_r);
  wq_grad_r[1] =   (|wq1_grad_r) & wq_valid_r[1];
  wq_data_r[1] =   wq1_data_r;
  wq_dep_r[2]  = | (wq2_dep_r & wq_valid_r);
  wq_grad_r[2] =   (|wq2_grad_r) & wq_valid_r[2];
  wq_data_r[2] =   wq2_data_r;
  wq_dep_r[3]  = | (wq3_dep_r & wq_valid_r);
  wq_grad_r[3] =   (|wq3_grad_r) & wq_valid_r[3];
  wq_data_r[3] =   wq3_data_r;
end

reg [`npuarc_DMP_FIFO_RANGE] wq_lq_dep_r;
always @*
begin : wq_lq_dep_handy_PROC
  // This is the row of the dependency matric
  //
  wq_lq_dep_r[0] = | wq0_lq_dep_r;
  wq_lq_dep_r[1] = | wq1_lq_dep_r;
  wq_lq_dep_r[2] = | wq2_lq_dep_r;
  wq_lq_dep_r[3] = | wq3_lq_dep_r;
end

//////////////////////////////////////////////////////////////////////////////
// Select entry to be processed (external)
//
////////////////////////////////////////////////////////////////////////////// 

reg                        wq_ext_rdentry_valid;
reg                        wq_ext_dealloc_set;
reg                        wq_ext_dealloc_pend_r;
reg [`npuarc_WQ_PTR_RANGE]        wq_ext_dealloc_entry_r;
reg [`npuarc_WQ_PTR_RANGE]        wq_ext_dealloc_entry_nxt;


always @*
begin : wq_ext_rdentry_PROC
  integer i;
  reg     f;
  
  // Default values
  //
  wq_ext_dealloc_set             = 1'b0;
  wq_ext_dealloc_entry_nxt       = wq_ext_dealloc_entry_r; 
  wq_ext_rdentry_valid           = wq_ext_dealloc_pend_r;
  wq_ext_rdentry0[`npuarc_WQ_PTR_RANGE] = wq_ext_dealloc_entry_r;
  
  
  f = 1'b0;
  for (i = 0; i < `npuarc_DMP_FIFO_DEPTH; i = i+1)
  begin
    if (    (wq_valid_r[i]) 
        &&  (wq_external_entries[i])
        &&  (wr_merge_hot_r[i] != 1'b1)
        &&  (!wq_dep_r[i])
        &&  (!wq_grad_r[i])
        &&  (!wq_lq_dep_r[i])
        &&  (!wq_out_r[i])
        &&  (!wq_ext_dealloc_pend_r)
        &&  (!f)
        )
    begin
      wq_ext_dealloc_set                       = 1'b1;
      wq_ext_dealloc_entry_nxt[`npuarc_WQ_PTR_RANGE]  = $unsigned(i);
      wq_ext_rdentry0[`npuarc_WQ_PTR_RANGE]           = $unsigned(i);
      wq_ext_rdentry_valid                     = 1'b1;
      f                                        = 1'b1;
    end
  end 
end

//////////////////////////////////////////////////////////////////////////////
// Select entry to be processed (internal)
//
////////////////////////////////////////////////////////////////////////////// 

reg                        wq_dc_rdentry_valid;
reg [`npuarc_WQ_PTR_RANGE]        wq_dc_rdentry0;
reg [`npuarc_WQ_PTR_RANGE]        wq_dc_rdentry1;
reg                        wq_dc_dealloc_set;
reg                        wq_dc_dealloc_pend_r;
reg [`npuarc_WQ_PTR_RANGE]        wq_dc_dealloc_entry_r;
reg [`npuarc_WQ_PTR_RANGE]        wq_dc_dealloc_entry_nxt;

// spyglass disable_block SelfDeterminedExpr-ML
// SMD: self determined expression
// SJ:  done on purpose
always @*
begin : wq_dc_rdentry_PROC
  integer i;
  reg     f;
  
  // Default values
  //
  wq_dc_dealloc_set             = 1'b0;
  wq_dc_dealloc_entry_nxt       = wq_dc_dealloc_entry_r; 
  wq_dc_rdentry_valid           = wq_dc_dealloc_pend_r;
  wq_dc_rdentry0[`npuarc_WQ_PTR_RANGE] = wq_dc_dealloc_entry_r;
  wq_dc_rdentry1[`npuarc_WQ_PTR_RANGE] = wq_dc_dealloc_entry_r;
  
  
  f = 1'b0;
  for (i = 0; i < `npuarc_DMP_FIFO_DEPTH; i = i+1)
  begin
    if (    (wq_valid_r[i]) 
        &&  (wq_internal_entries[i])  // consider having this coming 
                                      // from a flop (timing)
        &&  (!wq_dep_r[i])
        &&  (!wq_grad_r[i])
        &&  (!wq_dc_dealloc_pend_r)
        &&  (!f)
        )
    begin
      wq_dc_dealloc_set                       = 1'b1;
      wq_dc_dealloc_entry_nxt[`npuarc_WQ_PTR_RANGE]  = $unsigned(i);
      wq_dc_rdentry0[`npuarc_WQ_PTR_RANGE]           = $unsigned(i);
      wq_dc_rdentry1[`npuarc_WQ_PTR_RANGE]           = $unsigned(i+1);
      wq_dc_rdentry_valid                     = 1'b1;
      f                                       = 1'b1;
    end
  end 
end
// spyglass enable_block SelfDeterminedExpr-ML


//////////////////////////////////////////////////////////////////////////////
// Processing entries
//
////////////////////////////////////////////////////////////////////////////// 
reg                       wq_dc_processed;

always @*
begin : wq_read_PROC
  // Read-entry targeting wither external mem, per or iccm
  //
  wq_mem_per_iccm_read = 1'b0
                         | wq_mem_read
                         ;         

  wq_dc_processed      = 1'b0
                       | wq_dc_read
                       | wq_dccm_read_one
                       | wq_dccm_read_two
                       ;

end

reg [`npuarc_WQ_PTR_RANGE]  wq_dc_entry0_id;
reg [`npuarc_WQ_PTR_RANGE]  wq_dc_entry1_id;
//////////////////////////////////////////////////////////////////////////////
// Retiring entries
//
////////////////////////////////////////////////////////////////////////////// 
always @*
begin : wq_retire_PROC
  wq_mem_retire    = (wq_mem_wr_done | wq_mem_wr_excl_done | wq_mem_err_wr); 

  // Retirement of any entry
  //
  wq_retire       =  1'b0
                  | wq_mem_retire 
                  | wq_dc_read
                  | wq_dccm_read_one
                ;
                  

  // The retirement of dcache/dccm entries happen at the same time the entries
  // have been processed, i.e.: acknowledge by the target
  //
  wq_dc_retire_one =  1'b0
                    | wq_dc_read
                    | wq_dccm_read_one
                    ;
  wq_dc_retire_two = 1'b0
                    | wq_dccm_read_two
                    ;    
  
  wq_dc_entry0_id  = wq_dc_rdentry0;
  wq_dc_entry1_id  = wq_dc_rdentry1;
end


//////////////////////////////////////////////////////////////////////////////
// FIFO structure to keep track of write responses: one FIFO per external 
// target
//
////////////////////////////////////////////////////////////////////////////// 

npuarc_alb_dmp_simple_fifo 
  #(
    .DEPTH  (`npuarc_DMP_FIFO_DEPTH),  
    .DEPL2  (`npuarc_WQ_PTR_DEPTH),  
    .D_W    (`npuarc_WQ_PTR_DEPTH)  
   ) 
   u_alb_dmp_wq_bfifo_0 (
  .clk       (clk            ),                
  .rst_a     (rst_a          ),              
  
  .push      (wq_mem_read    ),               
  .data_in   (wq_ext_rdentry0),            
  .pop       (wq_mem_retire  ),                
  
  .head      (wq_mem_entry_id)               
);





reg [`npuarc_PADDR_RANGE] wq_mem_addr;  
reg                wq_mem_user_mode;
reg                wq_mem_debug;

//////////////////////////////////////////////////////////////////////////////
// Top memory address 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_mem_addr_err_PROC
  case (wq_mem_entry_id)
  2'd0:   
  begin
    wq_mem_addr      = wq0_addr_r;
    wq_mem_user_mode = wq0_user_mode_r;
    wq_mem_debug     = wq0_debug_r;
    wq_mem_scond     =    wq_valid_r[0]
                       &  wq0_scond_r
                       & (wq0_target_r == `npuarc_DMP_TARGET_MEM);
  end  
  2'd1:   
  begin
    wq_mem_addr      = wq1_addr_r;
    wq_mem_user_mode = wq1_user_mode_r;
    wq_mem_debug     = wq1_debug_r;
    wq_mem_scond     =    wq_valid_r[1]
                       &  wq1_scond_r
                       & (wq1_target_r == `npuarc_DMP_TARGET_MEM);
  end  
  2'd2:   
  begin
    wq_mem_addr      = wq2_addr_r;
    wq_mem_user_mode = wq2_user_mode_r;
    wq_mem_debug     = wq2_debug_r;
    wq_mem_scond     =    wq_valid_r[2]
                       &  wq2_scond_r
                       & (wq2_target_r == `npuarc_DMP_TARGET_MEM);
  end  
  default: 
  begin
    wq_mem_addr      = wq3_addr_r;
    wq_mem_user_mode = wq3_user_mode_r;
    wq_mem_debug     = wq3_debug_r;
    wq_mem_scond     =    wq_valid_r[3]
                       &  wq3_scond_r
                       & (wq3_target_r == `npuarc_DMP_TARGET_MEM);
  end    
  endcase
end







//////////////////////////////////////////////////////////////////////////////
// Instantiate block that processes bus errors
//
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_dmp_wq_err u_alb_dmp_wq_err_0 (
  .clk                      (clk                  ),        
  .rst_a                    (rst_a                ),      

  .wq_mem_err_wr            (wq_mem_err_wr        ),
  .wq_mem_addr              (wq_mem_addr          ),  
  .wq_mem_user_mode         (wq_mem_user_mode     ),
  .wq_mem_debug             (wq_mem_debug         ),





  .wq_err_r                 (wq_err_r             ),
  .wq_err_user_mode_r       (wq_err_user_mode_r   ),
  .wq_err_addr_r            (wq_err_addr_r        ),
  .wq_err_ack               (wq_err_ack           )
);


//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic defining write mux control
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wr_ptr_PROC
  // Selection of the write entries
  //
  wr0_0 =       dmp_wq_write0 
              & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd0) 
              & (~wq_merge_write);
  
  wr0_1 =  (     dmp_wq_write1 
               & (~dmp_wq_write0)
               & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd0))
          | (    dmp_wq_write0 
               & dmp_wq_write1  
               & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd0) 
               & wq_merge_write)
         | (    dmp_wq_write0 
              & dmp_wq_write1  
              & (wq_two_wrentry1[`npuarc_WQ_PTR_RANGE] == 2'd0)
              & (~wq_merge_write))
          ;
  
  wr0_merge  =   wq_merge_write 
               & wr_merge_hot_r[0]
               ;
  
  // 
  //
  wr1_0 =       dmp_wq_write0 
              & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd1) 
              & (~wq_merge_write);
  
  wr1_1 =  (     dmp_wq_write1 
               & (~dmp_wq_write0)
               & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd1))
          | (    dmp_wq_write0 
               & dmp_wq_write1  
               & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd1) 
               & wq_merge_write)
         | (    dmp_wq_write0 
              & dmp_wq_write1  
              & (wq_two_wrentry1[`npuarc_WQ_PTR_RANGE] == 2'd1)
              & (~wq_merge_write))
          ;
  
  wr1_merge  =   wq_merge_write 
               & wr_merge_hot_r[1]
               ;
  
  // 
  //
  wr2_0 =       dmp_wq_write0 
              & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd2) 
              & (~wq_merge_write);
  
  wr2_1 =  (     dmp_wq_write1 
               & (~dmp_wq_write0)
               & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd2))
          | (    dmp_wq_write0 
               & dmp_wq_write1  
               & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd2) 
               & wq_merge_write)
         | (    dmp_wq_write0 
              & dmp_wq_write1  
              & (wq_two_wrentry1[`npuarc_WQ_PTR_RANGE] == 2'd2)
              & (~wq_merge_write))
          ;
  
  wr2_merge  =   wq_merge_write 
               & wr_merge_hot_r[2]
               ;
  
  // 
  //
  wr3_0 =       dmp_wq_write0 
              & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd3) 
              & (~wq_merge_write);
  
  wr3_1 =  (     dmp_wq_write1 
               & (~dmp_wq_write0)
               & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd3))
          | (    dmp_wq_write0 
               & dmp_wq_write1  
               & (wq_one_wrentry0[`npuarc_WQ_PTR_RANGE] == 2'd3) 
               & wq_merge_write)
         | (    dmp_wq_write0 
              & dmp_wq_write1  
              & (wq_two_wrentry1[`npuarc_WQ_PTR_RANGE] == 2'd3)
              & (~wq_merge_write))
          ;
  
  wr3_merge  =   wq_merge_write 
               & wr_merge_hot_r[3]
               ;
  
  // 
  //

end

//////////////////////////////////////////////////////////////////////////////
// Stores targeting an external memory region
//
////////////////////////////////////////////////////////////////////////////
wire                   dc4_target_external0;
wire                   dc4_target_external1;

// Stores targeting an external memory region
//
assign dc4_target_external0 = 1'b1
                             & (wq_target0 != `npuarc_DMP_TARGET_DCCM)
                             & (wq_target0 != `npuarc_DMP_TARGET_DC)
                             ;
// Stores targeting an external memory region
//
assign dc4_target_external1 = 1'b1
                             & (wq_target1 != `npuarc_DMP_TARGET_DCCM)
                             & (wq_target1 != `npuarc_DMP_TARGET_DC)
                             ;

 
//////////////////////////////////////////////////////////////////////////////
// Stores targeting an internal memory region
//
////////////////////////////////////////////////////////////////////////////
wire                   dc4_target_internal0;
wire                   dc4_target_internal1;

// Stores targeting an internal memory region
//
assign dc4_target_internal0 = 1'b0
                            | (wq_target0 == `npuarc_DMP_TARGET_DCCM)
                            | (wq_target0 == `npuarc_DMP_TARGET_DC)
                            ;
// Stores targeting an internal memory region
//
assign dc4_target_internal1 = 1'b0
                            | (wq_target1 == `npuarc_DMP_TARGET_DCCM)
                            | (wq_target1 == `npuarc_DMP_TARGET_DC)
                            ;

  
//////////////////////////////////////////////////////////////////////////////
// Asynchronous process to build up a dependency matrix for ordering
// dependent writes. Writes to external targets are ordered: they are sent out 
// on the IBP bus in the same order they have committed. Writes to internal 
// memories (d-cache, ccms) can be re-ordered by the WQ.
//
//////////////////////////////////////////////////////////////////////////////

reg [`npuarc_DMP_FIFO_RANGE] dc4_dc_dep0;
reg [`npuarc_DMP_FIFO_RANGE] dc4_dc_dep1;
reg [`npuarc_DMP_FIFO_RANGE] dc4_ext_dep0;
reg [`npuarc_DMP_FIFO_RANGE] dc4_ext_dep1;
//reg [`DMP_FIFO_RANGE] dc4_addr_match0;
//reg [`DMP_FIFO_RANGE] dc4_addr_match1;

reg [`npuarc_DMP_FIFO_RANGE] dc4_dep0;
reg [`npuarc_DMP_FIFO_RANGE] dc4_dep1;


always @*
begin : wq_dep_PROC
  // Addr match
  //
  //dc4_addr_match0[0] = (dmp_wq_addr0[`PADDR_MSB:4] == wq0_addr_r[`PADDR_MSB:4]);
  
  // Create a dependency link between this internal write to all internal 
  // writes already in the WQ, i.e.: internal writes happens in order
  //
  dc4_dc_dep0[0]     =  dc4_target_internal0           // dc4 targets DC or DCCM
                       & wq_internal_entries[0];     
                                                      
  
  // Create a dependency link between this external write to all writes that 
  // are in the WQ
  //
  dc4_ext_dep0[0]    =   dc4_target_external0
                       & (  wq_recent_external_wr_r[0]
                          | wq_internal_entries[0]);                       
  
  
  //dc4_dep0[0]       =   ca_store_r
  //                     & wq_valid_r[0]
  //                     & (~wq_out_r[0])
  //                     & (  dc4_addr_match0[0]
  //                        | dc4_ext_dep0[0]);
  
  // Internal and external dependencies
  //
  dc4_dep0[0]        =   ca_store_r
                        & (wq_valid_r[0])
                        & (   (dc4_ext_dep0[0] & (~wq_out_r[0]))
                           |  dc4_dc_dep0[0]);
  
  
  //  Addr match
  //
  //dc4_addr_match1[0] = (dmp_wq_addr1[`PADDR_MSB:4] == wq0_addr_r[`PADDR_MSB:4]);
  
  
  // Create a dependency link between this internal write to all internal 
  // writes already in the WQ, i.e.: internal writes happens in order
  //
  dc4_dc_dep1[0]  =  dc4_target_internal1
                    & wq_internal_entries[0];
  
  // When writing two external entries create a link between 1 and 0,
  // i.e.: "1" can only go out after "0"
  //
  dc4_ext_dep1[0]  =  dmp_wq_write1
                     & dc4_target_external1
                     & (wq_wrentry0 == 2'd0);                  
            
  //dc4_dep1[0]        =    ca_store_r
  //                       & wq_valid_r[0]
  //                       & (~wq_out_r[0])
  //                       & (  dc4_addr_match1[0]
  //                          | dc4_ext_dep0[0]
  //                          | dc4_ext_dep1[0]);
  
  dc4_dep1[0]        =    ca_store_r
                         & wq_valid_r[0]
                         & (  (dc4_ext_dep0[0] & (~wq_out_r[0]))
                            | (dc4_ext_dep1[0] & (~wq_out_r[0]))
                            | dc4_dc_dep1[0]);
  
  
  // Addr match
  //
  //dc4_addr_match0[1] = (dmp_wq_addr0[`PADDR_MSB:4] == wq1_addr_r[`PADDR_MSB:4]);
  
  // Create a dependency link between this internal write to all internal 
  // writes already in the WQ, i.e.: internal writes happens in order
  //
  dc4_dc_dep0[1]     =  dc4_target_internal0           // dc4 targets DC or DCCM
                       & wq_internal_entries[1];     
                                                      
  
  // Create a dependency link between this external write to all writes that 
  // are in the WQ
  //
  dc4_ext_dep0[1]    =   dc4_target_external0
                       & (  wq_recent_external_wr_r[1]
                          | wq_internal_entries[1]);                       
  
  
  //dc4_dep0[1]       =   ca_store_r
  //                     & wq_valid_r[1]
  //                     & (~wq_out_r[1])
  //                     & (  dc4_addr_match0[1]
  //                        | dc4_ext_dep0[1]);
  
  // Internal and external dependencies
  //
  dc4_dep0[1]        =   ca_store_r
                        & (wq_valid_r[1])
                        & (   (dc4_ext_dep0[1] & (~wq_out_r[1]))
                           |  dc4_dc_dep0[1]);
  
  
  //  Addr match
  //
  //dc4_addr_match1[1] = (dmp_wq_addr1[`PADDR_MSB:4] == wq1_addr_r[`PADDR_MSB:4]);
  
  
  // Create a dependency link between this internal write to all internal 
  // writes already in the WQ, i.e.: internal writes happens in order
  //
  dc4_dc_dep1[1]  =  dc4_target_internal1
                    & wq_internal_entries[1];
  
  // When writing two external entries create a link between 1 and 0,
  // i.e.: "1" can only go out after "0"
  //
  dc4_ext_dep1[1]  =  dmp_wq_write1
                     & dc4_target_external1
                     & (wq_wrentry0 == 2'd1);                  
            
  //dc4_dep1[1]        =    ca_store_r
  //                       & wq_valid_r[1]
  //                       & (~wq_out_r[1])
  //                       & (  dc4_addr_match1[1]
  //                          | dc4_ext_dep0[1]
  //                          | dc4_ext_dep1[1]);
  
  dc4_dep1[1]        =    ca_store_r
                         & wq_valid_r[1]
                         & (  (dc4_ext_dep0[1] & (~wq_out_r[1]))
                            | (dc4_ext_dep1[1] & (~wq_out_r[1]))
                            | dc4_dc_dep1[1]);
  
  
  // Addr match
  //
  //dc4_addr_match0[2] = (dmp_wq_addr0[`PADDR_MSB:4] == wq2_addr_r[`PADDR_MSB:4]);
  
  // Create a dependency link between this internal write to all internal 
  // writes already in the WQ, i.e.: internal writes happens in order
  //
  dc4_dc_dep0[2]     =  dc4_target_internal0           // dc4 targets DC or DCCM
                       & wq_internal_entries[2];     
                                                      
  
  // Create a dependency link between this external write to all writes that 
  // are in the WQ
  //
  dc4_ext_dep0[2]    =   dc4_target_external0
                       & (  wq_recent_external_wr_r[2]
                          | wq_internal_entries[2]);                       
  
  
  //dc4_dep0[2]       =   ca_store_r
  //                     & wq_valid_r[2]
  //                     & (~wq_out_r[2])
  //                     & (  dc4_addr_match0[2]
  //                        | dc4_ext_dep0[2]);
  
  // Internal and external dependencies
  //
  dc4_dep0[2]        =   ca_store_r
                        & (wq_valid_r[2])
                        & (   (dc4_ext_dep0[2] & (~wq_out_r[2]))
                           |  dc4_dc_dep0[2]);
  
  
  //  Addr match
  //
  //dc4_addr_match1[2] = (dmp_wq_addr1[`PADDR_MSB:4] == wq2_addr_r[`PADDR_MSB:4]);
  
  
  // Create a dependency link between this internal write to all internal 
  // writes already in the WQ, i.e.: internal writes happens in order
  //
  dc4_dc_dep1[2]  =  dc4_target_internal1
                    & wq_internal_entries[2];
  
  // When writing two external entries create a link between 1 and 0,
  // i.e.: "1" can only go out after "0"
  //
  dc4_ext_dep1[2]  =  dmp_wq_write1
                     & dc4_target_external1
                     & (wq_wrentry0 == 2'd2);                  
            
  //dc4_dep1[2]        =    ca_store_r
  //                       & wq_valid_r[2]
  //                       & (~wq_out_r[2])
  //                       & (  dc4_addr_match1[2]
  //                          | dc4_ext_dep0[2]
  //                          | dc4_ext_dep1[2]);
  
  dc4_dep1[2]        =    ca_store_r
                         & wq_valid_r[2]
                         & (  (dc4_ext_dep0[2] & (~wq_out_r[2]))
                            | (dc4_ext_dep1[2] & (~wq_out_r[2]))
                            | dc4_dc_dep1[2]);
  
  
  // Addr match
  //
  //dc4_addr_match0[3] = (dmp_wq_addr0[`PADDR_MSB:4] == wq3_addr_r[`PADDR_MSB:4]);
  
  // Create a dependency link between this internal write to all internal 
  // writes already in the WQ, i.e.: internal writes happens in order
  //
  dc4_dc_dep0[3]     =  dc4_target_internal0           // dc4 targets DC or DCCM
                       & wq_internal_entries[3];     
                                                      
  
  // Create a dependency link between this external write to all writes that 
  // are in the WQ
  //
  dc4_ext_dep0[3]    =   dc4_target_external0
                       & (  wq_recent_external_wr_r[3]
                          | wq_internal_entries[3]);                       
  
  
  //dc4_dep0[3]       =   ca_store_r
  //                     & wq_valid_r[3]
  //                     & (~wq_out_r[3])
  //                     & (  dc4_addr_match0[3]
  //                        | dc4_ext_dep0[3]);
  
  // Internal and external dependencies
  //
  dc4_dep0[3]        =   ca_store_r
                        & (wq_valid_r[3])
                        & (   (dc4_ext_dep0[3] & (~wq_out_r[3]))
                           |  dc4_dc_dep0[3]);
  
  
  //  Addr match
  //
  //dc4_addr_match1[3] = (dmp_wq_addr1[`PADDR_MSB:4] == wq3_addr_r[`PADDR_MSB:4]);
  
  
  // Create a dependency link between this internal write to all internal 
  // writes already in the WQ, i.e.: internal writes happens in order
  //
  dc4_dc_dep1[3]  =  dc4_target_internal1
                    & wq_internal_entries[3];
  
  // When writing two external entries create a link between 1 and 0,
  // i.e.: "1" can only go out after "0"
  //
  dc4_ext_dep1[3]  =  dmp_wq_write1
                     & dc4_target_external1
                     & (wq_wrentry0 == 2'd3);                  
            
  //dc4_dep1[3]        =    ca_store_r
  //                       & wq_valid_r[3]
  //                       & (~wq_out_r[3])
  //                       & (  dc4_addr_match1[3]
  //                          | dc4_ext_dep0[3]
  //                          | dc4_ext_dep1[3]);
  
  dc4_dep1[3]        =    ca_store_r
                         & wq_valid_r[3]
                         & (  (dc4_ext_dep0[3] & (~wq_out_r[3]))
                            | (dc4_ext_dep1[3] & (~wq_out_r[3]))
                            | dc4_dc_dep1[3]);
  
  
end

//////////////////////////////////////////////////////////////////////////////
//
// DATA mask alignment
//
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DMP_BE_RANGE] dmp_wq_data_mask1;
always @*
begin : dmp_wq_data_mask1_PROC
  //
  // This is helpful in case of aligning the data during store graduation. In case 
  // the data needs to be used by two entries
  case (ca_mem_addr0_r[2:0])
  3'b000:
  begin
    dmp_wq_data_mask1 = {8{1'b0}};
  end
  3'b001:
  begin
    dmp_wq_data_mask1 = {8'h80};
  end
  3'b010:
  begin
    dmp_wq_data_mask1 = {8'hC0};
  end 
  3'b011:
  begin
    dmp_wq_data_mask1 = {8'hE0};
  end
  3'b100:
  begin
    dmp_wq_data_mask1 = {8'hF0};
  end 
  3'b101:
  begin
    dmp_wq_data_mask1 = {8'hF8};
  end
  3'b110:
  begin
    dmp_wq_data_mask1 = {8'hFC};
  end
  3'b111:
  begin
    dmp_wq_data_mask1 = {8'hFE};
  end
  default:
  begin
    dmp_wq_data_mask1 = {8{1'b0}};
  end
  endcase
end

reg [1:0]     ca_store_grad_prel0;
reg [1:0]     ca_store_grad_prel1;

reg           ca_store_grad_rtt_prel0;
reg           ca_store_grad_rtt_prel1;

always @*
begin : ca_store_grad_prel_PROC
  //
  //
  // In case of RTT provide the wr_ptr information that we are going to write
  //
  ca_store_grad_tag       = wq_wrentry0;
  ca_store_grad_rtt_prel0 = 1'b1;
  ca_store_grad_rtt_prel1 = 1'b0;

  if (&ca_size_r)
  begin
    //
    // When size is 64 bit
    if (&ca_store_grad_r)
    begin
      //
      // No adjustment required
      //
      if (dmp_wq_addr0[3:2] == 2'b11)
      begin
        //
        // it starts from bank 3
        //
        ca_store_grad_prel0 = 2'b01;  
        ca_store_grad_prel1 = ca_store_grad_r;  
        // Write_ptr 1 has all the information required by the RTT
        //
        ca_store_grad_tag       = wq_wrentry1;
        ca_store_grad_rtt_prel0 = 1'b0;
        ca_store_grad_rtt_prel1 = 1'b1;
//        ca_store_grad_prel1 = (dmp_wq_addr0[1:0] == 2'b00) ? 2'b10 : ca_store_grad_r;  
      end
      else
      begin
        //
        //
        ca_store_grad_prel0 = ca_store_grad_r;
        ca_store_grad_prel1 = (dmp_wq_addr0[3:2] == 2'b01) ? ca_store_grad_r : 2'b10; // will be useful in case of ecc
      end      
    end
    else
    begin
      //
      // Make some adjustments, in case of partial graduation
      // depending on ca_mem_addr0_r 
      //
      case (ca_store_grad_r)
      2'b01:
      begin
        //
        // In case of unaligned address that needs partial graduation
        //
        if (  (ca_mem_addr0_r[2:0] == 3'b101)
            | (ca_mem_addr0_r[2:0] == 3'b110)
            | (ca_mem_addr0_r[2:0] == 3'b111))
        begin
          //
          //
          ca_store_grad_prel0 = ca_store_grad_r;
          ca_store_grad_prel1 = ca_store_grad_r;
        end
        else
        begin
          //
          // No store graduation
          //
          ca_store_grad_prel0 = ca_store_grad_r;
          ca_store_grad_prel1 = 2'b00;
        end
      end

      2'b10:
      begin
        //
        //
        if (dmp_wq_addr0[3:2] == 2'b11)
        begin
          // bank 3 onwards
          //
          ca_store_grad_prel0 = 2'b00;
          ca_store_grad_prel1 = ca_store_grad_r;
          // Write_ptr 1 has all the information required by the RTT
          //
          ca_store_grad_tag       = wq_wrentry1;
          ca_store_grad_rtt_prel0 = 1'b0;
          ca_store_grad_rtt_prel1 = 1'b1;
        end
        else
        begin
          //
          //
          ca_store_grad_prel0 = ca_store_grad_r;
          ca_store_grad_prel1 = ca_store_grad_r;
        end
      end
      default:
      begin
        //
        //
        ca_store_grad_prel0 = 2'b00;
        ca_store_grad_prel1 = 2'b00;
      end 
      endcase

    end
  end
  else
  begin
    //
    // No adjustment required
    //
    ca_store_grad_prel0 = ca_store_grad_r;
    ca_store_grad_prel1 = ca_store_grad_r;
  end
  
end

//////////////////////////////////////////////////////////////////////////////
// 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_indata_PROC
  // Default values
  //
  wq_data0            = dmp_wq_data0;            
  wq_size0            = dmp_wq_size0;     
  wq_addr0            = dmp_wq_addr0;     
  wq_bank_mask0       = {dmp_wq_bank_hi0[1],
                         dmp_wq_bank_lo0[1],
                         dmp_wq_bank_hi0[0],
                         dmp_wq_bank_lo0[0]};
  wq_target0          = dmp_wq_target0;
  wq_way_hot0         = dmp_wq_way_hot0; 
  wq_ecc_mask0        = dmp_wq_ecc_data_mask0;
  wq_ecc_mask1        = dmp_wq_ecc_data_mask1;

  wq_data_mask0       = {8{1'b1}};
  wq_data_mask1       = dmp_wq_data_mask1;
  
  wq_data1            = dmp_wq_data1;            
  wq_size1            = dmp_wq_size1;     
  wq_addr1            = dmp_wq_addr1;     
  wq_bank_mask1       = {dmp_wq_bank_hi1[1],
                         dmp_wq_bank_lo1[1],
                         dmp_wq_bank_hi1[0],
                         dmp_wq_bank_lo1[0]};
  wq_target1          = dmp_wq_target1;
  wq_way_hot1         = dmp_wq_way_hot1; 
end  

always @*
begin : ca_grad_data_src_prel_PROC
  //
  // It indicates where the data is going to come from
  // Either upper or lower 32bit of the retirement
  // its a two bit vector (ca_grad_data_src_prel)
  // when set indicates that it gets the data from 
  // upper 32 otherwise lower 32 of the retirement
  //
  //
  ca_grad_data_src_prel[0] = ca_store_grad_swap_r[0];  
  ca_grad_data_src_prel[1] = ~ca_store_grad_swap_r[1];  
  
end


//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to determine the next values for the buffer
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_nxt_PROC
  // Default assignment
  //
  wq0_data_nxt        = wq0_data_r;   
  wq0_size_nxt        = wq0_size_r;   
  wq0_user_mode_nxt   = wq0_user_mode_r;   
  wq0_debug_nxt       = wq0_debug_r;   
  wq0_addr_nxt        = wq0_addr_r;   
  wq0_target_nxt      = wq0_target_r;
  wq0_bank_mask_nxt   = wq0_bank_mask_r;
  wq0_external_ex_nxt = wq0_external_ex_r;
  wq0_ecc_mask_nxt    = wq0_ecc_mask_r;
  wq0_ecc_addr_nxt    = wq0_ecc_addr_r;
  wq0_data_mask_nxt   = wq0_data_mask_r;
  
  wq0_grad_nxt        = wq0_grad_r;
  wq0_grad_tag_lo_nxt = wq0_grad_tag_lo_r;
  wq0_grad_tag_hi_nxt = wq0_grad_tag_hi_r;
  wq0_grad_data_src_nxt = wq0_grad_data_src_r;
  wq0_scond_nxt       = wq0_scond_r;  
  wq0_way_hot_nxt     = wq0_way_hot_r; 
  wq0_dep_nxt         = wq0_dep_r;
   
  wq1_data_nxt        = wq1_data_r;   
  wq1_size_nxt        = wq1_size_r;   
  wq1_user_mode_nxt   = wq1_user_mode_r;   
  wq1_debug_nxt       = wq1_debug_r;   
  wq1_addr_nxt        = wq1_addr_r;   
  wq1_target_nxt      = wq1_target_r;
  wq1_bank_mask_nxt   = wq1_bank_mask_r;
  wq1_external_ex_nxt = wq1_external_ex_r;
  wq1_ecc_mask_nxt    = wq1_ecc_mask_r;
  wq1_ecc_addr_nxt    = wq1_ecc_addr_r;
  wq1_data_mask_nxt   = wq1_data_mask_r;
  
  wq1_grad_nxt        = wq1_grad_r;
  wq1_grad_tag_lo_nxt = wq1_grad_tag_lo_r;
  wq1_grad_tag_hi_nxt = wq1_grad_tag_hi_r;
  wq1_grad_data_src_nxt = wq1_grad_data_src_r;
  wq1_scond_nxt       = wq1_scond_r;  
  wq1_way_hot_nxt     = wq1_way_hot_r; 
  wq1_dep_nxt         = wq1_dep_r;
   
  wq2_data_nxt        = wq2_data_r;   
  wq2_size_nxt        = wq2_size_r;   
  wq2_user_mode_nxt   = wq2_user_mode_r;   
  wq2_debug_nxt       = wq2_debug_r;   
  wq2_addr_nxt        = wq2_addr_r;   
  wq2_target_nxt      = wq2_target_r;
  wq2_bank_mask_nxt   = wq2_bank_mask_r;
  wq2_external_ex_nxt = wq2_external_ex_r;
  wq2_ecc_mask_nxt    = wq2_ecc_mask_r;
  wq2_ecc_addr_nxt    = wq2_ecc_addr_r;
  wq2_data_mask_nxt   = wq2_data_mask_r;
  
  wq2_grad_nxt        = wq2_grad_r;
  wq2_grad_tag_lo_nxt = wq2_grad_tag_lo_r;
  wq2_grad_tag_hi_nxt = wq2_grad_tag_hi_r;
  wq2_grad_data_src_nxt = wq2_grad_data_src_r;
  wq2_scond_nxt       = wq2_scond_r;  
  wq2_way_hot_nxt     = wq2_way_hot_r; 
  wq2_dep_nxt         = wq2_dep_r;
   
  wq3_data_nxt        = wq3_data_r;   
  wq3_size_nxt        = wq3_size_r;   
  wq3_user_mode_nxt   = wq3_user_mode_r;   
  wq3_debug_nxt       = wq3_debug_r;   
  wq3_addr_nxt        = wq3_addr_r;   
  wq3_target_nxt      = wq3_target_r;
  wq3_bank_mask_nxt   = wq3_bank_mask_r;
  wq3_external_ex_nxt = wq3_external_ex_r;
  wq3_ecc_mask_nxt    = wq3_ecc_mask_r;
  wq3_ecc_addr_nxt    = wq3_ecc_addr_r;
  wq3_data_mask_nxt   = wq3_data_mask_r;
  
  wq3_grad_nxt        = wq3_grad_r;
  wq3_grad_tag_lo_nxt = wq3_grad_tag_lo_r;
  wq3_grad_tag_hi_nxt = wq3_grad_tag_hi_r;
  wq3_grad_data_src_nxt = wq3_grad_data_src_r;
  wq3_scond_nxt       = wq3_scond_r;  
  wq3_way_hot_nxt     = wq3_way_hot_r; 
  wq3_dep_nxt         = wq3_dep_r;
   
  case ({wr0_0, 
         wr0_1, 
         wr0_merge
        })
  3'b100:
  begin
    // Write single entry, entry0
    //
    wq0_data_nxt        = wq_data0;    
    wq0_size_nxt        = wq_size0;   
    wq0_user_mode_nxt   = ca_user_mode_r;   
    wq0_debug_nxt       = db_active_r;   
    wq0_addr_nxt        = wq_addr0;    
    wq0_target_nxt      = wq_target0;    
    wq0_bank_mask_nxt   = wq_bank_mask0;
    wq0_ecc_mask_nxt    = wq_ecc_mask0;
    wq0_ecc_addr_nxt    = ca_mem_addr0_r[2:0];  
    wq0_data_mask_nxt   = wq_data_mask0;

    wq0_grad_nxt        = ca_store_grad_prel0;
    wq0_grad_tag_lo_nxt = ca_store_grad_tag_lo_r;
    wq0_grad_tag_hi_nxt = ca_store_grad_tag_hi_r;
    wq0_grad_data_src_nxt = ca_grad_data_src_prel;
    
    wq0_way_hot_nxt     = wq_way_hot0; 
    wq0_external_ex_nxt =  ca_load_r
                            & ca_store_r
                            & (wq_target0 != `npuarc_DMP_TARGET_DC)
                            & (wq_target0 != `npuarc_DMP_TARGET_DCCM)
                            ;
    wq0_scond_nxt       =  ca_store_r 
                            & ca_locked_r
                            & (  (wq_target0 != `npuarc_DMP_TARGET_DC)
                               );
    wq0_dep_nxt         = dc4_dep0;
  end
  
  3'b010:
  begin
    // Write single entry, entry1
    //
    wq0_data_nxt        = wq_data1;             
    wq0_size_nxt        = wq_size1;             
    wq0_user_mode_nxt   = ca_user_mode_r;       
    wq0_debug_nxt       = db_active_r;          
    wq0_addr_nxt        = wq_addr1;             
    wq0_target_nxt      = wq_target1;           
    wq0_bank_mask_nxt   = wq_bank_mask1;
    wq0_ecc_mask_nxt    = wq_ecc_mask1;
    wq0_ecc_addr_nxt    = 3'b000;
    wq0_data_mask_nxt   = wq_data_mask1;
    wq0_grad_nxt        = ca_store_grad_prel1;
    wq0_grad_tag_lo_nxt = ca_store_grad_tag_lo_r;
    wq0_grad_tag_hi_nxt = ca_store_grad_tag_hi_r;
    wq0_grad_data_src_nxt = ca_grad_data_src_prel;
    
    wq0_way_hot_nxt     = wq_way_hot1;          
    wq0_external_ex_nxt =   ca_load_r 
                             & ca_store_r
                             & (wq_target1 != `npuarc_DMP_TARGET_DC)
                             & (wq_target1 != `npuarc_DMP_TARGET_DCCM)
                             ;
    wq0_scond_nxt       =   ca_store_r 
                             & ca_locked_r
                             & (  (wq_target1 != `npuarc_DMP_TARGET_DC)
                               );
    wq0_dep_nxt         = dc4_dep1;
  end

  3'b001:
  begin
    // Merge entry. Do not change the address of this entry
    //
    wq0_data_nxt      = wq_merge_data | wq0_data_r;
    wq0_size_nxt      = wq_merge_size;
    wq0_user_mode_nxt = ca_user_mode_r;   
    wq0_bank_mask_nxt = wq_merge_mask | wq0_bank_mask_r;
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default:
    ;
  endcase
// spyglass enable_block W193  
  case ({wr1_0, 
         wr1_1, 
         wr1_merge
        })
  3'b100:
  begin
    // Write single entry, entry0
    //
    wq1_data_nxt        = wq_data0;    
    wq1_size_nxt        = wq_size0;   
    wq1_user_mode_nxt   = ca_user_mode_r;   
    wq1_debug_nxt       = db_active_r;   
    wq1_addr_nxt        = wq_addr0;    
    wq1_target_nxt      = wq_target0;    
    wq1_bank_mask_nxt   = wq_bank_mask0;
    wq1_ecc_mask_nxt    = wq_ecc_mask0;
    wq1_ecc_addr_nxt    = ca_mem_addr0_r[2:0];  
    wq1_data_mask_nxt   = wq_data_mask0;

    wq1_grad_nxt        = ca_store_grad_prel0;
    wq1_grad_tag_lo_nxt = ca_store_grad_tag_lo_r;
    wq1_grad_tag_hi_nxt = ca_store_grad_tag_hi_r;
    wq1_grad_data_src_nxt = ca_grad_data_src_prel;
    
    wq1_way_hot_nxt     = wq_way_hot0; 
    wq1_external_ex_nxt =  ca_load_r
                            & ca_store_r
                            & (wq_target0 != `npuarc_DMP_TARGET_DC)
                            & (wq_target0 != `npuarc_DMP_TARGET_DCCM)
                            ;
    wq1_scond_nxt       =  ca_store_r 
                            & ca_locked_r
                            & (  (wq_target0 != `npuarc_DMP_TARGET_DC)
                               );
    wq1_dep_nxt         = dc4_dep0;
  end
  
  3'b010:
  begin
    // Write single entry, entry1
    //
    wq1_data_nxt        = wq_data1;             
    wq1_size_nxt        = wq_size1;             
    wq1_user_mode_nxt   = ca_user_mode_r;       
    wq1_debug_nxt       = db_active_r;          
    wq1_addr_nxt        = wq_addr1;             
    wq1_target_nxt      = wq_target1;           
    wq1_bank_mask_nxt   = wq_bank_mask1;
    wq1_ecc_mask_nxt    = wq_ecc_mask1;
    wq1_ecc_addr_nxt    = 3'b000;
    wq1_data_mask_nxt   = wq_data_mask1;
    wq1_grad_nxt        = ca_store_grad_prel1;
    wq1_grad_tag_lo_nxt = ca_store_grad_tag_lo_r;
    wq1_grad_tag_hi_nxt = ca_store_grad_tag_hi_r;
    wq1_grad_data_src_nxt = ca_grad_data_src_prel;
    
    wq1_way_hot_nxt     = wq_way_hot1;          
    wq1_external_ex_nxt =   ca_load_r 
                             & ca_store_r
                             & (wq_target1 != `npuarc_DMP_TARGET_DC)
                             & (wq_target1 != `npuarc_DMP_TARGET_DCCM)
                             ;
    wq1_scond_nxt       =   ca_store_r 
                             & ca_locked_r
                             & (  (wq_target1 != `npuarc_DMP_TARGET_DC)
                               );
    wq1_dep_nxt         = dc4_dep1;
  end

  3'b001:
  begin
    // Merge entry. Do not change the address of this entry
    //
    wq1_data_nxt      = wq_merge_data | wq1_data_r;
    wq1_size_nxt      = wq_merge_size;
    wq1_user_mode_nxt = ca_user_mode_r;   
    wq1_bank_mask_nxt = wq_merge_mask | wq1_bank_mask_r;
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default:
    ;
  endcase
// spyglass enable_block W193  
  case ({wr2_0, 
         wr2_1, 
         wr2_merge
        })
  3'b100:
  begin
    // Write single entry, entry0
    //
    wq2_data_nxt        = wq_data0;    
    wq2_size_nxt        = wq_size0;   
    wq2_user_mode_nxt   = ca_user_mode_r;   
    wq2_debug_nxt       = db_active_r;   
    wq2_addr_nxt        = wq_addr0;    
    wq2_target_nxt      = wq_target0;    
    wq2_bank_mask_nxt   = wq_bank_mask0;
    wq2_ecc_mask_nxt    = wq_ecc_mask0;
    wq2_ecc_addr_nxt    = ca_mem_addr0_r[2:0];  
    wq2_data_mask_nxt   = wq_data_mask0;

    wq2_grad_nxt        = ca_store_grad_prel0;
    wq2_grad_tag_lo_nxt = ca_store_grad_tag_lo_r;
    wq2_grad_tag_hi_nxt = ca_store_grad_tag_hi_r;
    wq2_grad_data_src_nxt = ca_grad_data_src_prel;
    
    wq2_way_hot_nxt     = wq_way_hot0; 
    wq2_external_ex_nxt =  ca_load_r
                            & ca_store_r
                            & (wq_target0 != `npuarc_DMP_TARGET_DC)
                            & (wq_target0 != `npuarc_DMP_TARGET_DCCM)
                            ;
    wq2_scond_nxt       =  ca_store_r 
                            & ca_locked_r
                            & (  (wq_target0 != `npuarc_DMP_TARGET_DC)
                               );
    wq2_dep_nxt         = dc4_dep0;
  end
  
  3'b010:
  begin
    // Write single entry, entry1
    //
    wq2_data_nxt        = wq_data1;             
    wq2_size_nxt        = wq_size1;             
    wq2_user_mode_nxt   = ca_user_mode_r;       
    wq2_debug_nxt       = db_active_r;          
    wq2_addr_nxt        = wq_addr1;             
    wq2_target_nxt      = wq_target1;           
    wq2_bank_mask_nxt   = wq_bank_mask1;
    wq2_ecc_mask_nxt    = wq_ecc_mask1;
    wq2_ecc_addr_nxt    = 3'b000;
    wq2_data_mask_nxt   = wq_data_mask1;
    wq2_grad_nxt        = ca_store_grad_prel1;
    wq2_grad_tag_lo_nxt = ca_store_grad_tag_lo_r;
    wq2_grad_tag_hi_nxt = ca_store_grad_tag_hi_r;
    wq2_grad_data_src_nxt = ca_grad_data_src_prel;
    
    wq2_way_hot_nxt     = wq_way_hot1;          
    wq2_external_ex_nxt =   ca_load_r 
                             & ca_store_r
                             & (wq_target1 != `npuarc_DMP_TARGET_DC)
                             & (wq_target1 != `npuarc_DMP_TARGET_DCCM)
                             ;
    wq2_scond_nxt       =   ca_store_r 
                             & ca_locked_r
                             & (  (wq_target1 != `npuarc_DMP_TARGET_DC)
                               );
    wq2_dep_nxt         = dc4_dep1;
  end

  3'b001:
  begin
    // Merge entry. Do not change the address of this entry
    //
    wq2_data_nxt      = wq_merge_data | wq2_data_r;
    wq2_size_nxt      = wq_merge_size;
    wq2_user_mode_nxt = ca_user_mode_r;   
    wq2_bank_mask_nxt = wq_merge_mask | wq2_bank_mask_r;
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default:
    ;
  endcase
// spyglass enable_block W193  
  case ({wr3_0, 
         wr3_1, 
         wr3_merge
        })
  3'b100:
  begin
    // Write single entry, entry0
    //
    wq3_data_nxt        = wq_data0;    
    wq3_size_nxt        = wq_size0;   
    wq3_user_mode_nxt   = ca_user_mode_r;   
    wq3_debug_nxt       = db_active_r;   
    wq3_addr_nxt        = wq_addr0;    
    wq3_target_nxt      = wq_target0;    
    wq3_bank_mask_nxt   = wq_bank_mask0;
    wq3_ecc_mask_nxt    = wq_ecc_mask0;
    wq3_ecc_addr_nxt    = ca_mem_addr0_r[2:0];  
    wq3_data_mask_nxt   = wq_data_mask0;

    wq3_grad_nxt        = ca_store_grad_prel0;
    wq3_grad_tag_lo_nxt = ca_store_grad_tag_lo_r;
    wq3_grad_tag_hi_nxt = ca_store_grad_tag_hi_r;
    wq3_grad_data_src_nxt = ca_grad_data_src_prel;
    
    wq3_way_hot_nxt     = wq_way_hot0; 
    wq3_external_ex_nxt =  ca_load_r
                            & ca_store_r
                            & (wq_target0 != `npuarc_DMP_TARGET_DC)
                            & (wq_target0 != `npuarc_DMP_TARGET_DCCM)
                            ;
    wq3_scond_nxt       =  ca_store_r 
                            & ca_locked_r
                            & (  (wq_target0 != `npuarc_DMP_TARGET_DC)
                               );
    wq3_dep_nxt         = dc4_dep0;
  end
  
  3'b010:
  begin
    // Write single entry, entry1
    //
    wq3_data_nxt        = wq_data1;             
    wq3_size_nxt        = wq_size1;             
    wq3_user_mode_nxt   = ca_user_mode_r;       
    wq3_debug_nxt       = db_active_r;          
    wq3_addr_nxt        = wq_addr1;             
    wq3_target_nxt      = wq_target1;           
    wq3_bank_mask_nxt   = wq_bank_mask1;
    wq3_ecc_mask_nxt    = wq_ecc_mask1;
    wq3_ecc_addr_nxt    = 3'b000;
    wq3_data_mask_nxt   = wq_data_mask1;
    wq3_grad_nxt        = ca_store_grad_prel1;
    wq3_grad_tag_lo_nxt = ca_store_grad_tag_lo_r;
    wq3_grad_tag_hi_nxt = ca_store_grad_tag_hi_r;
    wq3_grad_data_src_nxt = ca_grad_data_src_prel;
    
    wq3_way_hot_nxt     = wq_way_hot1;          
    wq3_external_ex_nxt =   ca_load_r 
                             & ca_store_r
                             & (wq_target1 != `npuarc_DMP_TARGET_DC)
                             & (wq_target1 != `npuarc_DMP_TARGET_DCCM)
                             ;
    wq3_scond_nxt       =   ca_store_r 
                             & ca_locked_r
                             & (  (wq_target1 != `npuarc_DMP_TARGET_DC)
                               );
    wq3_dep_nxt         = dc4_dep1;
  end

  3'b001:
  begin
    // Merge entry. Do not change the address of this entry
    //
    wq3_data_nxt      = wq_merge_data | wq3_data_r;
    wq3_size_nxt      = wq_merge_size;
    wq3_user_mode_nxt = ca_user_mode_r;   
    wq3_bank_mask_nxt = wq_merge_mask | wq3_bank_mask_r;
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default:
    ;
  endcase
// spyglass enable_block W193  
end
//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to determine the clock gate enables
//
//////////////////////////////////////////////////////////////////////////////

assign wq0_store_grad_match1 = 1'b0
                                | wq0_store_grad_match1_lo
                                | wq0_store_grad_match1_hi
                                ;

assign wq0_store_grad_match1_garbage = 1'b0
                                        | wq0_store_grad_match1_lo_garbage
                                        | wq0_store_grad_match1_hi_garbage
                                        ;

assign wq1_store_grad_match1 = 1'b0
                                | wq1_store_grad_match1_lo
                                | wq1_store_grad_match1_hi
                                ;

assign wq1_store_grad_match1_garbage = 1'b0
                                        | wq1_store_grad_match1_lo_garbage
                                        | wq1_store_grad_match1_hi_garbage
                                        ;

assign wq2_store_grad_match1 = 1'b0
                                | wq2_store_grad_match1_lo
                                | wq2_store_grad_match1_hi
                                ;

assign wq2_store_grad_match1_garbage = 1'b0
                                        | wq2_store_grad_match1_lo_garbage
                                        | wq2_store_grad_match1_hi_garbage
                                        ;

assign wq3_store_grad_match1 = 1'b0
                                | wq3_store_grad_match1_lo
                                | wq3_store_grad_match1_hi
                                ;

assign wq3_store_grad_match1_garbage = 1'b0
                                        | wq3_store_grad_match1_lo_garbage
                                        | wq3_store_grad_match1_hi_garbage
                                        ;
always @*
begin : wq0_clock_gate_PROC
  // Derive clock gate enable for this entry
  //
  wq0_addr_cg0 = (wr0_0 | wr0_1 | wr0_merge) & ca_pass;
  wq0_data_cg0 = (  (wr0_0 | wr0_1 | wr0_merge) & ca_pass)
                     | wq0_store_grad_match1
                     ;
  wq0_ctl_cg0  = (wr0_0 | wr0_1)                & ca_pass;
end

always @*
begin : wq1_clock_gate_PROC
  // Derive clock gate enable for this entry
  //
  wq1_addr_cg0 = (wr1_0 | wr1_1 | wr1_merge) & ca_pass;
  wq1_data_cg0 = (  (wr1_0 | wr1_1 | wr1_merge) & ca_pass)
                     | wq1_store_grad_match1
                     ;
  wq1_ctl_cg0  = (wr1_0 | wr1_1)                & ca_pass;
end

always @*
begin : wq2_clock_gate_PROC
  // Derive clock gate enable for this entry
  //
  wq2_addr_cg0 = (wr2_0 | wr2_1 | wr2_merge) & ca_pass;
  wq2_data_cg0 = (  (wr2_0 | wr2_1 | wr2_merge) & ca_pass)
                     | wq2_store_grad_match1
                     ;
  wq2_ctl_cg0  = (wr2_0 | wr2_1)                & ca_pass;
end

always @*
begin : wq3_clock_gate_PROC
  // Derive clock gate enable for this entry
  //
  wq3_addr_cg0 = (wr3_0 | wr3_1 | wr3_merge) & ca_pass;
  wq3_data_cg0 = (  (wr3_0 | wr3_1 | wr3_merge) & ca_pass)
                     | wq3_store_grad_match1
                     ;
  wq3_ctl_cg0  = (wr3_0 | wr3_1)                & ca_pass;
end

assign wq_addr_cg1 = ca_store_r;

assign wq_data_cg1 = ( ca_store_r
                    & (~ca_dmi_scrubbing_conflict)
                     )
                   | wa_retire1_valid 
                   ;

assign wq_bank30_crossing   = ca_data_bank_sel_r[3] & ca_data_bank_sel_r[0]; 

//////////////////////////////////////////////////////////////////////////////
// Write merging
//////////////////////////////////////////////////////////////////////////////
assign dmp_wq_mem_write0  =   dmp_wq_write0
                           & (~db_active_r)
                           & (~ca_load_r)
                           & (~ca_locked_r)
                           & (  (dmp_wq_target0 == `npuarc_DMP_TARGET_MEM) 
                              )
                              ;
                              
assign dmp_wq_mem_write1  =  dmp_wq_write1
                           & (~db_active_r)
                           & (~ca_load_r)
                           & (~ca_locked_r)
                           & (  (dmp_wq_target0 == `npuarc_DMP_TARGET_MEM) 
                              )
                              ;
assign dmp_wq_non_mem  =     (dmp_wq_write0  | dmp_wq_write1)
                           & (dmp_wq_target0 != `npuarc_DMP_TARGET_MEM) 
                           ;

//////////////////////////////////////////////////////////////////////////////
// Write merging
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Size table
//
//////////////////////////////////////////////////////////////////////////////
//                         |
//        Size[2:0]        |           Read Value
//-------------------------|-------------------------------------------------
//          000            |             1 - Byte
//          001            |             2 - Bytes (Half Word)
//          010            |             4 - Bytes (Word)
//          011            |             8 - Bytes (Double Word)
//          100            |             3 - Bytes
//          101            |             5 - Bytes
//          110            |             6 - Bytes      
//          111            |             7 - Bytes
//////////////////////////////////////////////////////////////////////////////
always @*
begin : addr_inc_PROC
  case (dmp_wq_size0)
  3'b000: addr0_inc = 4'b0001;
  3'b001: addr0_inc = 4'b0010;
  3'b010: addr0_inc = 4'b0100;
  3'b011: addr0_inc = 4'b1000;
  3'b100: addr0_inc = 4'b0011;
  3'b101: addr0_inc = 4'b0101;
  3'b110: addr0_inc = 4'b0110;
  default:addr0_inc = 4'b0111;
  endcase
  
  case (dmp_wq_size1)
  3'b000: addr1_inc = 4'b0001;
  3'b001: addr1_inc = 4'b0010;
  3'b010: addr1_inc = 4'b0100;
  3'b011: addr1_inc = 4'b1000;
  3'b100: addr1_inc = 4'b0011;
  3'b101: addr1_inc = 4'b0101;
  3'b110: addr1_inc = 4'b0110;
  default:addr1_inc = 4'b0111;
  endcase
end

always @*
begin : mem_merge_PROC
  mem_merge     =   dmp_wq_mem_write0 
                  & (dmp_wq_addr0 == wq_merge_addr_r)
                  & (~ca_volatile_r)
                  & (~wq_merge_ovf)
                  & (~(|ca_store_grad_r))
                  & (~ca_load_r);
  
  mem_non_merge =   dmp_wq_mem_write0 
                  & (  (dmp_wq_addr0 != wq_merge_addr_r)
                     | wq_merge_ovf
                     | ca_load_r
                     |(| ca_store_grad_r)
                     | ca_locked_r
                     ); 
  
  merge_broken  =  dmp_wq_non_mem   
                 | sa_dsync_op_r  
                 | sa_dmb_op_r  
                 | sa_dmb_stall  
                 | x3_sync_op_r  
                 | x3_brk_op_r
                 | (x3_load_r & x3_store_r)
                 | dc3_ca_raw_hazard
                 | wq_merge_counter_expired_r
                 | ca_load_r
                 | (|ca_store_grad_r)
                 | dc4_war_hazard
                 | dc4_stall_r
                 | ca_locked_r
                 | wa_restart_r
                 | (~dmu_empty)
                 | dc2_dc_uop_stall
                 ; 
end

//////////////////////////////////////////////////////////////////////////////
// Write merging
//////////////////////////////////////////////////////////////////////////////
parameter WQ_NOT_MERGING = 1'b0;
parameter WQ_MERGING     = 1'b1;
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer

// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  RHS is zero extended

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow

// spyglass disable_block W398 STARC05-2.8.1.3 W484
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.

// spyglass disable_block W164a
// SMD: LHS width < RHS in assignment
// SJ:  correct width will be used

always @*
begin : wq_merge_fsm_PROC
  wq_merge_start                 = 1'b0;
  wq_merge_start_ptr             =    dmp_wq_mem_write1
                                    ? wq_wrentry1[`npuarc_WQ_PTR_RANGE]  
                                    : wq_wrentry0[`npuarc_WQ_PTR_RANGE]; 
  wq_merge_inc                   = 1'b0;
  wq_merge_done                  = 1'b0;
  wq_merge_write                 = 1'b0;

  wq_merge_counter_cg0           = 1'b0;
  wq_merge_counter_nxt           = wq_merge_counter_r;
  wq_merge_counter_expired_nxt   = wq_merge_counter_expired_r;
  
  wq_merge_addr_cg0              = 1'b0;
  wq_merge_addr_nxt              = wq_merge_addr_r;
  wq_merge_state_nxt             = wq_merge_state_r;
  
  case (wq_merge_state_r) 
  WQ_NOT_MERGING:
  begin
    wq_merge_addr_cg0  = dmp_wq_mem_write0 | dmp_wq_mem_write1;

    wq_merge_addr_nxt  =   dmp_wq_mem_write1
                         ? dmp_wq_addr1 + addr1_inc
                         : dmp_wq_addr0 + addr0_inc;

    if (  dmp_wq_mem_write0 
        & (wq_merge_addr_nxt[2:0] != 3'b000)
        & (~x3_load_r)
        & (~ca_volatile_r)
        & (~(|ca_store_grad_r))
        & ca_pass)
    begin
      wq_merge_start               = 1'b1;
      wq_merge_counter_cg0         = 1'b1;
      wq_merge_counter_nxt         = 8'd128;
      wq_merge_counter_expired_nxt = 1'b0;
      wq_merge_state_nxt           = WQ_MERGING;
    end
  end
  
  default: // WQ_MERGING:
  begin
    wq_merge_counter_cg0          = (| wq_merge_counter_r);    
    wq_merge_counter_nxt          = wq_merge_counter_r - 1'b1; 
    wq_merge_counter_expired_nxt  = (wq_merge_counter_r == 8'd1);
    
    casez ({mem_merge, mem_non_merge, merge_broken})
    3'b1?0:
    begin
      // A successfull mem merge
      //
      wq_merge_addr_cg0             = 1'b1;
      wq_merge_write                = 1'b1; 

      wq_merge_counter_cg0          = 1'b1;    
      wq_merge_counter_nxt          = 8'd128; 
      wq_merge_counter_expired_nxt  = 1'b0;
      
      if (wq_bank30_crossing)
      begin
        wq_merge_addr_nxt = dmp_wq_addr1    + addr1_inc;
        wq_merge_inc      = 1'b1;
      end
      else
      begin
        wq_merge_addr_nxt = wq_merge_addr_r + addr0_inc;
        wq_merge_inc      = 1'b0; 
      end
      
      if (wq_merge_addr_nxt[2:0] == 3'b000)
      begin
        wq_merge_done      = 1'b1;
        wq_merge_state_nxt = WQ_NOT_MERGING;
      end
    end
    
    3'b?10:
    begin
      // mem_non_merge
      //
      wq_merge_addr_cg0  = 1'b1;
      wq_merge_addr_nxt  =  dmp_wq_mem_write1
                          ? dmp_wq_addr1 + addr1_inc
                          : dmp_wq_addr0 + addr0_inc;
      
      if (  (wq_merge_addr_nxt[2:0] == 3'b000)
          | (ca_volatile_r))
      begin
        wq_merge_done      = 1'b1;
        wq_merge_state_nxt = WQ_NOT_MERGING;
      end
      else
      begin
        // Stay here and adjust the merge addr
        //
        wq_merge_counter_cg0          = 1'b1;    
        wq_merge_counter_nxt          = 8'd128; 
        wq_merge_counter_expired_nxt  = 1'b0;
      
        wq_merge_start                = 1'b1;
      end
    end
    
    3'b??1:
    begin
      //  non-mem, non-peripheral write, explict merge break
      //
      wq_merge_done      = 1'b1;
      wq_merge_state_nxt = WQ_NOT_MERGING;
    end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept     
    default:;
// spyglass enable_block W193
    endcase  
  end
  endcase
end
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on
// leda W547 on
// spyglass enable_block W164a
// spyglass enable_block W398 STARC05-2.8.1.3 W484

//////////////////////////////////////////////////////////////////////////////
// Asynchronous logic to determine next pointer values
//
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block W398 STARC05-2.8.1.3
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
always @*
begin : wr_merge_hot_nxt_PROC
  // We start merging when a store to external memory enters the wq. 
  // The merge is done when either the merge chain is broken or
  // when we filled out the entire write queue entry
  //
  wr_merge_hot_cg0 = ca_pass | wq_merge_done;
  
  casez ({wq_merge_start, wq_merge_done, wq_merge_inc})
  3'b1??: 
  begin
    // 
    //
    case (wq_merge_start_ptr)
    2'b00:   wr_merge_hot_nxt  = 4'b0001;
    2'b01:   wr_merge_hot_nxt  = 4'b0010;
    2'b10:   wr_merge_hot_nxt  = 4'b0100;
    default: wr_merge_hot_nxt  = 4'b1000;
    endcase  
    
  end   
  3'b?1?: 
  begin
    // Stop merging
    //
    wr_merge_hot_nxt  = {`npuarc_DMP_FIFO_DEPTH{1'b0}}; 
  end  
  
  3'b??1: 
  begin
    // New merge pointer
    //
    case (wq_one_wrentry0)
    2'b00:   wr_merge_hot_nxt  = 4'b0001;
    2'b01:   wr_merge_hot_nxt  = 4'b0010;
    2'b10:   wr_merge_hot_nxt  = 4'b0100;
    default: wr_merge_hot_nxt  = 4'b1000;
    endcase  
  end  
  default:
  begin
    // No changes
    //
    wr_merge_hot_nxt  = wr_merge_hot_r; 
  end  
  endcase
end

assign dmp_wq_bank_mask0 = {dmp_wq_bank_hi0[1],
                            dmp_wq_bank_lo0[1],
                            dmp_wq_bank_hi0[0],
                            dmp_wq_bank_lo0[0]};
// spyglass enable_block W398 STARC05-2.8.1.3
//////////////////////////////////////////////////////////////////////////////
// Asynchronous process to extract the merge data
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_merge_mask_PROC

  // Default values
  //
  wq_merge_mask[3:0]  = 4'd0;
     
  case (wq_merge_addr_r[2:0])
  3'b001: // 0x01 or 0x09
  begin
    // This will be written at the wr_ptr_merge_r location
    //
    wq_merge_mask[3:0]    =  wq_merge_addr_r[3] 
                           ? {dmp_wq_bank_mask0[3:2], 2'b00}
                           : dmp_wq_bank_mask0;
  end

  3'b010:  // 0x02 or 0x0A
  begin
    // This will be written at the wr_ptr_merge_r location
    //
    wq_merge_mask[3:0]    =  wq_merge_addr_r[3] 
                           ? {dmp_wq_bank_mask0[3:2], 2'b00}
                           : dmp_wq_bank_mask0;
  end

  3'b011: // 0x03 or 0x0B
  begin
    // This will be written at the wr_ptr_merge_r location
    //
    wq_merge_mask[3:0]    =  wq_merge_addr_r[3] 
                           ? {dmp_wq_bank_mask0[3:2], 2'b00}
                           : dmp_wq_bank_mask0;
  end

  3'b100: // 0x04 or 0x0C
  begin
    // This will be written at the wr_ptr_merge_r location
    //
    wq_merge_mask[3:0]    =  wq_merge_addr_r[3] 
                           ? {dmp_wq_bank_mask0[3], 3'b000}
                           : {dmp_wq_bank_mask0[3:1],1'b0};
  end

  3'b101: // 0x05 or 0x0D
  begin
    // This will be written at the wr_ptr_merge_r location
    //
    wq_merge_mask[3:0]    =  wq_merge_addr_r[3] 
                           ? {dmp_wq_bank_mask0[3], 3'b000}
                           : {dmp_wq_bank_mask0[3:1],1'b0};
  end

  3'b110: // 0x06 or 0x0E
  begin
    // This will be written at the wr_ptr_merge_r location
    //
    wq_merge_mask[3:0]    =  wq_merge_addr_r[3] 
                           ? {dmp_wq_bank_mask0[3], 3'b000}
                           : {dmp_wq_bank_mask0[3:1],1'b0};
  end
  
  3'b111: // 0x07 or 0x0F
  begin
    // This will be written at the wr_ptr_merge_r location
    //
    wq_merge_mask[3:0]    =  wq_merge_addr_r[3] 
                           ? {dmp_wq_bank_mask0[3], 3'b000}
                           : {dmp_wq_bank_mask0[3:1],1'b0};
  end
// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems
  default: ;
// spyglass enable_block W193
  endcase
end
//////////////////////////////////////////////////////////////////////////////
// Asynchronous process to extract the merge size
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wr_merge_hot_PROC
  case (1'b1)
  wr_merge_hot_r[0]: wq_merging_size = wq0_size_r;
  wr_merge_hot_r[1]: wq_merging_size = wq1_size_r;
  wr_merge_hot_r[2]: wq_merging_size = wq2_size_r;
  default:           wq_merging_size = wq3_size_r;
  endcase  
end

assign ca_store_byte   = ca_size_r == 2'b00;
assign ca_store_half   = ca_size_r == 2'b01; 
assign ca_store_word   = ca_size_r == 2'b10; 
assign ca_store_double = ca_size_r == 2'b11; 

//////////////////////////////////////////////////////////////////////////////
// Asynchronous process to extract the merge size
//
//////////////////////////////////////////////////////////////////////////////

always @*
begin : wq_merge_data_PROC
  wq_merge_data[63:0] = 64'd0;
  wq_merge_size       = 3'b000;
  wq_merge_ovf        = 1'b0;
  
  case (wq_merging_size)
  3'b000:
  begin
    // Merging entry has a single byte
    //
    wq_merge_data[63:8]   = dmp_wq_data0[55:0];
    wq_merge_ovf          = ca_store_double;
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept     
    case (1'b1)
    ca_store_byte:   wq_merge_size = 3'b001; // 1 + byte
    ca_store_half:   wq_merge_size = 3'b100; // 1 + half
    ca_store_word:   wq_merge_size = 3'b101; // 1 + word
    ca_store_double: wq_merge_size = 3'b011; // 1 + double
    default:;
    endcase
  end
   
  3'b001:
  begin
    // Merging entry has 2 bytes
    //
    wq_merge_data[63:16]  = dmp_wq_data0[47:0];
    wq_merge_ovf          = ca_store_double;
    
    case (1'b1)
    ca_store_byte:   wq_merge_size = 3'b100; // 2 + byte
    ca_store_half:   wq_merge_size = 3'b010; // 2 + half
    ca_store_word:   wq_merge_size = 3'b110; // 2 + word
    ca_store_double: wq_merge_size = 3'b011; // 2 + double
    default:;
    endcase
  end
  
  3'b100:
  begin
    // Merging entry has 3 bytes
    //
    wq_merge_data[63:24]  = dmp_wq_data0[39:0];
    wq_merge_ovf          = ca_store_double;
    
    case (1'b1)
    ca_store_byte:   wq_merge_size = 3'b010; // 3 + byte
    ca_store_half:   wq_merge_size = 3'b101; // 3 + half
    ca_store_word:   wq_merge_size = 3'b111; // 3 + word
    ca_store_double: wq_merge_size = 3'b011; // 3 + double
    default:;
    endcase
  end
  
  3'b010:
  begin
    // Merging entry has 4 bytes
    //
    wq_merge_data[63:32]  = dmp_wq_data0[31:0];
    wq_merge_ovf          = ca_store_double;
    
    case (1'b1)
    ca_store_byte:   wq_merge_size = 3'b101; // 4 + byte
    ca_store_half:   wq_merge_size = 3'b110; // 4 + half
    ca_store_word:   wq_merge_size = 3'b011; // 4 + word
    ca_store_double: wq_merge_size = 3'b011; // 4 + double
    default:;
    endcase
  end
  
  3'b101:
  begin
    // Merging entry has 5 bytes
    //
    wq_merge_data[63:40]  = dmp_wq_data0[23:0];
    wq_merge_ovf          = (ca_store_word | ca_store_double);
    
    case (1'b1)
    ca_store_byte:   wq_merge_size = 3'b110; // 5 + byte
    ca_store_half:   wq_merge_size = 3'b111; // 5 + half
    ca_store_word:   wq_merge_size = 3'b011; // 5 + word
    ca_store_double: wq_merge_size = 3'b011; // 5 + double
    default:;
    endcase
  end
  
  3'b110:
  begin
    // Merging entry has 6 bytes
    //
    wq_merge_data[63:48]  = dmp_wq_data0[15:0];
    wq_merge_ovf          = (ca_store_word | ca_store_double);
    
    case (1'b1)
    ca_store_byte:   wq_merge_size = 3'b111; // 6 + byte
    ca_store_half:   wq_merge_size = 3'b011; // 6 + half
    ca_store_word:   wq_merge_size = 3'b011; // 6 + word
    ca_store_double: wq_merge_size = 3'b011; // 6 + double
    default:;
    endcase
  end
  
  3'b111:
  begin
    // Merging entry has 7 bytes
    //
    wq_merge_data[63:56]  = dmp_wq_data0[7:0];
    wq_merge_ovf          = (ca_store_half | ca_store_word | ca_store_double);
    
    case (1'b1)
    ca_store_byte:   wq_merge_size = 3'b011; // 7 + byte
    ca_store_half:   wq_merge_size = 3'b011; // 7 + half
    ca_store_word:   wq_merge_size = 3'b011; // 7 + word
    ca_store_double: wq_merge_size = 3'b011; // 7 + double 
    default:;
    endcase
  end
// spyglass enable_block W193  
  default:
  begin
    // Merging entry has 8 bytes
    //
    wq_merge_ovf          = ca_store_r;
  end  
  endcase
end



//////////////////////////////////////////////////////////////////////////////
// Asynchronous logic to determine the next external entry to be retired
//
//////////////////////////////////////////////////////////////////////////////

always @*
begin : wq_ext_valid_PROC
  
  case (wq_ext_rdentry0)
  2'd0:
  begin
    wq_ext_valid              = wq_ext_rdentry_valid;                               
    wq_ext_bufferable         = wq_data_mem_attr_r[0];
    wq_ext_data_bank0         = wq0_aln_data_bank0;         
    wq_ext_data_bank1         = wq0_aln_data_bank1;   
    wq_ext_mask_bank0         = wq0_aln_mask_bank0;
    wq_ext_mask_bank1         = wq0_aln_mask_bank1;
    wq_ext_addr               = wq0_addr_r;   
    wq_ext_size               = wq0_size_r[2] ? 2'b11 : wq0_size_r[1:0];   
    wq_ext_user_mode          = wq0_user_mode_r;
    wq_ext_target             = wq0_target_r;  
    wq_ext_top_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[0]}} 
                                & wq0_bank_mask_r;
    wq_ext_scond              = wq0_scond_r;
  end
  
  2'd1:
  begin
    wq_ext_valid              = wq_ext_rdentry_valid;                               
    wq_ext_bufferable         = wq_data_mem_attr_r[1];
    wq_ext_data_bank0         = wq1_aln_data_bank0;         
    wq_ext_data_bank1         = wq1_aln_data_bank1;   
    wq_ext_mask_bank0         = wq1_aln_mask_bank0;
    wq_ext_mask_bank1         = wq1_aln_mask_bank1;
    wq_ext_addr               = wq1_addr_r;   
    wq_ext_size               = wq1_size_r[2] ? 2'b11 : wq1_size_r[1:0];   
    wq_ext_user_mode          = wq1_user_mode_r;
    wq_ext_target             = wq1_target_r;  
    wq_ext_top_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[1]}} 
                                & wq1_bank_mask_r;
    wq_ext_scond              = wq1_scond_r;
  end
  
  2'd2:
  begin
    wq_ext_valid              = wq_ext_rdentry_valid;                               
    wq_ext_bufferable         = wq_data_mem_attr_r[2];
    wq_ext_data_bank0         = wq2_aln_data_bank0;         
    wq_ext_data_bank1         = wq2_aln_data_bank1;   
    wq_ext_mask_bank0         = wq2_aln_mask_bank0;
    wq_ext_mask_bank1         = wq2_aln_mask_bank1;
    wq_ext_addr               = wq2_addr_r;   
    wq_ext_size               = wq2_size_r[2] ? 2'b11 : wq2_size_r[1:0];   
    wq_ext_user_mode          = wq2_user_mode_r;
    wq_ext_target             = wq2_target_r;  
    wq_ext_top_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[2]}} 
                                & wq2_bank_mask_r;
    wq_ext_scond              = wq2_scond_r;
  end
  
  default:
  begin
    wq_ext_valid              = wq_ext_rdentry_valid;                               
    wq_ext_bufferable         = wq_data_mem_attr_r[3];
    wq_ext_data_bank0         = wq3_aln_data_bank0;         
    wq_ext_data_bank1         = wq3_aln_data_bank1;   
    wq_ext_mask_bank0         = wq3_aln_mask_bank0;
    wq_ext_mask_bank1         = wq3_aln_mask_bank1;
    wq_ext_addr               = wq3_addr_r;   
    wq_ext_size               = wq3_size_r[2] ? 2'b11 : wq3_size_r[1:0];   
    wq_ext_user_mode          = wq3_user_mode_r;
    wq_ext_target             = wq3_target_r;  
    wq_ext_top_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[3]}} 
                                & wq3_bank_mask_r;
    wq_ext_scond              = wq3_scond_r;

  end
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous logic to determine the next internal entry to be retired
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_dc_valid_PROC
  
  case (wq_dc_rdentry0)
  2'd0:
  begin
    wq_dc_valid              = wq_dc_rdentry_valid;                                
    wq_way_hot               = wq0_way_hot_r;
    wq_dc_data_bank0         = wq0_aln_data_bank0;   
    wq_dc_data_bank1         = wq0_aln_data_bank1;   
    wq_dc_mask_bank0         = wq0_aln_mask_bank0;
    wq_dc_mask_bank1         = wq0_aln_mask_bank1;
    wq_dc_addr               = wq0_addr_r;   
    wq_dc_target             = wq0_target_r;  
    wq_dc_top_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[0]}} 
                               & wq0_bank_mask_r;
    wq_dc_scond              = wq0_scond_r;
    wq_skid_ctrl_mask        =   {16{dc3_wq_conflict[0] & (~x3_pass)}} // when there is no x3_pass; (either it is stalled by exu or dc3_stall_r)
                               & {wq0_aln_mask_bank1, wq0_aln_mask_bank0};
  end
  
  2'd1:
  begin
    wq_dc_valid              = wq_dc_rdentry_valid;                                
    wq_way_hot               = wq1_way_hot_r;
    wq_dc_data_bank0         = wq1_aln_data_bank0;   
    wq_dc_data_bank1         = wq1_aln_data_bank1;   
    wq_dc_mask_bank0         = wq1_aln_mask_bank0;
    wq_dc_mask_bank1         = wq1_aln_mask_bank1;
    wq_dc_addr               = wq1_addr_r;   
    wq_dc_target             = wq1_target_r;  
    wq_dc_top_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[1]}} 
                               & wq1_bank_mask_r;
    wq_dc_scond              = wq1_scond_r;
    wq_skid_ctrl_mask        =   {16{dc3_wq_conflict[1] & (~x3_pass)}} // when there is no x3_pass; (either it is stalled by exu or dc3_stall_r)
                               & {wq1_aln_mask_bank1, wq1_aln_mask_bank0};
  end
  
  2'd2:
  begin
    wq_dc_valid              = wq_dc_rdentry_valid;                                
    wq_way_hot               = wq2_way_hot_r;
    wq_dc_data_bank0         = wq2_aln_data_bank0;   
    wq_dc_data_bank1         = wq2_aln_data_bank1;   
    wq_dc_mask_bank0         = wq2_aln_mask_bank0;
    wq_dc_mask_bank1         = wq2_aln_mask_bank1;
    wq_dc_addr               = wq2_addr_r;   
    wq_dc_target             = wq2_target_r;  
    wq_dc_top_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[2]}} 
                               & wq2_bank_mask_r;
    wq_dc_scond              = wq2_scond_r;
    wq_skid_ctrl_mask        =   {16{dc3_wq_conflict[2] & (~x3_pass)}} // when there is no x3_pass; (either it is stalled by exu or dc3_stall_r)
                               & {wq2_aln_mask_bank1, wq2_aln_mask_bank0};
  end
  
  default:
  begin
    wq_dc_valid              = wq_dc_rdentry_valid;                                
    wq_way_hot               = wq3_way_hot_r;
    wq_dc_data_bank0         = wq3_aln_data_bank0;   
    wq_dc_data_bank1         = wq3_aln_data_bank1;   
    wq_dc_mask_bank0         = wq3_aln_mask_bank0;
    wq_dc_mask_bank1         = wq3_aln_mask_bank1;
    wq_dc_addr               = wq3_addr_r;   
    wq_dc_target             = wq3_target_r;  
    wq_dc_top_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[3]}} 
                               & wq3_bank_mask_r;
    wq_dc_scond              = wq3_scond_r;
    wq_skid_ctrl_mask        =   {16{dc3_wq_conflict[3] & (~x3_pass)}}
                               & {wq3_aln_mask_bank1, wq3_aln_mask_bank0};
  end
  endcase
end


//////////////////////////////////////////////////////////////////////////////
// Second internal entry to be retired
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_sec_valid_PROC
  case (wq_dc_rdentry1)
  2'd0:
  begin
    wq_sec_valid          = wq_dc_rdentry_valid & (~wq_dep_r[0]) & (~wq_grad_r[0]) & x3_pass;
    wq_sec_way_hot        = wq0_way_hot_r;
    wq_sec_data_bank0     = wq0_aln_data_bank0;
    wq_sec_data_bank1     = wq0_aln_data_bank1;
    wq_sec_mask_bank0     = wq0_aln_mask_bank0;   
    wq_sec_mask_bank1     = wq0_aln_mask_bank1;   
    wq_sec_addr           = wq0_addr_r;   
    wq_sec_target         = wq0_target_r;  
    wq_sec_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[0]}}  
                            & wq0_bank_mask_r;
  end
  
  2'd1:
  begin
    wq_sec_valid          = wq_dc_rdentry_valid & (~wq_dep_r[1]) & (~wq_grad_r[1]) & x3_pass;
    wq_sec_way_hot        = wq1_way_hot_r;
    wq_sec_data_bank0     = wq1_aln_data_bank0;
    wq_sec_data_bank1     = wq1_aln_data_bank1;
    wq_sec_mask_bank0     = wq1_aln_mask_bank0;   
    wq_sec_mask_bank1     = wq1_aln_mask_bank1;   
    wq_sec_addr           = wq1_addr_r;   
    wq_sec_target         = wq1_target_r;  
    wq_sec_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[1]}}  
                            & wq1_bank_mask_r;
  end
  
  2'd2:
  begin
    wq_sec_valid          = wq_dc_rdentry_valid & (~wq_dep_r[2]) & (~wq_grad_r[2]) & x3_pass;
    wq_sec_way_hot        = wq2_way_hot_r;
    wq_sec_data_bank0     = wq2_aln_data_bank0;
    wq_sec_data_bank1     = wq2_aln_data_bank1;
    wq_sec_mask_bank0     = wq2_aln_mask_bank0;   
    wq_sec_mask_bank1     = wq2_aln_mask_bank1;   
    wq_sec_addr           = wq2_addr_r;   
    wq_sec_target         = wq2_target_r;  
    wq_sec_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[2]}}  
                            & wq2_bank_mask_r;
  end
  
  2'd3:
  begin
    wq_sec_valid          = wq_dc_rdentry_valid & (~wq_dep_r[3]) & (~wq_grad_r[3]) & x3_pass;
    wq_sec_way_hot        = wq3_way_hot_r;
    wq_sec_data_bank0     = wq3_aln_data_bank0;
    wq_sec_data_bank1     = wq3_aln_data_bank1;
    wq_sec_mask_bank0     = wq3_aln_mask_bank0;   
    wq_sec_mask_bank1     = wq3_aln_mask_bank1;   
    wq_sec_addr           = wq3_addr_r;   
    wq_sec_target         = wq3_target_r;  
    wq_sec_bank_req_mask  =  {`npuarc_DMP_FIFO_DEPTH{wq_valid_r[3]}}  
                            & wq3_bank_mask_r;
  end
  
  default:
  begin
    wq_sec_valid          = 1'b0;
    wq_sec_way_hot        = 2'b00;
    wq_sec_data_bank0     = `npuarc_DOUBLE_SIZE'd0;
    wq_sec_data_bank1     = `npuarc_DOUBLE_SIZE'd0;
    wq_sec_mask_bank0     = `npuarc_DOUBLE_BE_SIZE'd0;   
    wq_sec_mask_bank1     = `npuarc_DOUBLE_BE_SIZE'd0;   
    wq_sec_addr           = `npuarc_PADDR_SIZE'd0;
    wq_sec_target         = `npuarc_DMP_TARGET_BITS'd0;  
    wq_sec_bank_req_mask  = 4'd0; 
  
  end
  endcase
end

//////////////////////////////////////////////////////////////////////////////
//@
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_dccm_entry_PROC
  wq_dccm_top_bank_req_mask = wq_dc_top_bank_req_mask;
  wq_dccm_sec_bank_req_mask = wq_sec_bank_req_mask;
end
//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to report a valid DCCM/DC entry in WQ
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_dc_entry_PROC
  wq_dc_entry =   1'b0
               |  (    wq_valid_r[0]
                    & (  (wq0_target_r == `npuarc_DMP_TARGET_DCCM) 
                       | (wq0_target_r == `npuarc_DMP_TARGET_DC))
                   ) 
      
               |  (    wq_valid_r[1]
                    & (  (wq1_target_r == `npuarc_DMP_TARGET_DCCM) 
                       | (wq1_target_r == `npuarc_DMP_TARGET_DC))
                   ) 
      
               |  (    wq_valid_r[2]
                    & (  (wq2_target_r == `npuarc_DMP_TARGET_DCCM) 
                       | (wq2_target_r == `npuarc_DMP_TARGET_DC))
                   ) 
      
               |  (    wq_valid_r[3]
                    & (  (wq3_target_r == `npuarc_DMP_TARGET_DCCM) 
                       | (wq3_target_r == `npuarc_DMP_TARGET_DC))
                   ) 
      
               ;
  
  wq_non_dc_entry =  1'b0
               |  (    wq_valid_r[0]
                    & (  (wq0_target_r != `npuarc_DMP_TARGET_DCCM) 
                       & (wq0_target_r != `npuarc_DMP_TARGET_DC))
                   ) 
      
               |  (    wq_valid_r[1]
                    & (  (wq1_target_r != `npuarc_DMP_TARGET_DCCM) 
                       & (wq1_target_r != `npuarc_DMP_TARGET_DC))
                   ) 
      
               |  (    wq_valid_r[2]
                    & (  (wq2_target_r != `npuarc_DMP_TARGET_DCCM) 
                       & (wq2_target_r != `npuarc_DMP_TARGET_DC))
                   ) 
      
               |  (    wq_valid_r[3]
                    & (  (wq3_target_r != `npuarc_DMP_TARGET_DCCM) 
                       & (wq3_target_r != `npuarc_DMP_TARGET_DC))
                   ) 
      
               ;

  wq_ex_non_dc_entry = 1'b0
               |  (   wq_valid_r[0]
                    & wq0_external_ex_r) 
      
               |  (   wq_valid_r[1]
                    & wq1_external_ex_r) 
      
               |  (   wq_valid_r[2]
                    & wq2_external_ex_r) 
      
               |  (   wq_valid_r[3]
                    & wq3_external_ex_r) 
      
               ;
                   
                
 
  wq_scond_entry = 1'b0
               |  (   wq_valid_r[0] 
                    & wq0_scond_r
                  )
               |  (   wq_valid_r[1] 
                    & wq1_scond_r
                  )
               |  (   wq_valid_r[2] 
                    & wq2_scond_r
                  )
               |  (   wq_valid_r[3] 
                    & wq3_scond_r
                  )
                ;
  

  wq_target_dc =   1'b0
               |  (   wq_valid_r[0] 
                    & (wq0_target_r == `npuarc_DMP_TARGET_DC)
                  )
               |  (   wq_valid_r[1] 
                    & (wq1_target_r == `npuarc_DMP_TARGET_DC)
                  )
               |  (   wq_valid_r[2] 
                    & (wq2_target_r == `npuarc_DMP_TARGET_DC)
                  )
               |  (   wq_valid_r[3] 
                    & (wq3_target_r == `npuarc_DMP_TARGET_DC)
                  )
               ;


end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to report external entries in the WQ
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin: wq_external_entries_PROC
  // External entries in the WQ
  //
  wq_external_entries[0] = (    wq_valid_r[0] 
                             &   (wq0_target_r != `npuarc_DMP_TARGET_DCCM)
                             &   (wq0_target_r != `npuarc_DMP_TARGET_DC)
                            );     
  wq_external_entries[1] = (    wq_valid_r[1] 
                             &   (wq1_target_r != `npuarc_DMP_TARGET_DCCM)
                             &   (wq1_target_r != `npuarc_DMP_TARGET_DC)
                            );     
  wq_external_entries[2] = (    wq_valid_r[2] 
                             &   (wq2_target_r != `npuarc_DMP_TARGET_DCCM)
                             &   (wq2_target_r != `npuarc_DMP_TARGET_DC)
                            );     
  wq_external_entries[3] = (    wq_valid_r[3] 
                             &   (wq3_target_r != `npuarc_DMP_TARGET_DCCM)
                             &   (wq3_target_r != `npuarc_DMP_TARGET_DC)
                            );     
end
//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to report internal entries in the WQ
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin: wq_internal_entries_PROC
  wq_internal_entries[0] = (    wq_valid_r[0] 
                             &  (~wq_external_entries[0]));     
  wq_internal_entries[1] = (    wq_valid_r[1] 
                             &  (~wq_external_entries[1]));     
  wq_internal_entries[2] = (    wq_valid_r[2] 
                             &  (~wq_external_entries[2]));     
  wq_internal_entries[3] = (    wq_valid_r[3] 
                             &  (~wq_external_entries[3]));     
end


reg [`npuarc_DMP_FIFO_RANGE] wq_dmu_conflict;
reg [`npuarc_DMP_FIFO_RANGE] wq_dmu_same_set_conflict;
//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to report set conflicts with the DMU (copy back unit)
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_dmu_conflict_PROC
  
  wq_dmu_conflict[0]  =  (    wq_valid_r[0]
                            & (wq0_target_r              == `npuarc_DMP_TARGET_DC)
                            & (wq0_addr_r[`npuarc_DC_SET_RANGE] == dmu_set_addr)  
                          )
                          ; 
      
  wq_dmu_conflict[1]  =  (    wq_valid_r[1]
                            & (wq1_target_r              == `npuarc_DMP_TARGET_DC)
                            & (wq1_addr_r[`npuarc_DC_SET_RANGE] == dmu_set_addr)  
                          )
                          ; 
      
  wq_dmu_conflict[2]  =  (    wq_valid_r[2]
                            & (wq2_target_r              == `npuarc_DMP_TARGET_DC)
                            & (wq2_addr_r[`npuarc_DC_SET_RANGE] == dmu_set_addr)  
                          )
                          ; 
      
  wq_dmu_conflict[3]  =  (    wq_valid_r[3]
                            & (wq3_target_r              == `npuarc_DMP_TARGET_DC)
                            & (wq3_addr_r[`npuarc_DC_SET_RANGE] == dmu_set_addr)  
                          )
                          ; 
      
   
  wq_dmu_same_set_conflict [0] = (   wq_dmu_conflict[0]
                                   )
                                   ; 
  wq_dmu_same_set_conflict [1] = (   wq_dmu_conflict[1]
                                   )
                                   ; 
  wq_dmu_same_set_conflict [2] = (   wq_dmu_conflict[2]
                                   )
                                   ; 
  wq_dmu_same_set_conflict [3] = (   wq_dmu_conflict[3]
                                   )
                                   ; 
  
   wq_dmu_set_conflict           = | (wq_dmu_same_set_conflict);
end


//////////////////////////////////////////////////////////////////////////////
// On the fly alignment
// 
//////////////////////////////////////////////////////////////////////////////

wire st_instrs_discarded_nxt;

assign st_instrs_discarded_nxt = (holdup_excpn_r & (|wq_garbage_r)) ? 1'b1 :
                                    st_instrs_discarded_r ? 1'b0 : st_instrs_discarded ;
always @(posedge clk or posedge rst_a)
begin : st_discard_proc 
  if (rst_a == 1'b1)
    st_instrs_discarded <= 1'b0;
  else 
    st_instrs_discarded <= st_instrs_discarded_nxt;
end

npuarc_alb_dmp_store_aligner u_alb_dmp_store_aligner_0 (
  .addr_3_to_0   (wq0_addr_r[3:0]                   ),
  .data          (wq0_data_r                        ),
  
  .bank0_data    (wq0_aln_data_bank0                ), 
  .bank1_data    (wq0_aln_data_bank1                ) 
);

npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_0 (
  .size           (wq0_size_r                       ),
  .addr_3_to_0    (wq0_addr_r[3:0]                  ),
  .valid_r        (~wq_garbage_r[0]                   ), 
  
  .bank0_mask     (wq0_aln_mask_bank0               ), // hi-lo
  .bank1_mask     (wq0_aln_mask_bank1               )  // hi-lo
);
npuarc_alb_dmp_store_aligner u_alb_dmp_store_aligner_1 (
  .addr_3_to_0   (wq1_addr_r[3:0]                   ),
  .data          (wq1_data_r                        ),
  
  .bank0_data    (wq1_aln_data_bank0                ), 
  .bank1_data    (wq1_aln_data_bank1                ) 
);

npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_1 (
  .size           (wq1_size_r                       ),
  .addr_3_to_0    (wq1_addr_r[3:0]                  ),
  .valid_r        (~wq_garbage_r[1]                   ), 
  
  .bank0_mask     (wq1_aln_mask_bank0               ), // hi-lo
  .bank1_mask     (wq1_aln_mask_bank1               )  // hi-lo
);
npuarc_alb_dmp_store_aligner u_alb_dmp_store_aligner_2 (
  .addr_3_to_0   (wq2_addr_r[3:0]                   ),
  .data          (wq2_data_r                        ),
  
  .bank0_data    (wq2_aln_data_bank0                ), 
  .bank1_data    (wq2_aln_data_bank1                ) 
);

npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_2 (
  .size           (wq2_size_r                       ),
  .addr_3_to_0    (wq2_addr_r[3:0]                  ),
  .valid_r        (~wq_garbage_r[2]                   ), 
  
  .bank0_mask     (wq2_aln_mask_bank0               ), // hi-lo
  .bank1_mask     (wq2_aln_mask_bank1               )  // hi-lo
);
npuarc_alb_dmp_store_aligner u_alb_dmp_store_aligner_3 (
  .addr_3_to_0   (wq3_addr_r[3:0]                   ),
  .data          (wq3_data_r                        ),
  
  .bank0_data    (wq3_aln_data_bank0                ), 
  .bank1_data    (wq3_aln_data_bank1                ) 
);

npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_3 (
  .size           (wq3_size_r                       ),
  .addr_3_to_0    (wq3_addr_r[3:0]                  ),
  .valid_r        (~wq_garbage_r[3]                   ), 
  
  .bank0_mask     (wq3_aln_mask_bank0               ), // hi-lo
  .bank1_mask     (wq3_aln_mask_bank1               )  // hi-lo
);

npuarc_alb_dmp_store_aligner u_alb_dmp_store_aligner_4 (
  .addr_3_to_0   (dmp_wq_addr0[3:0]                 ),
  .data          (dmp_wq_data0                      ),
  
  .bank0_data    (dc40_aln_data_bank0               ), 
  .bank1_data    (dc40_aln_data_bank1               ) 
);

npuarc_alb_dmp_store_aligner u_alb_dmp_store_aligner_5 (
  .addr_3_to_0   (dmp_wq_addr1[3:0]                 ),
  .data          (dmp_wq_data1                      ),
  
  .bank0_data    (dc41_aln_data_bank0               ), 
  .bank1_data    (dc41_aln_data_bank1               ) 
);

// DC4 store0
//
npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_4 (
  .size           (dmp_wq_size0              ),
  .addr_3_to_0    (dmp_wq_addr0[3:0]         ),
  .valid_r        (1'b1                      ),
  
  .bank0_mask     (dc40_mask_bank0           ), // hi-lo
  .bank1_mask     (dc40_mask_bank1           )  // hi-lo
);

// DC4 store1
//
npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_5 (
  .size           (dmp_wq_size1              ), 
  .addr_3_to_0    (dmp_wq_addr1[3:0]         ), 
  .valid_r        (1'b1                      ),
  
  .bank0_mask     (dc41_mask_bank0           ), // hi-lo
  .bank1_mask     (dc41_mask_bank1           )  // hi-lo
);


npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_6 (
  .size           (dc3_size0_r               ),
  .addr_3_to_0    (x3_mem_addr0_r[3:0]       ),
  .valid_r        (1'b1                      ),
  
  .bank0_mask     (dc30_mask_bank0           ), // hi-lo
  .bank1_mask     (dc30_mask_bank1           )  // hi-lo
);

// DC3 load1
//
npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_7 (
  .size           (dc3_size1_r              ),
  .addr_3_to_0    (x3_mem_addr1_r[3:0]      ),
  .valid_r        (1'b1                      ),

  .bank0_mask     (dc31_mask_bank0          ), // hi-lo
  .bank1_mask     (dc31_mask_bank1          )  // hi-lo
);

//////////////////////////////////////////////////////////////////////////////
// Check for partial/full mask matches on every bank
// We do this for load0 (x3_mem_addr0) and for load1 (x3_mem_addr1)
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_dmp_bank_match u_alb_dmp_bank_match_load0_0 (
  .dc3_mask          (dc30_mask_bank0[3:0]    ),
  
  .dc40_mask         (dc40_mask_bank0[3:0]       ),
  .dc41_mask         (dc41_mask_bank0[3:0]       ),
  .wq0_mask          (wq0_aln_mask_bank0[3:0]    ),
  .wq1_mask          (wq1_aln_mask_bank0[3:0]    ),
  .wq2_mask          (wq2_aln_mask_bank0[3:0]    ),
  .wq3_mask          (wq3_aln_mask_bank0[3:0]    ),
  
  .dc40_addr_match   (dc40_addr0_match_qual   ),
  .dc41_addr_match   (dc41_addr0_match_qual   ), 
  .wq0_addr_match    (wq0_addr0_match_qual    ),
  .wq1_addr_match    (wq1_addr0_match_qual    ),
  .wq2_addr_match    (wq2_addr0_match_qual    ),
  .wq3_addr_match    (wq3_addr0_match_qual    ),

  .wq_recent_wr_r    (wq_recent_wr_r             ),

  .match_dc40        (match0_dc40_bank0_lo    ),
  .match_dc41        (match0_dc41_bank0_lo    ),
  .match_wq0         (match0_wq0_bank0_lo     ),
  .match_wq1         (match0_wq1_bank0_lo     ),
  .match_wq2         (match0_wq2_bank0_lo     ),
  .match_wq3         (match0_wq3_bank0_lo     ),

  .replay            (replay0_bank0_lo        ),
  .fwd_enable        (fwd_enable0_bank0_lo    )
);
npuarc_alb_dmp_bank_match u_alb_dmp_bank_match_load1_0 (
  .dc3_mask          (dc31_mask_bank0[3:0]    ),
  
  .dc40_mask         (dc40_mask_bank0[3:0]       ),
  .dc41_mask         (dc41_mask_bank0[3:0]       ),
  .wq0_mask          (wq0_aln_mask_bank0[3:0]    ),
  .wq1_mask          (wq1_aln_mask_bank0[3:0]    ),
  .wq2_mask          (wq2_aln_mask_bank0[3:0]    ),
  .wq3_mask          (wq3_aln_mask_bank0[3:0]    ),
  
  .dc40_addr_match   (dc40_addr1_match_qual   ),
  .dc41_addr_match   (dc41_addr1_match_qual   ), 
  .wq0_addr_match    (wq0_addr1_match_qual    ),
  .wq1_addr_match    (wq1_addr1_match_qual    ),
  .wq2_addr_match    (wq2_addr1_match_qual    ),
  .wq3_addr_match    (wq3_addr1_match_qual    ),

  .wq_recent_wr_r    (wq_recent_wr_r             ),

  .match_dc40        (match1_dc40_bank0_lo    ),
  .match_dc41        (match1_dc41_bank0_lo    ),
  .match_wq0         (match1_wq0_bank0_lo     ),
  .match_wq1         (match1_wq1_bank0_lo     ),
  .match_wq2         (match1_wq2_bank0_lo     ),
  .match_wq3         (match1_wq3_bank0_lo     ),

  .replay            (replay1_bank0_lo        ),
  .fwd_enable        (fwd_enable1_bank0_lo    )
);

npuarc_alb_dmp_bank_match u_alb_dmp_bank_match_load0_1 (
  .dc3_mask          (dc30_mask_bank0[7:4]    ),
  
  .dc40_mask         (dc40_mask_bank0[7:4]       ),
  .dc41_mask         (dc41_mask_bank0[7:4]       ),
  .wq0_mask          (wq0_aln_mask_bank0[7:4]    ),
  .wq1_mask          (wq1_aln_mask_bank0[7:4]    ),
  .wq2_mask          (wq2_aln_mask_bank0[7:4]    ),
  .wq3_mask          (wq3_aln_mask_bank0[7:4]    ),
  
  .dc40_addr_match   (dc40_addr0_match_qual   ),
  .dc41_addr_match   (dc41_addr0_match_qual   ),
  .wq0_addr_match    (wq0_addr0_match_qual    ),
  .wq1_addr_match    (wq1_addr0_match_qual    ),
  .wq2_addr_match    (wq2_addr0_match_qual    ),
  .wq3_addr_match    (wq3_addr0_match_qual    ),

  .wq_recent_wr_r    (wq_recent_wr_r             ),

  .match_dc40        (match0_dc40_bank0_hi    ),
  .match_dc41        (match0_dc41_bank0_hi    ),
  .match_wq0         (match0_wq0_bank0_hi     ),
  .match_wq1         (match0_wq1_bank0_hi     ),
  .match_wq2         (match0_wq2_bank0_hi     ),
  .match_wq3         (match0_wq3_bank0_hi     ),

  .replay            (replay0_bank0_hi        ),
  .fwd_enable        (fwd_enable0_bank0_hi    )
);
npuarc_alb_dmp_bank_match u_alb_dmp_bank_match_load1_1 (
  .dc3_mask          (dc31_mask_bank0[7:4]    ),
  
  .dc40_mask         (dc40_mask_bank0[7:4]       ),
  .dc41_mask         (dc41_mask_bank0[7:4]       ),
  .wq0_mask          (wq0_aln_mask_bank0[7:4]    ),
  .wq1_mask          (wq1_aln_mask_bank0[7:4]    ),
  .wq2_mask          (wq2_aln_mask_bank0[7:4]    ),
  .wq3_mask          (wq3_aln_mask_bank0[7:4]    ),
  
  .dc40_addr_match   (dc40_addr1_match_qual   ),
  .dc41_addr_match   (dc41_addr1_match_qual   ),
  .wq0_addr_match    (wq0_addr1_match_qual    ),
  .wq1_addr_match    (wq1_addr1_match_qual    ),
  .wq2_addr_match    (wq2_addr1_match_qual    ),
  .wq3_addr_match    (wq3_addr1_match_qual    ),

  .wq_recent_wr_r    (wq_recent_wr_r             ),

  .match_dc40        (match1_dc40_bank0_hi    ),
  .match_dc41        (match1_dc41_bank0_hi    ),
  .match_wq0         (match1_wq0_bank0_hi     ),
  .match_wq1         (match1_wq1_bank0_hi     ),
  .match_wq2         (match1_wq2_bank0_hi     ),
  .match_wq3         (match1_wq3_bank0_hi     ),

  .replay            (replay1_bank0_hi        ),
  .fwd_enable        (fwd_enable1_bank0_hi    )
);

///////////////////////////////////////////////////////////////////////////////
//                                                                          
// Only need for load and not load_plus_size                              
//                                                                         
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_dmp_bank_match u_alb_dmp_bank_match_load0_2 (
  .dc3_mask          (dc30_mask_bank1[3:0]    ),
  
  .dc40_mask         (dc40_mask_bank1[3:0]       ),
  .dc41_mask         (dc41_mask_bank1[3:0]       ),
  .wq0_mask          (wq0_aln_mask_bank1[3:0]    ),
  .wq1_mask          (wq1_aln_mask_bank1[3:0]    ),
  .wq2_mask          (wq2_aln_mask_bank1[3:0]    ),
  .wq3_mask          (wq3_aln_mask_bank1[3:0]    ),
  
  .dc40_addr_match   (dc40_addr0_match_qual   ),
  .dc41_addr_match   (dc41_addr0_match_qual   ),
  .wq0_addr_match    (wq0_addr0_match_qual    ),
  .wq1_addr_match    (wq1_addr0_match_qual    ),
  .wq2_addr_match    (wq2_addr0_match_qual    ),
  .wq3_addr_match    (wq3_addr0_match_qual    ),

  .wq_recent_wr_r    (wq_recent_wr_r             ),

  .match_dc40        (match0_dc40_bank1_lo    ),
  .match_dc41        (match0_dc41_bank1_lo    ),
  .match_wq0         (match0_wq0_bank1_lo     ),
  .match_wq1         (match0_wq1_bank1_lo     ),
  .match_wq2         (match0_wq2_bank1_lo     ),
  .match_wq3         (match0_wq3_bank1_lo     ),

  .replay            (replay0_bank1_lo        ),
  .fwd_enable        (fwd_enable0_bank1_lo    )
);

npuarc_alb_dmp_bank_match u_alb_dmp_bank_match_load0_3 (
  .dc3_mask          (dc30_mask_bank1[7:4]    ),
  
  .dc40_mask         (dc40_mask_bank1[7:4]       ),
  .dc41_mask         (dc41_mask_bank1[7:4]       ),
  .wq0_mask          (wq0_aln_mask_bank1[7:4]    ),
  .wq1_mask          (wq1_aln_mask_bank1[7:4]    ),
  .wq2_mask          (wq2_aln_mask_bank1[7:4]    ),
  .wq3_mask          (wq3_aln_mask_bank1[7:4]    ),
  
  .dc40_addr_match   (dc40_addr0_match_qual   ),
  .dc41_addr_match   (dc41_addr0_match_qual   ),
  .wq0_addr_match    (wq0_addr0_match_qual    ),
  .wq1_addr_match    (wq1_addr0_match_qual    ),
  .wq2_addr_match    (wq2_addr0_match_qual    ),
  .wq3_addr_match    (wq3_addr0_match_qual    ),

  .wq_recent_wr_r    (wq_recent_wr_r             ),

  .match_dc40        (match0_dc40_bank1_hi    ),
  .match_dc41        (match0_dc41_bank1_hi    ),
  .match_wq0         (match0_wq0_bank1_hi     ),
  .match_wq1         (match0_wq1_bank1_hi     ),
  .match_wq2         (match0_wq2_bank1_hi     ),
  .match_wq3         (match0_wq3_bank1_hi     ),

  .replay            (replay0_bank1_hi        ),
  .fwd_enable        (fwd_enable0_bank1_hi    )
);

//////////////////////////////////////////////////////////////////////////////
// Control of forwarding mux (bank0 lo)
//
//////////////////////////////////////////////////////////////////////////////
reg  match_dc40_bank0_lo;
reg  match_dc41_bank0_lo;

always @*
begin : match_dc40_bank0_lo_PROC
  // Forward when there is a match from load0 or load1 
  //
  match_dc40_bank0_lo    = match0_dc40_bank0_lo   | match1_dc40_bank0_lo;
  match_dc41_bank0_lo    = match0_dc41_bank0_lo   | match1_dc41_bank0_lo;
  
  match_wq0_bank0_lo    = match0_wq0_bank0_lo | match1_wq0_bank0_lo;
  match_wq1_bank0_lo    = match0_wq1_bank0_lo | match1_wq1_bank0_lo;
  match_wq2_bank0_lo    = match0_wq2_bank0_lo | match1_wq2_bank0_lo;
  match_wq3_bank0_lo    = match0_wq3_bank0_lo | match1_wq3_bank0_lo;
end

//////////////////////////////////////////////////////////////////////////////
// Control of forwarding mux (bank0 hi)
//
//////////////////////////////////////////////////////////////////////////////
reg  match_dc40_bank0_hi;
reg  match_dc41_bank0_hi;

always @*
begin : match_dc40_bank0_hi_PROC
  // Forward when there is a match from load0 or load1 
  //
  match_dc40_bank0_hi    = match0_dc40_bank0_hi    | match1_dc40_bank0_hi;
  match_dc41_bank0_hi    = match0_dc41_bank0_hi    | match1_dc41_bank0_hi;
  
  match_wq0_bank0_hi    = match0_wq0_bank0_hi | match1_wq0_bank0_hi;
  match_wq1_bank0_hi    = match0_wq1_bank0_hi | match1_wq1_bank0_hi;
  match_wq2_bank0_hi    = match0_wq2_bank0_hi | match1_wq2_bank0_hi;
  match_wq3_bank0_hi    = match0_wq3_bank0_hi | match1_wq3_bank0_hi;
end

//////////////////////////////////////////////////////////////////////////////
// Control of forwarding mux (bank1 lo)
//
//////////////////////////////////////////////////////////////////////////////
reg  match_dc40_bank1_lo;
reg  match_dc41_bank1_lo;

always @*
begin : match_dc40_bank1_lo_PROC
  // Forward when there is a match from load0 or load1 
  //
  match_dc40_bank1_lo    = match0_dc40_bank1_lo;
  match_dc41_bank1_lo    = match0_dc41_bank1_lo;
  
  match_wq0_bank1_lo    = match0_wq0_bank1_lo;
  match_wq1_bank1_lo    = match0_wq1_bank1_lo;
  match_wq2_bank1_lo    = match0_wq2_bank1_lo;
  match_wq3_bank1_lo    = match0_wq3_bank1_lo;
end

//////////////////////////////////////////////////////////////////////////////
// Control of forwarding mux (bank1 hi)
//
//////////////////////////////////////////////////////////////////////////////
reg  match_dc40_bank1_hi;
reg  match_dc41_bank1_hi;

always @*
begin : match_dc40_bank1_hi_PROC
  // Forward when there is a match from load0 or load1 
  //
  match_dc40_bank1_hi    = match0_dc40_bank1_hi;
  match_dc41_bank1_hi    = match0_dc41_bank1_hi;
  
  match_wq0_bank1_hi    = match0_wq0_bank1_hi;
  match_wq1_bank1_hi    = match0_wq1_bank1_hi;
  match_wq2_bank1_hi    = match0_wq2_bank1_hi;
  match_wq3_bank1_hi    = match0_wq3_bank1_hi;
end

//////////////////////////////////////////////////////////////////////////////
// Forwarding mux (bank0 lo)
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_fwd_data_bank0_lo_PROC
  case (1'b1)
  match_dc40_bank0_lo: wq_fwd_data_bank0_lo = dc40_aln_data_bank0[`npuarc_DBL_LO_RANGE];
  match_dc41_bank0_lo: wq_fwd_data_bank0_lo = dc41_aln_data_bank0[`npuarc_DBL_LO_RANGE];
  match_wq0_bank0_lo: wq_fwd_data_bank0_lo = wq0_aln_data_bank0[`npuarc_DBL_LO_RANGE];
  match_wq1_bank0_lo: wq_fwd_data_bank0_lo = wq1_aln_data_bank0[`npuarc_DBL_LO_RANGE];
  match_wq2_bank0_lo: wq_fwd_data_bank0_lo = wq2_aln_data_bank0[`npuarc_DBL_LO_RANGE];
  default:            wq_fwd_data_bank0_lo = wq3_aln_data_bank0[`npuarc_DBL_LO_RANGE]; 
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// Forwarding mux (bank0 hi)
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_fwd_data_bank0_hi_PROC
  case (1'b1)
  match_dc40_bank0_hi: wq_fwd_data_bank0_hi = dc40_aln_data_bank0[`npuarc_DBL_HI_RANGE];
  match_dc41_bank0_hi: wq_fwd_data_bank0_hi = dc41_aln_data_bank0[`npuarc_DBL_HI_RANGE];
  match_wq0_bank0_hi: wq_fwd_data_bank0_hi = wq0_aln_data_bank0[`npuarc_DBL_HI_RANGE];
  match_wq1_bank0_hi: wq_fwd_data_bank0_hi = wq1_aln_data_bank0[`npuarc_DBL_HI_RANGE];
  match_wq2_bank0_hi: wq_fwd_data_bank0_hi = wq2_aln_data_bank0[`npuarc_DBL_HI_RANGE];
  default:          wq_fwd_data_bank0_hi = wq3_aln_data_bank0[`npuarc_DBL_HI_RANGE]; 
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// Forwarding mux (bank1 lo)
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_fwd_data_bank1_lo_PROC
  case (1'b1)
  match_dc40_bank1_lo: wq_fwd_data_bank1_lo = dc40_aln_data_bank1[`npuarc_DBL_LO_RANGE];
  match_dc41_bank1_lo: wq_fwd_data_bank1_lo = dc41_aln_data_bank1[`npuarc_DBL_LO_RANGE];
  match_wq0_bank1_lo: wq_fwd_data_bank1_lo = wq0_aln_data_bank1[`npuarc_DBL_LO_RANGE];
  match_wq1_bank1_lo: wq_fwd_data_bank1_lo = wq1_aln_data_bank1[`npuarc_DBL_LO_RANGE];
  match_wq2_bank1_lo: wq_fwd_data_bank1_lo = wq2_aln_data_bank1[`npuarc_DBL_LO_RANGE];
  default:            wq_fwd_data_bank1_lo = wq3_aln_data_bank1[`npuarc_DBL_LO_RANGE];
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// Forwarding mux (bank1 hi)
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_fwd_data_bank1_hi_PROC
  case (1'b1)
  match_dc40_bank1_hi: wq_fwd_data_bank1_hi = dc40_aln_data_bank1[`npuarc_DBL_HI_RANGE];
  match_dc41_bank1_hi: wq_fwd_data_bank1_hi = dc41_aln_data_bank1[`npuarc_DBL_HI_RANGE];
  match_wq0_bank1_hi: wq_fwd_data_bank1_hi = wq0_aln_data_bank1[`npuarc_DBL_HI_RANGE];
  match_wq1_bank1_hi: wq_fwd_data_bank1_hi = wq1_aln_data_bank1[`npuarc_DBL_HI_RANGE];
  match_wq2_bank1_hi: wq_fwd_data_bank1_hi = wq2_aln_data_bank1[`npuarc_DBL_HI_RANGE];
  default:            wq_fwd_data_bank1_hi = wq3_aln_data_bank1[`npuarc_DBL_HI_RANGE];
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// 
// Module instantiation: Detection of conflicts between DC2 loads
// and downstream stalls that can't be resolved without stalls
//
//////////////////////////////////////////////////////////////////////////////

wire dc2_grad_conflict;         
wire dc2_partial_match_conflict;
wire dc2_multi_match_conflict;  

wire x2_load_prel;

assign x2_load_prel = x2_load_r
                    | (|dc2_rmw_r)
                    ;


// Recompute the mask and size using ca_mem_addr0_r and dc4_mem_addr1 instead of
// dmp_wq_addr0 & dmp_wq_addr1. because in case of ecc those will be different.
//   
wire [7:0]                 dc40_mask_bank0_prel;
wire [7:0]                 dc40_mask_bank1_prel;
wire [7:0]                 dc41_mask_bank0_prel;
wire [7:0]                 dc41_mask_bank1_prel;

wire [2:0]                 dc4_size0;


assign dc4_size0 = (ca_data_bank_sel_r[0] & ca_data_bank_sel_r[3]) 
                 ? dc4_size0_r 
                 : {1'b0,ca_size_r};

// DC4 store0
//
npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_g4 (
  .size                        (dc4_size0                 ),
  .addr_3_to_0                 (ca_mem_addr0_r[3:0]       ),
  .valid_r                     (1'b1                      ),

  .bank0_mask                  (dc40_mask_bank0_prel      ), // hi-lo
  .bank1_mask                  (dc40_mask_bank1_prel      )  // hi-lo
);

// DC4 store1
//
npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_g5 (
  .size                        (dc4_size1_r               ),
  .addr_3_to_0                 (dc4_mem_addr1_r[3:0]      ),
  .valid_r                     (1'b1                      ),

  .bank0_mask                  (dc41_mask_bank0_prel      ), // hi-lo
  .bank1_mask                  (dc41_mask_bank1_prel      )  // hi-lo
);


npuarc_alb_dmp_wq_conflict #(.ADDR_MSB (11)) 
  u_alb_dmp_wq_conflict  (

  .x2_load_r                   (x2_load_prel              ),
  .x2_size_r                   (x2_size_r                 ),  
  .x2_mem_addr0_r              (x2_mem_addr0_r[11:0]),  
  .x2_mem_addr1_r              (dc2_mem_addr1_r[11:0]), 
  .x2_bank_sel_r               (dc2_data_bank_sel_r       ),

  .x3_store_r                  (x3_store_r                ),
  .x3_store_may_grad           (x3_store_may_grad         ),
  .x3_mem_addr0_r              (x3_mem_addr0_r[11:0]),  
  .x3_mem_addr1_r              (x3_mem_addr1_r[11:0]),  
  .x3_bank_sel_r               (dc3_bank_sel_r            ),
  .x30_mask_bank0              (dc30_mask_bank0           ), 
  .x30_mask_bank1              (dc30_mask_bank1           ), 
  .x31_mask_bank0              (dc31_mask_bank0           ), 
  .x31_mask_bank1              (dc31_mask_bank1           ), 
  
  .ca_store_r                  (ca_store_r                ), 
  .ca_grad_r                   ((|ca_store_grad_r)        ),
  .ca_mem_addr0_r              (ca_mem_addr0_r[11:0]), 
  .ca_mem_addr1_r              (dc4_mem_addr1_r[11:0]), 
  .ca_bank_sel_r               (ca_data_bank_sel_r        ),
  .ca0_mask_bank0              (dc40_mask_bank0_prel      ),
  .ca0_mask_bank1              (dc40_mask_bank1_prel      ),
  .ca1_mask_bank0              (dc41_mask_bank0_prel      ),
  .ca1_mask_bank1              (dc41_mask_bank1_prel      ),
 
  .wq_recent_wr_r              (wq_recent_wr_r            ), 
  .wq0_valid_r              (wq_valid_r[0]            ),
  .wq0_grad_r               ((|wq0_grad_r)          ),
  .wq0_addr_r               (wq0_addr_r[11:0] ), 
  .wq0_mask_bank0           (wq0_aln_mask_bank0     ),
  .wq0_mask_bank1           (wq0_aln_mask_bank1     ),
  .wq1_valid_r              (wq_valid_r[1]            ),
  .wq1_grad_r               ((|wq1_grad_r)          ),
  .wq1_addr_r               (wq1_addr_r[11:0] ), 
  .wq1_mask_bank0           (wq1_aln_mask_bank0     ),
  .wq1_mask_bank1           (wq1_aln_mask_bank1     ),
  .wq2_valid_r              (wq_valid_r[2]            ),
  .wq2_grad_r               ((|wq2_grad_r)          ),
  .wq2_addr_r               (wq2_addr_r[11:0] ), 
  .wq2_mask_bank0           (wq2_aln_mask_bank0     ),
  .wq2_mask_bank1           (wq2_aln_mask_bank1     ),
  .wq3_valid_r              (wq_valid_r[3]            ),
  .wq3_grad_r               ((|wq3_grad_r)          ),
  .wq3_addr_r               (wq3_addr_r[11:0] ), 
  .wq3_mask_bank0           (wq3_aln_mask_bank0     ),
  .wq3_mask_bank1           (wq3_aln_mask_bank1     ),
  
  .dc2_grad_conflict           (dc2_grad_conflict         ),
  .dc2_partial_match_conflict  (dc2_partial_match_conflict),
  .dc2_multi_match_conflict    (dc2_multi_match_conflict  )

);


//////////////////////////////////////////////////////////////////////////////
//
// DC3 FSM stall 
//
//////////////////////////////////////////////////////////////////////////////
function automatic [3:0] One_hot_func;
input [1:0] wq_dc_rdentry0;
begin
  case (wq_dc_rdentry0)
  2'b00:  One_hot_func = 4'b0001;
  2'b01:  One_hot_func = 4'b0010;
  2'b10:  One_hot_func = 4'b0100;
  default:One_hot_func = 4'b1000;
  endcase
end
endfunction

reg       dc3_stall_nxt;
reg       dc3_stall_next;

reg [2:0] dc3_stall_vector_r;
reg [2:0] dc3_stall_vector_nxt;
reg [2:0] dc3_stall_vector_next;

reg       dc3_stall_state_r;
reg       dc3_stall_state_nxt;
reg       dc3_stall_state_next;

parameter DC3_STALL_DEFAULT  = 1'b0;
parameter DC3_STALL_STALL    = 1'b1;

always @*
begin : dc3_stall_nxt_PROC
  // This is the FSM that stalls LD in DC3 when the addr conflict against
  // downstream stalls can be resolved with forwarding 
  //
  dc3_stall_nxt        = dc3_stall_r;
  dc3_stall_vector_nxt = dc3_stall_vector_r;
  dc3_stall_state_nxt  = dc3_stall_state_r;
  
  
  wq_fwd_replay        = wq_fwd_replay_prel;
  
  case (dc3_stall_state_r)
  DC3_STALL_DEFAULT:
  begin
    
    if (  (  dc2_grad_conflict
           | dc2_partial_match_conflict
           | dc2_multi_match_conflict)
        & x2_pass)   
    begin
      // A DC2 load conflicting with downstream stores
      //
      dc3_stall_nxt        = 1'b1;
      dc3_stall_vector_nxt = {dc2_multi_match_conflict,
                              dc2_partial_match_conflict,
                              dc2_grad_conflict}; 
      dc3_stall_state_nxt  = DC3_STALL_STALL;
    end
  end
  
  default: // DC3_STALL_STALL
  begin
    wq_fwd_replay = 1'b0;
    
    if ( (~dc3_partial_or_multi_conflict)
        | wa_restart_r)    
    begin
      // We are stalling because of conflict with graduating stores. Wait
      // until all stores have graduated and go back to default
      //
      if (  ~dc3_addr_conflict           // we shouldn't have stalled
          | wa_restart_r
          | (  (ca_store_grad_r == 2'b00)
             & (wq0_grad_r == 2'b00)
             & (wq1_grad_r == 2'b00)
             & (wq2_grad_r == 2'b00)
             & (wq3_grad_r == 2'b00)
            )
         ) 
      begin
        dc3_stall_nxt        = 1'b0;
        dc3_stall_vector_nxt = 3'b000;
        dc3_stall_state_nxt  = DC3_STALL_DEFAULT;
      end
    end
    else if (   (~dc3_dc4_conflict)
              & ((dc3_wq_conflict & One_hot_func(wq_dc_rdentry0)) == dc3_wq_conflict)
            )
    begin
      // As soon as the conflicting wq entry is removed from the WQ, we can
      // release the stall
      //
      dc3_stall_nxt        = 1'b0;
      dc3_stall_vector_nxt = 3'b000;
      dc3_stall_state_nxt  = DC3_STALL_DEFAULT;
    end
  end
  endcase
end



//////////////////////////////////////////////////////////////////////////////
// DC3 versus DC4/WQ
//
//////////////////////////////////////////////////////////////////////////////

always @*
begin : dc40_dc41_addr0_addr1_match_PROC
  // Store0 with Load0 match
  //
  dc40_addr0_match   = (   dmp_wq_addr0[`npuarc_PADDR_MSB:4] 
                       == x3_mem_addr0_r[`npuarc_PADDR_MSB:4]);   

  // Store1 with Load0 match
  //
  dc41_addr0_match   = (   dmp_wq_addr1[`npuarc_PADDR_MSB:4] 
                       == x3_mem_addr0_r[`npuarc_PADDR_MSB:4]);   
  
  // Store0 with Load1 match
  //
  dc40_addr1_match   = (   dmp_wq_addr0[`npuarc_PADDR_MSB:4]
                       == x3_mem_addr1_r[`npuarc_PADDR_MSB:4]);   

  // Store1 with Load1 match: 
  // 
  dc41_addr1_match   = (   dmp_wq_addr1[`npuarc_PADDR_MSB:4]
                       == x3_mem_addr1_r[`npuarc_PADDR_MSB:4]);   
  
  dc40_addr0_match_qual =  dc40_addr0_match
                        & ( x3_load_r
                           | (x3_store_r & (|dc3_rmw_r))
                          )
                        & (dc3_target_r == dc4_target_r)
                        & ca_store_r;

  dc41_addr0_match_qual =  dc41_addr0_match
                        & ( x3_load_r
                           | (x3_store_r & (|dc3_rmw_r))
                          )  
                        & (dc3_target_r == dc4_target_r)
                        & ca_store_r
                        & dmp_wq_write1;
  
  dc40_addr1_match_qual =  dc40_addr1_match
                        & ( x3_load_r
                           | (x3_store_r & (|dc3_rmw_r))
                          ) 
                        & (dc3_target_r == dc4_target_r)
                        & dc3_bank_sel_r[3] 
                        & dc3_bank_sel_r[0] 
                        & ca_store_r;
  
  dc41_addr1_match_qual =  dc41_addr1_match
                        & ( x3_load_r
                           | (x3_store_r & (|dc3_rmw_r))
                          ) 
                        & (dc3_target_r == dc4_target_r)
                        & ca_store_r
                        & dc3_bank_sel_r[3] 
                        & dc3_bank_sel_r[0] 
                        & dmp_wq_write1;

  wq0_addr0_match = (  wq0_addr_r[`npuarc_PADDR_MSB:4]
                      == x3_mem_addr0_r[`npuarc_PADDR_MSB:4]);  

  wq0_addr1_match = (  wq0_addr_r[`npuarc_PADDR_MSB:4]
                      == x3_mem_addr1_r[`npuarc_PADDR_MSB:4]);
 
 
  wq0_addr0_match_qual =  wq0_addr0_match
                           & ( x3_load_r
                              | (x3_store_r & (|dc3_rmw_r))
                             )
                           & (dc3_target_r == wq0_target_r)       
                           & wq_valid_r[0];

  wq0_addr1_match_qual =  wq0_addr1_match
                           & ( x3_load_r
                              | (x3_store_r & (|dc3_rmw_r))
                             )
                           & (dc3_target_r == wq0_target_r)       
                           & dc3_bank_sel_r[3] 
                           & dc3_bank_sel_r[0] 
                           & wq_valid_r[0];
                           

  wq1_addr0_match = (  wq1_addr_r[`npuarc_PADDR_MSB:4]
                      == x3_mem_addr0_r[`npuarc_PADDR_MSB:4]);  

  wq1_addr1_match = (  wq1_addr_r[`npuarc_PADDR_MSB:4]
                      == x3_mem_addr1_r[`npuarc_PADDR_MSB:4]);
 
 
  wq1_addr0_match_qual =  wq1_addr0_match
                           & ( x3_load_r
                              | (x3_store_r & (|dc3_rmw_r))
                             )
                           & (dc3_target_r == wq1_target_r)       
                           & wq_valid_r[1];

  wq1_addr1_match_qual =  wq1_addr1_match
                           & ( x3_load_r
                              | (x3_store_r & (|dc3_rmw_r))
                             )
                           & (dc3_target_r == wq1_target_r)       
                           & dc3_bank_sel_r[3] 
                           & dc3_bank_sel_r[0] 
                           & wq_valid_r[1];
                           

  wq2_addr0_match = (  wq2_addr_r[`npuarc_PADDR_MSB:4]
                      == x3_mem_addr0_r[`npuarc_PADDR_MSB:4]);  

  wq2_addr1_match = (  wq2_addr_r[`npuarc_PADDR_MSB:4]
                      == x3_mem_addr1_r[`npuarc_PADDR_MSB:4]);
 
 
  wq2_addr0_match_qual =  wq2_addr0_match
                           & ( x3_load_r
                              | (x3_store_r & (|dc3_rmw_r))
                             )
                           & (dc3_target_r == wq2_target_r)       
                           & wq_valid_r[2];

  wq2_addr1_match_qual =  wq2_addr1_match
                           & ( x3_load_r
                              | (x3_store_r & (|dc3_rmw_r))
                             )
                           & (dc3_target_r == wq2_target_r)       
                           & dc3_bank_sel_r[3] 
                           & dc3_bank_sel_r[0] 
                           & wq_valid_r[2];
                           

  wq3_addr0_match = (  wq3_addr_r[`npuarc_PADDR_MSB:4]
                      == x3_mem_addr0_r[`npuarc_PADDR_MSB:4]);  

  wq3_addr1_match = (  wq3_addr_r[`npuarc_PADDR_MSB:4]
                      == x3_mem_addr1_r[`npuarc_PADDR_MSB:4]);
 
 
  wq3_addr0_match_qual =  wq3_addr0_match
                           & ( x3_load_r
                              | (x3_store_r & (|dc3_rmw_r))
                             )
                           & (dc3_target_r == wq3_target_r)       
                           & wq_valid_r[3];

  wq3_addr1_match_qual =  wq3_addr1_match
                           & ( x3_load_r
                              | (x3_store_r & (|dc3_rmw_r))
                             )
                           & (dc3_target_r == wq3_target_r)       
                           & dc3_bank_sel_r[3] 
                           & dc3_bank_sel_r[0] 
                           & wq_valid_r[3];
                           

end

//////////////////////////////////////////////////////////////////////////////
//
// DC3 conflict consolidation
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_addr_conflict_PROC
  // DC30, DC40
  //
  dc30_dc40_mask_conflict = | (  {dc30_mask_bank1, dc30_mask_bank0}
                               & {dc40_mask_bank1, dc40_mask_bank0})
                          ;
  dc30_dc40_addr_conflict = dc40_addr0_match_qual
                          & dc30_dc40_mask_conflict
                          ;
  // DC30, DC41
  //
  dc30_dc41_mask_conflict = | (  {dc30_mask_bank1, dc30_mask_bank0}
                               & {dc41_mask_bank1, dc41_mask_bank0})
                            ;
  dc30_dc41_addr_conflict = dc41_addr0_match_qual
                          & dc30_dc41_mask_conflict
                          ;
  // DC31, DC40
  //
  dc31_dc40_mask_conflict = | (  {dc31_mask_bank1, dc31_mask_bank0}
                               & {dc40_mask_bank1, dc40_mask_bank0})
                          ;
  dc31_dc40_addr_conflict = dc40_addr1_match_qual
                          & dc31_dc40_mask_conflict
                          ;
  // DC30, WQ
  //
  dc30_wq0_mask_conflict = | (  {dc30_mask_bank1, dc30_mask_bank0}
                                 & {wq0_aln_mask_bank1, wq0_aln_mask_bank0})
                            ;
  dc30_wq0_addr_conflict = wq0_addr0_match_qual
                            & dc30_wq0_mask_conflict
                            ;
   
  // DC31, WQ
  //
  dc31_wq0_mask_conflict = | (  {dc31_mask_bank1, dc31_mask_bank0}
                                 & {wq0_aln_mask_bank1, wq0_aln_mask_bank0})
                            ;
  dc31_wq0_addr_conflict = wq0_addr1_match_qual
                            & dc31_wq0_mask_conflict
                            ;
   
  // DC30, WQ
  //
  dc30_wq1_mask_conflict = | (  {dc30_mask_bank1, dc30_mask_bank0}
                                 & {wq1_aln_mask_bank1, wq1_aln_mask_bank0})
                            ;
  dc30_wq1_addr_conflict = wq1_addr0_match_qual
                            & dc30_wq1_mask_conflict
                            ;
   
  // DC31, WQ
  //
  dc31_wq1_mask_conflict = | (  {dc31_mask_bank1, dc31_mask_bank0}
                                 & {wq1_aln_mask_bank1, wq1_aln_mask_bank0})
                            ;
  dc31_wq1_addr_conflict = wq1_addr1_match_qual
                            & dc31_wq1_mask_conflict
                            ;
   
  // DC30, WQ
  //
  dc30_wq2_mask_conflict = | (  {dc30_mask_bank1, dc30_mask_bank0}
                                 & {wq2_aln_mask_bank1, wq2_aln_mask_bank0})
                            ;
  dc30_wq2_addr_conflict = wq2_addr0_match_qual
                            & dc30_wq2_mask_conflict
                            ;
   
  // DC31, WQ
  //
  dc31_wq2_mask_conflict = | (  {dc31_mask_bank1, dc31_mask_bank0}
                                 & {wq2_aln_mask_bank1, wq2_aln_mask_bank0})
                            ;
  dc31_wq2_addr_conflict = wq2_addr1_match_qual
                            & dc31_wq2_mask_conflict
                            ;
   
  // DC30, WQ
  //
  dc30_wq3_mask_conflict = | (  {dc30_mask_bank1, dc30_mask_bank0}
                                 & {wq3_aln_mask_bank1, wq3_aln_mask_bank0})
                            ;
  dc30_wq3_addr_conflict = wq3_addr0_match_qual
                            & dc30_wq3_mask_conflict
                            ;
   
  // DC31, WQ
  //
  dc31_wq3_mask_conflict = | (  {dc31_mask_bank1, dc31_mask_bank0}
                                 & {wq3_aln_mask_bank1, wq3_aln_mask_bank0})
                            ;
  dc31_wq3_addr_conflict = wq3_addr1_match_qual
                            & dc31_wq3_mask_conflict
                            ;
   
  
  // Putting it all together
  //
  dc3_dc4_conflict  = dc30_dc40_addr_conflict
                    | dc31_dc40_addr_conflict
                    | dc30_dc41_addr_conflict
                    ;
                    
  dc3_addr_conflict = dc3_dc4_conflict
                    | dc30_wq0_addr_conflict
                    | dc31_wq0_addr_conflict
                    | dc30_wq1_addr_conflict
                    | dc31_wq1_addr_conflict
                    | dc30_wq2_addr_conflict
                    | dc31_wq2_addr_conflict
                    | dc30_wq3_addr_conflict
                    | dc31_wq3_addr_conflict
                    ;
                    
  dc3_partial_or_multi_conflict =  wq_fwd_replay_prel;                   
end

//////////////////////////////////////////////////////////////////////////////
// Set-up a conflict vector between DC3 and WQ
//
//////////////////////////////////////////////////////////////////////////////
task automatic wq_conflict;
  output [3:0] conflict;
  
  input        wq0_addr_conflict;
  input        wq1_addr_conflict;
  input        wq2_addr_conflict;
  input        wq3_addr_conflict;

  input [15:0] dc3_byte_mask; 
  input [15:0] wq0_byte_mask;  
  input [15:0] wq1_byte_mask;  
  input [15:0] wq2_byte_mask;  
  input [15:0] wq3_byte_mask;  
  
  reg [3:0]    mask_match;
  
  begin  
    mask_match[0] = | (dc3_byte_mask & wq0_byte_mask);
    mask_match[1] = | (dc3_byte_mask & wq1_byte_mask);
    mask_match[2] = | (dc3_byte_mask & wq2_byte_mask);
    mask_match[3] = | (dc3_byte_mask & wq3_byte_mask);

    conflict[0] = wq0_addr_conflict & mask_match[0]; 
    conflict[1] = wq1_addr_conflict & mask_match[1]; 
    conflict[2] = wq2_addr_conflict & mask_match[2]; 
    conflict[3] = wq3_addr_conflict & mask_match[3]; 
  end  
endtask

reg [3:0]   dc30_wq_conflict;
reg [3:0]   dc31_wq_conflict;
        
always @*
begin : dc3_wq_conflict_PROC
  // Create a conflict vector between DC3 and WQ
  //
  wq_conflict(dc30_wq_conflict, 
  
              wq0_addr0_match_qual,
              wq1_addr0_match_qual,
              wq2_addr0_match_qual,
              wq3_addr0_match_qual,
            
              {dc30_mask_bank1, dc30_mask_bank0},
              {wq0_aln_mask_bank1, wq0_aln_mask_bank0},
              {wq1_aln_mask_bank1, wq1_aln_mask_bank0},
              {wq2_aln_mask_bank1, wq2_aln_mask_bank0},
              {wq3_aln_mask_bank1, wq3_aln_mask_bank0}
            );
  
  wq_conflict(dc31_wq_conflict, 
             
              wq0_addr1_match_qual,
              wq1_addr1_match_qual,
              wq2_addr1_match_qual,
              wq3_addr1_match_qual,
              
              {8'd0, dc31_mask_bank0},
              {wq0_aln_mask_bank1, wq0_aln_mask_bank0},
              {wq1_aln_mask_bank1, wq1_aln_mask_bank0},
              {wq2_aln_mask_bank1, wq2_aln_mask_bank0},
              {wq3_aln_mask_bank1, wq3_aln_mask_bank0}
              );
  
  // The 4-bit dc3_wq_conflict vector indicates the WQ entries that conflict with
  // the DC3 load
  //
  dc3_wq_conflict = dc30_wq_conflict 
                  | dc31_wq_conflict
                  ;
end


//////////////////////////////////////////////////////////////////////////////
// Set-up a dc3 raw hazard.
//
//////////////////////////////////////////////////////////////////////////////
reg                    dc3_target_dc;

reg [`npuarc_DMP_FIFO_RANGE]  dc3_ca_raw_hazard_entries;

reg [`npuarc_DMP_FIFO_RANGE]  dc3_wq_raw_hazard_entries;

reg [`npuarc_DMP_FIFO_RANGE]  dc3_raw_hazard_entries_prel;
reg [`npuarc_DMP_FIFO_RANGE]  dc3_raw_hazard_entries;

reg                    dc4_setup_raw_hazard_cg0;

always @*
begin : dc3_raw_hazard_PROC
  // DC3 target
  //
  dc3_target_dc  =   (dc3_target_r == `npuarc_DMP_TARGET_DC)
                   | (dc3_target_r == `npuarc_DMP_TARGET_DCCM);
                   
  // RAW hazard involving a X3 load and a CA store.  
  //
  dc3_ca_raw_hazard =   (dc3_target_dc == 1'b0)
                      & (  dc40_addr0_match_qual
                         | dc40_addr1_match_qual
                         | dc41_addr0_match_qual);
                 
  // This vector registers the WQ entries that the load *will* be dependent upon. 
  // This strict hazard can not be resolved in CA as this store can't be put 
  // into the WQ and retired the same time
  //
  dc3_ca_raw_hazard_entries              =  {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  dc3_ca_raw_hazard_entries[wq_wrentry0] = dc3_ca_raw_hazard;

  // In case the CA store takes two entries in the WQ, make sure there is a raw hazard
  // against that entry
  //
  if (dmp_wq_write1)
  begin
    dc3_ca_raw_hazard_entries[wq_wrentry1] = dc3_ca_raw_hazard;
  end 
  
  // This vector register the WQ entries that the load *is*  dependent upon. 
  //
  dc3_wq_raw_hazard_entries[0] =   wq0_addr0_match_qual
                                  | wq0_addr1_match_qual 
                                  | wq0_addr0_match_qual;
                                  
  dc3_wq_raw_hazard_entries[1] =   wq1_addr0_match_qual
                                  | wq1_addr1_match_qual 
                                  | wq1_addr0_match_qual;
                                  
  dc3_wq_raw_hazard_entries[2] =   wq2_addr0_match_qual
                                  | wq2_addr1_match_qual 
                                  | wq2_addr0_match_qual;
                                  
  dc3_wq_raw_hazard_entries[3] =   wq3_addr0_match_qual
                                  | wq3_addr1_match_qual 
                                  | wq3_addr0_match_qual;
                                  
  
  // Create a single hazard vector. RAW dependendencies against stores in CA
  // and in the WQ
  //
  dc3_raw_hazard_entries_prel =   dc3_ca_raw_hazard_entries
                                | dc3_wq_raw_hazard_entries;
  
  // Exclude from this vector any entry that is retiring while the dependent
  // LD is in X3
  //
  dc3_raw_hazard_entries      = dc3_raw_hazard_entries_prel;
  
  if (wq_mem_retire)
  begin
    // Store to external memory retiring while the dependent load is in X3
    //
    dc3_raw_hazard_entries[wq_mem_entry_id] = 1'b0;
  end
  
  

 
  // Clock gate
  //
  dc4_setup_raw_hazard_cg0 = x3_load_r & x3_pass;
end

//////////////////////////////////////////////////////////////////////////////
// Set-up a CA RAW hazard
//
//////////////////////////////////////////////////////////////////////////////
reg                   dc4_update_raw_hazard_cg0;
reg [`npuarc_DMP_FIFO_RANGE] dc4_raw_hazard_entries_prel_r;
reg [`npuarc_DMP_FIFO_RANGE] dc4_raw_hazard_entries_prel_nxt;

reg [`npuarc_DMP_FIFO_RANGE] dc4_raw_hazard_entries;

always @*
begin : dc4_raw_hazard_PROC
  // This is the RAW entries between a CA load and the WQ. By default, assign to
  // the entries we set-up while the load was in X3.This default value needs to be
  // updated whenever the WQ retires an entry. 
  //
  dc4_raw_hazard_entries_prel_nxt = dc4_raw_hazard_entries_prel_r;
  dc4_raw_hazard_entries          = dc4_raw_hazard_entries_prel_r;
  
  dc4_update_raw_hazard_cg0       = 1'b0;
  
  // Exclude from this vector any WQ entry that is retiring while the LD is in
  // CA
  //
  if (wq_mem_retire)
  begin
    // Store to external memory retiring while the dependent load is in CA
    //
    dc4_update_raw_hazard_cg0                         = 1'b1;
    dc4_raw_hazard_entries_prel_nxt[wq_mem_entry_id]  = 1'b0;
    dc4_raw_hazard_entries[wq_mem_entry_id]           = 1'b0;
  end
  
  


  // We have a RAW hazard when the CA load depenends on *any* entry of the WQ
  //
  dc4_raw_hazard = | dc4_raw_hazard_entries;  
end

//////////////////////////////////////////////////////////////////////////////
// wq_order_ptr_1h is a vector that points to the most recent external entry 
// written in the WQ. It is used to ensure we send the IBP commands 
// in order to external targets. It is also used to ensure serialization of
// volatile reads 
//
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DMP_FIFO_RANGE] wq_maintain_order;
always @*
begin : wq_order_ptr_1h_PROC
  
  // We need to maintain ordering for strict volatile writes or for writes 
  // that are not out on the bus yet
  //
  wq_maintain_order =   (wq_valid_r & wq_strict_order_r)
                      | (~wq_out_r);
  
  // The order is only relevant for external  targets that are not yet out
  // on the IBP bus. We need to guarantee  ordering when there is an explicit 
  // RAW hazard.
  //
  wq_order_ptr_1h =  (  wq_external_entries 
                      & wq_maintain_order)
                   | dc4_raw_hazard_entries;
end




//////////////////////////////////////////////////////////////////////////////
// FWD info
//
//////////////////////////////////////////////////////////////////////////////

always @*
begin : wq_fwd_bank_PROC
  // This is a four bit vector that controls the fwd to the 4 different
  // banks. Convention: enable0 is for load0 and enable1 id for load1 
  // (unaligned)
  //
  wq_fwd_bank   = {fwd_enable0_bank1_hi, 
                   fwd_enable0_bank1_lo,
                   (fwd_enable0_bank0_hi | fwd_enable1_bank0_hi),
                   (fwd_enable0_bank0_lo | fwd_enable1_bank0_lo)};

  // We replay when any of the four banks find a replay condition
  //
  wq_fwd_replay_prel =   replay0_bank0_lo
                       | replay1_bank0_lo  
                       | replay0_bank0_hi  
                       | replay1_bank0_hi  
                       | replay0_bank1_lo  
                       | replay0_bank1_hi; 
  
end

//////////////////////////////////////////////////////////////////////////////
// RAW hazard 
//
//////////////////////////////////////////////////////////////////////////////

reg wq_partial_fwd;
reg wq_any_fwd;

always @*
begin : wq_fwd_PROC
  // This is set when there is any match against DC4/WQ
  //
  wq_any_fwd     = (| wq_fwd_bank);
  
  // A partial fwd happens when not all the load data comes from the fwd source
  //
  wq_partial_fwd =   (dc3_bank_sel_r != wq_fwd_bank)
                   & (| wq_fwd_bank);
  
  // A full fwd happens when we service the entire load from DC4/WQ forwarding
  //
  wq_full_fwd    = (dc3_bank_sel_r == wq_fwd_bank);
  

  // We request the result bus for an external load getting its result from the
  // forward path. This signal is used to prevent the graduation of this load.
  //
  dc3_fwd_req    =   wq_full_fwd
                   & (~wq_fwd_replay_prel)
                   & (~dc3_target_dc)
                   & dc3_fwd_allowed_r
                   & (~dc4_ecc_sb_error_r)
                   ;
end

//////////////////////////////////////////////////////////////////////////////
//  WQ strict ordering
//
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DMP_FIFO_RANGE] wq_strict_order;
always @*
begin : wq_strict_order_PROC
  // A write queue entry being written is strictly ordered when the CA store
  // carries a war hazard dependency against the LQ 
  // A further condition for strict ordering is the strict order attribute bit
  // of the AUX_VOLATILE register
  //
  wq_strict_order[0] =  wq_strict_order_r[0]
                      | (  (dc4_war_hazard | ca_strict_order_r)
                         & (wq_valid_r[0] == 1'b0)
                         & (wq_wrentry0 == 2'd0))
                      | (  (dc4_war_hazard | ca_strict_order_r)
                         & dmp_wq_write1 
                         & (wq_valid_r[0] == 1'b0)
                         & (wq_wrentry1 == 2'd0));
                         
  wq_strict_order[1] =  wq_strict_order_r[1]
                      | (  (dc4_war_hazard | ca_strict_order_r)
                         & (wq_valid_r[1] == 1'b0)
                         & (wq_wrentry0 == 2'd1))
                      | (  (dc4_war_hazard | ca_strict_order_r)
                         & dmp_wq_write1 
                         & (wq_valid_r[1] == 1'b0)
                         & (wq_wrentry1 == 2'd1));
                         
  wq_strict_order[2] =  wq_strict_order_r[2]
                      | (  (dc4_war_hazard | ca_strict_order_r)
                         & (wq_valid_r[2] == 1'b0)
                         & (wq_wrentry0 == 2'd2))
                      | (  (dc4_war_hazard | ca_strict_order_r)
                         & dmp_wq_write1 
                         & (wq_valid_r[2] == 1'b0)
                         & (wq_wrentry1 == 2'd2));
                         
  wq_strict_order[3] =  wq_strict_order_r[3]
                      | (  (dc4_war_hazard | ca_strict_order_r)
                         & (wq_valid_r[3] == 1'b0)
                         & (wq_wrentry0 == 2'd3))
                      | (  (dc4_war_hazard | ca_strict_order_r)
                         & dmp_wq_write1 
                         & (wq_valid_r[3] == 1'b0)
                         & (wq_wrentry1 == 2'd3));
                         
end

//////////////////////////////////////////////////////////////////////////////
// FIFO status
//
//////////////////////////////////////////////////////////////////////////////
reg  wq_one_valid;
reg  wq_two_valid;
reg  wq_three_valid;
reg  wq_full;

always @*
begin : wq_empty_PROC
  casez (wq_valid_r)
  4'b0001: wq_one_valid   = 1'b1;
  4'b0010: wq_one_valid   = 1'b1;
  4'b0100: wq_one_valid   = 1'b1;
  4'b1000: wq_one_valid   = 1'b1; 
  default: wq_one_valid   = 1'b0; 
  endcase  
  
  casez (wq_valid_r)
  4'b0011: wq_two_valid   = 1'b1;
  4'b0101: wq_two_valid   = 1'b1;
  4'b1001: wq_two_valid   = 1'b1;
  4'b0110: wq_two_valid   = 1'b1;
  4'b1010: wq_two_valid   = 1'b1;
  4'b1100: wq_two_valid   = 1'b1;
  default: wq_two_valid   = 1'b0; 
  endcase  
  
  casez (~wq_valid_r)
  4'b0001: wq_three_valid   = 1'b1;
  4'b0010: wq_three_valid   = 1'b1;
  4'b0100: wq_three_valid   = 1'b1;
  4'b1000: wq_three_valid   = 1'b1; 
  default: wq_three_valid   = 1'b0; 
  endcase 
  
  wq_full = &(wq_valid_r);
end


//////////////////////////////////////////////////////////////////////////////
// Graduating store alignement
//
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_dmp_grad_store_aligner u_alb_dmp_grad_store_aligner_w0_0 (
  .ecc_dmp_disable         (ecc_dmp_disable            ),
  .addr_r                  (wq0_ecc_addr_r          ),
  .wq_ecc_mask_r           (wq0_ecc_mask_r          ),
  .wq_store_grad_match0_lo (1'b0                       ),
  .wq_store_grad_match0_hi (1'b0                       ),
  .wq_store_grad_match1_lo (wq0_store_grad_match1_lo),
  .wq_store_grad_match1_hi (wq0_store_grad_match1_hi),
 
  .wq_grad_r               (wq0_grad_r              ),
  .wq_grad_data_src_r      (wq0_grad_data_src_r     ),
  .wq_data_mask_r          (wq0_data_mask_r         ), 
  .wq_data_r               (wq0_data_r              ),
  .wa_retire0_data         (wa_retire1_data            ),
  .wa_retire1_data         (wa_retire1_data            ),
  .wq_grad_prel            (wq0_grad_prel           ),
  .wq_wr_data              (wq0_wr_data0            )
  );  
npuarc_alb_dmp_grad_store_aligner u_alb_dmp_grad_store_aligner_w0_1 (
  .ecc_dmp_disable         (ecc_dmp_disable            ),
  .addr_r                  (wq1_ecc_addr_r          ),
  .wq_ecc_mask_r           (wq1_ecc_mask_r          ),
  .wq_store_grad_match0_lo (1'b0                       ),
  .wq_store_grad_match0_hi (1'b0                       ),
  .wq_store_grad_match1_lo (wq1_store_grad_match1_lo),
  .wq_store_grad_match1_hi (wq1_store_grad_match1_hi),
 
  .wq_grad_r               (wq1_grad_r              ),
  .wq_grad_data_src_r      (wq1_grad_data_src_r     ),
  .wq_data_mask_r          (wq1_data_mask_r         ), 
  .wq_data_r               (wq1_data_r              ),
  .wa_retire0_data         (wa_retire1_data            ),
  .wa_retire1_data         (wa_retire1_data            ),
  .wq_grad_prel            (wq1_grad_prel           ),
  .wq_wr_data              (wq1_wr_data0            )
  );  
npuarc_alb_dmp_grad_store_aligner u_alb_dmp_grad_store_aligner_w0_2 (
  .ecc_dmp_disable         (ecc_dmp_disable            ),
  .addr_r                  (wq2_ecc_addr_r          ),
  .wq_ecc_mask_r           (wq2_ecc_mask_r          ),
  .wq_store_grad_match0_lo (1'b0                       ),
  .wq_store_grad_match0_hi (1'b0                       ),
  .wq_store_grad_match1_lo (wq2_store_grad_match1_lo),
  .wq_store_grad_match1_hi (wq2_store_grad_match1_hi),
 
  .wq_grad_r               (wq2_grad_r              ),
  .wq_grad_data_src_r      (wq2_grad_data_src_r     ),
  .wq_data_mask_r          (wq2_data_mask_r         ), 
  .wq_data_r               (wq2_data_r              ),
  .wa_retire0_data         (wa_retire1_data            ),
  .wa_retire1_data         (wa_retire1_data            ),
  .wq_grad_prel            (wq2_grad_prel           ),
  .wq_wr_data              (wq2_wr_data0            )
  );  
npuarc_alb_dmp_grad_store_aligner u_alb_dmp_grad_store_aligner_w0_3 (
  .ecc_dmp_disable         (ecc_dmp_disable            ),
  .addr_r                  (wq3_ecc_addr_r          ),
  .wq_ecc_mask_r           (wq3_ecc_mask_r          ),
  .wq_store_grad_match0_lo (1'b0                       ),
  .wq_store_grad_match0_hi (1'b0                       ),
  .wq_store_grad_match1_lo (wq3_store_grad_match1_lo),
  .wq_store_grad_match1_hi (wq3_store_grad_match1_hi),
 
  .wq_grad_r               (wq3_grad_r              ),
  .wq_grad_data_src_r      (wq3_grad_data_src_r     ),
  .wq_data_mask_r          (wq3_data_mask_r         ), 
  .wq_data_r               (wq3_data_r              ),
  .wa_retire0_data         (wa_retire1_data            ),
  .wa_retire1_data         (wa_retire1_data            ),
  .wq_grad_prel            (wq3_grad_prel           ),
  .wq_wr_data              (wq3_wr_data0            )
  );  

//////////////////////////////////////////////////////////////////////////////
//
// Store graduation tag match
//
/////////////////////////////////////////////////////////////////////////////

always @*
begin : wq_store_grad_match1_PROC
  //
  // Channel 1
  //
  // Tag_lo
  wq0_store_grad_match1_lo = wq_valid_r[0]                       // Valid WQ entry
                              & wq0_grad_r[0]                     // WQ Entry has a grad bit set
                              & wa_retire1_valid                     // WA1 retirement is valid
                              & (wq0_grad_tag_lo_r == wa_retire1_tag)// WA1 retirement TAG
                              ;
  // Tag_hi
  wq0_store_grad_match1_hi = wq_valid_r[0]                       // Valid WQ entry
                              & wq0_grad_r[1]                     // WQ Entry has a grad bit set
                              & wa_retire1_valid                     // WA1 retirement is valid
                              & (wq0_grad_tag_hi_r == wa_retire1_tag)// WA1 retirement TAG
                              ; 

  // Garbage data
   wq0_store_grad_match1_lo_garbage = wq0_store_grad_match1_lo  // match entry
                                       & wa_retire1_garbage           // WA1 retirement is garbage
                                       ;
          
  wq0_store_grad_match1_hi_garbage = wq0_store_grad_match1_hi  // match entry
                                      & wa_retire1_garbage           // WA1 retirement is garbage
                                      ;
  // Tag_lo
  wq1_store_grad_match1_lo = wq_valid_r[1]                       // Valid WQ entry
                              & wq1_grad_r[0]                     // WQ Entry has a grad bit set
                              & wa_retire1_valid                     // WA1 retirement is valid
                              & (wq1_grad_tag_lo_r == wa_retire1_tag)// WA1 retirement TAG
                              ;
  // Tag_hi
  wq1_store_grad_match1_hi = wq_valid_r[1]                       // Valid WQ entry
                              & wq1_grad_r[1]                     // WQ Entry has a grad bit set
                              & wa_retire1_valid                     // WA1 retirement is valid
                              & (wq1_grad_tag_hi_r == wa_retire1_tag)// WA1 retirement TAG
                              ; 

  // Garbage data
   wq1_store_grad_match1_lo_garbage = wq1_store_grad_match1_lo  // match entry
                                       & wa_retire1_garbage           // WA1 retirement is garbage
                                       ;
          
  wq1_store_grad_match1_hi_garbage = wq1_store_grad_match1_hi  // match entry
                                      & wa_retire1_garbage           // WA1 retirement is garbage
                                      ;
  // Tag_lo
  wq2_store_grad_match1_lo = wq_valid_r[2]                       // Valid WQ entry
                              & wq2_grad_r[0]                     // WQ Entry has a grad bit set
                              & wa_retire1_valid                     // WA1 retirement is valid
                              & (wq2_grad_tag_lo_r == wa_retire1_tag)// WA1 retirement TAG
                              ;
  // Tag_hi
  wq2_store_grad_match1_hi = wq_valid_r[2]                       // Valid WQ entry
                              & wq2_grad_r[1]                     // WQ Entry has a grad bit set
                              & wa_retire1_valid                     // WA1 retirement is valid
                              & (wq2_grad_tag_hi_r == wa_retire1_tag)// WA1 retirement TAG
                              ; 

  // Garbage data
   wq2_store_grad_match1_lo_garbage = wq2_store_grad_match1_lo  // match entry
                                       & wa_retire1_garbage           // WA1 retirement is garbage
                                       ;
          
  wq2_store_grad_match1_hi_garbage = wq2_store_grad_match1_hi  // match entry
                                      & wa_retire1_garbage           // WA1 retirement is garbage
                                      ;
  // Tag_lo
  wq3_store_grad_match1_lo = wq_valid_r[3]                       // Valid WQ entry
                              & wq3_grad_r[0]                     // WQ Entry has a grad bit set
                              & wa_retire1_valid                     // WA1 retirement is valid
                              & (wq3_grad_tag_lo_r == wa_retire1_tag)// WA1 retirement TAG
                              ;
  // Tag_hi
  wq3_store_grad_match1_hi = wq_valid_r[3]                       // Valid WQ entry
                              & wq3_grad_r[1]                     // WQ Entry has a grad bit set
                              & wa_retire1_valid                     // WA1 retirement is valid
                              & (wq3_grad_tag_hi_r == wa_retire1_tag)// WA1 retirement TAG
                              ; 

  // Garbage data
   wq3_store_grad_match1_lo_garbage = wq3_store_grad_match1_lo  // match entry
                                       & wa_retire1_garbage           // WA1 retirement is garbage
                                       ;
          
  wq3_store_grad_match1_hi_garbage = wq3_store_grad_match1_hi  // match entry
                                      & wa_retire1_garbage           // WA1 retirement is garbage
                                      ;
end



always @*
begin : dmp_st_retire0_data_PROC 
  //
  // extract the data based on tag
  //
  case (dmp_st_retire0_tag_r)
  2'b00: dmp_st_retire0_data_r =  wq0_rtt_grad_data_r;
  2'b01: dmp_st_retire0_data_r =  wq1_rtt_grad_data_r;
  2'b10: dmp_st_retire0_data_r =  wq2_rtt_grad_data_r;
  2'b11: dmp_st_retire0_data_r =  wq3_rtt_grad_data_r;
  default: dmp_st_retire0_data_r = wq0_rtt_grad_data_r;
  endcase
end  

always @*
begin : dmp_st_retire1_data_PROC 
  //
  // extract the data based on tag
  //
  case (dmp_st_retire1_tag_r)
  2'b00: dmp_st_retire1_data_r =  wq0_rtt_grad_data_r;
  2'b01: dmp_st_retire1_data_r =  wq1_rtt_grad_data_r;
  2'b10: dmp_st_retire1_data_r =  wq2_rtt_grad_data_r;
  2'b11: dmp_st_retire1_data_r =  wq3_rtt_grad_data_r;
  default: dmp_st_retire1_data_r = wq0_rtt_grad_data_r;
  endcase
end  


  // MSB

  // MSB


always @*
begin : wq0_rtt_grad_data_nxt_PROC
  //
  // update the rtt data based on grad match
  //
  wq0_rtt_grad_data_nxt = wq0_rtt_grad_data_r;

  case (wq0_grad_r)
  2'b01: 
  begin
    //
    //
    if (wq0_store_grad_match1)
    begin
      //
      // 
      wq0_rtt_grad_data_nxt[31:0] = wq0_grad_data_src_r[0] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
  2'b10:
  begin
    //
    //
    if (wq0_store_grad_match1)
    begin
      //
      //
      wq0_rtt_grad_data_nxt[`npuarc_DBL_HI_RANGE] = wq0_grad_data_src_r[1] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
  2'b11:
  begin
    //
    //
    if (wq0_store_grad_match1)
    begin
      //
      //
      if (wq0_store_grad_match1_lo)
        wq0_rtt_grad_data_nxt[31:0]  = wq0_grad_data_src_r[0] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];

      if (wq0_store_grad_match1_hi)
        wq0_rtt_grad_data_nxt[`npuarc_DBL_HI_RANGE] = wq0_grad_data_src_r[1] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default: ;
// spyglass enable_block W193
  endcase
end
always @*
begin : wq1_rtt_grad_data_nxt_PROC
  //
  // update the rtt data based on grad match
  //
  wq1_rtt_grad_data_nxt = wq1_rtt_grad_data_r;

  case (wq1_grad_r)
  2'b01: 
  begin
    //
    //
    if (wq1_store_grad_match1)
    begin
      //
      // 
      wq1_rtt_grad_data_nxt[31:0] = wq1_grad_data_src_r[0] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
  2'b10:
  begin
    //
    //
    if (wq1_store_grad_match1)
    begin
      //
      //
      wq1_rtt_grad_data_nxt[`npuarc_DBL_HI_RANGE] = wq1_grad_data_src_r[1] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
  2'b11:
  begin
    //
    //
    if (wq1_store_grad_match1)
    begin
      //
      //
      if (wq1_store_grad_match1_lo)
        wq1_rtt_grad_data_nxt[31:0]  = wq1_grad_data_src_r[0] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];

      if (wq1_store_grad_match1_hi)
        wq1_rtt_grad_data_nxt[`npuarc_DBL_HI_RANGE] = wq1_grad_data_src_r[1] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default: ;
// spyglass enable_block W193
  endcase
end
always @*
begin : wq2_rtt_grad_data_nxt_PROC
  //
  // update the rtt data based on grad match
  //
  wq2_rtt_grad_data_nxt = wq2_rtt_grad_data_r;

  case (wq2_grad_r)
  2'b01: 
  begin
    //
    //
    if (wq2_store_grad_match1)
    begin
      //
      // 
      wq2_rtt_grad_data_nxt[31:0] = wq2_grad_data_src_r[0] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
  2'b10:
  begin
    //
    //
    if (wq2_store_grad_match1)
    begin
      //
      //
      wq2_rtt_grad_data_nxt[`npuarc_DBL_HI_RANGE] = wq2_grad_data_src_r[1] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
  2'b11:
  begin
    //
    //
    if (wq2_store_grad_match1)
    begin
      //
      //
      if (wq2_store_grad_match1_lo)
        wq2_rtt_grad_data_nxt[31:0]  = wq2_grad_data_src_r[0] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];

      if (wq2_store_grad_match1_hi)
        wq2_rtt_grad_data_nxt[`npuarc_DBL_HI_RANGE] = wq2_grad_data_src_r[1] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default: ;
// spyglass enable_block W193
  endcase
end
always @*
begin : wq3_rtt_grad_data_nxt_PROC
  //
  // update the rtt data based on grad match
  //
  wq3_rtt_grad_data_nxt = wq3_rtt_grad_data_r;

  case (wq3_grad_r)
  2'b01: 
  begin
    //
    //
    if (wq3_store_grad_match1)
    begin
      //
      // 
      wq3_rtt_grad_data_nxt[31:0] = wq3_grad_data_src_r[0] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
  2'b10:
  begin
    //
    //
    if (wq3_store_grad_match1)
    begin
      //
      //
      wq3_rtt_grad_data_nxt[`npuarc_DBL_HI_RANGE] = wq3_grad_data_src_r[1] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
  2'b11:
  begin
    //
    //
    if (wq3_store_grad_match1)
    begin
      //
      //
      if (wq3_store_grad_match1_lo)
        wq3_rtt_grad_data_nxt[31:0]  = wq3_grad_data_src_r[0] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];

      if (wq3_store_grad_match1_hi)
        wq3_rtt_grad_data_nxt[`npuarc_DBL_HI_RANGE] = wq3_grad_data_src_r[1] ? wa_retire1_data[`npuarc_DBL_HI_RANGE] : wa_retire1_data[31:0];
    end
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default: ;
// spyglass enable_block W193
  endcase
end


///////////////////////////////////////////////////////////////////////////////
//
// Garbage entry identification: In case of retirement of a LD/ST graduation with an error
//
///////////////////////////////////////////////////////////////////////////////

//  There are 3 ways under which we should set the garbage bit of a WQ entry:
//  Graduated store receiving garbage retirement: wq_grad_garbage
//  Strict-ordered store released by a LD retiring with an error: wq_strict_garbage
//  Genuine store with a store ordering dependency on a previous garbage store: wq_order_garbage

always @*
begin : wq_garbage_PROC
  // Default value
  //
  wq_grad_garbage   = {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  wq_strict_garbage = {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  
  // Graduated entry receives garbage data
  //
  wq_grad_garbage[0] = ~wq_garbage_r[0]
                     & (
                          1'b0
                        | wq0_store_grad_match1_garbage); // WQ0 has a match with retirement 0/1 interface
     
  wq_grad_garbage[1] = ~wq_garbage_r[1]
                     & ( 
                          1'b0
                        | wq1_store_grad_match1_garbage); // WQ1 has a match with retirement 0/1 interface
     
  wq_grad_garbage[2] = ~wq_garbage_r[2]
                     & (
                          1'b0
                        | wq2_store_grad_match1_garbage); // WQ2 has a match with retirement 0/1 interface
     
  wq_grad_garbage[3] = ~wq_garbage_r[3]
                     & (
                          1'b0
                        | wq3_store_grad_match1_garbage); // WQ3 has a match with retirement 0/1 interface
  
  // Helpers
  //
  lq_retire_error[0] = lq_data_retire & lq_data_err & (lq_data_rd_ptr == 2'b00); // LQ0 retires with error
  lq_retire_error[1] = lq_data_retire & lq_data_err & (lq_data_rd_ptr == 2'b01); // LQ1 retires with error
  lq_retire_error[2] = lq_data_retire & lq_data_err & (lq_data_rd_ptr == 2'b10); // LQ2 retires with error
  lq_retire_error[3] = lq_data_retire & lq_data_err & (lq_data_rd_ptr == 2'b11); // LQ3 retires with error
  
  // Strict-ordered entry depends upon load retiring with garbage data
  //
  wq_strict_garbage[0] = wq_strict_order_r[0] 
                       & (  (wq0_lq_dep_r[0] & lq_retire_error[0])
                          | (wq0_lq_dep_r[1] & lq_retire_error[1])
                          | (wq0_lq_dep_r[2] & lq_retire_error[2])
                          | (wq0_lq_dep_r[3] & lq_retire_error[3])
                          );
                          
  wq_strict_garbage[1] = wq_strict_order_r[1] 
                       & (  (wq1_lq_dep_r[0] & lq_retire_error[0])
                          | (wq1_lq_dep_r[1] & lq_retire_error[1])
                          | (wq1_lq_dep_r[2] & lq_retire_error[2])
                          | (wq1_lq_dep_r[3] & lq_retire_error[3])
                          );
                          
  wq_strict_garbage[2] = wq_strict_order_r[2] 
                       & (  (wq2_lq_dep_r[0] & lq_retire_error[0])
                          | (wq2_lq_dep_r[1] & lq_retire_error[1])
                          | (wq2_lq_dep_r[2] & lq_retire_error[2])
                          | (wq2_lq_dep_r[3] & lq_retire_error[3])
                          );
                          
  wq_strict_garbage[3] = wq_strict_order_r[3] 
                       & (  (wq3_lq_dep_r[0] & lq_retire_error[0])
                          | (wq3_lq_dep_r[1] & lq_retire_error[1])
                          | (wq3_lq_dep_r[2] & lq_retire_error[2])
                          | (wq3_lq_dep_r[3] & lq_retire_error[3])
                          );
                          

  // store ordering matrix setting garbage bit
  //
  wq_order_garbage[0] =  ~wq_garbage_r[0]
                      & (  (wq0_dep_r[1] & wq_garbage_r[1])
                         | (wq0_dep_r[2] & wq_garbage_r[2])
                         | (wq0_dep_r[3] & wq_garbage_r[3])
                        );
  
  wq_order_garbage[1] = ~wq_garbage_r[1]
                      & (  (wq1_dep_r[0] & wq_garbage_r[0])
                         | (wq1_dep_r[2] & wq_garbage_r[2])
                         | (wq1_dep_r[3] & wq_garbage_r[3])
                        );
  
  wq_order_garbage[2] = ~wq_garbage_r[2]
                      & (  (wq2_dep_r[0] & wq_garbage_r[0])
                         | (wq2_dep_r[1] & wq_garbage_r[1])
                         | (wq2_dep_r[3] & wq_garbage_r[3])
                        );
  
  wq_order_garbage[3] = ~wq_garbage_r[3]
                      & (  (wq3_dep_r[0] & wq_garbage_r[0])
                         | (wq3_dep_r[1] & wq_garbage_r[1])
                         | (wq3_dep_r[2] & wq_garbage_r[2])
                        );


  // Combine both source of garbage data
  //
  wq_set_garbage = wq_grad_garbage | wq_strict_garbage | wq_order_garbage;
  
end

//////////////////////////////////////////////////////////////////////////////
// Synchronous process
//
//////////////////////////////////////////////////////////////////////////////
assign wq_merge_state_next =
                        wq_merge_state_nxt;

always @(posedge clk or posedge rst_a)
begin : wq_merge_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_merge_state_r <= WQ_NOT_MERGING;
  end
  else
  begin
    wq_merge_state_r <= wq_merge_state_next;
  end
end

always @(posedge clk or posedge rst_a)
begin : wq_merge_addr_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_merge_addr_r <= {`npuarc_PADDR_SIZE{1'b0}};
  end
  else if (wq_merge_addr_cg0)
  begin
    wq_merge_addr_r <= wq_merge_addr_nxt;
  end
end

// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : wq_merge_counter_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_merge_counter_r         <= 8'd128;
    wq_merge_counter_expired_r <= 1'b0;
  end
  else if (wq_merge_counter_cg0)
  begin
    wq_merge_counter_r         <= wq_merge_counter_nxt;
    wq_merge_counter_expired_r <= wq_merge_counter_expired_nxt;
  end
end


always @(posedge clk or posedge rst_a)
begin : wr_merge_hot_reg_PROC
  if (rst_a == 1'b1)
  begin
    wr_merge_hot_r <= 4'b0000;
  end
  else if (wr_merge_hot_cg0)
  begin
    wr_merge_hot_r <= wr_merge_hot_nxt;
  end
end
// VPOST ON


//////////////////////////////////////////////////////////////////////////////
// Synchronous process for writing new information into the FIFO
//
//////////////////////////////////////////////////////////////////////////////



// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//

always @(posedge clk or posedge rst_a)
begin : wq0_sync_PROC
  if (rst_a == 1'b1)
  begin
    wq0_target_r        <= {`npuarc_DMP_TARGET_BITS{1'b0}};
    wq0_size_r          <= 3'b000;
    wq0_user_mode_r     <= 1'b0;
    wq0_debug_r         <= 1'b0;
    wq0_addr_r          <= {`npuarc_PADDR_SIZE{1'b0}};
    wq0_bank_mask_r     <= 4'b0000;
    wq0_ecc_mask_r      <= 8'd0;
    wq0_ecc_addr_r      <= 3'd0;
    wq0_data_mask_r     <= 8'd0;
  
    wq0_grad_tag_lo_r   <= `npuarc_GRAD_TAG_BITS'd0;
    wq0_grad_tag_hi_r   <= `npuarc_GRAD_TAG_BITS'd0;
    wq0_grad_data_src_r <= 2'b00;
    wq0_external_ex_r   <= 1'b0;
    wq0_scond_r         <= 1'b0;
    wq0_way_hot_r       <= {`npuarc_DC_WAYS{1'b0}};
  end
  else if (wq_addr_cg1 & wq0_addr_cg0)
  begin
      wq0_target_r      <= wq0_target_nxt;
      wq0_size_r        <= wq0_size_nxt;    
      wq0_user_mode_r   <= wq0_user_mode_nxt;    
      wq0_debug_r       <= wq0_debug_nxt;    
      wq0_addr_r        <= wq0_addr_nxt;    
      wq0_bank_mask_r   <= wq0_bank_mask_nxt;
      wq0_ecc_mask_r    <= wq0_ecc_mask_nxt;
      wq0_ecc_addr_r    <= wq0_ecc_addr_nxt;    
      wq0_data_mask_r    <= wq0_data_mask_nxt; 
    
      wq0_grad_tag_lo_r  <= wq0_grad_tag_lo_nxt; 
      wq0_grad_tag_hi_r  <= wq0_grad_tag_hi_nxt; 
      wq0_grad_data_src_r<= wq0_grad_data_src_nxt;
      wq0_external_ex_r <= wq0_external_ex_nxt;
      wq0_scond_r       <= wq0_scond_nxt;
      wq0_way_hot_r     <= wq0_way_hot_nxt; 
  end
end

always @(posedge clk or posedge rst_a)
begin : wq0_data_PROC
  if (rst_a == 1'b1)
  begin
    wq0_data_r          <= {`npuarc_DMP_DATA_BITS{1'b0}};
    wq0_grad_r          <= 2'd0;
    wq0_rtt_grad_data_r <= {`npuarc_DMP_DATA_BITS{1'b0}};
  end
  else if (wq_data_cg1 & wq0_data_cg0)
  begin
      wq0_data_r        <= wq0_store_grad_match1 ? wq0_wr_data0 : wq0_data_nxt;
      wq0_rtt_grad_data_r <= wq0_store_grad_match1 ?  wq0_rtt_grad_data_nxt : ca_wr_data_r; 
      wq0_grad_r        <= wq0_store_grad_match1 
                            ? wq0_grad_prel 
                            : wq0_grad_nxt;
  end
end

// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//

always @(posedge clk or posedge rst_a)
begin : wq1_sync_PROC
  if (rst_a == 1'b1)
  begin
    wq1_target_r        <= {`npuarc_DMP_TARGET_BITS{1'b0}};
    wq1_size_r          <= 3'b000;
    wq1_user_mode_r     <= 1'b0;
    wq1_debug_r         <= 1'b0;
    wq1_addr_r          <= {`npuarc_PADDR_SIZE{1'b0}};
    wq1_bank_mask_r     <= 4'b0000;
    wq1_ecc_mask_r      <= 8'd0;
    wq1_ecc_addr_r      <= 3'd0;
    wq1_data_mask_r     <= 8'd0;
  
    wq1_grad_tag_lo_r   <= `npuarc_GRAD_TAG_BITS'd0;
    wq1_grad_tag_hi_r   <= `npuarc_GRAD_TAG_BITS'd0;
    wq1_grad_data_src_r <= 2'b00;
    wq1_external_ex_r   <= 1'b0;
    wq1_scond_r         <= 1'b0;
    wq1_way_hot_r       <= {`npuarc_DC_WAYS{1'b0}};
  end
  else if (wq_addr_cg1 & wq1_addr_cg0)
  begin
      wq1_target_r      <= wq1_target_nxt;
      wq1_size_r        <= wq1_size_nxt;    
      wq1_user_mode_r   <= wq1_user_mode_nxt;    
      wq1_debug_r       <= wq1_debug_nxt;    
      wq1_addr_r        <= wq1_addr_nxt;    
      wq1_bank_mask_r   <= wq1_bank_mask_nxt;
      wq1_ecc_mask_r    <= wq1_ecc_mask_nxt;
      wq1_ecc_addr_r    <= wq1_ecc_addr_nxt;    
      wq1_data_mask_r    <= wq1_data_mask_nxt; 
    
      wq1_grad_tag_lo_r  <= wq1_grad_tag_lo_nxt; 
      wq1_grad_tag_hi_r  <= wq1_grad_tag_hi_nxt; 
      wq1_grad_data_src_r<= wq1_grad_data_src_nxt;
      wq1_external_ex_r <= wq1_external_ex_nxt;
      wq1_scond_r       <= wq1_scond_nxt;
      wq1_way_hot_r     <= wq1_way_hot_nxt; 
  end
end

always @(posedge clk or posedge rst_a)
begin : wq1_data_PROC
  if (rst_a == 1'b1)
  begin
    wq1_data_r          <= {`npuarc_DMP_DATA_BITS{1'b0}};
    wq1_grad_r          <= 2'd0;
    wq1_rtt_grad_data_r <= {`npuarc_DMP_DATA_BITS{1'b0}};
  end
  else if (wq_data_cg1 & wq1_data_cg0)
  begin
      wq1_data_r        <= wq1_store_grad_match1 ? wq1_wr_data0 : wq1_data_nxt;
      wq1_rtt_grad_data_r <= wq1_store_grad_match1 ?  wq1_rtt_grad_data_nxt : ca_wr_data_r; 
      wq1_grad_r        <= wq1_store_grad_match1 
                            ? wq1_grad_prel 
                            : wq1_grad_nxt;
  end
end

// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//

always @(posedge clk or posedge rst_a)
begin : wq2_sync_PROC
  if (rst_a == 1'b1)
  begin
    wq2_target_r        <= {`npuarc_DMP_TARGET_BITS{1'b0}};
    wq2_size_r          <= 3'b000;
    wq2_user_mode_r     <= 1'b0;
    wq2_debug_r         <= 1'b0;
    wq2_addr_r          <= {`npuarc_PADDR_SIZE{1'b0}};
    wq2_bank_mask_r     <= 4'b0000;
    wq2_ecc_mask_r      <= 8'd0;
    wq2_ecc_addr_r      <= 3'd0;
    wq2_data_mask_r     <= 8'd0;
  
    wq2_grad_tag_lo_r   <= `npuarc_GRAD_TAG_BITS'd0;
    wq2_grad_tag_hi_r   <= `npuarc_GRAD_TAG_BITS'd0;
    wq2_grad_data_src_r <= 2'b00;
    wq2_external_ex_r   <= 1'b0;
    wq2_scond_r         <= 1'b0;
    wq2_way_hot_r       <= {`npuarc_DC_WAYS{1'b0}};
  end
  else if (wq_addr_cg1 & wq2_addr_cg0)
  begin
      wq2_target_r      <= wq2_target_nxt;
      wq2_size_r        <= wq2_size_nxt;    
      wq2_user_mode_r   <= wq2_user_mode_nxt;    
      wq2_debug_r       <= wq2_debug_nxt;    
      wq2_addr_r        <= wq2_addr_nxt;    
      wq2_bank_mask_r   <= wq2_bank_mask_nxt;
      wq2_ecc_mask_r    <= wq2_ecc_mask_nxt;
      wq2_ecc_addr_r    <= wq2_ecc_addr_nxt;    
      wq2_data_mask_r    <= wq2_data_mask_nxt; 
    
      wq2_grad_tag_lo_r  <= wq2_grad_tag_lo_nxt; 
      wq2_grad_tag_hi_r  <= wq2_grad_tag_hi_nxt; 
      wq2_grad_data_src_r<= wq2_grad_data_src_nxt;
      wq2_external_ex_r <= wq2_external_ex_nxt;
      wq2_scond_r       <= wq2_scond_nxt;
      wq2_way_hot_r     <= wq2_way_hot_nxt; 
  end
end

always @(posedge clk or posedge rst_a)
begin : wq2_data_PROC
  if (rst_a == 1'b1)
  begin
    wq2_data_r          <= {`npuarc_DMP_DATA_BITS{1'b0}};
    wq2_grad_r          <= 2'd0;
    wq2_rtt_grad_data_r <= {`npuarc_DMP_DATA_BITS{1'b0}};
  end
  else if (wq_data_cg1 & wq2_data_cg0)
  begin
      wq2_data_r        <= wq2_store_grad_match1 ? wq2_wr_data0 : wq2_data_nxt;
      wq2_rtt_grad_data_r <= wq2_store_grad_match1 ?  wq2_rtt_grad_data_nxt : ca_wr_data_r; 
      wq2_grad_r        <= wq2_store_grad_match1 
                            ? wq2_grad_prel 
                            : wq2_grad_nxt;
  end
end

// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//

always @(posedge clk or posedge rst_a)
begin : wq3_sync_PROC
  if (rst_a == 1'b1)
  begin
    wq3_target_r        <= {`npuarc_DMP_TARGET_BITS{1'b0}};
    wq3_size_r          <= 3'b000;
    wq3_user_mode_r     <= 1'b0;
    wq3_debug_r         <= 1'b0;
    wq3_addr_r          <= {`npuarc_PADDR_SIZE{1'b0}};
    wq3_bank_mask_r     <= 4'b0000;
    wq3_ecc_mask_r      <= 8'd0;
    wq3_ecc_addr_r      <= 3'd0;
    wq3_data_mask_r     <= 8'd0;
  
    wq3_grad_tag_lo_r   <= `npuarc_GRAD_TAG_BITS'd0;
    wq3_grad_tag_hi_r   <= `npuarc_GRAD_TAG_BITS'd0;
    wq3_grad_data_src_r <= 2'b00;
    wq3_external_ex_r   <= 1'b0;
    wq3_scond_r         <= 1'b0;
    wq3_way_hot_r       <= {`npuarc_DC_WAYS{1'b0}};
  end
  else if (wq_addr_cg1 & wq3_addr_cg0)
  begin
      wq3_target_r      <= wq3_target_nxt;
      wq3_size_r        <= wq3_size_nxt;    
      wq3_user_mode_r   <= wq3_user_mode_nxt;    
      wq3_debug_r       <= wq3_debug_nxt;    
      wq3_addr_r        <= wq3_addr_nxt;    
      wq3_bank_mask_r   <= wq3_bank_mask_nxt;
      wq3_ecc_mask_r    <= wq3_ecc_mask_nxt;
      wq3_ecc_addr_r    <= wq3_ecc_addr_nxt;    
      wq3_data_mask_r    <= wq3_data_mask_nxt; 
    
      wq3_grad_tag_lo_r  <= wq3_grad_tag_lo_nxt; 
      wq3_grad_tag_hi_r  <= wq3_grad_tag_hi_nxt; 
      wq3_grad_data_src_r<= wq3_grad_data_src_nxt;
      wq3_external_ex_r <= wq3_external_ex_nxt;
      wq3_scond_r       <= wq3_scond_nxt;
      wq3_way_hot_r     <= wq3_way_hot_nxt; 
  end
end

always @(posedge clk or posedge rst_a)
begin : wq3_data_PROC
  if (rst_a == 1'b1)
  begin
    wq3_data_r          <= {`npuarc_DMP_DATA_BITS{1'b0}};
    wq3_grad_r          <= 2'd0;
    wq3_rtt_grad_data_r <= {`npuarc_DMP_DATA_BITS{1'b0}};
  end
  else if (wq_data_cg1 & wq3_data_cg0)
  begin
      wq3_data_r        <= wq3_store_grad_match1 ? wq3_wr_data0 : wq3_data_nxt;
      wq3_rtt_grad_data_r <= wq3_store_grad_match1 ?  wq3_rtt_grad_data_nxt : ca_wr_data_r; 
      wq3_grad_r        <= wq3_store_grad_match1 
                            ? wq3_grad_prel 
                            : wq3_grad_nxt;
  end
end

// leda NTL_CON32 on

// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions
// VPOST OFF
// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions

always @(posedge clk or posedge rst_a)
begin : wq0_dep_sync_PROC
  if (rst_a == 1'b1)
  begin
    wq0_dep_r <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (wq0_ctl_cg0)
    begin
// spyglass disable_block Ac_conv01
// SMD: Multiple synchronizers converging on flop
// SJ:  Signals are independent 
      wq0_dep_r                  <= wq0_dep_nxt;
// spyglass enable_block Ac_conv01
    end
    
    if (wq_mem_read)
    begin
      wq0_dep_r[wq_ext_rdentry0] <= 1'b0;
    end
    
    
    
  
    if (wq_dc_retire_one)
    begin
      wq0_dep_r[wq_dc_entry0_id] <= 1'b0;
    end
    
    if (wq_dc_retire_two)
    begin
      wq0_dep_r[wq_dc_entry0_id] <= 1'b0;
      wq0_dep_r[wq_dc_entry1_id] <= 1'b0;
    end
  end
end
// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions

always @(posedge clk or posedge rst_a)
begin : wq1_dep_sync_PROC
  if (rst_a == 1'b1)
  begin
    wq1_dep_r <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (wq1_ctl_cg0)
    begin
// spyglass disable_block Ac_conv01
// SMD: Multiple synchronizers converging on flop
// SJ:  Signals are independent 
      wq1_dep_r                  <= wq1_dep_nxt;
// spyglass enable_block Ac_conv01
    end
    
    if (wq_mem_read)
    begin
      wq1_dep_r[wq_ext_rdentry0] <= 1'b0;
    end
    
    
    
  
    if (wq_dc_retire_one)
    begin
      wq1_dep_r[wq_dc_entry0_id] <= 1'b0;
    end
    
    if (wq_dc_retire_two)
    begin
      wq1_dep_r[wq_dc_entry0_id] <= 1'b0;
      wq1_dep_r[wq_dc_entry1_id] <= 1'b0;
    end
  end
end
// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions

always @(posedge clk or posedge rst_a)
begin : wq2_dep_sync_PROC
  if (rst_a == 1'b1)
  begin
    wq2_dep_r <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (wq2_ctl_cg0)
    begin
// spyglass disable_block Ac_conv01
// SMD: Multiple synchronizers converging on flop
// SJ:  Signals are independent 
      wq2_dep_r                  <= wq2_dep_nxt;
// spyglass enable_block Ac_conv01
    end
    
    if (wq_mem_read)
    begin
      wq2_dep_r[wq_ext_rdentry0] <= 1'b0;
    end
    
    
    
  
    if (wq_dc_retire_one)
    begin
      wq2_dep_r[wq_dc_entry0_id] <= 1'b0;
    end
    
    if (wq_dc_retire_two)
    begin
      wq2_dep_r[wq_dc_entry0_id] <= 1'b0;
      wq2_dep_r[wq_dc_entry1_id] <= 1'b0;
    end
  end
end
// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions

always @(posedge clk or posedge rst_a)
begin : wq3_dep_sync_PROC
  if (rst_a == 1'b1)
  begin
    wq3_dep_r <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (wq3_ctl_cg0)
    begin
// spyglass disable_block Ac_conv01
// SMD: Multiple synchronizers converging on flop
// SJ:  Signals are independent 
      wq3_dep_r                  <= wq3_dep_nxt;
// spyglass enable_block Ac_conv01
    end
    
    if (wq_mem_read)
    begin
      wq3_dep_r[wq_ext_rdentry0] <= 1'b0;
    end
    
    
    
  
    if (wq_dc_retire_one)
    begin
      wq3_dep_r[wq_dc_entry0_id] <= 1'b0;
    end
    
    if (wq_dc_retire_two)
    begin
      wq3_dep_r[wq_dc_entry0_id] <= 1'b0;
      wq3_dep_r[wq_dc_entry1_id] <= 1'b0;
    end
  end
end
// VPOST ON
//////////////////////////////////////////////////////////////////////////////
//
// Dependency matrix that tracks dependencies between the WQ and LQ.
// WQ entry i depends on LQ entry j when wq[i]_lq_dep_r[j] == 1
// When an external entry is placed in the WQ, it depends on the LQ entries 
// that haven't had their command accepted on the IBP bus.
// A dependency is removed when the LQ entry is out on the IBP bus
//
//////////////////////////////////////////////////////////////////////////////
// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : wq0_lq_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq0_lq_dep_r         <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (wq0_ctl_cg0 == 1'b1)
    begin
      // Set up dependency between this WQ entry and last LQ entry
      //
      wq0_lq_dep_r         <=  lq_order_ptr_1h
                             & {`npuarc_DMP_FIFO_DEPTH{dc4_target_external0}};
    end
    
    if (  (wq_valid_r[0] | ca_store_r)
        & lq_cmd_read
        & (~wq_strict_order[0]))
    begin
      // Clear dependency when dependent LQ command has been processed (out on the 
      // IBP bus) and there is no strict ordering
      //
      wq0_lq_dep_r[lq_cmd_rd_ptr]  <= 1'b0;
    end
    
    if (  (wq_valid_r[0] | ca_store_r)
        & lq_data_retire)
    begin
      // Clear dependency when dependent LQ command has been retired 
      //
      wq0_lq_dep_r[lq_data_rd_ptr] <= 1'b0;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : wq1_lq_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq1_lq_dep_r         <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (wq1_ctl_cg0 == 1'b1)
    begin
      // Set up dependency between this WQ entry and last LQ entry
      //
      wq1_lq_dep_r         <=  lq_order_ptr_1h
                             & {`npuarc_DMP_FIFO_DEPTH{dc4_target_external0}};
    end
    
    if (  (wq_valid_r[1] | ca_store_r)
        & lq_cmd_read
        & (~wq_strict_order[1]))
    begin
      // Clear dependency when dependent LQ command has been processed (out on the 
      // IBP bus) and there is no strict ordering
      //
      wq1_lq_dep_r[lq_cmd_rd_ptr]  <= 1'b0;
    end
    
    if (  (wq_valid_r[1] | ca_store_r)
        & lq_data_retire)
    begin
      // Clear dependency when dependent LQ command has been retired 
      //
      wq1_lq_dep_r[lq_data_rd_ptr] <= 1'b0;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : wq2_lq_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq2_lq_dep_r         <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (wq2_ctl_cg0 == 1'b1)
    begin
      // Set up dependency between this WQ entry and last LQ entry
      //
      wq2_lq_dep_r         <=  lq_order_ptr_1h
                             & {`npuarc_DMP_FIFO_DEPTH{dc4_target_external0}};
    end
    
    if (  (wq_valid_r[2] | ca_store_r)
        & lq_cmd_read
        & (~wq_strict_order[2]))
    begin
      // Clear dependency when dependent LQ command has been processed (out on the 
      // IBP bus) and there is no strict ordering
      //
      wq2_lq_dep_r[lq_cmd_rd_ptr]  <= 1'b0;
    end
    
    if (  (wq_valid_r[2] | ca_store_r)
        & lq_data_retire)
    begin
      // Clear dependency when dependent LQ command has been retired 
      //
      wq2_lq_dep_r[lq_data_rd_ptr] <= 1'b0;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : wq3_lq_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq3_lq_dep_r         <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (wq3_ctl_cg0 == 1'b1)
    begin
      // Set up dependency between this WQ entry and last LQ entry
      //
      wq3_lq_dep_r         <=  lq_order_ptr_1h
                             & {`npuarc_DMP_FIFO_DEPTH{dc4_target_external0}};
    end
    
    if (  (wq_valid_r[3] | ca_store_r)
        & lq_cmd_read
        & (~wq_strict_order[3]))
    begin
      // Clear dependency when dependent LQ command has been processed (out on the 
      // IBP bus) and there is no strict ordering
      //
      wq3_lq_dep_r[lq_cmd_rd_ptr]  <= 1'b0;
    end
    
    if (  (wq_valid_r[3] | ca_store_r)
        & lq_data_retire)
    begin
      // Clear dependency when dependent LQ command has been retired 
      //
      wq3_lq_dep_r[lq_data_rd_ptr] <= 1'b0;
    end
  end
end

// VPOST ON

// VPOST OFF

// leda FM_1_7 on
// VPOST ON
// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions
//
// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : wq_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_valid_r              <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
    wq_out_r                <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
    wq_garbage_r            <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};

    wq_recent_wr_r          <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
    wq_recent_external_wr_r <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
    wq_volatile_r           <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
    wq_strict_order_r       <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
    wq_data_mem_attr_r      <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    // Write One
    //
    if (wq_write_one)
    begin
      // Avoid scrubbing when there is a DMI access to the same address
      //
      wq_valid_r[wq_wrentry0]         <=   ca_store_r
                                         & (~ca_dmi_scrubbing_conflict)
                                         ;

      wq_recent_wr_r                  <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
      wq_recent_wr_r[wq_wrentry0]     <=  1'b1
                                          & (~ca_dmi_scrubbing_conflict)
                                         ;
      wq_volatile_r[wq_wrentry0]      <= ca_volatile_r;
      wq_strict_order_r[wq_wrentry0]  <=   ca_store_r 
                                         & (dc4_war_hazard | ca_strict_order_r);
      wq_data_mem_attr_r[wq_wrentry0] <=   ca_store_r
                                         & (~ca_locked_r) 
                                         & ca_data_mem_attr_r;
    end

    // This tracks the most recent external write
    //
    if (  wq_write_one
        & dc4_target_external0
        & ca_store_r)
    begin
      wq_recent_external_wr_r              <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
      wq_recent_external_wr_r[wq_wrentry0] <= 1'b1;
    end
    
    // Write two
    //
    if (wq_write_two)
    begin
      wq_valid_r[wq_wrentry0]         <= ca_store_r
                                       & (~ca_dmi_scrubbing_conflict)
                                       ;
      wq_valid_r[wq_wrentry1]         <= ca_store_r
                                       & (~ca_dmi_scrubbing_conflict)
                                       ;
      wq_recent_wr_r[wq_wrentry0]     <= 1'b1
                                        & (~ca_dmi_scrubbing_conflict)
                                        ;
      wq_recent_wr_r[wq_wrentry1]     <= 1'b1
                                        & (~ca_dmi_scrubbing_conflict)
                                        ;
      wq_volatile_r[wq_wrentry0]      <= ca_volatile_r;
      wq_volatile_r[wq_wrentry1]      <= ca_volatile_r;
      wq_strict_order_r[wq_wrentry1]  <= ca_store_r
                                        & (dc4_war_hazard | ca_strict_order_r);
      wq_data_mem_attr_r[wq_wrentry1] <=   ca_store_r
                                         & (~ca_locked_r) 
                                         & ca_data_mem_attr_r;
    end
    
    // This tracks the most recent external write(s)
    //
    if (  wq_write_two
        & dc4_target_external1)
    begin
      wq_recent_external_wr_r              <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
      wq_recent_external_wr_r[wq_wrentry0] <= 1'b1;
      wq_recent_external_wr_r[wq_wrentry1] <= 1'b1;
    end

    // Entry processed (out on the bus)
    //
    if (wq_mem_per_iccm_read)
    begin
      wq_out_r[wq_ext_rdentry0]        <= 1'b1;
    end
    
    // Garbage bit setting
    //
    if (wq_set_garbage[0])
    begin
      wq_garbage_r[0]                 <= 1'b1;
    end
    if (wq_set_garbage[1])
    begin
      wq_garbage_r[1]                 <= 1'b1;
    end
    if (wq_set_garbage[2])
    begin
      wq_garbage_r[2]                 <= 1'b1;
    end
    if (wq_set_garbage[3])
    begin
      wq_garbage_r[3]                 <= 1'b1;
    end

    // Entry retirement
    //
    if (wq_mem_retire)
    begin
      wq_valid_r[wq_mem_entry_id]               <= 1'b0; 
      wq_recent_wr_r[wq_mem_entry_id]           <= 1'b0; 
      wq_recent_external_wr_r[wq_mem_entry_id]  <= 1'b0;
      wq_volatile_r[wq_mem_entry_id]            <= 1'b0;
      wq_strict_order_r[wq_mem_entry_id]        <= 1'b0;
      wq_data_mem_attr_r[wq_mem_entry_id]       <= 1'b0;
      wq_out_r[wq_mem_entry_id]                 <= 1'b0;
      wq_garbage_r[wq_mem_entry_id]             <= 1'b0;
    end
    
    
    
    if (wq_dc_retire_one)
    begin
      wq_valid_r[wq_dc_entry0_id]         <= 1'b0;
      wq_recent_wr_r[wq_dc_entry0_id]     <= 1'b0;
      wq_strict_order_r[wq_dc_entry0_id]  <= 1'b0;
      wq_data_mem_attr_r[wq_dc_entry0_id] <= 1'b0;
      wq_garbage_r[wq_dc_entry0_id]       <= 1'b0;
    end
    
    if (wq_dc_retire_two)
    begin
      wq_valid_r[wq_dc_entry0_id]         <= 1'b0;
      wq_valid_r[wq_dc_entry1_id]         <= 1'b0;
      wq_strict_order_r[wq_dc_entry0_id]  <= 1'b0;
      wq_strict_order_r[wq_dc_entry1_id]  <= 1'b0;
      wq_data_mem_attr_r[wq_dc_entry1_id] <= 1'b0;
      wq_recent_wr_r[wq_dc_entry0_id]     <= 1'b0;
      wq_recent_wr_r[wq_dc_entry1_id]     <= 1'b0;
      wq_garbage_r[wq_dc_entry0_id]       <= 1'b0;
      wq_garbage_r[wq_dc_entry1_id]       <= 1'b0;
   end
    
  end
end

// VPOST ON

// VPOST OFF

always @(posedge clk or posedge rst_a)
begin : wq_grad_st_rtt_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_grad_st_rtt_r        <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
    dmp_st_retire0_r           <= 1'b0;
    dmp_st_retire0_tag_r       <= 2'b00;
    dmp_st_retire1_r           <= 1'b0;
    dmp_st_retire1_tag_r       <= 2'b00;

  end
  else
  begin
    // Write One
    //
    if (wq_write_one)
    begin
     wq_grad_st_rtt_r[wq_wrentry0]    <= ca_store_r
                                       & (|ca_store_grad_r)
                                       & ca_store_grad_rtt_prel0; 
    end
    
    // Write two
    //
    if (wq_write_two)
    begin
      wq_grad_st_rtt_r[wq_wrentry0]    <= ca_store_r
                                        & (|ca_store_grad_r)
                                        & ca_store_grad_rtt_prel0;

      wq_grad_st_rtt_r[wq_wrentry1]    <= ca_store_r
                                        & (|ca_store_grad_r)
                                        & ca_store_grad_rtt_prel1;
    end
    

    // Entry retirement
    //
    
    if ( (  (wq0_store_grad_match1
            )
          & wq_grad_st_rtt_r[0]
          & (wq0_grad_prel == 2'b00))
       | (wq_grad_st_rtt_r[0] & (~wq_grad_r[0])) )  
    begin
      //
      // Entry 0
      //
      wq_grad_st_rtt_r[0]              <= 1'b0;
      dmp_st_retire0_r                 <= wq_grad_st_rtt_r[0];
      dmp_st_retire0_tag_r             <= 2'd0;

      if ( ( (wq1_store_grad_match1
             )
            & wq_grad_st_rtt_r[1]
            & (wq1_grad_prel == 2'b00))
         | (wq_grad_st_rtt_r[1] & (~wq_grad_r[1])) )      
      begin
        //
        wq_grad_st_rtt_r[1]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[1];
        dmp_st_retire1_tag_r           <= 2'd1;
      end
      else if ( ( (wq2_store_grad_match1
                  )
                 & wq_grad_st_rtt_r[2]
                 & (wq2_grad_prel == 2'b00))
              | (wq_grad_st_rtt_r[2] & (~wq_grad_r[2])) )      
      begin
        //
        wq_grad_st_rtt_r[2]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[2];
        dmp_st_retire1_tag_r           <= 2'd2;
      end 
      else if ( ( (wq3_store_grad_match1
                  )
                 & wq_grad_st_rtt_r[3]
                 & (wq3_grad_prel == 2'b00))
              | (wq_grad_st_rtt_r[3] & (~wq_grad_r[3])) )      
      begin
        //
        wq_grad_st_rtt_r[3]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[3];
        dmp_st_retire1_tag_r           <= 2'd3;
      end 
    end
    else if ( ( (wq1_store_grad_match1
                )
               & wq_grad_st_rtt_r[1]
               & (wq1_grad_prel == 2'b00))
            | (wq_grad_st_rtt_r[1] & (~wq_grad_r[1])) )    
    begin
      //
      // Entry 1
      //
      wq_grad_st_rtt_r[1]              <= 1'b0;
      dmp_st_retire0_r                 <= wq_grad_st_rtt_r[1];
      dmp_st_retire0_tag_r             <= 2'd1;

      if ( (  (wq0_store_grad_match1
              )
            & wq_grad_st_rtt_r[0]
            & (wq0_grad_prel == 2'b00))
         | (wq_grad_st_rtt_r[0] & (~wq_grad_r[0])) )      
      begin
        //
        wq_grad_st_rtt_r[0]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[0];
        dmp_st_retire1_tag_r           <= 2'd0;
      end
      else if ( ( (wq2_store_grad_match1
                  )
                 & wq_grad_st_rtt_r[2]
                 & (wq2_grad_prel == 2'b00))
              | (wq_grad_st_rtt_r[2] & (~wq_grad_r[2])) )      
      begin
        //
        wq_grad_st_rtt_r[2]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[2];
        dmp_st_retire1_tag_r           <= 2'd2;
      end 
      else if ( ( (wq3_store_grad_match1
                  )
                 & wq_grad_st_rtt_r[3]
                 & (wq3_grad_prel == 2'b00))
              | (wq_grad_st_rtt_r[3] & (~wq_grad_r[3])) )      
      begin
        //
        wq_grad_st_rtt_r[3]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[3];
        dmp_st_retire1_tag_r           <= 2'd3;
      end 
    end
    else if ( ( (wq2_store_grad_match1
                )
               & wq_grad_st_rtt_r[2]
               & (wq2_grad_prel == 2'b00))
            | (wq_grad_st_rtt_r[2] & (~wq_grad_r[2])) )    
    begin
      //
      // Entry 2
      //  
      wq_grad_st_rtt_r[2]              <= 1'b0;
      dmp_st_retire0_r                 <= wq_grad_st_rtt_r[2];
      dmp_st_retire0_tag_r             <= 2'd2;

      if ( (  (wq0_store_grad_match1
              )
            & wq_grad_st_rtt_r[0]
            & (wq0_grad_prel == 2'b00))
         | (wq_grad_st_rtt_r[0] & (~wq_grad_r[0])) )      
      begin
        //
        wq_grad_st_rtt_r[0]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[0];
        dmp_st_retire1_tag_r           <= 2'd0;
      end
      else if ( ( (wq1_store_grad_match1
                  )
                 & wq_grad_st_rtt_r[1]
                 & (wq1_grad_prel == 2'b00))
              | (wq_grad_st_rtt_r[1] & (~wq_grad_r[1])) )      
      begin
        //
        wq_grad_st_rtt_r[1]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[1];
        dmp_st_retire1_tag_r           <= 2'd1;
      end 
      else if ( ( (wq3_store_grad_match1
                  )
                 & wq_grad_st_rtt_r[3]
                 & (wq3_grad_prel == 2'b00))
              | (wq_grad_st_rtt_r[3] & (~wq_grad_r[3])) )      
      begin
        //
        wq_grad_st_rtt_r[3]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[3];
        dmp_st_retire1_tag_r           <= 2'd3;
      end 
    end
    else if ( ( (wq3_store_grad_match1
                )
               & wq_grad_st_rtt_r[3]
               & (wq3_grad_prel == 2'b00))
            | (wq_grad_st_rtt_r[3] & (~wq_grad_r[3])) )    
    begin
      //
      // Entry 3 
      //  
      wq_grad_st_rtt_r[3]              <= 1'b0;
      dmp_st_retire0_r                 <= wq_grad_st_rtt_r[3];
      dmp_st_retire0_tag_r             <= 2'd3;

      if ( (  (wq0_store_grad_match1
              )
            & wq_grad_st_rtt_r[0]
            & (wq0_grad_prel == 2'b00))
         | (wq_grad_st_rtt_r[0] & (~wq_grad_r[0])) )      
      begin
        //
        wq_grad_st_rtt_r[0]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[0];
        dmp_st_retire1_tag_r           <= 2'd0;
      end
      else if ( ( (wq1_store_grad_match1
                  )
                 & wq_grad_st_rtt_r[1]
                 & (wq1_grad_prel == 2'b00))
              | (wq_grad_st_rtt_r[1] & (~wq_grad_r[1])) )      
      begin
        //
        wq_grad_st_rtt_r[1]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[1];
        dmp_st_retire1_tag_r           <= 2'd1;
      end 
      else if ( ( (wq2_store_grad_match1
                  )
                 & wq_grad_st_rtt_r[2]
                 & (wq2_grad_prel == 2'b00))
              | (wq_grad_st_rtt_r[2] & (~wq_grad_r[2])) )      
      begin
        //
        wq_grad_st_rtt_r[2]            <= 1'b0;
        dmp_st_retire1_r               <= wq_grad_st_rtt_r[2];
        dmp_st_retire1_tag_r           <= 2'd2;
      end 
    end
    else
    begin
      dmp_st_retire0_r                 <= 1'b0;
      dmp_st_retire1_r                 <= 1'b0;
    end
  end
end
// VPOST ON

// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : wq_ext_dealloc_pend_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_ext_dealloc_pend_r  <= 1'b0;
    wq_ext_dealloc_entry_r <= {`npuarc_WQ_PTR_DEPTH{1'b0}};
  end
  else
  begin
    if (wq_ext_dealloc_set)
    begin
      wq_ext_dealloc_pend_r  <= 1'b1;
      wq_ext_dealloc_entry_r <= wq_ext_dealloc_entry_nxt;
    end
// spyglass disable_block W415a
// SMD: signal assigned multiple times in the same always block
// SJ:  done on purpose, last one has priority. 
    if (wq_mem_per_iccm_read) 
    begin
      wq_ext_dealloc_pend_r  <= 1'b0;
      wq_ext_dealloc_entry_r <= {`npuarc_WQ_PTR_DEPTH{1'b0}};
    end
// spyglass enable_block W415a
  end
end
// VPOST ON

// VPOST OFF

always @(posedge clk or posedge rst_a)
begin : wq_dc_dealloc_pend_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_dc_dealloc_pend_r  <= 1'b0;
    wq_dc_dealloc_entry_r <= {`npuarc_WQ_PTR_DEPTH{1'b0}};
  end
  else
  begin
    if (wq_dc_dealloc_set)
    begin
      wq_dc_dealloc_pend_r  <= 1'b1;
      wq_dc_dealloc_entry_r <= wq_dc_dealloc_entry_nxt;
    end
// spyglass disable_block W415a
// SMD: signal assigned multiple times in the same always block
// SJ:  done on purpose, last one has priority. 
    if (wq_dc_processed) //  
    begin
      wq_dc_dealloc_pend_r  <= 1'b0;
      wq_dc_dealloc_entry_r <= {`npuarc_WQ_PTR_DEPTH{1'b0}};
    end
// spyglass enable_block W415a
  end
end
// VPOST ON

//////////////////////////////////////////////////////////////////////////////
// RAW depenedencies
//
//////////////////////////////////////////////////////////////////////////////
// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : dc4_raw_haz_reg_PROC
  if (rst_a == 1'b1)
  begin
     dc4_raw_hazard_entries_prel_r <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (dc4_update_raw_hazard_cg0 == 1'b1)
    begin
      dc4_raw_hazard_entries_prel_r <= dc4_raw_hazard_entries_prel_nxt;
    end
// spyglass disable_block W415a
// SMD: signal assigned multiple times in the same always block
// SJ:  done on purpose, last one has priority.    
    if (dc4_setup_raw_hazard_cg0 == 1'b1)
    begin
      dc4_raw_hazard_entries_prel_r <= dc3_raw_hazard_entries;
    end
// spyglass enable_block W415a
  end
end
// VPOST ON

////////////////////////////////////////////////////////////////////////////
//
// DC3 Stall
//
///////////////////////////////////////////////////////////////////////////
always @*
begin
    dc3_stall_state_next   = dc3_stall_state_nxt;
    dc3_stall_next         = dc3_stall_nxt;
    dc3_stall_vector_next  = dc3_stall_vector_nxt;
end

always @(posedge clk or posedge rst_a)
begin : dc3_stall_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_stall_state_r  <= DC3_STALL_DEFAULT;
    dc3_stall_r        <= 1'b0;
    dc3_stall_vector_r <= 3'b000;
  end
  else
  begin
    dc3_stall_state_r  <= dc3_stall_state_next;
    dc3_stall_r        <= dc3_stall_next;
    dc3_stall_vector_r <= dc3_stall_vector_next;
  end
end  


// leda FM_1_7 on
// spyglass enable_block STARC05-2.2.3.3

endmodule // alb_dmp_wq_fifo

