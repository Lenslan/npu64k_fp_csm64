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
// ALB_DMP_LQ_FIFO
// 
// 
// 
// 
//
// ===========================================================================
//
// Description:
//  This module implements the Load  Queue Fifo. This block services load
//  instructions that accesses external memory.  
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_lq_fifo.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_lq_fifo (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  ////////// General input signals ///////////////////////////////////////////
  //
  input                           clk,            // clock
  input                           rst_a,          // reset

  ////////// Interface to the X3 //////////////////////////////////////////
  //
  input                           x3_store_r,      // X3 store  
  input                           x3_pass,         // X3 pass  
  input  [`npuarc_PADDR_RANGE]           x3_mem_addr0_r,  // X3 memory address
  input  [`npuarc_PADDR_RANGE]           x3_mem_addr1_r,  // X3 memory address
  input  [`npuarc_DMP_TARGET_RANGE]      dc3_target_r,    // DC3 target
  input  [3:0]                    dc3_bank_sel_r,  // DC3 bank sel

  ////////// FIFO speculative write /////////////////////////////////////////////////////
  //
  input                           lq_fifo_push,
  
  ////////// Entry of the  FIFO /////////////////////////////////////////
  //
  input                           ca_pass,
  input                           ca_load_r,
  input                           ca_store_r,
  input                           ca_locked_r,
  input                           ca_volatile_r,
  input                           ca_strict_order_r,
  input [`npuarc_PADDR_RANGE]            ca_mem_addr0_r,
  input [`npuarc_PADDR_RANGE]            ca_mem_addr1_r,
  input [1:0]                     ca_size_r,      
  input                           ca_sex_r,       
  input                           ca_user_mode_r,       
  input [`npuarc_GRAD_TAG_RANGE]         ca_grad_tag,       
  
  input [`npuarc_DMP_TARGET_RANGE]       dc4_target_r,     // DC4 memory target   
  input [3:0]                     dc4_bank_sel_r,
  input                           dc4_unaligned,    // DC4 crosses 64-bit
    
  ////////// Removal from the cmd FIFO //////////////////////////////////////
  //
  input                           lq_fifo_cmd_pop,
  output reg [`npuarc_LQ_PTR_RANGE]      lq_cmd_rd_ptr,
  
  ////////// Removal from the data FIFO /////////////////////////////////////
  //
  input                           lq_fifo_data_pop,
  input [`npuarc_LQ_PTR_RANGE]           lq_data_rd_ptr,
  
  input                           lq_data_retire,    // removal of war hazard
  
  ////////// Top of the cmd FIFO ////////////////////////////////////////////
  //
  output reg                      lq_fifo_cmd_valid,  
  output reg                      lq_fifo_cmd_unaligned,  
  output reg [`npuarc_PADDR_RANGE]       lq_fifo_cmd_addr,   
  output reg [`npuarc_PADDR_RANGE]       lq_fifo_cmd_addr1,   
  output reg [`npuarc_DMP_TARGET_RANGE]  lq_fifo_cmd_target, 
  output reg                      lq_fifo_cmd_ex, 
  output reg                      lq_fifo_cmd_llock,
  output reg [1:0]                lq_fifo_cmd_data_size, 
  output reg                      lq_fifo_cmd_user_mode, 

  ////////// Top of the data FIFO ////////////////////////////////////////////
  //
  output reg [1:0]                lq_fifo_data_size,       
  output reg                      lq_fifo_data_sex,        
  output reg [`npuarc_PADDR_RANGE]       lq_fifo_addr,     
  output reg [`npuarc_GRAD_TAG_RANGE]    lq_fifo_grad_tag,  
  output reg                      lq_fifo_unaligned,  
  output reg                      lq_fifo_data_llock,
  output reg                      lq_fifo_data_user_mode,  
  
  //////////  Outputs to WQ synchronization //////////////////////////////////
  //
  output reg [`npuarc_DMP_FIFO_RANGE]    lq_order_ptr_1h, // LQ most recent entry
  output reg                      dc4_war_hazard,  // WAR hazard

  //////////  Inputs for LQ  synchronization ////////////////////////////////////
  //
  input [`npuarc_DMP_FIFO_RANGE]         wq_order_ptr_1h,      // Last WQ mem/per/iccm entry 
  input                           dc4_raw_hazard,       // RAW hazard

  input                           wq_cmd_read,          // WQ entry processed
  input  [`npuarc_WQ_PTR_RANGE]          wq_rdentry0,          // WQ processed entry
 
  input                           wq_mem_retire,        // WQ mem entry retired
  input  [`npuarc_WQ_PTR_RANGE]          wq_mem_entry_id,      // WQ retired  entry
 
 



  ////////// Status reporting ////////////////////////////////////////////
  //
  output reg                      lq_fifo_empty,
  output reg                      lq_fifo_full,
  output reg                      lq_fifo_full_nxt 
// leda NTL_CON37 on  
// leda NTL_CON13C on  
);

// Local Declarations

reg [`npuarc_DMP_TARGET_RANGE]  lq_fifo_data_target;

reg                            lq_valid_cg0;
reg [`npuarc_DMP_FIFO_RANGE]          lq_valid_nxt;
reg [`npuarc_DMP_FIFO_RANGE]          lq_valid_r;
reg [`npuarc_DMP_FIFO_RANGE]          lq_out_r;
reg [`npuarc_DMP_FIFO_RANGE]          lq_volatile_r;

reg [`npuarc_DMP_FIFO_RANGE]          lq_cmd_wr_ptr_1h;
reg [`npuarc_LQ_PTR_RANGE]            lq_cmd_wr_ptr;

reg                            lq0_cmd_cg0;
reg                            lq0_cmd_cg1;

reg [`npuarc_PADDR_RANGE]             lq0_addr_nxt;
reg [`npuarc_PADDR_RANGE]             lq0_addr1_nxt;
reg  [1:0]                     lq0_size_nxt;  
reg                            lq0_sex_nxt;  
reg                            lq0_user_mode_nxt;  
reg [`npuarc_GRAD_TAG_RANGE]          lq0_tag_nxt;  
reg [`npuarc_DMP_TARGET_RANGE]        lq0_target_nxt;  
reg                            lq0_unaligned_nxt;  
reg                            lq0_ex_nxt;  
reg                            lq0_llock_nxt;  
  
reg [`npuarc_PADDR_RANGE]             lq0_addr_r;
reg [`npuarc_PADDR_RANGE]             lq0_addr1_r;
reg  [1:0]                     lq0_size_r;  
reg                            lq0_sex_r;  
reg                            lq0_user_mode_r;  
reg [`npuarc_GRAD_TAG_RANGE]          lq0_tag_r;  
reg [`npuarc_DMP_TARGET_RANGE]        lq0_target_r;  
reg                            lq0_unaligned_r;  
reg                            lq0_ex_r;  
reg                            lq0_llock_r;  
reg [`npuarc_DMP_FIFO_RANGE]          lq0_dep_r;
reg                            lq1_cmd_cg0;
reg                            lq1_cmd_cg1;

reg [`npuarc_PADDR_RANGE]             lq1_addr_nxt;
reg [`npuarc_PADDR_RANGE]             lq1_addr1_nxt;
reg  [1:0]                     lq1_size_nxt;  
reg                            lq1_sex_nxt;  
reg                            lq1_user_mode_nxt;  
reg [`npuarc_GRAD_TAG_RANGE]          lq1_tag_nxt;  
reg [`npuarc_DMP_TARGET_RANGE]        lq1_target_nxt;  
reg                            lq1_unaligned_nxt;  
reg                            lq1_ex_nxt;  
reg                            lq1_llock_nxt;  
  
reg [`npuarc_PADDR_RANGE]             lq1_addr_r;
reg [`npuarc_PADDR_RANGE]             lq1_addr1_r;
reg  [1:0]                     lq1_size_r;  
reg                            lq1_sex_r;  
reg                            lq1_user_mode_r;  
reg [`npuarc_GRAD_TAG_RANGE]          lq1_tag_r;  
reg [`npuarc_DMP_TARGET_RANGE]        lq1_target_r;  
reg                            lq1_unaligned_r;  
reg                            lq1_ex_r;  
reg                            lq1_llock_r;  
reg [`npuarc_DMP_FIFO_RANGE]          lq1_dep_r;
reg                            lq2_cmd_cg0;
reg                            lq2_cmd_cg1;

reg [`npuarc_PADDR_RANGE]             lq2_addr_nxt;
reg [`npuarc_PADDR_RANGE]             lq2_addr1_nxt;
reg  [1:0]                     lq2_size_nxt;  
reg                            lq2_sex_nxt;  
reg                            lq2_user_mode_nxt;  
reg [`npuarc_GRAD_TAG_RANGE]          lq2_tag_nxt;  
reg [`npuarc_DMP_TARGET_RANGE]        lq2_target_nxt;  
reg                            lq2_unaligned_nxt;  
reg                            lq2_ex_nxt;  
reg                            lq2_llock_nxt;  
  
reg [`npuarc_PADDR_RANGE]             lq2_addr_r;
reg [`npuarc_PADDR_RANGE]             lq2_addr1_r;
reg  [1:0]                     lq2_size_r;  
reg                            lq2_sex_r;  
reg                            lq2_user_mode_r;  
reg [`npuarc_GRAD_TAG_RANGE]          lq2_tag_r;  
reg [`npuarc_DMP_TARGET_RANGE]        lq2_target_r;  
reg                            lq2_unaligned_r;  
reg                            lq2_ex_r;  
reg                            lq2_llock_r;  
reg [`npuarc_DMP_FIFO_RANGE]          lq2_dep_r;
reg                            lq3_cmd_cg0;
reg                            lq3_cmd_cg1;

reg [`npuarc_PADDR_RANGE]             lq3_addr_nxt;
reg [`npuarc_PADDR_RANGE]             lq3_addr1_nxt;
reg  [1:0]                     lq3_size_nxt;  
reg                            lq3_sex_nxt;  
reg                            lq3_user_mode_nxt;  
reg [`npuarc_GRAD_TAG_RANGE]          lq3_tag_nxt;  
reg [`npuarc_DMP_TARGET_RANGE]        lq3_target_nxt;  
reg                            lq3_unaligned_nxt;  
reg                            lq3_ex_nxt;  
reg                            lq3_llock_nxt;  
  
reg [`npuarc_PADDR_RANGE]             lq3_addr_r;
reg [`npuarc_PADDR_RANGE]             lq3_addr1_r;
reg  [1:0]                     lq3_size_r;  
reg                            lq3_sex_r;  
reg                            lq3_user_mode_r;  
reg [`npuarc_GRAD_TAG_RANGE]          lq3_tag_r;  
reg [`npuarc_DMP_TARGET_RANGE]        lq3_target_r;  
reg                            lq3_unaligned_r;  
reg                            lq3_ex_r;  
reg                            lq3_llock_r;  
reg [`npuarc_DMP_FIFO_RANGE]          lq3_dep_r;


reg [`npuarc_DMP_FIFO_RANGE]          lq_strict_order_r;
reg [`npuarc_DMP_FIFO_RANGE]          lq_order_ptr_r;
reg [`npuarc_DMP_FIFO_RANGE]          lq0_wq_dep_r;
reg [`npuarc_DMP_FIFO_RANGE]          lq1_wq_dep_r;
reg [`npuarc_DMP_FIFO_RANGE]          lq2_wq_dep_r;
reg [`npuarc_DMP_FIFO_RANGE]          lq3_wq_dep_r;

// Module definition

///////////////////////////////////////////////////////////////////////////////
// This module hides the latency of the memory subsystem by queing incoming
// loads requests without blocking the pipeline.Command and data transfers are 
// decoupled, allowing for multiple outstanding transactions in the memory 
// system, as long as it is suported by the external bus protocol.
// The commands are sent out in the same order they entered into the load
// queue. The  command are transferred when they are accepted (ack) by the 
// memory system.
// 
///////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to determine the next values of the circular cmd FIFO
//
//////////////////////////////////////////////////////////////////////////////

always @*
begin : lq0_addr_nxt_PROC
  // Clock gate enable for this entry
  //
  lq0_cmd_cg0              = 1'b0;
  lq0_cmd_cg1              = ca_load_r;
  
  // Default assignments
  //
  lq0_addr_nxt             = lq0_addr_r;
  lq0_addr1_nxt            = lq0_addr1_r;
  lq0_size_nxt             = lq0_size_r;  
  lq0_sex_nxt              = lq0_sex_r;  
  lq0_user_mode_nxt        = lq0_user_mode_r;  
  lq0_tag_nxt              = lq0_tag_r;  
  lq0_target_nxt           = lq0_target_r;  
  lq0_unaligned_nxt        = lq0_unaligned_r;
  lq0_ex_nxt               = lq0_ex_r;
  lq0_llock_nxt            = lq0_llock_r;  
  
  if (  lq_fifo_push 
      & lq_cmd_wr_ptr_1h[0])
  begin
    // Turn on the clock
    //
    lq0_cmd_cg0             = ca_pass;
    
    // New cmd entry being written
    //
    lq0_addr_nxt            = ca_mem_addr0_r;
    lq0_addr1_nxt           = ca_mem_addr1_r;
    lq0_addr1_nxt[2:0]      = 3'b000;

    lq0_size_nxt            = ca_size_r;   
    lq0_sex_nxt             = ca_sex_r;    
    lq0_user_mode_nxt       = ca_user_mode_r;    
    lq0_tag_nxt             = ca_grad_tag;  
    lq0_target_nxt          = dc4_target_r;  
    lq0_unaligned_nxt       = dc4_unaligned;
    lq0_ex_nxt              = ca_load_r & ca_store_r;
    lq0_llock_nxt           = ca_load_r & ca_locked_r;  
  end
end

always @*
begin : lq1_addr_nxt_PROC
  // Clock gate enable for this entry
  //
  lq1_cmd_cg0              = 1'b0;
  lq1_cmd_cg1              = ca_load_r;
  
  // Default assignments
  //
  lq1_addr_nxt             = lq1_addr_r;
  lq1_addr1_nxt            = lq1_addr1_r;
  lq1_size_nxt             = lq1_size_r;  
  lq1_sex_nxt              = lq1_sex_r;  
  lq1_user_mode_nxt        = lq1_user_mode_r;  
  lq1_tag_nxt              = lq1_tag_r;  
  lq1_target_nxt           = lq1_target_r;  
  lq1_unaligned_nxt        = lq1_unaligned_r;
  lq1_ex_nxt               = lq1_ex_r;
  lq1_llock_nxt            = lq1_llock_r;  
  
  if (  lq_fifo_push 
      & lq_cmd_wr_ptr_1h[1])
  begin
    // Turn on the clock
    //
    lq1_cmd_cg0             = ca_pass;
    
    // New cmd entry being written
    //
    lq1_addr_nxt            = ca_mem_addr0_r;
    lq1_addr1_nxt           = ca_mem_addr1_r;
    lq1_addr1_nxt[2:0]      = 3'b000;

    lq1_size_nxt            = ca_size_r;   
    lq1_sex_nxt             = ca_sex_r;    
    lq1_user_mode_nxt       = ca_user_mode_r;    
    lq1_tag_nxt             = ca_grad_tag;  
    lq1_target_nxt          = dc4_target_r;  
    lq1_unaligned_nxt       = dc4_unaligned;
    lq1_ex_nxt              = ca_load_r & ca_store_r;
    lq1_llock_nxt           = ca_load_r & ca_locked_r;  
  end
end

always @*
begin : lq2_addr_nxt_PROC
  // Clock gate enable for this entry
  //
  lq2_cmd_cg0              = 1'b0;
  lq2_cmd_cg1              = ca_load_r;
  
  // Default assignments
  //
  lq2_addr_nxt             = lq2_addr_r;
  lq2_addr1_nxt            = lq2_addr1_r;
  lq2_size_nxt             = lq2_size_r;  
  lq2_sex_nxt              = lq2_sex_r;  
  lq2_user_mode_nxt        = lq2_user_mode_r;  
  lq2_tag_nxt              = lq2_tag_r;  
  lq2_target_nxt           = lq2_target_r;  
  lq2_unaligned_nxt        = lq2_unaligned_r;
  lq2_ex_nxt               = lq2_ex_r;
  lq2_llock_nxt            = lq2_llock_r;  
  
  if (  lq_fifo_push 
      & lq_cmd_wr_ptr_1h[2])
  begin
    // Turn on the clock
    //
    lq2_cmd_cg0             = ca_pass;
    
    // New cmd entry being written
    //
    lq2_addr_nxt            = ca_mem_addr0_r;
    lq2_addr1_nxt           = ca_mem_addr1_r;
    lq2_addr1_nxt[2:0]      = 3'b000;

    lq2_size_nxt            = ca_size_r;   
    lq2_sex_nxt             = ca_sex_r;    
    lq2_user_mode_nxt       = ca_user_mode_r;    
    lq2_tag_nxt             = ca_grad_tag;  
    lq2_target_nxt          = dc4_target_r;  
    lq2_unaligned_nxt       = dc4_unaligned;
    lq2_ex_nxt              = ca_load_r & ca_store_r;
    lq2_llock_nxt           = ca_load_r & ca_locked_r;  
  end
end

always @*
begin : lq3_addr_nxt_PROC
  // Clock gate enable for this entry
  //
  lq3_cmd_cg0              = 1'b0;
  lq3_cmd_cg1              = ca_load_r;
  
  // Default assignments
  //
  lq3_addr_nxt             = lq3_addr_r;
  lq3_addr1_nxt            = lq3_addr1_r;
  lq3_size_nxt             = lq3_size_r;  
  lq3_sex_nxt              = lq3_sex_r;  
  lq3_user_mode_nxt        = lq3_user_mode_r;  
  lq3_tag_nxt              = lq3_tag_r;  
  lq3_target_nxt           = lq3_target_r;  
  lq3_unaligned_nxt        = lq3_unaligned_r;
  lq3_ex_nxt               = lq3_ex_r;
  lq3_llock_nxt            = lq3_llock_r;  
  
  if (  lq_fifo_push 
      & lq_cmd_wr_ptr_1h[3])
  begin
    // Turn on the clock
    //
    lq3_cmd_cg0             = ca_pass;
    
    // New cmd entry being written
    //
    lq3_addr_nxt            = ca_mem_addr0_r;
    lq3_addr1_nxt           = ca_mem_addr1_r;
    lq3_addr1_nxt[2:0]      = 3'b000;

    lq3_size_nxt            = ca_size_r;   
    lq3_sex_nxt             = ca_sex_r;    
    lq3_user_mode_nxt       = ca_user_mode_r;    
    lq3_tag_nxt             = ca_grad_tag;  
    lq3_target_nxt          = dc4_target_r;  
    lq3_unaligned_nxt       = dc4_unaligned;
    lq3_ex_nxt              = ca_load_r & ca_store_r;
    lq3_llock_nxt           = ca_load_r & ca_locked_r;  
  end
end


//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to determine the write pointer
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lq_cmd_wr_ptr_PROC
  integer i;
  reg     f;
  
  // Default values
  //
  lq_cmd_wr_ptr_1h = {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  lq_cmd_wr_ptr    = {`npuarc_LQ_PTR_DEPTH{1'b0}};
  f                = 1'b0;
  
  // Find first available entry
  //  
  for (i = 0; i < `npuarc_DMP_FIFO_DEPTH; i = i+1)
  begin
    if (    (lq_valid_r[i] == 1'b0)
         && (!f))
    begin
      lq_cmd_wr_ptr_1h[i] = 1'b1;
      lq_cmd_wr_ptr       = $unsigned(i);
      f                   = 1'b1;
    end
  end
end

//////////////////////////////////////////////////////////////////////////////
// Dependency matrix- handy vectors
//
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DMP_FIFO_RANGE] lq_wq_dep_r;
always @*
begin : lq_wq_dep_handy_PROC
  // This is the row of the LQ-WQ dependency matrix 
  //
  lq_wq_dep_r[0] = | lq0_wq_dep_r;
  lq_wq_dep_r[1] = | lq1_wq_dep_r;
  lq_wq_dep_r[2] = | lq2_wq_dep_r;
  lq_wq_dep_r[3] = | lq3_wq_dep_r;
end

reg [`npuarc_DMP_FIFO_RANGE] lq_dep_r;
always @*
begin : lq_dep_handy_PROC
  // This is the row of the LQ dependency matrix 
  //
  lq_dep_r[0] = | lq0_dep_r;
  lq_dep_r[1] = | lq1_dep_r;
  lq_dep_r[2] = | lq2_dep_r;
  lq_dep_r[3] = | lq3_dep_r;
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to determine the command read pointer
//
//////////////////////////////////////////////////////////////////////////////
reg                 lq_cmd_valid;
reg                 lq_cmd_pend_set;
reg                 lq_cmd_pend_r;
reg [`npuarc_LQ_PTR_RANGE] lq_cmd_pend_entry_r;
reg [`npuarc_LQ_PTR_RANGE] lq_cmd_pend_entry_nxt;

always @*
begin : lq_cmd_rd_ptr_PROC
  integer i;
  reg     f;
  
  // Default values
  //
  lq_cmd_pend_set       = 1'b0;
  lq_cmd_pend_entry_nxt = lq_cmd_pend_entry_r;
  lq_cmd_rd_ptr         = lq_cmd_pend_entry_r;
  lq_cmd_valid          = lq_cmd_pend_r;
  f                     = 1'b0;

  // Find first valid entry that is not out on the IBP bus, that do not depend on 
  // any other entry
  //  
  for (i = 0; i < `npuarc_DMP_FIFO_DEPTH; i = i+1)
  begin
    if (    (lq_valid_r[i]  == 1'b1)
         && (lq_out_r[i]    == 1'b0)
         && (lq_dep_r[i]    == 1'b0)
         && (lq_wq_dep_r[i] == 1'b0)
         && (lq_cmd_pend_r  == 1'b0)
         && (!f))
    begin
      lq_cmd_rd_ptr            = $unsigned(i);
      lq_cmd_pend_set          = 1'b1;
      lq_cmd_pend_entry_nxt    = $unsigned(i);
      lq_cmd_valid             = 1'b1;
      f                        = 1'b1;
    end
  end
end

//////////////////////////////////////////////////////////////////////////////
// @
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lq_valid_nxt_PROC
  // Default value
  //
  lq_valid_cg0 = 1'b0;
  lq_valid_nxt = lq_valid_r;
  
  case ({lq_fifo_data_pop, lq_fifo_push})
  2'b0_1:
  begin
    // Only write. Make the entry that is being written valid and keep
    // the other valid entries intact
    //
    lq_valid_cg0                 = ca_pass;
    lq_valid_nxt                 = lq_valid_r | lq_cmd_wr_ptr_1h;
  end  
  
  2'b1_0:
  begin
    // Only read. Make the entry that is being read invalid and keep
    // the other valid entries intact
    //
    lq_valid_cg0                 = 1'b1;
    lq_valid_nxt                 = lq_valid_r;
    lq_valid_nxt[lq_data_rd_ptr] = 1'b0;
  end
  
  2'b1_1:
  begin
    // Combination of the two cases above.Set a new valid entry (1) and 
    // remove the entry just read (2).  
    //
    lq_valid_cg0                 = 1'b1;
    lq_valid_nxt                 = lq_valid_r;
    lq_valid_nxt[lq_cmd_wr_ptr]  = 1'b1;
    lq_valid_nxt[lq_data_rd_ptr] = 1'b0;
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept   
  default:
    ;
// spyglass enable_block W193  
  endcase  
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to report the top of the cmd FIFO
//
//////////////////////////////////////////////////////////////////////////////

always @*
begin : lq_fifo_cmd_valid_PROC
  lq_fifo_cmd_valid      = 1'b0;
  lq_fifo_cmd_addr       = {`npuarc_PADDR_SIZE{1'b0}};
  lq_fifo_cmd_addr1      = {`npuarc_PADDR_SIZE{1'b0}};
  lq_fifo_cmd_unaligned  = 1'b0;
  lq_fifo_cmd_target     = {`npuarc_DMP_TARGET_BITS{1'b0}}; 
  lq_fifo_cmd_ex         = 1'b0;
  lq_fifo_cmd_llock      = 1'b0;
  lq_fifo_cmd_data_size  = 2'd0;
  lq_fifo_cmd_user_mode  = 1'b0;
  
  // When a command has been sent out on the IBP bus, we should not
  // re-send it. 
  //   
  case (lq_cmd_rd_ptr)
  `npuarc_LQ_PTR_DEPTH'd0:
  begin
    lq_fifo_cmd_valid      = lq_cmd_valid; 
    lq_fifo_cmd_addr       = lq0_addr_r;
    lq_fifo_cmd_addr1      = lq0_addr1_r;
    lq_fifo_cmd_unaligned  = lq0_unaligned_r;
    lq_fifo_cmd_target     = lq0_target_r;
    lq_fifo_cmd_ex         = lq0_ex_r;
    lq_fifo_cmd_llock      = lq0_llock_r;
    lq_fifo_cmd_data_size  = lq0_size_r;
    lq_fifo_cmd_user_mode  = lq0_user_mode_r;
  end
  `npuarc_LQ_PTR_DEPTH'd1:
  begin
    lq_fifo_cmd_valid      = lq_cmd_valid; 
    lq_fifo_cmd_addr       = lq1_addr_r;
    lq_fifo_cmd_addr1      = lq1_addr1_r;
    lq_fifo_cmd_unaligned  = lq1_unaligned_r;
    lq_fifo_cmd_target     = lq1_target_r;
    lq_fifo_cmd_ex         = lq1_ex_r;
    lq_fifo_cmd_llock      = lq1_llock_r;
    lq_fifo_cmd_data_size  = lq1_size_r;
    lq_fifo_cmd_user_mode  = lq1_user_mode_r;
  end
  `npuarc_LQ_PTR_DEPTH'd2:
  begin
    lq_fifo_cmd_valid      = lq_cmd_valid; 
    lq_fifo_cmd_addr       = lq2_addr_r;
    lq_fifo_cmd_addr1      = lq2_addr1_r;
    lq_fifo_cmd_unaligned  = lq2_unaligned_r;
    lq_fifo_cmd_target     = lq2_target_r;
    lq_fifo_cmd_ex         = lq2_ex_r;
    lq_fifo_cmd_llock      = lq2_llock_r;
    lq_fifo_cmd_data_size  = lq2_size_r;
    lq_fifo_cmd_user_mode  = lq2_user_mode_r;
  end
  `npuarc_LQ_PTR_DEPTH'd3:
  begin
    lq_fifo_cmd_valid      = lq_cmd_valid; 
    lq_fifo_cmd_addr       = lq3_addr_r;
    lq_fifo_cmd_addr1      = lq3_addr1_r;
    lq_fifo_cmd_unaligned  = lq3_unaligned_r;
    lq_fifo_cmd_target     = lq3_target_r;
    lq_fifo_cmd_ex         = lq3_ex_r;
    lq_fifo_cmd_llock      = lq3_llock_r;
    lq_fifo_cmd_data_size  = lq3_size_r;
    lq_fifo_cmd_user_mode  = lq3_user_mode_r;
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default:
    ;
// spyglass enable_block W193
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to report the top of the data FIFO
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lq_fifo_data_size_PROC
  lq_fifo_data_size      = 2'b00;    
  lq_fifo_data_target    = {`npuarc_DMP_TARGET_BITS{1'b0}};    
  lq_fifo_data_sex       = 1'b0;      
  lq_fifo_addr           = {`npuarc_PADDR_SIZE{1'b0}};   
  lq_fifo_grad_tag       = {`npuarc_GRAD_TAG_BITS{1'b0}};  
  lq_fifo_unaligned      = 1'b0; 
  lq_fifo_data_llock     = 1'b0;
  lq_fifo_data_user_mode = 1'b0;
  
  case (lq_data_rd_ptr)
  `npuarc_LQ_PTR_DEPTH'd0:
  begin
    lq_fifo_data_size      = lq0_size_r;           
    lq_fifo_data_target    = lq0_target_r;           
    lq_fifo_data_sex       = lq0_sex_r;             
    lq_fifo_addr           = lq0_addr_r;   
    lq_fifo_grad_tag       = lq0_tag_r;   
    lq_fifo_unaligned      = lq0_unaligned_r;
    lq_fifo_data_llock     = lq0_llock_r;
    lq_fifo_data_user_mode = lq0_user_mode_r; 
  end
  
  `npuarc_LQ_PTR_DEPTH'd1:
  begin
    lq_fifo_data_size      = lq1_size_r;           
    lq_fifo_data_target    = lq1_target_r;           
    lq_fifo_data_sex       = lq1_sex_r;             
    lq_fifo_addr           = lq1_addr_r;   
    lq_fifo_grad_tag       = lq1_tag_r;   
    lq_fifo_unaligned      = lq1_unaligned_r;
    lq_fifo_data_llock     = lq1_llock_r;
    lq_fifo_data_user_mode = lq1_user_mode_r; 
  end
  
  `npuarc_LQ_PTR_DEPTH'd2:
  begin
    lq_fifo_data_size      = lq2_size_r;           
    lq_fifo_data_target    = lq2_target_r;           
    lq_fifo_data_sex       = lq2_sex_r;             
    lq_fifo_addr           = lq2_addr_r;   
    lq_fifo_grad_tag       = lq2_tag_r;   
    lq_fifo_unaligned      = lq2_unaligned_r;
    lq_fifo_data_llock     = lq2_llock_r;
    lq_fifo_data_user_mode = lq2_user_mode_r; 
  end
  
  `npuarc_LQ_PTR_DEPTH'd3:
  begin
    lq_fifo_data_size      = lq3_size_r;           
    lq_fifo_data_target    = lq3_target_r;           
    lq_fifo_data_sex       = lq3_sex_r;             
    lq_fifo_addr           = lq3_addr_r;   
    lq_fifo_grad_tag       = lq3_tag_r;   
    lq_fifo_unaligned      = lq3_unaligned_r;
    lq_fifo_data_llock     = lq3_llock_r;
    lq_fifo_data_user_mode = lq3_user_mode_r; 
  end
  
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default:
    ;
// spyglass enable_block W193
  endcase
end

//////////////////////////////////////////////////////////////////////////////
// On the fly generation of (partial) LQ addr1  (for WAR detection
// on unaligned loads) 
//
//////////////////////////////////////////////////////////////////////////////
reg [15:0] lq0_addr1;
reg [15:0] lq1_addr1;
reg [15:0] lq2_addr1;
reg [15:0] lq3_addr1;

// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
always @*
begin : lq_addr1_PROC
  lq0_addr1 = lq0_addr_r[19:4] + 1'b1;
  lq1_addr1 = lq1_addr_r[19:4] + 1'b1;
  lq2_addr1 = lq2_addr_r[19:4] + 1'b1;
  lq3_addr1 = lq3_addr_r[19:4] + 1'b1;
end
// leda W484 on
// leda B_3200 on
// leda BTTF_D002 on

//////////////////////////////////////////////////////////////////////////////
// Address matching for WAR hazard
//
//////////////////////////////////////////////////////////////////////////////

reg                    dc4_target_external;

reg                    dc40_war_addr0_match;
reg                    dc40_war_addr1_match;
reg                    dc41_war_addr0_match;

reg                    dc40_war_addr0_conflict;
reg                    dc40_war_addr1_conflict;
reg                    dc41_war_addr0_conflict;

reg                    lq0_load0_war_addr0_match;
reg                    lq0_load0_war_addr1_match;
reg                    lq0_load1_war_addr0_match;

reg                    lq0_load0_war_addr0_conflict;
reg                    lq0_load0_war_addr1_conflict;
reg                    lq0_load1_war_addr0_conflict;
reg                    lq1_load0_war_addr0_match;
reg                    lq1_load0_war_addr1_match;
reg                    lq1_load1_war_addr0_match;

reg                    lq1_load0_war_addr0_conflict;
reg                    lq1_load0_war_addr1_conflict;
reg                    lq1_load1_war_addr0_conflict;
reg                    lq2_load0_war_addr0_match;
reg                    lq2_load0_war_addr1_match;
reg                    lq2_load1_war_addr0_match;

reg                    lq2_load0_war_addr0_conflict;
reg                    lq2_load0_war_addr1_conflict;
reg                    lq2_load1_war_addr0_conflict;
reg                    lq3_load0_war_addr0_match;
reg                    lq3_load0_war_addr1_match;
reg                    lq3_load1_war_addr0_match;

reg                    lq3_load0_war_addr0_conflict;
reg                    lq3_load0_war_addr1_conflict;
reg                    lq3_load1_war_addr0_conflict;

always @*
begin : dc40_war_addr0_match_PROC
  // Compare the DC3 memory address with the addresses in DC4
  // and in the LQ. x3 is a store, ca/dc4 is a load
  
  // Check the CA load targets external memory
  //
  dc4_target_external     =   (dc4_target_r != `npuarc_DMP_TARGET_DCCM)
                            & (dc4_target_r != `npuarc_DMP_TARGET_DC);
  
  // Load0 against store0
  // 
  dc40_war_addr0_match    = (   x3_mem_addr0_r[19:4] 
                             == ca_mem_addr0_r[19:4]);
  
  // Load0 against store1
  // 
  dc40_war_addr1_match    = (   x3_mem_addr1_r[19:4] 
                             == ca_mem_addr0_r[19:4]);

  // Load1 against store0
  // 
  dc41_war_addr0_match    = (   x3_mem_addr0_r[19:4] 
                             == ca_mem_addr1_r[19:4]);
  
  dc40_war_addr0_conflict =  dc40_war_addr0_match
                         & x3_store_r
                         & ca_load_r
                         & (dc3_target_r == dc4_target_r)
                         & dc4_target_external;
  
  dc40_war_addr1_conflict =  dc40_war_addr1_match
                         & x3_store_r
                         & dc3_bank_sel_r[3]
                         & dc3_bank_sel_r[0]
                         & ca_load_r
                         & (dc3_target_r == dc4_target_r)
                         & dc4_target_external;
  
  dc41_war_addr0_conflict =  dc41_war_addr0_match
                         & x3_store_r
                         & ca_load_r
                         & dc4_bank_sel_r[3]
                         & dc4_bank_sel_r[0]
                         & (dc3_target_r == dc4_target_r)
                         & dc4_target_external;
  
  lq0_load0_war_addr0_match = (    x3_mem_addr0_r[19:4] 
                                  == lq0_addr_r[19:4]);
  
  lq0_load0_war_addr1_match = (    x3_mem_addr1_r[19:4] 
                                  == lq0_addr_r[19:4]);
  
  lq0_load1_war_addr0_match = (    x3_mem_addr0_r[19:4] 
                                  == lq0_addr1[15:0]);
  

  lq0_load0_war_addr0_conflict =   lq0_load0_war_addr0_match
                                    & x3_store_r
                                    & lq_valid_r[0]
                                    & (dc3_target_r == lq0_target_r);
                                   
  lq0_load0_war_addr1_conflict =   lq0_load0_war_addr1_match
                                    & x3_store_r
                                    & dc3_bank_sel_r[3]
                                    & dc3_bank_sel_r[0]
                                    & lq_valid_r[0]
                                    & (dc3_target_r == lq0_target_r);
                                    
  lq0_load1_war_addr0_conflict =   lq0_load1_war_addr0_match
                                    & x3_store_r
                                    & lq0_unaligned_r
                                    & lq0_addr_r[3]
                                    & lq_valid_r[0]
                                    & (dc3_target_r == lq0_target_r);
  lq1_load0_war_addr0_match = (    x3_mem_addr0_r[19:4] 
                                  == lq1_addr_r[19:4]);
  
  lq1_load0_war_addr1_match = (    x3_mem_addr1_r[19:4] 
                                  == lq1_addr_r[19:4]);
  
  lq1_load1_war_addr0_match = (    x3_mem_addr0_r[19:4] 
                                  == lq1_addr1[15:0]);
  

  lq1_load0_war_addr0_conflict =   lq1_load0_war_addr0_match
                                    & x3_store_r
                                    & lq_valid_r[1]
                                    & (dc3_target_r == lq1_target_r);
                                   
  lq1_load0_war_addr1_conflict =   lq1_load0_war_addr1_match
                                    & x3_store_r
                                    & dc3_bank_sel_r[3]
                                    & dc3_bank_sel_r[0]
                                    & lq_valid_r[1]
                                    & (dc3_target_r == lq1_target_r);
                                    
  lq1_load1_war_addr0_conflict =   lq1_load1_war_addr0_match
                                    & x3_store_r
                                    & lq1_unaligned_r
                                    & lq1_addr_r[3]
                                    & lq_valid_r[1]
                                    & (dc3_target_r == lq1_target_r);
  lq2_load0_war_addr0_match = (    x3_mem_addr0_r[19:4] 
                                  == lq2_addr_r[19:4]);
  
  lq2_load0_war_addr1_match = (    x3_mem_addr1_r[19:4] 
                                  == lq2_addr_r[19:4]);
  
  lq2_load1_war_addr0_match = (    x3_mem_addr0_r[19:4] 
                                  == lq2_addr1[15:0]);
  

  lq2_load0_war_addr0_conflict =   lq2_load0_war_addr0_match
                                    & x3_store_r
                                    & lq_valid_r[2]
                                    & (dc3_target_r == lq2_target_r);
                                   
  lq2_load0_war_addr1_conflict =   lq2_load0_war_addr1_match
                                    & x3_store_r
                                    & dc3_bank_sel_r[3]
                                    & dc3_bank_sel_r[0]
                                    & lq_valid_r[2]
                                    & (dc3_target_r == lq2_target_r);
                                    
  lq2_load1_war_addr0_conflict =   lq2_load1_war_addr0_match
                                    & x3_store_r
                                    & lq2_unaligned_r
                                    & lq2_addr_r[3]
                                    & lq_valid_r[2]
                                    & (dc3_target_r == lq2_target_r);
  lq3_load0_war_addr0_match = (    x3_mem_addr0_r[19:4] 
                                  == lq3_addr_r[19:4]);
  
  lq3_load0_war_addr1_match = (    x3_mem_addr1_r[19:4] 
                                  == lq3_addr_r[19:4]);
  
  lq3_load1_war_addr0_match = (    x3_mem_addr0_r[19:4] 
                                  == lq3_addr1[15:0]);
  

  lq3_load0_war_addr0_conflict =   lq3_load0_war_addr0_match
                                    & x3_store_r
                                    & lq_valid_r[3]
                                    & (dc3_target_r == lq3_target_r);
                                   
  lq3_load0_war_addr1_conflict =   lq3_load0_war_addr1_match
                                    & x3_store_r
                                    & dc3_bank_sel_r[3]
                                    & dc3_bank_sel_r[0]
                                    & lq_valid_r[3]
                                    & (dc3_target_r == lq3_target_r);
                                    
  lq3_load1_war_addr0_conflict =   lq3_load1_war_addr0_match
                                    & x3_store_r
                                    & lq3_unaligned_r
                                    & lq3_addr_r[3]
                                    & lq_valid_r[3]
                                    & (dc3_target_r == lq3_target_r);
  
end

//////////////////////////////////////////////////////////////////////////////
// Set-up a dc3 war hazard.
//
//////////////////////////////////////////////////////////////////////////////
reg                    dc3_ca_war_hazard;
reg [`npuarc_DMP_FIFO_RANGE]  dc3_ca_war_hazard_entry;

reg [`npuarc_DMP_FIFO_RANGE]  dc3_lq_war_hazard_entries;

reg [`npuarc_DMP_FIFO_RANGE]  dc3_war_hazard_entries_prel;
reg [`npuarc_DMP_FIFO_RANGE]  dc3_war_hazard_entries;

reg                    dc4_setup_war_hazard_cg0;

always @*
begin : dc3_war_hazard_PROC
  // WAR hazard involving a X3 store and a CA load. Note this only exist if the
  // CA load indeed graduates and makes into the LQ.
  // 
  dc3_ca_war_hazard  =     lq_fifo_push
                       & (  dc40_war_addr0_conflict
                          | dc40_war_addr1_conflict
                          | dc41_war_addr0_conflict);
                 
  // This vector registers the LQ entry that the store *will* be dependent upon. 
  // This strict hazard can not be resolved in CA as this load can't be put 
  // into the LQ and retired the same time
  //  
  dc3_ca_war_hazard_entry  =  lq_cmd_wr_ptr_1h
                            & {`npuarc_DMP_FIFO_DEPTH{dc3_ca_war_hazard}}
                            & {`npuarc_DMP_FIFO_DEPTH{ca_pass}};
  
  
  // This vector register the LQ entries that the store *is*  dependent upon. 
  // WAR hazard involving a X3 store and a LQ entry. 
  //
  dc3_lq_war_hazard_entries[0] =   lq0_load0_war_addr0_conflict
                                 | lq0_load0_war_addr1_conflict
                                 | lq0_load1_war_addr0_conflict;
                                 
  dc3_lq_war_hazard_entries[1] =   lq1_load0_war_addr0_conflict
                                 | lq1_load0_war_addr1_conflict
                                 | lq1_load1_war_addr0_conflict;
                                 
  dc3_lq_war_hazard_entries[2] =   lq2_load0_war_addr0_conflict
                                 | lq2_load0_war_addr1_conflict
                                 | lq2_load1_war_addr0_conflict;
                                 
  dc3_lq_war_hazard_entries[3] =   lq3_load0_war_addr0_conflict
                                 | lq3_load0_war_addr1_conflict
                                 | lq3_load1_war_addr0_conflict;
                                 
  
  // Create a single hazard vector. WAR dependendencies against loads in CA
  // and in the LQ
  //
  dc3_war_hazard_entries_prel = dc3_ca_war_hazard_entry 
                              | dc3_lq_war_hazard_entries;
  
  // Exclude from this vector any entry that is retiring while the dependent
  // ST is in X3
  //
  dc3_war_hazard_entries = dc3_war_hazard_entries_prel;
  
  if (lq_fifo_data_pop) 
  begin
    dc3_war_hazard_entries[lq_data_rd_ptr] = 1'b0;
  end
  
  // Clock gate
  //
  dc4_setup_war_hazard_cg0 = x3_store_r & x3_pass;
end

//////////////////////////////////////////////////////////////////////////////
// Set-up a CA WAR hazard
//
//////////////////////////////////////////////////////////////////////////////
reg                    dc4_update_war_hazard_cg0;
reg [`npuarc_DMP_FIFO_RANGE]  dc4_war_hazard_entries_prel_r;
reg [`npuarc_DMP_FIFO_RANGE]  dc4_war_hazard_entries_prel_nxt;

reg [`npuarc_DMP_FIFO_RANGE]  dc4_war_hazard_entries;

reg                    dc4_ex_external;
always @*
begin : dc4_war_hazard_PROC
  // This is the WAR entries between a CA store and the LQ. By default, assign to
  // the entries we set-up while the store was in X3. This default value needs to be
  // updated whenever the LQ retires an entry. 
  //
  dc4_war_hazard_entries_prel_nxt = dc4_war_hazard_entries_prel_r;
  dc4_war_hazard_entries          = dc4_war_hazard_entries_prel_r;
  
  dc4_update_war_hazard_cg0       = 1'b0;
  
  // Exclude from this vector any LQ entry that is retiring while the ST is in
  // CA
  //
  if (lq_data_retire) 
  begin
    dc4_update_war_hazard_cg0                       = 1'b1;
    dc4_war_hazard_entries_prel_nxt[lq_data_rd_ptr] = 1'b0;
    dc4_war_hazard_entries[lq_data_rd_ptr]          = 1'b0;
  end
  
  // The EX instruction creates an implicit war hazard against the LQ entry
  // we are about to write to.
  //
  dc4_ex_external = ca_load_r & ca_store_r & dc4_target_external;
  
  // We have a WAR hazard when the CA store depenends on *any* entry of the LQ
  // Furtheremore, an external EX instruction also creates an implicit WAR
  // hazard, as the load part of the exchange needs to retire before the 
  // store part of the exchange can be sent out.
  //
  dc4_war_hazard =    dc4_ex_external
                   | (| dc4_war_hazard_entries);  
end

//////////////////////////////////////////////////////////////////////////////
// lq_order_ptr_1h is a 1-hot encoded vector that points to the most recent 
// external entry written in the LQ.
//
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DMP_FIFO_RANGE] lq_maintain_order;
reg [`npuarc_DMP_FIFO_RANGE] lq_order_ptr_1h_prel;
always @*
begin : lq_order_ptr_1h_PROC
  // We need to maintain ordering for strict volatile reads or for reads that 
  // are not out on the bus yet
  //
  lq_maintain_order =   (lq_valid_r & lq_strict_order_r)
                      | (~lq_out_r);
  
  // The order is only relevant for external  targets that are not yet out
  // on the IBP bus. We need to guarantee  ordering when there is an 
  // explicit WAR hazard.
  //
  lq_order_ptr_1h_prel =   (  lq_valid_r   // all LQ entries are external
                            & lq_maintain_order)
                        | dc4_war_hazard_entries;
  
  
  // Default assignment
  //
  lq_order_ptr_1h     = lq_order_ptr_1h_prel;
  
  // The EX instruction creates an implicit war hazard against the LQ entry
  // we are about to write.
  //
  if (  ca_load_r
      & ca_store_r
      & dc4_target_external)
  begin
    // Add the LQ entry we are putting the EX into order ptr
    //
    lq_order_ptr_1h = lq_order_ptr_1h_prel | lq_cmd_wr_ptr_1h;
  end
  
end

//////////////////////////////////////////////////////////////////////////////
//  LQ strict ordering
//
//////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DMP_FIFO_RANGE] lq_strict_order;
always @*
begin : lq_strict_order_PROC
  //  A load queue entry being written is strictly ordered when the CA load
  // carries a raw hazard dependency against the WQ
  //
  lq_strict_order[0] =  lq_strict_order_r[0]
                      | (  (dc4_raw_hazard | ca_strict_order_r)
                         & (lq_valid_r[0] == 1'b0)
                         & (lq_cmd_wr_ptr == 2'd0));
                         
  lq_strict_order[1] =  lq_strict_order_r[1]
                      | (  (dc4_raw_hazard | ca_strict_order_r)
                         & (lq_valid_r[1] == 1'b0)
                         & (lq_cmd_wr_ptr == 2'd1));
                         
  lq_strict_order[2] =  lq_strict_order_r[2]
                      | (  (dc4_raw_hazard | ca_strict_order_r)
                         & (lq_valid_r[2] == 1'b0)
                         & (lq_cmd_wr_ptr == 2'd2));
                         
  lq_strict_order[3] =  lq_strict_order_r[3]
                      | (  (dc4_raw_hazard | ca_strict_order_r)
                         & (lq_valid_r[3] == 1'b0)
                         & (lq_cmd_wr_ptr == 2'd3));
                         
end


//////////////////////////////////////////////////////////////////////////////
// Asynchronous  logic to report status
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lq_fifo_status_PROC
  // The load queue gets full the cycke after we write to the last available 
  // entry
  //
  lq_fifo_empty     = ~(| lq_valid_r); 
  lq_fifo_full      = & lq_valid_r; 
  lq_fifo_full_nxt  = & lq_valid_nxt;
end


//////////////////////////////////////////////////////////////////////////////
// Synchronous process for the control of the  FIFO
//
//////////////////////////////////////////////////////////////////////////////

// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions
//
// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions
// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : lq_valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq_valid_r            <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
    lq_volatile_r         <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
    lq_order_ptr_r        <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
    lq_strict_order_r     <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (  lq_fifo_push 
        & ca_pass)
    begin
      lq_valid_r[lq_cmd_wr_ptr]          <= 1'b1;
      lq_volatile_r[lq_cmd_wr_ptr]       <= ca_volatile_r;
      lq_order_ptr_r                     <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
      lq_order_ptr_r[lq_cmd_wr_ptr]      <= 1'b1;
      
      lq_strict_order_r[lq_cmd_wr_ptr]  <= ca_strict_order_r | dc4_raw_hazard;        
    end
    
    if (lq_fifo_data_pop)
    begin
      lq_valid_r[lq_data_rd_ptr]          <= 1'b0;
      lq_volatile_r[lq_data_rd_ptr]       <= 1'b0;
      lq_order_ptr_r[lq_data_rd_ptr]      <= 1'b0;
      lq_strict_order_r[lq_data_rd_ptr]   <= 1'b0;
    end
  end
end


always @(posedge clk or posedge rst_a)
begin : lq_cmd_pend_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq_cmd_pend_r       <= 1'b0;
    lq_cmd_pend_entry_r <= {`npuarc_LQ_PTR_DEPTH{1'b0}};
  end
  else
  begin
    if (lq_cmd_pend_set == 1'b1)
    begin
      lq_cmd_pend_r        <= 1'b1;
      lq_cmd_pend_entry_r  <= lq_cmd_pend_entry_nxt; 
    end
    
    if (lq_fifo_cmd_pop == 1'b1)
    begin
      lq_cmd_pend_r        <= 1'b0;
    end
  end
end
// spyglass disable_block Ac_conv01
// SMD: Convergence
// SJ:  two accessing path is independent path
always @(posedge clk or posedge rst_a)
begin : lq_out_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq_out_r <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (lq_fifo_cmd_pop == 1'b1)
    begin
      lq_out_r[lq_cmd_rd_ptr]  <= 1'b1;
    end
    
    if (lq_fifo_data_pop == 1'b1)
    begin
      lq_out_r[lq_data_rd_ptr] <= 1'b0;
    end
  end
end
// spyglass enable_block Ac_conv01

// VPOST ON
// leda FM_1_7 on
// spyglass enable_block STARC05-2.2.3.3
//////////////////////////////////////////////////////////////////////////////
// Synchronous process for the cmd FIFO entries
//
//////////////////////////////////////////////////////////////////////////////
// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk or posedge rst_a)
begin : lq0_llock_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq0_llock_r      <= 1'b0;  
  end
  else
  begin
    if (lq0_cmd_cg0 == 1'b1)
    begin
      lq0_llock_r    <= lq0_llock_nxt;
    end    
  end
end  
always @(posedge clk)
begin : lq0_addr_reg_PROC
  if (lq0_cmd_cg1 & lq0_cmd_cg0)                                 
  begin                                               
    lq0_addr_r       <= lq0_addr_nxt;           
    lq0_addr1_r      <= lq0_addr1_nxt;    
    lq0_size_r       <= lq0_size_nxt;           
    lq0_sex_r        <= lq0_sex_nxt;            
    lq0_user_mode_r  <= lq0_user_mode_nxt;      
    lq0_tag_r        <= lq0_tag_nxt;            
    lq0_target_r     <= lq0_target_nxt;         
    lq0_unaligned_r  <= lq0_unaligned_nxt;      
    lq0_ex_r         <= lq0_ex_nxt;             
  end                                                 
end
always @(posedge clk or posedge rst_a)
begin : lq1_llock_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq1_llock_r      <= 1'b0;  
  end
  else
  begin
    if (lq1_cmd_cg0 == 1'b1)
    begin
      lq1_llock_r    <= lq1_llock_nxt;
    end    
  end
end  
always @(posedge clk)
begin : lq1_addr_reg_PROC
  if (lq1_cmd_cg1 & lq1_cmd_cg0)                                 
  begin                                               
    lq1_addr_r       <= lq1_addr_nxt;           
    lq1_addr1_r      <= lq1_addr1_nxt;    
    lq1_size_r       <= lq1_size_nxt;           
    lq1_sex_r        <= lq1_sex_nxt;            
    lq1_user_mode_r  <= lq1_user_mode_nxt;      
    lq1_tag_r        <= lq1_tag_nxt;            
    lq1_target_r     <= lq1_target_nxt;         
    lq1_unaligned_r  <= lq1_unaligned_nxt;      
    lq1_ex_r         <= lq1_ex_nxt;             
  end                                                 
end
always @(posedge clk or posedge rst_a)
begin : lq2_llock_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq2_llock_r      <= 1'b0;  
  end
  else
  begin
    if (lq2_cmd_cg0 == 1'b1)
    begin
      lq2_llock_r    <= lq2_llock_nxt;
    end    
  end
end  
always @(posedge clk)
begin : lq2_addr_reg_PROC
  if (lq2_cmd_cg1 & lq2_cmd_cg0)                                 
  begin                                               
    lq2_addr_r       <= lq2_addr_nxt;           
    lq2_addr1_r      <= lq2_addr1_nxt;    
    lq2_size_r       <= lq2_size_nxt;           
    lq2_sex_r        <= lq2_sex_nxt;            
    lq2_user_mode_r  <= lq2_user_mode_nxt;      
    lq2_tag_r        <= lq2_tag_nxt;            
    lq2_target_r     <= lq2_target_nxt;         
    lq2_unaligned_r  <= lq2_unaligned_nxt;      
    lq2_ex_r         <= lq2_ex_nxt;             
  end                                                 
end
always @(posedge clk or posedge rst_a)
begin : lq3_llock_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq3_llock_r      <= 1'b0;  
  end
  else
  begin
    if (lq3_cmd_cg0 == 1'b1)
    begin
      lq3_llock_r    <= lq3_llock_nxt;
    end    
  end
end  
always @(posedge clk)
begin : lq3_addr_reg_PROC
  if (lq3_cmd_cg1 & lq3_cmd_cg0)                                 
  begin                                               
    lq3_addr_r       <= lq3_addr_nxt;           
    lq3_addr1_r      <= lq3_addr1_nxt;    
    lq3_size_r       <= lq3_size_nxt;           
    lq3_sex_r        <= lq3_sex_nxt;            
    lq3_user_mode_r  <= lq3_user_mode_nxt;      
    lq3_tag_r        <= lq3_tag_nxt;            
    lq3_target_r     <= lq3_target_nxt;         
    lq3_unaligned_r  <= lq3_unaligned_nxt;      
    lq3_ex_r         <= lq3_ex_nxt;             
  end                                                 
end
// leda S_1C_R on
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions

//////////////////////////////////////////////////////////////////////////////
// Managing LQ dependency matrix
//
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions
// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : lq0_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq0_dep_r   <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (lq0_cmd_cg0 == 1'b1)  
    begin
      // Setting up dependency matrix
      //
// spyglass disable_block Ac_conv01
// SMD: Synchronizers converging on flop
// SJ:  Synchronized conv signals are independent
      lq0_dep_r <=  lq_order_ptr_r 
                     & (~lq_out_r);
// spyglass enable_block Ac_conv01
    end
    
    if (lq_fifo_cmd_pop == 1'b1)
    begin
      // Clear dependency when command of dependent entryes are accepted.
      //
      lq0_dep_r[lq_cmd_rd_ptr] <= 1'b0;
    end   
  
  end
end

always @(posedge clk or posedge rst_a)
begin : lq1_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq1_dep_r   <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (lq1_cmd_cg0 == 1'b1)  
    begin
      // Setting up dependency matrix
      //
// spyglass disable_block Ac_conv01
// SMD: Synchronizers converging on flop
// SJ:  Synchronized conv signals are independent
      lq1_dep_r <=  lq_order_ptr_r 
                     & (~lq_out_r);
// spyglass enable_block Ac_conv01
    end
    
    if (lq_fifo_cmd_pop == 1'b1)
    begin
      // Clear dependency when command of dependent entryes are accepted.
      //
      lq1_dep_r[lq_cmd_rd_ptr] <= 1'b0;
    end   
  
  end
end

always @(posedge clk or posedge rst_a)
begin : lq2_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq2_dep_r   <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (lq2_cmd_cg0 == 1'b1)  
    begin
      // Setting up dependency matrix
      //
// spyglass disable_block Ac_conv01
// SMD: Synchronizers converging on flop
// SJ:  Synchronized conv signals are independent
      lq2_dep_r <=  lq_order_ptr_r 
                     & (~lq_out_r);
// spyglass enable_block Ac_conv01
    end
    
    if (lq_fifo_cmd_pop == 1'b1)
    begin
      // Clear dependency when command of dependent entryes are accepted.
      //
      lq2_dep_r[lq_cmd_rd_ptr] <= 1'b0;
    end   
  
  end
end

always @(posedge clk or posedge rst_a)
begin : lq3_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq3_dep_r   <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (lq3_cmd_cg0 == 1'b1)  
    begin
      // Setting up dependency matrix
      //
// spyglass disable_block Ac_conv01
// SMD: Synchronizers converging on flop
// SJ:  Synchronized conv signals are independent
      lq3_dep_r <=  lq_order_ptr_r 
                     & (~lq_out_r);
// spyglass enable_block Ac_conv01
    end
    
    if (lq_fifo_cmd_pop == 1'b1)
    begin
      // Clear dependency when command of dependent entryes are accepted.
      //
      lq3_dep_r[lq_cmd_rd_ptr] <= 1'b0;
    end   
  
  end
end

// VPOST ON
//////////////////////////////////////////////////////////////////////////////
//
// Dependency matrix that tracks dependencies between the LQ and WQ.
// LQ entry i depends on WQ entry j when lq[i]_wq_dep_r[j] == 1
// When an entry is placed in the LQ, it depends on the WQ volatile entries 
// that haven't had their command accepted on the IBP bus.
// A dependency is removed when the WQ entry is out on the IBP bus
//
//////////////////////////////////////////////////////////////////////////////
// VPOST OFF
always @(posedge clk or posedge rst_a)
begin : lq0_wq_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq0_wq_dep_r         <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (lq0_cmd_cg0 == 1'b1)
    begin
      // Set up dependency between this LQ entry and last volatile WQ entry
      //
      lq0_wq_dep_r       <= wq_order_ptr_1h;
    end
    
    if (   (lq_valid_r[0] | lq_fifo_push)
         & wq_cmd_read
         & (~lq_strict_order[0]) )
    begin
      // Clear dependency when dependent WQ command has been processed (out on the 
      // IBP bus) and there is no explicit raw hazard for this entry
      //
      lq0_wq_dep_r[wq_rdentry0] <= 1'b0;
    end     
    
    if (  (lq_valid_r[0] | lq_fifo_push)
        & wq_mem_retire)
    begin
      // A LQ entry that has a strict dependency with a WQ entry needs to be serialized.
      // This implies the depenency is only cleared when the WQ entry retires. (wr_done)
      // 
      lq0_wq_dep_r[wq_mem_entry_id]  <= 1'b0;
    end

  
  
  
  
  end
end


always @(posedge clk or posedge rst_a)
begin : lq1_wq_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq1_wq_dep_r         <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (lq1_cmd_cg0 == 1'b1)
    begin
      // Set up dependency between this LQ entry and last volatile WQ entry
      //
      lq1_wq_dep_r       <= wq_order_ptr_1h;
    end
    
    if (   (lq_valid_r[1] | lq_fifo_push)
         & wq_cmd_read
         & (~lq_strict_order[1]) )
    begin
      // Clear dependency when dependent WQ command has been processed (out on the 
      // IBP bus) and there is no explicit raw hazard for this entry
      //
      lq1_wq_dep_r[wq_rdentry0] <= 1'b0;
    end     
    
    if (  (lq_valid_r[1] | lq_fifo_push)
        & wq_mem_retire)
    begin
      // A LQ entry that has a strict dependency with a WQ entry needs to be serialized.
      // This implies the depenency is only cleared when the WQ entry retires. (wr_done)
      // 
      lq1_wq_dep_r[wq_mem_entry_id]  <= 1'b0;
    end

  
  
  
  
  end
end


always @(posedge clk or posedge rst_a)
begin : lq2_wq_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq2_wq_dep_r         <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (lq2_cmd_cg0 == 1'b1)
    begin
      // Set up dependency between this LQ entry and last volatile WQ entry
      //
      lq2_wq_dep_r       <= wq_order_ptr_1h;
    end
    
    if (   (lq_valid_r[2] | lq_fifo_push)
         & wq_cmd_read
         & (~lq_strict_order[2]) )
    begin
      // Clear dependency when dependent WQ command has been processed (out on the 
      // IBP bus) and there is no explicit raw hazard for this entry
      //
      lq2_wq_dep_r[wq_rdentry0] <= 1'b0;
    end     
    
    if (  (lq_valid_r[2] | lq_fifo_push)
        & wq_mem_retire)
    begin
      // A LQ entry that has a strict dependency with a WQ entry needs to be serialized.
      // This implies the depenency is only cleared when the WQ entry retires. (wr_done)
      // 
      lq2_wq_dep_r[wq_mem_entry_id]  <= 1'b0;
    end

  
  
  
  
  end
end


always @(posedge clk or posedge rst_a)
begin : lq3_wq_dep_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq3_wq_dep_r         <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (lq3_cmd_cg0 == 1'b1)
    begin
      // Set up dependency between this LQ entry and last volatile WQ entry
      //
      lq3_wq_dep_r       <= wq_order_ptr_1h;
    end
    
    if (   (lq_valid_r[3] | lq_fifo_push)
         & wq_cmd_read
         & (~lq_strict_order[3]) )
    begin
      // Clear dependency when dependent WQ command has been processed (out on the 
      // IBP bus) and there is no explicit raw hazard for this entry
      //
      lq3_wq_dep_r[wq_rdentry0] <= 1'b0;
    end     
    
    if (  (lq_valid_r[3] | lq_fifo_push)
        & wq_mem_retire)
    begin
      // A LQ entry that has a strict dependency with a WQ entry needs to be serialized.
      // This implies the depenency is only cleared when the WQ entry retires. (wr_done)
      // 
      lq3_wq_dep_r[wq_mem_entry_id]  <= 1'b0;
    end

  
  
  
  
  end
end


// VPOST ON
// VPOST OFF
//////////////////////////////////////////////////////////////////////////////
// WAR depenedencies
//
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : ca_war_haz_reg_PROC
  if (rst_a == 1'b1)
  begin
     dc4_war_hazard_entries_prel_r <= {`npuarc_DMP_FIFO_DEPTH{1'b0}};
  end
  else
  begin
    if (dc4_update_war_hazard_cg0 == 1'b1)
    begin
      dc4_war_hazard_entries_prel_r <= dc4_war_hazard_entries_prel_nxt;
    end
    
    if (dc4_setup_war_hazard_cg0 == 1'b1)
    begin
      dc4_war_hazard_entries_prel_r <= dc3_war_hazard_entries;
    end
  end
end
// VPOST ON
// leda FM_1_7 on
// spyglass enable_block STARC05-2.2.3.3
endmodule // dmp_lq_fifo
