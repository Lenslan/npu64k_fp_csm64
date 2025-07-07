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
//   ALB_DMP_MQ_FIFO                 
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Miss Queue (MQ) Fifo for the data cache Miss Unit.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_mq_fifo.vpp
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



//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_mq_fifo (
  ////////// General input signals /////////////////////////////////////////
  //
  input                         clk,            // clock
  input                         rst_a,          // reset
  
  ////////// Entry of the FIFO /////////////////////////////////////////////
  //
  input                         ca_pass,        // No stall
  input                         ca_enable,      // No stall
  input                         ca_valid_r,     // CA valid inst  
  input [1:0]                   dmp_mq_write,   // miss instr enters mq
  input                         ca_userm_r,     // user mode
  input                         ca_store_r,     // CA store 
  input                         ca_locked_r,    // CA LLOCK/SCOND
  input                         ca_pre_alloc_r, // CA pre-alloc
  input                         ca_prefw_r,     // CA prefw
  input                         ca_pref_r,      // CA pref
  input                         ca_pref_l2_r,   // CA pref l2 cache
  input [39:0]          ca_mem_addr0_r, // CA memory address
  input [39:0]          ca_mem_addr1,   // CA memory address
  input                         ca_dt_miss_r,   // CA miss in the cache
  input                         ca_hit0_way,    // CA hit addr0
  //////////////// AUX interface ////////////////////////////////////////////
  //
  input                         aux_mq_write,
  input                         aux_mq_flush,
  input                         aux_mq_purge,
  input                         aux_mq_refill,
  input                         aux_mq_way,
  input                         aux_mq_lru_dirty,
  input [39:6]        aux_mq_addr,
  output wire                   mq_empty,
  output wire                   mq_one_or_less_entry,
    
  ////////// Conflict detection in DC3 load/store - physical address ///////
  //
  input [1:0]                   dc3_valid,       // X3 has valid load/store 
  input                         x3_load_r,       // X3 load  
  input                         x3_store_r,      // X3 store  
  input [1:0]                   x3_size_r,       // 00-b, 01-h, 10-w, 11-dw
  input [39:0]          x3_mem_addr0_r,      // X3 memory address
  input [39:6]        dc3_mem_addr1_r,     // X3 memory address
  input                         dc3_dt_line_cross_r, // addr1 is valid

  output wire [2:0]  mq_match0_val,  // MSB=valid, entry number
  output wire [2:0]  mq_match1_val,  // MSB=valid, entry number
  output wire [1:0]   mq_wrptr0,      // MSB=valid, entry number
  output wire [1:0]   mq_wrptr1,      // MSB=valid, entry number
    
  ////////// Forward detection with DC3 load/store to read data ////////////
  //
  input [15:0]      lb_valid_r,    // Valid words in Lbuf
  input                         lb_err_r,      // Err state in Lbuf
  input                         lsmq_done,     // No matched entry in LSMQ
  input                         lsmq_ld_err,   // Read  bus error
  input                         lsmq_st_err,   // Write bus error
   
  output [5:2]    mq_fwd_addr,   // Addr of 1st forward word
  output wire                   mq_lbfwd,      // Forward from Lbuf for load
  output wire                   mq_lbstore,    // Write to Lbuf for store
  output reg [11:0] mq_stmask,     // Byte write mask for store
  output reg [3:0]              mq_fwd_bank,   // Bank select for LBuf data

  output wire                   mq_addr0_hit,  // Lbuf hit for X3 addr0
  output wire                   mq_addr1_hit,  // Lbuf hit for X3 addr1

  ////////// Removal from the FIFO /////////////////////////////////////////
  //
  input                         lbuf_rd_last,   // Lbuf --> DC 
  ////////// Information from copy back unit ////////////////////////////////
  //
  input                         cb_cache_complete, // cache maintenance fl/pu
  input                         cb_complete,       // copy back is done
  input                         cb_way_select_r,   // LRU way for refill
  input                         cb_way_valid,      // not valid if all locked
  

  ////////// Entry to be retired ///////////////////////////////////////////
  //
  output wire                   mq_valid,
  output wire                   mq_dirty,
  output wire                   mq_userm,
  output wire                   mq_cb_complete,
  output wire                   mq_replacement_way,
  output wire                   mq_replacement_valid,
  output wire                   mq_pre_alloc,
  output wire                   mq_pref,
  output wire                   mq_scond,
  output wire [39:0]    mq_addr,   
  output wire [1:0]   mq_rdptr,
  output wire                   mq_cache_flush,
  output wire                   mq_cache_purge,
  output wire                   mq_cache_lock,
  output wire                   mq_cache_cb_complete,
  output reg                    mq_bus_err_r,
  
  ////////// Entry to be sent out on the command channel ///////////////////
  //
  output wire                   mq_cmd_valid,
  output wire                   mq_cmd_pre_alloc, 
  output wire                   mq_cmd_cache_op, 
  output wire                   mq_cmd_cache_rf, 
  output wire                   mq_cmd_userm,
  output wire [39:0]    mq_cmd_addr,   
  input  [1:0]        rf_cmd_rptr_r,
 

  ////////// Miss queue status //////////////////////////////////////////
  //
  output wire                   mq_wr_pending,
  output wire                   mq_entry_full,     // no entry available (pref)
  output wire                   mq_full
  );

// Local declarations.
wire                       mq_done_entry;  

reg [3:0]       mq_valid_r;
reg [3:0]       mq_dirty_r;
reg [3:0]       mq_valid_nxt;
reg [3:0]       mq_dirty_nxt;
reg [3:0]       mq_userm_nxt;  
reg [3:0]       mq_cb_complete_nxt;
reg [3:0]       mq_replacement_way_nxt;
reg [3:0]       mq_replacement_valid_nxt;
reg [3:0]       mq_userm_r;  
reg [3:0]       mq_cb_complete_r;
reg [3:0]       mq_replacement_way_r;
reg [3:0]       mq_replacement_valid_r;
reg [3:0]       mq_locked_r;
reg [3:0]       mq_scond_r;  
reg [3:0]       mq_locked_nxt;
reg [3:0]       mq_scond_nxt;  
reg [39:0]         mq_addr_r[3:0]; 
reg [39:0]         mq_addr_r0; 
reg [39:0]         mq_addr_nxt0; 
reg [39:0]         mq_addr_r1; 
reg [39:0]         mq_addr_nxt1; 
reg [39:0]         mq_addr_r2; 
reg [39:0]         mq_addr_nxt2; 
reg [39:0]         mq_addr_r3; 
reg [39:0]         mq_addr_nxt3; 

reg [3:0]       mq_pre_alloc_nxt;  
reg [3:0]       mq_pref_nxt;  
reg [3:0]       mq_pre_alloc_r;  
reg [3:0]       mq_pref_r;  
reg                        mq_bus_err_nxt;

// Cache maintenance
//
reg                        mq_cache_op_nxt;              
reg                        mq_cache_flush_nxt;           
reg                        mq_cache_purge_nxt;           
reg                        mq_cache_refill_nxt;          
reg                        mq_cache_cb_complete_nxt;          
reg                        mq_cache_op_r;              
reg                        mq_cache_flush_r;           
reg                        mq_cache_purge_r;           
reg                        mq_cache_refill_r;          
reg                        mq_cache_cb_complete_r;          
  
wire [2:0]      wrptr_next;
wire [2:0]      rdptr_next;
wire [2:0]      rdptr_inc_next;
wire [2:0]      dc4_match0_next;
wire [2:0]      dc4_match1_next;

wire [2:0]      wrptr0_inc;
wire [2:0]      wrptr1_inc;
wire [2:0]      wrptr2_inc;
wire [2:0]      wrptr_nxt;
reg  [2:0]      wrptr_r;
wire [1:0]       wrentry;
wire [1:0]       mq_wrptr2;
wire [1:0]       mq_wrptr3;
   
wire [2:0]      rdptr_inc;
reg  [2:0]      rdptr_inc_r;
wire [1:0]       mq_rdptr0;
wire [1:0]       rdptr_nxt;

reg  [2:0]      rdptr_r;
wire                       mq_ptr0_same;

wire [3:0]                 dc4_set_match;
wire [3:0]                 dc4_tag_match;
wire [3:0]                 dc4_addr_match;      // Address match with DC4
wire [3:0]                 dc4_match;           // Match with DC4
reg  [2:0]      dc4_match0;
reg  [2:0]      dc4_match1;
reg  [2:0]      dc4_match0_r;
reg  [2:0]      dc4_match1_r;
wire [3:0]      mq_addr_match0;      // Address match with MQ0
wire [3:0]      mq_addr_match1;      // Address match with MQ1
wire [3:0]      mq_match0;   
wire [3:0]      mq_match1;   
reg  [2:0]      mq_match0_r;   
reg  [2:0]      mq_match1_r;   
reg  [2:0]      mq_match0_nxt;   
reg  [2:0]      mq_match1_nxt;   
reg  [2:0]      mq_match0_next;   
reg  [2:0]      mq_match1_next;   

reg [15:0]     mq_wrd0_mask;
reg [15:0]     mq_wrd1_mask;
reg [15:0]     mq_wrd2_mask;
reg [15:0]     mq_rd0mask;
reg [15:0]     mq_rd1mask;
reg [15:0]     mq_rdmask;
reg                        last_word;
reg                        nxt_last_word;
reg  [11:0]    byte_mask;
reg  [2:0]                 word_valid;
wire [39:0]        wr_addr0;
   
wire [1:0]                 wr_dirty;
wire                       wrenable;
wire                       wr_two;
wire                       mq_write0;
wire                       mq_write1;
wire                       mq_wr_dirty0;
wire                       mq_wr_dirty1;
wire                       mq_one;


wire   mq_two_left;
wire   mq_three_left;

wire   ca_pass_qual;
assign ca_pass_qual  =  ca_pass
                        ;   


////////////////////////////////////////////////////////////////////////////
// Synchronous process for writing new information into the FIFO
//  
////////////////////////////////////////////////////////////////////////////

// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  register file with multiple write ports, conflict covered by assertions
//
// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions
// KS: Conditional reset datapath when safety enabled
// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ:  Valid is reset but Control, Address, Data should not be reset
//
// leda TEST_975 off
// LMD: Latch enabled by a clock affects data input of flipflops clocked 
//      by the trailing edge of the same clock
// LJ:
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
//
always @*
begin : mq_sync_fifo_PROC
      mq_addr_r[0]    = mq_addr_r0;
      mq_addr_r[1]    = mq_addr_r1;
      mq_addr_r[2]    = mq_addr_r2;
      mq_addr_r[3]    = mq_addr_r3;
end

always @*
begin : mq_sync_comb_PROC
    mq_valid_nxt                    = mq_valid_r                      ;
    mq_dirty_nxt                    = mq_dirty_r                      ;
    mq_userm_nxt                    = mq_userm_r                      ;
    mq_cb_complete_nxt              = mq_cb_complete_r                ;
    mq_replacement_valid_nxt        = mq_replacement_valid_r          ;
    mq_replacement_way_nxt          = mq_replacement_way_r            ;
    mq_locked_nxt                   = mq_locked_r                     ;
    mq_scond_nxt                    = mq_scond_r                      ;
    mq_pre_alloc_nxt                = mq_pre_alloc_r                  ;
    mq_pref_nxt                     = mq_pref_r                       ;
    mq_bus_err_nxt                  = mq_bus_err_r                    ;
    mq_cache_op_nxt                 = mq_cache_op_r                   ;
    mq_cache_flush_nxt              = mq_cache_flush_r                ;
    mq_cache_purge_nxt              = mq_cache_purge_r                ;
    mq_cache_refill_nxt             = mq_cache_refill_r               ;
    mq_cache_cb_complete_nxt        = mq_cache_cb_complete_r          ;
    
      mq_addr_nxt0    = mq_addr_r0;
      mq_addr_nxt1    = mq_addr_r1;
      mq_addr_nxt2    = mq_addr_r2;
      mq_addr_nxt3    = mq_addr_r3;
    
  begin
    // Separate writing of valid bit to reduce the load on ca_pass
    //
    if (mq_write0)
    begin
      mq_valid_nxt[mq_wrptr0]           =  1'b1; 
      mq_pre_alloc_nxt[mq_wrptr0]       =  ca_pre_alloc_r; 
      mq_pref_nxt[mq_wrptr0]            =  ca_pref_r
                                        | ca_pref_l2_r
                                        | ca_prefw_r; 
      mq_locked_nxt[mq_wrptr0]          =  ca_locked_r;
      mq_scond_nxt[mq_wrptr0]           =  ca_store_r & ca_locked_r;
      mq_dirty_nxt[mq_wrptr0]           =  ca_store_r;     
      mq_userm_nxt[mq_wrptr0]           =  ca_userm_r;    
// spyglass disable_block Ar_converge02
// SMD: reset converge on reset and data pins of flop
// SJ:  Reset convergence does not cause any functional issue
    if(mq_wrptr0 == 0)
      mq_addr_nxt0    = wr_addr0;
    if(mq_wrptr0 == 1)
      mq_addr_nxt1    = wr_addr0;
    if(mq_wrptr0 == 2)
      mq_addr_nxt2    = wr_addr0;
    if(mq_wrptr0 == 3)
      mq_addr_nxt3    = wr_addr0;
// spyglass enable_block Ar_converge02
      mq_cb_complete_nxt[mq_wrptr0]     =  ca_pre_alloc_r 
                                        & (~ca_dt_miss_r);  
      mq_replacement_way_nxt[mq_wrptr0] =  ca_hit0_way;
    end
    
    if (mq_write1)
    begin
      mq_valid_nxt[mq_wrptr1]           =  1'b1;     
      mq_pre_alloc_nxt[mq_wrptr0]       =  1'b0; 
      mq_dirty_nxt[mq_wrptr1]           = ca_store_r;     
      mq_userm_nxt[mq_wrptr1]           = ca_userm_r;     
    if(mq_wrptr1 == 0)
      mq_addr_nxt0    = ca_mem_addr1;
    if(mq_wrptr1 == 1)
      mq_addr_nxt1    = ca_mem_addr1;
    if(mq_wrptr1 == 2)
      mq_addr_nxt2    = ca_mem_addr1;
    if(mq_wrptr1 == 3)
      mq_addr_nxt3    = ca_mem_addr1;
      mq_cb_complete_nxt[mq_wrptr1]     = 1'b0;  
    end
     
    
    // AUX interface for cache maintenance
    //
    if (aux_mq_write)
    begin 
      mq_valid_nxt[mq_wrptr0]                 = 1'b1; 
      mq_userm_nxt[mq_wrptr0]                 = 1'b0;    
      mq_dirty_nxt[mq_wrptr0]                 = 1'b0;  
      mq_cache_op_nxt                         = 1'b1;          
      mq_cache_flush_nxt                      = aux_mq_flush;  
      mq_cache_purge_nxt                      = aux_mq_purge;  
      mq_cache_refill_nxt                     = aux_mq_refill; 
      
      mq_cache_cb_complete_nxt                = ~(  aux_mq_flush 
                                                 | aux_mq_purge
                                                 | aux_mq_refill);
      // Overload (reuse) the mq_replacement_way entry
      //
      mq_replacement_way_nxt[mq_wrptr0]       = aux_mq_way;
      mq_replacement_valid_nxt[mq_wrptr0]     = 1'b1;
    if(mq_wrptr0 == 0)
      mq_addr_nxt0    = { aux_mq_addr, {6{1'b0}}};
    if(mq_wrptr0 == 1)
      mq_addr_nxt1    = { aux_mq_addr, {6{1'b0}}};
    if(mq_wrptr0 == 2)
      mq_addr_nxt2    = { aux_mq_addr, {6{1'b0}}};
    if(mq_wrptr0 == 3)
      mq_addr_nxt3    = { aux_mq_addr, {6{1'b0}}};
      
      // The cb is not deemed complete for refills caused by cache locking
      // where the lru is dirty. In this case the copy back needs to evict
      // the LRU before the refill puts the new line into the cache.
      // Otherwise we say the cb is complete.
      //
      mq_cb_complete_nxt[mq_wrptr0]           = ~(   aux_mq_refill
                                                  & aux_mq_lru_dirty);
    end
    
    if (mq_wr_dirty0)
    begin
      mq_dirty_nxt[mq_match0_val[1:0]] = 1'b1;    
    end

    if (mq_wr_dirty1)
    begin
      mq_dirty_nxt[mq_match1_val[1:0]] = 1'b1;    
    end

    // Update entry with copy back information
    //
    if (cb_complete)
    begin
      mq_cb_complete_nxt[mq_rdptr0]       = 1'b1;
      mq_replacement_way_nxt[mq_rdptr0]   = cb_way_select_r;
      mq_replacement_valid_nxt[mq_rdptr0] = cb_way_valid;
    end

    
    // Cache maintenance
    //
    if (cb_cache_complete)
    begin
      mq_cache_cb_complete_nxt       = 1'b1;
    end
    
    
    
    
    if (lsmq_ld_err | lsmq_st_err)
    begin
      mq_bus_err_nxt                 = 1'b1;
    end
    
    if (mq_done_entry)
    begin
      mq_valid_nxt[mq_rdptr0]          = 1'b0;    
      mq_pre_alloc_nxt[mq_rdptr0]      = 1'b0;    
      mq_pref_nxt[mq_rdptr0]           = 1'b0;    
      mq_dirty_nxt[mq_rdptr0]          = 1'b0; 
      mq_cb_complete_nxt[mq_rdptr0]    = 1'b0;   

      mq_locked_nxt[mq_rdptr0]         = 1'b0;   
      mq_scond_nxt[mq_rdptr0]          = 1'b0;
      mq_cache_op_nxt                  = 1'b0;
      mq_cache_flush_nxt               = 1'b0;
      mq_cache_purge_nxt               = 1'b0;
      mq_cache_refill_nxt              = 1'b0;
// spyglass disable_block W415a
// SMD: signal assigned multiple times in the same always block
// SJ:  done on purpose, last one has priority. 
      mq_cache_cb_complete_nxt         = 1'b0;
      mq_bus_err_nxt                   = 1'b0;
// spyglass enable_block W415a
    end
    

  end // else: !if(rst_a)
end // block: mq_sync_PROC
always @(posedge clk or posedge rst_a)
begin : mq_sync_PROC
  if (rst_a == 1'b1)
  begin
    mq_valid_r                      <= {4{1'b0}};
    mq_dirty_r                      <= {4{1'b0}};
    mq_userm_r                      <= {4{1'b0}};
    mq_cb_complete_r                <= {4{1'b0}};
    mq_replacement_valid_r          <= {4{1'b0}};
    mq_replacement_way_r            <= {4{1'b0}};
    mq_locked_r                     <= {4{1'b0}};
    mq_scond_r                      <= {4{1'b0}};
    mq_pre_alloc_r                  <= {4{1'b0}};
    mq_pref_r                       <= {4{1'b0}};
    mq_bus_err_r                    <= 1'b0;
    mq_cache_op_r                   <= 1'b0;
    mq_cache_flush_r                <= 1'b0;
    mq_cache_purge_r                <= 1'b0;
    mq_cache_refill_r               <= 1'b0;
    mq_cache_cb_complete_r          <= 1'b0;
    
      mq_addr_r0    <= {40{1'b0}};
      mq_addr_r1    <= {40{1'b0}};
      mq_addr_r2    <= {40{1'b0}};
      mq_addr_r3    <= {40{1'b0}};
    
  end
  else
  begin
    mq_valid_r                      <= mq_valid_nxt                      ;
    mq_dirty_r                      <= mq_dirty_nxt                      ;
    mq_userm_r                      <= mq_userm_nxt                      ;
    mq_cb_complete_r                <= mq_cb_complete_nxt                ;
    mq_replacement_valid_r          <= mq_replacement_valid_nxt          ;
    mq_replacement_way_r            <= mq_replacement_way_nxt            ;
    mq_locked_r                     <= mq_locked_nxt                     ;
    mq_scond_r                      <= mq_scond_nxt                      ;
    mq_pre_alloc_r                  <= mq_pre_alloc_nxt                  ;
    mq_pref_r                       <= mq_pref_nxt                       ;
    mq_bus_err_r                    <= mq_bus_err_nxt                    ;
    mq_cache_op_r                   <= mq_cache_op_nxt                   ;
    mq_cache_flush_r                <= mq_cache_flush_nxt                ;
    mq_cache_purge_r                <= mq_cache_purge_nxt                ;
    mq_cache_refill_r               <= mq_cache_refill_nxt               ;
    mq_cache_cb_complete_r          <= mq_cache_cb_complete_nxt          ;
    mq_addr_r0                     <= mq_addr_nxt0                    ;
    mq_addr_r1                     <= mq_addr_nxt1                    ;
    mq_addr_r2                     <= mq_addr_nxt2                    ;
    mq_addr_r3                     <= mq_addr_nxt3                    ;
  end // else: !if(rst_a)
end // block: mq_sync_PROC
// leda TEST_975 on
// leda NTL_RST03 on
// leda FM_1_7 on
// spyglass enable_block STARC05-2.2.3.3
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

////////////////////////////////////////////////////////////////////////////
// Write logic to MQ 
//
////////////////////////////////////////////////////////////////////////////
  // Combine signal for ease of assertion
  //
  assign mq_write0    = wrenable & ca_pass_qual;
  assign mq_write1    = wr_two   & ca_pass_qual;
  assign mq_wr_dirty0 = wr_dirty[0] & ca_pass_qual;
  assign mq_wr_dirty1 = wr_dirty[1] & ca_pass_qual;
   
  assign wrentry = dmp_mq_write & 
                   {~mq_match1_val[2], 
                    ~mq_match0_val[2]};
  assign wrenable = | wrentry[1:0];
  assign wr_two   = & wrentry[1:0];
   
  assign wr_addr0   = wrentry[0] ? ca_mem_addr0_r : ca_mem_addr1;
   
  // Check the completion of cache maintenance operations.
  // Both the refill unit and the copy back unit need to be completed 
  //
  assign mq_cache_complete =  mq_cache_op_r
                            & mq_cache_cb_complete_r
                            ;                            
  
  // A MQ entry is done when either:
  // The entry is put in the cache by the rf unit (1)
  //
  // The entry corresponds to a cache maint op that has been completed (2)
  // 
  assign mq_done_entry = (  lbuf_rd_last         // (1)
                          | mq_cache_complete);  // (2)
  
    

  assign mq_rdptr  = mq_rdptr0;

  assign wr_dirty[0] = (mq_match0_val[2] & ca_store_r & 
                        (~mq_dirty_r[mq_match0_val[1:0]]));
  assign wr_dirty[1] = (mq_match1_val[2] & ca_store_r & 
                        (~mq_dirty_r[mq_match1_val[1:0]]));
   
////////////////////////////////////////////////////////////////////////////
// Mux logic to select the next entry for copy back/refill processing. 
//
////////////////////////////////////////////////////////////////////////////

  assign rdptr_nxt                =  ( (~mq_one & lbuf_rd_last ) 
                                    ? rdptr_inc_r[1:0] 
                                    : mq_rdptr0);
   
  assign mq_valid                 = mq_valid_r[mq_rdptr0];
  assign mq_dirty                 = mq_dirty_r[mq_rdptr0];
  assign mq_userm                 = mq_userm_r[mq_rdptr0];
  assign mq_cb_complete           = mq_cb_complete_r[mq_rdptr0];
  assign mq_replacement_way       = mq_replacement_way_r[mq_rdptr0];
  assign mq_replacement_valid     = mq_replacement_valid_r[mq_rdptr0];

  // Make sure the pre alloc command phase is done before we tell the line 
  // buffer there is a prealloc on top of the MQ fifo
  //
  assign mq_pre_alloc             = mq_pre_alloc_r[mq_rdptr0]
                                   & (mq_rdptr0 != rf_cmd_rptr_r)
                                   ;
  assign mq_pref                  = mq_pref_r[mq_rdptr0];
  assign mq_scond                 = mq_scond_r[mq_rdptr0];
  assign mq_addr                  = mq_addr_r[mq_rdptr0];

  assign mq_cache_flush           = mq_cache_flush_r  & (~mq_cache_complete);
  assign mq_cache_purge           = mq_cache_purge_r  & (~mq_cache_complete);
  assign mq_cache_lock            = mq_cache_refill_r & (~mq_cache_complete);
  assign mq_cache_cb_complete     = mq_cache_cb_complete_r;
  
////////////////////////////////////////////////////////////////////////////
// Logic to read next entry for BIU command request
//
////////////////////////////////////////////////////////////////////////////

  assign mq_cmd_valid       = mq_valid_r[rf_cmd_rptr_r[1:0]];
  assign mq_cmd_userm       = mq_userm_r[rf_cmd_rptr_r[1:0]];
  assign mq_cmd_addr        = mq_addr_r[rf_cmd_rptr_r[1:0]];

  assign mq_cmd_pre_alloc   = mq_pre_alloc_r[rf_cmd_rptr_r[1:0]];
  assign mq_cmd_cache_op    = mq_cache_op_r;
  assign mq_cmd_cache_rf    = mq_cache_refill_r;


   
////////////////////////////////////////////////////////////////////////////
// Asynchronous process for determining conflict detection with loads
//
////////////////////////////////////////////////////////////////////////////

  // Valid load/store in dc3 that match with address in dc4
  //
  assign dc4_set_match[0]  = (   ca_mem_addr0_r[13:6] 
                              == x3_mem_addr0_r[13:6]);
  assign dc4_tag_match[0]  = (   ca_mem_addr0_r[39:14] 
                              == x3_mem_addr0_r[39:14]);
  assign dc4_addr_match[0] = dc4_set_match[0] & dc4_tag_match[0];
  
  assign dc4_set_match[1]  = (   ca_mem_addr0_r[13:6] 
                              == dc3_mem_addr1_r[13:6]);
  assign dc4_tag_match[1]  = (   ca_mem_addr0_r[39:14] 
                              == dc3_mem_addr1_r[39:14]);
  assign dc4_addr_match[1] = dc4_set_match[1] & dc4_tag_match[1];
  
  assign dc4_set_match[2]  = (   ca_mem_addr1[13:6] 
                              == x3_mem_addr0_r[13:6]);
  assign dc4_tag_match[2]  = (   ca_mem_addr1[39:14] 
                              == x3_mem_addr0_r[39:14]);
  assign dc4_addr_match[2] = dc4_set_match[2] & dc4_tag_match[2];
  
  assign dc4_set_match[3]  = (   ca_mem_addr1[13:6] 
                              == dc3_mem_addr1_r[13:6]);
  assign dc4_tag_match[3]  = (   ca_mem_addr1[39:14] 
                              == dc3_mem_addr1_r[39:14]);
  assign dc4_addr_match[3] = dc4_set_match[3] & dc4_tag_match[3];
  
  assign dc4_match[0] =    dc3_valid[0] 
                         & dc4_addr_match[0]
                         ;
  
  assign dc4_match[1] =    dc3_valid[1] 
                         & dc4_addr_match[1]
                         ;

  assign dc4_match[2] =    dc3_valid[0] 
                         & dc4_addr_match[2]
                         ;
                        

  assign dc4_match[3] =    dc3_valid[1] 
                         & dc4_addr_match[3]
                         ;
   
always @*
begin : dc4_match_PROC
  casez ({wrentry, dc4_match[2], dc4_match[0]})
  4'b01_?_1:   dc4_match0 = {1'b1, mq_wrptr0};
  4'b10_1_?:   dc4_match0 = {1'b1, mq_wrptr0};
  4'b11_?_1:   dc4_match0 = {1'b1, mq_wrptr0};
  4'b11_1_0:   dc4_match0 = {1'b1, mq_wrptr1};
  default:     dc4_match0 = {1'b0, mq_wrptr0};
  endcase  
  casez ({wrentry, dc4_match[3], dc4_match[1]})
  4'b01_?_1:   dc4_match1 = {1'b1, mq_wrptr0};
  4'b10_1_?:   dc4_match1 = {1'b1, mq_wrptr0};
  4'b11_?_1:   dc4_match1 = {1'b1, mq_wrptr0};
  4'b11_1_0:   dc4_match1 = {1'b1, mq_wrptr1};
  default:     dc4_match1 = {1'b0, mq_wrptr0};
  endcase  
end

  // Valid load/store in dc3 that match with valid entry in FIFO
  //
  assign mq_addr_match0[0] = (    mq_addr_r[0][39:6]
                               == x3_mem_addr0_r[39:6]);

  assign mq_addr_match1[0] = (    mq_addr_r[0][39:6]
                               == dc3_mem_addr1_r[39:6]);

  
  
  assign mq_match0[0] =    mq_valid_r[0] 
                          & dc3_valid[0] 
                          & mq_addr_match0[0]
                          ;

  assign mq_match1[0] =    mq_valid_r[0] 
                          & dc3_valid[1] 
                          & mq_addr_match1[0]
                          ;
  
  // Valid load/store in dc3 that match with valid entry in FIFO
  //
  assign mq_addr_match0[1] = (    mq_addr_r[1][39:6]
                               == x3_mem_addr0_r[39:6]);

  assign mq_addr_match1[1] = (    mq_addr_r[1][39:6]
                               == dc3_mem_addr1_r[39:6]);

  
  
  assign mq_match0[1] =    mq_valid_r[1] 
                          & dc3_valid[0] 
                          & mq_addr_match0[1]
                          ;

  assign mq_match1[1] =    mq_valid_r[1] 
                          & dc3_valid[1] 
                          & mq_addr_match1[1]
                          ;
  
  // Valid load/store in dc3 that match with valid entry in FIFO
  //
  assign mq_addr_match0[2] = (    mq_addr_r[2][39:6]
                               == x3_mem_addr0_r[39:6]);

  assign mq_addr_match1[2] = (    mq_addr_r[2][39:6]
                               == dc3_mem_addr1_r[39:6]);

  
  
  assign mq_match0[2] =    mq_valid_r[2] 
                          & dc3_valid[0] 
                          & mq_addr_match0[2]
                          ;

  assign mq_match1[2] =    mq_valid_r[2] 
                          & dc3_valid[1] 
                          & mq_addr_match1[2]
                          ;
  
  // Valid load/store in dc3 that match with valid entry in FIFO
  //
  assign mq_addr_match0[3] = (    mq_addr_r[3][39:6]
                               == x3_mem_addr0_r[39:6]);

  assign mq_addr_match1[3] = (    mq_addr_r[3][39:6]
                               == dc3_mem_addr1_r[39:6]);

  
  
  assign mq_match0[3] =    mq_valid_r[3] 
                          & dc3_valid[0] 
                          & mq_addr_match0[3]
                          ;

  assign mq_match1[3] =    mq_valid_r[3] 
                          & dc3_valid[1] 
                          & mq_addr_match1[3]
                          ;
  
   
always @*
begin : mq_mux_PROC
  // [2] valid match, [1:0] the MQ entry number
  //     Converting 1-hot to pointer
  //
  mq_match0_nxt[2] = 1'b0;
  mq_match1_nxt[2] = 1'b0;
  mq_match0_nxt[1:0] = {2{1'b0}};
  mq_match1_nxt[1:0] = {2{1'b0}};
   
  if (mq_match0[0] && (!mq_match0_nxt[2]))
  begin
    mq_match0_nxt[2] = 1'b1;
    mq_match0_nxt[1:0] = 2'd0;
  end
  if (mq_match1[0] && (!mq_match1_nxt[2]))
  begin
    mq_match1_nxt[2] = 1'b1;
    mq_match1_nxt[1:0] = 2'd0;
  end
  if (mq_match0[1] && (!mq_match0_nxt[2]))
  begin
    mq_match0_nxt[2] = 1'b1;
    mq_match0_nxt[1:0] = 2'd1;
  end
  if (mq_match1[1] && (!mq_match1_nxt[2]))
  begin
    mq_match1_nxt[2] = 1'b1;
    mq_match1_nxt[1:0] = 2'd1;
  end
  if (mq_match0[2] && (!mq_match0_nxt[2]))
  begin
    mq_match0_nxt[2] = 1'b1;
    mq_match0_nxt[1:0] = 2'd2;
  end
  if (mq_match1[2] && (!mq_match1_nxt[2]))
  begin
    mq_match1_nxt[2] = 1'b1;
    mq_match1_nxt[1:0] = 2'd2;
  end
  if (mq_match0[3] && (!mq_match0_nxt[2]))
  begin
    mq_match0_nxt[2] = 1'b1;
    mq_match0_nxt[1:0] = 2'd3;
  end
  if (mq_match1[3] && (!mq_match1_nxt[2]))
  begin
    mq_match1_nxt[2] = 1'b1;
    mq_match1_nxt[1:0] = 2'd3;
  end

end

  // Next cycle, send match entry to LSMQ for mq_fifo field
  //
  assign mq_match0_val =   dc4_match0_r[2] 
                         ? dc4_match0_r 
                         : mq_match0_r;
  
  assign mq_match1_val =  dc4_match1_r[2] 
                        ? dc4_match1_r 
                        : mq_match1_r;

////////////////////////////////////////////////////////////////////////////
// Asynchronous process for determining forwarding from line buffer
//
////////////////////////////////////////////////////////////////////////////

   // Seperate logic for forwarding for speedpath reason
   //
  assign lb_match0 = (  mq_valid_r[mq_rdptr0] 
                      & dc3_valid[0] 
                      & (   mq_addr_r[mq_rdptr0][39:6]
                         == x3_mem_addr0_r[39:6]));
  
  assign lb_match1 = (   mq_valid_r[mq_rdptr0] 
                      & dc3_valid[1]
                      & (   mq_addr_r[mq_rdptr0][39:6]
                         == dc3_mem_addr1_r[39:6]));
   
always @*
begin : x3_mask_PROC
  casez ({x3_size_r, x3_mem_addr0_r[1:0]})
  4'b00?? : word_valid = 3'b001;
  4'b010? : word_valid = 3'b001;
  4'b0110 : word_valid = 3'b001;
  4'b0111 : word_valid = 3'b011;
  4'b1000 : word_valid = 3'b001;
  4'b1001 : word_valid = 3'b011;
  4'b101? : word_valid = 3'b011;
  4'b1100 : word_valid = 3'b011;
  4'b1101 : word_valid = 3'b111;
  4'b111? : word_valid = 3'b111;
  default : word_valid = 3'b000;
  endcase  

  mq_wrd0_mask[15:0] = {{15-2{1'b0}}, word_valid};
  mq_wrd1_mask[15:0] = {{15-1{1'b0}}, word_valid[2:1]};
  mq_wrd2_mask[15:0] = {{15{1'b0}},   word_valid[2]};
   
// leda W244 off   
// LMD: Shift by non-constant
// LJ:  Shift by address is needed for proper functionality
  mq_rd0mask = mq_wrd0_mask << x3_mem_addr0_r[5:2];
// leda W244 on   
  mq_rd1mask = x3_mem_addr0_r[2] ? mq_wrd1_mask : mq_wrd2_mask;
  mq_rdmask  = lb_match0 ? mq_rd0mask : mq_rd1mask;
   
  // Which bank to select (result bus) for forwarding
  //
  casez ({dc3_dt_line_cross_r, lb_match0, lb_match1, x3_mem_addr0_r[3:2]})
  5'b?1?00 : mq_fwd_bank[3:0] = 4'b0111;  // odd - even banks
  5'b?1?01 : mq_fwd_bank[3:0] = 4'b1110;
  5'b01?10 : mq_fwd_bank[3:0] = 4'b1101;
  5'b11?10 : mq_fwd_bank[3:0] = 4'b1100;  // No low word select
  5'b10110 : mq_fwd_bank[3:0] = 4'b0001;  // Addr1
  5'b01?11 : mq_fwd_bank[3:0] = 4'b1011;
  5'b11?11 : mq_fwd_bank[3:0] = 4'b1000;  // No low word select
  5'b10111 : mq_fwd_bank[3:0] = 4'b0011;  // Addr1
  default  : mq_fwd_bank[3:0] = 4'b0000;
  endcase  

  // Last 2 words of line buffer decoding
  //
  last_word = (& x3_mem_addr0_r[5:2]);
   
  // Byte mask for store hit
  //
  case ({x3_size_r, x3_mem_addr0_r[1:0]})
  4'b0000 : byte_mask = 12'h001;
  4'b0001 : byte_mask = 12'h002;
  4'b0010 : byte_mask = 12'h004;
  4'b0011 : byte_mask = 12'h008;
  4'b0100 : byte_mask = 12'h003;
  4'b0101 : byte_mask = 12'h006;
  4'b0110 : byte_mask = 12'h00c;
  4'b0111 : byte_mask = 12'h018;
  4'b1000 : byte_mask = 12'h00f;
  4'b1001 : byte_mask = 12'h01e;
  4'b1010 : byte_mask = 12'h03c;
  4'b1011 : byte_mask = 12'h078;
  4'b1100 : byte_mask = 12'h0ff;
  4'b1101 : byte_mask = 12'h1fe;
  4'b1110 : byte_mask = 12'h3fc;
  4'b1111 : byte_mask = 12'h7f8;
  default : byte_mask = 12'h000;
  endcase  

  nxt_last_word = (& x3_mem_addr0_r[5:3]) 
                  & (~x3_mem_addr0_r[2]);
  // Decode into line buffer write mask (8 bytes)
  //
  casez ({lb_match0, last_word, nxt_last_word})
  3'b100 : mq_stmask = byte_mask;
  3'b101 : mq_stmask = {4'h0,  byte_mask[7:0]};
  3'b110 : mq_stmask = {8'h00, byte_mask[3:0]};
  3'b001 : mq_stmask = {8'h00, byte_mask[11:8]};
  3'b010 : mq_stmask = {4'h0,  byte_mask[11:4]};
  default: mq_stmask = 12'h000;
  endcase

   
end

  // Compare to valid words in line buffer
  //
  assign mq_dvalid   = ((mq_rdmask & lb_valid_r)==mq_rdmask) & lsmq_done;
  assign mq_lbfwd    = mq_dvalid & (lb_match0 | lb_match1) & x3_load_r;
  assign mq_lbstore  = mq_dvalid & (lb_match0 | lb_match1) & x3_store_r;
  assign mq_fwd_addr = (lb_match0 ? x3_mem_addr0_r[5:2] : 
                        {6-2{1'b0}});

  assign mq_addr0_hit = mq_dvalid & lb_match0 & (~lb_err_r);
  assign mq_addr1_hit = mq_dvalid & lb_match1 & (~lb_err_r);


////////////////////////////////////////////////////////////////////////////
// Synchronous process for the pointer manipulation logic
//
////////////////////////////////////////////////////////////////////////////

assign    wrptr_next = 
            (  (ca_pass_qual & wrenable) 
                 | aux_mq_write
               )
               ? wrptr_nxt 
               : wrptr_r;
    
    // Instruction retired from the circular fifo. Advance the rdptr
    //
assign    rdptr_next =
             mq_done_entry ? rdptr_inc : rdptr_r;

    // rdptr increment
    //
assign     rdptr_inc_next = 
            mq_done_entry ?  (rdptr_inc + 2'b01) : rdptr_inc;
  
    // Match entry
    //
assign     dc4_match0_next    =
                       ca_valid_r ? 
                       (ca_pass_qual ? dc4_match0 : dc4_match0_r) : 
                       {2+1{1'b0}};
assign     dc4_match1_next    = 
                       ca_valid_r ? 
                       (ca_pass_qual ? dc4_match1 : dc4_match1_r) : 
                       {2+1{1'b0}};

always @(posedge clk or posedge rst_a)
begin: mq_ptr_sync_PROC
  if (rst_a == 1'b1)
  begin
    wrptr_r           <= {2+1{1'b0}};
    rdptr_r           <= {2+1{1'b0}};
    rdptr_inc_r       <= {2+1{1'b0}};
    dc4_match0_r      <= {2+1{1'b0}};
    dc4_match1_r      <= {2+1{1'b0}};
  end
  else
  begin
    wrptr_r           <= wrptr_next     ;
    rdptr_r           <= rdptr_next     ;
    rdptr_inc_r       <= rdptr_inc_next ;
    dc4_match0_r      <= dc4_match0_next;
    dc4_match1_r      <= dc4_match1_next;
  end
end

always @*
begin: mq_match_comb_PROC
    mq_match0_next[2] = mq_match0_nxt[2] | 
                                 (~ca_enable & mq_match0_r[2]);
    mq_match0_next[1:0] = mq_match0_nxt[2] ? 
                                  mq_match0_nxt[1:0] : 
                                  mq_match0_r[1:0];
    mq_match1_next[2] = mq_match1_nxt[2] | 
                                (~ca_enable & mq_match1_r[2]);
    mq_match1_next[1:0] = mq_match1_nxt[2] ? 
                                  mq_match1_nxt[1:0] : 
                                  mq_match1_r[1:0];
end
always @(posedge clk or posedge rst_a)
begin: mq_match_sync_PROC
  if (rst_a == 1'b1)
  begin
    mq_match0_r       <= {2+1{1'b0}};
    mq_match1_r       <= {2+1{1'b0}};
  end
  else if (ca_enable)
  begin
    mq_match0_r <= mq_match0_next; 
    mq_match1_r <= mq_match1_next; 
  end
end
            
  assign mq_empty         = (wrptr_r == rdptr_r);
  assign mq_one           = (wrptr_r == rdptr_inc_r);

  assign mq_one_or_less_entry = mq_one
                              | (~(|mq_valid_r));
      
  assign mq_entry_full    = (wrptr_r[2]!= rdptr_r[2]) 
                           & mq_ptr0_same;
// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One/two bits incrementor

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
  assign wrptr0_inc = wrptr_r + 2'b01;
  assign wrptr1_inc = wrptr_r + 2'b10;
  assign wrptr2_inc = wrptr_r + 2'b11;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on
  assign mq_wrptr0  = wrptr_r[1:0];
  assign mq_wrptr1  = wrptr0_inc[1:0];
  assign mq_wrptr2  = wrptr1_inc[1:0];
  assign mq_wrptr3  = wrptr2_inc[1:0];

// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor
//
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
  assign rdptr_inc  = rdptr_r + 2'b01;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on
  assign mq_rdptr0  = rdptr_r[1:0];

  assign mq_ptr0_same  = (mq_wrptr0 == mq_rdptr0);
  assign mq_wptr1_same = (mq_wrptr1 == mq_rdptr0);
  assign mq_wptr2_same = (mq_wrptr2 == mq_rdptr0);
  assign mq_wptr3_same = (mq_wrptr3 == mq_rdptr0);

  assign mq_full1    = (wrptr_r[2]!=rdptr_r[2]) 
                      & mq_ptr0_same;

  assign mq_one_left   = (wrptr0_inc[2]!=rdptr_r[2]) 
                        & mq_wptr1_same;
  assign mq_two_left   = (wrptr1_inc[2]!=rdptr_r[2]) 
                        & mq_wptr2_same;
  assign mq_three_left = (wrptr2_inc[2]!=rdptr_r[2]) 
                        & mq_wptr3_same;

  assign mq_full = 
                   (mq_full1 
                 | (mq_one_left   & (wrenable | (& dc3_valid))) 
                 | (mq_two_left   & (wr_two | (wrenable & (& dc3_valid)))) 
                 | (mq_three_left & (wr_two & (& dc3_valid))) )
                 ;

  
  assign mq_wr_pending = | (mq_valid_r & mq_dirty_r);

  assign wrptr_nxt = wr_two ? wrptr1_inc : wrptr0_inc;


endmodule // alb_dmp_mq_fifo

