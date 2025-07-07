// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
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
// Description:
// @p
//  The |utlb| module implements the micro-TLB function for memory management.
//  This is a fully associative memory with a configurable size of 4 or 8
//  entries and one or two lookup ports.
//  The uTLB supports update (entry write) by parallel write of an entire
//  entry, and also supports read access (of a full entry) to support aux
//  read.
//
// @e
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o cpu.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst", edc: { suffix: "auto", clk: "edc_clk", rst: "rst", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_udtlb (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                          clk,            // Processor clock
  input                          rst,            // Global reset
  input                          rst_init_disable_r,

  input [3:0]    alloc_entries,  // Allocatable entries

  //  Shared lib
  input                          shared_en_r,    // Shared lib enable (PID)
  input [`npuarc_SASID_RANGE]           sasid_r,        // Current pid slib membership
  input                          sasid_force_match,
  input                          eager_match,

  ////////// Look-up port(s) ///////////////////////////////////////////////
  // 
  // Request 0 for uTLB lookup
  input                            req0_valid_r,
  input  [`npuarc_PD0_VPN_RANGE]          req0_vpn_r,
  input  [`npuarc_PD0_ASID_RANGE]         req0_asid_r,
  //  Lookup result 0
  output reg                       rslt0_match,
  output reg                       rslt0_miss,
  output reg [`npuarc_DTLB_INDEX_RANGE]   rslt0_match_index,
  output reg                       rslt0_match_size,
  output reg                       rslt0_multiple_match,

  output reg [`npuarc_DTLB_ENTRIES_RANGE] rslt0_entry_match,
  output reg [`npuarc_DTLB_ENTRIES_RANGE] rslt0_entry_match_1h,

  output reg [`npuarc_PD1_PPN_RANGE]      rslt0_ppn_out,
  output reg [`npuarc_PD1_UA_RANGE]       rslt0_user_attr_out,
  output reg                       rslt0_wr_thru_out,
  output reg [`npuarc_PD1_PERM_RANGE]     rslt0_perm_out,
  output reg                       rslt0_cached_out,

  // Request 1 for uTLB lookup
  input                            req1_valid_r,
  input  [`npuarc_PD0_VPN_RANGE]          req1_vpn_r,
  input  [`npuarc_PD0_ASID_RANGE]         req1_asid_r,
  //  Lookup result 1
  output reg                       rslt1_match,
  output reg                       rslt1_miss,
  output reg [`npuarc_DTLB_INDEX_RANGE]   rslt1_match_index,
  output reg                       rslt1_match_size,
  output reg                       rslt1_multiple_match,

  output reg [`npuarc_DTLB_ENTRIES_RANGE] rslt1_entry_match,
  output reg [`npuarc_DTLB_ENTRIES_RANGE] rslt1_entry_match_1h,

  output reg [`npuarc_PD1_PPN_RANGE]      rslt1_ppn_out,
  output reg [`npuarc_PD1_UA_RANGE]       rslt1_user_attr_out,
  output reg                       rslt1_wr_thru_out,
  output reg [`npuarc_PD1_PERM_RANGE]     rslt1_perm_out,
  output reg                       rslt1_cached_out,

  ////////// Invalidate select uTLB entries /////////////////////////////////
  input  [`npuarc_DTLB_ENTRIES_RANGE]     invalidate_entries,
  // spyglass disable_block W240
  // SMD: inputs declared but not read
  // SJ:  unused in some configs but part of standard module interface
  input                            unlock_entries,
  // spyglass enable_block W240
  // status of entries, valid or invalid
  output                           inval_entry_avail,
  output     [`npuarc_DTLB_ENTRIES_RANGE] inval_entry_1h,

  ////////// Interface to read / write utlb entries /////////////////////////
  //
  input                          entry_rd_val,   // Valid read request
  input      [`npuarc_DTLB_INDEX_RANGE] entry_rd_addr,  // index for read
  output reg [`npuarc_UTLB_ENTRY_RANGE] entry_rd_data,  // LR read data (entry)

  // Update / aux write operation from jtlb
  input  [`npuarc_DTLB_ENTRIES_RANGE]   entry_update_1h, // may be more than 1 bit set
  input  [`npuarc_UTLB_ENTRY_RANGE]     entry_update_data  // new entry from jtlb
);
 
////////////////////////////////////////////////////////////////////////////
// Internal Signals
////////////////////////////////////////////////////////////////////////////

reg  init_enable_r;
reg  init_complete_r;
wire clr_entry_bits;

// uTLB entries 
// Registers for Entry 0
//  
// pd0
  reg  [`npuarc_PD0_VPN_RANGE]       entry0_vpn_r;
  wire [`npuarc_PD0_VPN_RANGE]       entry0_vpn_rr;
  reg  [`npuarc_PD0_VPN_RANGE]       entry0_vpn_nxt;

  reg  [`npuarc_PD0_ASID_RANGE]      entry0_asid_r;
  wire [`npuarc_PD0_ASID_RANGE]      entry0_asid_rr;
  reg  [`npuarc_PD0_ASID_RANGE]      entry0_asid_nxt;

  reg                         entry0_shared_r;
  wire                        entry0_shared_rr;

  reg                         entry0_shared_nxt;

//reg                         entry0_spare0_r;   // spare attr bit
//reg                         entry0_spare0_nxt;
       
  wire                        entry0_lock_r;
  wire                        entry0_lock_rr;
  reg                         entry0_lock_nxt;

  reg                         entry0_size_r;     // single bit for now
  wire                        entry0_size_rr;     // single bit for now
  reg                         entry0_size_nxt;

  reg                         entry0_valid_r;
  wire                        entry0_valid_rr;
  reg                         entry0_valid_nxt;

  reg                         entry0_global_r;
  wire                        entry0_global_rr;
  reg                         entry0_global_nxt;

// pd1
  reg  [`npuarc_PD1_PPN_RANGE]       entry0_ppn_r;
  reg  [`npuarc_PD1_PPN_RANGE]       entry0_ppn_nxt;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_UA_RANGE]        entry0_user_attr_r;
  reg  [`npuarc_PD1_UA_RANGE]        entry0_user_attr_nxt;

  reg                         entry0_wr_thru_r;
  reg                         entry0_wr_thru_nxt;
// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_PERM_RANGE]      entry0_perm_r;
  reg  [`npuarc_PD1_PERM_RANGE]      entry0_perm_nxt;

  reg                         entry0_cached_r;
  reg                         entry0_cached_nxt;
// leda NTL_CON32 on

//`let is_dtlb = (8 == 8);

assign entry0_vpn_rr = entry0_vpn_r;

assign entry0_asid_rr = entry0_asid_r;

assign entry0_shared_rr = entry0_shared_r;

assign entry0_lock_rr = entry0_lock_r;

assign entry0_size_rr = entry0_size_r;

assign entry0_valid_rr = entry0_valid_r;

assign entry0_global_rr = entry0_global_r;


// Registers for Entry 1
//  
// pd0
  reg  [`npuarc_PD0_VPN_RANGE]       entry1_vpn_r;
  wire [`npuarc_PD0_VPN_RANGE]       entry1_vpn_rr;
  reg  [`npuarc_PD0_VPN_RANGE]       entry1_vpn_nxt;

  reg  [`npuarc_PD0_ASID_RANGE]      entry1_asid_r;
  wire [`npuarc_PD0_ASID_RANGE]      entry1_asid_rr;
  reg  [`npuarc_PD0_ASID_RANGE]      entry1_asid_nxt;

  reg                         entry1_shared_r;
  wire                        entry1_shared_rr;

  reg                         entry1_shared_nxt;

//reg                         entry1_spare0_r;   // spare attr bit
//reg                         entry1_spare0_nxt;
       
  wire                        entry1_lock_r;
  wire                        entry1_lock_rr;
  reg                         entry1_lock_nxt;

  reg                         entry1_size_r;     // single bit for now
  wire                        entry1_size_rr;     // single bit for now
  reg                         entry1_size_nxt;

  reg                         entry1_valid_r;
  wire                        entry1_valid_rr;
  reg                         entry1_valid_nxt;

  reg                         entry1_global_r;
  wire                        entry1_global_rr;
  reg                         entry1_global_nxt;

// pd1
  reg  [`npuarc_PD1_PPN_RANGE]       entry1_ppn_r;
  reg  [`npuarc_PD1_PPN_RANGE]       entry1_ppn_nxt;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_UA_RANGE]        entry1_user_attr_r;
  reg  [`npuarc_PD1_UA_RANGE]        entry1_user_attr_nxt;

  reg                         entry1_wr_thru_r;
  reg                         entry1_wr_thru_nxt;
// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_PERM_RANGE]      entry1_perm_r;
  reg  [`npuarc_PD1_PERM_RANGE]      entry1_perm_nxt;

  reg                         entry1_cached_r;
  reg                         entry1_cached_nxt;
// leda NTL_CON32 on

//`let is_dtlb = (8 == 8);

assign entry1_vpn_rr = entry1_vpn_r;

assign entry1_asid_rr = entry1_asid_r;

assign entry1_shared_rr = entry1_shared_r;

assign entry1_lock_rr = entry1_lock_r;

assign entry1_size_rr = entry1_size_r;

assign entry1_valid_rr = entry1_valid_r;

assign entry1_global_rr = entry1_global_r;


// Registers for Entry 2
//  
// pd0
  reg  [`npuarc_PD0_VPN_RANGE]       entry2_vpn_r;
  wire [`npuarc_PD0_VPN_RANGE]       entry2_vpn_rr;
  reg  [`npuarc_PD0_VPN_RANGE]       entry2_vpn_nxt;

  reg  [`npuarc_PD0_ASID_RANGE]      entry2_asid_r;
  wire [`npuarc_PD0_ASID_RANGE]      entry2_asid_rr;
  reg  [`npuarc_PD0_ASID_RANGE]      entry2_asid_nxt;

  reg                         entry2_shared_r;
  wire                        entry2_shared_rr;

  reg                         entry2_shared_nxt;

//reg                         entry2_spare0_r;   // spare attr bit
//reg                         entry2_spare0_nxt;
       
  wire                        entry2_lock_r;
  wire                        entry2_lock_rr;
  reg                         entry2_lock_nxt;

  reg                         entry2_size_r;     // single bit for now
  wire                        entry2_size_rr;     // single bit for now
  reg                         entry2_size_nxt;

  reg                         entry2_valid_r;
  wire                        entry2_valid_rr;
  reg                         entry2_valid_nxt;

  reg                         entry2_global_r;
  wire                        entry2_global_rr;
  reg                         entry2_global_nxt;

// pd1
  reg  [`npuarc_PD1_PPN_RANGE]       entry2_ppn_r;
  reg  [`npuarc_PD1_PPN_RANGE]       entry2_ppn_nxt;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_UA_RANGE]        entry2_user_attr_r;
  reg  [`npuarc_PD1_UA_RANGE]        entry2_user_attr_nxt;

  reg                         entry2_wr_thru_r;
  reg                         entry2_wr_thru_nxt;
// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_PERM_RANGE]      entry2_perm_r;
  reg  [`npuarc_PD1_PERM_RANGE]      entry2_perm_nxt;

  reg                         entry2_cached_r;
  reg                         entry2_cached_nxt;
// leda NTL_CON32 on

//`let is_dtlb = (8 == 8);

assign entry2_vpn_rr = entry2_vpn_r;

assign entry2_asid_rr = entry2_asid_r;

assign entry2_shared_rr = entry2_shared_r;

assign entry2_lock_rr = entry2_lock_r;

assign entry2_size_rr = entry2_size_r;

assign entry2_valid_rr = entry2_valid_r;

assign entry2_global_rr = entry2_global_r;


// Registers for Entry 3
//  
// pd0
  reg  [`npuarc_PD0_VPN_RANGE]       entry3_vpn_r;
  wire [`npuarc_PD0_VPN_RANGE]       entry3_vpn_rr;
  reg  [`npuarc_PD0_VPN_RANGE]       entry3_vpn_nxt;

  reg  [`npuarc_PD0_ASID_RANGE]      entry3_asid_r;
  wire [`npuarc_PD0_ASID_RANGE]      entry3_asid_rr;
  reg  [`npuarc_PD0_ASID_RANGE]      entry3_asid_nxt;

  reg                         entry3_shared_r;
  wire                        entry3_shared_rr;

  reg                         entry3_shared_nxt;

//reg                         entry3_spare0_r;   // spare attr bit
//reg                         entry3_spare0_nxt;
       
  wire                        entry3_lock_r;
  wire                        entry3_lock_rr;
  reg                         entry3_lock_nxt;

  reg                         entry3_size_r;     // single bit for now
  wire                        entry3_size_rr;     // single bit for now
  reg                         entry3_size_nxt;

  reg                         entry3_valid_r;
  wire                        entry3_valid_rr;
  reg                         entry3_valid_nxt;

  reg                         entry3_global_r;
  wire                        entry3_global_rr;
  reg                         entry3_global_nxt;

// pd1
  reg  [`npuarc_PD1_PPN_RANGE]       entry3_ppn_r;
  reg  [`npuarc_PD1_PPN_RANGE]       entry3_ppn_nxt;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_UA_RANGE]        entry3_user_attr_r;
  reg  [`npuarc_PD1_UA_RANGE]        entry3_user_attr_nxt;

  reg                         entry3_wr_thru_r;
  reg                         entry3_wr_thru_nxt;
// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_PERM_RANGE]      entry3_perm_r;
  reg  [`npuarc_PD1_PERM_RANGE]      entry3_perm_nxt;

  reg                         entry3_cached_r;
  reg                         entry3_cached_nxt;
// leda NTL_CON32 on

//`let is_dtlb = (8 == 8);

assign entry3_vpn_rr = entry3_vpn_r;

assign entry3_asid_rr = entry3_asid_r;

assign entry3_shared_rr = entry3_shared_r;

assign entry3_lock_rr = entry3_lock_r;

assign entry3_size_rr = entry3_size_r;

assign entry3_valid_rr = entry3_valid_r;

assign entry3_global_rr = entry3_global_r;


// Registers for Entry 4
//  
// pd0
  reg  [`npuarc_PD0_VPN_RANGE]       entry4_vpn_r;
  wire [`npuarc_PD0_VPN_RANGE]       entry4_vpn_rr;
  reg  [`npuarc_PD0_VPN_RANGE]       entry4_vpn_nxt;

  reg  [`npuarc_PD0_ASID_RANGE]      entry4_asid_r;
  wire [`npuarc_PD0_ASID_RANGE]      entry4_asid_rr;
  reg  [`npuarc_PD0_ASID_RANGE]      entry4_asid_nxt;

  reg                         entry4_shared_r;
  wire                        entry4_shared_rr;

  reg                         entry4_shared_nxt;

//reg                         entry4_spare0_r;   // spare attr bit
//reg                         entry4_spare0_nxt;
       
  wire                        entry4_lock_r;
  wire                        entry4_lock_rr;
  reg                         entry4_lock_nxt;

  reg                         entry4_size_r;     // single bit for now
  wire                        entry4_size_rr;     // single bit for now
  reg                         entry4_size_nxt;

  reg                         entry4_valid_r;
  wire                        entry4_valid_rr;
  reg                         entry4_valid_nxt;

  reg                         entry4_global_r;
  wire                        entry4_global_rr;
  reg                         entry4_global_nxt;

// pd1
  reg  [`npuarc_PD1_PPN_RANGE]       entry4_ppn_r;
  reg  [`npuarc_PD1_PPN_RANGE]       entry4_ppn_nxt;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_UA_RANGE]        entry4_user_attr_r;
  reg  [`npuarc_PD1_UA_RANGE]        entry4_user_attr_nxt;

  reg                         entry4_wr_thru_r;
  reg                         entry4_wr_thru_nxt;
// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_PERM_RANGE]      entry4_perm_r;
  reg  [`npuarc_PD1_PERM_RANGE]      entry4_perm_nxt;

  reg                         entry4_cached_r;
  reg                         entry4_cached_nxt;
// leda NTL_CON32 on

//`let is_dtlb = (8 == 8);

assign entry4_vpn_rr = entry4_vpn_r;

assign entry4_asid_rr = entry4_asid_r;

assign entry4_shared_rr = entry4_shared_r;

assign entry4_lock_rr = entry4_lock_r;

assign entry4_size_rr = entry4_size_r;

assign entry4_valid_rr = entry4_valid_r;

assign entry4_global_rr = entry4_global_r;


// Registers for Entry 5
//  
// pd0
  reg  [`npuarc_PD0_VPN_RANGE]       entry5_vpn_r;
  wire [`npuarc_PD0_VPN_RANGE]       entry5_vpn_rr;
  reg  [`npuarc_PD0_VPN_RANGE]       entry5_vpn_nxt;

  reg  [`npuarc_PD0_ASID_RANGE]      entry5_asid_r;
  wire [`npuarc_PD0_ASID_RANGE]      entry5_asid_rr;
  reg  [`npuarc_PD0_ASID_RANGE]      entry5_asid_nxt;

  reg                         entry5_shared_r;
  wire                        entry5_shared_rr;

  reg                         entry5_shared_nxt;

//reg                         entry5_spare0_r;   // spare attr bit
//reg                         entry5_spare0_nxt;
       
  wire                        entry5_lock_r;
  wire                        entry5_lock_rr;
  reg                         entry5_lock_nxt;

  reg                         entry5_size_r;     // single bit for now
  wire                        entry5_size_rr;     // single bit for now
  reg                         entry5_size_nxt;

  reg                         entry5_valid_r;
  wire                        entry5_valid_rr;
  reg                         entry5_valid_nxt;

  reg                         entry5_global_r;
  wire                        entry5_global_rr;
  reg                         entry5_global_nxt;

// pd1
  reg  [`npuarc_PD1_PPN_RANGE]       entry5_ppn_r;
  reg  [`npuarc_PD1_PPN_RANGE]       entry5_ppn_nxt;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_UA_RANGE]        entry5_user_attr_r;
  reg  [`npuarc_PD1_UA_RANGE]        entry5_user_attr_nxt;

  reg                         entry5_wr_thru_r;
  reg                         entry5_wr_thru_nxt;
// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_PERM_RANGE]      entry5_perm_r;
  reg  [`npuarc_PD1_PERM_RANGE]      entry5_perm_nxt;

  reg                         entry5_cached_r;
  reg                         entry5_cached_nxt;
// leda NTL_CON32 on

//`let is_dtlb = (8 == 8);

assign entry5_vpn_rr = entry5_vpn_r;

assign entry5_asid_rr = entry5_asid_r;

assign entry5_shared_rr = entry5_shared_r;

assign entry5_lock_rr = entry5_lock_r;

assign entry5_size_rr = entry5_size_r;

assign entry5_valid_rr = entry5_valid_r;

assign entry5_global_rr = entry5_global_r;


// Registers for Entry 6
//  
// pd0
  reg  [`npuarc_PD0_VPN_RANGE]       entry6_vpn_r;
  wire [`npuarc_PD0_VPN_RANGE]       entry6_vpn_rr;
  reg  [`npuarc_PD0_VPN_RANGE]       entry6_vpn_nxt;

  reg  [`npuarc_PD0_ASID_RANGE]      entry6_asid_r;
  wire [`npuarc_PD0_ASID_RANGE]      entry6_asid_rr;
  reg  [`npuarc_PD0_ASID_RANGE]      entry6_asid_nxt;

  reg                         entry6_shared_r;
  wire                        entry6_shared_rr;

  reg                         entry6_shared_nxt;

//reg                         entry6_spare0_r;   // spare attr bit
//reg                         entry6_spare0_nxt;
       
  wire                        entry6_lock_r;
  wire                        entry6_lock_rr;
  reg                         entry6_lock_nxt;

  reg                         entry6_size_r;     // single bit for now
  wire                        entry6_size_rr;     // single bit for now
  reg                         entry6_size_nxt;

  reg                         entry6_valid_r;
  wire                        entry6_valid_rr;
  reg                         entry6_valid_nxt;

  reg                         entry6_global_r;
  wire                        entry6_global_rr;
  reg                         entry6_global_nxt;

// pd1
  reg  [`npuarc_PD1_PPN_RANGE]       entry6_ppn_r;
  reg  [`npuarc_PD1_PPN_RANGE]       entry6_ppn_nxt;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_UA_RANGE]        entry6_user_attr_r;
  reg  [`npuarc_PD1_UA_RANGE]        entry6_user_attr_nxt;

  reg                         entry6_wr_thru_r;
  reg                         entry6_wr_thru_nxt;
// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_PERM_RANGE]      entry6_perm_r;
  reg  [`npuarc_PD1_PERM_RANGE]      entry6_perm_nxt;

  reg                         entry6_cached_r;
  reg                         entry6_cached_nxt;
// leda NTL_CON32 on

//`let is_dtlb = (8 == 8);

assign entry6_vpn_rr = entry6_vpn_r;

assign entry6_asid_rr = entry6_asid_r;

assign entry6_shared_rr = entry6_shared_r;

assign entry6_lock_rr = entry6_lock_r;

assign entry6_size_rr = entry6_size_r;

assign entry6_valid_rr = entry6_valid_r;

assign entry6_global_rr = entry6_global_r;


// Registers for Entry 7
//  
// pd0
  reg  [`npuarc_PD0_VPN_RANGE]       entry7_vpn_r;
  wire [`npuarc_PD0_VPN_RANGE]       entry7_vpn_rr;
  reg  [`npuarc_PD0_VPN_RANGE]       entry7_vpn_nxt;

  reg  [`npuarc_PD0_ASID_RANGE]      entry7_asid_r;
  wire [`npuarc_PD0_ASID_RANGE]      entry7_asid_rr;
  reg  [`npuarc_PD0_ASID_RANGE]      entry7_asid_nxt;

  reg                         entry7_shared_r;
  wire                        entry7_shared_rr;

  reg                         entry7_shared_nxt;

//reg                         entry7_spare0_r;   // spare attr bit
//reg                         entry7_spare0_nxt;
       
  wire                        entry7_lock_r;
  wire                        entry7_lock_rr;
  reg                         entry7_lock_nxt;

  reg                         entry7_size_r;     // single bit for now
  wire                        entry7_size_rr;     // single bit for now
  reg                         entry7_size_nxt;

  reg                         entry7_valid_r;
  wire                        entry7_valid_rr;
  reg                         entry7_valid_nxt;

  reg                         entry7_global_r;
  wire                        entry7_global_rr;
  reg                         entry7_global_nxt;

// pd1
  reg  [`npuarc_PD1_PPN_RANGE]       entry7_ppn_r;
  reg  [`npuarc_PD1_PPN_RANGE]       entry7_ppn_nxt;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_UA_RANGE]        entry7_user_attr_r;
  reg  [`npuarc_PD1_UA_RANGE]        entry7_user_attr_nxt;

  reg                         entry7_wr_thru_r;
  reg                         entry7_wr_thru_nxt;
// leda NTL_CON32 on
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
  reg  [`npuarc_PD1_PERM_RANGE]      entry7_perm_r;
  reg  [`npuarc_PD1_PERM_RANGE]      entry7_perm_nxt;

  reg                         entry7_cached_r;
  reg                         entry7_cached_nxt;
// leda NTL_CON32 on

//`let is_dtlb = (8 == 8);

assign entry7_vpn_rr = entry7_vpn_r;

assign entry7_asid_rr = entry7_asid_r;

assign entry7_shared_rr = entry7_shared_r;

assign entry7_lock_rr = entry7_lock_r;

assign entry7_size_rr = entry7_size_r;

assign entry7_valid_rr = entry7_valid_r;

assign entry7_global_rr = entry7_global_r;



// Look-up Comb logic
//
  reg  [`npuarc_PD0_VPN_RANGE]     pd0_sz1pn_mask; //const
  reg  [`npuarc_PD1_PPN_RANGE]     pd1_sz1pn_mask; //const

  reg                       rslt0_lkup_valid;
  reg [`npuarc_DTLB_ENTRIES_RANGE] rslt0_vpn_match;
  reg [`npuarc_DTLB_ENTRIES_RANGE] rslt0_pid_match;
// leda NTL_CON12A off
// leda NTL_CON13A off
// LMD: undriven internal net Range:1-7
// LJ:  all bits are driven
  reg [`npuarc_DTLB_ENTRIES_RANGE] rslt0_entry_match_raw_1h;
// leda NTL_CON13A on
// leda NTL_CON12A on

  // for read data
  reg                       rslt0_shared_out;
  reg  [`npuarc_PD0_VPN_RANGE]     rslt0_vpn_out;
  reg                       rslt0_lock_out;
  reg                       rslt0_size_out;
  reg                       rslt0_valid_out;
  reg                       rslt0_global_out;
  reg  [`npuarc_PD0_ASID_RANGE]    rslt0_asid_out;

  reg                       rslt1_lkup_valid;
  reg [`npuarc_DTLB_ENTRIES_RANGE] rslt1_vpn_match;
  reg [`npuarc_DTLB_ENTRIES_RANGE] rslt1_pid_match;
// leda NTL_CON12A off
// leda NTL_CON13A off
// LMD: undriven internal net Range:1-7
// LJ:  all bits are driven
  reg [`npuarc_DTLB_ENTRIES_RANGE] rslt1_entry_match_raw_1h;
// leda NTL_CON13A on
// leda NTL_CON12A on

  // for read data
  reg                       rslt1_shared_out;
  reg  [`npuarc_PD0_VPN_RANGE]     rslt1_vpn_out;
  reg                       rslt1_lock_out;
  reg                       rslt1_size_out;
  reg                       rslt1_valid_out;
  reg                       rslt1_global_out;
  reg  [`npuarc_PD0_ASID_RANGE]    rslt1_asid_out;


  reg [`npuarc_DTLB_ENTRIES_RANGE] rslt_sasid_match;

//`for (8 = 0; 8 < 8; 8++)
//  reg [`PD0_VPN_RANGE]      vpn_mask8_r;
//`endfor

  // make one-hot select bus for reading addressed entry
  wire [`npuarc_DTLB_ENTRIES_RANGE] entry_rd_sel_1h;
  assign entry_rd_sel_1h = 8'h1 << entry_rd_addr;

  wire [`npuarc_DTLB_ENTRIES_RANGE] alloc_entry_mask;
  assign alloc_entry_mask = ~({8{1'b1}} << alloc_entries);

  reg [`npuarc_DTLB_ENTRIES_RANGE]  invalid_entries;

  wire                       req_size_r;
  wire                       req_global_r;

  assign req_size_r   = eager_match & entry_update_data[`npuarc_PCKD_PTE_SIZE];
  assign req_global_r = eager_match & entry_update_data[`npuarc_PCKD_PTE_GLOBAL];

// misc internal signals
// reg                         aux_write_en;
  
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Look-up Comb logic: checking vpn/asid/sasid against active TLB entries //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin :  i_match_PROC

  pd0_sz1pn_mask = {`npuarc_PD0_VPN_WIDTH{1'b1}};
  pd1_sz1pn_mask = {`npuarc_PD1_PPN_WIDTH{1'b1}};

// pre-compute shared-ASID match (result common to all lookup ports)
//
  rslt_sasid_match[0] = (shared_en_r & 
                           (  sasid_r[ entry0_asid_rr[`npuarc_PD0_SLIX_RANGE] ]
                            | sasid_force_match)
                         );
  rslt_sasid_match[1] = (shared_en_r & 
                           (  sasid_r[ entry1_asid_rr[`npuarc_PD0_SLIX_RANGE] ]
                            | sasid_force_match)
                         );
  rslt_sasid_match[2] = (shared_en_r & 
                           (  sasid_r[ entry2_asid_rr[`npuarc_PD0_SLIX_RANGE] ]
                            | sasid_force_match)
                         );
  rslt_sasid_match[3] = (shared_en_r & 
                           (  sasid_r[ entry3_asid_rr[`npuarc_PD0_SLIX_RANGE] ]
                            | sasid_force_match)
                         );
  rslt_sasid_match[4] = (shared_en_r & 
                           (  sasid_r[ entry4_asid_rr[`npuarc_PD0_SLIX_RANGE] ]
                            | sasid_force_match)
                         );
  rslt_sasid_match[5] = (shared_en_r & 
                           (  sasid_r[ entry5_asid_rr[`npuarc_PD0_SLIX_RANGE] ]
                            | sasid_force_match)
                         );
  rslt_sasid_match[6] = (shared_en_r & 
                           (  sasid_r[ entry6_asid_rr[`npuarc_PD0_SLIX_RANGE] ]
                            | sasid_force_match)
                         );
  rslt_sasid_match[7] = (shared_en_r & 
                           (  sasid_r[ entry7_asid_rr[`npuarc_PD0_SLIX_RANGE] ]
                            | sasid_force_match)
                         );

//--------------------------------------------------------------------------
// Match logic for lookup port 0
//--------------------------------------------------------------------------

  // use to quiet the input busses when not performing a lookup
  //rslt0_lkup_valid = utlb_en_r & req0_valid_r;
  rslt0_lkup_valid = req0_valid_r;

  // Compare request 0 vpn/asid with each uTLB entry, masking vpn bits not 
  // needed by the programmed size of each mapping.

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt0_vpn_match[0] = (entry0_valid_rr) & 
    ((entry0_size_rr | req_size_r) ? 
      // super-page match
      (~|(req0_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry0_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req0_vpn_r ^ entry0_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt0_pid_match[0] = 
    // Global highest priority
    (entry0_global_rr | req_global_r |
        (
          // ...then shared
          (entry0_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[0] :
          // not global, or shared; check asid
          (~|(req0_asid_r ^ entry0_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt0_vpn_match[1] = (entry1_valid_rr) & 
    ((entry1_size_rr | req_size_r) ? 
      // super-page match
      (~|(req0_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry1_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req0_vpn_r ^ entry1_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt0_pid_match[1] = 
    // Global highest priority
    (entry1_global_rr | req_global_r |
        (
          // ...then shared
          (entry1_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[1] :
          // not global, or shared; check asid
          (~|(req0_asid_r ^ entry1_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt0_vpn_match[2] = (entry2_valid_rr) & 
    ((entry2_size_rr | req_size_r) ? 
      // super-page match
      (~|(req0_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry2_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req0_vpn_r ^ entry2_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt0_pid_match[2] = 
    // Global highest priority
    (entry2_global_rr | req_global_r |
        (
          // ...then shared
          (entry2_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[2] :
          // not global, or shared; check asid
          (~|(req0_asid_r ^ entry2_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt0_vpn_match[3] = (entry3_valid_rr) & 
    ((entry3_size_rr | req_size_r) ? 
      // super-page match
      (~|(req0_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry3_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req0_vpn_r ^ entry3_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt0_pid_match[3] = 
    // Global highest priority
    (entry3_global_rr | req_global_r |
        (
          // ...then shared
          (entry3_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[3] :
          // not global, or shared; check asid
          (~|(req0_asid_r ^ entry3_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt0_vpn_match[4] = (entry4_valid_rr) & 
    ((entry4_size_rr | req_size_r) ? 
      // super-page match
      (~|(req0_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry4_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req0_vpn_r ^ entry4_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt0_pid_match[4] = 
    // Global highest priority
    (entry4_global_rr | req_global_r |
        (
          // ...then shared
          (entry4_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[4] :
          // not global, or shared; check asid
          (~|(req0_asid_r ^ entry4_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt0_vpn_match[5] = (entry5_valid_rr) & 
    ((entry5_size_rr | req_size_r) ? 
      // super-page match
      (~|(req0_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry5_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req0_vpn_r ^ entry5_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt0_pid_match[5] = 
    // Global highest priority
    (entry5_global_rr | req_global_r |
        (
          // ...then shared
          (entry5_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[5] :
          // not global, or shared; check asid
          (~|(req0_asid_r ^ entry5_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt0_vpn_match[6] = (entry6_valid_rr) & 
    ((entry6_size_rr | req_size_r) ? 
      // super-page match
      (~|(req0_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry6_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req0_vpn_r ^ entry6_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt0_pid_match[6] = 
    // Global highest priority
    (entry6_global_rr | req_global_r |
        (
          // ...then shared
          (entry6_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[6] :
          // not global, or shared; check asid
          (~|(req0_asid_r ^ entry6_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt0_vpn_match[7] = (entry7_valid_rr) & 
    ((entry7_size_rr | req_size_r) ? 
      // super-page match
      (~|(req0_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry7_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req0_vpn_r ^ entry7_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt0_pid_match[7] = 
    // Global highest priority
    (entry7_global_rr | req_global_r |
        (
          // ...then shared
          (entry7_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[7] :
          // not global, or shared; check asid
          (~|(req0_asid_r ^ entry7_asid_rr) )
        )
      );



//  Results for lookup port 0
//--------------------------------------------
  
//  Each entry's match result (result vector: 1 bit per entry)
//  
  rslt0_entry_match = 
                      rslt0_vpn_match
                    & rslt0_pid_match
                    & alloc_entry_mask // exclude unallocated entries
                    ;

// final match result; valid lookup matched any entry
//  
  rslt0_match  =  |rslt0_entry_match
//                  & rslt0_lkup_valid
                    ;

  rslt0_miss   = ~|rslt0_entry_match 
//                  & rslt0_lkup_valid
                    ;


// Find lowest set bit (one-hot result)
  rslt0_entry_match_raw_1h = find_first_set_1h(rslt0_entry_match);

  rslt0_entry_match_1h = {8{rslt0_lkup_valid}}
                          & rslt0_entry_match_raw_1h;

//  Find match index (of lowest set bit)...unused
  rslt0_match_index    = find_first_set(rslt0_entry_match);

//  Check for multiple hits
  rslt0_multiple_match = test_multi_set(rslt0_entry_match);


  // Shared lookup result and aux read output mux
  //-----------------------------------------------------------
  // (if simultaneous read and lookup, give precedence to read address)

  {// result pd1
   rslt0_ppn_out, 
   rslt0_user_attr_out,
   rslt0_wr_thru_out,
   rslt0_perm_out,
   rslt0_cached_out,
   // result pd0
   rslt0_shared_out,
   rslt0_vpn_out,
   rslt0_lock_out,
   rslt0_size_out,
   rslt0_valid_out,
   rslt0_global_out,
   rslt0_asid_out
  }  = 
      {`npuarc_PCKD_PTE_WIDTH{1'b0}}
    | ({`npuarc_PCKD_PTE_WIDTH{
            rslt0_entry_match_raw_1h[0]
          }}
        & {// entry pd1
           entry0_ppn_r,
           entry0_user_attr_r,
           entry0_wr_thru_r,
           entry0_perm_r,
           entry0_cached_r,
           // entry pd0
           entry0_shared_rr,
           entry0_vpn_rr,
           entry0_lock_rr,
           entry0_size_rr,
           entry0_valid_rr,
           entry0_global_rr,
           entry0_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
            rslt0_entry_match_raw_1h[1]
          }}
        & {// entry pd1
           entry1_ppn_r,
           entry1_user_attr_r,
           entry1_wr_thru_r,
           entry1_perm_r,
           entry1_cached_r,
           // entry pd0
           entry1_shared_rr,
           entry1_vpn_rr,
           entry1_lock_rr,
           entry1_size_rr,
           entry1_valid_rr,
           entry1_global_rr,
           entry1_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
            rslt0_entry_match_raw_1h[2]
          }}
        & {// entry pd1
           entry2_ppn_r,
           entry2_user_attr_r,
           entry2_wr_thru_r,
           entry2_perm_r,
           entry2_cached_r,
           // entry pd0
           entry2_shared_rr,
           entry2_vpn_rr,
           entry2_lock_rr,
           entry2_size_rr,
           entry2_valid_rr,
           entry2_global_rr,
           entry2_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
            rslt0_entry_match_raw_1h[3]
          }}
        & {// entry pd1
           entry3_ppn_r,
           entry3_user_attr_r,
           entry3_wr_thru_r,
           entry3_perm_r,
           entry3_cached_r,
           // entry pd0
           entry3_shared_rr,
           entry3_vpn_rr,
           entry3_lock_rr,
           entry3_size_rr,
           entry3_valid_rr,
           entry3_global_rr,
           entry3_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
            rslt0_entry_match_raw_1h[4]
          }}
        & {// entry pd1
           entry4_ppn_r,
           entry4_user_attr_r,
           entry4_wr_thru_r,
           entry4_perm_r,
           entry4_cached_r,
           // entry pd0
           entry4_shared_rr,
           entry4_vpn_rr,
           entry4_lock_rr,
           entry4_size_rr,
           entry4_valid_rr,
           entry4_global_rr,
           entry4_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
            rslt0_entry_match_raw_1h[5]
          }}
        & {// entry pd1
           entry5_ppn_r,
           entry5_user_attr_r,
           entry5_wr_thru_r,
           entry5_perm_r,
           entry5_cached_r,
           // entry pd0
           entry5_shared_rr,
           entry5_vpn_rr,
           entry5_lock_rr,
           entry5_size_rr,
           entry5_valid_rr,
           entry5_global_rr,
           entry5_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
            rslt0_entry_match_raw_1h[6]
          }}
        & {// entry pd1
           entry6_ppn_r,
           entry6_user_attr_r,
           entry6_wr_thru_r,
           entry6_perm_r,
           entry6_cached_r,
           // entry pd0
           entry6_shared_rr,
           entry6_vpn_rr,
           entry6_lock_rr,
           entry6_size_rr,
           entry6_valid_rr,
           entry6_global_rr,
           entry6_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
            rslt0_entry_match_raw_1h[7]
          }}
        & {// entry pd1
           entry7_ppn_r,
           entry7_user_attr_r,
           entry7_wr_thru_r,
           entry7_perm_r,
           entry7_cached_r,
           // entry pd0
           entry7_shared_rr,
           entry7_vpn_rr,
           entry7_lock_rr,
           entry7_size_rr,
           entry7_valid_rr,
           entry7_global_rr,
           entry7_asid_rr
          }
      )

    ;

  rslt0_match_size = rslt0_size_out;

//--------------------------------------------------------------------------
// Match logic for lookup port 1
//--------------------------------------------------------------------------

  // use to quiet the input busses when not performing a lookup
  //rslt1_lkup_valid = utlb_en_r & req1_valid_r;
  rslt1_lkup_valid = req1_valid_r;

  // Compare request 1 vpn/asid with each uTLB entry, masking vpn bits not 
  // needed by the programmed size of each mapping.

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt1_vpn_match[0] = (entry0_valid_rr) & 
    ((entry0_size_rr | req_size_r) ? 
      // super-page match
      (~|(req1_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry0_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req1_vpn_r ^ entry0_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt1_pid_match[0] = 
    // Global highest priority
    (entry0_global_rr | req_global_r |
        (
          // ...then shared
          (entry0_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[0] :
          // not global, or shared; check asid
          (~|(req1_asid_r ^ entry0_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt1_vpn_match[1] = (entry1_valid_rr) & 
    ((entry1_size_rr | req_size_r) ? 
      // super-page match
      (~|(req1_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry1_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req1_vpn_r ^ entry1_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt1_pid_match[1] = 
    // Global highest priority
    (entry1_global_rr | req_global_r |
        (
          // ...then shared
          (entry1_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[1] :
          // not global, or shared; check asid
          (~|(req1_asid_r ^ entry1_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt1_vpn_match[2] = (entry2_valid_rr) & 
    ((entry2_size_rr | req_size_r) ? 
      // super-page match
      (~|(req1_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry2_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req1_vpn_r ^ entry2_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt1_pid_match[2] = 
    // Global highest priority
    (entry2_global_rr | req_global_r |
        (
          // ...then shared
          (entry2_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[2] :
          // not global, or shared; check asid
          (~|(req1_asid_r ^ entry2_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt1_vpn_match[3] = (entry3_valid_rr) & 
    ((entry3_size_rr | req_size_r) ? 
      // super-page match
      (~|(req1_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry3_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req1_vpn_r ^ entry3_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt1_pid_match[3] = 
    // Global highest priority
    (entry3_global_rr | req_global_r |
        (
          // ...then shared
          (entry3_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[3] :
          // not global, or shared; check asid
          (~|(req1_asid_r ^ entry3_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt1_vpn_match[4] = (entry4_valid_rr) & 
    ((entry4_size_rr | req_size_r) ? 
      // super-page match
      (~|(req1_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry4_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req1_vpn_r ^ entry4_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt1_pid_match[4] = 
    // Global highest priority
    (entry4_global_rr | req_global_r |
        (
          // ...then shared
          (entry4_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[4] :
          // not global, or shared; check asid
          (~|(req1_asid_r ^ entry4_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt1_vpn_match[5] = (entry5_valid_rr) & 
    ((entry5_size_rr | req_size_r) ? 
      // super-page match
      (~|(req1_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry5_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req1_vpn_r ^ entry5_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt1_pid_match[5] = 
    // Global highest priority
    (entry5_global_rr | req_global_r |
        (
          // ...then shared
          (entry5_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[5] :
          // not global, or shared; check asid
          (~|(req1_asid_r ^ entry5_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt1_vpn_match[6] = (entry6_valid_rr) & 
    ((entry6_size_rr | req_size_r) ? 
      // super-page match
      (~|(req1_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry6_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req1_vpn_r ^ entry6_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt1_pid_match[6] = 
    // Global highest priority
    (entry6_global_rr | req_global_r |
        (
          // ...then shared
          (entry6_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[6] :
          // not global, or shared; check asid
          (~|(req1_asid_r ^ entry6_asid_rr) )
        )
      );

  // Compare page-size appropriate bits of VPN field and check entry valid bit
  rslt1_vpn_match[7] = (entry7_valid_rr) & 
    ((entry7_size_rr | req_size_r) ? 
      // super-page match
      (~|(req1_vpn_r[`npuarc_PD0_VPN_SZ1_RANGE] ^ entry7_vpn_rr[`npuarc_PD0_VPN_SZ1_RANGE])) :
      // Normal-page match, compare all bits
      ( ~|(req1_vpn_r ^ entry7_vpn_rr) )
    );

  // Check if global or shared and evaluate SASID or Compare ASID 
  rslt1_pid_match[7] = 
    // Global highest priority
    (entry7_global_rr | req_global_r |
        (
          // ...then shared
          (entry7_shared_rr) ?
          // if shared entry; check appropriate sasid reg bit and global en
          rslt_sasid_match[7] :
          // not global, or shared; check asid
          (~|(req1_asid_r ^ entry7_asid_rr) )
        )
      );



//  Results for lookup port 1
//--------------------------------------------
  
//  Each entry's match result (result vector: 1 bit per entry)
//  
  rslt1_entry_match = 
                      rslt1_vpn_match
                    & rslt1_pid_match
                    & alloc_entry_mask // exclude unallocated entries
                    ;

// final match result; valid lookup matched any entry
//  
  rslt1_match  =  |rslt1_entry_match
//                  & rslt1_lkup_valid
                    ;

  rslt1_miss   = ~|rslt1_entry_match 
//                  & rslt1_lkup_valid
                    ;


// Find lowest set bit (one-hot result)
  rslt1_entry_match_raw_1h = find_first_set_1h(rslt1_entry_match);

  rslt1_entry_match_1h = {8{rslt1_lkup_valid}}
                          & rslt1_entry_match_raw_1h;

//  Find match index (of lowest set bit)...unused
  rslt1_match_index    = find_first_set(rslt1_entry_match);

//  Check for multiple hits
  rslt1_multiple_match = test_multi_set(rslt1_entry_match);


  // Shared lookup result and aux read output mux
  //-----------------------------------------------------------
  // (if simultaneous read and lookup, give precedence to read address)

  {// result pd1
   rslt1_ppn_out, 
   rslt1_user_attr_out,
   rslt1_wr_thru_out,
   rslt1_perm_out,
   rslt1_cached_out,
   // result pd0
   rslt1_shared_out,
   rslt1_vpn_out,
   rslt1_lock_out,
   rslt1_size_out,
   rslt1_valid_out,
   rslt1_global_out,
   rslt1_asid_out
  }  = 
      {`npuarc_PCKD_PTE_WIDTH{1'b0}}
    | ({`npuarc_PCKD_PTE_WIDTH{
         (entry_rd_val ? 
            entry_rd_sel_1h[0] :
            rslt1_entry_match_raw_1h[0])
          }}
        & {// entry pd1
           entry0_ppn_r,
           entry0_user_attr_r,
           entry0_wr_thru_r,
           entry0_perm_r,
           entry0_cached_r,
           // entry pd0
           entry0_shared_rr,
           entry0_vpn_rr,
           entry0_lock_rr,
           entry0_size_rr,
           entry0_valid_rr,
           entry0_global_rr,
           entry0_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
         (entry_rd_val ? 
            entry_rd_sel_1h[1] :
            rslt1_entry_match_raw_1h[1])
          }}
        & {// entry pd1
           entry1_ppn_r,
           entry1_user_attr_r,
           entry1_wr_thru_r,
           entry1_perm_r,
           entry1_cached_r,
           // entry pd0
           entry1_shared_rr,
           entry1_vpn_rr,
           entry1_lock_rr,
           entry1_size_rr,
           entry1_valid_rr,
           entry1_global_rr,
           entry1_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
         (entry_rd_val ? 
            entry_rd_sel_1h[2] :
            rslt1_entry_match_raw_1h[2])
          }}
        & {// entry pd1
           entry2_ppn_r,
           entry2_user_attr_r,
           entry2_wr_thru_r,
           entry2_perm_r,
           entry2_cached_r,
           // entry pd0
           entry2_shared_rr,
           entry2_vpn_rr,
           entry2_lock_rr,
           entry2_size_rr,
           entry2_valid_rr,
           entry2_global_rr,
           entry2_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
         (entry_rd_val ? 
            entry_rd_sel_1h[3] :
            rslt1_entry_match_raw_1h[3])
          }}
        & {// entry pd1
           entry3_ppn_r,
           entry3_user_attr_r,
           entry3_wr_thru_r,
           entry3_perm_r,
           entry3_cached_r,
           // entry pd0
           entry3_shared_rr,
           entry3_vpn_rr,
           entry3_lock_rr,
           entry3_size_rr,
           entry3_valid_rr,
           entry3_global_rr,
           entry3_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
         (entry_rd_val ? 
            entry_rd_sel_1h[4] :
            rslt1_entry_match_raw_1h[4])
          }}
        & {// entry pd1
           entry4_ppn_r,
           entry4_user_attr_r,
           entry4_wr_thru_r,
           entry4_perm_r,
           entry4_cached_r,
           // entry pd0
           entry4_shared_rr,
           entry4_vpn_rr,
           entry4_lock_rr,
           entry4_size_rr,
           entry4_valid_rr,
           entry4_global_rr,
           entry4_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
         (entry_rd_val ? 
            entry_rd_sel_1h[5] :
            rslt1_entry_match_raw_1h[5])
          }}
        & {// entry pd1
           entry5_ppn_r,
           entry5_user_attr_r,
           entry5_wr_thru_r,
           entry5_perm_r,
           entry5_cached_r,
           // entry pd0
           entry5_shared_rr,
           entry5_vpn_rr,
           entry5_lock_rr,
           entry5_size_rr,
           entry5_valid_rr,
           entry5_global_rr,
           entry5_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
         (entry_rd_val ? 
            entry_rd_sel_1h[6] :
            rslt1_entry_match_raw_1h[6])
          }}
        & {// entry pd1
           entry6_ppn_r,
           entry6_user_attr_r,
           entry6_wr_thru_r,
           entry6_perm_r,
           entry6_cached_r,
           // entry pd0
           entry6_shared_rr,
           entry6_vpn_rr,
           entry6_lock_rr,
           entry6_size_rr,
           entry6_valid_rr,
           entry6_global_rr,
           entry6_asid_rr
          }
      )

    | ({`npuarc_PCKD_PTE_WIDTH{
         (entry_rd_val ? 
            entry_rd_sel_1h[7] :
            rslt1_entry_match_raw_1h[7])
          }}
        & {// entry pd1
           entry7_ppn_r,
           entry7_user_attr_r,
           entry7_wr_thru_r,
           entry7_perm_r,
           entry7_cached_r,
           // entry pd0
           entry7_shared_rr,
           entry7_vpn_rr,
           entry7_lock_rr,
           entry7_size_rr,
           entry7_valid_rr,
           entry7_global_rr,
           entry7_asid_rr
          }
      )

    ;

  entry_rd_data = {
                   // result pd1
                   rslt1_ppn_out & pd1_sz1pn_mask,
                   rslt1_user_attr_out,
                   rslt1_wr_thru_out,
                   rslt1_perm_out,
                   rslt1_cached_out,
                   // result pd0
                   rslt1_shared_out,
                   rslt1_vpn_out & pd0_sz1pn_mask,
                   1'b0,
                   rslt1_size_out,
                   rslt1_valid_out,
                   rslt1_global_out,
                   rslt1_asid_out
                   };


  rslt1_match_size = rslt1_size_out;


end // block: i_match_PROC
  
///////////////////////////////////////////////////////////////////////////
// collect status bits of invalid 

always @*
begin :  i_inval_status_PROC

  invalid_entries = {
                    ~entry7_valid_rr,
                    ~entry6_valid_rr,
                    ~entry5_valid_rr,
                    ~entry4_valid_rr,
                    ~entry3_valid_rr,
                    ~entry2_valid_rr,
                    ~entry1_valid_rr,
                    ~entry0_valid_rr
                   } & alloc_entry_mask; // exclude unallocated entries
end

// check if invalid entry available (for update)
assign inval_entry_avail = | invalid_entries;

// Find lowest invalid entry (for update)
assign inval_entry_1h = find_first_set_1h(invalid_entries);

  
///////////////////////////////////////////////////////////////////////////
// Generic functions used to generate lookup results
//  

// Find lowest set bit (one-hot result)
//
function automatic [`npuarc_DTLB_ENTRIES_RANGE] find_first_set_1h (
  input [`npuarc_DTLB_ENTRIES_RANGE] vec );
  reg found_one;
  integer i;
  begin
    found_one = 1'b0;
    find_first_set_1h = 8'd0;
    for (i=0; i<8; i=i+1)
    begin
      if (~found_one) // stop looking after first one
      begin
        if (vec[i]) 
        begin
          found_one = 1'b1;
          find_first_set_1h[i] = 1'b1;
        end
      end
    end
  end
endfunction
        

// spyglass disable_block W416
// SMD: Return type width 'm' is less than return value width 'n'
// SJ:  Only LSB few bits of integer i are used (auto-truncated)

// Find lowest set bit (bit ptr result)
//
function automatic [`npuarc_DTLB_INDEX_RANGE] find_first_set (
  input [`npuarc_DTLB_ENTRIES_RANGE] vec );
  reg found_one;
  integer i;
  begin
    found_one = 1'b0;
    find_first_set = 3'd0;
    for (i=0; i<8; i=i+1)
    begin
      if (~found_one) // stop looking after first one
      begin
        if (vec[i]) 
        begin
          found_one = 1'b1;
          find_first_set = $unsigned(i);
        end
      end
    end
  end
endfunction
// spyglass enable_block W416
        

// leda W489 off
//
function automatic test_multi_set (
  input [`npuarc_DTLB_ENTRIES_RANGE] vec );
  reg found_one;
  integer i;
  begin
    found_one = 1'b0;
    test_multi_set = 1'b0;
    for (i=0; i<8; i=i+1)
    begin
      if (vec[i]) 
      begin
        if (found_one)
          test_multi_set = 1'b1;
        found_one = 1'b1;
      end
    end
  end
endfunction
// leda W489 on
        

//  init_complete
//
always @(posedge clk or posedge rst)
begin : init_enable_PROC
  if (rst == 1'b1)
  begin
    init_enable_r   <= 1'b1;
    init_complete_r <= 1'b0;
  end
  else
  begin
      init_enable_r   <= 1'b0;

      init_complete_r <= init_enable_r       // set
                      || init_complete_r;    // retain;
  end
end

assign clr_entry_bits = init_enable_r && (~rst_init_disable_r);

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Write, update utlb entries                                             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//
// Write uTLB entry(ies) in uTLB miss that lead to JTLB hit.
// In this case only the uTLB entry selected by the Last Recently
// Used (LRU) mechanism is updated. During invalidation only the
// valid bits of all entries are cleared.
//

always @* 
begin :  i_entry_write_PROC

// Next value for each entry fields
   {// pd1
    entry0_ppn_nxt,
    entry0_user_attr_nxt,
    entry0_wr_thru_nxt,
    entry0_perm_nxt,
    entry0_cached_nxt,
    // pd0
    entry0_shared_nxt,
    entry0_vpn_nxt,
    entry0_lock_nxt,
    entry0_size_nxt,
    entry0_valid_nxt,
    entry0_global_nxt,
    entry0_asid_nxt
   } = entry_update_data;

   {// pd1
    entry1_ppn_nxt,
    entry1_user_attr_nxt,
    entry1_wr_thru_nxt,
    entry1_perm_nxt,
    entry1_cached_nxt,
    // pd0
    entry1_shared_nxt,
    entry1_vpn_nxt,
    entry1_lock_nxt,
    entry1_size_nxt,
    entry1_valid_nxt,
    entry1_global_nxt,
    entry1_asid_nxt
   } = entry_update_data;

   {// pd1
    entry2_ppn_nxt,
    entry2_user_attr_nxt,
    entry2_wr_thru_nxt,
    entry2_perm_nxt,
    entry2_cached_nxt,
    // pd0
    entry2_shared_nxt,
    entry2_vpn_nxt,
    entry2_lock_nxt,
    entry2_size_nxt,
    entry2_valid_nxt,
    entry2_global_nxt,
    entry2_asid_nxt
   } = entry_update_data;

   {// pd1
    entry3_ppn_nxt,
    entry3_user_attr_nxt,
    entry3_wr_thru_nxt,
    entry3_perm_nxt,
    entry3_cached_nxt,
    // pd0
    entry3_shared_nxt,
    entry3_vpn_nxt,
    entry3_lock_nxt,
    entry3_size_nxt,
    entry3_valid_nxt,
    entry3_global_nxt,
    entry3_asid_nxt
   } = entry_update_data;

   {// pd1
    entry4_ppn_nxt,
    entry4_user_attr_nxt,
    entry4_wr_thru_nxt,
    entry4_perm_nxt,
    entry4_cached_nxt,
    // pd0
    entry4_shared_nxt,
    entry4_vpn_nxt,
    entry4_lock_nxt,
    entry4_size_nxt,
    entry4_valid_nxt,
    entry4_global_nxt,
    entry4_asid_nxt
   } = entry_update_data;

   {// pd1
    entry5_ppn_nxt,
    entry5_user_attr_nxt,
    entry5_wr_thru_nxt,
    entry5_perm_nxt,
    entry5_cached_nxt,
    // pd0
    entry5_shared_nxt,
    entry5_vpn_nxt,
    entry5_lock_nxt,
    entry5_size_nxt,
    entry5_valid_nxt,
    entry5_global_nxt,
    entry5_asid_nxt
   } = entry_update_data;

   {// pd1
    entry6_ppn_nxt,
    entry6_user_attr_nxt,
    entry6_wr_thru_nxt,
    entry6_perm_nxt,
    entry6_cached_nxt,
    // pd0
    entry6_shared_nxt,
    entry6_vpn_nxt,
    entry6_lock_nxt,
    entry6_size_nxt,
    entry6_valid_nxt,
    entry6_global_nxt,
    entry6_asid_nxt
   } = entry_update_data;

   {// pd1
    entry7_ppn_nxt,
    entry7_user_attr_nxt,
    entry7_wr_thru_nxt,
    entry7_perm_nxt,
    entry7_cached_nxt,
    // pd0
    entry7_shared_nxt,
    entry7_vpn_nxt,
    entry7_lock_nxt,
    entry7_size_nxt,
    entry7_valid_nxt,
    entry7_global_nxt,
    entry7_asid_nxt
   } = entry_update_data;

end
  
wire entry_update_1h_0;
wire entry_update_1h_1;
wire entry_update_1h_2;
wire entry_update_1h_3;
wire entry_update_1h_4;
wire entry_update_1h_5;
wire entry_update_1h_6;
wire entry_update_1h_7;

assign entry_update_1h_0 = entry_update_1h[0];
assign entry_update_1h_1 = entry_update_1h[1];
assign entry_update_1h_2 = entry_update_1h[2];
assign entry_update_1h_3 = entry_update_1h[3];
assign entry_update_1h_4 = entry_update_1h[4];
assign entry_update_1h_5 = entry_update_1h[5];
assign entry_update_1h_6 = entry_update_1h[6];
assign entry_update_1h_7 = entry_update_1h[7];

// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: FF has neither asynchronous set nor asynchronous reset
// SJ:  To enable skipping reset of entry data to facilitate debug

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining uTLB entry 0                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk)
begin : utlb_entry0_PROC
  if (clr_entry_bits)
  begin
//  pd0
    entry0_shared_r  <= 1'b0;
    entry0_vpn_r     <= `npuarc_PD0_VPN_WIDTH'h0;
    entry0_size_r    <= 1'b0;
    entry0_global_r  <= 1'b0;
    entry0_asid_r    <= `npuarc_PD0_ASID_WIDTH'h0;
// pd1
    entry0_ppn_r       <= `npuarc_PD1_PPN_WIDTH'h0;
    entry0_user_attr_r <= `npuarc_PD1_UA_WIDTH'd0;
    entry0_wr_thru_r   <= 1'b0;
    entry0_perm_r      <= `npuarc_PD1_PERM_WIDTH'd0;
    entry0_cached_r    <= 1'b0;
  end
  else if (entry_update_1h_0)
  begin
//  pd0
    entry0_shared_r  <= entry0_shared_nxt;

    entry0_vpn_r     <= entry0_vpn_nxt;
    entry0_size_r    <= entry0_size_nxt;
    entry0_global_r  <= entry0_global_nxt;
    entry0_asid_r    <= entry0_asid_nxt;
// pd1
    entry0_ppn_r       <= entry0_ppn_nxt;
    entry0_perm_r      <= entry0_perm_nxt;
    entry0_user_attr_r <= entry0_user_attr_nxt;
    entry0_wr_thru_r   <= entry0_wr_thru_nxt;
    entry0_cached_r    <= entry0_cached_nxt;
  end
end
// leda NTL_CON32 on

//  entry valid bits (on invalidate, update only valid bits)
//
wire   entry0_valid_cg0;
assign entry0_valid_cg0 = entry_update_1h_0 || invalidate_entries[0];

always @(posedge clk)
begin : utlb_entry0_valid_PROC
  if (clr_entry_bits)
  begin
    entry0_valid_r   <= 1'b0;
  end
  else if (entry0_valid_cg0)
  begin
    entry0_valid_r   <= entry_update_1h_0 && entry0_valid_nxt;
  end
end

assign  entry0_lock_r   = 1'b0;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining uTLB entry 1                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk)
begin : utlb_entry1_PROC
  if (clr_entry_bits)
  begin
//  pd0
    entry1_shared_r  <= 1'b0;
    entry1_vpn_r     <= `npuarc_PD0_VPN_WIDTH'h0;
    entry1_size_r    <= 1'b0;
    entry1_global_r  <= 1'b0;
    entry1_asid_r    <= `npuarc_PD0_ASID_WIDTH'h0;
// pd1
    entry1_ppn_r       <= `npuarc_PD1_PPN_WIDTH'h0;
    entry1_user_attr_r <= `npuarc_PD1_UA_WIDTH'd0;
    entry1_wr_thru_r   <= 1'b0;
    entry1_perm_r      <= `npuarc_PD1_PERM_WIDTH'd0;
    entry1_cached_r    <= 1'b0;
  end
  else if (entry_update_1h_1)
  begin
//  pd0
    entry1_shared_r  <= entry1_shared_nxt;

    entry1_vpn_r     <= entry1_vpn_nxt;
    entry1_size_r    <= entry1_size_nxt;
    entry1_global_r  <= entry1_global_nxt;
    entry1_asid_r    <= entry1_asid_nxt;
// pd1
    entry1_ppn_r       <= entry1_ppn_nxt;
    entry1_perm_r      <= entry1_perm_nxt;
    entry1_user_attr_r <= entry1_user_attr_nxt;
    entry1_wr_thru_r   <= entry1_wr_thru_nxt;
    entry1_cached_r    <= entry1_cached_nxt;
  end
end
// leda NTL_CON32 on

//  entry valid bits (on invalidate, update only valid bits)
//
wire   entry1_valid_cg0;
assign entry1_valid_cg0 = entry_update_1h_1 || invalidate_entries[1];

always @(posedge clk)
begin : utlb_entry1_valid_PROC
  if (clr_entry_bits)
  begin
    entry1_valid_r   <= 1'b0;
  end
  else if (entry1_valid_cg0)
  begin
    entry1_valid_r   <= entry_update_1h_1 && entry1_valid_nxt;
  end
end

assign  entry1_lock_r   = 1'b0;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining uTLB entry 2                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk)
begin : utlb_entry2_PROC
  if (clr_entry_bits)
  begin
//  pd0
    entry2_shared_r  <= 1'b0;
    entry2_vpn_r     <= `npuarc_PD0_VPN_WIDTH'h0;
    entry2_size_r    <= 1'b0;
    entry2_global_r  <= 1'b0;
    entry2_asid_r    <= `npuarc_PD0_ASID_WIDTH'h0;
// pd1
    entry2_ppn_r       <= `npuarc_PD1_PPN_WIDTH'h0;
    entry2_user_attr_r <= `npuarc_PD1_UA_WIDTH'd0;
    entry2_wr_thru_r   <= 1'b0;
    entry2_perm_r      <= `npuarc_PD1_PERM_WIDTH'd0;
    entry2_cached_r    <= 1'b0;
  end
  else if (entry_update_1h_2)
  begin
//  pd0
    entry2_shared_r  <= entry2_shared_nxt;

    entry2_vpn_r     <= entry2_vpn_nxt;
    entry2_size_r    <= entry2_size_nxt;
    entry2_global_r  <= entry2_global_nxt;
    entry2_asid_r    <= entry2_asid_nxt;
// pd1
    entry2_ppn_r       <= entry2_ppn_nxt;
    entry2_perm_r      <= entry2_perm_nxt;
    entry2_user_attr_r <= entry2_user_attr_nxt;
    entry2_wr_thru_r   <= entry2_wr_thru_nxt;
    entry2_cached_r    <= entry2_cached_nxt;
  end
end
// leda NTL_CON32 on

//  entry valid bits (on invalidate, update only valid bits)
//
wire   entry2_valid_cg0;
assign entry2_valid_cg0 = entry_update_1h_2 || invalidate_entries[2];

always @(posedge clk)
begin : utlb_entry2_valid_PROC
  if (clr_entry_bits)
  begin
    entry2_valid_r   <= 1'b0;
  end
  else if (entry2_valid_cg0)
  begin
    entry2_valid_r   <= entry_update_1h_2 && entry2_valid_nxt;
  end
end

assign  entry2_lock_r   = 1'b0;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining uTLB entry 3                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk)
begin : utlb_entry3_PROC
  if (clr_entry_bits)
  begin
//  pd0
    entry3_shared_r  <= 1'b0;
    entry3_vpn_r     <= `npuarc_PD0_VPN_WIDTH'h0;
    entry3_size_r    <= 1'b0;
    entry3_global_r  <= 1'b0;
    entry3_asid_r    <= `npuarc_PD0_ASID_WIDTH'h0;
// pd1
    entry3_ppn_r       <= `npuarc_PD1_PPN_WIDTH'h0;
    entry3_user_attr_r <= `npuarc_PD1_UA_WIDTH'd0;
    entry3_wr_thru_r   <= 1'b0;
    entry3_perm_r      <= `npuarc_PD1_PERM_WIDTH'd0;
    entry3_cached_r    <= 1'b0;
  end
  else if (entry_update_1h_3)
  begin
//  pd0
    entry3_shared_r  <= entry3_shared_nxt;

    entry3_vpn_r     <= entry3_vpn_nxt;
    entry3_size_r    <= entry3_size_nxt;
    entry3_global_r  <= entry3_global_nxt;
    entry3_asid_r    <= entry3_asid_nxt;
// pd1
    entry3_ppn_r       <= entry3_ppn_nxt;
    entry3_perm_r      <= entry3_perm_nxt;
    entry3_user_attr_r <= entry3_user_attr_nxt;
    entry3_wr_thru_r   <= entry3_wr_thru_nxt;
    entry3_cached_r    <= entry3_cached_nxt;
  end
end
// leda NTL_CON32 on

//  entry valid bits (on invalidate, update only valid bits)
//
wire   entry3_valid_cg0;
assign entry3_valid_cg0 = entry_update_1h_3 || invalidate_entries[3];

always @(posedge clk)
begin : utlb_entry3_valid_PROC
  if (clr_entry_bits)
  begin
    entry3_valid_r   <= 1'b0;
  end
  else if (entry3_valid_cg0)
  begin
    entry3_valid_r   <= entry_update_1h_3 && entry3_valid_nxt;
  end
end

assign  entry3_lock_r   = 1'b0;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining uTLB entry 4                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk)
begin : utlb_entry4_PROC
  if (clr_entry_bits)
  begin
//  pd0
    entry4_shared_r  <= 1'b0;
    entry4_vpn_r     <= `npuarc_PD0_VPN_WIDTH'h0;
    entry4_size_r    <= 1'b0;
    entry4_global_r  <= 1'b0;
    entry4_asid_r    <= `npuarc_PD0_ASID_WIDTH'h0;
// pd1
    entry4_ppn_r       <= `npuarc_PD1_PPN_WIDTH'h0;
    entry4_user_attr_r <= `npuarc_PD1_UA_WIDTH'd0;
    entry4_wr_thru_r   <= 1'b0;
    entry4_perm_r      <= `npuarc_PD1_PERM_WIDTH'd0;
    entry4_cached_r    <= 1'b0;
  end
  else if (entry_update_1h_4)
  begin
//  pd0
    entry4_shared_r  <= entry4_shared_nxt;

    entry4_vpn_r     <= entry4_vpn_nxt;
    entry4_size_r    <= entry4_size_nxt;
    entry4_global_r  <= entry4_global_nxt;
    entry4_asid_r    <= entry4_asid_nxt;
// pd1
    entry4_ppn_r       <= entry4_ppn_nxt;
    entry4_perm_r      <= entry4_perm_nxt;
    entry4_user_attr_r <= entry4_user_attr_nxt;
    entry4_wr_thru_r   <= entry4_wr_thru_nxt;
    entry4_cached_r    <= entry4_cached_nxt;
  end
end
// leda NTL_CON32 on

//  entry valid bits (on invalidate, update only valid bits)
//
wire   entry4_valid_cg0;
assign entry4_valid_cg0 = entry_update_1h_4 || invalidate_entries[4];

always @(posedge clk)
begin : utlb_entry4_valid_PROC
  if (clr_entry_bits)
  begin
    entry4_valid_r   <= 1'b0;
  end
  else if (entry4_valid_cg0)
  begin
    entry4_valid_r   <= entry_update_1h_4 && entry4_valid_nxt;
  end
end

assign  entry4_lock_r   = 1'b0;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining uTLB entry 5                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk)
begin : utlb_entry5_PROC
  if (clr_entry_bits)
  begin
//  pd0
    entry5_shared_r  <= 1'b0;
    entry5_vpn_r     <= `npuarc_PD0_VPN_WIDTH'h0;
    entry5_size_r    <= 1'b0;
    entry5_global_r  <= 1'b0;
    entry5_asid_r    <= `npuarc_PD0_ASID_WIDTH'h0;
// pd1
    entry5_ppn_r       <= `npuarc_PD1_PPN_WIDTH'h0;
    entry5_user_attr_r <= `npuarc_PD1_UA_WIDTH'd0;
    entry5_wr_thru_r   <= 1'b0;
    entry5_perm_r      <= `npuarc_PD1_PERM_WIDTH'd0;
    entry5_cached_r    <= 1'b0;
  end
  else if (entry_update_1h_5)
  begin
//  pd0
    entry5_shared_r  <= entry5_shared_nxt;

    entry5_vpn_r     <= entry5_vpn_nxt;
    entry5_size_r    <= entry5_size_nxt;
    entry5_global_r  <= entry5_global_nxt;
    entry5_asid_r    <= entry5_asid_nxt;
// pd1
    entry5_ppn_r       <= entry5_ppn_nxt;
    entry5_perm_r      <= entry5_perm_nxt;
    entry5_user_attr_r <= entry5_user_attr_nxt;
    entry5_wr_thru_r   <= entry5_wr_thru_nxt;
    entry5_cached_r    <= entry5_cached_nxt;
  end
end
// leda NTL_CON32 on

//  entry valid bits (on invalidate, update only valid bits)
//
wire   entry5_valid_cg0;
assign entry5_valid_cg0 = entry_update_1h_5 || invalidate_entries[5];

always @(posedge clk)
begin : utlb_entry5_valid_PROC
  if (clr_entry_bits)
  begin
    entry5_valid_r   <= 1'b0;
  end
  else if (entry5_valid_cg0)
  begin
    entry5_valid_r   <= entry_update_1h_5 && entry5_valid_nxt;
  end
end

assign  entry5_lock_r   = 1'b0;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining uTLB entry 6                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk)
begin : utlb_entry6_PROC
  if (clr_entry_bits)
  begin
//  pd0
    entry6_shared_r  <= 1'b0;
    entry6_vpn_r     <= `npuarc_PD0_VPN_WIDTH'h0;
    entry6_size_r    <= 1'b0;
    entry6_global_r  <= 1'b0;
    entry6_asid_r    <= `npuarc_PD0_ASID_WIDTH'h0;
// pd1
    entry6_ppn_r       <= `npuarc_PD1_PPN_WIDTH'h0;
    entry6_user_attr_r <= `npuarc_PD1_UA_WIDTH'd0;
    entry6_wr_thru_r   <= 1'b0;
    entry6_perm_r      <= `npuarc_PD1_PERM_WIDTH'd0;
    entry6_cached_r    <= 1'b0;
  end
  else if (entry_update_1h_6)
  begin
//  pd0
    entry6_shared_r  <= entry6_shared_nxt;

    entry6_vpn_r     <= entry6_vpn_nxt;
    entry6_size_r    <= entry6_size_nxt;
    entry6_global_r  <= entry6_global_nxt;
    entry6_asid_r    <= entry6_asid_nxt;
// pd1
    entry6_ppn_r       <= entry6_ppn_nxt;
    entry6_perm_r      <= entry6_perm_nxt;
    entry6_user_attr_r <= entry6_user_attr_nxt;
    entry6_wr_thru_r   <= entry6_wr_thru_nxt;
    entry6_cached_r    <= entry6_cached_nxt;
  end
end
// leda NTL_CON32 on

//  entry valid bits (on invalidate, update only valid bits)
//
wire   entry6_valid_cg0;
assign entry6_valid_cg0 = entry_update_1h_6 || invalidate_entries[6];

always @(posedge clk)
begin : utlb_entry6_valid_PROC
  if (clr_entry_bits)
  begin
    entry6_valid_r   <= 1'b0;
  end
  else if (entry6_valid_cg0)
  begin
    entry6_valid_r   <= entry_update_1h_6 && entry6_valid_nxt;
  end
end

assign  entry6_lock_r   = 1'b0;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining uTLB entry 7                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk)
begin : utlb_entry7_PROC
  if (clr_entry_bits)
  begin
//  pd0
    entry7_shared_r  <= 1'b0;
    entry7_vpn_r     <= `npuarc_PD0_VPN_WIDTH'h0;
    entry7_size_r    <= 1'b0;
    entry7_global_r  <= 1'b0;
    entry7_asid_r    <= `npuarc_PD0_ASID_WIDTH'h0;
// pd1
    entry7_ppn_r       <= `npuarc_PD1_PPN_WIDTH'h0;
    entry7_user_attr_r <= `npuarc_PD1_UA_WIDTH'd0;
    entry7_wr_thru_r   <= 1'b0;
    entry7_perm_r      <= `npuarc_PD1_PERM_WIDTH'd0;
    entry7_cached_r    <= 1'b0;
  end
  else if (entry_update_1h_7)
  begin
//  pd0
    entry7_shared_r  <= entry7_shared_nxt;

    entry7_vpn_r     <= entry7_vpn_nxt;
    entry7_size_r    <= entry7_size_nxt;
    entry7_global_r  <= entry7_global_nxt;
    entry7_asid_r    <= entry7_asid_nxt;
// pd1
    entry7_ppn_r       <= entry7_ppn_nxt;
    entry7_perm_r      <= entry7_perm_nxt;
    entry7_user_attr_r <= entry7_user_attr_nxt;
    entry7_wr_thru_r   <= entry7_wr_thru_nxt;
    entry7_cached_r    <= entry7_cached_nxt;
  end
end
// leda NTL_CON32 on

//  entry valid bits (on invalidate, update only valid bits)
//
wire   entry7_valid_cg0;
assign entry7_valid_cg0 = entry_update_1h_7 || invalidate_entries[7];

always @(posedge clk)
begin : utlb_entry7_valid_PROC
  if (clr_entry_bits)
  begin
    entry7_valid_r   <= 1'b0;
  end
  else if (entry7_valid_cg0)
  begin
    entry7_valid_r   <= entry_update_1h_7 && entry7_valid_nxt;
  end
end

assign  entry7_lock_r   = 1'b0;


// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01


endmodule // utlb
