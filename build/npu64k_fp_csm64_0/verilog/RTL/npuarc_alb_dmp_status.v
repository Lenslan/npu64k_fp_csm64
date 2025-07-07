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
//   ALB_DMP_STATUS                 
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the status bits (lock, dirty, lru) for the Data
//  Cache
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_status.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_status (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used     
  //////////// Port0, write only unaligned (CA)  ////////////////////////// 
  //
  input                        dc_status0_write_even,
  input [`npuarc_DC_IDX_RANGE]        dc_status0_even_addr,
  input [2:0]                  dc_status0_even_wem,
  input [`npuarc_DC_WAY_RANGE]        dc_status0_even_way_hot,
  input                        dc_status0_even_dirty,
  input                        dc_status0_even_lru,
  
  input                        dc_status0_write_odd,
  input [`npuarc_DC_IDX_RANGE]        dc_status0_odd_addr,
  input [2:0]                  dc_status0_odd_wem,
  input [`npuarc_DC_WAY_RANGE]        dc_status0_odd_way_hot,
  input                        dc_status0_odd_dirty,
  input                        dc_status0_odd_lru,
// leda NTL_CON37 on  
// leda NTL_CON13C on  
  //////////// Port1, Read/write aligned (DMU, AUX) ///////////////////////// 
  //
  input                        dc_status1_read,
  input                        dc_status1_write,
  input  [`npuarc_DC_IDX_RANGE]       dc_status1_addr,
  input                        dc_status1_odd,
  input  [2:0]                 dc_status1_wem,     // lock, dirty, lru 
  input [`npuarc_DC_WAY_RANGE]        dc_status1_way_hot,
  input                        dc_status1_lock,
  input                        dc_status1_dirty,
  input                        dc_status1_lru,
  
  output reg                   status1_lru_even_r,    // dc3 lru even
  output reg                   status1_lock_even_r,   // dc3 lock even
  output reg [`npuarc_DC_WAY_RANGE]   status1_dirty_even_r,  // dc3 dirty even

  output reg                   status1_lru_odd_r,    // dc3 lru odd
  output reg                   status1_lock_odd_r,   // dc3 lock odd
  output reg [`npuarc_DC_WAY_RANGE]   status1_dirty_odd_r,  // dc3 dirty odd

  
  ////////// General input signals ///////////////////////////////////////////
  //
  input                        clk,
  input                        rst_a
);

// Local declarations
//

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
// Port0 
//
reg                  status0_write_even_r;
reg [`npuarc_DC_IDX_RANGE]  status0_even_addr_r;
reg [1:0]            status0_even_wem_r;
reg [`npuarc_DC_WAY_RANGE]  status0_even_way_hot_r;
reg                  status0_even_dirty_r;
reg                  status0_even_lru_r;

reg                  status0_write_odd_r;
reg [`npuarc_DC_IDX_RANGE]  status0_odd_addr_r;
reg [1:0]            status0_odd_wem_r;
reg [`npuarc_DC_WAY_RANGE]  status0_odd_way_hot_r;
reg                  status0_odd_dirty_r;
reg                  status0_odd_lru_r;

// Port1 
//
reg                  status1_read_even_r;
reg                  status1_read_odd_r;
reg                  status1_write_even_r;
reg                  status1_write_odd_r;
reg [`npuarc_DC_IDX_RANGE]  status1_addr_r;
reg [2:0]            status1_wem_r;
reg [`npuarc_DC_WAY_RANGE]  status1_way_hot_r;
reg                  status1_lock_r;
reg                  status1_dirty_r;
reg                  status1_lru_r;

wire [`npuarc_DC_IDX_RANGE] status1_addr_incr;

reg                  status1_lru_even_nxt;    
reg                  status1_lock_even_nxt;   
reg [`npuarc_DC_WAY_RANGE]  status1_dirty_even_nxt;  

reg                  status1_lru_odd_nxt;    
reg                  status1_lock_odd_nxt;   
reg [`npuarc_DC_WAY_RANGE]  status1_dirty_odd_nxt;  


// Status flops
//
reg [`npuarc_DC_STATUS_RANGE]  status_lock_even_r;
reg [`npuarc_DC_STATUS_RANGE]  status_lock_odd_r;
reg [`npuarc_DC_STATUS_RANGE]  status_lock_even_nxt;
reg [`npuarc_DC_STATUS_RANGE]  status_lock_odd_nxt;

reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r0;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt0;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r0;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt0;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r1;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt1;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r1;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt1;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r2;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt2;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r2;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt2;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r3;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt3;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r3;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt3;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r4;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt4;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r4;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt4;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r5;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt5;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r5;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt5;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r6;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt6;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r6;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt6;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r7;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt7;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r7;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt7;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r8;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt8;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r8;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt8;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r9;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt9;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r9;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt9;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r10;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt10;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r10;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt10;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r11;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt11;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r11;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt11;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r12;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt12;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r12;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt12;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r13;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt13;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r13;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt13;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r14;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt14;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r14;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt14;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r15;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt15;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r15;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt15;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r16;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt16;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r16;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt16;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r17;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt17;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r17;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt17;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r18;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt18;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r18;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt18;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r19;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt19;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r19;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt19;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r20;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt20;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r20;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt20;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r21;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt21;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r21;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt21;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r22;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt22;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r22;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt22;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r23;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt23;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r23;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt23;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r24;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt24;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r24;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt24;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r25;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt25;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r25;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt25;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r26;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt26;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r26;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt26;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r27;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt27;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r27;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt27;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r28;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt28;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r28;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt28;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r29;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt29;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r29;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt29;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r30;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt30;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r30;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt30;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r31;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt31;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r31;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt31;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r32;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt32;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r32;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt32;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r33;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt33;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r33;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt33;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r34;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt34;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r34;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt34;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r35;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt35;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r35;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt35;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r36;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt36;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r36;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt36;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r37;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt37;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r37;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt37;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r38;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt38;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r38;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt38;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r39;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt39;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r39;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt39;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r40;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt40;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r40;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt40;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r41;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt41;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r41;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt41;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r42;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt42;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r42;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt42;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r43;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt43;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r43;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt43;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r44;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt44;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r44;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt44;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r45;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt45;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r45;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt45;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r46;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt46;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r46;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt46;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r47;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt47;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r47;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt47;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r48;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt48;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r48;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt48;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r49;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt49;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r49;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt49;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r50;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt50;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r50;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt50;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r51;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt51;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r51;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt51;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r52;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt52;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r52;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt52;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r53;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt53;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r53;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt53;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r54;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt54;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r54;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt54;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r55;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt55;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r55;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt55;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r56;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt56;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r56;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt56;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r57;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt57;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r57;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt57;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r58;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt58;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r58;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt58;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r59;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt59;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r59;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt59;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r60;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt60;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r60;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt60;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r61;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt61;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r61;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt61;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r62;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt62;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r62;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt62;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r63;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt63;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r63;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt63;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r64;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt64;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r64;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt64;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r65;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt65;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r65;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt65;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r66;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt66;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r66;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt66;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r67;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt67;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r67;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt67;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r68;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt68;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r68;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt68;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r69;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt69;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r69;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt69;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r70;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt70;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r70;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt70;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r71;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt71;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r71;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt71;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r72;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt72;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r72;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt72;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r73;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt73;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r73;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt73;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r74;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt74;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r74;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt74;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r75;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt75;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r75;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt75;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r76;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt76;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r76;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt76;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r77;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt77;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r77;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt77;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r78;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt78;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r78;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt78;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r79;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt79;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r79;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt79;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r80;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt80;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r80;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt80;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r81;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt81;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r81;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt81;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r82;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt82;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r82;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt82;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r83;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt83;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r83;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt83;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r84;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt84;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r84;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt84;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r85;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt85;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r85;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt85;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r86;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt86;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r86;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt86;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r87;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt87;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r87;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt87;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r88;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt88;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r88;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt88;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r89;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt89;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r89;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt89;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r90;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt90;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r90;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt90;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r91;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt91;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r91;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt91;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r92;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt92;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r92;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt92;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r93;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt93;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r93;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt93;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r94;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt94;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r94;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt94;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r95;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt95;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r95;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt95;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r96;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt96;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r96;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt96;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r97;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt97;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r97;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt97;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r98;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt98;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r98;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt98;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r99;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt99;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r99;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt99;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r100;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt100;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r100;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt100;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r101;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt101;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r101;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt101;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r102;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt102;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r102;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt102;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r103;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt103;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r103;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt103;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r104;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt104;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r104;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt104;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r105;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt105;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r105;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt105;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r106;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt106;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r106;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt106;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r107;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt107;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r107;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt107;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r108;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt108;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r108;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt108;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r109;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt109;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r109;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt109;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r110;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt110;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r110;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt110;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r111;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt111;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r111;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt111;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r112;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt112;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r112;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt112;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r113;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt113;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r113;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt113;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r114;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt114;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r114;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt114;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r115;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt115;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r115;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt115;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r116;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt116;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r116;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt116;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r117;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt117;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r117;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt117;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r118;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt118;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r118;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt118;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r119;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt119;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r119;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt119;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r120;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt120;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r120;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt120;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r121;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt121;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r121;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt121;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r122;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt122;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r122;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt122;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r123;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt123;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r123;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt123;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r124;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt124;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r124;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt124;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r125;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt125;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r125;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt125;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r126;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt126;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r126;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt126;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r127;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_nxt127;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r127;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_nxt127;
reg [`npuarc_DC_WAY_RANGE]     status_dirty_even_r[`npuarc_DC_STATUS_RANGE];
reg [`npuarc_DC_WAY_RANGE]     status_dirty_odd_r[`npuarc_DC_STATUS_RANGE];

reg [`npuarc_DC_STATUS_RANGE]  status_lru_even_r;
reg [`npuarc_DC_STATUS_RANGE]  status_lru_odd_r;
reg [`npuarc_DC_STATUS_RANGE]  status_lru_even_nxt;
reg [`npuarc_DC_STATUS_RANGE]  status_lru_odd_nxt;
// leda NTL_CON32 on

// -----------------------------------------------------------------
// P0: CA write (even, odd)                  Dirty & LRU
// P1: DMU, AUX read/write aligned           Lock, Dirty and LRU
// P2: SMP read aligned                      Dirty


parameter LOCK  = 2;
parameter DIRTY = 1;
parameter LRU   = 0;

// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor. Never overflows
//
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
assign status1_addr_incr = status1_addr_r + 1'b1;
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on

//////////////////////////////////////////////////////////////////////////////
// @ Asynchronous process: Read port 1
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : status1_read_PROC
  status1_lru_even_nxt     = status1_lru_even_r;  
  status1_lock_even_nxt    = status1_lock_even_r; 
  status1_dirty_even_nxt   = status1_dirty_even_r;
  
  // Aux reads two sets at the time (even, odd)
  //
  status1_lru_odd_nxt      = status1_lru_odd_r;  
  status1_lock_odd_nxt     = status1_lock_odd_r; 
  status1_dirty_odd_nxt    = status1_dirty_odd_r;
  
  case (1'b1)
  status1_read_even_r: 
  begin
    status1_lru_even_nxt    = status_lru_even_r[status1_addr_r];
    status1_lock_even_nxt   = status_lock_even_r[status1_addr_r];
    status1_dirty_even_nxt  = status_dirty_even_r[status1_addr_r];
    
    status1_lru_odd_nxt     = status_lru_odd_r[status1_addr_r];
    status1_lock_odd_nxt    = status_lock_odd_r[status1_addr_r];
    status1_dirty_odd_nxt   = status_dirty_odd_r[status1_addr_r];
  end
  
  
  status1_read_odd_r:
  begin
    status1_lru_even_nxt    = status_lru_even_r[status1_addr_incr];
    status1_lock_even_nxt   = status_lock_even_r[status1_addr_incr];
    status1_dirty_even_nxt  = status_dirty_even_r[status1_addr_incr];
    
    status1_lru_odd_nxt     = status_lru_odd_r[status1_addr_r];
    status1_lock_odd_nxt    = status_lock_odd_r[status1_addr_r];
    status1_dirty_odd_nxt   = status_dirty_odd_r[status1_addr_r];
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept  
  default:
    ;
  endcase
end


// spyglass enable_block W193
//////////////////////////////////////////////////////////////////////////////
// @ Clock enables
//
//////////////////////////////////////////////////////////////////////////////
reg   status0_write_even_cg0;
reg   status0_write_odd_cg0;

reg   status1_write_even_cg0;
reg   status1_write_odd_cg0;

always @*
begin: status_write_cg_PROC
  // Port 0
  //
  status0_write_even_cg0 = dc_status0_write_even | status0_write_even_r;
  status0_write_odd_cg0  = dc_status0_write_odd  | status0_write_odd_r;
  
  // Port 1
  //
  status1_write_even_cg0 = dc_status1_write | status1_write_even_r;
  status1_write_odd_cg0  = dc_status1_write | status1_write_odd_r;
end

reg   status1_read_even_cg0;
reg   status1_read_odd_cg0;


always @*
begin: status_read_cg_PROC
  // Port 1
  //
  status1_read_even_cg0 = dc_status1_read | status1_read_even_r;
  status1_read_odd_cg0  = dc_status1_read | status1_read_odd_r;
  
end

//////////////////////////////////////////////////////////////////////////////
// @ Synchronous processes: write port 0
//
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : status0_write_even_reg_PROC
  if (rst_a == 1'b1)
  begin
    status0_write_even_r    <= 1'b0;
  end
  else if (status0_write_even_cg0)
  begin
    status0_write_even_r <= dc_status0_write_even;
  end
end

always @(posedge clk or posedge rst_a)
begin : status0_write_odd_reg_PROC
  if (rst_a == 1'b1)
  begin
    status0_write_odd_r <= 1'b0;
  end
  else if (status0_write_odd_cg0)
  begin
    status0_write_odd_r <= dc_status0_write_odd;
  end
end


// leda NTL_CON13C off
// leda NTL_RST03 off
// leda NTL_CON32 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used

// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin : status0_even_PROC
  if (dc_status0_write_even == 1'b1)
  begin
    status0_even_addr_r    <= dc_status0_even_addr;
    status0_even_wem_r     <= dc_status0_even_wem[1:0];
    status0_even_way_hot_r <= dc_status0_even_way_hot;
    status0_even_dirty_r   <= dc_status0_even_dirty;
    status0_even_lru_r     <= dc_status0_even_lru;     
  end
end

always @(posedge clk)
begin : status0_odd_PROC
  if (dc_status0_write_odd == 1'b1)
  begin
    status0_odd_addr_r    <= dc_status0_odd_addr;
    status0_odd_wem_r     <= dc_status0_odd_wem[1:0];
    status0_odd_way_hot_r <= dc_status0_odd_way_hot;
    status0_odd_dirty_r   <= dc_status0_odd_dirty;
    status0_odd_lru_r     <= dc_status0_odd_lru;      
  end
end
 // leda S_1C_R on
// leda NTL_CON32 on
// leda NTL_RST03 on
// leda NTL_CON13C on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
//////////////////////////////////////////////////////////////////////////////
// @ Synchronous processes: write port 1
//
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : status1_write_even_reg_PROC
  if (rst_a == 1'b1)
  begin
    status1_write_even_r    <= 1'b0;
  end
  else if (status1_write_even_cg0)
  begin
    status1_write_even_r <= dc_status1_write & (~dc_status1_odd);
  end
end

always @(posedge clk or posedge rst_a)
begin : status1_write_odd_reg_PROC
  if (rst_a == 1'b1)
  begin
    status1_write_odd_r     <= 1'b0;
  end
  else if (status1_write_odd_cg0)
  begin
    status1_write_odd_r <= dc_status1_write  & dc_status1_odd;
  end
end

// leda NTL_RST03 off
// leda G_551_1_C off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Datapath element, doesn't require reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin : status1_addr_PROC
  if (  (dc_status1_read  == 1'b1) | (dc_status1_write == 1'b1))
  begin
    status1_addr_r    <= dc_status1_addr;  
  end
end
// leda NTL_CON13C off
// leda NTL_CON32 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
always @(posedge clk)
begin : status1_flag_PROC
  if (dc_status1_write == 1'b1)
  begin
    status1_wem_r     <= dc_status1_wem;
    status1_way_hot_r <= dc_status1_way_hot;
    status1_lock_r    <= dc_status1_lock;
    status1_dirty_r   <= dc_status1_dirty;
    status1_lru_r     <= dc_status1_lru;      
  end
end
// leda S_1C_R on
// leda NTL_CON32 on
// leda NTL_CON13C on
// leda NTL_RST03 on
// leda G_551_1_C on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01


//////////////////////////////////////////////////////////////////////////////
// @ Synchronous processes: arrays
//
//////////////////////////////////////////////////////////////////////////////

// leda NTL_RST03 off
// leda G_551_1_C off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  This is modeling a memoru. Reset is not needed
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  This is modeling a memoru. Reset is not needed
//
// spyglass disable_block ResetFlop-ML
// SMD: Has neither asynchronous set/reset nor synchronous set/reset
// SJ:  This is modeling a memoru. Reset is not needed

// Lock even: can only be written by port1
//
always @*
begin : lock_even_sync_PROC
  status_lock_even_nxt = status_lock_even_r;
  if (  status1_write_even_r & status1_wem_r[LOCK] & status1_way_hot_r[0])
  begin
    status_lock_even_nxt[status1_addr_r] = status1_lock_r;
  end

end

// Lock odd: can only be written by port1
//
always @*
begin : lock_odd_sync_PROC
  status_lock_odd_nxt = status_lock_odd_r;
  if (  status1_write_odd_r & status1_wem_r[LOCK] & status1_way_hot_r[0])                             
  begin                                                   
    status_lock_odd_nxt[status1_addr_r] = status1_lock_r;  
  end                                                     
end
always @(posedge clk)
begin : lock_sync_PROC
    status_lock_even_r <= status_lock_even_nxt;
    status_lock_odd_r  <= status_lock_odd_nxt;  
end

// Dirty even : port0 or port1
//
// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions
//
always @*
begin
   status_dirty_even_r[0] = status_dirty_even_r0;
   status_dirty_even_r[1] = status_dirty_even_r1;
   status_dirty_even_r[2] = status_dirty_even_r2;
   status_dirty_even_r[3] = status_dirty_even_r3;
   status_dirty_even_r[4] = status_dirty_even_r4;
   status_dirty_even_r[5] = status_dirty_even_r5;
   status_dirty_even_r[6] = status_dirty_even_r6;
   status_dirty_even_r[7] = status_dirty_even_r7;
   status_dirty_even_r[8] = status_dirty_even_r8;
   status_dirty_even_r[9] = status_dirty_even_r9;
   status_dirty_even_r[10] = status_dirty_even_r10;
   status_dirty_even_r[11] = status_dirty_even_r11;
   status_dirty_even_r[12] = status_dirty_even_r12;
   status_dirty_even_r[13] = status_dirty_even_r13;
   status_dirty_even_r[14] = status_dirty_even_r14;
   status_dirty_even_r[15] = status_dirty_even_r15;
   status_dirty_even_r[16] = status_dirty_even_r16;
   status_dirty_even_r[17] = status_dirty_even_r17;
   status_dirty_even_r[18] = status_dirty_even_r18;
   status_dirty_even_r[19] = status_dirty_even_r19;
   status_dirty_even_r[20] = status_dirty_even_r20;
   status_dirty_even_r[21] = status_dirty_even_r21;
   status_dirty_even_r[22] = status_dirty_even_r22;
   status_dirty_even_r[23] = status_dirty_even_r23;
   status_dirty_even_r[24] = status_dirty_even_r24;
   status_dirty_even_r[25] = status_dirty_even_r25;
   status_dirty_even_r[26] = status_dirty_even_r26;
   status_dirty_even_r[27] = status_dirty_even_r27;
   status_dirty_even_r[28] = status_dirty_even_r28;
   status_dirty_even_r[29] = status_dirty_even_r29;
   status_dirty_even_r[30] = status_dirty_even_r30;
   status_dirty_even_r[31] = status_dirty_even_r31;
   status_dirty_even_r[32] = status_dirty_even_r32;
   status_dirty_even_r[33] = status_dirty_even_r33;
   status_dirty_even_r[34] = status_dirty_even_r34;
   status_dirty_even_r[35] = status_dirty_even_r35;
   status_dirty_even_r[36] = status_dirty_even_r36;
   status_dirty_even_r[37] = status_dirty_even_r37;
   status_dirty_even_r[38] = status_dirty_even_r38;
   status_dirty_even_r[39] = status_dirty_even_r39;
   status_dirty_even_r[40] = status_dirty_even_r40;
   status_dirty_even_r[41] = status_dirty_even_r41;
   status_dirty_even_r[42] = status_dirty_even_r42;
   status_dirty_even_r[43] = status_dirty_even_r43;
   status_dirty_even_r[44] = status_dirty_even_r44;
   status_dirty_even_r[45] = status_dirty_even_r45;
   status_dirty_even_r[46] = status_dirty_even_r46;
   status_dirty_even_r[47] = status_dirty_even_r47;
   status_dirty_even_r[48] = status_dirty_even_r48;
   status_dirty_even_r[49] = status_dirty_even_r49;
   status_dirty_even_r[50] = status_dirty_even_r50;
   status_dirty_even_r[51] = status_dirty_even_r51;
   status_dirty_even_r[52] = status_dirty_even_r52;
   status_dirty_even_r[53] = status_dirty_even_r53;
   status_dirty_even_r[54] = status_dirty_even_r54;
   status_dirty_even_r[55] = status_dirty_even_r55;
   status_dirty_even_r[56] = status_dirty_even_r56;
   status_dirty_even_r[57] = status_dirty_even_r57;
   status_dirty_even_r[58] = status_dirty_even_r58;
   status_dirty_even_r[59] = status_dirty_even_r59;
   status_dirty_even_r[60] = status_dirty_even_r60;
   status_dirty_even_r[61] = status_dirty_even_r61;
   status_dirty_even_r[62] = status_dirty_even_r62;
   status_dirty_even_r[63] = status_dirty_even_r63;
   status_dirty_even_r[64] = status_dirty_even_r64;
   status_dirty_even_r[65] = status_dirty_even_r65;
   status_dirty_even_r[66] = status_dirty_even_r66;
   status_dirty_even_r[67] = status_dirty_even_r67;
   status_dirty_even_r[68] = status_dirty_even_r68;
   status_dirty_even_r[69] = status_dirty_even_r69;
   status_dirty_even_r[70] = status_dirty_even_r70;
   status_dirty_even_r[71] = status_dirty_even_r71;
   status_dirty_even_r[72] = status_dirty_even_r72;
   status_dirty_even_r[73] = status_dirty_even_r73;
   status_dirty_even_r[74] = status_dirty_even_r74;
   status_dirty_even_r[75] = status_dirty_even_r75;
   status_dirty_even_r[76] = status_dirty_even_r76;
   status_dirty_even_r[77] = status_dirty_even_r77;
   status_dirty_even_r[78] = status_dirty_even_r78;
   status_dirty_even_r[79] = status_dirty_even_r79;
   status_dirty_even_r[80] = status_dirty_even_r80;
   status_dirty_even_r[81] = status_dirty_even_r81;
   status_dirty_even_r[82] = status_dirty_even_r82;
   status_dirty_even_r[83] = status_dirty_even_r83;
   status_dirty_even_r[84] = status_dirty_even_r84;
   status_dirty_even_r[85] = status_dirty_even_r85;
   status_dirty_even_r[86] = status_dirty_even_r86;
   status_dirty_even_r[87] = status_dirty_even_r87;
   status_dirty_even_r[88] = status_dirty_even_r88;
   status_dirty_even_r[89] = status_dirty_even_r89;
   status_dirty_even_r[90] = status_dirty_even_r90;
   status_dirty_even_r[91] = status_dirty_even_r91;
   status_dirty_even_r[92] = status_dirty_even_r92;
   status_dirty_even_r[93] = status_dirty_even_r93;
   status_dirty_even_r[94] = status_dirty_even_r94;
   status_dirty_even_r[95] = status_dirty_even_r95;
   status_dirty_even_r[96] = status_dirty_even_r96;
   status_dirty_even_r[97] = status_dirty_even_r97;
   status_dirty_even_r[98] = status_dirty_even_r98;
   status_dirty_even_r[99] = status_dirty_even_r99;
   status_dirty_even_r[100] = status_dirty_even_r100;
   status_dirty_even_r[101] = status_dirty_even_r101;
   status_dirty_even_r[102] = status_dirty_even_r102;
   status_dirty_even_r[103] = status_dirty_even_r103;
   status_dirty_even_r[104] = status_dirty_even_r104;
   status_dirty_even_r[105] = status_dirty_even_r105;
   status_dirty_even_r[106] = status_dirty_even_r106;
   status_dirty_even_r[107] = status_dirty_even_r107;
   status_dirty_even_r[108] = status_dirty_even_r108;
   status_dirty_even_r[109] = status_dirty_even_r109;
   status_dirty_even_r[110] = status_dirty_even_r110;
   status_dirty_even_r[111] = status_dirty_even_r111;
   status_dirty_even_r[112] = status_dirty_even_r112;
   status_dirty_even_r[113] = status_dirty_even_r113;
   status_dirty_even_r[114] = status_dirty_even_r114;
   status_dirty_even_r[115] = status_dirty_even_r115;
   status_dirty_even_r[116] = status_dirty_even_r116;
   status_dirty_even_r[117] = status_dirty_even_r117;
   status_dirty_even_r[118] = status_dirty_even_r118;
   status_dirty_even_r[119] = status_dirty_even_r119;
   status_dirty_even_r[120] = status_dirty_even_r120;
   status_dirty_even_r[121] = status_dirty_even_r121;
   status_dirty_even_r[122] = status_dirty_even_r122;
   status_dirty_even_r[123] = status_dirty_even_r123;
   status_dirty_even_r[124] = status_dirty_even_r124;
   status_dirty_even_r[125] = status_dirty_even_r125;
   status_dirty_even_r[126] = status_dirty_even_r126;
   status_dirty_even_r[127] = status_dirty_even_r127;
end

always @*
begin : dirty_even_sync_comb_PROC
    // Port 0
    //
    status_dirty_even_nxt0 =  status_dirty_even_r0;  
    status_dirty_even_nxt1 =  status_dirty_even_r1;  
    status_dirty_even_nxt2 =  status_dirty_even_r2;  
    status_dirty_even_nxt3 =  status_dirty_even_r3;  
    status_dirty_even_nxt4 =  status_dirty_even_r4;  
    status_dirty_even_nxt5 =  status_dirty_even_r5;  
    status_dirty_even_nxt6 =  status_dirty_even_r6;  
    status_dirty_even_nxt7 =  status_dirty_even_r7;  
    status_dirty_even_nxt8 =  status_dirty_even_r8;  
    status_dirty_even_nxt9 =  status_dirty_even_r9;  
    status_dirty_even_nxt10 =  status_dirty_even_r10;  
    status_dirty_even_nxt11 =  status_dirty_even_r11;  
    status_dirty_even_nxt12 =  status_dirty_even_r12;  
    status_dirty_even_nxt13 =  status_dirty_even_r13;  
    status_dirty_even_nxt14 =  status_dirty_even_r14;  
    status_dirty_even_nxt15 =  status_dirty_even_r15;  
    status_dirty_even_nxt16 =  status_dirty_even_r16;  
    status_dirty_even_nxt17 =  status_dirty_even_r17;  
    status_dirty_even_nxt18 =  status_dirty_even_r18;  
    status_dirty_even_nxt19 =  status_dirty_even_r19;  
    status_dirty_even_nxt20 =  status_dirty_even_r20;  
    status_dirty_even_nxt21 =  status_dirty_even_r21;  
    status_dirty_even_nxt22 =  status_dirty_even_r22;  
    status_dirty_even_nxt23 =  status_dirty_even_r23;  
    status_dirty_even_nxt24 =  status_dirty_even_r24;  
    status_dirty_even_nxt25 =  status_dirty_even_r25;  
    status_dirty_even_nxt26 =  status_dirty_even_r26;  
    status_dirty_even_nxt27 =  status_dirty_even_r27;  
    status_dirty_even_nxt28 =  status_dirty_even_r28;  
    status_dirty_even_nxt29 =  status_dirty_even_r29;  
    status_dirty_even_nxt30 =  status_dirty_even_r30;  
    status_dirty_even_nxt31 =  status_dirty_even_r31;  
    status_dirty_even_nxt32 =  status_dirty_even_r32;  
    status_dirty_even_nxt33 =  status_dirty_even_r33;  
    status_dirty_even_nxt34 =  status_dirty_even_r34;  
    status_dirty_even_nxt35 =  status_dirty_even_r35;  
    status_dirty_even_nxt36 =  status_dirty_even_r36;  
    status_dirty_even_nxt37 =  status_dirty_even_r37;  
    status_dirty_even_nxt38 =  status_dirty_even_r38;  
    status_dirty_even_nxt39 =  status_dirty_even_r39;  
    status_dirty_even_nxt40 =  status_dirty_even_r40;  
    status_dirty_even_nxt41 =  status_dirty_even_r41;  
    status_dirty_even_nxt42 =  status_dirty_even_r42;  
    status_dirty_even_nxt43 =  status_dirty_even_r43;  
    status_dirty_even_nxt44 =  status_dirty_even_r44;  
    status_dirty_even_nxt45 =  status_dirty_even_r45;  
    status_dirty_even_nxt46 =  status_dirty_even_r46;  
    status_dirty_even_nxt47 =  status_dirty_even_r47;  
    status_dirty_even_nxt48 =  status_dirty_even_r48;  
    status_dirty_even_nxt49 =  status_dirty_even_r49;  
    status_dirty_even_nxt50 =  status_dirty_even_r50;  
    status_dirty_even_nxt51 =  status_dirty_even_r51;  
    status_dirty_even_nxt52 =  status_dirty_even_r52;  
    status_dirty_even_nxt53 =  status_dirty_even_r53;  
    status_dirty_even_nxt54 =  status_dirty_even_r54;  
    status_dirty_even_nxt55 =  status_dirty_even_r55;  
    status_dirty_even_nxt56 =  status_dirty_even_r56;  
    status_dirty_even_nxt57 =  status_dirty_even_r57;  
    status_dirty_even_nxt58 =  status_dirty_even_r58;  
    status_dirty_even_nxt59 =  status_dirty_even_r59;  
    status_dirty_even_nxt60 =  status_dirty_even_r60;  
    status_dirty_even_nxt61 =  status_dirty_even_r61;  
    status_dirty_even_nxt62 =  status_dirty_even_r62;  
    status_dirty_even_nxt63 =  status_dirty_even_r63;  
    status_dirty_even_nxt64 =  status_dirty_even_r64;  
    status_dirty_even_nxt65 =  status_dirty_even_r65;  
    status_dirty_even_nxt66 =  status_dirty_even_r66;  
    status_dirty_even_nxt67 =  status_dirty_even_r67;  
    status_dirty_even_nxt68 =  status_dirty_even_r68;  
    status_dirty_even_nxt69 =  status_dirty_even_r69;  
    status_dirty_even_nxt70 =  status_dirty_even_r70;  
    status_dirty_even_nxt71 =  status_dirty_even_r71;  
    status_dirty_even_nxt72 =  status_dirty_even_r72;  
    status_dirty_even_nxt73 =  status_dirty_even_r73;  
    status_dirty_even_nxt74 =  status_dirty_even_r74;  
    status_dirty_even_nxt75 =  status_dirty_even_r75;  
    status_dirty_even_nxt76 =  status_dirty_even_r76;  
    status_dirty_even_nxt77 =  status_dirty_even_r77;  
    status_dirty_even_nxt78 =  status_dirty_even_r78;  
    status_dirty_even_nxt79 =  status_dirty_even_r79;  
    status_dirty_even_nxt80 =  status_dirty_even_r80;  
    status_dirty_even_nxt81 =  status_dirty_even_r81;  
    status_dirty_even_nxt82 =  status_dirty_even_r82;  
    status_dirty_even_nxt83 =  status_dirty_even_r83;  
    status_dirty_even_nxt84 =  status_dirty_even_r84;  
    status_dirty_even_nxt85 =  status_dirty_even_r85;  
    status_dirty_even_nxt86 =  status_dirty_even_r86;  
    status_dirty_even_nxt87 =  status_dirty_even_r87;  
    status_dirty_even_nxt88 =  status_dirty_even_r88;  
    status_dirty_even_nxt89 =  status_dirty_even_r89;  
    status_dirty_even_nxt90 =  status_dirty_even_r90;  
    status_dirty_even_nxt91 =  status_dirty_even_r91;  
    status_dirty_even_nxt92 =  status_dirty_even_r92;  
    status_dirty_even_nxt93 =  status_dirty_even_r93;  
    status_dirty_even_nxt94 =  status_dirty_even_r94;  
    status_dirty_even_nxt95 =  status_dirty_even_r95;  
    status_dirty_even_nxt96 =  status_dirty_even_r96;  
    status_dirty_even_nxt97 =  status_dirty_even_r97;  
    status_dirty_even_nxt98 =  status_dirty_even_r98;  
    status_dirty_even_nxt99 =  status_dirty_even_r99;  
    status_dirty_even_nxt100 =  status_dirty_even_r100;  
    status_dirty_even_nxt101 =  status_dirty_even_r101;  
    status_dirty_even_nxt102 =  status_dirty_even_r102;  
    status_dirty_even_nxt103 =  status_dirty_even_r103;  
    status_dirty_even_nxt104 =  status_dirty_even_r104;  
    status_dirty_even_nxt105 =  status_dirty_even_r105;  
    status_dirty_even_nxt106 =  status_dirty_even_r106;  
    status_dirty_even_nxt107 =  status_dirty_even_r107;  
    status_dirty_even_nxt108 =  status_dirty_even_r108;  
    status_dirty_even_nxt109 =  status_dirty_even_r109;  
    status_dirty_even_nxt110 =  status_dirty_even_r110;  
    status_dirty_even_nxt111 =  status_dirty_even_r111;  
    status_dirty_even_nxt112 =  status_dirty_even_r112;  
    status_dirty_even_nxt113 =  status_dirty_even_r113;  
    status_dirty_even_nxt114 =  status_dirty_even_r114;  
    status_dirty_even_nxt115 =  status_dirty_even_r115;  
    status_dirty_even_nxt116 =  status_dirty_even_r116;  
    status_dirty_even_nxt117 =  status_dirty_even_r117;  
    status_dirty_even_nxt118 =  status_dirty_even_r118;  
    status_dirty_even_nxt119 =  status_dirty_even_r119;  
    status_dirty_even_nxt120 =  status_dirty_even_r120;  
    status_dirty_even_nxt121 =  status_dirty_even_r121;  
    status_dirty_even_nxt122 =  status_dirty_even_r122;  
    status_dirty_even_nxt123 =  status_dirty_even_r123;  
    status_dirty_even_nxt124 =  status_dirty_even_r124;  
    status_dirty_even_nxt125 =  status_dirty_even_r125;  
    status_dirty_even_nxt126 =  status_dirty_even_r126;  
    status_dirty_even_nxt127 =  status_dirty_even_r127;  
  if( status0_even_addr_r == 0 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt0[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt0[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 1 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt1[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt1[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 2 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt2[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt2[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 3 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt3[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt3[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 4 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt4[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt4[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 5 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt5[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt5[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 6 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt6[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt6[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 7 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt7[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt7[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 8 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt8[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt8[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 9 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt9[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt9[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 10 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt10[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt10[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 11 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt11[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt11[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 12 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt12[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt12[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 13 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt13[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt13[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 14 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt14[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt14[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 15 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt15[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt15[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 16 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt16[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt16[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 17 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt17[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt17[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 18 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt18[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt18[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 19 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt19[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt19[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 20 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt20[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt20[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 21 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt21[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt21[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 22 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt22[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt22[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 23 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt23[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt23[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 24 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt24[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt24[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 25 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt25[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt25[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 26 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt26[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt26[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 27 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt27[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt27[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 28 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt28[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt28[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 29 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt29[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt29[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 30 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt30[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt30[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 31 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt31[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt31[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 32 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt32[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt32[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 33 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt33[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt33[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 34 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt34[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt34[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 35 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt35[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt35[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 36 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt36[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt36[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 37 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt37[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt37[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 38 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt38[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt38[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 39 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt39[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt39[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 40 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt40[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt40[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 41 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt41[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt41[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 42 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt42[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt42[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 43 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt43[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt43[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 44 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt44[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt44[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 45 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt45[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt45[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 46 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt46[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt46[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 47 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt47[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt47[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 48 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt48[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt48[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 49 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt49[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt49[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 50 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt50[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt50[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 51 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt51[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt51[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 52 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt52[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt52[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 53 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt53[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt53[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 54 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt54[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt54[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 55 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt55[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt55[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 56 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt56[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt56[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 57 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt57[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt57[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 58 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt58[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt58[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 59 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt59[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt59[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 60 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt60[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt60[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 61 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt61[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt61[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 62 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt62[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt62[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 63 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt63[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt63[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 64 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt64[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt64[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 65 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt65[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt65[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 66 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt66[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt66[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 67 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt67[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt67[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 68 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt68[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt68[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 69 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt69[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt69[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 70 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt70[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt70[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 71 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt71[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt71[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 72 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt72[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt72[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 73 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt73[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt73[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 74 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt74[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt74[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 75 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt75[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt75[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 76 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt76[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt76[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 77 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt77[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt77[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 78 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt78[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt78[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 79 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt79[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt79[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 80 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt80[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt80[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 81 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt81[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt81[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 82 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt82[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt82[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 83 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt83[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt83[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 84 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt84[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt84[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 85 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt85[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt85[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 86 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt86[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt86[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 87 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt87[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt87[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 88 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt88[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt88[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 89 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt89[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt89[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 90 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt90[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt90[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 91 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt91[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt91[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 92 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt92[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt92[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 93 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt93[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt93[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 94 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt94[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt94[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 95 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt95[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt95[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 96 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt96[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt96[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 97 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt97[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt97[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 98 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt98[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt98[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 99 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt99[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt99[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 100 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt100[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt100[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 101 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt101[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt101[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 102 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt102[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt102[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 103 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt103[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt103[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 104 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt104[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt104[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 105 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt105[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt105[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 106 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt106[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt106[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 107 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt107[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt107[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 108 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt108[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt108[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 109 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt109[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt109[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 110 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt110[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt110[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 111 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt111[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt111[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 112 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt112[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt112[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 113 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt113[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt113[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 114 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt114[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt114[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 115 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt115[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt115[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 116 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt116[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt116[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 117 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt117[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt117[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 118 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt118[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt118[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 119 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt119[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt119[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 120 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt120[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt120[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 121 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt121[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt121[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 122 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt122[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt122[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 123 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt123[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt123[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 124 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt124[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt124[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 125 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt125[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt125[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 126 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt126[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt126[1] =  status0_even_dirty_r;  
  end                                                                       
  end
  if( status0_even_addr_r == 127 )
  begin
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[0])                                         
  begin                                                                     
    status_dirty_even_nxt127[0] =  status0_even_dirty_r;  
  end                                                                       
  if (  status0_write_even_r                                                
      & status0_even_wem_r[DIRTY]                                           
      & status0_even_way_hot_r[1])                                         
  begin                                                                     
    status_dirty_even_nxt127[1] =  status0_even_dirty_r;  
  end                                                                       
  end
    // Port 1
    //
  if( status1_addr_r == 0 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt0[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt0[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 1 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt1[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt1[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 2 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt2[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt2[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 3 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt3[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt3[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 4 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt4[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt4[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 5 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt5[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt5[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 6 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt6[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt6[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 7 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt7[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt7[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 8 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt8[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt8[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 9 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt9[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt9[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 10 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt10[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt10[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 11 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt11[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt11[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 12 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt12[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt12[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 13 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt13[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt13[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 14 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt14[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt14[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 15 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt15[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt15[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 16 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt16[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt16[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 17 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt17[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt17[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 18 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt18[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt18[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 19 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt19[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt19[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 20 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt20[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt20[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 21 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt21[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt21[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 22 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt22[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt22[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 23 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt23[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt23[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 24 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt24[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt24[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 25 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt25[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt25[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 26 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt26[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt26[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 27 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt27[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt27[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 28 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt28[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt28[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 29 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt29[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt29[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 30 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt30[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt30[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 31 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt31[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt31[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 32 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt32[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt32[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 33 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt33[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt33[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 34 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt34[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt34[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 35 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt35[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt35[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 36 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt36[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt36[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 37 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt37[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt37[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 38 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt38[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt38[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 39 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt39[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt39[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 40 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt40[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt40[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 41 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt41[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt41[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 42 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt42[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt42[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 43 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt43[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt43[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 44 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt44[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt44[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 45 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt45[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt45[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 46 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt46[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt46[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 47 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt47[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt47[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 48 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt48[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt48[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 49 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt49[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt49[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 50 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt50[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt50[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 51 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt51[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt51[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 52 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt52[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt52[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 53 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt53[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt53[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 54 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt54[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt54[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 55 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt55[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt55[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 56 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt56[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt56[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 57 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt57[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt57[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 58 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt58[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt58[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 59 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt59[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt59[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 60 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt60[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt60[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 61 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt61[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt61[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 62 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt62[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt62[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 63 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt63[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt63[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 64 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt64[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt64[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 65 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt65[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt65[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 66 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt66[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt66[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 67 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt67[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt67[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 68 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt68[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt68[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 69 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt69[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt69[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 70 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt70[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt70[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 71 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt71[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt71[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 72 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt72[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt72[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 73 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt73[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt73[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 74 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt74[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt74[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 75 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt75[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt75[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 76 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt76[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt76[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 77 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt77[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt77[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 78 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt78[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt78[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 79 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt79[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt79[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 80 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt80[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt80[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 81 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt81[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt81[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 82 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt82[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt82[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 83 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt83[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt83[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 84 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt84[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt84[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 85 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt85[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt85[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 86 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt86[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt86[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 87 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt87[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt87[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 88 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt88[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt88[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 89 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt89[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt89[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 90 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt90[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt90[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 91 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt91[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt91[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 92 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt92[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt92[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 93 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt93[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt93[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 94 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt94[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt94[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 95 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt95[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt95[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 96 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt96[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt96[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 97 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt97[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt97[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 98 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt98[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt98[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 99 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt99[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt99[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 100 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt100[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt100[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 101 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt101[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt101[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 102 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt102[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt102[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 103 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt103[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt103[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 104 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt104[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt104[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 105 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt105[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt105[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 106 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt106[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt106[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 107 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt107[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt107[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 108 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt108[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt108[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 109 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt109[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt109[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 110 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt110[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt110[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 111 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt111[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt111[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 112 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt112[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt112[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 113 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt113[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt113[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 114 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt114[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt114[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 115 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt115[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt115[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 116 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt116[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt116[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 117 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt117[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt117[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 118 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt118[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt118[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 119 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt119[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt119[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 120 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt120[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt120[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 121 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt121[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt121[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 122 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt122[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt122[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 123 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt123[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt123[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 124 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt124[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt124[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 125 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt125[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt125[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 126 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt126[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt126[1] = status1_dirty_r;  
  end                                                            
  end
  if( status1_addr_r == 127 )
  begin
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[0])                                   
  begin                                                          
    status_dirty_even_nxt127[0] = status1_dirty_r;  
  end                                                            
  if (  status1_write_even_r                                     
      & status1_wem_r[DIRTY]                                     
      & status1_way_hot_r[1])                                   
  begin                                                          
    status_dirty_even_nxt127[1] = status1_dirty_r;  
  end                                                            
  end
end

always @(posedge clk)
begin : dirty_even_sync_PROC
    status_dirty_even_r0 <=  status_dirty_even_nxt0;  
    status_dirty_even_r1 <=  status_dirty_even_nxt1;  
    status_dirty_even_r2 <=  status_dirty_even_nxt2;  
    status_dirty_even_r3 <=  status_dirty_even_nxt3;  
    status_dirty_even_r4 <=  status_dirty_even_nxt4;  
    status_dirty_even_r5 <=  status_dirty_even_nxt5;  
    status_dirty_even_r6 <=  status_dirty_even_nxt6;  
    status_dirty_even_r7 <=  status_dirty_even_nxt7;  
    status_dirty_even_r8 <=  status_dirty_even_nxt8;  
    status_dirty_even_r9 <=  status_dirty_even_nxt9;  
    status_dirty_even_r10 <=  status_dirty_even_nxt10;  
    status_dirty_even_r11 <=  status_dirty_even_nxt11;  
    status_dirty_even_r12 <=  status_dirty_even_nxt12;  
    status_dirty_even_r13 <=  status_dirty_even_nxt13;  
    status_dirty_even_r14 <=  status_dirty_even_nxt14;  
    status_dirty_even_r15 <=  status_dirty_even_nxt15;  
    status_dirty_even_r16 <=  status_dirty_even_nxt16;  
    status_dirty_even_r17 <=  status_dirty_even_nxt17;  
    status_dirty_even_r18 <=  status_dirty_even_nxt18;  
    status_dirty_even_r19 <=  status_dirty_even_nxt19;  
    status_dirty_even_r20 <=  status_dirty_even_nxt20;  
    status_dirty_even_r21 <=  status_dirty_even_nxt21;  
    status_dirty_even_r22 <=  status_dirty_even_nxt22;  
    status_dirty_even_r23 <=  status_dirty_even_nxt23;  
    status_dirty_even_r24 <=  status_dirty_even_nxt24;  
    status_dirty_even_r25 <=  status_dirty_even_nxt25;  
    status_dirty_even_r26 <=  status_dirty_even_nxt26;  
    status_dirty_even_r27 <=  status_dirty_even_nxt27;  
    status_dirty_even_r28 <=  status_dirty_even_nxt28;  
    status_dirty_even_r29 <=  status_dirty_even_nxt29;  
    status_dirty_even_r30 <=  status_dirty_even_nxt30;  
    status_dirty_even_r31 <=  status_dirty_even_nxt31;  
    status_dirty_even_r32 <=  status_dirty_even_nxt32;  
    status_dirty_even_r33 <=  status_dirty_even_nxt33;  
    status_dirty_even_r34 <=  status_dirty_even_nxt34;  
    status_dirty_even_r35 <=  status_dirty_even_nxt35;  
    status_dirty_even_r36 <=  status_dirty_even_nxt36;  
    status_dirty_even_r37 <=  status_dirty_even_nxt37;  
    status_dirty_even_r38 <=  status_dirty_even_nxt38;  
    status_dirty_even_r39 <=  status_dirty_even_nxt39;  
    status_dirty_even_r40 <=  status_dirty_even_nxt40;  
    status_dirty_even_r41 <=  status_dirty_even_nxt41;  
    status_dirty_even_r42 <=  status_dirty_even_nxt42;  
    status_dirty_even_r43 <=  status_dirty_even_nxt43;  
    status_dirty_even_r44 <=  status_dirty_even_nxt44;  
    status_dirty_even_r45 <=  status_dirty_even_nxt45;  
    status_dirty_even_r46 <=  status_dirty_even_nxt46;  
    status_dirty_even_r47 <=  status_dirty_even_nxt47;  
    status_dirty_even_r48 <=  status_dirty_even_nxt48;  
    status_dirty_even_r49 <=  status_dirty_even_nxt49;  
    status_dirty_even_r50 <=  status_dirty_even_nxt50;  
    status_dirty_even_r51 <=  status_dirty_even_nxt51;  
    status_dirty_even_r52 <=  status_dirty_even_nxt52;  
    status_dirty_even_r53 <=  status_dirty_even_nxt53;  
    status_dirty_even_r54 <=  status_dirty_even_nxt54;  
    status_dirty_even_r55 <=  status_dirty_even_nxt55;  
    status_dirty_even_r56 <=  status_dirty_even_nxt56;  
    status_dirty_even_r57 <=  status_dirty_even_nxt57;  
    status_dirty_even_r58 <=  status_dirty_even_nxt58;  
    status_dirty_even_r59 <=  status_dirty_even_nxt59;  
    status_dirty_even_r60 <=  status_dirty_even_nxt60;  
    status_dirty_even_r61 <=  status_dirty_even_nxt61;  
    status_dirty_even_r62 <=  status_dirty_even_nxt62;  
    status_dirty_even_r63 <=  status_dirty_even_nxt63;  
    status_dirty_even_r64 <=  status_dirty_even_nxt64;  
    status_dirty_even_r65 <=  status_dirty_even_nxt65;  
    status_dirty_even_r66 <=  status_dirty_even_nxt66;  
    status_dirty_even_r67 <=  status_dirty_even_nxt67;  
    status_dirty_even_r68 <=  status_dirty_even_nxt68;  
    status_dirty_even_r69 <=  status_dirty_even_nxt69;  
    status_dirty_even_r70 <=  status_dirty_even_nxt70;  
    status_dirty_even_r71 <=  status_dirty_even_nxt71;  
    status_dirty_even_r72 <=  status_dirty_even_nxt72;  
    status_dirty_even_r73 <=  status_dirty_even_nxt73;  
    status_dirty_even_r74 <=  status_dirty_even_nxt74;  
    status_dirty_even_r75 <=  status_dirty_even_nxt75;  
    status_dirty_even_r76 <=  status_dirty_even_nxt76;  
    status_dirty_even_r77 <=  status_dirty_even_nxt77;  
    status_dirty_even_r78 <=  status_dirty_even_nxt78;  
    status_dirty_even_r79 <=  status_dirty_even_nxt79;  
    status_dirty_even_r80 <=  status_dirty_even_nxt80;  
    status_dirty_even_r81 <=  status_dirty_even_nxt81;  
    status_dirty_even_r82 <=  status_dirty_even_nxt82;  
    status_dirty_even_r83 <=  status_dirty_even_nxt83;  
    status_dirty_even_r84 <=  status_dirty_even_nxt84;  
    status_dirty_even_r85 <=  status_dirty_even_nxt85;  
    status_dirty_even_r86 <=  status_dirty_even_nxt86;  
    status_dirty_even_r87 <=  status_dirty_even_nxt87;  
    status_dirty_even_r88 <=  status_dirty_even_nxt88;  
    status_dirty_even_r89 <=  status_dirty_even_nxt89;  
    status_dirty_even_r90 <=  status_dirty_even_nxt90;  
    status_dirty_even_r91 <=  status_dirty_even_nxt91;  
    status_dirty_even_r92 <=  status_dirty_even_nxt92;  
    status_dirty_even_r93 <=  status_dirty_even_nxt93;  
    status_dirty_even_r94 <=  status_dirty_even_nxt94;  
    status_dirty_even_r95 <=  status_dirty_even_nxt95;  
    status_dirty_even_r96 <=  status_dirty_even_nxt96;  
    status_dirty_even_r97 <=  status_dirty_even_nxt97;  
    status_dirty_even_r98 <=  status_dirty_even_nxt98;  
    status_dirty_even_r99 <=  status_dirty_even_nxt99;  
    status_dirty_even_r100 <=  status_dirty_even_nxt100;  
    status_dirty_even_r101 <=  status_dirty_even_nxt101;  
    status_dirty_even_r102 <=  status_dirty_even_nxt102;  
    status_dirty_even_r103 <=  status_dirty_even_nxt103;  
    status_dirty_even_r104 <=  status_dirty_even_nxt104;  
    status_dirty_even_r105 <=  status_dirty_even_nxt105;  
    status_dirty_even_r106 <=  status_dirty_even_nxt106;  
    status_dirty_even_r107 <=  status_dirty_even_nxt107;  
    status_dirty_even_r108 <=  status_dirty_even_nxt108;  
    status_dirty_even_r109 <=  status_dirty_even_nxt109;  
    status_dirty_even_r110 <=  status_dirty_even_nxt110;  
    status_dirty_even_r111 <=  status_dirty_even_nxt111;  
    status_dirty_even_r112 <=  status_dirty_even_nxt112;  
    status_dirty_even_r113 <=  status_dirty_even_nxt113;  
    status_dirty_even_r114 <=  status_dirty_even_nxt114;  
    status_dirty_even_r115 <=  status_dirty_even_nxt115;  
    status_dirty_even_r116 <=  status_dirty_even_nxt116;  
    status_dirty_even_r117 <=  status_dirty_even_nxt117;  
    status_dirty_even_r118 <=  status_dirty_even_nxt118;  
    status_dirty_even_r119 <=  status_dirty_even_nxt119;  
    status_dirty_even_r120 <=  status_dirty_even_nxt120;  
    status_dirty_even_r121 <=  status_dirty_even_nxt121;  
    status_dirty_even_r122 <=  status_dirty_even_nxt122;  
    status_dirty_even_r123 <=  status_dirty_even_nxt123;  
    status_dirty_even_r124 <=  status_dirty_even_nxt124;  
    status_dirty_even_r125 <=  status_dirty_even_nxt125;  
    status_dirty_even_r126 <=  status_dirty_even_nxt126;  
    status_dirty_even_r127 <=  status_dirty_even_nxt127;  
end

// Dirty odd : port0 or port1
//
always @*
begin
   status_dirty_odd_r[0] = status_dirty_odd_r0;
   status_dirty_odd_r[1] = status_dirty_odd_r1;
   status_dirty_odd_r[2] = status_dirty_odd_r2;
   status_dirty_odd_r[3] = status_dirty_odd_r3;
   status_dirty_odd_r[4] = status_dirty_odd_r4;
   status_dirty_odd_r[5] = status_dirty_odd_r5;
   status_dirty_odd_r[6] = status_dirty_odd_r6;
   status_dirty_odd_r[7] = status_dirty_odd_r7;
   status_dirty_odd_r[8] = status_dirty_odd_r8;
   status_dirty_odd_r[9] = status_dirty_odd_r9;
   status_dirty_odd_r[10] = status_dirty_odd_r10;
   status_dirty_odd_r[11] = status_dirty_odd_r11;
   status_dirty_odd_r[12] = status_dirty_odd_r12;
   status_dirty_odd_r[13] = status_dirty_odd_r13;
   status_dirty_odd_r[14] = status_dirty_odd_r14;
   status_dirty_odd_r[15] = status_dirty_odd_r15;
   status_dirty_odd_r[16] = status_dirty_odd_r16;
   status_dirty_odd_r[17] = status_dirty_odd_r17;
   status_dirty_odd_r[18] = status_dirty_odd_r18;
   status_dirty_odd_r[19] = status_dirty_odd_r19;
   status_dirty_odd_r[20] = status_dirty_odd_r20;
   status_dirty_odd_r[21] = status_dirty_odd_r21;
   status_dirty_odd_r[22] = status_dirty_odd_r22;
   status_dirty_odd_r[23] = status_dirty_odd_r23;
   status_dirty_odd_r[24] = status_dirty_odd_r24;
   status_dirty_odd_r[25] = status_dirty_odd_r25;
   status_dirty_odd_r[26] = status_dirty_odd_r26;
   status_dirty_odd_r[27] = status_dirty_odd_r27;
   status_dirty_odd_r[28] = status_dirty_odd_r28;
   status_dirty_odd_r[29] = status_dirty_odd_r29;
   status_dirty_odd_r[30] = status_dirty_odd_r30;
   status_dirty_odd_r[31] = status_dirty_odd_r31;
   status_dirty_odd_r[32] = status_dirty_odd_r32;
   status_dirty_odd_r[33] = status_dirty_odd_r33;
   status_dirty_odd_r[34] = status_dirty_odd_r34;
   status_dirty_odd_r[35] = status_dirty_odd_r35;
   status_dirty_odd_r[36] = status_dirty_odd_r36;
   status_dirty_odd_r[37] = status_dirty_odd_r37;
   status_dirty_odd_r[38] = status_dirty_odd_r38;
   status_dirty_odd_r[39] = status_dirty_odd_r39;
   status_dirty_odd_r[40] = status_dirty_odd_r40;
   status_dirty_odd_r[41] = status_dirty_odd_r41;
   status_dirty_odd_r[42] = status_dirty_odd_r42;
   status_dirty_odd_r[43] = status_dirty_odd_r43;
   status_dirty_odd_r[44] = status_dirty_odd_r44;
   status_dirty_odd_r[45] = status_dirty_odd_r45;
   status_dirty_odd_r[46] = status_dirty_odd_r46;
   status_dirty_odd_r[47] = status_dirty_odd_r47;
   status_dirty_odd_r[48] = status_dirty_odd_r48;
   status_dirty_odd_r[49] = status_dirty_odd_r49;
   status_dirty_odd_r[50] = status_dirty_odd_r50;
   status_dirty_odd_r[51] = status_dirty_odd_r51;
   status_dirty_odd_r[52] = status_dirty_odd_r52;
   status_dirty_odd_r[53] = status_dirty_odd_r53;
   status_dirty_odd_r[54] = status_dirty_odd_r54;
   status_dirty_odd_r[55] = status_dirty_odd_r55;
   status_dirty_odd_r[56] = status_dirty_odd_r56;
   status_dirty_odd_r[57] = status_dirty_odd_r57;
   status_dirty_odd_r[58] = status_dirty_odd_r58;
   status_dirty_odd_r[59] = status_dirty_odd_r59;
   status_dirty_odd_r[60] = status_dirty_odd_r60;
   status_dirty_odd_r[61] = status_dirty_odd_r61;
   status_dirty_odd_r[62] = status_dirty_odd_r62;
   status_dirty_odd_r[63] = status_dirty_odd_r63;
   status_dirty_odd_r[64] = status_dirty_odd_r64;
   status_dirty_odd_r[65] = status_dirty_odd_r65;
   status_dirty_odd_r[66] = status_dirty_odd_r66;
   status_dirty_odd_r[67] = status_dirty_odd_r67;
   status_dirty_odd_r[68] = status_dirty_odd_r68;
   status_dirty_odd_r[69] = status_dirty_odd_r69;
   status_dirty_odd_r[70] = status_dirty_odd_r70;
   status_dirty_odd_r[71] = status_dirty_odd_r71;
   status_dirty_odd_r[72] = status_dirty_odd_r72;
   status_dirty_odd_r[73] = status_dirty_odd_r73;
   status_dirty_odd_r[74] = status_dirty_odd_r74;
   status_dirty_odd_r[75] = status_dirty_odd_r75;
   status_dirty_odd_r[76] = status_dirty_odd_r76;
   status_dirty_odd_r[77] = status_dirty_odd_r77;
   status_dirty_odd_r[78] = status_dirty_odd_r78;
   status_dirty_odd_r[79] = status_dirty_odd_r79;
   status_dirty_odd_r[80] = status_dirty_odd_r80;
   status_dirty_odd_r[81] = status_dirty_odd_r81;
   status_dirty_odd_r[82] = status_dirty_odd_r82;
   status_dirty_odd_r[83] = status_dirty_odd_r83;
   status_dirty_odd_r[84] = status_dirty_odd_r84;
   status_dirty_odd_r[85] = status_dirty_odd_r85;
   status_dirty_odd_r[86] = status_dirty_odd_r86;
   status_dirty_odd_r[87] = status_dirty_odd_r87;
   status_dirty_odd_r[88] = status_dirty_odd_r88;
   status_dirty_odd_r[89] = status_dirty_odd_r89;
   status_dirty_odd_r[90] = status_dirty_odd_r90;
   status_dirty_odd_r[91] = status_dirty_odd_r91;
   status_dirty_odd_r[92] = status_dirty_odd_r92;
   status_dirty_odd_r[93] = status_dirty_odd_r93;
   status_dirty_odd_r[94] = status_dirty_odd_r94;
   status_dirty_odd_r[95] = status_dirty_odd_r95;
   status_dirty_odd_r[96] = status_dirty_odd_r96;
   status_dirty_odd_r[97] = status_dirty_odd_r97;
   status_dirty_odd_r[98] = status_dirty_odd_r98;
   status_dirty_odd_r[99] = status_dirty_odd_r99;
   status_dirty_odd_r[100] = status_dirty_odd_r100;
   status_dirty_odd_r[101] = status_dirty_odd_r101;
   status_dirty_odd_r[102] = status_dirty_odd_r102;
   status_dirty_odd_r[103] = status_dirty_odd_r103;
   status_dirty_odd_r[104] = status_dirty_odd_r104;
   status_dirty_odd_r[105] = status_dirty_odd_r105;
   status_dirty_odd_r[106] = status_dirty_odd_r106;
   status_dirty_odd_r[107] = status_dirty_odd_r107;
   status_dirty_odd_r[108] = status_dirty_odd_r108;
   status_dirty_odd_r[109] = status_dirty_odd_r109;
   status_dirty_odd_r[110] = status_dirty_odd_r110;
   status_dirty_odd_r[111] = status_dirty_odd_r111;
   status_dirty_odd_r[112] = status_dirty_odd_r112;
   status_dirty_odd_r[113] = status_dirty_odd_r113;
   status_dirty_odd_r[114] = status_dirty_odd_r114;
   status_dirty_odd_r[115] = status_dirty_odd_r115;
   status_dirty_odd_r[116] = status_dirty_odd_r116;
   status_dirty_odd_r[117] = status_dirty_odd_r117;
   status_dirty_odd_r[118] = status_dirty_odd_r118;
   status_dirty_odd_r[119] = status_dirty_odd_r119;
   status_dirty_odd_r[120] = status_dirty_odd_r120;
   status_dirty_odd_r[121] = status_dirty_odd_r121;
   status_dirty_odd_r[122] = status_dirty_odd_r122;
   status_dirty_odd_r[123] = status_dirty_odd_r123;
   status_dirty_odd_r[124] = status_dirty_odd_r124;
   status_dirty_odd_r[125] = status_dirty_odd_r125;
   status_dirty_odd_r[126] = status_dirty_odd_r126;
   status_dirty_odd_r[127] = status_dirty_odd_r127;
end

always @*
begin : dirty_odd_sync_comb_PROC
    // Port 0
    //
    status_dirty_odd_nxt0 =  status_dirty_odd_r0;  
    status_dirty_odd_nxt1 =  status_dirty_odd_r1;  
    status_dirty_odd_nxt2 =  status_dirty_odd_r2;  
    status_dirty_odd_nxt3 =  status_dirty_odd_r3;  
    status_dirty_odd_nxt4 =  status_dirty_odd_r4;  
    status_dirty_odd_nxt5 =  status_dirty_odd_r5;  
    status_dirty_odd_nxt6 =  status_dirty_odd_r6;  
    status_dirty_odd_nxt7 =  status_dirty_odd_r7;  
    status_dirty_odd_nxt8 =  status_dirty_odd_r8;  
    status_dirty_odd_nxt9 =  status_dirty_odd_r9;  
    status_dirty_odd_nxt10 =  status_dirty_odd_r10;  
    status_dirty_odd_nxt11 =  status_dirty_odd_r11;  
    status_dirty_odd_nxt12 =  status_dirty_odd_r12;  
    status_dirty_odd_nxt13 =  status_dirty_odd_r13;  
    status_dirty_odd_nxt14 =  status_dirty_odd_r14;  
    status_dirty_odd_nxt15 =  status_dirty_odd_r15;  
    status_dirty_odd_nxt16 =  status_dirty_odd_r16;  
    status_dirty_odd_nxt17 =  status_dirty_odd_r17;  
    status_dirty_odd_nxt18 =  status_dirty_odd_r18;  
    status_dirty_odd_nxt19 =  status_dirty_odd_r19;  
    status_dirty_odd_nxt20 =  status_dirty_odd_r20;  
    status_dirty_odd_nxt21 =  status_dirty_odd_r21;  
    status_dirty_odd_nxt22 =  status_dirty_odd_r22;  
    status_dirty_odd_nxt23 =  status_dirty_odd_r23;  
    status_dirty_odd_nxt24 =  status_dirty_odd_r24;  
    status_dirty_odd_nxt25 =  status_dirty_odd_r25;  
    status_dirty_odd_nxt26 =  status_dirty_odd_r26;  
    status_dirty_odd_nxt27 =  status_dirty_odd_r27;  
    status_dirty_odd_nxt28 =  status_dirty_odd_r28;  
    status_dirty_odd_nxt29 =  status_dirty_odd_r29;  
    status_dirty_odd_nxt30 =  status_dirty_odd_r30;  
    status_dirty_odd_nxt31 =  status_dirty_odd_r31;  
    status_dirty_odd_nxt32 =  status_dirty_odd_r32;  
    status_dirty_odd_nxt33 =  status_dirty_odd_r33;  
    status_dirty_odd_nxt34 =  status_dirty_odd_r34;  
    status_dirty_odd_nxt35 =  status_dirty_odd_r35;  
    status_dirty_odd_nxt36 =  status_dirty_odd_r36;  
    status_dirty_odd_nxt37 =  status_dirty_odd_r37;  
    status_dirty_odd_nxt38 =  status_dirty_odd_r38;  
    status_dirty_odd_nxt39 =  status_dirty_odd_r39;  
    status_dirty_odd_nxt40 =  status_dirty_odd_r40;  
    status_dirty_odd_nxt41 =  status_dirty_odd_r41;  
    status_dirty_odd_nxt42 =  status_dirty_odd_r42;  
    status_dirty_odd_nxt43 =  status_dirty_odd_r43;  
    status_dirty_odd_nxt44 =  status_dirty_odd_r44;  
    status_dirty_odd_nxt45 =  status_dirty_odd_r45;  
    status_dirty_odd_nxt46 =  status_dirty_odd_r46;  
    status_dirty_odd_nxt47 =  status_dirty_odd_r47;  
    status_dirty_odd_nxt48 =  status_dirty_odd_r48;  
    status_dirty_odd_nxt49 =  status_dirty_odd_r49;  
    status_dirty_odd_nxt50 =  status_dirty_odd_r50;  
    status_dirty_odd_nxt51 =  status_dirty_odd_r51;  
    status_dirty_odd_nxt52 =  status_dirty_odd_r52;  
    status_dirty_odd_nxt53 =  status_dirty_odd_r53;  
    status_dirty_odd_nxt54 =  status_dirty_odd_r54;  
    status_dirty_odd_nxt55 =  status_dirty_odd_r55;  
    status_dirty_odd_nxt56 =  status_dirty_odd_r56;  
    status_dirty_odd_nxt57 =  status_dirty_odd_r57;  
    status_dirty_odd_nxt58 =  status_dirty_odd_r58;  
    status_dirty_odd_nxt59 =  status_dirty_odd_r59;  
    status_dirty_odd_nxt60 =  status_dirty_odd_r60;  
    status_dirty_odd_nxt61 =  status_dirty_odd_r61;  
    status_dirty_odd_nxt62 =  status_dirty_odd_r62;  
    status_dirty_odd_nxt63 =  status_dirty_odd_r63;  
    status_dirty_odd_nxt64 =  status_dirty_odd_r64;  
    status_dirty_odd_nxt65 =  status_dirty_odd_r65;  
    status_dirty_odd_nxt66 =  status_dirty_odd_r66;  
    status_dirty_odd_nxt67 =  status_dirty_odd_r67;  
    status_dirty_odd_nxt68 =  status_dirty_odd_r68;  
    status_dirty_odd_nxt69 =  status_dirty_odd_r69;  
    status_dirty_odd_nxt70 =  status_dirty_odd_r70;  
    status_dirty_odd_nxt71 =  status_dirty_odd_r71;  
    status_dirty_odd_nxt72 =  status_dirty_odd_r72;  
    status_dirty_odd_nxt73 =  status_dirty_odd_r73;  
    status_dirty_odd_nxt74 =  status_dirty_odd_r74;  
    status_dirty_odd_nxt75 =  status_dirty_odd_r75;  
    status_dirty_odd_nxt76 =  status_dirty_odd_r76;  
    status_dirty_odd_nxt77 =  status_dirty_odd_r77;  
    status_dirty_odd_nxt78 =  status_dirty_odd_r78;  
    status_dirty_odd_nxt79 =  status_dirty_odd_r79;  
    status_dirty_odd_nxt80 =  status_dirty_odd_r80;  
    status_dirty_odd_nxt81 =  status_dirty_odd_r81;  
    status_dirty_odd_nxt82 =  status_dirty_odd_r82;  
    status_dirty_odd_nxt83 =  status_dirty_odd_r83;  
    status_dirty_odd_nxt84 =  status_dirty_odd_r84;  
    status_dirty_odd_nxt85 =  status_dirty_odd_r85;  
    status_dirty_odd_nxt86 =  status_dirty_odd_r86;  
    status_dirty_odd_nxt87 =  status_dirty_odd_r87;  
    status_dirty_odd_nxt88 =  status_dirty_odd_r88;  
    status_dirty_odd_nxt89 =  status_dirty_odd_r89;  
    status_dirty_odd_nxt90 =  status_dirty_odd_r90;  
    status_dirty_odd_nxt91 =  status_dirty_odd_r91;  
    status_dirty_odd_nxt92 =  status_dirty_odd_r92;  
    status_dirty_odd_nxt93 =  status_dirty_odd_r93;  
    status_dirty_odd_nxt94 =  status_dirty_odd_r94;  
    status_dirty_odd_nxt95 =  status_dirty_odd_r95;  
    status_dirty_odd_nxt96 =  status_dirty_odd_r96;  
    status_dirty_odd_nxt97 =  status_dirty_odd_r97;  
    status_dirty_odd_nxt98 =  status_dirty_odd_r98;  
    status_dirty_odd_nxt99 =  status_dirty_odd_r99;  
    status_dirty_odd_nxt100 =  status_dirty_odd_r100;  
    status_dirty_odd_nxt101 =  status_dirty_odd_r101;  
    status_dirty_odd_nxt102 =  status_dirty_odd_r102;  
    status_dirty_odd_nxt103 =  status_dirty_odd_r103;  
    status_dirty_odd_nxt104 =  status_dirty_odd_r104;  
    status_dirty_odd_nxt105 =  status_dirty_odd_r105;  
    status_dirty_odd_nxt106 =  status_dirty_odd_r106;  
    status_dirty_odd_nxt107 =  status_dirty_odd_r107;  
    status_dirty_odd_nxt108 =  status_dirty_odd_r108;  
    status_dirty_odd_nxt109 =  status_dirty_odd_r109;  
    status_dirty_odd_nxt110 =  status_dirty_odd_r110;  
    status_dirty_odd_nxt111 =  status_dirty_odd_r111;  
    status_dirty_odd_nxt112 =  status_dirty_odd_r112;  
    status_dirty_odd_nxt113 =  status_dirty_odd_r113;  
    status_dirty_odd_nxt114 =  status_dirty_odd_r114;  
    status_dirty_odd_nxt115 =  status_dirty_odd_r115;  
    status_dirty_odd_nxt116 =  status_dirty_odd_r116;  
    status_dirty_odd_nxt117 =  status_dirty_odd_r117;  
    status_dirty_odd_nxt118 =  status_dirty_odd_r118;  
    status_dirty_odd_nxt119 =  status_dirty_odd_r119;  
    status_dirty_odd_nxt120 =  status_dirty_odd_r120;  
    status_dirty_odd_nxt121 =  status_dirty_odd_r121;  
    status_dirty_odd_nxt122 =  status_dirty_odd_r122;  
    status_dirty_odd_nxt123 =  status_dirty_odd_r123;  
    status_dirty_odd_nxt124 =  status_dirty_odd_r124;  
    status_dirty_odd_nxt125 =  status_dirty_odd_r125;  
    status_dirty_odd_nxt126 =  status_dirty_odd_r126;  
    status_dirty_odd_nxt127 =  status_dirty_odd_r127;  
  if( status0_odd_addr_r == 0 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt0[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt0[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 1 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt1[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt1[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 2 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt2[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt2[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 3 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt3[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt3[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 4 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt4[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt4[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 5 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt5[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt5[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 6 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt6[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt6[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 7 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt7[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt7[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 8 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt8[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt8[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 9 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt9[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt9[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 10 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt10[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt10[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 11 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt11[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt11[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 12 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt12[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt12[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 13 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt13[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt13[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 14 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt14[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt14[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 15 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt15[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt15[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 16 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt16[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt16[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 17 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt17[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt17[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 18 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt18[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt18[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 19 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt19[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt19[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 20 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt20[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt20[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 21 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt21[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt21[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 22 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt22[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt22[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 23 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt23[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt23[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 24 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt24[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt24[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 25 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt25[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt25[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 26 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt26[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt26[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 27 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt27[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt27[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 28 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt28[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt28[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 29 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt29[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt29[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 30 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt30[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt30[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 31 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt31[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt31[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 32 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt32[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt32[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 33 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt33[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt33[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 34 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt34[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt34[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 35 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt35[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt35[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 36 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt36[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt36[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 37 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt37[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt37[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 38 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt38[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt38[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 39 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt39[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt39[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 40 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt40[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt40[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 41 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt41[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt41[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 42 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt42[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt42[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 43 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt43[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt43[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 44 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt44[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt44[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 45 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt45[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt45[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 46 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt46[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt46[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 47 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt47[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt47[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 48 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt48[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt48[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 49 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt49[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt49[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 50 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt50[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt50[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 51 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt51[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt51[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 52 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt52[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt52[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 53 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt53[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt53[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 54 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt54[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt54[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 55 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt55[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt55[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 56 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt56[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt56[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 57 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt57[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt57[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 58 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt58[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt58[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 59 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt59[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt59[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 60 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt60[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt60[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 61 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt61[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt61[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 62 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt62[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt62[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 63 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt63[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt63[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 64 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt64[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt64[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 65 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt65[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt65[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 66 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt66[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt66[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 67 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt67[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt67[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 68 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt68[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt68[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 69 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt69[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt69[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 70 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt70[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt70[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 71 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt71[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt71[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 72 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt72[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt72[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 73 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt73[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt73[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 74 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt74[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt74[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 75 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt75[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt75[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 76 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt76[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt76[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 77 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt77[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt77[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 78 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt78[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt78[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 79 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt79[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt79[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 80 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt80[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt80[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 81 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt81[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt81[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 82 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt82[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt82[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 83 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt83[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt83[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 84 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt84[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt84[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 85 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt85[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt85[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 86 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt86[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt86[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 87 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt87[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt87[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 88 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt88[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt88[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 89 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt89[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt89[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 90 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt90[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt90[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 91 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt91[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt91[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 92 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt92[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt92[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 93 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt93[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt93[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 94 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt94[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt94[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 95 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt95[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt95[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 96 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt96[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt96[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 97 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt97[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt97[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 98 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt98[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt98[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 99 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt99[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt99[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 100 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt100[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt100[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 101 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt101[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt101[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 102 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt102[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt102[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 103 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt103[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt103[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 104 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt104[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt104[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 105 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt105[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt105[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 106 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt106[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt106[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 107 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt107[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt107[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 108 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt108[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt108[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 109 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt109[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt109[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 110 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt110[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt110[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 111 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt111[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt111[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 112 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt112[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt112[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 113 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt113[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt113[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 114 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt114[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt114[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 115 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt115[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt115[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 116 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt116[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt116[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 117 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt117[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt117[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 118 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt118[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt118[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 119 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt119[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt119[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 120 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt120[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt120[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 121 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt121[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt121[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 122 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt122[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt122[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 123 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt123[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt123[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 124 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt124[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt124[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 125 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt125[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt125[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 126 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt126[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt126[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
  if( status0_odd_addr_r == 127 )
  begin
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[0])                                      
  begin                                                                 
    status_dirty_odd_nxt127[0] = status0_odd_dirty_r;  
  end                                                                   
  if (  status0_write_odd_r                                             
      & status0_odd_wem_r[DIRTY]                                        
      & status0_odd_way_hot_r[1])                                      
  begin                                                                 
    status_dirty_odd_nxt127[1] = status0_odd_dirty_r;  
  end                                                                   
  end                                                            
    // Port 1
    //
  if( status1_addr_r == 0 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt0[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt0[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 1 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt1[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt1[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 2 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt2[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt2[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 3 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt3[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt3[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 4 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt4[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt4[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 5 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt5[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt5[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 6 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt6[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt6[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 7 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt7[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt7[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 8 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt8[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt8[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 9 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt9[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt9[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 10 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt10[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt10[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 11 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt11[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt11[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 12 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt12[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt12[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 13 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt13[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt13[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 14 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt14[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt14[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 15 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt15[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt15[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 16 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt16[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt16[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 17 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt17[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt17[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 18 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt18[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt18[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 19 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt19[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt19[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 20 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt20[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt20[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 21 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt21[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt21[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 22 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt22[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt22[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 23 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt23[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt23[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 24 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt24[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt24[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 25 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt25[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt25[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 26 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt26[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt26[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 27 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt27[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt27[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 28 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt28[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt28[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 29 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt29[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt29[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 30 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt30[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt30[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 31 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt31[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt31[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 32 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt32[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt32[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 33 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt33[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt33[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 34 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt34[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt34[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 35 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt35[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt35[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 36 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt36[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt36[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 37 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt37[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt37[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 38 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt38[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt38[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 39 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt39[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt39[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 40 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt40[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt40[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 41 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt41[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt41[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 42 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt42[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt42[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 43 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt43[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt43[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 44 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt44[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt44[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 45 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt45[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt45[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 46 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt46[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt46[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 47 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt47[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt47[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 48 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt48[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt48[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 49 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt49[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt49[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 50 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt50[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt50[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 51 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt51[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt51[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 52 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt52[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt52[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 53 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt53[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt53[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 54 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt54[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt54[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 55 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt55[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt55[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 56 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt56[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt56[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 57 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt57[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt57[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 58 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt58[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt58[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 59 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt59[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt59[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 60 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt60[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt60[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 61 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt61[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt61[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 62 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt62[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt62[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 63 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt63[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt63[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 64 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt64[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt64[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 65 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt65[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt65[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 66 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt66[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt66[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 67 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt67[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt67[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 68 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt68[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt68[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 69 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt69[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt69[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 70 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt70[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt70[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 71 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt71[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt71[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 72 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt72[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt72[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 73 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt73[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt73[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 74 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt74[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt74[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 75 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt75[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt75[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 76 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt76[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt76[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 77 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt77[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt77[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 78 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt78[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt78[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 79 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt79[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt79[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 80 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt80[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt80[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 81 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt81[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt81[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 82 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt82[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt82[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 83 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt83[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt83[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 84 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt84[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt84[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 85 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt85[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt85[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 86 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt86[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt86[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 87 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt87[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt87[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 88 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt88[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt88[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 89 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt89[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt89[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 90 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt90[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt90[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 91 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt91[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt91[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 92 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt92[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt92[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 93 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt93[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt93[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 94 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt94[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt94[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 95 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt95[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt95[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 96 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt96[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt96[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 97 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt97[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt97[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 98 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt98[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt98[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 99 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt99[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt99[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 100 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt100[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt100[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 101 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt101[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt101[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 102 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt102[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt102[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 103 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt103[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt103[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 104 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt104[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt104[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 105 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt105[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt105[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 106 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt106[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt106[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 107 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt107[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt107[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 108 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt108[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt108[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 109 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt109[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt109[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 110 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt110[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt110[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 111 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt111[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt111[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 112 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt112[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt112[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 113 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt113[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt113[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 114 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt114[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt114[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 115 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt115[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt115[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 116 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt116[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt116[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 117 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt117[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt117[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 118 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt118[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt118[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 119 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt119[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt119[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 120 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt120[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt120[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 121 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt121[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt121[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 122 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt122[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt122[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 123 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt123[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt123[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 124 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt124[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt124[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 125 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt125[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt125[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 126 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt126[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt126[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
  if( status1_addr_r == 127 )
  begin
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[0])                                    
  begin                                                           
    status_dirty_odd_nxt127[0] =   status1_dirty_r;  
  end                                                             
  if (  status1_write_odd_r                                       
      & status1_wem_r[DIRTY]                                      
      & status1_way_hot_r[1])                                    
  begin                                                           
    status_dirty_odd_nxt127[1] =   status1_dirty_r;  
  end                                                             
  end                                                            
end

always @(posedge clk)
begin : dirty_odd_sync_PROC
    status_dirty_odd_r0 <=  status_dirty_odd_nxt0;  
    status_dirty_odd_r1 <=  status_dirty_odd_nxt1;  
    status_dirty_odd_r2 <=  status_dirty_odd_nxt2;  
    status_dirty_odd_r3 <=  status_dirty_odd_nxt3;  
    status_dirty_odd_r4 <=  status_dirty_odd_nxt4;  
    status_dirty_odd_r5 <=  status_dirty_odd_nxt5;  
    status_dirty_odd_r6 <=  status_dirty_odd_nxt6;  
    status_dirty_odd_r7 <=  status_dirty_odd_nxt7;  
    status_dirty_odd_r8 <=  status_dirty_odd_nxt8;  
    status_dirty_odd_r9 <=  status_dirty_odd_nxt9;  
    status_dirty_odd_r10 <=  status_dirty_odd_nxt10;  
    status_dirty_odd_r11 <=  status_dirty_odd_nxt11;  
    status_dirty_odd_r12 <=  status_dirty_odd_nxt12;  
    status_dirty_odd_r13 <=  status_dirty_odd_nxt13;  
    status_dirty_odd_r14 <=  status_dirty_odd_nxt14;  
    status_dirty_odd_r15 <=  status_dirty_odd_nxt15;  
    status_dirty_odd_r16 <=  status_dirty_odd_nxt16;  
    status_dirty_odd_r17 <=  status_dirty_odd_nxt17;  
    status_dirty_odd_r18 <=  status_dirty_odd_nxt18;  
    status_dirty_odd_r19 <=  status_dirty_odd_nxt19;  
    status_dirty_odd_r20 <=  status_dirty_odd_nxt20;  
    status_dirty_odd_r21 <=  status_dirty_odd_nxt21;  
    status_dirty_odd_r22 <=  status_dirty_odd_nxt22;  
    status_dirty_odd_r23 <=  status_dirty_odd_nxt23;  
    status_dirty_odd_r24 <=  status_dirty_odd_nxt24;  
    status_dirty_odd_r25 <=  status_dirty_odd_nxt25;  
    status_dirty_odd_r26 <=  status_dirty_odd_nxt26;  
    status_dirty_odd_r27 <=  status_dirty_odd_nxt27;  
    status_dirty_odd_r28 <=  status_dirty_odd_nxt28;  
    status_dirty_odd_r29 <=  status_dirty_odd_nxt29;  
    status_dirty_odd_r30 <=  status_dirty_odd_nxt30;  
    status_dirty_odd_r31 <=  status_dirty_odd_nxt31;  
    status_dirty_odd_r32 <=  status_dirty_odd_nxt32;  
    status_dirty_odd_r33 <=  status_dirty_odd_nxt33;  
    status_dirty_odd_r34 <=  status_dirty_odd_nxt34;  
    status_dirty_odd_r35 <=  status_dirty_odd_nxt35;  
    status_dirty_odd_r36 <=  status_dirty_odd_nxt36;  
    status_dirty_odd_r37 <=  status_dirty_odd_nxt37;  
    status_dirty_odd_r38 <=  status_dirty_odd_nxt38;  
    status_dirty_odd_r39 <=  status_dirty_odd_nxt39;  
    status_dirty_odd_r40 <=  status_dirty_odd_nxt40;  
    status_dirty_odd_r41 <=  status_dirty_odd_nxt41;  
    status_dirty_odd_r42 <=  status_dirty_odd_nxt42;  
    status_dirty_odd_r43 <=  status_dirty_odd_nxt43;  
    status_dirty_odd_r44 <=  status_dirty_odd_nxt44;  
    status_dirty_odd_r45 <=  status_dirty_odd_nxt45;  
    status_dirty_odd_r46 <=  status_dirty_odd_nxt46;  
    status_dirty_odd_r47 <=  status_dirty_odd_nxt47;  
    status_dirty_odd_r48 <=  status_dirty_odd_nxt48;  
    status_dirty_odd_r49 <=  status_dirty_odd_nxt49;  
    status_dirty_odd_r50 <=  status_dirty_odd_nxt50;  
    status_dirty_odd_r51 <=  status_dirty_odd_nxt51;  
    status_dirty_odd_r52 <=  status_dirty_odd_nxt52;  
    status_dirty_odd_r53 <=  status_dirty_odd_nxt53;  
    status_dirty_odd_r54 <=  status_dirty_odd_nxt54;  
    status_dirty_odd_r55 <=  status_dirty_odd_nxt55;  
    status_dirty_odd_r56 <=  status_dirty_odd_nxt56;  
    status_dirty_odd_r57 <=  status_dirty_odd_nxt57;  
    status_dirty_odd_r58 <=  status_dirty_odd_nxt58;  
    status_dirty_odd_r59 <=  status_dirty_odd_nxt59;  
    status_dirty_odd_r60 <=  status_dirty_odd_nxt60;  
    status_dirty_odd_r61 <=  status_dirty_odd_nxt61;  
    status_dirty_odd_r62 <=  status_dirty_odd_nxt62;  
    status_dirty_odd_r63 <=  status_dirty_odd_nxt63;  
    status_dirty_odd_r64 <=  status_dirty_odd_nxt64;  
    status_dirty_odd_r65 <=  status_dirty_odd_nxt65;  
    status_dirty_odd_r66 <=  status_dirty_odd_nxt66;  
    status_dirty_odd_r67 <=  status_dirty_odd_nxt67;  
    status_dirty_odd_r68 <=  status_dirty_odd_nxt68;  
    status_dirty_odd_r69 <=  status_dirty_odd_nxt69;  
    status_dirty_odd_r70 <=  status_dirty_odd_nxt70;  
    status_dirty_odd_r71 <=  status_dirty_odd_nxt71;  
    status_dirty_odd_r72 <=  status_dirty_odd_nxt72;  
    status_dirty_odd_r73 <=  status_dirty_odd_nxt73;  
    status_dirty_odd_r74 <=  status_dirty_odd_nxt74;  
    status_dirty_odd_r75 <=  status_dirty_odd_nxt75;  
    status_dirty_odd_r76 <=  status_dirty_odd_nxt76;  
    status_dirty_odd_r77 <=  status_dirty_odd_nxt77;  
    status_dirty_odd_r78 <=  status_dirty_odd_nxt78;  
    status_dirty_odd_r79 <=  status_dirty_odd_nxt79;  
    status_dirty_odd_r80 <=  status_dirty_odd_nxt80;  
    status_dirty_odd_r81 <=  status_dirty_odd_nxt81;  
    status_dirty_odd_r82 <=  status_dirty_odd_nxt82;  
    status_dirty_odd_r83 <=  status_dirty_odd_nxt83;  
    status_dirty_odd_r84 <=  status_dirty_odd_nxt84;  
    status_dirty_odd_r85 <=  status_dirty_odd_nxt85;  
    status_dirty_odd_r86 <=  status_dirty_odd_nxt86;  
    status_dirty_odd_r87 <=  status_dirty_odd_nxt87;  
    status_dirty_odd_r88 <=  status_dirty_odd_nxt88;  
    status_dirty_odd_r89 <=  status_dirty_odd_nxt89;  
    status_dirty_odd_r90 <=  status_dirty_odd_nxt90;  
    status_dirty_odd_r91 <=  status_dirty_odd_nxt91;  
    status_dirty_odd_r92 <=  status_dirty_odd_nxt92;  
    status_dirty_odd_r93 <=  status_dirty_odd_nxt93;  
    status_dirty_odd_r94 <=  status_dirty_odd_nxt94;  
    status_dirty_odd_r95 <=  status_dirty_odd_nxt95;  
    status_dirty_odd_r96 <=  status_dirty_odd_nxt96;  
    status_dirty_odd_r97 <=  status_dirty_odd_nxt97;  
    status_dirty_odd_r98 <=  status_dirty_odd_nxt98;  
    status_dirty_odd_r99 <=  status_dirty_odd_nxt99;  
    status_dirty_odd_r100 <=  status_dirty_odd_nxt100;  
    status_dirty_odd_r101 <=  status_dirty_odd_nxt101;  
    status_dirty_odd_r102 <=  status_dirty_odd_nxt102;  
    status_dirty_odd_r103 <=  status_dirty_odd_nxt103;  
    status_dirty_odd_r104 <=  status_dirty_odd_nxt104;  
    status_dirty_odd_r105 <=  status_dirty_odd_nxt105;  
    status_dirty_odd_r106 <=  status_dirty_odd_nxt106;  
    status_dirty_odd_r107 <=  status_dirty_odd_nxt107;  
    status_dirty_odd_r108 <=  status_dirty_odd_nxt108;  
    status_dirty_odd_r109 <=  status_dirty_odd_nxt109;  
    status_dirty_odd_r110 <=  status_dirty_odd_nxt110;  
    status_dirty_odd_r111 <=  status_dirty_odd_nxt111;  
    status_dirty_odd_r112 <=  status_dirty_odd_nxt112;  
    status_dirty_odd_r113 <=  status_dirty_odd_nxt113;  
    status_dirty_odd_r114 <=  status_dirty_odd_nxt114;  
    status_dirty_odd_r115 <=  status_dirty_odd_nxt115;  
    status_dirty_odd_r116 <=  status_dirty_odd_nxt116;  
    status_dirty_odd_r117 <=  status_dirty_odd_nxt117;  
    status_dirty_odd_r118 <=  status_dirty_odd_nxt118;  
    status_dirty_odd_r119 <=  status_dirty_odd_nxt119;  
    status_dirty_odd_r120 <=  status_dirty_odd_nxt120;  
    status_dirty_odd_r121 <=  status_dirty_odd_nxt121;  
    status_dirty_odd_r122 <=  status_dirty_odd_nxt122;  
    status_dirty_odd_r123 <=  status_dirty_odd_nxt123;  
    status_dirty_odd_r124 <=  status_dirty_odd_nxt124;  
    status_dirty_odd_r125 <=  status_dirty_odd_nxt125;  
    status_dirty_odd_r126 <=  status_dirty_odd_nxt126;  
    status_dirty_odd_r127 <=  status_dirty_odd_nxt127;  
end

// LRU even : port0 or port1
//
always @*
begin : lru_even_sync_comb_PROC
  status_lru_even_nxt = status_lru_even_r;
  // Port 0
  //
  if (  status0_write_even_r 
      & status0_even_wem_r[LRU])
  begin
    status_lru_even_nxt[status0_even_addr_r] = status0_even_lru_r;
  end
  
  // Port 1
  //
  if (  status1_write_even_r 
      & status1_wem_r[LRU])
  begin
    status_lru_even_nxt[status1_addr_r] = status1_lru_r;
  end
end

// LRU odd : port0 or port1
//
always @*
begin : lru_odd_sync_comb_PROC
  status_lru_odd_nxt = status_lru_odd_r;
  // Port 0                                                      
  //                                                             
  if (  status0_write_odd_r                                      
      & status0_odd_wem_r[LRU])                                  
  begin                                                          
    status_lru_odd_nxt[status0_odd_addr_r] =  status0_odd_lru_r;  
  end                                                            
                                                                 
  // Port 1                                                      
  //                                                             
  if (  status1_write_odd_r                                      
      & status1_wem_r[LRU])                                      
  begin                                                          
    status_lru_odd_nxt[status1_addr_r] = status1_lru_r;           
  end                                                            
end
always @(posedge clk)
begin : lru_sync_PROC
    status_lru_even_r <= status_lru_even_nxt;
    status_lru_odd_r  <= status_lru_odd_nxt;           
end
// leda FM_1_7 on

// leda S_1C_R on
// leda G_551_1_C on
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
// spyglass enable_block ResetFlop-ML
//////////////////////////////////////////////////////////////////////////////
// @ Synchronous processes: Read port 1
//
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : status1_read_even_reg_PROC
  if (rst_a == 1'b1)
  begin
    status1_read_even_r   <= 1'b0;
  end
  else if (status1_read_even_cg0 == 1'b1)
  begin
    status1_read_even_r   <= dc_status1_read & (~dc_status1_odd);
  end
end

always @(posedge clk or posedge rst_a)
begin : status1_read_odd_reg_PROC
  if (rst_a == 1'b1)
  begin
    status1_read_odd_r    <= 1'b0;
  end
  else if (status1_read_odd_cg0 == 1'b1)
  begin
    status1_read_odd_r   <= dc_status1_read & dc_status1_odd;
  end
end

//////////////////////////////////////////////////////////////////////////////
// @ Synchronous processes: Read port 1 outputs
//
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : status1_port_sync_PROC
  if (rst_a == 1'b1)
  begin
    status1_lru_even_r      <= 1'b0;
    status1_lock_even_r     <= 1'b0;
    status1_dirty_even_r    <= {`npuarc_DC_WAYS{1'b0}};

    status1_lru_odd_r       <= 1'b0;
    status1_lock_odd_r      <= 1'b0;
    status1_dirty_odd_r     <= {`npuarc_DC_WAYS{1'b0}};
  end
  else if (status1_read_even_r | status1_read_odd_r)
  begin
    status1_lru_even_r    <= status1_lru_even_nxt;  
    status1_lock_even_r   <= status1_lock_even_nxt; 
    status1_dirty_even_r  <= status1_dirty_even_nxt;

    status1_lru_odd_r     <= status1_lru_odd_nxt;   
    status1_lock_odd_r    <= status1_lock_odd_nxt;  
    status1_dirty_odd_r   <= status1_dirty_odd_nxt; 
  end
end


endmodule // alb_dmp_status
