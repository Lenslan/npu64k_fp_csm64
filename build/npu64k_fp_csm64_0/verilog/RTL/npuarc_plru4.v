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
// Description:
// @p
//  The plru module implements a pseudo-LRU algorithm for appx. tracking the
//  least recently used (LRU) item in a set of eight items (e.g. utlb entries).
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
// `include "defines.v"

// Set simulation timescale
//
// `include "const.def"

module npuarc_plru4
(
  ////////// General input signals ///////////////////////////////////////////
  //
  input                         clk,            // Processor clock
  input                         rst,            // Global reset

  // Enable uTLB
  input                         lru_clear,     // reset to default state
  input      [3:0]              match_entry,   // use entry (perform update)
  output reg [3:0]              lru_entry      // least recently used item
);
  

// Internal signals
//
reg  [2:0]                     plru_bits_ce;
reg  [2:0]                     plru_bits_nxt;
reg  [2:0]                     plru_bits_r;


// Updating PLRU bits on entry hits
// U = unchanged
//----------|--------------------------|
//          |        PLRU BITS         |
//   hit    |                          |
//   way    |   bit[2]  bit[1]  bit[0] |
//----------|--------------------------|
//    0     |     0       U       0    |
//    1     |     0       U       1    |
//    2     |     1       0       U    |
//    3     |     1       1       U    |
//----------|--------------------------|
// 
// 0 = bit unchanged
// 1 = update bit

always @*
begin : lru_bits_ce_logic_PROC
  if (lru_clear)
  begin
    plru_bits_ce = 3'b111;
  end
  else
  begin
    case (1'b1)
      match_entry[0]:  plru_bits_ce = 3'b101;
      match_entry[1]:  plru_bits_ce = 3'b101;
      match_entry[2]:  plru_bits_ce = 3'b110;
      match_entry[3]:  plru_bits_ce = 3'b110;
      default:         plru_bits_ce = 3'b000;
    endcase // case (1'b1)
  end
end

// leda FM_2_4 off
// leda W443 off
// spyglass disable_block NoAssignX-ML
// SMD: RHS of assignment contains x
// SJ:  Done on purpose to cover multiple bit combinations
always @*
begin : lru_bits_nxt_logic_PROC
  if (lru_clear)
  begin
    plru_bits_nxt = 3'b000;
  end
  else
  begin
    case (1'b1)
      match_entry[0]:  plru_bits_nxt = 3'b0x0;
      match_entry[1]:  plru_bits_nxt = 3'b0x1;
      match_entry[2]:  plru_bits_nxt = 3'b10x;
      match_entry[3]:  plru_bits_nxt = 3'b11x;
      default:         plru_bits_nxt = 3'bxxx;
    endcase
  end
end
// leda FM_2_4 on
// leda W443 on
// spyglass enable_block NoAssignX-ML

// Selecting the Replacement (victim) entry
// 
//--------------------------|----------|
//        PLRU BITS         |          |
//                          |  victim  |
//   bit[2]  bit[1]  bit[0] |   way    |
//--------------------------|----------|
//     0       0       x    |    3     |
//     0       1       x    |    2     |
//     1       x       0    |    1     |
//     1       x       1    |    0     |
//--------------------------|----------|

always @*
begin : lru_repl_logic_PROC
  casez (plru_bits_r)
    3'b00?:  lru_entry = 4'b1000;
    3'b01?:  lru_entry = 4'b0100;
    3'b1?0:  lru_entry = 4'b0010;
    3'b1?1:  lru_entry = 4'b0001;
    default  lru_entry = 4'b1000;
  endcase
end

// LRU bits registers
//
always @(posedge clk or posedge rst)

begin : lru_registers_PROC
  if (rst == 1'b1)
  begin
    plru_bits_r <= 3'b0;
  end
  else
  begin
    //plru_bits_r <= plru_bits_r;
    if (plru_bits_ce[0])
    begin
      plru_bits_r[0] <= plru_bits_nxt[0];
    end
    if (plru_bits_ce[1])
    begin
      plru_bits_r[1] <= plru_bits_nxt[1];
    end
    if (plru_bits_ce[2])
    begin
      plru_bits_r[2] <= plru_bits_nxt[2];
    end
  end
end

endmodule
