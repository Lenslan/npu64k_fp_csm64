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
//  The plru8 module implements a pseudo-LRU algorithm for appx. tracking the
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

module npuarc_plru8
(
  ////////// General input signals ///////////////////////////////////////////
  //
  input                         clk,            // Processor clock
  input                         rst,            // Global reset

  // Enable uTLB
  input                         lru_clear,     // reset to default state
  input      [7:0]              match_entry,   // use entry (perform update)
  output reg [7:0]              lru_entry      // least recently used item
);
  

// Internal signals
//
reg  [6:0]                     plru_bits_ce;
reg  [6:0]                     plru_bits_nxt;
reg  [6:0]                     plru_bits_r;

  


// Updating PLRU bits on entry hits
// U = unchanged
//----------|----------------------------------------------------------|
//          |                    PLRU BITS                             |
//   hit    |                                                          |
//   way    |   bit[6]  bit[5]  bit[4]  bit[3]  bit[2]  bit[1]  bit[0] |
//----------|----------------------------------------------------------|
//    0     |     0       U       0       U       U       U       0    |
//    1     |     0       U       0       U       U       U       1    |
//    2     |     0       U       1       U       U       0       U    |
//    3     |     0       U       1       U       U       1       U    |
//    4     |     1       0       U       U       0       U       U    |
//    5     |     1       0       U       U       1       U       U    |
//    6     |     1       1       U       0       U       U       U    |
//    7     |     1       1       U       1       U       U       U    |
//----------|----------------------------------------------------------|
// 
// 0 = bit unchanged
// 1 = update bit

always @*
begin : lru_bits_ce_logic_PROC
  if (lru_clear)
  begin
    plru_bits_ce = 7'b111_1111;
  end
  else
  begin
    case (1'b1)
      match_entry[0]:  plru_bits_ce = 7'b101_0001;
      match_entry[1]:  plru_bits_ce = 7'b101_0001;
      match_entry[2]:  plru_bits_ce = 7'b101_0010;
      match_entry[3]:  plru_bits_ce = 7'b101_0010;
      match_entry[4]:  plru_bits_ce = 7'b110_0100;
      match_entry[5]:  plru_bits_ce = 7'b110_0100;
      match_entry[6]:  plru_bits_ce = 7'b110_1000;
      match_entry[7]:  plru_bits_ce = 7'b110_1000;
      default:         plru_bits_ce = 7'b000_0000;
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
    plru_bits_nxt = 7'b000_0000;
  end
  else
  begin
    case (1'b1)
      match_entry[0]:  plru_bits_nxt = 7'b0x0_xxx0;
      match_entry[1]:  plru_bits_nxt = 7'b0x0_xxx1;
      match_entry[2]:  plru_bits_nxt = 7'b0x1_xx0x;
      match_entry[3]:  plru_bits_nxt = 7'b0x1_xx1x;
      match_entry[4]:  plru_bits_nxt = 7'b10x_x0xx;
      match_entry[5]:  plru_bits_nxt = 7'b10x_x1xx;
      match_entry[6]:  plru_bits_nxt = 7'b11x_0xxx;
      match_entry[7]:  plru_bits_nxt = 7'b11x_1xxx;
      default:         plru_bits_nxt = 7'bxxx_xxxx;
    endcase
  end
end
// leda FM_2_4 on
// leda W443 on
// spyglass enable_block NoAssignX-ML

// Selecting the Replacement (victim) entry
// 
//----------------------------------------------------------|----------|
//                 PLRU BITS                                |          |
//                                                          |  victim  |
//   bit[6]  bit[5]  bit[4]  bit[3]  bit[2]  bit[1]  bit[0] |   way    |
//----------------------------------------------------------|----------|
//     0       0       x       0       x       x       x    |    7     |
//     0       0       x       1       x       x       x    |    6     |
//     0       1       x       x       0       x       x    |    5     |
//     0       1       x       x       1       x       x    |    4     |
//     1       x       0       x       x       0       x    |    3     |
//     1       x       0       x       x       1       x    |    2     |
//     1       x       1       x       x       x       0    |    1     |
//     1       x       1       x       x       x       1    |    0     |
//----------------------------------------------------------|----------|
// spyglass disable_block Clock_info03a
// SMD: Clock-Net is unconstrained
// SJ:  Is constrained
always @*
begin : lru_repl_logic_PROC
  casez (plru_bits_r)
    7'b00?0???:  lru_entry = 8'b1000_0000;
    7'b00?1???:  lru_entry = 8'b0100_0000;
    7'b01??0??:  lru_entry = 8'b0010_0000;
    7'b01??1??:  lru_entry = 8'b0001_0000;
    7'b1?0??0?:  lru_entry = 8'b0000_1000;
    7'b1?0??1?:  lru_entry = 8'b0000_0100;
    7'b1?1???0:  lru_entry = 8'b0000_0010;
    7'b1?1???1:  lru_entry = 8'b0000_0001;
    default:     lru_entry = 8'b1000_0000;
  endcase
end

// LRU bits registers
//
always @(posedge clk or posedge rst)

begin : lru_registers_PROC
  if (rst == 1'b1)
  begin
    plru_bits_r <= 7'b0;
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
    if (plru_bits_ce[3])
    begin
      plru_bits_r[3] <= plru_bits_nxt[3];
    end
    if (plru_bits_ce[4])
    begin
      plru_bits_r[4] <= plru_bits_nxt[4];
    end
    if (plru_bits_ce[5])
    begin
      plru_bits_r[5] <= plru_bits_nxt[5];
    end
    if (plru_bits_ce[6])
    begin
      plru_bits_r[6] <= plru_bits_nxt[6];
    end
  end
end

// spyglass enable_block Clock_info03a

endmodule
