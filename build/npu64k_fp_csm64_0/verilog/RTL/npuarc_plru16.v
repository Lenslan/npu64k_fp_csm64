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
//  The plru16 module implements a pseudo-LRU algorithm for appx. tracking the
//  least recently used (LRU) item in a set of 16 items (e.g. utlb entries).
// @e
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o plru16.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
// `include "defines.v"

// Set simulation timescale
//
// `include "const.def"

module npuarc_plru16
(
  ////////// General input signals ///////////////////////////////////////////
  //
  input                         clk,            // Processor clock
  input                         rst,            // Global reset

  // Enable uTLB
  input      [15:0]             match_entry,   // use entry (perform update)
  output reg [15:0]             lru_entry      // least recently used item
);
  

// Internal signals
//
reg  [14:0]                     plru_bits_ce;
reg  [14:0]                     plru_bits_nxt;
reg  [14:0]                     plru_bits_r;

  


// Updating PLRU bits on entry hits
// U = unchanged
//----------|-----------------------------------------------------------------|
//          |                          PLRU BITS                              |
//   hit    |                                                                 |
//   way    | bit:14   -  13 12   -  11 10  9  8   -   7  6  5  4  3  2  1  0 |
//----------|-----------------------------------------------------------------|
//    0     |      0   -   U  0   -   U  U  U  0   -   U  U  U  U  U  U  U  0 |
//    1     |      0   -   U  0   -   U  U  U  0   -   U  U  U  U  U  U  U  1 |
//    2     |      0   -   U  0   -   U  U  U  1   -   U  U  U  U  U  U  0  U |
//    3     |      0   -   U  0   -   U  U  U  1   -   U  U  U  U  U  U  1  U |
//    4     |      0   -   U  1   -   U  U  0  U   -   U  U  U  U  U  0  U  U |
//    5     |      0   -   U  1   -   U  U  0  U   -   U  U  U  U  U  1  U  U |
//    6     |      0   -   U  1   -   U  U  1  U   -   U  U  U  U  0  U  U  U |
//    7     |      0   -   U  1   -   U  U  1  U   -   U  U  U  U  1  U  U  U |
//    8     |      1   -   0  U   -   U  0  U  U   -   U  U  U  0  U  U  U  U |
//    9     |      1   -   0  U   -   U  0  U  U   -   U  U  U  1  U  U  U  U |
//   10     |      1   -   0  U   -   U  1  U  U   -   U  U  0  U  U  U  U  U |
//   11     |      1   -   0  U   -   U  1  U  U   -   U  U  1  U  U  U  U  U |
//   12     |      1   -   1  U   -   0  U  U  U   -   U  0  U  U  U  U  U  U |
//   13     |      1   -   1  U   -   0  U  U  U   -   U  1  U  U  U  U  U  U |
//   14     |      1   -   1  U   -   1  U  U  U   -   0  U  U  U  U  U  U  U |
//   15     |      1   -   1  U   -   1  U  U  U   -   1  U  U  U  U  U  U  U |
//----------|-----------------------------------------------------------------|
// 
// 0 = bit unchanged
// 1 = update bit

always @*
begin : lru_bits_ce_logic_PROC
  case (1'b1)
    match_entry[0] :  plru_bits_ce = 15'b1_01_0001_00000001;
    match_entry[1] :  plru_bits_ce = 15'b1_01_0001_00000001;
    match_entry[2] :  plru_bits_ce = 15'b1_01_0001_00000010;
    match_entry[3] :  plru_bits_ce = 15'b1_01_0001_00000010;
    match_entry[4] :  plru_bits_ce = 15'b1_01_0010_00000100;
    match_entry[5] :  plru_bits_ce = 15'b1_01_0010_00000100;
    match_entry[6] :  plru_bits_ce = 15'b1_01_0010_00001000;
    match_entry[7] :  plru_bits_ce = 15'b1_01_0010_00001000;
    match_entry[8] :  plru_bits_ce = 15'b1_10_0100_00010000;
    match_entry[9] :  plru_bits_ce = 15'b1_10_0100_00010000;
    match_entry[10]:  plru_bits_ce = 15'b1_10_0100_00100000;
    match_entry[11]:  plru_bits_ce = 15'b1_10_0100_00100000;
    match_entry[12]:  plru_bits_ce = 15'b1_10_1000_01000000;
    match_entry[13]:  plru_bits_ce = 15'b1_10_1000_01000000;
    match_entry[14]:  plru_bits_ce = 15'b1_10_1000_10000000;
    match_entry[15]:  plru_bits_ce = 15'b1_10_1000_10000000;
    default:          plru_bits_ce = 15'b0_00_0000_00000000;
  endcase
end

// leda FM_2_4 off
// leda W443 off
// spyglass disable_block NoAssignX-ML
// SMD: RHS of assignment contains x
// SJ:  Done on purpose to cover multiple bit combinations
always @*
begin : lru_bits_nxt_logic_PROC
  case (1'b1)
    match_entry[0] :  plru_bits_nxt = 15'b0_x0_xxx0_xxxxxxx0;
    match_entry[1] :  plru_bits_nxt = 15'b0_x0_xxx0_xxxxxxx1;
    match_entry[2] :  plru_bits_nxt = 15'b0_x0_xxx1_xxxxxx0x;
    match_entry[3] :  plru_bits_nxt = 15'b0_x0_xxx1_xxxxxx1x;
    match_entry[4] :  plru_bits_nxt = 15'b0_x1_xx0x_xxxxx0xx;
    match_entry[5] :  plru_bits_nxt = 15'b0_x1_xx0x_xxxxx1xx;
    match_entry[6] :  plru_bits_nxt = 15'b0_x1_xx1x_xxxx0xxx;
    match_entry[7] :  plru_bits_nxt = 15'b0_x1_xx1x_xxxx1xxx;
    match_entry[8] :  plru_bits_nxt = 15'b1_0x_x0xx_xxx0xxxx;
    match_entry[9] :  plru_bits_nxt = 15'b1_0x_x0xx_xxx1xxxx;
    match_entry[10]:  plru_bits_nxt = 15'b1_0x_x1xx_xx0xxxxx;
    match_entry[11]:  plru_bits_nxt = 15'b1_0x_x1xx_xx1xxxxx;
    match_entry[12]:  plru_bits_nxt = 15'b1_1x_0xxx_x0xxxxxx;
    match_entry[13]:  plru_bits_nxt = 15'b1_1x_0xxx_x1xxxxxx;
    match_entry[14]:  plru_bits_nxt = 15'b1_1x_1xxx_0xxxxxxx;
    match_entry[15]:  plru_bits_nxt = 15'b1_1x_1xxx_1xxxxxxx;
    default:          plru_bits_nxt = 15'bx_xx_xxxx_xxxxxxxx;
  endcase
end
// leda FM_2_4 on
// leda W443 on
// spyglass enable_block NoAssignX-ML

// Selecting the Replacement (victim) entry
// 
//------------------------------------------------------------|----------|
//                          PLRU BITS                         |          |
//                                                            |  victim  |
// bit:14  - 13 12  - 11 10  9  8  -  7  6  5  4  3  2  1  0  |   way    |
//------------------------------------------------------------|----------|
//      0  -  0  x  -  0  x  x  x  -  0  x  x  x  x  x  x  x  |    15    |
//      0  -  0  x  -  0  x  x  x  -  1  x  x  x  x  x  x  x  |    14    |
//      0  -  0  x  -  1  x  x  x  -  x  0  x  x  x  x  x  x  |    13    |
//      0  -  0  x  -  1  x  x  x  -  x  1  x  x  x  x  x  x  |    12    |
//      0  -  1  x  -  x  0  x  x  -  x  x  0  x  x  x  x  x  |    11    |
//      0  -  1  x  -  x  0  x  x  -  x  x  1  x  x  x  x  x  |    10    |
//      0  -  1  x  -  x  1  x  x  -  x  x  x  0  x  x  x  x  |     9    |
//      0  -  1  x  -  x  1  x  x  -  x  x  x  1  x  x  x  x  |     8    |
//      1  -  x  0  -  x  x  0  x  -  x  x  x  x  0  x  x  x  |     7    |
//      1  -  x  0  -  x  x  0  x  -  x  x  x  x  1  x  x  x  |     6    |
//      1  -  x  0  -  x  x  1  x  -  x  x  x  x  x  0  x  x  |     5    |
//      1  -  x  0  -  x  x  1  x  -  x  x  x  x  x  1  x  x  |     4    |
//      1  -  x  1  -  x  x  x  0  -  x  x  x  x  x  x  0  x  |     3    |
//      1  -  x  1  -  x  x  x  0  -  x  x  x  x  x  x  1  x  |     2    |
//      1  -  x  1  -  x  x  x  1  -  x  x  x  x  x  x  x  0  |     1    |
//      1  -  x  1  -  x  x  x  1  -  x  x  x  x  x  x  x  1  |     0    |
//------------------------------------------------------------|----------|

always @*
begin : lru_repl_logic_PROC
  casez (plru_bits_r)
    15'b0_0?_0???_0???????: lru_entry = 16'b1000_0000_0000_0000;
    15'b0_0?_0???_1???????: lru_entry = 16'b0100_0000_0000_0000;
    15'b0_0?_1???_?0??????: lru_entry = 16'b0010_0000_0000_0000;
    15'b0_0?_1???_?1??????: lru_entry = 16'b0001_0000_0000_0000;
    15'b0_1?_?0??_??0?????: lru_entry = 16'b0000_1000_0000_0000;
    15'b0_1?_?0??_??1?????: lru_entry = 16'b0000_0100_0000_0000;
    15'b0_1?_?1??_???0????: lru_entry = 16'b0000_0010_0000_0000;
    15'b0_1?_?1??_???1????: lru_entry = 16'b0000_0001_0000_0000;
    15'b1_?0_??0?_????0???: lru_entry = 16'b0000_0000_1000_0000;
    15'b1_?0_??0?_????1???: lru_entry = 16'b0000_0000_0100_0000;
    15'b1_?0_??1?_?????0??: lru_entry = 16'b0000_0000_0010_0000;
    15'b1_?0_??1?_?????1??: lru_entry = 16'b0000_0000_0001_0000;
    15'b1_?1_???0_??????0?: lru_entry = 16'b0000_0000_0000_1000;
    15'b1_?1_???0_??????1?: lru_entry = 16'b0000_0000_0000_0100;
    15'b1_?1_???1_???????0: lru_entry = 16'b0000_0000_0000_0010;
    15'b1_?1_???1_???????1: lru_entry = 16'b0000_0000_0000_0001;
    default:                lru_entry = 16'b1000_0000_0000_0000;
  endcase
end

// LRU bits registers
//
always @(posedge clk or posedge rst)

begin : lru_registers_PROC
  if (rst == 1'b1)
  begin
    plru_bits_r <= 15'b0;
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
    if (plru_bits_ce[7])
    begin
      plru_bits_r[7] <= plru_bits_nxt[7];
    end
    if (plru_bits_ce[8])
    begin
      plru_bits_r[8] <= plru_bits_nxt[8];
    end
    if (plru_bits_ce[9])
    begin
      plru_bits_r[9] <= plru_bits_nxt[9];
    end
    if (plru_bits_ce[10])
    begin
      plru_bits_r[10] <= plru_bits_nxt[10];
    end
    if (plru_bits_ce[11])
    begin
      plru_bits_r[11] <= plru_bits_nxt[11];
    end
    if (plru_bits_ce[12])
    begin
      plru_bits_r[12] <= plru_bits_nxt[12];
    end
    if (plru_bits_ce[13])
    begin
      plru_bits_r[13] <= plru_bits_nxt[13];
    end
    if (plru_bits_ce[14])
    begin
      plru_bits_r[14] <= plru_bits_nxt[14];
    end
  end
end

endmodule
