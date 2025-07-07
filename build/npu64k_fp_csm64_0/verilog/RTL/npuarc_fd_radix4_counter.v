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
// Certain materials incorporated herein are copyright (C) 2010 - 2012, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
// Description:
//
// FAST DIVIDER SUPPORT MODULE.
// down counter for radix 4 steps
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a
//  command line such as:
//
//   vpp +q +o fd_radix4_counter.vpp
//
// ===========================================================================
//
module npuarc_fd_radix4_counter (
  input              clk,         // Clock input
  input              reset_a,     // Asynchronous reset input
  input              start,       // load input, start counting down if not hold
  input              hold,        // freeze counter
  input    [5:0]     init_ct,     // 16 steps max
  output             done         // terminal count - reached zero
);

reg      [5:0]     count;

// Counter flops and count logic
// leda W484 off
// LMD: Possible loss of carry/borrow
// LJ: Counter stops at 1, so cannot underflow
// leda BTTF_D002 off
// LMD: Unequal lenth LHS and RHS in assignment
// LJ: Actually same as W484
always @ (posedge clk or posedge reset_a)
begin : count_PROC
  if (reset_a == 1'b1)
     count <= 6'h 00;                 // reset
  else
  if (start)
     count <= init_ct;                // load
  else
  if ((!hold) && (!done))
     count <= count - 6'h 01;         // count down
end
// leda BTTF_D002 on
// leda W484 on

assign done = (count == 6'h 01) ? 1'b 1 : 1'b 0; // terminal count

endmodule   // fd_radix4_counter

