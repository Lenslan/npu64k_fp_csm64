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
//   ##         #       #
//  #  #        #       #
// #    #       #       #
// #    #   ### #   ### #   ####   # ##
// #    #  #   ##  #   ##  #    #   #
// ######  #    #  #    #  ######   #
// #    #  #    #  #    #  #        #
// #    #  #   ##  #   ##  #    #   #
// #    #   ### #   ### #   ####    #
//
// ===========================================================================
//
// Description:
//
// @f:adder:
// @p
//  The |adder| module implements a fast 2's complement adder using a
//  Kogge-Stone parallel prefix look-ahead scheme~\cite{kogge73}.
//
//  It produces fast condition codes using a variety of logical short
//  cuts. It also produces a signal that is 1 when src1 is less than src2 and
//  0 at all other times. This can be used to implement |MIN| and |MAX|
//  instructions.
//
//  There is a {\em fast} sum output, produced using logic which assumes that
//  |carry_in| is always zero (as it is when computing an address).
// @e
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


module npuarc_alb_adder (
  ////////// Operands //////////////////////////////////////////////////////
  //
  src1,               // Operand 1
  src2,               // Operand 2
  carry_in,           // Carry in

  ////////// Adder ouptuts /////////////////////////////////////////////////
  //
  sum,                // Sum out
  sum_no_carry,       // Fast sum, assumes carry_in == 0
  zero,               // Zero result
  negative,           // Negative result
  carry_out,          // Carry out
  overflow,           // Overflow out
  lessthan           // 1 if src1 < src2, else 0 (timing optimized)
//  not_lessthan        // 1 if src1 >= src2, else 0 (timing optimized)
  );

////////////////////////////////////////////////////////////////////////////
// Input declarations
////////////////////////////////////////////////////////////////////////////

input   [`npuarc_DATA_RANGE]       src1;         // Operand 1
input   [`npuarc_DATA_RANGE]       src2;         // Operand 2
input                       carry_in;     // Carry in

////////////////////////////////////////////////////////////////////////////
// Output declarations
////////////////////////////////////////////////////////////////////////////

output  [`npuarc_DATA_RANGE]       sum;          // Sum result
output  [`npuarc_DATA_RANGE]       sum_no_carry; // Fast sum for address arith
output                      zero;         // Zero result
output                      negative;     // Negative result
output                      carry_out;    // Carry out
output                      overflow;     // Overflow
output                      lessthan;     // Less than
//output                      not_lessthan; // Greater than or equal

reg     [`npuarc_DATA_RANGE]       sum;
reg     [`npuarc_DATA_RANGE]       sum_no_carry;
reg                         zero;
reg                         negative;
reg                         carry_out;
reg                         overflow;
reg                         lessthan;
//reg                         not_lessthan;

// Declare arrays for the propagate and generate signals
//
reg     [`npuarc_DATA_RANGE]       _p0;
reg     [`npuarc_DATA_RANGE]       _g0;
reg     [`npuarc_DATA_RANGE]       _p1;
reg     [`npuarc_DATA_RANGE]       _g1;
reg     [`npuarc_DATA_RANGE]       _p2;
reg     [`npuarc_DATA_RANGE]       _g2;
reg     [`npuarc_DATA_RANGE]       _p3;
reg     [`npuarc_DATA_RANGE]       _g3;
reg     [`npuarc_DATA_RANGE]       _p4;
reg     [`npuarc_DATA_RANGE]       _g4;
// leda NTL_CON12A off
// leda NTL_CON13A off
// LMD: undriven internal net
// LJ:  Arithmetic module with not used bit
reg     [`npuarc_DATA_RANGE]       _g5;
reg     [`npuarc_DATA_RANGE]       _p5;
// leda NTL_CON12A on
// leda NTL_CON13A on
reg     [`npuarc_DATA_RANGE]       _g6;
reg     [`npuarc_DATA_RANGE]       _p6;

integer i;

// spyglass disable_block SelfDeterminedExpr-ML
// SMD: self determined expression
// SJ:  behavior code not structural so causes no issues
// SJ:  should change for loops to vpp for loops

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// A single combinational block containing all of the logic that          //
// makes up the complete adder.                                           //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : add_PROC

  //========================================================================
  // @p
  //  The adder is defined in three stages:
  //  \begin{enumerate}
  //     \item Sets of propagate and generate signals for each bit
  //           position are created.
  //
  //     \item A look-ahead carry tree is computed using a Kogge-Stone
  //          parallel prefix scheme.
  //
  //     \item The full-adder at each bit position is defined in terms
  //           of the inputs and the look-ahead carry signals.
  // \end{enumerate}
  // @e

  // @p
  // In the first stage, leaf-level propagate and generate signals are
  // defined for each bit in the sum.
  // @e
  _p0 = src1 | src2;
  _g0 = src1 & src2;


  // @p
  // The second stage comprises a parallel prefix look-ahead tree based
  // on the Kogge-Stone construction.
  // @e

  // @v:adder-logic-1:Parallel-prefix look-ahead tree for level 1:
  // Level 1 wiring
  //
  _g1[0] = _g0[0];
  _p1[0] = _p0[0];

  // Level 1 computational cells
  //
  for (i = 1; i < 32; i = i+1)
  begin
    _g1[i] = _g0[i] | (_g0[i-1] & _p0[i]);
    _p1[i] = _p0[i] & _p0[i-1];
  end
  // @e

  // @v:adder-logic-2:Parallel-prefix look-ahead tree for level 2:
  // Level 2 wiring
  //
  _g2[1:0] = _g1[1:0];
  _p2[1:0] = _p1[1:0];

  // Level 2 computations
  //
  for (i = 2; i < 32; i = i+1)
  begin
    _g2[i] = _g1[i] | (_g1[i-2] & _p1[i]);
    _p2[i] = _p1[i] & _p1[i-2];
  end
  // @e

  // @v:adder-logic-3:Parallel-prefix look-ahead tree for level 3:
  // Level 3 wiring
  //
  _g3[3:0] = _g2[3:0];
  _p3[3:0] = _p2[3:0];

  // Level 3 computations
  //
  for (i = 4; i < 32; i = i+1)
  begin
    _g3[i] = _g2[i] | (_g2[i-4] & _p2[i]);
    _p3[i] = _p2[i] & _p2[i-4];
  end
  // @e

  // @v:adder-logic-4:Parallel-prefix look-ahead tree for level 4:
  // Level 4 wiring
  //
  _g4[7:0] = _g3[7:0];
  _p4[7:0] = _p3[7:0];

  // Level 4 computations
  //
  for (i = 8; i < 32; i = i+1)
  begin
    _g4[i] = _g3[i] | (_g3[i-8] & _p3[i]);
    _p4[i] = _p3[i] & _p3[i-8];
  end
  // @e

  // @v:adder-logic-5:Parallel-prefix look-ahead tree for level 5:
  // Level 5 wiring
  //
  _g5[15:0] = _g4[15:0];
  _p5[15:0] = _p4[15:0];

  // Level 5 computations
  //
  for (i = 16; i < 32; i = i+1)
  begin
    _g5[i] = _g4[i] | (_g4[i-16] & _p4[i]);
    _p5[i] = _p4[i] & _p4[i-16];
  end
  // @e

  // @v:adder-logic-6:Parallel-prefix look-ahead tree for level 6:
  // Level 6 computations
  //
  _g6 = _g5 | (_p5 & {32{carry_in}});
  _p6 = (~_g0) & _p0;
  // @e

  // @p
  // The third stage comprise logic for the sum, and also the fast sum
  // which assumes there is no carry-in.
  // @e

  // @v:sum-logic:Sum and fast sum logic for the Kogge-Stone adder:
  sum          = _p6 ^ {_g6[30:0], carry_in};
  sum_no_carry = _p6 ^ {_g5[30:0], 1'b0};
  // @e

  // @p
  // Carry out is the most-significant {\em generate} signal at level 6
  // Overflow status is computed as the difference between carry-in and
  // carry-out of the most-significant bit position.
  // The negative result status bis is equivalent to the sign bit, |sum[31]|
  // Zero result is computed using a fast algorithm
  // The Less-than relation is computed by |(N ^ V)|, but as |N| = |sum[31]|
  // and |sum[31]| = |_p6[31] ^ _g6[30]|, and |V| = |_g6[31] ^ _g6[30]|,
  // then we can compute a less-than relation using simply |_g6[31] ^ _p6[31]|.
  // In principle this is as fast as generating overflow or carry-out.
  // @e
  // @v:status-logic:Status flag logic for the Kogge-Stone adder:
  carry_out = _g6[31];

  overflow = _g6[31] ^ _g6[30];

  negative = sum[31];

  zero = &( ~(_p6 ^ {_p0[30:0], carry_in}) );

  lessthan = _g6[31] ^ _p6[31];
  
//  not_lessthan = _g6[31] ^ (~_p6[31]);
  // @e

// spyglass enable_block SelfDeterminedExpr-ML

end
endmodule
