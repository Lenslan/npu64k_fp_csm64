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
// #                                                                   #
// #                        #                                    #     #
// #                                                                   #
// #       ####    ### #   ##     ####         #    #  # ###    ##    ####
// #      #    #  #   #     #    #    #        #    #  ##   #    #     #
// #      #    #  #   #     #    #             #    #  #    #    #     #
// #      #    #   ###      #    #             #    #  #    #    #     #
// #      #    #  #         #    #    #        #   ##  #    #    #     #  #
// #####   ####    ####   #####   ####          ### #  #    #  #####    ##
//                #    #
//                 ####
//
// ===========================================================================
//
// Description:
//
// @f:logic_unit:
// @p
//  This module implements the Logic Unit for an ARCompact instruction set.
//  The following instructions are provided by this unit:
//  \begin{itemize}
//    \item Basic logical operators: |AND|, |OR|, |XOR|, |NOT|, |TST|
//    \item Bit-wise operations: |BCLR|, |BTST|, |BMSK|, |BIC|, 
//             |BSET|, |BXOR|
//    \item Move operations: |MOV|, |EXTW|, |SEXW|, |EXTB|, |SEXB|
//    \item Shift and rotate operations: |ASL|, |ASR|, |LSR|, 
//             |RLC|, |ROR|, |RRC|
//    \item Conditional branch tests: |BBITn|
//  \end{itemize}
// @e
// ===========================================================================


// =======================================================================
// @v:logic-ucode:Logic unit microcode settings:
// =======================================================================
//  The behavior of the logic unit is determined by 12 ucode bits,
//  detailed below. The setting of each microcode bit is determined by the
//  decoder task for each instruction, which is given in acode_tasks.v
//
// -----------------------------------------------------------------------
//  \ _  Inst    A O X N T  B B B B B B   M   E S E S   A A L  R R R  R  B
//    \ _        N R O O S  C T M I S X   O   X E X E   S S S  L O R  O  B
//        \ _    D   R T T  L S S C E O   V   T X T X   L R R  C R C  L  I
//  ucode    \              R T K   T R       W W B B                    T
// ----------------------------------------------------------------------
//  and_op       1 0 0 1 1  1 1 1 1 0 0   0   0 0 0 0   0 0 0  0 0 0  0  1
//  or_op        0 1 0 0 0  0 0 0 0 1 0   0   0 0 0 0   0 0 0  0 0 0  0  0
//  xor_op       0 0 1 0 0  0 0 0 0 0 1   0   0 0 0 0   0 0 0  0 0 0  0  0
//  mov_op       0 0 0 0 0  0 0 0 0 0 0   1   1 1 1 1   0 0 0  0 0 0  0  0
//  shift_op     0 0 0 0 0  0 0 0 0 0 0   0   0 0 0 0   1 1 1  1 1 1  1  0
//  mask_sel     0 0 0 0 0  1 1 1 0 1 1   0   0 0 0 0   0 0 0  0 0 0  0  1
//  byte_size    0 0 0 0 0  0 0 0 0 0 0   0   0 0 1 1   0 0 0  0 0 0  0  0
//  half_size    0 0 0 0 0  0 0 0 0 0 0   0   1 1 0 0   0 0 0  0 0 0  0  0
//  left         0 0 0 0 0  0 0 0 0 0 0   0   0 0 0 0   1 0 0  1 0 0  1  0
//  rotate       0 0 0 0 0  0 0 0 0 0 0   0   0 0 0 0   0 0 0  1 1 1  1  0
//  with_carry   0 0 0 0 0  0 0 0 0 0 0   0   0 0 0 0   0 0 0  1 0 1  0  0
//  signed_op    0 0 0 0 0  0 0 0 0 0 0   0   0 0 0 0   1 1 0  0 0 0  0  0
//  ----------------------------------------------------------------------
//
//  The mutual-exclusivity of the microcode bits is essential for the
//  correct operation of the Logical Unit, as they control the muxing of
//  values in the large assign statement which implements the Logic Unit.
// =======================================================================
// @e

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_logic_unit (
  ////////// Operands //////////////////////////////////////////////////////
  //
  src1,               // source operand 1
  src2,               // source operand 2
  src2_mask,          // alternative mask input for src2
  carry_flag,         // carry flag

  ////////// Control signals ///////////////////////////////////////////////
  //
  or_op,              // logical OR operator
  and_op,             // logical AND operator
  xor_op,             // logical XOR operator
  mov_op,             // mov or extend operator
  signed_op,          // signed versus unsigned data
  mask_sel,           // operand 2 should be src2_mask
  byte_size,          // byte-sized extend or sign-extend
  half_size,          // half-word sized ext or sign-extend
  shift_op,           // Single-bit shift or rotate
  left,               // perform left or right shift
  rotate,             // perform rotation or shifting
  with_carry,         // rotate through carry

  ////////// Logic unit ouptuts ////////////////////////////////////////////
  //
  result,             // result output
  zero,               // zero result
  negative,           // negative result
  carry,              // carry out
  overflow            // overflow (used only by ASL)
);

////////////////////////////////////////////////////////////////////////////
// Input declarations
////////////////////////////////////////////////////////////////////////////

input   [`npuarc_DATA_RANGE]       src1;         // source operand 1
input   [`npuarc_DATA_RANGE]       src2;         // source operand 2
input   [`npuarc_DATA_RANGE]       src2_mask;    // alternative mask input for src2
input                       carry_flag;   // carry flag
input                       or_op;        // logical OR operator
input                       and_op;       // logical AND operator
input                       xor_op;       // logical XOR operator
input                       mov_op;       // mov or extend operator
input                       signed_op;    // signed vs. unsigned operations
input                       mask_sel;     // enables mask operand as src2
input                       byte_size;    // mov or extend is byte sized
input                       half_size;    // mov or extend is half-word sized
input                       shift_op;     // single-bit shift or rotate
input                       left;         // shift or rotate left
input                       rotate;       // rotate versus shift
input                       with_carry;   // include carry in rotation

////////////////////////////////////////////////////////////////////////////
// Output declarations
////////////////////////////////////////////////////////////////////////////

output  [`npuarc_DATA_RANGE]       result;       // logic unit result
output                      zero;         // zero flag result
output                      negative;     // negative flag result
output                      carry;        // carry out flag result
output                      overflow;     // overflow flag result

wire    [`npuarc_DATA_RANGE]       result;
wire                        negative;
wire                        zero;
wire                        carry;
wire                        overflow;

// Intermediate values
//
wire    [`npuarc_DATA_RANGE]       gated_src2;   // muxed version of src2
wire    [`npuarc_DATA_RANGE]       shift_val;    // shifter result
wire    [`npuarc_DATA_RANGE]       logic_result; // logical operations result
wire    [`npuarc_DATA_RANGE]       src2_15_to_0; // lower half of src2
wire    [`npuarc_DATA_RANGE]       src2_7_to_0;  // lower byte of src2

// @v:logic-logic:Logic unit implementation:
// Create multiplexed gated_src2 from src2 or src2_mask
//
assign gated_src2 = (src2      & {32{~mask_sel}})
                  | (src2_mask & {32{ mask_sel}});

// Perform the shift/rotate operation on src2
//
assign shift_val[30:1] = (left == 1'b1) 
                       ? src2[29:0] 
                       : src2[`npuarc_DATA_MSB:2];

assign shift_val[0]   = (carry_flag      &  left &  with_carry)
                      | (src2[`npuarc_DATA_MSB] &  left & (~with_carry) & rotate)
                      | (src2[1]         & (~left));

assign shift_val[`npuarc_DATA_MSB] = 
                        (src2[30] &  left)
                      | (src2[`npuarc_DATA_MSB]   & (~left) & signed_op)
                      | (src2[`npuarc_DATA_LSB]   & (~left) & rotate & (~with_carry))
                      | (carry_flag        & (~left) & rotate &  with_carry);


assign src2_15_to_0 = {16'd0, src2[15:0]};
assign src2_7_to_0  = {24'd0, src2[7:0]};

// Perform the bit-wise logical and single-bit shift operations
//
assign logic_result =
    (src1 & gated_src2) & {`npuarc_DATA_SIZE{and_op}}          // AND, BCLR, BTST, BIC
                                                        // BMSK, NOT, TST
  | (src1 | gated_src2) & {`npuarc_DATA_SIZE{or_op}}           // OR, BSET
  | (src1 ^ gated_src2) & {`npuarc_DATA_SIZE{xor_op}}          // XOR, BXOR
  | (src2 & {`npuarc_DATA_SIZE{  mov_op                        // MOV
                        & (~byte_size) & (~half_size)}})
  | (    src2_15_to_0                                   // EXTW
      & {`npuarc_DATA_SIZE{mov_op & half_size & (~signed_op)}})
  | (   { {16{src2[15]}}, src2[15:0] }                  // SEXW
      & {`npuarc_DATA_SIZE{mov_op & half_size &  signed_op}})
  | (   src2_7_to_0                                     // EXTB
      & {`npuarc_DATA_SIZE{mov_op & byte_size & (~signed_op)}})
  | (   { {24{src2[7]}}, src2[7:0] }                    // SEXB
      & {`npuarc_DATA_SIZE{mov_op & byte_size &  signed_op}})
  | (shift_val & {`npuarc_DATA_SIZE{shift_op}})                // ASL, RLC, ASR,
  ;                                                     // LSR, ROR, RRC.

assign zero     = (result == `npuarc_DATA_SIZE'd0);

assign negative = result[`npuarc_DATA_MSB];

assign carry    = (left == 1'b1)
                ? src2[`npuarc_DATA_MSB] & shift_op
                : src2[`npuarc_DATA_LSB] & shift_op
                ;

assign overflow = shift_op & left & signed_op 
                & (src2[30] != src2[`npuarc_DATA_MSB]);
// @e

// Select the result from this unit
//
assign result = logic_result;

endmodule
