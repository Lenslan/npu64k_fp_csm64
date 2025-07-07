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
//   ###   #                ###    #
//  #   #  #         #     #   #   #
//  #      #               #       #
//  #      # ###    ##     #      ####    ####   # ##
//   ###   ##   #    #    ####     #     #    #   #
//      #  #    #    #     #       #     ######   #
//      #  #    #    #     #       #     #        #
//  #   #  #    #    #     #       #  #  #    #   #
//   ###   #    #  #####   #        ##    ####    #
//
// ===========================================================================
//
// Description:
//
//  The shifter module is a 32-bit barrel shifter capable of performing
//  the shift and rotate operations required by the ARCompact instruction
//  set:
//        ASR - arithmetic shift right
//        ASL - arithmtic shift left
//        LSR - logical shift right
//        ROR - rotate right
//
//  The extended arithmetic shift operations are not implemented in
//  this design (i.e. no support for saturating shifts or for signed
//  shift distances).
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_shifter (

  ////////// Input operands ////////////////////////////////////////////////
  //
  input   [4:0]             src2_s5,    // src1 (value to be shifted)
  input   [`npuarc_DATA_RANGE]     src1,       // src2[4:0] (shift distance)

  ////////// Control inputs ////////////////////////////////////////////////
  //
  input                     arith,      // perform arithmetic shift
  input                     left,       // perform left shift
  input                     rotate,     // perform rotation (right only)

  ////////// Custom XBFU inputs ////////////////////////////////////////////
  //
  input                     xbfu_op,    // XBFU operation
  input   [`npuarc_DATA_RANGE]     bit_mask,   // 

  ////////// Result and status values //////////////////////////////////////
  //
  output  [`npuarc_DATA_RANGE]     result,     // shifter result
  output                    zero,       // 1=>result is zero
  output                    negative,   // 1=>result is negative
  output                    carry_out,  // 1=>carry out is set
  output                    overflow    // 1=>overflow is set
);


//==========================================================================
//
// The barrel shifter directly supports the precise set of shift and rotate
// functionality needed by the ASLM, ASRM, LSRM, and RORM instructions.
// Note that all through-carry single-bit shift operations are implemented
// in the Logical Unit in order to minimize the overall critical path
// through the combined set of functional units in the Execute stage of the
// pipeline.
//
// The shifter implementation is a very conventional funnel shifter, in
// which each partial result is optionally shifted 2^k bit positions to the
// right at the k-th stage of 5-stage combinational shift network. This is
// preceded by a single stage of operand selection which produces an initial
// 65-bit input (stage_0) divided into an upper and a lower half, according
// to the following table, with the least-significant bit set to 0.
//
//  ------------------------------------------------------------------------
//  ARCompact       Microcode            65-bit input to funnel shifter
//  ------------------------------------------------------------------------
//  instruction Left Rotate Arith. stage_0[62:32]  stage_0[31:0] stage_0[0]
//  ------------------------------------------------------------------------
//     ASRM        0     0       1     {32{sign_bit}}  src1[31:0]   1'b0
//     ASLM        1     0       1     src1[31:0]      32'd0        1'b0
//     LSRM        0     0       0     {32{sign_bit}}  src1[31:0]   1'b0
//     RORM        0     1       0     src1[31:0]      src1[31:0]   1'b0
//  ------------------------------------------------------------------------
//
// The sign_bit is set to 1 if performing an arithmetic shift and if the
// MSB (sign bit) of src1 is set to 1.
//
// The 63-bit input can be generated from src1 and the control bits using a
// 2:1 multiplexer for each of the upper (31-bit) and lower (32-bit) values.
//
// When shifting left we must use the 2's complement of the given shift
// amount. This is computed by a conventional negation operation, designed
// to yield the resultant bits in the order in which they are used in the
// muxing network.
// This relies on the fact that to compute shmt = 32-src2[4:0] we require:
//
//   shmt[0] = src2_5[0]           - negation doesn't change bit 0
//   shmt[1] = left & src2_5[0]    - inv. bit 1 for left shift if bit 0 set
//   shmt[2] = left & |src2_5[1:0] - inv. bit 2 if bits 1 or 0 are set
//   ... and similarly for bits 3 and 4.
//
//==========================================================================


// Declare some intermediate control signal wires
//
wire                        sign_bit;
wire                        asl_or_ror;
wire      [4:0]             shmt;
wire                        zero_shift;

// Declare the inter-stage wiring for the shift network
//
wire      [64:0]            stage_0;      // this is the input stage
wire      [63:0]            stage_1;
wire      [61:0]            stage_2;
wire      [57:0]            stage_3;
wire      [49:0]            stage_4;
wire      [33:0]            stage_5;      // this is the output stage

// XBFU 'AND mask' implicit operation by reusing SHIFT AND op
//
wire      [33:0]            xbfu_mask;    // XBFU mask or all 1's if unused
wire      [33:0]            masked_sh16;  // optional mask, gated with shmt[4]
wire      [33:0]            masked_sh0;   // optional mask, gated with !shmt[4]

// Define the sign- or zero-extension bit
//
assign sign_bit = arith & src1[31];

// For input selection we need to detect either ASL or ROR operations
//
assign asl_or_ror = left | rotate;

// Detect zero shift distance (used primarily for left shift)
//
assign zero_shift = (src2_s5 == 5'd0);

// Compute the shift amount, possibly by negating the input shift distance
//
assign shmt[4:0] =  {
                      src2_s5[4] ^ (left & (|src2_s5[3:0])),
                      src2_s5[3] ^ (left & (|src2_s5[2:0])),
                      src2_s5[2] ^ (left & (|src2_s5[1:0])),
                      src2_s5[1] ^ (left & src2_s5[0]),
                      src2_s5[0]
                    };

// Reuse the SHIFT AND to perform implicit AND for XBFU
//
assign xbfu_mask      = {1'b1, (bit_mask | {32{~xbfu_op}}), 1'b1};
assign masked_sh16    = xbfu_mask & {34{shmt[4]}};
assign masked_sh0     = xbfu_mask & {34{~shmt[4]}};


// Select the initial input vector according to the type of operation
//
assign stage_0[32:0]  = (left == 1'b1)
                      ? 33'd0
                      : {src1[31:0], 1'b0};

assign stage_0[64:33] = (asl_or_ror == 1'b1)
                      ? src1[31:0]
                      : {32{sign_bit}};

// Define the 5-stage funnel-shift network
// Stage 5 is altered to insert implicit AND for XBFU operation
//
assign stage_1 = (shmt[0] == 1'b1) ? stage_0[64:1]  : stage_0[63:0];
assign stage_2 = (shmt[1] == 1'b1) ? stage_1[63:2]  : stage_1[61:0];
assign stage_3 = (shmt[2] == 1'b1) ? stage_2[61:4]  : stage_2[57:0];
assign stage_4 = (shmt[3] == 1'b1) ? stage_3[57:8]  : stage_3[49:0];
assign stage_5 = (stage_4[49:16] & masked_sh16) | (stage_4[33:0] & masked_sh0);

// Result is derived from stage_5 unless there is a zero shift, in which
// stage_5[32:1] will be either 32'd0 (for left shift) or src1[31:0].
// In such cases we must OR-in the original source operand when there is
// a left shift of distance zero.
//
assign result     = stage_5[32:1] | ({32{zero_shift}} & src1 & xbfu_mask [32:1]);

assign negative   = result[31];

// Carry out is derived from the msb+1 of the result in stage_5 if
// shifting left when shift distance is non-zero, or from lsb-1 of
// stage_5 if shifting right. The result in stage_5 occupies bit
// positions stage_5[32:1], hence the carry may be in positions 33 or 0.
//
assign carry_out  = (stage_5[33] &  left & (~zero_shift))
                  | (stage_5[0]  & (~left));

// Zero is defined in terms of stage_5 and src1 in order to avoid
// the final OR-logic in the computation of the final result from
// influencing timing of the Z flag
//
assign zero       = (~zero_shift) & (stage_5[32:1] == 32'd0)
                  |  zero_shift   & ((src1[31:0] & xbfu_mask [32:1]) == 32'd0);

// Overflow will be ignored by instructions that do not update V flag
//
assign overflow = (result[31] != src1[31]);

endmodule
