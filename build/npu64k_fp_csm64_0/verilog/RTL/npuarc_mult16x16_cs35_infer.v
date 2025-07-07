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
// Certain materials incorporated herein are copyright (C) 2010 - 2013, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
// #     #  #######  ######   #######  #######
// #  #  #     #     #     #  #        #
// #  #  #     #     #     #  #        #
// #  #  #     #     ######   #####    #####
// #  #  #     #     #   #    #        #
// #  #  #     #     #    #   #        #
//  ## ##      #     #     #  #######  #######  #####
//
//       #     ###   #     #    #     ###
//      ##    #   #   #   #    ##    #   #
//     # #    #        # #    # #    #
//       #    ####      #       #    ####
//       #    #   #    # #      #    #   #
//       #    #   #   #   #     #    #   #
//     #####   ###   #     #  #####   ###
//
// ===========================================================================
//
// Description:
//
//  This version of the wtree_16x16 module infers a 17x17 multiplier, and
//  extends the inputs with sign or zero bits depending on whether each
//  operand is signed or unsigned. The least-significant 32 bits of the
//  product are returned.
//
//  The following instructions use this module:
//    MPY, MPYU, MPYHI, MPYHIU, MPYW, MPYWU
//
//  This file is formatted with 2-characters-per-tab indentation
//
// ===========================================================================

// Set simulation timescale
//
`include "const.def"

module npuarc_mult16x16_cs35_infer (
  input      [15:0]     dataa,        // multiplicand
  input      [15:0]     datab,        // multiplier
  input                 signed_op_a,  // 0 -> unsigned, 1 -> signed
  input                 signed_op_b,  // 0 -> unsigned, 1 -> signed

  output reg [34:0]     res_sum,      // final result
  output reg [34:0]     res_carry     // all zeros from inferred mpy
);

reg           [16:0]           src_1;
reg           [16:0]           src_2;
reg           [33:0]           product;

always @(*)
begin : multiply_PROC

  // Sign-extend or zero-extend each 16-bit operand to 17 bits
  // to allow signed multiplication to be used in all cases.
  //
  src_1       = {(signed_op_a & dataa[15]), dataa};
  src_2       = {(signed_op_b & datab[15]), datab};

   // leda FM_1_2 off
   // LMD: Usage of complex arithmetic operations that include 
   //      multiplication, division, remainder or modulus is 
   //      not recommended (important memory usage)
   // LJ:  This is inferred signed multiplier behavior code.
   //      This is waived for the following
   //      1. FM_1_2 Rule is tool issue & not a design issue 
   //      2. Coded to intend concise & simple representation
// spyglass disable_block W164b
// spyglass disable_block W164a
// SMD: unequal widths on LHS and RHS of assign statement
// SJ:  intentional
   product = $signed(src_1) * $signed(src_2);
   // leda FM_1_2 on

  res_sum   = {product[33], product[33:0]};
// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0
// LJ:  Behavioral code is a simple representation only
  res_carry = {35{1'b0}};
// leda NTL_CON16 on

end  // block : multiply_PROC
// spyglass enable_block W164a
// spyglass enable_block W164b
endmodule // module : mult16x16_cs35_infer
