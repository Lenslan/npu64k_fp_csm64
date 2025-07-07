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
// ######   #     #  #######  #######         #     #  #     #  ###  #######  
// #     #   #   #      #     #               #     #  ##    #   #      #     
// #     #    # #       #     #               #     #  # #   #   #      #     
// ######      #        #     #####           #     #  #  #  #   #      #     
// #     #     #        #     #               #     #  #   # #   #      #     
// #     #     #        #     #               #     #  #    ##   #      #     
// ######      #        #     #######  #####   #####   #     #  ###     #     
//
// ===========================================================================
//
// Description:
//
// @f:byte_unit:
// @p
//  This module implements the byte-level operations required by various
//  instructions the ARCv2 ISA. These operations are optional, and are
//  enabled by the SWAP_OPTION and the SHIFT_ASSIST option as indicated below:
//
//  Swap operations included when SWAP_OPTION is enabled
//  --------------------------------------------------------------------------
//   SWAP          : swap lower and upper half words
//   SWAPL (LSL16) : swap half words and zero upper half word
//   SWAPH (LSR16) : swap half words and zero lower half word
//   SWAPE         : reverse bytes, to convert between little/big endian
//  --------------------------------------------------------------------------
//
//  Shift operations included when SWAP_OPTION and SHIFT_ASSIST are enabled
//  --------------------------------------------------------------------------
//   ASR16 : arithmetic shift right 16 bits
//   ASR8  : arithmetic shift right 8 bits
//   LSR8  : logical shift right 8 bits
//   LSL8  : logical shift left 8 bits
//   ROL8  : rotate left 8 bits
//   ROR8  : rotate right 8 bits
//  --------------------------------------------------------------------------
// @e
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_byte_unit (

  ////////// Control signals ///////////////////////////////////////////////
  //
  swap_op,            // ucode
  signed_op,          // ucode
  half_size,          // ucode
  byte_size,          // ucode
  left,               // ucode
  rotate,             // ucode

  ////////// Operand ///////////////////////////////////////////////////////
  //
  src,                // 32-bit source operand

  ////////// Result ouptut /////////////////////////////////////////////////
  //
  result              // 32-bit result
);


// =======================================================================
// @v:byte-ucode:Byte unit microcode settings:
// =======================================================================
//  The behavior of the byte_op unit is determined by 6 ucode bits,
//  detailed below. The setting of each microcode bit is determined by the
//  decoder task for each instruction, which is given in acode_tasks.v
//
// -----------------------------------------------------------------------
// \ _  Inst
//   \ _
//       \ _
//  ucode   \   ASR16 LSL16 LSR16 ASR8 LSR8  LSL8  ROL8  ROR8  SWAPE  SWAP
// ----------------------------------------------------------------------
//  swap_op       1    1      1     1    1     1     1     1     1     1
//  signed_op     1    0      0     1    0     0     0     0     0     0
//  half_size     1    1      1     0    0     0     0     0     0     1
//  byte_size     0    0      0     1    1     1     1     1     0     0
//  left          0    1      0     0    0     1     1     0     0     0
//  rotate        0    0      0     0    0     0     1     1     1     1
//  ----------------------------------------------------------------------
//
//  The mutual-exclusivity of the microcode bits is essential for the
//  correct operation of the byte_op unit, as they control the muxing of
//  values in the case statement which implements the muxing.
// =======================================================================
// @e

localparam ASR16_UCODE  = 6'b111000;
localparam LSL16_UCODE  = 6'b101010;
localparam LSR16_UCODE  = 6'b101000;
localparam ASR8_UCODE   = 6'b110100;
localparam LSR8_UCODE   = 6'b100100;
localparam LSL8_UCODE   = 6'b100110;
localparam ROL8_UCODE   = 6'b100111;
localparam ROR8_UCODE   = 6'b100101;
localparam SWAPE_UCODE  = 6'b100001;
localparam SWAP_UCODE   = 6'b101001;

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Input declarations                                                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

input                       swap_op;        // enable byte-level operations
input                       signed_op;      // ucode
input                       half_size;      // ucode
input                       byte_size;      // ucode
input                       left;           // ucode
input                       rotate;         // ucode
input   [`npuarc_DATA_RANGE]       src;            // 32-bit operand


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Output declarations                                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

output  [`npuarc_DATA_RANGE]       result;         // byte operation result

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous process to implement the byte operations                  //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg     [`npuarc_DATA_RANGE]       result;
reg     [5:0]               opcode;
reg     [7:0]               byte0;
reg     [7:0]               byte1;
reg     [7:0]               byte2;
reg     [7:0]               byte3;
//reg     [7:0]               zero8;
reg     [7:0]               sign8;

always @*
begin : byte_op_PROC

  opcode = {swap_op, signed_op, half_size, byte_size, left, rotate};

  byte0  = src[7:0];
  byte1  = src[15:8];
  byte2  = src[23:16];
  byte3  = src[31:24];
//  zero8  = 8'd0;
  sign8  = {8{src[31]}};

  result = `npuarc_DATA_SIZE'd0;

  case ( opcode )
    LSL16_UCODE : result = { byte1, byte0, 8'd0, 8'd0 };
    LSR16_UCODE : result = { 8'd0, 8'd0, byte3, byte2 };
    SWAPE_UCODE : result = { byte0, byte1, byte2, byte3 };
    SWAP_UCODE  : result = { byte1, byte0, byte3, byte2 };
    ASR16_UCODE : result = { sign8, sign8, byte3, byte2 };
    ASR8_UCODE  : result = { sign8, byte3, byte2, byte1 };
    LSR8_UCODE  : result = { 8'd0, byte3, byte2, byte1 };
    LSL8_UCODE  : result = { byte2, byte1, byte0, 8'd0 };
    ROL8_UCODE  : result = { byte2, byte1, byte0, byte3 };
    ROR8_UCODE  : result = { byte0, byte3, byte2, byte1 };
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default: ;
// spyglass enable_block W193
  endcase
end

endmodule
