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
//   ALB_DMP_ECC_COMBINED                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the single bit and double bit ecc error detection.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_ecc_detection.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_ecc_combined_a (

  ////////// General input signals ///////////////////////////////////////////
  //
  input [31:0]           data_in,            // 32-bit data in
  input [`npuarc_ECC_CODE_MSB:0]ecc_code_in,        // ECC code in

  ///////// Global/System state /////////////////////////////////////////////
  //
  // output              ecc_error,         // indicates ECC error detected
  output                 i_parity,          // single bit error detected
  output [`npuarc_SYNDROME_MSB:0]syndrome          // double bit error detected
);

wire [31:0]             word_in;
wire [`npuarc_SYNDROME_MSB:0]  edc_in_tmp;
wire [`npuarc_SYNDROME_MSB:0]  calc_edc;

assign word_in = data_in;

// Since the encoder inverts last two EDC bits before storing them, invert them back before comparing with generated EDC
assign edc_in_tmp = {~ecc_code_in[5 ], ~ecc_code_in[4 ], ecc_code_in[3 :0]};

// Pick particular word bits by using masks, then XOR them
// Masks to select bits to be XORed
assign calc_edc[0] = ^(word_in & 32'b10101011010101010101010101011011);
assign calc_edc[1] = ^(word_in & 32'b11001101100110011001101001101101);
assign calc_edc[2] = ^(word_in & 32'b11110001111000011110001110001110);
assign calc_edc[3] = ^(word_in & 32'b00000001111111100000001111110000);
assign calc_edc[4] = ^(word_in & 32'b00000001111111111111110000000000);
assign calc_edc[5] = ^(word_in & 32'b11111110000000000000000000000000);

// Calculate syndrome by comparing received and calculated EDC bits
assign syndrome = edc_in_tmp ^ calc_edc;

// Overall parity check should be zero for no error and even number of bit error cases
assign i_parity = ^{word_in, ecc_code_in};

endmodule // alb_dmp_ecc_detection
