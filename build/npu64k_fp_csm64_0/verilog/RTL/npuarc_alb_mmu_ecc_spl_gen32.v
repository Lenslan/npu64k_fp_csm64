// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2017 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//
// ===========================================================================
//
// Description:
//  ECC code generator module for ARC HS
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o alb_mmu_ecc_spl_gen32.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_mmu_ecc_spl_gen32 
  (
  input       [39:0]           data_in,
  output wire [`npuarc_ECC_CODE_MSB:0]ecc_code   // ECC generated code out
  );


////////////////////////////////////////////////////////////////////////////////
// ECC Code Logic
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
// Generate ECC code     
// 
wire [39:0] word_in;
wire [5:0]  edc_tmp;
wire        overall_parity;

// Word to encode
assign word_in = data_in;

// To generate EDC bits, pick particular word bits by using masks, then XOR them
assign edc_tmp[0] = ^(word_in & 40'b1010101010101011010101010101010101011011);
assign edc_tmp[1] = ^(word_in & 40'b1100110011001101100110011001101001101101);
assign edc_tmp[2] = ^(word_in & 40'b1111000011110001111000011110001110001110);
assign edc_tmp[3] = ^(word_in & 40'b1111111100000001111111100000001111110000);
assign edc_tmp[4] = ^(word_in & 40'b0000000000000001111111111111110000000000);
assign edc_tmp[5] = ^(word_in & 40'b1111111111111110000000000000000000000000);

// Overall parity is the XOR of encoded word and generated EDC bits
assign overall_parity = (^word_in) ^ (^edc_tmp);

// Invert last two parity bits if all-zero and all-one protection is enabled
assign ecc_code = {overall_parity, ~edc_tmp[5 ], ~edc_tmp[4 ], edc_tmp[3 :0]};
  
  
endmodule 
