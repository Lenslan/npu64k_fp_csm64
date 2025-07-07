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
// ===========================================================================
//
// Description:
//  ECC code generator module for ARC HS
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o halt.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_ecc_gen32 
  (
  input       [31:0]        data,     // 32-bit data in

  output wire [6:0]        ecc_code  // ECC generated code out
  );



// Some day we can convert this to a package and use import to access these functions.
// package alb_ecc_funcs;

function automatic parity_gen32(
  input [31:0]            data    // 32-bit data in
  );
  begin
  // Generate parity for the 32bit data word
  parity_gen32 = ^data;  // xor all the bits
  end
  endfunction

function automatic parity_gen16(
  input [15:0]            data    // 16-bit data in
  );
  begin
  // Generate parity for the 16bit data word
  //
  parity_gen16  = ^data;  // xor all the bits
  end
  endfunction

function automatic [6:0] ecc_gen32 (
  input       [31:0]        data     // 32-bit data in
  );
  begin : ecc_gen32_FUNC

  ////////////////////////////////////////////////////////////////////////////////
  // ECC Code Logic
  ////////////////////////////////////////////////////////////////////////////////


  ////////////////////////////////////////////////////////////////////////////////
  // Generate ECC code
  //
    reg [5:0]  edc_tmp;
    reg        overall_parity;

    // To generate EDC bits, pick particular word bits by using masks, then XOR them
    edc_tmp[0] = ^(data & 32'b10101011010101010101010101011011);
    edc_tmp[1] = ^(data & 32'b11001101100110011001101001101101);
    edc_tmp[2] = ^(data & 32'b11110001111000011110001110001110);
    edc_tmp[3] = ^(data & 32'b00000001111111100000001111110000);
    edc_tmp[4] = ^(data & 32'b00000001111111111111110000000000);
    edc_tmp[5] = ^(data & 32'b11111110000000000000000000000000);

    // Overall parity is the XOR of encoded word and generated EDC bits
    overall_parity = ^{data,edc_tmp};

    // Invert last two parity bits if all-zero and all-one protection is enabled
    ecc_gen32 = {overall_parity, ~edc_tmp[5 ], ~edc_tmp[4 ], edc_tmp[3 :0]};

   end
   endfunction




// endpackage
  assign ecc_code = ecc_gen32(data);
endmodule 
