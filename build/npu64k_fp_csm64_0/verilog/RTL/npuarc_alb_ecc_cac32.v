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
//  ECC "Check & Correct" module for ARC HS
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

module npuarc_alb_ecc_cac32 #(
   parameter D_SIZE = 32)
(
// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems

  input                  clk,
  input                  rst_a,

  ////////// Input signals /////////////////////////////////////////////////////
  //
  input [31:0]           data_in,            // 32-bit data in
  input [`npuarc_ECC_CODE_MSB:0]            ecc_code_in,        // ECC code in
  
  input                  ecc_chk_en,         // enable ECC checking and correction

  ///////// Output Signals /////////////////////////////////////////////////////
  //
  output wire            ecc_error,         // indicates ECC error detected
  output wire            sb_error,          // single bit error detected
  output wire            db_error,          // double bit error detected
  output wire  [`npuarc_SYNDROME_MSB:0]  syndrome,
  output wire  [31:0]    data_out           // corrected data out   
  
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

  reg  [31:0]           i_data;              // corrected data
  localparam [31:0] introduce_error_for_testing = 0;  // For testing single-bit correction. 
  wire [31:0]             word_in;
  wire                    overall_parity;
  wire                    is_syndrome_non_zero;
  wire [`npuarc_ECC_CODE_MSB:0]  new_ecc;
  wire [`npuarc_SYNDROME_MSB:0]  new_edc;
  wire [`npuarc_SYNDROME_MSB:0]  old_edc;


  reg  [`npuarc_SYNDROME_MSB:0]  syndrome_r;
  //Register the syndrome
  always @(posedge clk or posedge rst_a)
  begin: syndrome_reg_PROC
    if (rst_a == 1'b1) begin
      syndrome_r <= {`npuarc_SYNDROME_MSB+1{1'b0}}; 
    end
    else begin
    syndrome_r <= syndrome;
    end
  end

  localparam show_fix = 0;
  //`define ecc_correct(synd,bit) synd: begin i_data[bit] = ~word_in[bit]; if (show_fix) $display("fix bit %2d",bit); end
  `define ecc_correct(synd,bit) synd: i_data[bit] = ~word_in[bit];

  assign word_in  = data_in ^ introduce_error_for_testing;
  assign new_ecc = ecc_gen32(word_in);

  assign new_edc = new_ecc    [`npuarc_SYNDROME_MSB:0];
  assign old_edc = ecc_code_in[`npuarc_SYNDROME_MSB:0];
  
  // Calculate syndrome by comparing received and calculated EDC, and
  // ignoring the parity bit.
  assign syndrome   = new_edc ^ old_edc;

  // Overall parity check should be zero for no error or cases with even # of bit errors.
  assign overall_parity = ^{word_in, ecc_code_in};

  // Check if the syndrome is non zero
  assign is_syndrome_non_zero = |syndrome;

  wire                    is_unused_syndrome;

  // Checks if the syndrome is unused syndrome
  assign is_unused_syndrome = (syndrome[5] & (syndrome[4] | syndrome[3]))
                          | (~(|syndrome[5:4]) & (&syndrome[3:0]))
                          | (&word_in[D_SIZE-1:0] & (&ecc_code_in));

  // If overall parity check fails and syndrome is used, then we flag a single bit error
  // Note that this also covers the case when syndrome is zero, 
  // and the overall parity fails.
  assign sb_error = ~is_unused_syndrome & overall_parity & ecc_chk_en;

  // Assert double error if syndrome is non-zero and overall parity overall parity does not match
  assign db_error = ecc_chk_en & ((is_syndrome_non_zero & ~overall_parity)
                | (overall_parity & is_unused_syndrome));

  assign ecc_error = (sb_error | db_error);

  always @*
  begin: data_out_PROC
    // Map error syndrome to faulty data bit location and correct it

    i_data = word_in;

    case(syndrome_r)
      `ecc_correct(6'd3  ,0)
      `ecc_correct(6'd5  ,1)
      `ecc_correct(6'd6  ,2)
      `ecc_correct(6'd7  ,3)
      `ecc_correct(6'd9  ,4)
      `ecc_correct(6'd10 ,5)
      `ecc_correct(6'd11 ,6)
      `ecc_correct(6'd12 ,7)
      `ecc_correct(6'd13 ,8)
      `ecc_correct(6'd14 ,9)
      `ecc_correct(6'd17 ,10)
      `ecc_correct(6'd18 ,11)
      `ecc_correct(6'd19 ,12)
      `ecc_correct(6'd20 ,13)
      `ecc_correct(6'd21 ,14)
      `ecc_correct(6'd22 ,15)
      `ecc_correct(6'd23 ,16)
      `ecc_correct(6'd24 ,17)
      `ecc_correct(6'd25 ,18)
      `ecc_correct(6'd26 ,19)
      `ecc_correct(6'd27 ,20)
      `ecc_correct(6'd28 ,21)
      `ecc_correct(6'd29 ,22)
      `ecc_correct(6'd30 ,23)
      `ecc_correct(6'd31 ,24)
      `ecc_correct(6'd33 ,25)
      `ecc_correct(6'd34 ,26)
      `ecc_correct(6'd35 ,27)
      `ecc_correct(6'd36 ,28)
      `ecc_correct(6'd37 ,29)
      `ecc_correct(6'd38 ,30)
      `ecc_correct(6'd39 ,31)
      endcase
end
  
`undef ecc_correct

// provided the corrected data out
assign data_out  = ({(32){sb_error}} & i_data) | ({(32){~sb_error}} & word_in);
// spyglass enable_block W193
endmodule 
