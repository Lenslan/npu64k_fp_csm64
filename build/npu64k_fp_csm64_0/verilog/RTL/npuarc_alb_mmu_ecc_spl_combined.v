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
//                     
//   ALB_MMU_ECC_SPL_COMBINED                  
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
//   vpp +q +o alb_mmu_ecc_spl_combined.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_mmu_ecc_spl_combined #(
  parameter D_SIZE = 32
                                 )( 
  ////////// General input signals ///////////////////////////////////////////
  //
  input [39:0]           data_in,            // 32-bit data in
  input [`npuarc_ECC_CODE_MSB:0]ecc_code_in,        // ECC code in
  input                  ecc_dmp_disable,    // ECC disable

  ///////// Global/System state /////////////////////////////////////////////
  //
  // output              ecc_error,         // indicates ECC error detected
  output [`npuarc_SYNDROME_MSB:0] syndrome,
  output                 sb_error,          // single bit error detected
  output                 db_error,          // double bit error detected
  output reg [57:0]      data_out           // corrected data
);

wire [39:0]             word_in;
wire [`npuarc_SYNDROME_MSB:0]  edc_in_tmp;
wire [`npuarc_SYNDROME_MSB:0]  calc_edc;
wire                    overall_parity;
wire                    is_syndrome_non_zero;
wire                    is_unused_syndrome;

assign word_in = data_in;

// Since the encoder inverts last two EDC bits before storing them, invert them back before comparing with generated EDC
assign edc_in_tmp = {~ecc_code_in[5 ], ~ecc_code_in[4 ], ecc_code_in[3 :0]};

// Pick particular word bits by using masks, then XOR them
// Masks to select bits to be XORed
assign calc_edc[0] = ^(word_in & 40'b1010101010101011010101010101010101011011);
assign calc_edc[1] = ^(word_in & 40'b1100110011001101100110011001101001101101);
assign calc_edc[2] = ^(word_in & 40'b1111000011110001111000011110001110001110);
assign calc_edc[3] = ^(word_in & 40'b1111111100000001111111100000001111110000);
assign calc_edc[4] = ^(word_in & 40'b0000000000000001111111111111110000000000);
assign calc_edc[5] = ^(word_in & 40'b1111111111111110000000000000000000000000);

// Calculate syndrome by comparing received and calculated EDC bits
assign syndrome = edc_in_tmp ^ calc_edc;

// Overall parity check should be zero for no error and even number of bit error cases
assign overall_parity = ^{word_in, ecc_code_in};


// Check if the syndrome is non zero
assign is_syndrome_non_zero = |syndrome;


// Checks if the syndrome is unused syndrome
assign is_unused_syndrome = (syndrome == 15) | (syndrome == 48) | (syndrome == 49) | (syndrome == 50) | (syndrome == 51) | (syndrome == 52) | 
                            (syndrome == 53) | (syndrome == 54) | (syndrome == 55) | (syndrome == 56) | (syndrome == 57) | (syndrome == 58) | 
                            (syndrome == 59) | (syndrome == 60) | (syndrome == 61) | (syndrome == 62) | (syndrome == 63) | (&data_in[D_SIZE-1:0] & (&ecc_code_in));


// If overall parity check fails and syndrome is used, then we flag a single bit error
// Note that this also covers the case when syndrome is zero, and the overall parity fails
assign sb_error = ~is_unused_syndrome & overall_parity & (~ecc_dmp_disable);

// Assert double error if syndrome is non-zero and overall parity overall parity does not match
assign db_error = (is_syndrome_non_zero & ~overall_parity & (~ecc_dmp_disable))
                | (overall_parity & is_unused_syndrome & (~ecc_dmp_disable));


always @*
begin: data_out_PROC
    // Map error syndrome to faulty data bit location and correct it

    data_out = data_in;

    // Do correction only if it is a single bit error and module is enabled
    if (sb_error) begin
        case(syndrome)
        (3 ) :        data_out[0] = ~data_in[0];
        (5 ) :        data_out[1] = ~data_in[1];
        (6 ) :        data_out[2] = ~data_in[2];
        (7 ) :        data_out[3] = ~data_in[3];
        (9 ) :        data_out[4] = ~data_in[4];
        (10) :        data_out[5] = ~data_in[5];
        (11) :        data_out[6] = ~data_in[6];
        (12) :        data_out[7] = ~data_in[7];
        (13) :        data_out[8] = ~data_in[8];
        (14) :        data_out[9] = ~data_in[9];
        (17) :        data_out[10] = ~data_in[10];
        (18) :        data_out[11] = ~data_in[11];
        (19) :        data_out[12] = ~data_in[12];
        (20) :        data_out[13] = ~data_in[13];
        (21) :        data_out[14] = ~data_in[14];
        (22) :        data_out[15] = ~data_in[15];
        (23) :        data_out[16] = ~data_in[16];
        (24) :        data_out[17] = ~data_in[17];
        (25) :        data_out[18] = ~data_in[18];
        (26) :        data_out[19] = ~data_in[19];
        (27) :        data_out[20] = ~data_in[20];
        (28) :        data_out[21] = ~data_in[21];
        (29) :        data_out[22] = ~data_in[22];
        (30) :        data_out[23] = ~data_in[23];
        (31) :        data_out[24] = ~data_in[24];
        (33) :        data_out[25] = ~data_in[25];
        (34) :        data_out[26] = ~data_in[26];
        (35) :        data_out[27] = ~data_in[27];
        (36) :        data_out[28] = ~data_in[28];
        (37) :        data_out[29] = ~data_in[29];
        (38) :        data_out[30] = ~data_in[30];
        (39) :        data_out[31] = ~data_in[31];
        (40) :        data_out[32] = ~data_in[32];
        (41) :        data_out[33] = ~data_in[33];
        (42) :        data_out[34] = ~data_in[34];
        (43) :        data_out[35] = ~data_in[35];
        (44) :        data_out[36] = ~data_in[36];
        (45) :        data_out[37] = ~data_in[37];
        (46) :        data_out[38] = ~data_in[38];
        (47) :        data_out[39] = ~data_in[39];
        endcase
    end
end
  
endmodule // alb_dmp_ecc_detection
