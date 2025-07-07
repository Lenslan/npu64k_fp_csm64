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

module npuarc_alb_dmp_ecc_combined_b #(
  parameter D_SIZE = 32
                             )(
  ////////// General input signals ///////////////////////////////////////////
  //
  input [31:0]           data_in,            // 32-bit data in
  input [`npuarc_ECC_CODE_MSB:0]ecc_code_in,        // ECC code in
  input                  i_parity,
  input [`npuarc_SYNDROME_MSB:0]syndrome,            // 32-bit data in
  input                  ecc_dmp_disable,    // ECC disable

  ///////// Global/System state /////////////////////////////////////////////
  //
  // output              ecc_error,         // indicates ECC error detected
  output                 sb_error,          // single bit error detected
  output                 db_error,          // double bit error detected
  output reg [31:0]      data_out           // corrected data
);



wire                    is_syndrome_non_zero;
wire                    is_unused_syndrome;
wire                    overall_parity;

// Overall parity check should be zero for no error and even number of bit error cases
assign overall_parity = i_parity;


// Check if the syndrome is non zero
assign is_syndrome_non_zero = |syndrome;


// Checks if the syndrome is unused syndrome
assign is_unused_syndrome = (syndrome[5] & (syndrome[4] | syndrome[3]))
                          | (~(|syndrome[5:4]) & (&syndrome[3:0]))
                          | (&data_in[D_SIZE-1:0] & (&ecc_code_in));

// If overall parity check fails and syndrome is used, then we flag a single bit error
// Note that this also covers the case when syndrome is zero, and the overall parity fails
assign sb_error = ~is_unused_syndrome & overall_parity & (~ecc_dmp_disable);

// Assert double error if syndrome is non-zero and overall parity overall parity does not match
assign db_error = (~ecc_dmp_disable)
                & (  (is_syndrome_non_zero & ~overall_parity) 
                   | (overall_parity & is_unused_syndrome));

always @*
begin: data_out_PROC
    // Map error syndrome to faulty data bit location and correct it

    data_out = data_in[31:0];

    // Do correction only if it is a single bit error and module is enabled
    if (sb_error) begin
        case(syndrome)
        6'd3  :        data_out[0] = ~data_in[0];
        6'd5  :        data_out[1] = ~data_in[1];
        6'd6  :        data_out[2] = ~data_in[2];
        6'd7  :        data_out[3] = ~data_in[3];
        6'd9  :        data_out[4] = ~data_in[4];
        6'd10 :        data_out[5] = ~data_in[5];
        6'd11 :        data_out[6] = ~data_in[6];
        6'd12 :        data_out[7] = ~data_in[7];
        6'd13 :        data_out[8] = ~data_in[8];
        6'd14 :        data_out[9] = ~data_in[9];
        6'd17 :        data_out[10] = ~data_in[10];
        6'd18 :        data_out[11] = ~data_in[11];
        6'd19 :        data_out[12] = ~data_in[12];
        6'd20 :        data_out[13] = ~data_in[13];
        6'd21 :        data_out[14] = ~data_in[14];
        6'd22 :        data_out[15] = ~data_in[15];
        6'd23 :        data_out[16] = ~data_in[16];
        6'd24 :        data_out[17] = ~data_in[17];
        6'd25 :        data_out[18] = ~data_in[18];
        6'd26 :        data_out[19] = ~data_in[19];
        6'd27 :        data_out[20] = ~data_in[20];
        6'd28 :        data_out[21] = ~data_in[21];
        6'd29 :        data_out[22] = ~data_in[22];
        6'd30 :        data_out[23] = ~data_in[23];
        6'd31 :        data_out[24] = ~data_in[24];
        6'd33 :        data_out[25] = ~data_in[25];
        6'd34 :        data_out[26] = ~data_in[26];
        6'd35 :        data_out[27] = ~data_in[27];
        6'd36 :        data_out[28] = ~data_in[28];
        6'd37 :        data_out[29] = ~data_in[29];
        6'd38 :        data_out[30] = ~data_in[30];
        6'd39 :        data_out[31] = ~data_in[31];
        endcase
    end
end

endmodule // alb_dmp_ecc_detection
