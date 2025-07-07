/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */



/*
 *************************************** MODULE INFO ***************************************************
 * Data bits: 64
 * Address bits: 0 (Address protection is enabled)
 * Fault coverage: The code can detect up to two bit errors and simultaneously corrects single bit errors.
 * All-zero and all-one protection is enabled. These faults will be detected as two-bit errors.
 * Required minimum ECC bits: 8 
 ********************************************************************************************************
 */



`define    VM_ECC_2ND_TOTAL_WIDTH    72
`define    VM_ECC_2ND_TOTAL_RANGE    71:0
`define    VM_ECC_2ND_CHKBIT_WIDTH   8
`define    VM_ECC_2ND_CHKBIT_RANGE   71:64

// This function returns the check bits
function automatic [7:0] vm_ecc_2nd_enc;
    input [63:0] data_in;
    // The word which ECC will be calculated
    reg [63:0] word_in;
    // Hold generated EDC bits
    reg [6:0] edc_tmp;
    // Overall parity for Hammming SECDED code
    reg overall_parity;
    reg [7 :0] ecc;
begin

    // Word to encode
    word_in = data_in;

    // To generate EDC bits, pick particular word bits by using masks, then XOR them
    edc_tmp[0] = ^(word_in & 64'b1010101101010101010101010101010101010110101010101010110101011011);
    edc_tmp[1] = ^(word_in & 64'b1100110110011001100110011001100110011011001100110011011001101101);
    edc_tmp[2] = ^(word_in & 64'b1111000111100001111000011110000111100011110000111100011110001110);
    edc_tmp[3] = ^(word_in & 64'b0000000111111110000000011111111000000011111111000000011111110000);
    edc_tmp[4] = ^(word_in & 64'b0000000111111111111111100000000000000011111111111111100000000000);
    edc_tmp[5] = ^(word_in & 64'b0000000111111111111111111111111111111100000000000000000000000000);
    edc_tmp[6] = ^(word_in & 64'b1111111000000000000000000000000000000000000000000000000000000000);

    // Overall parity is the XOR of encoded word and generated EDC bits
    overall_parity = (^word_in) ^ (^edc_tmp);

    // Invert last two parity bits if all-zero and all-one protection is enabled
    ecc = {overall_parity, ~edc_tmp[6 ], ~edc_tmp[5 ], edc_tmp[4 :0]};
    vm_ecc_2nd_enc = ecc;
end
endfunction


// This function returns the {overall_parity, syndrome}
function automatic [7:0] vm_ecc_2nd_dec_a;
    input [63:0] data_in;
    input [7 :0] ecc_in;
    // XOR of received and re-calculated EDC
    reg  [6:0] syndrome;
    reg overall_parity;
    // The word which ECC will be calculated
    reg  [63:0] word_in;
    // Decoder re-calculates the EDC from the received data
    reg  [6:0] calc_edc;
    // Temporary signal to hold received EDC
    reg  [6:0] edc_in_tmp;

begin
    // The word which EDC will be calculated again
    word_in = data_in;

    // Since the encoder inverts last two EDC bits before storing them, invert them back before comparing with generated EDC
    edc_in_tmp = {~ecc_in[6 ], ~ecc_in[5 ], ecc_in[4 :0]};

    // Pick particular word bits by using masks, then XOR them
    // Masks to select bits to be XORed
    calc_edc[0] = ^(word_in & 64'b1010101101010101010101010101010101010110101010101010110101011011);
    calc_edc[1] = ^(word_in & 64'b1100110110011001100110011001100110011011001100110011011001101101);
    calc_edc[2] = ^(word_in & 64'b1111000111100001111000011110000111100011110000111100011110001110);
    calc_edc[3] = ^(word_in & 64'b0000000111111110000000011111111000000011111111000000011111110000);
    calc_edc[4] = ^(word_in & 64'b0000000111111111111111100000000000000011111111111111100000000000);
    calc_edc[5] = ^(word_in & 64'b0000000111111111111111111111111111111100000000000000000000000000);
    calc_edc[6] = ^(word_in & 64'b1111111000000000000000000000000000000000000000000000000000000000);

    // Calculate syndrome by comparing received and calculated EDC bits
    syndrome = edc_in_tmp ^ calc_edc;

    // Overall parity check should be zero for no error and even number of bit error cases
    overall_parity = ^{word_in, ecc_in};
    vm_ecc_2nd_dec_a = {overall_parity, syndrome};
end
endfunction


// This function returns the {unknown_err, double_err, single_err};
function automatic [2:0] vm_ecc_2nd_dec_b;
    input enable;
    input [6:0] syndrome;
    input overall_parity;
    // We pass this to simplify some of the expressions in error signal generation logic
    input overall_parity_and_enable;
    reg single_err;
    reg double_err;
    reg unknown_err;

    // OR ed version of the syndrome
    reg  is_syndrome_non_zero;
    // Does the syndrome is used by the coding scheme?
    reg  is_unused_syndrome;

begin
    // Check if the syndrome is non zero
    is_syndrome_non_zero = |syndrome;


// Checks if the syndrome is unused syndrome
    is_unused_syndrome = (syndrome == 72) | (syndrome == 73) | (syndrome == 74) | (syndrome == 75) | (syndrome == 76) | (syndrome == 77) | 
    (syndrome == 78) | (syndrome == 79) | (syndrome == 80) | (syndrome == 81) | (syndrome == 82) | (syndrome == 83) | 
    (syndrome == 84) | (syndrome == 85) | (syndrome == 86) | (syndrome == 87) | (syndrome == 88) | (syndrome == 89) | 
    (syndrome == 90) | (syndrome == 91) | (syndrome == 92) | (syndrome == 93) | (syndrome == 94) | (syndrome == 95) | 
    (syndrome == 96) | (syndrome == 97) | (syndrome == 98) | (syndrome == 99) | (syndrome == 100) | (syndrome == 101) | 
    (syndrome == 102) | (syndrome == 103) | (syndrome == 104) | (syndrome == 105) | (syndrome == 106) | (syndrome == 107) | 
    (syndrome == 108) | (syndrome == 109) | (syndrome == 110) | (syndrome == 111) | (syndrome == 112) | (syndrome == 113) | 
    (syndrome == 114) | (syndrome == 115) | (syndrome == 116) | (syndrome == 117) | (syndrome == 118) | (syndrome == 119) | 
    (syndrome == 120) | (syndrome == 121) | (syndrome == 122) | (syndrome == 123) | (syndrome == 124) | (syndrome == 125) | 
    (syndrome == 126) | (syndrome == 127);

    // If overall parity check fails and syndrome is used, then we flag a single bit error
    // Note that this also covers the case when syndrome is zero, and the overall parity fails
    single_err = ~is_unused_syndrome & overall_parity_and_enable;

    // Assert double error if syndrome is non-zero and overall parity overall parity does not match
    double_err = is_syndrome_non_zero & ~overall_parity & enable;

    // If the syndrome is not used and overally parity fails, this is a detected multi odd bit error
    unknown_err = is_unused_syndrome & overall_parity_and_enable;

    vm_ecc_2nd_dec_b = {unknown_err, double_err, single_err};
end
endfunction


// This function returns the corrected data;
function automatic [63:0] vm_ecc_2nd_dec_c;
    input overall_parity_and_enable;
    input [6:0] syndrome;
    input [63:0] data_in;
    reg [63:0] data_out;
begin

    // Map error syndrome to faulty data bit location and correct it

    data_out = data_in;

    // Do correction only if it is a single bit error and module is enabled
    if (overall_parity_and_enable) begin
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
        (15) :        data_out[10] = ~data_in[10];
        (17) :        data_out[11] = ~data_in[11];
        (18) :        data_out[12] = ~data_in[12];
        (19) :        data_out[13] = ~data_in[13];
        (20) :        data_out[14] = ~data_in[14];
        (21) :        data_out[15] = ~data_in[15];
        (22) :        data_out[16] = ~data_in[16];
        (23) :        data_out[17] = ~data_in[17];
        (24) :        data_out[18] = ~data_in[18];
        (25) :        data_out[19] = ~data_in[19];
        (26) :        data_out[20] = ~data_in[20];
        (27) :        data_out[21] = ~data_in[21];
        (28) :        data_out[22] = ~data_in[22];
        (29) :        data_out[23] = ~data_in[23];
        (30) :        data_out[24] = ~data_in[24];
        (31) :        data_out[25] = ~data_in[25];
        (33) :        data_out[26] = ~data_in[26];
        (34) :        data_out[27] = ~data_in[27];
        (35) :        data_out[28] = ~data_in[28];
        (36) :        data_out[29] = ~data_in[29];
        (37) :        data_out[30] = ~data_in[30];
        (38) :        data_out[31] = ~data_in[31];
        (39) :        data_out[32] = ~data_in[32];
        (40) :        data_out[33] = ~data_in[33];
        (41) :        data_out[34] = ~data_in[34];
        (42) :        data_out[35] = ~data_in[35];
        (43) :        data_out[36] = ~data_in[36];
        (44) :        data_out[37] = ~data_in[37];
        (45) :        data_out[38] = ~data_in[38];
        (46) :        data_out[39] = ~data_in[39];
        (47) :        data_out[40] = ~data_in[40];
        (48) :        data_out[41] = ~data_in[41];
        (49) :        data_out[42] = ~data_in[42];
        (50) :        data_out[43] = ~data_in[43];
        (51) :        data_out[44] = ~data_in[44];
        (52) :        data_out[45] = ~data_in[45];
        (53) :        data_out[46] = ~data_in[46];
        (54) :        data_out[47] = ~data_in[47];
        (55) :        data_out[48] = ~data_in[48];
        (56) :        data_out[49] = ~data_in[49];
        (57) :        data_out[50] = ~data_in[50];
        (58) :        data_out[51] = ~data_in[51];
        (59) :        data_out[52] = ~data_in[52];
        (60) :        data_out[53] = ~data_in[53];
        (61) :        data_out[54] = ~data_in[54];
        (62) :        data_out[55] = ~data_in[55];
        (63) :        data_out[56] = ~data_in[56];
        (65) :        data_out[57] = ~data_in[57];
        (66) :        data_out[58] = ~data_in[58];
        (67) :        data_out[59] = ~data_in[59];
        (68) :        data_out[60] = ~data_in[60];
        (69) :        data_out[61] = ~data_in[61];
        (70) :        data_out[62] = ~data_in[62];
        (71) :        data_out[63] = ~data_in[63];
        endcase
    end
    vm_ecc_2nd_dec_c = data_out;
end
endfunction


// This function returns the corrected ecc code;
function automatic [7 :0] vm_ecc_2nd_dec_d;
    input overall_parity_and_enable;
    input [6:0] syndrome;
    input [7 :0] ecc_in;
    reg [7 :0] ecc_out;
begin
    // Map error syndrome to faulty data bit location and correct it

    ecc_out  = ecc_in;
    
    // Do correction only if it is a single bit error and module is enabled
    if (overall_parity_and_enable) begin
        case(syndrome)
        (1 ) :        ecc_out[0] = ~ecc_in[0];
        (2 ) :        ecc_out[1] = ~ecc_in[1];
        (4 ) :        ecc_out[2] = ~ecc_in[2];
        (8 ) :        ecc_out[3] = ~ecc_in[3];
        (16) :        ecc_out[4] = ~ecc_in[4];
        (32) :        ecc_out[5] = ~ecc_in[5];
        (64) :        ecc_out[6] = ~ecc_in[6];
        (0 ) :        ecc_out[7] = ~ecc_in[7];
        endcase
    end
    vm_ecc_2nd_dec_d = ecc_out;
end
endfunction

