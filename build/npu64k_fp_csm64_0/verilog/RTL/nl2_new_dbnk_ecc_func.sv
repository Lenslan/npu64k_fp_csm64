/*
 * Copyright (C) 2016-2017 Synopsys, Inc. All rights reserved.
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
 * Data bits: 128
 * Address bits: 0 (Address protection is enabled)
 * Fault coverage: The code can detect up to two bit errors and simultaneously corrects single bit errors.
 * All-zero and all-one protection is enabled. These faults will be detected as two-bit errors.
 * Required minimum ECC bits: 9 
 ********************************************************************************************************
 */



`define    NEW_DBNK_ECC_TOTAL_WIDTH    137
`define    NEW_DBNK_ECC_TOTAL_RANGE    136:0
`define    NEW_DBNK_ECC_CHKBIT_WIDTH   9
`define    NEW_DBNK_ECC_CHKBIT_RANGE   136:128

// This function returns the check bits
function automatic [8:0] new_dbnk_ecc_enc;
    input [127:0] data_in;
    // The word which ECC will be calculated
    reg [127:0] word_in;
    // Hold generated EDC bits
    reg [7:0] edc_tmp;
    // Overall parity for Hammming SECDED code
    reg overall_parity;
    reg [8 :0] ecc;
begin

    // Word to encode
    word_in = data_in;

    // To generate EDC bits, pick particular word bits by using masks, then XOR them
    edc_tmp[0] = ^(word_in & 128'b10101010110101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010110101010101010110101011011);
    edc_tmp[1] = ^(word_in & 128'b00110011011001100110011001100110011001100110011001100110011001100110011010011001100110011001100110011011001100110011011001101101);
    edc_tmp[2] = ^(word_in & 128'b00111100011110000111100001111000011110000111100001111000011110000111100011100001111000011110000111100011110000111100011110001110);
    edc_tmp[3] = ^(word_in & 128'b11000000011111111000000001111111100000000111111110000000011111111000000011111110000000011111111000000011111111000000011111110000);
    edc_tmp[4] = ^(word_in & 128'b00000000011111111111111110000000000000000111111111111111100000000000000011111111111111100000000000000011111111111111100000000000);
    edc_tmp[5] = ^(word_in & 128'b00000000011111111111111111111111111111111000000000000000000000000000000011111111111111111111111111111100000000000000000000000000);
    edc_tmp[6] = ^(word_in & 128'b00000000011111111111111111111111111111111111111111111111111111111111111100000000000000000000000000000000000000000000000000000000);
    edc_tmp[7] = ^(word_in & 128'b11111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);

    // Overall parity is the XOR of encoded word and generated EDC bits
    overall_parity = (^word_in) ^ (^edc_tmp);

    // Invert last two parity bits if all-zero and all-one protection is enabled
    ecc = {overall_parity, ~edc_tmp[7 ], ~edc_tmp[6 ], edc_tmp[5 :0]};
    new_dbnk_ecc_enc = ecc;
end
endfunction


// This function returns the {overall_parity, syndrome}
function automatic [8:0] new_dbnk_ecc_dec_a;
    input [127:0] data_in;
    input [8 :0] ecc_in;
    // XOR of received and re-calculated EDC
    reg  [7:0] syndrome;
    reg overall_parity;
    // The word which ECC will be calculated
    reg  [127:0] word_in;
    // Decoder re-calculates the EDC from the received data
    reg  [7:0] calc_edc;
    // Temporary signal to hold received EDC
    reg  [7:0] edc_in_tmp;

begin
    // The word which EDC will be calculated again
    word_in = data_in;

    // Since the encoder inverts last two EDC bits before storing them, invert them back before comparing with generated EDC
    edc_in_tmp = {~ecc_in[7 ], ~ecc_in[6 ], ecc_in[5 :0]};

    // Pick particular word bits by using masks, then XOR them
    // Masks to select bits to be XORed
    calc_edc[0] = ^(word_in & 128'b10101010110101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010110101010101010110101011011);
    calc_edc[1] = ^(word_in & 128'b00110011011001100110011001100110011001100110011001100110011001100110011010011001100110011001100110011011001100110011011001101101);
    calc_edc[2] = ^(word_in & 128'b00111100011110000111100001111000011110000111100001111000011110000111100011100001111000011110000111100011110000111100011110001110);
    calc_edc[3] = ^(word_in & 128'b11000000011111111000000001111111100000000111111110000000011111111000000011111110000000011111111000000011111111000000011111110000);
    calc_edc[4] = ^(word_in & 128'b00000000011111111111111110000000000000000111111111111111100000000000000011111111111111100000000000000011111111111111100000000000);
    calc_edc[5] = ^(word_in & 128'b00000000011111111111111111111111111111111000000000000000000000000000000011111111111111111111111111111100000000000000000000000000);
    calc_edc[6] = ^(word_in & 128'b00000000011111111111111111111111111111111111111111111111111111111111111100000000000000000000000000000000000000000000000000000000);
    calc_edc[7] = ^(word_in & 128'b11111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);

    // Calculate syndrome by comparing received and calculated EDC bits
    syndrome = edc_in_tmp ^ calc_edc;

    // Overall parity check should be zero for no error and even number of bit error cases
    overall_parity = ^{word_in, ecc_in};
    new_dbnk_ecc_dec_a = {overall_parity, syndrome};
end
endfunction


// This function returns the {unknown_err, double_err, single_err};
function automatic [2:0] new_dbnk_ecc_dec_b;
    input enable;
    input [7:0] syndrome;
    input      overall_parity;
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
    is_unused_syndrome = (syndrome == 63) | (syndrome == 138) | (syndrome == 139) | (syndrome == 140) | (syndrome == 141) | (syndrome == 142) | 
    (syndrome == 143) | (syndrome == 144) | (syndrome == 145) | (syndrome == 146) | (syndrome == 147) | (syndrome == 148) | 
    (syndrome == 149) | (syndrome == 150) | (syndrome == 151) | (syndrome == 152) | (syndrome == 153) | (syndrome == 154) | 
    (syndrome == 155) | (syndrome == 156) | (syndrome == 157) | (syndrome == 158) | (syndrome == 159) | (syndrome == 160) | 
    (syndrome == 161) | (syndrome == 162) | (syndrome == 163) | (syndrome == 164) | (syndrome == 165) | (syndrome == 166) | 
    (syndrome == 167) | (syndrome == 168) | (syndrome == 169) | (syndrome == 170) | (syndrome == 171) | (syndrome == 172) | 
    (syndrome == 173) | (syndrome == 174) | (syndrome == 175) | (syndrome == 176) | (syndrome == 177) | (syndrome == 178) | 
    (syndrome == 179) | (syndrome == 180) | (syndrome == 181) | (syndrome == 182) | (syndrome == 183) | (syndrome == 184) | 
    (syndrome == 185) | (syndrome == 186) | (syndrome == 187) | (syndrome == 188) | (syndrome == 189) | (syndrome == 190) | 
    (syndrome == 191) | (syndrome == 192) | (syndrome == 193) | (syndrome == 194) | (syndrome == 195) | (syndrome == 196) | 
    (syndrome == 197) | (syndrome == 198) | (syndrome == 199) | (syndrome == 200) | (syndrome == 201) | (syndrome == 202) | 
    (syndrome == 203) | (syndrome == 204) | (syndrome == 205) | (syndrome == 206) | (syndrome == 207) | (syndrome == 208) | 
    (syndrome == 209) | (syndrome == 210) | (syndrome == 211) | (syndrome == 212) | (syndrome == 213) | (syndrome == 214) | 
    (syndrome == 215) | (syndrome == 216) | (syndrome == 217) | (syndrome == 218) | (syndrome == 219) | (syndrome == 220) | 
    (syndrome == 221) | (syndrome == 222) | (syndrome == 223) | (syndrome == 224) | (syndrome == 225) | (syndrome == 226) | 
    (syndrome == 227) | (syndrome == 228) | (syndrome == 229) | (syndrome == 230) | (syndrome == 231) | (syndrome == 232) | 
    (syndrome == 233) | (syndrome == 234) | (syndrome == 235) | (syndrome == 236) | (syndrome == 237) | (syndrome == 238) | 
    (syndrome == 239) | (syndrome == 240) | (syndrome == 241) | (syndrome == 242) | (syndrome == 243) | (syndrome == 244) | 
    (syndrome == 245) | (syndrome == 246) | (syndrome == 247) | (syndrome == 248) | (syndrome == 249) | (syndrome == 250) | 
    (syndrome == 251) | (syndrome == 252) | (syndrome == 253) | (syndrome == 254) | (syndrome == 255);

    // If overall parity check fails and syndrome is used, then we flag a single bit error
    // Note that this also covers the case when syndrome is zero, and the overall parity fails
    single_err = ~is_unused_syndrome & overall_parity & enable;

    // Assert double error if syndrome is non-zero and overall parity overall parity does not match
    double_err = is_syndrome_non_zero & ~overall_parity & enable;

    // If the syndrome is not used and overally parity fails, this is a detected multi odd bit error
    unknown_err = overall_parity & is_unused_syndrome & enable;

    new_dbnk_ecc_dec_b = {unknown_err, double_err, single_err};
end
endfunction


// This function returns the corrected data;
function automatic [127:0] new_dbnk_ecc_dec_c;
    input single_err;
    input [7:0] syndrome;
    input [127:0] data_in;
    reg [127:0] data_out;
begin

    // Map error syndrome to faulty data bit location and correct it

    data_out = data_in;

    // Do correction only if it is a single bit error and module is enabled
    if (single_err) begin
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
        (65) :        data_out[56] = ~data_in[56];
        (66) :        data_out[57] = ~data_in[57];
        (67) :        data_out[58] = ~data_in[58];
        (68) :        data_out[59] = ~data_in[59];
        (69) :        data_out[60] = ~data_in[60];
        (70) :        data_out[61] = ~data_in[61];
        (71) :        data_out[62] = ~data_in[62];
        (72) :        data_out[63] = ~data_in[63];
        (73) :        data_out[64] = ~data_in[64];
        (74) :        data_out[65] = ~data_in[65];
        (75) :        data_out[66] = ~data_in[66];
        (76) :        data_out[67] = ~data_in[67];
        (77) :        data_out[68] = ~data_in[68];
        (78) :        data_out[69] = ~data_in[69];
        (79) :        data_out[70] = ~data_in[70];
        (80) :        data_out[71] = ~data_in[71];
        (81) :        data_out[72] = ~data_in[72];
        (82) :        data_out[73] = ~data_in[73];
        (83) :        data_out[74] = ~data_in[74];
        (84) :        data_out[75] = ~data_in[75];
        (85) :        data_out[76] = ~data_in[76];
        (86) :        data_out[77] = ~data_in[77];
        (87) :        data_out[78] = ~data_in[78];
        (88) :        data_out[79] = ~data_in[79];
        (89) :        data_out[80] = ~data_in[80];
        (90) :        data_out[81] = ~data_in[81];
        (91) :        data_out[82] = ~data_in[82];
        (92) :        data_out[83] = ~data_in[83];
        (93) :        data_out[84] = ~data_in[84];
        (94) :        data_out[85] = ~data_in[85];
        (95) :        data_out[86] = ~data_in[86];
        (96) :        data_out[87] = ~data_in[87];
        (97) :        data_out[88] = ~data_in[88];
        (98) :        data_out[89] = ~data_in[89];
        (99) :        data_out[90] = ~data_in[90];
        (100) :        data_out[91] = ~data_in[91];
        (101) :        data_out[92] = ~data_in[92];
        (102) :        data_out[93] = ~data_in[93];
        (103) :        data_out[94] = ~data_in[94];
        (104) :        data_out[95] = ~data_in[95];
        (105) :        data_out[96] = ~data_in[96];
        (106) :        data_out[97] = ~data_in[97];
        (107) :        data_out[98] = ~data_in[98];
        (108) :        data_out[99] = ~data_in[99];
        (109) :        data_out[100] = ~data_in[100];
        (110) :        data_out[101] = ~data_in[101];
        (111) :        data_out[102] = ~data_in[102];
        (112) :        data_out[103] = ~data_in[103];
        (113) :        data_out[104] = ~data_in[104];
        (114) :        data_out[105] = ~data_in[105];
        (115) :        data_out[106] = ~data_in[106];
        (116) :        data_out[107] = ~data_in[107];
        (117) :        data_out[108] = ~data_in[108];
        (118) :        data_out[109] = ~data_in[109];
        (119) :        data_out[110] = ~data_in[110];
        (120) :        data_out[111] = ~data_in[111];
        (121) :        data_out[112] = ~data_in[112];
        (122) :        data_out[113] = ~data_in[113];
        (123) :        data_out[114] = ~data_in[114];
        (124) :        data_out[115] = ~data_in[115];
        (125) :        data_out[116] = ~data_in[116];
        (126) :        data_out[117] = ~data_in[117];
        (127) :        data_out[118] = ~data_in[118];
        (129) :        data_out[119] = ~data_in[119];
        (130) :        data_out[120] = ~data_in[120];
        (131) :        data_out[121] = ~data_in[121];
        (132) :        data_out[122] = ~data_in[122];
        (133) :        data_out[123] = ~data_in[123];
        (134) :        data_out[124] = ~data_in[124];
        (135) :        data_out[125] = ~data_in[125];
        (136) :        data_out[126] = ~data_in[126];
        (137) :        data_out[127] = ~data_in[127];
        endcase
    end
    new_dbnk_ecc_dec_c = data_out;
end
endfunction


// This function returns the corrected ecc code;
function automatic [8 :0] new_dbnk_ecc_dec_d;
    input single_err;
    input [7:0] syndrome;
    input [8 :0] ecc_in;
    reg [8 :0] ecc_out;
begin
    // Map error syndrome to faulty data bit location and correct it

    ecc_out  = ecc_in;
    
    // Do correction only if it is a single bit error and module is enabled
    if (single_err) begin
        case(syndrome)
        (1 ) :        ecc_out[0] = ~ecc_in[0];
        (2 ) :        ecc_out[1] = ~ecc_in[1];
        (4 ) :        ecc_out[2] = ~ecc_in[2];
        (8 ) :        ecc_out[3] = ~ecc_in[3];
        (16) :        ecc_out[4] = ~ecc_in[4];
        (32) :        ecc_out[5] = ~ecc_in[5];
        (64) :        ecc_out[6] = ~ecc_in[6];
        (128) :        ecc_out[7] = ~ecc_in[7];
        (0 ) :        ecc_out[8] = ~ecc_in[8];
        endcase
    end
    new_dbnk_ecc_dec_d = ecc_out;
end
endfunction

