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

//prefix: am_ecc_2nd_ ALL_ZERO_ALL_ON:1 SECDED:1 PIPELINE:0 OVERWRITE_PREFIX:am_ecc_2nd_ generic:0
module am_ecc_2nd_decoder(
// Module input and output ports
      input enable
    , input [63:0] data_in
    , output [6:0] syndrome
    , input [7 :0] ecc_in
    , output [7 :0] ecc_out
    , output [63:0] data_out
    , output single_err
    , output double_err
);

`include "am_ecc_2nd_func.sv"


wire overall_parity;
wire overall_parity_and_enable;
wire   unknown_err, db_err, sb_err;
assign single_err = sb_err;
assign double_err = unknown_err || db_err;

assign overall_parity_and_enable = overall_parity & enable;


assign {overall_parity, syndrome} = 
    am_ecc_2nd_dec_a(
      data_in
    , ecc_in
    );

assign {
      unknown_err
    , db_err
    , sb_err
    } = am_ecc_2nd_dec_b(
      enable
    , syndrome
    , overall_parity
    , overall_parity_and_enable
    );

assign data_out = am_ecc_2nd_dec_c(
      overall_parity_and_enable
    , syndrome
    , data_in
    );

assign ecc_out = am_ecc_2nd_dec_d(
      overall_parity_and_enable
    , syndrome
    , ecc_in
    );
endmodule
