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

module nl2_dbnk_ecc_decoder(
// Module input and output ports
      input enable
    , input [127:0] data_in
    , input [8 :0] ecc_in
    , output [8 :0] ecc_out
    , output [127:0] data_out
    , output single_err
    , output double_err
    , output unknown_err
);

`include "nl2_dbnk_ecc_func.sv"

wire [7:0] syndrome;
wire overall_parity;

assign {overall_parity, syndrome} = 
    dbnk_ecc_dec_a(
      .data_in      (data_in    )
    , .ecc_in       (ecc_in     )
    );

assign {
      unknown_err
    , double_err
    , single_err
    } = dbnk_ecc_dec_b(
      .enable           (enable         )
    , .syndrome         (syndrome       )
    , .overall_parity   (overall_parity )
    );

assign data_out = dbnk_ecc_dec_c(
      .single_err       (single_err     )
    , .data_in          (data_in        )
    , .syndrome         (syndrome       )
    );

assign ecc_out = dbnk_ecc_dec_d(
      .single_err       (single_err     )
    , .ecc_in           (ecc_in         )
    , .syndrome         (syndrome       )
    );
endmodule
