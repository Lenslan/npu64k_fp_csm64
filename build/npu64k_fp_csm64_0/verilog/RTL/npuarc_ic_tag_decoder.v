// Library ARCv2HS-3.5.999999999
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
 * Data bits: 30
 * Address bits: 0 (Address protection is enabled)
 * Fault coverage: The code can detect up to two bit errors and simultaneously corrects single bit errors.
 * All-zero and all-one protection is enabled. These faults will be detected as two-bit errors.
 * Required minimum ECC bits: 7 
 ********************************************************************************************************
 */

module npuarc_ic_tag_ecc_decoder(
// Module input and output ports
      input enable
    , input [29:0] data_in
    , output [5:0] syndrome_out
    , input [6 :0] ecc_in
    , output [6 :0] ecc_out
    , output [29:0] data_out
    , output single_err
    , output double_err
    , output unknown_err
);

`include "npuarc_ic_tag_ecc_func.v"

wire [5:0] syndrome;
wire overall_parity;

assign {overall_parity, syndrome} = 
    ic_tag_ecc_dec_a(
      data_in    
    , ecc_in     
    );


assign syndrome_out = syndrome;

assign {
      unknown_err
    , double_err
    , single_err
    } = ic_tag_ecc_dec_b(
      enable         
    , syndrome
    , overall_parity
    );

assign data_out = ic_tag_ecc_dec_c(
      single_err     
    , syndrome
    , data_in
    );

assign ecc_out = ic_tag_ecc_dec_d(
      single_err     
    , syndrome
    , ecc_in
    );
endmodule
