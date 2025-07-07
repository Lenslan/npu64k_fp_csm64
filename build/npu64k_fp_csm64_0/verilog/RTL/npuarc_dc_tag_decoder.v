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
 * Data bits: 27
 * Address bits: 0 (Address protection is enabled)
 * Fault coverage: The code can detect up to two bit errors and simultaneously corrects single bit errors.
 * All-zero and all-one protection is enabled. These faults will be detected as two-bit errors.
 * Required minimum ECC bits: 7 
 ********************************************************************************************************
 */

module npuarc_dc_tag_ecc_decoder(
// Module input and output ports
      input enable
    , input clk
    , input rst_a
    , input [26:0] data_in_r
	, input ecc_error_cg
    , input [6 :0] ecc_in_r
    , input [26:0] data_in
    , output [5:0] syndrome_out
    , input [6 :0] ecc_in
    , output [6 :0] ecc_out
    , output [26:0] data_out
    , output single_err
    , output double_err
    , output unknown_err
);

`include "npuarc_dc_tag_ecc_func.v"

wire [5:0] syndrome;
reg  [5:0] syndrome_r;
wire overall_parity;
reg  overall_parity_r;

assign {overall_parity, syndrome} = 
    dc_tag_ecc_dec_a(
      data_in    
    , ecc_in     
    );

always @(posedge clk or posedge rst_a)
begin : dc_tag_ecc_ecc_dec_reg_PROC
   if( rst_a == 1'b1 )
   begin
      syndrome_r        <= {6 {1'b0}};
      overall_parity_r  <= 1'b0;
   end
   else if(ecc_error_cg)
   begin
      syndrome_r        <= syndrome;
      overall_parity_r  <= overall_parity;
   end
end


assign syndrome_out = syndrome_r;

assign {
      unknown_err
    , double_err
    , single_err
    } = dc_tag_ecc_dec_b(
      enable         
    , syndrome_r
    , overall_parity_r
    );

assign data_out = dc_tag_ecc_dec_c(
      single_err     
    , syndrome_r
    , data_in_r
    );

assign ecc_out = dc_tag_ecc_dec_d(
      single_err     
    , syndrome_r
    , ecc_in_r
    );
endmodule
