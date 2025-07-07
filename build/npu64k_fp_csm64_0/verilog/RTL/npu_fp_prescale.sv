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

// Floating-point prescaling multiplier
// - Round ties to nearest even
// - truncate subnormal to 0
// - infinity becomes nan

module npu_fp_prescale
  (
   input  logic [31:0] a,
   input  logic [7:0]  b,
   output logic [31:0] z
   );

  always_comb
  begin : scale_PROC
    logic [23:0]      m_int;
    logic [2:0][26:0] p;
    logic [26:0]      prod;
    logic [26:0]      prod1;
    logic [22:0]      mant;
    logic [9:0]       ex;
    // mantissa with explicit leading 1
    m_int = {1'b1,a[22:0]};
    // partial products, one bit for overflow
    p[0] = b[0] ? {3'b000, m_int       } : '0;
    p[1] = b[1] ? { 2'b00, m_int, 1'b0 } : '0;
    p[2] =        {  1'b0, m_int, 2'b00};
    // accumulate partial products, add for rounding
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
    prod  = p[0] + p[1] + p[2] + 2'b10;
    prod1 = p[0] + p[1] + p[2] + 3'b100;
// spyglass enable_block W164a
    // product exponent, subtract ue6m2 bias 31, so exponent bias is 127, add one on overflow
    ex    = {2'b00,a[30:23]} + {4'b0,b[7:2]} - 'd31 + prod[26];
    // round ties to nearest even
    prod[2]  &= prod[1:0] != '0;
    prod1[3] &= prod1[2:0] != '0;
    // normalize and convert to mantissa
    if (prod[26])
    begin
      mant = prod1[25:3];
    end
    else
    begin
      mant = prod[24:2];
    end
        
    if (a[30:23] == 8'hff)
    begin
      // nan
      z = '1;
    end
    else if (ex[9] || a[30:23] == 8'h00)
    begin
      // zero
      z = '0;
    end
    else if (ex[8:0] == '0)
    begin
      z = {1'b0,7'd0,prod1[26]&~prod[26],23'd0};
    end
    else if (ex[9:8] == 2'b01)
    begin
      // nan
      z = '1;
    end
    else
    begin
      // normal
      z = {1'b0,ex[7:0],mant};
    end
    // copy sign
    z[31] = a[31];
  end : scale_PROC
  
endmodule : npu_fp_prescale
