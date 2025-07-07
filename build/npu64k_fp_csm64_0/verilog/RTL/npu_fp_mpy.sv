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

// Floating-point multiplier
// - Round ties to nearest even
// - truncate subnormal to 0
// - infinity becomes nan

module npu_fp_mpy 
  (
   input  logic [31:0] a,
   input  logic [31:0] b,
   output logic [31:0] z
   );

  always_comb
  begin : mpy_proc
    logic        sgn;
    logic [7:0]  ea;
    logic [7:0]  eb;
    logic [23:0] ma;
    logic [23:0] mb;
    logic [9:0]  ez;
    logic [9:0]  ez_rounded;
    logic [47:0] mz;
    logic [24:0] mz_rounded;
    logic        rnd_val;
    logic        mnc;

    sgn     = a[31] ^ b[31];
    ea      = a[30:23];
    eb      = b[30:23];
    ma      = {1'b1,a[22:0]};
    mb      = {1'b1,b[22:0]};
    
    // initial exponent and mantissa product
    ez = ea + eb - 'd127;
    mz = ma * mb;
    
    if (mz[47]) 
    begin
      // overflow
      ez  = ez + 'd1;
      mnc = 0;
    end
    else
    begin
      // ensure leading 1 at position 47
      mz  = {mz[46:0], 1'b0};
      mnc = ez == '0;
    end

    // round ties to nearest even
    if (mnc) 
    begin
      rnd_val = mz[24]&(mz[25]|(|mz[23:0]));
    end
    else
    begin
      rnd_val = mz[23]&(mz[24]|(|mz[22:0]));
    end
    
    mz_rounded = {1'b0,mz[47:24]} + rnd_val;
    
    ez_rounded = ez;
    if (mz_rounded[24]) 
    begin
      // overflow after rounding
      ez_rounded = ez + 'd1;
      mz_rounded = {1'b0,mz_rounded[24:1]};
    end

    // return result
    // one of the inputs in NaN, so output is NaN
    if (eb == 8'hff)
    begin
      // second operand has highest priority
      z = '1;
      z[31] = b[31];
    end
    else if (ea == 8'hff)
    begin
      // first operand has medium priority
      z = '1;
      z[31] = a[31];
    end
    else if (ea == 8'h00 || eb == 8'h00 || ez_rounded[9] || (ez_rounded[8:0] == '0))
    begin
      // one of the inputs is 0 or result is too small, so output is 0
      z = '0;
      z[31] = sgn;
    end
    else if ((ez_rounded[9:8] == 2'b01) || (ez_rounded[7:0] == 8'hff))
    begin
      // result exponent overflow, return NaN
      z = '1;
      z[31] = sgn;
    end
    else
    begin
      // no special value
      z = {1'b0,ez_rounded[7:0],mz_rounded[22:0]};
      z[31] = sgn;
    end
  end : mpy_proc

endmodule : npu_fp_mpy
