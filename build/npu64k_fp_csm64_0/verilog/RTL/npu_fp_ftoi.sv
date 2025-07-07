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

// Floating-point to integer conversion with configurable rounding mode
// - 1: Round ties to nearest even
// - 0: round towards 0

module npu_fp_ftoi
  #(
    parameter int rnd_mode=0 // 0=round to zero, 1=convergent, ties to nearest even
  )
  (
   input  logic [31:0] a, // input floating-point value
   output logic [31:0] z // output integer
   );

  // sticky shifter
  function automatic logic [32:0] stickyshift(logic [32:0] i, logic [4:0] shamt);
    logic [32:0] res;
    res = i;
    if (shamt[0])
    begin
      res[1] = |res[1:0];
      res = {1'd0,res[32:1]};
    end
    if (shamt[1])
    begin
      res[2] = |res[2:0];
      res = {2'd0,res[32:2]};
    end
    if (shamt[2])
    begin
      res[4] = |res[4:0];
      res = {4'd0,res[32:4]};
    end
    if (shamt[3])
    begin
      res[8] = |res[8:0];
      res = {8'd0,res[32:8]};
    end
    if (shamt[4])
    begin
      res[16] = |res[16:0];
      res = {16'd0,res[32:16]};
    end
    return res;
  endfunction : stickyshift
  

  always_comb
  begin : conv_PROC
    logic [4:0]  shamt;
    logic [32:0] manti;
    logic [32:0] mantsh;
    logic        rnd;
    logic [30:0] mantrnd;
    // shift integer part of mantissa to lsbs
    // keep 2 bit round and sticky bit on lsb
    shamt   = 'd157 - a[30:23]; // 157=127+30
    manti   = {1'b1,a[22:0],9'd0};
    mantsh  = stickyshift(manti, shamt);
    rnd     = mantsh[1]&(mantsh[2]|mantsh[0]);
    if (rnd_mode != 0)
    begin
      // convergent rounding
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
      mantrnd = mantsh[2+:31] + rnd;
// spyglass enable_block W164a
    end
    else
    begin
      // truncate
      mantrnd = mantsh[2+:31];
    end
    // select result
    // input has 127 exponent offset, so:
    //  if exp < 126 then output 0
    //  if exp >= 127+31 then saturate output maxint/minint
    //  else denormalize
    if (a[30:23] < 'd126)
    begin
      // underflow, set to 0
      z = 32'd0;
    end
    else if (a[30:23] >= 'd158)
    begin
      // overflow, set to max/minint
      z = {a[31],{31{~a[31]}}};
    end
    else 
    begin
      // negation cannot overflow
      z = a[31] ? -{1'b0,mantrnd} : {1'b0,mantrnd};
    end
  end : conv_PROC
  
endmodule : npu_fp_ftoi
