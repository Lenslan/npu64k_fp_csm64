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

// Floating-point adder
// - Round ties to nearest even
// - truncate subnormal to 0
// - infinity becomes nan

module npu_fp_add
  (
   input  logic [31:0] a,
   input  logic [31:0] b,
   output logic [31:0] z
   );

  // sticky shifter, right
  function automatic logic [27:0] stickyshift(logic [27:0] i, logic [7:0] df);
    logic [4:0]  shamt;
    logic [27:0] res;
    shamt = (|df[7:5]) ? 5'h1f : df[4:0];
    res = i;
    if (shamt[0])
    begin
      res[1] = |res[1:0];
      res = {1'd0,res[27:1]};
    end
    if (shamt[1])
    begin
      res[2] = |res[2:0];
      res = {2'd0,res[27:2]};
    end
    if (shamt[2])
    begin
      res[4] = |res[4:0];
      res = {4'd0,res[27:4]};
    end
    if (shamt[3])
    begin
      res[8] = |res[8:0];
      res = {8'd0,res[27:8]};
    end
    if (shamt[4])
    begin
      res[16] = |res[16:0];
      res = {16'd0,res[27:16]};
    end
    return res;
  endfunction : stickyshift
  
  // barrelshift left
  function automatic logic [27:0] shiftleft(logic [27:0] i, logic [4:0] shamt);
    logic [27:0] res;
    res = i;
    if (shamt[4])
    begin
      res = {res[11:0], 16'h0000};
    end
    if (shamt[3])
    begin
      res = {res[19:0], 8'h00};
    end
    if (shamt[2])
    begin
      res = {res[23:0], 4'h0};
    end
    if (shamt[1])
    begin
      res = {res[25:0], 2'h0};
    end
    if (shamt[0])
    begin
      res = {res[26:0], 1'h0};
    end
    return res;
  endfunction : shiftleft

  // optimized 28b count leading zero bits
  function automatic logic [4:0] clz28(logic [27:0] i);
    logic [4:0]      e;
    logic [7:0]      v;
    logic [7:0][1:0] l;
    logic [3:0][2:0] m;
    logic [1:0][3:0] n;
    v = '0;
    l = '0;
    // loop over only 7
    for (int c = 0; c < 7; c++)
    begin
      v[c+1]    = i[4*c+:4] != '0;
      l[c+1][0] = (i[4*c+2+:2] == 2'b01) | (i[4*c+1+:3] == 3'b000);
      l[c+1][1] = (i[4*c+2+:2] == 2'b00);
    end
    // binary reduction
    for (int c = 0; c < 4; c++)
    begin
      m[c] = (v[2*c+1] != 1'b0) ? {1'b0,l[2*c+1]} : {1'b1,l[2*c+0]};
    end
    for (int c = 0; c < 2; c++)
    begin
      n[c] = (v[4*c+2+:2] != 2'b00) ? {1'b0,m[2*c+1]} : {1'b1,m[2*c+0]};
    end
    e = (v[7:4] != 4'b0000) ? {1'b0,n[1]} : {1'b1,n[0]};
    return e;
  endfunction : clz28

  
  // main process of information
  always_comb
  begin : add_proc
    logic [31:0] lrge,smll;
    logic        f_swap,e_swap,subtract;
    logic [7:0]  e_lrge,e_smll;        // exponents
    logic [22:0] f_lrge,f_smll;        // fractions
    logic [27:0] m_lrge,m_smll;        // the mantissa numbers
    logic [7:0]  e_diff;               // exponent difference
    logic [8:0]  e_comp;               // the biggest possible exponent
    logic [8:0]  e_rnd;                // exponent after rounding
    logic [4:0]  nrm;                  // leading zero count
    logic [27:0] m_z;                  // the mantissa numbers
    logic [27:0] m_s;                  // the normalized mantissa
    logic [22:0] m_o;                  // the rounded mantissa
    logic        nov;                  // no overflow after rounding
    logic        lsb_clr;              // values returned by rnd_eval function
    subtract = a[31] ^ b[31];
    e_swap   = a[30:23] < b[30:23];
    e_lrge   = e_swap ? b[30:23] : a[30:23];
    e_smll   = e_swap ? a[30:23] : b[30:23];
    f_swap   = a[30:0]  < b[30:0];
    lrge     = f_swap ? b : a;
    smll     = f_swap ? a : b;
    f_lrge   = lrge[22:0];
    f_smll   = smll[22:0];

    // mantissa of large and small
    m_lrge = {2'b01,f_lrge,3'b000};
    m_smll = {2'b01,f_smll,3'b000};

    // difference of exponents
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
    e_diff = e_lrge - e_smll;
// spyglass enable_block W164a

    // sticky shift right small input by e_diff
    m_smll = stickyshift(m_smll, e_diff);
      
    // compute m_z result: a +/- b
    m_smll = m_smll ^ {28{subtract}};
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
    m_z    = m_lrge + m_smll + subtract;
// spyglass enable_block W164a
    
    // prepare for normalization
    nrm    = clz28(m_z);

    // normalize the mantissa for leading zero case
    m_s    = shiftleft(m_z, nrm);
    
    // round ties to nearest even, overflow into exponent
    lsb_clr = (~m_s[4])&(m_s[2:0]==3'b000);
    // replace e_comp = e_large - nrm + 'd1 = e_large + ~nrm + 'd2
    {e_rnd,nov,m_o} = { 1'b0,e_lrge,1'b1,m_s[26:4]} + 
                      {        9'h2,         24'h0} +
                      {4'b1111,~nrm,         24'h0} +
                      m_s[3];
    m_o[0] = m_o[0] & (~lsb_clr);

    if (e_smll == 8'hff)
    begin
      // both are nan, second operand has higher priority
      z = {b[31], {31{1'b1}}};
    end
    else if (e_lrge == 8'hff)
    begin
      // biggest is nan or inf
      z = {lrge[31], {31{1'b1}}};
    end
    else if (e_lrge == 8'h00)
    begin
      // both are 0: 0 + -0 = 0; -0 + 0 = 0; -0 + -0 = -0;
      z = {lrge[31] & smll[31], {31{1'b0}}};
    end
    else if (e_smll == 8'h00)
    begin
      // smallest is 0
      z = lrge;
    end
    else if (m_z == '0)
    begin
      // exact zero, return +0
      z = '0;
    end
    else if (e_rnd[8] || (e_rnd[7:0] == '0))
    begin
      // smaller than can be represented --> zero
      z = {lrge[31], {31{1'b0}}};
    end
    else if (&e_rnd[7:0])
    begin
      // nan
      z = {lrge[31], {31{1'b1}}};
    end
    else if (nov)
    begin
      // no rounding overflow
      z = {lrge[31],e_rnd[7:0],m_o};
    end
    else
    begin
      // overflow from rounding
      z = {lrge[31],e_rnd[7:0],1'b0,m_o[22:1]};
    end
  end : add_proc

endmodule : npu_fp_add
