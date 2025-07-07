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

//
// NPU convolution accumulator stage
//
`include "npu_defines.v"

module npu_conv_mpy_acc
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter logic NPU_HAS_FLOAT = 1)
  (
   input  logic                        clk,      // Clock, all logic clocked at posedge
   input  logic                        rst_a,    // Asynchronous reset, active high
   input  logic                        a_init,   // Reinitialize the accumulator
   input  ixacc_t     [1:0]            ar_acc,   // Input accumulators
   input  mpy_cfg_t                    mpycfg,   // Multiplier format
   input  logic       [1:0]            acc_en,   // Accumulator enable
   input  out_norms_t [ISIZE-1:0]      norms,    // normalized inputs
   output ixacc_t     [1:0]            acc_out   // Output accumulators
   );

  //
  // Local typedefs
  //
  typedef union packed {
    struct packed {
      logic   [27:0]    frac;           // denormal mantissa
      logic   [31:0]    lrge;           // largest of inputs
    } fp;
    struct packed {
      logic   [27:0]    pad;
      acc_t             ac;             // integer result
    } i;
  } acc_hi_t;
  
  //
  // Local wires
  //
  ixacc_t                      acc_lo_r;       // lo integer accumulator
  ixacc_t                      acc_lo_nxt;
  acc_hi_t [ISIZE-1:0]         acc_hi_r;       // floating-point and hi integer accumulator
  acc_hi_t [ISIZE-1:0]         acc_hi_nxt;


  //
  // Functions
  //
  // sticky shifter
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
  
  // unsigned barrel left right
  function automatic logic [27:0] barrelshift(logic [27:0] i, logic [4:0] shamt);
    logic [27:0] res;
    res = i;
    if (shamt[4])
    begin
      res = {res[11:0],16'd0};
    end
    if (shamt[3])
    begin
      res = {res[19:0],8'd0};
    end
    if (shamt[2])
    begin
      res = {res[23:0],4'd0};
    end
    if (shamt[1])
    begin
      res = {res[25:0],2'd0};
    end
    if (shamt[0])
    begin
      res = {res[26:0],1'd0};
    end
    return res;
  endfunction : barrelshift

  // optimized 32b count leading zero bits
  function automatic logic [4:0] clz28(logic [27:0] i);
    logic [4:0]      e;
    logic [7:0]      v;
    logic [7:0][1:0] l;
    logic [3:0][2:0] m;
    logic [1:0][3:0] n;
    v = '0;
    l = '0;
    // loop over 7 only
    v[7] = 1'b1;
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
    // default
    acc_lo_nxt = '0;
    acc_hi_nxt = '0;
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
    for (int i = 0; i < ISIZE; i++)
    begin
      if (NPU_HAS_FLOAT && isfp(mpycfg))
      begin
        logic [31:0] smll;                 // small input
        logic        ovfl;                 // incoming exp overflow after norm adjust +7
        logic [7:0]  e_lrge,e_smll;        // exponents
        logic        swap,subtract;
        logic [22:0] f_lrge,f_smll;        // fractions
        logic [27:0] m_lrge,m_smll;        // the mantissa numbers
        logic [7:0]  e_diff;               // exponent difference
        // input from norm to standard format
        smll[31]         = norms[i].f.sgn;
        smll[30:23]      = norms[i].f.e;
        smll[22:0]       = norms[i].f.m[22:0];
        // identify biggest and smallest
        subtract                = ar_acc[0][i][31] ^ smll[31];
        swap                    = ar_acc[0][i][30:0] < smll[30:0];
        acc_hi_nxt[i].fp.lrge   = swap ? smll : ar_acc[0][i];
        smll                    = swap ? ar_acc[0][i] : smll;
        e_lrge                  = acc_hi_nxt[i].fp.lrge[30:23];
        e_smll                  = smll[30:23];
        f_lrge                  = acc_hi_nxt[i].fp.lrge[22:0];
        f_smll                  = smll[22:0];
        
        // explicit leading 1 on mantissas
        m_lrge = {2'b01,f_lrge,3'b000};
        if (e_smll == '0) 
        begin
          // force 0
          m_smll = '0;
        end
        else
        begin
          // normal
          m_smll = {2'b01,f_smll,3'b000};
        end
        
        // difference of exponents
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
        e_diff = acc_hi_nxt[i].fp.lrge[30:23] - e_smll;
// spyglass enable_block W164a
        
        // sticky shift right small input by e_diff
        m_smll = stickyshift(m_smll, e_diff);
        
        // compute m_z result: a +/- b
        m_smll                = m_smll ^ {28{subtract}};
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
        acc_hi_nxt[i].fp.frac = m_lrge + m_smll + subtract;
// spyglass enable_block W164a
      end // if (NPU_HAS_FLOAT && isfp(mpycfg))
      else
      begin
        acc_t [1:0] acc_ini;
        acc_t [1:0] a;
        acc_t [2:0] b;
        // integer mode
        if (a_init) 
        begin
          // initialize from AM memory
          acc_ini = {ar_acc[1][i],ar_acc[0][i]};
        end
        else
        begin
          // continue accumulation
          acc_ini = {acc_hi_r[i].i.ac,acc_lo_r[i]};
        end
        a = '0;
        b = '0;
        a[0] |= acc_ini[0];
        a[1] |= norms[i].i.sum0;
        b[0] |= acc_ini[1];
        b[1] |= norms[i].i.sum1;
        if (isfmdblcfdbl(mpycfg)) 
        begin
          a[0][25:24] &= 2'd0; // clear carry bits
          b[2][1:0]   |= acc_ini[0][25:24]; // carry from previous cycle low part
        end
        // actual full adders
        // spyglass disable_block W164a
        //SMD:Width mismatch
        //SJ :Intentional add and no influence to result
        acc_lo_nxt[i] = a[0] + a[1];
        acc_hi_nxt[i].i.ac = b[0] + b[1] + b[2];
        // spyglass enable_block W164a
      end // else: !if(NPU_HAS_FLOAT && isfp(mpycfg))
    end // for (int i = 0; i < ISIZE; i++)
// spyglass enable_block SelfDeterminedExpr-ML
  end : add_proc
  

  // accumulator registers
  // outputs: acc_r
  always_ff @(posedge clk or posedge rst_a) 
  begin : acc_reg_PROC
    if (rst_a == 1'b1) 
    begin
      acc_lo_r    <='0;
      acc_hi_r    <='0;
    end
    else 
    begin
      if (acc_en[0]) 
      begin
        acc_lo_r <= acc_lo_nxt;
      end
      if (acc_en[1]) 
      begin
        acc_hi_r <= acc_hi_nxt;
      end         
    end
  end : acc_reg_PROC
  

  //
  // final output
  //
  // outputs: acc_out
  always_comb
  begin : out_PROC
    acc_out[0] = acc_lo_r;
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
    for (int i = 0; i < ISIZE; i++)
    begin
      if (NPU_HAS_FLOAT && isfp(mpycfg))
      begin
        logic [8:0]  e_comp;               // the biggest possible exponent
        logic [8:0]  e_rnd;                // exponent after rounding
        logic [4:0]  nrm;                  // leading zero count
        logic [27:0] m_s;                  // the normalized mantissa
        logic [22:0] m_o;                  // the rounded mantissa
        logic        nov;                  // no overflow after rounding
        logic        lsb_clr;              // values returned by rnd_eval function
        // prepare for normalization
        nrm    = clz28(acc_hi_r[i].fp.frac);
        e_comp = {1'b0, acc_hi_r[i].fp.lrge[30:23]} + 'd1 - nrm;

        // normalize the mantissa for leading zero case
        m_s = barrelshift(acc_hi_r[i].fp.frac, nrm);
        
        // round ties to nearest even, overflow into exponent
        lsb_clr = (~m_s[4])&(m_s[2:0]==3'b000);
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
        {e_rnd,nov,m_o} = {e_comp,1'b1,m_s[26:4]} + m_s[3];
// spyglass enable_block W164a
        m_o[0] = m_o[0] & (~lsb_clr);
        
        if (acc_hi_r[i].fp.lrge[30:23] == 8'hff)
        begin
          // biggest is nan
          acc_out[1][i] = '1;
          acc_out[1][i][31] = 1'b0;
        end
        else if ( (acc_hi_r[i].fp.lrge[30:23] == 8'h00)  || (acc_hi_r[i].fp.frac == '0) || e_rnd[8] || (e_rnd[7:0] == '0))
        begin
          // exact zero or smaller than can be represented --> zero
          acc_out[1][i] = '0;
        end
        else if (&e_rnd[7:0])
        begin
          // nan
          acc_out[1][i] = '1;
          acc_out[1][i][31] = 1'b0;
        end
        else if (nov)
        begin
          // no rounding overflow
          acc_out[1][i] = {acc_hi_r[i].fp.lrge[31],e_rnd[7:0],m_o};
        end
        else
        begin
          // overflow from rounding
          acc_out[1][i] = {acc_hi_r[i].fp.lrge[31],e_rnd[7:0],1'b0,m_o[22:1]};
        end
      end // if (NPU_HAS_FLOAT && isfp(mpycfg))
      else
      begin
        acc_out[1][i] = acc_hi_r[i].i.ac;
        if (isfmdblcfdbl(mpycfg)) 
        begin
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
          // propagate carry
          acc_out[1][i]        = acc_out[1][i] + acc_out[0][i][25:24];
// spyglass enable_block W164a
          acc_out[0][i][25:24] = 2'b00;
        end
      end // else: !if(NPU_HAS_FLOAT && isfp(mpycfg))     
    end // for (int i = 0; i < ISIZE; i++)
// spyglass enable_block SelfDeterminedExpr-ML
  end : out_PROC


endmodule : npu_conv_mpy_acc
