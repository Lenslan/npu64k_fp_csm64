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
// Convolution normalization
//
`include "npu_defines.v"

module npu_conv_mpy_norm
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter logic NPU_HAS_FLOAT=1)
  (

   input  logic                          clk,                 // Clock, all logic clocked at posedge
   input  logic                          rst_a,               // Asynchronous reset, active high
// spyglass disable_block W240
//SMD:Unread input sum_en
//SJ :Read in config when NPU_L0_GATE_EN == 0, can be ignored in other config
   input  logic                          norm_en,             // Enable register
   input  mpy_cfg_t                      mpycfg,
// spyglass enable_block W240
   input  out_sns_t   [ISIZE-1:0]        sns_in,              // final sum output 0
   output out_norms_t [ISIZE-1:0]        norms_out            // normalized outputs
   );
  out_norms_t [ISIZE-1:0]       norms_out_nxt;
  out_norms_t [ISIZE-1:0]       norms_out_r;  
  logic       [ISIZE-1:0][9:0]  norms_exp;
  logic       [ISIZE-1:0][31:0] mant_norm_inv;
  logic       [ISIZE-1:0][31:0] mant_norm_shift;
  logic       [ISIZE-1:0][5:0]  leading_zeroes;


  // simple assignment
  assign norms_out = norms_out_r;

  
  // optimized 32b count leading 0
  function automatic logic [5:0] clz(logic [31:0] i);
    logic [5:0]      e;
    logic [7:0]      v;
    logic [7:0][1:0] l;
    logic [3:0][2:0] m;
    logic [1:0][3:0] n;
    v = '0;
    l = '0;
    // loop over 8
    for (int c = 0; c < 8; c++)
    begin
      v[c]    = i[4*c+:4] != '0;
      l[c][0] = (i[4*c+2+:2] == 2'b01) | (i[4*c+:4] == 4'b0001);
      l[c][1] = (i[4*c+2+:2] == 2'b00);
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
    e[4:0] = (v[7:4] != 4'b0000) ? {1'b0,n[1]} : {1'b1,n[0]};
    e[5]   = v == '0;
    return e;
  endfunction : clz

 
  // unsigned barrel left right
  function automatic logic [31:0] barrelshift(logic [31:0] i, logic [4:0] shamt);
    logic [31:0] res;
    res = i;
    if (shamt[4])
    begin
      res = {res[15:0],16'd0};
    end
    if (shamt[3])
    begin
      res = {res[23:0],8'd0};
    end
    if (shamt[2])
    begin
      res = {res[27:0],4'd0};
    end
    if (shamt[1])
    begin
      res = {res[29:0],2'd0};
    end
    if (shamt[0])
    begin
      res = {res[30:0],1'd0};
    end
    return res;
  endfunction : barrelshift

  
  //
  // normalization
  //
  // outputs norms_out_nxt, norms_exp
  always_comb
  begin : logic_PROC    
    norms_out_nxt = '0;
    norms_exp     = '0;
    
    for (int i = 0; i < ISIZE; i++)
    begin

      logic [30:0] sum0;
      logic [20:0] sum1;
      
      sum0 = sns_in[i].lo;
      sum1 = sns_in[i].hi;

      if (NPU_HAS_FLOAT && isfp(mpycfg))
      begin
        mant_norm_inv[i] = {sum0[30],sum0};
        if (sum0[30])
        begin
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
          mant_norm_inv[i] = -mant_norm_inv[i];
// spyglass enable_block W164a
        end
        leading_zeroes[i]  = clz(mant_norm_inv[i]);
        mant_norm_shift[i] = barrelshift(mant_norm_inv[i], leading_zeroes[i][4:0]);

        norms_exp[i] = {1'b0,sns_in[i].maxexp} - {4'b0000,leading_zeroes[i][4:0]} + 'd7; 
        
        norms_out_nxt[i].f.sgn  = sum0[30];
        norms_out_nxt[i].f.m = mant_norm_shift[i][30:8];
        if (sns_in[i].nan || (norms_exp[i][9:8]==2'b01 && !leading_zeroes[i][5]) || sns_in[i].maxexp=='1)
        begin
          norms_out_nxt[i].f.e = '1;
        end
        else if (sns_in[i].maxexp == '0 || norms_exp[i][9] || leading_zeroes[i][5])
        begin
          norms_out_nxt[i].f.e = '0;
        end
        else
        begin          
          norms_out_nxt[i].f.e = norms_exp[i][7:0];
        end
      end
      else
      begin
        norms_out_nxt[i].i.sum0 = {sum0[30],sum0};
        norms_out_nxt[i].i.sum1 = {{11{sum1[20]}},sum1};
      end

    end
    
  end : logic_PROC

  
  // output register
  always_ff @(posedge clk or posedge rst_a)
  begin : ff_PROC
    if (rst_a)
    begin
      norms_out_r      <= '0;
    end
    else
    begin
      if (norm_en)
      begin
        norms_out_r    <= norms_out_nxt;
      end
    end
  end : ff_PROC
  

endmodule : npu_conv_mpy_norm
