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
// Convolution compressor tree
//
`include "npu_defines.v"

module npu_conv_mpy_sum 
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter logic NPU_HAS_FLOAT=1)
  (
   input  logic                          clk,                 // Clock, all logic clocked at posedge
   input  logic                          rst_a,               // Asynchronous reset, active high
// spyglass disable_block W240
//SMD:Unread input sum_en
//SJ :Read in config when NPU_L0_GATE_EN == 0, can be ignored in other config
   input  logic                          sum_en,              // Enable register
   input  mpy_cfg_t                      mpycfg,
// spyglass enable_block W240
   input  out_prods_t [ISIZE-1:0]        prods,               // product inputs
   output out_sums_t [ISIZE-1:0]         sums                 // sum outputs

   );
  logic      [ISIZE-1:0][ISIZE-1:0]          prod_nan_ovf; 
  logic      [ISIZE-1:0][ISIZE-1:0][26:0]    prod_sgn;
  logic      [ISIZE-1:0][ISIZE-1:0][16:0]    prod_inl; // low products
  logic      [ISIZE-1:0][ISIZE-1:0]          prod_inc; // low products carry input
  logic      [ISIZE-1:0][ISIZE-1:0][16:0]    prod_inh; // high products
  out_sums_t [ISIZE-1:0]                     sums_r;   // registered sums
  out_sums_t [ISIZE-1:0]                     sums_nxt;

  
  //
  // Functions
  //
  // unsigned barrel shift right
  function automatic logic [25:0] barrelshift(logic [25:0] i, logic [7:0] shamt);
    logic [25:0] res;
    res = i;
    if (shamt[0])
    begin
      res = {1'd0,res[25:1]};
    end
    if (shamt[1])
    begin
      res = {2'd0,res[25:2]};
    end
    if (shamt[2])
    begin
      res = {4'd0,res[25:4]};
    end
    if (shamt[3])
    begin
      res = {8'd0,res[25:8]};
    end
    if (shamt[4])
    begin
      res = {16'd0,res[25:16]};
    end
    if (|shamt[7:5])
    begin
      res = '0;
    end
    return res;
  endfunction : barrelshift
  

  //
  // Assignments
  //
  assign sums  = sums_r;

  
  // normalize products across rows
  // outputs: prod_sgn
  always_comb 
  begin : sum_tree_PROC
    prod_sgn      = '0;
    if (NPU_HAS_FLOAT)
    begin
      for (int i = 0; i < ISIZE; i++) 
      begin
        for (int j = 0; j < ISIZE; j++) 
        begin        
          logic [7:0]  delta;
          logic [25:0] prod_shr;
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
          delta              = prods[i].maxexp - prods[i].prodb[j].f.e;
// spyglass enable_block W164a
          prod_shr           = barrelshift({prods[i].proda[j],4'h0}, delta);
          prod_sgn[i][j]     = {27{prods[i].prodb[j].f.sgn}} ^ {1'b0,prod_shr};
          prod_nan_ovf[i][j] = (!prods[i].prodb[j].f.zero) && (prods[i].prodb[j].f.e==8'hfe) && prods[i].proda[j][21];
        end
      end
    end
  end : sum_tree_PROC

  
  //
  // Second stage input, compute sum
  //
  always_comb 
  begin : prod_in_PROC
    prod_inl = '0;
    prod_inc = '0;
    prod_inh = '0;
    for (int i = 0; i < ISIZE; i++) 
    begin
      for (int j = 0; j < ISIZE; j++) 
      begin
        if ((!NPU_HAS_FLOAT) || (!isfp(mpycfg)))
        begin
          // invert upper bit for sign extension addition trick
          prod_inl[i][j]      = {~prods[i].proda[j][16],prods[i].proda[j][15:0]};
          prod_inh[i][j]      = {~prods[i].prodb[j].i[16],prods[i].prodb[j].i[15:0]};
        end
        else
        begin
          // invert upper bit for sign extension addition trick
          // split addition over 2 sum trees
          prod_inl[i][j]      = prods[i].prodb[j].f.zero ? '0 : {1'b0,prod_sgn[i][j][15:0]};
          prod_inc[i][j]      = (~prods[i].prodb[j].f.zero) & prods[i].prodb[j].f.sgn;
          prod_inh[i][j]      = prods[i].prodb[j].f.zero ? 17'h0400 : {6'b0,~prod_sgn[i][j][26],prod_sgn[i][j][25:16]};
        end
      end
    end
  end : prod_in_PROC


  //
  // Compute sum
  //
  // outputs: sums_nxt
  always_comb
  begin : sum_PROC
    sums_nxt = '0;
    for (int i = 0; i < ISIZE; i++)
    begin
      if (NPU_HAS_FLOAT && isfp(mpycfg))
      begin
        sums_nxt[i].maxexp    = prods[i].maxexp;
        sums_nxt[i].nan       = prods[i].nan;
      end
      for (int j = 0; j < ISIZE; j++) 
      begin
        sums_nxt[i].nan |= (NPU_HAS_FLOAT && prod_nan_ovf[i][j]);
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
        sums_nxt[i].sum_lower += prod_inl[i][j] + prod_inc[i][j];
        sums_nxt[i].sum_upper += prod_inh[i][j];
// spyglass enable_block W164a
      end
    end
  end : sum_PROC


  //
  // Output registers
  //
  always_ff @(posedge clk or posedge rst_a)
  begin : state_PROC
    if (rst_a == 1'b1)
    begin
      sums_r <= '0;
    end
    else if (sum_en)
    begin
      sums_r <= sums_nxt;
    end
  end : state_PROC
  
endmodule : npu_conv_mpy_sum
