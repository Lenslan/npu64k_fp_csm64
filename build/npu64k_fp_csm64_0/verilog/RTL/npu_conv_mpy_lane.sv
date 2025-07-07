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
// convolution multiplier array module
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv npu_conv_types.sv npu_conv_mpy_mul.sv npu_conv_mpy_sum.sv npu_conv_mpy_lane.sv npu_conv_mpy_prim.sv npu_conv_mpy_acc.sv
// analyze -format sverilog [list ../../../shared/RTL/npu_types.sv ../npu_conv_types.sv ../npu_conv_mpy_mul.sv ../npu_conv_mpy_sum.sv ../npu_conv_mpy_lane.sv ../npu_conv_mpy_prim.sv ../npu_conv_mpy_acc.sv]
//
`include "npu_defines.v"

module npu_conv_mpy_lane
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter logic NPU_HAS_FLOAT=1) (
  // clock and reset
  input  logic                                 clk,     // Clock, all logic clocked at posedge
  input  logic                                 rst_a,   // Asynchronous reset, active high
  ///////////////////////
  // configuration
  input  mpy_cfg_t                             mpy_cfg,   // Multiplier config
  // pipeline enable
  input  logic                                 mpy_en,    // multiplier output register enable
  input  logic                                 sum_en,    // Enable register
  input  logic                                 sn_en,     // Enable register
  input  logic                                 norm_en,   // Enable register
  input  logic      [1:0]                      acc_en,    // Accumulator register enable
  // data inputs
  input  mpy_fm_t   [ISIZE-1:0][ISIZE-1:0]     mpy_a,     // feature-maps
  input  mpy_cf_t   [ISIZE-1:0][ISIZE-1:0]     mpy_b,     // coefficients
  input  logic                                 a_init,    // Reinitialize the accumulator
  input  ixacc_t    [1:0]                      ar_acc,    // Input accumulators
  // result
  output ixacc_t    [1:0]                      aw_acc     // Output accumulators
  );
  
  // local wires
  logic                   a_init_nomerge_r;             // Buffered init bit
  out_prods_t [ISIZE-1:0] prods;
  out_sums_t  [ISIZE-1:0] sums;
  out_sns_t   [ISIZE-1:0] sns;
  out_norms_t [ISIZE-1:0] norms;

  
  //initial begin
  //  $vcdpluson(); 
  //end 
   
  //
  // Buffer controls
  //
  // outputs: a_init_nomerge_r
  always_ff @(posedge clk or posedge rst_a) 
  begin : ctrl_reg_PROC
    if (rst_a == 1'b1) 
    begin
      a_init_nomerge_r  <= 1'b0;
    end
    else 
    begin
      if (norm_en) 
      begin
        a_init_nomerge_r <= a_init;
      end
    end
  end : ctrl_reg_PROC
  
  
  // multipolier stage
  npu_conv_mpy_mul #(.NPU_HAS_FLOAT(NPU_HAS_FLOAT)) 
  u_mul_inst
  (
   .clk    ( clk     ),
   .rst_a  ( rst_a   ),
   .mpy_en ( mpy_en  ),
   .mpy_a  ( mpy_a   ),
   .mpy_b  ( mpy_b   ),
   .prods  ( prods   ),
   .mpycfg ( mpy_cfg )
  );

  // summation stage
  npu_conv_mpy_sum #(.NPU_HAS_FLOAT(NPU_HAS_FLOAT)) 
  u_sum_inst
  (
   .clk    ( clk     ),
   .rst_a  ( rst_a   ),
   .sum_en ( sum_en  ),
   .mpycfg ( mpy_cfg ),
   .prods  ( prods   ),
   .sums   ( sums    )
  );

  // final sum stage
  npu_conv_mpy_sn #(.NPU_HAS_FLOAT(NPU_HAS_FLOAT)) 
  u_sn_inst
  (
   .clk       ( clk     ),
   .rst_a     ( rst_a   ),
   .sn_en     ( sn_en   ),
   .mpycfg    ( mpy_cfg ),
   .sums_in   ( sums    ),
   .sns_out   ( sns     )
  );
  
  // normalization stage
  npu_conv_mpy_norm #(.NPU_HAS_FLOAT(NPU_HAS_FLOAT))  
  u_norm_inst
  (
   .clk       ( clk     ),
   .rst_a     ( rst_a   ),
   .norm_en   ( norm_en ),
   .mpycfg    ( mpy_cfg ),
   .sns_in    ( sns     ),
   .norms_out ( norms   )
  );
  
  // accumulate stage
  npu_conv_mpy_acc #(.NPU_HAS_FLOAT(NPU_HAS_FLOAT)) 
  u_acc_inst
  (
   .clk        ( clk              ),
   .rst_a      ( rst_a            ),
   .a_init     ( a_init_nomerge_r ),
   .ar_acc     ( ar_acc           ),
   .mpycfg     ( mpy_cfg          ),
   .acc_en     ( acc_en           ),
   .norms      ( norms            ),
   .acc_out    ( aw_acc           )
   );

endmodule : npu_conv_mpy_lane
