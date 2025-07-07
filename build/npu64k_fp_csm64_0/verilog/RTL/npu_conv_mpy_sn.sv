
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

module npu_conv_mpy_sn
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter logic NPU_HAS_FLOAT=1)
  (

   input  logic                          clk,                 // Clock, all logic clocked at posedge
   input  logic                          rst_a,               // Asynchronous reset, active high
// spyglass disable_block W240
//SMD:Unread input sum_en
//SJ :Read in config when NPU_L0_GATE_EN == 0, can be ignored in other config
   input  logic                          sn_en,              // Enable register
   input  mpy_cfg_t                      mpycfg,
// spyglass enable_block W240
   input  out_sums_t  [ISIZE-1:0]        sums_in,            // sum inputs
   output out_sns_t   [ISIZE-1:0]        sns_out             // final sum output 0
   );
  out_sns_t   [ISIZE-1:0] sns_out_nxt;
  out_sns_t   [ISIZE-1:0] sns_out_r;  
  logic       [1:0]       dualcycle_op_r;
  logic                   fp;


  // simple assignments
  assign sns_out = sns_out_r;

  
  //
  // final sum
  //
  always_comb
  begin : logic_PROC    
    sns_out_nxt    = '0;
    
    for (int i = 0; i < ISIZE; i++)
    begin
      logic [30:0] a,b,c;
      logic [20:0] d,e,f;
      a = '0;
      b = '0;
      c = '0;
      d = '0;
      e = '0;
      f = '0;
      case (mpycfg)
      f_bfloat16_e,f_fp16_e:
        begin
          if (NPU_HAS_FLOAT)
          begin
            a |= {10'd0,sums_in[i].sum_lower};
            b |= {sums_in[i].sum_upper[14:0],16'h0};
            c |= 32'hc000_0000; // 16*(-1<<26)
          end
        end
      i_8b8b_e:
        begin
          a |= {10'h0,sums_in[i].sum_lower};  
          b |= {10'h0,sums_in[i].sum_upper};
          c |= 32'hffe0_0000;   // 16*(-1<<16)+16*(-1<<16)
        end
      i_16b8b_e: 
        begin
          a |= {10'h0,sums_in[i].sum_lower};         
          b |= {2'h0,sums_in[i].sum_upper,8'h0};         
          c |= 32'heff0_0000; // 16*(-1<<16)+16*(-1<<24)
        end
      i_8b16b_e:
        begin
          if (dualcycle_op_r[0]) 
          begin
            // lower coef first
            a |= {10'h0,sums_in[i].sum_lower};
            b |= {10'h0,sums_in[i].sum_upper};
            c |= 32'hffe0_0000; // 16*(-1<<16)+16*(-1<<16)
          end
          if (dualcycle_op_r[1])
          begin
            a |= {2'h0,sums_in[i].sum_lower,8'h0};
            b |= {2'h0,sums_in[i].sum_upper,8'h0};
            c |= 32'he000_0000; // 16*(-1<<24)+16*(-1<<24)
          end
        end
      i_16b16b_e:
        begin 
          if (dualcycle_op_r[0])
          begin
            a |= {10'h0,sums_in[i].sum_lower};         
            b |= {7'h0,sums_in[i].sum_upper[15:0],8'h0};
            c |= 32'h00f0_0000; // 16*(-1<<16)+16*(-1<<24), low part
            
            d |= {16'h0,sums_in[i].sum_upper[20:16]};
            e |= 32'hffff_ffef; // 16*(-1<<16)+16*(-1<<24), high part
          end
          if (dualcycle_op_r[1])
          begin
            a |= {7'h0,sums_in[i].sum_lower[15:0],8'h0};  
            b |= {7'h0,sums_in[i].sum_upper[7:0],16'h0};
            c |= 32'h0000_0000; // 16*(-1<<24)+16*(-1<<32), low part
            
            d |= {16'h0,sums_in[i].sum_lower[20:16]};
            e |= {8'h0,sums_in[i].sum_upper[20:8]};
            f |= 32'hffff_eff0; // 16*(-1<<24)+16*(-1<<32), high part
          end
        end
      default:
        begin  //      i_sparse_e:
          // two outputs per row even/odd
          a |= {10'h0,sums_in[i].sum_lower};               // sum even            
          c |= 32'hfff0_0000; // 16*(-1<<16)
          d |= sums_in[i].sum_upper;                       // sum odd
          f |= 32'hfff0_0000; // 16*(-1<<16)
        end
      endcase // case (mpy_cfg)

// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :No overflow
      sns_out_nxt[i].lo = a + b + c;
      sns_out_nxt[i].hi = d + e + f;
// spyglass enable_block W164a
      sns_out_nxt[i].maxexp = sums_in[i].maxexp;
      sns_out_nxt[i].nan    = sums_in[i].nan;
    end // for (int i = 0; i < ISIZE; i++)
  end : logic_PROC

  
  // output register
  always_ff @(posedge clk or posedge rst_a)
  begin : ff_PROC
    if (rst_a)
    begin
      sns_out_r      <= '0;
      dualcycle_op_r <= 2'b01;
    end
    else
    begin
      if (sn_en)
      begin
        sns_out_r    <= sns_out_nxt;
      end
      if (mpycfg==i_16b16b_e || mpycfg==i_8b16b_e)
      begin
        if (sn_en) 
        begin
          dualcycle_op_r <= ~dualcycle_op_r;
        end
      end
    end
  end : ff_PROC
  
endmodule : npu_conv_mpy_sn
