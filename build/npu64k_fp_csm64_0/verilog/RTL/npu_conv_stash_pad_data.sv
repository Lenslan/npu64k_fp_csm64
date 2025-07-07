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
// convolution stash module padding
//  vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv npu_conv_types.sv npu_conv_stash_pad_data.sv
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../npu_conv_types.sv ../npu_conv_stash_pad_data.sv"

`include "npu_defines.v"
`include "npu_axi_macros.svh"
`include "npu_vm_macros.svh"
`include "npu_conv_macros.svh"

module npu_conv_stash_pad_data
  import npu_types::*;
  import npu_conv_types::*;
  (
   // Clock and reset
   input  logic                    clk,                       // Clock, all logic clocked at posedge
   input  logic                    rst_a,                     // Asynchronous reset, active high
   // HLAPI interface
   input  logic                    hlapi_valid,               // Request new HLAPI start
   output logic                    hlapi_accept,              // Acknowledge new HLAPI start
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore
   input  conv_hlapi_i_t           hlapi_i,                   // HLAPI parameters
   // Pad load input interface
   input  logic                    pad_valid,                 // Pad information is valid
   output logic                    pad_accept,                // Pad information is accepted
   input  ixpix_t        [3:0]     pad_data,                  // Pad information
   // Vector input interface
   input  logic                    vector_valid,              // Vector information is valid
   output logic                    vector_accept,             // Vector information is accepted
   input  vm_vector_t              vector_data,               // Vector information
// spyglass enable_block W240
   // Stash output interface
   output logic                    stash_valid,               // Stash information is valid
   input  logic                    stash_accept,              // Stash information is accepted
   output stash_data_t             stash_data                 // Stash information
   );
  // local wires
  logic       pp_en;         // ping-pong enable
  logic       pp_r;          // ping-pong between even/odd
  logic       cf_en;         // config enable
  logic       cf_inn_r;      // two input channel groups
  logic       cf_dino_r;     // i32 input convolution
  logic       cf_inn_nxt;    // two input channel groups
  logic       cf_dino_nxt;   // i32 input convolution
  logic       busy_r;        // set if busy
  logic       busy_nxt;      // next busy state
  logic       dw_dbl;        // DW convolution enable fm16
  

  // next state and enable
  assign dw_dbl       = (hlapi_i.fm_cfg==fm_cfg_16b_e ||
                         hlapi_i.fm_cfg==fm_cfg_fp16_e ||
                         hlapi_i.fm_cfg==fm_cfg_bf16_e) && 
                        (hlapi_i.conv_mode == `NINO(conv_mode_3x3dws1) || 
                         hlapi_i.conv_mode == `NINO(conv_mode_8x1dws1) ||
                         hlapi_i.conv_mode == `NINO(conv_mode_2x3dws2) || 
                         hlapi_i.conv_mode == `NINO(conv_mode_3x3dws1dl2));
  assign cf_en        = hlapi_valid & hlapi_accept;
  assign cf_inn_nxt   = hlapi_i.iter[6][1] || dw_dbl;
  assign cf_dino_nxt  = hlapi_i.conv_mode == `DINO(conv_mode_1x1);
  assign busy_nxt     = (busy_r & ~(vector_valid & vector_accept & vector_data.pad.flast)) | (hlapi_valid & hlapi_accept);
  assign hlapi_accept = ~busy_r;
  assign pp_en        = vector_valid & vector_accept;

  
  // flow control
  assign stash_valid   = pad_valid & vector_valid & busy_r;
  assign vector_accept = pad_valid & stash_accept & busy_r;
  assign pad_accept    = vector_valid & stash_accept & vector_data.pad.clast & busy_r;

  
  // store config parameters
  // outputs: busy_r, cf_inn_r, cf_dino_r, pp_r
  always_ff @(posedge clk or posedge rst_a)
  begin : cf_reg_PROC
    if (rst_a == 1'b1)
    begin
      busy_r    <= 1'b0;
      pp_r      <= 1'b0;
      cf_inn_r  <= 1'b0;
      cf_dino_r <= 1'b0;
    end
    else 
    begin
      busy_r    <= busy_nxt;
      if (pp_en || cf_en)
      begin
        pp_r <= (cf_en ? 1'b0 : ~pp_r);
      end
      if (cf_en)
      begin
        cf_inn_r  <= cf_inn_nxt;
        cf_dino_r <= cf_dino_nxt;
      end
    end
  end : cf_reg_PROC

  
  // pad the output
  // output: stash_data
generate
  always_comb
  begin : pad_PROC
    ixpix_t [1:0] pv;
    // select padding values
    case ({cf_inn_r, cf_dino_r})
    2'b11:
      begin
        // 2*i32
        pv[0] = pp_r ? pad_data[2] : pad_data[0];
        pv[1] = pp_r ? pad_data[3] : pad_data[1];
      end
    2'b10:
      begin
        // 2*i16
        pv[0] = pp_r ? pad_data[1] : pad_data[0];
        pv[1] = pv[0];
      end
    2'b01:
      begin
        // 1*i32
        pv[0] = pad_data[0];
        pv[1] = pad_data[1];
      end
    default: //2'b00:
      begin
        // 1*i16
        pv[0] = pad_data[0];
        pv[1] = pv[0];
      end
    endcase // case ({cf_inn_r, cf_dino_r})
    // actual padding
    stash_data = vector_data.data;
    for (int v = 0; v < VSIZE; v++)
    begin
      for (int i = 0; i < 4; i++)
      begin
        if (vector_data.pad.pad[v][i])
        begin
          stash_data[v][i*4+:4] = pv[0][i*4+:4];
        end
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression
//SJ :Ignore
        if (vector_data.pad.pad[v+VSIZE][i])
        begin
          stash_data[v+VSIZE][i*4+:4] = pv[1][i*4+:4];
        end
// spyglass enable_block SelfDeterminedExpr-ML
      end
    end
  end : pad_PROC
endgenerate

endmodule : npu_conv_stash_pad_data
