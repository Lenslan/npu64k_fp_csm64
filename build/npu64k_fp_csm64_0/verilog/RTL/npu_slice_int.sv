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
// File implementing a parameterizable synchronous SLICE
//
`include "npu_defines.v"

module npu_slice_int 
 #(
    parameter int DWIDTH = 4              // the bit per element in the SLICE
  )
 (input  logic              clk,          // clock
  input  logic              rst_a,        // asynchronous reset, active high, synchronous deassertion
  input  logic              valid_write,  // input data valid
  output logic              accept_write, // accept input data
  input  logic [DWIDTH-1:0] data_write,   // input data
  output logic              valid_read,   // output data valid
  input  logic              accept_read,  // accept output data
  output logic [DWIDTH-1:0] data_read);   // output data
  // local wires
  logic              val_r;   // valid bit
  logic              val_nxt; // next state
  logic [DWIDTH-1:0] data_r;  // data
  logic              data_en; // data enable

  // simple assignments
  assign accept_write = accept_read | (~val_r);
  assign valid_read   = val_r;
  assign data_en      = valid_write & accept_write;
  assign val_nxt      = (val_r & (~accept_write)) | valid_write;
  assign data_read    = data_r;

  // registers
  // outputs: val_r, data_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : vreg_PROC
    if (rst_a == 1'b1)
    begin
      val_r    <= 1'b0;
    end
    else
    begin
      val_r    <= val_nxt;
    end
  end : vreg_PROC

  if (`NPU_L0_GATE_EN && (DWIDTH >= `NPU_L0_GATE_THRESH))
  begin : arch_gate_GEN
    logic clk_gated;
    npu_clkgate 
    gate_inst
      (
       .clk_in       ( clk       ),
       .clock_enable ( data_en   ),
       .clk_out      ( clk_gated )
       );
  end : arch_gate_GEN
  else
  begin : infer_gate_GEN
    always_ff @(posedge clk or
                posedge rst_a)
    begin : dreg_PROC
      if (rst_a == 1'b1)
      begin
        data_r   <= {DWIDTH{1'b0}};
      end
      else
      begin
        if (data_en)
        begin
          data_r <= data_write;
        end
      end
    end : dreg_PROC
  end : infer_gate_GEN

endmodule : npu_slice_int
