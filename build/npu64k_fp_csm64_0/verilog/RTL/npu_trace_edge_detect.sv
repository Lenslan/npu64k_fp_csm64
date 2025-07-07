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

/*
 * Detect rising edge for trace valid
 */

`include "npu_defines.v"

module npu_trace_edge_detect
  (
   input  logic          clk,                // clock
   input  logic          rst_a,              // asynchronous reset, active high, synchronous deassertion
   input  logic          din,                // input data
   output logic          dout                // output data
   );
  // local wires
  logic           din_r;   // delayed input

  // simple assignments
  assign dout = ({din_r, din} == 2'b01);

  // registers
  // outputs: 
  always_ff @(posedge clk or posedge rst_a)
  begin : reg_PROC
    if (rst_a == 1'b1)
    begin
      din_r      <= 1'b0;
    end
    else
    begin
      din_r      <= din;
    end
  end : reg_PROC

endmodule : npu_trace_edge_detect
