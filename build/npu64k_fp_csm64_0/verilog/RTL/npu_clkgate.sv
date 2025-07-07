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

`include "npu_defines.v"
`ifdef SYNTHESIS
  `ifdef NPU_FPGA_NOT_REPLACE_CLKGATE
    `define NPU_REPLACE_CLKGATE_disabled 1
  `elsif NPU_REPLACE_CLKGATE
    `define NPU_REPLACE_CLKGATE_enabled 1
  `endif
`endif

module npu_clkgate
  (
  input  logic clk_in,
  input  logic clock_enable,
  output logic clk_out
  );

`ifdef NPU_REPLACE_CLKGATE_enabled

  `CellLibraryClockGate clk_gate0 (.Q(clk_out), .CK(clk_in), .EN(clock_enable), .SE(1'b0) );

`else // Simulation model

// Note: This is a behavioral block that must be replaced before synthesis.
// The replaced block instantiates the proper clockgate cell of the technology
// library.

  logic latch;

  always @*
  begin : latch_PROC
    if (!clk_in)
    begin
      latch = clock_enable;
    end
  end : latch_PROC

  assign clk_out = clk_in & latch;

`endif

endmodule : npu_clkgate
