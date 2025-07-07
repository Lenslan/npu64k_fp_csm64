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

// Level-1 clock gate (top-level architectural clock gating) used to save dynamic
// power when the component is idle by gatign the clock closer to the root of the
// clock tree

`include "npu_defines.v"

module npu_l1_clk_ctrl
  (
  input  logic clk_in,
  input  logic clock_enable,
  output logic clk_out
  );

`ifdef NPU_REMOVE_CLKGATE // L1 clock gate is removed from the design

  assign clk_out = clk_in;

`else // Specialized clock gate wrapper

  npu_clkgate
  u_npu_clkgate_inst (
    .clk_in(clk_in),
    .clock_enable(clock_enable),
    .clk_out(clk_out)
  );

`endif

endmodule : npu_l1_clk_ctrl
