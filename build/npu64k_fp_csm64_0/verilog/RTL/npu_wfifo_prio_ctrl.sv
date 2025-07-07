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

// This module is for generating per bank priority bits for FIFO output
//


`include "npu_defines.v"
module npu_wfifo_prio_ctrl
(
  // Clock and reset
  input  logic               clk,
  input  logic               rst_a,
  // FIFO priority
  input  logic               wfifo_raccept,
  input  logic               wfifo_rvalid,
  output logic               wfifo_prio
  );

  logic                      tim_en;
  logic    [2:0]             tim_r;
  logic    [2:0]             tim_nxt;

  assign tim_nxt    = wfifo_raccept ? '0 : tim_r + 'd1;
  assign tim_en     = wfifo_raccept | (wfifo_rvalid & (~tim_r[2]));
  assign wfifo_prio = tim_r[2];

  always_ff @(posedge clk or posedge rst_a)
  begin : tim_reg_PROC
    if (rst_a == 1'b1)
    begin
      tim_r       <= '0;
    end
    else if (tim_en)
    begin
      tim_r       <= tim_nxt;
    end
  end : tim_reg_PROC

endmodule : npu_wfifo_prio_ctrl
