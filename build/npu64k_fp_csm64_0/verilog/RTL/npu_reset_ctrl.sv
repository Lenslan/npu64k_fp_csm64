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
// Reset controller
//
// This module provides synchronous de-assertion of the asynchronous reset
// input. This is to ensure that the global asynchronous reset meets the reset
// recovery time of the FFs to avoid metastability. The reset output is fully
// asynchronous in test mode since the FFs are bypassed
//

module npu_reset_ctrl
  (
   input  logic clk,            // clock
   input  logic rst_a,          // External reset
   output logic rst,            // Synchronized reset
   input  logic test_mode       // test mode to bypass FFs
   );

  logic rst_sync_n;

  // -------------------------------------------------------------------------
  // Synchronizing flip-flops (with async clear function)

  npu_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(1), .TMR_CDC(1)
  ) u_reset_ctrl_cdc_sync (
    .clk        (clk),
    .rst_a      (rst_a),
    .din        ({3{1'b1}}),
    .dout       (rst_sync_n)
  );

  // -------------------------------------------------------------------------
  // Bypass the synchronization when test_mode is asserted. This gives full
  // control on the reset pin to the tester.

  assign rst   = test_mode ?  rst_a : !rst_sync_n;
  //assign rst_n = test_mode ? !rst_a :  rst_sync_n;

endmodule
