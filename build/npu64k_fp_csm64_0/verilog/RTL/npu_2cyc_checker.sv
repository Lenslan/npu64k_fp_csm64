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
// Multi-cycle path checker
//

module npu_2cyc_checker 
  #( 
     parameter int WIDTH = 1,
     parameter bit DISABLE_OPTION = 1'b0
   ) 
  (
// spyglass disable_block W240
//SMD:No unread signal
//SJ :clk rst_a and valid will be used in check config
   input  logic              clk,           // clock for checking
   input  logic              rst_a,         // reset for checking
   input  logic              valid,         // input data is valid
// spyglass enable_block W240
   input  logic [WIDTH-1:0]  data_in,       // input data
   output logic [WIDTH-1:0]  data_out       // output data
   );
  
`ifdef SYNTHESIS
  assign   data_out = data_in;
`else  
 `ifdef NO_2CYC_CHECKER
  assign   data_out = data_in;
 `else
// leda off
// LMD: turn Leda checking off
// LJ: this module contains special checker code that should be excepted from Synthesis and Leda checks

  
  // This signal is used to control the 2 cycle checker output by TB to prevent 'x' propagation 
  // to external signals. When this signal is 1, the checker output is same as the input.
  // default chekcer output 'x'
  logic checker_out_ctrl;
  assign checker_out_ctrl = DISABLE_OPTION;
  // Check 2-cycle timing paths: 
  // In the first cycle data_out is forced to X until the next clock cycle.
  // Only in the 2nd cycle data_out gets the value of data_in.
  assign data_out = (~checker_out_ctrl) & (~$stable(data_in,@(posedge clk))) & (rst_a == 1'b0) ? 'x : data_in;

  stable_check: assert property (@(posedge clk) disable iff (rst_a !== 1'b0) valid & ~$stable(data_in) |=> $stable(data_in))
    else      $error("[ERROR - %m]: Violation found \n");
 // leda on
 `endif
`endif

endmodule : npu_2cyc_checker
