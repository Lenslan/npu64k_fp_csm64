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
// File implementing a parameterizable round-robin arbiter
//

module npu_arb
  #(
    parameter int NUM_REQ = 16                // number of requesters
    )
  (
   input  logic               clk,   // clock
   input  logic               rst_a, // asynchronous reset, active high, synchornous deassertion
   input  logic [NUM_REQ-1:0] req,   // request input vector
   output logic [NUM_REQ-1:0] gnt,   // grant output vector
   input  logic               ok     // next arbitration
   );
  // local variables
  logic                     gnt_en;  // grant register enable
  logic  [NUM_REQ-1:0]      gnt_r;   // previous grant
  logic  [NUM_REQ-1:0]      gnt_nxt; // next grant state
  logic                     ok_r;    // enable arb in next cycle
  
  // actual grant
  assign gnt    = ok_r ? gnt_nxt : gnt_r;
  assign gnt_en = ok_r & ((req & gnt_nxt) != 0);
  
  // Store grant to keep track of round-robin scheme
  // outputs: gnt_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : state_reg_PROC
    if (rst_a == 1'b1)
    begin
      ok_r   <= 1'b0;
      gnt_r  <= {NUM_REQ{1'b0}};
    end
    else 
    begin
      ok_r   <= ok;
      if (gnt_en) 
      begin
        gnt_r <= gnt_nxt;
      end
    end
  end : state_reg_PROC
  
  // arbitration
  // outputs: gnt_nxt
  always_comb
  begin : gnt_PROC
    logic [NUM_REQ-1:0][1:0]         prio;    // array of priorities
    logic                            flg;     // temperature code flag
    logic [NUM_REQ-1:0][NUM_REQ-1:0] res;     // priority compare table
    // create priority table
    flg = 1'b0;
    for (int i = 0; i < NUM_REQ; i++) 
    begin
      prio[i][1] = req[i];   // request is priority msb
      prio[i][0] = flg;      // temperature code is priority lsb
      flg       |= gnt_r[i]; // update temperature code
    end
    // search for highest priority
    for (int i = 0; i < NUM_REQ; i = i + 1) 
    begin
      // set diagonal to 1
      res[i][i] = 1'b1;
      // greater than equal for half of the matrix, less than for other half
      for (int j = i + 1; j < NUM_REQ; j = j + 1) 
      begin
        res[i][j] = (prio[i] >= prio[j]);
        res[j][i] = !res[i][j];
      end
      // grant if entire row is 1
      gnt_nxt[i] = &res[i];
    end
  end : gnt_PROC
  
endmodule : npu_arb
