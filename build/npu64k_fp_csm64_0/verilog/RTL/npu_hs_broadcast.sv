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
// Handshake broadcasting module
//

module npu_hs_broadcast
  #(parameter int  NUM = 1,                        // number of broadcasting channels
    parameter bit  CNS = 1'b0)                     // if true then conservative to avoid read-after-write hazard problems
  (
   //
   // Clock and reset
   //
   input  logic           clk,                     // clock, all logic clocked at posedge
   input  logic           rst_a,                   // asynchronous reset, active high
   //
   // Input handshakes
   //
   input  logic           hsi_valid,               // input is valid
   output logic           hsi_accept,              // input is accepted when all output handshakes complete  
   //
   // Output handshakes
   //
   output logic [NUM-1:0] hso_valid,               // input is valid
   input  logic [NUM-1:0] hso_accept               // input is accepted when all output handshakes complete  
  );
  // local wires
  logic [NUM-1:0] pending_r;    // if true then corresponding output hadshake is pending
  logic [NUM-1:0] pending_nxt;  // next state
  logic           en;

  // drive outputs
  assign hso_valid = pending_r;
  
  // determine next state
  // outputs: pending_nxt, hsi_accept, en
  always_comb
  begin : state_nxt_PROC
    // default next state
    pending_nxt = pending_r;
    hsi_accept  = 1'b0;
    en          = 1'b0;
    if (pending_r != {NUM{1'b0}})
    begin
      // wait for handshape on outputs
      pending_nxt = pending_nxt & ~hso_accept;
      hsi_accept  = pending_nxt == {NUM{1'b0}};
      en          = hso_accept != {NUM{1'b0}};
    end
    else if (hsi_valid & ((!CNS) | (&hso_accept)))
    begin
      // start new handshake
      pending_nxt = {NUM{1'b1}};
      en          = 1'b1;
    end
    // else retain state
  end : state_nxt_PROC

  // state register
  // outputs: pending_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : state_PROC
    if (rst_a == 1'b1)
    begin
      pending_r <= {NUM{1'b0}};
    end
    else if (en)
    begin
      pending_r <= pending_nxt;      
    end
  end : state_PROC
 
endmodule : npu_hs_broadcast
