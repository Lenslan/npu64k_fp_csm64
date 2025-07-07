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
 * Skid buffer, isolates output accept and stall signals
 */
//POST_PROCESS { prefix: "//D:", wire_prefix:"t_",  ecc:false, edc: { suffix: "auto", clk: "clk_edc", rst: "rst_a", ports: [ "input [1:0] safety_diag_inject_edc,", "input [63:0] error_mask,", "input [63:0] valid_mask,", ], change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, encode_reset: true, error_signal:"%m_edc_err",  delegate:true},edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2} }


`include "npu_defines.v"

module npu_skid
  #(
    parameter int W = 8, // data width
    parameter int D = 1  // depth
    )
  (
   input  logic              clk,          // clock
   input  logic              rst_a,        // asynchronous reset, active high, synchronous deassertion
   input  logic              in_valid,     // input is valid
   output logic              in_accept,    // accept input
   input  logic [W-1:0]      in_data,      // data to be transferred
   output logic              int_valid,    // internal state is valid
   output logic              out_valid,    // output is valid
   input  logic              out_accept,   // output is accepted
   output logic [W-1:0]      out_data      // data to be transferred
   );
  // local wires
  logic                en;       // registre enable
  logic [D-1:0]        val_r;    // skid buffer valid
  logic [D-1:0][W-1:0] data_r;   // actual data
  logic [D-1:0]        val_nxt;  // skid buffer valid
  logic [D-1:0][W-1:0] data_nxt; // next data state

  // simple assignments
  assign in_accept = ~val_r[D-1];
  assign out_data  = val_r[0] ? data_r[0] : in_data;
  assign out_valid = val_r[0] | in_valid;
  assign int_valid = |val_r;

  // next state
  // outputs: en, val_nxt, data_nxt
  always_comb
  begin : nxt_PROC
    logic [D-1:0] xr;
    logic [D-1:0] val_new;
    // default
    en       = 1'b0;
    val_nxt  = val_r;
    data_nxt = data_r;
    if (val_r[0] && out_accept)
    begin
      // pop from queue
      en       = 1'b1;
      val_nxt  = val_nxt >> 1;
      data_nxt = data_nxt >> W;
    end
// spyglass disable_block W164a
// SMD:Width mismatch
// SJ :Intended to through out MSB
    val_new    = {val_nxt,1'b1};
// spyglass enable_block W164a
    xr         = val_new ^ val_nxt;
    if (in_valid & (~val_r[D-1]) & (val_r[0] | (~out_accept)))
    begin
      // push to queue if not full and output stalls or not empty
      en       = 1'b1;
      val_nxt  = val_new;
      for (int i = 0; i < D; i++)
      begin
        if (xr[i])
        begin
          data_nxt[i] = in_data;
        end
      end
    end
  end : nxt_PROC

  
  // next state
  // outputs: val_r
  always_ff @(posedge clk or posedge rst_a)
  begin : v_reg_PROC
    if (rst_a == 1'b1)
    begin
      val_r      <= 'd0;
    end
    else if (en)
    begin
      val_r      <= val_nxt;
    end
  end : v_reg_PROC

  // next data
  // outputs: data_r
  always_ff @(posedge clk or posedge rst_a)
  begin : d_reg_PROC
    if (rst_a == 1'b1)
    begin
      data_r <= '0;
    end
    else
    begin
      // spyglass disable_block FlopEConst
      //SMD:Enable pin tie 0
      //SJ :idma AM output tie 0
      if (en)
      begin
        data_r <= data_nxt;
      end
      // spyglass enable_block FlopEConst
    end
  end : d_reg_PROC

endmodule : npu_skid
