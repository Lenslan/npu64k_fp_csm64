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
 NPU configurable iterator
 vcs -sverilog npu_types.sv npu_iterator.sv +define+ABV_ON
 */

module npu_iterator
  import npu_types::*;
  #(parameter int N = 4,  // number of nested loops
    parameter int S = 1   // number of step
   ) 
  (
   input  logic                    clk,      // clock
   input  logic                    rst_a,    // asynchronous reset, active high
   input  logic                    soft_rst, // soft reset of address generator
   input  logic                    in_req,   // start new iteration
   output logic                    in_ack,   // acknowledge start
   input  offset_t         [N-1:0] in_shp,   // shape of the iterator
   output logic                    it_req,   // iterator valid
   input  logic                    it_ack,   // iterator accept
   output logic     [S-1:0][N-1:0] it_first, // first bits
   output logic     [S-1:0][N-1:0] it_last,  // last bits
   output logic     [S-1:0]        it_vald   // step valid bits
   );
  // local wires
  offset_t [N-1:0] shp_r;     // shape register
  offset_t [N-1:0] shp_nxt;   // shape register next state
  logic            shp_en;    // enable shape register
  offset_t [N-1:0] state_r;   // iterator state
  offset_t [N-1:0] state_nxt; // next iterator state
  logic    [N-1:0] state_en;  // register enables
  logic    [N-1:0] en;        // intermediate unqualified enable
  logic            busy_r;    // asserted if busy
  logic            busy_nxt;  // next state of busy
  logic            lst;       // last

  // simple outputs
  assign in_ack   = ~busy_r;
  assign state_en = (it_req && it_ack) ? en : '0;
  assign shp_en   = in_req & in_ack;
  assign it_req   = busy_r;
  assign busy_nxt = ((in_req & in_ack) | (busy_r & (~(lst & it_ack)))) & ~soft_rst;
  

  //
  // subtract one from input shape, to make -1 relative, so we can compare to 0
  //
  always_comb
    begin : sub_PROC
      for (int n = 0; n < N; n++)
      begin
        shp_nxt[n] = in_shp[n] - 'sd1;
      end
    end : sub_PROC

  
  // drive outputs
  // outputs: it_first, it_last, it_vald, en, state_nxt
  always_comb
  begin : out_PROC
    logic            f;         // symbol flag to indicate update
    logic            vld;       // Valid iteration flag
    // default outputs
    state_nxt = state_r;
    it_first  = '0;
    it_last   = '0;
    en        = '0;
    it_vald   = '0;
    vld       = 1'b1;
    // check first and last flags and increment state
    for (int s = 0; s < S; s++)
    begin
      f = 1'b1;
      it_vald[s] = vld;
      for (int n = N-1; n >= 0; n--)
      begin
        it_first[s][n] = state_nxt[n] == shp_r[n];
        it_last[s][n]  = state_nxt[n] == '0;
        en[n]          = en[n] | f;
        if (f)
        begin
          if (it_last[s][n])
          begin
            // at end of axis, reinitialize counter and continue with next axis
            state_nxt[n] = shp_r[n];
          end
          else
          begin
            // not at end of axis, decrement
            state_nxt[n] = state_nxt[n] - 'sd1;
            f = 1'b0;
          end
        end
      end
      // Next is valid if current is not last
      vld &= it_last[s] != '1;
    end
    lst = ~vld;
  end : out_PROC

  // state
  // outputs: shp_r, state_r, busy_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : state_PROC
    if (rst_a == 1'b1)
    begin
      busy_r  <= 1'b0;
      shp_r   <= '0;
      state_r <= '0;
    end
    else
    begin
      busy_r <= busy_nxt;
      if (shp_en)
      begin
        shp_r <= shp_nxt;
      end
      for (int n = 0; n < N; n++)
      begin
        if (shp_en | state_en[n])
        begin
          state_r[n] <= shp_en ? shp_nxt[n] : state_nxt[n];
        end
      end
    end
  end : state_PROC

`ifdef ABV_ON
  //
  // Assertions
  //

  generate
    genvar gn;
    for (gn = 0; gn < N; gn = gn + 1)
    begin : gen_prop
      property prop_pos;
        @(posedge clk) disable iff (rst_a == 1'b1) in_req |-> in_shp[gn] > 0;
      endproperty : prop_pos

      assert property (prop_pos) else $fatal(1, "Error: iterator needs to be positive");
    end
  endgenerate
`endif

endmodule : npu_iterator
