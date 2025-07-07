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
 * Arbiter for trace SWE
 */

`include "npu_defines.v"

module npu_trace_arb
  #(
    parameter int NUM = 8, // number of input sources
    parameter int DW  = 32 // data width
    )
  (
   input  logic                   clk,                // clock
   input  logic                   rst_a,              // asynchronous reset, active high, synchronous deassertion
   input  logic [NUM-1:0]         in_valid,           // input is valid
   output logic [NUM-1:0]         in_accept,          // accept input
   input  logic [NUM-1:0][DW-1:0] in_data,            // input data
   output logic                   out_valid,          // output is valid
   output logic [DW-1:0]          out_data            // output data
   );
  // local types
  typedef enum logic [1:0] { state_idle, state_valid_hi, state_valid_lo} state_t;
  // local wires
  state_t                 fsm_state_r;      // FSM state
  state_t                 fsm_state_nxt;    // FSM next state
  logic                   fsm_state_en;     // FSM register enable
  logic                   valid_gate;       // gate input valid start
  logic [NUM-1:0]         valid_int;        // internal input valid
  logic [NUM-1:0]         accept_int;       // internal input accept start
  logic [NUM-1:0]         accept_end;       // input accept end
  logic [NUM-1:0]         sel_r;            // selected input
  logic [NUM-1:0]         sel_nxt;          // selected input next
  logic                   sel_en;           // selected input enable
  logic                   start_hs;         // start handshake
  logic                   start_hs_d1;      // start handshake with 1 cycle delay
  logic                   start_hs_d2;      // start handshake with 2 cycle delay
  logic                   start_hs_d3;      // start handshake with 3 cycle delay
  logic                   start_hs_d4;      // start handshake with 4 cycle delay
  logic                   start_hs_d5;      // start handshake with 5 cycle delay
  logic                   end_hs;           // end handshake
  logic                   end_hs_d1;        // end handshake with 1 cycle delay
  logic                   end_hs_d2;        // end handshake with 2 cycle delay
  logic                   end_hs_d3;        // end handshake with 3 cycle delay
  logic                   end_hs_d4;        // end handshake with 4 cycle delay
  logic                   end_hs_d5;        // end handshake with 5 cycle delay

  // simple assignments
  assign end_hs       = (fsm_state_r == state_valid_hi) && (|accept_end);
  assign valid_gate   = fsm_state_r == state_idle;
  assign valid_int    = {NUM{valid_gate}} & in_valid;
  assign sel_nxt      = valid_int & accept_int;
  assign start_hs     = (sel_nxt != '0);
  assign in_accept    = accept_end;

  npu_arb
  #(
    .NUM_REQ ( NUM )
  )
  u_in_valid_arb
  (
    .clk    ( clk              ),
    .rst_a  ( rst_a            ),
    .req    ( valid_int        ),
    .gnt    ( accept_int       ),
    .ok     ( 1'b1             )
  );

  // next state of FSM
  always_comb
  begin : fsm_nxt_PROC
    // default outputs
    fsm_state_en    = 1'b0;
    fsm_state_nxt   = state_idle;
    out_valid       = 1'b0;
    out_data        = '0;
    accept_end      = '0;
    sel_en          = 1'b0;
    // state dependent
    case (fsm_state_r)
      state_valid_hi:
        begin
          out_valid |= 1'b1;
          for (int i = 0; i < NUM; i++)
          begin
            if (sel_r[i])
            begin
              out_data      |= in_data[i];
              accept_end[i] |= start_hs_d5;
            end
          end
          if (start_hs_d5)
          begin
            fsm_state_en   = 1'b1;
            fsm_state_nxt  = state_valid_lo;
          end
        end
      state_valid_lo:
        // keep out_valid low for 5 cycles
        begin
          if (end_hs_d5)
          begin
            fsm_state_en  = 1'b1;
            fsm_state_nxt = state_idle;
          end
        end
      default: // state_idle
        begin
          if (start_hs)
          begin
            sel_en  = 1'b1;
            fsm_state_en  = 1'b1;
            fsm_state_nxt = state_valid_hi;
          end
        end
    endcase // case (fsm_state_r)
  end :  fsm_nxt_PROC


  // registers
  // outputs: 
  always_ff @(posedge clk or posedge rst_a)
  begin : v_reg_PROC
    if (rst_a == 1'b1)
    begin
      fsm_state_r <= state_idle;
      start_hs_d1 <= 1'b0;
      start_hs_d2 <= 1'b0;
      start_hs_d3 <= 1'b0;
      start_hs_d4 <= 1'b0;
      start_hs_d5 <= 1'b0;
      end_hs_d1   <= 1'b0;
      end_hs_d2   <= 1'b0;
      end_hs_d3   <= 1'b0;
      end_hs_d4   <= 1'b0;
      end_hs_d5   <= 1'b0;
      sel_r       <= '0;
    end
    else
    begin
      if (fsm_state_en)
      begin
        fsm_state_r <= fsm_state_nxt;
      end
      start_hs_d1 <= start_hs;
      start_hs_d2 <= start_hs_d1;
      start_hs_d3 <= start_hs_d2;
      start_hs_d4 <= start_hs_d3;
      start_hs_d5 <= start_hs_d4;
      end_hs_d1   <= end_hs;
      end_hs_d2   <= end_hs_d1;
      end_hs_d3   <= end_hs_d2;
      end_hs_d4   <= end_hs_d3;
      end_hs_d5   <= end_hs_d4;
      if (sel_en)
      begin
        sel_r     <= sel_nxt;
      end
    end
  end : v_reg_PROC

endmodule : npu_trace_arb
