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

`include "npu_apb_macros.svh"

module arct_apb_slice
  #( parameter int AW = 32 )
 (
  input  logic                            clk,                    // debug apb clock
  input  logic                            rst_a,                  // debug apb asnyc reset, active low
  input  logic                            test_mode,              // disable reset sync in tst mode
  `APBSLV(AW,32,i_),
  `APBMST(AW,32,o_)
  );
  // state type, [0] = output select, [1] = output enable, [2] = input ready
  typedef enum logic [3:0] {state_idle_e=4'b0100, state_sel_e=4'b0001, state_en_e=4'b0011, state_rdy_e=4'b1100} state_t;
  // local wires
  logic            rst;        // synchronous reset
  state_t          state_r;    // FSM state
  state_t          state_nxt;
  logic            fen;        // forward enable
  logic   [AW-1:2] paddr_r;    // forward registers
  logic            pwrite_r;
  logic   [31:0]   pwdata_r;
  logic            ben;        // backward enable
  logic   [31:0]   prdata_r;   // backward registers
  logic            pslverr_r;

  
  //
  // Reset sync
  //
  npu_reset_ctrl 
  u_sync_rst
  (
    .clk        ( clk       ),
    .rst_a      ( rst_a     ),
    .test_mode  ( test_mode ),
    .rst        ( rst       )
  );

  
  //
  // Simple assignments
  //
  assign o_psel    = state_r[0];
  assign o_penable = state_r[1];
  assign o_paddr   = paddr_r;
  assign o_pwrite  = pwrite_r;
  assign o_pwdata  = pwdata_r;
  assign i_pready  = state_r[2];
  assign i_prdata  = prdata_r;
  assign i_pslverr = pslverr_r;


  //
  // Next state
  //
  always_comb
  begin : nxt_PROC
    // default
    fen       = 1'b0;
    ben       = 1'b0;
    state_nxt = state_r;
    case (state_r)
    state_rdy_e:
      begin
        state_nxt = state_idle_e;
      end
    state_en_e:
      begin
        if (o_pready)
        begin
          ben       = 1'b1;
          state_nxt = state_rdy_e;
        end
      end
    state_sel_e:
      begin
        state_nxt = state_en_e;
      end
    default:
      begin
        if (i_psel)
        begin
          fen       = 1'b1;
          state_nxt = state_sel_e;
        end
      end
    endcase // case (state_r)
  end : nxt_PROC

  
  //
  // state
  //
// spyglass disable_block Reset_check07
//SMD:Reset is driven by comb logic
//SJ :Reset Control TMR_CDC is not recongnized by spyglass
  always_ff @(posedge clk or posedge rst)
  begin : reg_PROC
    if (rst == 1'b1)
    begin
      state_r   <= state_idle_e;
      paddr_r   <= '0;
      pwrite_r  <= '0;
      pwdata_r  <= '0;
      prdata_r  <= '0;
      pslverr_r <= '0;
    end
    else 
    begin
      state_r <= state_nxt;
      if (fen)
      begin
        paddr_r   <= i_paddr;
        pwrite_r  <= i_pwrite;
        pwdata_r  <= i_pwdata;
      end
      if (ben)
      begin
        prdata_r  <= o_prdata;
        pslverr_r <= o_pslverr;
      end
    end
  end : reg_PROC
// spyglass enable_block Reset_check07
  
endmodule : arct_apb_slice

