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

// Initiator part of APB async bridge

`include "npu_apb_macros.svh"

module npu_apb_bridge_ini
#(
  parameter int ADDR_WIDTH   = 32,  // apb address width
  parameter int DATA_WIDTH   = 32   // apb data width
)(
  input logic pclk,            // APB clock
  input logic rst_a,           // async reset
  input logic tgt_pwr_dwn_a,   // other side is power down
  input logic test_mode,       // test mode enable
  `APBSLV(ADDR_WIDTH,DATA_WIDTH,ini_),
  `APBASYNCINI(ADDR_WIDTH,DATA_WIDTH,brg_)
  );
  typedef enum logic [1:0] { state_idle_e, state_setup_e, state_access_e, state_err_e } state_t;
  //  local wires
  logic                    sync_rst;
  logic                    pwr_dwn;
  logic                    brg_ack;
  logic                    den;
  logic   [ADDR_WIDTH-1:0] addr_r;
  logic                    write_r;
  logic   [DATA_WIDTH-1:0] wdata_r;
  logic                    state_en;
  state_t                  state_r;
  state_t                  state_nxt;
  logic                    breq_r;
  logic                    int_pslverr;
  

  //
  // Simple assignments
  //
  assign brg_req_a                = breq_r;
  assign brg_pcmd                 = {addr_r,write_r,wdata_r};
  assign {ini_prdata,int_pslverr} = brg_presp;

  
  //  
  // Local reset synchronizer
  //
  npu_reset_ctrl 
  u_reset_ctrl_main
  (
   .clk        ( pclk      ),
   .rst_a      ( rst_a     ),
   .test_mode  ( test_mode ),
   .rst        ( sync_rst  )
  );

  
  //
  // Synchronize power-down input
  //
  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS(2), 
    .WIDTH(1),
    .TMR_CDC(0)
  ) 
  u_event_cdc_sync 
  (
   .clk        ( pclk   ),
   .rst_a      ( sync_rst   ),
   .din        ( tgt_pwr_dwn_a ),
   .dout       ( pwr_dwn       )
  );

  
  //
  // Synchronize acknowledge
  //
  npu_cdc_sync 
  #(
    .SYNC_FF_LEVELS(2), 
    .WIDTH(1),
    .TMR_CDC(0)
  ) 
  u_ack_cdc_sync 
  (
   .clk        ( pclk     ),
   .rst_a      ( sync_rst  ),
   .din        ( brg_ack_a ),
   .dout       ( brg_ack   )
  );


  //
  // Next state and outputs
  //
  // outputs: state_en, state_nxt, den, ini_pready, ini_pslverr
  always_comb
  begin : nxt_PROC
    // default outputs
    state_en    = 1'b0;
    den         = 1'b0;
    state_nxt   = state_idle_e;
    ini_pready  = 1'b0;
    ini_pslverr = int_pslverr;
    // state dependent
    case (state_r)
    state_err_e:
      begin
        // power-down returns slv error
        state_en    = 1'b1;
        ini_pslverr = 1'b1;
        ini_pready  = 1'b1;        
      end
    state_access_e:
      begin
        // do handshake, wait for ack
        state_nxt = state_idle_e;
        if (pwr_dwn)
        begin
          state_en  = 1'b1;
          state_nxt = state_err_e;
        end
        else if (brg_ack)
        begin
          state_en   = 1'b1;
          ini_pready = 1'b1;
        end
      end
    state_setup_e:
      begin
        // wait until previous 4phase handshake has completed
        state_nxt = state_access_e;
        if (pwr_dwn)
        begin
          state_en  = 1'b1;
          state_nxt = state_err_e;
        end
        else if (ini_penable & (~brg_ack))
        begin
          state_en = 1'b1;
        end
      end
    default: // idle
      begin
        state_nxt = state_setup_e;
        ini_pready = 1'b1;
        if (ini_psel)
        begin
          den      = 1'b1;
          state_en = 1'b1;
        end
      end
    endcase // case (state_r)
  end : nxt_PROC

  
  //
  // State
  //
  always @(posedge pclk or posedge sync_rst)
  begin : state_reg_PROC
    if (sync_rst)
    begin
      breq_r  <= 1'b0;
      addr_r  <= '0;
      write_r <= '0;
      wdata_r <= '0;
      state_r <= state_idle_e;
    end
    else
    begin
      if (den)
      begin
// spyglass disable_block W164b
// SMD: Width mismatch
// SJ: Addr is MAX size which is trunk
        addr_r  <= ini_paddr;
// spyglass enable_block W164b
        write_r <= ini_pwrite;
        wdata_r <= ini_pwdata;
      end
      if (state_en)
      begin
        breq_r  <= state_nxt == state_access_e;
        state_r <= state_nxt;
      end
    end
  end : state_reg_PROC
  
endmodule : npu_apb_bridge_ini
