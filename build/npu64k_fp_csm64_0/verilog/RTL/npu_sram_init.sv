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
// Parameterizable npu sram initialization
// vcs -sverilog npu_types.sv npu_ecc_types.sv npu_sram_init.sv
// analyze -format sverilog [list ../npu_types.sv ../npu_ecc_types.sv ../npu_sram_init.sv]
//
 
module npu_sram_init
  import npu_types::*;
  #(
    parameter int ADDR_W = 16,      // address width
    parameter int NUM_BANKS = 32,   // number of sram banks
    parameter MEM_MODE = 0          // 1:AM, 0:VM    
    )
  (
   input  logic                                     clk,           // clock, all logic clocked at posedge
   input  logic                                     rst_a,         // asynchronous reset, active high
   input  logic                                     sram_init,     // sram initialization enable signal
   output logic                                     sram_init_end, // sram initialization end signal
   output logic [ADDR_W-1:0]                        cmd_addr       // write command address
   );

  // Local parameter 
  typedef enum logic [2:0] {
    IDLE = 3'b001, // idle state
    PROC = 3'b010, // read state
    DONE = 3'b100  // write state
  } state_t;
  localparam int PORTS_WIDTH = $clog2(NUM_BANKS);
  localparam int VM_ADDR_W   = 10;
  localparam int VM_ADDR_MSB = VM_ADDR_W - 1;
  localparam int AM_ADDR_W   = 7;
  localparam int AM_ADDR_MSB = AM_ADDR_W - 1;
  localparam int INT_ADDR_W   = (MEM_MODE) ?  AM_ADDR_W : VM_ADDR_W;
  localparam int INT_ADDR_MSB = (MEM_MODE) ?  AM_ADDR_MSB : VM_ADDR_MSB;
  
  state_t                init_state_r;
  state_t                init_state_nxt;
  logic                  init_state_en;
  logic [INT_ADDR_MSB:0] init_addr_r;
  logic [INT_ADDR_MSB:0] init_addr_nxt; 
  logic                  init_addr_en;

  assign init_state_en = |(init_state_r^init_state_nxt);
  always_ff @(posedge clk or posedge rst_a)
  begin : init_state_reg_PROC
    if(rst_a == 1'b1)
    begin
      init_state_r <= IDLE;  
    end
    else if (init_state_en)
    begin
     init_state_r <= init_state_nxt;   
    end    
  end : init_state_reg_PROC

  always_comb
  begin : init_state_PROC
    init_state_nxt = init_state_r;
    init_addr_nxt = init_addr_r;
    init_addr_en = 1'b0;
    sram_init_end = 1'b0;
    cmd_addr = 'b0;
// spyglass disable_block W164b
// SMD: LHS large than RHS
// SJ: Has default value, and RHS is the real size
    cmd_addr = init_addr_r[INT_ADDR_MSB:0] << PORTS_WIDTH;
// spyglass enable_block W164b
    case(init_state_r)
    IDLE: 
    begin
      init_addr_nxt = '0;
      if(sram_init)
      begin    
        init_state_nxt = PROC;
      end
    end
    PROC: 
    begin
      init_addr_en = 1'b1;  
      if (&init_addr_r)
      begin
        init_state_nxt = DONE;
        init_addr_nxt = 'b0; 
      end
      else
      begin
        init_addr_nxt = init_addr_r + 1'b1; 
      end
    end    
    DONE: 
    begin
      if(~sram_init)
      begin
        init_state_nxt = IDLE;
      end
      sram_init_end = 1'b1;
    end
    default: 
    begin
      init_state_nxt = IDLE;
    end
    endcase
  end : init_state_PROC
  
  always_ff @(posedge clk or posedge rst_a)
  begin : init_addr_reg_PROC
    if(rst_a == 1'b1)
    begin
      init_addr_r <= 'b0;  
    end
    else if (init_addr_en)
    begin
     init_addr_r <= init_addr_nxt;   
    end    
  end : init_addr_reg_PROC
endmodule
