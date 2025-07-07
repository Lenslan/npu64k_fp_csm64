/*
 * Copyright (C) 2021-2022 Synopsys, Inc. All rights reserved.
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
// File implementing a parameterizable synchronous FIFO
//


`include "npu_macros.svh"
`include "npu_defines.v"

module npu_fifo 
  #(
    parameter int SIZE   = 4,                            // the number of elements in the FIFO
    parameter int DWIDTH = 4,                            // the bit per element in the FIFO
    parameter bit FRCVAL = 1'b0,                         // if true then always valid read data and check for underflow
    parameter bit FRCACC = 1'b0,                         // if true then always accept write data and check for overflow
    parameter int LANES  = 1                             // replicate control laogic per lane
    )
  (
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore
   input  logic                   clk,          // clock
   input  logic                   rst_a,        // asynchronous reset, active high, synchronous deassertion
// spyglass enable_block W240
   input  logic                   valid_write,  // input data valid
   output logic                   accept_write, // accept input data
   input  logic [DWIDTH-1:0]      data_write,   // input data
   output logic                   valid_read,   // output data valid
   input  logic                   accept_read,  // accept output data
   output logic [DWIDTH-1:0]      data_read     // output data
   );
  // spyglass disable_block ImproperRangeIndex-ML
  // local parameters
  localparam int SIZE_CL2 = (SIZE > 0) ? $clog2(SIZE) : 1;
  localparam int CHUNK    = DWIDTH/LANES;
  localparam int REMCHUNK = DWIDTH-(LANES-1)*CHUNK;
  // local wires
  logic                                  full_r;        // if true FIFO is full
  logic                                  empty_r;       // if true FIFO is empty
  logic                                  full_nxt;
  logic                                  empty_nxt;
  logic                                  rd_en;         // write enable
  logic [SIZE_CL2:0]                     rd_pnt_nxt;    // read pointer with extra msb bit next
  logic [LANES-1:0][SIZE_CL2:0]          rd_pnt_nomerge_r;  // read pointer with extra msb bit per lane
  logic                                  wr_en;         // read enable
  logic [SIZE_CL2:0]                     wr_pnt_r;      // write pointer with extra msb bit
  logic [SIZE_CL2:0]                     wr_pnt_nxt;    // write pointer with extra msb bit next
  logic [SIZE-1:0]                       fifo_en;       // fifo register enable
  logic [SIZE-1:0][DWIDTH-1:0]           fifo_data_r;   // fifo storage array
  logic [SIZE-1:0][DWIDTH-1:0]           fifo_data_nxt; // fifo storage array
  logic           [DWIDTH-1:0]           fifo_rst_val;  // 
  
if (SIZE > 0)
begin : nonzero_GEN

  assign fifo_rst_val = '0;
  
  // read and write enables
  assign accept_write = (~full_r)  | FRCACC;
  assign valid_read   = (~empty_r) | FRCVAL;
  assign wr_en        = valid_write && accept_write;
  assign rd_en        = valid_read  && accept_read;
  assign fifo_data_nxt = {{SIZE}{data_write}};

  // Drive outputs
  // outputs: data_read
  always_comb
  begin : out_PROC
    logic [SIZE_CL2:0] rptr;      // read pointer without msb
    // read data
    for (int l = 0; l < (LANES-1); l++)
    begin
      rptr           = rd_pnt_nomerge_r[l];
      rptr[SIZE_CL2] = 1'b0;
      data_read[CHUNK*l+:CHUNK] = fifo_data_r[rptr][CHUNK*l+:CHUNK];
    end
    rptr           = rd_pnt_nomerge_r[LANES-1];
    rptr[SIZE_CL2] = 1'b0;
    data_read[DWIDTH-1-:REMCHUNK] = fifo_data_r[rptr][DWIDTH-1-:REMCHUNK];
  end : out_PROC

  // next state
  // outputs: rd_pnt_nxt, wr_pnt_nxt, fifo_en
  always_comb
  begin : nxt_PROC
    logic [SIZE_CL2:0] ptr; // pointer without msb
    // next read pointer
    ptr           = rd_pnt_nomerge_r[0];
    ptr[SIZE_CL2] = 1'b0;
    if (ptr == $unsigned(SIZE-1))
    begin
      // reset to 0
      rd_pnt_nxt                = {(SIZE_CL2+1){1'b0}};
    end
    else
    begin
      // increment, clear msb
      rd_pnt_nxt                = rd_pnt_nomerge_r[0] + 1'b1;
      rd_pnt_nxt[SIZE_CL2]      = 1'b0;
    end
    // next write pointer
    ptr           = wr_pnt_r;
    ptr[SIZE_CL2] = 1'b0;
    if (ptr == $unsigned(SIZE-1))
    begin
      // reset to 0
      wr_pnt_nxt           = {(SIZE_CL2+1){1'b0}};
    end
    else
    begin
      // increment, clear msb
      wr_pnt_nxt           = wr_pnt_r + 1'b1;
      wr_pnt_nxt[SIZE_CL2] = 1'b0;
    end
    // fifo enable is onehot0
    fifo_en      = {SIZE{1'b0}};
    fifo_en[ptr] = wr_en;
  end : nxt_PROC


  // next state of full and empty
  // outputs: empty_nxt, full_nxt
  always_comb
  begin : fe_PROC
    case ({wr_en,rd_en})
    2'b10:
      begin
        // only write
        full_nxt  = wr_pnt_nxt == rd_pnt_nomerge_r[0];
        empty_nxt = 1'b0;
      end
    2'b01:
      begin
        // only read
        full_nxt  = 1'b0;
        empty_nxt = wr_pnt_r == rd_pnt_nxt;
      end
    default:
      begin
        // read and write or no read nor write
        full_nxt  = full_r;
        empty_nxt = empty_r;
      end
    endcase // case ({wr_en,rd_en})
  end : fe_PROC

        
  // State proc
  // outputs: rd_pnt_nomerge_r, wr_pnt_r, fifo_data_r, full_r, empty_r
// spyglass disable_block Reset_check07
//SMD: Clear Pins driven by comb logic
//SJ : Reset from npu_reset_ctrl BCM99 module
  always_ff @(posedge clk or posedge rst_a)
  begin : state_reg_PROC
    if (rst_a == 1'b1)
    begin
      full_r             <= 1'b0;
      empty_r            <= 1'b1;
    end
    else
    begin 
      // update full&empty state
      full_r             <= full_nxt;
      empty_r            <= empty_nxt;
    end
  end : state_reg_PROC
// spyglass enable_block Reset_check07

  always_ff @(posedge clk or posedge rst_a)
  begin
    if (rst_a == 1'b1)
    begin
      wr_pnt_r           <= {(SIZE_CL2+1){1'b0}};
    end
    else
    begin
      // Update write pointer
      if (wr_en) 
      begin
        wr_pnt_r         <= wr_pnt_nxt;
      end
    end
  end

  always_ff @(posedge clk or posedge rst_a)
  begin
    if (rst_a == 1'b1)
    begin
      rd_pnt_nomerge_r   <= {(LANES*(SIZE_CL2+1)){1'b0}};
    end
    else
    begin
      // Update read pointer
      if (rd_en) 
      begin
        rd_pnt_nomerge_r <= {LANES{rd_pnt_nxt}};
      end
    end
  end

  //`VPOST_OFF
  always_ff @(posedge clk or posedge rst_a)
  begin : data_reg_PROC
   if (rst_a == 1'b1)
   begin
     fifo_data_r        <= {SIZE{fifo_rst_val}};
   end
   else
   begin 
     // Update FIFO data
     `FOR_ASSIGN_EN(0, SIZE, fifo_en, fifo_data_r, fifo_data_nxt)
   end
 end : data_reg_PROC
 //`VPOST_ON
`ifdef ABV_ON
  //
  // Assertions
  //
  property prop_ovf;
  @(posedge clk) disable iff (rst_a == 1'b1) valid_write & full_r & FRCACC |-> accept_read;
  endproperty : prop_ovf
  a_ovf: assert property (prop_ovf) else $fatal(1, "Error: default write accept overflow");
  property prop_uvf;
  @(posedge clk) disable iff (rst_a == 1'b1) accept_read & FRCVAL |-> ~empty_r;
  endproperty : prop_uvf
  a_uvf: assert property (prop_uvf) else $fatal(1, "Error: default read valid underflow");
`endif
// spyglass enable_block ImproperRangeIndex-ML
end : nonzero_GEN
else
begin : zero_GEN
  assign full_r       = '0;        // if true FIFO is full
  assign empty_r      = 1'b1;       // if true FIFO is empty
  assign full_nxt     = '0;
  assign empty_nxt    = 1'b1;
  assign rd_en        = '0;         // write enable
  assign rd_pnt_nxt   = '0;    // read pointer with extra msb bit next
  assign rd_pnt_nomerge_r = '0;      // read pointer with extra msb bit
  assign wr_en        = '0;         // read enable
  assign wr_pnt_r     = '0;      // write pointer with extra msb bit
  assign wr_pnt_nxt   = '0;    // write pointer with extra msb bit next
  assign fifo_en      = '0;       // fifo register enable
  assign fifo_data_r  = '0;   // fifo storage array
  assign fifo_data_nxt = '0; // fifo storage array
  // FIFO is transparent
  assign valid_read   = valid_write;
  assign accept_write = accept_read;
  assign data_read    = data_write;
end : zero_GEN
  
endmodule : npu_fifo
