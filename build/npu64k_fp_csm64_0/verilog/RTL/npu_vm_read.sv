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
// Parameterizable VM read interface
// vcs -sverilog npu_types.sv npu_agu.sv npu_iterator.sv npu_fifo.sv npu_vm_read.sv
// analyze -format sverilog [list ../npu_types.sv ../npu_iterator.sv ../npu_fifo.sv ../npu_vm_read.sv]
//

`include "npu_defines.v"
`include "npu_vm_macros.svh"

module npu_vm_read
  import npu_types::*;
  #(
    parameter int D = 5,                            // depth of read data FIFO
    parameter int R = 4,                            // rank of read operation
    parameter int F = 0                             // if true then fast read, bypass FIFO
    )
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    soft_rst,            // if true then abort sequence, because 
   output logic                    busy,                // if true then more data pending
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
   input  offset_t   [R-1:0]       iter,                // iterations per dimension
   input  offset_t   [R-1:0]       offset,              // signed offset from end of axis to start of next axis per dimension
   input  buf_t                    bf,                  // buffer base pointer and length
   input  vm_addr_t                ptr,                 // pointer in buffer (unsigned)
   `VMRMST(1,vm_rd_),                                   // VM read interface
   output logic                    out_valid,           // Output is valid
   input  logic                    out_accept,          // Output is accepted
   output ixpix_t                  out_ixpix            // Read data
   );
  //
  // Internal wires
  //
  // soft reset signals
  logic                    isoft_rst;         // stretched soft reset
  logic    [4:0]           soft_rst_r;        // soft reset delay line
  logic    [4:0]           soft_rst_nxt;      // soft reset delay line, next
  // iterator soft reset gated controls
  logic                    iin_valid;         // new command valid
  logic                    iin_accept;        // new command accept
  // iterator outputs
  logic                    it_req;            // iterator valid
  logic                    it_ack;            // iterator accept
  // pending read data counter
  logic                    pend_en;           // enable pending counter
  logic    [2:0]           pend_r;            // number of pending read data including fifo
  logic    [2:0]           pend_nxt;          // next value of pending read data
  logic                    can_issue;         // true if less than max pending reads
  // internal handshakes
  logic                    int_valid;         // Output fifo is valid
  logic                    int_accept;        // Output fifo is accepted
  // signals for FIFO bypassing
  logic                    d_valid;           // Actual valid input to FIFO
  ixpix_t                  d_ixpix;           // FIFO output data

  //
  // Address generation
  //
  npu_agu
  #(
    .R (R )
  )
  u_agu_inst
  (
   .clk        ( clk            ),
   .rst_a      ( rst_a          ),
   .soft_rst   ( soft_rst       ),
   .in_valid   ( iin_valid      ),
   .in_accept  ( iin_accept     ),
   .iter       ( iter           ),
   .offset     ( offset         ),
   .bf         ( bf             ),
   .ptr        ( ptr            ),
   .out_valid  ( it_req         ),
   .out_accept ( it_ack         ),
   .out_addr   ( vm_rd_cmd_addr )
   );

  
  //
  // Delay soft reset to flush pending data
  //
  assign isoft_rst    = soft_rst | (soft_rst_r != '0);
  assign soft_rst_nxt = {soft_rst_r[3:0], soft_rst};
  always_ff @(posedge clk or posedge rst_a)
  begin : soft_reg_PROC
    if (rst_a == 1'b1)
    begin
      soft_rst_r <= '0;
    end
    else if (isoft_rst)
    begin
      soft_rst_r <= soft_rst_nxt;
    end
  end : soft_reg_PROC
  
  
  
  // stall input interface during soft reset
  assign iin_valid = in_valid & !isoft_rst;
  assign in_accept = iin_accept & !isoft_rst;
  
  // drive VM command interface if pending read fits FIFO
  assign busy            = pend_r != '0;
  assign can_issue       = pend_r != unsigned'(D);
  assign vm_rd_cmd_valid = it_req & can_issue;
  assign it_ack          = vm_rd_cmd_accept & can_issue;
  
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :intentionally unconnected    
  //
  // FIFO storing VM read data
  npu_fifo
   #(
     .SIZE   ( D              ),
     .DWIDTH ( $bits(ixpix_t) ),
     .FRCVAL ( 1'b0           ),
     .FRCACC ( 1'b1           ) // FIFO can always accept, guarded by the pending counter
    )
  u_dfifo_inst
    (
     .clk          ( clk          ),
     .rst_a        ( rst_a        ),
     .valid_write  ( d_valid      ),
     .accept_write (              ), // intentionally unconnected
     .data_write   ( vm_rd_rdata  ),
     .valid_read   ( int_valid    ),
     .accept_read  ( int_accept   ),
     .data_read    ( d_ixpix      )
     );
// spyglass enable_block W287b
  if (F == 0)
  begin : f0_GEN
    // no fast read mode, always buffer read data
    assign d_valid    = vm_rd_rvalid;
    assign out_valid  = int_valid & ~isoft_rst;
    assign out_ixpix  = d_ixpix;
  end : f0_GEN
  else
  begin : f1_GEN
    // fast read mode, first read data bypasses FIFO
    assign d_valid    = int_valid ? vm_rd_rvalid : vm_rd_rvalid&~out_accept;
    assign out_valid  = (int_valid|vm_rd_rvalid) & ~isoft_rst;
    assign out_ixpix  = int_valid ? d_ixpix : vm_rd_rdata;
  end  : f1_GEN
  assign int_accept = out_accept | isoft_rst;


  //
  // Pending read data counting
  //
  // outputs: pend_en, pend_nxt
  always_comb
  begin : pend_nxt_PROC
    // default values
    pend_en = 1'b0;
    pend_nxt = pend_r;
    if (soft_rst)
    begin
      pend_en  = 1'b1;
      pend_nxt = '0;
    end
    else if ((it_req&it_ack) != (out_valid&out_accept))
    begin
      // increment or decrement
      pend_en = 1'b1;
      if (it_req&it_ack)
      begin
        pend_nxt = pend_nxt + 1'b1;
      end
      else
      begin
        pend_nxt = pend_nxt - 1'b1;
      end
    end
  end : pend_nxt_PROC

  // pending register
  // outputs: pend_r
  always_ff @(posedge clk or posedge rst_a)
  begin : pend_reg_PROC
    if (rst_a == 1'b1)
    begin
      pend_r <= '0;
    end
    else if (pend_en)
    begin
      pend_r <= pend_nxt;
    end
  end : pend_reg_PROC
endmodule : npu_vm_read
