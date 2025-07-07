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
// Parameterizable maxpool stash VM read interface
// vcs -sverilog npu_types.sv npu_iterator.sv npu_fifo.sv npu_gtoa_mp_vm_read.sv
// analyze -format sverilog [list ../npu_types.sv ../npu_iterator.sv ../npu_fifo.sv ../npu_gtoa_mp_vm_read.sv]
//

`include "npu_defines.v"
`include "npu_vm_macros.svh"

module npu_gtoa_mp_vm_read
  import npu_types::*;
  #(
    parameter int R = 4                                 // rank of read operation
    )
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   output logic                    busy,                // if true then more data pending
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
   input  offset_t   [R-1:0]       iter,                // iterations per dimension
   input  offset_t   [R-1:0]       offset,              // signed offset from end of axis to start of next axis per dimension
   input  buf_t                    bf,                  // buffer base pointer and length
   input  vm_addr_t                ptr,                 // pointer in buffer (unsigned)
   output logic                    rd_hs,               // read handshake on VM interface
   input  logic                    canrd,               // read is depencency free
   `VMRMST(1,vm_rd_),                                   // VM read interface
   output logic                    out_valid,           // Output is valid
   input  logic                    out_accept,          // Output is accepted
   output ixpix_t                  out_ixpix            // Read data
   );
  //
  // Internal wires
  //
  // iterator outputs
  logic                    it_req;            // iterator valid
  logic                    it_ack;            // iterator accept
  // pending read data counter
  logic                    pend_en;           // enable pending counter
  logic    [1:0]           pend_r;            // number of pending read data including fifo
  logic    [1:0]           pend_nxt;          // next value of pending read data
  logic                    can_issue;         // true if less than max pending reads
  
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
   .soft_rst   ( 1'b0           ), // intentionally 0, no soft reset
   .in_valid   ( in_valid       ),
   .in_accept  ( in_accept      ),
   .iter       ( iter           ),
   .offset     ( offset         ),
   .bf         ( bf             ),
   .ptr        ( ptr            ),
   .out_valid  ( it_req         ),
   .out_accept ( it_ack         ),
   .out_addr   ( vm_rd_cmd_addr )
   );

  
  // drive VM command interface if pending read fits FIFO
  assign busy            = pend_r != '0;
  assign can_issue       = pend_r != '1;
  assign vm_rd_cmd_valid = it_req & can_issue & canrd;
  assign it_ack          = vm_rd_cmd_accept & can_issue & canrd;
  assign rd_hs           = vm_rd_cmd_valid & vm_rd_cmd_accept;
                                      
    
  //
  // FIFO storing VM read data
  //
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentional open
  npu_fifo
   #(
     .SIZE   ( 3              ),
     .DWIDTH ( $bits(ixpix_t) ),
     .FRCVAL ( 1'b0           ),
     .FRCACC ( 1'b1           ) // FIFO can always accept, guarded by the use_acc FIFO
    )
  u_dfifo_inst
    (
     .clk          ( clk          ),
     .rst_a        ( rst_a        ),
     .valid_write  ( vm_rd_rvalid ),
     .accept_write (              ), // intentionally unconnected
     .data_write   ( vm_rd_rdata  ),
     .valid_read   ( out_valid    ),
     .accept_read  ( out_accept   ),
     .data_read    ( out_ixpix    )
     );
// spyglass enable_block W287b

  
  //
  // Pending read data counting
  //
  // outputs: pend_en, pend_nxt
  always_comb
  begin : pend_nxt_PROC
    // default values
    pend_en  = 1'b0;
    pend_nxt = pend_r;
    if ((it_req&it_ack) != (out_valid&out_accept))
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

endmodule : npu_gtoa_mp_vm_read
