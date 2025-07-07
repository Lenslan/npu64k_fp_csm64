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
// Parameterizable maxpool stash VM write interface
// vcs -sverilog npu_types.sv npu_iterator.sv npu_gtoa_mp_vm_write.sv
// analyze -format sverilog [list ../npu_types.sv ../npu_iterator.sv ../npu_gtoa_mp_vm_write.sv]
//

`include "npu_defines.v"
`include "npu_vm_macros.svh"


module npu_gtoa_mp_vm_write
  import npu_types::*;
  #(
    parameter int R = 4                                 // rank of read operation
    )
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
   input  offset_t   [R-1:0]       iter,                // iterations per dimension
   input  offset_t   [R-1:0]       offset,              // signed offset from end of axis to start of next axis per dimension
   input  buf_t                    bf,                  // buffer base pointer and length
   input  vm_addr_t                ptr,                 // pointer in buffer (unsigned)
   output logic                    wr_hs,               // write handshake on VM interface
   input  logic                    canwr,               // write is dependency free
   input  logic                    out_valid,           // Output is valid
   output logic                    out_accept,          // Output is accepted
   input  ixpix_t                  out_ixpix,           // Write data
   `VMWMST(1,vm_wr_)                                    // VM write interface
   );
  //
  // Internal wires
  //
  // iterator outputs
  logic                    it_req;            // iterator valid
  logic                    it_ack;            // iterator accept

  
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
   .soft_rst   ( 1'b0           ), // intentionally left open, no soft reset
   .in_valid   ( in_valid       ),
   .in_accept  ( in_accept      ),
   .iter       ( iter           ),
   .offset     ( offset         ),
   .bf         ( bf             ),
   .ptr        ( ptr            ),
   .out_valid  ( it_req         ),
   .out_accept ( it_ack         ),
   .out_addr   ( vm_wr_cmd_addr )
   );

  
  // connect flow controls
  assign vm_wr_cmd_valid = out_valid & it_req & canwr;
  assign it_ack          = out_valid & vm_wr_cmd_accept;
  assign out_accept      = it_req    & vm_wr_cmd_accept;
  assign vm_wr_wdata     = out_ixpix;
  assign vm_wr_wstrb     = '1;
  assign wr_hs           = vm_wr_cmd_valid & vm_wr_cmd_accept;
   
endmodule : npu_gtoa_mp_vm_write
