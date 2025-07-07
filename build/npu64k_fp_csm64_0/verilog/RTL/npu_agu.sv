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
// vcs -sverilog npu_types.sv npu_iterator.sv npu_agu.sv
// analyze -format sverilog [list ../npu_types.sv ../npu_iterator.sv ../npu_agu.sv]
//

module npu_agu
  import npu_types::*;
  #(
    parameter int R = 4                                 // rank of read operation
  )
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    soft_rst,            // if true then soft reset iterator
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
   input  offset_t   [R-1:0]       iter,                // iterations per dimension
   input  offset_t   [R-1:0]       offset,              // signed offset from end of axis to start of next axis per dimension
   input  buf_t                    bf,                  // buffer base pointer and length
   input  vm_addr_t                ptr,                 // pointer in buffer (unsigned)
   output logic                    out_valid,           // Output is valid
   input  logic                    out_accept,          // Output is accepted
   output vm_addr_t                out_addr             // Read address
   );
  //
  // Internal wires
  //
  // Parameter register
  logic                    par_en;            // register enable
  offset_t   [R-1:0]       offset_r;          // signed offset from end of axis to start of next axis per dimension
  buf_t                    bf_r;              // buffer base pointer and length
  // Address register
  logic                    ptr_en;            // VM address register enable
  vm_addr_t                ptr_r;             // VM address register
  vm_addr_t                ptr_nxt;           // VM address register next
  // iterator outputs
  logic    [R-1:0]         it_first;          // first bits
  logic    [R-1:0]         it_last;           // last bits

  
  //
  // Address generation
  //
  assign ptr_en = (in_valid & in_accept) | (out_valid & out_accept);
  // next state
  // outputs: ptr_nxt
  always_comb
  begin : ptr_nxt_PROC
    // temporary signals
    offset_t              of; // offset to be added, signed
    // default outputs
    ptr_nxt = '0;
    // next pointer value
    if (in_accept)
    begin
      // new command
      ptr_nxt |= ptr;
    end
    else
    begin
      // select offset
      of = offset_r[0];
      for (int r = 1; r < R; r++)
      begin
        if (~it_last[r])
        begin
          of = offset_r[r];
        end
      end
      ptr_nxt |= incr_vm(ptr_r, of, bf_r);
    end
  end : ptr_nxt_PROC

  
  // pointer register
  // outputs: ptr_r
  always_ff @(posedge clk or posedge rst_a)
  begin : ptr_reg_PROC
    if (rst_a == 1'b1)
    begin
      ptr_r <= '0;
    end
    else if (ptr_en)
    begin
      ptr_r <= ptr_nxt;
    end
  end : ptr_reg_PROC

  // assign VM address
  assign out_addr = ptr_r;

  
  //
  // Parameter registers
  //
  assign par_en = in_valid & in_accept;
  // outputs: 
  always_ff @(posedge clk or posedge rst_a)
  begin : par_reg_PROC
    if (rst_a == 1'b1)
    begin
      offset_r <= '0;
      bf_r     <= '0;
    end
    else if (par_en)
    begin
      offset_r <= offset;
      bf_r     <= bf;
    end
  end : par_reg_PROC
  

  //
  // Iterator instance
  //
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally left open
  npu_iterator
  #(
    .N ( R ) // rank
  )
  u_iter_inst
  (
   .clk      ( clk              ),
   .rst_a    ( rst_a            ),
   .soft_rst ( soft_rst         ),
   .in_req   ( in_valid         ),
   .in_ack   ( in_accept        ),
   .in_shp   ( iter             ),
   .it_req   ( out_valid        ),
   .it_ack   ( out_accept       ),
   .it_first ( it_first         ),
   .it_last  ( it_last          ),
   .it_vald  (                  ) // intentionally left open
   );
// spyglass enable_block W287b

endmodule : npu_agu
