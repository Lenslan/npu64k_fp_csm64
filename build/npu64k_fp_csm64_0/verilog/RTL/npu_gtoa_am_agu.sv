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
// Configurable AM address generator
//

module npu_gtoa_am_agu
  import npu_types::*;
  #(
    parameter int R = 4
    )
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
   input  offset_t   [R-1:0]       iter,                // iterations per dimension
   input  offset_t   [R-1:0]       offset,              // signed offset from end of axis to start of next axis per dimension
   input  am_addr_t                ptr,                 // pointer in buffer (unsigned)
   output logic                    out_valid,           // output address is valid
   input  logic                    out_accept,          // output address is accepted
   output am_addr_t                out_addr             // AM address
   );
  //
  // Internal wires
  //
  // Iterator outputs
  logic      [R-1:0] it_last;
  // Running address register
  am_addr_t          ptr_r;
  am_addr_t          ptr_nxt;
  logic              ptr_en;
  logic              offset_en;
  offset_t   [R-1:0] offset_r;
  localparam int AM_ADDR_LEN = $bits(am_addr_t);

  //
  // Simple assignments
  //
  assign out_addr     = ptr_r;
  
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected  
  //
  // Instantiate loop iterator
  //
  npu_iterator
    #(
      .N ( R )
      )
  u_iterator_inst
    (
    .clk      ( clk          ),
    .rst_a    ( rst_a        ),
    .soft_rst ( 1'b0         ),
    .in_req   ( in_valid     ),
    .in_ack   ( in_accept    ),
    .in_shp   ( iter         ),
    .it_req   ( out_valid    ),
    .it_ack   ( out_accept   ),
    .it_first (              ), // intentionally unconnected
    .it_last  ( it_last      ), 
    .it_vald  (              )  // intentionally unconnected
   );
// spyglass enable_block W287b

  //
  // Address generation
  //
  // next state
  // outputs: ptr_en, ptr_nxt, offset_en
  always_comb
  begin : ptr_nxt_PROC
    // default outputs
    ptr_en = 1'b0;
    ptr_nxt = '0;
    offset_en = 1'b0;
    // state dependent values
    if (in_valid & in_accept)
    begin
      // accept new sequence
      ptr_en   = 1'b1;
      ptr_nxt |= ptr;
      offset_en = 1'b1;
    end
    else if (out_valid & out_accept)
    begin
      offset_t              of; // offset to be added, signed
      ptr_en = 1'b1;
      // select offset
      of = offset_r[0];
      for (int r = 1; r < R; r++)
      begin
        if (~it_last[r])
        begin
          of = offset_r[r];
        end
      end
      // increment pointer by sign extended offset
      ptr_nxt |= ptr_r + of[AM_ADDR_LEN-1:0];
    end
  end : ptr_nxt_PROC
  
  // pointer register
  // outputs: ptr_r
  always_ff @(posedge clk or posedge rst_a)
  begin : ptr_reg_PROC
    if (rst_a == 1'b1)
    begin
      ptr_r   <= '0;
      offset_r <= '0;
    end
    else 
    begin
      if (ptr_en)
      begin
        ptr_r <= ptr_nxt;
      end
      if (offset_en)
      begin
        offset_r <= offset;
      end
    end
  end : ptr_reg_PROC

endmodule : npu_gtoa_am_agu
