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
// Parameterizable VM read lane interface
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_fifo.sv ../../shared/RTL/npu_vm_read.sv ../../shared/RTL/npu_vm_lane_read.sv
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_fifo.sv ../../../shared/RTL/npu_vm_read.sv ../../../shared/RTL/npu_vm_lane_read.sv"
//

`include "npu_defines.v"
`include "npu_vm_macros.svh"

module npu_vm_lane_read
  import npu_types::*;
  #(
    parameter int D = 5,                                // read FIFO size
    parameter int R = 4,                                // rank of read operation
    parameter int G = VSIZE                             // vector width
    )
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
   input  offset_t   [R-1:0]       iter,                // iterations per dimension
   input  offset_t   [R-1:0]       offset,              // signed offset from end of axis to start of next axis per dimension
   input  offset_t                 stride,              // input stride
   input  vm_addr_t                ptr,                 // pointer in buffer (unsigned)
   input  buf_t                    bf,                  // buffer descriptor
   `VMRMST(G,vm_rd_),                                   // VM read interface
   output logic                    out_valid,           // Output is valid
   input  logic                    out_accept,          // Output is accepted
   output ixpix_t    [G-1:0]       out_data             // Read data
   );
  // internal wires
  logic     [G-1:0] i_val;      // HLAPI valid per bank
  logic     [G-1:0] i_acc;      // HLAPI accept per bank
  logic     [G-1:0] i_busy;     // busy per bank
  logic     [G-1:0] v_val;      // output valid per bank
  logic     [G-1:0] v_acc;      // output accept per bank
  ixpix_t   [G-1:0] int_data;   // internal data
  logic     [G-1:0] one_r;      // if true then stride 0 and broadcsat read data
  logic     [G-1:0] one_nxt;
  

  // simple assignments
  assign in_accept  = &{i_acc,~i_busy};
  for (genvar bnk = 0; bnk < G; bnk++)
  begin : one_r_to_out_GEN
    assign out_data[bnk]   = one_r[bnk] ? int_data[0] : int_data[bnk];
  end : one_r_to_out_GEN
  assign out_valid  = one_r[0] ? v_val[0] : &v_val;
  assign v_acc      = out_valid & out_accept ? '1 : '0;

  
  // new HLAPI
  // outputs: i_val, one_nxt
  always_comb
  begin : hlapi_PROC
    // default outputs
    i_val           = '0;
    one_nxt         = one_r;
    if (in_valid & in_accept)
    begin
      // new HLAPI
      if (stride == '0)
      begin
        // one lane only and broadcast read data
        one_nxt     = '1;
        i_val[0]    = 1'b1;
      end
      else
      begin
        // use all lanes
        one_nxt     = '0;
        i_val       = '1;
      end
    end
  end : hlapi_PROC
  
  for (genvar bnk = 0; bnk < G; bnk++)
  begin : lanes
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Width mismatch
//SJ :Ignore
    vm_addr_t i_ptr;
    assign i_ptr      = incr_vm(ptr, stride*bnk, bf);
// spyglass enable_block SelfDeterminedExpr-ML
// spyglass disable_block W287b
//SMD:Unconnected output
//SJ :intentionaly unconnected
    npu_vm_read
      #(
        .D ( D ),
        .R ( R ) 
        )
    u_vm_rd_bnk_inst
      (
       .clk        ( clk               ),
       .rst_a      ( rst_a             ),
       .soft_rst   ( 1'b0              ),
       .busy       ( i_busy[bnk]       ),
       .in_valid   ( i_val[bnk]        ),
       .in_accept  ( i_acc[bnk]        ),
       .iter       ( iter              ),
       .offset     ( offset            ),
       .bf         ( bf                ),
       .ptr        ( i_ptr             ),
       `VMRINST_S(1,vm_rd_,vm_rd_,bnk  ),
       .out_valid  ( v_val[bnk]        ),
       .out_accept ( v_acc[bnk]        ),
       .out_ixpix  ( int_data[bnk]     )
       );

  end : lanes
// spyglass enable_block W287b

  // state of one-lane vs multi-lane
  always_ff @(posedge clk or posedge rst_a)
  begin : one_reg_PROC
    if (rst_a == 1'b1)
    begin
      one_r <= '0;
    end
    else
    begin
      one_r <= one_nxt;
    end
  end : one_reg_PROC
  
endmodule : npu_vm_lane_read
