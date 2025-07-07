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
// Parameterizable maxpool stash VM read lane interface
// vcs -sverilog ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_agu.sv ../../shared/RTL/npu_fifo.sv ../../npu_act/RTL/npu_gtoa_mp_vm_write.sv ../../npu_act/RTL/npu_gtoa_mp_vm_lane_write.sv +incdir+../../shared/RTL
//

`include "npu_defines.v"
`include "npu_vm_macros.svh"


module npu_gtoa_mp_vm_lane_write
  import npu_types::*;
  #(
    parameter int R = 4,                                // rank of read operation
    parameter int G = VSIZE,                            // data vectorization
    parameter int V = VSIZE                             // enable vectorization
    )
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
   input  offset_t   [R-1:0]       iter,                // iterations per dimension
   input  offset_t   [R-1:0]       offset,              // signed offset from end of axis to start of next axis per dimension
   input  offset_t                 stride,              // input stride
   input  offset_t                 ptr,                 // pointer in buffer (unsigned)
   input  buf_t                    bf,                  // buffer descriptor
   input  logic      [V-1:0]       mask,                // Write enable mask
   output logic      [G-1:0]       wr_hs,               // write handshake on VM interface
   input  logic      [G-1:0]       canwr,               // write is dependency free
   input  logic                    out_valid,           // Output is valid
   output logic                    out_accept,          // Output is accepted
   input  ixpix_t    [G-1:0]       out_data,            // Write data
   `VMWMST(G,vm_wr_)                                    // VM write interface
   );
  // internal wires
  logic     [G-1:0] i_val;      // HLAPI valid per bank
  logic     [G-1:0] i_acc;      // HLAPI accept per bank
  logic     [G-1:0] v_val;      // output valid per bank
  logic     [G-1:0] v_acc;      // output accept per bank
  logic     [G-1:0] i_wr_hs;    // write handshake per bank
  logic             mask_en;    // write enable mask enable
  logic     [V-1:0] mask_r;     // write enable mask
  logic     [V-1:0] mask_nxt;   // write enable mask
  logic             todo_en;    // to do register enable
  logic     [G-1:0] todo_r;     // banks remaining to write
  logic     [G-1:0] todo_nxt;
  logic             done_r;     // delayed done
  logic             done_nxt;   // delayed done
  
  
  // simple assignments
  assign in_accept   = &i_acc;
  assign i_val       = (in_valid && in_accept) ? '1 : '0;
  assign wr_hs       = mask_r == 2'b01 ? {G{i_wr_hs[0]}} : i_wr_hs;
  // TODO: mask_nxt is not used for now. Do we keep it?
  if (G != V)
  begin : ne_GEN
    // rotate mask after accept
    assign mask_en   = (in_valid & in_accept) | (out_valid & out_accept);
    assign mask_nxt  = (in_valid & in_accept) ? mask : {mask_r[G-1:0], mask_r[V-1:G]};
  end : ne_GEN
  else
  begin : eq_GEN
    // keep mask
    assign mask_en   = (in_valid & in_accept);
    assign mask_nxt  = mask;
  end : eq_GEN

  // mask configuration
  // outputs: mask_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : fsm_reg_PROC
    if (rst_a == 1'b1)
    begin
      mask_r        <= '0;
    end
    else if (mask_en)
    begin
      mask_r        <= mask;
    end
  end : fsm_reg_PROC
  
  // internal VM wires
  `VMWWIRES(G,vm_int_);
  for (genvar bnk = 0; bnk < G; bnk++)
  begin : lanes
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression
//SJ :Ignore
    vm_addr_t i_ptr;
    assign i_ptr      = incr_vm(ptr, stride*bnk, bf);
// spyglass enable_block SelfDeterminedExpr-ML
    npu_gtoa_mp_vm_write
      #(
        .R ( R ) 
        )
    u_vm_wr_bnk_inst
      (
       .clk        ( clk               ),
       .rst_a      ( rst_a             ),
       .in_valid   ( i_val[bnk]        ),
       .in_accept  ( i_acc[bnk]        ),
       .iter       ( iter              ),
       .offset     ( offset            ),
       .bf         ( bf                ),
       .ptr        ( i_ptr             ),
       .wr_hs      ( i_wr_hs[bnk]      ),
       .canwr      ( canwr[bnk]        ),
       .out_valid  ( v_val[bnk]        ),
       .out_accept ( v_acc[bnk]        ),
       .out_ixpix  ( out_data[bnk]     ),
       `VMWINST_S(1,vm_wr_,vm_int_,bnk)
       );
  end

  assign vm_wr_cmd_valid   = vm_int_cmd_valid &  mask_r[G-1:0];
  assign vm_int_cmd_accept = vm_wr_cmd_accept | ~mask_r[G-1:0];
  assign vm_wr_cmd_addr    = vm_int_cmd_addr;
  assign vm_wr_wdata       = vm_int_wdata;
  assign vm_wr_wstrb       = vm_int_wstrb;

  // track write state
  // outputs: todo_nxt, todo_en, out_accept, v_val
  always_comb
  begin : merge_nxt_PROC
    // default outputs
    todo_nxt     = todo_r;
    todo_en      = 1'b0;
    v_val        = '0;
    if (done_r)
    begin
      // delayed accept
      out_accept = out_valid;
      done_nxt   = ~out_valid;
    end
    else
    begin
      // no accept yet
      if (todo_r == '0 && out_valid)
      begin
        todo_nxt = '1;
      end
      v_val      = todo_nxt;
      todo_nxt  &= ~v_acc;
      if ((v_val & v_acc) != '0)
      begin
        todo_en  = 1'b1;
      end
      out_accept = out_valid & (todo_nxt == '0);
      // delayed accept if not valid
      done_nxt   = (todo_r != '0) & (todo_nxt == '0) & (~out_valid);
    end
  end : merge_nxt_PROC
  
  // to do writes
  // outputs: todo_r, done_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : todo_reg_PROC
    if (rst_a == 1'b1)
    begin
      todo_r <= '0;
      done_r <= 1'b0;
    end
    else 
    begin
      done_r <= done_nxt;
      if (todo_en)
      begin
        todo_r <= todo_nxt;
      end
    end
  end : todo_reg_PROC
  
endmodule : npu_gtoa_mp_vm_lane_write
