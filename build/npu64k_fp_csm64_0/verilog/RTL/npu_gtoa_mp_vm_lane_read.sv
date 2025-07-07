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
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_fifo.sv ../../shared/RTL/npu_gtoa_mp_vm_read.sv ../../shared/RTL/npu_gtoa_mp_vm_lane_read.sv
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_fifo.sv ../../../shared/RTL/npu_gtoa_mp_vm_read.sv ../../../shared/RTL/npu_gtoa_mp_vm_lane_read.sv"
//

`include "npu_defines.v"
`include "npu_vm_macros.svh"


module npu_gtoa_mp_vm_lane_read
  import npu_types::*;
  #(
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
   input  logic      [G-1:0]       mask,                // maxpool stash mask
   output logic      [G-1:0]       mask_o,              // maxpool stash mask out
   output logic      [G-1:0]       rd_hs,               // read handshake on VM interface
   input  logic      [G-1:0]       canrd,               // read is depencency free
   `VMRMST(G,vm_rd_),                               // VM read interface
   output logic                    out_valid,           // Output is valid
   input  logic                    out_accept,          // Output is accepted
   output ixpix_t    [G-1:0]       out_data             // Read data
   );
  // internal wires
  logic     [G-1:0] i_val;      // HLAPI valid per bank
  logic     [G-1:0] i_acc;      // HLAPI accept per bank
  logic     [G-1:0] v_val;      // output valid per bank
  logic     [G-1:0] v_acc;      // output accept per bank
  logic     [G-1:0] i_rd_hs;    // read handshake per bank
  logic             mask_en;    // write enable mask enable
  logic     [G-1:0] mask_r;     // write enable mask
  logic     [G-1:0] mask_nxt;   // write enable mask
  logic             in_validi;  // HLAPI valid internal
  logic             in_accepti; // HLAPI accept internal
  logic                  rv_pend_cntr_en;  // read valid pending counter enable
  logic     [G-1:0][1:0] rv_pend_cntr_r;   // read valid pending counter
  logic     [G-1:0][1:0] rv_pend_cntr_nxt; // read valid pending counter next
  `VMRWIRES(G,vm_int_);

  // simple assignments
  assign in_accept  = in_accepti & (rv_pend_cntr_r == '0);
  assign in_validi  = in_valid & (rv_pend_cntr_r == '0);
  assign in_accepti = &i_acc;
  assign i_val      = (in_validi && in_accepti) ? '1 : '0;
  assign mask_en    = (in_validi & in_accepti);
  assign mask_nxt   = mask;
  assign mask_o     = mask_r;

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
      mask_r        <= mask_nxt;
    end
  end : fsm_reg_PROC

  // mask external read command if stash only read 1 bank
  // copy internal signals and handshake from bank 0
  always_comb
  begin : mask_bnk_PROC
    if(mask_r == 2'b01)
    begin
      vm_rd_cmd_valid   = {{(G-1){1'b0}}, vm_int_cmd_valid[0]};
      vm_rd_cmd_addr    = {G{vm_int_cmd_addr[0]}};
      vm_int_cmd_accept = {G{vm_rd_cmd_accept[0]}};
      vm_int_rvalid     = {G{vm_rd_rvalid[0]}};
      vm_int_rdata      = {G{vm_rd_rdata[0]}};
      rd_hs             = {G{i_rd_hs[0]}};
    end
    else
    begin
      vm_rd_cmd_valid   = vm_int_cmd_valid;
      vm_rd_cmd_addr    = vm_int_cmd_addr;
      vm_int_cmd_accept = vm_rd_cmd_accept;
      vm_int_rvalid     = vm_rd_rvalid;
      vm_int_rdata      = vm_rd_rdata;
      rd_hs             = i_rd_hs;
    end
  end : mask_bnk_PROC

  // counter for pending rvalid
  // if counter is not 0, new hlapi valid cannot be accepted
  // because command and rvalid must be under the same mask mode
  always_comb
  begin : pend_cnt_PROC
    rv_pend_cntr_en  = 1'b0;
    rv_pend_cntr_nxt = rv_pend_cntr_r;
    for (int i = 0; i < G; i++)
    begin
      if(vm_int_cmd_valid[i] & vm_int_cmd_accept[i])
      begin
        rv_pend_cntr_en = 1'b1;
        rv_pend_cntr_nxt[i] = rv_pend_cntr_nxt[i] + 'd1;
      end
      if(vm_int_rvalid[i])
      begin
        rv_pend_cntr_en = 1'b1;
        rv_pend_cntr_nxt[i] = rv_pend_cntr_nxt[i] - 'd1;
      end
    end
  end : pend_cnt_PROC

  // pending counter register update
  // outputs: rv_pend_cntr_r
  always_ff @(posedge clk or
              posedge rst_a)
  begin : pend_reg_PROC
    if (rst_a == 1'b1)
    begin
      rv_pend_cntr_r <= '0;
    end
    else if (rv_pend_cntr_en)
    begin
      rv_pend_cntr_r <= rv_pend_cntr_nxt;
    end
  end : pend_reg_PROC

  for (genvar bnk = 0; bnk < G; bnk++)
  begin : lanes
// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression
//SJ :Ignore (stride * bnk)
    vm_addr_t i_ptr;
    assign i_ptr      = incr_vm(ptr, stride*bnk, bf);
// spyglass enable_block SelfDeterminedExpr-ML
// spyglass disable_block W287b
//SMD:intentionaly unconnected
    npu_gtoa_mp_vm_read
      #(
        .R ( R ) 
        )
    u_vm_rd_bnk_inst
      (
       .clk        ( clk               ),
       .rst_a      ( rst_a             ),
       .busy       (                   ), // intentionaly unconnected
       .in_valid   ( i_val[bnk]        ),
       .in_accept  ( i_acc[bnk]        ),
       .iter       ( iter              ),
       .offset     ( offset            ),
       .bf         ( bf                ),
       .ptr        ( i_ptr             ),
       .rd_hs      ( i_rd_hs[bnk]      ),
       .canrd      ( canrd[bnk]        ),
       `VMRINST_S(1,vm_rd_,vm_int_,bnk ),
       .out_valid  ( v_val[bnk]        ),
       .out_accept ( v_acc[bnk]        ),
       .out_ixpix  ( out_data[bnk]     )
       );
  end : lanes
// spyglass enable_block W287b

  assign out_valid = &v_val;
  assign v_acc     = out_valid & out_accept ? '1 : '0;

endmodule : npu_gtoa_mp_vm_lane_read
