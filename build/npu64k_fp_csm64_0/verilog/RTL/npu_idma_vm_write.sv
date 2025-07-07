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
// Top-level file for the iDMA VM Write 
//

`include "npu_vm_macros.svh"

module npu_idma_vm_write
  import npu_types::*;
  #(
    // HLAPI type
    int  S        = DMA_VM_LANES,
    int  STU_D    = DMA_VM_LANES*8*ISIZE
  )
(
  // VM AGU interface 
  input  vm_addr_t [S-1:0]       vm_waddr,    // Generated VM address 
  input  logic     [S-1:0]       vm_valid,    // Enable each VM lanes
  output logic                   vm_accept,   // Accept by VM load/store

  // VM Request Interface
  `VMWMST(S,vm_wr_),                          // VM read

  // Output data
  input  logic                    out_valid,
  input  logic [STU_D-1:0]        out_data,
  input  logic [STU_D/8-1:0]      out_wstrb,
  output logic                    out_accept,

  output logic                    idle,
  // clock and reset
  //
  input  logic                    clk,         // clock, all logic clocked at posedge
  input  logic                    rst_dp       // reset, active high

);

  //Data FIFO wires
  logic         [S-1:0]      push_wr;
  logic         [S-1:0]      wr_fifo_avail;
  ixpix_t       [S-1:0]      wr_fifo_wdata;
  ixbit_t       [S-1:0]      wr_fifo_wstrb;
  vm_addr_t     [S-1:0]      wr_fifo_waddr;
  logic         [S-1:0]      wr_fifo_valid;
  logic         [S-1:0]      pop_wr;
  ixpix_t       [S-1:0]      wr_fifo_rdata;
  vm_addr_t     [S-1:0]      wr_fifo_raddr;
  ixbit_t       [S-1:0]      wr_fifo_rstrb;

  // VM access
  always_comb
  begin : vm_access_nxt_PROC
    vm_wr_cmd_valid      =  'b0;
    vm_wr_cmd_addr       =  'b0;
    vm_wr_wdata          =  'b0;
    vm_wr_wstrb          =  'b0;

    push_wr              =  'b0;
    pop_wr               =  'b0;
    wr_fifo_wdata        =  'b0;
    wr_fifo_wstrb        =  'b0;
    wr_fifo_waddr        =  'b0;
    
    vm_accept            = 1'b0;
    out_accept           = 1'b0;

    // vm_valid has all involved lanes available and data valid
    // push VM command and address into FIFO
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self determined expression
// SJ: Intention implement 
    if (((wr_fifo_avail & vm_valid) == vm_valid) && out_valid)
    begin
      for (int i=0; i<S; i++) begin
        if (vm_valid[i] == 1) begin
          wr_fifo_wdata[i] = out_data[128*i+:128];
          wr_fifo_wstrb[i] = out_wstrb[16*i+:16];
          wr_fifo_waddr[i] = vm_waddr[i];
          push_wr[i]       = 1'b1;
        end
      end
      vm_accept            = 1'b1;
      out_accept           = 1'b1;
    end
// spyglass enable_block SelfDeterminedExpr-ML

    // Write VM data in ports
    for (int i=0; i<S; i++) begin
      if (wr_fifo_valid[i]) begin
        vm_wr_cmd_valid[i]     =  1'b1;
        vm_wr_cmd_addr[i]      =  wr_fifo_raddr[i];
        vm_wr_wdata[i]         =  wr_fifo_rdata[i];
        vm_wr_wstrb[i]         =  wr_fifo_rstrb[i];
        if (vm_wr_cmd_accept[i]) begin
          pop_wr[i]            = 1'b1;
        end
      end
    end
  end : vm_access_nxt_PROC

  // FIFO to store rdata
  genvar gvr_i;
  generate
    for(gvr_i = 0; gvr_i < S; gvr_i = gvr_i + 1) 
    begin: wr_fifo_inst
      npu_fifo 
      #(
        .SIZE   ( 8  ),
        .DWIDTH (ISIZE*PIX_W+16+16) //data+address
      )
      u_wdata_fifo_inst
      (           
         .clk          ( clk                 ),
         .rst_a        ( rst_dp              ),
         .valid_write  ( push_wr[gvr_i]      ), 
         .accept_write ( wr_fifo_avail[gvr_i]),
         .data_write   ( {wr_fifo_waddr[gvr_i], wr_fifo_wdata[gvr_i], wr_fifo_wstrb[gvr_i]}),
         .valid_read   ( wr_fifo_valid[gvr_i]),
         .accept_read  ( pop_wr[gvr_i]       ),
         .data_read    ( {wr_fifo_raddr[gvr_i], wr_fifo_rdata[gvr_i], wr_fifo_rstrb[gvr_i]})
      );
    end : wr_fifo_inst
  endgenerate

  assign idle   =  (~(|wr_fifo_valid || |vm_valid));

endmodule : npu_idma_vm_write
