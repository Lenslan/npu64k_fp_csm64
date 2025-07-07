
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
// VM Memory STALL Inject module 
//


`include "npu_vm_macros.svh"

module npu_vm_inj_stall
  import npu_types::*;
  #(parameter RD_IDX=0,
    parameter WR_IDX=0,
    parameter VM_RPORTS=1,
    parameter VM_WPORTS=1
   )
  (
   //
   // interfaces
   //
   // write request
   `VMWSLV(VM_WPORTS,slv_nn_vm_wr_),
   // read request
   `VMRSLV(VM_RPORTS,slv_nn_vm_rd_),
   
   // write request
   `VMWMST(VM_WPORTS,mst_nn_vm_wr_),
   // read request
   `VMRMST(VM_RPORTS,mst_nn_vm_rd_),
   //
   // clock and rst_a
   //
// spyglass disable_block W240
//SMD:Input but not read
//SJ :clk and rst_a will be used in define VM_MEM_INJECT_READ_STALL and VM_MEM_INJECT_WRITE_STALL
   input logic      clk,                   // clock, all logic clocked at posedge
   input logic      rst_a                  // asynchronous rst_a, active high
// spyglass enable_block W240
  );

`ifdef VM_MEM_INJECT_READ_STALL
  logic [VM_RPORTS-1:0]   rd_stall_flag;
  logic [VM_RPORTS-1:0]   rd_stall_flag_dl1;
  logic [VM_RPORTS-1:0]   rd_stall_flag_dl2;
  logic [VM_RPORTS-1:0]   rd_stall_flag_dl3;

  always_ff @(posedge clk or posedge rst_a)
  begin : mem_rd_stall_flag_PROC
    if (rst_a ==1'b1)
    begin
      rd_stall_flag        <= '0;
      rd_stall_flag_dl1    <= '0;
      rd_stall_flag_dl2    <= '0;
      rd_stall_flag_dl3    <= '0;
    end
    else
    begin
      rd_stall_flag        <= $random;
      rd_stall_flag_dl1    <= rd_stall_flag;
      rd_stall_flag_dl2    <= rd_stall_flag_dl1;
      rd_stall_flag_dl3    <= rd_stall_flag_dl2;
    end
  end : mem_rd_stall_flag_PROC
`endif
  
`ifdef VM_MEM_INJECT_WRITE_STALL
  logic [VM_WPORTS-1:0]   wr_stall_flag;

  always_ff @(posedge clk or posedge rst_a)
  begin : mem_wr_stall_flag_PROC
    if (rst_a ==1'b1)
    begin
      wr_stall_flag        <= '0;
    end
    else
    begin
      wr_stall_flag        <= $random;
    end
  end : mem_wr_stall_flag_PROC
`endif

  always_comb
  begin : mem_connect_PROC
`ifndef DMA_VM_MEM_INJECT_READ_STALL_MLV
    mst_nn_vm_rd_cmd_valid  = slv_nn_vm_rd_cmd_valid; 
`endif
    mst_nn_vm_rd_cmd_addr   = slv_nn_vm_rd_cmd_addr ; 
    slv_nn_vm_rd_rvalid     = mst_nn_vm_rd_rvalid   ; 
    slv_nn_vm_rd_rdata      = mst_nn_vm_rd_rdata    ; 
    slv_nn_vm_rd_cmd_accept = mst_nn_vm_rd_cmd_accept;

`ifndef DMA_VM_MEM_INJECT_WRITE_STALL_MLV
    mst_nn_vm_wr_cmd_valid  = slv_nn_vm_wr_cmd_valid;
`endif
    mst_nn_vm_wr_cmd_addr   = slv_nn_vm_wr_cmd_addr ;
    mst_nn_vm_wr_wdata      = slv_nn_vm_wr_wdata    ;
    mst_nn_vm_wr_wstrb      = slv_nn_vm_wr_wstrb    ;
    slv_nn_vm_wr_cmd_accept = mst_nn_vm_wr_cmd_accept;
`ifdef VM_MEM_INJECT_READ_STALL
    for (int n=RD_IDX; n<VM_RPORTS; n++) 
    begin
`ifdef DMA_VM_MEM_INJECT_READ_STALL_MLV
       mst_nn_vm_rd_cmd_valid[n]  = (rd_stall_flag[n] == 1'b0) ? slv_nn_vm_rd_cmd_valid[n] : 1'b0; 
`endif
      slv_nn_vm_rd_cmd_accept[n] = (rd_stall_flag[n] == 1'b0) ? mst_nn_vm_rd_cmd_accept[n] : 1'b0;
      slv_nn_vm_rd_rvalid[n]     = (rd_stall_flag_dl3[n] == 1'b0) ? mst_nn_vm_rd_rvalid[n] : 1'b0;
    end
`endif
`ifdef VM_MEM_INJECT_WRITE_STALL
    for (int n=WR_IDX; n<VM_WPORTS; n++) 
    begin
`ifdef DMA_VM_MEM_INJECT_WRITE_STALL_MLV
       mst_nn_vm_wr_cmd_valid[n]  = (wr_stall_flag[n] == 1'b0) ? slv_nn_vm_wr_cmd_valid[n] : 1'b0; 
`endif
      slv_nn_vm_wr_cmd_accept[n] = (wr_stall_flag[n] == 1'b0) ? mst_nn_vm_wr_cmd_accept[n] : 1'b0;
    end
`endif
  end : mem_connect_PROC

endmodule : npu_vm_inj_stall
