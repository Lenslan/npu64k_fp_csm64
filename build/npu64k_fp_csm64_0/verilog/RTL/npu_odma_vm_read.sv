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
// Top-level file for the oDMA VM LOAD
//
 
`include "npu_defines.v"
`include "npu_vm_macros.svh"
module npu_odma_vm_read 
  import npu_types::*;
  #(
    // HLAPI type
    int  S        = DMA_VM_LANES,
    int  STU_D    = DMA_VM_LANES*8*ISIZE,
    int  DATA_LEN = $clog2(DMA_VM_LANES*ISIZE)
  )
(
  // VM AGU interface 
  input  vm_addr_t [S-1:0]      vm_raddr,    // Generated VM address 
  input  logic     [S-1:0]      vm_valid,    // Enable each VM lanes
  output logic                  vm_accept,   // Accept by VM load/store

  // VM Request Interface
  `VMRMST(S,vm_rd_),                          // VM read

  // VM Output data
  output logic                  out_valid,
  output logic [STU_D-1:0]      out_data,
  output logic [DATA_LEN:0]     out_len,
  input  logic                  out_accept,
  output logic                  idle,

  // clock and reset
  //
  input logic                   clk,         // clock, all logic clocked at posedge
  input logic                   rst_dp       // reset, active high

);

  localparam int LEN_W      = $clog2(ISIZE*PIX_W*S/8);

  // VM access acknowledge flags
  logic     [S-1:0]      ackf_r;
  logic     [S-1:0]      ackf_nxt;
  logic                  ackf_en;

  //command FIFO wires
  logic                  push_cmd;         //allocate a buffer
  logic                  cmd_fifo_avail;   //Any avaliable buffer space
  logic                  vld_cmd;          //cmd buffer is valid
  logic                  pop_cmd;          //release a buffer
  logic     [S-1:0]      vld_bnk;          //VM lanes involved in this command

  //Data FIFO wires
  logic     [S-1:0]      push_rd;
  ixpix_t   [S-1:0]      rd_fifo_wdata;
  logic     [S-1:0]      pop_rd;
  logic     [S-1:0]      vld_rd;
  ixpix_t   [S-1:0]      rd_fifo_rdata;

  //Planes data
  logic     [S*ISIZE*PIX_W-1:0]  data_pln;
  logic     [LEN_W:0]            data_len;

  //
  // Functions
  //
// spyglass disable_block W416
//SMD:Function return type width mismatch
//SJ :Int type $countones(b) return in some config and can be ignore
  function automatic logic [3:0] count1s(input logic [7:0] b);
    return $countones(b);
  endfunction : count1s
// spyglass enable_block W416

  // VM access
  assign vm_rd_cmd_valid = cmd_fifo_avail ? vm_valid & (~ackf_r) : '0;
  assign vm_rd_cmd_addr  = vm_raddr;
  assign push_rd         = vm_rd_rvalid;
  assign rd_fifo_wdata   = vm_rd_rdata;
  assign out_valid       =  (vld_rd == vld_bnk) && vld_cmd;
// spyglass disable_block W164a
//SMD:Width mismatch
//SJ :No overflow and ignore
  assign data_len        = {count1s({{(8-S){1'b0}},vld_bnk}),4'h0}; // units of ISIZE
// spyglass enable_block W164a
  // data process
generate
if(S==1) begin: Sis1
  always_comb
  begin : data_pln_PROC
    data_pln            =  'b0;
    data_pln = rd_fifo_rdata[0];
  end
end 
else begin: Sbiggerthan1
  always_comb
  begin : data_pln_PROC
    data_pln            =  'b0;
    for (int i=S-1; i>=0; i--) 
    begin
      if (vld_bnk[i]) 
      begin
        data_pln = {data_pln[(S-1)*ISIZE*PIX_W-1:0], rd_fifo_rdata[i]}; // shift-in data
      end
    end

  end
end
endgenerate 

  always_comb
  begin : vm_access_nxt_PROC
    vm_accept           =  'b0;
    push_cmd            =  'b0;
    pop_cmd             =  'b0;
    pop_rd              =  'b0;
    // VM load ports information
    ackf_en  = cmd_fifo_avail & (|vm_valid);
    ackf_nxt = vm_rd_cmd_accept | (~vm_rd_cmd_valid);
    if (&ackf_nxt)
    begin
      ackf_nxt  = '0;
      vm_accept = ackf_en;
      push_cmd  = ackf_en;
    end

    // data transferred
    if ((vld_rd == vld_bnk) && vld_cmd && out_accept)
    begin
      pop_cmd = 1'b1;
      pop_rd  = vld_bnk;
    end
  end : vm_access_nxt_PROC
  
  // Register Update 
  always_ff @(posedge clk or
              posedge rst_dp)
  begin : reg_update_PROC
    if (rst_dp == 1'b1)
    begin
      ackf_r           <=  'b0;
    end
    else
    begin
      if (ackf_en)
      begin
        ackf_r         <=  ackf_nxt;
      end
    end
  end : reg_update_PROC
  

  // FIFO to store command 
  npu_fifo 
  #(
    .SIZE   ( 6  ),
    .DWIDTH ( S  )
  )
  u_rcmd_fifo_inst
  (           
     .clk          ( clk                 ),
     .rst_a        ( rst_dp              ),
     .valid_write  ( push_cmd            ), 
     .accept_write ( cmd_fifo_avail      ),
     .data_write   ( vm_valid            ),
     .valid_read   ( vld_cmd             ),
     .accept_read  ( pop_cmd             ),
     .data_read    ( vld_bnk             )
  );


  // FIFO to store rdata
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentional unconnect
  for (genvar gvr_i = 0; gvr_i < S; gvr_i = gvr_i + 1)
    begin : rd_fifo_inst
      npu_fifo 
      #(
        .SIZE   ( 6           ),
        .DWIDTH ( ISIZE*PIX_W ),
        .FRCACC ( 1'b1        )
      )
      u_rdata_fifo_inst
      (           
         .clk          ( clk                 ),
         .rst_a        ( rst_dp              ),
         .valid_write  ( push_rd[gvr_i]      ), 
         .accept_write (                     ),
         .data_write   ( rd_fifo_wdata[gvr_i]),
         .valid_read   ( vld_rd[gvr_i]       ),
         .accept_read  ( pop_rd[gvr_i]       ),
         .data_read    ( rd_fifo_rdata[gvr_i])
      );
    end : rd_fifo_inst
// spyglass enable_block W287b

  // Assign Output
  assign  out_data    =  data_pln;
  assign  out_len     =  data_len;
  assign  idle        =  ~vld_cmd;

endmodule : npu_odma_vm_read
