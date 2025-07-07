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
// Top-level file for the iDMA XM to VM transfer
//
 
`include "npu_vm_macros.svh"
`include "npu_axi_macros.svh"

module npu_idma_fm_write
  import npu_types::*;
  #(
    parameter int  DMA_S       = DMA_VM_LANES,
    parameter int  N           = NUM_FM_LOOPS,
    parameter int  STU_D       = DMA_VM_LANES*8*ISIZE,
    parameter int  AD_WID      = $clog2(DMA_VM_LANES*ISIZE)
  )
(
  // Descr Input
  input  logic                  hlapi_i_valid ,// new HLAPI issue descriptor valid
  input  dma_hlapi_i_t          hlapi_i,       // HLAPI input descriptor
  output logic                  hlapi_i_accept,// new HLAPI issue descriptor accept

  // VM Request Interface
  `VMWMST(DMA_S,vm_wr_),                          // VM read

  output logic                  fm_rd_accept,
  output logic [AD_WID-1:0]     fm_rd_num,
  output logic [AD_WID-1:0]     fm_rd_alsb,
  input  logic [STU_D-1:0]      fm_rd_data,
  input  logic [15:0]           fm_vld_size,

  output logic                  idle,            //AXI read is idle

  // clock and reset
  //
  input logic                   clk,         // clock, all logic clocked at posedge
  input logic                   rst_dp       // reset, active high

);

   logic [2-1:0]            hlapi_v_valid ;           // new HLAPI issue descriptor valid
   logic [2-1:0]            hlapi_v_accept;           // new HLAPI issue descriptor accept

   // VM AGU
   vm_addr_t [DMA_S-1:0]    vm_waddr;    // Generated VM address 
   logic     [DMA_S-1:0]    vm_valid;    // Enable each VM lanes
   logic                    vm_accept;   // Accept by VM load/store
   logic                    vm_in_req;
   logic                    vm_in_ack;
   offset_t [N-1:0]         vm_in_shp;
   logic    [DMA_S-1:0][N-1:0]vm_it_first;
   logic    [DMA_S-1:0][N-1:0]vm_it_last;
   logic    [DMA_S-1:0]       vm_it_vald;
   logic                    vm_it_req;
   logic                    vm_it_ack;
   logic                    vm_idle;

   // VM Write
   logic                    out_valid;
   logic [STU_D-1:0]        out_data;
   logic                    out_accept;
   logic [STU_D/8-1:0]      out_wstrb;
   logic                    vm_write_idle;

   //
   // Broadcast HLAPI handshake signals
   //
   npu_hs_broadcast
     #(.NUM (2))
   u_hs_inst
   (
    .clk        ( clk            ),
    .rst_a      ( rst_dp         ), 
    .hsi_valid  ( hlapi_i_valid  ),
    .hsi_accept ( hlapi_i_accept ),
    .hso_valid  ( hlapi_v_valid  ),
    .hso_accept ( hlapi_v_accept )
   );

   npu_iterator
   #(
       .N (N),
       .S (DMA_S)
   ) u_npu_vm_iter (
     .clk           (clk                 ),
     .rst_a         (rst_dp              ),
     .soft_rst      (1'b0                ),
     .in_req        (vm_in_req           ),
     .in_ack        (vm_in_ack           ),
     .in_shp        (vm_in_shp           ),
     .it_req        (vm_it_req           ),
     .it_ack        (vm_it_ack           ),
     .it_first      (vm_it_first         ),
     .it_last       (vm_it_last          ),
     .it_vald       (vm_it_vald          ) 
   );

   npu_dma_vm_agu
   #(
       .N (N),
       .S (DMA_S)
   ) u_npu_vm_agu (
     .clk           (clk                 ),
     .rst_a         (rst_dp              ),
     // New descr issue
     .in_req        (hlapi_v_valid[0]    ),
     .in_ack        (hlapi_v_accept[0]   ),
     .in_shp        (hlapi_i.vm_seq      ),
     // Iterations
     .vm_in_req     (vm_in_req           ),
     .vm_in_ack     (vm_in_ack           ),
     .vm_in_shp     (vm_in_shp           ),
     .vm_it_req     (vm_it_req           ),
     .vm_it_ack     (vm_it_ack           ),
     .vm_it_first   (vm_it_first         ),
     .vm_it_last    (vm_it_last          ), 
     .vm_it_vald    (vm_it_vald          ),

     // VM sequence
     .vm_addr       (vm_waddr            ),
     .vm_valid      (vm_valid            ),
     .vm_accept     (vm_accept           ),

     // Idle
     .idle          (vm_idle             )
   );


   // XM data process to VM
   npu_idma_xm_process 
   #(
     .STU_D(STU_D),
     .S (DMA_VM_LANES)
    ) u_npu_idma_xm_process (
    // Descr
    .hlapi_i_valid        (hlapi_v_valid[1] ),
    .hlapi_i_accept       (hlapi_v_accept[1]),
    .hlapi_i              (hlapi_i          ),

    // Data Lenth
    .vm_valid             (vm_valid      ),

    // FM Buffer Input
    .fm_buffer_rd_num     (fm_rd_num     ),
    .fm_buffer_rd_alsb    (fm_rd_alsb    ),
    .fm_buffer_rd_data    (fm_rd_data    ),
    .fm_buffer_rd_accept  (fm_rd_accept  ),
    .fm_buffer_vld_size   (fm_vld_size   ),

    // Output data
    .out_valid            (out_valid     ),
    .out_accept           (out_accept    ),
    .out_data             (out_data      ),
    .out_wstrb            (out_wstrb     ),

    .rst_dp               (rst_dp        ),
    .clk                  (clk           )
   );

   // VM write
   npu_idma_vm_write
   #(
     .STU_D(STU_D),
     .S (DMA_VM_LANES)
    ) u_npu_idma_vm_write (
    // VM AGU input
    .vm_waddr        (vm_waddr      ),
    .vm_valid        (vm_valid      ),
    .vm_accept       (vm_accept     ),

    // VM access Interface
    `VMWINST_B(vm_wr_,vm_wr_),

    // Output data
    .out_valid       (out_valid     ),
    .out_accept      (out_accept    ),
    .out_data        (out_data      ),
    .out_wstrb       (out_wstrb     ),

    .idle            (vm_write_idle ),

    .rst_dp          (rst_dp        ),
    .clk             (clk           )
    );


   // Assign Output
   assign idle    =   vm_idle && vm_write_idle;


endmodule : npu_idma_fm_write

