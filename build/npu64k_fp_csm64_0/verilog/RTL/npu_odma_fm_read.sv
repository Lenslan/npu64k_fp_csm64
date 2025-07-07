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
// Top-level file for the npu_odma_vm_to_xm_transfer
//

`include "npu_defines.v"
`include "npu_vm_macros.svh"
`include "npu_axi_macros.svh"


module npu_odma_fm_read
  import npu_types::*;
  #(
    // HLAPI type
    parameter int  STU_D       = DMA_VM_LANES*8*ISIZE,
    parameter int  AD_WID      = $clog2(DMA_VM_LANES*ISIZE),
    parameter int  DATA_LEN    = AD_WID,
    parameter int  N           = NUM_FM_LOOPS,
    parameter int  DMA_S       = DMA_VM_LANES
  )
(
   input  logic                    hlapi_i_valid,   // new HLAPI issue descriptor valid
   input  dma_hlapi_i_t            hlapi_i,         // HLAPI input descriptor
   output logic                    hlapi_i_accept,  // new HLAPI issue descriptor accept

   // VM Request Interface
   `VMRMST(DMA_S,vm_rd_),                          // VM read

   // Buffer
   output logic                    fm_wr_valid,
   output logic [AD_WID-1:0]       fm_wr_num,
   output logic [AD_WID-1:0]       fm_wr_alsb,
   output logic [STU_D-1:0]        fm_wr_data,
   input  logic                    fm_wr_accept,

   // States, Reset, Clock
   output logic                    idle,            //AXI write is idle
   input  logic                    rst_dp,          //reset compute datapath
   input  logic                    clk
);

   logic [2-1:0]            hlapi_v_valid ;           // new HLAPI issue descriptor valid
   logic [2-1:0]            hlapi_v_accept;           // new HLAPI issue descriptor accept

   // VM AGU interface 
  vm_addr_t [DMA_S-1:0]       vm_raddr;    // Generated VM address 
  logic     [DMA_S-1:0]       vm_valid;    // Enable each VM lanes
  logic                       vm_accept;   // Accept by VM load/store
  logic                       vm_in_req;
  logic                       vm_in_ack;
  offset_t  [N-1:0]           vm_in_shp;
  logic     [DMA_S-1:0][N-1:0]vm_it_first;
  logic     [DMA_S-1:0][N-1:0]vm_it_last;
  logic     [DMA_S-1:0]       vm_it_vald;
  logic                       vm_it_req;
  logic                       vm_it_ack;
  logic                       vm_idle;
  logic                       agu_idle;
  logic                       xmp_idle;

  logic                       out_valid;
  logic     [STU_D-1:0]       out_data;
  logic     [DATA_LEN:0]      out_len;
  logic                       out_accept;

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
    .vm_addr       (vm_raddr            ),
    .vm_valid      (vm_valid            ),
    .vm_accept     (vm_accept           ),

    // Idle
    .idle          (agu_idle            )
  );

   npu_odma_vm_read
   #(
     .STU_D(STU_D),
     .S (DMA_VM_LANES)
    ) u_npu_odma_vm_read (
    // VM AGU input
    .vm_raddr        (vm_raddr      ),
    .vm_valid        (vm_valid      ),
    .vm_accept       (vm_accept     ),

    // VM access Interface
    `VMRINST_B(vm_rd_,vm_rd_),
    // Output data
    .out_valid       (out_valid     ),
    .out_len         (out_len       ),
    .out_accept      (out_accept    ),
    .out_data        (out_data      ),
    .idle            (vm_idle       ),

    .rst_dp          (rst_dp        ),
    .clk             (clk           )
    );

   // VM data process to XM
   npu_odma_xm_process 
   #(
     .STU_D(STU_D),
     .S (DMA_VM_LANES)
    ) u_npu_odma_xm_process (
    // Descr
    .hlapi_i_valid         (hlapi_v_valid[1] ),
    .hlapi_i_accept        (hlapi_v_accept[1]),
    .hlapi_i               (hlapi_i          ),

    // VM Output data
    .out_valid             (out_valid     ),
    .out_len               (out_len       ),
    .out_accept            (out_accept    ),
    .out_data              (out_data      ),

    // FM Buffer Output
    .fm_buffer_wr_valid    (fm_wr_valid   ),
    .fm_buffer_wr_num      (fm_wr_num     ),
    .fm_buffer_wr_alsb     (fm_wr_alsb    ),
    .fm_buffer_wr_data     (fm_wr_data    ),
    .fm_buffer_wr_accept   (fm_wr_accept  ),
    .idle                  (xmp_idle      ),

    .rst_dp                (rst_dp        ),
    .clk                   (clk           )
   );

  // Assign Output
  assign  idle   = agu_idle && vm_idle && xmp_idle;

endmodule : npu_odma_fm_read
