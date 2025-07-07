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
// Top-level file for the iDMA FM read with compression & gather support
//
 
`include "npu_defines.v"
`include "npu_axi_macros.svh"
`include "npu_vm_macros.svh"

module npu_idma_fm_read
  import npu_types::*;
  #(
    // HLAPI type
    parameter int  N              = NUM_FM_LOOPS,
    parameter int  STU_D          = ISIZE*DMA_VM_LANES*8,
    parameter int  AD_WID         = $clog2(DMA_VM_LANES*ISIZE),
    parameter int  AXI_OST        = 16,
    parameter int  META_BUF_SIZE2 = 1,
    parameter int  XM_BUF_SIZE    = 1024,
    parameter int  MAXIAWUW       = 1,
    parameter int  MAXIWUW        = 1,
    parameter int  MAXIBUW        = 1,
    parameter int  MAXIARUW       = 1,
    parameter int  MAXIRUW        = 1, 
    parameter int  AXI_MST_IDW    = 1
  )
(
   // Signals from MMIO register, controlled by valid/accept handshake
   input   logic               hlapi_i_valid,   // new HLAPI issue descriptor valid
   output  logic               hlapi_i_accept,  // new HLAPI issue descriptor accept
   input   hlapi_xm_agu_t      hlapi_i,         // HLAPI input descriptor
   input   logic               hlapi_i_init,    // iDMA VM init mode enable 
   input   logic               hlapi_i_gather,  // iDMA VM Gather mode enable 
   input   pix_t               hlapi_i_zero,    // iDMA VM ZP 
   input   logic [31:0]        hlapi_i_bc,      // iDMA B-DMA
   
   `AXIRMST(AXI_MST_IDW,STU_D,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,idma_fm_axi_),    // AXI FM data transfer, read-only
// spyglass disable_block W240
//SMD:Declared input but not read
//SJ :Ignore idma meta axi signals because no compress in some config
   `AXIRMST(AXI_MST_IDW,STU_D,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,idma_meta_axi_),  // AXI Metadata transfer, read-only
// spyglass enable_block W240
   `VMRMST(1,vm_rd_),                                    // VM read for gather load
   input   logic [64-1: 0]     vmid,

   output  logic               fm_wr_valid,
   output  logic [AD_WID-1:0]  fm_wr_num,
   output  logic [AD_WID-1:0]  fm_wr_alsb,
   output  logic [STU_D-1:0]   fm_wr_data,
   input   logic               fm_wr_accept,

   output  logic [31:0]        fm_rd_trans,
   output  logic               axi_rd_err,
   output  logic               idle,
   input   logic               rst_dp,          // reset compute datapath
   input   logic               clk
);

   logic   [4-1:0]             hlapi_v_valid;
   logic   [4-1:0]             hlapi_v_accept;


   //
   // Broadcast HLAPI handshake signals
   //
   npu_hs_broadcast
     #(.NUM (4))
   u_hs_inst
   (
    .clk        ( clk            ),
    .rst_a      ( rst_dp         ), 
    .hsi_valid  ( hlapi_i_valid  ),
    .hsi_accept ( hlapi_i_accept ),
    .hso_valid  ( hlapi_v_valid  ),
    .hso_accept ( hlapi_v_accept )
   );

  logic                      imeta_agu_idle;
  logic                      imeta_axi_idle;
  logic                      imeta_axi_err;
  logic                      ifm_agu_idle;
  logic                      ifm_axi_idle;
  logic                      ifm_axi_err;
  logic                      ifm_dcp_idle;
  logic                      boost;
  logic  [1:0]               rd_ost;
  logic  [7:0]               bc_flags;

  // Metadata buffer
  logic                      imeta_wr_valid;
  logic  [AD_WID-1:0]        imeta_wr_num;
  logic  [AD_WID-1:0]        imeta_wr_alsb;
  logic  [STU_D-1:0]         imeta_wr_data;
  logic                      imeta_wr_accept;

  logic                      imeta_rd_accept;
  logic [AD_WID-1:0]         imeta_rd_num;
  logic [AD_WID-1:0]         imeta_rd_alsb;
  logic [STU_D-1:0]          imeta_rd_data;
  logic [15:0]               imeta_vld_size;

  // Metadata buffer
  logic                      ifm_wr_valid;
  logic  [AD_WID-1:0]        ifm_wr_num;
  logic  [AD_WID-1:0]        ifm_wr_alsb;
  logic  [STU_D-1:0]         ifm_wr_data;
  logic                      ifm_wr_accept;

  // Meta Input iters
  logic                      imeta_in_req;
  logic                      imeta_in_ack;
  offset_t [N-1:0]           imeta_in_shp;
  logic [NUM_FM_LOOPS-1:0]   imeta_it_first;
  logic [NUM_FM_LOOPS-1:0]   imeta_it_last;
  logic                      imeta_it_vald;
  logic                      imeta_it_req;
  logic                      imeta_it_ack;
  logic [31:0]               imeta_len_trans;
  logic                      imeta_r_valid;
  xm_buf_t                   imeta_r_request;
  logic                      imeta_r_accept;

  // Gather Load
  logic [15:0][1:0]          gather_idx; //{idh8,idw8}
  logic                      gather_valid;
  logic                      gather_accept;

  assign  imeta_rd_data       =   '0;
  assign  imeta_vld_size      =   '0;
  assign  imeta_axi_idle      =   1'b1;
  assign  imeta_axi_err       =   1'b0;
  assign  imeta_agu_idle      =   1'b1;
  assign  hlapi_v_accept[0]   =   1'b1;
  assign  imeta_len_trans     =   '0;

  assign  idma_meta_axi_arvalid    = 1'b0;
  assign  idma_meta_axi_arid       =  '0;
  assign  idma_meta_axi_aruser     =  '0;
  assign  idma_meta_axi_ar.addr    =  '0;
  assign  idma_meta_axi_ar.cache   = 4'h0;   // device non-bufferable
  assign  idma_meta_axi_ar.prot    = 3'b010; // unprivileged, non-secure, data access
  assign  idma_meta_axi_ar.lock    = npu_axi_lock_normal_e;
  assign  idma_meta_axi_ar.burst   = npu_axi_burst_incr_e;
  assign  idma_meta_axi_ar.len     = 8'h00;
  assign  idma_meta_axi_ar.size    = 3'd6;   // 512b data
  assign  idma_meta_axi_ar.region  = 2'd0;   // 512b data
  assign  idma_meta_axi_rready     = 1'b0;

  npu_idma_gather_idx_load
   u_npu_idma_gather_idx_load (
    .clk             (clk                 ),
    .rst_a           (rst_dp              ),
    // New descr issue
    .hlapi_i_valid   (hlapi_v_valid[1]    ),
    .hlapi_i_accept  (hlapi_v_accept[1]   ),
    .hlapi_i_seq     (hlapi_i             ),
    .hlapi_i_gather  (hlapi_i_gather      ),

    // VM read
    `VMRINST_B(vm_rd_,vm_rd_),

    // gather IDX
    .gather_idx      (gather_idx          ),
    .gather_valid    (gather_valid        ),
    .gather_accept   (gather_accept       )
  );

  // FM Input iters
  logic                      ifm_in_req;
  logic                      ifm_in_ack;
  offset_t [N-1:0]           ifm_in_shp;
  logic [NUM_FM_LOOPS-1:0]   ifm_it_first;
  logic [NUM_FM_LOOPS-1:0]   ifm_it_last;
  logic                      ifm_it_vald;
  logic                      ifm_it_req;
  logic                      ifm_it_ack;
  logic [31:0]               ifm_len_trans;
  logic                      ifm_r_valid;
  xm_buf_t                   ifm_r_request;
  logic                      ifm_r_accept;


  npu_iterator
  #(
      .N (N),
      .S (1)
  ) u_npu_idma_fm_iter (
    .clk             (clk                 ),
    .rst_a           (rst_dp              ),
    .soft_rst        (1'b0                ),
    .in_req          (ifm_in_req          ),
    .in_ack          (ifm_in_ack          ),
    .in_shp          (ifm_in_shp          ),
    .it_req          (ifm_it_req          ),
    .it_ack          (ifm_it_ack          ),
    .it_first        (ifm_it_first        ),
    .it_last         (ifm_it_last         ), 
    .it_vald         (ifm_it_vald         ) 
  );

  npu_idma_fm_dcp_agu
   u_npu_dma_fm_dcp_agu (
    .clk             (clk                 ),
    .rst_a           (rst_dp              ),
    // New descr issue
    .hlapi_i_valid   (hlapi_v_valid[2]    ),
    .hlapi_i_accept  (hlapi_v_accept[2]   ),
    .hlapi_i_seq     (hlapi_i             ),
    .hlapi_i_init    (hlapi_i_init        ),
    .hlapi_i_gather  (hlapi_i_gather      ),
    .hlapi_i_bc      (hlapi_i_bc          ),
    // Iterations
    .fm_in_req       (ifm_in_req          ),
    .fm_in_ack       (ifm_in_ack          ),
    .fm_in_shp       (ifm_in_shp          ),
    .fm_it_req       (ifm_it_req          ),
    .fm_it_ack       (ifm_it_ack          ),
    .fm_it_first     (ifm_it_first        ),
    .fm_it_last      (ifm_it_last         ), 
    .fm_len_trans    (ifm_len_trans       ),
    // Metabuffer Load
    .meta_rd_num     (imeta_rd_num        ),
    .meta_rd_alsb    (imeta_rd_alsb       ),
    .meta_rd_data    (imeta_rd_data       ),
    .meta_rd_accept  (imeta_rd_accept     ),
    .meta_vld_size   (imeta_vld_size      ),
    // gather VM load
    .gather_idx      (gather_idx          ),
    .gather_valid    (gather_valid        ),
    .gather_accept   (gather_accept       ),

    // XM sequence
    .fm_valid        (ifm_r_valid         ),
    .fm_request      (ifm_r_request       ),
    .fm_accept       (ifm_r_accept        ),
    .boost           (boost               ),
    .rd_ost          (rd_ost              ),
    .bc_flags        (bc_flags            ),

    // Idle
    .idle            (ifm_agu_idle        )
  );

  npu_dma_axi_read
  #(
    .AXI_MST_IDW (AXI_MST_IDW),
    .MAXIAWUW(MAXIAWUW),
    .MAXIWUW(MAXIWUW ),
    .MAXIBUW(MAXIBUW ),
    .MAXIARUW(MAXIARUW),
    .MAXIRUW(MAXIRUW ),
    .AXI_OST(AXI_OST),
    .BUFFER_SIZE(XM_BUF_SIZE),
    .DMA_VM_LANES_L(DMA_VM_LANES),
    .STU_D(STU_D)
   ) u_npu_idma_fm_axi_read (

   `AXIRINST(dma_saxi_,idma_fm_axi_),  // AXI data transfer, read-only

   // XM read data stream
   .xm_r_valid       (ifm_r_valid    ),
   .xm_r_request     (ifm_r_request  ),
   .xm_r_accept      (ifm_r_accept   ),
   .boost            (boost          ),
   .rd_ost           (rd_ost         ),
   .bc_flags         (bc_flags       ),

   .buffer_wr_valid  (ifm_wr_valid   ),
   .buffer_wr_num    (ifm_wr_num     ),
   .buffer_wr_alsb   (ifm_wr_alsb    ),
   .buffer_wr_data   (ifm_wr_data    ),
   .buffer_wr_accept (ifm_wr_accept  ),

   .vmid             (vmid           ),
   .idle             (ifm_axi_idle   ),
   .err_st           (ifm_axi_err    ),
   .rst_dp           (rst_dp         ),
   .clk              (clk            )
  );

  npu_stu_fm_decompress
  #(
   .DMA_VM_LANES_L(DMA_VM_LANES)
   )
   u_npu_idma_fm_decompress (
    .clk              (clk                 ),
    .rst_dp           (rst_dp              ),
    // New descr issue
    .hlapi_i_valid    (hlapi_v_valid[3]    ),
    .hlapi_i_accept   (hlapi_v_accept[3]   ),
    .hlapi_i_seq      (hlapi_i             ),
    .hlapi_i_zero     (hlapi_i_zero        ),

    // Compressed Data/Normal Data input
    .buffer_wr_valid  (ifm_wr_valid  ),
    .buffer_wr_num    (ifm_wr_num    ),
    .buffer_wr_alsb   (ifm_wr_alsb   ),
    .buffer_wr_data   (ifm_wr_data   ),
    .buffer_wr_accept (ifm_wr_accept ),

    // Normal Data output
    .fm_wr_valid      (fm_wr_valid   ),
    .fm_wr_num        (fm_wr_num     ),
    .fm_wr_alsb       (fm_wr_alsb    ),
    .fm_wr_data       (fm_wr_data    ),
    .fm_wr_accept     (fm_wr_accept  ),

    // Idle
    .fm_axi_idle      (ifm_axi_idle  ),
    .fm_agu_idle      (ifm_agu_idle  ),
    .idle             (ifm_dcp_idle  )
  );

   // Output Assign
   assign idle         = ifm_axi_idle & ifm_agu_idle & imeta_axi_idle & imeta_agu_idle & ifm_dcp_idle;
   assign axi_rd_err   = ifm_axi_err || imeta_axi_err;
// spyglass disable_block W164a
//SMD:Width missmatch
//SJ :no overflow and ignore
   assign fm_rd_trans  = ifm_len_trans + imeta_len_trans;
// spyglass enable_block W164a

endmodule : npu_idma_fm_read
