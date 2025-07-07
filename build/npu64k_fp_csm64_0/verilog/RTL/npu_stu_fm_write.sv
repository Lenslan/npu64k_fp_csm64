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

 
`include "npu_defines.v"
`include "npu_axi_macros.svh"

module npu_stu_fm_write
  import npu_types::*;
  #(
    // HLAPI type
    parameter int  N              = NUM_FM_LOOPS,
    parameter int  DMA_VM_LANES_L = 4,
    parameter int  STU_D          = DMA_VM_LANES_L*8*ISIZE,
    parameter int  AD_WID         = $clog2(DMA_VM_LANES_L*ISIZE),
    parameter int  META_BUF_SIZE2 = 1,
    parameter int  XM_BUF_SIZE    = 1024,
    parameter int  XM_BUF_SIZE2   = 5,
    parameter int  AXI_OST        = 16,
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
   input   pix_t               hlapi_i_zero,    // VM ZP
   
   `AXIWMST(AXI_MST_IDW,STU_D,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,stu_fm_axi_),    // AXI FM data transfer, write-only
// spyglass disable_block W240
//SMD:Declared input but not read
//SJ :Ignore stu_meta_axi because no compress in some config
   `AXIWMST(AXI_MST_IDW,STU_D,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,stu_meta_axi_),  // AXI Metadata transfer, write-only
// spyglass enable_block W240
   output  logic               fm_rd_accept,
   output  logic [AD_WID-1:0]  fm_rd_num,
   output  logic [AD_WID-1:0]  fm_rd_alsb,
   input   logic [STU_D-1:0]   fm_rd_data,
   input   logic [15:0]        fm_vld_size,

   input   logic [64-1: 0]  vmid,
   input   logic               read_idle,
   output  logic [31:0]        fm_wr_trans,
   output  logic               axi_wr_err,
   output  logic               idle,
   input   logic               rst_dp,          // reset compute datapath
   input   logic               clk
);

   logic   [3-1:0]             hlapi_v_valid;
   logic   [3-1:0]             hlapi_v_accept;

   //
   // Broadcast HLAPI handshake signals
   //
   npu_hs_broadcast
     #(.NUM (3))
   u_hs_inst
   (
    .clk        ( clk            ),
    .rst_a      ( rst_dp         ), 
    .hsi_valid  ( hlapi_i_valid  ),
    .hsi_accept ( hlapi_i_accept ),
    .hso_valid  ( hlapi_v_valid  ),
    .hso_accept ( hlapi_v_accept )
   );

  // FM buffer read
  logic                      ifm_rd_accept;
  logic [AD_WID-1:0]         ifm_rd_num;
  logic [AD_WID-1:0]         ifm_rd_alsb;
  logic [STU_D-1:0]          ifm_rd_data;
  logic [15:0]               ifm_vld_size;

  // Metadata Buffer
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

  // Compressed Block Container
  logic                      cps_len_valid;
  logic                      cps_full;
  logic [13:0]               cps_blen;
  logic [13:0]               cps_len;
  logic                      cps_len_accept;

  // IDLEs
  logic                      ifm_cps_idle;
  logic                      ifm_axi_idle;
  logic                      ifm_agu_idle;
  logic                      imeta_agu_idle;
  logic                      imeta_axi_idle;
  logic                      imeta_axi_err;
  logic                      ifm_axi_err;


  npu_stu_fm_compress
  #(
      .XM_BUF_SIZE2(XM_BUF_SIZE2),
      .DMA_VM_LANES_L(DMA_VM_LANES_L)
  ) u_npu_stu_fm_compress (
    .clk              (clk                 ),
    .rst_dp           (rst_dp              ),
    // New descr issue
    .hlapi_i_valid    (hlapi_v_valid[0]    ),
    .hlapi_i_accept   (hlapi_v_accept[0]   ),
    .hlapi_i_seq      (hlapi_i             ),
    .hlapi_i_zero     (hlapi_i_zero        ),

    // Normal Data input
    .buffer_rd_num    (fm_rd_num     ),
    .buffer_rd_alsb   (fm_rd_alsb    ),
    .buffer_rd_data   (fm_rd_data    ),
    .buffer_rd_accept (fm_rd_accept  ),
    .buffer_vld_size  (fm_vld_size   ),

    // Compressed Data/Normal Data Output
    .fm_rd_num        (ifm_rd_num    ),
    .fm_rd_alsb       (ifm_rd_alsb   ),
    .fm_rd_data       (ifm_rd_data   ),
    .fm_rd_accept     (ifm_rd_accept ),
    .fm_vld_size      (ifm_vld_size  ),

    // Compressed Container Block Lenth
    .cps_len_valid    (cps_len_valid ),
    .cps_full         (cps_full      ),
    .cps_blen         (cps_blen      ),
    .cps_len          (cps_len       ),
    .cps_len_accept   (cps_len_accept),

    // Idle
    .read_idle        (read_idle     ),
    .idle             (ifm_cps_idle  )
  );

  // FM Output iters
  logic                      ifm_in_req;
  logic                      ifm_in_ack;
  offset_t [N-1:0]           ifm_in_shp;
  logic [NUM_FM_LOOPS-1:0]   ifm_it_first;
  logic [NUM_FM_LOOPS-1:0]   ifm_it_last;
  logic                      ifm_it_vald;
  logic                      ifm_it_req;
  logic                      ifm_it_ack;
  logic [31:0]               ifm_len_trans;
  logic                      ifm_w_valid;
  xm_buf_t                   ifm_w_request;
  logic                      ifm_w_accept;
  logic                      boost;
  logic [1:0]                wr_ost;

  npu_iterator
  #(
      .N (N),
      .S (1)
  ) u_npu_stu_fm_iter (
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

  npu_stu_fm_cps_agu
  #(
      .DMA_VM_LANES_L(DMA_VM_LANES_L)
   ) u_npu_stu_cps_fm_agu (
    .clk             (clk                 ),
    .rst_a           (rst_dp              ),
    // New descr issue
    .hlapi_i_valid   (hlapi_v_valid[1]    ),
    .hlapi_i_accept  (hlapi_v_accept[1]   ),
    .hlapi_i_seq     (hlapi_i             ),
    // Iterations
    .fm_in_req       (ifm_in_req          ),
    .fm_in_ack       (ifm_in_ack          ),
    .fm_in_shp       (ifm_in_shp          ),
    .fm_it_req       (ifm_it_req          ),
    .fm_it_ack       (ifm_it_ack          ),
    .fm_it_first     (ifm_it_first        ),
    .fm_it_last      (ifm_it_last         ), 
    .fm_len_trans    (ifm_len_trans       ),

    // Compressed Container Block Lenth
    .cps_len_valid   (cps_len_valid       ),
    .cps_full        (cps_full            ),
    .cps_blen        (cps_blen            ),
    .cps_len         (cps_len             ),
    .cps_len_accept  (cps_len_accept      ),

    // Metabuffer Store 
    .meta_wr_valid   (imeta_wr_valid      ),
    .meta_wr_num     (imeta_wr_num        ),
    .meta_wr_alsb    (imeta_wr_alsb       ),
    .meta_wr_data    (imeta_wr_data       ),
    .meta_wr_accept  (imeta_wr_accept     ),

    // XM sequence
    .fm_valid        (ifm_w_valid         ),
    .fm_request      (ifm_w_request       ),
    .fm_accept       (ifm_w_accept        ),
    .boost           (boost               ),
    .wr_ost          (wr_ost              ),
    // Idle
    .idle            (ifm_agu_idle        )
  );

  npu_dma_axi_write
  #(
    .AXI_MST_IDW(AXI_MST_IDW),
    .AXI_OST(AXI_OST),
    .BUFFER_SIZE(XM_BUF_SIZE),
    .MAXIAWUW(MAXIAWUW),
    .MAXIWUW(MAXIWUW ),
    .MAXIBUW(MAXIBUW ),
    .MAXIARUW(MAXIARUW),
    .MAXIRUW(MAXIRUW ),
    .DMA_VM_LANES_L(DMA_VM_LANES_L),
    .STU_D(STU_D)
   ) u_npu_stu_fm_axi_write (

   `AXIWINST(dma_daxi_,stu_fm_axi_),  // AXI data transfer, write-only
   // XM write data stream
   .xm_w_valid       (ifm_w_valid   ),
   .xm_w_request     (ifm_w_request ),
   .xm_w_accept      (ifm_w_accept  ),
   .boost            (boost         ),
   .wr_ost           (wr_ost        ),

   .buffer_rd_accept (ifm_rd_accept ),
   .buffer_rd_num    (ifm_rd_num    ),
   .buffer_rd_alsb   (ifm_rd_alsb   ),
   .buffer_rd_data   (ifm_rd_data   ),
   .buffer_vld_size  (ifm_vld_size  ),

   .vmid             (vmid          ),
   .idle             (ifm_axi_idle  ),
   .err_st           (ifm_axi_err   ),
   .rst_dp           (rst_dp        ),
   .clk              (clk           )
  );

  assign     imeta_wr_accept   = 1'b0;
  assign     hlapi_v_accept[2] = 1'b1;
  assign     imeta_agu_idle    = 1'b1;
  assign     imeta_axi_idle    = 1'b1;
  assign     imeta_axi_err     = 1'b0;

  assign     stu_meta_axi_awvalid       = 1'b0;
  assign     stu_meta_axi_awid          = 1'b0;
  assign     stu_meta_axi_awuser        = '0;
  assign     stu_meta_axi_aw.addr       = '0;
  assign     stu_meta_axi_aw.cache      = 4'h0;   // device non-bufferable
  assign     stu_meta_axi_aw.prot       = 3'b010; // unprivileged, non-secure, data access
  assign     stu_meta_axi_aw.lock       = npu_axi_lock_normal_e;
  assign     stu_meta_axi_aw.burst      = npu_axi_burst_incr_e;
  assign     stu_meta_axi_aw.len        = 8'h00;
  assign     stu_meta_axi_aw.size       = 3'd6;   // 512b data
  assign     stu_meta_axi_aw.region     = 2'd0;
  assign     stu_meta_axi_wvalid        = 1'b0;
  assign     stu_meta_axi_wdata         = '0;
  assign     stu_meta_axi_wstrb         = '0;
  assign     stu_meta_axi_wuser         = '0;
  assign     stu_meta_axi_wlast         = 1'b0;
  assign     stu_meta_axi_bready        = 1'b1;   // always accept bresp

   // Output Assign
   assign idle         = ifm_axi_idle & ifm_agu_idle & imeta_axi_idle & imeta_agu_idle & ifm_cps_idle;
   assign axi_wr_err   = ifm_axi_err || imeta_axi_err;
// spyglass disable_block W164a
//SMD:Width missmatch
//SJ :No overflow
   assign fm_wr_trans  = ifm_len_trans;
// spyglass enable_block W164a

endmodule : npu_stu_fm_write
