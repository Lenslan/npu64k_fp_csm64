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

`include "npu_axi_macros.svh"
module npu_ustu_fm_read
  import npu_types::*;
  import npu_stu_types::*;
  #(
    // HLAPI type
    parameter int  N              = NUM_FM_LOOPS,
    parameter int  STU_D          = ISIZE*32,
    parameter int  BUFFER_SIZE    = 1024,
    parameter int  AXI_OST        = 16,
    parameter int  MAXIAWUW       = 1,             // AXI MMIO slave AW user width
    parameter int  MAXIWUW        = 1,             // AXI MMIO slave W user width
    parameter int  MAXIBUW        = 1,             // AXI MMIO slave B user width
    parameter int  MAXIARUW       = 1,             // AXI MMIO slave AR user width
    parameter int  MAXIRUW        = 1,             // AXI MMIO slave R user width
    parameter int  AXI_MST_IDW    = 1
  )
(
   // Signals from MMIO register, controlled by valid/accept handshake
   input   logic               hlapi_i_valid,   // new HLAPI issue descriptor valid
   output  logic               hlapi_i_accept,  // new HLAPI issue descriptor accept
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input   hlapi_stu_agu_t     hlapi_i,         // HLAPI input descriptor
// spyglass enable_block W240

   
   `AXIRMST(AXI_MST_IDW,STU_D,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,stu_fm_axi_),    // AXI FM data transfer, read-only

   output  logic               fm_wr_valid,
   output  logic [5:0]         fm_wr_num,
   output  logic [5:0]         fm_wr_alsb,
   output  logic [511:0]       fm_wr_data,
   input   logic               fm_wr_accept,

   input   logic               buffer_rls_valid,
   input   logic [5:0]         buffer_rls,
   output  logic [31:0]        fm_rd_trans,
   output  logic               axi_rd_err,
   input   logic [64-1: 0]        vmid,
   output  logic               idle,
   input   logic               rst_dp,          // reset compute datapath
   input   logic               clk
);

  //
  // FM Output iters
  logic                      fm_in_req;
  logic                      fm_in_ack;
  offset_t [N-1:0]           fm_in_shp;
  logic [NUM_FM_LOOPS-1:0]   fm_it_first;
  logic [NUM_FM_LOOPS-1:0]   fm_it_last;
  logic                      fm_it_vald;
  logic                      fm_it_req;
  logic                      fm_it_ack;
  logic [31:0]               fm_len_trans;

  // FM trans
  logic                      fm_r_valid;
  xm_buf_t                   fm_r_request;
  logic                      fm_r_accept;

  logic                      fm_agu_idle;
  logic                      fm_axi_idle;
  logic                      boost;
  logic [1:0]                ost_cfg;

  npu_iterator
  #(
      .N (N),
      .S (1)
  ) u_npu_ustu_fm_read_iter (
    .clk           (clk                 ),
    .rst_a         (rst_dp              ),
    .soft_rst      (1'b0                ),
    .in_req        (fm_in_req           ),
    .in_ack        (fm_in_ack           ),
    .in_shp        (fm_in_shp           ),
    .it_req        (fm_it_req           ),
    .it_ack        (fm_it_ack           ),
    .it_first      (fm_it_first         ),
    .it_last       (fm_it_last          ), 
    .it_vald       (fm_it_vald          ) 
  );

  npu_stu_xm_agu
    u_npu_ustu_fm_read_agu (
    .clk           (clk                 ),
    .rst_a         (rst_dp              ),
    // New descr issue
    .hlapi_i_valid (hlapi_i_valid       ),
    .hlapi_i_accept(hlapi_i_accept      ),
    .hlapi_i_seq   (hlapi_i             ),
    // Iterations
    .xm_in_req     (fm_in_req           ),
    .xm_in_ack     (fm_in_ack           ),
    .xm_in_shp     (fm_in_shp           ),
    .xm_it_req     (fm_it_req           ),
    .xm_it_ack     (fm_it_ack           ),
    .xm_it_first   (fm_it_first         ),
    .xm_it_last    (fm_it_last          ), 
    .xm_len_trans  (fm_len_trans        ),
    .boost         (boost               ),
    .ost_cfg       (ost_cfg             ),
    // XM sequence
    .xm_valid      (fm_r_valid          ),
    .xm_request    (fm_r_request        ),
    .xm_accept     (fm_r_accept         ),
    // Idle
    .idle          (fm_agu_idle         )
  );

  npu_ustu_axi_read
  #(
    .AXI_MST_IDW(AXI_MST_IDW),
    .MAXIAWUW(MAXIAWUW),
    .MAXIWUW(MAXIWUW ),
    .MAXIBUW(MAXIBUW ),
    .MAXIARUW(MAXIARUW),
    .MAXIRUW(MAXIRUW ),
    .AXI_OST(AXI_OST),
    .BUFFER_SIZE(BUFFER_SIZE),
    .STU_D(STU_D)
   ) u_npu_ustu_axi_read (

   `AXIRINST(dma_saxi_,stu_fm_axi_),  // AXI data transfer, read-only
   // XM write data stream
   .xm_r_valid       (fm_r_valid    ),
   .xm_r_request     (fm_r_request  ),
   .xm_r_accept      (fm_r_accept   ),
   .boost            (boost         ),
   .ost_cfg          (ost_cfg       ),

   .buffer_wr_valid  (fm_wr_valid   ),
   .buffer_wr_num    (fm_wr_num     ),
   .buffer_wr_alsb   (fm_wr_alsb    ),
   .buffer_wr_data   (fm_wr_data    ),
   .buffer_wr_accept (fm_wr_accept  ),

   .buffer_rls_valid (buffer_rls_valid),
   .buffer_rls       (buffer_rls    ),
   .vmid             (vmid          ),
   .idle             (fm_axi_idle   ),
   .err_st           (axi_rd_err    ),
   .rst_dp           (rst_dp        ),
   .clk              (clk           )
  );

  // Output Assign
  assign idle            =  fm_axi_idle & fm_agu_idle;
  assign fm_rd_trans     =  fm_len_trans;

  endmodule : npu_ustu_fm_read

