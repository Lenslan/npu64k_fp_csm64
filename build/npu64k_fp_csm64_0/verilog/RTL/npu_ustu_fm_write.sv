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
// Top-level file for the STU AGU
//

`include "npu_axi_macros.svh"

module npu_ustu_fm_write
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
   input   logic                 hlapi_i_valid,   // new HLAPI issue descriptor valid
   output  logic                 hlapi_i_accept,  // new HLAPI issue descriptor accept
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input   hlapi_stu_agu_t       hlapi_i,         // HLAPI input descriptor
// spyglass enable_block W240
   
   `AXIWMST(AXI_MST_IDW,STU_D,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,stu_fm_axi_),    // AXI FM data transfer, write-only
   output logic                  fm_rd_accept,
   output logic [5:0]            fm_rd_num,
   output logic [5:0]            fm_rd_alsb,
   input  logic [511:0]          fm_rd_data,
   input  logic [15:0]           fm_vld_size,

   output  logic [31:0]          fm_wr_trans,
   output  logic                 axi_wr_err,
   input   logic [64-1: 0]     vmid,
   output  logic                 idle,
   input   logic                 rst_dp,          // reset compute datapath
   input   logic                 clk
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
  logic                      fm_w_valid;
  xm_buf_t                   fm_w_request;
  logic                      fm_w_accept;

  logic                      fm_agu_idle;
  logic                      fm_axi_idle;
  logic                      boost;
  logic [1:0]                ost_cfg;

  npu_iterator
  #(
      .N (N),
      .S (1)
  ) u_npu_ustu_fm_write_iter (
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
    u_npu_ustu_fm_write_agu (
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
    .xm_valid      (fm_w_valid          ),
    .xm_request    (fm_w_request        ),
    .xm_accept     (fm_w_accept         ),
    // Idle
    .idle          (fm_agu_idle         )
  );

  npu_ustu_axi_write
  #(
    .AXI_MST_IDW(AXI_MST_IDW),
    .BUFFER_SIZE(BUFFER_SIZE),
    .MAXIAWUW(MAXIAWUW),
    .MAXIWUW(MAXIWUW ),
    .MAXIBUW(MAXIBUW ),
    .MAXIARUW(MAXIARUW),
    .MAXIRUW(MAXIRUW ),
    .AXI_OST(AXI_OST),
    .STU_D(STU_D)
   ) u_npu_ustu_axi_write (

   `AXIWINST(dma_daxi_,stu_fm_axi_),  // AXI data transfer, write-only
   // XM write data stream
   .xm_w_valid       (fm_w_valid    ),
   .xm_w_request     (fm_w_request  ),
   .xm_w_accept      (fm_w_accept   ),
   .boost            (boost         ),
   .ost_cfg          (ost_cfg       ),

   .buffer_rd_accept (fm_rd_accept  ),
   .buffer_rd_num    (fm_rd_num     ),
   .buffer_rd_alsb   (fm_rd_alsb    ),
   .buffer_rd_data   (fm_rd_data    ),
   .buffer_vld_size  (fm_vld_size   ),

   .vmid             (vmid          ),
   .idle             (fm_axi_idle   ),
   .err_st           (axi_wr_err    ),
   .rst_dp           (rst_dp        ),
   .clk              (clk           )
  );

  // Output Assign
  assign idle            =  fm_axi_idle & fm_agu_idle;
  assign fm_wr_trans     =  fm_len_trans;

endmodule : npu_ustu_fm_write
