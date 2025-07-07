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

// AXI module to convert AXI ID width only, no output ID


`include "npu_defines.v"
`include "npu_axi_macros.svh"

module npu_axi_idtrack
  import npu_types::*;
  #(
    parameter int SIZE    = 1,    // max number of pending transactions
    parameter int AXISIDW = 5,    // primaray side ID width
    parameter int AXIMIDW = 4,    // secondary side ID width
    parameter int AXIDW   = 128,  // data-width
    parameter int AXIAWUW = 1,    // user-signal width
    parameter int AXIWUW  = 1,
    parameter int AXIBUW  = 1,
    parameter int AXIARUW = 1,
    parameter int AXIRUW  = 1
  )
  (
   // clock and reset
   input logic clk,
   input logic rst_a,
   // AXI slave interface
   `AXISLV(AXISIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // AXI master interface
   `AXIMST(AXIMIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_)
   );
  // local wires
  logic ar_fifo_valid_write;
  logic ar_fifo_accept_write;
  logic ar_fifo_accept_read;
  logic aw_fifo_valid_write;
  logic aw_fifo_accept_write;
  logic aw_fifo_accept_read;

  // flow controls
  assign axi_mst_arvalid     = axi_slv_arvalid & ar_fifo_accept_write;
  assign axi_slv_arready     = axi_mst_arready & ar_fifo_accept_write;
  assign ar_fifo_valid_write = axi_slv_arvalid & axi_mst_arready;
  assign ar_fifo_accept_read = axi_mst_rvalid & axi_slv_rready & axi_mst_rlast;
  assign axi_mst_awvalid     = axi_slv_awvalid & aw_fifo_accept_write;
  assign axi_slv_awready     = axi_mst_awready & aw_fifo_accept_write;
  assign aw_fifo_valid_write = axi_slv_awvalid & axi_mst_awready;
  assign aw_fifo_accept_read = axi_mst_bvalid & axi_slv_bready;

  // cross assign most signals
  assign axi_mst_arid      = '0;
  assign axi_mst_aruser    = axi_slv_aruser;
  assign axi_mst_ar.addr   = axi_slv_ar.addr;
  assign axi_mst_ar.cache  = axi_slv_ar.cache;
  assign axi_mst_ar.prot   = axi_slv_ar.prot;
  assign axi_mst_ar.lock   = axi_slv_ar.lock;
  assign axi_mst_ar.burst  = axi_slv_ar.burst;
  assign axi_mst_ar.len    = axi_slv_ar.len;
  assign axi_mst_ar.size   = axi_slv_ar.size;
  assign axi_mst_ar.region = axi_slv_ar.region;
  assign axi_slv_rvalid    = axi_mst_rvalid;
  assign axi_mst_rready    = axi_slv_rready;
  assign axi_slv_rdata     = axi_mst_rdata;
  assign axi_slv_rresp     = axi_mst_rresp;
  assign axi_slv_ruser     = axi_mst_ruser;
  assign axi_slv_rlast     = axi_mst_rlast;
  assign axi_mst_awid      = '0;
  assign axi_mst_awuser    = axi_slv_awuser;
  assign axi_mst_aw.addr   = axi_slv_aw.addr;
  assign axi_mst_aw.cache  = axi_slv_aw.cache;
  assign axi_mst_aw.prot   = axi_slv_aw.prot;
  assign axi_mst_aw.lock   = axi_slv_aw.lock;
  assign axi_mst_aw.burst  = axi_slv_aw.burst;
  assign axi_mst_aw.len    = axi_slv_aw.len;
  assign axi_mst_aw.size   = axi_slv_aw.size;
  assign axi_mst_aw.region = axi_slv_aw.region;
  assign axi_mst_wvalid    = axi_slv_wvalid;
  assign axi_slv_wready    = axi_mst_wready;
  assign axi_mst_wdata     = axi_slv_wdata;
  assign axi_mst_wstrb     = axi_slv_wstrb;
  assign axi_mst_wuser     = axi_slv_wuser;
  assign axi_mst_wlast     = axi_slv_wlast;
  assign axi_slv_bvalid    = axi_mst_bvalid;
  assign axi_mst_bready    = axi_slv_bready;
  assign axi_slv_buser     = axi_mst_buser;
  assign axi_slv_bresp     = axi_mst_bresp;


  //
  // FIFO for tracking pending readresponses
  //
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected
  npu_fifo
  #(
    .SIZE    ( SIZE    ),
    .DWIDTH  ( AXISIDW ),
    .FRCVAL  ( 1'b1    )
  ) 
  u_arid_fifo_inst
  (
    .clk          ( clk                  ),
    .rst_a        ( rst_a                ),
    .valid_write  ( ar_fifo_valid_write  ),
    .accept_write ( ar_fifo_accept_write ),
    .data_write   ( axi_slv_arid         ),
    .valid_read   (                      ), // intentionally left dunconnected
    .accept_read  ( ar_fifo_accept_read  ),
    .data_read    ( axi_slv_rid          )
  );
  

  //
  // FIFO for tracking pending read responses
  //
  npu_fifo
  #(
    .SIZE    ( SIZE    ),
    .DWIDTH  ( AXISIDW ),
    .FRCVAL  ( 1'b1    )
  ) 
  u_awid_fifo_inst
  (
    .clk          ( clk                  ),
    .rst_a        ( rst_a                ),
    .valid_write  ( aw_fifo_valid_write  ),
    .accept_write ( aw_fifo_accept_write ),
    .data_write   ( axi_slv_awid         ),
    .valid_read   (                      ), // intentionally left unconnected
    .accept_read  ( aw_fifo_accept_read  ),
    .data_read    ( axi_slv_bid          )
  );
// spyglass enable_block W287b

endmodule : npu_axi_idtrack
