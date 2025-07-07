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

// AXI register slice


`include "npu_defines.v"
`include "npu_axi_macros.svh"

module npu_axi_slice_sub
  import npu_types::*;
  #(
    parameter int AXIIDW       = 4,
    parameter int AXIDW        = 128,
    parameter int AXIAWUW      = 1,
    parameter int AXIWUW       = 1,
    parameter int AXIBUW       = 1,
    parameter int AXIARUW      = 1,
    parameter int AXIRUW       = 1,
    // FIFO depth specification
    parameter int AWFIFO_DEPTH = 1,
    parameter int WFIFO_DEPTH  = 2,
    parameter int BFIFO_DEPTH  = 1,
    parameter int ARFIFO_DEPTH = 1,
    parameter int RFIFO_DEPTH  = 2
  )
  (
   // clock and reset
   input logic clk,
   input logic rst_a,
   // AXI slave interface
   `AXISLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // AXI master interface
   `AXIMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_)
   );
  // type definitions
  typedef struct packed {
    logic          [AXIIDW-1:0]  awid;
    logic          [AXIAWUW-1:0] awuser;
    npu_axi_cmd_t                aw;
  } aw_t;
  typedef struct packed {
    logic          [AXIDW-1:0]   wdata;
    logic          [AXIDW/8-1:0] wstrb;
    logic          [AXIWUW-1:0]  wuser;
    logic                        wlast;
  } w_t;
  typedef struct packed {
    logic          [AXIIDW-1:0]  bid;
    logic          [AXIBUW-1:0]  buser;
    npu_axi_resp_t               bresp;
  } b_t;
  typedef struct packed {
    logic          [AXIIDW-1:0]  arid;
    logic          [AXIARUW-1:0] aruser;
    npu_axi_cmd_t                ar;
  } ar_t;
  typedef struct packed {
    logic          [AXIIDW-1:0]  rid;
    logic          [AXIDW-1:0]   rdata;
    npu_axi_resp_t               rresp;
    logic          [AXIRUW-1:0]  ruser;
    logic                        rlast;
  } r_t;

  
  // Write command FIFO
  //
  aw_t axi_slv_awtmp;
  aw_t axi_mst_awtmp;
  assign axi_slv_awtmp.awid   = axi_slv_awid;
  assign axi_slv_awtmp.awuser = axi_slv_awuser;
  assign axi_slv_awtmp.aw     = axi_slv_aw;
  assign axi_mst_awid         = axi_mst_awtmp.awid;
  assign axi_mst_awuser       = axi_mst_awtmp.awuser;
  assign axi_mst_aw           = axi_mst_awtmp.aw;
  
  npu_fifo
    #(
      .SIZE   ( AWFIFO_DEPTH ),
      .DWIDTH ( $bits(aw_t)  ),
      .FRCVAL ( 1'b0         ),
      .FRCACC ( 1'b0         )
      )
  aw_fifo_inst
    (
     .clk          ( clk             ),
     .rst_a        ( rst_a           ),
     .valid_write  ( axi_slv_awvalid ),
     .accept_write ( axi_slv_awready ),
     .data_write   ( axi_slv_awtmp   ),
     .valid_read   ( axi_mst_awvalid ),
     .accept_read  ( axi_mst_awready ),
     .data_read    ( axi_mst_awtmp   )
     );


  //
  // Write data FIFO
  //
  w_t axi_slv_wtmp;
  w_t axi_mst_wtmp;
  assign axi_slv_wtmp.wdata = axi_slv_wdata;
  assign axi_slv_wtmp.wstrb = axi_slv_wstrb;
  assign axi_slv_wtmp.wuser = axi_slv_wuser;
  assign axi_slv_wtmp.wlast = axi_slv_wlast;
  assign axi_mst_wdata      = axi_mst_wtmp.wdata;
  assign axi_mst_wstrb      = axi_mst_wtmp.wstrb;
  assign axi_mst_wuser      = axi_mst_wtmp.wuser;
  assign axi_mst_wlast      = axi_mst_wtmp.wlast;
   
   npu_fifo
    #(
      .SIZE   ( WFIFO_DEPTH ),
      .DWIDTH ( $bits(w_t)  ),
      .FRCVAL ( 1'b0        ),
      .FRCACC ( 1'b0        )
      )
  w_fifo_inst
    (
     .clk          ( clk             ),
     .rst_a        ( rst_a           ),
     .valid_write  ( axi_slv_wvalid ),
     .accept_write ( axi_slv_wready ),
     .data_write   ( axi_slv_wtmp   ),
     .valid_read   ( axi_mst_wvalid ),
     .accept_read  ( axi_mst_wready ),
     .data_read    ( axi_mst_wtmp   )
     );
  

  //
  // Write response FIFO
  //
  b_t axi_slv_btmp;
  b_t axi_mst_btmp;
  assign axi_mst_btmp.bid   = axi_mst_bid;
  assign axi_mst_btmp.buser = axi_mst_buser;
  assign axi_mst_btmp.bresp = axi_mst_bresp;
  assign axi_slv_bid        = axi_slv_btmp.bid;
  assign axi_slv_buser      = axi_slv_btmp.buser;
  assign axi_slv_bresp      = axi_slv_btmp.bresp;
  
  npu_fifo
    #(
      .SIZE   ( BFIFO_DEPTH ),
      .DWIDTH ( $bits(b_t)  ),
      .FRCVAL ( 1'b0        ),
      .FRCACC ( 1'b0        )
      )
  b_fifo_inst
    (
     .clk          ( clk             ),
     .rst_a        ( rst_a           ),
     .valid_write  ( axi_mst_bvalid ),
     .accept_write ( axi_mst_bready ),
     .data_write   ( axi_mst_btmp   ),
     .valid_read   ( axi_slv_bvalid ),
     .accept_read  ( axi_slv_bready ),
     .data_read    ( axi_slv_btmp   )
     );
  

  //
  // Read command FIFO
  //
  ar_t axi_slv_artmp;
  ar_t axi_mst_artmp;
  assign axi_slv_artmp.arid   = axi_slv_arid;
  assign axi_slv_artmp.aruser = axi_slv_aruser;
  assign axi_slv_artmp.ar     = axi_slv_ar;
  assign axi_mst_arid         = axi_mst_artmp.arid;
  assign axi_mst_aruser       = axi_mst_artmp.aruser;
  assign axi_mst_ar           = axi_mst_artmp.ar;

  npu_fifo
    #(
      .SIZE   ( ARFIFO_DEPTH ),
      .DWIDTH ( $bits(ar_t)  ),
      .FRCVAL ( 1'b0         ),
      .FRCACC ( 1'b0         )
      )
  ar_fifo_inst
    (
     .clk          ( clk             ),
     .rst_a        ( rst_a           ),
     .valid_write  ( axi_slv_arvalid ),
     .accept_write ( axi_slv_arready ),
     .data_write   ( axi_slv_artmp   ),
     .valid_read   ( axi_mst_arvalid ),
     .accept_read  ( axi_mst_arready ),
     .data_read    ( axi_mst_artmp   )
     );

  
  //
  // Read data FIFO
  //
  r_t axi_slv_rtmp;
  r_t axi_mst_rtmp;
  assign axi_mst_rtmp.rid   = axi_mst_rid;
  assign axi_mst_rtmp.rdata = axi_mst_rdata;
  assign axi_mst_rtmp.rresp = axi_mst_rresp;
  assign axi_mst_rtmp.ruser = axi_mst_ruser;
  assign axi_mst_rtmp.rlast = axi_mst_rlast;
  assign axi_slv_rid        = axi_slv_rtmp.rid;
  assign axi_slv_rdata      = axi_slv_rtmp.rdata;
  assign axi_slv_rresp      = axi_slv_rtmp.rresp;
  assign axi_slv_ruser      = axi_slv_rtmp.ruser;
  assign axi_slv_rlast      = axi_slv_rtmp.rlast;
   
   npu_fifo
    #(
      .SIZE   ( RFIFO_DEPTH ),
      .DWIDTH ( $bits(r_t)  ),
      .FRCVAL ( 1'b0        ),
      .FRCACC ( 1'b0        )
      )
  r_fifo_inst
    (
     .clk          ( clk            ),
     .rst_a        ( rst_a          ),
     .valid_write  ( axi_mst_rvalid ),
     .accept_write ( axi_mst_rready ),
     .data_write   ( axi_mst_rtmp   ),
     .valid_read   ( axi_slv_rvalid ),
     .accept_read  ( axi_slv_rready ),
     .data_read    ( axi_slv_rtmp   )
     );

endmodule : npu_axi_slice_sub
