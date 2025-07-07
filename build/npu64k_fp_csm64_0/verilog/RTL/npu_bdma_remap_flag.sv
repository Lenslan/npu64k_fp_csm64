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


// Route AXI transactions based on address bits
// The address map is passed as a set of signals
// If apertures overlap then the first will win
// e.g. decbase[3]=20'hf0000, decsize[3]=20'hffff0, decmst[3]='d4
// means aperture 3 from 0xf0000000 to 0xf000ffff will map to master port log2(4)=2
// if apertures overlap then last will win, so if a default aperture is required define it
// so for a default port set decbase[0] = 0, decsize[0] = ffffffff, dec


`include "npu_axi_macros.svh"


module npu_bdma_remap_flag
  import npu_types::*;
  #(
    parameter int  NUM     = 2,            // number of master ports (one slave)
    parameter int  AXIDW   = 32,           // master data width
    parameter int  AXIIDW  = 4,            // AXI slave ID width
    parameter int  AXIAWUW = 1,            // AXI slave AW user width
    parameter int  AXIWUW  = 1,            // AXI slave W user width
    parameter int  AXIBUW  = 1,            // AXI slave B user width
    parameter int  AXIARUW = 1,            // AXI slave AR user width
    parameter int  AXIRUW  = 1             // AXI slave R user width
    )
  (
   input  logic                                 clk,          // clock
   input  logic                                 rst_a,        // asynchronous reset, active high, synchronous deassertion
   // single AXI slave interface
   `AXISLVN(NUM,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // AXI master interface array
   `AXIMSTN(NUM,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_),
   input  logic [1:0]                           ptidx_a
  );

   always_comb
   begin : remap_AR_flag_PROC
    int i;
    case (ptidx_a)
    2'b01:
      begin
        for (i = 0; i < NUM; i++)
        begin
          axi_mst_aruser[i][68-1:0] = axi_slv_aruser[i][68-1:0];
          axi_mst_aruser[i][68+0]   = axi_slv_aruser[i][68+1];
          axi_mst_aruser[i][68+1]   = axi_slv_aruser[i][68+0];
          axi_mst_aruser[i][68+2]   = axi_slv_aruser[i][68+3];
          axi_mst_aruser[i][68+3]   = axi_slv_aruser[i][68+2];
        end
      end
    2'b10:
      begin
        for (i = 0; i < NUM; i++)
        begin
          axi_mst_aruser[i][68-1:0] = axi_slv_aruser[i][68-1:0];
          axi_mst_aruser[i][68+0]   = axi_slv_aruser[i][68+2];
          axi_mst_aruser[i][68+1]   = axi_slv_aruser[i][68+3];
          axi_mst_aruser[i][68+2]   = axi_slv_aruser[i][68+0];
          axi_mst_aruser[i][68+3]   = axi_slv_aruser[i][68+1];
        end
      end
    2'b11:
      begin
        for (i = 0; i < NUM; i++)
        begin
          axi_mst_aruser[i][68-1:0] = axi_slv_aruser[i][68-1:0];
          axi_mst_aruser[i][68+0]   = axi_slv_aruser[i][68+3];
          axi_mst_aruser[i][68+1]   = axi_slv_aruser[i][68+2];
          axi_mst_aruser[i][68+2]   = axi_slv_aruser[i][68+1];
          axi_mst_aruser[i][68+3]   = axi_slv_aruser[i][68+0];
        end
      end
    default:
      begin
        axi_mst_aruser = axi_slv_aruser;
      end
    endcase // case (mpy_cfg)
   end : remap_AR_flag_PROC

   assign axi_mst_arvalid  = axi_slv_arvalid;  // read command valid \
   assign axi_slv_arready  = axi_mst_arready; // read command accept \
   assign axi_mst_arid     = axi_slv_arid;     // read command ID \
   assign axi_mst_ar       = axi_slv_ar;       // read command \
   assign axi_slv_rvalid   = axi_mst_rvalid;  // read data valid \
   assign axi_mst_rready   = axi_slv_rready;   // read data accept \
   assign axi_slv_rid      = axi_mst_rid;     // read data id \
   assign axi_slv_rdata    = axi_mst_rdata;   // read data \
   assign axi_slv_rresp    = axi_mst_rresp;   // read response \
   assign axi_slv_ruser    = axi_mst_ruser;   // read data user field \
   assign axi_slv_rlast    = axi_mst_rlast;   // read last \
   assign axi_mst_awvalid  = axi_slv_awvalid;  // write command valid \
   assign axi_slv_awready  = axi_mst_awready; // write command accept \
   assign axi_mst_awid     = axi_slv_awid;     // write command ID \
   assign axi_mst_awuser   = axi_slv_awuser;   // write command user field \
   assign axi_mst_aw       = axi_slv_aw;       // write command \
   assign axi_mst_wvalid   = axi_slv_wvalid;   // write data valid \
   assign axi_slv_wready   = axi_mst_wready;  // write data accept \
   assign axi_mst_wdata    = axi_slv_wdata;    // write data \
   assign axi_mst_wstrb    = axi_slv_wstrb;    // write data strobe \
   assign axi_mst_wuser    = axi_slv_wuser;    // write data user field \
   assign axi_mst_wlast    = axi_slv_wlast;    // write data last \
   assign axi_slv_bvalid   = axi_mst_bvalid;  // write response valid \
   assign axi_mst_bready   = axi_slv_bready;   // write response accept \
   assign axi_slv_bid      = axi_mst_bid;     // write response id \
   assign axi_slv_buser    = axi_mst_buser;   // read data user field \
   assign axi_slv_bresp    = axi_mst_bresp;   // write response \


endmodule : npu_bdma_remap_flag
