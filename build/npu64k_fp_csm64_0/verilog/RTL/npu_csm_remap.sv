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
// address range is {a[log2(CSM_SIZE)-1:12+log2(NUM_BANK*VG)], [11+log2(NUM_BANK*VG):12+log2(NUM_BANK)], a[11+log2(NUM_BANK):12], a[11:0]}


`include "npu_defines.v"
`include "npu_axi_macros.svh"

module npu_csm_remap
  import npu_types::*;
  #(
    parameter int  NUMMST  = 1,            // number of master ports (one slave)
    parameter int  NUMAP   = 1,            // number of address apertures in address decoder
    parameter int  AXIDW   = 32,           // AXI data width
    parameter int  AXIIDW  = 1,            // AXI slave ID width
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
   `AXISLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // AXI master interface array
   `AXIMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_),
   // address decoder inputs
   input logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decbase,   // 4KB base address per aperture, decbase[15:12] is the number of group per VM
   input logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decsize,   // 4KB mask to specify aperture size
   input logic [NUMAP-1:0][NUMMST-1:0]          decmst     // onehot0 mast of the decoded master
  );

   localparam int NUM_BANK    = `NPU_CSM_BANKS_PER_GRP;       // Number of banks per group
   localparam int CSM_SIZE    = `NPU_CSM_SIZE_PER_GRP;        // Total CSM size
   localparam int DRPBIT      = 3;                            // decbase[DRPBIT+11:12] means number of groups per VM which need to be droped from address to CLN
   localparam int BANK_ADDR   = $clog2(NUM_BANK)+12;          // addr[BANK_ADDR-1:12] means different banks in single group
   localparam int INBANK_ADDR = 12;                           // addr[11:0] is in same bank
   localparam int CSM_ADDR    = $clog2(CSM_SIZE);             // addr[CSM_ADDR-1:BANK_ADDR+decbase[DRPBIT]] in different 4KB pages
   localparam int ADDR_BITS   = 26;

   npu_axi_cmd_t                                int_slv_ar;
   npu_axi_cmd_t                                int_slv_aw;

   always_comb
   begin : remap_address_PROC
      int_slv_ar = axi_slv_ar;
      int_slv_aw = axi_slv_aw;

      int_slv_ar.addr  = {axi_slv_ar.addr[ADDR_BITS-1:BANK_ADDR] >> decbase[0][INBANK_ADDR+DRPBIT-1:INBANK_ADDR], axi_slv_ar.addr[12-1:0]};
      int_slv_aw.addr  = {axi_slv_aw.addr[ADDR_BITS-1:BANK_ADDR] >> decbase[0][INBANK_ADDR+DRPBIT-1:INBANK_ADDR], axi_slv_aw.addr[12-1:0]};
   end : remap_address_PROC


   assign axi_mst_arvalid  = axi_slv_arvalid; // read command valid \
   assign axi_slv_arready  = axi_mst_arready; // read command accept \
   assign axi_mst_arid     = axi_slv_arid;    // read command ID \
   assign axi_mst_aruser   = axi_slv_aruser;  // read command user field \
   assign axi_mst_ar       = int_slv_ar;      // read command \
   assign axi_slv_rvalid   = axi_mst_rvalid;  // read data valid \
   assign axi_mst_rready   = axi_slv_rready;  // read data accept \
   assign axi_slv_rid      = axi_mst_rid;     // read data id \
   assign axi_slv_rdata    = axi_mst_rdata;   // read data \
   assign axi_slv_rresp    = axi_mst_rresp;   // read response \
   assign axi_slv_ruser    = axi_mst_ruser;   // read data user field \
   assign axi_slv_rlast    = axi_mst_rlast;   // read last \
   assign axi_mst_awvalid  = axi_slv_awvalid; // write command valid \
   assign axi_slv_awready  = axi_mst_awready; // write command accept \
   assign axi_mst_awid     = axi_slv_awid;    // write command ID \
   assign axi_mst_awuser   = axi_slv_awuser;  // write command user field \
   assign axi_mst_aw       = int_slv_aw;      // write command \
   assign axi_mst_wvalid   = axi_slv_wvalid;  // write data valid \
   assign axi_slv_wready   = axi_mst_wready;  // write data accept \
   assign axi_mst_wdata    = axi_slv_wdata;   // write data \
   assign axi_mst_wstrb    = axi_slv_wstrb;   // write data strobe \
   assign axi_mst_wuser    = axi_slv_wuser;   // write data user field \
   assign axi_mst_wlast    = axi_slv_wlast;   // write data last \
   assign axi_slv_bvalid   = axi_mst_bvalid;  // write response valid \
   assign axi_mst_bready   = axi_slv_bready;  // write response accept \
   assign axi_slv_bid      = axi_mst_bid;     // write response id \
   assign axi_slv_buser    = axi_mst_buser;   // read data user field \
   assign axi_slv_bresp    = axi_mst_bresp;   // write response \



endmodule : npu_csm_remap
