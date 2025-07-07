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


`include "npu_defines.v"
`include "npu_axi_macros.svh"


module npu_axi_remap
  import npu_types::*;
  #(
    parameter int  NUMMST  = 2,            // number of master ports (one slave)
    parameter int  NUMAP   = 1,            // number of address apertures in address decoder
    parameter int  AXIMDW  = 32,           // master data width
    parameter int  AXISDW  = 32,           // slave data width
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
   `AXISLV(AXIIDW,AXISDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // AXI master interface array
   `AXIMST(AXIIDW,AXIMDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_),
   // address decoder inputs
   input logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decbase,   // 4KB base address per aperture
   input logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decsize,   // 4KB mask to specify aperture size
   input logic [NUMAP-1:0][NUMMST-1:0]          decmst     // onehot0 mast of the decoded master
  );

   `AXIWIRES(AXIIDW,AXISDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,iaxi_slv_);

   npu_axi_cmd_t                                int_slv_ar;
   npu_axi_cmd_t                                int_slv_aw;

   always_comb
   begin : remap_waddr_PROC
     logic b;
     b = 1'b1;

     //default output
     int_slv_aw  =  axi_slv_aw;

     //detect && remap
     //AP0 --> original address range
     //AP1 --> remap base and size
     for (int a = 0; a < NUMAP; a=a+2)
     begin
       if (b & ((decsize[a] & axi_slv_aw.addr[NPU_AXI_ADDR_W-1:12]) == decbase[a]))
       begin
         b = 1'b0;
         int_slv_aw.addr = {(decbase[a+1] | (axi_slv_aw.addr[NPU_AXI_ADDR_W-1:12] & decsize[a+1])), axi_slv_aw.addr[11:0]};
       end
     end
   end : remap_waddr_PROC

   always_comb
   begin : remap_raddr_PROC
     logic b;
     b = 1'b1;

     //default output
     int_slv_ar  =  axi_slv_ar;

     //detect && remap
     //AP0 --> original address range
     //AP1 --> remap base and size
     for (int a = 0; a < NUMAP; a=a+2)
     begin
       if (b & ((decsize[a] & axi_slv_ar.addr[NPU_AXI_ADDR_W-1:12]) == decbase[a]))
       begin
         b = 1'b0;
         int_slv_ar.addr = {(decbase[a+1] | (axi_slv_ar.addr[NPU_AXI_ADDR_W-1:12] & decsize[a+1])), axi_slv_ar.addr[11:0]};
       end
     end
   end : remap_raddr_PROC

   
   
   assign iaxi_slv_arvalid  = axi_slv_arvalid;  // read command valid \
   assign axi_slv_arready   = iaxi_slv_arready; // read command accept \
   assign iaxi_slv_arid     = axi_slv_arid;     // read command ID \
   assign iaxi_slv_aruser   = axi_slv_aruser;   // read command user field \
   assign iaxi_slv_ar       = int_slv_ar;       // read command \
   assign axi_slv_rvalid    = iaxi_slv_rvalid;  // read data valid \
   assign iaxi_slv_rready   = axi_slv_rready;   // read data accept \
   assign axi_slv_rid       = iaxi_slv_rid;     // read data id \
   assign axi_slv_rdata     = iaxi_slv_rdata;   // read data \
   assign axi_slv_rresp     = iaxi_slv_rresp;   // read response \
   assign axi_slv_ruser     = iaxi_slv_ruser;   // read data user field \
   assign axi_slv_rlast     = iaxi_slv_rlast;   // read last \
   assign iaxi_slv_awvalid  = axi_slv_awvalid;  // write command valid \
   assign axi_slv_awready   = iaxi_slv_awready; // write command accept \
   assign iaxi_slv_awid     = axi_slv_awid;     // write command ID \
   assign iaxi_slv_awuser   = axi_slv_awuser;   // write command user field \
   assign iaxi_slv_aw       = int_slv_aw;       // write command \
   assign iaxi_slv_wvalid   = axi_slv_wvalid;   // write data valid \
   assign axi_slv_wready    = iaxi_slv_wready;  // write data accept \
   assign iaxi_slv_wdata    = axi_slv_wdata;    // write data \
   assign iaxi_slv_wstrb    = axi_slv_wstrb;    // write data strobe \
   assign iaxi_slv_wuser    = axi_slv_wuser;    // write data user field \
   assign iaxi_slv_wlast    = axi_slv_wlast;    // write data last \
   assign axi_slv_bvalid    = iaxi_slv_bvalid;  // write response valid \
   assign iaxi_slv_bready   = axi_slv_bready;   // write response accept \
   assign axi_slv_bid       = iaxi_slv_bid;     // write response id \
   assign axi_slv_buser     = iaxi_slv_buser;   // read data user field \
   assign axi_slv_bresp     = iaxi_slv_bresp;   // write response \

   npu_axi_bridge
   #(
     .AXIIDW   ( AXIIDW  ),
     .AXISAWUW ( AXIAWUW ),
     .AXISWUW  ( AXIWUW  ),
     .AXISBUW  ( AXIBUW  ),
     .AXISARUW ( AXIARUW ),
     .AXISRUW  ( AXIRUW  ),
     .AXIMAWUW ( AXIAWUW ),
     .AXIMWUW  ( AXIWUW  ),
     .AXIMBUW  ( AXIBUW  ),
     .AXIMARUW ( AXIARUW ),
     .AXIMRUW  ( AXIRUW  ),
     .AXISDW   ( AXISDW  ),
     .AXIMDW   ( AXIMDW  )
   )
   u_wid_cvt_inst
   (
     .clk    ( clk   ),
     .rst_a  ( rst_a ),
     `AXIINST(axi_slv_,iaxi_slv_),
     `AXIINST(axi_mst_,axi_mst_)
   );

endmodule : npu_axi_remap
