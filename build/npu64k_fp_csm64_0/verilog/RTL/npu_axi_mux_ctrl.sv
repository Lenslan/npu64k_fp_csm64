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
// If apertures overlap then the last will win
// e.g. decbase[3]=20'hf0000, decsize[3]=20'hffff0, decmst[3]='d4
// means aperture 3 from 0xf0000000 to 0xf000ffff will map to master port log2(4)=2
// if apertures overlap then last will win, so if a default aperture is required define it
// so for a default port set decbase[0] = 0, decsize[0] = ffffffff, dec


`include "npu_axi_macros.svh"

module npu_axi_mux_ctrl
  import npu_types::*;
  #(
    parameter int  NUMSLV  = 2,            // number of slave ports (one master)
    parameter int  AXIDW   = 32,           // data width
    parameter int  AXISIDW = 4,            // AXI slave ID width
    parameter int  AXIMIDW = 5,            // AXI master ID width, needs to be equal to AXISIDW+log2(NUMSLV)
    parameter int  AXIAWUW = 1,            // AXI slave AW user width
    parameter int  AXIWUW  = 1,            // AXI slave W user width
    parameter int  AXIBUW  = 1,            // AXI slave B user width
    parameter int  AXIARUW = 1,            // AXI slave AR user width
    parameter int  AXIRUW  = 1             // AXI slave R user width
    )
  (
   input  logic                                 clk,          // clock
   input  logic                                 rst_a,        // asynchronous reset, active high, synchronous deassertion
   output logic [NUMSLV-1:0]                    wfifo_rd,     // write FIFO output data
   // array of AXI slave interfaces
   `AXINODATASLVN(NUMSLV,AXISIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // AXI master interface
   `AXINODATAMST(AXIMIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_)
   );
  //`VPOST_OFF
  // local types
  typedef logic [NUMSLV-1:0] slv_oh_t;
  // local wires
  slv_oh_t                  wgnt;            // write command grant
  logic                     wfifo_wval;      // write FIFO input valid
  logic                     wfifo_wacc;      // write FIFO input accept
  logic                     wfifo_rval;      // write FIFO output valid
  logic                     wfifo_racc;      // write FIFO output accept
  slv_oh_t                  rgnt;            // read command grant
  logic                     wnxt;
  logic                     rnxt;
  
  
  //////////////////////////////////////////////////////////////////////
  //
  // Write datapath
  //
  //////////////////////////////////////////////////////////////////////

  
  //
  // write command arbitration
  //
  slv_oh_t                  wreq;
  assign    wreq = {NUMSLV{wfifo_wacc}} & axi_slv_awvalid;

  npu_arb
  #(.NUM_REQ( $bits(slv_oh_t) ) )
  u_aw_arb
    (
     .clk   ( clk             ),
     .rst_a ( rst_a           ),
     .req   ( wreq            ),
     .gnt   ( wgnt            ),
     .ok    ( wnxt            )
     );
  assign wnxt            = axi_mst_awready || (~axi_mst_awvalid);
  assign axi_mst_awvalid = wfifo_wacc & (axi_slv_awvalid != '0);
  assign axi_slv_awready = wfifo_wacc & axi_mst_awready ? wgnt : '0;
  assign wfifo_wval      = axi_mst_awvalid & axi_mst_awready;
  if (AXIMIDW > AXISIDW) begin
// spyglass disable_block W116
// SMD: OR bus should have equal assign width
// SJ: Left-handside MSB is the extra bit for error
    always_comb
    begin : awdec_PROC
      // default outputs
      axi_mst_awid   = '0;
      axi_mst_awuser = '0;
      axi_mst_aw     = '0;
      for (int i = 0; i < NUMSLV; i++)
      begin
        if (wgnt[i])
        begin
          axi_mst_awid[AXIMIDW-1:AXISIDW] |= unsigned'(i);
          axi_mst_awid[AXISIDW-1:0]       |= axi_slv_awid[i];
          axi_mst_awuser                  |= axi_slv_awuser[i];
          axi_mst_aw                      |= axi_slv_aw[i];
        end
      end
    end : awdec_PROC
// spyglass enable_block W116
  end
  else begin
    always_comb
    begin : awdec_PROC
      // default outputs
      axi_mst_awid   = '0;
      axi_mst_awuser = '0;
      axi_mst_aw     = '0;
      for (int i = 0; i < NUMSLV; i++)
      begin
        if (wgnt[i])
        begin
          axi_mst_awid[AXISIDW-1:0]       |= axi_slv_awid[i];
          axi_mst_awuser                  |= axi_slv_awuser[i];
          axi_mst_aw                      |= axi_slv_aw[i];
        end
      end
    end : awdec_PROC
  end

  
  //
  // write data including ordering FIFO
  //
  //`VPOST_ON
  npu_fifo
    #(
      .SIZE   ( 4               ),
      .DWIDTH ( $bits(slv_oh_t) ),
      .FRCVAL ( 1'b0            ),
      .FRCACC ( 1'b0            )
      ) 
  u_wfifo_inst
    (
     .clk          ( clk        ),
     .rst_a        ( rst_a      ),
     .valid_write  ( wfifo_wval ),
     .accept_write ( wfifo_wacc ),
     .data_write   ( wgnt       ),
     .valid_read   ( wfifo_rval ),
     .accept_read  ( wfifo_racc ),
     .data_read    ( wfifo_rd   )
     );
  //`VPOST_OFF
  assign axi_mst_wvalid = wfifo_rval ? |(wfifo_rd & axi_slv_wvalid) : '0;
  assign axi_slv_wready = wfifo_rval & axi_mst_wready ? wfifo_rd : '0;
  assign wfifo_racc     = axi_mst_wvalid & axi_mst_wready & axi_mst_wlast;
  always_comb
  begin : wdec_PROC
    // default outputs
    axi_mst_wuser = '0;
    axi_mst_wlast = '0;
    for (int i = 0; i < NUMSLV; i++)
    begin
      if (wfifo_rd[i])
      begin
        axi_mst_wuser |= axi_slv_wuser[i];
        axi_mst_wlast |= axi_slv_wlast[i];
      end
    end
  end : wdec_PROC

  
  //
  // write response return
  //
  assign axi_slv_buser = {NUMSLV{axi_mst_buser}};
  assign axi_slv_bresp = {NUMSLV{axi_mst_bresp}};
  assign axi_slv_bid   = {NUMSLV{axi_mst_bid[AXISIDW-1:0]}};
  if (AXIMIDW > AXISIDW) begin
    always_comb
    begin : b_PROC
      // default outputs
      axi_slv_bvalid = '0;
      axi_mst_bready = 1'b0;
      for (int i = 0; i < NUMSLV; i++)
      begin
// spyglass disable_block W362
// SMD: logic width mismatch
// SJ: Ignored due to loop iter used
        if (axi_mst_bid[AXIMIDW-1:AXISIDW] == unsigned'(i))
        begin
          axi_slv_bvalid[i] |= axi_mst_bvalid;
          axi_mst_bready    |= axi_slv_bready[i];
        end
// spyglass enable_block W362
      end
    end : b_PROC
  end
  else begin
    always_comb
    begin : b_PROC
      // default outputs
      axi_slv_bvalid = '0;
      axi_mst_bready = 1'b0;
      for (int i = 0; i < NUMSLV; i++)
      begin
        axi_slv_bvalid[i] |= axi_mst_bvalid;
        axi_mst_bready    |= axi_slv_bready[i];
      end
    end : b_PROC
  end


  
  //////////////////////////////////////////////////////////////////////
  //
  // Read datapath
  //
  //////////////////////////////////////////////////////////////////////


  //
  // read command arbitration
  //
  npu_arb
  #(.NUM_REQ( $bits(slv_oh_t) ) )
  u_ar_arb
    (
     .clk   ( clk             ),
     .rst_a ( rst_a           ),
     .req   ( axi_slv_arvalid ),
     .gnt   ( rgnt            ),
     .ok    ( rnxt            )
     );
  assign rnxt            = axi_mst_arready || (~axi_mst_arvalid);
  assign axi_mst_arvalid = (axi_slv_arvalid != '0);
  assign axi_slv_arready = axi_mst_arready ? rgnt : '0;
  if (AXIMIDW > AXISIDW) begin
// spyglass disable_block W116
// SMD: OR bus should have equal assign width
// SJ: Left-handside MSB is the extra bit for error
    always_comb
    begin : ardec_PROC
      // default outputs
      axi_mst_arid   = '0;
      axi_mst_aruser = '0;
      axi_mst_ar     = '0;
      for (int i = 0; i < NUMSLV; i++)
      begin
        if (rgnt[i])
        begin
          axi_mst_arid[AXIMIDW-1:AXISIDW] |= unsigned'(i);
          axi_mst_arid[AXISIDW-1:0]       |= axi_slv_arid[i];
          axi_mst_aruser                  |= axi_slv_aruser[i];
          axi_mst_ar                      |= axi_slv_ar[i];
        end
      end
    end : ardec_PROC
// spyglass enable_block W116
  end
  else begin
    always_comb
    begin : ardec_PROC
      // default outputs
      axi_mst_arid   = '0;
      axi_mst_aruser = '0;
      axi_mst_ar     = '0;
      for (int i = 0; i < NUMSLV; i++)
      begin
        if (rgnt[i])
        begin
          axi_mst_arid[AXISIDW-1:0]       |= axi_slv_arid[i];
          axi_mst_aruser                  |= axi_slv_aruser[i];
          axi_mst_ar                      |= axi_slv_ar[i];
        end
      end
    end : ardec_PROC
  end


  //
  // read response return
  //
  assign axi_slv_ruser = {NUMSLV{axi_mst_ruser}};
  assign axi_slv_rresp = {NUMSLV{axi_mst_rresp}};
  assign axi_slv_rlast = {NUMSLV{axi_mst_rlast}};
  assign axi_slv_rid   = {NUMSLV{axi_mst_rid[AXISIDW-1:0]}};
  if (AXIMIDW > AXISIDW) begin
    always_comb
    begin : r_PROC
      // default outputs
      axi_slv_rvalid = '0;
      axi_mst_rready = 1'b0;
      for (int i = 0; i < NUMSLV; i++)
      begin
// spyglass disable_block W362
// SMD: logic width mismatch
// SJ: Ignored due to loop iter used
        if (axi_mst_rid[AXIMIDW-1:AXISIDW] == unsigned'(i))
        begin
          axi_slv_rvalid[i] = axi_mst_rvalid;
          axi_mst_rready    = axi_slv_rready[i];
        end
// spyglass enable_block W362
      end
    end : r_PROC
  end
  else begin
    always_comb
    begin : r_PROC
      // default outputs
      axi_slv_rvalid = '0;
      axi_mst_rready = 1'b0;
      for (int i = 0; i < NUMSLV; i++)
      begin
        axi_slv_rvalid[i] = axi_mst_rvalid;
        axi_mst_rready    = axi_slv_rready[i];
      end
    end : r_PROC
  end
  
  
`ifdef ABV_ON
  // assertions
  property pcfg;
  @(rst_a)  AXIMIDW == (AXISIDW+$clog2(NUMSLV));
  endproperty : pcfg
  assert property (pcfg) else $warning("Warning: ID width should match AXIMIDW == (AXISIDW+$clog2(NUMSLV))");  
`endif
  
endmodule : npu_axi_mux_ctrl
