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

// AXI full switch matrix
// The address map is passed as a set of signals
// If apertures overlap then the last will win
// e.g. decbase[3]=20'hf0000, decsize[3]=20'hffff0, decmst[3]='d2
// means aperture 3 from 0xf0000000 to 0xf000ffff will map to master port 2
// if apertures overlap then last will win,
// so for a default port set it as aperture 0 as decbase[0] = 0, decsize[0] = ffffffff, decmst[0] = default master port
// address spaces not mapped will return an decerr response



`include "npu_defines.v"
`include "npu_axi_macros.svh"

module npu_axi_matrix_ctrl
  import npu_types::*;
  #(
    parameter int  NUMSLV  = 2,            // number of slave ports
    parameter int  NUMMST  = 2,            // number of master ports
    parameter int  NUMAP   = 1,            // number of address apertures in address decoder
    parameter int  AXIDW   = 32,           // data width
    parameter int  AXISIDW = 4,            // AXI slave ID width
    parameter int  AXIMIDW = 5,            // AXI master ID width, needs to be equal to AXISIDW+log2(NUMSLV)
    parameter int  AXIAWUW = 1,            // AXI slave AW user width
    parameter int  AXIWUW  = 1,            // AXI slave W user width
    parameter int  AXIBUW  = 1,            // AXI slave B user width
    parameter int  AXIARUW = 1,            // AXI slave AR user width
    parameter int  AXIRUW  = 1,            // AXI slave R user width
    parameter int  SYNCFB  = 0,            // AXI slave Sync flag base
    parameter int  SYNCFW  = 1,            // AXI slave Sync flag size
    parameter int  BC      = 0             // AXI use broadcase routine
    )
  (
   input  logic                                 clk,          // clock
   input  logic                                 rst_a,        // asynchronous reset, active high, synchronous deassertion
   input  logic [1:0]                           ptidx_a,      // GRPID
   // array of AXI slave interfaces
   `AXINODATASLVN(NUMSLV,AXISIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // array of AXI master interfaces
   `AXINODATAMSTN(NUMMST,AXIMIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_),
// spyglass disable_block W241
//SMD: Output pin never set
//SJ : Will be set when SLV > 1 and will not be used when SLV=1
   output [NUMMST-1:0][NUMSLV-1:0]              wfifo_rd,
   output [NUMSLV-1:0][NUMMST:0]                rgnt,
// spyglass enable_block W241
   input logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decbase,     // 4KB base address per aperture
   input logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decsize,     // 4KB mask to specify aperture size
   input logic [NUMAP-1:0][NUMMST-1:0]          decmst,      // onehot index of the decoded master
   input logic [NUMSLV-1:0][NUMMST-1:0]         decslv       // enable slave to master connections
   );
  // AXI wires [NUMSLV][NUMMST]
  `AXINODATAWIRESN(NUMSLV*NUMMST,AXISIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_int_);
  // AXI wires [NUMMST][NUMSLV]
  `AXINODATAWIRESN(NUMMST*NUMSLV,AXISIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_trn_);
  localparam int NUMID = AXISIDW>4 ? 16 : 1<<AXISIDW; // max number of pending IDs
  

  ////////////////////////////////////////////////////////////////////////////////////////
  //
  // Slave demux instances
  //
  ////////////////////////////////////////////////////////////////////////////////////////
  if (NUMMST == 1)
  begin : bp_slv_GEN
    assign axi_int_arvalid = axi_slv_arvalid;
    assign axi_slv_arready = axi_int_arready;
    assign axi_int_arid    = axi_slv_arid;
    assign axi_int_aruser  = axi_slv_aruser;
    assign axi_int_ar      = axi_slv_ar;
    assign axi_slv_rvalid  = axi_int_rvalid;
    assign axi_int_rready  = axi_slv_rready;
    assign axi_slv_rid     = axi_int_rid;
    //assign axi_slv_rdata   = axi_int_rdata;
    assign axi_slv_rresp   = axi_int_rresp;
    assign axi_slv_ruser   = axi_int_ruser;
    assign axi_slv_rlast   = axi_int_rlast;
    assign axi_int_awvalid = axi_slv_awvalid;
    assign axi_slv_awready = axi_int_awready;
    assign axi_int_awid    = axi_slv_awid;
    assign axi_int_awuser  = axi_slv_awuser;
    assign axi_int_aw      = axi_slv_aw;
    assign axi_int_wvalid  = axi_slv_wvalid;
    assign axi_slv_wready  = axi_int_wready;
    //assign axi_int_wdata   = axi_slv_wdata;
    //assign axi_int_wstrb   = axi_slv_wstrb;
    assign axi_int_wuser   = axi_slv_wuser;
    assign axi_int_wlast   = axi_slv_wlast;
    assign axi_slv_bvalid  = axi_int_bvalid;
    assign axi_int_bready  = axi_slv_bready;
    assign axi_slv_bid     = axi_int_bid;
    assign axi_slv_buser   = axi_int_buser;
    assign axi_slv_bresp   = axi_int_bresp;
  end : bp_slv_GEN
  else
  begin : slv_GEN
    genvar gs;
    `AXINODATAWIRESN(NUMSLV*NUMMST,AXISIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_int1_);
    `AXINODATAWIRESN(NUMSLV*NUMMST,AXISIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_int2_);
    for (gs = 0; gs < NUMSLV; gs++)
    begin : gs_slv_GEN
      // local mask to disable some apertures
      logic [NUMAP-1:0][NUMMST-1:0] ldecmst;
      always_comb
      begin : ldec_PROC
        for (int a = 0; a < NUMAP; a++)
        begin
          ldecmst[a] = decmst[a] & decslv[gs];
        end
      end : ldec_PROC
  
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
      // address decoding and demuxing
      npu_axi_demux_ctrl
              #(
                .NUMMST  ( NUMMST  ),
                .NUMAP   ( NUMAP   ),
                .NUMID   ( NUMID   ),
                .AXIDW   ( AXIDW   ),
                .AXIIDW  ( AXISIDW ),
                .AXIAWUW ( AXIAWUW ),
                .AXIWUW  ( AXIWUW  ),
                .AXIBUW  ( AXIBUW  ),
                .AXIARUW ( AXIARUW ),
                .AXIRUW  ( AXIRUW  ),
                .SYNCFB  ( SYNCFB  ),
                .SYNCFW  ( SYNCFW  ),
                .BC      ( BC      )
                )
      i_slv_inst
              (
               .clk     ( clk     ),
               .rst_a   ( rst_a   ),
               .ptidx_a ( ptidx_a ),
               `AXINODATAINSTM(gs,axi_slv_,axi_slv_),
               `AXINODATAINSTM(gs*NUMMST+:NUMMST,axi_mst_,axi_int2_),
               .rgnt    ( rgnt[gs]),
               .decbase ( decbase ),
               .decsize ( decsize ),
               .decmst  ( ldecmst )
               );
      // buffer for AXI slave command channel
      for (genvar gm = 0; gm < NUMMST; gm++)
      begin : bufc_GEN
        npu_slice_int #(
                   .DWIDTH (AXISIDW+AXIARUW+$bits(npu_axi_cmd_t))
        ) u_ar_slice_inst (
          .clk          ( clk        ),
          .rst_a        ( rst_a      ),
          .valid_write  ( axi_int2_arvalid[gs*NUMMST+gm]),
          .accept_write ( axi_int2_arready[gs*NUMMST+gm]),
          .data_write   ( {axi_int2_arid[gs*NUMMST+gm], axi_int2_aruser[gs*NUMMST+gm], axi_int2_ar[gs*NUMMST+gm]}),
          .valid_read   ( axi_int1_arvalid[gs*NUMMST+gm]),
          .accept_read  ( axi_int1_arready[gs*NUMMST+gm]),
          .data_read    ( {axi_int1_arid[gs*NUMMST+gm], axi_int1_aruser[gs*NUMMST+gm], axi_int1_ar[gs*NUMMST+gm]})
          );

        npu_slice_int #(
                   .DWIDTH (AXISIDW+AXIAWUW+$bits(npu_axi_cmd_t))
        ) u_aw_slice_inst (
          .clk          ( clk        ),
          .rst_a        ( rst_a      ),
          .valid_write  ( axi_int2_awvalid[gs*NUMMST+gm]),
          .accept_write ( axi_int2_awready[gs*NUMMST+gm]),
          .data_write   ( {axi_int2_awid[gs*NUMMST+gm], axi_int2_awuser[gs*NUMMST+gm], axi_int2_aw[gs*NUMMST+gm]}),
          .valid_read   ( axi_int1_awvalid[gs*NUMMST+gm]),
          .accept_read  ( axi_int1_awready[gs*NUMMST+gm]),
          .data_read    ( {axi_int1_awid[gs*NUMMST+gm], axi_int1_awuser[gs*NUMMST+gm], axi_int1_aw[gs*NUMMST+gm]})
          );

      end : bufc_GEN
    end : gs_slv_GEN
// spyglass enable_block SelfDeterminedExpr-ML

// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
    always_comb
    begin : fwd_PROC
      for (int s = 0; s < NUMSLV; s++)
      begin
        for (int m = 0; m < NUMMST; m++)
        begin
          // Forward data and response channels
          axi_int2_rvalid[s*NUMMST+m] = axi_int1_rvalid[s*NUMMST+m];
          axi_int1_rready[s*NUMMST+m] = axi_int2_rready[s*NUMMST+m];
          axi_int2_rid[s*NUMMST+m]    = axi_int1_rid[s*NUMMST+m];
          //axi_int2_rdata[s*NUMMST+m]  = axi_int1_rdata[s*NUMMST+m];
          axi_int2_rresp[s*NUMMST+m]  = axi_int1_rresp[s*NUMMST+m];
          axi_int2_ruser[s*NUMMST+m]  = axi_int1_ruser[s*NUMMST+m];
          axi_int2_rlast[s*NUMMST+m]  = axi_int1_rlast[s*NUMMST+m];
          axi_int1_wvalid[s*NUMMST+m] = axi_int2_wvalid[s*NUMMST+m];
          axi_int2_wready[s*NUMMST+m] = axi_int1_wready[s*NUMMST+m];
          //axi_int1_wdata[s*NUMMST+m]  = axi_int2_wdata[s*NUMMST+m];
          //axi_int1_wstrb[s*NUMMST+m]  = axi_int2_wstrb[s*NUMMST+m];
          axi_int1_wuser[s*NUMMST+m]  = axi_int2_wuser[s*NUMMST+m];
          axi_int1_wlast[s*NUMMST+m]  = axi_int2_wlast[s*NUMMST+m];
          axi_int2_bvalid[s*NUMMST+m] = axi_int1_bvalid[s*NUMMST+m];
          axi_int1_bready[s*NUMMST+m] = axi_int2_bready[s*NUMMST+m];
          axi_int2_bid[s*NUMMST+m]    = axi_int1_bid[s*NUMMST+m];
          axi_int2_buser[s*NUMMST+m]  = axi_int1_buser[s*NUMMST+m];
          axi_int2_bresp[s*NUMMST+m]  = axi_int1_bresp[s*NUMMST+m];
        end
      end
    end : fwd_PROC
// spyglass enable_block SelfDeterminedExpr-ML

// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
    // disable some slave to master connections
    always_comb
    begin : s2m_PROC
      for (int s = 0; s < NUMSLV; s++)
      begin
        for (int m = 0; m < NUMMST; m++)
        begin
          if (decslv[s][m])
          begin
            // forward
            axi_int_arvalid[s*NUMMST+m]  = axi_int1_arvalid[s*NUMMST+m];
            axi_int1_arready[s*NUMMST+m] = axi_int_arready[s*NUMMST+m];
            axi_int_arid[s*NUMMST+m]     = axi_int1_arid[s*NUMMST+m];
            axi_int_aruser[s*NUMMST+m]   = axi_int1_aruser[s*NUMMST+m];
            axi_int_ar[s*NUMMST+m]       = axi_int1_ar[s*NUMMST+m];
            axi_int1_rvalid[s*NUMMST+m]  = axi_int_rvalid[s*NUMMST+m];
            axi_int_rready[s*NUMMST+m]   = axi_int1_rready[s*NUMMST+m];
            axi_int1_rid[s*NUMMST+m]     = axi_int_rid[s*NUMMST+m];
            //axi_int1_rdata[s*NUMMST+m]   = axi_int_rdata[s*NUMMST+m];
            axi_int1_rresp[s*NUMMST+m]   = axi_int_rresp[s*NUMMST+m];
            axi_int1_ruser[s*NUMMST+m]   = axi_int_ruser[s*NUMMST+m];
            axi_int1_rlast[s*NUMMST+m]   = axi_int_rlast[s*NUMMST+m];
            axi_int_awvalid[s*NUMMST+m]  = axi_int1_awvalid[s*NUMMST+m];
            axi_int1_awready[s*NUMMST+m] = axi_int_awready[s*NUMMST+m];
            axi_int_awid[s*NUMMST+m]     = axi_int1_awid[s*NUMMST+m];
            axi_int_awuser[s*NUMMST+m]   = axi_int1_awuser[s*NUMMST+m];
            axi_int_aw[s*NUMMST+m]       = axi_int1_aw[s*NUMMST+m];
            axi_int_wvalid[s*NUMMST+m]   = axi_int1_wvalid[s*NUMMST+m];
            axi_int1_wready[s*NUMMST+m]  = axi_int_wready[s*NUMMST+m];
            //axi_int_wdata[s*NUMMST+m]    = axi_int1_wdata[s*NUMMST+m];
            //axi_int_wstrb[s*NUMMST+m]    = axi_int1_wstrb[s*NUMMST+m];
            axi_int_wuser[s*NUMMST+m]    = axi_int1_wuser[s*NUMMST+m];
            axi_int_wlast[s*NUMMST+m]    = axi_int1_wlast[s*NUMMST+m];
            axi_int1_bvalid[s*NUMMST+m]  = axi_int_bvalid[s*NUMMST+m];
            axi_int_bready[s*NUMMST+m]   = axi_int1_bready[s*NUMMST+m];
            axi_int1_bid[s*NUMMST+m]     = axi_int_bid[s*NUMMST+m];
            axi_int1_buser[s*NUMMST+m]   = axi_int_buser[s*NUMMST+m];
            axi_int1_bresp[s*NUMMST+m]   = axi_int_bresp[s*NUMMST+m];
          end // if (decslv[s][m])
          else
          begin
            // block
            axi_int_arvalid[s*NUMMST+m]  = '0;
            axi_int1_arready[s*NUMMST+m] = '0;
            axi_int_arid[s*NUMMST+m]     = '0;
            axi_int_aruser[s*NUMMST+m]   = '0;
            axi_int_ar[s*NUMMST+m]       = '0;
            axi_int1_rvalid[s*NUMMST+m]  = '0;
            axi_int_rready[s*NUMMST+m]   = '0;
            axi_int1_rid[s*NUMMST+m]     = '0;
            //axi_int1_rdata[s*NUMMST+m]   = '0;
            axi_int1_rresp[s*NUMMST+m]   = npu_axi_resp_t'(0);
            axi_int1_ruser[s*NUMMST+m]   = '0;
            axi_int1_rlast[s*NUMMST+m]   = '0;
            axi_int_awvalid[s*NUMMST+m]  = '0;
            axi_int1_awready[s*NUMMST+m] = '0;
            axi_int_awid[s*NUMMST+m]     = '0;
            axi_int_awuser[s*NUMMST+m]   = '0;
            axi_int_aw[s*NUMMST+m]       = '0;
            axi_int_wvalid[s*NUMMST+m]   = '0;
            axi_int1_wready[s*NUMMST+m]  = '0;
            //axi_int_wdata[s*NUMMST+m]    = '0;
            //axi_int_wstrb[s*NUMMST+m]    = '0;
            axi_int_wuser[s*NUMMST+m]    = '0;
            axi_int_wlast[s*NUMMST+m]    = '0;
            axi_int1_bvalid[s*NUMMST+m]  = '0;
            axi_int_bready[s*NUMMST+m]   = '0;
            axi_int1_bid[s*NUMMST+m]     = '0;
            axi_int1_buser[s*NUMMST+m]   = '0;
            axi_int1_bresp[s*NUMMST+m]   = npu_axi_resp_t'(0);
          end // else: !if(decslv[s][m])
        end // for (int m = 0; m < NUMMST; m++)
      end // for (int s = 0; s < NUMSLV; s++)
    end : s2m_PROC
  end : slv_GEN  
// spyglass enable_block SelfDeterminedExpr-ML


  ////////////////////////////////////////////////////////////////////////////////////////
  //
  // Transpose wires from [NUMSLV][NUMMST] to [NUMMST][NUMSLV]
  //
  ////////////////////////////////////////////////////////////////////////////////////////
// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
  genvar gi;
  for (gi = 0; gi < NUMMST; gi++)
  begin : gi_GEN
    genvar gj;
    for (gj = 0; gj < NUMSLV; gj++)
    begin : gj_GEN
      assign axi_trn_arvalid[gi*NUMSLV+gj] = axi_int_arvalid[gj*NUMMST+gi];
      assign axi_int_arready[gj*NUMMST+gi] = axi_trn_arready[gi*NUMSLV+gj];
      assign axi_trn_arid   [gi*NUMSLV+gj] = axi_int_arid   [gj*NUMMST+gi];
      assign axi_trn_aruser [gi*NUMSLV+gj] = axi_int_aruser [gj*NUMMST+gi];
      assign axi_trn_ar     [gi*NUMSLV+gj] = axi_int_ar     [gj*NUMMST+gi];
      assign axi_int_rvalid [gj*NUMMST+gi] = axi_trn_rvalid [gi*NUMSLV+gj];
      assign axi_trn_rready [gi*NUMSLV+gj] = axi_int_rready [gj*NUMMST+gi];
      assign axi_int_rid    [gj*NUMMST+gi] = axi_trn_rid    [gi*NUMSLV+gj];
      //assign axi_int_rdata  [gj*NUMMST+gi] = axi_trn_rdata  [gi*NUMSLV+gj];
      assign axi_int_rresp  [gj*NUMMST+gi] = axi_trn_rresp  [gi*NUMSLV+gj];
      assign axi_int_ruser  [gj*NUMMST+gi] = axi_trn_ruser  [gi*NUMSLV+gj];
      assign axi_int_rlast  [gj*NUMMST+gi] = axi_trn_rlast  [gi*NUMSLV+gj];
      assign axi_trn_awvalid[gi*NUMSLV+gj] = axi_int_awvalid[gj*NUMMST+gi];
      assign axi_int_awready[gj*NUMMST+gi] = axi_trn_awready[gi*NUMSLV+gj];
      assign axi_trn_awid   [gi*NUMSLV+gj] = axi_int_awid   [gj*NUMMST+gi];
      assign axi_trn_awuser [gi*NUMSLV+gj] = axi_int_awuser [gj*NUMMST+gi];
      assign axi_trn_aw     [gi*NUMSLV+gj] = axi_int_aw     [gj*NUMMST+gi];
      assign axi_trn_wvalid [gi*NUMSLV+gj] = axi_int_wvalid [gj*NUMMST+gi];
      assign axi_int_wready [gj*NUMMST+gi] = axi_trn_wready [gi*NUMSLV+gj];
      //assign axi_trn_wdata  [gi*NUMSLV+gj] = axi_int_wdata  [gj*NUMMST+gi];
      //assign axi_trn_wstrb  [gi*NUMSLV+gj] = axi_int_wstrb  [gj*NUMMST+gi];
      assign axi_trn_wuser  [gi*NUMSLV+gj] = axi_int_wuser  [gj*NUMMST+gi];
      assign axi_trn_wlast  [gi*NUMSLV+gj] = axi_int_wlast  [gj*NUMMST+gi];
      assign axi_int_bvalid [gj*NUMMST+gi] = axi_trn_bvalid [gi*NUMSLV+gj];
      assign axi_trn_bready [gi*NUMSLV+gj] = axi_int_bready [gj*NUMMST+gi];
      assign axi_int_bid    [gj*NUMMST+gi] = axi_trn_bid    [gi*NUMSLV+gj];
      assign axi_int_buser  [gj*NUMMST+gi] = axi_trn_buser  [gi*NUMSLV+gj];
      assign axi_int_bresp  [gj*NUMMST+gi] = axi_trn_bresp  [gi*NUMSLV+gj];
    end : gj_GEN
  end : gi_GEN
// spyglass enable_block SelfDeterminedExpr-ML


  ////////////////////////////////////////////////////////////////////////////////////////
  //
  // Master mux instances
  //
  ////////////////////////////////////////////////////////////////////////////////////////
  if (NUMSLV == 1)
  begin : bp_mst_GEN
    assign axi_mst_arvalid = axi_trn_arvalid;
    assign axi_trn_arready = axi_mst_arready;
    assign axi_mst_arid    = axi_trn_arid;
    assign axi_mst_aruser  = axi_trn_aruser;
    assign axi_mst_ar      = axi_trn_ar;
    assign axi_trn_rvalid  = axi_mst_rvalid;
    assign axi_mst_rready  = axi_trn_rready;
    assign axi_trn_rid     = axi_mst_rid;
    //assign axi_trn_rdata   = axi_mst_rdata;
    assign axi_trn_rresp   = axi_mst_rresp;
    assign axi_trn_ruser   = axi_mst_ruser;
    assign axi_trn_rlast   = axi_mst_rlast;
    assign axi_mst_awvalid = axi_trn_awvalid;
    assign axi_trn_awready = axi_mst_awready;
    assign axi_mst_awid    = axi_trn_awid;
    assign axi_mst_awuser  = axi_trn_awuser;
    assign axi_mst_aw      = axi_trn_aw;
    assign axi_mst_wvalid  = axi_trn_wvalid;
    assign axi_trn_wready  = axi_mst_wready;
    //assign axi_mst_wdata   = axi_trn_wdata;
    //assign axi_mst_wstrb   = axi_trn_wstrb;
    assign axi_mst_wuser   = axi_trn_wuser;
    assign axi_mst_wlast   = axi_trn_wlast;
    assign axi_trn_bvalid  = axi_mst_bvalid;
    assign axi_mst_bready  = axi_trn_bready;
    assign axi_trn_bid     = axi_mst_bid;
    assign axi_trn_buser   = axi_mst_buser;
    assign axi_trn_bresp   = axi_mst_bresp;
  end : bp_mst_GEN
  else
  begin : mst_GEN
    genvar gm;
    for (gm = 0; gm < NUMMST; gm++)
    begin : gm_mst_GEN
      npu_axi_mux_ctrl
              #(
                .NUMSLV  ( NUMSLV  ),
                .AXIDW   ( AXIDW   ),
                .AXISIDW ( AXISIDW ),
                .AXIMIDW ( AXIMIDW ),
                .AXIAWUW ( AXIAWUW ),
                .AXIWUW  ( AXIWUW  ),
                .AXIBUW  ( AXIBUW  ),
                .AXIARUW ( AXIARUW ),
                .AXIRUW  ( AXIRUW  )
                )
      i_mst_inst
              (
               .clk       ( clk         ),
               .rst_a     ( rst_a       ),
               .wfifo_rd  ( wfifo_rd[gm]),
               `AXINODATAINSTM(gm*NUMSLV+:NUMSLV,axi_slv_,axi_trn_),
               `AXINODATAINSTM(gm,axi_mst_,axi_mst_)
               );
    end : gm_mst_GEN
  end : mst_GEN
  
endmodule : npu_axi_matrix_ctrl
