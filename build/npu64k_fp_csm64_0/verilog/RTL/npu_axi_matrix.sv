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

module npu_axi_matrix
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
   `AXISLVN(NUMSLV,AXISIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // array of AXI master interfaces
   `AXIMSTN(NUMMST,AXIMIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_),
   input logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decbase,     // 4KB base address per aperture
   input logic [NUMAP-1:0][NPU_AXI_ADDR_W-1:12] decsize,     // 4KB mask to specify aperture size
   input logic [NUMAP-1:0][NUMMST-1:0]          decmst,      // onehot index of the decoded master
   input logic [NUMSLV-1:0][NUMMST-1:0]         decslv       // enable slave to master connections
   );
  
   logic  [NUMMST-1:0][NUMSLV-1:0]     wfifo_rd;
   logic  [NUMSLV-1:0][NUMMST:0]       rgnt;

   logic  [NUMMST*NUMSLV-1:0][AXIDW-1:0]   axi_int_rdata;
   logic  [NUMMST*NUMSLV-1:0][AXIDW-1:0]   axi_int2_rdata;
   logic  [NUMMST*NUMSLV-1:0][AXIDW-1:0]   axi_trn_rdata;

   logic  [NUMMST*NUMSLV-1:0][AXIDW-1:0]   axi_int_wdata;
   logic  [NUMMST*NUMSLV-1:0][AXIDW/8-1:0] axi_int_wstrb;
   logic  [NUMMST*NUMSLV-1:0][AXIDW-1:0]   axi_int2_wdata;
   logic  [NUMMST*NUMSLV-1:0][AXIDW/8-1:0] axi_int2_wstrb;
   logic  [NUMMST*NUMSLV-1:0][AXIDW-1:0]   axi_trn_wdata;
   logic  [NUMMST*NUMSLV-1:0][AXIDW/8-1:0] axi_trn_wstrb;


npu_axi_matrix_ctrl
     #(
       .NUMSLV  ( NUMSLV   ),
       .NUMMST  ( NUMMST   ),
       .NUMAP   ( NUMAP    ),
       .AXIDW   ( AXIDW    ),
       .AXISIDW ( AXISIDW  ),
       .AXIMIDW ( AXIMIDW  ), 
       .AXIAWUW ( AXIAWUW  ),
       .AXIWUW  ( AXIWUW   ),
       .AXIBUW  ( AXIBUW   ),
       .AXIARUW ( AXIARUW  ),
       .AXIRUW  ( AXIRUW   ),
       .SYNCFB  ( SYNCFB   ),
       .SYNCFW  ( SYNCFW   ),
       .BC      ( BC       )
     )
u_axi_mat_ctrl
  (
       .clk    ( clk   ),
       .rst_a  ( rst_a ),
       .ptidx_a( ptidx_a),
       .decslv ( decslv),
       `AXINODATAINST(axi_slv_,axi_slv_),
       `AXINODATAINST(axi_mst_,axi_mst_),
       .wfifo_rd(wfifo_rd),
       .rgnt(rgnt),
       .decbase  ( decbase ),
       .decsize  ( decsize ),
       .decmst   ( decmst  )
     );

  // Extend wires
  assign axi_int2_wdata = {NUMMST{axi_slv_wdata}};
  assign axi_int2_wstrb = {NUMMST{axi_slv_wstrb}};
  assign axi_trn_rdata  = {NUMSLV{axi_mst_rdata}};

// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
  //from demux
  if (NUMMST == 1)
  begin : no_demux_PROC
    always_comb
    begin : r_demux_PROC
      // default outputs
      axi_slv_rdata = '0;
      // go over master ports to implement OR bus
      for (int m = 0; m < NUMSLV; m++)
      begin
        axi_slv_rdata[m] |= axi_int2_rdata[m];
      end
    end : r_demux_PROC
  end :  no_demux_PROC
  else
  begin :  demux_PROC
    always_comb
    begin : r_demux_PROC
      // default outputs
      axi_slv_rdata = '0;
      // go over master ports to implement OR bus
      for (int m = 0; m < NUMSLV; m++)
      begin
        for (int n = 0; n < NUMMST; n++)
        begin
          if (rgnt[m][n])
          begin
            axi_slv_rdata[m] |= axi_int2_rdata[m*NUMMST+n];
          end
        end
      end
    end : r_demux_PROC
  end :  demux_PROC
// spyglass enable_block SelfDeterminedExpr-ML

// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
  //from mux
  if (NUMSLV == 1)
  begin : no_mux_PROC
    always_comb
    begin : wdec_mux_PROC
      // default outputs
      axi_mst_wdata = '0;
      axi_mst_wstrb = '0;
      for (int i = 0; i < NUMMST; i++)
      begin
        axi_mst_wdata[i] |= axi_trn_wdata[i];
        axi_mst_wstrb[i] |= axi_trn_wstrb[i];
      end
    end : wdec_mux_PROC
  end : no_mux_PROC
  else 
  begin : mux_PROC
    always_comb
    begin : wdec_mux_PROC
      // default outputs
      axi_mst_wdata = '0;
      axi_mst_wstrb = '0;
      for (int i = 0; i < NUMMST; i++)
      begin
        for (int j = 0; j < NUMSLV; j++)
        begin
          if (wfifo_rd[i][j])
          begin
            axi_mst_wdata[i] |= axi_trn_wdata[i*NUMSLV+j];
            axi_mst_wstrb[i] |= axi_trn_wstrb[i*NUMSLV+j];
          end
        end
      end
    end : wdec_mux_PROC
  end : mux_PROC
// spyglass enable_block SelfDeterminedExpr-ML

// spyglass disable_block SelfDeterminedExpr-ML W163
// SMD: Self-determin expression
// SJ: Reviewed
  //Use decoder to select target
  always_comb
  begin : s2m_data_PROC
    for (int gs = 0; gs < NUMSLV; gs++)
    begin : slv_data_PROC
      if (NUMMST == 1) 
      begin
        // forward
        axi_int2_rdata[gs]   = axi_int_rdata[gs];
        axi_int_wdata[gs]    = axi_int2_wdata[gs];
        axi_int_wstrb[gs]    = axi_int2_wstrb[gs];
      end
      else
      begin
        for (int m = 0; m < NUMMST; m++)
        begin
          if (decslv[gs][m])
          begin
            // forward
            axi_int2_rdata[gs*NUMMST+m]   = axi_int_rdata[gs*NUMMST+m];
            axi_int_wdata[gs*NUMMST+m]    = axi_int2_wdata[m*NUMSLV+gs];
            axi_int_wstrb[gs*NUMMST+m]    = axi_int2_wstrb[m*NUMSLV+gs];
          end
          else
          begin
            // block
            axi_int2_rdata[gs*NUMMST+m]   = '0;
            axi_int_wdata[gs*NUMMST+m]    = '0;
            axi_int_wstrb[gs*NUMMST+m]    = '0;
          end
        end
      end
    end : slv_data_PROC
  end : s2m_data_PROC 
// spyglass enable_block SelfDeterminedExpr-ML W163


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
      assign axi_int_rdata[gj*NUMMST+gi] = axi_trn_rdata[gj*NUMMST+gi];
      assign axi_trn_wdata[gi*NUMSLV+gj] = axi_int_wdata[gj*NUMMST+gi];
      assign axi_trn_wstrb[gi*NUMSLV+gj] = axi_int_wstrb[gj*NUMMST+gi];
    end : gj_GEN
  end : gi_GEN
// spyglass enable_block SelfDeterminedExpr-ML

endmodule : npu_axi_matrix
