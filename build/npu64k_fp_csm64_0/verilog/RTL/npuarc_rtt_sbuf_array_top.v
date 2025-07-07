// Library ARC_Trace-3.0.999999999
// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   rtt_sbuf_array_top
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_sbuf_array_top.vpp
//
// ===========================================================================


`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_sbuf_array_top
(



input  prdcr_clk_0,



input                                  dsm_wr_en,
input                                  dsm_rd_en,
input  [(`npuarc_DSM_WDT)-1:0]                dsm_wr_data,
output [(`npuarc_DSM_WDT)-1:0]                dsm_rd_data,
input  [`npuarc_DSM_BUF_DEPTH-1:0]           dsm_wr_ptr,
input  [`npuarc_DSM_BUF_DEPTH-1:0]           dsm_rd_ptr,


input                                  vdspm_wr_en,
input                                  vdspm_rd_en,
input  [(`npuarc_VDSPSW_WDT)-1:0]             vdspm_wr_data,
output [(`npuarc_VDSPSW_WDT)-1:0]             vdspm_rd_data,
input  [`npuarc_VDSPM_BUF_DEPTH-1:0]           vdspm_wr_ptr,
input  [`npuarc_VDSPM_BUF_DEPTH-1:0]           vdspm_rd_ptr,

input                                  errm_wr_en,
input                                  errm_rd_en,
input  [(`npuarc_ERRM_WDT)-1:0]               errm_wr_data,
output [(`npuarc_ERRM_WDT)-1:0]               errm_rd_data,
input  [`npuarc_ERRM_BUF_DEPTH-1:0]           errm_wr_ptr,
input  [`npuarc_ERRM_BUF_DEPTH-1:0]           errm_rd_ptr,


input                                  otm_wr_en,
input                                  otm_rd_en,
input  [(`npuarc_OTM_WDT)-1:0]                otm_wr_data,
output [(`npuarc_OTM_WDT)-1:0]                otm_rd_data,
input  [`npuarc_OTM_BUF_DEPTH-1:0]           otm_wr_ptr,
input  [`npuarc_OTM_BUF_DEPTH-1:0]           otm_rd_ptr,

input                                  pcm_wr_en,
input                                  pcm_rd_en,
input  [(`npuarc_PCM_WDT)-1:0]                pcm_wr_data,
output [(`npuarc_PCM_WDT)-1:0]                pcm_rd_data,
input  [`npuarc_PCM_BUF_DEPTH-1:0]           pcm_wr_ptr,
input  [`npuarc_PCM_BUF_DEPTH-1:0]           pcm_rd_ptr,


input                                  ptcm_wr_en,
input                                  ptcm_rd_en,
input  [(120)-1:0]               ptcm_wr_data,
output [(120)-1:0]               ptcm_rd_data,
input  [`npuarc_PTCM_BUF_DEPTH-1:0]           ptcm_wr_ptr,
input  [`npuarc_PTCM_BUF_DEPTH-1:0]           ptcm_rd_ptr,



input                                  ptm_wr_en,
input                                  ptm_rd_en,
input  [(`npuarc_PTM_WDT)-1:0]                ptm_wr_data,
output [(`npuarc_PTM_WDT)-1:0]                ptm_rd_data,
input  [`npuarc_PTM_BUF_DEPTH-1:0]           ptm_wr_ptr,
input  [`npuarc_PTM_BUF_DEPTH-1:0]           ptm_rd_ptr,




input                                  rfm_wr_en,
input                                  rfm_rd_en,
input  [(`npuarc_RFM_WDT)-1:0]                rfm_wr_data,
output [(`npuarc_RFM_WDT)-1:0]                rfm_rd_data,
input  [`npuarc_RFM_BUF_DEPTH-1:0]           rfm_wr_ptr,
input  [`npuarc_RFM_BUF_DEPTH-1:0]           rfm_rd_ptr,



input                                  wpm_wr_en,
input                                  wpm_rd_en,
input  [(`npuarc_WPM_WDT)-1:0]                wpm_wr_data,
output [(`npuarc_WPM_WDT)-1:0]                wpm_rd_data,
input  [`npuarc_WPM_BUF_DEPTH-1:0]           wpm_wr_ptr,
input  [`npuarc_WPM_BUF_DEPTH-1:0]           wpm_rd_ptr,

input rst_a

);









///////////////////////////
//     DSM
//////////////////////////

npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_DSM_WDT),
       .FIFO_SIZE(`npuarc_DSM_BUF_DEPTH)
      )
u_dsm_array_0 (
.rtt_clk(prdcr_clk_0),
.rst_a(rst_a),
.wr_en(dsm_wr_en),
.rd_en(dsm_rd_en),
.wr_data(dsm_wr_data),
.rd_data(dsm_rd_data),
.wr_ptr(dsm_wr_ptr),
.rd_ptr(dsm_rd_ptr)

);




///////////////////////////
//     VDSPM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_VDSPSW_WDT),
       .FIFO_SIZE(`npuarc_VDSPM_BUF_DEPTH)
      )
u_vdspm_array_0 (
.rtt_clk(prdcr_clk_0),
.rst_a(rst_a),
.wr_en(vdspm_wr_en),
.rd_en(vdspm_rd_en),
.wr_data(vdspm_wr_data),
.rd_data(vdspm_rd_data),
.wr_ptr(vdspm_wr_ptr),
.rd_ptr(vdspm_rd_ptr)

);

///////////////////////////
//     ERRM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_ERRM_WDT),
       .FIFO_SIZE(`npuarc_ERRM_BUF_DEPTH)
      )
u_errm_array_0 (
.rtt_clk(prdcr_clk_0),
.rst_a(rst_a),
.wr_en(errm_wr_en),
.rd_en(errm_rd_en),
.wr_data(errm_wr_data),
.rd_data(errm_rd_data),
.wr_ptr(errm_wr_ptr),
.rd_ptr(errm_rd_ptr)

);


///////////////////////////
//     OTM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_OTM_WDT),
       .FIFO_SIZE(`npuarc_OTM_BUF_DEPTH)
      )
u_otm_array_0 (
.rtt_clk(prdcr_clk_0),
.rst_a(rst_a),
.wr_en(otm_wr_en),
.rd_en(otm_rd_en),
.wr_data(otm_wr_data),
.rd_data(otm_rd_data),
.wr_ptr(otm_wr_ptr),
.rd_ptr(otm_rd_ptr)

);

///////////////////////////
//     PCM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_PCM_WDT),
       .FIFO_SIZE(`npuarc_PCM_BUF_DEPTH)
      )
u_pcm_array_0 (
.rtt_clk(prdcr_clk_0),
.rst_a(rst_a),
.wr_en(pcm_wr_en),
.rd_en(pcm_rd_en),
.wr_data(pcm_wr_data),
.rd_data(pcm_rd_data),
.wr_ptr(pcm_wr_ptr),
.rd_ptr(pcm_rd_ptr)

);

///////////////////////////
//     PTCM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(120),
       .FIFO_SIZE(`npuarc_PTCM_BUF_DEPTH)
      )
u_ptcm_array_0 (
.rtt_clk(prdcr_clk_0),
.rst_a(rst_a),
.wr_en(ptcm_wr_en),
.rd_en(ptcm_rd_en),
.wr_data(ptcm_wr_data),
.rd_data(ptcm_rd_data),
.wr_ptr(ptcm_wr_ptr),
.rd_ptr(ptcm_rd_ptr)

);



///////////////////////////
//     PTM
//////////////////////////
// spyglass disable_block SelfDeterminedExpr-ML
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_PTM_WDT),
       .FIFO_SIZE(`npuarc_PTM_BUF_DEPTH)
      )
u_ptm_array_0 (
.rtt_clk(prdcr_clk_0),
.rst_a(rst_a),
.wr_en(ptm_wr_en),
.rd_en(ptm_rd_en),
.wr_data(ptm_wr_data),
.rd_data(ptm_rd_data),
.wr_ptr(ptm_wr_ptr),
.rd_ptr(ptm_rd_ptr)

);
// spyglass enable_block SelfDeterminedExpr-ML

///////////////////////////
//     RFM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_RFM_WDT),
       .FIFO_SIZE(`npuarc_RFM_BUF_DEPTH)
      )
u_rfm_array_0 (
.rtt_clk(prdcr_clk_0),
.rst_a(rst_a),
.wr_en(rfm_wr_en),
.rd_en(rfm_rd_en),
.wr_data(rfm_wr_data),
.rd_data(rfm_rd_data),
.wr_ptr(rfm_wr_ptr),
.rd_ptr(rfm_rd_ptr)

);


///////////////////////////
//     WPM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_WPM_WDT),
       .FIFO_SIZE(`npuarc_WPM_BUF_DEPTH)
      )
u_wpm_array_0 (
.rtt_clk(prdcr_clk_0),
.rst_a(rst_a),
.wr_en(wpm_wr_en),
.rd_en(wpm_rd_en),
.wr_data(wpm_wr_data),
.rd_data(wpm_rd_data),
.wr_ptr(wpm_wr_ptr),
.rd_ptr(wpm_rd_ptr)

);
endmodule
