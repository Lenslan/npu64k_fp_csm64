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
//   rtt_ptcm_sbuf
//
// ===========================================================================
//
// Description:
//
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_ptcm_sbuf.vpp
//
// ===========================================================================

`include "npuarc_rtt_pkg_defines.v"
`include "npuarc_arc_rtt_defines.v"
module npuarc_rtt_ptcm_sbuf (
                          rtt_clk,
                          rst_a,
                          wr_en,
                          rd_en,
                          rd_vld,

                          wr_ptr,
                          rd_ptr,
                          full,
                          empty,
                          num_fill
                         );

//-------------------------------------------------------------------
//parametes can be overwrite
//-------------------------------------------------------------------
parameter FIFO_SIZE       = 9;
parameter FIFO_DATA_WIDTH = 10;


input                          rtt_clk;         // Clock
input                          rst_a;       // FIFO Reset
input                          wr_en;       // Write enable
input                          rd_en;       // Read enable
output                         rd_vld;

output    [FIFO_SIZE-1:0]           wr_ptr;      // Write pointer
output   [FIFO_SIZE-1:0]           rd_ptr;

output                         full;        // FIFO full
output                         empty;       // FIFO empty
output [FIFO_SIZE:0]           num_fill;    // No. of locations filled


wire                           rd_en_i;
assign rd_en_i = rd_en;



npuarc_rtt_fifo
  #(
       .FIFO_SIZE(`npuarc_PTCM_BUF_DEPTH)
      )
u_ptcm_sbuf_fifo
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(wr_en),
.rd_en(rd_en_i),
.rd_vld(rd_vld),
.full(full),
.empty(empty),
.num_fill(num_fill),
.wr_ptr(wr_ptr),
.rd_ptr(rd_ptr)
);




endmodule
