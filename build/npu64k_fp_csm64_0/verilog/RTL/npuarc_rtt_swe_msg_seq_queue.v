// Library ARC_Trace-3.0.999999999
// Copyright (C) 2012-2019 Synopsys, Inc. All rights reserved.
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
//   rtt_swe_msg_seq_queue
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_swe_msg_seq_queue.vpp
//
// ===========================================================================


`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_swe_msg_seq_queue (
                              rtt_clk,
                              rst_a,
                              wr_en,
                              rd_en,
                              wr_data,
                              rd_data,
                              wr_ptr,
                              rd_ptr,
                              empty,
                              full
                             );

input                          rtt_clk;
input                          rst_a;
input                          wr_en;
input                          rd_en;

input   [20-1:0]    wr_data;
output  [20-1:0]    rd_data;       

output                         empty;
output                         full;


output reg   [9-1:0]   wr_ptr;
output reg   [9-1:0]   rd_ptr;

wire   [9:0]   wr_ptr_xx;
wire   [9:0]   rd_ptr_xx;
reg           fifo_empty;
reg           fifo_full;

reg  [20-1:0] msg_seq_order_q [305:0];

// spyglass disable_block STARC-2.3.4.3
// SMD: Register with no reset/set
// SJ: flops used as memory, no reset required
// spyglass disable_block Ar_resetcross01
// SMD: Unsynchronized reset crossing detected
// SJ: flops used as memory, no reset required
always @(posedge rtt_clk)
begin
  if(wr_en)
    msg_seq_order_q[wr_ptr] <= wr_data;
end
// spyglass enable_block Ar_resetcross01
// spyglass enable_block STARC-2.3.4.3

assign rd_data = rd_en ? msg_seq_order_q[rd_ptr] : 20'b0;

assign wr_ptr_xx = wr_ptr + 1'b1;
always @(posedge rtt_clk or posedge rst_a)
begin
  if(rst_a == 1'b1 )
    wr_ptr <= 9'b0;
  else if(wr_en && wr_ptr == 9'd305)
    wr_ptr <= 9'b0;
  else if(wr_en)
    wr_ptr <= wr_ptr_xx[9-1:0];
end

assign rd_ptr_xx = rd_ptr + 1'b1;
always @(posedge rtt_clk or posedge rst_a)
begin
  if(rst_a == 1'b1 )
    rd_ptr <= 9'b0;
  else if(rd_en && rd_ptr == 9'd305)
    rd_ptr <= 9'b0;
  else if(rd_en)
    rd_ptr <= rd_ptr_xx[9-1:0];
end

assign empty = fifo_empty;
always @( posedge rtt_clk or posedge rst_a )
begin
  if( rst_a == 1'b1 )
    fifo_empty <= 1'b1;
  else if( wr_en && (~rd_en) )
    fifo_empty <= 1'b0;
  else if((rd_en && (~wr_en)) &&
          (rd_ptr_xx[9-1:0] == wr_ptr))
    fifo_empty <= 1'b1;
end

assign full = fifo_full; 
always @( posedge rtt_clk or posedge rst_a )
begin
  if( rst_a == 1'b1 )
    fifo_full <= 1'b0;
  else if( wr_en && (~rd_en) &&
           (wr_ptr_xx[9-1:0] == rd_ptr))
    fifo_full <= 1'b1;
  else if( rd_en && (~wr_en) )
    fifo_full <= 1'b0;
end

endmodule
