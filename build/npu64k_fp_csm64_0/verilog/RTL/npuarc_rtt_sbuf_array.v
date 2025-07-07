// Library ARC_Trace-3.0.999999999
// Copyright (C) 2018 Synopsys, Inc. All rights reserved.
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
//   rtt_sbuf_array
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_sbuf_array.vpp
//
// ===========================================================================


`include "npuarc_rtt_pkg_defines.v"
`include "npuarc_arc_rtt_defines.v"
module npuarc_rtt_sbuf_array (
                          rtt_clk,
                          rst_a,
                          wr_en,
                          rd_en,
                          wr_data,
                          rd_data,
                          wr_ptr,
                          rd_ptr

                         );

//-------------------------------------------------------------------
//parametes can be overwrite
//-------------------------------------------------------------------
parameter FIFO_SIZE       = 9;
parameter FIFO_DATA_WIDTH = 10;

parameter FIFO_DEPTH      = 1 << FIFO_SIZE;

//leda NTL_CON32 off

input                                rtt_clk;  // Clock
input                                rst_a;
input                                wr_en;    // Write enable
input                                rd_en;    // Read enable
input   [(FIFO_DATA_WIDTH-1):0]      wr_data;
output   [(FIFO_DATA_WIDTH-1):0]     rd_data;
input    [FIFO_SIZE-1:0]             wr_ptr;   // Write pointer
input   [FIFO_SIZE-1:0]              rd_ptr;


reg   [(FIFO_DATA_WIDTH-1):0] rd_data;
reg    [(FIFO_DATA_WIDTH-1):0] fifo_mem [(FIFO_DEPTH-1):0]; // Memory


// leda W396 off
// LMD: Register with no reset/set
// LJ: Memory Data does not have reset. Only enable has reset.
// spyglass disable_block STARC-2.3.4.3 ResetFlop-ML Ar_resetcross01
// SMD: Register with no reset/set
// SJ: flops used as memory, no reset required
//------------------------------------------------------
// Writing Data into Memory
//------------------------------------------------------
always @(posedge rtt_clk)
begin : MEM_WR_BLK_PROC
  if( wr_en)
    fifo_mem[wr_ptr] <= wr_data;
end

//------------------------------------------------------
// Reading Data from Memory
//------------------------------------------------------
always @(posedge rtt_clk or posedge rst_a)
begin : MEM_RDATA_BLK_PROC
  if (rst_a == 1'b1)
      rd_data <= {FIFO_DATA_WIDTH{1'b0}};
  else if(rd_en)
      rd_data <= fifo_mem[rd_ptr];
end

// spyglass enable_block STARC-2.3.4.3 ResetFlop-ML Ar_resetcross01
// leda W396 on
//leda NTL_CON32 on
endmodule
