// Library ARC_Trace-3.0.999999999
// Copyright (C) 2017 Synopsys, Inc. All rights reserved.
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
//   rtt_otm_sbuf
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_cstm_sbuf.vpp
//
// ===========================================================================


`include "npuarc_rtt_pkg_defines.v"
`include "npuarc_arc_rtt_defines.v"
module npuarc_rtt_cstm_sbuf (
                          rtt_clk,
                          rst_a,
                          wr_en,
                          rd_en,
                          rd_vld,
                          wr_data,
                          rd_data,

                          empty
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
input  [FIFO_DATA_WIDTH-1:0]   wr_data;

output [FIFO_DATA_WIDTH-1:0]   rd_data;
output                         empty;       // FIFO empty

reg    [FIFO_DATA_WIDTH-1:0]   mem;
reg    [FIFO_DATA_WIDTH-1:0]   rd_data;
wire                           rd_en;
reg                            rd_vld;
reg                            empty;

//-------------------------------------------------------
// Empty Generation Logic
//-------------------------------------------------------

// leda W396 off
// LMD: Register with no reset/set
// LJ: Memory Data does not have reset. Only enable has reset.
// spyglass disable_block STARC-2.3.4.3
// SMD: Register with no reset/set
// SJ: flops used as memory, no reset required
// spyglass disable_block Ar_resetcross01
// SMD: Unsynchronized reset crossing detected
// SJ: flops used as memory, no reset required
//------------------------------------------------------
// Writing Data into Memory
//------------------------------------------------------
always @(posedge rtt_clk)
begin : MEM_WR_BLK_PROC
  if( wr_en)
    mem <= wr_data;
end
// spyglass enable_block Ar_resetcross01

//------------------------------------------------------
// Reading Data from Memory
//------------------------------------------------------
always @(posedge rtt_clk or posedge rst_a)
begin : MEM_RDATA_BLK_PROC
  if (rst_a == 1'b1)
      rd_data <= {FIFO_DATA_WIDTH{1'b0}};
  else if(rd_en)
      rd_data <= mem;
end

//------------------------------------------------------
// Read Data Valid
//------------------------------------------------------
always @(posedge rtt_clk or posedge rst_a)
begin : MEM_RDVALID_BLK_PROC
  if( rst_a == 1'b1 )
    rd_vld <= 1'b0;
  else
    rd_vld <= rd_en;
end

//-------------------------------------------------------
// FIFO Empty Generation Logic
//-------------------------------------------------------
always @( posedge rtt_clk or posedge rst_a )
begin : EMP_GEN_PROC
  if( rst_a == 1'b1 )
    empty <= 1'b1;
  else if (wr_en && (~rd_en) )
    empty <= 1'b0;
  else if (rd_en && (~wr_en) )
    empty <= 1'b1;
end

// spyglass enable_block STARC-2.3.4.3
// leda W396 on
//leda NTL_CON32 on
endmodule
