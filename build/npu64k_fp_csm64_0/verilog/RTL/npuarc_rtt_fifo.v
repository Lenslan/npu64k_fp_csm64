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
//   rtt_fifo
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_fifo.vpp
//
// ===========================================================================

`include "npuarc_rtt_pkg_defines.v"
`include "npuarc_arc_rtt_defines.v"
module npuarc_rtt_fifo(
                          rtt_clk,
                          rst_a,
                          wr_en,
                          rd_en,
                          rd_vld,
                          full,
                          empty,
                          num_fill,
                          wr_ptr,
                          rd_ptr
                         );

//-------------------------------------------------------------------
//parametes can be overwrite
//-------------------------------------------------------------------
parameter FIFO_SIZE       = 9;
localparam ONE_UNIT       = 1'b1;

input                          rtt_clk;         // Clock
input                          rst_a;       // FIFO Reset
input                          wr_en;       // Write enable
input                          rd_en;       // Read enable
output                         rd_vld;
output                         full;        // FIFO full
output                         empty;       // FIFO empty
// leda NTL_CON32 off
output [FIFO_SIZE:0]           num_fill;    // No. of locations filled
// leda NTL_CON32 on
output    [FIFO_SIZE-1:0]           wr_ptr;      // Write pointer
output   [FIFO_SIZE-1:0]           rd_ptr;
reg                            rd_vld;
wire                           full;
wire                           empty;
reg    [FIFO_SIZE:0]           num_fill;

reg                            fifo_full;
reg                            fifo_empty;
reg   [FIFO_SIZE-1:0]          wr_ptr;      // Write pointer
reg   [FIFO_SIZE-1:0]          rd_ptr;
wire  [FIFO_SIZE-1:0]          wr_ptr_xx;
wire  [FIFO_SIZE-1:0]          rd_ptr_xx;
wire  [FIFO_SIZE:0]            num_fill_xx;
wire  [FIFO_SIZE:0]            num_fill_yy;

//------------------------------------------------------
// Read Data Valid
//------------------------------------------------------
always @(posedge rtt_clk or posedge rst_a)
begin : MEM_RDVALID_BLK_PROC
  if( rst_a == 1'b1 )
    begin
      rd_vld <= 1'b0;
    end
  else
    begin
      rd_vld <= rd_en;
     end
end

//leda BTTF_D002 off
//leda B_3200 off
// spyglass disable_block SelfDeterminedExpr-ML
//-------------------------------------------------------
// Write Pointer
//-------------------------------------------------------

assign wr_ptr_xx = (wr_ptr + ONE_UNIT);

always @( posedge rtt_clk or posedge rst_a )
begin : WR_PTR_PROC
  if( rst_a == 1'b1 )
    wr_ptr <= {(FIFO_SIZE){1'b0}};
  else if( wr_en )
    wr_ptr <= wr_ptr_xx[FIFO_SIZE-1:0];
end

//-------------------------------------------------------
// Read Pointer
//-------------------------------------------------------

assign rd_ptr_xx = (rd_ptr + ONE_UNIT);

always @( posedge rtt_clk or posedge rst_a )
begin : RD_PTR_PROC
  if( rst_a == 1'b1 )
    rd_ptr <= {(FIFO_SIZE){1'b0}};
  else if( rd_en )
    rd_ptr <= rd_ptr_xx[FIFO_SIZE-1:0];
end



//-------------------------------------------------------
// Empty Generation Logic
//-------------------------------------------------------
assign empty = fifo_empty;

//-------------------------------------------------------
// FIFO Empty Generation Logic
//-------------------------------------------------------
always @( posedge rtt_clk or posedge rst_a )
begin : FIFO_EMP_GEN_PROC
  if( rst_a == 1'b1 )
    fifo_empty <= 1'b1;
  else if( wr_en && (~rd_en) )
    fifo_empty <= 1'b0;
  else if((rd_en && (~wr_en)) &&
          (rd_ptr_xx[FIFO_SIZE-1:0] == wr_ptr))
    fifo_empty <= 1'b1;
end

//-------------------------------------------------------
// Full Generation Logic
//-------------------------------------------------------
assign full = fifo_full;

//-------------------------------------------------------
// FIFO Full Generation Logic
//-------------------------------------------------------
always @( posedge rtt_clk or posedge rst_a )
begin : FIFO_FUL_GEN_PROC
  if( rst_a == 1'b1 )
    fifo_full <= 1'b0;
  else if( wr_en && (~rd_en) &&
           (wr_ptr_xx[FIFO_SIZE-1:0] == rd_ptr))
    fifo_full <= 1'b1;
  else if( rd_en && (~wr_en) )
    fifo_full <= 1'b0;
end

//-------------------------------------------------------
// No. of empty locations remained logic
//-------------------------------------------------------
//
// leda W631 off
// leda NTL_CON32 off
// Waiving off self assignment for the statement in the default case

assign num_fill_xx = (num_fill + ONE_UNIT);
assign num_fill_yy = (num_fill - ONE_UNIT);

//-------------------------------------------------------
// Generation of No. of locations filled logic
//-------------------------------------------------------
always @(posedge rtt_clk or posedge rst_a)
begin : NO_FILL_GEN_PROC
  if(rst_a== 1'b1 )
    num_fill <= {(FIFO_SIZE+1){1'b0}};
  else
    case( {wr_en,rd_en} )
      2'b10 : num_fill <= num_fill_xx[FIFO_SIZE:0];
      2'b01 : num_fill <= num_fill_yy[FIFO_SIZE:0];
      default : num_fill <= num_fill;
    endcase
end
// spyglass enable_block SelfDeterminedExpr-ML
// leda W631 on
// leda NTL_CON32 on
//leda BTTF_D002 on
//leda B_3200 on


endmodule
