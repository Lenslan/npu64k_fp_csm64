// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//                     
//                     
//   ALB_DMP_SIMPLE_BFIFO                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements a simple parametrizable FIFO structure
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_simple_fifo.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//

// Set simulation timescale
//
// synopsys translate_off

///////////////////////////////////////////////////////////////////////////
// Common Verilog definitions
///////////////////////////////////////////////////////////////////////////

// Verilog simulator timescale definition for all modules
//
`timescale 1 ns / 10 ps

// synopsys translate_on


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }


module npuarc_alb_dmp_simple_fifo 
  #(
    parameter DEPTH = 4,  // Fifo depth
    parameter DEPL2 = 2,  // Log2 depth
    parameter D_W   = 2   // Data width
   )
   (
  
  ////////// General input signals ///////////////////////////////////////////
  //
  input                  clk,                 // clock
  input                  rst_a,               // reset
  

  ////////// FIFO inputs ////////////////////////////////////////////////////
  //
  input  wire            push,                // push new FIFO element
  input  wire [2-1:0]  data_in,             // new FIFO element
  input  wire            pop,                 // pop head FIFO element
  
  ////////// FIFO output ////////////////////////////////////////////////////
  //
  output wire [2-1:0]  head                 // head FIFO element
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Declarations for the FIFO data elements and validity flip-flops          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg [4-1:0]       valid_r;         
reg [4-1:0]       valid_nxt;         

reg [2-1:0]         data_r[4-1:0];          

reg [2-1:0]       wr_ptr_r;  
reg [2-1:0]       rd_ptr_r;                  

//////////////////////////////////////////////////////////////////////////////
// Asynchronous processes
// 
//////////////////////////////////////////////////////////////////////////////
assign head = data_r[rd_ptr_r];



always @*
begin : wq_bfifo_valid_nxt_PROC
  //
  // Default Value
  
  valid_nxt = valid_r;
  
  if (push == 1'b1)
  begin
    valid_nxt[wr_ptr_r] = 1'b1;
  end
  
  if (pop == 1'b1)
  begin
    valid_nxt[rd_ptr_r] = 1'b0;
  end
end


//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
// 
//////////////////////////////////////////////////////////////////////////////
// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions
//
// leda NTL_RST03 off
// LMD: All registers must be asynchronously set or reset Range:0-51
// LJ:  Synthesis will take care
//
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor
//
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
//
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk or posedge rst_a)
begin : wq_bfifo_valid_regs_PROC
  if (rst_a == 1'b1)
  begin
    valid_r <= {DEPTH{1'b0}};
  end
  else
  begin
    valid_r <= valid_nxt;
  end
end

reg [1:0] rd_ptr_nxt;
reg       rd_ptr_cg;
always @(posedge clk or posedge rst_a)
begin : wq_bfifo_rd_ptr_regs_PROC
  if (rst_a == 1'b1)
  begin
    rd_ptr_r  <= {2{1'b0}};
  end
  else if (pop == 1'b1)
  begin
    rd_ptr_r  <= rd_ptr_r + 1'b1;
  end
end

always @(posedge clk or posedge rst_a)
begin : wq_bfifo_wr_ptr_regs_PROC
  if (rst_a == 1'b1)
  begin
    wr_ptr_r  <= {2{1'b0}};
  end
  else if (push == 1'b1)
  begin
    wr_ptr_r  <= wr_ptr_r + 1'b1;
  end
end
// VPOST OFF
// spyglass disable_block ResetFlop-ML
// SMD: Has neither asynchronous set/reset nor synchronous set/reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin: wq_bfifo_data_regs_PROC
  if (push == 1'b1)
  begin
    data_r[wr_ptr_r] <= data_in;
  end
end
// spyglass enable_block ResetFlop-ML
// VPOST ON
// leda W484 on
// leda B_3200 on
// leda NTL_RST03 on
// leda FM_1_7 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

endmodule // alb_dmp_simple_fifo

