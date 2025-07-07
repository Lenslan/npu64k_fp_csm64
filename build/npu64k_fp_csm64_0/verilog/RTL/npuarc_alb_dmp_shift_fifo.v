// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2018 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
/// ===========================================================================
//
// Description:
//  This file implements the data memory input FIFO. This
//  is a parametrizable FIFO. This is a shift FIFO and the head
//  of the FIFO is registered.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_shift_fifo.vpp
//
// ===========================================================================


// synopsys translate_off

///////////////////////////////////////////////////////////////////////////
// Common Verilog definitions
///////////////////////////////////////////////////////////////////////////

// Verilog simulator timescale definition for all modules
//
`timescale 1 ns / 10 ps

// synopsys translate_on


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_dmp_shift_fifo
  (
  ////////// General input signals ///////////////////////////////////////////
  //
  input                    clk,                 // clock
  input                    rst_a,               // reset
  
  ////////// FIFO control ////////////////////////////////////////////////////
  //
  input  wire              push,                // push new FIFO element
  input  wire              pop,                 // pop head FIFO element
  
  ////////// input payload ////////////////////////////////////////////////////
  //
  input  wire [89-1:0] data_in,             // new FIFO element
 
  ////////// FIFO output ////////////////////////////////////////////////////
  //
  output wire              valid_out,           // output valid
  output wire [89-1:0] data_out,            // output payload

  ///////// FIFO 's Contents  //////////////////////////////////////////////
  //
  output reg [89-1:0]  data0_r,
  output reg [89-1:0]  data1_r,
  output reg [89-1:0]  data2_r,

  ////////// FIFO status ////////////////////////////////////////////////////
  //
  output reg [3-1:0] valid_r, // valid_entries 
  output wire              one_empty,             // one empty 
  output wire              two_empty,             // two empty
  output wire              full                   // full 
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Declarations for the FIFO data elements and validity flip-flops          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//reg [3-1:0]       valid_r;         
reg [3-1:0]       valid_nxt;         
reg                                   valid_cg0;


//reg [89-1:0]                      data0_r;
reg [89-1:0]                      data0_nxt;
reg                                   data0_cg0;
//reg [89-1:0]                      data1_r;
reg [89-1:0]                      data1_nxt;
reg                                   data1_cg0;
//reg [89-1:0]                      data2_r;
reg [89-1:0]                      data2_nxt;
reg                                   data2_cg0;

reg                                   ibp_valid;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Determine the next value of valid bits
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : valid_nxt_PROC
  // Default value going into the FIFO, with clock enable
  //
  valid_cg0   = push | pop;
  valid_nxt   = valid_r;
  
  casez ({push, pop})
  2'b10:  valid_nxt = {valid_nxt[1:0], 1'b1}; // only push
  2'b01:  valid_nxt = {1'b0, valid_nxt[2:1]}; // only pop
  default:valid_nxt = valid_r;                // no change
  endcase
  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Determine the next value of the FIFO entries
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : data_nxt_PROC
  // When there is only a push or pop,
  // Shift when we pop. Nothing gets shifted into last entry
  //
  // When there is a push and pop. 
  // (1) when valid_r[1] is true then valid_r[0] gets from valid_r[1]
  // (2) when valid_r[1] is not true then valid_r[0] gets data_in
  //
  data0_nxt     = valid_r[1] ? data1_r     : data_in;

  data1_nxt     = valid_r[2] ? data2_r     : data_in;

  data2_nxt     = data_in;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Determine the clock gate enables
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : data_cg_PROC
  // Clock gate enable for the payload entries
  //
  data0_cg0 =  (push & (~valid_r[0]))    // when there is no valid
             | (push & pop & (valid_r[1:0] == 2'b01)) // When there is one valid and there is a push and pop
             | (pop  & valid_r[1]);
  
  data1_cg0 =  ( push & (valid_r[1:0] == 2'b01) & (~pop))
             | ( push & pop & (valid_r == 3'b011)) 
             | ( pop  & valid_r[2]);
  
  data2_cg0 =  (push  & (valid_r[2:0] == 3'b011) & (~pop))
             | (push & pop & (valid_r == 3'b111));
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous process
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : valid_reg_PROC
  if (rst_a == 1'b1)
  begin
    valid_r   <= {3{1'b0}};
  end
  else if (valid_cg0 == 1'b1)
  begin
    valid_r <= valid_nxt;
  end
end

// spyglass disable_block Clock_info03b
// SMD: Data pin of flop clocked by clk , is tied to constant value
// SJ:  Standard bus

always @(posedge clk or posedge rst_a)
begin : data0_reg_PROC
  if (rst_a == 1'b1)
  begin
    data0_r     <= 89'b0;
  end
  else if (data0_cg0 == 1'b1)
  begin
    data0_r     <= data0_nxt;
  end
end
always @(posedge clk or posedge rst_a)
begin : data1_reg_PROC
  if (rst_a == 1'b1)
  begin
    data1_r     <= 89'b0;
  end
  else if (data1_cg0 == 1'b1)
  begin
    data1_r     <= data1_nxt;
  end
end
always @(posedge clk or posedge rst_a)
begin : data2_reg_PROC
  if (rst_a == 1'b1)
  begin
    data2_r     <= 89'b0;
  end
  else if (data2_cg0 == 1'b1)
  begin
    data2_r     <= data2_nxt;
  end
end

// spyglass enable_block Clock_info03b

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output assignments
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign  valid_out   = valid_r[0];          
assign  data_out    = data0_r;
assign  one_empty   = (valid_r == 3'b011);
assign  two_empty   = (valid_r == 3'b001);
assign  full        = (valid_r[2]);

endmodule


