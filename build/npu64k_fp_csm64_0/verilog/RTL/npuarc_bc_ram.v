// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2012 Synopsys, Inc. All rights reserved.
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
// BC_RAM
//
// ===========================================================================
//
// Description:
//
//  This file implements a behavioural model of a branch cache memory, for
//  use in simulation of the ARCv2HS processor.
//
//
//  NOTE: this module should not be synthesized, nor should it be used
//  for gate-level simulation as it contains no delay information.
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o bc_ram.vpp
//
// ===========================================================================

// spyglass disable_block ALL
// Configuration-dependent macro definitions
//

`include "npuarc_defines.v"

// Simulation timestep information
//
// synopsys translate_off

///////////////////////////////////////////////////////////////////////////
// Common Verilog definitions
///////////////////////////////////////////////////////////////////////////

// Verilog simulator timescale definition for all modules
//
`timescale 1 ns / 10 ps

// synopsys translate_on

// leda off

module npuarc_bc_ram (
  input                       clk,      // clock input
  input   [67:0] din,      // write data input
  input   [11:4]  addr,     // address for read or write
  input                       cs,       // ME (memory enable), RAM chip select, active high
  input                       we,       // write enable, active high
  input   [67:0] wem,      // write enable mask, active high
  input                       ds,       // deep sleep, active high
  input                       sd,       // shutdown, active high
// spyglass disable_block W240
// SMD: Input declared but not read.
// SJ:  This only a func model. Port required in real design.
  input                       ls,       // light sleep
// spyglass enable_block W240
  output  [67:0] dout      // read data output

);

`ifndef FPGA_INFER_MEMORIES   // {
`ifdef VERILATOR  // {
`define XCAM_MODEL
`endif            // }
`ifdef TTVTOC     // {
`define XCAM_MODEL
`endif            // }

//synopsys translate_off

reg   /*sparse*/  [67:0]   mem[0:256-1];
// need to declare memories from 0 to maximum upper size exactly as written here.
// sparse is a directive to the simulator to save memory on unused addresses

`ifdef SAFETY_SRAM_SIM //{
reg  [67:0]  data_out_prel=0;//Initialize the signal
`else //}{
reg  [67:0]  data_out_prel;
`endif //}

// use input mask to only write bits for which the mask bit is high
wire [67:0]  data_in_prel = (din & wem) | (mem[addr] & ~wem);

`ifndef XCAM_MODEL  // {
reg      sd_r;
integer                   index;
`endif              // }

// These are currently unused...
//  reg [3:0] b_bits;
//  reg [2:0] type0;
//  reg [1:0] offset; 
//  reg [31:12] tag; 
//  reg [31:1] bta; 
//  reg d_bit;
//  reg f_bit;
//  reg [1:0] way;
//  reg [1:0] size0;

always @(posedge clk)
begin: bc_ram_PROC
`ifndef XCAM_MODEL  // {
  sd_r <= sd;
  if (sd == 1'b1) begin // currently memory is shut down
    if (sd_r == 1'b0) begin
      for (index = 0; index < 256; index = index + 1)
      begin
        mem[index] = {68{1'b x}}; 
      end
    end  
    data_out_prel <= $random;
  end else if (ds == 1'b1)
  begin // currently memory is in retention mode, all wr/rd accesses are ignored
    data_out_prel <= $random;
  end else if (cs == 1'b1 && sd == 1'b0 && ds == 1'b0)
`else  // } {
  if (cs == 1'b1)
`endif  // }
  begin
    if (we == 1'b1)
    begin
      // Doing a write
      //
      mem[addr]     <= data_in_prel;  
`ifndef XCAM_MODEL  // {
      data_out_prel <= $random;
`else  // } {
      data_out_prel <= 68'd0;
`endif  // }
    end
    else
    begin
      // Doing a read
      //
      data_out_prel <= (^mem[addr] === 1'bx) ? ($random) : mem[addr];
    end
  end
end

assign dout = data_out_prel;


//synopsys translate_on

`else  // } {

// This part is for FPGA memory modelling

wire [67:0] wren = {68{cs & we}} & wem;

npuarc_fpga_sram #(
  .MEM_SIZE(256),
  .ADDR_MSB(11),
  .ADDR_LSB(4),
  .PIPELINED(1'b0),
  .DATA_WIDTH(68),
  .WR_SIZE(1),
  .SYNC_OUT(0),
  .RAM_STL("no_rw_check"))
u_bc_sram (
  .clk              (clk),
  .din              (din),
  .addr             (addr),
  .regen            (1'b1),
  .rden             (cs & !we),
  .wren             (wren),
  .dout             (dout));

`endif  // }

endmodule
// spyglass enable_block ALL

//leda on
