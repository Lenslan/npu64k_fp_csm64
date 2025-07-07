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
// PT_RAM
//
// ===========================================================================
//
// Description:
//
//  This file implements a behavioural model of a branch prediction table
//  memory, for use in simulation of the ARCv2 processor.
//
//
//  NOTE: this module should not be synthesized, nor should it be used
//  for gate-level simulation as it contains no delay information.
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o pt_ram.vpp
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
module npuarc_pt_ram (
  input                   clk,      // clock input
  input   [7:0]           din,      // write data input
  input   [13:4]          addr,     // address for read or write
  input                   cs,       // ME (memory enable), RAM chip select, active high
  input                   we,       // write enable, active high
  input   [7:0]           wem,      // write enable mask, active high
  input                   ds,       // deep sleep, active high
  input                   sd,       // shutdown, active high
// spyglass disable_block W240
// SMD: Input declared but not read.
// SJ:  This only a func model. Port required in real design.
  input                   ls,       // light sleep
// spyglass enable_block W240
  output  [7:0]           dout      // read data output

);

`ifndef FPGA_INFER_MEMORIES   // {

`ifdef VERILATOR  // {
`define XCAM_MODEL
`endif            // }
`ifdef TTVTOC     // {
`define XCAM_MODEL
`endif            // }

//synopsys translate_off

reg   /*sparse*/  [7:0]    mem[0:1024-1];
// need to declare memories from 0 to maximum upper limit exactly as written here.
// sparse is a directive to the simulator to save memory on unused addresses
`ifdef SAFETY_SRAM_SIM //{
reg  [7:0]  data_out_prel=0;
`else
reg  [7:0]  data_out_prel;
`endif
wire [7:0]  data_in_prel = (din & wem) | (mem[addr] & ~wem);  // use input mask to only write bits for which the mask bit is high
wire [7:0]  data_tmp = mem[addr];
`ifndef XCAM_MODEL  // {
reg         sd_r;
integer     index;
`endif  // }

`ifndef XCAM_MODEL  // {
reg  [31:0] random_tmp; // place holder for random number
`endif  // }

always @(posedge clk)
begin: pt_ram_PROC
`ifndef XCAM_MODEL  // {
  sd_r <= sd;
  if (sd == 1'b1)
  begin // currently memory is shut down
    if (sd_r == 1'b0)
    begin
      for (index = 0; index < 1024; index = index + 1)
        begin
          random_tmp = $random;
          mem[index] = random_tmp[7:0]; 
        end
    end  
    random_tmp = $random;
    data_out_prel <= random_tmp[7:0];
  end else if (ds == 1'b1)
  begin // currently memory is in retention mode, all wr/rd accesses are ignored
    random_tmp = $random;
    data_out_prel <= random_tmp[7:0];
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
      random_tmp = $random;
      data_out_prel <= random_tmp[7:0];
`else  // } {
      data_out_prel <= 8'b0;
`endif  // }
    end
    else
    begin
      // Doing a read
      //
`ifndef XCAM_MODEL  // {
      random_tmp = $random;
      data_out_prel <= ((^data_tmp) === 1'bx) ? (random_tmp[7:0]) : data_tmp;
`else  // } {
      data_out_prel <= data_tmp;
`endif  // }
    end
  end
end

assign dout =  data_out_prel;


//synopsys translate_on

`else  // } {

// This part is for FPGA memory modeling

wire [7:0] wren = {8{cs & we}} & wem;

npuarc_fpga_sram #(
  .MEM_SIZE(1024),
  .ADDR_MSB(13),
  .ADDR_LSB(4),
  .PIPELINED(1'b0),
  .DATA_WIDTH(8),
  .WR_SIZE(1),
  .SYNC_OUT(0),
  .RAM_STL("no_rw_check"))
u_pt_sram (
  .clk              (clk),
  .din              (din),
  .addr             (addr),
  .regen            (1'b1),
  .rden             (cs & !we),
  .wren             (wren),
  .dout             (dout));
  
`endif  // }

endmodule

//leda on
// spyglass enable_block ALL
