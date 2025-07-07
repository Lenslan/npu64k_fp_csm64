// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2011 Synopsys, Inc. All rights reserved.
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
// ###   ####      #####      #   #######   #        #####      #     #     #
//  #   #    #     #    #    # #     #     # #       #    #    # #    ##   ##
//  #   #          #    #   #   #    #    #   #      #    #   #   #   # # # #
//  #   #          #    #  #     #   #   #     #     #####   #     #  #  #  #
//  #   #          #    #  #######   #   #######     #  #    #######  #     #
//  #   #    #     #    #  #     #   #   #     #     #   #   #     #  #     #
// ###   ####  ### #####   #     #   #   #     # ### #    #  #     #  #     #
//
// ===========================================================================
//
// Description:
//
//  This file implements a behavioural model of an I-cache data memory, for
//  use in simulation of the ARCv2HS processor.
//
//
//  NOTE: this module should not be synthesized, nor should it be used
//  for gate-level simulation as it contains no delay information.
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o ic_data_ram.vpp
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
module npuarc_ic_data_ram (
  input          clk,      // clock input
  input   [77:0] din,      // write data input
  input   [10:0] addr,     // address for read or write
  input          cs,       // RAM chip select, active high
  input          we,       // write enable, active high
  input   [9:0]  wem,      //byte enable, active high
  input          ds,       // deep sleep, active high
  input          sd,       // shutdown, active high
// spyglass disable_block W240
// SMD: Input declared but not read.
// SJ:  This only a func model. Port required in real design.
  input          ls,       // light sleep
// spyglass enable_block W240
  output  [77:0] dout  // read data output
);

`ifndef FPGA_INFER_MEMORIES
`ifdef VERILATOR  // {
`define XCAM_MODEL
`endif            // }
`ifdef TTVTOC     // {
`define XCAM_MODEL
`endif            // }


wire [77:0] dmask = {
                        {7{wem[9]}},  // ECC
                        {7{wem[8]}},  // ECC
                        {8{wem[7]}},
                        {8{wem[6]}},
                        {8{wem[5]}},
                        {8{wem[4]}},
                        {8{wem[3]}},
                        {8{wem[2]}},
                        {8{wem[1]}},
                        {8{wem[0]}}};

// synopsys translate_off

npuarc_ram_core #(
    77,
    77, // bit enabled
    10,
    0
  ) ram_core (
  .clk (clk),
  .din (din),
  .addr (addr),
  .cs (cs),
  .we (we),
  .ds (ds),      
  .sd (sd),      
  .wem (dmask),
  .dout (dout)
);


// synopsys translate_on

`else

// memory read enable
wire rden = cs & ~we;
// memory bit write enables
wire [77:0] wren = {78{cs & we}} & {
                        {7{wem[9]}},  // ECC
                        {7{wem[8]}},  // ECC
                        {8{wem[7]}},
                        {8{wem[6]}},
                        {8{wem[5]}},
                        {8{wem[4]}},
                        {8{wem[3]}},
                        {8{wem[2]}},
                        {8{wem[1]}},
                        {8{wem[0]}}};

npuarc_fpga_sram #(
  .MEM_SIZE((1<<(10+1))),
  .ADDR_MSB(10),
  .ADDR_LSB(0),
  .PIPELINED(1'b0),
  .DATA_WIDTH(78),
   .WR_SIZE     (1), 
  .SYNC_OUT(0),
  .RAM_STL("no_rw_check"))
u_icdata_sram (
  .clk              (clk),
  .din              (din),
  .addr             (addr),
  .regen            (1'b1),
  .rden             (rden),
  .wren             (wren),
  .dout             (dout));

`endif

endmodule

// leda on
// spyglass enable_block ALL
