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
// ######    #####    #######    #      #####      ######      #     #     #
// #     #  #     #      #      # #    #     #     #     #    # #    ##   ##
// #     #  #            #     #   #   #           #     #   #   #   # # # #
// #     #  #            #    #     #  #  ####     ######   #     #  #  #  #
// #     #  #            #    #######  #     #     #   #    #######  #     #
// #     #  #     #      #    #     #  #     #     #    #   #     #  #     #
// ######    #####  #### #    #     #   ##### #### #     #  #     #  #     #
//
// ===========================================================================
//
// Description:
//  This file implements a behavioural model of a D-cache tag memory, for
//  use in simulation of the ARCv2HS processor.
//
//
//  NOTE: this module should not be synthesized, nor should it be used
//  for gate-level simulation as it contains no delay information.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o dc_tag_ram.vpp
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

// LEDA off
module npuarc_dc_tag_ram (
  input                       clk,      // clock input
  input   [33:0]    din,      // write data input
  input   [13:7]     addr,     // address for read or write
  input                       cs,       // RAM chip select, active high
  input                       we,       // memory write enable, active high
  input   [33:0]    wem,      // bit write enable, active high
  output  [33:0]    dout,      // read data output
  input                       ds,       // deep sleep, active high
  input                       sd,       // shutdown, active high
// spyglass disable_block W240
// SMD: Input declared but not read.
// SJ:  This only a func model. Port required in real design.
  input                       ls       // light sleep
// spyglass enable_block W240
);

`ifndef FPGA_INFER_MEMORIES  // {
`ifdef VERILATOR   // {
`define XCAM_MODEL
`endif  // }
`ifdef TTVTOC  // {
`define XCAM_MODEL
`endif  // }

reg     [33:0]    mem[0:(256/2)-1];

reg     [33:0]    data_out_prel;
wire    [33:0]    read_before_write;
wire    [33:0]    read_mod_write;
reg                         cs_delay;
reg     [13:7]     addr_r;
reg                         write_cycle_r;

wire    [33:0]    dout_shadow;
`ifndef XCAM_MODEL  // {
reg                         sd_r;
integer                     index;
`endif  // }
  
assign read_before_write = (  (cs  == 1'b1)
                            & (we  == 1'b1)
                            & (wem != {34{1'b1}}))
                          ? mem[addr]
                          : {34{1'b0}};

assign read_mod_write =   (din               &  wem)
                        | (read_before_write & ~wem);

// perform a tag write
always @(posedge clk)
begin: dc_tag_write_PROC
  cs_delay <= cs; 
  addr_r   <= addr;
  
`ifndef XCAM_MODEL  // {
  sd_r <= sd;
  if (sd == 1'b1)
  begin // currently memory is shut down
    if(sd_r == 1'b0)
    begin
      for (index = 0; index < 256/2; index = index + 1)
      begin
        mem[index] = $random;
      end
    end  
   end 
   else if (cs == 1'b1 && sd == 1'b0 && ds == 1'b0)
`else  // } {
  if (cs == 1'b1)
`endif  // }
  begin
     if (we == 1'b1)
     begin
       // Doing a write
       //
       mem[addr]     <= read_mod_write;
     end
  end
end

// spyglass disable_block W164b
// SMD: LHS < RHS in assignment
// SJ:  data_out_prel being filled with $random, overflow is not worried about
`ifndef XCAM_MODEL  // {
// spyglass disable_block STARC05-2.10.1.4a
// SMD: signal compared with x
// SJ:  checking if memory is initialized
// spyglass disable_block STARC05-2.10.1.4b
// SMD: signal compared with value containing x or z
// SJ:  checking if memory is initialized
assign dout =  (^mem[addr_r] === 1'bx) ? ($random) : mem[addr_r];
assign dout_shadow =  (^mem[addr_r] === 1'bx) ? ($random) : mem[addr_r];
// spyglass enable_block STARC05-2.10.1.4a
// spyglass enable_block STARC05-2.10.1.4b
`else  // } {
assign dout =  mem[addr_r];
assign dout_shadow =  mem[addr_r];
`endif  // }
`undef XCAM_MODEL
// spyglass enable_block W164b
`else  // } {

// This part is for FPGA memory modelling

// the following 3 wires work around a VTOC code generation bug
wire rden = cs & !we;
wire [33:0] wrcs = {34{cs & we}};
wire [33:0] wren = wrcs & wem;

npuarc_fpga_sram #(
  .MEM_SIZE(128),
  .ADDR_MSB(13),
  .ADDR_LSB(7),
  .PIPELINED(1'b0),
  .DATA_WIDTH(34 ),
  .WR_SIZE(1),
  .SYNC_OUT(0),
  .RAM_STL("no_rw_check"))
u_dct_sram (
  .clk              (clk),
  .din              (din),
  .addr             (addr),
  .regen            (1'b1),
  .rden             (rden),
  .wren             (wren),
  .dout             (dout));

`endif  // }

endmodule
// LEDA on
// spyglass enable_block ALL
