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
//  #####      #     #     #  ####    ####   #####   #####
//  #    #    # #    ##   ## #    #  #    #  #    #  #
//  #    #   #   #   # # # # #       #    #  #    #  #
//  #####   #     #  #  #  # #       #    #  #####   #####
//  #  #    #######  #     # #       #    #  #  #    #
//  #   #   #     #  #     # #    #  #    #  #   #   #
//  #    #  #     #  #     #  ####    ####   #    #  #####
//
// ===========================================================================
//
// Description:
//
//  This file implements a behavioural model of an single port sram, for
//  use in simulation of the ARCv2HS processor.
//
//
//  NOTE: this module should not be synthesized, nor should it be used
//  for gate-level simulation as it contains no delay information.
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o ram_core_simple.vpp
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
`ifdef VERILATOR
`define XCAM_MODEL
`endif
`ifdef TTVTOC
`define XCAM_MODEL
`endif
`ifndef RAM_MODEL_OUTINIT 
`define RAM_MODEL_OUTINIT 
`endif

// LEDA off
module npuarc_ram_core #(
  parameter  par_data_msb =  31,
  parameter  par_be_msb   =  31,
  parameter  par_addr_msb =  19,
  parameter  par_addr_lsb =  2
  ) (
  input   [par_data_msb: 0]            din,      // write data input
  input   [par_addr_msb:par_addr_lsb]  addr,     // address for read or write
  input                                cs,       // RAM chip select, active high
  input                                we,       // memory write enable, active high
  input   [par_be_msb             :0]  wem,      // byte write enables, active high
  input                                ds,       // deep sleep, active high
  input                                sd,       // shutdown, active high
  output reg  [par_data_msb       :0]  dout,     // read data output
  input                                clk       // clock input
  );
parameter par_addr_width = (par_addr_msb-par_addr_lsb+1);
parameter par_mem_size = (1 << par_addr_width);
// synopsys translate_off

// Local Declarations
reg  [par_data_msb:0] ram_core_0[0:(par_mem_size-1)];

`ifndef XCAM_MODEL // {
reg                   sd_r;
integer               index;
`endif            // }
wire [par_data_msb:0] dmask;
wire [par_data_msb:0] din_qual;

assign dmask = wem;   
assign din_qual = (dmask & din) | (~dmask & ram_core_0[addr]);
 
`ifdef RAM_MODEL_OUTINIT // {
integer i;
wire [par_data_msb:0] dout_int; 
assign dout_int = ram_core_0[addr];
`endif             // }   // RAM_MODEL_OUTINIT

//control
wire read  = cs & ! (we);
wire write = cs & (we);

//read
`ifdef SAFETY_SRAM_SIM //{
initial dout=0;
`endif //}

`ifndef XCAM_MODEL // {
always @(posedge clk or posedge sd or posedge ds)
`else            // } {
always @(posedge clk)
`endif           // }
begin
 `ifndef XCAM_MODEL  // {
  if (sd == 1'b1) begin     // current memory is shut down
   `ifdef RAM_MODEL_OUTINIT // {
    dout <= $random;
   `else              // } {
    dout <= {(par_data_msb+1){1'bx}};
   `endif             // }
  end else if (ds == 1'b1) begin // current memory is ratetion mode, all wr/rd access is igored
   `ifdef RAM_MODEL_OUTINIT // {
    dout <= $random;
   `else              // } {
    dout <= {(par_data_msb+1){1'bx}};
   `endif             // }
  end else if (read == 1'b1 && sd == 1'b0 && ds == 1'b0)
 `else              // } {
  if (read)
 `endif             // }

 `ifndef XCAM_MODEL  // {
  begin
   `ifdef RAM_MODEL_OUTINIT // {
       for (i = 0; i <= par_data_msb; i = i + 1) begin
    dout[i] <= (dout_int[i] === 1'bx) ? ($random) : dout_int[i];
       end
   `else              // } {
    dout <= ram_core_0[addr];
   `endif             // }   // RAM_MODEL_OUTINIT
  end
  else if (write) begin
   `ifdef RAM_MODEL_OUTINIT // {
    dout <= $random;
   `else              // } {
    dout <= {(par_data_msb+1){1'bx}};
   `endif             // }   // RAM_MODEL_OUTINIT
  end
 `else              // } {
  begin
    dout <= ram_core_0[addr];
  end
 `endif             // }
end

//write

always @(posedge clk)
begin
 `ifndef XCAM_MODEL  // {
  sd_r <= sd;
  if (sd == 1'b1) begin     // current memory is shut down
     if (sd_r == 1'b0) begin
       for (index = 0; index < par_mem_size ; index = index + 1)
         begin
           ram_core_0[index] = {(par_data_msb+1){1'b0}};
         end
     end  
  end else if(write == 1'b1 && sd == 1'b0 && ds == 1'b0)
 `else              // } {
  if (write)
 `endif             // }
  begin
    ram_core_0[addr] = din_qual;
  end
end

//synopsys translate_on

endmodule // ram_core
// LEDA on
// spyglass enable_block ALL
