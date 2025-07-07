// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright 2010-2018 Synopsys, Inc. All rights reserved.
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
// #####     ####   ####   #     #     #####      #     #     #
//  #   #   #    # #    #  ##   ##     #    #    # #    ##   ##
//  #   #   #      #       # # # #     #    #   #   #   # # # #
//  #   #   #      #       #  #  #     #####   #     #  #  #  #
//  #   #   #      #       #     #     #  #    #######  #     #
//  #   #   #    # #    #  #     #     #   #   #     #  #     #
// #####    ####   ####    #     # ### #    #  #     #  #     #
//
// ===========================================================================
//
// Description:
//  This file implements a behavioural model of an DCCM memory, for
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
//   vpp +q +o dccm_ram.vpp
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
// LEDA off
module npuarc_dccm_ram #(
  parameter  par_data_msb =  38,
  parameter  par_be_msb   =  4,
  parameter  par_addr_msb =  14,
  parameter  par_addr_lsb =  4
  ) (
  input                                ds,
  input                                sd,
// spyglass disable_block W240
// SMD: Input declared but not read.
// SJ:  This only a func model. Port required in real design.
  input                                ls,   // light sleep control - no behavioural modelling needed.
// spyglass enable_block W240
  input                                clk,  // clock input
  input   [par_data_msb: 0]            din,  // write data input
  input   [par_addr_msb:par_addr_lsb]  addr, // address for read or write
  input                                cs,   // RAM chip select, active high
  input                                we,   // memory write enable, active high
  input   [par_be_msb             :0]  wem,  // byte write enables, active high
  output  [par_data_msb           :0]  dout  // read data output
  );

parameter par_addr_width = (par_addr_msb-par_addr_lsb+1);
parameter par_mem_size   = (1 << par_addr_width);
parameter par_data_bits  = (par_data_msb+1);
parameter par_be_bits    = (par_be_msb+1);
`ifndef FPGA_INFER_MEMORIES // {

// Local Declarations

reg  [par_data_msb:0] rd_data;
reg  [par_data_msb:0] rd_data_end;
reg  [par_data_msb:0] rd_mod_data;
reg  [par_data_msb:0] rd_mod_data_end;

wire [par_data_msb:0]            dout_shadow;
wire [par_data_msb:0] data_mask;

reg  [par_data_msb:0] dccm_mem_1[0:(par_mem_size-1)];

reg  [par_addr_msb:par_addr_lsb] addr_r;

`ifndef XCAM_MODEL // {
reg                              sd_r;
integer                          index;
`endif            // }

// Module Definition


wire dccm_read  = cs & !we;
wire dccm_write = cs & we;

///////////////////////////////////////////////////////////////////////////
// Initialize memory with Zero's
//
//////////////////////////////////////////////////////////////////////////
// synopsys translate_off
`ifndef XCAM_MODEL // {
integer i;
initial
begin
  for (i=0; i < par_mem_size; i=i+1) 
  begin
    dccm_mem_1[i] = {par_data_bits{1'b0}};
  end
end
`endif            // }
// synopsys translate_on

//////////////////////////////////////////////////////////////////////////
// Capture the read address
//
//////////////////////////////////////////////////////////////////////////

`ifndef XCAM_MODEL // {
always @(posedge clk or posedge ds)
`else            // } {
always @(posedge clk)
`endif           // }
begin
 `ifndef XCAM_MODEL // {
  if (ds == 1'b1)
  begin
    addr_r       <= 'dx;
  end 
  else if (dccm_read == 1'b1 && sd == 1'b0 && ds == 1'b0) 
 `else             // } {
  if (dccm_read)
 `endif            // }
  begin
    addr_r      <= addr;
  end
end

`ifndef XCAM_MODEL // {
reg                   read_cycle1_r;              
reg                   read_cycle2_r;              
reg                   write_cycle_r;              

//////////////////////////////////////////////////////////////////////////
// Probing the clock inverter 
// using this information to model 1.5 cycle memory
// During a Read:
//   Dout = XXX in first cycle 
//   Dout = data in second cycle
// During a Write:
//   Dout = XXX after a write
//////////////////////////////////////////////////////////////////////////
wire clk_free = npuarc_alb_srams.clk;
// spyglass disable_block W398, STARC05-2.8.1.3
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
always @(posedge clk_free)
begin
  read_cycle1_r   <= dccm_read;
  read_cycle2_r   <= read_cycle1_r;
  
  casez ({dccm_read, dccm_write})
  2'b?1:
  begin
    // write
    //
    write_cycle_r   <= 1'b1;
    read_cycle1_r   <= 1'b0;
    read_cycle2_r   <= 1'b0;  
  end
  
  2'b1?:
  begin
    // read
    //
    write_cycle_r   <= 1'b0;
  end
// spyglass disable_block W193
// SMD: empty statements
// SJ:  empty default statements kept and empty statements cause no problems  
  default:
    ;
// spyglass enable_block W193
  endcase
end
`endif            // }
// spyglass enable_block W398, STARC05-2.8.1.3
//////////////////////////////////////////////////////////////////////////
// Read and Write cycles definition
//
//////////////////////////////////////////////////////////////////////////

// compute write data mask from wem
assign data_mask = { {7{wem[4]}},{8{wem[3]}},{8{wem[2]}},{8{wem[1]}},{8{wem[0]}}};

// perform write operation
`ifndef XCAM_MODEL // {
always @(posedge clk or posedge sd or posedge sd_r)
`else            // } {
always @(posedge clk)
`endif           // }
begin
 `ifndef XCAM_MODEL // {
  sd_r <= sd;
  if  (sd == 1'b1)
  begin // current memory is shut down
    if (sd_r == 1'b0)
    begin
      for (index = 0; index < par_mem_size; index = index + 1)
      begin
        dccm_mem_1[index] = {(par_data_msb+1){1'b0}};
      end
    end  
  end 
  else if  (dccm_write == 1'b1 && sd == 1'b0 && ds == 1'b0)
 `else             // } {
  if (dccm_write)
 `endif            // }
  begin
    // First do a read
    `ifndef XCAM_MODEL // {
// spyglass disable_block STARC05-2.10.1.4a
// SMD: signal compared with x
// SJ:  checking if memory is initialized
// spyglass disable_block STARC05-2.10.1.4b
// SMD: signal compared with value containing x or z
// SJ:  checking if memory is initialized
    rd_data            = (^dccm_mem_1[addr] === 1'bx) ? $random : dccm_mem_1[addr];
// spyglass enable_block STARC05-2.10.1.4a
// spyglass enable_block STARC05-2.10.1.4b
    `else             // } {
    rd_data          = dccm_mem_1[addr];
    `endif            // }
    // rd_data is always big endian, rd_data_end matches din endianness
    rd_data_end        =  Endian_func(rd_data); 

    // Based on the write mask, build the read-modify-data: rd_mod_data
    //
    rd_mod_data      = (data_mask & din) | (~data_mask & rd_data_end);
    // rd_mod_data_end is always big endian
    rd_mod_data_end       = Endian_func(rd_mod_data);
    dccm_mem_1[addr]      = rd_mod_data_end;
  end
end

// perform read operation
wire [par_data_msb:0] dccm_mem_rd_data_prel = dccm_mem_1[addr_r];

`ifndef XCAM_MODEL       // {
reg  [par_data_msb:0] dccm_mem_rd_data;

always @*
begin
  if (write_cycle_r)
  begin
// spyglass disable_block W164b
// spyglass disable_block W164a
    dccm_mem_rd_data = $random;
// spyglass enable_block W164b
// spyglass enable_block W164a
  end
  else
  begin
    case (read_cycle1_r)
    1'b1: dccm_mem_rd_data = dccm_mem_rd_data_prel;
    default:;
    endcase

  end
end
`else                   // } {
wire [par_data_msb:0] dccm_mem_rd_data = dccm_mem_rd_data_prel;
`endif                  // }

assign dout =  Endian_func(dccm_mem_rd_data);
assign dout_shadow = Endian_func(dccm_mem_rd_data);


function [par_data_msb:0] Endian_func;
input [par_data_msb:0] din;
begin
  Endian_func = { din[38:32],din[7:0],  din[15:8], din[23:16],din[31:24]};
end
endfunction


`else        // } { FPGA_INFER_MEMORIES follows...
     
// Memories will be inferred automatically by Synplify
// For FPGA memory is modelled as posedge i.e. 
// inverted clock input is inverted back

wire write = cs &  we;
wire rden  = cs & ~we;
wire [par_data_msb:0] wren = {par_data_bits{write}} &
              { {7{wem[4]}},{8{wem[3]}},{8{wem[2]}},{8{wem[1]}},{8{wem[0]}}};


npuarc_fpga_sram 
  #(.MEM_SIZE    (2048),
    .DATA_WIDTH  (39),
    .ADDR_MSB    (10),
    .ADDR_LSB    (0), 
    .WR_SIZE     (1), 
    .SYNC_OUT    (0),
    .PIPELINED   (0),
    .RAM_STL     ("no_rw_check")) 
     u_dccm_ram (
  .clk     (clk ),    
  .din     (din ),    
  .addr    (addr),   
  .regen   (1'b1),  
  .rden    (rden),   
  .wren    (wren),   
  .dout    (dout)  
);

`endif       // }

endmodule // dccm_ram
// leda on
// spyglass enable_block ALL
