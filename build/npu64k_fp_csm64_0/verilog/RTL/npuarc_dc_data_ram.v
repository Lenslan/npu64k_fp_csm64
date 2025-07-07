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
// #####   ####     #####      ##   #######  ##       #####     ##    #     #
// #    # #    #    #    #    #  #     #    #  #      #    #   #  #   ##   ##
// #    # #         #    #   #    #    #   #    #     #    #  #    #  # # # #
// #    # #         #    #   #    #    #   #    #     #####   #    #  #  #  #
// #    # #         #    #   ######    #   ######     #  #    ######  #     #
// #    # #    #    #    #   #    #    #   #    #     #   #   #    #  #     #
// #####   #### ### #####    #    #    #   #    # ### #    #  #    #  #     #
//
// ===========================================================================
//
// Description:
//  This file implements a behavioural model of a D-cache data memory, for
//  use in simulation of the ARCv2HS processor.
//

//  NOTE: this module should not be synthesized, nor should it be used
//  for gate-level simulation as it contains no delay information.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o dc_data_ram.vpp
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
module npuarc_dc_data_ram (
  input                       clk,      // clock input
  input   [77:0]    din,      // write data input
  input   [13:4]     addr,     // address for read or write
  input                       cs,       // RAM chip select, active high
  input                       we,       // write enable, active high
  input   [9:0]  wem,      // byte write enables, active high
  input                       ds,       // deep sleep, active high
  input                       sd,       // shutdown, active high
// spyglass disable_block W240
// SMD: Input declared but not read.
// SJ:  This only a func model. Port required in real design.
   input                      ls,       // light sleep
// spyglass enable_block W240
  output  [77:0]    dout      // read data output
);


`ifndef FPGA_INFER_MEMORIES   // {
`ifdef VERILATOR  // {
`define XCAM_MODEL
`endif            // }
`ifdef TTVTOC     // {
`define XCAM_MODEL
`endif            // }

reg  [7:0]    mem_b0[0:1023];
reg  [7:0]    mem_b1[0:1023];
reg  [7:0]    mem_b2[0:1023];
reg  [7:0]    mem_b3[0:1023];
reg  [6:0]    mem_b4[0:1023]; // ECC bits
reg  [7:0]    mem_b5[0:1023];
reg  [7:0]    mem_b6[0:1023];
reg  [7:0]    mem_b7[0:1023];
reg  [7:0]    mem_b8[0:1023];
reg  [6:0]    mem_b9[0:1023]; // ECC bits

`ifndef XCAM_MODEL  // {
reg      sd_r;
integer                   index;
`endif  // }

reg  [13:4]  addr_r;

`ifndef XCAM_MODEL  // {
reg                   read_cycle1_r;
reg                   read_cycle2_r;
reg                   write_cycle_r;
`endif  // }

wire dc_data_read  = cs & !we;
wire dc_data_write = cs & we;

wire [77:0]    dout_shadow;

//////////////////////////////////////////////////////////////////////////
// Capture the read address
//
//////////////////////////////////////////////////////////////////////////

always @(posedge clk)
begin
  `ifndef XCAM_MODEL  // {
  if(ds == 1'b1)
  begin
    addr_r       <= 'dx;
  end 
  else if (dc_data_read == 1'b1 && sd == 1'b0 && ds == 1'b0)
  `else // } {
  if (dc_data_read)
  `endif  // }
  begin
    addr_r      <= addr;
  end
end

// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty default statements kept
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.

`ifndef XCAM_MODEL  // {
//////////////////////////////////////////////////////////////////////////
// Probing the clock inverter 
// using this information to model 1.5 cycle memory
// During a Read:
//      Dout = XXX in first cycle
//      Dout = data in second cycle
// During a Write:
//      Dout = XXX after a write
//////////////////////////////////////////////////////////////////////////

wire clk_free = npuarc_alb_srams.clk;

always @(posedge clk_free)
begin
  read_cycle1_r   <= dc_data_read;
  read_cycle2_r   <= read_cycle1_r;
  
  casez ({dc_data_read, dc_data_write})
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

  default:
    ;
  endcase

end
`endif  // }

// spyglass enable_block W398
//////////////////////////////////////////////////////////////////////////
// Perform the write operation
//
//////////////////////////////////////////////////////////////////////////

always @(posedge clk)
begin: dc_data_write_PROC

`ifndef XCAM_MODEL  // {
  sd_r <= sd;
  if(sd == 1'b1)
  begin         //currently memory is shut down
    if(sd_r == 1'b0)
    begin       //start of memory shut down
      for (index = 0; index < 1024; index = index + 1)
      begin
        mem_b0[index] = $random;
        mem_b1[index] = $random;
        mem_b2[index] = $random;
        mem_b3[index] = $random;
        mem_b4[index] = $random; // ECC bits
        mem_b5[index] = $random;
        mem_b6[index] = $random;
        mem_b7[index] = $random;
        mem_b8[index] = $random;
        mem_b9[index] = $random; // ECC bits
      end  // for
    end    // if(sd_r == 1'b0)
  end      // if(sd == 1'b1)
  else if(cs == 1'b1 && (we == 1'b1) && sd == 1'b0 && ds == 1'b0)
`else // } {
  if ((cs == 1'b1) && (we == 1'b1))
`endif  // }

  begin
    //Bank0
    //
    if (wem[0] == 1'b1)
    begin
      mem_b0[addr]       <= din[7:0];
    end
    //Bank1
    //
    if (wem[1] == 1'b1)
    begin
      mem_b1[addr]       <= din[15:8];
    end
    //Bank2
    //
    if (wem[2] == 1'b1)
    begin
      mem_b2[addr]       <= din[23:16];
    end
    //Bank3
    //
    if (wem[3] == 1'b1)
    begin
      mem_b3[addr]       <= din[31:24];
    end
    //Bank4 ECC Bits
    //
    if (wem[4] == 1'b1)
    begin
      mem_b4[addr]       <= din[38:32];
    end
    //Bank5
    //
    if (wem[5] == 1'b1)
    begin
      mem_b5[addr]       <= din[46:39];
    end
    //Bank6
    //
    if (wem[6] == 1'b1)
    begin
      mem_b6[addr]       <= din[54:47];
    end
    //Bank7
    //
    if (wem[7] == 1'b1)
    begin
      mem_b7[addr]       <= din[62:55];
    end
    //Bank8
    //
    if (wem[8] == 1'b1)
    begin
      mem_b8[addr]       <= din[70:63];
    end
    //Bank9 ECC Bits
    //
    if (wem[9] == 1'b1)
    begin
      mem_b9[addr]       <= din[77:71];
    end
  end  // if ((cs == 1'b1) && (we == 1'b1))
end    // dc_data_write_PROC

//////////////////////////////////////////////////////////////////////////
// Perform the read operation
//
//////////////////////////////////////////////////////////////////////////
// spyglass disable_block STARC05-2.10.1.4a
// SMD: signal compared with x
// SJ:  checking if memory is initialized
// spyglass disable_block STARC05-2.10.1.4b
// SMD: signal compared with value containing x or z
// SJ:  checking if memory is initialized
wire [7:0] tmp_mem_b0 = (^mem_b0[addr_r] === 1'bx) ? $random : mem_b0[addr_r];
wire [7:0] tmp_mem_b1 = (^mem_b1[addr_r] === 1'bx) ? $random : mem_b1[addr_r];
wire [7:0] tmp_mem_b2 = (^mem_b2[addr_r] === 1'bx) ? $random : mem_b2[addr_r];
wire [7:0] tmp_mem_b3 = (^mem_b3[addr_r] === 1'bx) ? $random : mem_b3[addr_r];
wire [6:0] tmp_mem_b4 = (^mem_b4[addr_r] === 1'bx) ? $random : mem_b4[addr_r]; // ECC bits
wire [7:0] tmp_mem_b5 = (^mem_b5[addr_r] === 1'bx) ? $random : mem_b5[addr_r];
wire [7:0] tmp_mem_b6 = (^mem_b6[addr_r] === 1'bx) ? $random : mem_b6[addr_r];
wire [7:0] tmp_mem_b7 = (^mem_b7[addr_r] === 1'bx) ? $random : mem_b7[addr_r];
wire [7:0] tmp_mem_b8 = (^mem_b8[addr_r] === 1'bx) ? $random : mem_b8[addr_r];
wire [6:0] tmp_mem_b9 = (^mem_b9[addr_r] === 1'bx) ? $random : mem_b9[addr_r]; // ECC bits

// spyglass enable_block STARC05-2.10.1.4a
// spyglass enable_block STARC05-2.10.1.4b

wire [77:0] dc_mem_rd_data_prel = {
                              tmp_mem_b9,
                              tmp_mem_b8,
                              tmp_mem_b7,
                              tmp_mem_b6,
                              tmp_mem_b5,
                              tmp_mem_b4,
                              tmp_mem_b3,
                              tmp_mem_b2,
                              tmp_mem_b1,
                              tmp_mem_b0
                             };       

// model 1.5 cycle memory
`ifndef XCAM_MODEL  // {
`ifdef SAFETY_SRAM_SIM //{
reg  [77:0] data_out_prel=0;
`else //} {
reg  [77:0] data_out_prel;
`endif //}
always @*
begin
  if (write_cycle_r)
  begin
// spyglass disable_block W164b
// SMD: LHS < RHS in assignment
// SJ:  Not a problem to have empty bits
    data_out_prel = $random;
  end
  else
  begin
    case (read_cycle1_r)
    1'b1: data_out_prel = dc_mem_rd_data_prel;
    default:;
    endcase
  end
// spyglass enable_block W164b
end


assign dout = data_out_prel;
assign dout_shadow = data_out_prel;
`else // } {
assign dout = dc_mem_rd_data_prel;
assign dout_shadow = dc_mem_rd_data_prel;
`endif  // }
`undef XCAM_MODEL

`else  // } {
//////////////////////////////////////////////////////////////////////////
// This part is for FPGA memory modelling
//
// Memory layout:
//
//  <--ECC (7) or parity(1)-->, <--32-->,  <--ECC (7) or parity(1)-->, <--32-->

wire                  rden; // memory read enable
wire [77:0]           wren; // write enables

assign rden = cs & ~we;
assign wren =   {78{cs & we}} 
             &  { {7{wem[9]}}, {8{wem[8]}}, {8{wem[7]}}, {8{wem[6]}}, {8{wem[5]}},   
                  {7{wem[4]}}, {8{wem[3]}}, {8{wem[2]}}, {8{wem[1]}}, {8{wem[0]}} };

npuarc_fpga_sram 
  #(.MEM_SIZE    (1024),
    .DATA_WIDTH  (78),
    .ADDR_MSB    (13),
    .ADDR_LSB    (4), 
    .WR_SIZE     (1), 
    .SYNC_OUT    (0),
    .PIPELINED   (0),
    .RAM_STL     ("no_rw_check")) 
     u_dc_data_ram (
  .clk     (clk ),    
  .din     (din ),    
  .addr    (addr),   
  .regen   (1'b1),  
  .rden    (rden),   
  .wren    (wren),   
  .dout    (dout)  
);
    
`endif  // }

// spyglass enable_block W193

endmodule

// leda on
// spyglass enable_block ALL
