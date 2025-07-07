// Library ARCv2HS-3.5.999999999

// generic RAM  (used by MMU nTLB)

// spyglass disable_block ALL
//
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
module npuarc_mmu_ntlb_pd0_ram
#(parameter 
  RAM_DATA_WIDTH  = 32 + 7*(1) + (((3 == 3) || (3 == 3) || (2 == 2) || (3 == 3) || (0 == 3) || (0 == 3) || (0 == 3)) && 0 ),
  RAM_ADDR_WIDTH  = 7,
  RAM_DEPTH       = 128
)
(
  input                        clk,  // clock input
  input   [RAM_DATA_WIDTH-1:0] din,  // write data input
  input   [RAM_ADDR_WIDTH-1:0] addr, // address for read or write
  input                        cs,   // ME (memory enable) active high
  input                        we,   // write enable, active high
//input   [RAM_DATA_WIDTH-1:0] wem,  // write enable mask, active high
  input   [(4+4)-1:0] wem,  // write enable mask, active high
  input                        ds,   // deep sleep, active high
  input                        sd,   // shutdown, active high
  input                        ls,   // light sleep
  output  [RAM_DATA_WIDTH-1:0] dout  // read data output

);

`ifdef FPGA_INFER_MEMORIES 
`define npuarc_SIMPLE_RAM_MODELS 1
`endif
`ifdef TTVTOC 
`define npuarc_SIMPLE_RAM_MODELS 1
`endif
`ifndef npuarc_SIMPLE_RAM_MODELS

reg   /*sparse*/  [RAM_DATA_WIDTH-1:0]    mem[0:RAM_DEPTH - 1];
// need to declare memories from 0 to maximum upper limit exactly as written here.
// sparse is a directive to the simulator to save memory on unused addresses

`ifdef SAFETY_SRAM_SIM //{
reg  [RAM_DATA_WIDTH-1:0]    data_out_prel=0;
`else //} {
reg  [RAM_DATA_WIDTH-1:0]    data_out_prel;
`endif //}
reg  [RAM_DATA_WIDTH-1:0]    data_in_prel;
reg      sd_r;
integer                   index;
// per way write mask (4b),expand to (wr en) bit mask
wire [RAM_DATA_WIDTH-1:0]  webm;
parameter WAY_DATA_WIDTH   = (RAM_DATA_WIDTH - (7*4*1*(1)))/4;
assign webm =
  { {7{wem[7] & wem[3]}},      // way3 ecc      
    {WAY_DATA_WIDTH{wem[3]}},  //      data
    {7{wem[6] & wem[2]}},      // way2 ecc
    {WAY_DATA_WIDTH{wem[2]}},  //      data
    {7{wem[5] & wem[1]}},      // way1 ecc
    {WAY_DATA_WIDTH{wem[1]}},  //      data
    {7{wem[4] & wem[0]}},      // way0 ecc
    {WAY_DATA_WIDTH{wem[0]}}   //      data
  };

always @(posedge clk)
begin: mmu_ntlb_ram_PROC
 sd_r <= sd;
// spyglass disable_block NoAssignX-ML
// SMD: RHS of assignment contains 'X'
// SJ:  Okay for RAM_DATA_WIDTH
 if(sd == 1'b1)begin//current memory is shut down
     if(sd_r == 1'b0)begin
       for (index = 0; index < RAM_DEPTH; index = index + 1)
         begin
           mem[index] = {RAM_DATA_WIDTH{1'b x}}; 
         end
     end  
// spyglass disable_block W164a
// spyglass disable_block W164b
// SMD: LHS and RHS unequal widths
// SJ:  empty bits okay
     data_out_prel <= {$random, $random, $random};
// spyglass enable_block NoAssignX-ML
 end else if(ds == 1'b1)begin//current memory is ratetion mode, all wr/rd access is igored
     data_out_prel <= {$random, $random, $random};
 end else if(cs == 1'b1 && sd == 1'b0 && ds == 1'b0)

  begin
     if (we == 1'b1)
     begin
       // Doing a write
       // use input mask to only write bits for which the mask bit is high
       //
       data_in_prel   = (din & webm) | (mem[addr] & ~webm);
       mem[addr]     <= data_in_prel;  
       data_out_prel <= {$random, $random, $random};
     end
     else
     begin
       // Doing a read
       //
// spyglass disable_block STARC05-2.10.1.4a
// SMD: signal compared with x
// SJ:  checking if memory is initialized
// spyglass disable_block STARC05-2.10.1.4b
// SMD: signal compared with value containing x or z
// SJ:  checking if memory is initialized
       data_out_prel <= (^mem[addr] === 1'bx) ? $random : mem[addr];
// spyglass enable_block STARC05-2.10.1.4a
// spyglass enable_block STARC05-2.10.1.4b
// spyglass enable_block W164a
// spyglass enable_block W164b
     end
  end
end

assign dout =  data_out_prel;

wire [RAM_DATA_WIDTH-1:0] dout_shadow;
assign dout_shadow = data_out_prel;

  // Initialize RAM contents to avoid undefined values
  //
  // synopsys translate_off
  integer i;

  initial
    for (i = 0; i < RAM_DEPTH; i = i + 1) mem[i] = 0;
  // synopsys translate_on


`else

// This part is for FPGA memory modelling
    
wire                  rden; // memory read enable

wire [RAM_DATA_WIDTH-1:0] wren; // write enables
assign rden = cs & ~we;
parameter WAY_DATA_WIDTH   = (RAM_DATA_WIDTH - (7*4*1*(1)))/4;
assign wren =
  { {7{wem[3]}},               // way3 ecc      
    {WAY_DATA_WIDTH{wem[3]}},  //      data
    {7{wem[2]}},               // way2 ecc
    {WAY_DATA_WIDTH{wem[2]}},  //      data
    {7{wem[1]}},               // way1 ecc
    {WAY_DATA_WIDTH{wem[1]}},  //      data
    {7{wem[0]}},               // way0 ecc
    {WAY_DATA_WIDTH{wem[0]}}   //      data
  };

  // Initialize RAM contents to avoid undefined values
  //
`ifndef TTVTOC 
  // synopsys translate_off
  integer i;

  initial
    for (i = 0; i < RAM_DEPTH; i = i + 1) u_mmu_ntlb_pd0_ram.mem_r[i] = 0;
  // synopsys translate_on
`endif


npuarc_fpga_sram 
  #(.MEM_SIZE    (RAM_DEPTH),
    .DATA_WIDTH  (RAM_DATA_WIDTH),
    .ADDR_MSB    (RAM_ADDR_WIDTH-1),
    .ADDR_LSB    (0), 
    .WR_SIZE     (1),  
    .SYNC_OUT    (0),
    .PIPELINED   (0),
    .RAM_STL     ("no_rw_check")) 
     u_mmu_ntlb_pd0_ram (
  .clk     (clk ),    
  .din     (din ),    
  .addr    (addr),   
  .regen   (1'b1),  
  .rden    (rden),   
  .wren    ({RAM_DATA_WIDTH{cs & we}} & wren),   
  .dout    (dout)  
);


`undef npuarc_SIMPLE_RAM_MODELS
`endif



endmodule
// leda on
// spyglass enable_block ALL
