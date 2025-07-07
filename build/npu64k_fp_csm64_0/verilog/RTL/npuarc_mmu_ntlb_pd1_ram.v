// Library ARCv2HS-3.5.999999999



// spyglass disable_block ALL
//
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
module npuarc_mmu_ntlb_pd1_ram
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

// No wr mask needed
wire [RAM_DATA_WIDTH-1:0]  wem = {RAM_DATA_WIDTH{1'b1}};
// spyglass disable_block W164a
// spyglass disable_block W164b
// SMD: LHS and RHS unequal widths
// SJ:  empty bits okay
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
// spyglass enable_block NoAssignX-ML

     data_out_prel <= $random;
 end else if(ds == 1'b1)begin//current memory is ratetion mode, all wr/rd access is igored
     data_out_prel <= $random;
 end else if(cs == 1'b1 && sd == 1'b0 && ds == 1'b0)

  begin
     if (we == 1'b1)
     begin
       // Doing a write
       // use input mask to only write bits for which the mask bit is high
       //
       data_in_prel   = (din & wem) | (mem[addr] & ~wem);
       mem[addr]     <= data_in_prel;  
       data_out_prel <= $random;
// spyglass enable_block W164a
// spyglass enable_block W164b
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
    for (i = 0; i < RAM_DEPTH; i = i + 1) 
    begin
      mem[i] =
        0
      ;
    end
      
  // synopsys translate_on

`else
// This part is for FPGA memory modelling
    
wire                  rden; // memory read enable
// No wr mask needed
wire [RAM_DATA_WIDTH-1:0]  wem = {RAM_DATA_WIDTH{1'b1}};
assign rden = cs & ~we;

  // Initialize RAM contents to avoid undefined values
  //
`ifndef TTVTOC 
  // synopsys translate_off
  integer i;

  initial
    for (i = 0; i < RAM_DEPTH; i = i + 1)  
    begin
      u_mmu_ntlb_pd1_ram.mem_r[i] =
        0
      ;
    end
      
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
     u_mmu_ntlb_pd1_ram (
  .clk     (clk ),    
  .din     (din ),    
  .addr    (addr),   
  .regen   (1'b1),  
  .rden    (rden),   
  .wren    ({RAM_DATA_WIDTH{cs & we}} & wem),   
  .dout    (dout)  
);


`undef npuarc_SIMPLE_RAM_MODELS
`endif

// Function to generate ecc code while initializing mmu pd1 ram
function [6:0] ecc_code;
   
   input [57:0]      data_in;
begin


   ecc_code[0] = data_in[ 0] ^ data_in[ 1] ^ data_in[ 3] ^ data_in[ 4] ^ 
                        data_in[ 6] ^ data_in[ 8] ^ data_in[10] ^ data_in[11] ^
                        data_in[13] ^ data_in[15] ^ data_in[17] ^ data_in[19] ^ 
                        data_in[21] ^ data_in[23] ^ data_in[25] ^ data_in[26] ^
                        data_in[28] ^ data_in[30]
                                                  ^ data_in[32] ^ data_in[34] ^
                        data_in[36] ^ data_in[38] ^ data_in[40] ^ data_in[42] ^
                        data_in[44] ^ data_in[46] ^ data_in[48] ^ data_in[50] ^
                        data_in[52] ^ data_in[54] ^ data_in[56]  
                      ;
    
   ecc_code[1] = data_in[ 0] ^ data_in[ 2] ^ data_in[ 3] ^ data_in[ 5] ^ 
                        data_in[ 6] ^ data_in[ 9] ^ data_in[10] ^ data_in[12] ^
                        data_in[13] ^ data_in[16] ^ data_in[17] ^ data_in[20] ^ 
                        data_in[21] ^ data_in[24] ^ data_in[25] ^ data_in[27] ^
                        data_in[28] ^ data_in[31]
                                                  ^ data_in[32] ^ data_in[35] ^
                        data_in[36] ^ data_in[39] ^ data_in[40] ^ data_in[43] ^
                        data_in[44] ^ data_in[47] ^ data_in[48] ^ data_in[51] ^
                        data_in[52] ^ data_in[55] ^ data_in[56]  
                      ;

   ecc_code[2] = data_in[ 1] ^ data_in[ 2] ^ data_in[ 3] ^ data_in[ 7] ^ 
                        data_in[ 8] ^ data_in[ 9] ^ data_in[10] ^ data_in[14] ^ 
                        data_in[15] ^ data_in[16] ^ data_in[17] ^ data_in[22] ^ 
                        data_in[23] ^ data_in[24] ^ data_in[25] ^ data_in[29] ^
                        data_in[30] ^ data_in[31] 
                                                  ^ data_in[32] ^ data_in[37] ^
                        data_in[38] ^ data_in[39] ^ data_in[40] ^ data_in[45] ^
                        data_in[46] ^ data_in[47] ^ data_in[48] ^ data_in[53] ^
                        data_in[54] ^ data_in[55] ^ data_in[56]  
                      ;

   ecc_code[3] = data_in[ 4] ^ data_in[ 5] ^ data_in[ 6] ^ data_in[ 7] ^ 
                        data_in[ 8] ^ data_in[ 9] ^ data_in[10] ^ data_in[18] ^
                        data_in[19] ^ data_in[20] ^ data_in[21] ^ data_in[22] ^ 
                        data_in[23] ^ data_in[24] ^ data_in[25]
                                                                ^ data_in[33] ^
                        data_in[34] ^ data_in[35] ^ data_in[36] ^ data_in[37] ^
                        data_in[38] ^ data_in[39] ^ data_in[40] ^ data_in[49] ^
                        data_in[50] ^ data_in[51] ^ data_in[52] ^ data_in[53] ^
                        data_in[54] ^ data_in[55] ^ data_in[56] 
                      ;

   ecc_code[4] = data_in[11] ^ data_in[12] ^ data_in[13] ^ data_in[14] ^ 
                        data_in[15] ^ data_in[16] ^ data_in[17] ^ data_in[18] ^ 
                        data_in[19] ^ data_in[20] ^ data_in[21] ^ data_in[22] ^
                        data_in[23] ^ data_in[24] ^ data_in[25] 
                                                                ^ data_in[41] ^
                        data_in[42] ^ data_in[43] ^ data_in[44] ^ data_in[45] ^
                        data_in[46] ^ data_in[47] ^ data_in[48] ^ data_in[49] ^
                        data_in[50] ^ data_in[51] ^ data_in[52] ^ data_in[53] ^
                        data_in[54] ^ data_in[55] ^ data_in[56] 
                      ;

   ecc_code[5] = data_in[26] ^ data_in[27] ^ data_in[28] ^ data_in[29] ^ 
                        data_in[30] ^ data_in[31]
                                                  ^ data_in[32] ^ data_in[33] ^
                        data_in[34] ^ data_in[35] ^ data_in[36] ^ data_in[37] ^
                        data_in[38] ^ data_in[39] ^ data_in[40] ^ data_in[41] ^
                        data_in[42] ^ data_in[43] ^ data_in[44] ^ data_in[45] ^
                        data_in[46] ^ data_in[47] ^ data_in[48] ^ data_in[49] ^
                        data_in[50] ^ data_in[51] ^ data_in[52] ^ data_in[53] ^
                        data_in[54] ^ data_in[55] ^ data_in[56]
                      ;

   ecc_code[6] = data_in[ 0] ^ data_in[ 1] ^ data_in[ 2] ^ data_in[ 3] ^
                        data_in[ 4] ^ data_in[ 5] ^ data_in[ 6] ^ data_in[ 7] ^
                        data_in[ 8] ^ data_in[ 9] ^ data_in[10] ^ data_in[11] ^
                        data_in[12] ^ data_in[13] ^ data_in[14] ^ data_in[15] ^
                        data_in[16] ^ data_in[17] ^ data_in[18] ^ data_in[19] ^
                        data_in[20] ^ data_in[21] ^ data_in[22] ^ data_in[23] ^
                        data_in[24] ^ data_in[25] ^ data_in[26] ^ data_in[27] ^
                        data_in[28] ^ data_in[29] ^ data_in[30] ^ data_in[31] ^
                        data_in[32] ^ data_in[33] ^ data_in[34] ^ data_in[35] ^ 
                        data_in[36] ^ data_in[37] ^ data_in[38] ^ data_in[39] ^
                        data_in[40] ^ data_in[41] ^ data_in[42] ^ data_in[43] ^
                        data_in[44] ^ data_in[45] ^ data_in[46] ^ data_in[47] ^
                        data_in[48] ^ data_in[49] ^ data_in[50] ^ data_in[51] ^ 
                        data_in[52] ^ data_in[53] ^ data_in[54] ^ data_in[55] ^
                        data_in[56] ^
                        ecc_code[0] ^ ecc_code[1] ^ ecc_code[2] ^ ecc_code[3] ^
                        ecc_code[4] ^ ecc_code[5]
                      ;
end
endfunction //: gen_ecc_pd1


endmodule
// leda on
// spyglass enable_block ALL
