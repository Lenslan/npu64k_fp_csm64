`include "nl2_cln_defines.v"

module nl2_scm_dbank_sram_wrapper
  #(parameter MEM_SIZE   = 1,
    parameter DATA_WIDTH = 8,
    parameter ECC_WIDTH  = 0,
    parameter MASK_WIDTH = 1,
    parameter ADDR_MSB   = 0,
    parameter N_NARROW   = 4)
(
input                      clk,
input                      sd,
input                      ds,
input   [DATA_WIDTH-1:0]   data_wr,
input   [ADDR_MSB:0]       addr_in,
input                      read_en,
input                      wrte_en,
input   [MASK_WIDTH-1:0]   mask_in[N_NARROW-1:0],
output  [DATA_WIDTH-1:0]   data_rd
);

localparam RAW_WIDTH_NARROW = DATA_WIDTH/N_NARROW;
localparam DATA_WIDTH_NARROW = `nl2_WIDTH_NARROW;
localparam ECC_WIDTH_NARROW = ECC_WIDTH/N_NARROW;
localparam DATA_WIDTH_ALL = DATA_WIDTH-ECC_WIDTH;

/////////////////////////////////////////////////////////////////////////////////
// Instantiate four SRAM modules
/////////////////////////////////////////////////////////////////////////////////

for (genvar i=0; i<N_NARROW; i++) begin: g
  logic [RAW_WIDTH_NARROW-1:0] i_data_wr;
  logic [RAW_WIDTH_NARROW-1:0] i_data_rd;
  // split write data and ecc
  assign i_data_wr = {data_wr[(DATA_WIDTH_ALL+ECC_WIDTH_NARROW*i)+:ECC_WIDTH_NARROW], data_wr[(DATA_WIDTH_NARROW*i)+:DATA_WIDTH_NARROW]};
  // merge read data and ecc
  assign data_rd[(DATA_WIDTH_ALL+ECC_WIDTH_NARROW*i)+:ECC_WIDTH_NARROW] = i_data_rd[DATA_WIDTH_NARROW+:ECC_WIDTH_NARROW];
  assign data_rd[(DATA_WIDTH_NARROW*i)+:DATA_WIDTH_NARROW] = i_data_rd[0+:DATA_WIDTH_NARROW];
// spyglass disable_block Ac_unsync02 Ac_glitch04
// SMD: Unsynchronized Crossing
// SJ:  static 
  nl2_scm_dbank_sram
    #(.MEM_SIZE   (MEM_SIZE),   // MEM_SIZE is expressed as number of rows
      .DATA_WIDTH (RAW_WIDTH_NARROW),
      .ADDR_MSB   (ADDR_MSB))
  u_scm_dbank_sram
  (.clk    (clk),                       // clock input
   .sd     (sd),
   .ds     (ds),
   .din    (i_data_wr),                 // write data input
   .addr   (addr_in),                   // address for read or write
   .regen  (1'b0),                      // register enable (unused)
   .rden   (read_en),                   // memory read enable
   .wren   (wrte_en),                   // memory write enable
   .mask   (mask_in[i]),                // data write enables
   .dout   (i_data_rd)                  // read data output
  );
// spyglass enable_block Ac_unsync02 Ac_glitch04
end: g

endmodule // scm_dbank_sram_wrapper
