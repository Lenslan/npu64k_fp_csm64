`include "nl2_cln_defines.v"

module nl2_scm_dbank_sram_all
  #(parameter ADDR_SIZE  = 10,
    parameter DATA_WIDTH = 8,
    parameter ECC_WIDTH  = 0,
    parameter MASK_WIDTH = 1,
    parameter N_NARROW   = 4,
    parameter N_SRAM     = 4)
(
input   [N_SRAM-1:0]       ck_in,
input                      sd,
input                      ds,
input   [DATA_WIDTH-1:0]   data_wr,
input   [ADDR_SIZE-1:0]    addr_in,
input   [MASK_WIDTH-1:0]   mask_in[N_NARROW-1:0],
input   [N_SRAM-1:0]       read_en,
input   [N_SRAM-1:0]       wrte_en,
output  [DATA_WIDTH-1:0]   data_rd[N_SRAM-1:0]
);

localparam NUM_ROWS = `nl2_CFG_SCM_DATA_BANK_SIZE / (N_SRAM * (DATA_WIDTH-ECC_WIDTH)/8);

/////////////////////////////////////////////////////////////////////////////////
// Instantiate four SRAM modules
/////////////////////////////////////////////////////////////////////////////////

for (genvar i=0; i<N_SRAM; i++) begin: g
  nl2_scm_dbank_sram_wrapper
    #(.MEM_SIZE   (NUM_ROWS),   // MEM_SIZE is expressed as number of rows
      .DATA_WIDTH (DATA_WIDTH),
      .ECC_WIDTH  (ECC_WIDTH),
      .MASK_WIDTH (MASK_WIDTH),
      .ADDR_MSB   (ADDR_SIZE-1),
      .N_NARROW   (N_NARROW))
  u_scm_dbank_sram_wrapper
  (.clk    (ck_in[i]),   // clock input
   .sd     (sd),
   .ds     (ds),
   .data_wr (data_wr),    // write data input
   .addr_in (addr_in),    // address for read or write
   .read_en (read_en[i]), // memory read enable
   .wrte_en (wrte_en[i]), // memory write enable
   .mask_in (mask_in),    // data write enables
   .data_rd (data_rd[i])  // read data output
  );
end: g

endmodule // scm_dbank_sram_all
