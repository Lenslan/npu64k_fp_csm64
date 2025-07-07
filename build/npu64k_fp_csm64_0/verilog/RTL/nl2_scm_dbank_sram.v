// Use only for simulation and modeling.
//
`include "nl2_cln_defines.v"
// spyglass disable_block ALL
// leda off

module nl2_scm_dbank_sram
  #(parameter MEM_SIZE   = 1,
    parameter DATA_WIDTH = 8,
    parameter ADDR_MSB   = 0,
    parameter ADDR_LSB   = 0,
    parameter WR_SIZE    = 8,
    parameter SYNC_OUT   = 1'b1,
    parameter PIPELINED  = 1'b0,
    localparam MASK_SIZE = DATA_WIDTH/WR_SIZE)
(
input                                   clk,      // clock input
input                                   ds,       // deep sleep, active high
input                                   sd,       // shutdown, active high
input   [DATA_WIDTH-1:0]                din,      // write data input
input   [ADDR_MSB:ADDR_LSB]             addr,     // address for read or write
input                                   regen,    // register enable
input                                   rden,     // memory read enable
input                                   wren,     // memory write enable
input   [MASK_SIZE-1:0]                 mask,     // data write enables
output  [DATA_WIDTH-1:0]                dout      // read data output
);


`ifndef FPGA_INFER_MEMORIES   // {

// synopsys translate_off
reg     /*sparse*/ [DATA_WIDTH-1:0]     mem_r[0:MEM_SIZE-1];
reg     [ADDR_MSB:ADDR_LSB]             addr_r;
wire    [DATA_WIDTH-1:0]                dout0;
reg     [DATA_WIDTH-1:0]                dout1;
wire    [DATA_WIDTH-1:0]                dout2;
reg     [DATA_WIDTH-1:0]                dout3;

wire    [DATA_WIDTH-1:0]                bit_mask;

wire [DATA_WIDTH-1:0]                    din_i;
wire [ADDR_MSB:ADDR_LSB]                 addr_i;
wire                                     wren_i;
wire                                     rden_i;
wire [MASK_SIZE-1:0]                     mask_i;
wire                                     regen_i;

assign #0.01  din_i   = din;
assign #0.01  addr_i  = addr;
assign #0.01  wren_i  = wren;
assign #0.01  rden_i  = rden;
assign #0.01  mask_i  = mask;
assign #0.01  regen_i = regen;


// Generate a write bit mask from the write byte mask
// MSB bit of the mask is for ECC field (remaining bits)
generate
  for (genvar i=0; i<(MASK_SIZE-1); i=i+1)
    begin: bit_mask_gen
      assign bit_mask [i*WR_SIZE +: WR_SIZE] = {WR_SIZE{mask_i[i] & wren_i}};
    end
endgenerate

assign bit_mask[DATA_WIDTH-1: WR_SIZE*(MASK_SIZE-1)] = {(DATA_WIDTH-(WR_SIZE*(MASK_SIZE-1))){mask_i[MASK_SIZE-1] & wren_i}};

initial
begin: ini
  integer i;
  for (i=0; i < MEM_SIZE; i=i+1)
    mem_r[i] = {DATA_WIDTH{1'b0}};
end

assign dout0 = mem_r[addr];

always @(posedge clk)
begin
  if (rden_i)
    addr_r <= addr_i;
  if (rden_i && SYNC_OUT)
    dout1 <= dout0;
  if (regen_i && PIPELINED)
    dout3 <= dout2;  
end

generate
  for (genvar i=0; i<(DATA_WIDTH); i=i+1)
  begin: memblock
    always @(posedge clk)
    begin
      if (wren_i && bit_mask[i])
        mem_r[addr_i][i] <= din_i[i];
    end
  end
endgenerate

assign dout2 = SYNC_OUT ? dout1 : mem_r[addr_r];
assign dout = PIPELINED ? dout3 : dout2;

// synopsys translate_on

`else  // } {

wire    [DATA_WIDTH-1:0]                bit_mask;

wire [DATA_WIDTH-1:0]                    din_i;
wire [ADDR_MSB:ADDR_LSB]                 addr_i;
wire                                     wren_i;
wire                                     rden_i;
wire [MASK_SIZE-1:0]                     mask_i;

assign #0.01  din_i   = din;
assign #0.01  addr_i  = addr;
assign #0.01  wren_i  = wren;
assign #0.01  rden_i  = rden;
assign #0.01  mask_i  = mask;

// Generate a write bit mask from the write byte mask
// MSB bit of the mask is for ECC field (remaining bits)
generate
  for (genvar i=0; i<(MASK_SIZE-1); i=i+1)
    begin: bit_mask_gen
      assign bit_mask [i*WR_SIZE +: WR_SIZE] = {WR_SIZE{mask_i[i] & wren_i}};
    end
endgenerate

assign bit_mask[DATA_WIDTH-1: WR_SIZE*(MASK_SIZE-1)] = {(DATA_WIDTH-(WR_SIZE*(MASK_SIZE-1))){mask_i[MASK_SIZE-1] & wren_i}};

nl2_fpga_sram #(
    .MEM_SIZE   (MEM_SIZE),
    .ADDR_MSB   (ADDR_MSB),
    .ADDR_LSB   (ADDR_LSB),
    .PIPELINED  (1'b0),
    .DATA_WIDTH (DATA_WIDTH),
    .WR_SIZE    (1),
    .SYNC_OUT   (0),
    .RAM_STL    ("no_rw_check"))
u_scm_dbank_ram (
    .clk   (clk),
    .din   (din_i),
    .addr  (addr_i),
    .regen (1'b1),
    .rden  (rden_i),
    .wren  (bit_mask),
    .dout  (dout)
);

`endif  // }
  
endmodule // scm_dbank_sram

// leda on
// spyglass enable_block ALL
