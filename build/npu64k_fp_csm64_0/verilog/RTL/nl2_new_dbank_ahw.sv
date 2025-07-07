`include "nl2_cln_defines.v"

// -----------------------------------------------------------------------------
// Address History Window
//
// This module is capturing address and banks of the previous write accesses. If 
// there is a valid scrubbing request, it provides its bank selection and 
// address. Then, all the write acccess contained in the history is checked for 
// a match. If there is a write that matches the scrubbing bank and address, 
// then the scrubbing is canceled. There is an extra register on write data
// pipeline that needs to be checked for an address match.
//
// Inputs:
//
// bnk_wr             : Write bank selection      
// bnk_addr           : Write address
// scrub_bnk          : Scrubbing bank selection
// scrub_addr         : Scrubbing address
//
// Outputs:
// 
// scrub_cancel       : Scrubbing should be canceled
//
// -----------------------------------------------------------------------------

module nl2_new_dbank_ahw
  #(
    parameter N_SRAM     = 4,  // legal range: {2,4}
    parameter HIST_DEPTH = 2,  // History Depth
    parameter BLOCK_ADDR_SIZE = `nl2_SRAM_BLOCK_ADDR_SIZE
    )
(
 // Write transaction on memory interface
 input                       shift_en,
 input [N_SRAM-1:0]          bnk_wr,
 input [BLOCK_ADDR_SIZE-1:0] bnk_addr, 

 // Scrubbing bank and address
 input [N_SRAM-1:0]          scrub_bnk,
 input [BLOCK_ADDR_SIZE-1:0] scrub_addr,

 output reg                  scrub_cancel,

 input                       clk,
 input                       rst_a

 );


typedef struct packed {
  logic [N_SRAM-1:0]             bnk;
  logic [BLOCK_ADDR_SIZE-1:0]    addr;
} ahw_s;


ahw_s                         history [HIST_DEPTH-1:0];
logic [HIST_DEPTH-1:0]        match;

always @(posedge clk or posedge rst_a)
begin : history_reg_PROC
  if (rst_a) begin
    for (int i = 0; i < HIST_DEPTH; i = i + 1) begin
      history[i] <= 'b0 ;
    end
  end
  else begin

    if (shift_en) begin
      // Capture the incoming write transaction
      history[0].bnk   <=  bnk_wr;
      history[0].addr  <=  bnk_addr;

      // Shift the history on every cycle
      for (int i = 1; i < HIST_DEPTH; i = i + 1) begin
        history[i] <= history[i-1];
      end
    end

  end
end // block: history_reg_PROC


// Check all the address history window for matches
for (genvar x = 0; x < HIST_DEPTH; x = x + 1) 
begin: match_PROC
  assign match[x] = (scrub_bnk  == history[x].bnk ) &&
                    (scrub_addr == history[x].addr);
end



// Cancel the scrubbing request
always_comb 
begin : cancel_PROC
  
  scrub_cancel = (| match) ;

end // block: cancel_PROC



endmodule // new_dbank_ahw
