`include "nl2_cln_defines.v"

// -----------------------------------------------------------------------------
// Scrubbing control module is capturing information about the scrubbing 
// command: bank selection and address. One of the requirement for
// processing the scrubbing is to have the write data register containing 
// the scrubbing data. When the scrubbing command is captured and scrubbing 
// data is ready, the scrubbing process will be enabled when the targeted
// dbank is enabled.
//
// Inputs:
//
// req_scrub          : Requested scrubbing
// req_bnk            : Requested scrubbing bank selection
// req_addr           : Requested scrubbing bank address
// req_data_rcv       : Write data register contain scrubbing data
// dbank_active_next  : Next dbank active
//
// Outputs:
// 
// req_ack            : Acknowledge that the scrubbing command has been captured
// scrub_proc         : Scrubbing in process (should last 1 cycle)
// scrub_bnk          : Scrubbing bank selection
// scrub_addr         : Scrubbing bank address
//
// -----------------------------------------------------------------------------

module nl2_new_dbank_scrub_ctl
  #(
    parameter N_SRAM    = 4,  // legal range: {2,4}
    parameter BLOCK_ADDR_SIZE = `nl2_SRAM_BLOCK_ADDR_SIZE
    )
(
// Request interface for scrubbing
input                            req_scrub,      
output                           req_ack,      
input               [N_SRAM-1:0] req_bnk,     
input      [BLOCK_ADDR_SIZE-1:0] req_addr, 
input                            req_data_rcv,   

input               [N_SRAM-1:0] dbank_active_next,

// Output interface 
output reg                       scrub_pending,
output reg                       scrub_proc,
output reg          [N_SRAM-1:0] scrub_bnk,
output reg [BLOCK_ADDR_SIZE-1:0] scrub_addr,

input                            clk,
input                            rst_a
);


// State of the capture register (1 = active, 0 = idle)
logic                            scrub_en;
  

// Scrubbing is enabled if the following conditions are all met
// 1. Scrubbing command has been captured
// 2. Write data register contains scrubbing data
// 3. Next dbank enabled is matching the
// Scrubbing process should last 1 cycle per scrubbing command
assign scrub_proc   = scrub_en & req_data_rcv & ( |(scrub_bnk & dbank_active_next)) ; 

// Acknowledge that scrubbing request has been captured.
assign req_ack = req_scrub & (~scrub_en | scrub_proc) ;


always @(posedge clk or posedge rst_a)
begin : scrub_reg_PROC
  if (rst_a) begin
    scrub_en    <=  'b0 ;
    scrub_bnk   <=  'b0 ;
    scrub_addr  <=  'b0 ;
  end 
  else begin
    // Capture the scrubing bank and address
    if ( req_ack ) begin
      // Scrubbing request received
      scrub_en    <= 1'b1 ;
      scrub_bnk   <= req_bnk ;
      scrub_addr  <= req_addr;
    end
    else if (scrub_proc) begin
      // No new scrubbing request
      scrub_en    <= 1'b0 ;
      scrub_bnk   <=  'b0 ;
    end

  end // else: !if(rst_a)

end // block: scrub_reg_PROC



assign scrub_pending = scrub_en;



endmodule // new_dbank_scrub_ctl

