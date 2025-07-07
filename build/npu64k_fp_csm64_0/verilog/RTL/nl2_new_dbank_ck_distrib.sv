// A dbank module consists of four sub-banks each with a 128-bit word
// size.  The read/write channel to the cluster is also 128
// bits. Access to the sub-banks is therefore staggered, such that a
// 128-bit word arriving through the write channel is immediately
// forwarded to the corresponding sub-bank. Next cycle, the next
// arriving word is written to the next sub-bank, etc. This way we
// reduce the amount of buffering as much as possible, saving
// flipflops. Note that sometimes an arriving word must wait briefly
// until the corresponding sub-bank receives its positive clock edge.
// The controller needs to wait until dbank_active_next[] indicates
// the imminent arrival of a sub-bank posedge.
//

module nl2_new_dbank_ck_distrib
  #(
    parameter N_SRAM    = 4, // legal range: {2,4}
    parameter WAIT_SIZE = 4
    )
(
input  [WAIT_SIZE-1:0] dbank_sram_waitcyc, // dbank wait cycles, 0 means no-wait, single-cycle access.
input                  dbank_clk,          // input from clock generator
input                  dbank_idle,         // dbank idle
output                 dbank_accept_en,    // Enable the write data accept
output [N_SRAM-1:0]    dbank_sram_clk,     // staggered clocks for the sub-banks
output                 dbank_ctrl_clk,     // control clock, same skew as sram_clk
output [N_SRAM-1:0]    dbank_active_next,  // high if corresponding sram_clk has upcoming posedge
input                  rst_a
);

reg [2:0] nidle_state_r;
always @(posedge dbank_clk or posedge rst_a)
  if (rst_a)
    nidle_state_r <= 3'd0;
  else
    nidle_state_r <= {nidle_state_r[1:0], ~dbank_idle};

reg [WAIT_SIZE-1:0] sram_cycle_ctr;


always @(posedge dbank_clk or posedge rst_a)
  if (rst_a)
    sram_cycle_ctr <= 'd0;
  else if (sram_cycle_ctr == dbank_sram_waitcyc)
    sram_cycle_ctr <= 'd0;
  else
    sram_cycle_ctr <= sram_cycle_ctr + 'd1;


reg [N_SRAM-1:0] clock_enable_r;

always @(posedge dbank_clk or posedge rst_a)
  if (rst_a)
    clock_enable_r <= 'b0;
  else
    // each sub-bank is activated one cycle after its neighbor is activated
    clock_enable_r <= {clock_enable_r[N_SRAM-2:0], (sram_cycle_ctr == 'd0)};


wire [N_SRAM-1:0] clock_enable_en;
assign clock_enable_en = (|nidle_state_r) ? clock_enable_r : {N_SRAM{1'b0}};


for (genvar j=0; j < N_SRAM; j++)
begin: clkgate_BLK
  nl2_cln_clkgate 
  u_cg (
        .clk_in         (dbank_clk),
        .clock_enable_r (clock_enable_en[j]),
        .clk_out        (dbank_sram_clk[j])
        );
end

reg   ctrl_active;
wire  ctrl_clk_en;
always @(posedge dbank_clk or posedge rst_a)
  if (rst_a)
    ctrl_active <= 1'b0;
  else
    // TODO: test for a non-empty dbank cmd queue:
    ctrl_active <= 1'b1;


assign ctrl_clk_en =  ctrl_active & (| nidle_state_r);
assign dbank_accept_en = ctrl_clk_en;

nl2_cln_clkgate 
  u_cg_ctl (
            .clk_in         (dbank_clk),
            .clock_enable_r (ctrl_clk_en),
            .clk_out        (dbank_ctrl_clk)
            ); 

assign dbank_active_next = clock_enable_r;

endmodule // new_dbank_ck_distrib
