`include "nl2_cln_defines.v"

//////////////////////////////////////////////////////////////////////////////
// DBANK_RD_CTRL
//////////////////////////////////////////////////////////////////////////////

module nl2_new_dbank_rd_ctrl
  #(
    parameter N_SRAM        = 4,   // legal range: {2,4}
    parameter BNK_ADDR_SIZE = 10,
    parameter CMD_ID_SIZE   = 1,
    parameter BNK_DATA_WIDTH= 8,
    parameter SRAM_SEL_MSB  = 7,
    parameter SRAM_SEL_LSB  = 6,
    parameter BLOCK_ADDR_SIZE = `nl2_SRAM_BLOCK_ADDR_SIZE,
    parameter INTERLEAVE_ADR = $clog2(`nl2_CFG_SCM_INTERLEAVE)
    )
(
input                [N_SRAM-1:0]    dbank_active_next,
input                [N_SRAM-1:0]    capture_dbank_next,
input                                do_rd,
input            [BNK_ADDR_SIZE-1:0] cmd_addr,
input              [CMD_ID_SIZE-1:0] cmd_id,
input                                wrap,
input           [`nl2_CLN_CMD_BURST_RNG] burst_size,
input            [`nl2_IBP_CMD_DATA_RNG] data_size,
input                                excl,
input                                cmd_tag_err,

output reg [N_SRAM-1:0]              target_sram,
output reg                           rd_done,
output reg     [BLOCK_ADDR_SIZE-1:0] bnk_rd_block_addr,
output reg              [N_SRAM-1:0] bnk_rd_en,
output                               bnk_rd_last,
output                  [N_SRAM-1:0] bnk_rd_data_sel,
output         [BLOCK_ADDR_SIZE-1:0] bnk_rd_data_block_addr,
output                               bnk_rd_data_ecc_en,
input                                ecc_enable,

output reg                           snd_valid,
output                               rd_excl_ok,
output                               rd_tag_err,
output             [CMD_ID_SIZE-1:0] rd_id,

input                                rd_stall,
output                               rd_idle,

input                                dbank_ctrl_clk,
input                                rst_a
);


// When we start an SRAM read, we push its id on a fifo.  When the
// source synchronous channel is ready to accept data, and when the
// SRAM at the head of the fifo is ready (i.e. after waiting the
// prescribed number of wait cycles), then the data from the SRAM at
// the head of the fifo is forwarded to the source synchronous
// channel.
//
wire              fifo_full;
wire              fifo_sram_valid;
wire [N_SRAM-1:0] fifo_sram; // 1-hot id of the next SRAM that must deliver its read data.
reg               fifo_push;
reg               fifo_pop;

nl2_cln_fifo
  #(.WIDTH (N_SRAM+3+CMD_ID_SIZE
           +BLOCK_ADDR_SIZE+1
  ),
    .DEPTH (N_SRAM))
u_fifo
(
.fifo_full       (fifo_full), // Never will be true when DEPTH > N_SRAM
.fifo_head_valid (fifo_sram_valid),
.fifo_head_data  ({fifo_sram
                  ,bnk_rd_data_block_addr
                  ,bnk_rd_data_ecc_en
                  ,rd_tag_err
                  ,rd_excl_ok
                  ,rd_id
                  ,bnk_rd_last}),
.fifo_in         ({bnk_rd_en
                  ,bnk_rd_block_addr
                  ,ecc_enable
                  ,cmd_tag_err
                  ,excl
                  ,cmd_id
                  ,rd_done}),
.push            (fifo_push),
.pop             (fifo_pop),
.clk             (dbank_ctrl_clk),
.rst_a           (rst_a)
);

// Compute the address that comes next:
function automatic [INTERLEAVE_ADR-1:0] step
  (input [INTERLEAVE_ADR-1:0] addr,
   input [`nl2_IBP_CMD_DATA_RNG]  data_size,
   input [INTERLEAVE_ADR-1:0] wrap_mask);
  begin
    reg [BNK_ADDR_SIZE-1:0] nbytes;
// spyglass disable_block W486
// SMD: Rhs width with shift is more than lhs width
// SJ:  overflow will not happen
    nbytes = $unsigned(1) << data_size;
// spyglass enable_block W486
    step = (~wrap_mask & addr)
         | ( wrap_mask & ((addr + nbytes) & ~(nbytes - 1)));
  end
endfunction // step

// Make a 1-hot bank select vector out of a bank address:
function automatic [N_SRAM-1:0] sram_select
  (input [INTERLEAVE_ADR-1:0] addr);
  begin
    reg [SRAM_SEL_MSB - SRAM_SEL_LSB:0] bank_id;
    bank_id = addr[SRAM_SEL_MSB:SRAM_SEL_LSB];
// spyglass disable_block W486
// SMD: Rhs width with shift is more than lhs width
// SJ:  overflow will not happen
    sram_select = $unsigned(1) << bank_id;
// spyglass enable_block W486
  end
endfunction // sram_select

localparam S_RCTL_SIZE = 1;
typedef enum reg [S_RCTL_SIZE-1:0] {
  S_RCTL_WAIT = 1'b0,
  S_RCTL_BUSY = 1'b1
} rctl_phase_t;

typedef struct packed {
  rctl_phase_t               phase;
  reg   [INTERLEAVE_ADR-1:0] addr;
  reg   [INTERLEAVE_ADR-1:0] wrap_mask;
  reg   [`nl2_CLN_CMD_BURST_RNG] burst_size;
} rctl_state_s;

rctl_state_s rctl_state;
rctl_state_s rctl_state_next;
wire [INTERLEAVE_ADR-1:0] cmd_addr_lo = cmd_addr[INTERLEAVE_ADR-1:0];
reg  [INTERLEAVE_ADR-1:0] bnk_rd_addr;

reg [N_SRAM-1:0] sram_available;
// reg [N_SRAM-1:0] target_sram;

always @*
begin: rctl_PROC
  reg sram_ready;
  target_sram     = {N_SRAM{1'b0}};
  sram_ready      = 1'b0;
// spyglass disable_block Ac_conv01
// SMD: Unsynchronized Crossing
// SJ:  static 
  rd_done         = 1'b0;
// spyglass enable_block Ac_conv01
  bnk_rd_en       = {N_SRAM{1'b0}};
  fifo_push       = 1'b0;
  rctl_state_next = rctl_state;
  bnk_rd_addr     = rctl_state.addr;

  case (rctl_state.phase)
    S_RCTL_WAIT:
      begin
        bnk_rd_addr = cmd_addr_lo;
        if (do_rd)
        begin
          if (wrap)
            rctl_state_next.wrap_mask = ((1 + burst_size) << data_size) - 1;
          else
            rctl_state_next.wrap_mask = {INTERLEAVE_ADR{1'b1}};
          target_sram = sram_select(cmd_addr_lo);
          sram_ready = |{target_sram & dbank_active_next & sram_available};
          if (sram_ready && !rd_stall)
          begin
            bnk_rd_en = target_sram;
            fifo_push = 1'b1;
            if (burst_size == 0)
            begin
              rd_done = 1'b1;
              rctl_state_next = '{phase:S_RCTL_WAIT, default:0};
            end
            else
            begin
              rctl_state_next.burst_size = burst_size - 1;
              rctl_state_next.addr = step(cmd_addr_lo, data_size, rctl_state_next.wrap_mask);
              rctl_state_next.phase = S_RCTL_BUSY;
            end
          end
          else
          begin
            rctl_state_next.burst_size = burst_size;
            rctl_state_next.addr = cmd_addr_lo;
            rctl_state_next.phase = S_RCTL_BUSY;
          end
        end
      end

    S_RCTL_BUSY:
      begin
        target_sram = sram_select(rctl_state.addr);
        sram_ready = |{target_sram & dbank_active_next & sram_available};
        if (sram_ready && !rd_stall)
        begin
          bnk_rd_en = target_sram;
          fifo_push = 1;
          if (rctl_state.burst_size == 0)
          begin
            rd_done = 1'b1;
            rctl_state_next = '{phase:S_RCTL_WAIT, default:0};
          end
          else
          begin
            rctl_state_next.burst_size = rctl_state.burst_size - 1;
            rctl_state_next.addr = step(rctl_state.addr, data_size, rctl_state.wrap_mask);
          end
        end
      end
  endcase
end

always @(posedge dbank_ctrl_clk or posedge rst_a)
begin: rctl_reg_PROC
  if (rst_a)
  begin
    rctl_state   <= '{phase:S_RCTL_WAIT, default:0};
  end
  else
  begin
// spyglass disable_block Ac_unsync02 Ac_glitch04
// SMD: Unsynchronized Crossing
// SJ:  static
    rctl_state   <= rctl_state_next;
// spyglass enable_block Ac_unsync02 Ac_glitch04
  end
end

// Keep track of pending reads in the SRAMs:
reg [N_SRAM-1:0] sram_busy_r;
reg [N_SRAM-1:0] sram_busy_next;
reg [N_SRAM-1:0] sram_rd_done;

always @*
begin
  sram_busy_next = sram_busy_r;
  sram_rd_done = {N_SRAM{1'b0}}; 
  if (fifo_pop)
  begin
    sram_rd_done = fifo_sram;
    sram_busy_next = sram_busy_next & ~sram_rd_done;
  end
  if (fifo_push)
    sram_busy_next = sram_busy_next | target_sram;
end

always @(posedge dbank_ctrl_clk or posedge rst_a)
begin
  if (rst_a)
    sram_busy_r <= {N_SRAM{1'b0}};
  else
// spyglass disable_block Ac_unsync02 Ac_glitch04
// SMD: Unsynchronized Crossing
// SJ:  static
    sram_busy_r <= sram_busy_next;
// spyglass enable_block Ac_unsync02 Ac_glitch04
end

assign sram_available = ~sram_busy_r | sram_rd_done;

// Send SRAM read data to the source synchronous read channel.
always @*
begin
  snd_valid  = 1'b0;
  fifo_pop   = 1'b0;
  if (fifo_sram_valid)
  begin
    // Oldest pending SRAM read is ready to send ?
    snd_valid = |{fifo_sram & capture_dbank_next};
    if (snd_valid)
    begin
      fifo_pop = 1'b1;
    end
  end
end // always @ *

// Return zeros when it is not used
assign bnk_rd_data_sel = fifo_pop ? fifo_sram : 'b0;

// The lower address bits are used for:
//   - least significant BNK_DATA_WIDTH byte(s) (use wr_mask instead)
//   - Sub-bank SRAM select
// The position of bank select bits is determined by CFG_SCM_INTERLEAVE, and they
// are not part of the block_addr (because they are always constant within a bank):
if (`nl2_CFG_SCM_INTERLEAVE == N_SRAM * BNK_DATA_WIDTH/8)
begin: block_addr_simple_ASGN
  assign bnk_rd_block_addr =
                      cmd_addr[BNK_ADDR_SIZE-1 : `nl2_CFG_BNK_ADR+INTERLEAVE_ADR];
end
else
begin: block_addr_complex_ASGN
  assign bnk_rd_block_addr
    = {(
       cmd_addr[BNK_ADDR_SIZE-1 :`nl2_CFG_BNK_ADR+INTERLEAVE_ADR])
      ,bnk_rd_addr[INTERLEAVE_ADR-1:($clog2(N_SRAM)+ $clog2(BNK_DATA_WIDTH/8))]
      };
end

// Shared memory always supports exclusive access, so responds with rd_excl_ok
assign  rd_idle = !fifo_sram_valid;



endmodule // dbank_rd_ctrl
