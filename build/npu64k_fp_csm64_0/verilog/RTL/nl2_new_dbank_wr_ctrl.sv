`include "nl2_cln_defines.v"

module nl2_new_dbank_wr_ctrl
  #(
    parameter N_SRAM        = 4, // legal range: {2,4}
    parameter BNK_ADDR_SIZE = 10,
    parameter CMD_ID_SIZE   = 1,
    parameter BNK_DATA_SIZE = 65536, 
    parameter BNK_DATA_WIDTH= 8,
    parameter SRAM_SEL_MSB  = 7,
    parameter SRAM_SEL_LSB  = 6,
    parameter RMW_ECC_PIPE  = 1,
    parameter BLOCK_ADDR_SIZE = `nl2_SRAM_BLOCK_ADDR_SIZE,
    parameter INTERLEAVE_ADR = $clog2(`nl2_CFG_SCM_INTERLEAVE),
    // The following is immutable:
    localparam LAST_ADDR       =  BNK_DATA_SIZE/(BNK_DATA_WIDTH/8) -1
    )
(
input                   [N_SRAM-1:0] dbank_active_next,
input                   [N_SRAM-1:0] capture_dbank_next,
input                                do_wr,
input            [BNK_ADDR_SIZE-1:0] cmd_addr,
input              [CMD_ID_SIZE-1:0] cmd_id,
input                                cmd_err,
input                                wrap,
input           [`nl2_CLN_CMD_BURST_RNG] burst_size,
input            [`nl2_IBP_CMD_DATA_RNG] data_size,
input                                excl,
input                                excl_err,
output reg [N_SRAM-1:0]              target_sram,
output                               init_going,
output reg                           init_done,
input                                software_reset,
input                                init_cmd,
output reg                           wr_done,
output reg     [BLOCK_ADDR_SIZE-1:0] bnk_wr_block_addr,
output reg              [N_SRAM-1:0] bnk_wr_en,

input                                rcv_valid,
output reg                           rcv_accept,
input                                rcv_rmw_req,
output reg              [N_SRAM-1:0] bnk_rmw_rd_en,
output reg              [N_SRAM-1:0] bnk_rmw_rd_data_sel,
output                               wr_rsp_valid,
output                               wr_excl_ok,
output             [CMD_ID_SIZE-1:0] wr_id,
output                               wr_err,

input                                wr_stall,
output                               wr_idle,

input                                dbank_ctrl_clk,
input                                rst_a
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

localparam S_WCTL_SIZE = 3;
typedef enum reg [S_WCTL_SIZE-1:0] {
  S_WCTL_RESET,
  S_WCTL_INIT,
  S_WCTL_WAIT_FOR_CMD,
  S_WCTL_READ,
  S_WCTL_ENCODE,
  S_WCTL_ENCODE2,                    
  S_WCTL_BUSY_WRITE
} wctl_phase_t;

typedef struct packed {
  wctl_phase_t               phase;
  reg   [BNK_ADDR_SIZE-1:`nl2_CFG_BNK_ADR+INTERLEAVE_ADR] addr_hi;
  reg   [INTERLEAVE_ADR-1:0] addr_lo;
  reg   [INTERLEAVE_ADR-1:0] wrap_mask;
  reg   [`nl2_CLN_CMD_BURST_RNG] burst_size;
  reg                        ecc_encoded;
} wctl_state_s;

wctl_state_s wctl_state;
wctl_state_s wctl_state_next;
wire [INTERLEAVE_ADR-1:0] cmd_addr_lo = cmd_addr[INTERLEAVE_ADR-1:0];
reg  [INTERLEAVE_ADR-1:0] bnk_wr_addr;
reg  [INTERLEAVE_ADR-1:0] bnk_wr_addr_next;

wire read_modify_write;
assign read_modify_write = rcv_rmw_req;

wire [BNK_ADDR_SIZE-1:`nl2_CFG_BNK_ADR+INTERLEAVE_ADR] init_addr;
wire [BNK_ADDR_SIZE-1:`nl2_CFG_BNK_ADR+INTERLEAVE_ADR] init_addr_next;
assign init_going = (wctl_state.phase == S_WCTL_INIT) | (wctl_state.phase == S_WCTL_RESET);
assign init_addr = wctl_state.addr_hi;
assign init_addr_next = wctl_state_next.addr_hi;

always @*
begin: wctl_PROC
//  reg [N_SRAM-1:0] target_sram;
  target_sram        = {N_SRAM{1'b0}};
// spyglass disable_block Ac_conv01 Ac_conv02
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
  wr_done            = 1'b0;
  bnk_wr_en          = {N_SRAM{1'b0}};
// spyglass enable_block Ac_conv01 Ac_conv02
  bnk_rmw_rd_en      = {N_SRAM{1'b0}};
  bnk_rmw_rd_data_sel = {N_SRAM{1'b0}};
  init_done          = 1'b0;
  rcv_accept         = 1'b0;
  wctl_state_next    = wctl_state;
  bnk_wr_addr = wctl_state.addr_lo;

  case (wctl_state.phase)
    S_WCTL_RESET:
      begin
        if (do_wr)
        begin
          if (cmd_addr[0]==1'b0) // start sram init process
          begin
            wctl_state_next.phase = S_WCTL_INIT;
            wctl_state_next.addr_hi = 0;
            wctl_state_next.addr_lo = 0;
          end
          else begin // this is a software reset
            wctl_state_next = '{phase:S_WCTL_WAIT_FOR_CMD, default:0};
            init_done      = 1'b1;
            wr_done        = 1'b1;
          end
        end
        else if (software_reset)
        begin // this is a software reset
          wctl_state_next = '{phase:S_WCTL_WAIT_FOR_CMD, default:0};
          init_done      = 1'b1;
          wr_done        = 1'b1;
        end
      end
    S_WCTL_INIT:
      begin
        target_sram = sram_select(wctl_state.addr_lo);
        if (|{target_sram & dbank_active_next})
        begin
          bnk_wr_en = target_sram;
          if ( {wctl_state.addr_hi,wctl_state_next.addr_lo[INTERLEAVE_ADR-1:$clog2(BNK_DATA_WIDTH/8)]} == LAST_ADDR )
          begin
            wctl_state_next = '{phase:S_WCTL_WAIT_FOR_CMD, default:0};
            init_done      = 1'b1;
            wr_done        = 1'b1;
          end
          else
          begin
            {wctl_state_next.addr_hi,wctl_state_next.addr_lo[INTERLEAVE_ADR-1:$clog2(BNK_DATA_WIDTH/8)]} = {wctl_state_next.addr_hi,wctl_state_next.addr_lo[INTERLEAVE_ADR-1:$clog2(BNK_DATA_WIDTH/8)]} + 'b1;
          end
        end
      end
    S_WCTL_WAIT_FOR_CMD:
      begin
        bnk_wr_addr = cmd_addr_lo;
        if (do_wr && init_cmd ) begin
          // Memory initialization
          wctl_state_next = '{phase:S_WCTL_RESET, default:0};
        end
        else 
        if (do_wr)
        begin
          if (wrap)
            wctl_state_next.wrap_mask = ((1 + burst_size) << data_size) - 1;
          else
            wctl_state_next.wrap_mask = {INTERLEAVE_ADR{1'b1}};

          target_sram = sram_select(cmd_addr_lo);
          if (rcv_valid & |{target_sram & dbank_active_next} & !wr_stall)
          begin
//          if (read_modify_write && !excl)
            if (read_modify_write)
            begin
              bnk_rmw_rd_en = target_sram;
              wctl_state_next.burst_size = burst_size;
              wctl_state_next.addr_lo = cmd_addr_lo;
              wctl_state_next.phase = S_WCTL_READ;
            end
            else
            begin
              rcv_accept = 1'b1;
//            bnk_wr_en = target_sram & {N_SRAM{!excl}};
              bnk_wr_en = target_sram;
              if (burst_size == 0)
              begin
                wr_done = 1'b1;
                wctl_state_next = '{phase:S_WCTL_WAIT_FOR_CMD, default:0};
              end
              else
              begin
                wctl_state_next.burst_size = burst_size - 1;
                wctl_state_next.addr_lo = step(cmd_addr_lo, data_size, wctl_state_next.wrap_mask);
                wctl_state_next.phase = S_WCTL_BUSY_WRITE;
              end
            end
          end
          else
          begin
            wctl_state_next.burst_size = burst_size;
            wctl_state_next.addr_lo = cmd_addr_lo;
            wctl_state_next.phase = S_WCTL_BUSY_WRITE;
          end
        end
      end

    S_WCTL_BUSY_WRITE:
      begin
        target_sram = sram_select(wctl_state.addr_lo);
        if (rcv_valid & |{target_sram & dbank_active_next} & !wr_stall)
        begin
          wctl_state_next.ecc_encoded = 1'b0;
//        if (read_modify_write && !wctl_state.ecc_encoded && !excl)
          if (read_modify_write && !wctl_state.ecc_encoded)
          begin
            bnk_rmw_rd_en = target_sram;
            wctl_state_next.phase = S_WCTL_READ;
          end
          else
          begin
            rcv_accept = 1'b1;
//          bnk_wr_en = target_sram & {N_SRAM{!excl}};
            bnk_wr_en = target_sram ;
            if (wctl_state.burst_size == 0)
            begin
              wr_done = 1'b1;
              wctl_state_next = '{phase:S_WCTL_WAIT_FOR_CMD, default:0};
            end
            else
            begin
              wctl_state_next.burst_size = wctl_state.burst_size - 1;
              wctl_state_next.addr_lo = step(wctl_state.addr_lo, data_size, wctl_state_next.wrap_mask);
            end
          end
        end
      end
    S_WCTL_READ:
      begin
        target_sram = sram_select(wctl_state.addr_lo);
        if (|{target_sram & capture_dbank_next}) begin
          bnk_rmw_rd_data_sel = target_sram;
          wctl_state_next.phase = S_WCTL_ENCODE;
        end
      end
    S_WCTL_ENCODE:
      begin
        // First cycle for ECC encoding
        if ( RMW_ECC_PIPE == 1 )
          wctl_state_next.phase = S_WCTL_ENCODE2;
        else begin
          wctl_state_next.phase = S_WCTL_BUSY_WRITE;
          wctl_state_next.ecc_encoded = 1'b1;
        end
      end
    S_WCTL_ENCODE2:
      begin
        // Second cycle for ECC encoding
        wctl_state_next.phase = S_WCTL_BUSY_WRITE;
        wctl_state_next.ecc_encoded = 1'b1;
      end

  endcase
end

always @(posedge dbank_ctrl_clk or posedge rst_a)
begin: wctl_reg_PROC
  if (rst_a)
  begin
    wctl_state <= '{phase:S_WCTL_RESET, default:0};
  end
  else
  begin
// spyglass disable_block Ac_unsync01 Ac_unsync02 Ac_glitch04
// SMD: Unsynchronized Crossing
// SJ:  static 
    wctl_state <= wctl_state_next;
// spyglass enable_block Ac_unsync01 Ac_unsync02 Ac_glitch04
  end
end

// The lower address bits are used for:
//   - least significant BNK_DATA_WIDTH byte(s) (use wr_mask instead)
//   - Sub-bank SRAM select
// The position of bank select bits is determined by CFG_SCM_INTERLEAVE, and they
// are not part of the block_addr (because they are always constant within a bank):
if (`nl2_CFG_SCM_INTERLEAVE == N_SRAM * BNK_DATA_WIDTH/8)
begin: block_addr_simple_ASGN
  assign bnk_wr_block_addr =
                      init_going ? init_addr :
                      cmd_addr[BNK_ADDR_SIZE-1 : `nl2_CFG_BNK_ADR+INTERLEAVE_ADR];
end
else
begin: block_addr_complex_ASGN
  assign bnk_wr_block_addr
    = {(
        init_going ? init_addr :
       cmd_addr[BNK_ADDR_SIZE-1 :`nl2_CFG_BNK_ADR+INTERLEAVE_ADR])
      ,bnk_wr_addr[INTERLEAVE_ADR-1:($clog2(N_SRAM)+ $clog2(BNK_DATA_WIDTH/8))]
      };
end

assign bnk_wr_addr_next  =  wctl_state_next.addr_lo;


wire              fifo_full;
wire              fifo_sram_done;
wire [N_SRAM-1:0] fifo_sram; // 1-hot id of the next SRAM that must deliver its read data.
wire              bnk_wr_last;
wire              fifo_push;
wire              fifo_pop;
wire              wr_excl;
assign fifo_push = rcv_accept;
//assign fifo_pop  = fifo_sram_done & | {fifo_sram & dbank_active_next}; 
assign fifo_pop  = fifo_sram_done & (|{fifo_sram & capture_dbank_next} | wr_excl); 
assign wr_rsp_valid = bnk_wr_last & fifo_pop;

nl2_cln_fifo
  #(.WIDTH (N_SRAM+4+CMD_ID_SIZE),
    .DEPTH (N_SRAM))
u_fifo
(
.fifo_full       (fifo_full), // Never will be true when DEPTH > N_SRAM
.fifo_head_valid (fifo_sram_done),
.fifo_head_data  ({fifo_sram,bnk_wr_last,wr_excl,wr_excl_ok,wr_id,wr_err}),
.fifo_in         ({bnk_wr_en,wr_done,excl,(excl & !excl_err),cmd_id,cmd_err}),
.push            (fifo_push),
.pop             (fifo_pop),
.clk             (dbank_ctrl_clk),
.rst_a           (rst_a)
);

assign wr_idle = !fifo_sram_done;



endmodule // dbank_wr_ctrl
