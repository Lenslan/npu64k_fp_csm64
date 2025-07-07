`include "nl2_cln_defines.v"

module nl2_new_dbank_top
  #(
    parameter CMD_ID_SIZE      = 1,   // legal range: >= 1
    parameter WR_ID_SIZE       = 1,
    parameter N_SRAM           = 4, // legal range: {2,4}
    parameter BNK_DATA_SIZE    = 65536, 
    parameter BNK_ADDR_SIZE    = 10,
    parameter BNK_DATA_WIDTH   = 8, // legal range: >= 8, and power of 2
    parameter BLOCK_ADDR_SIZE = `nl2_SRAM_BLOCK_ADDR_SIZE,
    parameter INTERLEAVE_ADR  = $clog2(`nl2_CFG_SCM_INTERLEAVE),
    parameter BNK_ECC_WIDTH    = 0,
    parameter RMW_ECC_PIPE     = 1,
    parameter WAIT_SIZE        = 4, // legal range: >= 1
    parameter CTRL_CHANNELS    = 0,
    //
    // The following parameters are derived and immutable:
    //
    localparam BNK_RAW_WIDTH   = BNK_DATA_WIDTH + BNK_ECC_WIDTH,
    localparam BNK_NUM_NARROW  = `nl2_DBANK_NUM_NARROW,
    localparam BNK_MASK_WIDTH_NARROW  = BNK_DATA_WIDTH/ (8 * BNK_NUM_NARROW),
    localparam BNK_MASK_WIDTH  = BNK_DATA_WIDTH/8,
    localparam BNK_RAW_MASK_WIDTH_NARROW  = `nl2_DBANK_MASK_WIDTH_NARROW,
    localparam BNK_RAW_MASK_WIDTH  = BNK_NUM_NARROW * BNK_RAW_MASK_WIDTH_NARROW,
    localparam BNK_ECC_ENABLE  = 1,
    // Extra bits
    // 1. Memory intialization
    // 2. scrub_enable   
    // 3. ecc_error
    // 4. wrap
    // 5. read
    // 6. excl
    // 7. excl_err
    localparam BNK_CMD_FW_SIZE = BNK_ADDR_SIZE + `nl2_CLN_CMD_BURST_SIZE + CMD_ID_SIZE + BNK_ECC_ENABLE + `nl2_IBP_CMD_DATA_SIZE + 7,
    localparam BNK_RD_FW_SIZE  = 5 + BNK_DATA_WIDTH + CMD_ID_SIZE, // {cmd_id, rd_ecc_dbe, rd_ecc_sbe,rd_last,rd_excl_ok,rd_data}
    localparam BNK_WR_FW_SIZE  = BNK_DATA_WIDTH/8 + BNK_DATA_WIDTH,
    localparam BNK_WRSP_FW_SIZE = WR_ID_SIZE + 3, //{last, cmd_id, dbe, sbe/excl_ok}
    // Need to match the round-trip latency of the read path
    // Add an extra entry for non-ECC dbank
    localparam RD_FIFO_DEPTH    = N_SRAM + 2,
    localparam SCRUB_FIFO_DEPTH = 1, // Depth of the Scrubbing FIFO
    localparam SRAM_SEL_LSB    = $clog2(BNK_DATA_WIDTH/8),
    localparam SRAM_SEL_MSB    = SRAM_SEL_LSB + $clog2(N_SRAM) - 1
    )
(
input                 [WAIT_SIZE-1:0] dbank_sram_waitcyc,
output                   [N_SRAM-1:0] dbank_sram_clk,
// SRAM interface:
output          [BLOCK_ADDR_SIZE-1:0] block_addr,
output                   [N_SRAM-1:0] bnk_rd_en,
input             [BNK_RAW_WIDTH-1:0] bnk_rd_data[N_SRAM-1:0],
output                   [N_SRAM-1:0] bnk_wr_en,
output            [BNK_RAW_WIDTH-1:0] bnk_wr_data,
output [BNK_RAW_MASK_WIDTH_NARROW-1:0] bnk_wr_mask[BNK_NUM_NARROW-1:0],
// Bank command channel from dbank_bottom:
input                                 phy_bnk_cmd_valid[2],
input           [BNK_CMD_FW_SIZE-1:0] phy_bnk_cmd_data[2],
output                                phy_bnk_cmd_accept[2],

// Bank write data channel from dbank_bottom:
input                                 phy_bnk_wr_valid[1+CTRL_CHANNELS],
input            [BNK_WR_FW_SIZE-1:0] phy_bnk_wr_data[1+CTRL_CHANNELS],
output      logic                     phy_bnk_wr_accept[1+CTRL_CHANNELS],
// Bank read data channel to dbank_bottom:
output                                phy_bnk_rd_valid[1+CTRL_CHANNELS],
output           [BNK_RD_FW_SIZE-1:0] phy_bnk_rd_data[1+CTRL_CHANNELS],
input                                 phy_bnk_rd_accept[1+CTRL_CHANNELS],
// Bank write response channel to dbank_bottom:
output                                phy_bnk_rsp_valid,
output         [BNK_WRSP_FW_SIZE-1:0] phy_bnk_rsp_data,
input                                 phy_bnk_rsp_accept,
output logic                          mem_dbnk_sbe_err,
output logic                          mem_dbnk_dbe_err,
// Misc:
input                                 software_reset,
output                                dbank_idle,
input                                 dbank_clk,
input                                 rst_a
);

   
// These values can be swapped as required.
// It is only used for readability
typedef enum logic {
   RD = 0,
   WR = 1
} chan_t;

   
// spyglass disable_block W401
// SMD: clock is internally generated and used
// SJ:  intended and causes no issues
wire                          dbank_ctrl_clk;
// spyglass enable_block W401
wire                          dbank_accept_en;
wire             [N_SRAM-1:0] src_dbank_active_next;
wire             [N_SRAM-1:0] dbank_active_next[2];
wire             [N_SRAM-1:0] capture_dbank_next[2];
   
wire                          do_rd;
wire                          do_wr;

wire                          cmd_init[2];
wire                          cmd_err[2];
wire                          cmd_ecc_enable[2];
wire                          cmd_scrub_enable[2];
wire                          excl_err[2];
wire    [CMD_ID_SIZE-1:0]     cmd_id[2];
wire    [CMD_ID_SIZE-1:0]     wr_id;
wire    [CMD_ID_SIZE-1:0]     bnk_rd_id;

wire                          do_scrub;
wire                          scrub_pending;
wire                          bnk_scrub_proc;
wire [N_SRAM-1:0]             bnk_scrub_wr_en;
wire [BLOCK_ADDR_SIZE-1:0]    bnk_scrub_addr;
wire                          scrub_ack;
wire                          scrub_data_rdy;
wire                          scrub_ctl_valid;
wire                          bnk_out_scrub_req;
wire [N_SRAM-1:0]             bnk_out_sram_sel;
wire [BLOCK_ADDR_SIZE-1:0]    bnk_out_block_addr;

wire      [BNK_ADDR_SIZE-1:0] cmd_addr[2];
wire     [`nl2_CLN_CMD_BURST_RNG] burst_size[2];
wire      [`nl2_IBP_CMD_DATA_RNG] data_size[2];
wire                          read[2];
wire                          wrap[2];
wire                          excl[2];
   
wire                          rd_done;
wire                          wr_done;

wire                          bnk_rd_last;
wire             [N_SRAM-1:0] bnk_rd_data_sel;
wire    [BLOCK_ADDR_SIZE-1:0] bnk_rd_data_block_addr;
wire                          bnk_rd_data_ecc_en;
wire                          bnk_rd_excl_ok;
wire                          bnk_rd_tag_err;
   
wire                          bnk_wr_rmw_req;
wire      [N_SRAM-1:0]        bnk_rmw_rd_en;
wire      [N_SRAM-1:0]        bnk_rmw_rd_data_sel;
wire      [BNK_RAW_WIDTH-1:0] bnk_wr_data_raw;
wire [BNK_RAW_MASK_WIDTH_NARROW-1:0] bnk_wr_mask_raw[BNK_NUM_NARROW-1:0];
wire      [N_SRAM-1:0]        bnk_wr_en_raw;
wire      [N_SRAM-1:0]        bnk_rd_en_raw;
reg       [BNK_RAW_WIDTH-1:0] incoming_rd_data;
wire                          wr_ctrl_rcv_valid;
wire                          wr_ctrl_rcv_accept;
wire                          wr_ctrl_rcv_rmw_req;
wire                          rd_ctrl_snd_valid;

wire                          bnk_out_accept;
wire                          bnk_out_valid;
wire                          bnk_out_last;
wire                          bnk_out_err;
wire                          bnk_out_rmw;
wire                          bnk_out_sbe;
wire                          bnk_out_dbe;
wire                          bnk_out_excl_ok;
wire     [BNK_DATA_WIDTH-1:0] bnk_out_rdata;
wire        [CMD_ID_SIZE-1:0] bnk_out_rid;

wire                          bnk_rmw_dbe;
wire                          bnk_rmw_sbe;

wire                          wdata_in_ecc_en;
wire                          wdata_in_valid;
wire                          wdata_in_accept;
wire     [BNK_MASK_WIDTH-1:0] wdata_in_mask;
wire     [BNK_DATA_WIDTH-1:0] wdata_in_data;
wire    [BLOCK_ADDR_SIZE-1:0] wdata_in_block_addr;


wire                          rd_stall;
wire                          wr_stall;
wire                          wr_excl_ok;
wire                          wr_rsp_valid;
wire                          wr_err;
wire                          rd_idle;
wire                          wr_idle;
wire                          buf_idle;

wire                          init_going;
wire                          init_done;

typedef struct packed {
  logic     [CMD_ID_SIZE-1:0]    rid;
  logic                          dbe;
  logic                          sbe;
  logic                          last;
  logic                          err;
  logic                          excl_ok;
  logic     [BNK_DATA_WIDTH-1:0] rdata;
} rd_fifo_s;


wire [N_SRAM-1:0]             target_sram [2];
   

   
wire        rd_fifo_full;
wire        rd_fifo_valid;
rd_fifo_s   rd_fifo_out;
rd_fifo_s   rd_fifo_in;
wire        rd_fifo_push;
wire        rd_fifo_pop;


wire        rsp_fifo_full;
wire        bnk_rsp_valid;
wire  [BNK_WRSP_FW_SIZE-1:0] bnk_rsp_out;

logic                      phy_bnk_cmd_valid_l1cg[2];
logic                      phy_bnk_cmd_accept_raw[2];
logic                      phy_bnk_wr_valid_l1cg[1+CTRL_CHANNELS];
logic                      phy_bnk_wr_accept_raw[1+CTRL_CHANNELS];

  assign  phy_bnk_cmd_valid_l1cg [WR]   = phy_bnk_cmd_valid  [WR];
  assign  phy_bnk_cmd_valid_l1cg [RD]   = phy_bnk_cmd_valid  [RD];
  assign  phy_bnk_cmd_accept [WR]       = phy_bnk_cmd_accept_raw [WR];
  assign  phy_bnk_cmd_accept [RD]       = phy_bnk_cmd_accept_raw [RD];   
  assign  phy_bnk_wr_valid_l1cg         = phy_bnk_wr_valid;
  assign  phy_bnk_wr_accept             = phy_bnk_wr_accept_raw;


/////////////////////////////////////////////////////////////////////////////////
// Clock Distributer: derive SRAM clocks from dbank_clk:
/////////////////////////////////////////////////////////////////////////////////

nl2_new_dbank_ck_distrib
  #(.N_SRAM    (N_SRAM),
    .WAIT_SIZE (WAIT_SIZE))
u_dbank_ck_distrib
(
.dbank_sram_waitcyc   (dbank_sram_waitcyc),
.dbank_idle           (dbank_idle),
.dbank_clk            (dbank_clk),
.dbank_accept_en      (dbank_accept_en),
.dbank_sram_clk       (dbank_sram_clk),
.dbank_ctrl_clk       (dbank_ctrl_clk),
.dbank_active_next    (src_dbank_active_next),
.rst_a                (rst_a)
);


/////////////////////////////////////////////////////////////////////////////////
// Arbiter for the READ/WRITEaccesses
///////////////////////////// ////////////////////////////////////////////////////

logic [1:0]          access_req;
logic [1:0]          access_gnt;
logic [N_SRAM-1:0]   capture_bnk [2];
logic                arb_enable;

// wr_ctrl_rcv_valid should be zero if the write register contains scrubbing data
assign access_req[WR] =  do_wr && !wr_stall && |(src_dbank_active_next & target_sram[WR]) && (wr_ctrl_rcv_valid || init_going);
assign access_req[RD] =  do_rd && !rd_stall && |(src_dbank_active_next & target_sram[RD]) && !(do_scrub | scrub_pending);

// RR updated on the last beat of a transaction.  
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
assign arb_enable = wr_done || rd_done;
// spyglass enable_block Ac_conv01

// Capturing the decision o every phase
// spyglass disable_block Ac_unsync02 Ac_glitch04
// SMD: Unsynchronized Crossing
// SJ:  static enable
always @(posedge dbank_ctrl_clk or posedge rst_a) 
begin : capture_reg_PROC
  if (rst_a) begin
    capture_bnk [WR] <= 'b0 ;
    capture_bnk [RD] <= 'b0 ;
  end   
  else begin
    for (int i = 0; i < N_SRAM; i = i + 1) begin
      if ( src_dbank_active_next[i] ) begin
        capture_bnk [RD][i] <= bnk_rd_en_raw [i];
        capture_bnk [WR][i] <= bnk_wr_en_raw [i] | bnk_rmw_rd_en [i] ;
      end   
    end   
  end   
end
// spyglass enable_block Ac_unsync02 Ac_glitch04
   
// Making a decision which commmand will have access for the next sequence of pulse
// The decision is made on the last pulse of the sequence for the next sequence
// spyglass disable_block W240 
// SMD: declared but not read
// SJ: Do not care the warning of "declared but not read" 
logic        binary_out_unused; 
// spyglass enable_block W240
nl2_cln_rr_select 
  #(.LENGTH (2))
u_cln_rr 
  (
   .unitary_out (access_gnt),
   .binary_out  (binary_out_unused),
   .valid_in    (access_req),
   .next        (arb_enable),
   .clk         (dbank_clk),
   .rst_a       (rst_a));

// Propagate the dbank_active_next pulses to the controller only if the access has been granted.
assign dbank_active_next[WR] = access_gnt[WR] ? src_dbank_active_next : 'b0;
assign dbank_active_next[RD] = access_gnt[RD] ? src_dbank_active_next : 'b0;

// Pulses used to capture the read data (next following sequence)
assign capture_dbank_next[WR] = capture_bnk [WR] & src_dbank_active_next ;
assign capture_dbank_next[RD] = capture_bnk [RD] & src_dbank_active_next ;

/////////////////////////////////////////////////////////////////////////////////
// synchronous command channel:
/////////////////////////////////////////////////////////////////////////////////
assign phy_bnk_cmd_accept_raw[WR] = wr_done & dbank_accept_en;
assign phy_bnk_cmd_accept_raw[RD] = rd_done & dbank_accept_en;
   
assign {cmd_init[WR], cmd_id[WR], cmd_ecc_enable[WR], cmd_scrub_enable[WR], cmd_err[WR], cmd_addr[WR], burst_size[WR], data_size[WR], wrap[WR], read[WR], excl[WR], excl_err[WR]} = phy_bnk_cmd_data[WR];
assign {cmd_init[RD], cmd_id[RD], cmd_ecc_enable[RD], cmd_scrub_enable[RD], cmd_err[RD], cmd_addr[RD], burst_size[RD], data_size[RD], wrap[RD], read[RD], excl[RD], excl_err[RD]} = phy_bnk_cmd_data[RD];   

assign do_rd  = phy_bnk_cmd_valid_l1cg[RD];
assign do_wr  = phy_bnk_cmd_valid_l1cg[WR];
   

wire [BLOCK_ADDR_SIZE-1:0] bnk_rd_block_addr;
wire [BLOCK_ADDR_SIZE-1:0] bnk_wr_block_addr;
assign block_addr = (bnk_scrub_proc ? bnk_scrub_addr    : 'b0 ) |  
                    (access_gnt[RD] ? bnk_rd_block_addr : 'b0 ) | 
                    (access_gnt[WR] ? bnk_wr_block_addr : 'b0 ) ;


//////////////////////////////////////////////////////////////////////////////
// SRAM write controller:
//////////////////////////////////////////////////////////////////////////////

nl2_new_dbank_wr_ctrl
  #(.N_SRAM         (N_SRAM),
    .CMD_ID_SIZE    (CMD_ID_SIZE),
    .BNK_DATA_SIZE  (BNK_DATA_SIZE),
    .BNK_ADDR_SIZE  (BNK_ADDR_SIZE),
    .BNK_DATA_WIDTH (BNK_DATA_WIDTH),
    .BLOCK_ADDR_SIZE (BLOCK_ADDR_SIZE),
    .RMW_ECC_PIPE   (RMW_ECC_PIPE),
    .INTERLEAVE_ADR (INTERLEAVE_ADR),
    .SRAM_SEL_MSB   (SRAM_SEL_MSB),
    .SRAM_SEL_LSB   (SRAM_SEL_LSB))
u_dbank_wr_ctrl
(
.dbank_active_next     (dbank_active_next[WR]),
.capture_dbank_next    (capture_dbank_next[WR]),
.software_reset        (software_reset),
.do_wr                 (do_wr),
.cmd_addr              (cmd_addr[WR]),
.cmd_id                (cmd_id[WR]),
.cmd_err               (cmd_err[WR]),
.wrap                  (wrap[WR]),
.burst_size            (burst_size[WR]),
.data_size             (data_size[WR]),
.excl                  (excl[WR]),
.excl_err              (excl_err[WR]),

.target_sram           (target_sram[WR]),
.wr_done               (wr_done),
.init_going            (init_going),
.init_done             (init_done),
.init_cmd              (cmd_init[WR]),
.bnk_wr_block_addr     (bnk_wr_block_addr),
.bnk_wr_en             (bnk_wr_en_raw),

.rcv_valid             (wr_ctrl_rcv_valid),
.rcv_accept            (wr_ctrl_rcv_accept),

.rcv_rmw_req           (wr_ctrl_rcv_rmw_req),
.bnk_rmw_rd_en         (bnk_rmw_rd_en),
.bnk_rmw_rd_data_sel   (bnk_rmw_rd_data_sel),

.wr_stall              (wr_stall),
.wr_id                 (wr_id),
.wr_excl_ok            (wr_excl_ok),
.wr_idle               (wr_idle),
.wr_rsp_valid          (wr_rsp_valid),
.wr_err                (wr_err),
                        
.dbank_ctrl_clk        (dbank_ctrl_clk),
.rst_a                 (rst_a)
);

//////////////////////////////////////////////////////////////////////////////
// SRAM read controller:
//////////////////////////////////////////////////////////////////////////////

nl2_new_dbank_rd_ctrl
  #(.N_SRAM         (N_SRAM),
    .CMD_ID_SIZE    (CMD_ID_SIZE),
    .BNK_ADDR_SIZE  (BNK_ADDR_SIZE),
    .BNK_DATA_WIDTH (BNK_DATA_WIDTH),
    .BLOCK_ADDR_SIZE (BLOCK_ADDR_SIZE),
    .INTERLEAVE_ADR (INTERLEAVE_ADR),
    .SRAM_SEL_MSB   (SRAM_SEL_MSB),
    .SRAM_SEL_LSB   (SRAM_SEL_LSB))
u_dbank_rd_ctrl
(
.dbank_active_next   (dbank_active_next[RD]),
.capture_dbank_next  (capture_dbank_next[RD]), 
.do_rd               (do_rd),
.cmd_addr            (cmd_addr[RD]),
.cmd_id              (cmd_id[RD]),
.wrap                (wrap[RD]),
.burst_size          (burst_size[RD]),
.data_size           (data_size[RD]),
.excl                (excl[RD]),
.cmd_tag_err         (cmd_err[RD]),

.target_sram         (target_sram[RD]), 
.rd_done             (rd_done),
.bnk_rd_block_addr   (bnk_rd_block_addr),
.bnk_rd_en           (bnk_rd_en_raw),
.bnk_rd_last         (bnk_rd_last),
.bnk_rd_data_sel     (bnk_rd_data_sel),
.bnk_rd_data_block_addr (bnk_rd_data_block_addr),
.bnk_rd_data_ecc_en  (bnk_rd_data_ecc_en),
.ecc_enable          (cmd_ecc_enable[RD]),

.snd_valid           (rd_ctrl_snd_valid),
.rd_excl_ok          (bnk_rd_excl_ok),
.rd_tag_err          (bnk_rd_tag_err),
.rd_id               (bnk_rd_id),

.rd_stall            (rd_stall),
.rd_idle             (rd_idle),

.dbank_ctrl_clk      (dbank_ctrl_clk),
.rst_a               (rst_a)
);

for (genvar i=1; i<=CTRL_CHANNELS; i++)
begin
  assign phy_bnk_rd_valid[i]  = 1'b0;
  assign phy_bnk_rd_data[i]   =  'b0;
  assign phy_bnk_wr_accept_raw[i] = 1'b0;
end
/////////////////////////////////////////////////////////////////////////////////
// Select incoming read_data
/////////////////////////////////////////////////////////////////////////////////

// Return all zeros if there was command error

always @*
begin: rd_data_sel_PROC
  incoming_rd_data = 'b0;
  for (int i = 0; i < N_SRAM; i = i + 1)
    if (bnk_rd_data_sel[i] && !cmd_err[RD])
      incoming_rd_data |= bnk_rd_data[i];
    else if (bnk_rmw_rd_data_sel[i] && !(cmd_err[WR] || excl_err[WR]))
      incoming_rd_data |= bnk_rd_data[i];
end

//////////////////////////////////////////////////////////////////////////////
// SRAM ECC control:
//////////////////////////////////////////////////////////////////////////////
wire       bnk_wr_rmw_err;

nl2_new_dbank_buf_ctrl
  #(.N_SRAM        (N_SRAM),
    .N_NARROW      (BNK_NUM_NARROW),
    .CMD_ID_SIZE   (CMD_ID_SIZE),
    .RMW_ECC_PIPE  (RMW_ECC_PIPE),
    .BNK_ADDR_SIZE (BNK_ADDR_SIZE),
    .BNK_DATA_WIDTH(BNK_DATA_WIDTH),
    .BLOCK_ADDR_SIZE (BLOCK_ADDR_SIZE),
    .INTERLEAVE_ADR (INTERLEAVE_ADR),
    .BNK_ECC_WIDTH (BNK_ECC_WIDTH),
    .SRAM_SEL_MSB  (SRAM_SEL_MSB),
    .SRAM_SEL_LSB  (SRAM_SEL_LSB))
u_dbank_buf_ctrl
(.wr_done            (wr_done),
 .rd_done            (rd_done),
 .do_wr              (do_wr),
 .do_rd              (do_rd),
 .do_scrub           (do_scrub),
 .init_going         (init_going),
 .rdata_in_ecc_en    (bnk_rd_data_ecc_en),
 .wdata_in_scrub     (do_scrub), // Indicate that is scrub data is ready
 .wdata_in_ecc_en    (wdata_in_ecc_en),
 .wdata_in_valid     (wdata_in_valid),    
 .wdata_in_accept    (wdata_in_accept),   
 .wdata_in_mask      (wdata_in_mask),      
 .wdata_in_data      (wdata_in_data),      
 .wdata_in_block_addr(wdata_in_block_addr),

 .wdata_out_scrub    (scrub_ctl_valid), // Indicate that is scrub data is occupting the write register
 .wdata_out_valid    (wr_ctrl_rcv_valid),
 .wdata_out_accept   (wr_ctrl_rcv_accept | bnk_scrub_proc),
 .wdata_out_ecc      (bnk_wr_data_raw[BNK_RAW_WIDTH-1:BNK_DATA_WIDTH]),
 .wdata_out_data     (bnk_wr_data_raw[BNK_DATA_WIDTH-1:0]),
 .wdata_out_mask     (bnk_wr_mask_raw),
 .wdata_out_rmw_req  (bnk_wr_rmw_req),
 .wdata_out_err      (bnk_wr_rmw_err),
 .wdata_rmw_read     (|bnk_rmw_rd_data_sel),

 .rdata_in_valid     (rd_ctrl_snd_valid),
 .rdata_in_tag_err   (bnk_rd_tag_err),
 .rdata_in_excl_ok   (bnk_rd_excl_ok),
 .rdata_in_id        (bnk_rd_id),
 .rdata_in_last      (bnk_rd_last),
 .rdata_in_ecc       (incoming_rd_data[BNK_RAW_WIDTH-1:BNK_DATA_WIDTH]),
 .rdata_in_data      (incoming_rd_data[BNK_DATA_WIDTH-1:0]),
 .rdata_in_block_addr (bnk_rd_data_block_addr),
 .rdata_in_sram_sel   (bnk_rd_data_sel),

 .rdata_out_accept   (bnk_out_accept),
 .rdata_out_valid    (bnk_out_valid),
 .rdata_out_rd_id    (bnk_out_rid),
 .rdata_out_sbe      (bnk_out_sbe),
 .rdata_out_dbe      (bnk_out_dbe),
 .rdata_out_last     (bnk_out_last),
 .rdata_out_err      (bnk_out_err),
 .rdata_out_rmw      (bnk_out_rmw),
 .rdata_out_excl_ok  (bnk_out_excl_ok),
 .rdata_out_data     (bnk_out_rdata),
 .rmw_out_dbe        (bnk_rmw_dbe),
 .rmw_out_sbe        (bnk_rmw_sbe),
                      
 .rdata_out_scrub_req  (bnk_out_scrub_req),
 .rdata_out_sram_sel   (bnk_out_sram_sel),
 .rdata_out_block_addr (bnk_out_block_addr),

 .buf_idle           (buf_idle),
 .dbank_ctrl_clk     (dbank_ctrl_clk),
 .rst_a              (rst_a)
);

for (genvar i=0; i<BNK_NUM_NARROW; i++) begin: g_bnk_wr_mask
assign bnk_wr_mask[i] = init_going ? {BNK_RAW_MASK_WIDTH_NARROW{1'b1}} :
                                     bnk_wr_mask_raw[i];
end: g_bnk_wr_mask

assign bnk_wr_data = bnk_wr_data_raw;
assign bnk_wr_en = ( bnk_scrub_proc ? bnk_scrub_wr_en : {N_SRAM{1'b0}} ) |
                   ((cmd_err[WR] | bnk_wr_rmw_err | excl_err[WR] | !dbank_accept_en) ? {N_SRAM{1'b0}}  :  bnk_wr_en_raw );
assign bnk_rd_en = (cmd_err[RD] |                !dbank_accept_en ? {N_SRAM{1'b0}} : bnk_rd_en_raw ) | 
                   (cmd_err[WR] | excl_err[WR] | !dbank_accept_en ? {N_SRAM{1'b0}} : bnk_rmw_rd_en ) ;
assign wr_ctrl_rcv_rmw_req = bnk_wr_rmw_req & !cmd_err[WR];

reg                  wr_rsp_valid_d1;
reg                  wr_err_d1;
reg [WR_ID_SIZE-1:0] wr_id_d1;
reg                  wr_excl_ok_d1;

always @(posedge dbank_ctrl_clk or posedge rst_a)
begin : write_reg_PROC
  if (rst_a)
    begin
      wr_rsp_valid_d1 <= 1'b0;
      wr_id_d1        <= {WR_ID_SIZE{1'b0}};
      wr_excl_ok_d1   <= 1'b0;
      wr_err_d1       <= 1'b0;
    end
  else
    begin
      wr_rsp_valid_d1 <= wr_rsp_valid;
      wr_id_d1        <= wr_id[WR_ID_SIZE-1:0];
      wr_excl_ok_d1   <= wr_excl_ok;
      wr_err_d1       <= wr_err;
    end
end

assign bnk_rsp_valid =  (bnk_out_rmw & !excl_err[WR]) | wr_rsp_valid_d1;
assign bnk_rsp_out   =  (bnk_out_rmw) ? {1'b0, 
                                         wr_id,
                                         bnk_rmw_dbe, 
                                         bnk_rmw_sbe}
                     : {wr_rsp_valid_d1, wr_id_d1, wr_err_d1, wr_excl_ok_d1}
                     ;


logic     read_ecc_valid_r;

always @(posedge dbank_ctrl_clk or posedge rst_a)
begin : read_ecc_reg_PROC
  if (rst_a)
    begin
      read_ecc_valid_r  <= 1'b0 ;
    end
  else
    begin
      read_ecc_valid_r  <=  rd_ctrl_snd_valid;
    end
end

always @(posedge dbank_clk or posedge rst_a)
begin : mem_dbnk_err_reg_PROC
  if (rst_a)
    begin
       mem_dbnk_sbe_err <= 1'b0 ;
       mem_dbnk_dbe_err <= 1'b0 ;
    end
  else
    begin
       mem_dbnk_sbe_err <= (bnk_out_rmw & !excl_err[WR] & bnk_rmw_sbe) | (bnk_out_sbe & read_ecc_valid_r);
       mem_dbnk_dbe_err <= (bnk_out_rmw & !excl_err[WR] & bnk_rmw_dbe) | (bnk_out_dbe & read_ecc_valid_r);
    end
end





//////////////////////////////////////////////////////////////////////////////
// Scrubbing
//////////////////////////////////////////////////////////////////////////////

typedef struct packed {
  logic             [N_SRAM-1:0] bnk_sel;
  logic    [BLOCK_ADDR_SIZE-1:0] bnk_addr;
  logic     [BNK_DATA_WIDTH-1:0] bnk_data;
} scrub_info_s;

logic                     scrub_cmd_fifo_full;
logic                     scrub_cmd_fifo_valid;
scrub_info_s              scrub_cmd_fifo_out;
scrub_info_s              scrub_cmd_fifo_in;
scrub_info_s              scrub_cmd;
logic                     scrub_cmd_fifo_push;
logic                     scrub_cmd_fifo_pop;

logic                     scrub_cancel;
logic                     scrub_valid;

logic                     scrub_cancel_stg2;


assign do_scrub   =   scrub_cmd_fifo_valid & ~scrub_cancel_stg2;

// Push the scrub information into the FIFO
assign scrub_cmd_fifo_push         =  (bnk_out_scrub_req & read_ecc_valid_r && ~scrub_cancel & cmd_scrub_enable[RD] & ~scrub_cmd_fifo_full);

assign scrub_cmd_fifo_in.bnk_sel   =  bnk_out_sram_sel;
assign scrub_cmd_fifo_in.bnk_addr  =  bnk_out_block_addr;
assign scrub_cmd_fifo_in.bnk_data  =  bnk_out_rdata;

// Pop a FIFO entry if the scrub command has been acknowledged
assign scrub_cmd_fifo_pop    =  scrub_cmd_fifo_valid & (scrub_ack | scrub_cancel_stg2);

// Mux the FIFO output and scrubbing command
assign scrub_cmd =  scrub_cmd_fifo_out;

assign scrub_cancel_stg2 = scrub_cmd_fifo_valid && wr_ctrl_rcv_valid && 
                           (scrub_cmd.bnk_sel  == target_sram[WR] && 
                            scrub_cmd.bnk_addr == bnk_wr_block_addr);



if ( SCRUB_FIFO_DEPTH == 1) begin : G_SCRUB_REG

  // DEPTH = 1
  // Register stage that acts like a single entry FIFO
  
  assign scrub_cmd_fifo_full = scrub_cmd_fifo_valid & ~scrub_cmd_fifo_pop;
  
  always @(posedge dbank_ctrl_clk or posedge rst_a)
    begin : scrub_cmd_reg_PROC
      if (rst_a) begin
        scrub_cmd_fifo_valid  <= 'b0 ;
        scrub_cmd_fifo_out    <= 'b0 ;
      end
      else  begin
        if ( scrub_cmd_fifo_push )
          scrub_cmd_fifo_valid  <= 1'b1 ;
        else if ( scrub_cmd_fifo_pop )
          scrub_cmd_fifo_valid  <= 1'b0 ;

        if ( scrub_cmd_fifo_push )
          scrub_cmd_fifo_out  <=  scrub_cmd_fifo_in;

      end
    end


end
else begin : G_SCRUB_FIFO

  // DEPTH >= 2
  
  nl2_cln_fifo
    #(.WIDTH ($bits(scrub_info_s)),
      .DEPTH (SCRUB_FIFO_DEPTH))
  u_scrub_cmd_fifo
    (
     .fifo_full       (scrub_cmd_fifo_full),
     .fifo_head_valid (scrub_cmd_fifo_valid),
     .fifo_head_data  (scrub_cmd_fifo_out),
     .fifo_in         (scrub_cmd_fifo_in),
     .push            (scrub_cmd_fifo_push),
     .pop             (scrub_cmd_fifo_pop),
     .clk             (dbank_ctrl_clk),
     .rst_a           (rst_a)
     );

end



// Avoid capturing the scrubbing command before the scrubbing data is accepted
// Scrubbing data can be accepted before the command, but srcubbing command cannot be
// accepted before the scrubbing data. ECC generation is requiring the address.
assign scrub_valid  =  do_scrub & ~scrub_cancel_stg2 & (~wr_ctrl_rcv_valid | wr_ctrl_rcv_accept) ;


nl2_new_dbank_scrub_ctl
  #( .N_SRAM          (N_SRAM),
     .BLOCK_ADDR_SIZE (BLOCK_ADDR_SIZE))
u_dbank_scrub_ctl
  (
   .req_scrub         (scrub_valid), 
   .req_ack           (scrub_ack), 
   .req_bnk           (scrub_cmd.bnk_sel), 
   .req_addr          (scrub_cmd.bnk_addr), 
   .req_data_rcv      (scrub_ctl_valid), 
   .dbank_active_next (src_dbank_active_next),
   .scrub_pending     (scrub_pending),
   .scrub_proc        (bnk_scrub_proc), 
   .scrub_bnk         (bnk_scrub_wr_en), 
   .scrub_addr        (bnk_scrub_addr), 
   .clk               (dbank_ctrl_clk),
   .rst_a             (rst_a)
   );



nl2_new_dbank_ahw
  #( .N_SRAM          (N_SRAM),
     .BLOCK_ADDR_SIZE (BLOCK_ADDR_SIZE),
     .HIST_DEPTH      (N_SRAM))
u_dbank_ahw
  (
   .shift_en         (|src_dbank_active_next),
   .bnk_wr           (bnk_wr_en),
   .bnk_addr         (block_addr), 
   .scrub_bnk        (bnk_out_sram_sel), 
   .scrub_addr       (bnk_out_block_addr), 
   .scrub_cancel     (scrub_cancel), 
   .clk              (dbank_ctrl_clk),
   .rst_a            (rst_a)
   );


assign wdata_in_ecc_en      = do_scrub ? 1'b1                   : cmd_ecc_enable[WR];
assign wdata_in_valid       = do_scrub ? 1'b1                   : phy_bnk_wr_valid[0];
assign wdata_in_mask        = do_scrub ? {BNK_MASK_WIDTH{1'b1}} : phy_bnk_wr_data[0][BNK_WR_FW_SIZE-1:BNK_DATA_WIDTH];
assign wdata_in_data        = do_scrub ? scrub_cmd.bnk_data     : phy_bnk_wr_data[0][BNK_DATA_WIDTH-1:0];

assign wdata_in_block_addr  = bnk_scrub_proc ? bnk_scrub_addr   : bnk_wr_block_addr;


assign phy_bnk_wr_accept_raw[0] =  wdata_in_accept & ~do_scrub & dbank_accept_en;


//////////////////////////////////////////////////////////////////////////////
// rdata channel skidding
//////////////////////////////////////////////////////////////////////////////


// If rd channel is full, stash the comming data into the fifo and hold all new read operations
nl2_cln_fifo
  #(.WIDTH ($bits(rd_fifo_s)),
    .DEPTH (RD_FIFO_DEPTH  )) // todo: when DWAIT is not zero, we need more entries
u_rd_fifo
(
.fifo_full       (rd_fifo_full),
.fifo_head_valid (rd_fifo_valid),
.fifo_head_data  (rd_fifo_out),
.fifo_in         (rd_fifo_in),
.push            (rd_fifo_push),
.pop             (rd_fifo_pop),
.clk             (dbank_ctrl_clk),
.rst_a           (rst_a)
);


assign rd_fifo_in.last     = bnk_out_last;
assign rd_fifo_in.err      = bnk_out_err;
assign rd_fifo_in.excl_ok  = bnk_out_excl_ok;
assign rd_fifo_in.rdata    = bnk_out_rdata;
assign rd_fifo_in.sbe      = bnk_out_sbe;
assign rd_fifo_in.dbe      = bnk_out_dbe;
assign rd_fifo_in.rid      = bnk_out_rid;




// Accept incoming read data if there is storage
assign bnk_out_accept      = !rd_fifo_full ;

assign rd_fifo_pop         = phy_bnk_rd_accept[0] & rd_fifo_valid;
assign rd_fifo_push        = bnk_out_valid & !rd_fifo_full;

assign phy_bnk_rd_valid[0] = rd_fifo_valid
                           | ((!software_reset | cmd_init[WR]) && init_done) // send a message to indiate that the sram init process has finished
                           ;
assign phy_bnk_rd_data[0]  =  {rd_fifo_out.rid, rd_fifo_out.dbe, rd_fifo_out.sbe, rd_fifo_out.last, rd_fifo_out.err, rd_fifo_out.excl_ok, rd_fifo_out.rdata};





//////////////////////////////////////////////////////////////////////////////
// response channel skiddin
//////////////////////////////////////////////////////////////////////////////

// If rsp channel is full, stash the comming response into the fifo and hold all new operations
wire       rsp_fifo_valid;
wire [BNK_WRSP_FW_SIZE-1:0] rsp_fifo_out;
wire       rsp_fifo_push;
nl2_cln_fifo
  #(.WIDTH (BNK_WRSP_FW_SIZE),
    .DEPTH (N_SRAM+1))
u_rsp_fifo
(
.fifo_full       (rsp_fifo_full),
.fifo_head_valid (rsp_fifo_valid),
.fifo_head_data  (rsp_fifo_out),
.fifo_in         (bnk_rsp_out),
.push            (rsp_fifo_push),
.pop             (phy_bnk_rsp_accept & rsp_fifo_valid),
.clk             (dbank_ctrl_clk),
.rst_a           (rst_a)
);

// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
assign rsp_fifo_push     = bnk_rsp_valid & (rsp_fifo_valid | !phy_bnk_rsp_accept) & !rsp_fifo_full;
// spyglass enable_block Ac_conv01
assign phy_bnk_rsp_data  = rsp_fifo_valid ? rsp_fifo_out : bnk_rsp_out;
assign phy_bnk_rsp_valid = rsp_fifo_valid | bnk_rsp_valid;



// Credit counter for the read FIFO
//
// The credit is associated to the FIFO storage. There is 1 credit for each FIFO
// entry. The credit counter is decremented is each read access and incremented on
// every data returned.

// The extra credit with ECC enabled is the memory output register.
localparam INITIAL_CREDIT = RD_FIFO_DEPTH;
localparam CREDIT_CNT_W   = $clog2(INITIAL_CREDIT+1); // 0 is extra value

logic [CREDIT_CNT_W-1:0] rd_credit_cnt_r;
logic [CREDIT_CNT_W-1:0] rd_credit_cnt_nxt;
logic                    rd_credit_consume;
logic                    rd_credit_return;

// The credit is only counted when the clock is active
assign rd_credit_consume  =  access_gnt[RD] & dbank_accept_en;


// Return a credit on every entry popped from the FIFO
assign rd_credit_return   =  rd_fifo_pop;

// There is no credita available is the counter is zero and no credit is returned.
// If there is timing issue, the combinational part (rd_credit_return) should be removed 
// from the expression and the FIFO depth incremetned by 1.
assign rd_stall = (~|rd_credit_cnt_r) & ~rd_credit_return;


always_comb begin : crdit_cnt_PROC

  case ({ rd_credit_consume, rd_credit_return} )
    2'b01 :   rd_credit_cnt_nxt = rd_credit_cnt_r + 1;
    2'b10 :   rd_credit_cnt_nxt = rd_credit_cnt_r - 1;
    default:  rd_credit_cnt_nxt = rd_credit_cnt_r;
  endcase

end

always @(posedge dbank_ctrl_clk or posedge rst_a)
begin : credit_cnt_reg_PROC
  if (rst_a) begin
    rd_credit_cnt_r  <=  CREDIT_CNT_W'(INITIAL_CREDIT);
  end
  else  begin
    rd_credit_cnt_r  <=  rd_credit_cnt_nxt;
  end
end


assign wr_stall = rsp_fifo_valid;
assign dbank_idle = !phy_bnk_cmd_valid [WR]
                  & !phy_bnk_cmd_valid [RD]
                  & !phy_bnk_wr_valid[0]
                  & !phy_bnk_rd_valid[0]
                  & !phy_bnk_rsp_valid
                  & rd_idle
                  & wr_idle
                  & buf_idle
                  & !scrub_cmd_fifo_valid
                  & !init_going;


endmodule // new_dbank_top
