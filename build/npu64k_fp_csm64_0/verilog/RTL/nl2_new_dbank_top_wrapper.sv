`include "nl2_cln_defines.v"

module nl2_new_dbank_top_wrapper
  #(
    parameter N_CMD_IDS       = 1,  // valid range: >= 1
    parameter N_WR_IDS        = 1,  // valid range: >=   = BLOCK_ADDR_SIZE1
    parameter N_SRAM          = `nl2_CFG_SCM_DATA_SUB_BANKS, // legal range: {2,4}    
    parameter BNK_DATA_WIDTH   = 8, // legal range: >= 8, and power of 2
    parameter BNK_ECC_WIDTH    = 0,
    parameter BNK_IN_DATA_PIPE = 1,
    parameter CMD_ADDR_SIZE   = `nl2_CFG_BNK_ADDR_SIZE, // valid range: >= 1
    parameter DATA_SIZE_TOP   = `nl2_DBANK_DATA_WIDTH,
    parameter DATA_SIZE_PATH  = `nl2_DBANK_DATA_WIDTH, // valid range: power of 2 and >= 8
    parameter MULTICAST_SIZE  = 1,  // valid range: >= 1
    parameter CTRL_CHANNELS   = `nl2_CFG_BNK_CTRL_CHANNELS, // valid range: >= 0
    parameter INTERLEAVE_ADR  = $clog2(`nl2_CFG_SCM_INTERLEAVE),  // Max Supported Burst Length
    parameter BLOCK_ADDR_SIZE = `nl2_SRAM_BLOCK_ADDR_SIZE,
    parameter WAIT_SIZE       = 4,
    //
    // The following parameters are derived and immutable:
    //
    localparam SPLIT_CMD_RD_WR = 1, // valid range: 0,1
    localparam CMD_ID_SIZE   = $clog2(N_CMD_IDS),
    localparam CMD_ID_XSIZE  = (CMD_ID_SIZE == 0) ? 1 : CMD_ID_SIZE,
    localparam WR_ID_SIZE    = $clog2(N_WR_IDS),
    localparam WR_ID_XSIZE   = (WR_ID_SIZE == 0) ? 1 : WR_ID_SIZE,
    localparam WSTB_SIZE_PATH = DATA_SIZE_PATH/8,
    localparam WSTB_SIZE_TOP  = DATA_SIZE_TOP/8,
    // Extra bits :
    // 1. xcmd_wcombine
    // 2. xcmd_fast_wrsp
    localparam XCMD_SIZE     = 2 + MULTICAST_SIZE,
    localparam BNK_ECC_ENABLE  = 1,
    // Extra bits
    // 1. Memory intialization
    // 2. scrub_enable   
    // 3. ecc_error
    // 4. wrap
    // 5. read
    // 6. excl
    // 7. excl_err
    localparam BNK_CMD_FW_SIZE   = `nl2_CFG_BNK_ADDR_SIZE + `nl2_CLN_CMD_BURST_SIZE + CMD_ID_XSIZE + BNK_ECC_ENABLE + `nl2_IBP_CMD_DATA_SIZE + 7,
    localparam BNK_RD_FW_SIZE    = CMD_ID_XSIZE + 5 + DATA_SIZE_PATH, // {cmd_id, rd_ecc_dbe, rd_ecc_sbe,rd_last,rd_excl_ok,rd_data} 
    localparam BNK_WR_FW_SIZE    = DATA_SIZE_PATH + WSTB_SIZE_PATH,  // {wr_data,wr_mask}
    localparam BNK_WRSP_FW_SIZE  = WR_ID_XSIZE + 3, //{last, wr_id, dbe, sbe/wr_excl_okay}
    localparam CLOG2_WSTB_PATH_BYTES = $clog2(WSTB_SIZE_PATH),
    localparam CLOG2_WSTB_TOP_BYTES = $clog2(WSTB_SIZE_TOP),
    localparam OUTSTANDING_ADR = $clog2(`nl2_CFG_TXC),
    localparam BNK_RAW_WIDTH   = BNK_DATA_WIDTH + BNK_ECC_WIDTH,
    localparam BNK_DATA_SIZE   = `nl2_CFG_SCM_DATA_SIZE/1,
    localparam BNK_NUM_NARROW  = `nl2_DBANK_NUM_NARROW,
    localparam BNK_MASK_WIDTH_NARROW  = BNK_DATA_WIDTH/ (8 * BNK_NUM_NARROW),
    localparam BNK_RAW_MASK_WIDTH_NARROW  = `nl2_DBANK_MASK_WIDTH_NARROW
)
(
//////////////////////////////////////////////////////////////////////////////////
input                              axi_clk,
// AXI4 read command channel:
input                              axi_arvalid,
output                             axi_arready,
input           [CMD_ID_XSIZE-1:0] axi_arid,          
input          [CMD_ADDR_SIZE-1:0] axi_araddr,
input                        [2:0] axi_arsize,
input         [`nl2_AXI_CMD_BURST_RNG] axi_arlen,
input                        [1:0] axi_arburst,
input                              axi_arlock,
input                        [2:0] axi_arprot,
input                        [3:0] axi_arcache,
input              [`nl2_AXI_USER_RNG] axi_aruser,
// AXI4 write command channel:
input                              axi_awvalid,
output                             axi_awready,
input            [WR_ID_XSIZE-1:0] axi_awid,          
input          [CMD_ADDR_SIZE-1:0] axi_awaddr,
input                        [2:0] axi_awsize,
input         [`nl2_AXI_CMD_BURST_RNG] axi_awlen,
input                        [1:0] axi_awburst,
input                              axi_awlock,
input                        [2:0] axi_awprot,
input                        [3:0] axi_awcache,
input              [`nl2_AXI_USER_RNG] axi_awuser,
// AXI4 read data channel:
output                             axi_rvalid,
input                              axi_rready,
output         [DATA_SIZE_TOP-1:0] axi_rdata,
output                             axi_rlast,
output                       [1:0] axi_rresp,
output          [CMD_ID_XSIZE-1:0] axi_rid,
// AXI4 write data channel:
input                              axi_wvalid,
output                             axi_wready,
input          [DATA_SIZE_TOP-1:0] axi_wdata,
input          [WSTB_SIZE_TOP-1:0] axi_wstrb,
input                              axi_wlast,
// AXI4 write response channel:
output                             axi_bvalid,
input                              axi_bready,
output                       [1:0] axi_bresp,
output           [WR_ID_XSIZE-1:0] axi_bid,
////////////////////////////////////////////////////////////////////////////////
// dbank related
// SRAM interface
input                 [WAIT_SIZE-1:0] dbank_sram_waitcyc,
output                   [N_SRAM-1:0] dbank_sram_clk,
// SRAM interface:
output          [BLOCK_ADDR_SIZE-1:0] block_addr,
output                   [N_SRAM-1:0] bnk_rd_en,
input             [BNK_RAW_WIDTH-1:0] bnk_rd_data[N_SRAM-1:0],
output                   [N_SRAM-1:0] bnk_wr_en,
output            [BNK_RAW_WIDTH-1:0] bnk_wr_data,
output [BNK_RAW_MASK_WIDTH_NARROW-1:0] bnk_wr_mask[BNK_NUM_NARROW-1:0],
output                                mem_dbnk_sbe_err,
output                                mem_dbnk_dbe_err,
input                                 software_reset,
input                                 dbank_clk,
////////////////////////////////////////////////////////////////////////////////

//////////////////
input logic     cmd_ecc_enable,
input logic     cmd_scrub_enable,
output                               init_done,
input                                init_start,

////////////////////////////////////////////////////////////////////////////////
// Misc.
input                              clst_ready,
input                              rst_a
);

/////////////////////////////////////////////////////////////////////////////////
// synchronous CMD channel to dbank_top:
logic                             phy_slv_cmd_valid[1+SPLIT_CMD_RD_WR];
logic       [BNK_CMD_FW_SIZE-1:0] phy_slv_cmd_data[1+SPLIT_CMD_RD_WR];
logic                             phy_slv_cmd_accept[1+SPLIT_CMD_RD_WR];
// synchronous WR channel to dbank_top:
logic                             phy_slv_wr_valid[1+CTRL_CHANNELS];
logic        [BNK_WR_FW_SIZE-1:0] phy_slv_wr_data[1+CTRL_CHANNELS];
logic                             phy_slv_wr_accept[1+CTRL_CHANNELS];
// synchronous RD channel from dbank_top:
logic                             phy_slv_rd_valid[1+CTRL_CHANNELS];
logic        [BNK_RD_FW_SIZE-1:0] phy_slv_rd_data[1+CTRL_CHANNELS];
logic                             phy_slv_rd_accept[1+CTRL_CHANNELS];
// synchronous WRSP channel from dbank_top:
logic                             phy_slv_wrsp_valid;
logic      [BNK_WRSP_FW_SIZE-1:0] phy_slv_wrsp_data;
logic                             phy_slv_wrsp_accept;

logic                          dbank_idle;
logic                          slv_ready;


assign slv_ready = 1'b1 ;

//////////////////////////////////////////////////////////////////////////////
//exclusive monitor
logic [1:0] excl_err;

nl2_new_dbank_excl_monitor
  #(.CMD_ID_SIZE    (CMD_ID_XSIZE),
    .CMD_ADDR_SIZE  (`nl2_CFG_BNK_ADDR_SIZE),
    .WR_ID_SIZE     (WR_ID_XSIZE)
    )
u_dbank_excl_monitor
(
.axi_arvalid   (axi_arvalid),
.axi_arready   (axi_arready),
.axi_arlock    (axi_arlock),
.axi_arid      (axi_arid),
.axi_araddr    (axi_araddr[`nl2_CFG_BNK_ADDR_SIZE-1:0]),
.axi_awvalid   (axi_awvalid),
.axi_awready   (axi_awready),
.axi_awlock    (axi_awlock),
.axi_awid      (axi_awid),
.axi_awaddr    (axi_awaddr[`nl2_CFG_BNK_ADDR_SIZE-1:0]),
.excl_err      (excl_err),
.axi_clk       (axi_clk),
.rst_a         (rst_a)
);

//////////////////////////////////////////////////////////////////////////////
// Synchronize write responses to their corresponding wr_last occurence:
//////////////////////////////////////////////////////////////////////////////



///////////////////////////////////////////////////////////////////////
// new_dbank_axi2bnk instantiate:
///////////////////////////////////////////////////////////////////////
nl2_new_dbank_axi2bnk #(.CMD_ID_SIZE    (CMD_ID_XSIZE),
                    .WR_ID_SIZE     (WR_ID_XSIZE),
                    .CMD_ADDR_SIZE  (`nl2_CFG_BNK_ADDR_SIZE),
                    .DATA_SIZE      (DATA_SIZE_TOP),
                    .BNK_ADDR_SIZE  (`nl2_CFG_BNK_ADDR_SIZE),                    
                    .BNK_DATA_WIDTH (`nl2_DBANK_DATA_WIDTH),
                    .BNK_IN_DATA_PIPE (BNK_IN_DATA_PIPE),
                    .CTRL_CHANNELS  (CTRL_CHANNELS),
                    .MULTICAST_SIZE (MULTICAST_SIZE))
u_new_dbank_axi2bnk
(

// Bank command channel from dbank_bottom
.phy_bnk_cmd_valid                  (phy_slv_cmd_valid),
.phy_bnk_cmd_data                   (phy_slv_cmd_data ),
.phy_bnk_cmd_accept                 (phy_slv_cmd_accept),
// Bank write data channel from dbank_bottom
.phy_bnk_wr_valid                   (phy_slv_wr_valid),
.phy_bnk_wr_data                    (phy_slv_wr_data),
.phy_bnk_wr_accept                  (phy_slv_wr_accept),
// Bank read data channel to dbank_bottom
.phy_bnk_rd_valid                   (phy_slv_rd_valid),
.phy_bnk_rd_data                    (phy_slv_rd_data),
.phy_bnk_rd_accept                  (phy_slv_rd_accept),
// Bank write response channel to dbank_bottom
.phy_bnk_rsp_valid                  (phy_slv_wrsp_valid),
.phy_bnk_rsp_data                   (phy_slv_wrsp_data),
.phy_bnk_rsp_accept                 (phy_slv_wrsp_accept),

.axi_arvalid           (axi_arvalid),
.axi_arready           (axi_arready), 
.axi_arid              (axi_arid),         
.axi_araddr            (axi_araddr[`nl2_CFG_BNK_ADDR_SIZE-1:0]),
.axi_arsize            (axi_arsize),
.axi_arlen             (axi_arlen),
.axi_arburst           (axi_arburst),
.axi_arlock            (axi_arlock),
.axi_arprot            (axi_arprot),
.axi_arcache           (axi_arcache),
.axi_aruser            (axi_aruser),

.axi_awvalid           (axi_awvalid),
.axi_awready           (axi_awready), 
.axi_awid              (axi_awid),          
.axi_awaddr            (axi_awaddr[`nl2_CFG_BNK_ADDR_SIZE-1:0]),
.axi_awsize            (axi_awsize),
.axi_awlen             (axi_awlen),
.axi_awburst           (axi_awburst),
.axi_awlock            (axi_awlock),
.axi_awprot            (axi_awprot),
.axi_awcache           (axi_awcache),
.axi_awuser            (axi_awuser),

.axi_rvalid            (axi_rvalid),
.axi_rready            (axi_rready),
.axi_rdata             (axi_rdata),
.axi_rlast             (axi_rlast),
.axi_rresp             (axi_rresp),
.axi_rid               (axi_rid),

.axi_wvalid            (axi_wvalid),
.axi_wdata             (axi_wdata),
.axi_wready            (axi_wready),
.axi_wstrb             (axi_wstrb),
.axi_wlast             (axi_wlast),

.axi_bready            (axi_bready),
.axi_bid               (axi_bid),
.axi_bvalid            (axi_bvalid),
.axi_bresp             (axi_bresp),
.cmd_scrub_enable      (cmd_scrub_enable),    
.cmd_ecc_enable        (cmd_ecc_enable), 
.excl_err              (excl_err),


.disable_rst_init      (software_reset), //input
.init_done             (init_done),
.init_start            (init_start),
 
.slv_ready             (slv_ready),
.axi_clk               (axi_clk),
.rst_a                 (rst_a)

);

///////////////////////////////////////////////////////////////////////
// new_dbank_top instantiate:
///////////////////////////////////////////////////////////////////////
nl2_new_dbank_top
  #(
   .CMD_ID_SIZE        (CMD_ID_XSIZE),
   .WR_ID_SIZE         (WR_ID_XSIZE),   
   .N_SRAM             (`nl2_CFG_SCM_DATA_SUB_BANKS),
   .BNK_DATA_SIZE      (BNK_DATA_SIZE),
   .BNK_ADDR_SIZE      (`nl2_CFG_BNK_ADDR_SIZE),
   .BNK_DATA_WIDTH     (`nl2_DBANK_DATA_WIDTH),
   .BNK_ECC_WIDTH      (`nl2_DBANK_ECC_WIDTH),
   .WAIT_SIZE          (WAIT_SIZE),
   .CTRL_CHANNELS      (`nl2_CFG_BNK_CTRL_CHANNELS)       
   )
u_dbank_top(
.dbank_sram_waitcyc                 (dbank_sram_waitcyc),
.dbank_sram_clk                     (dbank_sram_clk),
// SRAM interface
.block_addr                         (block_addr),
.bnk_rd_en                          (bnk_rd_en),
.bnk_rd_data                        (bnk_rd_data),
.bnk_wr_en                          (bnk_wr_en),
.bnk_wr_data                        (bnk_wr_data),
.bnk_wr_mask                        (bnk_wr_mask),
// Bank command channel from dbank_bottom
.phy_bnk_cmd_valid                  (phy_slv_cmd_valid),
.phy_bnk_cmd_data                   (phy_slv_cmd_data ),
.phy_bnk_cmd_accept                 (phy_slv_cmd_accept),
// Bank write data channel from dbank_bottom
.phy_bnk_wr_valid                   (phy_slv_wr_valid),
.phy_bnk_wr_data                    (phy_slv_wr_data),
.phy_bnk_wr_accept                  (phy_slv_wr_accept),
// Bank read data channel to dbank_bottom
.phy_bnk_rd_valid                   (phy_slv_rd_valid),
.phy_bnk_rd_data                    (phy_slv_rd_data),
.phy_bnk_rd_accept                  (phy_slv_rd_accept),
// Bank write response channel to dbank_bottom
.phy_bnk_rsp_valid                  (phy_slv_wrsp_valid),
.phy_bnk_rsp_data                   (phy_slv_wrsp_data),
.phy_bnk_rsp_accept                 (phy_slv_wrsp_accept),
.mem_dbnk_sbe_err                   (mem_dbnk_sbe_err),
.mem_dbnk_dbe_err                   (mem_dbnk_dbe_err),
//Misc
.software_reset                     (software_reset), //input
.dbank_idle                         (dbank_idle), //output
.dbank_clk                          (dbank_clk),
.rst_a                              (rst_a)

);


endmodule // dbank_top_wrapper

