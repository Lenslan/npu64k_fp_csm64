



// build_check_str =  UNIT_LEVEL_BUILD





















// CFG_SCM_DATA_BANKS = 1
// NUM_ADDED = -7


//============================================================================
// Determine the clock gating configuration
//============================================================================

//============================================================================
// Determine the power domain configuration
//============================================================================
//============================================================================
// Determine the soft reset configuration
//============================================================================
//============================================================================
// Determine HAS_APEX of each core configuration
//============================================================================








// NO_CLN                    = 0
// PRECHECK_SLV_ARC_COUNT    = 0
// PRECHECK_SLV_DEV_COUNT    = 5
// PRECHECK_MST_CCM_COUNT    = 0
// PRECHECK_MST_NOC_COUNT    = 1
// PRECHECK_MST_PER_COUNT    = 0
// PRECHECK_DEV0_PROTOCOL    = 1
// PRECHECK_CCM0_PROTOCOL    = -1
// PRECHECK_NOC0_PROTOCOL    = 1
// PRECHECK_NOC0_DATA_SIZE   = 64
// CFG_PHYCHAN               = 3
// CFG_MST_RST_APERTURE      = 1
// HAS_CDMA                  = 0
// HAS_SCM                   = 1
// HAS_SCU                   = 0
// HAS_MCIP                  = 0
// CLN_HAS_PDM               = 1
// CFG_PERF_CTR              = 0
// CFG_QOS                   = 0
// CFG_IOMMU                 = 0
// CFG_MONITOR               = 0
// CFG_MST_NOC_ACE           = 0
// CFG_MST_NOC_DVM           = 0
// CFG_MST_NOC_EVICT         = 0




// RPATH_NARROW_CHANNELS = 1
// WPATH_NARROW_CHANNELS = 1
// CONFIGURATION_CHANNELS = 0

// CFG_RPATH_NARROW_CHANNELS  = 2
// CFG_WPATH_NARROW_CHANNELS  = 2
// CFG_RPATH_WIDE_CHANNELS    = 0
// CFG_WPATH_WIDE_CHANNELS    = 0
// CFG_CONFIGURATION_CHANNELS = 1



// est_txc = 16 ; minimal_txc = 32 ; required_txc = 32 ; CFG_TXC =  32









// DMA_CMD_FIFO_DEPTH   = 4
// DMA_RD_FIFO_DEPTH    = 7
// DMA_WR_FIFO_DEPTH    = 7
// DMA_WRSP_FIFO_DEPTH  = 4
// HSCA_CMD_FIFO_DEPTH  = 5
// HSCA_CMD2_FIFO_DEPTH = 4
// HSCA_RD_FIFO_DEPTH   = 6
// HSCA_WR_FIFO_DEPTH   = 9
// HSCA_WR2_FIFO_DEPTH  = 6
// HSCA_WRSP_FIFO_DEPTH = 4
// DEV_CMD_FIFO_DEPTH   = 4
// DEV_RD_FIFO_DEPTH    = 7
// DEV_WR_FIFO_DEPTH    = 7
// DEV_WRSP_FIFO_DEPTH  = 4
// NOC_CMD_FIFO_DEPTH   = 5
// NOC_RD_FIFO_DEPTH    = 7
// NOC_WR_FIFO_DEPTH    = 6
// NOC_WRSP_FIFO_DEPTH  = 4
// CCM_CMD_FIFO_DEPTH   = 4
// CCM_RD_FIFO_DEPTH    = 5
// CCM_WR_FIFO_DEPTH    = 5
// CCM_WRSP_FIFO_DEPTH  = 6














// CFG_SLV_ARC_COUNT = 0
// CFG_SLV_DEV_COUNT = 5

// dev0 cfg_slv[0].cmd_fifo_depths    = 8'd4
// dev0 cfg_slv[0].xwr_fifo_depths    = 8'd9
// dev0 cfg_slv[0].rd_fifo_depths     = 8'd9
// dev0 cfg_slv[0].wrsp_fifo_depths   = 8'd4
// dev1 cfg_slv[1].cmd_fifo_depths    = 8'd4
// dev1 cfg_slv[1].xwr_fifo_depths    = 8'd9
// dev1 cfg_slv[1].rd_fifo_depths     = 8'd9
// dev1 cfg_slv[1].wrsp_fifo_depths   = 8'd4
// dev2 cfg_slv[2].cmd_fifo_depths    = 8'd4
// dev2 cfg_slv[2].xwr_fifo_depths    = 8'd9
// dev2 cfg_slv[2].rd_fifo_depths     = 8'd9
// dev2 cfg_slv[2].wrsp_fifo_depths   = 8'd4
// dev3 cfg_slv[3].cmd_fifo_depths    = 8'd4
// dev3 cfg_slv[3].xwr_fifo_depths    = 8'd9
// dev3 cfg_slv[3].rd_fifo_depths     = 8'd9
// dev3 cfg_slv[3].wrsp_fifo_depths   = 8'd4
// dev4 cfg_slv[4].cmd_fifo_depths    = 8'd4
// dev4 cfg_slv[4].xwr_fifo_depths    = 8'd9
// dev4 cfg_slv[4].rd_fifo_depths     = 8'd9
// dev4 cfg_slv[4].wrsp_fifo_depths   = 8'd4

// CFG_MST_CCM_COUNT = 0
// CFG_MST_NOC_COUNT = 1
// CFG_MST_PER_COUNT = 0


// noc0 cfg_mst[0].cmd_fifo_depths    = 8'd3,8'd3
// noc0 cfg_mst[0].xwr_fifo_depths    = 8'd3
// noc0 cfg_mst[0].rd_fifo_depths     = 8'd3
// noc0 cfg_mst[0].wrsp_fifo_depths   = 8'd3
// aux cfg_mst[1].cmd_fifo_depths    = 8'd3,8'd3
// aux cfg_mst[1].xwr_fifo_depths    = 8'd3
// aux cfg_mst[1].rd_fifo_depths     = 8'd3
// aux cfg_mst[1].wrsp_fifo_depths   = 8'd5

















// Import TXC partitioning parameters from configuration



// TXC partitioning summary:
//   SLV0 connects to 1 cohorts [0]
//   SLV1 connects to 4 cohorts [0,1,2,3]
//   SLV2 connects to 4 cohorts [0,1,2,3]
//   SLV3 connects to 4 cohorts [0,1,2,3]
//   SLV4 connects to 4 cohorts [0,1,2,3]
//   SLV5 connects to 1 cohorts [1]

// TXC partitioning summary:
//   SLV0 connects to 8 TXCs [0,1,2,3,4,5,6,7]
//   SLV1 connects to 32 TXCs [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
//   SLV2 connects to 32 TXCs [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
//   SLV3 connects to 32 TXCs [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
//   SLV4 connects to 32 TXCs [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
//   SLV5 connects to 8 TXCs [8,9,10,11,12,13,14,15]



    


    
    


    
    


    
    


    
    


    
  

    


  
  
  
  
  






















`include "nl2_cln_defines.v"
module nl2_new_dbank_top_layer
#(
    parameter  N_CMD_IDS       = 4,  // valid range: >= 1
    parameter  N_WR_IDS        = 1,  // valid range: >= 1
    parameter  CMD_ADDR_SIZE   = `nl2_CFG_BNK_ADDR_SIZE, // address width: 15 to 20
    parameter  BNK_DATA_WIDTH  = `nl2_DBANK_DATA_WIDTH,  // data width: 64,128,256,512
    parameter  BNK_IN_DATA_PIPE = 1,
    parameter  WAIT_SIZE       = 2,  // bit width of waitcycle input: 1,2,4
    parameter  DATA_SIZE_TOP   = BNK_DATA_WIDTH,
    //
    // The following parameters are derived and immutable:
    //
    localparam N_SRAM          = `nl2_CFG_SCM_DATA_SUB_BANKS,  // number of SRAM sub banks instantiated: 1,2,4
    localparam CTRL_CHANNELS   = `nl2_CFG_BNK_CTRL_CHANNELS, // additional multiplexed data channels: 0
    localparam BLOCK_ADDR_SIZE = `nl2_SRAM_BLOCK_ADDR_SIZE,  // address bits used for sub bank row index: 9 to 13
    localparam DBANK_NUM_NARROW = `nl2_DBANK_NUM_NARROW,  // number of ECC encoder/decoders
    localparam INTERLEAVE_ADR  = $clog2(`nl2_CFG_SCM_INTERLEAVE),  // Max Supported Burst Length
    // localparam DATA_SIZE_TOP   = BNK_DATA_WIDTH,
    localparam DATA_SIZE_PATH  = BNK_DATA_WIDTH, // valid range: power of 2 and >= 8
    localparam MULTICAST_SIZE  = 1,  // valid range: >= 1
    localparam REGION_SIZE     = 4,
    localparam CMD_OUTSTANDING = 3,  // valid range: >= 3
    localparam FAST_WRSP       = 0,  // valid range: 0,1
    localparam HAS_AUX         = 0, // valid range: 0,1
    localparam HAS_MCIP        = 0, // valid range: 0,1
    localparam CMD_ID_SIZE   = $clog2(N_CMD_IDS),
    localparam CMD_ID_XSIZE  = (CMD_ID_SIZE == 0) ? 1 : CMD_ID_SIZE,
    localparam WR_ID_SIZE    = $clog2(N_WR_IDS),
    localparam WR_ID_XSIZE   = (WR_ID_SIZE == 0) ? 1 : WR_ID_SIZE,
    localparam WSTB_SIZE_PATH = DATA_SIZE_PATH/8,
    localparam WR_FW_SIZE     = DATA_SIZE_PATH + WSTB_SIZE_PATH + 1,  // {wr_data,wr_mask,wr_last}
    localparam WSTB_SIZE_TOP  = DATA_SIZE_TOP/8,
    localparam XCMD_SIZE     = 1/* xcmd_wcombine*/ + 1/* xcmd_fast_wrsp */ + MULTICAST_SIZE,
    localparam CLOG2_WSTB_PATH_BYTES = $clog2(WSTB_SIZE_PATH),
    localparam CLOG2_WSTB_TOP_BYTES = $clog2(WSTB_SIZE_TOP),
    localparam OUTSTANDING_ADR = $clog2(`nl2_CFG_TXC)
 )
(
//////////////////////////////////////////////////////////////////////////////////
//input                              clk,  //axi clock 
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

output                             mem_dbnk_sbe_err,
output                             mem_dbnk_dbe_err,
////////////////////////////////////////////////////////////////////////////////
input                              mem_ecc_enb, // DBNK ECC enable (static)
input                              mem_scrub_enb, // DBNK Scrub enable (static)
 
input                              mem_init, // Memory Initialization (rising edge)
output                             mem_init_done, // Memory Done (level)
input                              disable_rst_init, // Disables H/W mem init on reset assertion when ‘1’
input                              sd, // DBANK memories power domain management
input                              ds, // DBANK memories power domain management

input                              dbnk_clk,
// Misc.
input                              rst_a
 );

/////////////////////////////////////////////////////////////////////////////////
// Instantiate full SRAM module for each DBANK
/////////////////////////////////////////////////////////////////////////////////
logic   [N_SRAM-1:0] dbank_sram_clk;
logic     [BLOCK_ADDR_SIZE-1:0] dbank_block_addr;
logic   [N_SRAM-1:0] dbank_rd_en;
logic          [`nl2_DBANK_RAW_WIDTH-1:0] dbank_rd_data[N_SRAM-1:0]; 
logic   [N_SRAM-1:0] dbank_wr_en;
logic          [`nl2_DBANK_RAW_WIDTH-1:0] dbank_wr_data;
logic  [`nl2_DBANK_MASK_WIDTH_NARROW-1:0] dbank_wr_mask[DBANK_NUM_NARROW-1:0];    
 

for (genvar bnk=0; bnk<1;bnk++)
begin: g_scm_dbank_sram_all
  nl2_scm_dbank_sram_all
    #(.ADDR_SIZE  (BLOCK_ADDR_SIZE),
      .DATA_WIDTH (`nl2_DBANK_RAW_WIDTH),
      .ECC_WIDTH  (`nl2_DBANK_ECC_WIDTH),
      .MASK_WIDTH (`nl2_DBANK_MASK_WIDTH_NARROW),
      .N_NARROW   (DBANK_NUM_NARROW),
      .N_SRAM     (N_SRAM))
  u_scm_dbank_sram_all
  (.ck_in     (dbank_sram_clk),
   .data_wr   (dbank_wr_data),
   .sd        (sd),
   .ds        (ds),
   .addr_in   (dbank_block_addr),
   .mask_in   (dbank_wr_mask),
   .read_en   (dbank_rd_en),
   .wrte_en   (dbank_wr_en),
   .data_rd   (dbank_rd_data)
   );
end : g_scm_dbank_sram_all


nl2_new_dbank_top_wrapper
 #(
   .N_SRAM             (N_SRAM),
   .N_CMD_IDS          (N_CMD_IDS),
   .N_WR_IDS           (N_WR_IDS),
   .BNK_DATA_WIDTH     (BNK_DATA_WIDTH),
   .BNK_IN_DATA_PIPE   (BNK_IN_DATA_PIPE),
   .INTERLEAVE_ADR     (INTERLEAVE_ADR),
   .BLOCK_ADDR_SIZE    (BLOCK_ADDR_SIZE),
   .WAIT_SIZE          (WAIT_SIZE),
   .BNK_ECC_WIDTH      (`nl2_DBANK_ECC_WIDTH),
   .CMD_ADDR_SIZE   (CMD_ADDR_SIZE), // valid range: >= 1
   .DATA_SIZE_TOP   (DATA_SIZE_TOP),
   .DATA_SIZE_PATH  (DATA_SIZE_PATH), // valid range: power of 2 and >= 8
   .CTRL_CHANNELS      (CTRL_CHANNELS))
u_new_dbank_top_wrapper
  (
.dbank_sram_waitcyc (2'd`nl2_CFG_SCM_DATA_BANK_WAIT_CYCLES),
.dbank_sram_clk      (dbank_sram_clk),
// SRAM interface:
.block_addr         (dbank_block_addr),
.bnk_rd_en          (dbank_rd_en),
.bnk_rd_data        (dbank_rd_data),
.bnk_wr_en          (dbank_wr_en),
.bnk_wr_data        (dbank_wr_data),
.bnk_wr_mask        (dbank_wr_mask),

.mem_dbnk_sbe_err   (mem_dbnk_sbe_err),
.mem_dbnk_dbe_err   (mem_dbnk_dbe_err),

.axi_clk           (dbnk_clk), //same clock domain
// AXI4 read command channel:
.axi_arvalid      (axi_arvalid),
.axi_arready      (axi_arready),
.axi_arid         (axi_arid),          
.axi_araddr       (axi_araddr) ,
.axi_arsize       (axi_arsize) ,
.axi_arlen        (axi_arlen),
.axi_arburst      (axi_arburst),
.axi_arlock       (axi_arlock),
.axi_arprot       (axi_arprot),
.axi_arcache      (axi_arcache),
.axi_aruser       ('0),
// AXI4 write command channel:
.axi_awvalid      (axi_awvalid),
.axi_awready      (axi_awready),
.axi_awid         (axi_awid),          
.axi_awaddr       (axi_awaddr),
.axi_awsize       (axi_awsize),
.axi_awlen        (axi_awlen),
.axi_awburst      (axi_awburst),
.axi_awlock       (axi_awlock),
.axi_awprot       (axi_awprot),
.axi_awcache      (axi_awcache),
.axi_awuser       ('0),
// AXI4 read data channel:
.axi_rvalid      (axi_rvalid),
.axi_rready      (axi_rready),
.axi_rdata       (axi_rdata),
.axi_rlast       (axi_rlast),
.axi_rresp       (axi_rresp),
.axi_rid         (axi_rid),
// AXI4 write data channel:
.axi_wvalid      (axi_wvalid),
.axi_wready      (axi_wready),
.axi_wdata       (axi_wdata),
.axi_wstrb       (axi_wstrb),
.axi_wlast       (axi_wlast),
// AXI4 write response channel:
.axi_bvalid      (axi_bvalid),
.axi_bready      (axi_bready),
.axi_bresp       (axi_bresp),
.axi_bid         (axi_bid),

.cmd_ecc_enable     (mem_ecc_enb), 
.cmd_scrub_enable   (mem_scrub_enb),
// Misc:
.software_reset     (disable_rst_init),
.init_start         (mem_init), 
.init_done          (mem_init_done),
.dbank_clk          (dbnk_clk),
.clst_ready         (1'b1), //TODO
.rst_a              (rst_a)
);



endmodule //dbank_top_dut


