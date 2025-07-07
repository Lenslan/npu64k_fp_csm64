//////////////////////////////////////////////////////////////////////////////
// HAMMERHEAD CLUSTER NETWORK CONFIGURATION: CFG_0
// TODO: add description here
//////////////////////////////////////////////////////////////////////////////

// DEV_IDW = 7

// Configure CLN DMA: No Cluster DMA

// Configure the shared cache and memory (SCM):
//   - CFG_SCM_INTERLEAVE Must be set to be >=CFG_TXC_BLOCK_SIZE
//   - TODO: check with CLN verif team if value CFG_SCM_INTERLEAVE=1024 is covered or if they stop at 512
// 2 sub-banks, each bank active for every the other cycle

// Configure reset aperture

// Configure MCIP



// Physical Channel type
//   - Values:
//       PHYCHAN_SOURCE_SYNCHRONOUS = 1
//       PHYCHAN_ASYNC_FIFO         = 2
//       PHYCHAN_SYNCHRONOUS        = 3
//       PHYCHAN_PER_CHANNEL        = 0
//   - TODO: The significant area associated with AsyncFifo channels can be recovered by removing fifos
//            from the CLN vchan_demux modules. This is still pending
//   - Warning: If the value is not PHYCHAN_PER_CHANNEL, then all settings per channel below
//              are overruled
// Number of transaction controllers. This limits the concurrency.
// Must be set large enough to fit a burst of 16 beats x 512bit = 1024bytes (data_size=512)

// New option. To improve timing. TODO : add description

// Set to 1 if the AUX space must be accessible through an AHB peripheral port:


// Debug and observability:

// Set to 1 for a small IOMMU and 2 for a large IOMMU:

// Include performance counters (1..32):

// Include quality of service features:

// Define monitor number:

// Define performance option choice, see arcv3clusternetwork/RTL/configuration.vpp
// Values:
//    CFG_PERF_OPT_A = 0, CFG_SCM_DATA_BANKS=2
//    CFG_PERF_OPT_M = 1, CFG_SCM_DATA_BANKS=4
//    CFG_PERF_OPT_B = 2, CFG_SCM_DATA_BANKS=8
//    CFG_PERF_OPT_X = 3, CFG_SCM_DATA_BANKS=32
//
//PERF_OPT_SET_FROM_CFG_FILE = -1


// NOC master ACE port:

// If ACE master port, enable handling DVM message:

// If ACE master port, enable emicting evict transaction:

// Include active configuration register:

// Include cluster power domain:


// Include clock-gating











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



    


    
    


    
    


    
    


    
    


    
  

    


  
  
  
  
  























// Following needed for SystemVerilog which only has `ifdef...`endif
// Define a symbol for every phychan type that we are using:
`define CFG_PHYCHAN_SYNCHRONOUS 1

`define CLOG2_MAX_VCHAN_FIFO_DEPTH_X 4
`define ASYNC_FIFO_SIZE_X            10
`define ASYNC_FIFO_SIZE_CL2_X        4


`define nl2_CLN_SRCSYN_SUBCHAN_SIZE      10
