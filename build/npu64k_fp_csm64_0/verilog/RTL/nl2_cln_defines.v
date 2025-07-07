
`ifndef nl2_CLN_DEFINES_INCLUDED_
`define nl2_CLN_DEFINES_INCLUDED_


`include "nl2_cln_timescale.v"
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



    


    
    


    
    


    
    


    
    


    
  

    


  
  
  
  
  























  





`define nl2_CLN_SYNC_LEGACY_IMPL   1

`define nl2_CLN_IS_DBANK_TOP        1
`define nl2_DBNK_HAS_EXCL_MON       1
`define nl2_DBNK_AXI_INTERFACE      1
`define nl2_BNK_CNTRL_PIPE          0
`define nl2_BNK_IN_DATA_PIPE        0
`define nl2_BNK_OUT_DATA_PIPE       0
`define nl2_DBNK_HAS_SFTY           1
`define nl2_DBNK_INTF_ECC_WIDTH     128
`define nl2_CFG_DBNK_PARITY         EVEN

// Determine HAS_APEX of each core configuration

`define nl2_IBP_MAX_TX_BYTES 2048


`define nl2_IBP_CMD_SPACE_SIZE 3
`define nl2_IBP_CMD_SPACE_RNG  2:0
`define nl2_IBP_CMD_BURST_SIZE 4
`define nl2_IBP_CMD_BURST_RNG  3:0
`define nl2_IBP_CMD_DATA_SIZE  3
`define nl2_IBP_CMD_DATA_RNG   2:0
`define nl2_IBP_CMD_CTRL_SIZE  31
`define nl2_IBP_CMD_FULCTRL_SIZE  37

`define nl2_AXI_CMD_BURST_SIZE 8
`define nl2_AXI_CMD_BURST_RNG  7:0
`define nl2_CLN_CMD_BURST_SIZE 8
`define nl2_CLN_CMD_BURST_RNG  7:0
`define nl2_CLN_CMD_CTRL_SIZE  35
`define nl2_CLN_CMD_FULCTRL_SIZE 41

`define nl2_ARC_CMD_BURST_SIZE 4
`define nl2_ARC_CMD_CTRL_SIZE 31
`define nl2_ARC_CMD_FULCTRL_SIZE 37


`define nl2_IBP_CMD_SPACE_MEMORY  0
`define nl2_IBP_CMD_SPACE_AUX     1   
`define nl2_IBP_CMD_SPACE_RTT     2   
`define nl2_IBP_CMD_SPACE_VIRTMEM 3
`define nl2_IBP_CMD_SPACE_XSPC0   4 
`define nl2_IBP_CMD_SPACE_XSPC1   5 
`define nl2_IBP_CMD_SPACE_XSPC2   6
`define nl2_IBP_CMD_SPACE_RSVD7   7

`define nl2_AXI_USER_SIZE 3
`define nl2_AXI_USER_RNG  2 :0

// IBP write response size
`define nl2_IBP_WRSP_SIZE 2
`define nl2_IBP_WRSP_RNG  1 :0
`define nl2_IBP_WRSP_OKAY      2'b00
`define nl2_IBP_WRSP_ERR       2'b10
`define nl2_IBP_WRSP_EXCL_OKAY 2'b01

`define nl2_CFG_ADDR_SIZE     52
`define nl2_CLN_HAS_ARCH_CGATE 0
`define nl2_CLN_EXPORT_IRQ     0

`define nl2_CLN_VERSION_MINOR 0
`define nl2_CLN_VERSION_MAJOR 32
`define nl2_DEF_CLN_VER       32
`define nl2_AUX_BCR_ADDR_SIZE 8
`define nl2_CLUSTER_BUILD     8'hCF

`define nl2_CLN_HAS_DEBUG 0
`define nl2_CLN_HAS_RTT   0


`define nl2_CLN_HAS_MCIP 0

`define nl2_CLN_HAS_DMA 0

`define nl2_CLN_HAS_AUX 0

`define nl2_CLN_HAS_PDM 1
`define nl2_CLN_PDM_FG  0
`define nl2_CFG_CLN_EXPORT_SRAM_PG 1


`define nl2_CFG_MONITOR 0

`define nl2_CFG_SLV_EXTERNAL    5
`define nl2_CFG_ARC_DEV         5
`define nl2_CFG_SLV_ALL         6
`define nl2_CFG_SLV_ADR         3
`define nl2_CFG_SLV_ADR_M1      2
`define nl2_CFG_ARC_TRACE_CNTRL 0
`define nl2_SLV_IBP_TTU_ID      4
`define nl2_SLV_APB_TRC_ID      5
`define nl2_CLN_DMA_ID          5
`define nl2_CLN_SEQUENCER_ID    5
`define nl2_CFG_SLV_DBG         0
`define nl2_CFG_ACR             0

`define nl2_CFG_SLV_ARC_ADR    1
`define nl2_CFG_SLV_ARC_ADR_M1 0

`define nl2_CLN_MULTICAST_SIZE 0

`define nl2_TXB_REF_COUNT_SIZE 3
`define nl2_TXB_REF_COUNT_RNG  3-1:0

`ifdef nl2_CFG_PERF_OPT
`define nl2_CFG_PERF_OPT 0
`endif


`define nl2_CFG_EXISTS_DEV0
`define nl2_CFG_EXISTS_DEV1
`define nl2_CFG_EXISTS_DEV2
`define nl2_CFG_EXISTS_DEV3
`define nl2_CFG_EXISTS_DEV4

`define nl2_CFG_EXISTS_NOC0




`define nl2_CFG_MST_ALL 2
`define nl2_CFG_MST_ADR 2
`define nl2_MST_ID_ERR 2

`define nl2_CFG_MST_RST_APERTURE 1
`define nl2_CFG_MST_RST_APERTURE_REGID `nl2_CFG_MST_RST_APERTURE_REGID
`define nl2_CFG_MST_RST_APERTURE_ADDR `nl2_CFG_MST_RST_APERTURE_ADDR
`define nl2_CFG_MST_RST_APERTURE_SIZE `nl2_CFG_MST_RST_APERTURE_SIZE


// The AxID to use when MST port runs out of buffers:
`define nl2_CLN_MST_REMAP_ID 0

`define nl2_MAX_ADDR_SIZE 52

`define nl2_CFG_TXC_BLOCK_SIZE 4096

`define nl2_ADEP_GRANUL 4

`define nl2_ADEP_BLOCKS_PER_4k 1024

`define nl2_CFG_ADDR_SIZE_M1  51

`define nl2_CFG_CMD_GRAY_SIZE 3

`define nl2_MAX_VCHAN_FIFO_DEPTH       15
`define nl2_CLOG2_MAX_VCHAN_FIFO_DEPTH 4

`define nl2_PHYCHAN_SOURCE_SYNCHRONOUS 1
`define nl2_PHYCHAN_ASYNC_FIFO         2
`define nl2_PHYCHAN_SYNCHRONOUS        3
`define nl2_PHYCHAN_PER_CHANNEL        0
`define nl2_CFG_PHYCHAN 3

`define nl2_CFG_SYNC3 0
`define nl2_CFG_SYNCN 0


`define nl2_CLN_ARC_ASYNC 0

// Next two only used with CFG_PHYCHAN_ASYNC_FIFO:
`define nl2_ASYNC_FIFO_SIZE     10
`define nl2_ASYNC_FIFO_SIZE_CL2 4


`define nl2_HAS_SCM 1



`define nl2_MAX_SCM_CACHE_ASSOC_ADDR 4
`define nl2_MAX_SCM_CACHE_SETS_ADDR  16
`define nl2_MAX_SCM_CACHE_ADDR_SIZE  46
`define nl2_MAX_SCM_CACHE_OP_SIZE    35

`define nl2_CFG_EXISTS_SRAM0

`define nl2_CFG_BNK_CTRL_CHANNELS 0


`define nl2_CFG_BNK_CMD_FIFO_DEPTH 9
`define nl2_CFG_BNK_WR_FIFO_DEPTH 9
`define nl2_CFG_BNK_RD_FIFO_DEPTH 9


`define nl2_CFG_SCM_DATA_SUB_BANKS 2

`define nl2_CFG_BNK_ALL 1
`define nl2_CFG_BNK_ALL_M1 0
`define nl2_CFG_BNK_ADR 0
`define nl2_CFG_BNK_ADR_M1 -1


`define nl2_CFG_SCM_CACHE 0
`define nl2_CFG_TBK_ALL 8
`define nl2_CFG_TBK_ALL_M1 7
`define nl2_CFG_TBK_ADR 3
`define nl2_CFG_TBK_ADR_M1 2

// Next two are for timing constraints
`define nl2_CFG_SCM_DATA_BANK_WAIT_CYCLES 1
`define nl2_CFG_SCM_CACHE_TAG_WAIT_CYCLES 0

// Next two are typically equal to previous two, but could be different:
`define nl2_CFG_SCM_DWAIT_RESET 1
`define nl2_CFG_SCM_TWAIT_RESET 0


`define nl2_CFG_SCM_CACHE_ASSOC 8
`define nl2_CFG_SCM_CACHE_ASSOC_M1 7
`define nl2_CFG_SCM_CACHE_ASSOC_ADDR 3
`define nl2_CFG_SCM_CACHE_ASSOC_ADDR_M1 2
`define nl2_MAX_SCM_CACHE_ASSOC_ADDR_M1 3

`define nl2_SCM_BLOCKS_PER_4k 1


`define nl2_CFG_NUM_SRC 10
`define nl2_CFG_SRC_ADR 4

`define nl2_CFG_NUM_DST 10
`define nl2_CFG_DST_ADR 4

`define nl2_CFG_MST_NOC_ACE 0
`define nl2_CFG_MST_NOC_DVM 0
`define nl2_CFG_MST_NOC_EVICT 0

`define nl2_CFG_ARC_ABORT 0
`define nl2_CFG_AUX_SLAVE_PORT 0
`define nl2_CFG_IOMMU 0
`define nl2_CFG_PERF_CTR 0
`define nl2_CFG_QOS 0
                           


`define nl2_CLN_HAS_SOFT_RESET 0

`define nl2_CLN_SRCSYN_SUBCHAN_SIZE 10
`define nl2_CFG_HAVE_PHYCHAN_SRCSYN_SPLT 0




`define nl2_SCM_DBANK_CTRL_FIF_DEP 32
`define nl2_SCM_DBANK_CTRL_FIF_DEP_M1 31

`define nl2_SCM_DBANK_CTRL_FIF_CANDIDATES 4


`define nl2_SCM_TAG_LOOKUP_FIF_DEP 8
`define nl2_SCM_TAG_LOOKUP_FIF_DEP_M1 7
`define nl2_SCM_TAG_LOOKUP_FIF_CANDIDATES 4
`define nl2_SCM_TAG_LOOKUP_FIF_CANDIDATES_M1 3


`define nl2_SCM_TAG_LOOKUP_TAG_FIF_DEP 10
`define nl2_SCM_TAG_LOOKUP_TAG_FIF_DEP_M1 9

`define nl2_CLN_QOS_RDOM 8 


`define nl2_CLN_MST_QUEUE_FIF_DEP 32
`define nl2_CLN_MST_QUEUE_FIF_DEP_M1 31



`define nl2_CFG_TXC 32
`define nl2_CFG_TXC_M1 31
`define nl2_CFG_TXC_ADR 5
`define nl2_CFG_TXC_ADR_M1 4

`define nl2_CFG_TXB_PRIVATE 4

`define nl2_CFG_TXB 9
`define nl2_CFG_TXB_M1 8
`define nl2_CFG_TXB_ADR 4
`define nl2_CFG_TXB_ADR_M1 3

`define nl2_TXB_ID_NONE 15

`define nl2_TXB_ID_SCU 9

`define nl2_TXB_ID_NONBLK 9

`define nl2_TXB_ID_SLV 8  

  `define nl2_TXB_ID_BANK0 7  


  `define nl2_TXB_ID_NOC0 6  

`define nl2_TXB_ID_CCM 5  


`define nl2_CFG_TXB_RESERVABLE 6

`define nl2_CFG_DEBUG_OBSV 0

`define nl2_CFG_MST_NOC_COUNT 1
`define nl2_CFG_MST_CCM_COUNT 0
`define nl2_CFG_SLV_ARC_COUNT 0
`define nl2_CFG_SLV_DEV_COUNT 5
`define nl2_CFG_MST_PER_COUNT 0

`define nl2_CFG_ARC_COUNT 0

`define nl2_CFG_NOC_COUNT 1

`define nl2_CFG_DEV_COUNT 5

`define nl2_CFG_CCM_COUNT 0

`define nl2_CFG_PER_COUNT 0

`define nl2_CFG_DEV_TOTAL_COUNT 5

`define nl2_CFG_RPATH_NARROW_CHANNELS 2
`define nl2_CFG_RPATH_WIDE_CHANNELS 0

`define nl2_CFG_WPATH_NARROW_CHANNELS 2
`define nl2_CFG_WPATH_WIDE_CHANNELS 0

`define nl2_WIDTH_NARROW 128
`define nl2_WIDTH_NARROW_M1 127
`define nl2_WIDTH_NARROW_P1 129
`define nl2_WIDTH_NARROW_P2 130

`define nl2_WIDTH_WIDE 512
`define nl2_WIDTH_WIDE_M1 511
`define nl2_WIDTH_WIDE_P1 513
`define nl2_WIDTH_WIDE_P2 514

`define nl2_CLN_HAS_WIDE_PATH 1

`define nl2_CLN_WPATH_PCHAN_OUTREG  1
`define nl2_CLN_SRC2TXB_CMPL_OUTREG 1

`define nl2_TXB_SZ     2048
`define nl2_TXB_PTR_SZ 8

// How many error bits per TXB:
`define nl2_TXB_ERR_SIZE 4

`define nl2_CFG_SLV_ARC_CMD_ID_SIZE_MAX 0
`define nl2_CFG_SLV_ARC_WR_ID_SIZE_MAX 0

  

`define nl2_CFG_DEV0_CMD_FIFO_DEPTH 4  
`define nl2_CFG_DEV0_WR_FIFO_DEPTH 9  
`define nl2_CFG_DEV0_RD_FIFO_DEPTH 9  
`define nl2_CFG_DEV0_CMD_ID_SIZE 1  
`define nl2_CFG_DEV0_CMD_OUTSTANDING 8  
`define nl2_CFG_DEV0_DATA_SIZE 32 
`define nl2_CFG_DEV0_PROTOCOL 1
`define nl2_CFG_DEV0_ADDR_SIZE           40
`define nl2_CFG_DEV0_CTRL_CHANNELS       0
`define nl2_CFG_DEV0_MULTICAST           0
`define nl2_CFG_DEV0_SPLIT_CMD_RD_WR     0
`define nl2_CFG_DEV0_WR_ID_SIZE          1
`define nl2_CFG_DEV0_WRSP_FIFO_DEPTHS    4
`define nl2_CFG_DEV0_FAST_WRSP           0


     `define nl2_CFG_DEV0_PROTOCOL_ACEL
  

`define nl2_CFG_DEV1_CMD_FIFO_DEPTH 4  
`define nl2_CFG_DEV1_WR_FIFO_DEPTH 9  
`define nl2_CFG_DEV1_RD_FIFO_DEPTH 9  
`define nl2_CFG_DEV1_CMD_ID_SIZE 7  
`define nl2_CFG_DEV1_CMD_OUTSTANDING 32  
`define nl2_CFG_DEV1_DATA_SIZE 512 
`define nl2_CFG_DEV1_PROTOCOL 1
`define nl2_CFG_DEV1_ADDR_SIZE           40
`define nl2_CFG_DEV1_CTRL_CHANNELS       0
`define nl2_CFG_DEV1_MULTICAST           0
`define nl2_CFG_DEV1_SPLIT_CMD_RD_WR     0
`define nl2_CFG_DEV1_WR_ID_SIZE          7
`define nl2_CFG_DEV1_WRSP_FIFO_DEPTHS    4
`define nl2_CFG_DEV1_FAST_WRSP           0


     `define nl2_CFG_DEV1_PROTOCOL_ACEL
  

`define nl2_CFG_DEV2_CMD_FIFO_DEPTH 4  
`define nl2_CFG_DEV2_WR_FIFO_DEPTH 9  
`define nl2_CFG_DEV2_RD_FIFO_DEPTH 9  
`define nl2_CFG_DEV2_CMD_ID_SIZE 7  
`define nl2_CFG_DEV2_CMD_OUTSTANDING 32  
`define nl2_CFG_DEV2_DATA_SIZE 512 
`define nl2_CFG_DEV2_PROTOCOL 1
`define nl2_CFG_DEV2_ADDR_SIZE           40
`define nl2_CFG_DEV2_CTRL_CHANNELS       0
`define nl2_CFG_DEV2_MULTICAST           0
`define nl2_CFG_DEV2_SPLIT_CMD_RD_WR     0
`define nl2_CFG_DEV2_WR_ID_SIZE          7
`define nl2_CFG_DEV2_WRSP_FIFO_DEPTHS    4
`define nl2_CFG_DEV2_FAST_WRSP           0


     `define nl2_CFG_DEV2_PROTOCOL_ACEL
  

`define nl2_CFG_DEV3_CMD_FIFO_DEPTH 4  
`define nl2_CFG_DEV3_WR_FIFO_DEPTH 9  
`define nl2_CFG_DEV3_RD_FIFO_DEPTH 9  
`define nl2_CFG_DEV3_CMD_ID_SIZE 7  
`define nl2_CFG_DEV3_CMD_OUTSTANDING 32  
`define nl2_CFG_DEV3_DATA_SIZE 512 
`define nl2_CFG_DEV3_PROTOCOL 1
`define nl2_CFG_DEV3_ADDR_SIZE           40
`define nl2_CFG_DEV3_CTRL_CHANNELS       0
`define nl2_CFG_DEV3_MULTICAST           0
`define nl2_CFG_DEV3_SPLIT_CMD_RD_WR     0
`define nl2_CFG_DEV3_WR_ID_SIZE          7
`define nl2_CFG_DEV3_WRSP_FIFO_DEPTHS    4
`define nl2_CFG_DEV3_FAST_WRSP           0


     `define nl2_CFG_DEV3_PROTOCOL_ACEL
  

`define nl2_CFG_DEV4_CMD_FIFO_DEPTH 4  
`define nl2_CFG_DEV4_WR_FIFO_DEPTH 9  
`define nl2_CFG_DEV4_RD_FIFO_DEPTH 9  
`define nl2_CFG_DEV4_CMD_ID_SIZE 7  
`define nl2_CFG_DEV4_CMD_OUTSTANDING 32  
`define nl2_CFG_DEV4_DATA_SIZE 512 
`define nl2_CFG_DEV4_PROTOCOL 1
`define nl2_CFG_DEV4_ADDR_SIZE           40
`define nl2_CFG_DEV4_CTRL_CHANNELS       0
`define nl2_CFG_DEV4_MULTICAST           0
`define nl2_CFG_DEV4_SPLIT_CMD_RD_WR     0
`define nl2_CFG_DEV4_WR_ID_SIZE          7
`define nl2_CFG_DEV4_WRSP_FIFO_DEPTHS    4
`define nl2_CFG_DEV4_FAST_WRSP           0


     `define nl2_CFG_DEV4_PROTOCOL_ACEL
`define nl2_CFG_SLV_DEV_CMD_ID_SIZE_MAX 7
`define nl2_CFG_SLV_DEV_WR_ID_SIZE_MAX 7
`define nl2_CFG_NOF_SLV_DEV_PROTOCOL_IBP 0
`define nl2_CFG_NOF_SLV_DEV_PROTOCOL_ACEL 5
`define nl2_CFG_NOF_SLV_DEV_PROTOCOL_AXI4 0
`define nl2_CFG_NOF_SLV_DEV_PROTOCOL_APB 0

`define nl2_CFG_SLV_WR_ID_SIZE_MAX 7


// Shared Coherency Unit (SCU):
`define nl2_HAS_SCU       0
`define nl2_SNP_NO_SNP       4'b0000  //NoSnoop
`define nl2_SNP_RD_SHD       4'b1000  //ReadShared
`define nl2_SNP_RD_UNQ       4'b1001  //ReadUnique
`define nl2_SNP_CL_SHD       4'b1010  //CleanShared
`define nl2_SNP_CL_UNQ       4'b1011  //CleanUnique
`define nl2_SNP_RD_CPY       4'b1100  //ReadCopy
`define nl2_SNP_MK_UNQ       4'b1101  //MakeUnique
`define nl2_SNP_RD_SHO       4'b1110  //ReadSharedOnly
`define nl2_SNP_CL_INV       4'b1111  //CleanInvalid
`define nl2_SNP_MK_INV       4'b0001  //MakeInvalid
`define nl2_SNP_WR_CL        4'b0010  //WriteClean
`define nl2_SNP_WR_BCK       4'b0011  //WriteBack
`define nl2_SNP_EVT          4'b0100  //Evict
`define nl2_SNP_WR_UNQ       4'b0101  //WriteUnique

`define nl2_ARC_DC_ASSOC         2

`define nl2_ARC_DC_BSIZE         64
`define nl2_STB_IDX_BITS   5
`define nl2_WTB_ENTRIES     32
`define nl2_SCU_DC_HW_PREFETCH 0
`define nl2_ARC_PDB_ASSOC      2
`define nl2_ARC_PF_INDX_BITS   2
`define nl2_ARC_PF_TAG_BITS    43
`define nl2_ARC_PF_SET_INDX    8:7
`define nl2_ARC_PF_BANK_ID     6
`define nl2_ARC_PF_TAG_RANGE   51:9
`define nl2_ARC_PF_INDX_RANGE  3:0
`define nl2_ARC_PF_STAG_RANGE  44:0

`define nl2_CFG_SCM_INTERLEAVE 4096
`define nl2_CFG_SCM_CACHE_BLOCK_ADDR 6
`define nl2_CFG_SCM_CACHE_BLOCK_SIZE 64
`define nl2_CFG_SCM_CACHE_TAG_BANKS 8
`define nl2_CFG_SCM_CACHE_TAG_BANKS_ADDR 3
`define nl2_CFG_SCM_DATA_SIZE  2097152
`define nl2_CFG_SCM_CACHE_ASSOC 8
`define nl2_CFG_SCM_CACHE_MAX_SIZE 2097152
`define nl2_CFG_SCM_PREFETCH_STREAMS 0
`define nl2_CFG_SCM_RESET 1

`define nl2_CFG_SCM_ECC 1

`define nl2_SCM_WITH_ECC 1
`define nl2_BNK_SRAM_HAS_ECC 1
`define nl2_SCM_HAS_ECC 1
`define nl2_SCM_HAS_ECC_ADDR 0
`define nl2_DBNK_HAS_SCRUB 1
`define nl2_DBNK_GEN_CLK_REG 0

`define nl2_CFG_BNK_ADDR_SIZE 21
`define nl2_CFG_BNK_ADDR_SIZE_M1 20


`define nl2_CFG_SCM_DATA_BANK_SIZE 2097152
`define nl2_CFG_SCM_CACHE_SETS 4096
`define nl2_CFG_SCM_CACHE_SETS_ADDR 12
`define nl2_CFG_SCM_CACHE_SETS_ADDR_M1 11
`define nl2_CFG_SCM_WAYS 8


`define nl2_DBANK_DATA_WIDTH 512
`define nl2_DBANK_NUM_NARROW 4
`define nl2_DBANK_ECC_WIDTH  36
`define nl2_DBANK_ECC_WIDTH_NARROW 9
`define nl2_DBANK_RAW_WIDTH  548
`define nl2_DBANK_MASK_WIDTH_NARROW 17





`define nl2_TBANK_DATA_WIDTH 39
`define nl2_TBANK_ECC_WIDTH  0
`define nl2_TBANK_RAW_WIDTH  39
`define nl2_TBANK_DATA_WIDTH_M1 38
`define nl2_TBANK_ECC_WIDTH_M1  -1
`define nl2_TBANK_RAW_WIDTH_M1  38
`define nl2_TBANK_DATA_WIDTH_OUT 312
`define nl2_TBANK_ECC_WIDTH_OUT  0
`define nl2_TBANK_RAW_WIDTH_OUT  312
`define nl2_TBANK_DATA_WIDTH_OUT_M1 311
`define nl2_TBANK_ECC_WIDTH_OUT_M1  -1
`define nl2_TBANK_RAW_WIDTH_OUT_M1  311
`define nl2_CFG_SCM_CACHE_INDEX_ADDR 9
`define nl2_CFG_SCM_CACHE_INDEX_ADDR_M1 8
`define nl2_CFG_SCM_CACHE_TAG_ADDR 34

`define nl2_SRAM_BLOCK_ADDR_SIZE 14                     


`define nl2_CLN_SEQUENCER_N_CMD_IDS 4
`define nl2_CLN_SEQUENCER_CMD_ID_SIZE 2
`define nl2_CLN_SEQUENCER_CMD_OUTSTANDING 8

`define nl2_UAUX_START_ADDR       2147483648   
`define nl2_UAUX_END_ADDR         4294967295   

`define nl2_CFG_CMD_ID_SIZE_MAX 7
`define nl2_CFG_CMD_ID_SIZE_MAX_M1 6

`define nl2_CFG_SLV0_CMD_ID_SIZE 1
`define nl2_CFG_SLV1_CMD_ID_SIZE 7
`define nl2_CFG_SLV2_CMD_ID_SIZE 7
`define nl2_CFG_SLV3_CMD_ID_SIZE 7
`define nl2_CFG_SLV4_CMD_ID_SIZE 7

`define nl2_CFG_MST_NOC_RDID_SIZE 10

`define nl2_AT_LEAST_ONE_AXI_PORT
`define nl2_CFG_NOC0_CMD_FIFO_DEPTH 3  
`define nl2_CFG_NOC0_WR_FIFO_DEPTH 3  
`define nl2_CFG_NOC0_RD_FIFO_DEPTH 3  
`define nl2_CFG_NOC0_ADDR_SIZE 40  
`define nl2_CFG_NOC0_DATA_SIZE 64  
`define nl2_CFG_NOC0_OUTSTANDING 2  
`define nl2_CFG_NOC0_AXI_TYPE 1
`define nl2_CFG_NOC0_WRSP_FIFO_DEPTH 3
`define nl2_CFG_NOC0_CMD_ID_SIZE 2
`define nl2_CFG_NOC0_CTRL_CHANNELS 0
`define nl2_CFG_NOC0_N_STAGES 0
`define nl2_CFG_NOF_MST_NOC_PROTOCOL_AXI4 1
`define nl2_CFG_NOF_MST_NOC_PROTOCOL_IBP 0


//for dumping mst_switchbox parameter:
//MST_CMD_IDX_IN_MST_WR_ARRAY
// 0~CFG_MST_CCM_COUNT-1               : CCM
// CFG_MST_CCM_COUNT~MST_CCM_NOC_NUM-1 : NOC

    `define nl2_CFG_NOC0_CMD_IDX 0
    `define nl2_CFG_NOC0_SPLIT_CMD_RD_WR 1

//for dumping slv_switchbox parameter:
//CMD_IDX_IN_SLV_WR_ARRAY

  `define nl2_CFG_DEV0_NAME dev0 // for verify
  `define nl2_CFG_DEV0_CMD_IDX 0

  `define nl2_CFG_DEV1_NAME dev1 // for verify
  `define nl2_CFG_DEV1_CMD_IDX 0

  `define nl2_CFG_DEV2_NAME dev2 // for verify
  `define nl2_CFG_DEV2_CMD_IDX 0

  `define nl2_CFG_DEV3_NAME dev3 // for verify
  `define nl2_CFG_DEV3_CMD_IDX 0

  `define nl2_CFG_DEV4_NAME dev4 // for verify
  `define nl2_CFG_DEV4_CMD_IDX 0


`define nl2_CFG_MST_MAX_APT_ADR 2

`define nl2_PHASE_RD_START     0
`define nl2_PHASE_RD_DISPATCH  1
`define nl2_PHASE_RD_ACCESS    2
`define nl2_PHASE_RD_DELIVER   3

`define nl2_PHASE_WR_START     0
`define nl2_PHASE_WR_DATA      1
`define nl2_PHASE_WR_EARLY     2
`define nl2_PHASE_WR_DISPATCH  3
`define nl2_PHASE_WR_ACCESS    4
`define nl2_PHASE_WR_RESPONSE  5

`define nl2_NUM_ORD_RD_PHASES 4
`define nl2_NUM_ORD_WR_PHASES 6
`define nl2_ORD_PHASE_SIZE    3


`define nl2_CFG_NUM_PCHAN_WRITE 2
`define nl2_CFG_ADR_PCHAN_WRITE 1

`define nl2_CFG_NUM_PCHAN_READ 2
`define nl2_CFG_ADR_PCHAN_READ 1

`define nl2_CFG_NUM_CCHAN 1
`define nl2_CFG_ADR_CCHAN 1

`define nl2_CFG_MAX_PCHAN_PER_PARTITION 4

// Note that we can effectively only deal with 1, 2 or 4 pchans per partition.
`define nl2_CFG_NUM_PCHAN_READ_PARTITIONS 1
`define nl2_CFG_NUM_PCHAN_READ_PER_PARTITION 2

`define nl2_CFG_NUM_TXB_PER_PCHAN_READ 5

`define nl2_CFG_NUM_PCHAN_WRITE_PARTITIONS 1
`define nl2_CFG_NUM_PCHAN_WRITE_PER_PARTITION 2

`define nl2_CFG_NUM_SRC_PER_PARTITION 10
`define nl2_CFG_SRC_ADR_PER_PARTITION 4

`define nl2_CFG_NUM_DST_PER_PARTITION 10
`define nl2_CFG_DST_ADR_PER_PARTITION 4

////////////////////////////////////////////////////////////////////////////////

`define nl2_NUM_TXC_FOR_SLV0 8 
`define nl2_NUM_TXC_FOR_SLV1 32 
`define nl2_NUM_TXC_FOR_SLV2 32 
`define nl2_NUM_TXC_FOR_SLV3 32 
`define nl2_NUM_TXC_FOR_SLV4 32 
`define nl2_NUM_TXC_FOR_SLV5 8 

////////////////////////////////////////////////////////////////////////////////

// `CFG_TRACE_ROM_ID < `CFG_CDMA_MST_ID < `CFG_AUX_MST_ID < `CFG_MCIP_MST_ID
// master id of internal MCIP port:
`define nl2_CFG_MCIP_MST_ID  1

//if mcip ports need to be exposed to dev, turn this value to 1
`define nl2_MCIP_PORTS_EXPOSED_TO_DEV 0


// master id of internal trace port:
`define nl2_CFG_TRACE_ROM_ID  1


// master id of internal cDMA port:
`define nl2_CFG_CDMA_MST_ID  1


// master id of internal AUX port:
`define nl2_CFG_AUX_MST_ID  1

`define nl2_AUX_ADDR_SIZE          32
`define nl2_CLN_DMA_BUILD          8'hE6
`define nl2_CLN_ID_ADDR            32'h298
`define nl2_CLNR_ADDR              32'h640
`define nl2_CLNR_DATA              32'h641
`define nl2_CLNR_DATA_NXT          32'h642
`define nl2_GLOBAL_CLK_GATE_DIS    32'h9A9
`define nl2_CLNR_BCR_0             32'hF61
`define nl2_CLNR_BCR_1             32'hF62
`define nl2_CLNR_BCR_2             32'hF63
`define nl2_CLNR_SCM_BCR_0         32'hF64
`define nl2_CLNR_SCM_BCR_1         32'hF65

`define nl2_BCR_MST_NOC_0_PROT        1
`define nl2_BCR_MST_NOC_0_ADDR_SIZE   40
`define nl2_BCR_MST_NOC_0_DATA_SIZE   1
`define nl2_BCR_MST_NOC_0_OUTSTANDING 2
`define nl2_BCR_MST_NOC_0_RDID_SIZE   2
`define nl2_BCR_MST_NOC_0_APT         1



`define nl2_BCR_SLV_0_PROT             1
`define nl2_BCR_SLV_0_ADDR_SIZE        40 
`define nl2_BCR_SLV_0_DATA_SIZE        0
`define nl2_BCR_SLV_0_CMD_ID_SIZE      1
`define nl2_BCR_SLV_0_OUTSTANDING  8
`define nl2_BCR_SLV_0_DCACHE       0
`define nl2_BCR_SLV_0_CPU_DCACHE_ASSOC 0 
`define nl2_BCR_SLV_0_CPU_DCACHE_SIZE  0
`define nl2_BCR_SLV_0_MULTICAST        0
`define nl2_BCR_SLV_1_PROT             1
`define nl2_BCR_SLV_1_ADDR_SIZE        40 
`define nl2_BCR_SLV_1_DATA_SIZE        4
`define nl2_BCR_SLV_1_CMD_ID_SIZE      7
`define nl2_BCR_SLV_1_OUTSTANDING      0
`define nl2_BCR_SLV_1_DCACHE       0
`define nl2_BCR_SLV_1_CPU_DCACHE_ASSOC 0 
`define nl2_BCR_SLV_1_CPU_DCACHE_SIZE  0
`define nl2_BCR_SLV_1_MULTICAST        0
`define nl2_BCR_SLV_2_PROT             1
`define nl2_BCR_SLV_2_ADDR_SIZE        40 
`define nl2_BCR_SLV_2_DATA_SIZE        4
`define nl2_BCR_SLV_2_CMD_ID_SIZE      7
`define nl2_BCR_SLV_2_OUTSTANDING      0
`define nl2_BCR_SLV_2_DCACHE       0
`define nl2_BCR_SLV_2_CPU_DCACHE_ASSOC 0 
`define nl2_BCR_SLV_2_CPU_DCACHE_SIZE  0
`define nl2_BCR_SLV_2_MULTICAST        0
`define nl2_BCR_SLV_3_PROT             1
`define nl2_BCR_SLV_3_ADDR_SIZE        40 
`define nl2_BCR_SLV_3_DATA_SIZE        4
`define nl2_BCR_SLV_3_CMD_ID_SIZE      7
`define nl2_BCR_SLV_3_OUTSTANDING      0
`define nl2_BCR_SLV_3_DCACHE       0
`define nl2_BCR_SLV_3_CPU_DCACHE_ASSOC 0 
`define nl2_BCR_SLV_3_CPU_DCACHE_SIZE  0
`define nl2_BCR_SLV_3_MULTICAST        0
`define nl2_BCR_SLV_4_PROT             1
`define nl2_BCR_SLV_4_ADDR_SIZE        40 
`define nl2_BCR_SLV_4_DATA_SIZE        4
`define nl2_BCR_SLV_4_CMD_ID_SIZE      7
`define nl2_BCR_SLV_4_OUTSTANDING      0
`define nl2_BCR_SLV_4_DCACHE       0
`define nl2_BCR_SLV_4_CPU_DCACHE_ASSOC 0 
`define nl2_BCR_SLV_4_CPU_DCACHE_SIZE  0
`define nl2_BCR_SLV_4_MULTICAST        0
 
`define nl2_BCR_RPATH_NARROW_CHANNELS  2
`define nl2_BCR_RPATH_WIDE_CHANNELS    0
`define nl2_BCR_WPATH_NARROW_CHANNELS  2
`define nl2_BCR_WPATH_WIDE_CHANNELS    0
`define nl2_BCR_SCM_TAG_BANKS 3

`define nl2_BCR_SCM_DATA_BANKS 0


`define nl2_BCR_SCM_DATA_BANK_SIZE 11


`define nl2_BCR_SCM_CACHE_ASSOC 8

`define nl2_BCR_SCM_CACHE_SETS 12


`define nl2_BCR_SCM_DATA_SUB_BANKS 1


`define nl2_BCR_SCM_DATA_BANK_WIDTH 2


`define nl2_BCR_SCM_SUPERBLOCKS 0

`define nl2_BCR_SCM_DATA_BANK_SIZE_75 0


`define nl2_BCR_SCM_CACHE_BLOCK_SIZE 1
 //}


    //`let DEF_CLN_SCM0 = {2'd0,3'd0,2'd2,2'd1,5'd12,5'd11,3'd0, 3'd3, 1'd1, 4'd8, 1'd0,1'd0} 

`define nl2_DEF_CLN_BCR0 537034753
`define nl2_DEF_CLN_BCR1 525544
`define nl2_DEF_CLN_BCR2 8194
`define nl2_DEF_CLN_SCM0 78733792
`define nl2_DEF_CLN_SCM1 1
`define nl2_NO_CLN          0
// Select whether we use an IBPv3 interface or a physical channel to the ARC core:
`define nl2_CLN_ARC_PHYCHAN_INTERFACE 0


`define nl2_HAS_CLN_SFTY 0

`define nl2_CLN_CTRL_SAFETY 0
`define nl2_NPU_CTRL_SAFETY 0
`define nl2_HW_ERROR_INJECTION 0    
`define nl2_CLN_MONITORED_DEVICES 0    
`define nl2_CLN_MONITORED_DEVICES_PREFIX     "md"

`endif // CLN_DEFINES_INCLUDED_


