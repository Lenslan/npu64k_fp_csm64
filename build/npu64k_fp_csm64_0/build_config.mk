# From npu_ext_config.vpp - start



 NPU_VER_MAJOR           =  1
 NPU_VER_MINOR           =  2
 NPU_VER                 =  18
 NPU_VER_IS_VIC2_GA      =  1
 NPU_VER_VIC2_LCA01      =  17
 NPU_VER_VIC2_GA         =  18


#: NPU top
 NPU_HAS_MMU                  =  1

 NPU_EXPORT_CTI_IF            =  0

 NPU_SLICE_NUM                =  16

 NPU_HAS_POWERDOMAINS         =  0


 NPU_SAFETY_LEVEL             =  0

 NPU_EXT_IRQ                  =  1

 NPU_MEM_ECC                  =  1
 NPU_MEM_ADDR_ECC             =  0
 NPU_BUS_ECC                  =  0
 NPU_BUS_ADDR_ECC             =  0
 NPU_BUS_PARITY_MODE          =  1
 NPU_CST_BUS_ECC_PER_32b      =  1
 NPU_CST_BUS_ECC_PER_64b      =  2

 NPU_DEV_ARC_HAS_WDT          = 1

 NPU_E2E_SECDED               = 0

#: FIXME: this should be guarded by safety level
 NPU_MEM_SECDED               = 1

 NPU_MEM_EXPORT_ERR_PORT      = 1



#: npu l1core
 NPU_HAS_FLOAT                =  1
 NPU_SLICE_FLOAT_EN           =  16777215

 NPU_SLICE_MAC                = 4096

 NPU_SLICE_MEM                = 2

 NPU_MPY_IMPL                 = 1

 NPU_DEV_GTOA_HAS_ALU1        = 1
 ACT_HAS_ALU1                 = 1


 NPU_DEV_GTOA_HAS_STR0        = 1
 NPU_GTOA_HAS_STR0            = 1


#: NPU l2core.cln
 NPU_CSM_SIZE                 = 67108864
 NPU_CSM_SIZE_PER_GRP         = 16777216
 NPU_CSM_MASK                 = 67108863
 NPU_CSM_BANKS                = 32
 NPU_CSM_BANKS_PER_GRP        = 8
 NPU_CSM_RAM_GEN_CLK_REG      = 0
 NPU_CSM_BW                   = 64
 NPU_L2_PERIPH_SIZE           = 4194304
 NPU_L2_PERIPH_MASK           = 4194303

#: NPU l2core.stu
 NPU_STU_CHAN_NUM             = 8
 NPU_STU_HAS_CDC              = 1

 NPU_REMAP_BRIDGE             = 1

#: npu l2core.arc_trace
# NPU_ARC_TRACE
 NPU_ARC_TRACE                = 1
 RTT_CORESIGHT_OPTION         = 1

 RTT_ATB_RATIO                = 2

 ATDATA_WIDTH                 = 64

 SWE_ATDATA_WIDTH             = 64

 HAS_NEXUS_IF                 = 0

 HAS_ON_CHIP_MEM              = 0

 NEXUS_DATA_WDT               = 1

 RTT_SYTM_OPTION              = 0

 RTT_SYTM_CTR_OPTION          = 0

 RTT_POWER_DOMAINS            = 0

 EXTERNAL_TRACE_IF            = 0

 RTT_USING_AHB                = 0

 RTT_USING_AXI                = 1

 ARC_RTT_CORE_NUM             = 0

 ARC_RTT_MEM_BUS_WIDTH        = 64





#:======================================================
# NOTE: following options are for internal useage only
 NPU_SYS_HAS_VPX              = 0
 NPU_SYS_HAS_HS               = 0

 NPU_DEV_CFG_NU4K5            = 0

 NPU_DEV_ARC_SAFETY_LEVEL = 0

 NPU_DEV_ARC_MEM_ECC = 1

 NPU_DEV_CFG_HOST_AXI_INITIATORS = 1

 NPU_L0_GATE_EN       = 0
 NPU_L0_GATE_THRESH   = 1024

 NPU_ODMA_BUFFER_SIZE = 1024
 NPU_IDMA_BUFFER_SIZE = 1024
 NPU_STU_BUFFER_SIZE  = 2048
 NPU_REORDER_BUFFER_SIZE = 0
 NPU_DISABLE_DMA_CPS  = 1
 NPU_DISABLE_DMA_PLN  = 1

 NPU_SLICE_AM_SIZE = 128
 NPU_SLICE_VM_SIZE = 512


 NPU_CFG                  = npu64k_fp_csm64_0
 NPU_ARC_CFG              = npu_arc_se_ad1k_N64_mem_ecc_pg1
 NPU_ARC_RDF              = RDF_ts07_SVT_LVT_area_pg1

 NPU_RTL_SIM_VCS          = 0
 NPU_RTL_SIM_XC           = 1
 NPU_RTL_SIM_MODELSIM     = 2

 NPU_ARC_DEV         = 0

 NPU_HAS_RTT              = 0
 NPU_RTT_CORESIGHT        = 1
 NPU_NUM_GRP         = 4
 NPU_NUM_SLC_PER_GRP = 4
 NPU_NUM_STU_PER_GRP = 2

 NPU_SLICE_ISIZE = 16
 NPU_SLICE_DSIZE = 8
 NPU_SLICE_VSIZE = 8

 RTLA_TECH = 07

 NPU_HAS_ARCH_CGATE     =  0

 NPU_CLK_ENA_RST        =  0

 NPU_CTRL_SAFETY              = 0
 CLN_MONITORED_DEVICES        = 0
 CLN_MONITORED_DEVICES_PREFIX = "md"
 HW_ERROR_INJECTION           = 0
 NPU_MAX_INJ_MASK_MSB         = 0
 NPU_MIN_INJ_MASK_MSB         = 0


 NPU_HAS_L2ARC          = 1

 DUO_L2ARC              = 1

 NPU_VMIDW              = 64

 NPU_AXI_DATA_WIDTH     = 512

 NPU_RDF_HIER_LEVEL   = 2

 NPU_EXPORT_RAM_PG    = 1
 NPU_MEM_POWER_DOMAINS = 1

 NPU_PD_NPU_CORE_WRAP          = 0

 NPU_GTOA_IO_FP_SCALE  = 1

 NPU_HAS_JTAG  = 0

 NPU_CONV_HAS_FM8CF16 = 1
 NPU_CONV_HAS_FM16CF8 = 1

 NPU_ARC_DCCM_BASE = 1879048192

 ARCHITT_BUILD = 0
# From npu_ext_config.vpp - end

NCONFDIR       = ${NPU_HOME}/config
NCONFIG        = npu64k_fp_csm64_0
BUILD_PRJ      = ${NPU_HOME}/build
NPRJ_CONFIG    = $(BUILD_PRJ)/config
NPRJ_SRC       = $(BUILD_PRJ)/verilog
NPRJ_RTL       = $(NPRJ_SRC)/RTL
NPRJ_TB        = $(BUILD_PRJ)/tb
NPRJ_SIM       = $(BUILD_PRJ)/sim
NPRJ_SYN       = $(BUILD_PRJ)/syn
NPRJ_TESTS     = $(BUILD_PRJ)/tests
NPRJ_TAPI      = $(BUILD_PRJ)/npx_apis
LOGD           = $(BUILD_PRJ)/logs
BSIZE          = $(NPU_SLICE_DSIZE)
VSIZE          = $(NPU_SLICE_VSIZE)
ISIZE          = $(NPU_SLICE_ISIZE)
NPU_SFTY       = $(NPU_SAFETY_LEVEL)
MEM_ECC        = $(NPU_MEM_ECC)
MEM_ADDR_ECC   = $(NPU_MEM_ADDR_ECC)
BUS_ECC        = $(NPU_BUS_ECC)

TB_DPI_ARC_EN ?= 0
TB_CCT_SYS    ?= 1
TB_CCT_PWR    ?= 1
TB_CCT_ADV    ?= 0

export NCONFIG BUILD_PRJ NPRJ_CONFIG NPRJ_SRC NPRJ_TB NPU_CLN_FPGA_SRAM
export BSIZE ISIZE VSIZE
export RTLA_TECH NPU_HAS_L2ARC
export MEM_ECC MEM_ADDR_ECC BUS_ECC NPU_SFTY

