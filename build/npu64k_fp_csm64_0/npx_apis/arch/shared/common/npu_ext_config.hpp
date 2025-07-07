
#ifndef NPU_EXT_CONFIG_HPP_INCLUDED
#define NPU_EXT_CONFIG_HPP_INCLUDED


#define NPU_VER_MAJOR             1
#define NPU_VER_MINOR             2
#define NPU_VER                   18
#define NPU_VER_IS_VIC2_GA        1
#define NPU_VER_VIC2_LCA01        17
#define NPU_VER_VIC2_GA           18


//: NPU top
#define NPU_HAS_MMU                    1

#define NPU_EXPORT_CTI_IF              0

#define NPU_SLICE_NUM                  16

#define NPU_HAS_POWERDOMAINS           1


#define NPU_SAFETY_LEVEL               0

#define NPU_EXT_IRQ                    1

#define NPU_MEM_ECC                    1
#define NPU_MEM_ADDR_ECC               0
#define NPU_BUS_ECC                    0
#define NPU_BUS_ADDR_ECC               0
#define NPU_BUS_PARITY_MODE            1
#define NPU_CST_BUS_ECC_PER_32b        1
#define NPU_CST_BUS_ECC_PER_64b        2

#define NPU_DEV_ARC_HAS_WDT           1

#define NPU_E2E_SECDED                0

//: FIXME: this should be guarded by safety level
#define NPU_MEM_SECDED                1

#define NPU_MEM_EXPORT_ERR_PORT       1



//: npu l1core
#define NPU_HAS_FLOAT                  1
#define NPU_SLICE_FLOAT_EN             16777215

#define NPU_SLICE_MAC                 4096

#define NPU_SLICE_MEM                 2

#define NPU_MPY_IMPL                  1

#define NPU_DEV_GTOA_HAS_ALU1         1
#define ACT_HAS_ALU1                  1


#define NPU_DEV_GTOA_HAS_STR0         1
#define NPU_GTOA_HAS_STR0             1


//: NPU l2core.cln
#define NPU_CSM_SIZE                  67108864
#define NPU_CSM_SIZE_PER_GRP          16777216
#define NPU_CSM_MASK                  67108863
#define NPU_CSM_BANKS                 32
#define NPU_CSM_BANKS_PER_GRP         8
#define NPU_CSM_RAM_GEN_CLK_REG       0
#define NPU_CSM_BW                    64
#define NPU_L2_PERIPH_SIZE            4194304
#define NPU_L2_PERIPH_MASK            4194303

//: NPU l2core.stu
#define NPU_STU_CHAN_NUM              8
#define NPU_STU_HAS_CDC               1

#define NPU_REMAP_BRIDGE              1

//: npu l2core.arc_trace
// NPU_ARC_TRACE
#define NPU_ARC_TRACE                 1
#define RTT_CORESIGHT_OPTION          1

#define RTT_ATB_RATIO                 2

#define ATDATA_WIDTH                  64

#define SWE_ATDATA_WIDTH              64

#define HAS_NEXUS_IF                  0

#define HAS_ON_CHIP_MEM               0

#define NEXUS_DATA_WDT                1

#define RTT_SYTM_OPTION               0

#define RTT_SYTM_CTR_OPTION           0

#define RTT_POWER_DOMAINS             0

#define EXTERNAL_TRACE_IF             0

#define RTT_USING_AHB                 0

#define RTT_USING_AXI                 1

#define ARC_RTT_CORE_NUM              0

#define ARC_RTT_MEM_BUS_WIDTH         64


//: arcsync
#define ARCSYNC_TYPE_CL_NPUSLICE      0
#define ARCSYNC_TYPE_CL_NPX           0
#define ARCSYNC_TYPE_CL_VPX           1
#define ARCSYNC_TYPE_CL_HOST          2
#define ARCSYNC_NUM_CLUSTER           3
#define ARCSYNC_MAX_CORES_PER_CL      32
#define ARCSYNC_NUM_CORE_CL0          18
#define ARCSYNC_TYPE_CL0              0
#define ARCSYNC_ITF_CL0               0
#define ARCSYNC_ITF_STUB_CL0          0
#define ARCSYNC_PFX_CL0               
#define ARCSYNC_NUM_CORE_CL1          4
#define ARCSYNC_TYPE_CL1              1
#define ARCSYNC_ITF_CL1               1
#define ARCSYNC_ITF_STUB_CL1          1
#define ARCSYNC_PFX_CL1               v0
#define ARCSYNC_NUM_CORE_CL2          1
#define ARCSYNC_TYPE_CL2              2
#define ARCSYNC_ITF_CL2               1
#define ARCSYNC_ITF_STUB_CL2          1
#define ARCSYNC_PFX_CL2               h0
#define ARCSYNC_NUM_CORE_CL3          0
#define ARCSYNC_TYPE_CL3              0
#define ARCSYNC_ITF_CL3               0
#define ARCSYNC_ITF_STUB_CL3          0
#define ARCSYNC_PFX_CL3               
#define ARCSYNC_NUM_CORE_CL4          0
#define ARCSYNC_TYPE_CL4              0
#define ARCSYNC_ITF_CL4               0
#define ARCSYNC_ITF_STUB_CL4          0
#define ARCSYNC_PFX_CL4               
#define ARCSYNC_NUM_CORE_CL5          0
#define ARCSYNC_TYPE_CL5              0
#define ARCSYNC_ITF_CL5               0
#define ARCSYNC_ITF_STUB_CL5          0
#define ARCSYNC_PFX_CL5               
#define ARCSYNC_NUM_CORE_CL6          0
#define ARCSYNC_TYPE_CL6              0
#define ARCSYNC_ITF_CL6               0
#define ARCSYNC_ITF_STUB_CL6          0
#define ARCSYNC_PFX_CL6               
#define ARCSYNC_NUM_CORE_CL7          0
#define ARCSYNC_TYPE_CL7              0
#define ARCSYNC_ITF_CL7               0
#define ARCSYNC_ITF_STUB_CL7          0
#define ARCSYNC_PFX_CL7               
#define ARCSYNC_NUM_ATOMIC_CNT        64
#define ARCSYNC_VIRT_MACHINES         8
#define ARCSYNC_NUM_IRQ_PER_CORE      1
#define ARCSYNC_NUM_EVT_PER_CORE      1
#define ARCSYNC_NUM_IRQ_PER_VPROC     1
#define ARCSYNC_NUM_EVT_PER_VPROC     1
#define ARCSYNC_VIRT_PROC             3
  #define ARCSYNC_HAS_ATOMIC_CNT       1

#define ARCSYNC_NUM_GFRC              1
#define ARCSYNC_ATOMIC_CNT_WIDTH      8
#define ARCSYNC_HAS_PMU               1
#define ARCSYNC_PMU_RESET_PMODE       1
#define ARCSYNC_CORE_CLK_ENA_RST      0
#define ARCSYNC_PDM_HAS_FG            1
#define ARCSYNC_PMU_VPX_MODE          1
#define ARCSYNC_BASE_ADDR             868352
#define ARCSYNC_HAS_CDC               1



//:======================================================
// NOTE: following options are for internal useage only
#define NPU_SYS_HAS_VPX               0
#define NPU_SYS_HAS_HS                0

#define NPU_DEV_CFG_NU4K5             0

#define NPU_DEV_ARC_SAFETY_LEVEL  0

#define NPU_DEV_ARC_MEM_ECC  1

#define NPU_DEV_CFG_HOST_AXI_INITIATORS  1

#define NPU_L0_GATE_EN        0
#define NPU_L0_GATE_THRESH    1024

#define NPU_ODMA_BUFFER_SIZE  1024
#define NPU_IDMA_BUFFER_SIZE  1024
#define NPU_STU_BUFFER_SIZE   2048
#define NPU_REORDER_BUFFER_SIZE  0
#define NPU_DISABLE_DMA_CPS   1
#define NPU_DISABLE_DMA_PLN   1

#define NPU_SLICE_AM_SIZE  128
#define NPU_SLICE_VM_SIZE  512



#define NPU_RTL_SIM_VCS           0
#define NPU_RTL_SIM_XC            1
#define NPU_RTL_SIM_MODELSIM      2


#define NPU_HAS_RTT               0
#define NPU_RTT_CORESIGHT         1
#define NPU_NUM_GRP          4
#define NPU_NUM_SLC_PER_GRP  4
#define NPU_NUM_STU_PER_GRP  2

#define NPU_SLICE_ISIZE  16
#define NPU_SLICE_DSIZE  8
#define NPU_SLICE_VSIZE  8

#define RTLA_TECH  07

#define NPU_HAS_ARCH_CGATE       0

#define NPU_CLK_ENA_RST          0

#define NPU_CTRL_SAFETY               0
#define CLN_MONITORED_DEVICES         0
#define CLN_MONITORED_DEVICES_PREFIX  "md"
#define HW_ERROR_INJECTION            0
#define NPU_MAX_INJ_MASK_MSB          0
#define NPU_MIN_INJ_MASK_MSB          0

#endif //NPU_EXT_CONFIG_HPP_INCLUDED

#define NPU_HAS_L2ARC           1

#define DUO_L2ARC               1

#define NPU_VMIDW               64

#define NPU_AXI_DATA_WIDTH      512

#define NPU_RDF_HIER_LEVEL    2

#define NPU_EXPORT_RAM_PG     1
#define NPU_MEM_POWER_DOMAINS  1

#define NPU_PD_NPU_CORE_WRAP           0

#define NPU_GTOA_IO_FP_SCALE   1

#define NPU_HAS_JTAG   0

#define NPU_CONV_HAS_FM8CF16  1
#define NPU_CONV_HAS_FM16CF8  1

#define NPU_ARC_DCCM_BASE  1879048192

#define ARCHITT_BUILD  0
