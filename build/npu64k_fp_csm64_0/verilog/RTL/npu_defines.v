/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */


`ifndef NPU_DEFINES_V_INCLUDED
`define NPU_DEFINES_V_INCLUDED








`define NPU_VER_MAJOR             1
`define NPU_VER_MINOR             2
`define NPU_VER                   18
`define NPU_VER_IS_VIC2_GA        1
`define NPU_VER_VIC2_LCA01        17
`define NPU_VER_VIC2_GA           18


//: NPU top
`define NPU_HAS_MMU                    1

`define NPU_EXPORT_CTI_IF              0

`define NPU_SLICE_NUM                  16

`define NPU_HAS_POWERDOMAINS           1

`define NPU_AXI_INITIATORS             5

`define NPU_AXI_TARGETS                1

`define NPU_AXI_TARGET_ID_WIDTH        16

`define NPU_SAFETY_LEVEL               0

`define NPU_EXT_IRQ                    1

`define NPU_MEM_ECC                    1
`define NPU_MEM_ADDR_ECC               0
`define NPU_BUS_ECC                    0
`define NPU_BUS_ADDR_ECC               0
`define NPU_BUS_PARITY_MODE            1
`define NPU_CST_BUS_ECC_PER_32b        1
`define NPU_CST_BUS_ECC_PER_64b        2
`define NPU_ECC_PIPELINE              0

`define NPU_DEV_ARC_HAS_WDT           1

`define NPU_E2E_SECDED                0

//: FIXME: this should be guarded by safety level
`define NPU_MEM_SECDED                1

`define NPU_MEM_EXPORT_ERR_PORT       1



//: npu l1core
`define NPU_HAS_FLOAT                  1
`define NPU_SLICE_FLOAT_EN             16777215

`define NPU_SLICE_MAC                 4096

`define NPU_SLICE_MEM                 2

`define NPU_MPY_IMPL                  1

`define NPU_DEV_GTOA_HAS_ALU1         1
`define ACT_HAS_ALU1                  1

`define NPU_SLICE_VM_BANKS            32

`define NPU_SLICE_AXI_HAS_UITF        1

`define NPU_TOP_AXI_HAS_UITF          0

`define NPU_DEV_GTOA_RF_MUX_ORBUS     1
`define NPU_GTOA_RF_MUX_ORBUS         1

`define NPU_DEV_GTOA_HAS_STR0         1
`define NPU_GTOA_HAS_STR0             1


//: NPU l2core.cln
`define NPU_CSM_SIZE                  67108864
`define NPU_CSM_SIZE_PER_GRP          16777216
`define NPU_CSM_MASK                  67108863
`define NPU_CSM_BANKS                 32
`define NPU_CSM_BANKS_PER_GRP         8
`define NPU_CSM_RAM_GEN_CLK_REG       0
`define NPU_CSM_BW                    64
`define NPU_CLN_PHYCHAN               3
`define NPU_CLN_SLV_DEV_FAST_WRSP     0
`define NPU_CLN_PERF_OPT              0
`define NPU_L2_PERIPH_SIZE            4194304
`define NPU_L2_PERIPH_MASK            4194303

//: NPU l2core.stu
`define NPU_STU_CHAN_NUM              8
`define NPU_STU_HAS_CDC               1

`define NPU_REMAP_BRIDGE              1

//: npu l2core.arc_trace
// NPU_ARC_TRACE
`define NPU_ARC_TRACE                 1
`define RTT_CORESIGHT_OPTION          1

`define RTT_ATB_RATIO                 2

`define ATDATA_WIDTH                  64

`define SWE_ATDATA_WIDTH              64

`define HAS_NEXUS_IF                  0

`define HAS_ON_CHIP_MEM               0

`define NEXUS_DATA_WDT                1

`define RTT_SYTM_OPTION               0

`define RTT_SYTM_CTR_OPTION           0

`define RTT_POWER_DOMAINS             0

`define EXTERNAL_TRACE_IF             0

`define RTT_USING_AHB                 0

`define RTT_USING_AXI                 1

`define ARC_RTT_CORE_NUM              0

`define ARC_RTT_MEM_BUS_WIDTH         64





//:======================================================
// NOTE: following options are for internal useage only
`define NPU_SYS_HAS_VPX               0
`define NPU_SYS_HAS_HS                0

`define NPU_DEV_CFG_NU4K5             0

`define NPU_DEV_ARC_SAFETY_LEVEL  0

`define NPU_DEV_ARC_MEM_ECC  1

`define NPU_DEV_CFG_HOST_AXI_INITIATORS  1

`define NPU_L0_GATE_EN        0
`define NPU_L0_GATE_THRESH    1024

`define NPU_ODMA_BUFFER_SIZE  1024
`define NPU_IDMA_BUFFER_SIZE  1024
`define NPU_STU_BUFFER_SIZE   2048
`define NPU_REORDER_BUFFER_SIZE  0
`define NPU_DISABLE_DMA_CPS   1
`define NPU_DISABLE_DMA_PLN   1

`define NPU_SLICE_AM_SIZE  128
`define NPU_SLICE_VM_SIZE  512

`define NPU_REPLACE_CLKGATE       1
`define Mem_npu_vec_bank          mem_ts07n0g41p11sacrl256sa24_1024x144_bwe1_bk2_cm2_cd1_pg1_b0r0_wrapper
`define Mem_npu_acc_bank          mem_ts07n0g41p11sacrl256sa24_128x288_bwe1_bk1_cm1_cd1_pg1_b0r0_wrapper
`define CellLibraryClockGate      HDBSVT08_CKGTPLT_V5Y2_1
`define CellLibrarySync2Gate      `CELLLIBRARYSYNC2GATE
`define CellLibrarySync3Gate      `CELLLIBRARYSYNC3GATE


`define NPU_RTL_SIM_VCS           0
`define NPU_RTL_SIM_XC            1
`define NPU_RTL_SIM_MODELSIM      2

`define NPU_ARC_DEV          0

`define NPU_HAS_RTT               0
`define NPU_RTT_CORESIGHT         1
`define NPU_NUM_GRP          4
`define NPU_NUM_SLC_PER_GRP  4
`define NPU_NUM_STU_PER_GRP  2

`define NPU_SLICE_ISIZE  16
`define NPU_SLICE_DSIZE  8
`define NPU_SLICE_VSIZE  8

`define RTLA_TECH  07

`define NPU_HAS_ARCH_CGATE       0

`define NPU_CLK_ENA_RST          0

`define NPU_CTRL_SAFETY               0
`define CLN_MONITORED_DEVICES         0
`define CLN_MONITORED_DEVICES_PREFIX  "md"
`define HW_ERROR_INJECTION            0
`define NPU_MAX_INJ_MASK_MSB          0
`define NPU_MIN_INJ_MASK_MSB          0


`define NPU_HAS_L2ARC           1

`define DUO_L2ARC               1

`define NPU_VMIDW               64

`define NPU_AXI_DATA_WIDTH      512

`define NPU_RDF_HIER_LEVEL    2

`define NPU_EXPORT_RAM_PG     1
`define NPU_MEM_POWER_DOMAINS  1

`define NPU_PD_NPU_CORE_WRAP           0

`define NPU_GTOA_IO_FP_SCALE   1

`define NPU_HAS_JTAG   0

`define NPU_CONV_HAS_FM8CF16  1
`define NPU_CONV_HAS_FM16CF8  1

`define NPU_ARC_DCCM_BASE  1879048192

`define ARCHITT_BUILD  0



// Version of the NPU and CNN:
// 1:  EV5x / CNN 1.0
// 2:  EV6x 2.00a Montreal / CNN v2.0 iplib
// 3:  EV6x 2.10a Tofino / CNN v3.0 iplib
// 4:  Bug fix for the DMA compression (2.12 = Tofino + fix for 9001328561)
// 5:  EV6x 2.20a Toronto / CNN v3.1 iplib
// 6:  EV7x 3.00a Vancouver / CNN v3.2 iplib
// 7 to 15: Reserved for future EV/CNN/DNN releases
//
// 16: NPX6 release 1.00a (NPU Victoria)
// 17: NPX release 2.00a-lca01 (Victoria2 LCA)
// 18: NPX release 2.00a (Victoria2 GA)
//
`define NPU_VERSION  18

`define NPU_HAS_SFTY_BCR             0
`define NPU_MEM_ECC                  1
`define NPU_SLICE_NUM                16
`define NPU_SAFETY_LEVEL             0

// L2 controller presence
`define NPU_HAS_L2_CTRL              1

// Always true for Victoria 1 and Victoria 2
`define NPU_HAS_L2_CTRL             1
`define NPU_HAS_L1_CTRL              1
`define NPU_HAS_EVT_MGT              1

// Calculated values for the STU BCR
`define NPU_STU_BCR          3

// Calculated values for the MAC BCR
`define NPU_MAC_BCR   4

//Size of the Accumulator Memory in each of the NPU slices
//    0:   Reserved
//    1:   32KB  AM per NPU slice
//    2:   64KB  AM per NPU slice
//    3:   128KB AM per NPU slice
//    4:   256KB AM per NPU slice
//    5-7: Reserved
//Size of the Vector Memory in each of the NPU slices
//    0:   Reserved
//    1:   128KB VM per NPU slice
//    2:   256KB VM per NPU slice
//    3:   512KB VM per NPU slice
//    4:   1MB   VM per NPU slice
//    5-7: Reserved
`define NPU_AM_SIZE         131072
`define NPU_AM_SIZE_BCR     3
`define NPU_VM_SIZE         524288
`define NPU_VM_SIZE_BCR     3



// --- Connections to MSS

`define NPU_BUS_ECC_ALL_ZERO_ALL_ONE 1


// NPU master port 0 for L2NoC
`define NPU_MST0_PREF          npu_mst0_axi_
`define NPU_MST0_SUPPORT_RATIO 0
`define NPU_MST0_CLK_NAME      clk
`define NPU_MST0_CLK_EN
`define NPU_MST0_PROT          axi4
`define NPU_MST0_DATA_WIDTH    64
`define NPU_MST0_ADDR_WIDTH    40
`define NPU_MST0_RW            rw
`define NPU_MST0_EXCL          1
`define NPU_MST0_LOCK          1
`define NPU_MST0_ID_WIDTH      5
`define NPU_MST0_BUS_ECC       0
`define NPU_MST0_BUS_ECC_PROT  32
`define NPU_MST0_BUS_PARITY    1

// NPU master port 1
`define NPU_MST1_PREF          npu_mst1_axi_
`define NPU_MST1_SUPPORT_RATIO 0
`define NPU_MST1_CLK_NAME      clk
`define NPU_MST1_CLK_EN
`define NPU_MST1_PROT          axi4
`define NPU_MST1_DATA_WIDTH    512
`define NPU_MST1_ADDR_WIDTH    40
`define NPU_MST1_RW            rw
`define NPU_MST1_EXCL          1
`define NPU_MST1_LOCK          1
`define NPU_MST1_ID_WIDTH      5
`define NPU_MST1_BUS_ECC       0
`define NPU_MST1_BUS_ECC_PROT  32
`define NPU_MST1_BUS_PARITY    1
// NPU master port 2
`define NPU_MST2_PREF          npu_mst2_axi_
`define NPU_MST2_SUPPORT_RATIO 0
`define NPU_MST2_CLK_NAME      clk
`define NPU_MST2_CLK_EN
`define NPU_MST2_PROT          axi4
`define NPU_MST2_DATA_WIDTH    512
`define NPU_MST2_ADDR_WIDTH    40
`define NPU_MST2_RW            rw
`define NPU_MST2_EXCL          1
`define NPU_MST2_LOCK          1
`define NPU_MST2_ID_WIDTH      5
`define NPU_MST2_BUS_ECC       0
`define NPU_MST2_BUS_ECC_PROT  32
`define NPU_MST2_BUS_PARITY    1
// NPU master port 3
`define NPU_MST3_PREF          npu_mst3_axi_
`define NPU_MST3_SUPPORT_RATIO 0
`define NPU_MST3_CLK_NAME      clk
`define NPU_MST3_CLK_EN
`define NPU_MST3_PROT          axi4
`define NPU_MST3_DATA_WIDTH    512
`define NPU_MST3_ADDR_WIDTH    40
`define NPU_MST3_RW            rw
`define NPU_MST3_EXCL          1
`define NPU_MST3_LOCK          1
`define NPU_MST3_ID_WIDTH      5
`define NPU_MST3_BUS_ECC       0
`define NPU_MST3_BUS_ECC_PROT  32
`define NPU_MST3_BUS_PARITY    1
// NPU master port 4
`define NPU_MST4_PREF          npu_mst4_axi_
`define NPU_MST4_SUPPORT_RATIO 0
`define NPU_MST4_CLK_NAME      clk
`define NPU_MST4_CLK_EN
`define NPU_MST4_PROT          axi4
`define NPU_MST4_DATA_WIDTH    512
`define NPU_MST4_ADDR_WIDTH    40
`define NPU_MST4_RW            rw
`define NPU_MST4_EXCL          1
`define NPU_MST4_LOCK          1
`define NPU_MST4_ID_WIDTH      5
`define NPU_MST4_BUS_ECC       0
`define NPU_MST4_BUS_ECC_PROT  32
`define NPU_MST4_BUS_PARITY    1

// NPU DMI port 0
`define NPU_SLV0_PREF             npu_dmi0_axi_
`define NPU_SLV0_PROT             axi4
`define NPU_SLV0_SUPPORT_RATIO    0
`define NPU_SLV0_CLK_NAME         clk
`define NPU_SLV0_CLK_EN
`define NPU_SLV0_DATA_WIDTH       512
`define NPU_SLV0_ADDR_WIDTH       40
`define NPU_SLV0_RESP             1
`define NPU_SLV0_ID_WIDTH         16
`define NPU_SLV0_REG_W            0
`define NPU_SLV0_NUM_REG          1
//' 0xe0000000, 256MB
`define NPU_SLV0_REG0_APER_WIDTH  28
`define NPU_SLV0_REG0_BASE_ADDR   917504
`define NPU_SLV0_BUS_ECC          0
`define NPU_SLV0_BUS_ECC_PROT     32
`define NPU_SLV0_BUS_PARITY       1

// NPU Cfg DMI port SLV1
`define NPU_SLV1_PREF             npu_cfg_axi_
`define NPU_SLV1_PROT             axi4
`define NPU_SLV1_SUPPORT_RATIO    0
`define NPU_SLV1_CLK_NAME         clk
`define NPU_SLV1_CLK_EN
`define NPU_SLV1_DATA_WIDTH       32
`define NPU_SLV1_ADDR_WIDTH       40
`define NPU_SLV1_RESP             1
`define NPU_SLV1_ID_WIDTH         16
`define NPU_SLV1_REG_W            0
// config base at 0x
`define NPU_SLV1_NUM_REG          1
`define NPU_SLV1_REG0_APER_WIDTH  20
`define NPU_SLV1_REG0_BASE_ADDR   983040
`define NPU_SLV1_BUS_ECC          0
`define NPU_SLV1_BUS_ECC_PROT     32
`define NPU_SLV1_BUS_PARITY       1

// ARCSync DMI port SLV2
`define NPU_SLV2_PREF             arcsync_axi_
`define NPU_SLV2_PROT             axi4
`define NPU_SLV2_SUPPORT_RATIO    0
`define NPU_SLV2_CLK_NAME         clk
`define NPU_SLV2_CLK_EN
`define NPU_SLV2_ADDR_WIDTH       40
`define NPU_SLV2_DATA_WIDTH       64
`define NPU_SLV2_RESP             1
`define NPU_SLV2_ID_WIDTH         16
`define NPU_SLV2_REG_W            0
`define NPU_SLV2_NUM_REG          1
`define NPU_SLV2_REG0_APER_WIDTH  24
`define NPU_SLV2_REG0_BASE_ADDR   868352
`define NPU_SLV2_BUS_ECC          0
`define NPU_SLV2_BUS_ECC_PROT     32
`define NPU_SLV2_BUS_PARITY       1


// Host master port 0
`define NPU_MST5_PREF          host_axi_
`define NPU_MST5_SUPPORT_RATIO 1
`define NPU_MST5_CLK_NAME      clk
`define NPU_MST5_CLK_EN
`define NPU_MST5_PROT          axi4
`define NPU_MST5_DATA_WIDTH    64
`define NPU_MST5_ADDR_WIDTH    40
`define NPU_MST5_RW            rw
`define NPU_MST5_EXCL          1
`define NPU_MST5_LOCK          1
`define NPU_MST5_ID_WIDTH      1
`define NPU_MST5_BUS_ECC       0
`define NPU_MST5_BUS_ECC_PROT  32
`define NPU_MST5_BUS_PARITY    1


//master port for TB, signals are not needed by ARChitect flow
`define NPU_MST6_PREF            bri4tb_
`define NPU_MST6_PROT            axi
`define NPU_MST6_ID_WIDTH        4
`define NPU_MST6_DATA_WIDTH      32
`define NPU_MST6_RW              rw
`define NPU_MST6_LOCK            0
`define NPU_MST6_EXCL            0
`define NPU_MST6_CLK_NAME        clk
`define NPU_MST6_CLK_EN


`define NPU_ARCV2MSS   1
`define NPU_ADDR_WIDTH 40
`define NPU_NUM_MST    7
`define NPU_NUM_SLV    3
//npu_axi_initiators      =5; vpx_axi_initiators=0; host_axi_initiators=1; trace_axi_initiators=1
//npu_axi_targets         =3   ; vpx_axi_targets   = 0;





`define MDB_TB 0

`define SLICE_AXI_HAS_UITF 1
`define SLICE_AXI_UITF

`define MAXGRP 4
`define BSIZE 8
`define ISIZE `NPU_SLICE_ISIZE
`define VSIZE `NPU_SLICE_VSIZE
`define NPU_INT_AXI_DWIDTH 512

`define NPU_CLN_PFX "nl2_"


`define NPU_ENABLE_DP_CLOCK_GATE




`define   L2_MST_CFG_AP0_DECBASE    28'h00E_6000
`define   L2_MST_CFG_AP0_DECSIZE    28'hFFF_FF80
`define   L2_MST_CFG_AP0_DECMST      6'h4

`define   L2_MST_CFG_AP1_DECBASE    28'h00E_0000
`define   L2_MST_CFG_AP1_DECSIZE    28'hFFF_F000
`define   L2_MST_CFG_AP1_DECMST      6'h0

`define   L2_MST_CFG_AP2_DECBASE    28'h00E_6080
`define   L2_MST_CFG_AP2_DECSIZE    28'hFFF_FFFE
`define   L2_MST_CFG_AP2_DECMST      6'h0

`define   L2_MST_CFG_AP3_DECBASE    28'h00E_1000
`define   L2_MST_CFG_AP3_DECSIZE    28'hFFF_F000
`define   L2_MST_CFG_AP3_DECMST      6'h1        

`define   L2_MST_CFG_AP4_DECBASE    28'h00E_6082
`define   L2_MST_CFG_AP4_DECSIZE    28'hFFF_FFFE
`define   L2_MST_CFG_AP4_DECMST      6'h1        

`define   L2_MST_CFG_AP5_DECBASE    28'h00E_2000
`define   L2_MST_CFG_AP5_DECSIZE    28'hFFF_F000
`define   L2_MST_CFG_AP5_DECMST      6'h2

`define   L2_MST_CFG_AP6_DECBASE    28'h00E_6084
`define   L2_MST_CFG_AP6_DECSIZE    28'hFFF_FFFE
`define   L2_MST_CFG_AP6_DECMST      6'h2

`define   L2_MST_CFG_AP7_DECBASE    28'h00E_3000
`define   L2_MST_CFG_AP7_DECSIZE    28'hFFF_F000
`define   L2_MST_CFG_AP7_DECMST      6'h3

`define   L2_MST_CFG_AP8_DECBASE    28'h00E_6086
`define   L2_MST_CFG_AP8_DECSIZE    28'hFFF_FFFE
`define   L2_MST_CFG_AP8_DECMST      6'h3

`define   L2_MST_CFG_AP9_DECBASE    28'h00E_8000
`define   L2_MST_CFG_AP9_DECSIZE    28'hFFF_C018
`define   L2_MST_CFG_AP9_DECMST      6'h0

`define   L2_MST_CFG_AP10_DECBASE   28'h00E_8008
`define   L2_MST_CFG_AP10_DECSIZE   28'hFFF_C018
`define   L2_MST_CFG_AP10_DECMST     6'h1

`define   L2_MST_CFG_AP11_DECBASE   28'h00E_8010
`define   L2_MST_CFG_AP11_DECSIZE   28'hFFF_C018
`define   L2_MST_CFG_AP11_DECMST     6'h2

`define   L2_MST_CFG_AP12_DECBASE   28'h00E_8018
`define   L2_MST_CFG_AP12_DECSIZE   28'hFFF_C018
`define   L2_MST_CFG_AP12_DECMST     6'h3

`define   L2_MST_CFG_AP13_DECBASE   28'h0
`define   L2_MST_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   L2_MST_CFG_AP13_DECMST     6'h20

`define   L2_MST_CFG_AP14_DECBASE   28'h0
`define   L2_MST_CFG_AP14_DECSIZE   28'hFFF_FFFF
`define   L2_MST_CFG_AP14_DECMST     6'h20

`define   L2_MST_CFG_AP15_DECBASE   28'h0
`define   L2_MST_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   L2_MST_CFG_AP15_DECMST     6'h20

`define   L2_MST_CFG_DECBASE_RST_VAL {`L2_MST_CFG_AP15_DECBASE, `L2_MST_CFG_AP14_DECBASE, `L2_MST_CFG_AP13_DECBASE,  `L2_MST_CFG_AP12_DECBASE, \
                                          `L2_MST_CFG_AP11_DECBASE, `L2_MST_CFG_AP10_DECBASE, `L2_MST_CFG_AP9_DECBASE,   `L2_MST_CFG_AP8_DECBASE,  \
                                          `L2_MST_CFG_AP7_DECBASE,  `L2_MST_CFG_AP6_DECBASE,  `L2_MST_CFG_AP5_DECBASE,   `L2_MST_CFG_AP4_DECBASE,  \
                                          `L2_MST_CFG_AP3_DECBASE,  `L2_MST_CFG_AP2_DECBASE,  `L2_MST_CFG_AP1_DECBASE,   `L2_MST_CFG_AP0_DECBASE   \
                                         }

`define   L2_MST_CFG_DECSIZE_RST_VAL {`L2_MST_CFG_AP15_DECSIZE, `L2_MST_CFG_AP14_DECSIZE, `L2_MST_CFG_AP13_DECSIZE,  `L2_MST_CFG_AP12_DECSIZE, \
                                          `L2_MST_CFG_AP11_DECSIZE, `L2_MST_CFG_AP10_DECSIZE, `L2_MST_CFG_AP9_DECSIZE,   `L2_MST_CFG_AP8_DECSIZE,  \
                                          `L2_MST_CFG_AP7_DECSIZE,  `L2_MST_CFG_AP6_DECSIZE,  `L2_MST_CFG_AP5_DECSIZE,   `L2_MST_CFG_AP4_DECSIZE,  \
                                          `L2_MST_CFG_AP3_DECSIZE,  `L2_MST_CFG_AP2_DECSIZE,  `L2_MST_CFG_AP1_DECSIZE,   `L2_MST_CFG_AP0_DECSIZE   \
                                         }

`define   L2_MST_CFG_DECMST_RST_VAL  {`L2_MST_CFG_AP15_DECMST,  `L2_MST_CFG_AP14_DECMST,  `L2_MST_CFG_AP13_DECMST,  `L2_MST_CFG_AP12_DECMST,\
                                          `L2_MST_CFG_AP11_DECMST,  `L2_MST_CFG_AP10_DECMST,  `L2_MST_CFG_AP9_DECMST,   `L2_MST_CFG_AP8_DECMST, \
                                          `L2_MST_CFG_AP7_DECMST,   `L2_MST_CFG_AP6_DECMST,   `L2_MST_CFG_AP5_DECMST,   `L2_MST_CFG_AP4_DECMST, \
                                          `L2_MST_CFG_AP3_DECMST,   `L2_MST_CFG_AP2_DECMST,   `L2_MST_CFG_AP1_DECMST,   `L2_MST_CFG_AP0_DECMST  \
                                         }

`define   L2_CBU_CFG_AP0_DECBASE    28'h00E_6400
`define   L2_CBU_CFG_AP0_DECSIZE    28'hFFF_FF00
`define   L2_CBU_CFG_AP0_DECMST      6'h2

`define   L2_CBU_CFG_AP1_DECBASE    28'h00E_0000
`define   L2_CBU_CFG_AP1_DECSIZE    28'hFFF_0000
`define   L2_CBU_CFG_AP1_DECMST      6'h0

`define   L2_CBU_CFG_AP2_DECBASE    28'h00E_8000
`define   L2_CBU_CFG_AP2_DECSIZE    28'hFFF_C000
`define   L2_CBU_CFG_AP2_DECMST      6'h0

`define   L2_CBU_CFG_AP3_DECBASE    28'h0
`define   L2_CBU_CFG_AP3_DECSIZE    28'h0
`define   L2_CBU_CFG_AP3_DECMST      6'h1        

`define   L2_CBU_CFG_AP4_DECBASE    28'h0        
`define   L2_CBU_CFG_AP4_DECSIZE    28'hFFF_FFFF
`define   L2_CBU_CFG_AP4_DECMST      6'h20       

`define   L2_CBU_CFG_AP5_DECBASE    28'h0        
`define   L2_CBU_CFG_AP5_DECSIZE    28'hFFF_FFFF
`define   L2_CBU_CFG_AP5_DECMST      6'h20       

`define   L2_CBU_CFG_AP6_DECBASE    28'h0        
`define   L2_CBU_CFG_AP6_DECSIZE    28'hFFF_FFFF
`define   L2_CBU_CFG_AP6_DECMST      6'h20       

`define   L2_CBU_CFG_AP7_DECBASE    28'h0        
`define   L2_CBU_CFG_AP7_DECSIZE    28'hFFF_FFFF
`define   L2_CBU_CFG_AP7_DECMST      6'h20       

`define   L2_CBU_CFG_AP8_DECBASE    28'h0        
`define   L2_CBU_CFG_AP8_DECSIZE    28'hFFF_FFFF
`define   L2_CBU_CFG_AP8_DECMST      6'h20       

`define   L2_CBU_CFG_AP9_DECBASE    28'h0        
`define   L2_CBU_CFG_AP9_DECSIZE    28'hFFF_FFFF
`define   L2_CBU_CFG_AP9_DECMST      6'h20       

`define   L2_CBU_CFG_AP10_DECBASE   28'h0        
`define   L2_CBU_CFG_AP10_DECSIZE   28'hFFF_FFFF
`define   L2_CBU_CFG_AP10_DECMST     6'h20       

`define   L2_CBU_CFG_AP11_DECBASE   28'h0        
`define   L2_CBU_CFG_AP11_DECSIZE   28'hFFF_FFFF
`define   L2_CBU_CFG_AP11_DECMST     6'h20       

`define   L2_CBU_CFG_AP12_DECBASE   28'h0        
`define   L2_CBU_CFG_AP12_DECSIZE   28'hFFF_FFFF
`define   L2_CBU_CFG_AP12_DECMST     6'h20       

`define   L2_CBU_CFG_AP13_DECBASE   28'h0        
`define   L2_CBU_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   L2_CBU_CFG_AP13_DECMST     6'h20       

`define   L2_CBU_CFG_AP14_DECBASE   28'h0        
`define   L2_CBU_CFG_AP14_DECSIZE   28'hFFF_FFFF
`define   L2_CBU_CFG_AP14_DECMST     6'h20       

`define   L2_CBU_CFG_AP15_DECBASE   28'h0        
`define   L2_CBU_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   L2_CBU_CFG_AP15_DECMST     6'h20       

`define   L2_CBU_CFG_DECBASE_RST_VAL {`L2_CBU_CFG_AP15_DECBASE, `L2_CBU_CFG_AP14_DECBASE, `L2_CBU_CFG_AP13_DECBASE,  `L2_CBU_CFG_AP12_DECBASE, \
                                          `L2_CBU_CFG_AP11_DECBASE, `L2_CBU_CFG_AP10_DECBASE, `L2_CBU_CFG_AP9_DECBASE,   `L2_CBU_CFG_AP8_DECBASE,  \
                                          `L2_CBU_CFG_AP7_DECBASE,  `L2_CBU_CFG_AP6_DECBASE,  `L2_CBU_CFG_AP5_DECBASE,   `L2_CBU_CFG_AP4_DECBASE,  \
                                          `L2_CBU_CFG_AP3_DECBASE,  `L2_CBU_CFG_AP2_DECBASE,  `L2_CBU_CFG_AP1_DECBASE,   `L2_CBU_CFG_AP0_DECBASE   \
                                         }

`define   L2_CBU_CFG_DECSIZE_RST_VAL {`L2_CBU_CFG_AP15_DECSIZE, `L2_CBU_CFG_AP14_DECSIZE, `L2_CBU_CFG_AP13_DECSIZE,  `L2_CBU_CFG_AP12_DECSIZE, \
                                          `L2_CBU_CFG_AP11_DECSIZE, `L2_CBU_CFG_AP10_DECSIZE, `L2_CBU_CFG_AP9_DECSIZE,   `L2_CBU_CFG_AP8_DECSIZE,  \
                                          `L2_CBU_CFG_AP7_DECSIZE,  `L2_CBU_CFG_AP6_DECSIZE,  `L2_CBU_CFG_AP5_DECSIZE,   `L2_CBU_CFG_AP4_DECSIZE,  \
                                          `L2_CBU_CFG_AP3_DECSIZE,  `L2_CBU_CFG_AP2_DECSIZE,  `L2_CBU_CFG_AP1_DECSIZE,   `L2_CBU_CFG_AP0_DECSIZE   \
                                         }

`define   L2_CBU_CFG_DECMST_RST_VAL  {`L2_CBU_CFG_AP15_DECMST,  `L2_CBU_CFG_AP14_DECMST,  `L2_CBU_CFG_AP13_DECMST,  `L2_CBU_CFG_AP12_DECMST,\
                                          `L2_CBU_CFG_AP11_DECMST,  `L2_CBU_CFG_AP10_DECMST,  `L2_CBU_CFG_AP9_DECMST,   `L2_CBU_CFG_AP8_DECMST, \
                                          `L2_CBU_CFG_AP7_DECMST,   `L2_CBU_CFG_AP6_DECMST,   `L2_CBU_CFG_AP5_DECMST,   `L2_CBU_CFG_AP4_DECMST, \
                                          `L2_CBU_CFG_AP3_DECMST,   `L2_CBU_CFG_AP2_DECMST,   `L2_CBU_CFG_AP1_DECMST,   `L2_CBU_CFG_AP0_DECMST  \
                                         }

`define   L2_REMP_CFG_AP0_DECBASE    28'h00E_8000
`define   L2_REMP_CFG_AP0_DECSIZE    28'hFFF_F000
`define   L2_REMP_CFG_AP0_DECMST      6'h20       

`define   L2_REMP_CFG_AP1_DECBASE    28'h00E_8000
`define   L2_REMP_CFG_AP1_DECSIZE    28'h000_0FFF
`define   L2_REMP_CFG_AP1_DECMST      6'h20       

`define   L2_REMP_CFG_AP2_DECBASE    28'h0        
`define   L2_REMP_CFG_AP2_DECSIZE    28'hFFF_FFFF
`define   L2_REMP_CFG_AP2_DECMST      6'h20       

`define   L2_REMP_CFG_AP3_DECBASE    28'h0       
`define   L2_REMP_CFG_AP3_DECSIZE    28'hFFF_FFFF
`define   L2_REMP_CFG_AP3_DECMST      6'h20      

`define   L2_REMP_CFG_AP4_DECBASE    28'h0        
`define   L2_REMP_CFG_AP4_DECSIZE    28'hFFF_FFFF
`define   L2_REMP_CFG_AP4_DECMST      6'h20       

`define   L2_REMP_CFG_AP5_DECBASE    28'h0        
`define   L2_REMP_CFG_AP5_DECSIZE    28'hFFF_FFFF
`define   L2_REMP_CFG_AP5_DECMST      6'h20       

`define   L2_REMP_CFG_AP6_DECBASE    28'h0        
`define   L2_REMP_CFG_AP6_DECSIZE    28'hFFF_FFFF
`define   L2_REMP_CFG_AP6_DECMST      6'h20       

`define   L2_REMP_CFG_AP7_DECBASE    28'h0        
`define   L2_REMP_CFG_AP7_DECSIZE    28'hFFF_FFFF
`define   L2_REMP_CFG_AP7_DECMST      6'h20       

`define   L2_REMP_CFG_AP8_DECBASE    28'h0        
`define   L2_REMP_CFG_AP8_DECSIZE    28'hFFF_FFFF
`define   L2_REMP_CFG_AP8_DECMST      6'h20       

`define   L2_REMP_CFG_AP9_DECBASE    28'h0        
`define   L2_REMP_CFG_AP9_DECSIZE    28'hFFF_FFFF
`define   L2_REMP_CFG_AP9_DECMST      6'h20       

`define   L2_REMP_CFG_AP10_DECBASE   28'h0        
`define   L2_REMP_CFG_AP10_DECSIZE   28'hFFF_FFFF
`define   L2_REMP_CFG_AP10_DECMST     6'h20       

`define   L2_REMP_CFG_AP11_DECBASE   28'h0        
`define   L2_REMP_CFG_AP11_DECSIZE   28'hFFF_FFFF
`define   L2_REMP_CFG_AP11_DECMST     6'h20       

`define   L2_REMP_CFG_AP12_DECBASE   28'h0        
`define   L2_REMP_CFG_AP12_DECSIZE   28'hFFF_FFFF
`define   L2_REMP_CFG_AP12_DECMST     6'h20       

`define   L2_REMP_CFG_AP13_DECBASE   28'h0        
`define   L2_REMP_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   L2_REMP_CFG_AP13_DECMST     6'h20       

`define   L2_REMP_CFG_AP14_DECBASE   28'h0        
`define   L2_REMP_CFG_AP14_DECSIZE   28'hFFF_FFFF
`define   L2_REMP_CFG_AP14_DECMST     6'h20       

`define   L2_REMP_CFG_AP15_DECBASE   28'h0        
`define   L2_REMP_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   L2_REMP_CFG_AP15_DECMST     6'h20       

`define   L2_REMP_CFG_DECBASE_RST_VAL {`L2_REMP_CFG_AP15_DECBASE, `L2_REMP_CFG_AP14_DECBASE, `L2_REMP_CFG_AP13_DECBASE,  `L2_REMP_CFG_AP12_DECBASE, \
                                           `L2_REMP_CFG_AP11_DECBASE, `L2_REMP_CFG_AP10_DECBASE, `L2_REMP_CFG_AP9_DECBASE,   `L2_REMP_CFG_AP8_DECBASE,  \
                                           `L2_REMP_CFG_AP7_DECBASE,  `L2_REMP_CFG_AP6_DECBASE,  `L2_REMP_CFG_AP5_DECBASE,   `L2_REMP_CFG_AP4_DECBASE,  \
                                           `L2_REMP_CFG_AP3_DECBASE,  `L2_REMP_CFG_AP2_DECBASE,  `L2_REMP_CFG_AP1_DECBASE,   `L2_REMP_CFG_AP0_DECBASE   \
                                          }

`define   L2_REMP_CFG_DECSIZE_RST_VAL {`L2_REMP_CFG_AP15_DECSIZE, `L2_REMP_CFG_AP14_DECSIZE, `L2_REMP_CFG_AP13_DECSIZE,  `L2_REMP_CFG_AP12_DECSIZE, \
                                           `L2_REMP_CFG_AP11_DECSIZE, `L2_REMP_CFG_AP10_DECSIZE, `L2_REMP_CFG_AP9_DECSIZE,   `L2_REMP_CFG_AP8_DECSIZE,  \
                                           `L2_REMP_CFG_AP7_DECSIZE,  `L2_REMP_CFG_AP6_DECSIZE,  `L2_REMP_CFG_AP5_DECSIZE,   `L2_REMP_CFG_AP4_DECSIZE,  \
                                           `L2_REMP_CFG_AP3_DECSIZE,  `L2_REMP_CFG_AP2_DECSIZE,  `L2_REMP_CFG_AP1_DECSIZE,   `L2_REMP_CFG_AP0_DECSIZE   \
                                          }

`define   L2_REMP_CFG_DECMST_RST_VAL  {`L2_REMP_CFG_AP15_DECMST,  `L2_REMP_CFG_AP14_DECMST,  `L2_REMP_CFG_AP13_DECMST,  `L2_REMP_CFG_AP12_DECMST,\
                                           `L2_REMP_CFG_AP11_DECMST,  `L2_REMP_CFG_AP10_DECMST,  `L2_REMP_CFG_AP9_DECMST,   `L2_REMP_CFG_AP8_DECMST, \
                                           `L2_REMP_CFG_AP7_DECMST,   `L2_REMP_CFG_AP6_DECMST,   `L2_REMP_CFG_AP5_DECMST,   `L2_REMP_CFG_AP4_DECMST, \
                                           `L2_REMP_CFG_AP3_DECMST,   `L2_REMP_CFG_AP2_DECMST,   `L2_REMP_CFG_AP1_DECMST,   `L2_REMP_CFG_AP0_DECMST  \
                                          }

`define   CLN_GRP0_TOP_CFG_AP0_DECBASE    28'h00E_0000
`define   CLN_GRP0_TOP_CFG_AP0_DECSIZE    28'hFFF_F000
`define   CLN_GRP0_TOP_CFG_AP0_DECMST      6'h1

`define   CLN_GRP0_TOP_CFG_AP1_DECBASE    28'h00E_1000
`define   CLN_GRP0_TOP_CFG_AP1_DECSIZE    28'hFFF_F000
`define   CLN_GRP0_TOP_CFG_AP1_DECMST      6'h2

`define   CLN_GRP0_TOP_CFG_AP2_DECBASE    28'h00E_2000
`define   CLN_GRP0_TOP_CFG_AP2_DECSIZE    28'hFFF_F000
`define   CLN_GRP0_TOP_CFG_AP2_DECMST      6'h3

`define   CLN_GRP0_TOP_CFG_AP3_DECBASE    28'h00E_3000
`define   CLN_GRP0_TOP_CFG_AP3_DECSIZE    28'hFFF_F000
`define   CLN_GRP0_TOP_CFG_AP3_DECMST      6'h4

`define   CLN_GRP0_TOP_CFG_AP4_DECBASE    28'h00E_6080
`define   CLN_GRP0_TOP_CFG_AP4_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP0_TOP_CFG_AP4_DECMST      6'h1

`define   CLN_GRP0_TOP_CFG_AP5_DECBASE    28'h00E_6082
`define   CLN_GRP0_TOP_CFG_AP5_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP0_TOP_CFG_AP5_DECMST      6'h2

`define   CLN_GRP0_TOP_CFG_AP6_DECBASE    28'h00E_6084
`define   CLN_GRP0_TOP_CFG_AP6_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP0_TOP_CFG_AP6_DECMST      6'h3

`define   CLN_GRP0_TOP_CFG_AP7_DECBASE    28'h00E_6086
`define   CLN_GRP0_TOP_CFG_AP7_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP0_TOP_CFG_AP7_DECMST      6'h4

`define   CLN_GRP0_TOP_CFG_AP8_DECBASE    28'h00E_8000
`define   CLN_GRP0_TOP_CFG_AP8_DECSIZE    28'h00F_C018
`define   CLN_GRP0_TOP_CFG_AP8_DECMST      6'h1

`define   CLN_GRP0_TOP_CFG_AP9_DECBASE    28'h00E_8008
`define   CLN_GRP0_TOP_CFG_AP9_DECSIZE    28'h00F_C018
`define   CLN_GRP0_TOP_CFG_AP9_DECMST      6'h2        

`define   CLN_GRP0_TOP_CFG_AP10_DECBASE   28'h00E_8010
`define   CLN_GRP0_TOP_CFG_AP10_DECSIZE   28'h00F_C018
`define   CLN_GRP0_TOP_CFG_AP10_DECMST     6'h3        

`define   CLN_GRP0_TOP_CFG_AP11_DECBASE   28'h00E_8018
`define   CLN_GRP0_TOP_CFG_AP11_DECSIZE   28'h00F_C018
`define   CLN_GRP0_TOP_CFG_AP11_DECMST     6'h4

`define   CLN_GRP0_TOP_CFG_AP12_DECBASE   28'h00E_6000
`define   CLN_GRP0_TOP_CFG_AP12_DECSIZE   28'hFFF_FF80
`define   CLN_GRP0_TOP_CFG_AP12_DECMST     6'h1        

`define   CLN_GRP0_TOP_CFG_AP13_DECBASE   28'h0        
`define   CLN_GRP0_TOP_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP0_TOP_CFG_AP13_DECMST     6'h20       

`define   CLN_GRP0_TOP_CFG_AP14_DECBASE   28'h0        
`define   CLN_GRP0_TOP_CFG_AP14_DECSIZE   28'h0
`define   CLN_GRP0_TOP_CFG_AP14_DECMST     6'h0

`define   CLN_GRP0_TOP_CFG_AP15_DECBASE   28'h0        
`define   CLN_GRP0_TOP_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP0_TOP_CFG_AP15_DECMST     6'h20       

`define   CLN_GRP0_TOP_CFG_DECBASE_RST_VAL {`CLN_GRP0_TOP_CFG_AP15_DECBASE, `CLN_GRP0_TOP_CFG_AP14_DECBASE, `CLN_GRP0_TOP_CFG_AP13_DECBASE,  `CLN_GRP0_TOP_CFG_AP12_DECBASE, \
                                           `CLN_GRP0_TOP_CFG_AP11_DECBASE, `CLN_GRP0_TOP_CFG_AP10_DECBASE, `CLN_GRP0_TOP_CFG_AP9_DECBASE,   `CLN_GRP0_TOP_CFG_AP8_DECBASE,  \
                                           `CLN_GRP0_TOP_CFG_AP7_DECBASE,  `CLN_GRP0_TOP_CFG_AP6_DECBASE,  `CLN_GRP0_TOP_CFG_AP5_DECBASE,   `CLN_GRP0_TOP_CFG_AP4_DECBASE,  \
                                           `CLN_GRP0_TOP_CFG_AP3_DECBASE,  `CLN_GRP0_TOP_CFG_AP2_DECBASE,  `CLN_GRP0_TOP_CFG_AP1_DECBASE,   `CLN_GRP0_TOP_CFG_AP0_DECBASE   \
                                          }

`define   CLN_GRP0_TOP_CFG_DECSIZE_RST_VAL {`CLN_GRP0_TOP_CFG_AP15_DECSIZE, `CLN_GRP0_TOP_CFG_AP14_DECSIZE, `CLN_GRP0_TOP_CFG_AP13_DECSIZE,  `CLN_GRP0_TOP_CFG_AP12_DECSIZE, \
                                           `CLN_GRP0_TOP_CFG_AP11_DECSIZE, `CLN_GRP0_TOP_CFG_AP10_DECSIZE, `CLN_GRP0_TOP_CFG_AP9_DECSIZE,   `CLN_GRP0_TOP_CFG_AP8_DECSIZE,  \
                                           `CLN_GRP0_TOP_CFG_AP7_DECSIZE,  `CLN_GRP0_TOP_CFG_AP6_DECSIZE,  `CLN_GRP0_TOP_CFG_AP5_DECSIZE,   `CLN_GRP0_TOP_CFG_AP4_DECSIZE,  \
                                           `CLN_GRP0_TOP_CFG_AP3_DECSIZE,  `CLN_GRP0_TOP_CFG_AP2_DECSIZE,  `CLN_GRP0_TOP_CFG_AP1_DECSIZE,   `CLN_GRP0_TOP_CFG_AP0_DECSIZE   \
                                          }

`define   CLN_GRP0_TOP_CFG_DECMST_RST_VAL  {`CLN_GRP0_TOP_CFG_AP15_DECMST,  `CLN_GRP0_TOP_CFG_AP14_DECMST,  `CLN_GRP0_TOP_CFG_AP13_DECMST,  `CLN_GRP0_TOP_CFG_AP12_DECMST,\
                                           `CLN_GRP0_TOP_CFG_AP11_DECMST,  `CLN_GRP0_TOP_CFG_AP10_DECMST,  `CLN_GRP0_TOP_CFG_AP9_DECMST,   `CLN_GRP0_TOP_CFG_AP8_DECMST, \
                                           `CLN_GRP0_TOP_CFG_AP7_DECMST,   `CLN_GRP0_TOP_CFG_AP6_DECMST,   `CLN_GRP0_TOP_CFG_AP5_DECMST,   `CLN_GRP0_TOP_CFG_AP4_DECMST, \
                                           `CLN_GRP0_TOP_CFG_AP3_DECMST,   `CLN_GRP0_TOP_CFG_AP2_DECMST,   `CLN_GRP0_TOP_CFG_AP1_DECMST,   `CLN_GRP0_TOP_CFG_AP0_DECMST  \
                                          }

`define   CLN_GRP0_BOT_CFG_AP0_DECBASE    28'h0        
`define   CLN_GRP0_BOT_CFG_AP0_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP0_BOT_CFG_AP0_DECMST      6'h20       

`define   CLN_GRP0_BOT_CFG_AP1_DECBASE    28'h00E_8000
`define   CLN_GRP0_BOT_CFG_AP1_DECSIZE    28'h00F_C007
`define   CLN_GRP0_BOT_CFG_AP1_DECMST      6'h0

`define   CLN_GRP0_BOT_CFG_AP2_DECBASE    28'h00E_8001
`define   CLN_GRP0_BOT_CFG_AP2_DECSIZE    28'h00F_C007
`define   CLN_GRP0_BOT_CFG_AP2_DECMST      6'h1        

`define   CLN_GRP0_BOT_CFG_AP3_DECBASE    28'h00E_8002
`define   CLN_GRP0_BOT_CFG_AP3_DECSIZE    28'h00F_C007
`define   CLN_GRP0_BOT_CFG_AP3_DECMST      6'h2        

`define   CLN_GRP0_BOT_CFG_AP4_DECBASE    28'h00E_8003
`define   CLN_GRP0_BOT_CFG_AP4_DECSIZE    28'h00F_C007
`define   CLN_GRP0_BOT_CFG_AP4_DECMST      6'h3        

`define   CLN_GRP0_BOT_CFG_AP5_DECBASE    28'h00E_8004
`define   CLN_GRP0_BOT_CFG_AP5_DECSIZE    28'h00F_C007
`define   CLN_GRP0_BOT_CFG_AP5_DECMST      6'h4        

`define   CLN_GRP0_BOT_CFG_AP6_DECBASE    28'h00E_8005
`define   CLN_GRP0_BOT_CFG_AP6_DECSIZE    28'h00F_C007
`define   CLN_GRP0_BOT_CFG_AP6_DECMST      6'h5        

`define   CLN_GRP0_BOT_CFG_AP7_DECBASE    28'h00E_8006
`define   CLN_GRP0_BOT_CFG_AP7_DECSIZE    28'h00F_C007
`define   CLN_GRP0_BOT_CFG_AP7_DECMST      6'h6        

`define   CLN_GRP0_BOT_CFG_AP8_DECBASE    28'h00E_8007
`define   CLN_GRP0_BOT_CFG_AP8_DECSIZE    28'h00F_C007
`define   CLN_GRP0_BOT_CFG_AP8_DECMST      6'h7        

`define   CLN_GRP0_BOT_CFG_AP9_DECBASE    28'h00E_0000
`define   CLN_GRP0_BOT_CFG_AP9_DECSIZE    28'hFFF_F000
`define   CLN_GRP0_BOT_CFG_AP9_DECMST      6'h8

`define   CLN_GRP0_BOT_CFG_AP10_DECBASE   28'h00E_6000
`define   CLN_GRP0_BOT_CFG_AP10_DECSIZE   28'hFFF_FF80
`define   CLN_GRP0_BOT_CFG_AP10_DECMST     6'h8        

`define   CLN_GRP0_BOT_CFG_AP11_DECBASE   28'h00E_6080
`define   CLN_GRP0_BOT_CFG_AP11_DECSIZE   28'hFFF_FFFE
`define   CLN_GRP0_BOT_CFG_AP11_DECMST     6'h8        

`define   CLN_GRP0_BOT_CFG_AP12_DECBASE   28'h0        
`define   CLN_GRP0_BOT_CFG_AP12_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP0_BOT_CFG_AP12_DECMST     6'h20

`define   CLN_GRP0_BOT_CFG_AP13_DECBASE   28'h0        
`define   CLN_GRP0_BOT_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP0_BOT_CFG_AP13_DECMST     6'h20       

`define   CLN_GRP0_BOT_CFG_AP14_DECBASE   28'h0        
`define   CLN_GRP0_BOT_CFG_AP14_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP0_BOT_CFG_AP14_DECMST     6'h20       

`define   CLN_GRP0_BOT_CFG_AP15_DECBASE   28'h0        
`define   CLN_GRP0_BOT_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP0_BOT_CFG_AP15_DECMST     6'h20       

`define   CLN_GRP0_BOT_CFG_DECBASE_RST_VAL {`CLN_GRP0_BOT_CFG_AP15_DECBASE, `CLN_GRP0_BOT_CFG_AP14_DECBASE, `CLN_GRP0_BOT_CFG_AP13_DECBASE,  `CLN_GRP0_BOT_CFG_AP12_DECBASE, \
                                           `CLN_GRP0_BOT_CFG_AP11_DECBASE, `CLN_GRP0_BOT_CFG_AP10_DECBASE, `CLN_GRP0_BOT_CFG_AP9_DECBASE,   `CLN_GRP0_BOT_CFG_AP8_DECBASE,  \
                                           `CLN_GRP0_BOT_CFG_AP7_DECBASE,  `CLN_GRP0_BOT_CFG_AP6_DECBASE,  `CLN_GRP0_BOT_CFG_AP5_DECBASE,   `CLN_GRP0_BOT_CFG_AP4_DECBASE,  \
                                           `CLN_GRP0_BOT_CFG_AP3_DECBASE,  `CLN_GRP0_BOT_CFG_AP2_DECBASE,  `CLN_GRP0_BOT_CFG_AP1_DECBASE,   `CLN_GRP0_BOT_CFG_AP0_DECBASE   \
                                          }

`define   CLN_GRP0_BOT_CFG_DECSIZE_RST_VAL {`CLN_GRP0_BOT_CFG_AP15_DECSIZE, `CLN_GRP0_BOT_CFG_AP14_DECSIZE, `CLN_GRP0_BOT_CFG_AP13_DECSIZE,  `CLN_GRP0_BOT_CFG_AP12_DECSIZE, \
                                           `CLN_GRP0_BOT_CFG_AP11_DECSIZE, `CLN_GRP0_BOT_CFG_AP10_DECSIZE, `CLN_GRP0_BOT_CFG_AP9_DECSIZE,   `CLN_GRP0_BOT_CFG_AP8_DECSIZE,  \
                                           `CLN_GRP0_BOT_CFG_AP7_DECSIZE,  `CLN_GRP0_BOT_CFG_AP6_DECSIZE,  `CLN_GRP0_BOT_CFG_AP5_DECSIZE,   `CLN_GRP0_BOT_CFG_AP4_DECSIZE,  \
                                           `CLN_GRP0_BOT_CFG_AP3_DECSIZE,  `CLN_GRP0_BOT_CFG_AP2_DECSIZE,  `CLN_GRP0_BOT_CFG_AP1_DECSIZE,   `CLN_GRP0_BOT_CFG_AP0_DECSIZE   \
                                          }

`define   CLN_GRP0_BOT_CFG_DECMST_RST_VAL  {`CLN_GRP0_BOT_CFG_AP15_DECMST,  `CLN_GRP0_BOT_CFG_AP14_DECMST,  `CLN_GRP0_BOT_CFG_AP13_DECMST,  `CLN_GRP0_BOT_CFG_AP12_DECMST,\
                                           `CLN_GRP0_BOT_CFG_AP11_DECMST,  `CLN_GRP0_BOT_CFG_AP10_DECMST,  `CLN_GRP0_BOT_CFG_AP9_DECMST,   `CLN_GRP0_BOT_CFG_AP8_DECMST, \
                                           `CLN_GRP0_BOT_CFG_AP7_DECMST,   `CLN_GRP0_BOT_CFG_AP6_DECMST,   `CLN_GRP0_BOT_CFG_AP5_DECMST,   `CLN_GRP0_BOT_CFG_AP4_DECMST, \
                                           `CLN_GRP0_BOT_CFG_AP3_DECMST,   `CLN_GRP0_BOT_CFG_AP2_DECMST,   `CLN_GRP0_BOT_CFG_AP1_DECMST,   `CLN_GRP0_BOT_CFG_AP0_DECMST  \
                                          }

`define   CLN_GRP0_CCM_CFG_AP0_DECBASE    28'h00E_0000        
`define   CLN_GRP0_CCM_CFG_AP0_DECSIZE    28'hFFF_FC00
`define   CLN_GRP0_CCM_CFG_AP0_DECMST      6'h0       
`define   CLN_GRP0_CCM_CFG_AP1_DECBASE    28'h00E_0400        
`define   CLN_GRP0_CCM_CFG_AP1_DECSIZE    28'hFFF_FC00
`define   CLN_GRP0_CCM_CFG_AP1_DECMST      6'h1       
`define   CLN_GRP0_CCM_CFG_AP2_DECBASE    28'h00E_0800        
`define   CLN_GRP0_CCM_CFG_AP2_DECSIZE    28'hFFF_FC00
`define   CLN_GRP0_CCM_CFG_AP2_DECMST      6'h2       
`define   CLN_GRP0_CCM_CFG_AP3_DECBASE    28'h00E_0C00        
`define   CLN_GRP0_CCM_CFG_AP3_DECSIZE    28'hFFF_FC00
`define   CLN_GRP0_CCM_CFG_AP3_DECMST      6'h3       
`define   CLN_GRP0_CCM_CFG_AP4_DECBASE    28'h00E_6080
`define   CLN_GRP0_CCM_CFG_AP4_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP0_CCM_CFG_AP4_DECMST      6'h4       
`define   CLN_GRP0_CCM_CFG_AP5_DECBASE    28'h00E_6081
`define   CLN_GRP0_CCM_CFG_AP5_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP0_CCM_CFG_AP5_DECMST      6'h5       
`define   CLN_GRP0_CCM_CFG_AP6_DECBASE    28'h00E_6000        
`define   CLN_GRP0_CCM_CFG_AP6_DECSIZE    28'hFFF_FF80
`define   CLN_GRP0_CCM_CFG_AP6_DECMST      6'h6

`define   CLN_GRP0_CCM_CFG_DECBASE_RST_VAL { \
                                           `CLN_GRP0_CCM_CFG_AP6_DECBASE,  \
                                           `CLN_GRP0_CCM_CFG_AP5_DECBASE, \
                                           `CLN_GRP0_CCM_CFG_AP4_DECBASE, \
                                           `CLN_GRP0_CCM_CFG_AP3_DECBASE, \
                                           `CLN_GRP0_CCM_CFG_AP2_DECBASE, \
                                           `CLN_GRP0_CCM_CFG_AP1_DECBASE, \
                                           `CLN_GRP0_CCM_CFG_AP0_DECBASE  \
                                          }

`define   CLN_GRP0_CCM_CFG_DECSIZE_RST_VAL { \
                                           `CLN_GRP0_CCM_CFG_AP6_DECSIZE,  \
                                           `CLN_GRP0_CCM_CFG_AP5_DECSIZE, \
                                           `CLN_GRP0_CCM_CFG_AP4_DECSIZE, \
                                           `CLN_GRP0_CCM_CFG_AP3_DECSIZE, \
                                           `CLN_GRP0_CCM_CFG_AP2_DECSIZE, \
                                           `CLN_GRP0_CCM_CFG_AP1_DECSIZE, \
                                           `CLN_GRP0_CCM_CFG_AP0_DECSIZE  \
                                          }

`define   CLN_GRP0_CCM_CFG_DECMST_RST_VAL  { \
                                           `CLN_GRP0_CCM_CFG_AP6_DECMST,  \
                                           `CLN_GRP0_CCM_CFG_AP5_DECMST, \
                                           `CLN_GRP0_CCM_CFG_AP4_DECMST, \
                                           `CLN_GRP0_CCM_CFG_AP3_DECMST, \
                                           `CLN_GRP0_CCM_CFG_AP2_DECMST, \
                                           `CLN_GRP0_CCM_CFG_AP1_DECMST, \
                                           `CLN_GRP0_CCM_CFG_AP0_DECMST  \
                                          }

`define   CLN_GRP0_REMP_CFG_AP0_DECBASE    28'h2
`define   CLN_GRP0_REMP_CFG_AP0_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP0_REMP_CFG_AP0_DECMST      6'h20       

`define   CLN_GRP0_REMP_CFG_AP1_DECBASE    28'h0
`define   CLN_GRP0_REMP_CFG_AP1_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP0_REMP_CFG_AP1_DECMST      6'h20

`define   CLN_GRP0_REMP_CFG_DECBASE_RST_VAL {`CLN_GRP0_REMP_CFG_AP1_DECBASE,   `CLN_GRP0_REMP_CFG_AP0_DECBASE   \
                                           }

`define   CLN_GRP0_REMP_CFG_DECSIZE_RST_VAL {`CLN_GRP0_REMP_CFG_AP1_DECSIZE,   `CLN_GRP0_REMP_CFG_AP0_DECSIZE   \
                                           }

`define   CLN_GRP0_REMP_CFG_DECMST_RST_VAL  {`CLN_GRP0_REMP_CFG_AP1_DECMST,   `CLN_GRP0_REMP_CFG_AP0_DECMST  \
                                           }

`define   CLN_GRP1_TOP_CFG_AP0_DECBASE    28'h00E_0000
`define   CLN_GRP1_TOP_CFG_AP0_DECSIZE    28'hFFF_F000
`define   CLN_GRP1_TOP_CFG_AP0_DECMST      6'h2

`define   CLN_GRP1_TOP_CFG_AP1_DECBASE    28'h00E_1000
`define   CLN_GRP1_TOP_CFG_AP1_DECSIZE    28'hFFF_F000
`define   CLN_GRP1_TOP_CFG_AP1_DECMST      6'h1

`define   CLN_GRP1_TOP_CFG_AP2_DECBASE    28'h00E_2000
`define   CLN_GRP1_TOP_CFG_AP2_DECSIZE    28'hFFF_F000
`define   CLN_GRP1_TOP_CFG_AP2_DECMST      6'h4

`define   CLN_GRP1_TOP_CFG_AP3_DECBASE    28'h00E_3000
`define   CLN_GRP1_TOP_CFG_AP3_DECSIZE    28'hFFF_F000
`define   CLN_GRP1_TOP_CFG_AP3_DECMST      6'h3

`define   CLN_GRP1_TOP_CFG_AP4_DECBASE    28'h00E_6080
`define   CLN_GRP1_TOP_CFG_AP4_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP1_TOP_CFG_AP4_DECMST      6'h2

`define   CLN_GRP1_TOP_CFG_AP5_DECBASE    28'h00E_6082
`define   CLN_GRP1_TOP_CFG_AP5_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP1_TOP_CFG_AP5_DECMST      6'h1

`define   CLN_GRP1_TOP_CFG_AP6_DECBASE    28'h00E_6084
`define   CLN_GRP1_TOP_CFG_AP6_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP1_TOP_CFG_AP6_DECMST      6'h4

`define   CLN_GRP1_TOP_CFG_AP7_DECBASE    28'h00E_6086
`define   CLN_GRP1_TOP_CFG_AP7_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP1_TOP_CFG_AP7_DECMST      6'h3

`define   CLN_GRP1_TOP_CFG_AP8_DECBASE    28'h00E_8000
`define   CLN_GRP1_TOP_CFG_AP8_DECSIZE    28'h00F_C018
`define   CLN_GRP1_TOP_CFG_AP8_DECMST      6'h2

`define   CLN_GRP1_TOP_CFG_AP9_DECBASE    28'h00E_8008
`define   CLN_GRP1_TOP_CFG_AP9_DECSIZE    28'h00F_C018
`define   CLN_GRP1_TOP_CFG_AP9_DECMST      6'h1

`define   CLN_GRP1_TOP_CFG_AP10_DECBASE   28'h00E_8010
`define   CLN_GRP1_TOP_CFG_AP10_DECSIZE   28'h00F_C018
`define   CLN_GRP1_TOP_CFG_AP10_DECMST     6'h4

`define   CLN_GRP1_TOP_CFG_AP11_DECBASE   28'h00E_8018
`define   CLN_GRP1_TOP_CFG_AP11_DECSIZE   28'h00F_C018
`define   CLN_GRP1_TOP_CFG_AP11_DECMST     6'h3

`define   CLN_GRP1_TOP_CFG_AP12_DECBASE   28'h00E_6000
`define   CLN_GRP1_TOP_CFG_AP12_DECSIZE   28'hFFF_FF80
`define   CLN_GRP1_TOP_CFG_AP12_DECMST     6'h1        

`define   CLN_GRP1_TOP_CFG_AP13_DECBASE   28'h0
`define   CLN_GRP1_TOP_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP1_TOP_CFG_AP13_DECMST     6'h20

`define   CLN_GRP1_TOP_CFG_AP14_DECBASE   28'h0
`define   CLN_GRP1_TOP_CFG_AP14_DECSIZE   28'h0
`define   CLN_GRP1_TOP_CFG_AP14_DECMST     6'h0

`define   CLN_GRP1_TOP_CFG_AP15_DECBASE   28'h0
`define   CLN_GRP1_TOP_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP1_TOP_CFG_AP15_DECMST     6'h20

`define   CLN_GRP1_TOP_CFG_DECBASE_RST_VAL {`CLN_GRP1_TOP_CFG_AP15_DECBASE, `CLN_GRP1_TOP_CFG_AP14_DECBASE, `CLN_GRP1_TOP_CFG_AP13_DECBASE,  `CLN_GRP1_TOP_CFG_AP12_DECBASE, \
                                                `CLN_GRP1_TOP_CFG_AP11_DECBASE, `CLN_GRP1_TOP_CFG_AP10_DECBASE, `CLN_GRP1_TOP_CFG_AP9_DECBASE,   `CLN_GRP1_TOP_CFG_AP8_DECBASE,  \
                                                `CLN_GRP1_TOP_CFG_AP7_DECBASE,  `CLN_GRP1_TOP_CFG_AP6_DECBASE,  `CLN_GRP1_TOP_CFG_AP5_DECBASE,   `CLN_GRP1_TOP_CFG_AP4_DECBASE,  \
                                                `CLN_GRP1_TOP_CFG_AP3_DECBASE,  `CLN_GRP1_TOP_CFG_AP2_DECBASE,  `CLN_GRP1_TOP_CFG_AP1_DECBASE,   `CLN_GRP1_TOP_CFG_AP0_DECBASE   \
                                               }

`define   CLN_GRP1_TOP_CFG_DECSIZE_RST_VAL {`CLN_GRP1_TOP_CFG_AP15_DECSIZE, `CLN_GRP1_TOP_CFG_AP14_DECSIZE, `CLN_GRP1_TOP_CFG_AP13_DECSIZE,  `CLN_GRP1_TOP_CFG_AP12_DECSIZE, \
                                                `CLN_GRP1_TOP_CFG_AP11_DECSIZE, `CLN_GRP1_TOP_CFG_AP10_DECSIZE, `CLN_GRP1_TOP_CFG_AP9_DECSIZE,   `CLN_GRP1_TOP_CFG_AP8_DECSIZE,  \
                                                `CLN_GRP1_TOP_CFG_AP7_DECSIZE,  `CLN_GRP1_TOP_CFG_AP6_DECSIZE,  `CLN_GRP1_TOP_CFG_AP5_DECSIZE,   `CLN_GRP1_TOP_CFG_AP4_DECSIZE,  \
                                                `CLN_GRP1_TOP_CFG_AP3_DECSIZE,  `CLN_GRP1_TOP_CFG_AP2_DECSIZE,  `CLN_GRP1_TOP_CFG_AP1_DECSIZE,   `CLN_GRP1_TOP_CFG_AP0_DECSIZE   \
                                               }

`define   CLN_GRP1_TOP_CFG_DECMST_RST_VAL  {`CLN_GRP1_TOP_CFG_AP15_DECMST,  `CLN_GRP1_TOP_CFG_AP14_DECMST,  `CLN_GRP1_TOP_CFG_AP13_DECMST,  `CLN_GRP1_TOP_CFG_AP12_DECMST,\
                                                `CLN_GRP1_TOP_CFG_AP11_DECMST,  `CLN_GRP1_TOP_CFG_AP10_DECMST,  `CLN_GRP1_TOP_CFG_AP9_DECMST,   `CLN_GRP1_TOP_CFG_AP8_DECMST, \
                                                `CLN_GRP1_TOP_CFG_AP7_DECMST,   `CLN_GRP1_TOP_CFG_AP6_DECMST,   `CLN_GRP1_TOP_CFG_AP5_DECMST,   `CLN_GRP1_TOP_CFG_AP4_DECMST, \
                                                `CLN_GRP1_TOP_CFG_AP3_DECMST,   `CLN_GRP1_TOP_CFG_AP2_DECMST,   `CLN_GRP1_TOP_CFG_AP1_DECMST,   `CLN_GRP1_TOP_CFG_AP0_DECMST  \
                                               }

`define   CLN_GRP1_BOT_CFG_AP0_DECBASE    28'h0
`define   CLN_GRP1_BOT_CFG_AP0_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP1_BOT_CFG_AP0_DECMST      6'h20

`define   CLN_GRP1_BOT_CFG_AP1_DECBASE    28'h00E_8000
`define   CLN_GRP1_BOT_CFG_AP1_DECSIZE    28'h00F_C007
`define   CLN_GRP1_BOT_CFG_AP1_DECMST      6'h0

`define   CLN_GRP1_BOT_CFG_AP2_DECBASE    28'h00E_8001
`define   CLN_GRP1_BOT_CFG_AP2_DECSIZE    28'h00F_C007
`define   CLN_GRP1_BOT_CFG_AP2_DECMST      6'h1

`define   CLN_GRP1_BOT_CFG_AP3_DECBASE    28'h00E_8002
`define   CLN_GRP1_BOT_CFG_AP3_DECSIZE    28'h00F_C007
`define   CLN_GRP1_BOT_CFG_AP3_DECMST      6'h2

`define   CLN_GRP1_BOT_CFG_AP4_DECBASE    28'h00E_8003
`define   CLN_GRP1_BOT_CFG_AP4_DECSIZE    28'h00F_C007
`define   CLN_GRP1_BOT_CFG_AP4_DECMST      6'h3

`define   CLN_GRP1_BOT_CFG_AP5_DECBASE    28'h00E_8004
`define   CLN_GRP1_BOT_CFG_AP5_DECSIZE    28'h00F_C007
`define   CLN_GRP1_BOT_CFG_AP5_DECMST      6'h4

`define   CLN_GRP1_BOT_CFG_AP6_DECBASE    28'h00E_8005
`define   CLN_GRP1_BOT_CFG_AP6_DECSIZE    28'h00F_C007
`define   CLN_GRP1_BOT_CFG_AP6_DECMST      6'h5

`define   CLN_GRP1_BOT_CFG_AP7_DECBASE    28'h00E_8006
`define   CLN_GRP1_BOT_CFG_AP7_DECSIZE    28'h00F_C007
`define   CLN_GRP1_BOT_CFG_AP7_DECMST      6'h6

`define   CLN_GRP1_BOT_CFG_AP8_DECBASE    28'h00E_8007
`define   CLN_GRP1_BOT_CFG_AP8_DECSIZE    28'h00F_C007
`define   CLN_GRP1_BOT_CFG_AP8_DECMST      6'h7

`define   CLN_GRP1_BOT_CFG_AP9_DECBASE    28'h00E_1000
`define   CLN_GRP1_BOT_CFG_AP9_DECSIZE    28'hFFF_F000
`define   CLN_GRP1_BOT_CFG_AP9_DECMST      6'h8

`define   CLN_GRP1_BOT_CFG_AP10_DECBASE   28'h00E_6000
`define   CLN_GRP1_BOT_CFG_AP10_DECSIZE   28'hFFF_FF80
`define   CLN_GRP1_BOT_CFG_AP10_DECMST     6'h8

`define   CLN_GRP1_BOT_CFG_AP11_DECBASE   28'h00E_6082
`define   CLN_GRP1_BOT_CFG_AP11_DECSIZE   28'hFFF_FFFE
`define   CLN_GRP1_BOT_CFG_AP11_DECMST     6'h8

`define   CLN_GRP1_BOT_CFG_AP12_DECBASE   28'h0        
`define   CLN_GRP1_BOT_CFG_AP12_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP1_BOT_CFG_AP12_DECMST     6'h20

`define   CLN_GRP1_BOT_CFG_AP13_DECBASE   28'h0
`define   CLN_GRP1_BOT_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP1_BOT_CFG_AP13_DECMST     6'h20

`define   CLN_GRP1_BOT_CFG_AP14_DECBASE   28'h0
`define   CLN_GRP1_BOT_CFG_AP14_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP1_BOT_CFG_AP14_DECMST     6'h20

`define   CLN_GRP1_BOT_CFG_AP15_DECBASE   28'h0
`define   CLN_GRP1_BOT_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP1_BOT_CFG_AP15_DECMST     6'h20

`define   CLN_GRP1_BOT_CFG_DECBASE_RST_VAL {`CLN_GRP1_BOT_CFG_AP15_DECBASE, `CLN_GRP1_BOT_CFG_AP14_DECBASE, `CLN_GRP1_BOT_CFG_AP13_DECBASE,  `CLN_GRP1_BOT_CFG_AP12_DECBASE, \
                                                `CLN_GRP1_BOT_CFG_AP11_DECBASE, `CLN_GRP1_BOT_CFG_AP10_DECBASE, `CLN_GRP1_BOT_CFG_AP9_DECBASE,   `CLN_GRP1_BOT_CFG_AP8_DECBASE,  \
                                                `CLN_GRP1_BOT_CFG_AP7_DECBASE,  `CLN_GRP1_BOT_CFG_AP6_DECBASE,  `CLN_GRP1_BOT_CFG_AP5_DECBASE,   `CLN_GRP1_BOT_CFG_AP4_DECBASE,  \
                                                `CLN_GRP1_BOT_CFG_AP3_DECBASE,  `CLN_GRP1_BOT_CFG_AP2_DECBASE,  `CLN_GRP1_BOT_CFG_AP1_DECBASE,   `CLN_GRP1_BOT_CFG_AP0_DECBASE   \
                                               }

`define   CLN_GRP1_BOT_CFG_DECSIZE_RST_VAL {`CLN_GRP1_BOT_CFG_AP15_DECSIZE, `CLN_GRP1_BOT_CFG_AP14_DECSIZE, `CLN_GRP1_BOT_CFG_AP13_DECSIZE,  `CLN_GRP1_BOT_CFG_AP12_DECSIZE, \
                                                `CLN_GRP1_BOT_CFG_AP11_DECSIZE, `CLN_GRP1_BOT_CFG_AP10_DECSIZE, `CLN_GRP1_BOT_CFG_AP9_DECSIZE,   `CLN_GRP1_BOT_CFG_AP8_DECSIZE,  \
                                                `CLN_GRP1_BOT_CFG_AP7_DECSIZE,  `CLN_GRP1_BOT_CFG_AP6_DECSIZE,  `CLN_GRP1_BOT_CFG_AP5_DECSIZE,   `CLN_GRP1_BOT_CFG_AP4_DECSIZE,  \
                                                `CLN_GRP1_BOT_CFG_AP3_DECSIZE,  `CLN_GRP1_BOT_CFG_AP2_DECSIZE,  `CLN_GRP1_BOT_CFG_AP1_DECSIZE,   `CLN_GRP1_BOT_CFG_AP0_DECSIZE   \
                                               }

`define   CLN_GRP1_BOT_CFG_DECMST_RST_VAL  {`CLN_GRP1_BOT_CFG_AP15_DECMST,  `CLN_GRP1_BOT_CFG_AP14_DECMST,  `CLN_GRP1_BOT_CFG_AP13_DECMST,  `CLN_GRP1_BOT_CFG_AP12_DECMST,\
                                                `CLN_GRP1_BOT_CFG_AP11_DECMST,  `CLN_GRP1_BOT_CFG_AP10_DECMST,  `CLN_GRP1_BOT_CFG_AP9_DECMST,   `CLN_GRP1_BOT_CFG_AP8_DECMST, \
                                                `CLN_GRP1_BOT_CFG_AP7_DECMST,   `CLN_GRP1_BOT_CFG_AP6_DECMST,   `CLN_GRP1_BOT_CFG_AP5_DECMST,   `CLN_GRP1_BOT_CFG_AP4_DECMST, \
                                                `CLN_GRP1_BOT_CFG_AP3_DECMST,   `CLN_GRP1_BOT_CFG_AP2_DECMST,   `CLN_GRP1_BOT_CFG_AP1_DECMST,   `CLN_GRP1_BOT_CFG_AP0_DECMST  \
                                               }

`define   CLN_GRP1_CCM_CFG_AP0_DECBASE    28'h00E_1000
`define   CLN_GRP1_CCM_CFG_AP0_DECSIZE    28'hFFF_FC00
`define   CLN_GRP1_CCM_CFG_AP0_DECMST      6'h0
`define   CLN_GRP1_CCM_CFG_AP1_DECBASE    28'h00E_1400
`define   CLN_GRP1_CCM_CFG_AP1_DECSIZE    28'hFFF_FC00
`define   CLN_GRP1_CCM_CFG_AP1_DECMST      6'h1
`define   CLN_GRP1_CCM_CFG_AP2_DECBASE    28'h00E_1800
`define   CLN_GRP1_CCM_CFG_AP2_DECSIZE    28'hFFF_FC00
`define   CLN_GRP1_CCM_CFG_AP2_DECMST      6'h2
`define   CLN_GRP1_CCM_CFG_AP3_DECBASE    28'h00E_1C00
`define   CLN_GRP1_CCM_CFG_AP3_DECSIZE    28'hFFF_FC00
`define   CLN_GRP1_CCM_CFG_AP3_DECMST      6'h3
`define   CLN_GRP1_CCM_CFG_AP4_DECBASE    28'h00E_6082
`define   CLN_GRP1_CCM_CFG_AP4_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP1_CCM_CFG_AP4_DECMST      6'h4
`define   CLN_GRP1_CCM_CFG_AP5_DECBASE    28'h00E_6083
`define   CLN_GRP1_CCM_CFG_AP5_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP1_CCM_CFG_AP5_DECMST      6'h5
`define   CLN_GRP1_CCM_CFG_AP6_DECBASE    28'h00E_6000
`define   CLN_GRP1_CCM_CFG_AP6_DECSIZE    28'hFFF_FF80
`define   CLN_GRP1_CCM_CFG_AP6_DECMST      6'h6

`define   CLN_GRP1_CCM_CFG_DECBASE_RST_VAL { \
                                                `CLN_GRP1_CCM_CFG_AP6_DECBASE,  \
                                                `CLN_GRP1_CCM_CFG_AP5_DECBASE, \
                                                `CLN_GRP1_CCM_CFG_AP4_DECBASE, \
                                                `CLN_GRP1_CCM_CFG_AP3_DECBASE, \
                                                `CLN_GRP1_CCM_CFG_AP2_DECBASE, \
                                                `CLN_GRP1_CCM_CFG_AP1_DECBASE, \
                                                `CLN_GRP1_CCM_CFG_AP0_DECBASE  \
                                               }

`define   CLN_GRP1_CCM_CFG_DECSIZE_RST_VAL { \
                                                `CLN_GRP1_CCM_CFG_AP6_DECSIZE,  \
                                                `CLN_GRP1_CCM_CFG_AP5_DECSIZE, \
                                                `CLN_GRP1_CCM_CFG_AP4_DECSIZE, \
                                                `CLN_GRP1_CCM_CFG_AP3_DECSIZE, \
                                                `CLN_GRP1_CCM_CFG_AP2_DECSIZE, \
                                                `CLN_GRP1_CCM_CFG_AP1_DECSIZE, \
                                                `CLN_GRP1_CCM_CFG_AP0_DECSIZE  \
                                               }

`define   CLN_GRP1_CCM_CFG_DECMST_RST_VAL  { \
                                                `CLN_GRP1_CCM_CFG_AP6_DECMST,  \
                                                `CLN_GRP1_CCM_CFG_AP5_DECMST, \
                                                `CLN_GRP1_CCM_CFG_AP4_DECMST, \
                                                `CLN_GRP1_CCM_CFG_AP3_DECMST, \
                                                `CLN_GRP1_CCM_CFG_AP2_DECMST, \
                                                `CLN_GRP1_CCM_CFG_AP1_DECMST, \
                                                `CLN_GRP1_CCM_CFG_AP0_DECMST  \
                                               }

`define   CLN_GRP1_REMP_CFG_AP0_DECBASE    28'h2
`define   CLN_GRP1_REMP_CFG_AP0_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP1_REMP_CFG_AP0_DECMST      6'h20       

`define   CLN_GRP1_REMP_CFG_AP1_DECBASE    28'h0
`define   CLN_GRP1_REMP_CFG_AP1_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP1_REMP_CFG_AP1_DECMST      6'h20

`define   CLN_GRP1_REMP_CFG_DECBASE_RST_VAL {`CLN_GRP1_REMP_CFG_AP1_DECBASE,   `CLN_GRP1_REMP_CFG_AP0_DECBASE   \
                                           }

`define   CLN_GRP1_REMP_CFG_DECSIZE_RST_VAL {`CLN_GRP1_REMP_CFG_AP1_DECSIZE,   `CLN_GRP1_REMP_CFG_AP0_DECSIZE   \
                                           }

`define   CLN_GRP1_REMP_CFG_DECMST_RST_VAL  {`CLN_GRP1_REMP_CFG_AP1_DECMST,   `CLN_GRP1_REMP_CFG_AP0_DECMST  \
                                           }


`define   CLN_GRP2_TOP_CFG_AP0_DECBASE    28'h00E_0000
`define   CLN_GRP2_TOP_CFG_AP0_DECSIZE    28'hFFF_F000
`define   CLN_GRP2_TOP_CFG_AP0_DECMST      6'h3

`define   CLN_GRP2_TOP_CFG_AP1_DECBASE    28'h00E_1000
`define   CLN_GRP2_TOP_CFG_AP1_DECSIZE    28'hFFF_F000
`define   CLN_GRP2_TOP_CFG_AP1_DECMST      6'h4

`define   CLN_GRP2_TOP_CFG_AP2_DECBASE    28'h00E_2000
`define   CLN_GRP2_TOP_CFG_AP2_DECSIZE    28'hFFF_F000
`define   CLN_GRP2_TOP_CFG_AP2_DECMST      6'h1

`define   CLN_GRP2_TOP_CFG_AP3_DECBASE    28'h00E_3000
`define   CLN_GRP2_TOP_CFG_AP3_DECSIZE    28'hFFF_F000
`define   CLN_GRP2_TOP_CFG_AP3_DECMST      6'h2
                                                           
`define   CLN_GRP2_TOP_CFG_AP4_DECBASE    28'h00E_6080
`define   CLN_GRP2_TOP_CFG_AP4_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP2_TOP_CFG_AP4_DECMST      6'h3

`define   CLN_GRP2_TOP_CFG_AP5_DECBASE    28'h00E_6082
`define   CLN_GRP2_TOP_CFG_AP5_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP2_TOP_CFG_AP5_DECMST      6'h4

`define   CLN_GRP2_TOP_CFG_AP6_DECBASE    28'h00E_6084
`define   CLN_GRP2_TOP_CFG_AP6_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP2_TOP_CFG_AP6_DECMST      6'h1

`define   CLN_GRP2_TOP_CFG_AP7_DECBASE    28'h00E_6086
`define   CLN_GRP2_TOP_CFG_AP7_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP2_TOP_CFG_AP7_DECMST      6'h2

`define   CLN_GRP2_TOP_CFG_AP8_DECBASE    28'h00E_8000
`define   CLN_GRP2_TOP_CFG_AP8_DECSIZE    28'h00F_C018
`define   CLN_GRP2_TOP_CFG_AP8_DECMST      6'h3

`define   CLN_GRP2_TOP_CFG_AP9_DECBASE    28'h00E_8008
`define   CLN_GRP2_TOP_CFG_AP9_DECSIZE    28'h00F_C018
`define   CLN_GRP2_TOP_CFG_AP9_DECMST      6'h4

`define   CLN_GRP2_TOP_CFG_AP10_DECBASE   28'h00E_8010
`define   CLN_GRP2_TOP_CFG_AP10_DECSIZE   28'h00F_C018
`define   CLN_GRP2_TOP_CFG_AP10_DECMST     6'h1

`define   CLN_GRP2_TOP_CFG_AP11_DECBASE   28'h00E_8018
`define   CLN_GRP2_TOP_CFG_AP11_DECSIZE   28'h00F_C018
`define   CLN_GRP2_TOP_CFG_AP11_DECMST     6'h2

`define   CLN_GRP2_TOP_CFG_AP12_DECBASE   28'h00E_6000
`define   CLN_GRP2_TOP_CFG_AP12_DECSIZE   28'hFFF_FF80
`define   CLN_GRP2_TOP_CFG_AP12_DECMST     6'h1

`define   CLN_GRP2_TOP_CFG_AP13_DECBASE   28'h0
`define   CLN_GRP2_TOP_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP2_TOP_CFG_AP13_DECMST     6'h20

`define   CLN_GRP2_TOP_CFG_AP14_DECBASE   28'h0
`define   CLN_GRP2_TOP_CFG_AP14_DECSIZE   28'h0
`define   CLN_GRP2_TOP_CFG_AP14_DECMST     6'h0

`define   CLN_GRP2_TOP_CFG_AP15_DECBASE   28'h0
`define   CLN_GRP2_TOP_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP2_TOP_CFG_AP15_DECMST     6'h20

`define   CLN_GRP2_TOP_CFG_DECBASE_RST_VAL {`CLN_GRP2_TOP_CFG_AP15_DECBASE, `CLN_GRP2_TOP_CFG_AP14_DECBASE, `CLN_GRP2_TOP_CFG_AP13_DECBASE,  `CLN_GRP2_TOP_CFG_AP12_DECBASE, \
                                                `CLN_GRP2_TOP_CFG_AP11_DECBASE, `CLN_GRP2_TOP_CFG_AP10_DECBASE, `CLN_GRP2_TOP_CFG_AP9_DECBASE,   `CLN_GRP2_TOP_CFG_AP8_DECBASE,  \
                                                `CLN_GRP2_TOP_CFG_AP7_DECBASE,  `CLN_GRP2_TOP_CFG_AP6_DECBASE,  `CLN_GRP2_TOP_CFG_AP5_DECBASE,   `CLN_GRP2_TOP_CFG_AP4_DECBASE,  \
                                                `CLN_GRP2_TOP_CFG_AP3_DECBASE,  `CLN_GRP2_TOP_CFG_AP2_DECBASE,  `CLN_GRP2_TOP_CFG_AP1_DECBASE,   `CLN_GRP2_TOP_CFG_AP0_DECBASE   \
                                               }

`define   CLN_GRP2_TOP_CFG_DECSIZE_RST_VAL {`CLN_GRP2_TOP_CFG_AP15_DECSIZE, `CLN_GRP2_TOP_CFG_AP14_DECSIZE, `CLN_GRP2_TOP_CFG_AP13_DECSIZE,  `CLN_GRP2_TOP_CFG_AP12_DECSIZE, \
                                                `CLN_GRP2_TOP_CFG_AP11_DECSIZE, `CLN_GRP2_TOP_CFG_AP10_DECSIZE, `CLN_GRP2_TOP_CFG_AP9_DECSIZE,   `CLN_GRP2_TOP_CFG_AP8_DECSIZE,  \
                                                `CLN_GRP2_TOP_CFG_AP7_DECSIZE,  `CLN_GRP2_TOP_CFG_AP6_DECSIZE,  `CLN_GRP2_TOP_CFG_AP5_DECSIZE,   `CLN_GRP2_TOP_CFG_AP4_DECSIZE,  \
                                                `CLN_GRP2_TOP_CFG_AP3_DECSIZE,  `CLN_GRP2_TOP_CFG_AP2_DECSIZE,  `CLN_GRP2_TOP_CFG_AP1_DECSIZE,   `CLN_GRP2_TOP_CFG_AP0_DECSIZE   \
                                               }

`define   CLN_GRP2_TOP_CFG_DECMST_RST_VAL  {`CLN_GRP2_TOP_CFG_AP15_DECMST,  `CLN_GRP2_TOP_CFG_AP14_DECMST,  `CLN_GRP2_TOP_CFG_AP13_DECMST,  `CLN_GRP2_TOP_CFG_AP12_DECMST,\
                                                `CLN_GRP2_TOP_CFG_AP11_DECMST,  `CLN_GRP2_TOP_CFG_AP10_DECMST,  `CLN_GRP2_TOP_CFG_AP9_DECMST,   `CLN_GRP2_TOP_CFG_AP8_DECMST, \
                                                `CLN_GRP2_TOP_CFG_AP7_DECMST,   `CLN_GRP2_TOP_CFG_AP6_DECMST,   `CLN_GRP2_TOP_CFG_AP5_DECMST,   `CLN_GRP2_TOP_CFG_AP4_DECMST, \
                                                `CLN_GRP2_TOP_CFG_AP3_DECMST,   `CLN_GRP2_TOP_CFG_AP2_DECMST,   `CLN_GRP2_TOP_CFG_AP1_DECMST,   `CLN_GRP2_TOP_CFG_AP0_DECMST  \
                                               }

`define   CLN_GRP2_BOT_CFG_AP0_DECBASE    28'h0
`define   CLN_GRP2_BOT_CFG_AP0_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP2_BOT_CFG_AP0_DECMST      6'h20

`define   CLN_GRP2_BOT_CFG_AP1_DECBASE    28'h00E_8000
`define   CLN_GRP2_BOT_CFG_AP1_DECSIZE    28'h00F_C007
`define   CLN_GRP2_BOT_CFG_AP1_DECMST      6'h0

`define   CLN_GRP2_BOT_CFG_AP2_DECBASE    28'h00E_8001
`define   CLN_GRP2_BOT_CFG_AP2_DECSIZE    28'h00F_C007
`define   CLN_GRP2_BOT_CFG_AP2_DECMST      6'h1

`define   CLN_GRP2_BOT_CFG_AP3_DECBASE    28'h00E_8002
`define   CLN_GRP2_BOT_CFG_AP3_DECSIZE    28'h00F_C007
`define   CLN_GRP2_BOT_CFG_AP3_DECMST      6'h2

`define   CLN_GRP2_BOT_CFG_AP4_DECBASE    28'h00E_8003
`define   CLN_GRP2_BOT_CFG_AP4_DECSIZE    28'h00F_C007
`define   CLN_GRP2_BOT_CFG_AP4_DECMST      6'h3

`define   CLN_GRP2_BOT_CFG_AP5_DECBASE    28'h00E_8004
`define   CLN_GRP2_BOT_CFG_AP5_DECSIZE    28'h00F_C007
`define   CLN_GRP2_BOT_CFG_AP5_DECMST      6'h4

`define   CLN_GRP2_BOT_CFG_AP6_DECBASE    28'h00E_8005
`define   CLN_GRP2_BOT_CFG_AP6_DECSIZE    28'h00F_C007
`define   CLN_GRP2_BOT_CFG_AP6_DECMST      6'h5

`define   CLN_GRP2_BOT_CFG_AP7_DECBASE    28'h00E_8006
`define   CLN_GRP2_BOT_CFG_AP7_DECSIZE    28'h00F_C007
`define   CLN_GRP2_BOT_CFG_AP7_DECMST      6'h6

`define   CLN_GRP2_BOT_CFG_AP8_DECBASE    28'h00E_8007
`define   CLN_GRP2_BOT_CFG_AP8_DECSIZE    28'h00F_C007
`define   CLN_GRP2_BOT_CFG_AP8_DECMST      6'h7

`define   CLN_GRP2_BOT_CFG_AP9_DECBASE    28'h00E_2000
`define   CLN_GRP2_BOT_CFG_AP9_DECSIZE    28'hFFF_F000
`define   CLN_GRP2_BOT_CFG_AP9_DECMST      6'h8

`define   CLN_GRP2_BOT_CFG_AP10_DECBASE   28'h00E_6000
`define   CLN_GRP2_BOT_CFG_AP10_DECSIZE   28'hFFF_FF80
`define   CLN_GRP2_BOT_CFG_AP10_DECMST     6'h8

`define   CLN_GRP2_BOT_CFG_AP11_DECBASE   28'h00E_6084
`define   CLN_GRP2_BOT_CFG_AP11_DECSIZE   28'hFFF_FFFE
`define   CLN_GRP2_BOT_CFG_AP11_DECMST     6'h8

`define   CLN_GRP2_BOT_CFG_AP12_DECBASE   28'h0        
`define   CLN_GRP2_BOT_CFG_AP12_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP2_BOT_CFG_AP12_DECMST     6'h20

`define   CLN_GRP2_BOT_CFG_AP13_DECBASE   28'h0
`define   CLN_GRP2_BOT_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP2_BOT_CFG_AP13_DECMST     6'h20

`define   CLN_GRP2_BOT_CFG_AP14_DECBASE   28'h0
`define   CLN_GRP2_BOT_CFG_AP14_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP2_BOT_CFG_AP14_DECMST     6'h20

`define   CLN_GRP2_BOT_CFG_AP15_DECBASE   28'h0
`define   CLN_GRP2_BOT_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP2_BOT_CFG_AP15_DECMST     6'h20

`define   CLN_GRP2_BOT_CFG_DECBASE_RST_VAL {`CLN_GRP2_BOT_CFG_AP15_DECBASE, `CLN_GRP2_BOT_CFG_AP14_DECBASE, `CLN_GRP2_BOT_CFG_AP13_DECBASE,  `CLN_GRP2_BOT_CFG_AP12_DECBASE, \
                                                `CLN_GRP2_BOT_CFG_AP11_DECBASE, `CLN_GRP2_BOT_CFG_AP10_DECBASE, `CLN_GRP2_BOT_CFG_AP9_DECBASE,   `CLN_GRP2_BOT_CFG_AP8_DECBASE,  \
                                                `CLN_GRP2_BOT_CFG_AP7_DECBASE,  `CLN_GRP2_BOT_CFG_AP6_DECBASE,  `CLN_GRP2_BOT_CFG_AP5_DECBASE,   `CLN_GRP2_BOT_CFG_AP4_DECBASE,  \
                                                `CLN_GRP2_BOT_CFG_AP3_DECBASE,  `CLN_GRP2_BOT_CFG_AP2_DECBASE,  `CLN_GRP2_BOT_CFG_AP1_DECBASE,   `CLN_GRP2_BOT_CFG_AP0_DECBASE   \
                                               }

`define   CLN_GRP2_BOT_CFG_DECSIZE_RST_VAL {`CLN_GRP2_BOT_CFG_AP15_DECSIZE, `CLN_GRP2_BOT_CFG_AP14_DECSIZE, `CLN_GRP2_BOT_CFG_AP13_DECSIZE,  `CLN_GRP2_BOT_CFG_AP12_DECSIZE, \
                                                `CLN_GRP2_BOT_CFG_AP11_DECSIZE, `CLN_GRP2_BOT_CFG_AP10_DECSIZE, `CLN_GRP2_BOT_CFG_AP9_DECSIZE,   `CLN_GRP2_BOT_CFG_AP8_DECSIZE,  \
                                                `CLN_GRP2_BOT_CFG_AP7_DECSIZE,  `CLN_GRP2_BOT_CFG_AP6_DECSIZE,  `CLN_GRP2_BOT_CFG_AP5_DECSIZE,   `CLN_GRP2_BOT_CFG_AP4_DECSIZE,  \
                                                `CLN_GRP2_BOT_CFG_AP3_DECSIZE,  `CLN_GRP2_BOT_CFG_AP2_DECSIZE,  `CLN_GRP2_BOT_CFG_AP1_DECSIZE,   `CLN_GRP2_BOT_CFG_AP0_DECSIZE   \
                                               }

`define   CLN_GRP2_BOT_CFG_DECMST_RST_VAL  {`CLN_GRP2_BOT_CFG_AP15_DECMST,  `CLN_GRP2_BOT_CFG_AP14_DECMST,  `CLN_GRP2_BOT_CFG_AP13_DECMST,  `CLN_GRP2_BOT_CFG_AP12_DECMST,\
                                                `CLN_GRP2_BOT_CFG_AP11_DECMST,  `CLN_GRP2_BOT_CFG_AP10_DECMST,  `CLN_GRP2_BOT_CFG_AP9_DECMST,   `CLN_GRP2_BOT_CFG_AP8_DECMST, \
                                                `CLN_GRP2_BOT_CFG_AP7_DECMST,   `CLN_GRP2_BOT_CFG_AP6_DECMST,   `CLN_GRP2_BOT_CFG_AP5_DECMST,   `CLN_GRP2_BOT_CFG_AP4_DECMST, \
                                                `CLN_GRP2_BOT_CFG_AP3_DECMST,   `CLN_GRP2_BOT_CFG_AP2_DECMST,   `CLN_GRP2_BOT_CFG_AP1_DECMST,   `CLN_GRP2_BOT_CFG_AP0_DECMST  \
                                               }

`define   CLN_GRP2_CCM_CFG_AP0_DECBASE    28'h00E_2000
`define   CLN_GRP2_CCM_CFG_AP0_DECSIZE    28'hFFF_FC00
`define   CLN_GRP2_CCM_CFG_AP0_DECMST      6'h0
`define   CLN_GRP2_CCM_CFG_AP1_DECBASE    28'h00E_2400
`define   CLN_GRP2_CCM_CFG_AP1_DECSIZE    28'hFFF_FC00
`define   CLN_GRP2_CCM_CFG_AP1_DECMST      6'h1
`define   CLN_GRP2_CCM_CFG_AP2_DECBASE    28'h00E_2800
`define   CLN_GRP2_CCM_CFG_AP2_DECSIZE    28'hFFF_FC00
`define   CLN_GRP2_CCM_CFG_AP2_DECMST      6'h2
`define   CLN_GRP2_CCM_CFG_AP3_DECBASE    28'h00E_2C00
`define   CLN_GRP2_CCM_CFG_AP3_DECSIZE    28'hFFF_FC00
`define   CLN_GRP2_CCM_CFG_AP3_DECMST      6'h3
`define   CLN_GRP2_CCM_CFG_AP4_DECBASE    28'h00E_6084
`define   CLN_GRP2_CCM_CFG_AP4_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP2_CCM_CFG_AP4_DECMST      6'h4
`define   CLN_GRP2_CCM_CFG_AP5_DECBASE    28'h00E_6085
`define   CLN_GRP2_CCM_CFG_AP5_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP2_CCM_CFG_AP5_DECMST      6'h5
`define   CLN_GRP2_CCM_CFG_AP6_DECBASE    28'h00E_6000
`define   CLN_GRP2_CCM_CFG_AP6_DECSIZE    28'hFFF_FF80
`define   CLN_GRP2_CCM_CFG_AP6_DECMST      6'h6

`define   CLN_GRP2_CCM_CFG_DECBASE_RST_VAL { \
                                                `CLN_GRP2_CCM_CFG_AP6_DECBASE,  \
                                                `CLN_GRP2_CCM_CFG_AP5_DECBASE, \
                                                `CLN_GRP2_CCM_CFG_AP4_DECBASE, \
                                                `CLN_GRP2_CCM_CFG_AP3_DECBASE, \
                                                `CLN_GRP2_CCM_CFG_AP2_DECBASE, \
                                                `CLN_GRP2_CCM_CFG_AP1_DECBASE, \
                                                `CLN_GRP2_CCM_CFG_AP0_DECBASE  \
                                               }

`define   CLN_GRP2_CCM_CFG_DECSIZE_RST_VAL { \
                                                `CLN_GRP2_CCM_CFG_AP6_DECSIZE,  \
                                                `CLN_GRP2_CCM_CFG_AP5_DECSIZE, \
                                                `CLN_GRP2_CCM_CFG_AP4_DECSIZE, \
                                                `CLN_GRP2_CCM_CFG_AP3_DECSIZE, \
                                                `CLN_GRP2_CCM_CFG_AP2_DECSIZE, \
                                                `CLN_GRP2_CCM_CFG_AP1_DECSIZE, \
                                                `CLN_GRP2_CCM_CFG_AP0_DECSIZE  \
                                               }

`define   CLN_GRP2_CCM_CFG_DECMST_RST_VAL  { \
                                                `CLN_GRP2_CCM_CFG_AP6_DECMST,  \
                                                `CLN_GRP2_CCM_CFG_AP5_DECMST, \
                                                `CLN_GRP2_CCM_CFG_AP4_DECMST, \
                                                `CLN_GRP2_CCM_CFG_AP3_DECMST, \
                                                `CLN_GRP2_CCM_CFG_AP2_DECMST, \
                                                `CLN_GRP2_CCM_CFG_AP1_DECMST, \
                                                `CLN_GRP2_CCM_CFG_AP0_DECMST  \
                                               }

`define   CLN_GRP2_REMP_CFG_AP0_DECBASE    28'h2
`define   CLN_GRP2_REMP_CFG_AP0_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP2_REMP_CFG_AP0_DECMST      6'h20

`define   CLN_GRP2_REMP_CFG_AP1_DECBASE    28'h0
`define   CLN_GRP2_REMP_CFG_AP1_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP2_REMP_CFG_AP1_DECMST      6'h20

`define   CLN_GRP2_REMP_CFG_DECBASE_RST_VAL {`CLN_GRP2_REMP_CFG_AP1_DECBASE,   `CLN_GRP2_REMP_CFG_AP0_DECBASE   \
                                           }

`define   CLN_GRP2_REMP_CFG_DECSIZE_RST_VAL {`CLN_GRP2_REMP_CFG_AP1_DECSIZE,   `CLN_GRP2_REMP_CFG_AP0_DECSIZE   \
                                           }

`define   CLN_GRP2_REMP_CFG_DECMST_RST_VAL  {`CLN_GRP2_REMP_CFG_AP1_DECMST,   `CLN_GRP2_REMP_CFG_AP0_DECMST  \
                                           }

`define   CLN_GRP3_TOP_CFG_AP0_DECBASE    28'h00E_0000
`define   CLN_GRP3_TOP_CFG_AP0_DECSIZE    28'hFFF_F000
`define   CLN_GRP3_TOP_CFG_AP0_DECMST      6'h4

`define   CLN_GRP3_TOP_CFG_AP1_DECBASE    28'h00E_1000
`define   CLN_GRP3_TOP_CFG_AP1_DECSIZE    28'hFFF_F000
`define   CLN_GRP3_TOP_CFG_AP1_DECMST      6'h3

`define   CLN_GRP3_TOP_CFG_AP2_DECBASE    28'h00E_2000
`define   CLN_GRP3_TOP_CFG_AP2_DECSIZE    28'hFFF_F000
`define   CLN_GRP3_TOP_CFG_AP2_DECMST      6'h2

`define   CLN_GRP3_TOP_CFG_AP3_DECBASE    28'h00E_3000
`define   CLN_GRP3_TOP_CFG_AP3_DECSIZE    28'hFFF_F000
`define   CLN_GRP3_TOP_CFG_AP3_DECMST      6'h1

`define   CLN_GRP3_TOP_CFG_AP4_DECBASE    28'h00E_6080
`define   CLN_GRP3_TOP_CFG_AP4_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP3_TOP_CFG_AP4_DECMST      6'h4
                                                           
`define   CLN_GRP3_TOP_CFG_AP5_DECBASE    28'h00E_6082
`define   CLN_GRP3_TOP_CFG_AP5_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP3_TOP_CFG_AP5_DECMST      6'h3
                                                           
`define   CLN_GRP3_TOP_CFG_AP6_DECBASE    28'h00E_6084
`define   CLN_GRP3_TOP_CFG_AP6_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP3_TOP_CFG_AP6_DECMST      6'h2

`define   CLN_GRP3_TOP_CFG_AP7_DECBASE    28'h00E_6086
`define   CLN_GRP3_TOP_CFG_AP7_DECSIZE    28'hFFF_FFFE
`define   CLN_GRP3_TOP_CFG_AP7_DECMST      6'h1

`define   CLN_GRP3_TOP_CFG_AP8_DECBASE    28'h00E_8000
`define   CLN_GRP3_TOP_CFG_AP8_DECSIZE    28'h00F_C018
`define   CLN_GRP3_TOP_CFG_AP8_DECMST      6'h4
                                                           
`define   CLN_GRP3_TOP_CFG_AP9_DECBASE    28'h00E_8008
`define   CLN_GRP3_TOP_CFG_AP9_DECSIZE    28'h00F_C018
`define   CLN_GRP3_TOP_CFG_AP9_DECMST      6'h3
                                                           
`define   CLN_GRP3_TOP_CFG_AP10_DECBASE   28'h00E_8010
`define   CLN_GRP3_TOP_CFG_AP10_DECSIZE   28'h00F_C018
`define   CLN_GRP3_TOP_CFG_AP10_DECMST     6'h2
                                                           
`define   CLN_GRP3_TOP_CFG_AP11_DECBASE   28'h00E_8018
`define   CLN_GRP3_TOP_CFG_AP11_DECSIZE   28'h00F_C018
`define   CLN_GRP3_TOP_CFG_AP11_DECMST     6'h1

`define   CLN_GRP3_TOP_CFG_AP12_DECBASE   28'h00E_6000
`define   CLN_GRP3_TOP_CFG_AP12_DECSIZE   28'hFFF_FF80
`define   CLN_GRP3_TOP_CFG_AP12_DECMST     6'h1

`define   CLN_GRP3_TOP_CFG_AP13_DECBASE   28'h0
`define   CLN_GRP3_TOP_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP3_TOP_CFG_AP13_DECMST     6'h20

`define   CLN_GRP3_TOP_CFG_AP14_DECBASE   28'h0
`define   CLN_GRP3_TOP_CFG_AP14_DECSIZE   28'h0
`define   CLN_GRP3_TOP_CFG_AP14_DECMST     6'h0

`define   CLN_GRP3_TOP_CFG_AP15_DECBASE   28'h0
`define   CLN_GRP3_TOP_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP3_TOP_CFG_AP15_DECMST     6'h20

`define   CLN_GRP3_TOP_CFG_DECBASE_RST_VAL {`CLN_GRP3_TOP_CFG_AP15_DECBASE, `CLN_GRP3_TOP_CFG_AP14_DECBASE, `CLN_GRP3_TOP_CFG_AP13_DECBASE,  `CLN_GRP3_TOP_CFG_AP12_DECBASE, \
                                                `CLN_GRP3_TOP_CFG_AP11_DECBASE, `CLN_GRP3_TOP_CFG_AP10_DECBASE, `CLN_GRP3_TOP_CFG_AP9_DECBASE,   `CLN_GRP3_TOP_CFG_AP8_DECBASE,  \
                                                `CLN_GRP3_TOP_CFG_AP7_DECBASE,  `CLN_GRP3_TOP_CFG_AP6_DECBASE,  `CLN_GRP3_TOP_CFG_AP5_DECBASE,   `CLN_GRP3_TOP_CFG_AP4_DECBASE,  \
                                                `CLN_GRP3_TOP_CFG_AP3_DECBASE,  `CLN_GRP3_TOP_CFG_AP2_DECBASE,  `CLN_GRP3_TOP_CFG_AP1_DECBASE,   `CLN_GRP3_TOP_CFG_AP0_DECBASE   \
                                               }

`define   CLN_GRP3_TOP_CFG_DECSIZE_RST_VAL {`CLN_GRP3_TOP_CFG_AP15_DECSIZE, `CLN_GRP3_TOP_CFG_AP14_DECSIZE, `CLN_GRP3_TOP_CFG_AP13_DECSIZE,  `CLN_GRP3_TOP_CFG_AP12_DECSIZE, \
                                                `CLN_GRP3_TOP_CFG_AP11_DECSIZE, `CLN_GRP3_TOP_CFG_AP10_DECSIZE, `CLN_GRP3_TOP_CFG_AP9_DECSIZE,   `CLN_GRP3_TOP_CFG_AP8_DECSIZE,  \
                                                `CLN_GRP3_TOP_CFG_AP7_DECSIZE,  `CLN_GRP3_TOP_CFG_AP6_DECSIZE,  `CLN_GRP3_TOP_CFG_AP5_DECSIZE,   `CLN_GRP3_TOP_CFG_AP4_DECSIZE,  \
                                                `CLN_GRP3_TOP_CFG_AP3_DECSIZE,  `CLN_GRP3_TOP_CFG_AP2_DECSIZE,  `CLN_GRP3_TOP_CFG_AP1_DECSIZE,   `CLN_GRP3_TOP_CFG_AP0_DECSIZE   \
                                               }

`define   CLN_GRP3_TOP_CFG_DECMST_RST_VAL  {`CLN_GRP3_TOP_CFG_AP15_DECMST,  `CLN_GRP3_TOP_CFG_AP14_DECMST,  `CLN_GRP3_TOP_CFG_AP13_DECMST,  `CLN_GRP3_TOP_CFG_AP12_DECMST,\
                                                `CLN_GRP3_TOP_CFG_AP11_DECMST,  `CLN_GRP3_TOP_CFG_AP10_DECMST,  `CLN_GRP3_TOP_CFG_AP9_DECMST,   `CLN_GRP3_TOP_CFG_AP8_DECMST, \
                                                `CLN_GRP3_TOP_CFG_AP7_DECMST,   `CLN_GRP3_TOP_CFG_AP6_DECMST,   `CLN_GRP3_TOP_CFG_AP5_DECMST,   `CLN_GRP3_TOP_CFG_AP4_DECMST, \
                                                `CLN_GRP3_TOP_CFG_AP3_DECMST,   `CLN_GRP3_TOP_CFG_AP2_DECMST,   `CLN_GRP3_TOP_CFG_AP1_DECMST,   `CLN_GRP3_TOP_CFG_AP0_DECMST  \
                                               }

`define   CLN_GRP3_BOT_CFG_AP0_DECBASE    28'h0
`define   CLN_GRP3_BOT_CFG_AP0_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP3_BOT_CFG_AP0_DECMST      6'h20

`define   CLN_GRP3_BOT_CFG_AP1_DECBASE    28'h00E_8000
`define   CLN_GRP3_BOT_CFG_AP1_DECSIZE    28'h00F_C007
`define   CLN_GRP3_BOT_CFG_AP1_DECMST      6'h0

`define   CLN_GRP3_BOT_CFG_AP2_DECBASE    28'h00E_8001
`define   CLN_GRP3_BOT_CFG_AP2_DECSIZE    28'h00F_C007
`define   CLN_GRP3_BOT_CFG_AP2_DECMST      6'h1

`define   CLN_GRP3_BOT_CFG_AP3_DECBASE    28'h00E_8002
`define   CLN_GRP3_BOT_CFG_AP3_DECSIZE    28'h00F_C007
`define   CLN_GRP3_BOT_CFG_AP3_DECMST      6'h2

`define   CLN_GRP3_BOT_CFG_AP4_DECBASE    28'h00E_8003
`define   CLN_GRP3_BOT_CFG_AP4_DECSIZE    28'h00F_C007
`define   CLN_GRP3_BOT_CFG_AP4_DECMST      6'h3

`define   CLN_GRP3_BOT_CFG_AP5_DECBASE    28'h00E_8004
`define   CLN_GRP3_BOT_CFG_AP5_DECSIZE    28'h00F_C007
`define   CLN_GRP3_BOT_CFG_AP5_DECMST      6'h4

`define   CLN_GRP3_BOT_CFG_AP6_DECBASE    28'h00E_8005
`define   CLN_GRP3_BOT_CFG_AP6_DECSIZE    28'h00F_C007
`define   CLN_GRP3_BOT_CFG_AP6_DECMST      6'h5

`define   CLN_GRP3_BOT_CFG_AP7_DECBASE    28'h00E_8006
`define   CLN_GRP3_BOT_CFG_AP7_DECSIZE    28'h00F_C007
`define   CLN_GRP3_BOT_CFG_AP7_DECMST      6'h6

`define   CLN_GRP3_BOT_CFG_AP8_DECBASE    28'h00E_8007
`define   CLN_GRP3_BOT_CFG_AP8_DECSIZE    28'h00F_C007
`define   CLN_GRP3_BOT_CFG_AP8_DECMST      6'h7

`define   CLN_GRP3_BOT_CFG_AP9_DECBASE    28'h00E_3000
`define   CLN_GRP3_BOT_CFG_AP9_DECSIZE    28'hFFF_F000
`define   CLN_GRP3_BOT_CFG_AP9_DECMST      6'h8

`define   CLN_GRP3_BOT_CFG_AP10_DECBASE   28'h00E_6000
`define   CLN_GRP3_BOT_CFG_AP10_DECSIZE   28'hFFF_FF80
`define   CLN_GRP3_BOT_CFG_AP10_DECMST     6'h8

`define   CLN_GRP3_BOT_CFG_AP11_DECBASE   28'h00E_6086
`define   CLN_GRP3_BOT_CFG_AP11_DECSIZE   28'hFFF_FFFE
`define   CLN_GRP3_BOT_CFG_AP11_DECMST     6'h8

`define   CLN_GRP3_BOT_CFG_AP12_DECBASE   28'h0        
`define   CLN_GRP3_BOT_CFG_AP12_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP3_BOT_CFG_AP12_DECMST     6'h20

`define   CLN_GRP3_BOT_CFG_AP13_DECBASE   28'h0
`define   CLN_GRP3_BOT_CFG_AP13_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP3_BOT_CFG_AP13_DECMST     6'h20

`define   CLN_GRP3_BOT_CFG_AP14_DECBASE   28'h0
`define   CLN_GRP3_BOT_CFG_AP14_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP3_BOT_CFG_AP14_DECMST     6'h20

`define   CLN_GRP3_BOT_CFG_AP15_DECBASE   28'h0
`define   CLN_GRP3_BOT_CFG_AP15_DECSIZE   28'hFFF_FFFF
`define   CLN_GRP3_BOT_CFG_AP15_DECMST     6'h20

`define   CLN_GRP3_BOT_CFG_DECBASE_RST_VAL {`CLN_GRP3_BOT_CFG_AP15_DECBASE, `CLN_GRP3_BOT_CFG_AP14_DECBASE, `CLN_GRP3_BOT_CFG_AP13_DECBASE,  `CLN_GRP3_BOT_CFG_AP12_DECBASE, \
                                                `CLN_GRP3_BOT_CFG_AP11_DECBASE, `CLN_GRP3_BOT_CFG_AP10_DECBASE, `CLN_GRP3_BOT_CFG_AP9_DECBASE,   `CLN_GRP3_BOT_CFG_AP8_DECBASE,  \
                                                `CLN_GRP3_BOT_CFG_AP7_DECBASE,  `CLN_GRP3_BOT_CFG_AP6_DECBASE,  `CLN_GRP3_BOT_CFG_AP5_DECBASE,   `CLN_GRP3_BOT_CFG_AP4_DECBASE,  \
                                                `CLN_GRP3_BOT_CFG_AP3_DECBASE,  `CLN_GRP3_BOT_CFG_AP2_DECBASE,  `CLN_GRP3_BOT_CFG_AP1_DECBASE,   `CLN_GRP3_BOT_CFG_AP0_DECBASE   \
                                               }

`define   CLN_GRP3_BOT_CFG_DECSIZE_RST_VAL {`CLN_GRP3_BOT_CFG_AP15_DECSIZE, `CLN_GRP3_BOT_CFG_AP14_DECSIZE, `CLN_GRP3_BOT_CFG_AP13_DECSIZE,  `CLN_GRP3_BOT_CFG_AP12_DECSIZE, \
                                                `CLN_GRP3_BOT_CFG_AP11_DECSIZE, `CLN_GRP3_BOT_CFG_AP10_DECSIZE, `CLN_GRP3_BOT_CFG_AP9_DECSIZE,   `CLN_GRP3_BOT_CFG_AP8_DECSIZE,  \
                                                `CLN_GRP3_BOT_CFG_AP7_DECSIZE,  `CLN_GRP3_BOT_CFG_AP6_DECSIZE,  `CLN_GRP3_BOT_CFG_AP5_DECSIZE,   `CLN_GRP3_BOT_CFG_AP4_DECSIZE,  \
                                                `CLN_GRP3_BOT_CFG_AP3_DECSIZE,  `CLN_GRP3_BOT_CFG_AP2_DECSIZE,  `CLN_GRP3_BOT_CFG_AP1_DECSIZE,   `CLN_GRP3_BOT_CFG_AP0_DECSIZE   \
                                               }

`define   CLN_GRP3_BOT_CFG_DECMST_RST_VAL  {`CLN_GRP3_BOT_CFG_AP15_DECMST,  `CLN_GRP3_BOT_CFG_AP14_DECMST,  `CLN_GRP3_BOT_CFG_AP13_DECMST,  `CLN_GRP3_BOT_CFG_AP12_DECMST,\
                                                `CLN_GRP3_BOT_CFG_AP11_DECMST,  `CLN_GRP3_BOT_CFG_AP10_DECMST,  `CLN_GRP3_BOT_CFG_AP9_DECMST,   `CLN_GRP3_BOT_CFG_AP8_DECMST, \
                                                `CLN_GRP3_BOT_CFG_AP7_DECMST,   `CLN_GRP3_BOT_CFG_AP6_DECMST,   `CLN_GRP3_BOT_CFG_AP5_DECMST,   `CLN_GRP3_BOT_CFG_AP4_DECMST, \
                                                `CLN_GRP3_BOT_CFG_AP3_DECMST,   `CLN_GRP3_BOT_CFG_AP2_DECMST,   `CLN_GRP3_BOT_CFG_AP1_DECMST,   `CLN_GRP3_BOT_CFG_AP0_DECMST  \
                                               }

`define   CLN_GRP3_CCM_CFG_AP0_DECBASE    28'h00E_3000
`define   CLN_GRP3_CCM_CFG_AP0_DECSIZE    28'hFFF_FC00
`define   CLN_GRP3_CCM_CFG_AP0_DECMST      6'h0
`define   CLN_GRP3_CCM_CFG_AP1_DECBASE    28'h00E_3400
`define   CLN_GRP3_CCM_CFG_AP1_DECSIZE    28'hFFF_FC00
`define   CLN_GRP3_CCM_CFG_AP1_DECMST      6'h1
`define   CLN_GRP3_CCM_CFG_AP2_DECBASE    28'h00E_3800
`define   CLN_GRP3_CCM_CFG_AP2_DECSIZE    28'hFFF_FC00
`define   CLN_GRP3_CCM_CFG_AP2_DECMST      6'h2
`define   CLN_GRP3_CCM_CFG_AP3_DECBASE    28'h00E_3C00
`define   CLN_GRP3_CCM_CFG_AP3_DECSIZE    28'hFFF_FC00
`define   CLN_GRP3_CCM_CFG_AP3_DECMST      6'h3
`define   CLN_GRP3_CCM_CFG_AP4_DECBASE    28'h00E_6086
`define   CLN_GRP3_CCM_CFG_AP4_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP3_CCM_CFG_AP4_DECMST      6'h4
`define   CLN_GRP3_CCM_CFG_AP5_DECBASE    28'h00E_6087
`define   CLN_GRP3_CCM_CFG_AP5_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP3_CCM_CFG_AP5_DECMST      6'h5
`define   CLN_GRP3_CCM_CFG_AP6_DECBASE    28'h00E_6000
`define   CLN_GRP3_CCM_CFG_AP6_DECSIZE    28'hFFF_FF80
`define   CLN_GRP3_CCM_CFG_AP6_DECMST      6'h6

`define   CLN_GRP3_CCM_CFG_DECBASE_RST_VAL { \
                                                `CLN_GRP3_CCM_CFG_AP6_DECBASE,  \
                                                `CLN_GRP3_CCM_CFG_AP5_DECBASE, \
                                                `CLN_GRP3_CCM_CFG_AP4_DECBASE, \
                                                `CLN_GRP3_CCM_CFG_AP3_DECBASE, \
                                                `CLN_GRP3_CCM_CFG_AP2_DECBASE, \
                                                `CLN_GRP3_CCM_CFG_AP1_DECBASE, \
                                                `CLN_GRP3_CCM_CFG_AP0_DECBASE  \
                                               }

`define   CLN_GRP3_CCM_CFG_DECSIZE_RST_VAL { \
                                                `CLN_GRP3_CCM_CFG_AP6_DECSIZE,  \
                                                `CLN_GRP3_CCM_CFG_AP5_DECSIZE, \
                                                `CLN_GRP3_CCM_CFG_AP4_DECSIZE, \
                                                `CLN_GRP3_CCM_CFG_AP3_DECSIZE, \
                                                `CLN_GRP3_CCM_CFG_AP2_DECSIZE, \
                                                `CLN_GRP3_CCM_CFG_AP1_DECSIZE, \
                                                `CLN_GRP3_CCM_CFG_AP0_DECSIZE  \
                                               }

`define   CLN_GRP3_CCM_CFG_DECMST_RST_VAL  { \
                                                `CLN_GRP3_CCM_CFG_AP6_DECMST,  \
                                                `CLN_GRP3_CCM_CFG_AP5_DECMST, \
                                                `CLN_GRP3_CCM_CFG_AP4_DECMST, \
                                                `CLN_GRP3_CCM_CFG_AP3_DECMST, \
                                                `CLN_GRP3_CCM_CFG_AP2_DECMST, \
                                                `CLN_GRP3_CCM_CFG_AP1_DECMST, \
                                                `CLN_GRP3_CCM_CFG_AP0_DECMST  \
                                               }

`define   CLN_GRP3_REMP_CFG_AP0_DECBASE    28'h2
`define   CLN_GRP3_REMP_CFG_AP0_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP3_REMP_CFG_AP0_DECMST      6'h20

`define   CLN_GRP3_REMP_CFG_AP1_DECBASE    28'h0
`define   CLN_GRP3_REMP_CFG_AP1_DECSIZE    28'hFFF_FFFF
`define   CLN_GRP3_REMP_CFG_AP1_DECMST      6'h20

`define   CLN_GRP3_REMP_CFG_DECBASE_RST_VAL {`CLN_GRP3_REMP_CFG_AP1_DECBASE,   `CLN_GRP3_REMP_CFG_AP0_DECBASE   \
                                           }

`define   CLN_GRP3_REMP_CFG_DECSIZE_RST_VAL {`CLN_GRP3_REMP_CFG_AP1_DECSIZE,   `CLN_GRP3_REMP_CFG_AP0_DECSIZE   \
                                           }

`define   CLN_GRP3_REMP_CFG_DECMST_RST_VAL  {`CLN_GRP3_REMP_CFG_AP1_DECMST,   `CLN_GRP3_REMP_CFG_AP0_DECMST  \
                                           }


`endif //NPU_DEFINES_V_INCLUDED

