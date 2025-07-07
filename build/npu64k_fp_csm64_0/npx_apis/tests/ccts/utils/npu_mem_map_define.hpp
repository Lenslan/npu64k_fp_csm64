/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2022 Synopsys, Inc.                              **/
/** All Rights Reserved.                                                **/
/**                                                                     **/
/** This Synopsys software and all associated documentation are         **/
/** proprietary to Synopsys, Inc. and may only be used pursuant to the  **/
/** terms and conditions of a written license agreement with Synopsys,  **/
/** Inc. All other use, reproduction, modification, or distribution of  **/
/** this Synopsys software or the associated documentation is strictly  **/
/** prohibited.                                                         **/
/**                                                                     **/
/*************************************************************************/

//local CPU core address map
#ifndef NPU_ARC_DCCM_BASE
#define NPU_ARC_DCCM_BASE           0x70000000
#endif
#define LOCAL_PERI_BASE             0xF0000000
//L2 local peripheral
#define L2_DM_OFFSET                0x0
#define L2_ISTU0_MMIO_OFFSET        0x080000
#define L2_OSTU0_MMIO_OFFSET        0x081000
#define L2_ISTU1_MMIO_OFFSET        0x082000
#define L2_OSTU1_MMIO_OFFSET        0x083000
#define L2_ISTU2_MMIO_OFFSET        0x084000
#define L2_OSTU2_MMIO_OFFSET        0x085000
#define L2_ISTU3_MMIO_OFFSET        0x086000
#define L2_OSTU3_MMIO_OFFSET        0x087000
#define USTU0_MMIO_OFFSET           0x080000
#define USTU1_MMIO_OFFSET           0x081000
#define USTU2_MMIO_OFFSET           0x082000
#define USTU3_MMIO_OFFSET           0x083000
#define USTU4_MMIO_OFFSET           0x084000
#define USTU5_MMIO_OFFSET           0x085000
#define USTU6_MMIO_OFFSET           0x086000
#define USTU7_MMIO_OFFSET           0x087000

#define L2_PERI_DM_BASE             (LOCAL_PERI_BASE + L2_DM_OFFSET        )
#define L2_ISTU0_MMIO_BASE          (LOCAL_PERI_BASE + L2_ISTU0_MMIO_OFFSET)
#define L2_OSTU0_MMIO_BASE          (LOCAL_PERI_BASE + L2_OSTU0_MMIO_OFFSET)
#define L2_ISTU1_MMIO_BASE          (LOCAL_PERI_BASE + L2_ISTU1_MMIO_OFFSET)
#define L2_OSTU1_MMIO_BASE          (LOCAL_PERI_BASE + L2_OSTU1_MMIO_OFFSET)
#define L2_ISTU2_MMIO_BASE          (LOCAL_PERI_BASE + L2_ISTU2_MMIO_OFFSET)
#define L2_OSTU2_MMIO_BASE          (LOCAL_PERI_BASE + L2_OSTU2_MMIO_OFFSET)
#define L2_ISTU3_MMIO_BASE          (LOCAL_PERI_BASE + L2_ISTU3_MMIO_OFFSET)
#define L2_OSTU3_MMIO_BASE          (LOCAL_PERI_BASE + L2_OSTU3_MMIO_OFFSET)
//L1 local peripheral
#define L1_DM_OFFSET                0x0
#define L1_IDMA_MMIO_OFFSET         0x080000
#define L1_ODMA_MMIO_OFFSET         0x081000
#define L1_CONV_MMIO_OFFSET         0x082000
#define L1_GTOA_MMIO_OFFSET         0x083000
#define L1_SFTY_MMIO_OFFSET         0x084000
#define L1_AM_OFFSET                0x100000
#define L1_VM_OFFSET                0x200000

#define L1_PERI_DM_BASE             (LOCAL_PERI_BASE + L1_DM_OFFSET       )
#define L1_PERI_IDMA_MMIO_BASE      (LOCAL_PERI_BASE + L1_IDMA_MMIO_OFFSET)
#define L1_PERI_ODMA_MMIO_BASE      (LOCAL_PERI_BASE + L1_ODMA_MMIO_OFFSET)
#define L1_PERI_CONV_MMIO_BASE      (LOCAL_PERI_BASE + L1_CONV_MMIO_OFFSET)
#define L1_PERI_GTOA_MMIO_BASE      (LOCAL_PERI_BASE + L1_GTOA_MMIO_OFFSET)
#define L1_PERI_SFTY_MMIO_BASE      (LOCAL_PERI_BASE + L1_SFTY_MMIO_OFFSET)
#define L1_PERI_AM_BASE             (LOCAL_PERI_BASE + L1_AM_OFFSET       )
#define L1_PERI_VM_BASE             (LOCAL_PERI_BASE + L1_VM_OFFSET       )
//End CPU core address map
//
//Inter Cluster address map
//Global SCMs(IC0)
#define INTER_CLST0_BASE            0xB0000000
#define IC_NPU0_SCM_BASE            (INTER_CLST0_BASE + 0x1000000 * 0)
#define IC_NPU1_SCM_BASE            (INTER_CLST0_BASE + 0x1000000 * 1)
//...

//Global control(IC1)
#define INTER_CLST1_BASE            0xD0000000
#define IC_NPU0_L2_PERI_BASE        (INTER_CLST1_BASE + 0x400000 * 0)
#define IC_NPU1_L2_PERI_BASE        (INTER_CLST1_BASE + 0x400000 * 1)
//...
#define IC_ARCSYNC_MMIO_BASE        (INTER_CLST1_BASE + 0x400000 * 16)

//Local Cluster address map
#define LOCAL_CLST0_BASE            0xE0000000
#define GET_LC_SL_PERI_BASE(x)      (LOCAL_CLST0_BASE + 0x400000 * (x%NPU_NUM_SLC_PER_GRP + 4*(x/NPU_NUM_SLC_PER_GRP)))
#define LC_SL0_PERI_BASE            GET_LC_SL_PERI_BASE(0)
#define LC_SL1_PERI_BASE            GET_LC_SL_PERI_BASE(1)
#define LC_SL2_PERI_BASE            GET_LC_SL_PERI_BASE(2)
#define LC_SL3_PERI_BASE            GET_LC_SL_PERI_BASE(3)
#define LC_SL4_PERI_BASE            GET_LC_SL_PERI_BASE(4)
#define LC_SL5_PERI_BASE            GET_LC_SL_PERI_BASE(5)
#define LC_SL6_PERI_BASE            GET_LC_SL_PERI_BASE(6)
#define LC_SL7_PERI_BASE            GET_LC_SL_PERI_BASE(7)
#define LC_SL8_PERI_BASE            GET_LC_SL_PERI_BASE(8)
#define LC_SL9_PERI_BASE            GET_LC_SL_PERI_BASE(9)
#define LC_SL10_PERI_BASE           GET_LC_SL_PERI_BASE(10)
#define LC_SL11_PERI_BASE           GET_LC_SL_PERI_BASE(11)
#define LC_SL12_PERI_BASE           GET_LC_SL_PERI_BASE(12)
#define LC_SL13_PERI_BASE           GET_LC_SL_PERI_BASE(13)
#define LC_SL14_PERI_BASE           GET_LC_SL_PERI_BASE(14)
#define LC_SL15_PERI_BASE           GET_LC_SL_PERI_BASE(15)
#define LC_SL16_PERI_BASE           GET_LC_SL_PERI_BASE(16)
#define LC_SL17_PERI_BASE           GET_LC_SL_PERI_BASE(17)
#define LC_SL18_PERI_BASE           GET_LC_SL_PERI_BASE(18)
#define LC_SL19_PERI_BASE           GET_LC_SL_PERI_BASE(19)
#define LC_SL20_PERI_BASE           GET_LC_SL_PERI_BASE(20)
#define LC_SL21_PERI_BASE           GET_LC_SL_PERI_BASE(21)
#define LC_SL22_PERI_BASE           GET_LC_SL_PERI_BASE(22)
#define LC_SL23_PERI_BASE           GET_LC_SL_PERI_BASE(23)
#define LC_L2_PERI_BASE             (LOCAL_CLST0_BASE + 0x400000 * 24)
#define LC_CLN_AUX_BASE             (LOCAL_CLST0_BASE + 0x400000 * 25) //+0x6400000
#define LC_CSM_BASE                 (LOCAL_CLST0_BASE + 0x08000000)
//#define LC_CSM_BASE                 0xD0000000

#define LC_L2_PERI_DM_BASE          (LC_L2_PERI_BASE + L2_DM_OFFSET     )
#define LC_L2_ARC1_DM_BASE          (LC_L2_PERI_DM_BASE + 0X40000       )
#define LC_L2_ISTU0_MMIO_BASE       (LC_L2_PERI_BASE + L2_ISTU0_MMIO_OFFSET)
#define LC_L2_OSTU0_MMIO_BASE       (LC_L2_PERI_BASE + L2_OSTU0_MMIO_OFFSET)
#define LC_L2_ISTU1_MMIO_BASE       (LC_L2_PERI_BASE + L2_ISTU1_MMIO_OFFSET)
#define LC_L2_OSTU1_MMIO_BASE       (LC_L2_PERI_BASE + L2_OSTU1_MMIO_OFFSET)
#define LC_L2_ISTU2_MMIO_BASE       (LC_L2_PERI_BASE + L2_ISTU2_MMIO_OFFSET)
#define LC_L2_OSTU2_MMIO_BASE       (LC_L2_PERI_BASE + L2_OSTU2_MMIO_OFFSET)
#define LC_L2_ISTU3_MMIO_BASE       (LC_L2_PERI_BASE + L2_ISTU3_MMIO_OFFSET)
#define LC_L2_OSTU3_MMIO_BASE       (LC_L2_PERI_BASE + L2_OSTU3_MMIO_OFFSET)

#define USTU0_MMIO_BASE             (LC_L2_PERI_BASE + USTU0_MMIO_OFFSET)
#define USTU1_MMIO_BASE             (LC_L2_PERI_BASE + USTU1_MMIO_OFFSET)
//SLICE 0
#define LC_SL0_PERI_DM_BASE         (LC_SL0_PERI_BASE + L1_DM_OFFSET       )
#define LC_SL0_IDMA_MMIO_BASE       (LC_SL0_PERI_BASE + L1_IDMA_MMIO_OFFSET)
#define LC_SL0_ODMA_MMIO_BASE       (LC_SL0_PERI_BASE + L1_ODMA_MMIO_OFFSET)
#define LC_SL0_CONV_MMIO_BASE       (LC_SL0_PERI_BASE + L1_CONV_MMIO_OFFSET)
#define LC_SL0_GTOA_MMIO_BASE       (LC_SL0_PERI_BASE + L1_GTOA_MMIO_OFFSET)
#define LC_SL0_SFTY_MMIO_BASE       (LC_SL0_PERI_BASE + L1_SFTY_MMIO_OFFSET)
#define LC_SL0_AM_BASE              (LC_SL0_PERI_BASE + L1_AM_OFFSET       )
#define LC_SL0_VM_BASE              (LC_SL0_PERI_BASE + L1_VM_OFFSET       )
//SLICE 1
#define LC_SL1_PERI_DM_BASE         (LC_SL1_PERI_BASE + L1_DM_OFFSET       )
#define LC_SL1_IDMA_MMIO_BASE       (LC_SL1_PERI_BASE + L1_IDMA_MMIO_OFFSET)
#define LC_SL1_ODMA_MMIO_BASE       (LC_SL1_PERI_BASE + L1_ODMA_MMIO_OFFSET)
#define LC_SL1_CONV_MMIO_BASE       (LC_SL1_PERI_BASE + L1_CONV_MMIO_OFFSET)
#define LC_SL1_GTOA_MMIO_BASE       (LC_SL1_PERI_BASE + L1_GTOA_MMIO_OFFSET)
#define LC_SL1_SFTY_MMIO_BASE       (LC_SL1_PERI_BASE + L1_SFTY_MMIO_OFFSET)
#define LC_SL1_AM_BASE              (LC_SL1_PERI_BASE + L1_AM_OFFSET       )
#define LC_SL1_VM_BASE              (LC_SL1_PERI_BASE + L1_VM_OFFSET       )
//SLICE ...
//
// cln auxs 
#define LC_CLUSTER_BUILD            (LC_CLN_AUX_BASE + (0x0CF << 4))
#define LC_CLNR_ADDR_ADDR           (LC_CLN_AUX_BASE + (0x640 << 4))
#define LC_CLNR_DATA                (LC_CLN_AUX_BASE + (0x641 << 4))
#define LC_CLNR_DATA_NXT            (LC_CLN_AUX_BASE + (0x642 << 4))
#define LC_GLOBAL_CLK_GATE_DIS      (LC_CLN_AUX_BASE + (0x9A9 << 4))
#define LC_CLNR_BCR_0               (LC_CLN_AUX_BASE + (0xF61 << 4))
#define LC_CLNR_BCR_1               (LC_CLN_AUX_BASE + (0xF62 << 4))
#define LC_CLNR_BCR_2               (LC_CLN_AUX_BASE + (0xF63 << 4))
#define LC_CLNR_SCM_BCR_0           (LC_CLN_AUX_BASE + (0xF64 << 4))
#define LC_CLNR_SCM_BCR_1           (LC_CLN_AUX_BASE + (0xF65 << 4))

#define LC_CLN_MST_NOC_0_0_ADDR     (LC_CLN_AUX_BASE + 0x124)
#define LC_CLN_MST_NOC_0_0_SIZE     (LC_CLN_AUX_BASE + 0x125)
#define LC_CLN_MST_NOC_0_1_ADDR     (LC_CLN_AUX_BASE + 2560)

#define LC_CLNR_SHMEM_ADDR          (LC_CLN_AUX_BASE + 0x0C8)
#define LC_CLNR_SHMEM_SIZE          (LC_CLN_AUX_BASE + 0x0C9)

#define LC_CLNR_MST_CCM_0_0_ADDR    (LC_CLN_AUX_BASE + 0x300)
#define LC_CLNR_MST_CCM_0_0_SIZE    (LC_CLN_AUX_BASE + 0x301)
#define LC_CLNR_MST_CCM_1_0_ADDR    (LC_CLN_AUX_BASE + 0x308)
#define LC_CLNR_MST_CCM_1_0_SIZE    (LC_CLN_AUX_BASE + 0x309)




//local SCM

