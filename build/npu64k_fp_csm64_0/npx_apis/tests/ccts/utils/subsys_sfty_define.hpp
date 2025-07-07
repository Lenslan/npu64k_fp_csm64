//=======================================================================
// COPYRIGHT (C) 2012-2023 SYNOPSYS INC.
// This software and the associated documentation are confidential and
// proprietary to Synopsys, Inc. Your use or disclosure of this software
// is subject to the terms and conditions of a written license agreement
// between you, or your company, and Synopsys, Inc. In the event of
// publications, the following notice is applicable:
//
// ALL RIGHTS RESERVED
//
// The entire notice above must be reproduced on all authorized copies.
//
// $Revision: 1.1.1.1 $
//-----------------------------------------------------------------------
#ifndef SUBSYS_DEFINE_H
#define SUBSYS_DEFINE_H

//-----------------------------------------------------------------------
// This file contains project C code
// The info below may or may not apply to your project
//-----------------------------------------------------------------------

// Defines for data manipulations
#define CORE0  0
#define CORE1  1 
#define CORE2  2 
#define CORE3  3 
#define CORE4  4 
#define CORE5  5 
#define CORE6  6 
#define CORE7  7 
#define CORE8  8 
#define CORE9  9 
#define CORE10 10
#define CORE11 11
#define CORE12 12
#define CORE13 13
#define CORE14 14
#define CORE15 15
#define CORE16 16
#define CORE17 17

#define ARCSYNC_COREID_NPXL2C0         0
#define ARCSYNC_COREID_NPXL2C1         17
#define ARCSYNC_COREID_NPXL1C0         1
#define ARCSYNC_COREID_NPXL1C1         2
#define ARCSYNC_COREID_NPXL1C2         3
#define ARCSYNC_COREID_NPXL1C3         4
#define ARCSYNC_COREID_NPXL1C4         5
#define ARCSYNC_COREID_NPXL1C5         6
#define ARCSYNC_COREID_NPXL1C6         7
#define ARCSYNC_COREID_NPXL1C7         8
#define ARCSYNC_COREID_NPXL1C8         9
#define ARCSYNC_COREID_NPXL1C9         10
#define ARCSYNC_COREID_NPXL1C10        11
#define ARCSYNC_COREID_NPXL1C11        12
#define ARCSYNC_COREID_NPXL1C12        13
#define ARCSYNC_COREID_NPXL1C13        14
#define ARCSYNC_COREID_NPXL1C14        15
#define ARCSYNC_COREID_NPXL1C15        16
#define NPU_L1GRP0                     0
#define NPU_L1GRP1                     1
#define NPU_L1GRP2                     2
#define NPU_L1GRP3                     3
#define NPU_L2GRP                      4
#define ARCSYNC_BASE_ADDR                   0xD4000000
#define ARCSYNC_BASE_ADDR_CORE_STATUS       0xD4000000
#define ARCSYNC_BASE_ADDR_CORE_RUN          0xD4002000
#define ARCSYNC_CORE_PMU_RSTCNT_BASE        0x1000 + (32 * 8) 
#define ARCSYNC_CORE_PMU_PUCNT_BASE         0x1000 + (36 * 8) 
#define ARCSYNC_CORE_PMU_PDCNT_BASE         0x1000 + (40 * 8) 
#define ARCSYNC_CORE_PMODE_BASE             0x2000 
#define ARCSYNC_CORE_STATUS_BASE            0x2C80 
#define ARCSYNC_CORE_RESET_BASE             0x2F00 
#define ARCSYNC_CORE_CLK_EN_BASE            0x3180
#define ARCSYNC_CORE_RUN_BASE               0x2280
#define ARCSYNC_CORE_RUN_NPXL2ARC0     0x2280
#define ARCSYNC_CORE_RUN_NPXL1S0       0x2284
#define ARCSYNC_CORE_RUN_NPXL1S1       0x2288
#define ARCSYNC_CORE_RUN_NPXL1S2       0x228C
#define ARCSYNC_CORE_RUN_NPXL1S3       0x2290
#define ARCSYNC_CORE_RUN_NPXL1S4       0x2294
#define ARCSYNC_CORE_RUN_NPXL1S5       0x2298
#define ARCSYNC_CORE_RUN_NPXL1S6       0x229C
#define ARCSYNC_CORE_RUN_NPXL1S7       0x22A0
#define ARCSYNC_CORE_RUN_NPXL1S8       0x22A4
#define ARCSYNC_CORE_RUN_NPXL1S9       0x22A8
#define ARCSYNC_CORE_RUN_NPXL1S10      0x22AC
#define ARCSYNC_CORE_RUN_NPXL1S11      0x22B0
#define ARCSYNC_CORE_RUN_NPXL1S12      0x22B4
#define ARCSYNC_CORE_RUN_NPXL1S13      0x22B8
#define ARCSYNC_CORE_RUN_NPXL1S14      0x22BC
#define ARCSYNC_CORE_RUN_NPXL1S15      0x22C0
#define ARCSYNC_CORE_RUN_NPXL2ARC1     0x22C4

#define ARCSYNC_NPUGRP0_PMODE          0x10DC   // 0x1000 + 44 * PP (Here PP-NUM CLUSTERS is 5) 
#define ARCSYNC_NPUGRP1_PMODE          0x10F0
#define ARCSYNC_NPUGRP2_PMODE          0x1104
#define ARCSYNC_NPUGRP3_PMODE          0x1118
#define ARCSYNC_GRP_CLK_EN             0x1014  // 0x1000 + 4 * PP                                       
#define ARCSYNC_GRP_RST                0x1028  // 0x1000 + 8 * PP      

#define ARCSYNC_MAP_VM_VRPOC_BASE      0x13000
#define ARCSYNC_VM_0                   0x0
#define ARCSYNC_VM_1                   0x1
#define ARCSYNC_VM_2                   0x2
#define ARCSYNC_VM_3                   0x3
#define ARCSYNC_VM_4                   0x4
#define ARCSYNC_VM_5                   0x5
#define ARCSYNC_VM_6                   0x6
#define ARCSYNC_VM_7                   0x7
#define ARCSYNC_VPROC_NPU0             0x0
#define ARCSYNC_VPROC_NPU1             0x1
#define ARCSYNC_VPROC_VPX0             0x2
#define ARCSYNC_VPROC_VPX1             0x3
#define ARCSYNC_VM0_EID_SEND_EVENT_BASE   0x14000
#define ARCSYNC_VM0_EID_RAISE_IRQ_BASE    0x14050
#define ARCSYNC_VM0_EID_ACK_IRQ_BASE      0x14064
#define ARCSYNC_VM0_AC_ACK_IRQ_BASE       0x14104
//#define ARCSYNC_VM0_AC_CONFIG_BASE        0x14118
#define ARCSYNC_VM0_AC_CONFIG_BASE        0x8000
#define ARCSYNC_VM0_AC_CONTROL_BASE       0x14138
#define ARCSYNC_EID_ACK_IRQ_BASE          0x4000
#define EVENT_0                           0x0
#define EVENT_1                           0x1
#define IRQ_0                           0x0
#define IRQ_1                           0x1
#define ACK_0                           0x0
#define ACK_1                           0x1
#define VPROC0                          0x0
#define VPROC1                          0x1
#define VPROC2                          0x2
// User extension aux register EVT_VM_SEL
#define AR_EVT_VM_SEL 0xf00
// User extension aux register EVT_VM_MAP
#define AR_EVT_VM_MAP 0xf01
// User extension aux register EVT_CTRL
#define AR_EVT_CTRL 0xf02
// User extension aux register EVT_FILTER_LO
#define AR_EVT_FILTER_LO 0xf04
// User extension aux register EVT_FILTER_HI
#define AR_EVT_FILTER_HI 0xf05
// User extension aux register EVT_CNT_SEL
#define AR_EVT_CNT_SEL 0xf0a
// User extension aux register EVT_CNT_VAL
#define AR_EVT_CNT_VAL 0xf0b

// AUX register for TLB Control TLBPD0
#define AR_TLBPD0 0x460
// AUX register for TLB Control TLBPD1
#define AR_TLBPD1 0x461
// AUX register for TLB Control TLBCOMMAND
#define AR_TLBCOMMAND 0x465
// AUX register for TLB Control PID
#define AR_PID 0x468

// maximum number of virtual machines
#define MAX_VM_CONTEXTS 8

//
// Virtual event types ISSUE/DONE pairs even/odd
//

// L1 virtual events
// virtual peer events 0..23
#define EVT_PEER0        0
#define EVT_PEER1        1
#define EVT_PEER2        2
#define EVT_PEER3        3
#define EVT_PEER4        4
#define EVT_PEER5        5
#define EVT_PEER6        6
#define EVT_PEER7        7
#define EVT_PEER8        8
#define EVT_PEER9        9
#define EVT_PEER10       10
#define EVT_PEER11       11
#define EVT_PEER12       12
#define EVT_PEER13       13
#define EVT_PEER14       14
#define EVT_PEER15       15
#define EVT_PEER16       16
#define EVT_PEER17       17
#define EVT_PEER18       18
#define EVT_PEER19       19
#define EVT_PEER20       20
#define EVT_PEER21       21
#define EVT_PEER22       22
#define EVT_PEER23       23
// virtual accelerators events 24..31
#define EVT_IDMA_ISSUE   24
#define EVT_IDMA_DONE    25
#define EVT_ODMA_ISSUE   26
#define EVT_ODMA_DONE    27
#define EVT_CONV_ISSUE   28
#define EVT_CONV_DONE    29
#define EVT_ACT_ISSUE    30
#define EVT_ACT_DONE     31
// 32..39 reserved
#define EVT_PARENT       40

// L2 virtual events
// child virtual events 0..23
#define EVT_CHILD0       0
#define EVT_CHILD1       1
#define EVT_CHILD2       2
#define EVT_CHILD3       3
#define EVT_CHILD4       4
#define EVT_CHILD5       5
#define EVT_CHILD6       6
#define EVT_CHILD7       7
#define EVT_CHILD8       8
#define EVT_CHILD9       9
#define EVT_CHILD10      10
#define EVT_CHILD11      11
#define EVT_CHILD12      12
#define EVT_CHILD13      13
#define EVT_CHILD14      14
#define EVT_CHILD15      15
#define EVT_CHILD16      16
#define EVT_CHILD17      17
#define EVT_CHILD18      18
#define EVT_CHILD19      19
#define EVT_CHILD20      20
#define EVT_CHILD21      21
#define EVT_CHILD22      22
#define EVT_CHILD23      23
// accelerators virtual events 24..39
#define EVT_STU0_ISSUE   24
#define EVT_STU0_DONE    25
#define EVT_STU1_ISSUE   26
#define EVT_STU1_DONE    27
#define EVT_STU2_ISSUE   28
#define EVT_STU2_DONE    29
#define EVT_STU3_ISSUE   30
#define EVT_STU3_DONE    31
#define EVT_STU4_ISSUE   32
#define EVT_STU4_DONE    33
#define EVT_STU5_ISSUE   34
#define EVT_STU5_DONE    35
#define EVT_STU6_ISSUE   36
#define EVT_STU6_DONE    37
#define EVT_STU7_ISSUE   38
#define EVT_STU7_DONE    39
// ARCSync virtual events 40..42
#define EVT_ARCSYNC_AC   40
#define EVT_ARCSYNC_EVT0 41
#define EVT_ARCSYNC_EVT1 42

//
// Physical, event EVT_INT needs to be last
//
// Physical event index for child and peer events: 2*24 events
#define EVT_PHY_CHILDPEER_BASE  0
// Physical event index for accelerator events: 16 events
#define EVT_PHY_ACC_BASE        48
// Physical event index for ARCSync events: VMNUM*4 events
#define EVT_PHY_PARARCSYNC_BASE 64

//Write signature address to write and read data from mem location to sync
#define WRITE_SIGNATURE_ADD 0xC0000000

#endif
