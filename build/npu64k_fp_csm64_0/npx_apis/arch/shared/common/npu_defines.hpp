/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2023 Synopsys, Inc.                              **/
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

/*
 * npu_defines.h
 *
 * File defining the fixed configuration parameters of the NPU
 *
 */

#ifndef SHARED_COMMON_NPU_DEFINES_HPP_
#define SHARED_COMMON_NPU_DEFINES_HPP_

#include "npu_config.hpp"  // NOLINT [build/include_subdir]

// include memory map
#include "npu_mem_map.hpp"  // NOLINT [build/include_subdir]

// spatial vectorization size: derived from npu_slice_mac

// number of parallel coefficient decoders
#define NUM_COEF_QUEUE 8

// max number of loops in the HLAPI
#define CONV_HLAPI_LOOPS 8
#define CONV_FM_LOOPS    6
#define CONV_AM_LOOPS    3
// #define CONV_HLP_GP      7
// #define CONV_HLP_NO      6
// #define CONV_HLP_NI      5
// #define CONV_HLP_FD      4
// #define CONV_HLP_FH      3
// #define CONV_HLP_FW      2
// #define CONV_HLP_INN     1
// #define CONV_HLP_ONN     0

// number of dimensions in feature-map address generation
#define NUM_FM_LOOPS     6

// number of dimensions in the activation unit
#define ACT_HLAPI_LOOPS  3
#define ACT_FM_LOOPS     6
#define ACT_AM_LOOPS     4
// maximum number of instruction in a program
#define ACT_PROG_LEN    18
// number of scalar/parameter/accumulator registers in activation accelerator
#define ACT_SREG_NUM     8
#define ACT_SREG_SAVE    4
#define ACT_AREG_NUM     8
#define ACT_BREG_NUM     8
// size of activation look-up table
#define ACT_LUT_SIZE    16
// ALU1 enable
//#define ACT_HAS_ALU1
// stride0 support
//#define NPU_GTOA_HAS_STR0

// number of lanes from DMA to access VM; ixpix_t per lane
#define DMA_VM_LANES     1

// number of lanes from STU to access XM; ixpix_t per lane
#define STU_XM_LANES     4

// Maximum size of a compress group:
// 3 bytes sum, 4*2 bytes available, 4 * ISIZE nonzero pixels
#define CPS_GROUP_SIZE (3 + 4 * 2 + 4 * ISIZE)

// CSM bank interleave at 512B bounaries
#define CSM_BANK_INTERLEAVE_L2 9
#define CSM_BANK_INTERLEAVE    (1 << CSM_BANK_INTERLEAVE_L2)

// Delay cycles on reading a memory <arb>,<addr>,<data>
#define MEM_RD_DELAY     1

// DMA control bits
#define CTRL_DMA_HALT   (1<<0)
#define CTRL_DMA_RESET  (1<<1)
#define CTRL_DMA_CLKFRC (1<<2)

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
// physical event index for child and peer events: 2*24 events
#define EVT_PHY_CHILDPEER_BASE  0
// physical event index for accelerator events: 16 events
#define EVT_PHY_ACC_BASE        48
// physical event index for ARCSync events: VMNUM*4 events
#define EVT_PHY_PARARCSYNC_BASE 64

#ifdef SYSTEMC
// SystemC modelling events only
#define EVT_PHY_NONE            110
// 16+1 interrupts
#define EVT_PHY_INT             111
#endif


// Utilities
#define RDIV_UP(m, b)  (((m) + (b) -1) / (b))
#define ROUND_UP(m, b) (RDIV_UP(m, b) * (b))

#define __AN              4
#ifndef RTL_ARC
  #define NPU_TAPI_ST_PACK_PRAGMA
#endif

#ifdef NPU_TAPI_ST_PACK_PRAGMA
  #define __PACKED
  #define __ALIGNED(n)
  #define __PALIGNED(n)
#else
  #define __PACKED      __attribute__((packed))
  #define __ALIGNED(n)  __attribute__ ((aligned(n)))
  #define __PALIGNED(n) __attribute__ ((packed, aligned(n)))
#endif

#ifndef NPU_FINST_VERIF
  #define NPU_FINST_VERIF 0
#endif

#ifndef NPU_MLI_TAPI_EN
  #define NPU_MLI_TAPI_EN 1
#endif
// #define __PACKED

// Feature versioning
#define NPU_HAS_PACKMODE (NPU_VER_IS_VIC2_GA)

// Debug
//- gloabl systemc model debug flag
#ifndef NPU_SYSC_DEBUG
  #define NPU_SYSC_DEBUG 1
#endif
#if NPU_SYSC_DEBUG
  #define DBGV(...) do { __VA_ARGS__; } while (0);
#else
  #define DBGV(...)
#endif

// Platform
#ifndef NPU_PLATFORM
  #define NPU_PLATFORM 1
#endif

// Utilities
#define NRDIV_UP(v, b) ((v) + (b) - 1) / (b)
#define NRND_UP(v, b) (b) * (NRDIV_UP(v, b))

#endif  // SHARED_COMMON_NPU_DEFINES_HPP_
