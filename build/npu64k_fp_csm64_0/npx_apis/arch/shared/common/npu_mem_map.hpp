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
 * npu_mem_map.hpp
 *
 * File defining the base address of the NPU
 *
 */

#ifndef NPU_MEM_MAP_INCLUDED
#define NPU_MEM_MAP_INCLUDED

//
// Base addresses
//

// base address for fast ARC access to DCCM
#define NPU_FAST_DCCM_BASE         ((char*)NPU_ARC_DCCM_BASE)
// slice local peripheral bus access
#define NPU_INTRA_SLICE_DCCM_BASE  ((char*)0xf0000000)
#define NPU_INTRA_SLICE_IDMA_BASE  ((char*)0xf0080000)
#define NPU_INTRA_SLICE_ODMA_BASE  ((char*)0xf0081000)
#define NPU_INTRA_SLICE_CONV_BASE  ((char*)0xf0082000)
#define NPU_INTRA_SLICE_GTOA_BASE  ((char*)0xf0083000)
#define NPU_INTRA_SLICE_ISTU_BASE  ((char*)0xf0080000)
#define NPU_INTRA_SLICE_OSTU_BASE  ((char*)0xf0081000)
#define NPU_INTRA_SLICE_AM_BASE    ((char*)0xf0100000)
#define NPU_INTRA_SLICE_VM_BASE    ((char*)0xf0200000)

// NPU peripheral buses via CLN
#define NPU_INTER_SLICE_BASE       ((char*)0xe0000000)
#define NPU_INTER_STU_BASE         ((char*)0xe6080000)

// NPU CSM
#define NPU_CSM_BASE               ((char*)0xe8000000)

// | NPU_SLICE_MEM | AM size | VM size |
// | ------------- | ------- | ------- |
// |     0         | 64KB    | 256KB   |
// |     1         | 128KB   | 256KB   |
// |     2         | 128KB   | 512KB   |
// |     2         | 32KB    | 128KB   |
#if (NPU_SLICE_MEM == 0)
    #define NPU_VM_SIZE           0x00040000
    #define NPU_AM_SIZE           0x00010000
#elif (NPU_SLICE_MEM == 1)
    #define NPU_VM_SIZE           0x00040000
    #define NPU_AM_SIZE           0x00020000
#elif (NPU_SLICE_MEM == 2)
    #define NPU_VM_SIZE           0x00080000
    #define NPU_AM_SIZE           0x00020000
#elif (NPU_SLICE_MEM == 3)
    #define NPU_VM_SIZE           0x00020000
    #define NPU_AM_SIZE           0x00008000
#else
    #error Not supported memory config(NPU_SLICE_MEM)
#endif

#define NPU_DCCM_SIZE         0x00008000

#endif
