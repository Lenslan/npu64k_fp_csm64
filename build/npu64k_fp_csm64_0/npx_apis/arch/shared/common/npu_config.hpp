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
 * npu_config.h
 *
 * File defining the configuration of the NPU
 *
 */

#ifndef NPU_CONFIG_INCLUDED
#define NPU_CONFIG_INCLUDED

//
// Configuration
//

// external configuration with user specified configuration
#include "npu_ext_config.hpp"

//Check config
#if   !defined(NPU_SLICE_NUM)   || !defined(NPU_SLICE_MAC)    \
   || !defined(NPU_SLICE_DSIZE) || !defined(NPU_SLICE_ISIZE)   \
   || !defined(NPU_CSM_SIZE)    || !defined(NPU_CSM_BANKS) 
  #error "ERROR: definitions in npu_ext_config.hpp is NOT completed!"
#endif

// AXI port width
#define AXI_PORT_WIDTH (ISIZE * 4 * 8)
#define AXI_PORT_WIDTH_BYTES (AXI_PORT_WIDTH/8)

// AXI 4K boundary
#define AXI_BOUNDARY 0x1000

// the burst length
#define AXI_MAX_BURST_SIZE_BEATS 16

// 16KB axi2axi buffer size for stu
#define STU_AXI2AXI_BUFFER_SIZE (16*1024)

// definition of the width of the primitive datatype pix_t
#if (NPU_SLICE_DSIZE==8)  //  8-bit HW datapath
  #define CFG_8B
#else                    // 12-bit HW datapath
  #define CFG_12B
#endif
#define BSIZE NPU_SLICE_DSIZE
#define ISIZE NPU_SLICE_ISIZE
#define VSIZE NPU_SLICE_VSIZE

// number of VM memory banks
#define VM_NUM_BANKS NPU_SLICE_VM_BANKS

// CSM
#define CSM_SIZE         NPU_CSM_SIZE
#define CSM_NUM_BANKS    NPU_CSM_BANKS

#endif //NPU_CONFIG_INCLUDED


