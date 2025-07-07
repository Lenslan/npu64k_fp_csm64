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
 * npu_stu_hlapi.h
 *
 * File defining the STU HLAPI structure
 *
 */
#ifndef NPU_STU_HLAPI_INCLUDED
#define NPU_STU_HLAPI_INCLUDED


#include "npu_hlapi.hpp"


#define STU_MAJOR 0x02
#define STU_MINOR 0x00


namespace npu_stu {
//
// import global NPU types
//
using namespace npu;


/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// STU HLAPI top-level
//
/////////////////////////////////////////////////////////////////////////////////////////////////////
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
  
  struct stu_hlapi_i_t {
    hlapi_i_t                        common;          // Common input parameters
    // XM AGU input sequence
    hlapi_stu_agu_t                  xmi_seq;         // XM access parameters
    // XM AGU output sequence
    hlapi_stu_agu_t                  xmo_seq;         // XM access parameters
  } __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
struct stu_hlapi_t {
  stu_hlapi_i_t       i;     // inputs at the lowest address
  hlapi_io_t          io;    // input&outputs in between input and output
  hlapi_o_t           o;     // outputs only at highest address
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

// ensure all STU HLAPIs have same size on all platforms
//static_assert(sizeof(stu_hlapi_t) == 240, "unexpected STU HLAPI size");

}
#endif
