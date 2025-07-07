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
 * npu_tops_types.h
 *
 * File defining the NPU tops specific datatypes
 * only datatypes shared between high-level and cycle-based model
 *
 */

#ifndef NPU_TOP_TYPES_INCLUDED
#define NPU_TOP_TYPES_INCLUDED

// include slice and STU HLAPI datatypes
#include "npu_slice_types.hpp"
#include "npu_stu_hlapi.hpp"

#include <vector>

namespace npu_top {
  using namespace npu;
  using namespace npu_slice;
  using namespace npu_stu;

  //
  // Top registers
  //
  struct top_regs {
    ctrl_dma_regs<stu_hlapi_t> stu0;   // STU0 registers
    ctrl_dma_regs<stu_hlapi_t> stu1;   // STU1 registers
    ctrl_dma_regs<stu_hlapi_t> stu2;   // STU2 registers
    ctrl_dma_regs<stu_hlapi_t> stu3;   // STU3 registers
    ctrl_dma_regs<stu_hlapi_t> stu4;   // STU4 registers
    ctrl_dma_regs<stu_hlapi_t> stu5;   // STU5 registers
    ctrl_dma_regs<stu_hlapi_t> stu6;   // STU6 registers
    ctrl_dma_regs<stu_hlapi_t> stu7;   // STU7 registers
    std::vector<slice_regs>    slices; // per slice registers

    top_regs(int n) : slices(n) {
    }
  };
}

#endif
