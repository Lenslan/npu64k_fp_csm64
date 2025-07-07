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
 * npu_slices_types.h
 *
 * File defining the NPU slices specific datatypes
 * only datatypes shared between high-level and cycle-based model
 *
 */

#ifndef NPU_SLICE_TYPES_INCLUDED
#define NPU_SLICE_TYPES_INCLUDED

// include DMA and convolution HLPIA datatypes
#include "npu_types.hpp"
#include "npu_dma_hlapi.hpp"
#include "npu_conv_hlapi.hpp"
#include "npu_act_hlapi.hpp"


namespace npu_slice {
  using namespace npu;
  using namespace npu_conv;
  using namespace npu_act;
  using namespace npu_idma;
  using namespace npu_odma;

  //
  // Slice regisers
  //
  struct slice_regs {
    ctrl_dma_regs<conv_hlapi_t> conv;
    ctrl_dma_regs<act_hlapi_t>  act;
    ctrl_dma_regs<dma_hlapi_t>  idma;
    ctrl_dma_regs<dma_hlapi_t>  odma;
  };
}

#endif
