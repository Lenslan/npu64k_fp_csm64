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

#ifndef SHARED_COMMON_TENSOR_API_IMPL_TENSOR_DMA_RT_LIST_PRIV_HPP_
#define SHARED_COMMON_TENSOR_API_IMPL_TENSOR_DMA_RT_LIST_PRIV_HPP_
private:
bool                            ini;  // if false then empty list
bool                            tps;  // if true then STU typ else iDMA/oDMA
// pointer to head of the list
union {
  dma_hlapi_t*                  d;
  stu_hlapi_t*                  s;
} head;
// pointer to tail of the list
union {
  dma_hlapi_t*                  d;
  stu_hlapi_t*                  s;
} tail;
// pointer to MMIO registers
union {
  ctrl_dma_regs<dma_hlapi_t>*   d;
  ctrl_dma_regs<stu_hlapi_t>*   s;
} mmio;
#endif  // SHARED_COMMON_TENSOR_API_IMPL_TENSOR_DMA_RT_LIST_PRIV_HPP_
