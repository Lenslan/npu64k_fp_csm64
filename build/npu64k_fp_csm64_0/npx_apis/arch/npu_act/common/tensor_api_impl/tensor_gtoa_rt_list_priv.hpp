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

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_RT_LIST_PRIV_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_RT_LIST_PRIV_HPP_
private:
bool                            ini;   // if false then empty list
// pointer to head of the list
act_hlapi_t*                    head;
// pointer to tail of the list
act_hlapi_t*                    tail;
// pointer to MMIO registers
ctrl_dma_regs<act_hlapi_t>*     mmio;
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_RT_LIST_PRIV_HPP_
