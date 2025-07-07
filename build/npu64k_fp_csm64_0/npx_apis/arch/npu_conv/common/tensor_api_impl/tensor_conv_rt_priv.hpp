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
 * tensor_conv_rt_priv.hpp
 *
 * File defining the private members of the tensor convolution run-time class
 *
 */

#ifndef NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_RT_PRIV_HPP_
#define NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_RT_PRIV_HPP_
public:
// data members
conv_hlapi_t                 hlapi;   // HLAPI parameters
ctrl_dma_regs<conv_hlapi_t>* mmio;    // base address of accelerator MMIO registers
#endif  // NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_RT_PRIV_HPP_
