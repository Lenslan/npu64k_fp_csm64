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
 * tensor_conv_param_priv.hpp
 *
 * NPU specific implementation of the private members of the convolution parameter object
 *
 */

#ifndef NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_PARAM_PRIV_HPP_
#define NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_PARAM_PRIV_HPP_
protected:
//
// implementation specific private data members
//
conv_params_impl_spec             impl_spec; // implementation specifics
impl_spec_container_t<B>          tens;      // tensor information
impl_spec_container_t<B>          tensb;     // tensor information for secondary tensor matmat mode
conv_params_impl_shapes           shapes;    // tensor shapes
conv_params_impl_main             hlapi;     // runtime parameters
bool                              use_acc;   // use input accumulator
bool                              keep_acc;  // keep output accumulator
fm_cfg_t                          fm_tp;     // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
cf_cfg_t                          cf_tp;     // coefficient type: cf_cfg_4b_zp_e, cf_cfg_4b_nozp_e, cf_cfg_8b_zp_e, cf_cfg_8b_nozp_e, cf_cfg_16b_e
int                               pck_mpy;   // packing multiplier
#endif  // NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_PARAM_PRIV_HPP_
