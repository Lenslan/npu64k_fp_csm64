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

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_REDUCE_PARAM_PRIV_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_REDUCE_PARAM_PRIV_HPP_
gtoa_act_params_impl_shapes shapes;     // buffer shapes
aoffset_t cmax;                         // number of channels
int red_dim;                            // spatial dimensions to reduce
bool red_accum;                         // use reduce program that support accumulate
void set_reduce_params();
void init_reduce_i(act_red_op_t opi, bool useAcc);
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_REDUCE_PARAM_PRIV_HPP_
