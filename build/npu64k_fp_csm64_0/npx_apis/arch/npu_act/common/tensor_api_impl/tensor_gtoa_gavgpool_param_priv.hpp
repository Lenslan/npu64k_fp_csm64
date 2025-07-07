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

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GAVGPOOL_PARAM_PRIV_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GAVGPOOL_PARAM_PRIV_HPP_
gtoa_act_params_impl_shapes shapes;     // buffer shapes
aoffset_t                   cmax;       // number of channels
shape<3>                    ishp;       // input shape
shape<3>                    oshp;       // output shape
act_dtype_t                 itp;        // input datatype
act_dtype_t                 otp;        // output datatype
bool                        mode;       // legacy(false) or v2(true)
void set_gavgpool_params();
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GAVGPOOL_PARAM_PRIV_HPP_
