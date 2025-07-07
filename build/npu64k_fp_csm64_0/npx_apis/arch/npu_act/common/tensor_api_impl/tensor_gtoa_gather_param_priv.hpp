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

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GATHER_PARAM_PRIV_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GATHER_PARAM_PRIV_HPP_
gtoa_act_params_impl_shapes shapes;     // buffer shapes
shape<3> inner;    // shape of inner tensor [C2][C1][C0]
shape<2> ishp;     // shape of the outer dictionary tensor [H][W]
shape<2> oshp;     // shape of the outer index and output tensor [Y][X]
aoffset_t crnd;    // inner channels rounded up to ISIZE
aoffset_t vrnd;    // inner X rounded up to TNSVSIZE
aoffset_t vrndc;   // inner X rounded up to ISIZE
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GATHER_PARAM_PRIV_HPP_
