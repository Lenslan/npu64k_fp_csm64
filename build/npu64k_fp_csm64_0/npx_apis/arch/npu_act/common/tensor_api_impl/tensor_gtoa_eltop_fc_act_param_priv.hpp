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

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_ELTOP_FC_ACT_PARAM_PRIV_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_ELTOP_FC_ACT_PARAM_PRIV_HPP_

protected:
gtoa_act_params_impl_shapes shapes;  // buffer shapes
aoffset_t                   cmax;    // number of channels
bool                        ea_ord;  // ordering of eltwise and activation function
bool                        fp16scl; // scaling factor is fp16
inline void set_per_channel(aoffset_t p) {
  // multiply by number of per channel parameters
  shapes.pshape[0] = shapes.pshape[0]*p;
}
// pure virtual function to initialeze the activation function specific microcode
virtual void init_prog(act_bin_op_t o, bool ea) = 0;
void set_shapes();
private:
act_bin_op_t                op;

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_ELTOP_FC_ACT_PARAM_PRIV_HPP_
