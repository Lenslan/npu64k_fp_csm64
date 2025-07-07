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

#ifndef TENSOR_GTOA_ACT_PARAM_PRIV_HPP_         // [NOLINT]
#define TENSOR_GTOA_ACT_PARAM_PRIV_HPP_         // [NOLINT]

protected:
  gtoa_act_params_impl_shapes shapes;  // buffer shapes
  aoffset_t                   cmax;    // number of channels
  aoffset_t                   mpstr;   // maxpool stride
  shape<3>                    str;     // output stride
  bool                        fp16scl;  // scaling factor is fp16
  inline void set_per_channel(aoffset_t p) {
    // multiply by number of per channel parameters
    shapes.pshape[0] = shapes.pshape[0]*p;
  }
  // pure virtual function to initialeze the activation function specific microcode
  virtual void init_prog(act_alay_t l) = 0;
  void set_shapes();
  int pool_overlap;
  act_pool_mode_t pmode;
  act_pool_size_t psize;

#endif    // TENSOR_GTOA_ACT_PARAM_PRIV_HPP_       // [NOLINT]
