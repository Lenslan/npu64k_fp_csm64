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
 * tensor_gtoa_eltop_fc_prelu_inline.hpp
 *
 * File defining a tensor level prelu API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_ELTOP_FC_PRELU_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_ELTOP_FC_PRELU_INLINE_HPP_
#include "./legacy/tensor_gtoa_eltop_fc_prelu_inline_legacy.hpp"

// constructors
// Fully connected convolution + eltop + prelu from accumulator (32b/48b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_eltop_fc_prelu_params<B>::gtoa_eltop_fc_prelu_params(
    aoffset_t                  noi,           // number output channels (not vectors)
    act_bin_op_t               opi,           // eltwise binary operation to perform
    act_dtype_t                in0tp,         // primary input type
    act_dtype_t                in1tp,         // secondary input type
    act_dtype_t                outtp,         // output type
    bool                       eltact,        // first eltop then activ
    bool                       inastri)       // if true then input stream
    : gtoa_eltop_fc_act_params<B>(noi, opi, in0tp, in1tp, outtp, eltact, inastri) {
  gtoa_eltop_fc_act_params<B>::set_per_channel(ELTOP_FC_PRELU_PAR_PER_CHAN);
}

template<template<typename> class B>
void gtoa_eltop_fc_prelu_params<B>::init_prog(act_bin_op_t op, bool ea) {
  // initialize the eltwise FC PReLU microcode
  init_eltop_fc_prelu(gtoa_params<B>::hlapi, op, ea, gtoa_eltop_fc_act_params<B>::fp16scl);
}

//
// Parameter encoding functions
//
// BRB0: empty
// BRH1: postscale + asymmetric offset
// BRW1: scale
// BRW2: bias

template<template<typename> class B>
void gtoa_eltop_fc_prelu_params<B>::param_enc(
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,        // per channel bias [Cout]
                                  const tensor_t<fp_e5m10_t,1,xbuffer_t>&   posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<fp_e5m10_t,1,xbuffer_t>&   negscale,    // per channel negative scaling factor [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,        // per channel postscale[Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  gtoa_eltop_fc_act_params<B>::fp16scl = true;
  init_eltop_fc_prelu(gtoa_params<B>::hlapi,
                      gtoa_eltop_fc_act_params<B>::op,
                      gtoa_eltop_fc_act_params<B>::ea_ord,
                      gtoa_eltop_fc_act_params<B>::fp16scl);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_eltop_fc_prelu_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltop_fc_prelu_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)(post.read({j}).data)) | (((int32_t)asymm.read({j}))<<8);
        bparsh[2*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = sclpst;                             // BRH1 postscale + offset
        bparsw[1*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = ((uint32_t)posscale.read({j}).data<<16)|
          negscale.read({j}).data;                                                                    // BRW1 positive/negative scaling
        bparsw[1*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = bias.read({j}).data;                // BRW2 bias
        j++;
      }
    }
  }
}

template<template<typename> class B>
void gtoa_eltop_fc_prelu_params<B>::param_enc(
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,        // per channel bias [Cout]
                                  const tensor_t<fp_e8m7_t,1,xbuffer_t>&    posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<fp_e8m7_t,1,xbuffer_t>&    negscale,    // per channel negative scaling factor [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,        // per channel postscale[Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  gtoa_eltop_fc_act_params<B>::fp16scl = false;
  init_eltop_fc_prelu(gtoa_params<B>::hlapi,
                      gtoa_eltop_fc_act_params<B>::op,
                      gtoa_eltop_fc_act_params<B>::ea_ord,
                      gtoa_eltop_fc_act_params<B>::fp16scl);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_eltop_fc_prelu_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltop_fc_prelu_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)(post.read({j}).data)) | (((int32_t)asymm.read({j}))<<8);
        bparsh[2*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = sclpst;                             // BRH1 postscale + offset
        bparsw[1*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = ((uint32_t)posscale.read({j}).data<<16)|
          negscale.read({j}).data;                                                                    // BRW1 positive/negative scaling
        bparsw[1*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = bias.read({j}).data;                // BRW2 bias
        j++;
      }
    }
  }
}

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_ELTOP_FC_PRELU_INLINE_HPP_
