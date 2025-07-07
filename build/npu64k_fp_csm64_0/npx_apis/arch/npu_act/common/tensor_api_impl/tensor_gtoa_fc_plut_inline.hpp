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
 * tensor_gtoa_fc_plut_inline.hpp
 *
 * File defining a tensor level fc + plut API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_FC_PLUT_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_FC_PLUT_INLINE_HPP_
#include "./legacy/tensor_gtoa_fc_plut_inline_legacy.hpp"

// constructors
// Fully connected convolution + plut from accumulator (32b/48b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_fc_plut_params<B>::gtoa_fc_plut_params(
    aoffset_t                  noi,           // number output channels (not vectors)
    act_dtype_t                intp,          // type of input
    act_dtype_t                outtp,         // type of output
    bool                       inastri,       // if true then input stream
    bool                       poscli)        // do post scaling
    : gtoa_fc_act_params<B>(noi, intp, outtp, inastri) {
  gtoa_fc_act_params<B>::set_per_channel(FC_PLUT_PAR_PER_CHAN);
  poscl = poscli;
}

template<template<typename> class B>
void gtoa_fc_plut_params<B>::init_prog() {
  // initialize the FC PLUT microcode
  init_fc_lut(gtoa_params<B>::hlapi, poscl, gtoa_fc_act_params<B>::fp16scl);
}

//
// Parameter encoding functions
//
// BRH0: optional post scale and shift
// BRH1: postscale + asymmetric offset
// BRW1: bias

template<template<typename> class B>
void gtoa_fc_plut_params<B>::param_enc(
  const tensor_t<fp_e8m23_t, 1, xbuffer_t>&  bias,     // per channel bias
  const tensor_t<prescale_t, 1, xbuffer_t>&  post,     // per channel post scale
  const tensor_t<int8_t, 1, xbuffer_t>&      asymm,    // per channel output quantization offset
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&      obuf) {   // NOLINT [runtime/references]
  gtoa_fc_act_params<B>::fp16scl = true;
  poscl = false;
  init_fc_lut(gtoa_params<B>::hlapi, poscl, gtoa_fc_act_params<B>::fp16scl);
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  //int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);       // pointer to start of BRB0 values
  int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);      // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);      // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_fc_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_act_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)post.read({j}).data) | (((int32_t)asymm.read({j}))<<8);
        fp_e5m10_t fscale((float)1.0);
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = fscale.data;               // BRH0 scale
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = sclpst;                    // BRH1 postscale + offset
        bparsw[1*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = bias.read({j}).data;       // BRW1 bias
        j++;
      }
    }
  }
}

template<template<typename> class B>
void gtoa_fc_plut_params<B>::param_enc(
  const tensor_t<fp_e8m23_t, 1, xbuffer_t>&  bias,   // per channel bias
  const tensor_t<fp_e5m10_t, 1, xbuffer_t>&  scale,  // per channel scaling factor
  const tensor_t<prescale_t, 1, xbuffer_t>&  post,   // per channel post scale
  const tensor_t<int8_t, 1, xbuffer_t>&      asymm,  // per channel output quantization offset
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&    obuf) {   // NOLINT [runtime/references]
  gtoa_fc_act_params<B>::fp16scl = true;
  poscl = true;
  init_fc_lut(gtoa_params<B>::hlapi, poscl, gtoa_fc_act_params<B>::fp16scl);
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  //int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);       // pointer to start of BRB0 values
  int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);      // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);      // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_fc_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_act_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)post.read({j}).data) | (((int32_t)asymm.read({j}))<<8);
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = scale.read({j}).data;      // BRH0 scale
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = sclpst;                    // BRH1 postscale + offset
        bparsw[1*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = bias.read({j}).data;       // BRW1 bias
        j++;
      }
    }
  }
}

template<template<typename> class B>
void gtoa_fc_plut_params<B>::param_enc(
  const tensor_t<fp_e8m23_t, 1, xbuffer_t>&  bias,   // per channel bias
  const tensor_t<fp_e8m7_t, 1, xbuffer_t>&   scale,  // per channel scaling factor
  const tensor_t<prescale_t, 1, xbuffer_t>&  post,   // per channel post scale
  const tensor_t<int8_t, 1, xbuffer_t>&      asymm,  // per channel output quantization offset
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&    obuf) {   // NOLINT [runtime/references]
  gtoa_fc_act_params<B>::fp16scl = false;
  poscl = true;
  init_fc_lut(gtoa_params<B>::hlapi, poscl, gtoa_fc_act_params<B>::fp16scl);
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  //int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);       // pointer to start of BRB0 values
  int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);      // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);      // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_fc_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_act_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)post.read({j}).data) | (((int32_t)asymm.read({j}))<<8);
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = scale.read({j}).data;      // BRH0 scale
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = sclpst;                    // BRH1 postscale + offset
        bparsw[1*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = bias.read({j}).data;       // BRW1 bias
        j++;
      }
    }
  }
}

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_FC_PLUT_INLINE_HPP_
