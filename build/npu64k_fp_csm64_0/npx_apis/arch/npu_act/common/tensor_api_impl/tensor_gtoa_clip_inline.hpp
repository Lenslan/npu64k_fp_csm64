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

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CLIP_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CLIP_INLINE_HPP_
/*
 * tensor_gtoa_clip_inline.hpp
 *
 * File defining a tensor level clip API base on the generic tensor operation API
 *
 */
#define HLAPI gtoa_params<B>::hlapi

// constructors
template<template<typename> class B>
gtoa_clip_params<B>::gtoa_clip_params(
                                      // number output channels (not vectors)
                                      aoffset_t noi,
                                      // output shape
                                      const shape<3>& oshpi,
                                      // output stride
                                      const shape<3>& ostr,
                                      // type of primary input
                                      act_dtype_t intp,
                                      // type of output
                                      act_dtype_t outtp,
                                      // if true then input stream directly from convolution
                                      bool  inastri)
: gtoa_act_params<B>(noi, oshpi, ostr, intp, outtp, inastri) {
  assert((intp == dtype_int32) || (intp == dtype_fp32));
  gtoa_act_params<B>::set_per_channel(CLIP_PAR_PER_CHAN);
}

template<template<typename> class B>
void gtoa_clip_params<B>::init_prog(act_alay_t l) {
  // initialize the PReLU microcode
  init_clip(gtoa_params<B>::hlapi, l);
}

//
// Parameter encoding functions
//
// BRB0: prescale
// BRW1: clipmax
// BRW2: clipmin

// 32b input, 8b output
template<template<typename> class B>
void gtoa_clip_params<B>::param_enc(
                                    // per channel 2b+6b prescale for scaling down wide acc
                                    const tensor_t<prescale_t, 1, xbuffer_t>& prescale,
                                    // per channel output maximum clip value [Cout]
                                    const tensor_t<fp_e8m23_t, 1, xbuffer_t>& clipmax,
                                    // per channel output minimum clip value [Cout]
                                    const tensor_t<fp_e8m23_t, 1, xbuffer_t>& clipmin,
                                    // outputs, buffers preallocated by caller
                                    // output encoded parameters
                                    const gtoa_params_impl_pchan<xbuffer_t>& obuf) {
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);  // pointer to start of BRB0 values
  // int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);  // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);  // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_act_params<B>::cmax) {
        bparsc[4*c*CLIP_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = prescale.read({j}).data;  // BRB0 prescale
        bparsw[1*c*CLIP_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = clipmax.read({0}).data;   // BRW1 clipmax
        bparsw[1*c*CLIP_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = clipmin.read({0}).data;   // BRW2 clipmin
        j++;
      }
    }
  }
}

#undef HLAPI
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CLIP_INLINE_HPP_

