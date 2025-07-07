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

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_CLIP_INLINE_LEGACY_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_CLIP_INLINE_LEGACY_HPP_
/*
 * tensor_gtoa_clip_inline.hpp
 *
 * File defining a tensor level clip API base on the generic tensor operation API
 *
 */

// constructors
// typical clip from accumulator (32b/48b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_clip_params<B>::gtoa_clip_params(
                                      // number output channels (not vectors)
                                      aoffset_t noi,
                                      // output shape
                                      const shape<3>& oshpi,
                                      // output stride
                                      const shape<3>& ostr,
                                      // double wide input accumulator
                                      bool accdbli,
                                      // 16b output feature-map
                                      bool fmdbli,
                                      // if true then input stream directly from convolution
                                      bool  inastri)
: gtoa_act_params<B>(noi, oshpi, ostr, accdbli, fmdbli, inastri) {
  gtoa_act_params<B>::set_per_channel(CLIP_PAR_PER_CHAN);
}
// clip from accumulator (32b/48b) to accumulator (32b)
template<template<typename> class B>
gtoa_clip_params<B>::gtoa_clip_params(
                                      // number output channels (not vectors)
                                      aoffset_t noi,
                                      // output shape
                                      const shape<3>& oshpi,
                                      // double wide input accumulator
                                      bool accdbli,
                                      // if true then input stream
                                      bool inastri)
: gtoa_act_params<B>(noi, oshpi, accdbli, inastri) {
  gtoa_act_params<B>::set_per_channel(CLIP_PAR_PER_CHAN);
}

//
// Parameter encoding functions
//
// BRB0: prescale
// BRW1: clipmax
// BRW2: clipmin


// 16b /8b input, 8b output
template<template<typename> class B>
template<typename T>
void gtoa_clip_params<B>::param_enc(
                                    // per tensor output maximum clip value [Cout]
                                    const tensor_t<T, 1, xbuffer_t>& clipmax,
                                    // per tensor output minimum clip value [Cout]
                                    const tensor_t<T, 1, xbuffer_t>& clipmin,
                                    // outputs, buffers preallocated by caller
                                    // output encoded parameters
                                    const gtoa_params_impl_pchan<xbuffer_t>& obuf) {
  static_assert(((std::is_same<T, int8_t>::value) ||
                 (std::is_same<T, int16_t>::value)),
                  "param type is not supported");
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);  // pointer to start of BRB0 values
  // int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);  // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);  // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_act_params<B>::cmax) {
        // calculate floating parameter
        int8_t     iprescale(prescale_t().data);
        fp_e8m23_t fclipmax((float)clipmax.read({0}));
        fp_e8m23_t fclipmin((float)clipmin.read({0}));
        bparsc[4*c*CLIP_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = iprescale;       // BRB0 prescale
        bparsw[1*c*CLIP_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fclipmax.data;   // BRW1 clipmax
        bparsw[1*c*CLIP_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = fclipmin.data;   // BRW2 clipmin
        j++;
      }
    }
  }
}

// 48b input, 8b output
template<template<typename> class B>
void gtoa_clip_params<B>::param_enc(
                                    // per channel 2b+6b prescale for scaling down wide acc
                                    const tensor_t<prescale_t, 1, xbuffer_t>& prescale,
                                    // per channel output maximum clip value [Cout]
                                    const tensor_t<int16_t, 1, xbuffer_t>& clipmax,
                                    // per channel output minimum clip value [Cout]
                                    const tensor_t<int16_t, 1, xbuffer_t>& clipmin,
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
        // calculate floating parameter
        fp_e8m23_t fclipmax((float)clipmax.read({0}));
        fp_e8m23_t fclipmin((float)clipmin.read({0}));
        // convert legacy prescale
        uint8_t  pre = static_cast<uint8_t>(prescale.read({j}));
        int pre_exp = ((pre>>2)& 0x3f)-16;  // exp-47+31
        if (pre_exp < 0)  pre_exp = 0;
        int8_t  iprescale = (pre_exp << 2) | (pre & 0x03);
        bparsc[4*c*CLIP_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = iprescale;       // BRB0 prescale
        bparsw[1*c*CLIP_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fclipmax.data;   // BRW1 clipmax
        bparsw[1*c*CLIP_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = fclipmin.data;   // BRW2 clipmin
        j++;
      }
    }
  }
}

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_CLIP_INLINE_LEGACY_HPP_

