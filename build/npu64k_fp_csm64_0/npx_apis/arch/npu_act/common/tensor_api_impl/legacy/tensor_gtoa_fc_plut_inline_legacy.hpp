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
 * tensor_gtoa_fc_plut_inline_legacy.hpp
 *
 * File defining a tensor level fc + plut API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_FC_PLUT_INLINE_LEGACY_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_FC_PLUT_INLINE_LEGACY_HPP_

// constructors
// Fully connected convolution + plut from accumulator (32b/48b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_fc_plut_params<B>::gtoa_fc_plut_params(
    aoffset_t                  noi,           // number output channels (not vectors)
    bool                       fmdbli,        // 16b output feature-map
    bool                       inastri,       // if true then input stream
    bool                       poscli)        // do post scaling
    : gtoa_fc_act_params<B>(noi, fmdbli, inastri) {
  gtoa_fc_act_params<B>::set_per_channel(FC_PLUT_PAR_PER_CHAN);
  poscl = poscli;
}

//
// Parameter encoding functions
//
// BRH0: optional post scale and shift
// BRH1: postscale + asymmetric offset
// BRW1: bias

// 32b/48b input, 8b output, no post-scaling
template<template<typename> class B>
void gtoa_fc_plut_params<B>::param_enc(
  const tensor_t<int32_t, 1, xbuffer_t>&  bias,     // per channel bias
  const tensor_t<int8_t, 1, xbuffer_t>&   asymm,    // per channel output quantization offset
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&      obuf) {   // NOLINT [runtime/references]
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  //int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);       // pointer to start of BRB0 values
  int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);   // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);      // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_fc_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_act_params<B>::cmax) {
        // calculate floating parameter
        fp_e8m23_t fbias((float)bias.read({j}));
        int32_t    iasymm(asymm.read({j}));
        int16_t    ipost((iasymm<<8) | prescale_t().data);
        fp_e5m10_t fposscale((float)1.0);
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = fposscale.data;  // BRH0 scale
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = ipost;           // BRH1 postscale + offset
        bparsw[1*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fbias.data;      // BRW1 bias
        j++;
      }
    }
  }
}


// 32b/48b input, 16b output, no post-scaling
template<template<typename> class B>
void gtoa_fc_plut_params<B>::param_enc(
  const tensor_t<int32_t, 1, xbuffer_t>&      bias,    // per channel bias
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&        obuf) {    // NOLINT [runtime/references]
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  //int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);       // pointer to start of BRB0 values
  int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);   // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);      // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_fc_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_act_params<B>::cmax) {
        // calculate floating parameter
        fp_e8m23_t fbias((float)bias.read({j}));
        int16_t    ipost(prescale_t().data);
        fp_e5m10_t fposscale((float)1.0);
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = fposscale.data;  // BRH0 scale
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = ipost;           // BRH1 postscale + offset
        bparsw[1*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fbias.data;      // BRW1 bias
        j++;
      }
    }
  }
}

// 32b/48b input, 8b output, with post-scaling
template<template<typename> class B>
void gtoa_fc_plut_params<B>::param_enc(
  const tensor_t<int32_t, 1, xbuffer_t>&  bias,   // per channel bias
  const tensor_t<int16_t, 1, xbuffer_t>&  scale,  // per channel scaling factor
  const tensor_t<uint8_t, 1, xbuffer_t>&  shift,  // per channel shift right amount
  const tensor_t<int8_t, 1, xbuffer_t>&   asymm,  // per channel output quantization offset
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&    obuf) {   // NOLINT [runtime/references]
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  //int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);       // pointer to start of BRB0 values
  int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);   // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);      // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_fc_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_act_params<B>::cmax) {
        // calculate floating parameter
        fp_e8m23_t fbias((float)bias.read({j}));
        int32_t    iasymm(asymm.read({j}));
        int16_t    ipost((iasymm<<8) | prescale_t().data);
        fp_e5m10_t fposscale(scl_fix2flt(scale.read({j}), shift.read({j})));
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = fposscale.data;  // BRH0 scale
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = ipost;           // BRH1 postscale + offset
        bparsw[1*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fbias.data;      // BRW1 bias
        j++;
      }
    }
  }
}

// 32b input, 16b output, with post-scaling
template<template<typename> class B>
void gtoa_fc_plut_params<B>::param_enc(
  const tensor_t<int32_t, 1, xbuffer_t>&  bias,    // per channel bias
  const tensor_t<int16_t, 1, xbuffer_t>&  scale,   // per channel scaling factor
  const tensor_t<uint8_t, 1, xbuffer_t>&  shift,   // per channel shift right amount
  // outputs, buffers preallocated by caller
  gtoa_params_impl_pchan<xbuffer_t>&      obuf) {  // NOLINT [runtime/references]
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  //int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);       // pointer to start of BRB0 values
  int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);   // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);      // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_fc_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_act_params<B>::cmax) {
        // calculate floating parameter
        fp_e8m23_t fbias((float)bias.read({j}));
        int16_t    ipost(prescale_t().data);
        fp_e5m10_t fposscale(scl_fix2flt(scale.read({j}), shift.read({j})));
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = fposscale.data;  // BRH0 scale
        bparsh[2*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = ipost;           // BRH1 postscale + offset
        bparsw[1*c*FC_PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fbias.data;      // BRW1 bias
        j++;
      }
    }
  }
}

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_FC_PLUT_INLINE_LEGACY_HPP_
