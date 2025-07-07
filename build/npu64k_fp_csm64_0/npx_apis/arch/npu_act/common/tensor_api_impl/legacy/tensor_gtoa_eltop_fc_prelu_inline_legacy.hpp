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
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_ELTOP_FC_PRELU_INLINE_LEGACY_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_ELTOP_FC_PRELU_INLINE_LEGACY_HPP_

// constructors
// Fully connected convolution + eltop + prelu from accumulator (32b/48b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_eltop_fc_prelu_params<B>::gtoa_eltop_fc_prelu_params(
    aoffset_t                  noi,           // number output channels (not vectors)
    bool                       fmidbli,       // 16b output feature-map
    bool                       fmodbli,       // 16b output feature-map
    act_bin_op_t               opi,           // eltwise binary operation to perform
    bool                       eltact,        // first eltop then activ
    bool                       inastri)       // if true then input stream
    : gtoa_eltop_fc_act_params<B>(noi, fmidbli, fmodbli, opi, eltact, inastri) {
  gtoa_eltop_fc_act_params<B>::set_per_channel(ELTOP_FC_PRELU_PAR_PER_CHAN);
}

//
// Parameter encoding functions
//
// BRB0: empty
// BRH1: postscale + asymmetric offset
// BRW1: scale
// BRW2: bias

// 32b/48b input, 8b output
template<template<typename> class B>
void gtoa_eltop_fc_prelu_params<B>::param_enc(
    const tensor_t<int32_t, 1, xbuffer_t>&      bias,        // bias
    const tensor_t<int16_t, 1, xbuffer_t>&      posscale,    // positive scaling factor
    const tensor_t<int16_t, 1, xbuffer_t>&      negscale,    // negative scaling factor
    const tensor_t<uint8_t, 1, xbuffer_t>&      posshift,    // positive shift right amount
    const tensor_t<uint8_t, 1, xbuffer_t>&      negshift,    // negative shift right amount
    const tensor_t<int8_t, 1, xbuffer_t>&       asymm,       // output quantization offset
    // outputs, buffers preallocated by caller
    gtoa_params_impl_pchan<xbuffer_t>&          obuf) {      // NOLINT [runtime/refereces]
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_eltop_fc_prelu_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltop_fc_prelu_params<B>::cmax) {
        fp_e8m23_t fbias((float)bias.read({j}));
        int32_t    iasymm(asymm.read({j}));
        int16_t    ipost((iasymm<<8) | prescale_t().data);
        fp_e5m10_t fposscale(scl_fix2flt(posscale.read({j}), posshift.read({j})));
        fp_e5m10_t fnegscale(scl_fix2flt(negscale.read({j}), negshift.read({j})));
        // dump
        bparsh[2*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = ipost;                // BRH1 postscale + offset
        bparsw[1*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = ((uint32_t)fposscale.data<<16)|
          fnegscale.data;       // BRW1 positive/negative scaling
        bparsw[1*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = fbias.data;           // BRW2 bias
        j++;
      }
    }
  }
}


// 32b/48b input, 16b output
template<template<typename> class B>
void gtoa_eltop_fc_prelu_params<B>::param_enc(
    const tensor_t<int32_t, 1, xbuffer_t>&      bias,        // bias
    const tensor_t<int16_t, 1, xbuffer_t>&      posscale,    // positive scaling factor
    const tensor_t<int16_t, 1, xbuffer_t>&      negscale,    // negative scaling factor
    const tensor_t<uint8_t, 1, xbuffer_t>&      posshift,    // positive shift right amount
    const tensor_t<uint8_t, 1, xbuffer_t>&      negshift,    // negative shift right amount
    // outputs, buffers preallocated by caller
    gtoa_params_impl_pchan<xbuffer_t>&          obuf) {      // NOLINT [runtime/refereces]
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_eltop_fc_prelu_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltop_fc_prelu_params<B>::cmax) {
        fp_e8m23_t fbias((float)bias.read({j}));
        int16_t    ipost(prescale_t().data);
        fp_e5m10_t fposscale(scl_fix2flt(posscale.read({j}), posshift.read({j})));
        fp_e5m10_t fnegscale(scl_fix2flt(negscale.read({j}), negshift.read({j})));
        // dump
        bparsh[2*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = ipost;                // BRH1 postscale + offset
        bparsw[1*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = ((uint32_t)fposscale.data<<16)|
          fnegscale.data;       // BRW1 positive/negative scaling
        bparsw[1*c*ELTOP_FC_PRELU_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = fbias.data;           // BRW2 bias
        j++;
      }
    }
  }
}

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_ELTOP_FC_PRELU_INLINE_LEGACY_HPP_
