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
 * tensor_gtoa_mean_inline.hpp
 *
 * File defining channelwise reduce mean API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_MEAN_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_MEAN_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// chanel wise reduce mean operation for feature-map (8b/16b) input
template <template <typename> class B>
gtoa_mean_params<B>::gtoa_mean_params(
    aoffset_t       noi,        // number output channels (not vectors)
    const shape<3>& ishpi,      // input shape
    size_t          num,        // total number of elements in pool
    act_dtype_t     intp,       // type of primary input
    act_dtype_t     outtp,      // type of output
    bool            bfp32scl,   // use fp32 as prescale
    bool            chnpad) :   // If true ,will do chnpad during the mean
  gtoa_creduce_base_params<B>(noi, ishpi, intp, outtp) {

  cmax = noi;
  this->bfp32scl = bfp32scl;

    // if num aligned with ISIZE or chnpad on the fly is disabled, chn_pa=-1
  this->ch_pad = (num % ISIZE == 0 || !chnpad) ? -1 : num - (cmax-ISIZE);

  init_mean(HLAPI, alayo16, false, ch_pad); //fp32 

  // 1/num as fp32 number in SR0
  float recip = 1.0/(float)num;
  fp_e8m23_t frecip(recip);
  HLAPI.i.u.op.scl[0] = frecip.data;

  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(ishpi[SPATIAL_W], TNSVSIZE);

  // per tensor parameter
  gtoa_creduce_base_params<B>::shapes.pshape = {(aoffset_t)(4*CMEAN_PER_CHAN)};

  HLAPI.i.u.op.bnum      = 4*CMEAN_PER_CHAN;
}


//
// Parameter encoding functions
//
// BRB0: prescale fp8
// BRW1: bias fp32
template<template<typename> class B>
inline void gtoa_mean_params<B>::param_enc(
                                  const tensor_t<prescale_t,1,xbuffer_t>&      prescale,    // Input tensor scale value.
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&      bias,        // nput tensor bias value (used for both asym and bias).
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&           obuf         // output encoded parameters
                                  ) {
  
  init_mean(HLAPI, alayo16, false, ch_pad); //fp32 scale = false

  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRC values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;

  for (short i = 0; i < ISIZE; i++) {
    auto svalue = prescale.read({j}).data;        // BRW0 prescale
    auto bvalue = bias.read({j}).data;            // BRW1 bias 0

    bparsc[i] = svalue;                           // BRB0 scale
    bparsw[ISIZE+i] = bvalue;                     // BRW1 bias
    if (prescale.get_dim(0) > 1) j++;
  }
}

//
// Parameter encoding functions
//
// BRW0: prescale fp32
// BRW1: bias fp32
template<template<typename> class B>
inline void gtoa_mean_params<B>::param_enc(
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&      prescale,    // Input tensor scale value.
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&      bias,        // nput tensor bias value (used for both asym and bias).
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&           obuf         // output encoded parameters
                                  ) {
  init_mean(HLAPI, alayo16, true, ch_pad); //fp32 scale = true

  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;

  for (short i = 0; i < ISIZE; i++) {
      auto svalue = prescale.read({j}).data;      // BRW0 prescale
      auto bvalue = bias.read({j}).data;          // BRW1 bias
      bparsw[i] = svalue;                         // BRW0 scale
      bparsw[ISIZE+i] = bvalue;                   // BRW1 bias
      if (prescale.get_dim(0) > 1) j++;
  }
}
#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_MEAN_INLINE_HPP_
