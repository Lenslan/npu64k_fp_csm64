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
 * tensor_gtoa_fc_prelu_inline.hpp
 *
 * File defining a tensor level prelu API base on the generic tensor operation API
 *
 */
#include "./legacy/tensor_gtoa_fc_prelu_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi

// constructors
// Fully connected convolution + prelu from accumulator (32b/48b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_fc_prelu_params<B>::gtoa_fc_prelu_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     act_dtype_t                intp,          // type of primary input
                                     act_dtype_t                outtp,         // type of output
                                     bool                       inastri        // if true then input stream
                                     ) : gtoa_fc_act_params<B>(noi, intp, outtp, inastri) {
  gtoa_fc_act_params<B>::set_per_channel(FC_PRELU_PAR_PER_CHAN);
}

template<template<typename> class B>
void gtoa_fc_prelu_params<B>::init_prog() {
  // initialize the FC PReLU microcode
  init_fc_prelu(gtoa_params<B>::hlapi, gtoa_fc_act_params<B>::fp16scl);
}

//
// Parameter encoding functions
//
// BRW0: positive/negative scale
// BRW1: bias
// BRH4: postscale + asymmetric offset

template<template<typename> class B>
void gtoa_fc_prelu_params<B>::param_enc(const tensor_t<fp_e8m23_t,1,xbuffer_t>&      bias,  // per channel bias [Cout]
                                  const tensor_t<fp_e5m10_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<fp_e5m10_t,1,xbuffer_t>&      negscale,    // per channel negative scaling factor [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&      post,        // per channel postscale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&          asymm,       // per channel output offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&         obuf         // output encoded parameters
                                  ) {
  gtoa_fc_act_params<B>::fp16scl = true;
  init_fc_prelu(gtoa_params<B>::hlapi, gtoa_fc_act_params<B>::fp16scl);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  // int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB0 values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH2 values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_fc_prelu_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_prelu_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)(post.read({j}).data)) | (((int32_t)asymm.read({j}))<<8);
        bparsw[1*c*FC_PRELU_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = ((uint32_t)posscale.read({j}).data<<16)|
          negscale.read({j}).data;                                                       // BRW0 positive/negative scaling
        bparsw[1*c*FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = bias.read({j}).data;            // BRW1 bias
        bparsh[2*c*FC_PRELU_PAR_PER_CHAN*ISIZE+4*ISIZE+i] = sclpst;                         // BRH4 asymm+postscale
        j++;
      }
    }
  }
}

template<template<typename> class B>
void gtoa_fc_prelu_params<B>::param_enc(const tensor_t<fp_e8m23_t,1,xbuffer_t>&      bias,  // per channel bias [Cout]
                                  const tensor_t<fp_e8m7_t,1,xbuffer_t>&       posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<fp_e8m7_t,1,xbuffer_t>&       negscale,    // per channel negative scaling factor [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&      post,        // per channel postscale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&          asymm,       // per channel output offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&         obuf         // output encoded parameters
                                  ) {
  gtoa_fc_act_params<B>::fp16scl = false;
  init_fc_prelu(gtoa_params<B>::hlapi, gtoa_fc_act_params<B>::fp16scl);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  // int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB0 values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH2 values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_fc_prelu_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_prelu_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)(post.read({j}).data)) | (((int32_t)asymm.read({j}))<<8);
        bparsw[1*c*FC_PRELU_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = ((uint32_t)posscale.read({j}).data<<16)|
          negscale.read({j}).data;                                                       // BRW0 positive/negative scaling
        bparsw[1*c*FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = bias.read({j}).data;            // BRW1 bias
        bparsh[2*c*FC_PRELU_PAR_PER_CHAN*ISIZE+4*ISIZE+i] = sclpst;                         // BRH4 asymm+postscale
        j++;
      }
    }
  }
}

#undef HLAPI
