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
 * tensor_gtoa_fc_prelu_inline_legacy.hpp
 *
 * File defining a tensor level prelu API base on the generic tensor operation API
 *
 */

// constructors
// Fully connected convolution + prelu from accumulator (32b/48b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_fc_prelu_params<B>::gtoa_fc_prelu_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     bool                       fmdbli,        // 16b output feature-map
                                     bool                       inastri        // if true then input stream
                                     ) : gtoa_fc_act_params<B>(noi, fmdbli, inastri) {
  gtoa_fc_act_params<B>::set_per_channel(FC_PRELU_PAR_PER_CHAN);
}

//
// Parameter encoding functions
//
// BRW0: positive/negative scale
// BRW1: bias
// BRH4: postscale + asymmetric offset

// 32b/48b input, 8b output
template<template<typename> class B>
void gtoa_fc_prelu_params<B>::param_enc(const tensor_t<int32_t,1,xbuffer_t>&      bias,        // per channel bias [Cout]
                                  const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<int16_t,1,xbuffer_t>&      negscale,    // per channel negative scaling factor [Cout]
                                  const tensor_t<uint8_t,1,xbuffer_t>&      posshift,    // per channel positive shift right amount [Cout]
                                  const tensor_t<uint8_t,1,xbuffer_t>&      negshift,    // per channel negative shift right amount [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&         obuf         // output encoded parameters
                                  ) {
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  //int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB0 values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH2 values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW2 values
  aoffset_t j = 0;
  aoffset_t o = 0;
  aoffset_t in_param_shape = bias.get_dim(0);
  aoffset_t out_param_shape = asymm.get_dim(0);
  int ci = (gtoa_fc_prelu_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_prelu_params<B>::cmax) {
        // calculate floating parameter
        fp_e8m23_t fbias((float)bias.read({j}));
        fp_e5m10_t fposscale(scl_fix2flt(posscale.read({j}), posshift.read({j})));
        fp_e5m10_t fnegscale(scl_fix2flt(negscale.read({j}), negshift.read({j})));
        bparsw[1*c*FC_PRELU_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = ((uint32_t)fposscale.data<<16)|
          fnegscale.data;       // BRW0 positive/negative scaling
        bparsw[1*c*FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fbias.data;           // BRW1 bias
        j = (in_param_shape == 1 ? 0 : j + 1);
      }
      if (o < gtoa_fc_prelu_params<B>::cmax) {
        int32_t    iasymm(asymm.read({o}));
        int16_t    ipost((iasymm<<8) | prescale_t().data);
        bparsh[2*c*FC_PRELU_PAR_PER_CHAN*ISIZE+4*ISIZE+i] = ipost;                // BRH4 postscale + offset
        o = (out_param_shape == 1 ? 0 : o + 1);
      }
    }
  }
}


// 32b/48b input, 16b output
template<template<typename> class B>
void gtoa_fc_prelu_params<B>::param_enc(const tensor_t<int32_t,1,xbuffer_t>&      bias,        // per channel bias [Cout]
                                  const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<int16_t,1,xbuffer_t>&      negscale,    // per channel negative scaling factor [Cout]
                                  const tensor_t<uint8_t,1,xbuffer_t>&      posshift,    // per channel positive shift right amount [Cout]
                                  const tensor_t<uint8_t,1,xbuffer_t>&      negshift,    // per channel negative shift right amount [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&         obuf         // output encoded parameters
                                  ) {
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  //int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB0 values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH2 values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_fc_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_fc_act_params<B>::cmax) {
        // calculate floating parameter
        fp_e8m23_t fbias((float)bias.read({j}));
        int16_t    ipost(prescale_t().data);
        fp_e5m10_t fposscale(scl_fix2flt(posscale.read({j}), posshift.read({j})));
        fp_e5m10_t fnegscale(scl_fix2flt(negscale.read({j}), negshift.read({j})));
        bparsw[1*c*FC_PRELU_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = ((uint32_t)fposscale.data<<16)|
          fnegscale.data;       // BRW0 positive/negative scaling
        bparsw[1*c*FC_PRELU_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fbias.data;           // BRW1 bias
        bparsh[2*c*FC_PRELU_PAR_PER_CHAN*ISIZE+4*ISIZE+i] = ipost;                // BRH4 postscale + offset
        j++;
      }
    }
  }
}
