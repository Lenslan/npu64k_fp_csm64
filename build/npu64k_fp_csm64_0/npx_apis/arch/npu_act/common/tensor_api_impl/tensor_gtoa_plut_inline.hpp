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
 * tensor_gtoa_plut_inline.hpp
 *
 * File defining a tensor level prelu API base on the generic tensor operation API
 *
 */
#include "./legacy/tensor_gtoa_plut_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi

// constructor
template<template<typename> class B>
gtoa_plut_params<B>::gtoa_plut_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     const shape<3>&            ostr,          // output stride
                                     act_dtype_t                intp,          // type of primary input
                                     act_dtype_t                outtp,         // type of output
                                     bool                       inastri,       // if true then input stream
                                     bool                       poscli         // do post scaling
                                     ) : gtoa_act_params<B>(noi, oshpi, ostr, intp, outtp, inastri) {
  gtoa_act_params<B>::set_per_channel(PLUT_PAR_PER_CHAN);
  poscl = poscli;
}
template<template<typename> class B>
void gtoa_plut_params<B>::init_prog(act_alay_t l) {
  // dummy function
  init_lut(gtoa_params<B>::hlapi, l, poscl, gtoa_act_params<B>::fp16scl);
}

//
// Parameter encoding functions
//
// BRB0: prescale
// BRH1: optional scale
// BRH2: post-scale + asymmetric offset
// BRW2: bias

// 32b input, 8b output, no post-scaling
template<template<typename> class B>
void gtoa_plut_params<B>::param_enc(const tensor_t<prescale_t,1,xbuffer_t>&   prescale,    // per channel 2b+6b prescale for scaling down wide accumulators (pse
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,          // per channel bias [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,          // per channel post scale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,         // per channel offset[Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&         obuf          // output encoded parameters
                                  ) {
  gtoa_act_params<B>::fp16scl = false;
  init_lut(gtoa_params<B>::hlapi, gtoa_params<B>::onn == 2 ? alayo32 : alayo16, poscl, gtoa_act_params<B>::fp16scl);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB0 values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH0 values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW0 values
  aoffset_t j = 0;
  int ci = (gtoa_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_act_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)(post.read({j}).data)) | (((int32_t)asymm.read({j}))<<8);
        bparsc[4*c*PLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = static_cast<uint8_t>(prescale.read({j}));         // BRB0 prescale set
        bparsh[2*c*PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int16_t)0;                         // BRH1 set to 0
        bparsh[2*c*PLUT_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = sclpst;                             // BRH2 postscale
        bparsw[1*c*PLUT_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = (int32_t)bias.read({j}).data;       // BRW2 bias
      j++;
      }
    }
  }
}

// 32b input, 8b output, with post-scaling, bf16 scale
template<template<typename> class B>
void gtoa_plut_params<B>::param_enc(const tensor_t<prescale_t,1,xbuffer_t>&   prescale,    // per channel 2b+6b prescale for scaling down wide accumulators (pse
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,          // per channel bias [Cout]
                                  const tensor_t<fp_e8m7_t,1,xbuffer_t>&    scale,         // per channel scaling factor [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,          // per channel post scale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,         // per channel offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&         obuf          // output encoded parameters
                                  ) {
  gtoa_act_params<B>::fp16scl = false;
  init_lut(gtoa_params<B>::hlapi, gtoa_params<B>::onn == 2 ? alayo32 : alayo16, poscl, gtoa_act_params<B>::fp16scl);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB0 values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH0 values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW0 values
  aoffset_t j = 0;
  int ci = (gtoa_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_act_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)(post.read({j}).data)) | (((int32_t)asymm.read({j}))<<8);
        bparsc[4*c*PLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = static_cast<uint8_t>(prescale.read({j}));         // BRB0 prescale set
        bparsh[2*c*PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int16_t)scale.read({j}).data;      // BRH1 scale
        bparsh[2*c*PLUT_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = sclpst;                             // BRH2 postscale
        bparsw[1*c*PLUT_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = (int32_t)bias.read({j}).data;       // BRW2 bias
      j++;
      }
    }
  }
}

// 32b input, 8b output, with post-scaling, fp16 scale
template<template<typename> class B>
void gtoa_plut_params<B>::param_enc(const tensor_t<prescale_t,1,xbuffer_t>&   prescale,    // per channel 2b+6b prescale for scaling down wide accumulators (pse
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,          // per channel bias [Cout]
                                  const tensor_t<fp_e5m10_t,1,xbuffer_t>&   scale,         // per channel scaling factor [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,          // per channel post scale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,         // per channel offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&         obuf          // output encoded parameters
                                  ) {
  gtoa_act_params<B>::fp16scl = true;
  init_lut(gtoa_params<B>::hlapi, gtoa_params<B>::onn == 2 ? alayo32 : alayo16, poscl, gtoa_act_params<B>::fp16scl);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB0 values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH0 values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW0 values
  aoffset_t j = 0;
  int ci = (gtoa_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_act_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)(post.read({j}).data)) | (((int32_t)asymm.read({j}))<<8);
        bparsc[4*c*PLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = static_cast<uint8_t>(prescale.read({j}));         // BRB0 prescale set
        bparsh[2*c*PLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int16_t)scale.read({j}).data;      // BRH1 scale
        bparsh[2*c*PLUT_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = sclpst;                             // BRH2 postscale
        bparsw[1*c*PLUT_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = (int32_t)bias.read({j}).data;       // BRW2 bias
      j++;
      }
    }
  }
}

#undef HLAPI
