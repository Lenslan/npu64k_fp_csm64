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
 * tensor_gtoa_eltop_relu6_inline.hpp
 *
 * File defining a tensor level eltwise operation fused with subsequent relu6 API base on the generic tensor operation API
 *
 */
#include "./legacy/tensor_gtoa_eltop_relu6_inline_legacy.hpp"

// constructors
template<template<typename> class B>
gtoa_eltop_relu6_params<B>::gtoa_eltop_relu6_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     const shape<3>&            ostr,          // output stride
                                     act_bin_op_t               opi,           // eltwise binary operation to perform
                                     act_dtype_t                in0tp,         // type of primary input
                                     act_dtype_t                in1tp,         // type of secondary input
                                     act_dtype_t                outtp,         // type of output
                                     bool                       eltact,        // if true then first eltop then activ, else first activ then eltop 
                                     bool                       inastri        // if true then input stream
                                     ) : gtoa_eltop_act_params<B>(noi, oshpi, ostr, opi, in0tp, in1tp, outtp, eltact, inastri) {
  gtoa_eltop_act_params<B>::set_per_channel(ELTOP_RELU6_PAR_PER_CHAN);
}

template<template<typename> class B>
void gtoa_eltop_relu6_params<B>::init_prog(act_alay_t l, act_bin_op_t op, bool ea, broadcast_t brdc_f) {
  // initialize the eltwise PReLU microcode
  init_eltop_relu6(gtoa_params<B>::hlapi, l, op, ea, gtoa_eltop_act_params<B>::fp16scl, brdc_f);
}

//
// Parameter encoding functions
//
// BRB0: prescale0
// BRB1: prescale1
// BRH1: posscale
// BRH2: postscale + asymmetric offset
// BRW2: clipmax
// BRW3: bias

template<template<typename> class B>
void gtoa_eltop_relu6_params<B>::param_enc(
                                  const tensor_t<prescale_t,1,xbuffer_t>&   prescale0,   // per channel 2b+6b prescale for scaling down wide accumulators
                                  const tensor_t<prescale_t,1,xbuffer_t>&   prescale1,   // per channel 2b+6b prescale for scaling down wide accumulators
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,        // per channel bias [Cout]
                                  const tensor_t<fp_e5m10_t,1,xbuffer_t>&   posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   clipmax,     // per channel output maximum clip value [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,        // per channel post scale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  gtoa_eltop_act_params<B>::fp16scl = true;
  init_eltop_relu6(gtoa_params<B>::hlapi,
                   gtoa_params<B>::onn == 2 ? alayo32 : alayo16,
                   gtoa_eltop_act_params<B>::op,
                   gtoa_eltop_act_params<B>::ea_ord,
                   gtoa_eltop_act_params<B>::fp16scl,
                   gtoa_eltop_act_params<B>::brdc_f);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_eltop_relu6_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltop_relu6_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)post.read({j}).data) | (((int32_t)asymm.read({j}))<<8);
        bparsc[4*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = (int8_t)prescale0.read({j}).data;   // BRB0 prescale0
        bparsc[4*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int8_t)prescale1.read({j}).data;   // BRB1 prescale1
        bparsh[2*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int16_t)posscale.read({j}).data;   // BRH1 scale
        bparsh[2*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = sclpst;                             // BRH2 postscale + offset
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = (int32_t)clipmax.read({j}).data;    // BRW2 clipmax
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+3*ISIZE+i] = (int32_t)bias.read({j}).data;       // BRW3 bias
        j++;
      }
    }
  }
}

template<template<typename> class B>
void gtoa_eltop_relu6_params<B>::param_enc(
                                  const tensor_t<prescale_t,1,xbuffer_t>&   prescale0,   // per channel 2b+6b prescale for scaling down wide accumulators
                                  const tensor_t<prescale_t,1,xbuffer_t>&   prescale1,   // per channel 2b+6b prescale for scaling down wide accumulators
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,        // per channel bias [Cout]
                                  const tensor_t<fp_e8m7_t,1,xbuffer_t>&    posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   clipmax,     // per channel output maximum clip value [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,        // per channel post scale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  gtoa_eltop_act_params<B>::fp16scl = false;
  init_eltop_relu6(gtoa_params<B>::hlapi,
                   gtoa_params<B>::onn == 2 ? alayo32 : alayo16,
                   gtoa_eltop_act_params<B>::op,
                   gtoa_eltop_act_params<B>::ea_ord,
                   gtoa_eltop_act_params<B>::fp16scl,
                   gtoa_eltop_act_params<B>::brdc_f);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_eltop_relu6_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltop_relu6_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)post.read({j}).data) | (((int32_t)asymm.read({j}))<<8);
        bparsc[4*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = (int8_t)prescale0.read({j}).data;   // BRB0 prescale0
        bparsc[4*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int8_t)prescale1.read({j}).data;   // BRB1 prescale1
        bparsh[2*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int16_t)posscale.read({j}).data;   // BRH1 scale
        bparsh[2*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = sclpst;                             // BRH2 postscale + offset
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = (int32_t)clipmax.read({j}).data;    // BRW2 clipmax
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+3*ISIZE+i] = (int32_t)bias.read({j}).data;       // BRW3 bias
        j++;
      }
    }
  }
}
