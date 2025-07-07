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
 * tensor_gtoa_eltop_clip_inline.hpp
 *
 * File defining a tensor level eltwise operation fused with subsequent clip API base on the generic tensor operation API
 *
 */
#include "./legacy/tensor_gtoa_eltop_clip_inline_legacy.hpp"

// constructors
template<template<typename> class B>
gtoa_eltop_clip_params<B>::gtoa_eltop_clip_params(
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
  gtoa_eltop_act_params<B>::set_per_channel(ELTOP_CLIP_PAR_PER_CHAN);
}

template<template<typename> class B>
void gtoa_eltop_clip_params<B>::init_prog(act_alay_t l, act_bin_op_t op, bool ea, broadcast_t brdc_f) {
  // initialize the eltwise PReLU microcode
  init_eltop_clip(gtoa_params<B>::hlapi, l, op, ea);
}

//
// Parameter encoding functions
//
// BRB0: prescale0
// BRB1: prescale1
// BRW1: clipmax
// BRW2: clipmin

template<template<typename> class B>
void gtoa_eltop_clip_params<B>::param_enc(
                                  const tensor_t<prescale_t,1,xbuffer_t>&   prescale0,   // per channel 2b+6b prescale for scaling down wide accumulators 
                                  const tensor_t<prescale_t,1,xbuffer_t>&   prescale1,   // per channel 2b+6b prescale for scaling down wide accumulators
                                  const tensor_t<fp_e8m23_t, 1, xbuffer_t>& clipmax,     // per channel output maximum clip value [Cout]
                                  const tensor_t<fp_e8m23_t, 1, xbuffer_t>& clipmin,     // per channel output minimum clip value [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  //int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_eltop_clip_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltop_clip_params<B>::cmax) {
        bparsc[4*c*ELTOP_CLIP_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = (int8_t)prescale0.read({j}).data;   // BRB0 prescale input accum
        bparsc[4*c*ELTOP_CLIP_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int8_t)prescale1.read({j}).data;   // BRB1 prescale input featuremap
        bparsw[1*c*ELTOP_CLIP_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int32_t)clipmax.read({j}).data;    // BRW1 clipmax
        bparsw[1*c*ELTOP_CLIP_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = (int32_t)clipmin.read({j}).data;    // BRW2 clipmin
        j++;
      }
    }
  }
}

