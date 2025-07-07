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
 * tensor_gtoa_eltop_flut_inline.hpp
 *
 * File defining a tensor level eltwise operation fused with subsequent flut API based on the generic tensor operation API
 *
 */
// #include "./legacy/tensor_gtoa_eltop_flut_inline_legacy.hpp"

// constructors
template<template<typename> class B>
gtoa_eltop_flut_params<B>::gtoa_eltop_flut_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     const shape<3>&            ostr,          // output stride
                                     act_bin_op_t               opi,           // eltwise binary operation to perform
                                     act_dtype_t                in0tp,         // type of primary input
                                     act_dtype_t                in1tp,         // type of secondary input
                                     act_dtype_t                outtp,         // type of output
                                     flut_typ_t                 tp,            // type of fixed look-up table
                                     bool                       eltact,        // if true then first eltop then activ, else first activ then eltop
                                     bool                       inastri        // if true then input stream
                                     ) : gtoa_eltop_act_params<B>(noi, oshpi, ostr, opi, in0tp, in1tp, outtp, eltact, inastri) {
  gtoa_eltop_act_params<B>::set_per_channel(ELTOP_FLUT_PAR_PER_CHAN);
  typ = tp;
}

template<template<typename> class B>
void gtoa_eltop_flut_params<B>::init_prog(act_alay_t l, act_bin_op_t op, bool ea, broadcast_t brdc_f) {
  act_una_op_t tp;
  switch (typ) {
  case flut_typ_exp_e:
    tp = op_exp0;
    break;
  case flut_typ_recip_e:
    tp = op_recip0;
    break;
  case flut_typ_rsqrt_e:
    tp = op_rsqrt0;
    break;
  default:
    assert(0 && "unsupported fixed look-up table");
  }
  // initialize the eltwise flut microcode
  init_eltop_flut(gtoa_params<B>::hlapi, tp, l, op, ea, brdc_f);
}

//
// Parameter encoding functions
//
// BRB0: prescale0
// BRB1: prescale1
// BRH1: postscale + asymmetric offset
// BRW1: bias

template<template<typename> class B>
void gtoa_eltop_flut_params<B>::param_enc(
                                  const tensor_t<prescale_t,1,xbuffer_t>&   prescale0,   // per channel 2b+6b prescale for scaling down wide accumulators 
                                  const tensor_t<prescale_t,1,xbuffer_t>&   prescale1,   // per channel 2b+6b prescale for scaling down wide accumulators 
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,        // per channel bias [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,        // per channel output scale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_eltop_flut_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltop_flut_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)post.read({j}).data) | (((int32_t)asymm.read({j}))<<8);
        bparsc[4*c*ELTOP_FLUT_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = (int8_t)prescale0.read({j}).data;   // BRB0 prescale0
        bparsc[4*c*ELTOP_FLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int8_t)prescale1.read({j}).data;   // BRB1 prescale1
        bparsh[2*c*ELTOP_FLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = sclpst;                             // BRH1 postscale + offset
        bparsw[1*c*ELTOP_FLUT_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int32_t)bias.read({j}).data;       // BRW1 bias
        j++;
      }
    }
  }
}


