/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2022-2023 Synopsys, Inc.                              **/
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
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_RESCALE_INLINE_LEGACY_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_RESCALE_INLINE_LEGACY_HPP_
/*
 * tensor_gtoa_rescale_inline_legacy.hpp
 *
 * File defining a tensor level rescale API base on the generic tensor operation API
 *
 */

// constructors
// typical rescale from accumulator (32b/48b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_rescale_params<B>::gtoa_rescale_params(
                           aoffset_t        noi,      // number output channels (not vectors)
                           const shape<3>&  oshpi,    // output shape, indexed by spatial_axis_t
                           const shape<3>&  ostr,     // output stride
                           bool             accdbli,  // double wide input accumulator
                           bool             fmdbli,   // 16b output feature-map
                           bool             inastri)  // if true then input stream
                           : gtoa_act_params<B>(noi, oshpi, ostr, accdbli, fmdbli, inastri) {
  gtoa_act_params<B>::set_per_channel(RESCALE_PAR_PER_CHAN);
}
// rescale from accumulator (32b/48b) to accumulator (32b)
template<template<typename> class B>
gtoa_rescale_params<B>::gtoa_rescale_params(
                            aoffset_t        noi,     // number output channels (not vectors)
                            const shape<3>&  oshpi,   // output shape, indexed by spatial_axis_t
                            bool             accdbli,  // double wide input accumulator
                            bool             inastri)  // if true then input stream
                            : gtoa_act_params<B>(noi, oshpi, accdbli, inastri) {
  gtoa_act_params<B>::set_per_channel(RESCALE_PAR_PER_CHAN);
}

//
// Parameter encoding functions
//
// BRB0: prescale
// BRH1: scale
// BRH2: postscale + asymmetric offset
// BRW2: bias

// 32b input, 8b output
template<template<typename> class B>
void gtoa_rescale_params<B>::param_enc(
                                       const tensor_t<int32_t, 1, xbuffer_t>& in_bias,
                                                                        // per channel bias [Cout]
                                       const tensor_t<int16_t, 1, xbuffer_t>& scale,
                                                     // per channel positive scaling factor [Cout]
                                       const tensor_t<uint8_t, 1, xbuffer_t>& shift,
                                                 // per channel positive shift right amount [Cout]
                                       const tensor_t<int8_t, 1, xbuffer_t>& out_bias,
                                                  // per channel output quantization offset [Cout]
                                                  // outputs, buffers preallocated by caller
                                       const gtoa_params_impl_pchan<xbuffer_t>& obuf) {
                                                                      // output encoded parameters
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);       // pointer to start of BRB0 values
  int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);      // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);      // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_rescale_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_rescale_params<B>::cmax) {
        // calculate floating parameter
        fp_e8m23_t fbias((float)in_bias.read({j}));
        int8_t     iprescale(prescale_t().data);
        int32_t    iasymm(out_bias.read({j}));
        int16_t    ipost((iasymm<<8) | prescale_t().data);
        fp_e5m10_t fposscale(scl_fix2flt(scale.read({j}), shift.read({j})));
        bparsc[4*c*RESCALE_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = iprescale;       // BRB0 prescale
        bparsh[2*c*RESCALE_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fposscale.data;  // BRH1 scale
        bparsh[2*c*RESCALE_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = ipost;           // BRH2 postscale + offset
        bparsw[1*c*RESCALE_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = fbias.data;      // BRW2 bias
        j++;
      }
    }
  }
}

// 48b input, 8b output
template<template<typename> class B>
void gtoa_rescale_params<B>::param_enc(const tensor_t<prescale_t, 1, xbuffer_t>& prescale,
                                  // per channel 2b+6b prescale for scaling down wide accumulators
                                       const tensor_t<int32_t, 1, xbuffer_t>& in_bias,
                                                                        // per channel bias [Cout]
                                       const tensor_t<int16_t, 1, xbuffer_t>& scale,
                                                     // per channel positive scaling factor [Cout]
                                       const tensor_t<uint8_t, 1, xbuffer_t>& shift,
                                                 // per channel positive shift right amount [Cout]
                                       const tensor_t<int8_t, 1, xbuffer_t>& out_bias,
                                                  // per channel output quantization offset [Cout]
                                                  // outputs, buffers preallocated by caller
                                       const gtoa_params_impl_pchan<xbuffer_t>& obuf ) {
                                                                      // output encoded parameters
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);        // pointer to start of BRB0 values
  int16_t* bparsh  = reinterpret_cast<int16_t*>(bpars);       // pointer to start of BRH2 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);       // pointer to start of BRW2 values
  aoffset_t j = 0;
  int ci = (gtoa_act_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_act_params<B>::cmax) {
        // calculate floating parameter
        fp_e8m23_t fbias((float)in_bias.read({j}));
        int32_t    iasymm(out_bias.read({j}));
        int16_t    ipost((iasymm<<8) | prescale_t().data);
        fp_e5m10_t fposscale(scl_fix2flt(scale.read({j}), shift.read({j})));
        // convert legacy prescale
        uint8_t  pre = static_cast<uint8_t>(prescale.read({j}));
        int pre_exp = ((pre>>2)& 0x3f)-16;  // exp-47+31
        if (pre_exp < 0)  pre_exp = 0;
        int8_t  iprescale = (pre_exp << 2) | (pre & 0x03);
        bparsc[4*c*RESCALE_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = iprescale;       // BRB0 prescale
        bparsh[2*c*RESCALE_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fposscale.data;  // BRH1 scale
        bparsh[2*c*RESCALE_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = ipost;           // BRH2 postscale + offset
        bparsw[1*c*RESCALE_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = fbias.data;      // BRW2 bias
      j++;
      }
    }
  }
}
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_RESCALE_INLINE_LEGACY_HPP_
