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
 * tensor_gtoa_eltop_relu6_inline_legacy.hpp
 *
 * File defining a tensor level eltwise operation fused with subsequent relu6 API base on the generic tensor operation API
 *
 */

// constructors
// typical relu6 from accumulator (32b/48b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_eltop_relu6_params<B>::gtoa_eltop_relu6_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     const shape<3>&            ostr,          // output stride
                                     act_bin_op_t               opi,           // eltwise binary operation to perform
                                     bool                       accdbli,       // double wide input accumulator
                                     bool                       fmidbli,       // 16b input feature-map
                                     bool                       fmodbli,       // 16b output feature-map
                                     bool                       eltact,        // if true then first eltop then activ, else first activ then eltop 
                                     bool                       inastri        // if true then input stream
                                     ) : gtoa_eltop_act_params<B>(noi, oshpi, ostr, opi, accdbli, fmidbli, fmodbli, eltact, inastri) {
  gtoa_eltop_act_params<B>::set_per_channel(ELTOP_RELU6_PAR_PER_CHAN);
}
// relu6 from accumulator (32b/48b) to accumulator (32b)
template<template<typename> class B>
gtoa_eltop_relu6_params<B>::gtoa_eltop_relu6_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     act_bin_op_t               opi,           // eltwise binary operation to perform
                                     bool                       accdbli,       // double wide input accumulator
                                     bool                       fmidbli,       // 16b input feature-map
                                     bool                       eltact,        // if true then first eltop then activ, else first activ then eltop 
                                     bool                       inastri        // if true then input stream
                                     ) : gtoa_eltop_act_params<B>(noi, oshpi, opi, accdbli, fmidbli, eltact, inastri) {
  gtoa_eltop_act_params<B>::set_per_channel(ELTOP_RELU6_PAR_PER_CHAN);
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
                                  const tensor_t<int32_t,1,xbuffer_t>&      bias,        // per channel bias [Cout]
                                  const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<uint8_t,1,xbuffer_t>&      posshift,    // per channel positive shift right amount [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
                                  const tensor_t<int32_t,1,xbuffer_t>&      clipmax,     // per channel output maximum clip value [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  aoffset_t o = 0;
  aoffset_t p0 = 0;
  aoffset_t p1 = 0;
  aoffset_t b0 = 0;
  aoffset_t b1 = 0;
  aoffset_t in0_param_shape = prescale0.get_dim(0);
  aoffset_t in1_param_shape = prescale1.get_dim(0);
  aoffset_t in_param_shape  = posscale.get_dim(0);
  aoffset_t out_param_shape = asymm.get_dim(0);
  int ci = (gtoa_eltop_relu6_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltop_relu6_params<B>::cmax) {
        fp_e8m23_t fbias((float)bias.read({j}));
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+3*ISIZE+i] = fbias.data;      // BRW3 bias
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+4*ISIZE+i] = 0;               // BRW4 bias
        fp_e5m10_t fposscale(scl_fix2flt(posscale.read({j}), posshift.read({j})));
        bparsh[2*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fposscale.data;  // BRH1 scale
        j++;
      }
      if (p0 < gtoa_eltop_relu6_params<B>::cmax) {
        // convert legacy prescale
        uint8_t  pre0 = static_cast<uint8_t>(prescale0.read({p0}));
        int pre0_exp = ((pre0>>2)& 0x3f)-16;  // exp-47+31
        if (pre0_exp < 0)  pre0_exp = 0;
        int8_t  iprescale0 = (pre0_exp << 2) | (pre0 & 0x03);
        bparsc[4*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = iprescale0;      // BRB0 prescale0
        p0 = (in0_param_shape == 1 ? 0 : p0 + 1);
      }
      if (p1 < gtoa_eltop_relu6_params<B>::cmax) {
        // convert legacy prescale
        uint8_t  pre1 = static_cast<uint8_t>(prescale1.read({p1}));
        int pre1_exp = ((pre1>>2)& 0x3f)-16;  // exp-47+31
        if (pre1_exp < 0)  pre1_exp = 0;
        int8_t  iprescale1 = (pre1_exp << 2) | (pre1 & 0x03);
        bparsc[4*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = iprescale1;      // BRB1 prescale1
        p1 = (in1_param_shape == 1 ? 0 : p1 + 1);
      }
      if (o < gtoa_eltop_relu6_params<B>::cmax) {
        fp_e8m23_t fclipmax((float)clipmax.read({o}));
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = fclipmax.data;   // BRW2 clipmax
        int32_t    iasymm(asymm.read({o}));
        int16_t    ipost((iasymm<<8) | prescale_t().data);
        bparsh[2*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = ipost;           // BRH2 postscale + offset
        fp_e8m23_t post_scale = fp_e8m23_t((float)1);
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+5*ISIZE+i] = post_scale.data;              // BRW5 output scale and shift
        o = (out_param_shape == 1 ? 0 : o + 1);
      }
    }
  }
}

template<template<typename> class B>
template<typename T>
void gtoa_eltop_relu6_params<B>::param_enc(
                                  const tensor_t<int16_t,1,xbuffer_t>&      prescale0,   // per channel 2b+6b prescale for scaling down wide accumulators 
                                  const tensor_t<int16_t,1,xbuffer_t>&      prescale1,   // per channel 2b+6b prescale for scaling down wide accumulators 
                                  const tensor_t<int8_t,1,xbuffer_t>&       preshift0,   // per channel 2b+6b preshift for scaling down wide accumulators (pse
                                  const tensor_t<int8_t,1,xbuffer_t>&       preshift1,   // per channel 2b+6b preshift for scaling down wide accumulators (pse
                                  const tensor_t<int32_t,1,xbuffer_t>&      bias0,       // per channel bias [Cout]
                                  const tensor_t<int32_t,1,xbuffer_t>&      bias1,       // per channel bias [Cout]
                                  const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       posshift,    // per channel positive shift right amount [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
                                  const tensor_t<T,1,xbuffer_t>&            clipmax,     // per channel output maximum clip value [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
auto scale = tensor_t<int16_t, 1, xbuffer_t>();
auto shift = tensor_t<uint8_t,1,xbuffer_t>();

gtoa_eltop_relu6_params<B>::param_enc(prescale0,
                                      prescale1,
                                      preshift0,
                                      preshift1,
                                      bias0,
                                      bias1,
                                      posscale,
                                      posshift,
                                      asymm,
                                      scale,
                                      shift,
                                      clipmax,
                                      obuf);
}


  // BRB0: prescale0
  // BRB1: prescale1
  // BRH1: posscale
  // BRH2: postscale + asymmetric offset
  // BRW2: clipmax
  // BRW3: bias for in1
  // BRW4: bias for in2
  // BRW5: post scale and shift
template<template<typename> class B>
template<typename T>
void gtoa_eltop_relu6_params<B>::param_enc(
                                  const tensor_t<int16_t,1,xbuffer_t>&      prescale0,   // per channel 2b+6b prescale for scaling down wide accumulators 
                                  const tensor_t<int16_t,1,xbuffer_t>&      prescale1,   // per channel 2b+6b prescale for scaling down wide accumulators 
                                  const tensor_t<int8_t,1,xbuffer_t>&       preshift0,   // per channel 2b+6b preshift for scaling down wide accumulators (pse
                                  const tensor_t<int8_t,1,xbuffer_t>&       preshift1,   // per channel 2b+6b preshift for scaling down wide accumulators (pse
                                  const tensor_t<int32_t,1,xbuffer_t>&      bias0,       // per channel bias [Cout]
                                  const tensor_t<int32_t,1,xbuffer_t>&      bias1,       // per channel bias [Cout]
                                  const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       posshift,    // per channel positive shift right amount [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
                                  const tensor_t<int16_t,1,xbuffer_t>&      scale,       // per channel scaling factor [Cout]
                                  const tensor_t<uint8_t,1,xbuffer_t>&      shift,       // per channel shift right amount [Cout]
                                  const tensor_t<T,1,xbuffer_t>&            clipmax,     // per channel output maximum clip value [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  static_assert(((std::is_same<T, int8_t>::value) ||
                 (std::is_same<T, int32_t>::value)),
                  "param type is not supported");
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  aoffset_t o = 0;
  aoffset_t p0 = 0;
  aoffset_t p1 = 0;
  aoffset_t b0 = 0;
  aoffset_t b1 = 0;
  aoffset_t in0_param_shape = prescale0.get_dim(0);
  aoffset_t in1_param_shape = prescale1.get_dim(0);
  aoffset_t in_param_shape  = posscale.get_dim(0);
  aoffset_t out_param_shape = asymm.get_dim(0);

  uint8_t shift_bias0 = 0;
  uint8_t shift_bias1 = 0;
  prescale_t encoded_prescale_0;
  prescale_t encoded_prescale_1;
  int16_t _prescale0 = 0;
  int16_t _prescale1 = 0;
  fp_e5m10_t fposscale;
  fp_e5m10_t fnegscale;
  fp_e8m23_t foutscaleshift;
  fp_e8m23_t fbias0;
  fp_e8m23_t fbias1;
  bool is_out_scale = scale.get_buffer().get_size() != 0;

  int ci = (gtoa_eltop_relu6_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      shift_bias0 = kPreScaleShiftBias;
      shift_bias1 = kPreScaleShiftBias;
      if (j < gtoa_eltop_relu6_params<B>::cmax) {
        fp_e5m10_t fposscale(scl_fix2flt(posscale.read({j}), (shift_bias0 - posshift.read({j}))));
        fp_e8m23_t fclipmax((float)clipmax.read({j}));
        bparsh[2*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fposscale.data;                 // BRH1 shiftp+scalep
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = fclipmax.data;                  // BRW2 clipmax
        j = (in_param_shape == 1 ? 0 : j + 1);
      }
      if (p0 < gtoa_eltop_relu6_params<B>::cmax) {
        _prescale0 = prescale0.read({p0});
        if (_prescale0 == 1) {
          shift_bias0 = kPreScaleOneShiftBias;
          _prescale0 = 0;
        }
        encoded_prescale_0 = SET_PRESCALE_EXP((_prescale0), (shift_bias0 - preshift0.read({p0})));
        bparsc[4*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = encoded_prescale_0.data;                 // BRB0 prescale input accum
        p0 = (in0_param_shape == 1 ? 0 : p0 + 1);
      }
      if (p1 < gtoa_eltop_relu6_params<B>::cmax) {
        _prescale1 = prescale1.read({p1});
        if (_prescale1 == 1) {
          shift_bias1 = kPreScaleOneShiftBias;
          _prescale1 = 0;
        }
        encoded_prescale_1 = SET_PRESCALE_EXP((_prescale1), (shift_bias1 - preshift1.read({p1})));
        bparsc[4*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = encoded_prescale_1.data;                 // BRB1 prescale input featuremap
        p1 = (in1_param_shape == 1 ? 0 : p1 + 1);
      }
      if (b0 < gtoa_eltop_relu6_params<B>::cmax) {
        fp_e8m23_t fbias0_((float)bias0.read({b0}));
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+3*ISIZE+i] = fbias0_.data;                            // BRW3 bias
        b0 = (in0_param_shape == 1 ? 0 : b0 + 1);
      }
      if (b1 < gtoa_eltop_relu6_params<B>::cmax) {
        fp_e8m23_t fbias1_((float)bias1.read({b1}));
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+4*ISIZE+i] = fbias1_.data;                            // BRW4 bias
        b1 = (in1_param_shape == 1 ? 0 : b1 + 1);
      }
      if (o < gtoa_eltop_relu6_params<B>::cmax) {
        int32_t    iasymm(asymm.read({o}));
        int16_t    ipost((iasymm<<8) | prescale_t().data);
        bparsh[2*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = ipost;                                   // BRH2 asymm output offset
        fp_e8m23_t post_scale = fp_e8m23_t((float)1);
        if (is_out_scale) {
          post_scale = fp_e8m23_t(scl_fix2flt(scale.read({o}), shift.read({o})));
        } 
        bparsw[1*c*ELTOP_RELU6_PAR_PER_CHAN*ISIZE+5*ISIZE+i] = post_scale.data;                             // BRW5 output scale and shift
        o = (out_param_shape == 1 ? 0 : o + 1);
      }
    }
  }
}
