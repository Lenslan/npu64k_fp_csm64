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
 * tensor_gtoa_bmul_inline.hpp
 *
 * File defining multiply channel wise broadcast rsqrt API base on the generic tensor operation API
 * Used for second parts of layernormalization
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_BMUL_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_BMUL_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

template<template<typename> class B>
gtoa_bmul_params<B>::gtoa_bmul_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     act_dtype_t                in0tp,         // type of primary input
                                     act_dtype_t                in1tp,         // type of secondary input
                                     act_dtype_t                outtp,         // type of output
                                     bool                       sati           // Saturate output
                                     ) : gtoa_binary_params<B>(noi, oshpi, in0tp, in1tp, outtp, op_mpy) {
  HLAPI.i.u.op.io_en    = 0;
  bool i0dbl = (in0tp == dtype_int16) || (in0tp == dtype_fp16) || (in0tp == dtype_bf16);
  bool i1dbl = (in1tp == dtype_int16) || (in1tp == dtype_fp16) || (in1tp == dtype_bf16);
  bool odbl  = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  HLAPI.i.u.op.bf = (i0dbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                    (i1dbl ? 1 << ACT_BF_OP_IN1DBL_START : 0) |
                    (odbl  ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                    (sati  ? 1 << ACT_BF_OP_OUTSAT_START : 0);


  // update mask and floating mode field based on input/output type
  switch (in0tp) {
    case dtype_int8:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_fp16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0FP16_MASK;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0BF16_MASK;
      break;
    case dtype_int32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0FP32_MASK;
      break;
    default: assert(0 && "unsupported input datatype!");
  }
  switch (in1tp) {
    case dtype_int8:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1INT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1INT32_MASK;
      break;
    case dtype_fp16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1FP16_MASK;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1BF16_MASK;
      break;
    case dtype_int32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1INT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1FP32_MASK;
      break;
    default: assert(0 && "unsupported input datatype!");
  }
  switch (outtp) {
    case dtype_int8:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_fp16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTFP16_MASK;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTBF16_MASK;
      break;
    case dtype_int32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OAC;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OAC;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTFP32_MASK;
      break;
    default: assert(0 && "unsupported output datatype!");
  }
  // default scaling factor type
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;

  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // input0 feature-map in ixpix_t [D][H][W][C] format
    gtoa_binary_params<B>::shapes.ishape = { (aoffset_t)(i0dbl  ? 2*c : c), 1,
                      (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  } else {
    // input0 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/VSIZE][H][ONN/lsb/msb] format
    gtoa_binary_params<B>::shapes.ishape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  }
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0) {
    // input1 feature-map in ixpix_t [D][H][W][C] format
    gtoa_binary_params<B>::shapes.i1shape = { (aoffset_t)(i1dbl  ? 2*c : c), 1,
                       (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  } else {
    // input1 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/VSIZE][H][ONN/lsb/msb] format
    gtoa_binary_params<B>::shapes.i1shape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  }
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // output feature-map in ixpix_t [D][H][W][C] format
    gtoa_binary_params<B>::shapes.oshape = { (aoffset_t)(odbl  ? 2*c : c), 1,
                      (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  } else {
    // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/VSIZE][H][ONN] format
    gtoa_binary_params<B>::shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  }

  // parameter dimension ixpix_t [C]
  gtoa_binary_params<B>::shapes.pshape = { (aoffset_t)(4*c) };
  gtoa_binary_params<B>::set_per_channel(BMUL_PER_CHAN);

  HLAPI.i.u.op.bnum      = 4*BMUL_PER_CHAN*c;

  spodd = (w*oshpi[SPATIAL_H]*oshpi[SPATIAL_D])%2;
}

template<template<typename> class B>
void gtoa_bmul_params<B>::set_binary_params() {
  gtoa_binary_params<B>::set_binary_params();
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2] = RDIV_UP(HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2], 2);
}

// Support broadcast 16bit tensor
template<template<typename> class B>
inline void gtoa_bmul_params<B>::get_shapes(
  // structure with implementation specific minimum buffer sizes
                      gtoa_act_params_impl_shapes& s
                      ) {
  s = gtoa_binary_params<B>::shapes;
  bool ifm0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool ifm1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0;
  int fmi0dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmi1dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN1DBL_MASK) != 0 ? 2 : 1;
  auto& b_f = gtoa_binary_params<B>::brdc_f;
  if (b_f.in0_h) s.ishape[ifm0_en ? 3 : 1] = 1;
  if (b_f.in0_w) s.ishape[ifm0_en ? 2 : 2] = 1;
  if (b_f.in0_c) s.ishape[ifm0_en ? 0 : 4] = fmi0dbl;
  if (b_f.in1_h) s.i1shape[ifm1_en ? 3 : 1] = 1;
  if (b_f.in1_w) s.i1shape[ifm1_en ? 2 : 2] = 1;
  if (b_f.in1_c) s.i1shape[ifm1_en ? 0 : 4] = fmi1dbl;
}

template<template<typename> class B>
void gtoa_bmul_params<B>::init_bin_prog(act_bin_op_t opi, broadcast_t brdc_f) {
  // initialize the eltwise mult scale microcode
  bool odbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0;
  init_bmul_scale(gtoa_params<B>::hlapi, alayo16, odbl, brdc_f, spodd);
}

// initialize the secondary input tensors, support broadcast bf16 tensor
template<template<typename> class B>
template<template<typename> class BD>
void  gtoa_bmul_params<B>::init_l1_input1(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  shape<6> msb_shape = {
    (aoffset_t)HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1],
    (aoffset_t)(gtoa_binary_params<B>::shapes.i1shape[0]/HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1]),
    (aoffset_t)gtoa_binary_params<B>::shapes.i1shape[1],
    (aoffset_t)gtoa_binary_params<B>::shapes.i1shape[2],
    (aoffset_t)gtoa_binary_params<B>::shapes.i1shape[3],
    (aoffset_t)gtoa_binary_params<B>::shapes.i1shape[4]};

  //tensor_t<ixpix_t,5,B> t = reinterpret_cast<const impl_spec_container_t<B>*>(&p)->data.broadcast(shapes.i1shape);
  auto &t = reinterpret_cast<const impl_spec_container_t<B>*>(&p)->data;
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, B> t0(t.split(0, aoffset_t(t.get_dim(0)/HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])));
  tensor_t<ixpix_t, 6, B> tb = t0.broadcast(msb_shape);
  //[D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 7, B> t1(tb.split(3, tb.get_dim(3)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, B> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

  // fill the HLAPI offset parameters msb c h w d
  HLAPI.i.u.op.secondary.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.secondary.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.secondary.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.secondary.fm_agu.stride   = gtoa_binary_params<B>::brdc_f.in1_w ? 1 : t2.get_offset(0); // W8 (don't use 0 here in case of w-bcast, use 1)

  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(2)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(3)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W 
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(4)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(5)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(4)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
  (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP = off(c) + (1-on)*off(onn)
}

template<template<typename> class B>
void gtoa_bmul_params<B>::param_enc(
                                const tensor_t<fp_e8m23_t,1,xbuffer_t>&   scale,        // per channel post scale [Cout]
                                const tensor_t<int8_t,1,xbuffer_t>&       bias,         // per channel bias [Cout]
                                gtoa_params_impl_pchan<xbuffer_t>&        obuf          // output encoded parameters
                                ) {

  assert(  (HLAPI.i.u.op.bf & 1 << ACT_BF_OP_OUTDBL_START) == 0 && "bias dtype should be same as output");

  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int16_t*  bparsh  = (int16_t*)bpars;              // pointer to start of BRB values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_bmul_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_bmul_params<B>::cmax) {
        auto bvalue = ((uint32_t)(prescale_t(1.0f).data)) | (((int32_t)bias.read({j}))<<8); // store int8 bias in brh0
        auto svalue = scale.read({j}).data;

        auto idx = c * BMUL_PER_CHAN;
        bparsh[idx*ISIZE*2+i] = bvalue;                               // BRH0 bias
        bparsw[(idx + 1)*ISIZE+i] = svalue;                           // BRW1 scale

        j++;
      }
    }
  }
}

template<template<typename> class B>
void gtoa_bmul_params<B>::param_enc(
                                const tensor_t<fp_e8m23_t,1,xbuffer_t>&   scale,        // per channel post scale [Cout]
                                const tensor_t<int16_t,1,xbuffer_t>&      bias,         // per channel bias [Cout]
                                gtoa_params_impl_pchan<xbuffer_t>&        obuf          // output encoded parameters
                                ) {

  assert(  (HLAPI.i.u.op.bf & 1 << ACT_BF_OP_OUTDBL_START) != 0 && "bias dtype should be same as output");

  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int16_t*  bparsh  = (int16_t*)bpars;              // pointer to start of BRB values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_bmul_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_bmul_params<B>::cmax) {
        auto bvalue = bias.read({j});
        auto svalue = scale.read({j}).data;

        auto idx = c * BMUL_PER_CHAN;
        bparsh[idx*ISIZE*2+i] = bvalue;                               // BRH0 bias
        bparsw[(idx + 1)*ISIZE+i] = svalue;                           // BRW1 scale

        j++;
      }
    }
  }
}

#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_BMUL_INLINE_HPP_
