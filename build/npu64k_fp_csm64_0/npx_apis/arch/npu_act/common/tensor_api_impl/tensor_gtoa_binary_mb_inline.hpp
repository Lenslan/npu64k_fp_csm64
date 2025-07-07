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
 * tensor_gtoa_binary_mb_inline.hpp
 *
 * File defining a tensor level binary API base on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_BINARY_MB_INLINE_HPP_        // [NOLINT]

#define TENSOR_GTOA_BINARY_MB_INLINE_HPP_        // [NOLINT]
#include "./legacy/tensor_gtoa_binary_mb_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi

// constructors
template<template<typename> class B>
gtoa_binary_mb_params<B>::gtoa_binary_mb_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     act_dtype_t                in0tp,         // type of primary input
                                     act_dtype_t                in1tp,         // type of secondary input
                                     act_dtype_t                outtp,         // type of output
                                     act_bin_op_t               opi,           // binary operation to perform
                                     bool                       sati           // do saturation on output
                                     ) : gtoa_binary_params<B>(noi, oshpi, in0tp, in1tp, outtp, opi) {
  bool i0dbl = (in0tp == dtype_int16) || (in0tp == dtype_fp16) || (in0tp == dtype_bf16);
  bool odbl  = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  HLAPI.i.u.op.bf = (i0dbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
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
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;

  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // input0 feature-map in ixpix_t [D][H][W][C] format
    gtoa_binary_params<B>::shapes.ishape = { (aoffset_t)(i0dbl  ? 2*c : c), 1,
                      (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  } else {
    // input0 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
    gtoa_binary_params<B>::shapes.ishape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  }
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // output feature-map in ixpix_t [D][H][W][C] format
    gtoa_binary_params<B>::shapes.oshape = { (aoffset_t)(odbl  ? 2*c : c), 1,
                      (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  } else {
    // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
    gtoa_binary_params<B>::shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  }
  // parameter dimension ixpix_t [C]
  gtoa_binary_params<B>::shapes.pshape = { (aoffset_t)(4*c) };
  gtoa_binary_params<B>::set_per_channel(BINARY_PAR_PER_CHAN);
}

template<template<typename> class B>
void gtoa_binary_mb_params<B>::init_bin_prog(act_bin_op_t opi, broadcast_t brdc_f) {
  bool isfp = (opi == op_fadd  || opi == op_fsub  || opi == op_frsub || opi == op_fmin
            || opi == op_fmax  || opi == op_faddf || opi == op_fsubf || opi == op_frsubf
            || opi == op_fminf || opi == op_fmaxf || opi == op_feq   || opi == op_frelun
            || opi == op_fneq  || opi == op_fgt   || opi == op_fgte  || opi == op_flt
            || opi == op_flte  || opi == op_mpy);
  // initialize the binary_mb microcode
  if (isfp) {
    init_binary_rw_fp(HLAPI, opi);
  } else {
    init_binary_rw(HLAPI, opi);
  }
}

//
// Parameter encoding functions
//
// BRW0: source operand 1
template<template<typename> class B>
// per channel B operand
void gtoa_binary_mb_params<B>::param_enc(const tensor_t<int32_t, 1, xbuffer_t>&    bop,
                                  // outputs, buffers preallocated by caller
                                  // output encoded parameters
                                  gtoa_params_impl_pchan<xbuffer_t>&         obuf
                                  ) {
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);  // pointer to start of BRW0 values
  aoffset_t j = 0;
  int ci = (gtoa_binary_mb_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_binary_mb_params<B>::cmax) {
        bparsw[1*c*BINARY_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = (int32_t)bop.read({j});    // BRW0 operand
        j++;
      }
    }
  }
}

#undef HLAPI

#endif  // TENSOR_GTOA_BINARY_MB_INLINE_HPP_      // [NOLINT]
