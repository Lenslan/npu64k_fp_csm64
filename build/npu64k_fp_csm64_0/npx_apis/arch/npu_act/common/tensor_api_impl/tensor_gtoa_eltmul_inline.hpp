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
 * tensor_gtoa_eltop_eltmul_inline.hpp
 *
 * File defining a tensor level eltwise operation fused with subsequent eltmul API base on the generic tensor operation API
 *
 */

#include "./legacy/tensor_gtoa_eltmul_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi

// constructors

template<template<typename> class B>
gtoa_eltmul_params<B>::gtoa_eltmul_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     act_dtype_t                in0tp,         // type of primary input
                                     act_dtype_t                in1tp,         // type of secondary input
                                     act_dtype_t                outtp,         // type of output
                                     bool                       poscli         // do post scaling
                                     ) : gtoa_binary_params<B>(noi, oshpi, in0tp, in1tp, outtp, op_mpyh) {
  HLAPI.i.u.op.io_en    = 0;
  bool i0dbl = (in0tp == dtype_int16) || (in0tp == dtype_fp16) || (in0tp == dtype_bf16);
  bool i1dbl = (in1tp == dtype_int16) || (in1tp == dtype_fp16) || (in1tp == dtype_bf16);
  bool odbl  = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  HLAPI.i.u.op.bf = (i0dbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                    (i1dbl ? 1 << ACT_BF_OP_IN1DBL_START : 0) |
                    (odbl  ? 1 << ACT_BF_OP_OUTDBL_START : 0);
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
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTSAT_MASK;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTSAT_MASK;
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
  fp16scl = true;
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
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0) {
    // input1 feature-map in ixpix_t [D][H][W][C] format
    gtoa_binary_params<B>::shapes.i1shape = { (aoffset_t)(i1dbl  ? 2*c : c), 1,
                       (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  } else {
    // input1 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
    gtoa_binary_params<B>::shapes.i1shape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
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
  gtoa_binary_params<B>::set_per_channel(ELTOP_ELTMUL_SCALE_PAR_PER_CHAN);
  poscl = poscli;
  spodd = (w*oshpi[SPATIAL_H]*oshpi[SPATIAL_D])%2;
}

template<template<typename> class B>
void gtoa_eltmul_params<B>::init_bin_prog(act_bin_op_t opi, broadcast_t brdc_f) {
  // initialize the eltwise mult scale microcode
  init_eltmul(gtoa_params<B>::hlapi, alayo16, fp16scl, brdc_f, spodd, poscl);
}

template<template<typename> class B>
void gtoa_eltmul_params<B>::set_binary_params() {
  gtoa_binary_params<B>::set_binary_params();
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2] = RDIV_UP(HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2], 2);
}

//
// Parameter encoding functions
//
// BRH0: asymmetric output offset
// BRH1: posscale+posshift
// BRW1: asymmi0
// BRW2: asymmi1

template<template<typename> class B>
void gtoa_eltmul_params<B>::param_enc(
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   asymmi0,     // per channel zpa [Cout]
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   asymmi1,     // per channel zpb [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,        // per channel post scale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymmo,      // per channel output quantization offset [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  fp16scl = false;
  init_eltmul(gtoa_params<B>::hlapi, alayo16, fp16scl, gtoa_binary_params<B>::brdc_f, spodd, poscl);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  aoffset_t p0 = 0;
  aoffset_t p1 = 0;
  aoffset_t in0_param_shape = asymmi0.get_dim(0);
  aoffset_t in1_param_shape = asymmi1.get_dim(0);
  int ci = (gtoa_eltmul_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltmul_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)(post.read({j}).data)) | (((int32_t)asymmo.read({j}))<<8);
        bparsh[2*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = sclpst;                         // BRH0 asymm+postscale
        bparsh[2*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (int16_t)0;                     // BRH1 set to 0
        bparsw[1*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (-asymmi0.read({p0})).data;     // BRW1 bias 0
        bparsw[1*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = (-asymmi1.read({p1})).data;     // BRW2 bias 1
        j++;
        if (in0_param_shape > 1) p0++;
        if (in1_param_shape > 1) p1++;
      }
    }
  }
}

template<template<typename> class B>
void gtoa_eltmul_params<B>::param_enc(
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   asymmi0,     // per channel zpa [Cout]
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   asymmi1,     // per channel zpb [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,        // per channel post scale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymmo,      // per channel output quantization offset [Cout]
                                  const tensor_t<fp_e5m10_t,1,xbuffer_t>&   scale,       // per channel positive scaling factor [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  fp16scl = true;
  init_eltmul(gtoa_params<B>::hlapi, alayo16, fp16scl, gtoa_binary_params<B>::brdc_f, spodd, poscl);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  // int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  aoffset_t p0 = 0;
  aoffset_t p1 = 0;
  aoffset_t in0_param_shape = asymmi0.get_dim(0);
  aoffset_t in1_param_shape = asymmi1.get_dim(0);
  int ci = (gtoa_eltmul_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltmul_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)(post.read({j}).data)) | (((int32_t)asymmo.read({j}))<<8);
        bparsh[2*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = sclpst;                         // BRH0 asymm+postscale
        bparsh[2*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = scale.read({j}).data;           // BRH1 scale
        bparsw[1*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (-asymmi0.read({p0})).data;     // BRW1 bias 0
        bparsw[1*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = (-asymmi1.read({p1})).data;     // BRW2 bias 1
        j++;
        if (in0_param_shape > 1) p0++;
        if (in1_param_shape > 1) p1++;
      }
    }
  }
}

template<template<typename> class B>
void gtoa_eltmul_params<B>::param_enc(
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   asymmi0,     // per channel zpa [Cout]
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   asymmi1,     // per channel zpb [Cout]
                                  const tensor_t<prescale_t,1,xbuffer_t>&   post,        // per channel post scale [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymmo,      // per channel output quantization offset [Cout]
                                  const tensor_t<fp_e8m7_t,1,xbuffer_t>&    scale,       // per channel positive scaling factor [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  fp16scl = false;
  init_eltmul(gtoa_params<B>::hlapi, alayo16, fp16scl, gtoa_binary_params<B>::brdc_f, spodd, poscl);
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  // int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  aoffset_t p0 = 0;
  aoffset_t p1 = 0;
  aoffset_t in0_param_shape = asymmi0.get_dim(0);
  aoffset_t in1_param_shape = asymmi1.get_dim(0);
  int ci = (gtoa_eltmul_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltmul_params<B>::cmax) {
        int16_t sclpst = ((uint32_t)(post.read({j}).data)) | (((int32_t)asymmo.read({j}))<<8);
        bparsh[2*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = sclpst;                         // BRH0 asymm+postscale
        bparsh[2*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = scale.read({j}).data;           // BRH1 scale
        bparsw[1*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = (-asymmi0.read({p0})).data;     // BRW1 bias 0
        bparsw[1*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = (-asymmi1.read({p1})).data;     // BRW2 bias 1
        j++;
        if (in0_param_shape > 1) p0++;
        if (in1_param_shape > 1) p1++;
      }
    }
  }
}

