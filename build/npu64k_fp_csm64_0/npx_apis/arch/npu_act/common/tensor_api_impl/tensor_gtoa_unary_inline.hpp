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
 * tensor_gtoa_unary_inline.hpp
 *
 * File defining a tensor level unary API base on the generic tensor operation API
 *
 */
#include "./legacy/tensor_gtoa_unary_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi

// constructors
template<template<typename> class B>
gtoa_unary_params<B>::gtoa_unary_params(
                                        aoffset_t                  noi,           // number output channels (not vectors)
                                        const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                        act_una_op_t               opi,           // unary operation to perform
                                        act_dtype_t                intp,          // type of primary input
                                        act_dtype_t                outtp,         // type of output
                                        bool                       sati           // do saturation
                  ) {  
  // round parameters
  cmax = noi;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);

  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  switch (intp) {
  case dtype_int48:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 2, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)c, 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_fp32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP32 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  default:
    assert(0 && "unsupported input type");
  }

  switch (outtp) {
  case dtype_int32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OAC;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    HLAPI.i.u.op.bf       |= sati ? 1<<ACT_BF_OP_OUTSAT_START : 0;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    HLAPI.i.u.op.bf       |= sati ? 1<<ACT_BF_OP_OUTSAT_START : 0;
    shapes.oshape          = { (aoffset_t)c, 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_fp32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OAC;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP32 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  default:
    assert(0 && "unsupported output type");
  }
  // parameter dimension ixpix_t [C]
  shapes.pshape = { noi };
  switch (opi) {
  case op_fabs:
  case op_raddv:
  case op_rminv:
  case op_rmaxv:
    init_unary_fp(HLAPI, opi);
    break;
  default:
    assert (intp != dtype_fp32 && intp != dtype_fp16 && intp != dtype_bf16 &&
            outtp != dtype_fp32 && outtp != dtype_fp16 && outtp != dtype_bf16);
    init_unary(HLAPI, opi);
    break;
  }
  set_unary_params();
}

template<template<typename> class B>
gtoa_unary_params<B>::gtoa_unary_params(
                                        aoffset_t                  noi,           // number output channels (not vectors)
                                        const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                        act_bin_op_t               opi,           // binary operation to perform with second input zero
                                        act_dtype_t                intp,          // type of primary input
                                        act_dtype_t                outtp,         // type of output
                                        bool                       sati           // do saturation
                  ) {  
  // round parameters
  cmax = noi;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);

  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  switch (intp) {
  case dtype_int48:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 2, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)c, 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_fp32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP32 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  default:
    assert(0 && "unsupported input type");
  }

  switch (outtp) {
  case dtype_int32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OAC;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    HLAPI.i.u.op.bf       |= sati ? 1<<ACT_BF_OP_OUTSAT_START : 0;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    HLAPI.i.u.op.bf       |= sati ? 1<<ACT_BF_OP_OUTSAT_START : 0;
    shapes.oshape          = { (aoffset_t)c, 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_fp32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OAC;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP32 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  default:
    assert(0 && "unsupported output type");
  }
  // parameter dimension ixpix_t [C]
  shapes.pshape = { noi };
  switch (opi) {
  case op_feq:
  case op_fneq:
  case op_fgt:
  case op_fgte:
  case op_flt:
  case op_flte:
  case op_fadd:
  case op_frsub:
  case op_fmin:
  case op_fmax:
    init_unary_fp(HLAPI, opi);
    break;
  default:
    assert (intp != dtype_fp32 && intp != dtype_fp16 && intp != dtype_bf16 &&
            outtp != dtype_fp32 && outtp != dtype_fp16 && outtp != dtype_bf16);
    init_unary(HLAPI, opi);
    break;
  }
  set_unary_params();
}

// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void gtoa_unary_params<B>::set_unary_params()
{
  int fmidbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmodbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.ishape[4];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.ishape[1]*shapes.ishape[2]*shapes.ishape[3];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.ishape[0];
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // W/8 for feature-map input
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]/TNSVSIZE;
    // double feature-map input
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]/fmidbl;
  }
  if((HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0) {
    // accumulator input AGU
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.ishape);
  }
  else if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // feature-map input AGU
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]    = fmidbl;                       // mlsb
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.ishape[3];             // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.ishape[2]/TNSVSIZE;       // W/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.ishape[4];             // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.ishape[0] / (fmidbl);  // C
  }
  if((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // feature-map output AGU
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = fmodbl;                       // mlsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.oshape[3];             // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.oshape[2]/TNSVSIZE;       // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.oshape[4];             // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.oshape[0] / (fmodbl);  // C
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable        = (int8_t)((1<<TNSVSIZE)-1);
  } else if((HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0) {
    // accumulator output AGU
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.oshape);     
  }
}

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_unary_params<B>::init_l1_output(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t,6,BD> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t,7,BD> t1(t0.split(3, p.data.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t,7,BD> t2(t1.transpose({3,0,5,4,6,1,2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t2.get_offset(0);                    // W8
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(5)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_unary_params<B>::init_l1_input(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t,6,BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t,7,BD> t1(t0.split(3, p.data.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t,7,BD> t2(t1.transpose({3,0,5,4,6,1,2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = t2.get_offset(0);                    // W8
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(2)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(5)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP
}

template<template<typename> class B>
inline void gtoa_unary_params<B>::get_shapes(
                      gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                      ) {
  s = shapes;
}


#undef HLAPI

