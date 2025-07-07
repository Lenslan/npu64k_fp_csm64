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
 * tensor_gtoa_eltop_act_inline.hpp
 *
 * File defining a tensor level activation function API base on the generic tensor operation API
 *
 */

//
// Constructors
//
#include "./legacy/tensor_gtoa_eltop_act_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi
template<template<typename> class B>
gtoa_eltop_act_params<B>::gtoa_eltop_act_params(
                                 aoffset_t                  noi,           // number output channels (not vectors)
                                 const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                 const shape<3>&            ostr,          // output stride
                                 act_bin_op_t               opi,           // eltwise binary operation to perform
                                 act_dtype_t                in0tp,         // type of primary input
                                 act_dtype_t                in1tp,         // type of secondary input
                                 act_dtype_t                outtp,         // type of output
                                 bool                       eltact,        // if true then first eltop then activ, else first activ then eltop 
                                 bool                       inastri        // if true then input stream
                                 ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  op = opi;
  ea_ord = eltact;
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  bool i0dbl = (in0tp == dtype_int16) || (in0tp == dtype_fp16) || (in0tp == dtype_bf16) || (in0tp == dtype_int48);
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
      HLAPI.i.u.op.io_en |= (inastri ? ACT_IO_EN_ASTR0 : ACT_IO_EN_AC0);
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_int48:
      HLAPI.i.u.op.io_en |= (inastri ? ACT_IO_EN_ASTR0 : ACT_IO_EN_AC0);
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= (inastri ? ACT_IO_EN_ASTR0 : ACT_IO_EN_AC0);
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

  cmax  = noi;
  mpstr = 1;
  str   = ostr;
  // default scaling factor type
  fp16scl = true;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // input feature-map in ixpix_t [D][H][W][C] format
    shapes.ishape = { (aoffset_t)(i0dbl ? 2 * c : c), 1, (aoffset_t)(w*TNSVSIZE), (aoffset_t)(oshpi[SPATIAL_H]), (aoffset_t)(oshpi[SPATIAL_D]) };
  } else {
     // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
    shapes.ishape = { (aoffset_t)(i0dbl ? 2 : 1), oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  }
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.i1shape = { (aoffset_t)(i1dbl ? 2*c:c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // output feature-map in ixpix_t [D][H][W][C] format
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    shapes.oshape = { (aoffset_t)(odbl ? 2*c:c), 1, (aoffset_t)(w*TNSVSIZE*str[SPATIAL_W]), (aoffset_t)(oshpi[SPATIAL_H]*str[SPATIAL_H]), (aoffset_t)(oshpi[SPATIAL_D]*str[SPATIAL_D]) };
  } else {
    // output accumulator shape
    shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  }
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  // maxpool overlap buffer ixpix_t [stash_sz]
  shapes.mpshape = {(aoffset_t)(2*c*(oshpi[SPATIAL_H]))};
  // default onn and pooling
  gtoa_params<B>::onn = 1;
  pmode = pnone;
}

// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void gtoa_eltop_act_params<B>::set_impl_params(
                                      const gtoa_act_params_impl_spec& p // structure with implementation specific parameters
                                      ) {
  gtoa_params<B>::onn = p.onn;
  set_shapes();
}

template<template<typename> class B>
void gtoa_eltop_act_params<B>::get_impl_params(
                                      gtoa_act_params_impl_spec& p       // return structure with implementation specific parameters
                                      ) {
  p.onn = gtoa_params<B>::onn;
}

// Fused maxpooling parameters
template<template<typename> class B>
void gtoa_eltop_act_params<B>::maxpool_enable(
                                       bool            twod,     // false: 1D (horizontally) or true: 2D
                                       bool            filter3,  // false: 2x2 (2) or true: 3x3 (3) maxpooling 2D (1D) filter size
                                       bool            stride2,  // false: stride 1 or true stride 2
                                       const shape<2>& padlim    // maxpool padding limits
                                       ) {
  // set padding bitfield
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PEN_MASK;
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PMIN_MASK;
  // determine pooling mode bits
  pmode = twod ? prowcol : pcol;
  if (filter3) {
    psize = stride2 ? p3s2 : p3s1;
    pool_overlap = stride2 ? 1 : 2;
  } else {
    psize = stride2 ? p2s2 : p2s1;
    pool_overlap = stride2 ? 0 : 1;
  }
  HLAPI.i.u.op.padlim = padlim;
  mpstr = stride2 ? 2 : 1;
  HLAPI.i.u.op.pad_stride = 1;
  HLAPI.i.u.op.out.fm.enable    = (1<<(TNSVSIZE/mpstr))-1;

  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-4][SPATIAL_W] = (1-shapes.ishape[2])*TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-5][SPATIAL_W] = (1-shapes.ishape[2])*TNSVSIZE;;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-6][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_H] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_H] = 1-shapes.ishape[1];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-4][SPATIAL_H] = 1-shapes.ishape[1];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-5][SPATIAL_H] = 1-shapes.ishape[1];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-6][SPATIAL_H] = 0;

  if ((pmode != prowcol) && (pmode != pcol)) {
    pool_overlap = 0;
  }
}


template<template<typename> class B>
void gtoa_eltop_act_params<B>::set_shapes() {
  HLAPI.i.u.op.bf |= gtoa_params<B>::onn == 2 ? (1 << ACT_BF_OP_ALAY_START) : 0;
  int in0dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int in1dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN1DBL_MASK) != 0 ? 2 : 1;
  int fmodbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  bool ifm0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  int i_c = ifm0_en ? shapes.ishape[0]/in0dbl : shapes.ishape[4];   // [c]
  int c   = (cmax+ISIZE-1)/ISIZE;           // rounded up with i16
  int c2  = 2*((cmax+ISIZE*2-1)/(2*ISIZE)); // rounded up with i32
  if (gtoa_params<B>::onn == 2) {
    // o32 accumulator layout
    shapes.ishape[0] = 2;
    i_c = (shapes.ishape[4]+1)/2;
    shapes.ishape[4] = i_c;
    shapes.pshape[0] = (shapes.pshape[0]/c)*c2;
    if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
      shapes.oshape[0] = (shapes.oshape[0]/c)*c2;
    }
    else if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0) {
      // [c][d][w][h][1] -> [c/onn][d][w][h][onn]
      shapes.oshape[4] = ((shapes.oshape[4]/c)*c2)/2;
      shapes.oshape[0] = 2;
    }
    init_prog(alayo32, op, ea_ord, brdc_f);
  } else {
    // o16 accumulator layout
    init_prog(alayo16, op, ea_ord, brdc_f);
  }
  // iterators
  if (ifm0_en) {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3]   = shapes.ishape[0] / (in0dbl * gtoa_params<B>::onn);
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2]   = shapes.ishape[2] * shapes.ishape[3] * shapes.ishape[4] / TNSVSIZE;  // [NOLINT]
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1]   = gtoa_params<B>::onn;
    // primary feature-map input AGU
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]    = gtoa_params<B>::onn * in0dbl;    // mlsb/onn
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.ishape[3];                // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]    = RDIV_UP(shapes.ishape[2],TNSVSIZE); // W/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.ishape[4];                // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.ishape[0] / (gtoa_params<B>::onn*in0dbl); // C
  } else {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = i_c;
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.ishape[1]*shapes.ishape[2]*shapes.ishape[3];
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? shapes.ishape[0] / 2 : shapes.ishape[0];
    // primary accumulator input AGU
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-2] = 1 - (brdc_f.in0_h ? gtoa_params<B>::onn*in0dbl : 0);
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-3] = 1 - (brdc_f.in0_w ? gtoa_params<B>::onn*in0dbl*(brdc_f.in0_h ? 1 : shapes.ishape[1]) : 0);
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-4] = 1 - (brdc_f.in0_c ? gtoa_params<B>::onn*in0dbl*(brdc_f.in0_h ? 1 : shapes.ishape[1])*(brdc_f.in0_w ? 1 : shapes.ishape[2]) : 0);
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-1] = gtoa_params<B>::onn*in0dbl;       // ONN|mlsb
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-2] = shapes.ishape[1]; // H
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-3] = shapes.ishape[2]; // W
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-4] = shapes.ishape[3]*shapes.ishape[4]; // D*C
  }
  // secondary feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
    HLAPI.i.u.op.secondary.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.secondary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1]    = gtoa_params<B>::onn * in1dbl;     // mlsb/onn
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.i1shape[3];                // H
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3]    = RDIV_UP(shapes.i1shape[2],TNSVSIZE); // W/8
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.i1shape[4];                // D
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.i1shape[0] / (gtoa_params<B>::onn*in1dbl); // C
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // feature-map output AGU
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = gtoa_params<B>::onn*fmodbl;        // ONN|mlsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.oshape[3]/str[SPATIAL_H];  // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.oshape[2]/(TNSVSIZE*str[SPATIAL_W]);  // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.oshape[4]/str[SPATIAL_D];  // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.oshape[0] / (gtoa_params<B>::onn*fmodbl); // C
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable        = static_cast<int8_t>((1<<(TNSVSIZE/mpstr))-1);
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf = (static_cast<int>(pmode << ACT_BF_PL_MODE_START)) |
                                                  (static_cast<int>(psize << ACT_BF_PL_SIZE_START));
  } else if((HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0) {
    // accumulator output AGU
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.oshape);
  }
  if (pmode != pnone) {
    // re-calculate the output shape and overlap buffer shape based on maxpooling types
    int oldh = shapes.oshape[3]/str[SPATIAL_H];
    int newh;
    shapes.oshape[2] = shapes.oshape[2]/mpstr;
    switch (psize) {
      case p2s1:
        newh  = ((pmode == prowcol) ? (oldh - 1) : oldh);
        break;
      case p3s1:
        newh  = ((pmode == prowcol) ? (oldh - 2) : oldh);
        break;
      case p2s2:
        newh  = ((pmode == prowcol) ? (oldh/2) : RDIV_UP(oldh, 2));
        break;
      case p3s2:
        newh  = ((pmode == prowcol) ? ((oldh - 1)/2) : RDIV_UP(oldh, 2));
        break;
      default: assert(0 && "unknown size");
    }
    shapes.oshape[3] = (aoffset_t)(newh*str[SPATIAL_H]);
    shapes.mpshape[0] = (aoffset_t)(pool_overlap*fmodbl*c*oldh);
    // re-assign the output feature-map iterators on height dimension
    if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]  = (aoffset_t)newh;  // H
    }
    // set pooling iterator counts from activation output shapes
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-1]    = gtoa_params<B>::onn*fmodbl;
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-2]    = oldh;                   // H
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-3]
    = (shapes.oshape[2]*mpstr)/(TNSVSIZE*str[SPATIAL_W]);   // W/8
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-4]
    = shapes.oshape[0]/(gtoa_params<B>::onn*fmodbl);   // C/ONN
  } else {
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-1]    = 0;
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-2]    = 0;
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-3]    = 0;
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-4]    = 0;
  }
}

// initialize the input 0 tensor
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_eltop_act_params<B>::init_l1_input0(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                              ) {
  tensor_t<ixpix_t,5,B> t = reinterpret_cast<const impl_spec_container_t<B>*>(&p)->data.broadcast(shapes.ishape);
  gtoa_params<B>::itens.data = t;
  t.resize(2, ROUND_UP(t.get_dim(2),TNSVSIZE)); // ensure is multiple of TNSVSIZE (P10019796-66167)
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t,6,B> t0(t.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t,7,B> t1(t0.split(3, t.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t,7,B> t2(t1.transpose({3,0,5,4,6,1,2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = localptr_t<ixpix_t>(t2.get_ptr());
  HLAPI.i.u.op.primary.fm_agu.buf.base = localptr_t<ixpix_t>(t2.get_base());
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = brdc_f.in0_w ? 1 : t2.get_offset(0); // W8 (don't use 0 here in case of w-bcast, use 1)
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

// initialize the input 1 tensor
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_eltop_act_params<B>::init_l1_input(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                              ) {
  tensor_t<ixpix_t,5,B> t = reinterpret_cast<const impl_spec_container_t<B>*>(&p)->data.broadcast(shapes.i1shape);
  gtoa_params<B>::i1tens.data = t;
  t.resize(2, ROUND_UP(t.get_dim(2),TNSVSIZE)); // ensure is multiple of TNSVSIZE // FIX TO BE DONE FOR P10019796-66167
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t,6,B> t0(t.split(0, HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t,7,B> t1(t0.split(3, t.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t,7,B> t2(t1.transpose({3,0,5,4,6,1,2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.secondary.fm_agu.ptr      = localptr_t<ixpix_t>(t2.get_ptr());
  HLAPI.i.u.op.secondary.fm_agu.buf.base = localptr_t<ixpix_t>(t2.get_base());
  HLAPI.i.u.op.secondary.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.secondary.fm_agu.stride   = brdc_f.in1_w ? 1 : t2.get_offset(0); // W8 (don't use 0 here in case of w-bcast, use 1)
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
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP
}

// initialize the output tensor
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_eltop_act_params<B>::init_l1_output(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                              ) {
  gtoa_params<B>::tens = p;
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t,6,B> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t,7,B> t1(t0.split(3, p.data.get_dim(2)/(TNSVSIZE/mpstr)));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t,7,B> t2(t1.transpose({3,0,5,4,6,1,2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = localptr_t<ixpix_t>(t2.get_ptr());
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = localptr_t<ixpix_t>(t2.get_base());
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t2.get_offset(0)*str[SPATIAL_W];     // W8
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(2)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(3)*str[SPATIAL_W]+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)*str[SPATIAL_W]+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(5)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)*str[SPATIAL_W]+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP
}


template<template<typename> class B>
inline void gtoa_eltop_act_params<B>::get_shapes(
                      gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                      ) {
  s = shapes;
  bool ifm0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  if (brdc_f.in0_h) s.ishape[ifm0_en ? 3 : 1] = 1;
  if (brdc_f.in0_w) s.ishape[ifm0_en ? 2 : 2] = 1;
  if (brdc_f.in0_c) s.ishape[ifm0_en ? 0 : 4] = 1;
  if (brdc_f.in1_h) s.i1shape[3] = 1;
  if (brdc_f.in1_w) s.i1shape[2] = 1;
  if (brdc_f.in1_c) s.i1shape[0] = 1; // or i1dbl?2:1
}

template<template<typename> class B>
inline void gtoa_eltop_act_params<B>::set_broadcast_flags(
                      broadcast_t bc_flags
                      ) {
  brdc_f = bc_flags;
}

template<template<typename> class B>
inline void gtoa_eltop_act_params<B>::get_op(
                      act_bin_op_t& elt_op           
                      ) {
  elt_op = op;
}

template<template<typename> class B>
inline void gtoa_eltop_act_params<B>::set_Hdim_AM_by_one(void) {
  shapes.ishape[SPATIAL_H] = 1;
}

template<template<typename> class B>
void gtoa_eltop_act_params<B>::set_tile_channel(aoffset_t noc) {
  gtoa_eltop_act_params<B>::cmax = noc;
}

#undef HLAPI
