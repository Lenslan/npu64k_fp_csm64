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
 * tensor_gtoa_act_inline.hpp
 *
 * File defining a tensor level activation function API base on the generic tensor operation API
 *
 */

//
// Constructors
//
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_ACT_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_ACT_INLINE_HPP_

#include "./legacy/tensor_gtoa_act_inline_legacy.hpp"

#define HLAPI gtoa_params<B>::hlapi

template<template<typename> class B>
gtoa_act_params<B>::gtoa_act_params(
                                 // number output channels (not vectors)
                                 aoffset_t                  noi,
                                 // output shape, indexed by spatial_axis_t
                                 const shape<3>&            oshpi,
                                 const shape<3>&            ostr,          // output stride
                                 // type of primary input
                                 act_dtype_t                intp,
                                 // type of output
                                 act_dtype_t                outtp,
                                 // if true then input stream
                                 bool                       inastri) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  bool idbl = (intp  == dtype_int16) || (intp  == dtype_fp16) || (intp  == dtype_bf16) || (intp == dtype_int48);
  bool odbl = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  HLAPI.i.u.op.bf = (idbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                    (odbl ? 1 << ACT_BF_OP_OUTDBL_START : 0);

  // update mask and floating mode field based on input/output type
  switch (intp) {
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
  cmax = noi;
  mpstr = 1;
  str   = ostr;
  // default scaling factor type
  fp16scl = true;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // input feature-map in ixpix_t [D][H][W][C] format
    shapes.ishape = { (aoffset_t)(idbl  ? 2 * c : c),
                      1,
                      (aoffset_t)(w*TNSVSIZE),
                      (aoffset_t)(oshpi[SPATIAL_H]),
                      (aoffset_t)(oshpi[SPATIAL_D]) };
  } else {
     // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
    shapes.ishape = { (aoffset_t)(idbl ? 2 : 1),
                      (aoffset_t)(oshpi[SPATIAL_H]),
                      (aoffset_t)w,
                      (aoffset_t)(oshpi[SPATIAL_D]),
                      (aoffset_t)c };
  }
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // output feature-map in ixpix_t [D][H][W][C] format
    shapes.oshape = { (aoffset_t)(odbl  ? 2*c : c),
                      1,
                      (aoffset_t)(w*TNSVSIZE*str[SPATIAL_W]),
                      (aoffset_t)(oshpi[SPATIAL_H]*str[SPATIAL_H]),
                      (aoffset_t)(oshpi[SPATIAL_D]*str[SPATIAL_D]) };
    // maxpool overlap buffer ixpix_t [stash_sz]
    shapes.mpshape = {(aoffset_t)(2*c*(oshpi[SPATIAL_H]))};
  } else {
    // output accumulator shape
    shapes.oshape = { 1,
                      (aoffset_t)(oshpi[SPATIAL_H]),
                      (aoffset_t)w,
                      (aoffset_t)(oshpi[SPATIAL_D]),
                      (aoffset_t)c };
  }
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  // default onn and pooling
  gtoa_params<B>::onn = 1;
  pmode = pnone;
}

// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void gtoa_act_params<B>::set_impl_params(
                                      // structure with implementation specific parameters
                                      const gtoa_act_params_impl_spec& p
                                      ) {
  gtoa_params<B>::onn = p.onn;
  set_shapes();
}

template<template<typename> class B>
void gtoa_act_params<B>::get_impl_params(
                                      // return structure with implementation specific parameters
                                      gtoa_act_params_impl_spec& p
                                      ) {
  p.onn = gtoa_params<B>::onn;
}

// Fused maxpooling parameters
template<template<typename> class B>
void gtoa_act_params<B>::maxpool_enable(
                                       // false: 1D (horizontally) or true: 2D
                                       bool            twod,
                                       // false: 2x2 (2) or true: 3x3 (3)
                                       // maxpooling 2D (1D) filter size
                                       bool            filter3,
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
  HLAPI.i.u.op.out.fm.enable    = (1 << (TNSVSIZE / mpstr)) - 1;
  int i_w = shapes.ishape[2];
  int i_h = shapes.ishape[1];
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    i_w = shapes.ishape[2] / TNSVSIZE;
    i_h = shapes.ishape[3];
  }

  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_W] = 0;              // mlsb
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_W] = 0;              // H
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_W] = TNSVSIZE;          // W
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-4][SPATIAL_W] = (1-i_w)*TNSVSIZE;  // D (fm) or D*C (acc)
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-5][SPATIAL_W] = (1-i_w)*TNSVSIZE;  // C (fm)
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-6][SPATIAL_W] = 0;              // not used
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_H] = 0;              // mlsb
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_H] = 1;              // H
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_H] = 1-i_h;          // W
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-4][SPATIAL_H] = 1-i_h;          // D (fm) or D*C (acc)
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-5][SPATIAL_H] = 1-i_h;          // C (fm)
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-6][SPATIAL_H] = 0;              // not used

  if ((pmode != prowcol) && (pmode != pcol)) {
    pool_overlap = 0;
  }
}

template<template<typename> class B>
void gtoa_act_params<B>::set_shapes() {
  int fmi0dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmodbl  = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  bool ifm0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool iac0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0;
  bool istr_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_ASTR0) != 0;
  bool ofm_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0;
  bool oac_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0;
  HLAPI.i.u.op.bf |= gtoa_params<B>::onn == 2 ? (1 << ACT_BF_OP_ALAY_START) : 0;
  int fmdbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  int i_c = (iac0_en | istr_en) ? shapes.ishape[4] : shapes.ishape[0]/fmi0dbl;   // [c]
  int c  = (cmax+ISIZE-1)/ISIZE;       // rounded up with i16
  int c2 = 2*((cmax+ISIZE*2-1)/(2*ISIZE));   // rounded up with i32
  if (gtoa_params<B>::onn == 2) {
    // o32 accumulator layout
    i_c = (i_c + 1) / 2;
    if (iac0_en | istr_en) {
      shapes.ishape[0] = 2;
      shapes.ishape[4] = i_c;
    }
    shapes.pshape[0] = (shapes.pshape[0] / c) * c2;
    if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
      shapes.oshape[0] = (shapes.oshape[0] / c) * c2;
    } else if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0) {
      // [c][d][w][h][1] -> [c/onn][d][w][h][onn]
      shapes.oshape[4] = ((shapes.oshape[4] / c) * c2) / 2;
      shapes.oshape[0] = 2;
    }
    init_prog(alayo32);
  } else {
    // o16 accumulator layout
    init_prog(alayo16);
  }
  // iterators
  if (ofm_en) {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3]   = shapes.oshape[0] / (fmodbl * gtoa_params<B>::onn);
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2]   = shapes.oshape[2] * shapes.oshape[3] * shapes.oshape[4] / (TNSVSIZE * str[SPATIAL_H] * str[SPATIAL_W] * str[SPATIAL_D]);  // [NOLINT]
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1]   = gtoa_params<B>::onn;
  } else if (oac_en) {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = i_c;
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = shapes.oshape[1] * shapes.oshape[2] * shapes.oshape[3]; // oshpi[SPATIAL_H] * w * oshpi[SPATIAL_D]  // NOLINT
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = shapes.oshape[0];
  }

  // primary feature-map input
  if (ifm0_en) {
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]    = gtoa_params<B>::onn*fmi0dbl;  // mlsb
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.ishape[3];  // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.ishape[2]/TNSVSIZE;  // W/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.ishape[4];  // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.ishape[0]
                                                        / (gtoa_params<B>::onn * fmi0dbl);  // C
  }
  // accumulator input AGU
  if (iac0_en | istr_en) {
    for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    int accdbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 1] = gtoa_params<B>::onn*accdbl;  // ONN|mlsb
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 2] = shapes.ishape[1];  // H
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 3] = shapes.ishape[2];  // W
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 4] = shapes.ishape[3]
                                                        * shapes.ishape[4];  // D*C
  }
  // feature-map output
  if (ofm_en) {
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]
    = gtoa_params<B>::onn*fmdbl;        // ONN|mlsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]    = shapes.oshape[3] / str[SPATIAL_H];  // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]
    = shapes.oshape[2]/(TNSVSIZE*str[SPATIAL_W]);   // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]    = shapes.oshape[4] / str[SPATIAL_D];  // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5]
    = shapes.oshape[0] / (gtoa_params<B>::onn*fmdbl);    // C
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf = (static_cast<int>(pmode << ACT_BF_PL_MODE_START)) |
                                                  (static_cast<int>(psize << ACT_BF_PL_SIZE_START));
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable        = (1 << TNSVSIZE / mpstr) - 1;
  } else if (oac_en) {
    // accumulator output
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
        newh  = ((pmode == prowcol) ? (oldh/2) : RDIV_UP(oldh, 2));  // round up if 1d
        break;
      case p3s2:
        newh  = ((pmode == prowcol) ? ((oldh - 1)/2) : RDIV_UP(oldh, 2));  // round up if 1d
        break;
      default: assert(0 && "unknown size");
    }
    shapes.oshape[3] = (aoffset_t)(newh*str[SPATIAL_H]);
    shapes.mpshape[0] = (aoffset_t)(pool_overlap*fmdbl*c*oldh);
    // re-assign the output feature-map iterators on height dimension
    if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]  = (aoffset_t)newh;  // H
    }
    // set pooling iterator counts from activation output shapes
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-1]    = gtoa_params<B>::onn*fmdbl;
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-2]    = oldh;                   // H
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-3]
    = (shapes.oshape[2]*mpstr)/(TNSVSIZE*str[SPATIAL_W]);   // W/8
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-4]
    = shapes.oshape[0]/(gtoa_params<B>::onn*fmdbl);   // C/ONN
  } else {
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-1]    = 0;
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-2]    = 0;
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-3]    = 0;
    HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-4]    = 0;
  }
}

// reshape ofm iteratot (to make tricks)
template<template<typename> class B>
void gtoa_act_params<B>::reshape_ofm_iter(const shape<5>& oshape) {
  assert(shapes.oshape[0]*shapes.oshape[2]*shapes.oshape[3]*shapes.oshape[4] == oshape[0]*oshape[2]*oshape[3]*oshape[4]);
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    int fmdbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = oshape[3] / str[SPATIAL_H];              // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = oshape[2] / (TNSVSIZE*str[SPATIAL_W]);      // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = oshape[4] / str[SPATIAL_D];              // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5] = oshape[0] / (gtoa_params<B>::onn*fmdbl); // C
  }
}

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_act_params<B>::init_l1(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                              ) {
  gtoa_params<B>::tens = p;
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, B> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t, 7, B> t1(t0.split(3, p.data.get_dim(2)/(TNSVSIZE/mpstr)));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, B> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

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



// initialize the primary input tensors
  template<template<typename> class B>
  template<template<typename> class BD>
  void gtoa_act_params<B>::init_l1_input(
                                  // structure with allocated buffers and tensors in
                                  // L1 memory [D][H][W][Grp][C]
                                  const impl_spec_container_t<BD>&  p) {
  gtoa_params<B>::itens = p;
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, B> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5]));
  tensor_t<ixpix_t, 7, B> t1(t0.split(3, p.data.get_dim(2) / TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, B> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = localptr_t<ixpix_t>(t2.get_ptr());
  HLAPI.i.u.op.primary.fm_agu.buf.base = localptr_t<ixpix_t>(t2.get_base());
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
inline void gtoa_act_params<B>::get_shapes(
                      // structure with implementation specific minimum buffer sizes
                      gtoa_act_params_impl_shapes& s
                      ) {
  s = shapes;
}

template<template<typename> class B>
void gtoa_act_params<B>::set_tile_channel(aoffset_t noc) {
  gtoa_act_params<B>::cmax = noc;
}

#undef HLAPI
#endif   // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_ACT_INLINE_HPP_
