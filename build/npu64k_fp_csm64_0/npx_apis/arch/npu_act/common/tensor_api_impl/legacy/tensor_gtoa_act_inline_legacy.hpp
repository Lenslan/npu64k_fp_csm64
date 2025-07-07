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
 * tensor_gtoa_act_inline_legacy.hpp
 *
 * File defining a tensor level activation function API base on the generic tensor operation API
 *
 */

//
// Constructors
//
// AM32/48 to VM8/16
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_ACT_INLINE_LEGACY_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_ACT_INLINE_LEGACY_HPP_
#define HLAPI gtoa_params<B>::hlapi
template<template<typename> class B>
gtoa_act_params<B>::gtoa_act_params(
                                 // number output channels (not vectors)
                                 aoffset_t                  noi,
                                 // output shape, indexed by spatial_axis_t
                                 const shape<3>&            oshpi,
                                 const shape<3>&            ostr,          // output stride
                                 // double wide input accumulator
                                 bool                       accdbli,
                                 bool                       fmdbli,        // 16b output feature-map
                                 // if true then input stream
                                 bool                       inastri) : gtoa_params<B>() {
  // legacy uses FP16 scale
  fp16scl = true;
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  if (inastri) {
    // input from streaming FIFO
    HLAPI.i.u.op.io_en    = ACT_IO_EN_ASTR0 | ACT_IO_EN_OFM;
  } else {
    // input from AM
    HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_OFM;
  }
  HLAPI.i.u.op.bf       = (accdbli ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                          (fmdbli  ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                          (1 << ACT_BF_OP_OUTSAT_START);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  mpstr = 1;
  str   = ostr;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);
  // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { (aoffset_t)(accdbli ? 2 : 1), oshpi[SPATIAL_H], (aoffset_t)w,
                    oshpi[SPATIAL_D], (aoffset_t)c };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmdbli  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE*str[SPATIAL_W]),
                    (aoffset_t)(oshpi[SPATIAL_H]*str[SPATIAL_H]),
                    (aoffset_t)(oshpi[SPATIAL_D]*str[SPATIAL_D]) };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  // maxpool overlap buffer ixpix_t [stash_sz]
  shapes.mpshape = {(aoffset_t)(2*c*(oshpi[SPATIAL_H]))};
  // default onn and pooling
  gtoa_params<B>::onn = 1;
  pmode = pnone;
}
// AM32/48 to AM32
template<template<typename> class B>
gtoa_act_params<B>::gtoa_act_params(
                                 // number output channels (not vectors)
                                 aoffset_t                  noi,
                                 // output shape, indexed by spatial_axis_t
                                 const shape<3>&            oshpi,
                                 // double wide input accumulator
                                 bool                       accdbli,
                                 // if true then input stream
                                 bool                       inastri) : gtoa_params<B>() {
  // legacy uses FP16 scale
  fp16scl = true;
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  if (inastri) {
    // input from streaming FIFO
    HLAPI.i.u.op.io_en    = ACT_IO_EN_ASTR0 | ACT_IO_EN_OAC;
  } else {
    // input from AM
    HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_OAC;
  }
  HLAPI.i.u.op.bf       = (accdbli ? 1 << ACT_BF_OP_IN0DBL_START : 0);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  mpstr = 1;
  str = {1, 1, 1};
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { (aoffset_t)(accdbli ? 2 : 1), oshpi[SPATIAL_H], (aoffset_t)w,
                    oshpi[SPATIAL_D], (aoffset_t)c };
  // output accumulator shape
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  // default onn and pooling
  gtoa_params<B>::onn = 1;
  pmode = pnone;
}
// FM8/16 to FM8/16
template<template<typename> class B>
gtoa_act_params<B>::gtoa_act_params(
                                   // number output channels (not vectors)
                                   aoffset_t                  noi,
                                   // double wide input featuremap
                                   bool                       fmidbli,
                                   // output shape, indexed by spatial_axis_t
                                   const shape<3>&            oshpi,
                                   // output stride
                                   const shape<3>&            ostr,
                                   // 16b output feature-map
                                   bool                       fmodbli,
                                   // if true then input stream
                                   bool                       inastri) : gtoa_params<B>() {
  // legacy uses FP16 scale
  fp16scl = true;
  // enable feature map input and feature map output
  HLAPI.i.bf            = 0;       // function, not LUT init
  if (inastri) {
    // input from streaming FIFO
    HLAPI.i.u.op.io_en    = ACT_IO_EN_ASTR0 | ACT_IO_EN_OFM;
  } else {
    // input from VM
    HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  }
  HLAPI.i.u.op.bf       = (fmidbli ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                          (fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                          (1 << ACT_BF_OP_OUTSAT_START);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  mpstr = 1;
  str   = ostr;
  int c = (noi + ISIZE-1) / ISIZE;
  int w = (oshpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmidbli  ? 2 * c : c),
                    1,
                    (aoffset_t)(w*TNSVSIZE),
                    (aoffset_t)(oshpi[SPATIAL_H]),
                    (aoffset_t)(oshpi[SPATIAL_D])
                  };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmodbli  ? 2 * c : c),
                    1,
                    (aoffset_t)(w * TNSVSIZE * str[SPATIAL_W]),
                    (aoffset_t)(oshpi[SPATIAL_H] * str[SPATIAL_H]),
                    (aoffset_t)(oshpi[SPATIAL_D] * str[SPATIAL_D])
                  };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  // maxpool overlap buffer ixpix_t [stash_sz]
  shapes.mpshape = {(aoffset_t)(2*c*(oshpi[SPATIAL_H]))};
  // default onn and pooling
  gtoa_params<B>::onn = 1;
  pmode = pnone;
}
// FM8/16 to AM32
template<template<typename> class B>
gtoa_act_params<B>::gtoa_act_params(
                                 // number output channels (not vectors)
                                 aoffset_t                  noi,
                                 // double wide input featuremap
                                 bool                       fmidbli,
                                 // output shape, indexed by spatial_axis_t
                                 const shape<3>&            oshpi,
                                 // if true then input stream
                                 bool                       inastri) : gtoa_params<B>() {
  // legacy uses FP16 scale
  fp16scl = true;
  // enable vm input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  if (inastri) {
    // input from streaming FIFO
    HLAPI.i.u.op.io_en    = ACT_IO_EN_ASTR0 | ACT_IO_EN_OAC;
  } else {
    // input from VM
    HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_OAC;
  }
  HLAPI.i.u.op.bf       = (fmidbli ? 1 << ACT_BF_OP_IN0DBL_START : 0);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  mpstr = 1;
  str = {1, 1, 1};
  int c = (noi + ISIZE - 1) / ISIZE;
  int w = (oshpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmidbli  ? 2 * c : c),
                    1,
                    (aoffset_t)(w * TNSVSIZE),
                    (aoffset_t)(oshpi[SPATIAL_H]), (aoffset_t)(oshpi[SPATIAL_D])
                  };
  // output accumulator shape
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  // default onn and pooling
  gtoa_params<B>::onn = 1;
  pmode = pnone;
}
#undef HLAPI
#endif   // NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_ACT_INLINE_LEGACY_HPP_
