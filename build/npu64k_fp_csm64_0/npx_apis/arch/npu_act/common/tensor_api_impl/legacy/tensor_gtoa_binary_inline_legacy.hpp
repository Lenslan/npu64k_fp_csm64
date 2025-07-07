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
 * tensor_gtoa_binary_inline_legacy.hpp
 *
 * File defining a tensor level unary API base on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_BINARY_INLINE_LEGACY_HPP_           // [NOLINT]
#define TENSOR_GTOA_BINARY_INLINE_LEGACY_HPP_           // [NOLINT]
#define HLAPI gtoa_params<B>::hlapi

// constructor
// binary operation from:
// input0 accumulator (32b) + input1 accumulator (32b) to output feature-map (8b/16b)
// input0 accumulator (32b) + input1 per channel param to output feature-map (8b/16b)
// input0 accumulator (32b) + input1 scalar register 0 to output feature-map (8b/16b)
template<template<typename> class B>
gtoa_binary_params<B>::gtoa_binary_params(
                                     // number output channels (not vectors)
                                     aoffset_t                  noi,
                                     // output shape, indexed by spatial_axis_t
                                     const shape<3>&            oshpi,
                                     // 16b output feature-map
                                     bool                       fmodbli,
                                     // binary operation to perform
                                     act_bin_op_t               opi,
                                     // saturate output
                                     bool                       sati) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init

  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input0 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // input1 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.i1shape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmodbli  ? 2*c : c), 1,
                    (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  op = opi;
}

// binary operation from:
// input0 feature-map (8b/16b) + input1 accumulator (32b) to output feature-map (8b/16b)
// input0 feature-map (8b/16b) + input1 per channel param to output feature-map (8b/16b)
// input0 feature-map (8b/16b) + input1 scalar register 0 to output feature-map (8b/16b)
template<template<typename> class B>
gtoa_binary_params<B>::gtoa_binary_params(
                                     // number output channels (not vectors)
                                     aoffset_t                  noi,
                                     // output shape, indexed by spatial_axis_t
                                     const shape<3>&            oshpi,
                                     // 16b input feature-map
                                     bool                       fmidbli,
                                     // 16b output feature-map
                                     bool                       fmodbli,
                                     // binary operation to perform
                                     act_bin_op_t               opi,
                                     // saturate output
                                     bool                       sati) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init

  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input0 feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmidbli  ? 2*c : c), 1,
                    (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // input1 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.i1shape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmodbli  ? 2*c : c), 1,
                    (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  op = opi;
}

// binary operation from:
// input0 feature-map (8b/16b) + input1 feature-map (8b/16b) to output feature-map (8b/16b)
template<template<typename> class B>
gtoa_binary_params<B>::gtoa_binary_params(
                                     // number output channels (not vectors)
                                     aoffset_t                  noi,
                                     // output shape, indexed by spatial_axis_t
                                     const shape<3>&            oshpi,
                                     // 16b input feature-map 0
                                     bool                       fmi0dbli,
                                     // 16b input feature-map 1
                                     bool                       fmi1dbli,
                                     // 16b output feature-map
                                     bool                       fmodbli,
                                     // binary operation to perform
                                     act_bin_op_t               opi,
                                     // saturate output
                                     bool                       sati) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init

  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input0 feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmi0dbli  ? 2*c : c), 1,
                    (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // input1 feature-map in ixpix_t [D][H][W][C] format
  shapes.i1shape = { (aoffset_t)(fmi1dbli  ? 2*c : c), 1,
                     (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmodbli  ? 2*c : c), 1,
                    (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  op = opi;
}

// binary operation from:
// input0 accumulator (32b) + input1 accumulator (32b) to output accumulator (32b)
// input0 accumulator (32b) + input1 per channel param to output accumulator (32b)
// input0 accumulator (32b) + input1 scalar register 0 to output accumulator (32b)
template<template<typename> class B>
gtoa_binary_params<B>::gtoa_binary_params(
                                     // number output channels (not vectors)
                                     aoffset_t                  noi,
                                     // output shape, indexed by spatial_axis_t
                                     const shape<3>&            oshpi,
                                     // binary operation to perform
                                     act_bin_op_t               opi) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init

  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input0 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // input1 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.i1shape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  op = opi;
}

// binary operation from:
// input0 feature-map (8b/16b) + input1 accumulator (32b) to output accumulator (32b)
// input0 feature-map (8b/16b) + input1 per channel param to output accumulator (32b)
// input0 feature-map (8b/16b) + input1 scalar register 0 to output accumulator (32b)
template<template<typename> class B>
gtoa_binary_params<B>::gtoa_binary_params(
                                    // number output channels (not vectors)
                                     aoffset_t                  noi,
                                     // output shape, indexed by spatial_axis_t
                                     const shape<3>&            oshpi,
                                     // 16b input feature-map
                                     bool                       fmidbli,
                                     // binary operation to perform
                                     act_bin_op_t               opi) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init

  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input0 feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmidbli  ? 2*c : c), 1,
                    (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // input1 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.i1shape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  op = opi;
}

// binary operation from:
// input0 feature-map (8b/16b) + input1 feature-map (8b/16b) to output accumulator (32b)
template<template<typename> class B>
gtoa_binary_params<B>::gtoa_binary_params(
                                     // number output channels (not vectors)
                                     aoffset_t                  noi,
                                     // output shape, indexed by spatial_axis_t
                                     const shape<3>&            oshpi,
                                     // 16b input feature-map 0
                                     bool                       fmi0dbli,
                                     // 16b input feature-map 1
                                     bool                       fmi1dbli,
                                     // binary operation to perform
                                     act_bin_op_t               opi) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init

  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input0 feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmi0dbli  ? 2*c : c), 1,
                    (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // input1 feature-map in ixpix_t [D][H][W][C] format
  shapes.i1shape = { (aoffset_t)(fmi1dbli  ? 2*c : c), 1,
                     (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  op = opi;
}

#undef HLAPI
#endif    // TENSOR_GTOA_BINARY_INLINE_LEGACY_HPP_    // [NOLINT]
