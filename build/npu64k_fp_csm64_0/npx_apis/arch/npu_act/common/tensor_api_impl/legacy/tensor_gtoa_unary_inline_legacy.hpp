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
 * tensor_gtoa_unary_inline_legacy.hpp
 *
 * File defining a tensor level unary API base on the generic tensor operation API
 *
 */

#define HLAPI gtoa_params<B>::hlapi

// constructor
// unary operation from accumulator (32b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_unary_params<B>::gtoa_unary_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmdbli,        // 16b output feature-map
                                     act_una_op_t               opi,           // unary operation to perform
                                     bool                       sati           // saturate output
                                     ) : gtoa_params<B>() {
  // enable accumulator input and feature-map output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (          0<<ACT_BF_OP_IN0DBL_START    ) |
                          (fmdbli  ? 1<<ACT_BF_OP_OUTDBL_START : 0) |
                          (sati    ? 1<<ACT_BF_OP_OUTSAT_START : 0);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmdbli  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { noi };
  bool fop = (opi == op_fabs || opi == op_raddv || opi == op_rmaxv || opi == op_rminv);
  if (fop) {
    // select floating point version program
    init_unary_fp(HLAPI, opi);
  } else {
    // select integer version program
    init_unary(HLAPI, opi);
  }
  set_unary_params();
}

// unary operation from accumulator (32b) to accumulator (32b)
template<template<typename> class B>
gtoa_unary_params<B>::gtoa_unary_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     act_una_op_t               opi           // unary operation to perform
                                     ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = (          0<<ACT_BF_OP_IN0DBL_START    ) |
                          (          0<<ACT_BF_OP_OUTDBL_START    ) |
                          (          0<<ACT_BF_OP_OUTSAT_START    );
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { noi };
  bool fop = (opi == op_fabs || opi == op_raddv || opi == op_rmaxv || opi == op_rminv);
  if (fop) {
    // select floating point version program
    init_unary_fp(HLAPI, opi);
  } else {
    // select integer version program
    init_unary(HLAPI, opi);
  }
  set_unary_params();
}

// unary operation from feature-map (8b/16b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_unary_params<B>::gtoa_unary_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmidbli,       // 16b input feature-map
                                     bool                       fmodbli,       // 16b output feature-map
                                     act_una_op_t               opi,           // unary operation to perform
                                     bool                       sati          // saturate output
                                     ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (fmidbli ? 1<<ACT_BF_OP_IN0DBL_START : 0) |
                          (fmodbli ? 1<<ACT_BF_OP_OUTDBL_START : 0) |
                          (sati    ? 1<<ACT_BF_OP_OUTSAT_START : 0);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmidbli  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmodbli  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { noi };
  bool fop = (opi == op_fabs || opi == op_raddv || opi == op_rmaxv || opi == op_rminv);
  if (fop) {
    // select floating point version program
    init_unary_fp(HLAPI, opi);
  } else {
    // select integer version program
    init_unary(HLAPI, opi);
  }
  set_unary_params();
}

// unary operation from feature-map (8b/16b) to accumulator (32b)
template<template<typename> class B>
gtoa_unary_params<B>::gtoa_unary_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmdbli,        // 16b input feature-map
                                     act_una_op_t               opi            // unary operation to perform
                                     ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = (fmdbli  ? 1<<ACT_BF_OP_IN0DBL_START : 0) |
                          (          0<<ACT_BF_OP_OUTDBL_START    ) |
                          (          0<<ACT_BF_OP_OUTSAT_START    );
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmdbli  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { noi };
  bool fop = (opi == op_fabs || opi == op_raddv || opi == op_rmaxv || opi == op_rminv);
  if (fop) {
    // select floating point version program
    init_unary_fp(HLAPI, opi);
  } else {
    // select integer version program
    init_unary(HLAPI, opi);
  }
  set_unary_params();
}

// constructor
// unary operation from accumulator (32b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_unary_params<B>::gtoa_unary_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmdbli,        // 16b output feature-map
                                     act_bin_op_t               opi,           // unary operation to perform
                                     bool                       sati           // saturate output
                                     ) : gtoa_params<B>() {
  // enable accumulator input and feature-map output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (          0<<ACT_BF_OP_IN0DBL_START    ) |
                          (fmdbli  ? 1<<ACT_BF_OP_OUTDBL_START : 0) |
                          (sati    ? 1<<ACT_BF_OP_OUTSAT_START : 0);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmdbli  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { noi };
  bool fop = (opi == op_feq || opi == op_fneq || opi == op_fgt || opi == op_fgte
           || opi == op_flt || opi == op_flte || opi == op_fadd || opi == op_frsub);
  if (fop) {
    // select floating point version program
    init_unary_fp(HLAPI, opi);
  } else {
    // select integer version program
    init_unary(HLAPI, opi);
  }
  set_unary_params();
}

// unary operation from accumulator (32b) to accumulator (32b)
template<template<typename> class B>
gtoa_unary_params<B>::gtoa_unary_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     act_bin_op_t               opi           // unary operation to perform
                                     ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = (          0<<ACT_BF_OP_IN0DBL_START    ) |
                          (          0<<ACT_BF_OP_OUTDBL_START    ) |
                          (          0<<ACT_BF_OP_OUTSAT_START    );
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { noi };
  bool fop = (opi == op_feq || opi == op_fneq || opi == op_fgt || opi == op_fgte
           || opi == op_flt || opi == op_flte || opi == op_fadd || opi == op_frsub);
  if (fop) {
    // select floating point version program
    init_unary_fp(HLAPI, opi);
  } else {
    // select integer version program
    init_unary(HLAPI, opi);
  }
  set_unary_params();
}

// unary operation from feature-map (8b/16b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_unary_params<B>::gtoa_unary_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmidbli,       // 16b input feature-map
                                     bool                       fmodbli,       // 16b output feature-map
                                     act_bin_op_t               opi,           // unary operation to perform
                                     bool                       sati           // saturate output
                                     ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (fmidbli ? 1<<ACT_BF_OP_IN0DBL_START : 0) |
                          (fmodbli ? 1<<ACT_BF_OP_OUTDBL_START : 0) |
                          (sati    ? 1<<ACT_BF_OP_OUTSAT_START : 0);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmidbli  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmodbli  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { noi };
  bool fop = (opi == op_feq || opi == op_fneq || opi == op_fgt || opi == op_fgte
           || opi == op_flt || opi == op_flte || opi == op_fadd || opi == op_frsub);
  if (fop) {
    // select floating point version program
    init_unary_fp(HLAPI, opi);
  } else {
    // select integer version program
    init_unary(HLAPI, opi);
  }
  set_unary_params();
}

// unary operation from feature-map (8b/16b) to accumulator (32b)
template<template<typename> class B>
gtoa_unary_params<B>::gtoa_unary_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmdbli,        // 16b input feature-map
                                     act_bin_op_t               opi            // unary operation to perform
                                     ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = (fmdbli  ? 1<<ACT_BF_OP_IN0DBL_START : 0) |
                          (          0<<ACT_BF_OP_OUTDBL_START    ) |
                          (          0<<ACT_BF_OP_OUTSAT_START    );
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmdbli  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { noi };
  bool fop = (opi == op_feq || opi == op_fneq || opi == op_fgt || opi == op_fgte
           || opi == op_flt || opi == op_flte || opi == op_fadd || opi == op_frsub);
  if (fop) {
    // select floating point version program
    init_unary_fp(HLAPI, opi);
  } else {
    // select integer version program
    init_unary(HLAPI, opi);
  }
  set_unary_params();
}

#undef HLAPI

