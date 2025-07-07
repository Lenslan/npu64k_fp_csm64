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
 * tensor_gtoa_exp_inline.hpp
 *
 * File defining a tensor level exponent function API base on the generic tensor operation API
 *
 */

#define HLAPI gtoa_params<B>::hlapi

//
// Constructors
//
// AM32 to AM32
template<template<typename> class B>
gtoa_exp_params<B>::gtoa_exp_params(
                                 aoffset_t                  noi,           // number output channels (not vectors)
                                 const shape<3>&            oshpi          // output shape, indexed by spatial_axis_t
                                 ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = 0;
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0FP32_MASK | ACT_BF_OP_OUTFP32_MASK;
  cmax = noi;
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;    
  // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { (aoffset_t)1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // no per channel parameters
  shapes.pshape = { (aoffset_t)0 };
  // default onn and pooling
  gtoa_params<B>::onn = 1;
  // initialize HLAPI program
  init_exp(HLAPI, false, true);
  init_hlapi();
}

// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void gtoa_exp_params<B>::set_impl_params(
                                      const gtoa_act_params_impl_spec& p // structure with implementation specific parameters
                                      ) {
}

template<template<typename> class B>
void gtoa_exp_params<B>::get_impl_params(
                                      gtoa_act_params_impl_spec& p       // return structure with implementation specific parameters
                                      ) {
  p.onn = 1;
}

template<template<typename> class B>
void gtoa_exp_params<B>::init_hlapi() {
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.ishape[4];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.ishape[1]*shapes.ishape[2]*shapes.ishape[3];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.ishape[0];
  // accumulator input AGU
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0) {
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i]    = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.ishape);
  }
  // feature-map input AGU
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // feature-map input AGU
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    int fmdbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]    = fmdbl;             // mlsb
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.ishape[3];  // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.ishape[2]/TNSVSIZE;  // W/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.ishape[4];  // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.ishape[0] / (fmdbl); // C
  }
  // accumulator output AGU
  for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
    HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
  HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.oshape);
  HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-1]    = 0;
  HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-2]    = 0;
  HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-3]    = 0;
  HLAPI.i.u.op.out.fm.pool.iter[ACT_POOL_LOOPS-4]    = 0;
}

// initialize the input tensor
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_exp_params<B>::init_l1_input(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                              ) {
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
inline void gtoa_exp_params<B>::get_shapes(
                                          gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                                          ) {
  s = shapes;
}

#undef HLAPI

