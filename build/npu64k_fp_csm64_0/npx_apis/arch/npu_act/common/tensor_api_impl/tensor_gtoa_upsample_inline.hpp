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
 * tensor_gtoa_upsample_inline.hpp
 *
 * File defining a tensor level upsample API base on the generic tensor operation API
 *
 */


#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_UPSAMPLE_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_UPSAMPLE_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// constructor
// upsample operation from feature-map (8b/16b) to feature-map (8b/16b), with output broadcast
// input shape is from [0,offset*(oshpi-1)]
template<template<typename> class B>
gtoa_upsample_params<B>::gtoa_upsample_params(
             aoffset_t                  noi,           // number output channels (not vectors)
             float                      hstart,        // input start position h
             float                      hdelta,        // input h increment per output h
             const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
             bool                       fmdbli         // 16b I/O feature-map
                                     )
             : gtoa_params<B>() {
  no              = noi;
  ishp            = oshpi;
  ishp[SPATIAL_H] = 1+ceilf((oshpi[SPATIAL_H]-1)*hdelta);
  oshp            = oshpi;
  mode            = true;
  fmdbl           = fmdbli;
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_GTH | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = fmdbli ? (1 << ACT_BF_OP_IN0DBL_START) |
                                   (1 << ACT_BF_OP_OUTDBL_START) : 0;
  int c  = RDIV_UP(noi, ISIZE);
  int wo = NRND_UP(oshpi[SPATIAL_W], TNSVSIZE);
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmdbli  ? 2 * c : c), 1, ishp[SPATIAL_W],
                    ishp[SPATIAL_H], ishp[SPATIAL_D] };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmdbli  ? 2 * c : c), 1, (aoffset_t)wo,
                    oshp[SPATIAL_H], oshp[SPATIAL_D] };
  init_upsample(HLAPI, hstart, hdelta);
  set_upsample_params();
}


// upsample operation from feature-map (8b/16b) to feature-map (8b/16b), with output broadcast
template<template<typename> class B>
gtoa_upsample_params<B>::gtoa_upsample_params(
             aoffset_t                  noi,           // number output channels (not vectors)
             const shape<3>&            ishpi,         // output shape, indexed by spatial_axis_t
             const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
             bool                       fmdbli         // 16b I/O feature-map
                                     )
             : gtoa_params<B>() {
  no    = noi;
  ishp  = ishpi;
  oshp  = oshpi;
  mode  = false;
  fmdbl = fmdbli;
  for (int i = 0; i < 3; i++) {
    assert(((oshpi[i] % ishpi[i]) == 0) && "output width should be multiple of input width");
  }
  // enable gather input and feature-map output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = fmdbli ? (1 << ACT_BF_OP_IN0DBL_START) |
                                   (1 << ACT_BF_OP_OUTDBL_START) : 0;
  int c  = RDIV_UP(noi, ISIZE);
  int wo = NRND_UP(oshpi[SPATIAL_W], (TNSVSIZE * oshpi[SPATIAL_W]) / ishpi[SPATIAL_W]);
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmdbli  ? 2 * c : c), 1, ishpi[SPATIAL_W],
                    ishpi[SPATIAL_H], ishpi[SPATIAL_D] };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmdbli  ? 2 * c : c), 1, (aoffset_t)wo,
                    oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  init_upsample(HLAPI);
  set_upsample_params();
}


// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void gtoa_upsample_params<B>::set_upsample_params() {
  int fmdbli = fmdbl ? 2 : 1;
  if (mode) {
    // V2 mode, gather over H
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1]   = 1;
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2]   = RDIV_UP(oshp[SPATIAL_W], TNSVSIZE) * oshp[SPATIAL_D] * (shapes.oshape[0]/fmdbli);
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3]   = oshp[SPATIAL_H];
    // feature-map input AGU
    for (int i = 0; i < ACT_FM_LOOPS; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
      HLAPI.i.u.op.out.fm.fm_agu.iter[i]  = 1;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = shapes.oshape[0];                 // C*mlsb
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = RDIV_UP(oshp[SPATIAL_W], TNSVSIZE);  // W
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = oshp[2];                          // D
    HLAPI.i.u.op.primary.fm_agu.iter[0]                = oshp[1];                          // H, gather dimension
    // feature-map output AGU
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]  = shapes.oshape[0];                 // C*msb/lsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]  = RDIV_UP(oshp[SPATIAL_W], TNSVSIZE);  // W
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]  = oshp[2];                          // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]  = oshp[1];                          // H
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable        = (int8_t)((1 << TNSVSIZE)-1);
  } else {
    // V1 mode, iterators, inner loop writes same input multiple times
    shape<3> tshp(ishp);
    tshp[0] = RDIV_UP(tshp[0], TNSVSIZE);
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3]   = 1;
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2]   = get_shape_size(tshp) * (shapes.ishape[0]/fmdbli);
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1]   = get_shape_size(oshp) / get_shape_size(ishp);
    // feature-map input AGU
    for (int i = 0; i < ACT_FM_LOOPS - 4; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = ishp[2];            // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = tshp[0];            // W
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = ishp[1];            // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.ishape[0];   // C
    // feature-map output AGU
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]  = oshp[0] / ishp[0];  // Winner
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]  = oshp[1] / ishp[1];  // Hinner
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]  = oshp[2];            // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]  = tshp[0];            // Wouter
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5]  = ishp[1];            // Houter
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 6]  = shapes.oshape[0];   // C
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable        = (int8_t)((1 << TNSVSIZE) - 1);
  }
}

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_upsample_params<B>::init_l1_output(
  const impl_spec_container_t<BD>&  p   // buffers and tensors in L1 memory [D][H][W][Grp][C]
                                ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  if (mode) {
    // fill the HLAPI offset parameters
    HLAPI.i.u.op.out.fm.fm_agu.ptr      = p.data.get_ptr();
    HLAPI.i.u.op.out.fm.fm_agu.buf.base = p.data.get_base();
    HLAPI.i.u.op.out.fm.fm_agu.buf.len  = p.data.get_size();
    HLAPI.i.u.op.out.fm.fm_agu.stride   = p.data.get_offset(2);                       // W8
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);        // C*msb/lsb
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)*TNSVSIZE+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // W
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(4)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // D
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(3)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(4)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // H
  } else {
    shape<3> tshp(ishp);
    tshp[0] = RDIV_UP(tshp[0], TNSVSIZE);
    // remove GRP axis
    tensor_t<ixpix_t, 4, BD> t0(p.data.reduce(1));
    // [D][H][W][C] --> [D][IH][H/IH][IW/8][W8][W/IW][C]
    // from outer to inner
    tensor_t<ixpix_t, 5, BD> t1(t0.split(2, tshp[1]));
    tensor_t<ixpix_t, 6, BD> t2(t1.split(1, tshp[0]));
    tensor_t<ixpix_t, 7, BD> t3(t2.split(1, TNSVSIZE));
    // transpose to [D][IH][H/IH][IW/8][W8][W/IW][C] --> [W8][C][IH][IW/8][D][H/IH][W/IW]
    tensor_t<ixpix_t, 7, BD> t4(t3.transpose({1, 4, 6, 3, 5, 0, 2}));
    // fill the HLAPI offset parameters
    HLAPI.i.u.op.out.fm.fm_agu.ptr      = t4.get_ptr();
    HLAPI.i.u.op.out.fm.fm_agu.buf.base = t4.get_base();
    HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t4.get_size();
    HLAPI.i.u.op.out.fm.fm_agu.stride   = t4.get_offset(6);                     // W8
    for (int i = 0; i < 6; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1 - i] = t4.get_offset_last(i);
    }
  }
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_upsample_params<B>::init_l1_input(
  const impl_spec_container_t<BD>&  p  // buffers and tensors in L1 memory [D][H][W][Grp][C]
                                ) {
  gtoa_params<B>::itens = p;
  if (mode) {
    // fill the HLAPI offset parameters
    HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
    HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
    HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
    HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                  // W8
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);   // C
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)*TNSVSIZE +
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);  // W
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(4) +
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE +
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);  // D
    HLAPI.i.u.op.primary.fm_agu.offsets[1]              = p.data.get_offset(2);   // W
    HLAPI.i.u.op.primary.fm_agu.offsets[0]              = p.data.get_offset(3);   // H 
  } else {
    // remove GRP axis
    tensor_t<ixpix_t, 4, BD> t0(p.data.reduce(1));
    // resize W to multiple of TNSVSIZE
    t0.resize(1, NRND_UP(t0.get_dim(1), TNSVSIZE));
    // [D][H][W][C] --> [D][H][W/8][W8][C] --> [W8][C][H][W/8][D]
    tensor_t<ixpix_t, 5, BD> t1(t0.split(1, t0.get_dim(1) / TNSVSIZE));
    tensor_t<ixpix_t, 5, BD> t2(t1.transpose({4, 2, 3, 0, 1}));
    // fill the HLAPI offset parameters
    HLAPI.i.u.op.primary.fm_agu.ptr      = t2.get_ptr();
    HLAPI.i.u.op.primary.fm_agu.buf.base = t2.get_base();
    HLAPI.i.u.op.primary.fm_agu.buf.len  = t2.get_size();
    HLAPI.i.u.op.primary.fm_agu.stride   = t2.get_offset(4);                    // W8
    for (int i = 0; i < 4; i++) {
      HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1 - i] = t2.get_offset_last(i);
    }
  }
}

template<template<typename> class B>
inline void gtoa_upsample_params<B>::get_shapes(
  gtoa_act_params_impl_shapes& s   // implementation specific minimum buffer sizes
                      ) {
  s = shapes;
}


#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_UPSAMPLE_INLINE_HPP_
