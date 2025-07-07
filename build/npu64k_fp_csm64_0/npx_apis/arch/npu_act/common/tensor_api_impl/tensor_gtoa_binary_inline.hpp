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
 * tensor_gtoa_binary_inline.hpp
 *
 * File defining a tensor level unary API base on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_BINARY_INLINE_HPP_           // [NOLINT]
#define TENSOR_GTOA_BINARY_INLINE_HPP_           // [NOLINT]
#include "./legacy/tensor_gtoa_binary_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi

// constructor
// floating point extensions
template<template<typename> class B>
gtoa_binary_params<B>::gtoa_binary_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     act_dtype_t                in0tp,         // type of primary input
                                     act_dtype_t                in1tp,         // type of secondary input
                                     act_dtype_t                outtp,         // type of output
                                     act_bin_op_t               opi            // binary operation to perform
                                     ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  cmax = noi;
  op = opi;
}

// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void gtoa_binary_params<B>::set_binary_params() {
  int fmi0dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmi1dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN1DBL_MASK) != 0 ? 2 : 1;
  int fmodbl  = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  bool ifm0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool ifm1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0;
  bool iac0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0;
  bool iac1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC1) != 0;
  bool ofm_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0;
  bool oac_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0;
  init_bin_prog(op, brdc_f);

  // iterators
  if (ofm_en) {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.oshape[0]/fmodbl;
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.oshape[2]
                                             *shapes.oshape[3]*shapes.oshape[4]/TNSVSIZE;
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.oshape[1];
  } else if (oac_en) {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.oshape[4];
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.oshape[1]*shapes.oshape[2]*shapes.oshape[3];
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.oshape[0];
  }
  // primary feature-map input
  if (ifm0_en) {
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]    = fmi0dbl;            // mlsb
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.ishape[3];  // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.ishape[2]/TNSVSIZE;  // W/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.ishape[4];  // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.ishape[0] / (fmi0dbl);  // C
  }
  // primary accumulator input
  if (iac0_en) {
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.ishape);
  }
  // secondary feature-map input
  if (ifm1_en) {
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.secondary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.secondary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1]    = fmi1dbl;            // mlsb
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.i1shape[3];  // H
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.i1shape[2]/TNSVSIZE;  // W/8
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.i1shape[4];  // D
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.i1shape[0] / (fmi1dbl);  // C
  }
  // secondary accumulator input
  if (iac1_en) {
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.secondary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.secondary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.secondary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.secondary.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.i1shape);
  }
  // feature-map output
  if (ofm_en) {
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = fmodbl;               // mlsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.oshape[3];    // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.oshape[2]/TNSVSIZE;   // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.oshape[4];    // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.oshape[0] / (fmodbl);   // C
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable        = (int8_t)((1 << TNSVSIZE)-1);
  }
  // accumulator output
  if (oac_en) {
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
void gtoa_binary_params<B>::init_l1_output(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t, 7, BD> t1(t0.split(3, p.data.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, BD> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

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

// initialize the primary input tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_binary_params<B>::init_l1_input0(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  tensor_t<ixpix_t,5,B> t = reinterpret_cast<const impl_spec_container_t<B>*>(&p)->data.broadcast(shapes.ishape);
  gtoa_params<B>::itens.data = t;
  t.resize(2, ROUND_UP(t.get_dim(2),TNSVSIZE)); // ensure is multiple of TNSVSIZE // FIX TO BE DONE FOR P10019796-66167
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, B> t0(t.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t, 7, B> t1(t0.split(3, t.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, B> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t2.get_base();
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

// initialize the secondary input tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_binary_params<B>::init_l1_input1(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  tensor_t<ixpix_t,5,B> t = reinterpret_cast<const impl_spec_container_t<B>*>(&p)->data.broadcast(shapes.i1shape);
  gtoa_params<B>::i1tens.data = t;
  t.resize(2, ROUND_UP(t.get_dim(2),TNSVSIZE)); // ensure is multiple of TNSVSIZE // FIX TO BE DONE FOR P10019796-66167
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, B> t0(t.split(0, HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t, 7, B> t1(t0.split(3, t.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, B> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.secondary.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.secondary.fm_agu.buf.base = t2.get_base();
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

template<template<typename> class B>
inline void gtoa_binary_params<B>::get_shapes(
  // structure with implementation specific minimum buffer sizes
                      gtoa_act_params_impl_shapes& s
                      ) {
  s = shapes;
  bool ifm0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool ifm1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0;
  if (brdc_f.in0_h) s.ishape[ifm0_en ? 3 : 1] = 1;
  if (brdc_f.in0_w) s.ishape[ifm0_en ? 2 : 2] = 1;
  if (brdc_f.in0_c) s.ishape[ifm0_en ? 0 : 4] = 1;
  if (brdc_f.in1_h) s.i1shape[ifm1_en ? 3 : 1] = 1;
  if (brdc_f.in1_w) s.i1shape[ifm1_en ? 2 : 2] = 1;
  if (brdc_f.in1_c) s.i1shape[ifm1_en ? 0 : 4] = 1;
}

template<template<typename> class B>
inline void gtoa_binary_params<B>::set_broadcast_flags(
                      broadcast_t bc_flags
                      ) {
  brdc_f = bc_flags;
}

#undef HLAPI
#endif    // TENSOR_GTOA_BINARY_INLINE_HPP_    // [NOLINT]
