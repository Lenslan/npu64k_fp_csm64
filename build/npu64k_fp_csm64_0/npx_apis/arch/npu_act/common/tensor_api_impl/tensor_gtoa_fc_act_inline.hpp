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
 * tensor_gtoa_fc_act_inline.hpp
 *
 * File defining a tensor level activation function API following FC layer base on the generic tensor operation API
 *
 */

//
// Constructors
//
#include "./legacy/tensor_gtoa_fc_act_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi
template<template<typename> class B>
gtoa_fc_act_params<B>::gtoa_fc_act_params(
                                 aoffset_t                  noi,           // number output channels (not vectors)
                                 act_dtype_t                intp,          // type of primary input
                                 act_dtype_t                outtp,         // type of output
                                 bool                       inastri        // if true then input stream
                                 ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  bool odbl = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  HLAPI.i.u.op.bf = (odbl ? 1 << ACT_BF_OP_OUTDBL_START : 0);
  // update mask and floating mode field based on input/output type
  switch (intp) {
    case dtype_int32:
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
      fp16scl = (intp == dtype_fp16);
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTSAT_MASK;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
      fp16scl = (intp == dtype_fp16);
      break;
    case dtype_fp16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTFP16_MASK;
      fp16scl = true;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTBF16_MASK;
      fp16scl = false;
      break;
    default: assert(0 && "unsupported output datatype!");
  }
  cmax = noi;
  // input number in vyixacc_t
  int c_in = RDIV_UP(noi, ISIZE*TNSVSIZE);
  // output number in ixpix_t
  int c_out = RDIV_UP(noi, ISIZE);
  // output number padded to multiples of TNSVSIZE
  int c_out_up = ROUND_UP(c_out, TNSVSIZE);
  // input accumulator in vyixacc_t [C][1][1][1][1] format
  shapes.ishape = { 1, 1, 1, 1, (aoffset_t)c_in };
  // output feature-map in ixpix_t [1][1][1][C] format
  shapes.oshape = { (aoffset_t)(odbl  ? 2*c_out_up : c_out_up), 1, 1, 1, 1};
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c_out_up) };
  // maxpool overlap buffer set by zero as a  [No_Pool]
  shapes.mpshape = {(aoffset_t)(0)};
  // default onn and pooling
  gtoa_params<B>::onn = 1;
}

// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void gtoa_fc_act_params<B>::set_impl_params(
                                      const gtoa_act_params_impl_spec& p // structure with implementation specific parameters
                                      ) {
  gtoa_params<B>::onn = p.onn;
  set_shapes();
}

template<template<typename> class B>
void gtoa_fc_act_params<B>::get_impl_params(
                                      gtoa_act_params_impl_spec& p       // return structure with implementation specific parameters
                                      ) {
  p.onn = gtoa_params<B>::onn;
}

template<template<typename> class B>
void gtoa_fc_act_params<B>::set_shapes() {
  int fmdbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  init_prog();

  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = 1;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.ishape[4];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = TNSVSIZE;
  // accumulator input AGU
  for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
    HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
  HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-1] = 1;       // ONN|mlsb
  HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-2] = 1; // H
  HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-3] = 1; // W
  HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-4] = shapes.ishape[4]; // D*C
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = fmdbl;       // ONN|mlsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = 1;  // H
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = 1;  // W
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = 1;  // D
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.oshape[0] / fmdbl; // C
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf = 0;  // disable maxpooling
  // writeback one line
  HLAPI.i.u.op.out.fm.enable        = 0x01;
}

// initialize the output tensor
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_fc_act_params<B>::init_l1(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                              ) {
  gtoa_params<B>::tens = p;
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t,6,B> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]));
  // transpose to [Grp][C][D][W][H][ONN|msb|lsb]
  tensor_t<ixpix_t,6,B> t1(t0.transpose({0,4,3,5,1,2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = localptr_t<ixpix_t>(t1.get_ptr());
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = localptr_t<ixpix_t>(t1.get_base());
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t1.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = 1;
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t1.get_offset(0);     // ONN
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t1.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);    // H
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = t1.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t1.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);    // W
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = t1.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t1.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t1.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);    // D
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-5] = t1.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4])*t1.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t1.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t1.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);    // C*GRP
}


template<template<typename> class B>
inline void gtoa_fc_act_params<B>::get_shapes(
                      gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                      ) {
  s = shapes;
}

template<template<typename> class B>
void gtoa_fc_act_params<B>::set_tile_channel(aoffset_t noc) {
  gtoa_fc_act_params<B>::cmax = noc;
}

#undef HLAPI
