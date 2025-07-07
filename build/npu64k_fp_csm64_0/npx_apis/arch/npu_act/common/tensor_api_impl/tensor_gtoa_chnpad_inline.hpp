/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2023 Synopsys, Inc.                              **/
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

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CHNPAD_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CHNPAD_INLINE_HPP_

/*
 * tensor_gtoa_chnpad_inline.hpp
 *
 * File defining a tensor level binary API base on the generic tensor operation API
 *
 */

#define HLAPI gtoa_params<B>::hlapi

// constructors
// floating point extensions
template<template<typename> class B>
gtoa_chnpad_params<B>::gtoa_chnpad_params(
    aoffset_t       noi,        // number output channels (not vectors)
    const shape<3>& ishpi,      // input shape
    // type of primary input
    act_dtype_t                intp,
    // type of output
    act_dtype_t                outtp
    ) : gtoa_params<B>() {
  assert(noi <= ISIZE && "noi must less than ISIZE!");
  cmax = noi;
  bool i0dbl = (intp == dtype_int16) || (intp == dtype_fp16) || (intp == dtype_bf16);
  bool odbl  = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  HLAPI.i.u.op.bf = (i0dbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                    (odbl  ? 1 << ACT_BF_OP_OUTDBL_START : 0);

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
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0FP32_MASK;
      break;
    default: assert(0 && "unsupported input datatype!");
  }
  switch (outtp) {
    case dtype_int8:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
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
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (ishpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;

  // iter number of in0 is same as the full tensor
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // input0 feature-map in ixpix_t [D][H][W][C] format
    shapes.ishape = { (aoffset_t)(i0dbl  ? 2*c : c),
                      (aoffset_t)1,
                      (aoffset_t)(w*TNSVSIZE),
                      ishpi[SPATIAL_H],
                      ishpi[SPATIAL_D] };
  } else {
    // input0 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
    shapes.ishape = { (aoffset_t)1, 
                      ishpi[SPATIAL_H],
                      (aoffset_t)w,
                      ishpi[SPATIAL_D],
                      (aoffset_t)c };
  }

  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // output feature-map in ixpix_t [D][H][W][C] format
    shapes.oshape = { (aoffset_t)(odbl  ? 2*c : c), (aoffset_t)1,
                      (aoffset_t)(w*TNSVSIZE), ishpi[SPATIAL_H], ishpi[SPATIAL_D] };
  } else {
    // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
    shapes.oshape = { (aoffset_t)1, ishpi[SPATIAL_H], (aoffset_t)w, ishpi[SPATIAL_D], (aoffset_t)c };
  }
  // No paramters
  shapes.pshape = {0};
  HLAPI.i.u.op.bnum      = 0;

  set_chanpad_params();

  int ch_pad = (noi % ISIZE == 0) ? noi : noi % ISIZE;
  // out = c > noi ? 0 : input
  init_chan_pad(HLAPI, ch_pad);
}

// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void  gtoa_chnpad_params<B>::set_chanpad_params() {
  int fmi0dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmi1dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN1DBL_MASK) != 0 ? 2 : 1;
  int fmodbl  = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  bool ifm0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool ifm1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0;
  bool iac0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0;
  bool iac1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC1) != 0;
  bool ofm_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0;
  bool oac_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0;

  // iterators
 
  if (ofm_en) {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.oshape[2]
                                        *shapes.oshape[3]*shapes.oshape[4]/TNSVSIZE; // inner
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.oshape[0]/fmodbl;
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.oshape[1];
  } else if (oac_en) {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.oshape[1]*shapes.oshape[2]*shapes.oshape[3];
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.oshape[4];
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
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.ishape[2]/TNSVSIZE;   // W/8
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
void  gtoa_chnpad_params<B>::init_l1_output(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]

  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, p.data.get_dim(0)/HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]));

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
void  gtoa_chnpad_params<B>::init_l1_input(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  auto &t = reinterpret_cast<const impl_spec_container_t<B>*>(&p)->data;
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, B> t0(t.split(0, aoffset_t(t.get_dim(0)/HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])));

  //[D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 7, B> t1(t0.split(3, t0.get_dim(3)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, B> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = t2.get_offset(0); // W8 (don't use 0 here in case of w-bcast, use 1)

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
inline void  gtoa_chnpad_params<B>::get_shapes(
  // structure with implementation specific minimum buffer sizes
                      gtoa_act_params_impl_shapes& s
                      ) {
  s = shapes;
}

#undef HLAPI
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CHNPAD_INLINE_HPP_
