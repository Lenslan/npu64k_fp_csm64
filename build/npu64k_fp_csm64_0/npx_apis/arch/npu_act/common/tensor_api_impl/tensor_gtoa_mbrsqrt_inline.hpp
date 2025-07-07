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
 * tensor_gtoa_mbrsqrt_inline.hpp
 *
 * File defining multiply channel wise broadcast rsqrt API base on the generic tensor operation API
 * Used for second parts of layernormalization
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_MBRSQRT_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_MBRSQRT_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// mbrsqrt operation for feature-map (8b/16b) input
// for add + rsqrt + mul
template <template <typename> class B>
gtoa_mbrsqrt_params<B>::gtoa_mbrsqrt_params(
            aoffset_t                  noi,           // number output channels (not vectors)
            const shape<3>&            ishpi0,        // input0 shape
            float                      epsilon,       // epsilon
            act_dtype_t                in0tp,         // type of primary input
            act_dtype_t                in1tp,         // type of secondary input
            act_dtype_t                outtp,         // type of output
            bool                       sati )         // Saturate output
  : gtoa_params<B>() {

  cmax = noi;

  HLAPI.i.u.op.bf = 0;
  HLAPI.i.u.op.io_en = 0;

  // TODO add int48
  bool i0dbl = (in0tp == dtype_int16) || (in0tp == dtype_fp16) || (in0tp == dtype_bf16);
  bool i1dbl = (in1tp == dtype_int16) || (in1tp == dtype_fp16) || (in1tp == dtype_bf16);
  bool odbl  = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  HLAPI.i.u.op.bf = (i0dbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                    (i1dbl ? 1 << ACT_BF_OP_IN1DBL_START : 0) |
                    (odbl ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                    (sati ? 1 << ACT_BF_OP_OUTSAT_START : 0);

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
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC0;
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
    case dtype_int32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1INT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1FP32_MASK;
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

  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(ishpi0[SPATIAL_W], TNSVSIZE);

  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // input feature-map in ixpix_t [D][H][W][1][C] format
    shapes.ishape = {(aoffset_t)(i0dbl ? 2 * c : c),
                    1,
                    (aoffset_t)(w * TNSVSIZE),
                    ishpi0[SPATIAL_H],
                    ishpi0[SPATIAL_D]};
  } else {
    // input accumulator in vyixacc_t [D][H][W/TNSVSIZE][C/ISIZE*dbl] format
    shapes.ishape = {(aoffset_t)c,
                    (aoffset_t)w,
                    ishpi0[SPATIAL_H],
                    ishpi0[SPATIAL_D],
                    1};
  }

  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0) {
    // input feature-map in ixpix_t [D][H][W][1][dbl] format
    shapes.i1shape = {(aoffset_t)(i1dbl ? 2 : 1),
                    1,
                    (aoffset_t)(w * TNSVSIZE),
                    ishpi0[SPATIAL_H],
                    ishpi0[SPATIAL_D]};
  } else {
    // input accumulator in vyixacc_t [D][H][W/TNSVSIZE][C/ISIZE*dbl] format
    shapes.i1shape = {(aoffset_t)1,
                    (aoffset_t)w,
                    ishpi0[SPATIAL_H],
                    ishpi0[SPATIAL_D],
                    1};
  }
 
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // output feature-map in ixpix_t [D][H][W][1][C] format
    shapes.oshape = {(aoffset_t)(odbl ? 2 * c : c),
                    1,
                    (aoffset_t)(w * TNSVSIZE),
                    ishpi0[SPATIAL_H],
                    ishpi0[SPATIAL_D]};
  } else {
    // output accumulator in vyixacc_t [D][H][W/TNSVSIZE][C/ISIZE] format
    shapes.oshape = {(aoffset_t)(c),
                    (aoffset_t)w,
                    ishpi0[SPATIAL_H],
                    ishpi0[SPATIAL_D],
                    1};
  }

  gtoa_mbrsqrt_params<B>::spatial_max = w * ishpi0[SPATIAL_H] * ishpi0[SPATIAL_D];
  // parameter dimension, since c is the inner most loop, here we use larger params buffer 
  // because no circular parameter buffer for parameters.
  // Since we do not want to do rsqrt in inner most loop, we move it up. 
  shapes.pshape = {(aoffset_t)(4*c*spatial_max*MBRSQRT_PER_CHAN)};

  HLAPI.i.u.op.bnum      = 4*c*spatial_max*MBRSQRT_PER_CHAN;

  set_mbrsqrt_params();
  init_add_rsqrt_scale(HLAPI, epsilon, odbl); //bias has same size of output
}

// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void gtoa_mbrsqrt_params<B>::set_mbrsqrt_params() {
  int fmi0dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmi1dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN1DBL_MASK) != 0 ? 2 : 1;
  int fmodbl  = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  bool ifm0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool ifm1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0;
  bool iac0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0;
  bool iac1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC1) != 0;
  bool ofm_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0;
  bool oac_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0;

    //  Channel/ISIZE
  int i_c = shapes.ishape[0]/fmi0dbl;

  // H*W*D/TNSVSIZE
  int i_spatial;
  if (ifm0_en) {
    i_spatial = RDIV_UP(shapes.ishape[2], TNSVSIZE) * shapes.ishape[3] * shapes.ishape[4];
  } else {
    i_spatial = shapes.ishape[1] * shapes.ishape[2] * shapes.ishape[3];
  }

  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = i_c;            // inner channel loop
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = i_spatial;      // middle spatial loop
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = 1;              // outer

  // primary feature-map input
  if (ifm0_en) {
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = shapes.ishape[0];                 // C
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = 1;
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = RDIV_UP(shapes.ishape[2], TNSVSIZE); // w/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.ishape[3];                 // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.ishape[4];                 // D
  } else if (iac0_en) {  // primary accumulator input
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
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1] = shapes.i1shape[0];                 // C
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 2] = 1;
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 3] = RDIV_UP(shapes.i1shape[2], TNSVSIZE); // w/8
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.i1shape[3];                 // H
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.i1shape[4];                 // D
  } else if (iac1_en) {  // secondary accumulator input
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
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1] = shapes.oshape[0];                 // C
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = 1;
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = RDIV_UP(shapes.oshape[2], TNSVSIZE); // w/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.oshape[3];                 // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.oshape[4];                 // D
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable        = (int8_t)((1 << TNSVSIZE)-1);
  } else if (oac_en) {   // accumulator output
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.oshape);
  }
}

// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void gtoa_mbrsqrt_params<B>::get_shapes(
        gtoa_act_params_impl_shapes&   s            // structure with implementation specific minimum buffer sizes
        ){
    s = shapes;
}

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_mbrsqrt_params<B>::init_l1_output(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  HLAPI.i.u.op.out.fm.fm_agu.ptr = p.data.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len = p.data.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride = p.data.get_offset(2); // W
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset(0); // C
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset(1); // 1
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // W
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // H
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 5] = p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]) * p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // D
}

// initialize the primary input tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_mbrsqrt_params<B>::init_l1_input0(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  HLAPI.i.u.op.primary.fm_agu.ptr = p.data.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len = p.data.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride = p.data.get_offset(2); // W
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset(0); // C
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset(1); // 1
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // W
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 4] = p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // H
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 5] = p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]) * p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // D
}

// initialize the secondary input tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_mbrsqrt_params<B>::init_l1_input1(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  HLAPI.i.u.op.secondary.fm_agu.ptr = localptr_t<ixpix_t>(p.data.get_ptr());
  HLAPI.i.u.op.secondary.fm_agu.buf.base = localptr_t<ixpix_t>(p.data.get_base());
  HLAPI.i.u.op.secondary.fm_agu.buf.len = p.data.get_size();
  HLAPI.i.u.op.secondary.fm_agu.stride = p.data.get_offset(2);
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset(0); // C
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset(1); // 1
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // W
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 4] = p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1]) *  p.data.get_offset(0); // H
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 5] = p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 4]) * p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0); // D
}

template<template<typename> class B>
void gtoa_mbrsqrt_params<B>::param_enc(
                                const tensor_t<fp_e8m23_t,1,xbuffer_t>&   scale,        // per channel post scale [Cout]
                                const tensor_t<int8_t,1,xbuffer_t>&       bias,         // per channel bias [Cout]
                                gtoa_params_impl_pchan<xbuffer_t>&        obuf          // output encoded parameters
                                ) {

  assert(  (HLAPI.i.u.op.bf & 1 << ACT_BF_OP_OUTDBL_START) == 0 && "bias dtype should be same as output");

  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int16_t*  bparsh  = (int16_t*)bpars;              // pointer to start of BRB values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_mbrsqrt_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_mbrsqrt_params<B>::cmax) {
        auto bvalue = ((uint32_t)(prescale_t(1.0f).data)) | (((int32_t)bias.read({j}))<<8); // store int8 bias in brh0
        auto svalue = scale.read({j}).data;
        for (int s = 0; s < gtoa_mbrsqrt_params<B>::spatial_max; s++) {
          auto idx = (s*ci + c) * MBRSQRT_PER_CHAN;
          bparsh[idx*ISIZE*2+i] = bvalue;                               // BRH0 bias
          bparsw[(idx + 1)*ISIZE+i] = svalue;                           // BRW1 scale
        }
        j++;
      }
    }
  }
}

template<template<typename> class B>
void gtoa_mbrsqrt_params<B>::param_enc(
                                const tensor_t<fp_e8m23_t,1,xbuffer_t>&   scale,        // per channel post scale [Cout]
                                const tensor_t<int16_t,1,xbuffer_t>&      bias,         // per channel bias [Cout]
                                gtoa_params_impl_pchan<xbuffer_t>&        obuf          // output encoded parameters
                                ) {

  assert(  (HLAPI.i.u.op.bf & 1 << ACT_BF_OP_OUTDBL_START) != 0 && "bias dtype should be same as output");

  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int16_t*  bparsh  = (int16_t*)bpars;              // pointer to start of BRB values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_mbrsqrt_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_mbrsqrt_params<B>::cmax) {
        auto bvalue = bias.read({j});
        auto svalue = scale.read({j}).data;
        for (int s = 0; s < gtoa_mbrsqrt_params<B>::spatial_max; s++) {
          auto idx = (s*ci + c) * MBRSQRT_PER_CHAN;
          bparsh[idx*ISIZE*2+i] = bvalue;                         // BRC0 bias
          bparsw[(idx + 1)*ISIZE+i] = svalue;                           // BRW1 scale
        }
        j++;
      }
    }
  }
}

template<template<typename> class B>
void gtoa_mbrsqrt_params<B>::set_tile_channel(aoffset_t noc) {
  gtoa_mbrsqrt_params<B>::cmax = noc;
}

#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_MBRSQRT_INLINE_HPP_
