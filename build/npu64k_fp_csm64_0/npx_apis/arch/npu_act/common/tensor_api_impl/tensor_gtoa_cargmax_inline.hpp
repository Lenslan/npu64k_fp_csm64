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
 * tensor_gtoa_cargmax_inline.hpp
 *
 * File defining a tensor level ARGMAX API based on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_CARGMAX_INLINE_HPP_  // [NOLINT]
#define TENSOR_GTOA_CARGMAX_INLINE_HPP_  // [NOLINT]

#define HLAPI gtoa_params<B>::hlapi

// Generic constructor for ARGMAX reduction over spatial or channel
template<template<typename> class B>
gtoa_cargmax0_params<B>::gtoa_cargmax0_params(
                       aoffset_t                noi,          // number input channels, multiple of ISIZE (not vectors)
                       const shape<3>&          ishpi,        // input shape, indexed by spatial_axis_t
                       act_dtype_t              fmtpi         // feature-map data type
                       ) {
  assert(((noi % ISIZE) == 0) && "cargmax requires argument noi%ISIZE==0");
  bool fmdbli = fmtpi != dtype_int8;
  fmtp = fmtpi;

  // divide and round up channels by ISIZE
  aoffset_t ich = RDIV_UP(noi, ISIZE);
  // number of width iterations
  aoffset_t iw  = RDIV_UP(ishpi[SPATIAL_W], TNSVSIZE);
  // set shapes, input VM, output VM
  shapes.ishape = {(aoffset_t)(fmdbli ? 2 * ich : ich), 1, ishpi[SPATIAL_W],
                   ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  shapes.oshape = {4, 1, (aoffset_t)(iw * TNSVSIZE),
                   ishpi[SPATIAL_H], ishpi[SPATIAL_D]};

  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  switch (fmtp) {
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_IN0FMODE_START;
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_IN0FMODE_START;
    break;
  default:
    assert(0 && "unsupported input type");
  }

  // output is 16b feature-map
  HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf |= ACT_BF_OP_OUTDBL_MASK;
  HLAPI.i.u.op.bf |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;

  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1]   = ich;              // inner loop over the channels
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2]   = iw * ishpi[SPATIAL_H] * ishpi[SPATIAL_D];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3]   = 1;

  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]   = fmdbli ? 2 : 1;          // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]   = ich;                     // channel
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]   = iw;                      // width
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]   = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5]   = ishpi[SPATIAL_D];        // depth

  // output to VM   
  for (int i = 0; i < ACT_FM_LOOPS - 4; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]    = 4;                                    // output is 16b
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]    = iw;                                   // width
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]    = ishpi[SPATIAL_H];                     // height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]    = ishpi[SPATIAL_D];                     // depth

  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback all columns
  HLAPI.i.u.op.out.fm.enable        = static_cast<int8_t>((1 << TNSVSIZE) - 1);

  // initialize microcode
  init_argmax_c0(HLAPI);
}
template<template<typename> class B>
gtoa_cargmax1_params<B>::gtoa_cargmax1_params(
                       const gtoa_cargmax0_params<B>& p0         // constructed by 0 object
                       ) {
  assert(((p0.shapes.oshape[2] % TNSVSIZE) == 0) && "cargmax1 input width is multiple of VSIZE");
  // sizes from c0
  aoffset_t no = p0.shapes.oshape[0];
  aoffset_t iw = p0.shapes.oshape[2]/TNSVSIZE;
  aoffset_t ih = p0.shapes.oshape[3];
  aoffset_t id = p0.shapes.oshape[4];

  // shapes
  shapes.ishape = {4, 1, (aoffset_t)(iw*TNSVSIZE), ih, id};
  shapes.oshape = {2, 1, (aoffset_t)(iw*TNSVSIZE), ih, id};

  // initialize HLAPI
  HLAPI.i.bf            = 0;       // function, not LUT init
  // input from VM and output to VM
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0DBL_MASK;
  HLAPI.i.u.op.bf |= ACT_BF_OP_OUTDBL_MASK;
  HLAPI.i.u.op.bf |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
  HLAPI.i.u.op.bf |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1]   = iw*ih*id;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2]   = 1;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3]   = 1;
  
  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]   = 1;                       // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]   = no;                      // channel
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]   = iw;                      // width
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]   = ih;                      // height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5]   = id;                      // depth
  
  // feature-map output AGU to VM
  for (int i = 0; i < ACT_FM_LOOPS - 4; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]    = 2;                      // output is 16b
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]    = iw;                     // width
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]    = ih;                     // height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]    = id;                     // depth

  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback one column only
  HLAPI.i.u.op.out.fm.enable        = (1<<TNSVSIZE)-1;

  // initialize microcode
  init_argmax_c1(HLAPI);
}

//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_cargmax0_params<B>::init_l1_input(
                                       // structure with allocated buffers and tensors in L1 memory
                                       const impl_spec_container_t<BD>&    p
                                       ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  tensor_t<ixpix_t, 5, BD> t0(p.data);
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t0.get_size();
  // offset to spatial element in W dimension
  HLAPI.i.u.op.primary.fm_agu.stride   = t0.get_offset(2);
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = t0.get_offset(0);         // msb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] = t0.get_offset(0);         // OC
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] = t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(0) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OW
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 4] = t0.get_offset(3) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(0) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 5] = t0.get_offset(4) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]) * t0.get_offset(3) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(0) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OD
}
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_cargmax1_params<B>::init_l1_input(
                                       // structure with allocated buffers and tensors in L1 memory
                                       const impl_spec_container_t<BD>&    p
                                       ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  tensor_t<ixpix_t, 5, BD> t0(p.data);
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t0.get_size();
  // offset to spatial element in W dimension
  HLAPI.i.u.op.primary.fm_agu.stride   = t0.get_offset(2);
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = t0.get_offset(0);         // msb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] = t0.get_offset(0);         // OC
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] = t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(0) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OW
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 4] = t0.get_offset(3) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(0) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 5] = t0.get_offset(4) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]) * t0.get_offset(3) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(0) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OD
}
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_cargmax0_params<B>::init_l1_output(
                                        // structure with allocated buffers
                                        // and tensors in L1 memory
                                        const impl_spec_container_t<BD>&    p
                                        ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  tensor_t<ixpix_t, 5, BD> t0(p.data);
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t0.get_size();
  // offset to spatial element in W dimension
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t0.get_offset(2);
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = t0.get_offset(0);         // msb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OW
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = t0.get_offset(3) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OH
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = t0.get_offset(4) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]) * t0.get_offset(3) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OD
}
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_cargmax1_params<B>::init_l1_output(
                                        // structure with allocated buffers
                                        // and tensors in L1 memory
                                        const impl_spec_container_t<BD>&    p
                                        ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  tensor_t<ixpix_t, 5, BD> t0(p.data);
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t0.get_size();
  // offset to spatial element in W dimension
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t0.get_offset(2);
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = t0.get_offset(0);         // msb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OW
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = t0.get_offset(3) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OH
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = t0.get_offset(4) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]) * t0.get_offset(3) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(2) * TNSVSIZE +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OD
}


template<template<typename> class B>
inline void gtoa_cargmax0_params<B>::get_shapes(
                                // structure with implementation specific minimum buffer sizes
                                gtoa_act_params_impl_shapes& s
                                           ) {
  s = shapes;
}

template<template<typename> class B>
inline void gtoa_cargmax1_params<B>::get_shapes(
                                // structure with implementation specific minimum buffer sizes
                                gtoa_act_params_impl_shapes& s
                                           ) {
  s = shapes;
}

#undef HLAPI
#endif  // TENSOR_GTOA_CARGMAX_INLINE_HPP_   // [NOLINT]
