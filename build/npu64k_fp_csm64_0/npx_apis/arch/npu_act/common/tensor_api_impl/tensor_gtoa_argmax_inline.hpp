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
 * tensor_gtoa_argmax_inline.hpp
 *
 * File defining a tensor level ARGMAX API based on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_ARGMAX_INLINE_HPP_  // [NOLINT]
#define TENSOR_GTOA_ARGMAX_INLINE_HPP_  // [NOLINT]

#define HLAPI gtoa_params<B>::hlapi

// Generic constructor for ARGMAX reduction over spatial
template<template<typename> class B>
gtoa_argmax_params<B>::gtoa_argmax_params(
                       aoffset_t                noi,          // number input channels (not vectors)
                       const shape<3>&          ishpi,        // input shape, indexed by spatial_axis_t
                       act_dtype_t              fmtpi         // feature-map data type
                       ) {
  bool fmdbli = fmtpi != dtype_int8;
  fmtp = fmtpi;

  // divide and round up channels by ISIZE
  int ich = RDIV_UP(noi, ISIZE);
  // number of width iterations
  int iw  = RDIV_UP(ishpi[SPATIAL_W], TNSVSIZE);
  // set shapes
  shapes.ishape = {(aoffset_t)(fmdbli ? 2 * ich : ich), 1, ishpi[SPATIAL_W],
                   ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  shapes.oshape = {(aoffset_t)(2 * ich), 1, 1, ishpi[SPATIAL_H], ishpi[SPATIAL_D]};

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
  // pad with min value
  HLAPI.i.u.op.bf  |= ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PMIN_MASK;
  HLAPI.i.u.op.bf  |= ACT_BF_OP_OUTDBL_MASK;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1]   = iw;              // inner loop over the kernel
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2]   = ishpi[SPATIAL_H] * ishpi[SPATIAL_D];
  // middle loop spatial output
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3]   = ich;             // outer loop channel
  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]   = fmdbli ? 2 : 1;          // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]   = iw;                      // width
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]   = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]   = ishpi[SPATIAL_D];        // depth
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5]   = ich;                     // channel
  // input padding settings (only pad columns)
  HLAPI.i.u.op.pad_stride                          = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = (1 - iw) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - iw) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = (1 - iw) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 0;
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS - 4; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]    = 2;                      // output is 16b
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]    = ishpi[SPATIAL_H];       // output height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]    = ishpi[SPATIAL_D];       // output depth
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]    = ich;                    // channel vectors
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback one column only
  HLAPI.i.u.op.out.fm.enable        = 1;
  // set padding window
  HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
  HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
  HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W] - 1;
  HLAPI.i.u.op.padlim[SPATIAL_H] = (aoffset_t)0x7fff;
  // initialize microcode
  init_argmax(HLAPI, TNSVSIZE==2);
}

template<template<typename> class B>
gtoa_argmax_params<B>::gtoa_argmax_params(
                                       // number output channels (not vectors)
                                       aoffset_t                noi,
                                       // input shape, indexed by spatial_axis_t
                                       const shape<3>&          ishpi,
                                       // 16b input/output feature-map
                                       bool                     fmdbli
                                       ) {
  // copy parameters
  fmtp = fmdbli ? dtype_int16 : dtype_int8;
  // divide and round up channels by ISIZE
  int ich = RDIV_UP(noi, ISIZE);
  // number of width iterations
  int iw  = RDIV_UP(ishpi[SPATIAL_W], TNSVSIZE);
  // set shapes
  shapes.ishape = {(aoffset_t)(fmdbli ? 2 * ich : ich), 1, ishpi[SPATIAL_W],
                   ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  shapes.oshape = {(aoffset_t)(2 * ich), 1, 1, ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf            = 0;       // function, not LUT init
  // input and output is feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  // input/output attributes
  HLAPI.i.u.op.bf  = ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PMIN_MASK;
  // enable input padding, pad to minint
  // double or single width inputs, output always double
  HLAPI.i.u.op.bf |= fmdbli ? ACT_BF_OP_IN0DBL_MASK | ACT_BF_OP_OUTDBL_MASK : ACT_BF_OP_OUTDBL_MASK;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1]   = iw;              // inner loop over the kernel
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2]   = ishpi[SPATIAL_H] * ishpi[SPATIAL_D];
                                                              // middle loop spatial output
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3]   = ich;             // outer loop channel
  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]   = fmdbli ? 2 : 1;           // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]   = iw;                      // width
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]   = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]   = ishpi[SPATIAL_D];        // depth
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5]   = ich;                     // channel
  // input padding settings (only pad columns)
  HLAPI.i.u.op.pad_stride                          = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = (1 - iw) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - iw) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = (1 - iw) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 0;
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS - 4; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]    = 2;                      // output is 16b
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]    = ishpi[SPATIAL_H];       // output height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]    = ishpi[SPATIAL_D];       // output depth
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]    = ich;                    // channel vectors
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback one column only
  HLAPI.i.u.op.out.fm.enable        = 1;
  // set padding window
  HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
  HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
  HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W] - 1;
  HLAPI.i.u.op.padlim[SPATIAL_H] = (aoffset_t)0x7fff;
  // initialize microcode
  init_argmax(HLAPI, TNSVSIZE==2);
}

template<template<typename> class B>
void gtoa_argmax_params<B>::set_pack_mode(
                                      pack_mode_t pmi
                                      ) {
#if NPU_VER_IS_VIC2_GA
  int pinc;
  switch (pmi) {
  case pack_mode_i8_e:   HLAPI.i.u.op.bf |= ACT_BF_OP_PADV2I8_MASK;  pinc = 2; break;
  case pack_mode_i4_e:   HLAPI.i.u.op.bf |= ACT_BF_OP_PADV4I4_MASK;  pinc = 4; break;
  default:               HLAPI.i.u.op.bf |= ACT_BF_OP_PADI16_MASK;   pinc = 1; break;
  }
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.pad_offs[i][SPATIAL_W] = HLAPI.i.u.op.pad_offs[i][SPATIAL_W] * pinc;
  }
#else
  assert(0);
#endif
}

//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_argmax_params<B>::init_l1_output(
                                        // structure with allocated buffers
                                        // and tensors in L1 memory
                                        const impl_spec_container_t<BD>&    p
                                        ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/mlsb][mlsb]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = 1;     // unit stride, not used, only 1 output
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = t0.get_offset(0);         // msb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = t0.get_offset(4)+
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OH
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = t0.get_offset(5) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(4) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OD
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = t0.get_offset(1) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]) * t0.get_offset(5) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(4) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OC
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_argmax_params<B>::init_l1_input(
                                       // structure with allocated buffers and tensors in L1 memory
                                       const impl_spec_container_t<BD>&    p
                                       ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/mlsb][mlsb]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5]));
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t0.get_size();
  // offset to spatial element in W dimension
  HLAPI.i.u.op.primary.fm_agu.stride   = t0.get_offset(3);
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = t0.get_offset(0);     // msb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] = t0.get_offset(3) * TNSVSIZE +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OW
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] = t0.get_offset(4) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(3) * TNSVSIZE +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 4] = t0.get_offset(5) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * t0.get_offset(4) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(3) * TNSVSIZE +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OD
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 5] = t0.get_offset(1) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]) * t0.get_offset(5) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * t0.get_offset(4) +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t0.get_offset(3) * TNSVSIZE +
    (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t0.get_offset(0);    // OC
}


template<template<typename> class B>
inline void gtoa_argmax_params<B>::get_shapes(
                                // structure with implementation specific minimum buffer sizes
                                gtoa_act_params_impl_shapes& s
                                           ) {
  s = shapes;
}

#undef HLAPI
#endif  // TENSOR_GTOA_ARGMAX_INLINE_HPP_   // [NOLINT]
