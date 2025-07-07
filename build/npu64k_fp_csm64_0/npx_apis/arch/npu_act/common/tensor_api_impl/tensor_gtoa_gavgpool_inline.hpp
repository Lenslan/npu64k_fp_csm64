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
 * tensor_gtoa_gavgpool_inline.hpp
 *
 * File defining a tensor level global average pool API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GAVGPOOL_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GAVGPOOL_INLINE_HPP_
#include "./legacy/tensor_gtoa_gavgpool_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi

// constructor
template <template <typename> class B>
gtoa_gavgpool_params<B>::gtoa_gavgpool_params(
     aoffset_t                  noi,           // number output channels (not vectors)
     const shape<3>&            ishpi,         // input shape
     const shape<3>&            padlim,        // padding boundaries
     int                        numdim,        // number of inner spatial dimensions to be pooled
     act_dtype_t                itpi,          // input feature-map type: int8, int16, fp16, bf16
     act_dtype_t                otpi) {        // output feature-map type: int8, int16, fp16, bf16
  assert(numdim >= 1 && "average pool requires at least one reduction dimension");
  cmax = noi;
  ishp = ishpi;
  oshp = ishpi;
  itp  = itpi;
  otp  = otpi;
  mode = true;
  // reduce axes while computing number of elements to scale
  float scale(1.0f);
  for (int i = 0; i < numdim; i++) {
    oshp[i] = 1;
    scale *= ishpi[i];
  }
  // reciprocal
  scale = 1.0f/scale;
  // attributes
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  bool idbl = (itp == dtype_int16) || (itp == dtype_fp16) || (itp == dtype_bf16);
  bool odbl = (otp == dtype_int16) || (otp == dtype_fp16) || (otp == dtype_bf16);
  HLAPI.i.u.op.bf = (idbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                    (odbl ? 1 << ACT_BF_OP_OUTDBL_START : 0);
  // enable input zero padding
  HLAPI.i.u.op.bf  |= ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PZERO_MASK;
  // update mask and floating mode field based on input/output type
  switch (itp) {
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
  default: assert(0 && "unsupported input datatype!");
  }
  switch (otp) {
  case dtype_int8:
    HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTSAT_MASK;
    HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
    break;
  case dtype_int16:
    HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTSAT_MASK;
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
  default: assert(0 && "unsupported output datatype!");
  }
  // shapes
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(ishp[SPATIAL_W], TNSVSIZE);
  shapes.ishape = {(aoffset_t)(idbl ? 2 * c : c),
                   1,
                   ishp[SPATIAL_W],
                   ishp[SPATIAL_H],
                   ishp[SPATIAL_D]};
  shapes.oshape = {(aoffset_t)(odbl ? 2 * c : c),
                   1,
                   1,
                   (numdim >= 2) ? (aoffset_t)1 : ishp[SPATIAL_H],
                   (numdim >= 3) ? (aoffset_t)1 : ishp[SPATIAL_D]};
  // ucode iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = 1;
  switch (numdim) {
  case 1:
    // reduce W
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = c*
      ishp[SPATIAL_H]*
      ishp[SPATIAL_D];                                          // DHC
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = w;                 // W
    break;
  case 2:
    // reduce HW
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = c*
      ishp[SPATIAL_D];                                         // DC
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = ishp[SPATIAL_H]*
      w;                                                       // HW
    break;
  default:
    // reduce DHW
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = c;                // C
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = ishp[SPATIAL_D]*
      ishp[SPATIAL_H]*
      w;                                                       // DHW
  }
  // input feature-map iterator
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = idbl ? 2 : 1;     // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = w;                // W/8
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = ishp[SPATIAL_H];  // H
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4] = ishp[SPATIAL_D];  // D
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5] = c;   // C
  // output feature-map iterator
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1] = odbl ? 2 : 1;      // mlsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = shapes.oshape[3];  // H
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = shapes.oshape[4];  // D
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = c;                 // C
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf = 0;  // disable maxpooling
  // writeback all lines
  HLAPI.i.u.op.out.fm.enable = 1;  // only lane only
  // padding
  HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
  HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
  HLAPI.i.u.op.padlim[SPATIAL_W] = padlim[SPATIAL_W];
  HLAPI.i.u.op.padlim[SPATIAL_H] = padlim[SPATIAL_H];
  HLAPI.i.u.op.pad_stride                            = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = -(TNSVSIZE * (w - 1));
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = -(TNSVSIZE * (w - 1));
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = -(TNSVSIZE * (w - 1));
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - ishp[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - ishp[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
  // micro-code
  init_gavgpool_v2(HLAPI, scale);
}

template<template<typename> class B>
void gtoa_gavgpool_params<B>::set_pack_mode(
                                      pack_mode_t pmi
                                      ) {
  int pinc;
  switch (pmi) {
  case pack_mode_i8_e:   HLAPI.i.u.op.bf |= ACT_BF_OP_PADV2I8_MASK;  pinc = 2; break;
  case pack_mode_i4_e:   HLAPI.i.u.op.bf |= ACT_BF_OP_PADV4I4_MASK;  pinc = 4; break;
  default:               HLAPI.i.u.op.bf |= ACT_BF_OP_PADI16_MASK;   pinc = 1; break;
  }
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.pad_offs[i][SPATIAL_W] = HLAPI.i.u.op.pad_offs[i][SPATIAL_W] * pinc;
  }
}

// initialize the input tensors
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_gavgpool_params<B>::init_l1_input(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
  const impl_spec_container_t<BD> &p) {
  if (mode) {
    gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
    // fill the HLAPI offset parameters
    HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
    HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
    HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
    HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                                // W
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset(0);               // msb/lsb
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset(2)*TNSVSIZE +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0);          // W8
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0);          // H
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 4] = p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * p.data.get_offset(2) * TNSVSIZE +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0);          // D
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 5] = p.data.get_offset(0) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]) * p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * p.data.get_offset(2) * TNSVSIZE;  // C
  } else {
    gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
    // fill the legacy HLAPI offset parameters
    HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
    HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
    HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
    HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                         // W
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset(0);        // msb/lsb
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0);   // H
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset(2) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0);   // W
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 4] = p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0);   // D
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 5] = p.data.get_offset(0) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]) * p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(2) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * p.data.get_offset(3);   // C
  }
}

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_gavgpool_params<B>::init_l1_output(
  // structure with allocated buffers and tensors in L1 memory
  const impl_spec_container_t<BD>& p) {
  if (mode) {
    gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
    // fill the HLAPI offset parameters
    HLAPI.i.u.op.out.fm.fm_agu.ptr      = p.data.get_ptr();
    HLAPI.i.u.op.out.fm.fm_agu.buf.base = p.data.get_base();
    HLAPI.i.u.op.out.fm.fm_agu.buf.len  = p.data.get_size();
    HLAPI.i.u.op.out.fm.fm_agu.stride   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = p.data.get_offset(0);       // mlsb
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0);  // H
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * p.data.get_offset(3) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * p.data.get_offset(0);  // D
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = p.data.get_offset(0) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]) * p.data.get_offset(4) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * p.data.get_offset(3);  // C
  } else {
    gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
    // [D][H][W][Grp][C] --> [D][H][W][Grp][C/mlsb][mlsb]
    tensor_t<ixpix_t, 6, B> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5]));
    // transpose to [Grp][C][D=1][W=1][H=1][mlsb]
    tensor_t<ixpix_t, 6, B> t1(t0.transpose({0, 4, 3, 5, 1, 2}));
    // fill the HLAPI offset parameters
    HLAPI.i.u.op.out.fm.fm_agu.ptr      = localptr_t<ixpix_t>(t1.get_ptr());
    HLAPI.i.u.op.out.fm.fm_agu.buf.base = localptr_t<ixpix_t>(t1.get_base());
    HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t1.get_size();
    HLAPI.i.u.op.out.fm.fm_agu.stride   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = t1.get_offset(0);       // mlsb
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = t1.get_offset(1) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // H
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = t1.get_offset(2) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // W
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = t1.get_offset(3) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // D
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 5] = t1.get_offset(4) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // Grp*C
  }
}

template <template <typename> class B>
inline void gtoa_gavgpool_params<B>::get_shapes(
    gtoa_act_params_impl_shapes& s  // structure with implementation specific minimum buffer sizes
) {
  s = shapes;
}

#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_GAVGPOOL_INLINE_HPP_
