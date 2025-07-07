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
 * tensor_gtoa_interp_inline.hpp
 *
 * File defining a tensor level linear interpolation API base on the generic tensor operation API
 * this API supports multiple padding modes and datatypes
 * interpolation is done over the H dimension
 * bilinear interpolation can be done by calling this API twice, transposing W and H for the second call
 *
 */


#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_INTERP_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_INTERP_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// v2 constructor, VM(int8/int16/fp16/bf16) to VM(int8/int16/fp16/bf16)
template<template<typename> class B>
gtoa_interp_params<B>::gtoa_interp_params(
     aoffset_t                  noi,           // number input&output channels (not vectors)
     float                      hstart,        // height index start, passed through SR0
     float                      hdelta,        // height index increment per output, passed through SR1
     const shape<3>&            oshpi,         // tile output shape, indexed by spatial_axis_t
     act_dtype_t                intp,          // input datatype:  int8, int16, bf16, fp16
     act_dtype_t                outtp          // output datatype: int8, int16, bf16, fp16
     ) {
  ishp            = oshpi;
  ishp[SPATIAL_H] = 1+ceilf((oshpi[SPATIAL_H]-1)*hdelta);
  oshp            = oshpi;

  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  
  HLAPI.i.u.op.io_en    = ACT_IO_EN_GTH | ACT_IO_EN_OFM;
  switch (intp) {
  case dtype_int16:
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    break;
  case dtype_int8:
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    break;
  case dtype_fp16:
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_IN0FMODE_START;
    break;
  case dtype_bf16:
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_IN0FMODE_START;
    break;
  default:
    assert(0 && "unsupported input type");
  }
  switch (outtp) {
  case dtype_int16:
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    break;
  case dtype_int8:
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    break;
  case dtype_fp16:
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_OUTFMODE_START;
    break;
  case dtype_bf16:
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_OUTFMODE_START;
    break;
  default:
    assert(0 && "unsupported output type");
  }
  bool fmidbli = (HLAPI.i.u.op.bf & (1<<ACT_BF_OP_IN0DBL_START)) != 0;
  bool fmodbli = (HLAPI.i.u.op.bf & (1<<ACT_BF_OP_OUTDBL_START)) != 0;
  int c  = RDIV_UP(noi, ISIZE);
  int wo = NRND_UP(oshpi[SPATIAL_W], TNSVSIZE);
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmidbli  ? 2 * c : c), 1, ishp[SPATIAL_W],
                    ishp[SPATIAL_H], ishp[SPATIAL_D] };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmodbli  ? 2 * c : c), 1, (aoffset_t)wo,
                    oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // per channel shape, used to pass fixed parameters
  shapes.pshape = { 0 };
  // initialize micro-code
  int32_t offset = fp_e8m23_t(hstart).data;
  int32_t deltaf = fp_e8m23_t(hdelta).data;
  init_interp1d(HLAPI, offset, deltaf);

  // no parameter
  HLAPI.i.u.op.bnum = 0;

  // iterators, inner loop writes same input multiple times
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1] = 1;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2] = (c*oshp[2]*wo)/TNSVSIZE;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3] = oshp[1];
  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]  = 1;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1] = fmidbli ? 2 : 1;  // msb/lsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2] = 2;                // top/bottom
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3] = c;                // C
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4] = wo/TNSVSIZE;         // W
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5] = oshp[2];          // D
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-6] = oshp[1];          // H
  // feature-map output AGU
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]  = fmodbli ? 2*c : c;  // C*msb/lsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]  = wo/TNSVSIZE;           // W
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]  = oshp[2];            // D
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]  = oshp[1];            // H
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
  // writeback all lines
  HLAPI.i.u.op.out.fm.enable        = (int8_t)((1 << TNSVSIZE)-1);
}

// legacy constructor
// interp operation from feature-map (8b/16b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_interp_params<B>::gtoa_interp_params(
             aoffset_t                  noi,           // number output channels (not vectors)
             float                      delta,         // increment per output
             aoffset_t                  hout,          // total feature-map output height
             const shape<3>&            ishpi,         // tile input shape
             const shape<3>&            oshpi,         // tile output shape
             bool                       fmidbli,       // 16b I feature-map
             bool                       fmodbli        // 16b O feature-map
                                     )
             : gtoa_params<B>() {
  ishp = ishpi;
  oshp = oshpi;
  assert((ishpi[0] == oshpi[0]) && "tile input width should be equal to output width");
  assert((ishpi[2] == oshpi[2]) && "tile input depth should be equal to output depth");

  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  
  HLAPI.i.u.op.io_en    = ACT_IO_EN_GTH  | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (fmidbli ? (1 << ACT_BF_OP_IN0DBL_START) : 0) |
                          (fmodbli ? (1 << ACT_BF_OP_OUTDBL_START) : 0) |
                                     (1 << ACT_BF_OP_OUTSAT_START);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  int c  = RDIV_UP(noi, ISIZE);
  int wo = NRND_UP(oshpi[SPATIAL_W], TNSVSIZE);
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = { (aoffset_t)(fmidbli  ? 2 * c : c), 1, ishpi[SPATIAL_W],
                    ishpi[SPATIAL_H], ishpi[SPATIAL_D] };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmodbli  ? 2 * c : c), 1, (aoffset_t)wo,
                    oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // per channel shape, used to pass fixed parameters
  shapes.pshape = { 0 };
  // initialize micro-code
  int32_t offset = fp_e8m23_t(float(0.0)).data;
  int32_t deltaf = fp_e8m23_t(delta).data;
  // int8_t  scale  = fmidbli == fmodbli ? 15 : (fmidbli ? 23 : 7);
  init_interp1d(HLAPI, offset, deltaf);

  // no parameter
  HLAPI.i.u.op.bnum = 0;

  // iterators, inner loop writes same input multiple times
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1] = 1;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2] = (c*oshp[2]*wo)/TNSVSIZE;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3] = oshp[1];
  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]  = 1;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1] = fmidbli ? 2 : 1;  // msb/lsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2] = 2;                // top/bottom
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3] = c;                // C
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4] = wo/TNSVSIZE;         // W
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5] = oshp[2];          // D
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-6] = oshp[1];          // H
  // feature-map output AGU
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]  = fmodbli ? 2*c : c;  // C*msb/lsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]  = wo/TNSVSIZE;           // W
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]  = oshp[2];            // D
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]  = oshp[1];            // H
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
  // writeback all lines
  HLAPI.i.u.op.out.fm.enable        = (int8_t)((1 << TNSVSIZE)-1);
}

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_interp_params<B>::init_l1_output(
  const impl_spec_container_t<BD>&  p   // buffers and tensors in L1 memory [D][H][W][Grp][C]
                                ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
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
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_interp_params<B>::init_l1_input(
  const impl_spec_container_t<BD>&  p  // buffers and tensors in L1 memory [D][H][W][Grp][C]
                                ) {
  gtoa_params<B>::itens = p;
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                  // W8
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);   // msb/lsb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(3) +  // H2
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] =
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]*p.data.get_offset(0) +
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(3) +
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);  // C
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(2)*TNSVSIZE +
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]*p.data.get_offset(0) +
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(3) +
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);  // W
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = p.data.get_offset(4) +
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*p.data.get_offset(2)*TNSVSIZE +
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]*p.data.get_offset(0) +
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(3) +
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);  // D
   HLAPI.i.u.op.primary.fm_agu.offsets[1] = p.data.get_offset(2);  // W 
   HLAPI.i.u.op.primary.fm_agu.offsets[0] = p.data.get_offset(3);  // H 
}

template<template<typename> class B>
inline void gtoa_interp_params<B>::get_shapes(
  gtoa_act_params_impl_shapes& s   // implementation specific minimum buffer sizes
                      ) {
  s = shapes;
}

#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_INTERP_INLINE_HPP_
