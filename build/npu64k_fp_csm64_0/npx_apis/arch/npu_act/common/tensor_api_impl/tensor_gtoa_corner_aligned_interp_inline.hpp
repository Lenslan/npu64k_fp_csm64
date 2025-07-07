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
 * tensor_gtoa_corner_aligned_interp_inline.hpp
 *
 * File defining a tensor level corner_aligned_interp API base on the generic tensor operation API
 *
 */


#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CORNER_ALIGNED_INTERP_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CORNER_ALIGNED_INTERP_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// constructor
// corner_aligned_interp operation from feature-map (8b/16b) to feature-map (8b/16b)
template<template<typename> class B>
gtoa_corner_aligned_interp_params<B>::gtoa_corner_aligned_interp_params(
             aoffset_t                  noi,           // number output channels (not vectors)
             aoffset_t                  hin,           // total feature-map input height
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
  // ratio and offset increment per output
  rat   = hin/hout;
  fp_e8m23_t fdelta(static_cast<float>(static_cast<double>(hin-1)/
                                       static_cast<double>(hout-1)));
  delta = fdelta.data;

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
  // int8_t  scale  = fmidbli == fmodbli ? 15 : (fmidbli ? 23 : 7);
  init_interp1d(HLAPI, offset, delta);

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
void gtoa_corner_aligned_interp_params<B>::init_l1_output(
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
void gtoa_corner_aligned_interp_params<B>::init_l1_input(
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
inline void gtoa_corner_aligned_interp_params<B>::get_shapes(
  gtoa_act_params_impl_shapes& s   // implementation specific minimum buffer sizes
                      ) {
  s = shapes;
}

template<template<typename> class B>
inline void gtoa_corner_aligned_interp_params<B>::param_enc(
     gtoa_params_impl_pchan<xbuffer_t>& obuf) {  // NOLINT [runtime/references]
  int8_t*  bpars   = reinterpret_cast<int8_t*>(obuf.tns.get_ptr());
  //int8_t*  bparsc  = reinterpret_cast<int8_t*>(bpars);   // pointer to start of BRB0 values
  int32_t* bparsw  = reinterpret_cast<int32_t*>(bpars);  // poiinter to start of BRW2 values
  for (int i = 0; i < ISIZE; i++) {
    bparsw[0*ISIZE+i] = fp_e8m23_t((float)1.0).data;  // BRW0 1.0
  }
}

template<template<typename> class B>
inline acc_t gtoa_corner_aligned_interp_params<B>::get_offset() const {
  return (acc_t)delta;
}


#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_CORNER_ALIGNED_INTERP_INLINE_HPP_
