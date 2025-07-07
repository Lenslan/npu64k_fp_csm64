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
 * tensor_gtoa_softmax_inline.hpp
 *
 * File defining a tensor level SOFTMAX API based on the generic tensor operation API
 *
 */

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_SOFTMAX_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_SOFTMAX_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

//
// Softmax MAX and ARGMAX function, scalar register 0 encodes the input bias
//
template<template<typename> class B>
gtoa_softmax_max_params<B>::gtoa_softmax_max_params(
                aoffset_t                noi          // number channels (not vectors); 16b
                                                    ) {
  // divide and round up channels by ISIZE
  no = noi;
  int ich = RDIV_UP(noi, ISIZE);
  // set shapes
  shapes.ishape = { (aoffset_t)(2*ich), 1, 1, 1, 1};
  shapes.oshape = { 0, 0, 0, 0, 0};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf         = 0;       // function, not LUT init
  // input is 16b feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0;
  HLAPI.i.u.op.bf    = ACT_BF_OP_IN0DBL_MASK;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = ich;              // inner loop over channels
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = 1;                // middle loop spatial output
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = 1;                // outer loop channel
  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-2; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = 2;    // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = ich;  // channel
  // initialize microcode
  init_argmax_c(HLAPI);
}

//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_softmax_max_params<B>::init_l1_input(
  const impl_spec_container_t<BD>& p  // structure with allocated buffers and tensors
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][G][C/mlsb][mlsb]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]));
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = 0;
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = t0.get_offset(0);  // msb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = t0.get_offset(1)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);  // OC
}

template<template<typename> class B>
inline void gtoa_softmax_max_params<B>::get_shapes(
  gtoa_act_params_impl_shapes& s        // structure with minimum  buffer sizes
                                           ) {
  s = shapes;
}


//
// Softmax EXP,SUM/RECIP
//
template<template<typename> class B>
gtoa_softmax_exp_params<B>::gtoa_softmax_exp_params(
                const gtoa_softmax_max_params<B>& o
                                                    ) {
  // divide and round up channels by ISIZE
  no = o.no;
  int ich = RDIV_UP(no, ISIZE);
  // set shapes
  shapes.ishape = { (aoffset_t)(2*ich), 1, 1, 1, 1};
  shapes.oshape = { (aoffset_t)(2*ich), 1, 1, 1, 1};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf         = 0;       // function, not LUT init
  // input and output is 16b feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0|ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf    = ACT_BF_OP_IN0DBL_MASK|ACT_BF_OP_OUTDBL_MASK|ACT_BF_OP_OUTSAT_MASK;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = ich;               // inner loop over channels
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = 1;                 // middle loop spatial output
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = 1;                 // outer loop channel
  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-2; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = 2;     // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = ich;   // channel
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS-2; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]   = 2;     // mlsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]   = ich;   // channel
  HLAPI.i.u.op.out.fm.enable = 1;  // enable one output lane
  // initialize microcode, sum output and pick up from VR7
  init_exp(HLAPI, true, false);
}

//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_softmax_exp_params<B>::init_l1_input(
  const impl_spec_container_t<BD>&    p  // structure with allocated tensors in L1 memory
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][G][C/mlsb][mlsb]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]));
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = 0;                 // no spatial dimension
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = t0.get_offset(0);     // msb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = t0.get_offset(1)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OC
}
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_softmax_exp_params<B>::init_l1_output(
    const impl_spec_container_t<BD>&    p  // structure with allocated tensors in L1 memory
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][G][C/mlsb][mlsb]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]));
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = 0;                       // no spatial dimension
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t0.get_offset(0);     // msb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t0.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OC
}

template<template<typename> class B>
inline void gtoa_softmax_exp_params<B>::get_shapes(
    gtoa_act_params_impl_shapes& s    // structure with implementation minimum buffer sizes
                                           ) {
  s = shapes;
}

//
// Softmax scale
//
template<template<typename> class B>
gtoa_softmax_scale_params<B>::gtoa_softmax_scale_params(
  const gtoa_softmax_max_params<B>& o
                                                    ) {
  // divide and round up channels by ISIZE
  no = o.no;
  int ich = RDIV_UP(no, ISIZE);
  // set shapes
  shapes.ishape = { (aoffset_t)(2*ich), 1, 1, 1, 1};
  shapes.oshape = { (aoffset_t)(2*ich), 1, 1, 1, 1};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf         = 0;       // function, not LUT init
  // input and output is feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0|ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf    = ACT_BF_OP_IN0DBL_MASK|ACT_BF_OP_OUTDBL_MASK|ACT_BF_OP_OUTSAT_MASK;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = ich;                // inner loop over channels
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = 1;                  // middle loop spatial output
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = 1;                  // outer loop channel
  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-2; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = 2;      // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = ich;    // channel
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS-2; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]   = 2;      // mlsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]   = ich;    // channel
  HLAPI.i.u.op.out.fm.enable = 1;  // enable one output lane
  // initialize microcode
  init_recip_scale(HLAPI);
  // scale result to 16b
  HLAPI.i.u.op.scl[1] = 13;
}

//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_softmax_scale_params<B>::init_l1_input(
  const impl_spec_container_t<BD>&    p  // structure with allocated tensors in L1 memory
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][G][C/mlsb][mlsb]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]));
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = 0;                       // no spatial dimension
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = t0.get_offset(0);     // msb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = t0.get_offset(1)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OC
}
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_softmax_scale_params<B>::init_l1_output(
  const impl_spec_container_t<BD>&    p  // structure with allocated tensors in L1 memory
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][G][C/mlsb][mlsb]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]));
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = 0;                    // no spatial dimension
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t0.get_offset(0);     // msb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t0.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OC
}

template<template<typename> class B>
inline void gtoa_softmax_scale_params<B>::get_shapes(
  gtoa_act_params_impl_shapes& s   // structure with implementation minimum buffer sizes
                                           ) {
  s = shapes;
}
#undef HLAPI
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_SOFTMAX_INLINE_HPP_
