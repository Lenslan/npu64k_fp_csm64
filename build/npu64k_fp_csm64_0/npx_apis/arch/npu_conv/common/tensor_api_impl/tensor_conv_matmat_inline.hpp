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
 * tensor_conv_inline.hpp
 *
 * File defining the native specific inline functions for the tensor convolution objects
 *
 */

#ifndef NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_MATMAT_INLINE_HPP_
#define NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_MATMAT_INLINE_HPP_

// #define TENSOR_CONV_INLINE_HPP_DEBUG
#ifdef TENSOR_CONV_INLINE_HPP_DEBUG
  #define LDBGV(...) DBGV(__VA_ARGS__)
#else
  #define LDBGV(...)
#endif


// All identifiers related to the tensor API go into namespace tensor::v200
namespace tensor::v200 {

//
// Matrix multiplier member functions
//
// constructor for 1D/2D/3D convolution object, supporting various datatypes
template<template<typename> class B>
matmat_params<B>::matmat_params(
                                aoffset_t                 nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                                aoffset_t                 noi,           // number output channels (not vectors)
                                aoffset_t                 vii,           // spatial dimension of input and output
                                bool                      use_acci,      // use input accumulator from AM else 0
                                bool                      keep_acci,     // keep output accumulator in AM else stream
                                fm_cfg_t                  fma_tpi,       // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
                                fm_cfg_t                  fmb_tpi,       // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
                                aoffset_t                 bi             // batch size
                                ) : conv_base<B>() {
  assert ((fma_tpi == fmb_tpi) && "matmat required both tensors of same type");
  batch    = bi;
  ni       = nii;
  no       = noi;
  vi       = vii;
  use_acc  = use_acci;
  keep_acc = keep_acci;
  fm_tp    = fma_tpi;
  cf_tp    = fmb_tpi == fm_cfg_8b_e ? cf_cfg_8b_nozp_e : (fmb_tpi == fm_cfg_16b_e ? cf_cfg_16b_e : (fmb_tpi == fm_cfg_bf16_e ? cf_cfg_bf16_e : cf_cfg_fp16_e));
  impl_spec.cf_4b     = 0;
  impl_spec.cf_mode   = coef_mode_fm;
  impl_spec.inn       = 1;
  impl_spec.onn       = 1;
  impl_spec.conv_mode = DINO(conv_mode_1x1);
  hlapi.i.fm_padlim   = {(aoffset_t)(vi-1), (aoffset_t)(no-1), 0};
}
template<template<typename> class B>
matmat_params<B>::matmat_params(
                                aoffset_t                 nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                                aoffset_t                 noi,           // number output channels (not vectors)
                                aoffset_t                 vii,           // spatial dimension of input and output
                                const shape<2>&           padlim,        // padding limit for tiled matrix multiply
                                bool                      use_acci,      // use input accumulator from AM else 0
                                bool                      keep_acci,     // keep output accumulator in AM else stream
                                fm_cfg_t                  fma_tpi,       // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
                                fm_cfg_t                  fmb_tpi,       // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
                                aoffset_t                 bi             // batch size
                                ) : conv_base<B>() {
  assert ((fma_tpi == fmb_tpi) && "matmat required both tensors of same type");
  batch    = bi;
  ni       = nii;
  no       = noi;
  vi       = vii;
  use_acc  = use_acci;
  keep_acc = keep_acci;
  fm_tp    = fma_tpi;
  cf_tp    = fmb_tpi == fm_cfg_8b_e ? cf_cfg_8b_nozp_e : (fmb_tpi == fm_cfg_16b_e ? cf_cfg_16b_e : (fmb_tpi == fm_cfg_bf16_e ? cf_cfg_bf16_e : cf_cfg_fp16_e));
  impl_spec.cf_4b     = 0;
  impl_spec.cf_mode   = coef_mode_fm;
  impl_spec.inn       = 1;
  impl_spec.onn       = 1;
  impl_spec.conv_mode = DINO(conv_mode_1x1);
  hlapi.i.fm_padlim   = {padlim[0], padlim[1], 0};
}
// V1 legacy constructor
template<template<typename> class B>
matmat_params<B>::matmat_params(
                                aoffset_t                          nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                                aoffset_t                          noi,           // number output channels (not vectors), in units of 8b or 16b feature-map pixels
                                aoffset_t                          vii,           // spatial dimension of input and output
                                bool                               use_acci,      // use input accumulator to accumulate over multiple tiles
                                bool                               keep_acci,     // keep output accumulator to accumulate over multiple tiles
                                bool                               fma_dbli,      // 8b or 16b matrix A
                                bool                               fmb_dbli       // 8b or 16b matrix B
                                ) : conv_base<B>() {
  // copy parameters into data members
  assert ((fma_dbli == fmb_dbli) && "matmat required both tensors of same type");
  batch    = 1;
  ni       = nii;
  no       = noi;
  vi       = vii;
  use_acc  = use_acci;
  keep_acc = keep_acci;
  fm_tp    = fma_dbli ? fm_cfg_16b_e : fm_cfg_8b_e;
  cf_tp    = fmb_dbli ? cf_cfg_16b_e : cf_cfg_8b_nozp_e;
  impl_spec.cf_4b     = 0;
  impl_spec.cf_mode   = coef_mode_fm;
  impl_spec.inn       = 1;
  impl_spec.onn       = 1;
  impl_spec.conv_mode = DINO(conv_mode_1x1);
  hlapi.i.fm_padlim   = {(aoffset_t)(vi-1), (aoffset_t)(no-1), 0};
}

template<template<typename> class B>
matmat_params<B>::matmat_params(
                                aoffset_t                          nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                                aoffset_t                          noi,           // number output channels (not vectors), in units of 8b or 16b feature-map pixels
                                aoffset_t                          vii,           // spatial dimension of input and output
                                const shape<2>&                    padlim,        // padding limit for tiled matrix multiply
                                bool                               use_acci,      // use input accumulator to accumulate over multiple tiles
                                bool                               keep_acci,     // keep output accumulator to accumulate over multiple tiles
                                bool                               fma_dbli,      // 8b or 16b matrix A
                                bool                               fmb_dbli       // 8b or 16b matrix B
                                ) : conv_base<B>() {
  // copy parameters into data members
  assert ((fma_dbli == fmb_dbli) && "matmat required both tensors of same type");
  batch    = 1;
  ni       = nii;
  no       = noi;
  vi       = vii;
  use_acc  = use_acci;
  keep_acc = keep_acci;
  fm_tp    = fma_dbli ? fm_cfg_16b_e : fm_cfg_8b_e;
  cf_tp    = fmb_dbli ? cf_cfg_16b_e : cf_cfg_8b_nozp_e;
  impl_spec.cf_4b     = 0;
  impl_spec.cf_mode   = coef_mode_fm;
  impl_spec.inn       = 1;
  impl_spec.onn       = 1;
  impl_spec.conv_mode = DINO(conv_mode_1x1);
  hlapi.i.fm_padlim   = {padlim[0], padlim[1], 0};
}

template<template<typename> class B>
void matmat_params<B>::get_shapes(
                                  conv_params_impl_shapes&    p       // structure with implementation specific minimum buffer sizes
                                  ) {
  bool fma_dbl = fm_tp == fm_cfg_16b_e || fm_tp == fm_cfg_bf16_e || fm_tp == fm_cfg_fp16_e;
  bool fmb_dbl = cf_tp == cf_cfg_16b_e || cf_tp == cf_cfg_bf16_e || cf_tp == cf_cfg_fp16_e;
  // dimensions to multiple of 16
  int ci = fma_dbl ? ROUND_UP(ni, ISIZE) : ROUND_UP(ni, 2*ISIZE);
  int co = ROUND_UP(no, ISIZE);
  // round spatial input and output dimension to multiple of TNSVSIZE
  int vr = ROUND_UP(vi, TNSVSIZE);
  // Matrix A shape: ixpix_t    [D][H][W][Grp][Ci*mlsb]     = [vi][batch][ci]
  p.ishape = {(aoffset_t)((fma_dbl ? 2*ci:ci)/ISIZE), (aoffset_t)batch, (aoffset_t)vr, 1, 1};
  // Matrix B shape: ixpix_t    [D][H][W][Grp][Ci*mlsb]     = [co][batch][ci]
  p.ishapeb = {(aoffset_t)((fmb_dbl ? 2*ci:ci)/ISIZE), (aoffset_t)batch, (aoffset_t)co, 1, 1};
  // Matrix C shape:  vyixacc_t  [chn][dep][col][row][msb/lsb/onn] = [chn*batch][1][col][1][msb]
  p.oshape =
    {(aoffset_t)((fm_tp == fm_cfg_16b_e && cf_tp == cf_cfg_16b_e) ? 2:1), 1, (aoffset_t)(vr/TNSVSIZE), 1, (aoffset_t)((use_acc|keep_acc) ? co*batch/ISIZE : 1)};
  // set HLAPI attributes
  hlapi.i.bf = (((uint32_t)impl_spec.conv_mode) << CONV_BF_CONV_MODE_START) |
    (((uint32_t)impl_spec.cf_mode) << CONV_BF_CF_MODE_START)   |
    (((uint32_t)fm_tp)     << CONV_BF_FM_CFG_START)    |
    (((uint32_t)cf_tp)     << CONV_BF_CF_CFG_START)    |
    (((uint32_t)use_acc)   << CONV_BF_USE_ACC_START)   |
    (((uint32_t)keep_acc)  << CONV_BF_KEEP_ACC_START);
  hlapi.i.fm_padpos   = {0,0,0};
  // iterators
  if (!fma_dbl) {
    // stash reads v8i32 per cycle
    hlapi.i.iter[CONV_ITER_GRP]       = batch;
    hlapi.i.iter[CONV_ITER_NO]        = co/ISIZE;
    hlapi.i.iter[CONV_ITER_NI]        = ci/(2*ISIZE);
    hlapi.i.iter[CONV_ITER_QD]        = 1;
    hlapi.i.iter[CONV_ITER_COL]       = vr/TNSVSIZE;
    hlapi.i.iter[CONV_ITER_ROW]       = 1;
    hlapi.i.iter[CONV_ITER_INN]       = 1;
    hlapi.i.iter[CONV_ITER_ONN]       = 1;
    // coefficients read in 4 cycles 2*2*v8i16
    hlapi.i.cf_iter[CONV_CF_ITER_IN]  = 2;
    hlapi.i.cf_iter[CONV_CF_ITER_NI]  = ci/ISIZE;
    hlapi.i.cf_iter[CONV_CF_ITER_NO]  = co/ISIZE;
    hlapi.i.cf_iter[CONV_CF_ITER_GRP] = batch;
  } else {
    // stash reads v8i32 per cycle; coefficients replicated and two sets used in two cycles
    hlapi.i.iter[CONV_ITER_GRP]       = batch;
    hlapi.i.iter[CONV_ITER_NO]        = co/ISIZE;
    hlapi.i.iter[CONV_ITER_NI]        = ci/ISIZE;
    hlapi.i.iter[CONV_ITER_QD]        = 1;
    hlapi.i.iter[CONV_ITER_COL]       = vr/TNSVSIZE;
    hlapi.i.iter[CONV_ITER_ROW]       = 1;
    hlapi.i.iter[CONV_ITER_INN]       = 1;
    hlapi.i.iter[CONV_ITER_ONN]       = 1;
    // coefficients read in 2 cycles 2*v8i16
    hlapi.i.cf_iter[CONV_CF_ITER_IN]  = 2;
    hlapi.i.cf_iter[CONV_CF_ITER_NI]  = 2*ci/ISIZE;
    hlapi.i.cf_iter[CONV_CF_ITER_NO]  = co/ISIZE;
    hlapi.i.cf_iter[CONV_CF_ITER_GRP] = batch;
  }
}

template<template<typename> class B>
void matmat_params<B>::set_alt_shape(
                                     aoffset_t                nii,        // number input channels (not vectors),
                                     // in units of 8b or 16b feature-map pixels
                                     aoffset_t                noi,        // number output channels (not vectors)
                                     aoffset_t                vi,         // number spatial elements (not vectors)
                                     bool                     use_acci,   // use input accumulator
                                     bool                     keep_acci,  // keep output accumulator
                                     conv_params_impl_alt&    alt         // encoded alternative shape
                                     ) {
  assert(0&&"not implemented yet");
}

template<template<typename> class B>
template<template<typename> class BD>
void matmat_params<B>::init_l1_a(
                                 const impl_spec_container_t<BD>&   p       // set the input matrix A
                                 ) {
  // ensure batch dimension is after input channel dimension
  assert((batch == 1 || (p.data.get_offset(1) == (2*p.data.get_offset(0)*hlapi.i.iter[CONV_ITER_NI])))
         && "matmat primary feature-map batch (group) dimension should be next to channel dimension in memory");
  // For matrix A, the row iterator is used to pad the output channel dimension
  tens = p;
  hlapi.i.fm_buf.len                      = p.data.get_size();
  hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_COL] = 1;
  hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_ROW] = 1;
  hlapi.i.fm_doffsets[CONV_FM_DOFF_COL]   = p.data.get_offset(2);
  hlapi.i.fm_doffsets[CONV_FM_DOFF_ROW]   =
    p.data.get_offset(3)+2*(1-impl_spec.inn)*p.data.get_offset(0);
  hlapi.i.fm_doffsets[CONV_FM_DOFF_CHAN]  = p.data.get_offset(0);
  // one quadrant pointing to next input channel group
  quadrant_t q;
  hlapi.i.quad_iter      = {1, 1, 1};
  // at end of quadrant move to next NI set of input channels
  int vr = ROUND_UP(vi, TNSVSIZE);
  q.pdoffs[CONV_PAD_COL] = (1-(vr/TNSVSIZE))*TNSVSIZE;
  q.pdoffs[CONV_PAD_ROW] = 0;
  q.pdoffs[CONV_PAD_DEP] = 0;
  q.doffs                = q.pdoffs[CONV_PAD_COL]*p.data.get_offset(2) + 2*p.data.get_offset(0);
  hlapi.i.quad_data[3]   = q;
}

template<template<typename> class B>
template<template<typename> class BD>
void matmat_params<B>::init_l1_b(
                                 const impl_spec_container_t<BD>&   p       // set the input matrix B
                                 ) {
  // ensure batch dimension is after input channel dimension
  assert((batch == 1 || (p.data.get_offset(1) == (2*p.data.get_offset(0)*hlapi.i.iter[CONV_ITER_NI])))
         && "matmat secondary feature-map batch (group) dimension should be next to channel dimension in memory");
  tensb = p;
  hlapi.i.cf_offsets[CONV_CF_ITER_IN]  = NUM_COEF_QUEUE*p.data.get_offset(2);
  hlapi.i.cf_offsets[CONV_CF_ITER_NI]  = p.data.get_offset(0)-NUM_COEF_QUEUE*p.data.get_offset(2);
  hlapi.i.cf_offsets[CONV_CF_ITER_NO]  = NUM_COEF_QUEUE*p.data.get_offset(2)+(1-hlapi.i.cf_iter[CONV_CF_ITER_NI])*p.data.get_offset(0);
  hlapi.i.cf_offsets[CONV_CF_ITER_GRP] = p.data.get_offset(0)+
    NUM_COEF_QUEUE*p.data.get_offset(2)*(3-hlapi.i.cf_iter[CONV_CF_ITER_IN]-2*hlapi.i.cf_iter[CONV_CF_ITER_NO]);
}

template<template<typename> class B>
poffset_t matmat_params<B>::update_ptra(
                                        aoffset_t              spat_offset,  // spatial offset
                                        aoffset_t              chan_offset   // channel offset
                                        ) {
  return tens.data.get_offset({chan_offset, 0, spat_offset, 0, 0});
}

template<template<typename> class B>
poffset_t matmat_params<B>::update_ptrb(
                                        aoffset_t              spat_offset,  // spatial offset
                                        aoffset_t              chan_offset   // channel offset
                                        ) {
  return tensb.data.get_offset({chan_offset, 0, spat_offset, 0, 0});
}
}  // namespace tensor::v200
#undef LDBGV
#endif  // NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_MATMAT_INLINE_HPP_
