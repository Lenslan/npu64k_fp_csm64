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
 * tensor_conv_fc_inline.hpp
 *
 * File defining the native specific inline functions for the tensor convolution objects
 *
 */

#ifndef NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_FC_INLINE_HPP_
#define NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_FC_INLINE_HPP_

// #define TENSOR_CONV_INLINE_HPP_DEBUG
#ifdef TENSOR_CONV_INLINE_HPP_DEBUG
  #define LDBGV(...) DBGV(__VA_ARGS__)
#else
  #define LDBGV(...)
#endif

// All identifiers related to the tensor API go into namespace tensor::v200
namespace tensor::v200 {

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// FC convolution inline function
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
template<template<typename> class B>
fc_params<B>::fc_params(aoffset_t                          grpi,          // number of groups
                        aoffset_t                          nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                        aoffset_t                          noi,           // number output channels (not vectors)
                        bool                               use_acci,      // use input accumulator
                        bool                               keep_acci,     // keep output accumulator
                        fm_cfg_t                           fm_tpi,    // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
                        cf_cfg_t                           cf_tpi     // coefficient type: cf_cfg_4b_zp_e, cf_cfg_4b_nozp_e, cf_cfg_8b_zp_e, 
                        ) : conv_base<B>() {
  // copy parameters into object
  grp      = grpi;
  ni       = nii;
  no       = noi;
  use_acc  = use_acci;
  keep_acc = keep_acci;
  fm_tp    = fm_tpi;
  cf_tp    = cf_tpi;
  // select default implementation
  impl_spec.cf_4b = 0;                          // FIXME: default w/o 4b cf
  impl_spec.cf_mode = coef_mode_uncompressed;   // FIXME: default is w/ uncompressed cf
  impl_spec.inn = 1;
  impl_spec.onn = 1;
  impl_spec.conv_mode = FC(conv_mode_fc);
}

template<template<typename> class B>
fc_params<B>::fc_params(aoffset_t                          grpi,          // number of groups
                        aoffset_t                          nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                        aoffset_t                          noi,           // number output channels (not vectors)
                        bool                               use_acci,      // use input accumulator
                        bool                               keep_acci,     // keep output accumulator
                        bool                               fm_dbli,       // 8b or 16b feature-maps
                        bool                               cf_dbli,       // 8b or 16b coefficients
                        bool                               cf_zpi         // coefficients include a zero-point
                        ) : conv_base<B>() {
  // copy parameters into object
  grp      = grpi;
  ni       = nii;
  no       = noi;
  use_acc  = use_acci;
  keep_acc = keep_acci;
  fm_tp    = fm_dbli ? fm_cfg_16b_e : fm_cfg_8b_e;
  cf_tp    = cf_dbli ? cf_cfg_16b_e : (cf_zpi ? cf_cfg_8b_zp_e: cf_cfg_8b_nozp_e);
  // select default implementation
  impl_spec.cf_4b = 0;                          // FIXME: default w/o 4b cf
  impl_spec.cf_mode = coef_mode_uncompressed;   // FIXME: default is w/ uncompressed cf
  impl_spec.inn = 1;
  impl_spec.onn = 1;
  impl_spec.conv_mode = FC(conv_mode_fc);
}

template<template<typename> class B>
fc_params<B>::fc_params(aoffset_t                          nii,           // number input channels (not vectors), in units of 8b or 16b feature-map pixels
                        aoffset_t                          noi,           // number output channels (not vectors)
                        bool                               use_acci,      // use input accumulator
                        bool                               keep_acci,     // keep output accumulator
                        bool                               fm_dbli,       // 8b or 16b feature-maps
                        bool                               cf_dbli,       // 8b or 16b coefficients
                        bool                               cf_zpi         // coefficients include a zero-point
                        ) : conv_base<B>() {
  // copy parameters into object
  grp      = 1;
  ni       = nii;
  no       = noi;
  use_acc  = use_acci;
  keep_acc = keep_acci;
  fm_tp    = fm_dbli ? fm_cfg_16b_e : fm_cfg_8b_e;
  cf_tp    = cf_dbli ? cf_cfg_16b_e : (cf_zpi ? cf_cfg_8b_zp_e: cf_cfg_8b_nozp_e);
  // select default implementation
  impl_spec.cf_4b = 0;                          // FIXME: default w/o 4b cf
  impl_spec.cf_mode = coef_mode_uncompressed;   // FIXME: default is w/ uncompressed cf
  impl_spec.inn = 1;
  impl_spec.onn = 1;
  impl_spec.conv_mode = FC(conv_mode_fc);
}

template<template<typename> class B>
void fc_params<B>::get_shapes(conv_params_impl_shapes& s) {
 
  hlapi.i.bf = (((uint32_t)impl_spec.conv_mode) << CONV_BF_CONV_MODE_START) |
    (((uint32_t)impl_spec.cf_mode) << CONV_BF_CF_MODE_START)   |
    (((uint32_t)fm_tp)     << CONV_BF_FM_CFG_START)    |
    (((uint32_t)cf_tp)     << CONV_BF_CF_CFG_START)    |
    (((uint32_t)use_acc)   << CONV_BF_USE_ACC_START)   |
    (((uint32_t)keep_acc)  << CONV_BF_KEEP_ACC_START);
  hlapi.i.fm_padlim[0]   = 0;
  hlapi.i.fm_padlim[1]   = 0;
  hlapi.i.fm_padlim[2]   = 0;
  hlapi.i.fm_padpos[0]   = 0;
  hlapi.i.fm_padpos[1]   = 0;
  hlapi.i.fm_padpos[2]   = 0;
  bool fm_dbl = (fm_tp == fm_cfg_16b_e) || (fm_tp == fm_cfg_bf16_e) || (fm_tp == fm_cfg_fp16_e);
  // derived shapes by rounding
  int ic   = ROUND_UP((fm_dbl) ? 2*ni : ni, ISIZE);
  int oc   = ROUND_UP(no, ISIZE*TNSVSIZE);
  shapes.ishape = {   // ixpix_t [dep][row][col][grp][chn]
    (aoffset_t)(ic/ISIZE),
    (aoffset_t)grp,
    (aoffset_t)1,
    (aoffset_t)1,
    (aoffset_t)1
  };
  shapes.oshape = {   // vyixacc_t [chn][dep][col][row][msb/lsb/onn]
    (aoffset_t)((fm_tp==fm_cfg_16b_e&&cf_tp==cf_cfg_16b_e) ? 2 : 1),
    (aoffset_t)1,
    (aoffset_t)1,
    (aoffset_t)1,
    (aoffset_t)((use_acc|keep_acc) ? oc/(ISIZE*TNSVSIZE) : 1),
  };
  shapes.pshape = {   // ixpix_t [chn]
    (aoffset_t)(ic/ISIZE),
  };

  int cbytenum = grp*ic*oc*(cf_tp == cf_cfg_16b_e?2:1);
  if (cf_tp == cf_cfg_4b_zp_e||cf_tp == cf_cfg_4b_nozp_e) {
    cbytenum = ROUND_UP(cbytenum, 2);  // only need half the coefficients for encoding in 4b mode
  }
  // round up to number of ixpix_t and v8ixpix_t
  switch (impl_spec.cf_mode) {
    case coef_mode_sparse:
      // need 10b to encode coef of 8b
      cbytenum = RDIV_UP(RDIV_UP(RDIV_UP(10*cbytenum, 8), 16), 8)*8*16;
      break;
    case coef_mode_compressed:
      // need 9b to encode coef of 8b
      cbytenum = RDIV_UP(RDIV_UP(RDIV_UP(9*cbytenum, 8), 16), 8)*8*16;
      break;
    default:
      // need 8b to encode
      break;
  }
  if (cf_tp == cf_cfg_8b_zp_e || cf_tp == cf_cfg_4b_zp_e) {
    // add per channel zero-points
    cbytenum += oc;
  }
  hlapi.i.cf_offsets  = {8, 8, 8, 8};
  shapes.cshape = RDIV_UP(cbytenum, ISIZE);
  s = shapes;
  hlapi.i.iter[CONV_ITER_GRP] = grp;
  hlapi.i.iter[CONV_ITER_NO]  = (impl_spec.cf_mode == coef_mode_sparse)
                              ? oc/(ISIZE*TNSVSIZE*2)
                              : oc/(ISIZE*TNSVSIZE);
  hlapi.i.iter[CONV_ITER_NI]  = ic/ISIZE;
  hlapi.i.iter[CONV_ITER_QD]  = 1;
  hlapi.i.iter[CONV_ITER_COL] = 1;
  hlapi.i.iter[CONV_ITER_ROW] = 1;
  hlapi.i.iter[CONV_ITER_INN] = 1;
  hlapi.i.iter[CONV_ITER_ONN] = 1;
  hlapi.i.cf_iter[CONV_CF_ITER_IN]  = 16;
  hlapi.i.cf_iter[CONV_CF_ITER_NI]  = ic/ISIZE;
  hlapi.i.cf_iter[CONV_CF_ITER_NO]  = oc/ISIZE;
  hlapi.i.cf_iter[CONV_CF_ITER_GRP] = 1;
}

template<template<typename> class B>
template<template<typename> class BD>
void fc_params<B>::init_l1(const impl_spec_container_t<BD>& p) {
  tens = p;
  hlapi.i.fm_ptr      = tens.data.get_ptr();
  hlapi.i.fm_buf.base = tens.data.get_base();
  hlapi.i.fm_buf.len  = tens.data.get_size();
  // data: ixpix_t [D][H][W][G][C]
  hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_COL] = 0;
  hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_ROW] = 0;
  hlapi.i.fm_doffsets[CONV_FM_DOFF_COL]   = tens.data.get_offset(0);
  hlapi.i.fm_doffsets[CONV_FM_DOFF_ROW]   = 0;
  hlapi.i.fm_doffsets[CONV_FM_DOFF_CHAN]  = 8*tens.data.get_offset(0);
  // only one quadrant
  hlapi.i.quad_iter[0]   = 1;
  hlapi.i.quad_iter[1]   = 1;
  hlapi.i.quad_iter[2]   = 1;
  // last quadrant move to next set of input channels
  quadrant_t q;
  q.pdoffs[CONV_PAD_COL] = 0;
  q.pdoffs[CONV_PAD_ROW] = 0;
  q.pdoffs[CONV_PAD_DEP] = 0;
  q.doffs                = tens.data.get_offset(0);
  hlapi.i.quad_data[3]   = q;
}

// coefficient encoding function, supporting 8b or 16b coefficients without zero-points
template<template<typename> class B>
void fc_params<B>::coef_enc(
    const tensor_t<coef_t, 4, xbuffer_t>& icf,  // input coefficients
                                             // [Grp][Cout][Cin][Coef h/l], h/l only for cf16 mode
    // outputs, buffers preallocated by caller
    conv_params_impl_coef<xbuffer_t>& obuf,  // output encoded coefficients NOLINT[runtime/references]
    xbuffer_t<coef_t>& tbuf            // allocator for temporary buffers NOLINT[runtime/references]
    ) {
  size_t l;
  if (cf_tp==cf_cfg_16b_e) {
    npu_conv::coef_enc(icf,                 // input coefficients [Grp][Cout/Grp][Cin/Grp][Coef h/l]
                       tbuf,
                       TNSVSIZE,
                       fm_tp==fm_cfg_16b_e, // 16b feature-map
                       obuf.cbuf,           // output encoded coefficient tensor
                       l);                  // size of used coefficient buffer in bytes
  } else {
    npu_conv::coef_enc(icf.reduce(0),       // input coefficients [Grp][Cout/Grp][Cin/Grp], 8b only
                       tbuf,
                       TNSVSIZE,
                       impl_spec.cf_mode,   // coefficient compression mode uncompressed
                                            // or compressed or sparse
                       fm_tp==fm_cfg_16b_e,  // 16b feature-map
                       cf_tp==cf_cfg_4b_nozp_e,  // 4b coefficient encoding
                       obuf.cbuf,           // output encoded coefficient tensor
                       l);                  // size of used coefficient buffer in bytes
  }
  // reduce the buffer size
  obuf.cbuf.set_size(l);
}

// coefficient encoding function, supporting 8b only with zero-points
template<template<typename> class B>
void fc_params<B>::coef_enc(
    const tensor_t<coef_t, 3, xbuffer_t>& icf,    // input coefficients [Grp][Cout][Cin], 8b only
    const tensor_t<coef_t, 1, xbuffer_t>& izp,    // input zero-points [Grp*Cout]
    // outputs, buffers preallocated by caller
    conv_params_impl_coef<xbuffer_t>& obuf,       // output encoded coefficients NOLINT [runtime/references]
    xbuffer_t<coef_t>& tbuf           // allocator for temporary buffers NOLINT [runtime/references]
    ) {
  size_t l;
  npu_conv::coef_enc(
      icf,                 // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
      izp,                 // input zero-points [Cout]
      tbuf,
      TNSVSIZE,
      impl_spec.cf_mode,   // coefficient compression mode uncompressed or compressed or sparse
      fm_tp==fm_cfg_16b_e,  // 16b feature-map
      cf_tp==cf_cfg_4b_zp_e,  // 4b coefficient encoding
      obuf.cbuf,           // output encoded coefficient tensor
      l);                  // size of used coefficient buffer in bytes
  // reduce the buffer size
  obuf.cbuf.set_size(l);
}

// coefficient encoding function, supporting FP16 only
template<template<typename> class B>
void fc_params<B>::coef_enc(
    const tensor_t<fp_e5m10_t,3,xbuffer_t>& icf,  // input coefficients [Grp][Cout][Cin], FP16
    // outputs, buffers preallocated by caller
    conv_params_impl_coef<xbuffer_t>&       obuf, // output encoded coefficients NOLINT [runtime/references]
    xbuffer_t<coef_t>&                      tbuf  // temporary buffer NOLINT [runtime/references]
    ) {
  assert(cf_tp == cf_cfg_fp16_e);
  tensor_t<coef_t,3,xbuffer_t> tcf = static_cast<tensor_t<coef_t,3,xbuffer_t> >(icf);
  size_t l;
  npu_conv::coef_enc(
      tcf.split(0,icf.get_dim(0)), // input coefficients [Grp][Cout/Grp][Cin/Grp][h/l]
      tbuf,                        // temp buffer
      TNSVSIZE,
      true,                        // 16b
      obuf.cbuf,                   // output encoded coefficient tensor
      l);                          // size of used coefficient buffer in bytes
  // reduce the buffer size
  obuf.cbuf.set_size(l);
}

// coefficient encoding function, supporting FP16 only
template<template<typename> class B>
void fc_params<B>::coef_enc(
    const tensor_t<fp_e8m7_t,3,xbuffer_t>& icf,   // input coefficients [Grp][Cout][Cin], BF16
    // outputs, buffers preallocated by caller
    conv_params_impl_coef<xbuffer_t>&      obuf,  // output encoded coefficients NOLINT [runtime/references]
    xbuffer_t<coef_t>&                     tbuf   // temporary buffer NOLINT [runtime/references]
    ) {
  assert(cf_tp == cf_cfg_bf16_e);
  tensor_t<coef_t,3,xbuffer_t> tcf = static_cast<tensor_t<coef_t,3,xbuffer_t> >(icf);
  size_t l;
  npu_conv::coef_enc(
      tcf.split(0,icf.get_dim(0)), // input coefficients [Grp][Cout/Grp][Cin/Grp][h/l]
      tbuf,                        // temp buffer
      TNSVSIZE,
      true,                        // 16b
      obuf.cbuf,                   // output encoded coefficient tensor
      l);                          // size of used coefficient buffer in bytes
  // reduce the buffer size
  obuf.cbuf.set_size(l);
}
}  // namespace tensor::v200
#undef LDBGV
#endif  // NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_FC_INLINE_HPP_
