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

#ifndef NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_CONV_INLINE_HPP_
#define NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_CONV_INLINE_HPP_

// #define TENSOR_CONV_INLINE_HPP_DEBUG
#ifdef TENSOR_CONV_INLINE_HPP_DEBUG
  #define LDBGV(...) DBGV(__VA_ARGS__)
#else
  #define LDBGV(...)
#endif

// All identifiers related to the tensor API go into namespace tensor::v200
namespace tensor::v200 {

//////////////////////////////////////////////////////////////////////////////////
//
// Inline methods for the convolution parameter object used by the AOT/JIT compiler
//
//////////////////////////////////////////////////////////////////////////////////
//
// constructors
//
template<template<typename> class B>
conv_params<B>::conv_params(
              aoffset_t                 grpi,      // number of groups in convolution
              aoffset_t                 nii,       // number input channels (not vectors), in units of 8b or 16b feature-map pixels
              aoffset_t                 noi,       // number output channels (not vectors)
              const shape<3>&           oshpi,     // output shape, indexed by spatial_axis_t
              const shape<3>&           filteri,   // filter dimension, indexed by spatial_axis_t
              const shape<3>&           stridei,   // filter stride, indexed by spatial_axis_t
              const shape<3>&           dili,      // filter dilation, indexed by spatial_axis_t
              const shape<3>&           padlimi,   // right&bottom limit of padding window, indexed by spatial_axis_t
              bool                      use_acci,  // use input accumulator
              bool                      keep_acci, // keep output accumulator
              fm_cfg_t                  fm_tpi,    // feature-map type: fm_cfg_8b_e, fm_cfg_16b_e, fm_cfg_bf16_e, fm_cfg_fp16_e
              cf_cfg_t                  cf_tpi,    // coefficient type: cf_cfg_4b_zp_e, cf_cfg_4b_nozp_e, cf_cfg_8b_zp_e,
                                                   // cf_cfg_8b_nozp_e, cf_cfg_16b_e, cf_cfg_bf16_e, cf_cfg_fp16_e
              pack_mode_t               pcki
              ) : conv_base<B>() {
  assert((fm_tpi == fm_cfg_bf16_e && cf_tpi == cf_cfg_bf16_e) ||
         (fm_tpi == fm_cfg_fp16_e && cf_tpi == cf_cfg_fp16_e) ||
         (fm_tpi != fm_cfg_bf16_e && cf_tpi != cf_cfg_bf16_e && fm_tpi != fm_cfg_fp16_e && cf_tpi != cf_cfg_fp16_e));

  // copy parameters into object
  grp      = grpi;
  ni       = nii;
  no       = noi;
  oshp     = oshpi;
  filter   = filteri;
  stride   = stridei;
  dil      = dili;
  padlim   = padlimi;
  use_acc  = use_acci;
  keep_acc = keep_acci;
  fm_tp    = fm_tpi;
  cf_tp    = cf_tpi;
  pck      = pcki;

  set_default_params();
}

// legacy constructor
template<template<typename> class B>
conv_params<B>::conv_params(
              aoffset_t                 grpi,      // number of groups in convolution
              aoffset_t                 nii,       // number input channels per group, in units of 8b or 16b feature-map pixels
              aoffset_t                 noi,       // number output channels per group
              const shape<3>&           oshpi,     // output shape
              const shape<3>&           filteri,   // filter dimension
              const shape<3>&           stridei,   // filter stride
              const shape<3>&           dili,      // filter dilation
              const shape<3>&           padlimi,   // right&bottom limit of padding window
              bool                      use_acci,  // use input accumulator
              bool                      keep_acci, // keep output accumulator
              bool                      fm_dbli,   // 8b or 16b feature-maps
              bool                      cf_dbli,   // 8b or 16b coefficients
              bool                      cf_zpi     // coefficients include a zero-point
              ) : conv_base<B>() {
  // copy parameters into object
  grp      = grpi;
  ni       = nii;
  no       = noi;
  oshp     = oshpi;
  filter   = filteri;
  stride   = stridei;
  dil      = dili;
  padlim   = padlimi;
  use_acc  = use_acci;
  keep_acc = keep_acci;
  fm_tp    = fm_dbli ? fm_cfg_16b_e : fm_cfg_8b_e;
  cf_tp    = cf_dbli ? cf_cfg_16b_e : (cf_zpi ? cf_cfg_8b_zp_e: cf_cfg_8b_nozp_e);
  pck      = pack_mode_i16_e;
  set_default_params();
}

template<template<typename> class B>
void conv_params<B>::set_default_params() {
  // select default implementation
  impl_spec.cf_4b     = 0;
  impl_spec.cf_mode   = coef_mode_uncompressed;
  impl_spec.inn       = 1;
  impl_spec.onn       = 1;
  impl_spec.conv_mode = DINO(conv_mode_1x1);
  int dni = (fm_tp == fm_cfg_16b_e) || (fm_tp == fm_cfg_bf16_e) || (fm_tp == fm_cfg_fp16_e) ? 2*ni : ni;
  switch (pck) {
  case pack_mode_i4_e: pck_mpy = 4;  break;
  case pack_mode_i8_e: pck_mpy = 2;  break;
  default:             pck_mpy = 1;  break;
  }

  if (ni == 1 && no == 1) {
    // depthwise
    if (filter[SPATIAL_H] == 1 && stride[SPATIAL_W] == 1 && dil[SPATIAL_W] == 1) {
      if (TNSVSIZE == 2) {
        impl_spec.conv_mode = NINO(conv_mode_4x1dws1);
      } else {
        impl_spec.conv_mode = NINO(conv_mode_8x1dws1);
      }
    } else if (stride[SPATIAL_W] == 2 && stride[SPATIAL_H] == 2) {
      impl_spec.conv_mode = NINO(conv_mode_2x3dws2);
    } else if (stride[SPATIAL_W] == 1 && stride[SPATIAL_H] == 1 &&
               dil[SPATIAL_W] == 2 && dil[SPATIAL_H] == 2) {
      impl_spec.conv_mode = NINO(conv_mode_3x3dws1dl2);
    } else if (stride[SPATIAL_W] == 1 && stride[SPATIAL_H] == 1 &&
               dil[SPATIAL_W] == 1 && dil[SPATIAL_H] == 1) {
      impl_spec.conv_mode = NINO(conv_mode_3x3dws1);
    } else {
      // emulate using normal convolution
      impl_spec.conv_mode = DINO(conv_mode_1x1);
    }
  } else if ((grp != 1) && (ni == 8) && (no == 8) &&
             (fm_tp != fm_cfg_16b_e) && (cf_tp != cf_cfg_16b_e) &&
             (fm_tp != fm_cfg_bf16_e) && (fm_tp != fm_cfg_fp16_e) &&
             ((dil[SPATIAL_W] == 1 && stride[SPATIAL_W] == 1) ||
              (dil[SPATIAL_W] == 2 && stride[SPATIAL_W] == 1) ||
              (dil[SPATIAL_W] == 1 && stride[SPATIAL_W] == 2))) {
    // grouped convolution with group size smaller than or equal 8
    if (dil[SPATIAL_W] == 2) {
      impl_spec.conv_mode = NINO(conv_mode_4x1g2s1dl2);
    } else if (stride[SPATIAL_W] == 2) {
      impl_spec.conv_mode = NINO(conv_mode_2x1g2s2);
    } else {
      impl_spec.conv_mode = NINO(conv_mode_4x1g2s1);
    }
  } else if ((((grp == 1) && (dni <= ISIZE)) || ((grp != 1) && ((ni % ISIZE) == 0) && ((ni % (2*ISIZE)) != 0) && (no == ni))) &&
             ((dil[SPATIAL_W] == 1 && stride[SPATIAL_W] == 1) ||
              (dil[SPATIAL_W] == 2 && stride[SPATIAL_W] == 1) ||
              (dil[SPATIAL_W] == 1 && stride[SPATIAL_W] == 2))) {
    // 2x1i16o16 convolution
    if (dil[SPATIAL_W] == 2) {
      impl_spec.conv_mode = NINO(conv_mode_2x1s1dl2);
    } else if (stride[SPATIAL_W] == 2) {
      impl_spec.conv_mode = NINO(conv_mode_2x1s2);
    } else {
      impl_spec.conv_mode = NINO(conv_mode_2x1s1);
    }
  } else if ((grp == 1) && (ni <= ISIZE) && (fm_tp != fm_cfg_16b_e) && (cf_tp != cf_cfg_16b_e) &&
             (fm_tp != fm_cfg_bf16_e) && (fm_tp != fm_cfg_fp16_e)) {
    // 1x1i16o16 convolution
    impl_spec.conv_mode = NINO(conv_mode_1x1);
  } else {
    // 1x1i32o16 convolution
    impl_spec.inn = 1;
    impl_spec.onn = 1;
    if (grp == 1) {
      if (ni > (2*ISIZE) && (cf_tp != cf_cfg_16b_e) && (fm_tp != fm_cfg_16b_e) &&
          (fm_tp != fm_cfg_bf16_e) && (fm_tp != fm_cfg_fp16_e)) {
        impl_spec.inn = 2;
      } else if (no > ISIZE && (cf_tp != cf_cfg_16b_e) && (fm_tp != fm_cfg_16b_e) &&
                 (fm_tp != fm_cfg_bf16_e) && (fm_tp != fm_cfg_fp16_e)) {
        impl_spec.onn = 2;
      }
    } else if (((ni % (2*ISIZE)) == 0) && (no == ni) &&
               (fm_tp != fm_cfg_16b_e) && (cf_tp != cf_cfg_16b_e) &&
               (fm_tp != fm_cfg_bf16_e) && (fm_tp != fm_cfg_fp16_e)) {
      // i32o32 int8 grouped convolution
      impl_spec.onn = 2;
    } // else emulate grouped convolution using full 1x1 convlution
  }
}


//
// Derive shapes based on implementation settings
//
template<template<typename> class B>
void conv_params<B>::get_shapes(conv_params_impl_shapes& s) {  // NOLINT [runtime/references]
  // set HLAPI attributes
  if (impl_spec.cf_4b) {
    if (cf_tp == cf_cfg_8b_zp_e) {
      cf_tp = cf_cfg_4b_zp_e;
    } else if (cf_tp == cf_cfg_8b_nozp_e) {
      cf_tp = cf_cfg_4b_nozp_e;
    }
  }

  hlapi.i.bf = (((uint32_t)impl_spec.conv_mode) << CONV_BF_CONV_MODE_START) |
    (((uint32_t)impl_spec.cf_mode) << CONV_BF_CF_MODE_START)   |
    (((uint32_t)fm_tp)     << CONV_BF_FM_CFG_START)    |
    (((uint32_t)cf_tp)     << CONV_BF_CF_CFG_START)    |
    (((uint32_t)use_acc)   << CONV_BF_USE_ACC_START)   |
    (((uint32_t)keep_acc)  << CONV_BF_KEEP_ACC_START)  |
    (((uint32_t)pck)       << CONV_BF_PACK_MODE_START);
  hlapi.i.fm_padlim   = padlim;
  // derived shapes by rounding
  int iw   = 1+(oshp[SPATIAL_W]-1)*stride[SPATIAL_W]+(filter[SPATIAL_W]-1)*dil[SPATIAL_W];
  int ih   = 1+(oshp[SPATIAL_H]-1)*stride[SPATIAL_H]+(filter[SPATIAL_H]-1)*dil[SPATIAL_H];
  int id   = 1+(oshp[SPATIAL_D]-1)*stride[SPATIAL_D]+(filter[SPATIAL_D]-1)*dil[SPATIAL_D];
  int ow   = RDIV_UP(oshp[SPATIAL_W], TNSVSIZE);
  //int ft_dil = 1;
  bool fm_dbl = (fm_tp == fm_cfg_16b_e) || (fm_tp == fm_cfg_bf16_e) || (fm_tp == fm_cfg_fp16_e);
  bool cf_dbl = (cf_tp == cf_cfg_16b_e) || (cf_tp == cf_cfg_bf16_e) || (cf_tp == cf_cfg_fp16_e);
  bool odbl   = (fm_tp == fm_cfg_16b_e) && (cf_tp == cf_cfg_16b_e);
  switch (impl_spec.conv_mode) {
  case NINO(conv_mode_3x3dws1):
  case NINO(conv_mode_3x3dws1dl2):
  case NINO(conv_mode_2x3dws2):
  case NINO(conv_mode_8x1dws1):
  case NINO(conv_mode_4x1dws1):
    impl_spec.onn = 1;
    impl_spec.inn = 1;
    shapes.ishape = {   // ixpix_t [dep][row][col][grp][chn]
      (aoffset_t)(fm_dbl ? 2 : 1),
      (aoffset_t)RDIV_UP(grp, ISIZE),
      (aoffset_t)iw,
      (aoffset_t)ih,
      (aoffset_t)id
    };
    shapes.oshape = {   // vyixacc_t [chn][dep][col][row][msb/lsb/onn]
      (aoffset_t)(odbl ? 2 : 1),
      oshp[SPATIAL_H],
      (aoffset_t)ow,
      oshp[SPATIAL_D],
      (aoffset_t)((use_acc|keep_acc) ? RDIV_UP(grp, ISIZE) : 1)
    };
    break;
  case NINO(conv_mode_2x1g2s2):
  case NINO(conv_mode_4x1g2s1dl2):
  case NINO(conv_mode_4x1g2s1):
    impl_spec.onn = 1;
    impl_spec.inn = 1;
    shapes.ishape = {   // ixpix_t [dep][row][col][grp][chn]
      (aoffset_t)1,
      (aoffset_t)RDIV_UP(grp, 2),
      (aoffset_t)iw,
      (aoffset_t)ih,
      (aoffset_t)id
    };
    shapes.oshape = {   // vyixacc_t [chn][dep][col][row][msb/lsb/onn]
      (aoffset_t)1,
      oshp[SPATIAL_H],
      (aoffset_t)ow,
      oshp[SPATIAL_D],
      (aoffset_t)((use_acc|keep_acc) ? RDIV_UP(grp, 2) : 1),
    };
    break;
  case NINO(conv_mode_2x1s1):
  case NINO(conv_mode_2x1s1dl2):
  case NINO(conv_mode_2x1s2):
    impl_spec.onn = 1;
    impl_spec.inn = 1;
    shapes.ishape = {   // ixpix_t [dep][row][col[chn]
      (aoffset_t)(fm_dbl ? RDIV_UP(ni, ISIZE/2) : RDIV_UP(ni, ISIZE)),
      (aoffset_t)grp,
      (aoffset_t)iw,
      (aoffset_t)ih,
      (aoffset_t)id
    };
    shapes.oshape = {   // vyixacc_t [chn][dep][col][row][msb/lsb/onn]
      (aoffset_t)((odbl || (impl_spec.onn != 1)) ? 2 : 1),
      oshp[SPATIAL_H],
      (aoffset_t)ow,
      oshp[SPATIAL_D],
      (aoffset_t)((use_acc|keep_acc)?grp*RDIV_UP(no, impl_spec.onn*ISIZE):1),
    };
    break;
  default: // DINO(1x1), NINO(1x1)
    shapes.ishape = {   // ixpix_t [dep][row][col[chn]
      (aoffset_t)(fm_dbl ? 2*RDIV_UP(ni, ISIZE) : RDIV_UP(ni, ISIZE)),
      (aoffset_t)grp,
      (aoffset_t)iw,
      (aoffset_t)ih,
      (aoffset_t)id
    };
    shapes.oshape = {   // vyixacc_t [chn][dep][col][row][msb/lsb/onn]
      (aoffset_t)((odbl || (impl_spec.onn != 1) || (impl_spec.cf_mode == coef_mode_sparse)) ? 2 : 1),
      oshp[SPATIAL_H],
      (aoffset_t)ow,
      oshp[SPATIAL_D],
      (aoffset_t)((use_acc|keep_acc)? ((impl_spec.cf_mode == coef_mode_sparse) ?
                                       RDIV_UP(grp*no, 2*ISIZE) :
                                       RDIV_UP(grp*no, impl_spec.onn*ISIZE)) : 1),
    };
    break;
  }
  // padding shape
  shapes.pshape = {   // ixpix_t [chn]
    (aoffset_t)(shapes.ishape[0] * shapes.ishape[1])
  };
  // derive number of quadrants and worst-case coefficient buffer size
  int qd;
  int reduce_ni = ((fm_tp == fm_cfg_16b_e) || (fm_tp == fm_cfg_bf16_e) || (fm_tp == fm_cfg_fp16_e)) ? 2 : 1;
  int ic   = grp*RDIV_UP(ni, ISIZE);
  int oc   = grp*RDIV_UP(no, ISIZE);
  int gp   = RDIV_UP(grp, ISIZE);
  switch (impl_spec.conv_mode) {
  case DINO(conv_mode_1x1):
  case NINO(conv_mode_1x1):
    qd = {(aoffset_t)(filter[SPATIAL_W]*filter[SPATIAL_H]*filter[SPATIAL_D])};
    if (impl_spec.conv_mode == DINO(conv_mode_1x1)) {
      if (impl_spec.cf_mode == coef_mode_sparse) {
        // sparse mode, use dual input
        impl_spec.inn = 2;
        impl_spec.onn = 1;
      }
      if (grp != 0 && impl_spec.onn == 2) {
        // grouped, groupsize multiples of i32o32
        hlapi.i.iter[CONV_ITER_GRP] = grp;
        hlapi.i.iter[CONV_ITER_NO]  = RDIV_UP(no, 2*ISIZE);
        hlapi.i.iter[CONV_ITER_NI]  = RDIV_UP(ni, 2*ISIZE);
        hlapi.i.iter[CONV_ITER_QD]  = qd;
        hlapi.i.iter[CONV_ITER_COL] = RDIV_UP(oshp[SPATIAL_W], TNSVSIZE);
        hlapi.i.iter[CONV_ITER_ROW] = oshp[SPATIAL_H];
        hlapi.i.iter[CONV_ITER_INN] = 1;
        hlapi.i.iter[CONV_ITER_ONN] = 2;
        hlapi.i.cf_iter[CONV_CF_ITER_GRP] = grp;
        hlapi.i.cf_iter[CONV_CF_ITER_NO]  = hlapi.i.iter[CONV_ITER_NO];
        hlapi.i.cf_iter[CONV_CF_ITER_NI]  = hlapi.i.iter[CONV_ITER_NI];
        shapes.cshape = 4*ISIZE*ISIZE*
          hlapi.i.iter[CONV_ITER_GRP]*
          hlapi.i.cf_iter[CONV_CF_ITER_NO]*
          hlapi.i.cf_iter[CONV_CF_ITER_NI]*
          hlapi.i.iter[CONV_ITER_QD];
      } else {
        // normal 1x1 convolution
        hlapi.i.iter[CONV_ITER_GRP] = 1;
        hlapi.i.iter[CONV_ITER_NO]  = (impl_spec.cf_mode == coef_mode_sparse) ?
          RDIV_UP(grp*no, 2*ISIZE) : RDIV_UP(grp*no, impl_spec.onn*ISIZE);
        hlapi.i.iter[CONV_ITER_NI]  = RDIV_UP(grp*ni, (fm_dbl?1:2*impl_spec.inn)*ISIZE);
        hlapi.i.iter[CONV_ITER_QD]  = qd;
        hlapi.i.iter[CONV_ITER_COL] = RDIV_UP(oshp[SPATIAL_W], TNSVSIZE);
        hlapi.i.iter[CONV_ITER_ROW] = oshp[SPATIAL_H];
        hlapi.i.iter[CONV_ITER_INN] = impl_spec.inn;
        hlapi.i.iter[CONV_ITER_ONN] = impl_spec.onn;
        hlapi.i.cf_iter[CONV_CF_ITER_GRP] = 1;
        hlapi.i.cf_iter[CONV_CF_ITER_NO]  = hlapi.i.iter[CONV_ITER_NO];
        hlapi.i.cf_iter[CONV_CF_ITER_NI]  = RDIV_UP(grp*ni, (2*impl_spec.inn*ISIZE));
        shapes.cshape = (cf_dbl?2:1)*2*ISIZE*ISIZE*
          hlapi.i.iter[CONV_ITER_GRP]*
          hlapi.i.cf_iter[CONV_CF_ITER_NO]*
          hlapi.i.cf_iter[CONV_CF_ITER_NI]*
          hlapi.i.iter[CONV_ITER_QD]*
          hlapi.i.iter[CONV_ITER_INN]*
          hlapi.i.iter[CONV_ITER_ONN];
      }
    } else {
      int nn =  impl_spec.inn;
      int nni = ROUND_UP(ic, nn)            * ISIZE;  // nn*((ic+nn-1)/nn)*ISIZE;
      int nno = ROUND_UP(oc, impl_spec.onn) * ISIZE;
                      // impl_spec.onn*((oc+impl_spec.onn-1)/impl_spec.onn)*ISIZE;
      shapes.cshape = nni*nno*qd*(cf_dbl?2:1)/grp;
      hlapi.i.iter[CONV_ITER_GRP] = grp;
      hlapi.i.iter[CONV_ITER_NO]  = (no+impl_spec.onn*ISIZE-1)/(impl_spec.onn*ISIZE);
      hlapi.i.iter[CONV_ITER_NI]  = (ni+impl_spec.inn*ISIZE-1)/(impl_spec.inn*ISIZE);
      hlapi.i.iter[CONV_ITER_QD]  = qd;
      hlapi.i.iter[CONV_ITER_COL] = (oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
      hlapi.i.iter[CONV_ITER_ROW] = oshp[SPATIAL_H];
      hlapi.i.iter[CONV_ITER_INN] = impl_spec.inn;
      hlapi.i.iter[CONV_ITER_ONN] =
        impl_spec.cf_mode == coef_mode_sparse ? (impl_spec.onn/2) : impl_spec.onn;
      hlapi.i.cf_iter[CONV_CF_ITER_NI]  =
        (ni+impl_spec.inn*ISIZE-1)/(impl_spec.inn*ISIZE)*impl_spec.inn;
      hlapi.i.cf_iter[CONV_CF_ITER_NO]  =
        (no+impl_spec.onn*ISIZE-1)/(impl_spec.onn*ISIZE)*impl_spec.onn;
      hlapi.i.cf_iter[CONV_CF_ITER_GRP] = grp;
    }
    if (cf_tp == cf_cfg_4b_zp_e || cf_tp == cf_cfg_4b_nozp_e) {
      shapes.cshape /= 2;  // only need half the coefficients for encoding in 4b mode
    }
    switch (impl_spec.cf_mode) {
      case coef_mode_sparse:
        // need 10b to encode coef of 8b
        shapes.cshape = ((((10*shapes.cshape+7)/8)+7)/8+15)/16*16*8;
        break;
      case coef_mode_compressed:
        // need 9b to encode coef of 8b
        shapes.cshape = ((((9*shapes.cshape+7)/8)+7)/8+15)/16*16*8;
        break;
      default:
        // need 8b to encode
        break;
    }
    if (cf_tp == cf_cfg_8b_zp_e || cf_tp == cf_cfg_4b_zp_e) {
      // add per channel zero-points
      shapes.cshape += NRND_UP(grp*no, ISIZE*impl_spec.onn);
    }
    hlapi.i.cf_iter[CONV_CF_ITER_IN]  = RDIV_UP(shapes.cshape,
                                                hlapi.i.cf_iter[CONV_CF_ITER_NI]*
                                                hlapi.i.cf_iter[CONV_CF_ITER_NO]*
                                                hlapi.i.cf_iter[CONV_CF_ITER_GRP]*
                                                TNSVSIZE*ISIZE);  /* align to v8i16pix_t */
    shapes.cshape = NRND_UP(shapes.cshape, ISIZE*TNSVSIZE);
    break;
  case NINO(conv_mode_2x3dws2):
    qd = { (aoffset_t)(((dil[SPATIAL_W]*filter[SPATIAL_W]+1)/2)*
                                  ((dil[SPATIAL_H]*filter[SPATIAL_H]+2)/3)*
                                  filter[SPATIAL_D]) };
    shapes.cshape = ROUND_UP(grp, ISIZE)*qd*(cf_dbl?2:1)*8;
    hlapi.i.iter[CONV_ITER_GRP] = RDIV_UP(grp, ISIZE);
    hlapi.i.iter[CONV_ITER_NO]  = 1;
    hlapi.i.iter[CONV_ITER_NI]  = 1;
    hlapi.i.iter[CONV_ITER_QD]  = qd;
    hlapi.i.iter[CONV_ITER_COL] = (oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
    hlapi.i.iter[CONV_ITER_ROW] = oshp[SPATIAL_H];
    hlapi.i.iter[CONV_ITER_INN] = impl_spec.inn;
    hlapi.i.iter[CONV_ITER_ONN] = impl_spec.onn;
    hlapi.i.cf_iter[CONV_CF_ITER_NI]  = 1;
    hlapi.i.cf_iter[CONV_CF_ITER_NO]  = 1;
    hlapi.i.cf_iter[CONV_CF_ITER_GRP] = RDIV_UP(grp, ISIZE);
    switch (impl_spec.cf_mode) {
      case coef_mode_compressed:
        // need 9b to encode coef of 8b
        shapes.cshape = ((((8*shapes.cshape+(shapes.cshape/12*16)+7)/8)+7)/8+15)/16*16*8;
        break;
      default:
        // need 8b to encode
        break;
    }
    if (cf_tp == cf_cfg_8b_zp_e || cf_tp == cf_cfg_4b_zp_e) {
      // add per channel zero-points
      shapes.cshape += gp*ISIZE;
    }
    hlapi.i.cf_iter[CONV_CF_ITER_IN]  = ((shapes.cshape*9/6)/(hlapi.i.cf_iter[CONV_CF_ITER_NI]
       *hlapi.i.cf_iter[CONV_CF_ITER_NO]*hlapi.i.cf_iter[CONV_CF_ITER_GRP])+TNSVSIZE*ISIZE-1)/(TNSVSIZE*ISIZE); /*v8i16pix_t*/
    break;
  case NINO(conv_mode_8x1dws1):
    qd = { (aoffset_t)(((dil[SPATIAL_W]*filter[SPATIAL_W]+7)/8)*
                       ((dil[SPATIAL_H]*filter[SPATIAL_H]+0)/1)*
                         filter[SPATIAL_D]) };
    shapes.cshape = ROUND_UP(grp, ISIZE)*qd*(cf_dbl?2:1)*8;
    hlapi.i.iter[CONV_ITER_GRP] = RDIV_UP(grp, ISIZE);
    hlapi.i.iter[CONV_ITER_NO]  = 1;
    hlapi.i.iter[CONV_ITER_NI]  = 1;
    hlapi.i.iter[CONV_ITER_QD]  = qd;
    hlapi.i.iter[CONV_ITER_COL] = (oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
    hlapi.i.iter[CONV_ITER_ROW] = oshp[SPATIAL_H];
    hlapi.i.iter[CONV_ITER_INN] = impl_spec.inn;
    hlapi.i.iter[CONV_ITER_ONN] = impl_spec.onn;
    hlapi.i.cf_iter[CONV_CF_ITER_NI]  = 1;
    hlapi.i.cf_iter[CONV_CF_ITER_NO]  = 1;
    hlapi.i.cf_iter[CONV_CF_ITER_GRP] = RDIV_UP(grp, ISIZE);
    switch (impl_spec.cf_mode) {
      case coef_mode_compressed:
        // need 9b to encode coef of 8b
        shapes.cshape = ((((9*shapes.cshape+7)/8)+7)/8+15)/16*16*8;
        break;
      default:
        // need 8b to encode
        break;
    }
    if (cf_tp == cf_cfg_8b_zp_e || cf_tp == cf_cfg_4b_zp_e) {
      // add per channel zero-points
      shapes.cshape += gp*ISIZE;
    }
    hlapi.i.cf_iter[CONV_CF_ITER_IN]  = (shapes.cshape/(hlapi.i.cf_iter[CONV_CF_ITER_NI]
      *hlapi.i.cf_iter[CONV_CF_ITER_NO]*hlapi.i.cf_iter[CONV_CF_ITER_GRP])+TNSVSIZE*ISIZE-1)/(TNSVSIZE*ISIZE); /*v8i16pix_t*/
    break;
  case NINO(conv_mode_4x1dws1):
      qd = { (aoffset_t)(((dil[SPATIAL_W]*filter[SPATIAL_W]+3)/4)*
                       ((dil[SPATIAL_H]*filter[SPATIAL_H]+0)/1)*
                         filter[SPATIAL_D]) };
    shapes.cshape = grp*qd*(cf_dbl?2:1)*8;
    hlapi.i.iter[CONV_ITER_GRP] = (grp+ISIZE-1)/ISIZE;
    hlapi.i.iter[CONV_ITER_NO]  = 1;
    hlapi.i.iter[CONV_ITER_NI]  = 1;
    hlapi.i.iter[CONV_ITER_QD]  = qd;
    hlapi.i.iter[CONV_ITER_COL] = (oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
    hlapi.i.iter[CONV_ITER_ROW] = oshp[SPATIAL_H];
    hlapi.i.iter[CONV_ITER_INN] = impl_spec.inn;
    hlapi.i.iter[CONV_ITER_ONN] = impl_spec.onn;
    hlapi.i.cf_iter[CONV_CF_ITER_NI]  = 1;
    hlapi.i.cf_iter[CONV_CF_ITER_NO]  = 1;
    hlapi.i.cf_iter[CONV_CF_ITER_GRP] = (grp+ISIZE-1)/ISIZE;
    switch (impl_spec.cf_mode) {
    case coef_mode_compressed: shapes.cshape = ((((9*shapes.cshape+3)/4)+3)/4+15)/16*16*8;    break; // need 9b to encode coef of 8b
    default:                                                                break; // need 8b to encode
    }
    if (cf_tp == cf_cfg_8b_zp_e || cf_tp == cf_cfg_4b_zp_e) {
      // add per channel zero-points
      shapes.cshape += gp*ISIZE;
    }
    hlapi.i.cf_iter[CONV_CF_ITER_IN]  = (shapes.cshape/(hlapi.i.cf_iter[CONV_CF_ITER_NI]*hlapi.i.cf_iter[CONV_CF_ITER_NO]*hlapi.i.cf_iter[CONV_CF_ITER_GRP])+TNSVSIZE*ISIZE-1)/(TNSVSIZE*ISIZE); /*v8i16pix_t*/
    break;
  case NINO(conv_mode_2x1s1):
  case NINO(conv_mode_2x1s1dl2):
  case NINO(conv_mode_2x1s2): {
      qd = {(aoffset_t)(((filter[SPATIAL_W]+1)/2)*filter[SPATIAL_H]*filter[SPATIAL_D])};

      int l_2x1_nni = ROUND_UP(ni, impl_spec.inn*ISIZE);  // ni*i16
      int l_2x1_nno = ROUND_UP(no, impl_spec.onn*ISIZE);  // no*i16
      int l_2x1_ksz = 2*1;
      shapes.cshape = l_2x1_nni*l_2x1_nno*qd*l_2x1_ksz*(cf_dbl?2:1)*grp;

      hlapi.i.iter[CONV_ITER_GRP] = grp;
      hlapi.i.iter[CONV_ITER_NO]  = RDIV_UP(no, impl_spec.onn*ISIZE);
      hlapi.i.iter[CONV_ITER_NI]  = RDIV_UP(ni, impl_spec.inn*ISIZE/reduce_ni);
      hlapi.i.iter[CONV_ITER_QD]  = qd;
      hlapi.i.iter[CONV_ITER_COL] = RDIV_UP(oshp[SPATIAL_W], TNSVSIZE);
      hlapi.i.iter[CONV_ITER_ROW] = oshp[SPATIAL_H];
      hlapi.i.iter[CONV_ITER_INN] = impl_spec.inn;
      hlapi.i.iter[CONV_ITER_ONN] = impl_spec.onn;
      hlapi.i.cf_iter[CONV_CF_ITER_NI]  = RDIV_UP(ni, impl_spec.inn*ISIZE)*impl_spec.inn;
      hlapi.i.cf_iter[CONV_CF_ITER_NO]  = RDIV_UP(no, impl_spec.onn*ISIZE)*impl_spec.onn;
      hlapi.i.cf_iter[CONV_CF_ITER_GRP] = grp;
      switch (impl_spec.cf_mode) {
      case coef_mode_sparse:
        // need 10b to encode coef of 8b
        shapes.cshape = ((((10*shapes.cshape+7)/8)+7)/8+15)/16*16*8;
        break;
      case coef_mode_compressed:
        // need 9b to encode coef of 8b
        shapes.cshape = ((((9*shapes.cshape+7)/8)+7)/8+15)/16*16*8;
        break;
      default:
        // need 8b to encode
        break;
      }
      if (cf_tp == cf_cfg_8b_zp_e || cf_tp == cf_cfg_4b_zp_e) {
        // add per channel zero-points
        shapes.cshape += l_2x1_nno*grp;
      }

      hlapi.i.cf_iter[CONV_CF_ITER_IN]  = (shapes.cshape/(hlapi.i.cf_iter[CONV_CF_ITER_NI]
        *hlapi.i.cf_iter[CONV_CF_ITER_NO]*hlapi.i.cf_iter[CONV_CF_ITER_GRP])+TNSVSIZE*ISIZE-1)/(TNSVSIZE*ISIZE); /*v8i16pix_t*/
    }
    break;
  case NINO(conv_mode_3x3dws1):
  case NINO(conv_mode_3x3dws1dl2):
    qd = { (aoffset_t)(((dil[SPATIAL_W]*filter[SPATIAL_W]+2)/(dil[SPATIAL_W]*3))*
                       ((dil[SPATIAL_H]*filter[SPATIAL_H]+2)/(dil[SPATIAL_H]*3))*
                         filter[SPATIAL_D]) };
    // shapes.cshape = (((gp*9)+7)/8)*qd*(cf_dbl?2:1)*8*ISIZE;
    shapes.cshape = gp*qd*9*(cf_dbl?2:1)*ISIZE;
    if (impl_spec.cf_4b) shapes.cshape = NRND_UP(shapes.cshape/2, ISIZE*NUM_COEF_QUEUE);

    shapes.cshape = NRND_UP(shapes.cshape, ISIZE*TNSVSIZE);

    hlapi.i.iter[CONV_ITER_GRP] = RDIV_UP(grp, ISIZE);
    hlapi.i.iter[CONV_ITER_NO]  = 1;
    hlapi.i.iter[CONV_ITER_NI]  = 1;
    hlapi.i.iter[CONV_ITER_QD]  = qd;
    hlapi.i.iter[CONV_ITER_COL] = (oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
    hlapi.i.iter[CONV_ITER_ROW] = oshp[SPATIAL_H];
    hlapi.i.iter[CONV_ITER_INN] = impl_spec.inn;
    hlapi.i.iter[CONV_ITER_ONN] = impl_spec.onn;
    hlapi.i.cf_iter[CONV_CF_ITER_NI]  = 1;
    hlapi.i.cf_iter[CONV_CF_ITER_NO]  = 1;
    hlapi.i.cf_iter[CONV_CF_ITER_GRP] = RDIV_UP(grp, ISIZE);
    switch (impl_spec.cf_mode) {
      case coef_mode_compressed:
        // need 9b to encode coef of 8b
        shapes.cshape = ((((9*shapes.cshape+7)/8)+7)/8+15)/16*16*8;
        break;
      default:
        // need 8b to encode
        break;
    }
    if (cf_tp == cf_cfg_8b_zp_e || cf_tp == cf_cfg_4b_zp_e) {
      // add per channel zero-points
      shapes.cshape += gp*ISIZE;
    }
    hlapi.i.cf_iter[CONV_CF_ITER_IN]  = (shapes.cshape/(hlapi.i.cf_iter[CONV_CF_ITER_NI]
      *hlapi.i.cf_iter[CONV_CF_ITER_NO]*hlapi.i.cf_iter[CONV_CF_ITER_GRP])+TNSVSIZE*ISIZE-1)/(TNSVSIZE*ISIZE); /*v8i16pix_t*/
    break;
  case NINO(conv_mode_4x1g2s1dl2):
  case NINO(conv_mode_4x1g2s1):
    //assert((1==impl_spec.inn*impl_spec.onn) && (grp==2)) ;
    qd = {(aoffset_t)(((filter[SPATIAL_W]+3)/4)*filter[SPATIAL_H]*filter[SPATIAL_D])};
    shapes.cshape = RDIV_UP(grp, 2)*ISIZE*ISIZE*4*qd*(cf_dbl?2:1)/2;
    switch (impl_spec.cf_mode) {
    case coef_mode_compressed:
      shapes.cshape = ((((9*shapes.cshape+7)/8)+7)/8+15)/16*16*8;
      break;  // need 9b to encode coef of 8b
    default:
      break;  // need 8b to encode
    }
    if (cf_tp == cf_cfg_8b_zp_e || cf_tp == cf_cfg_4b_zp_e) {  // add per channel zero-points
      shapes.cshape += grp * 8;
    }
    hlapi.i.iter[CONV_ITER_GRP] = RDIV_UP(grp, 2);
    hlapi.i.iter[CONV_ITER_NO]  = RDIV_UP(no, ISIZE);
    hlapi.i.iter[CONV_ITER_NI]  = RDIV_UP(ni, ISIZE);
    hlapi.i.iter[CONV_ITER_QD]  = qd;
    hlapi.i.iter[CONV_ITER_COL] = RDIV_UP(oshp[SPATIAL_W], TNSVSIZE);
    hlapi.i.iter[CONV_ITER_ROW] = oshp[SPATIAL_H];
    hlapi.i.iter[CONV_ITER_INN] = 1;
    hlapi.i.iter[CONV_ITER_ONN] = 1;
    hlapi.i.cf_iter[CONV_CF_ITER_GRP] = RDIV_UP(grp, 2);
    hlapi.i.cf_iter[CONV_CF_ITER_NO]  = RDIV_UP(no, ISIZE);
    hlapi.i.cf_iter[CONV_CF_ITER_NI]  = RDIV_UP(ni, ISIZE);
    hlapi.i.cf_iter[CONV_CF_ITER_IN]  = (shapes.cshape/
                                         (hlapi.i.cf_iter[CONV_CF_ITER_NI]*
                                          hlapi.i.cf_iter[CONV_CF_ITER_NO]*
                                          hlapi.i.cf_iter[CONV_CF_ITER_GRP])+TNSVSIZE*ISIZE-1)/(TNSVSIZE*ISIZE);
    break;
  case NINO(conv_mode_2x1g2s2):
    assert((1==impl_spec.inn*impl_spec.onn));
    qd = { (aoffset_t)((((filter[SPATIAL_W] - 1) * dil[SPATIAL_W] + 2) / 2) *
                       filter[SPATIAL_H] * filter[SPATIAL_D]) };
    shapes.cshape = RDIV_UP(grp, 2) * ISIZE * ISIZE * 2 * qd * (cf_dbl ? 2 : 1) / 2;
    switch (impl_spec.cf_mode) {
    case coef_mode_compressed:
      shapes.cshape = ((((9 * shapes.cshape + 7) / 8) + 7) / 8 + 15) / 16 * 16 * 8;
      break;  // need 9b to encode coef of 8b
    default:
      break;  // need 8b to encode
    }
    if (cf_tp == cf_cfg_8b_zp_e || cf_tp == cf_cfg_4b_zp_e) {  // add per channel zero-points
      shapes.cshape += grp * 8;
    }
    hlapi.i.iter[CONV_ITER_GRP] = RDIV_UP(grp, 2);
    hlapi.i.iter[CONV_ITER_NO]  = RDIV_UP(no, ISIZE);
    hlapi.i.iter[CONV_ITER_NI]  = RDIV_UP(ni, ISIZE);
    hlapi.i.iter[CONV_ITER_QD]  = qd;
    hlapi.i.iter[CONV_ITER_COL] = RDIV_UP(oshp[SPATIAL_W], TNSVSIZE);
    hlapi.i.iter[CONV_ITER_ROW] = oshp[SPATIAL_H];
    hlapi.i.iter[CONV_ITER_INN] = 1;
    hlapi.i.iter[CONV_ITER_ONN] = 1;
    hlapi.i.cf_iter[CONV_CF_ITER_GRP] = RDIV_UP(grp, 2);
    hlapi.i.cf_iter[CONV_CF_ITER_NO]  = RDIV_UP(no, ISIZE);
    hlapi.i.cf_iter[CONV_CF_ITER_NI]  = RDIV_UP(ni, ISIZE);
    hlapi.i.cf_iter[CONV_CF_ITER_IN]  = (shapes.cshape /
                                         (hlapi.i.cf_iter[CONV_CF_ITER_NI] *
                                          hlapi.i.cf_iter[CONV_CF_ITER_NO] *
                                          hlapi.i.cf_iter[CONV_CF_ITER_GRP]) + TNSVSIZE*ISIZE-1)/(TNSVSIZE*ISIZE);
    break;
  default:
    assert(0);  // not implemented
    break;
  }
  // Default to fetch linearly
  hlapi.i.cf_offsets  = {8, 8, 8, 8}; //?{NUM_COEF_QUEUE, NUM_COEF_QUEUE, NUM_COEF_QUEUE, NUM_COEF_QUEUE}
  // round coefficients to ixpix_t
  shapes.cshape = RDIV_UP(shapes.cshape, ISIZE);
  s = shapes;
}


//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void conv_params<B>::init_l1(const impl_spec_container_t<BD>& p) {
  bool fm_dbl = (fm_tp == fm_cfg_16b_e) || (fm_tp == fm_cfg_bf16_e) || (fm_tp == fm_cfg_fp16_e);
  tens = p;
  hlapi.i.fm_ptr      = tens.data.get_ptr();
  hlapi.i.fm_buf.base = tens.data.get_base();
  hlapi.i.fm_buf.len  = tens.data.get_size();
  int dino = impl_spec.cf_mode == coef_mode_sparse ? 2 : impl_spec.inn;
  // data: ixpix_t [D][H][W][G][C]
  switch (impl_spec.conv_mode) {
  case DINO(conv_mode_1x1):
  case NINO(conv_mode_1x1):
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_COL] = stride[SPATIAL_W];
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_ROW] = stride[SPATIAL_H];
    hlapi.i.fm_doffsets[CONV_FM_DOFF_COL]   = tens.data.get_offset(2)*stride[SPATIAL_W];  // w*std[w]
    hlapi.i.fm_doffsets[CONV_FM_DOFF_ROW]   =  // TO DO: should be (impl_spec.inn-1)?
      tens.data.get_offset(3)*stride[SPATIAL_H]+2*(1-dino)*tens.data.get_offset(0);
    break;
  case NINO(conv_mode_2x1s1):
  case NINO(conv_mode_2x1s1dl2):
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_COL] = stride[SPATIAL_W];
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_ROW] = stride[SPATIAL_H];
    hlapi.i.fm_doffsets[CONV_FM_DOFF_COL]   = tens.data.get_offset(2)*stride[SPATIAL_W];  // w*std[w]
    hlapi.i.fm_doffsets[CONV_FM_DOFF_ROW]   =
      tens.data.get_offset(3)*stride[SPATIAL_H]+2*(1-impl_spec.inn)*tens.data.get_offset(0);
    break;
  case NINO(conv_mode_2x1s2):
    assert(2 == stride[SPATIAL_W]);
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_COL] = 1;  // stride[SPATIAL_W];
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_ROW] = stride[SPATIAL_H];
    hlapi.i.fm_doffsets[CONV_FM_DOFF_COL]   = tens.data.get_offset(2);  // W dimension offset=1
    hlapi.i.fm_doffsets[CONV_FM_DOFF_ROW]   =  // H dimension offset=stride_H
      tens.data.get_offset(3)*stride[SPATIAL_H] + 2*(1-impl_spec.inn)*tens.data.get_offset(0);
    break;
  case NINO(conv_mode_3x3dws1):
  case NINO(conv_mode_3x3dws1dl2):
  case NINO(conv_mode_2x3dws2):
  case NINO(conv_mode_8x1dws1):
  case NINO(conv_mode_4x1dws1):
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_COL] = 1;
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_ROW] = 1;
    hlapi.i.fm_doffsets[CONV_FM_DOFF_COL]   = tens.data.get_offset(2);
    hlapi.i.fm_doffsets[CONV_FM_DOFF_ROW]   =
      fm_dbl ? (tens.data.get_offset(3) - tens.data.get_offset(0)) : tens.data.get_offset(3);
    break;
  case NINO(conv_mode_2x1g2s2):
    assert(2 == stride[SPATIAL_W]);
    // assert(1==stride[SPATIAL_H]);
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_COL] = 1;
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_ROW] = 2;  // stride[SPATIAL_H];
    hlapi.i.fm_doffsets[CONV_FM_DOFF_COL]   = 1;
            // tens.data.get_offset(2);//*stride[SPATIAL_W]; //w*std[w]
    hlapi.i.fm_doffsets[CONV_FM_DOFF_ROW]   =
      tens.data.get_offset(3)*2/*stride[SPATIAL_H]*/+2*(1-impl_spec.inn)*tens.data.get_offset(0);
    break;
  case NINO(conv_mode_4x1g2s1):
  case NINO(conv_mode_4x1g2s1dl2):
    assert(1 == stride[SPATIAL_H]);
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_COL] = 1;
    hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_ROW] = stride[SPATIAL_H];
    hlapi.i.fm_doffsets[CONV_FM_DOFF_COL]   = tens.data.get_offset(2);
    hlapi.i.fm_doffsets[CONV_FM_DOFF_ROW]   =
      tens.data.get_offset(3)*stride[SPATIAL_H]+2*(1-impl_spec.inn)*tens.data.get_offset(0);
    break;
  default:
    assert(0);  // not implemented
  }
  hlapi.i.fm_doffsets[CONV_FM_DOFF_CHAN]   = tens.data.get_offset(0);
  // encode quadrants
  quad_enc();
}

//
// Set a smaller, alternative tile shape e.g. for the boundaries of the feature-map
//
template<template<typename> class B>
void conv_params<B>::set_alt_shape(
    aoffset_t               grpi,       // number of groups in convolution
    aoffset_t               nii,        // number input channels (not vectors), in units of 8b or
                                        // 16b feature-map pixels
    aoffset_t               noi,        // number output channels (not vectors)
    const shape<3>&         oshpi,      // output shape, indexed by spatial_axis_t
    bool                    use_acci,   // use input accumulator
    bool                    keep_acci,  // keep output accumulator
    conv_params_impl_alt&   alt         // encoded alternative shape
    ) {
  assert(0 && "not implemented yet");
}

//
// Precompute the pointer offset when updating an input feature-map tensor pointer
//
template<template<typename> class B>
poffset_t conv_params<B>::update_ptr(
                                  const shape<3>&        spat_offset,  // spatial offset
                                  aoffset_t              chan_offset   // channel offset
                                  ) {
  aoffset_t chan_off = chan_offset % tens.data.get_dim(0);
  aoffset_t grp_off = chan_offset / tens.data.get_dim(0);
  return tens.data.get_offset({chan_off, grp_off, spat_offset[0], spat_offset[1], spat_offset[2]});
}

//
// encoding for quadrants
//
template<template<typename> class B>
void conv_params<B>::quad_enc() {
  bool fm_dbl = (fm_tp == fm_cfg_16b_e) || (fm_tp == fm_cfg_bf16_e) || (fm_tp == fm_cfg_fp16_e);
  quadrant_t q;
  int collast;  // column offset from first column to last
  int deplast;  // column offset from first depth to last
  int nn = 1;   // input multiplier
  switch (impl_spec.conv_mode) {
  case DINO(conv_mode_1x1):
    nn = 2;
    // no break, continue intentionally
    [[fallthrough]];
  case NINO(conv_mode_1x1):
    collast = (((oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE)-1)*TNSVSIZE*stride[SPATIAL_W];
    deplast = oshp[SPATIAL_D] - 1;
    // next filter column
    q.pdoffs[CONV_PAD_COL] = dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = 0;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[0]   = q;
    hlapi.i.quad_iter[0]   = filter[SPATIAL_W];
    // next filter row
    q.pdoffs[CONV_PAD_COL] = (1-filter[SPATIAL_W])*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[1]   = q;
    hlapi.i.quad_iter[1]   = filter[SPATIAL_H];
    // next depth
    q.pdoffs[CONV_PAD_COL] = (1-filter[SPATIAL_W])*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-filter[SPATIAL_H])*dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = dil[SPATIAL_D] - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[2]   = q;
    hlapi.i.quad_iter[2]   = filter[SPATIAL_D];
    // last quadrant move to next set of input channels
    q.pdoffs[CONV_PAD_COL] = (1-filter[SPATIAL_W])*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-filter[SPATIAL_H])*dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = (1-filter[SPATIAL_D])*dil[SPATIAL_D] - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4)
                            + impl_spec.inn*nn*tens.data.get_offset(0);
    hlapi.i.quad_data[3]   = q;
    break;
  case NINO(conv_mode_2x1s1):
  case NINO(conv_mode_2x1s1dl2):
  case NINO(conv_mode_2x1s2):
  {
    collast = (((oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE)-1)*TNSVSIZE*stride[SPATIAL_W];
    deplast = oshp[SPATIAL_D] - 1;
    int qw = (filter[SPATIAL_W]+1)/2;
    // next filter column
    q.pdoffs[CONV_PAD_COL] = 2*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = 0;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[0]   = q;
    hlapi.i.quad_iter[0]   = (filter[SPATIAL_W]+1)/2;
    // next filter row
    q.pdoffs[CONV_PAD_COL] = (1-qw)*2*dil[SPATIAL_W] - collast;
    // q.pdoffs[CONV_PAD_COL] = (1-qw)*(2+dil[SPATIAL_W]-1) - collast;
    q.pdoffs[CONV_PAD_ROW] = dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[1]   = q;
    hlapi.i.quad_iter[1]   = filter[SPATIAL_H];
    // next depth
    q.pdoffs[CONV_PAD_COL] = (1-qw)*2*dil[SPATIAL_W] - collast;
    // q.pdoffs[CONV_PAD_COL] = (1-qw)*(2+dil[SPATIAL_W]-1) - collast;
    // q.pdoffs[CONV_PAD_COL] = (1-filter[SPATIAL_W])*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-filter[SPATIAL_H])*dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = dil[SPATIAL_D] - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[2]   = q;
    hlapi.i.quad_iter[2]   = filter[SPATIAL_D];
    // last quadrant move to next set of input channels
    q.pdoffs[CONV_PAD_COL] = (1-qw)*2*dil[SPATIAL_W] - collast;
    // q.pdoffs[CONV_PAD_COL] = (1-qw)*(2+dil[SPATIAL_W]-1) - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-filter[SPATIAL_H])*dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = (1-filter[SPATIAL_D])*dil[SPATIAL_D] - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4)
                            + impl_spec.inn*nn*tens.data.get_offset(0);
    hlapi.i.quad_data[3]   = q;
    break;
  }
  case NINO(conv_mode_3x3dws1):
  {
    nn = fm_dbl ? 2 : 1;
    assert (ni == 1 && no == 1);
    assert (stride[SPATIAL_W] == 1 && stride[SPATIAL_H] == 1 && stride[SPATIAL_D] == 1); // else not implemented yet (do strided output)
    collast = (((oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE)-1)*TNSVSIZE;
    deplast = oshp[SPATIAL_D] - 1;
    aoffset_t fw = (dil[SPATIAL_W]*(filter[SPATIAL_W]-1)+3)/3;
    aoffset_t fh = (dil[SPATIAL_H]*(filter[SPATIAL_H]-1)+3)/3;
    // next filter column
    q.pdoffs[CONV_PAD_COL] = 3 - collast;
    q.pdoffs[CONV_PAD_ROW] = 0;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[0]   = q;
    hlapi.i.quad_iter[0]   = fw;
    // next filter row
    q.pdoffs[CONV_PAD_COL] = (1-fw)*3 - collast;
    q.pdoffs[CONV_PAD_ROW] = 3;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[1]   = q;
    hlapi.i.quad_iter[1]   = fh;
    // next depth
    q.pdoffs[CONV_PAD_COL] = (1-fw)*3 - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-fh)*3;
    q.pdoffs[CONV_PAD_DEP] = dil[SPATIAL_D] - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[2]   = q;
    hlapi.i.quad_iter[2]   = filter[SPATIAL_D];
    // last quadrant move to next set of input channels
    q.pdoffs[CONV_PAD_COL] = (1-fw)*3 - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-fh)*3;
    q.pdoffs[CONV_PAD_DEP] = (1-filter[SPATIAL_D])*dil[SPATIAL_D] - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4)
                             + impl_spec.inn*nn*tens.data.get_offset(0);
    hlapi.i.quad_data[3]   = q;
    break;
  }
  case NINO(conv_mode_3x3dws1dl2):
  {
    nn = fm_dbl ? 2 : 1;
    assert (ni == 1 && no == 1 && impl_spec.inn == 1 && impl_spec.onn == 1);
    assert (stride[SPATIAL_W] == 1 && stride[SPATIAL_H] == 1 && stride[SPATIAL_D] == 1); // else not implemented yet (do strided output)
    collast = (((oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE)-1)*TNSVSIZE;
    deplast = oshp[SPATIAL_D] - 1;
    aoffset_t fw = (dil[SPATIAL_W]*(filter[SPATIAL_W]-1)+dil[SPATIAL_W]*3)/(dil[SPATIAL_W]*3);
    aoffset_t fh = (dil[SPATIAL_H]*(filter[SPATIAL_H]-1)+dil[SPATIAL_H]*3)/(dil[SPATIAL_H]*3);
    // next filter column
    q.pdoffs[CONV_PAD_COL] = dil[SPATIAL_W]*3 - collast;
    q.pdoffs[CONV_PAD_ROW] = 0;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[0]   = q;
    hlapi.i.quad_iter[0]   = fw;
    // next filter row
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*3 - collast;
    q.pdoffs[CONV_PAD_ROW] = dil[SPATIAL_H]*3;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[1]   = q;
    hlapi.i.quad_iter[1]   = fh;
    // next depth
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*3 - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-fh)*dil[SPATIAL_H]*3;
    q.pdoffs[CONV_PAD_DEP] = dil[SPATIAL_D] - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[2]   = q;
    hlapi.i.quad_iter[2]   = filter[SPATIAL_D];
    // last quadrant move to next set of input channels
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*3 - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-fh)*dil[SPATIAL_H]*3;
    q.pdoffs[CONV_PAD_DEP] = (1-filter[SPATIAL_D])*dil[SPATIAL_D] - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4)
                            + impl_spec.inn*nn*tens.data.get_offset(0);
    hlapi.i.quad_data[3]   = q;
    break;
  }
  case NINO(conv_mode_2x3dws2):
  {
    nn = fm_dbl ? 2 : 1;
    assert (ni == 1 && no == 1);
    collast = (((oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE)-1)*TNSVSIZE*2;
    deplast = oshp[SPATIAL_D] - 1;
    aoffset_t fw = (dil[SPATIAL_W]*(filter[SPATIAL_W]-1)+dil[SPATIAL_W]*2)/(dil[SPATIAL_W]*2);
    aoffset_t fh = (dil[SPATIAL_H]*(filter[SPATIAL_H]-1)+dil[SPATIAL_H]*3)/(dil[SPATIAL_H]*3);
    // next filter column
    q.pdoffs[CONV_PAD_COL] = dil[SPATIAL_W]*2 - collast;
    q.pdoffs[CONV_PAD_ROW] = 0;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[0]   = q;
    hlapi.i.quad_iter[0]   = fw;
    // next filter row
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*2 - collast;
    q.pdoffs[CONV_PAD_ROW] = dil[SPATIAL_H]*3;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[1]   = q;
    hlapi.i.quad_iter[1]   = fh;
    // next depth
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*2 - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-fh)*dil[SPATIAL_H]*3;
    q.pdoffs[CONV_PAD_DEP] = dil[SPATIAL_D] - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[2]   = q;
    hlapi.i.quad_iter[2]   = filter[SPATIAL_D];
    // last quadrant move to next set of input channels
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*2 - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-fh)*dil[SPATIAL_H]*3;
    q.pdoffs[CONV_PAD_DEP] = (1-filter[SPATIAL_D])*dil[SPATIAL_D] - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4)
                             + impl_spec.inn*nn*tens.data.get_offset(0);
    hlapi.i.quad_data[3]   = q;
    break;
  }
  case NINO(conv_mode_8x1dws1):
  {
    nn = fm_dbl ? 2 : 1;
    assert (ni == 1 && no == 1 && impl_spec.inn == 1 && impl_spec.onn == 1);
    collast = (((oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE)-1)*TNSVSIZE;
    deplast = oshp[SPATIAL_D] - 1;
    aoffset_t fw = (dil[SPATIAL_W]*(filter[SPATIAL_W]-1)+dil[SPATIAL_W]*8)/(dil[SPATIAL_W]*8);
    aoffset_t fh = (dil[SPATIAL_H]*(filter[SPATIAL_H]-1)+dil[SPATIAL_H]*1)/(dil[SPATIAL_H]*1);
    // next filter column
    q.pdoffs[CONV_PAD_COL] = dil[SPATIAL_W]*8 - collast;
    q.pdoffs[CONV_PAD_ROW] = 0;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[0]   = q;
    hlapi.i.quad_iter[0]   = fw;
    // next filter row
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*8 - collast;
    q.pdoffs[CONV_PAD_ROW] = dil[SPATIAL_H]*1;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[1]   = q;
    hlapi.i.quad_iter[1]   = fh;
    // next depth
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*8 - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-fh)*dil[SPATIAL_H]*1;
    q.pdoffs[CONV_PAD_DEP] = dil[SPATIAL_D] - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[2]   = q;
    hlapi.i.quad_iter[2]   = filter[SPATIAL_D];
    // last quadrant move to next set of input channels
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*8 - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-fh)*dil[SPATIAL_H]*1;
    q.pdoffs[CONV_PAD_DEP] = (1-filter[SPATIAL_D])*dil[SPATIAL_D] - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4)
                             + impl_spec.inn*nn*tens.data.get_offset(0);
    hlapi.i.quad_data[3]   = q;
    break;
  }
  case NINO(conv_mode_4x1dws1):
  {
    nn = fm_dbl ? 2 : 1;
    assert (ni == 1 && no == 1 && impl_spec.inn == 1 && impl_spec.onn == 1);
    collast = (((oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE)-1)*TNSVSIZE;
    deplast = oshp[SPATIAL_D] - 1;
    aoffset_t fw = (dil[SPATIAL_W]*(filter[SPATIAL_W]-1)+dil[SPATIAL_W]*4)/(dil[SPATIAL_W]*4);
    aoffset_t fh = (dil[SPATIAL_H]*(filter[SPATIAL_H]-1)+dil[SPATIAL_H]*1)/(dil[SPATIAL_H]*1);
    // next filter column
    q.pdoffs[CONV_PAD_COL] = dil[SPATIAL_W]*4 - collast;
    q.pdoffs[CONV_PAD_ROW] = 0;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2) + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[0]   = q;
    hlapi.i.quad_iter[0]   = fw;
    // next filter row
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*4 - collast;
    q.pdoffs[CONV_PAD_ROW] = dil[SPATIAL_H]*1;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2) + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[1]   = q;
    hlapi.i.quad_iter[1]   = fh;
    // next depth
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*4 - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-fh)*dil[SPATIAL_H]*1;
    q.pdoffs[CONV_PAD_DEP] = dil[SPATIAL_D] - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2) + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[2]   = q;
    hlapi.i.quad_iter[2]   = filter[SPATIAL_D];
    // last quadrant move to next set of input channels
    q.pdoffs[CONV_PAD_COL] = (1-fw)*dil[SPATIAL_W]*4 - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-fh)*dil[SPATIAL_H]*1;
    q.pdoffs[CONV_PAD_DEP] = (1-filter[SPATIAL_D])*dil[SPATIAL_D] - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2) + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4) + impl_spec.inn*nn*tens.data.get_offset(0);
    hlapi.i.quad_data[3]   = q;
    break;
  }
  case NINO(conv_mode_2x1g2s2):
  {
    collast = (((oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE)-1)*TNSVSIZE*stride[SPATIAL_W];
    deplast = oshp[SPATIAL_D] - 1;
    int qw = (filter[SPATIAL_W]+1)/2;
    // next filter column
    q.pdoffs[CONV_PAD_COL] = 2*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = 0;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[0]   = q;
    hlapi.i.quad_iter[0]   = (filter[SPATIAL_W]+1)/2;
    // next filter row
    q.pdoffs[CONV_PAD_COL] = (1-qw)*2*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[1]   = q;
    hlapi.i.quad_iter[1]   = filter[SPATIAL_H];
    // next depth
    q.pdoffs[CONV_PAD_COL] = (1-qw)*2*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-filter[SPATIAL_H])*dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = dil[SPATIAL_D] - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[2]   = q;
    hlapi.i.quad_iter[2]   = filter[SPATIAL_D];
    // last quadrant move to next set of input channels
    q.pdoffs[CONV_PAD_COL] = (1-qw)*(2*dil[SPATIAL_W]) - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-filter[SPATIAL_H])*dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = (1-filter[SPATIAL_D])*dil[SPATIAL_D] - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4)
                            + impl_spec.inn*nn*tens.data.get_offset(0);
    hlapi.i.quad_data[3]   = q;
    break;
  }
  case NINO(conv_mode_4x1g2s1dl2):
  case NINO(conv_mode_4x1g2s1):
  {
    collast = (((oshp[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE)-1)*TNSVSIZE*stride[SPATIAL_W];
    deplast = oshp[SPATIAL_D] - 1;
    int qw = (filter[SPATIAL_W]+3)/4;
    // next filter column
    q.pdoffs[CONV_PAD_COL] = (4*dil[SPATIAL_W]) - collast;
    q.pdoffs[CONV_PAD_ROW] = 0;
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[0]   = q;
    hlapi.i.quad_iter[0]   = (filter[SPATIAL_W]+3)/4;
    // next filter row
    q.pdoffs[CONV_PAD_COL] = (1-qw)*4*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = 0 - deplast;
    q.doffs                =   q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[1]   = q;
    hlapi.i.quad_iter[1]   = filter[SPATIAL_H];
    // next depth
    q.pdoffs[CONV_PAD_COL] = (1-qw)*4*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-filter[SPATIAL_H])*dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = dil[SPATIAL_D] - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                             + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                             + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4);
    hlapi.i.quad_data[2]   = q;
    hlapi.i.quad_iter[2]   = filter[SPATIAL_D];
    // last quadrant move to next set of input channels
    q.pdoffs[CONV_PAD_COL] = (1-qw)*dil[SPATIAL_W] - collast;
    q.pdoffs[CONV_PAD_ROW] = (1-filter[SPATIAL_H])*dil[SPATIAL_H];
    q.pdoffs[CONV_PAD_DEP] = (1-filter[SPATIAL_D])*dil[SPATIAL_D] - deplast;
    q.doffs                =  q.pdoffs[CONV_PAD_COL]*tens.data.get_offset(2)
                            + q.pdoffs[CONV_PAD_ROW]*tens.data.get_offset(3)
                            + q.pdoffs[CONV_PAD_DEP]*tens.data.get_offset(4)
                            + impl_spec.inn*nn*tens.data.get_offset(0);
    hlapi.i.quad_data[3]   = q;
    break;
  }
  default:
    // not implemented yet
    assert(0);
    break;
  }
  // multiply padding offsets by packing factor
  hlapi.i.fm_pdoffsets[CONV_FM_PDOFF_COL] *= pck_mpy;
  for (int q = 0; q < 4; q++) {
    hlapi.i.quad_data[q].pdoffs[CONV_PAD_COL] *= pck_mpy;
  }
}

// coefficient encoding function, supporting 8b or 16b coefficients without zero-points
template<template<typename> class B>
void conv_params<B>::coef_enc(
    const tensor_t<coef_t, 7, xbuffer_t>& icf,  // input coefficients
                                                // [Grp][Cout][Fd][Fh][Fw][Cin][Coef h/l]
                                                // , h/l only for cf16 mode
    // outputs, buffers preallocated by caller
    conv_params_impl_coef<xbuffer_t>& obuf,  // output encoded coefficients NOLINT[runtime/references]
    xbuffer_t<coef_t>& tbuf           // allocator for temporary buffers NOLINT [runtime/references]
    ) {
  size_t l;
  assert((cf_tp != cf_cfg_bf16_e) && (cf_tp != cf_cfg_fp16_e));
  if (cf_tp == cf_cfg_16b_e) {
    npu_conv::coef_enc(
        icf,                   // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][Coef h/l]
        tbuf,                  // temporary xbuf
        impl_spec.conv_mode,   // convolution mode
        fm_tp == fm_cfg_16b_e, // 16b feature-map
        obuf.cbuf,             // output encoded coefficient tensor
        l);                    // size of used coefficient buffer in bytes
  } else {
    npu_conv::coef_enc(
        icf.reduce(0),         // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
        tbuf,                  // temporary xbuf
        impl_spec.conv_mode,   // convolution mode
        impl_spec.cf_mode,     // coefficient compression mode uncompressed or compressed or sparse
        fm_tp == fm_cfg_16b_e, // 16b feature-map
        cf_tp == cf_cfg_4b_nozp_e, // 4b coefficient encoding
        impl_spec.inn,         // inner input loop
        impl_spec.onn,         // inner output loop
        obuf.cbuf,             // output encoded coefficient tensor
        l);                    // size of used coefficient buffer in bytes
  }
  // reduce the buffer size
  obuf.cbuf.set_size(l);
}

// coefficient encoding function, supporting 8b only with zero-points
template<template<typename> class B>
void conv_params<B>::coef_enc(
    const tensor_t<coef_t, 6, xbuffer_t>& icf,  // input coefficients
                                                // [Grp][Cout][Fd][Fh][Fw][Cin], 8b only
    const tensor_t<coef_t, 1, xbuffer_t>& izp,  // input zero-points [Grp][Cout]
    // outputs, buffers preallocated by caller
    conv_params_impl_coef<xbuffer_t>& obuf,     // output encoded coefficients NOLINT [runtime/references]
    xbuffer_t<coef_t>& tbuf                     // temporary xbuf NOLINT [runtime/references]
    ) {
  size_t l;
  npu_conv::coef_enc(
      icf,                  // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp], 8b only
      izp,                  // input zero-points [Cout]
      tbuf,                 // temporary xbuf
      impl_spec.conv_mode,  // convolution mode
      impl_spec.cf_mode,    // coefficient compression mode uncompressed or compressed or sparse
      fm_tp == fm_cfg_16b_e, // 16b feature-map
      cf_tp == cf_cfg_4b_zp_e, // 4b coefficient encoding
      impl_spec.inn,        // inner input loop
      impl_spec.onn,        // inner output loop
      obuf.cbuf,            // output encoded coefficient tensor
      l);                   // size of used coefficient buffer in bytes
  // reduce the buffer size
  obuf.cbuf.set_size(l);
}

// floating-point coefficient encoders
template<template<typename> class B>
void conv_params<B>::coef_enc(const tensor_t<fp_e5m10_t,6,xbuffer_t>&  icf,    // fp16 input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp]
                              // outputs, buffers preallocated by caller
                              conv_params_impl_coef<xbuffer_t>&        obuf,   // output encoded coefficients
                              xbuffer_t<coef_t>&                       tbuf    // temporary xbuf NOLINT [runtime/references]
                              ) {
  assert(cf_tp == cf_cfg_fp16_e);
  tensor_t<coef_t,6,xbuffer_t> tcf = static_cast<tensor_t<coef_t,6,xbuffer_t> >(icf);

  size_t l;
  npu_conv::coef_enc(
      tcf.split(0,icf.get_dim(0)), // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][h/l]
      tbuf,                        // temp buffer
      impl_spec.conv_mode,         // convolution mode
      true,                        // 16b
      obuf.cbuf,                   // output encoded coefficient tensor
      l);                          // length
  // reduce the buffer size
  obuf.cbuf.set_size(l);
}
template<template<typename> class B>
void conv_params<B>::coef_enc(const tensor_t<fp_e8m7_t,6,xbuffer_t>&  icf,     // bf16 input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp]
                              // outputs, buffers preallocated by caller
                              conv_params_impl_coef<xbuffer_t>&       obuf,    // output encoded coefficients
                              xbuffer_t<coef_t>&                      tbuf     // temporary xbuf NOLINT [runtime/references]
                              ) {
  assert(cf_tp == cf_cfg_bf16_e);
  tensor_t<coef_t,6,xbuffer_t> tcf = static_cast<tensor_t<coef_t,6,xbuffer_t> >(icf);
  size_t l;

  npu_conv::coef_enc(
      tcf.split(0,icf.get_dim(0)), // input coefficients [Grp][Cout/Grp][Fd][Fh][Fw][Cin/Grp][h/l]
      tbuf,                        // temp buffer
      impl_spec.conv_mode,         // convolution mode
      true,                        // 16b
      obuf.cbuf,                   // output encoded coefficient tensor
      l);                          // length
  // reduce the buffer size
  obuf.cbuf.set_size(l);
}

// pad encoding
template<template<typename> class B>
void conv_params<B>::pad_enc(
    const tensor_t<pix_t, 2, xbuffer_t>&
      ipd,    // input feature-map zero-points [Cin][h/l], h/l only for fm16 mode
    // outputs, buffers preallocated by caller
    conv_params_impl_pad<xbuffer_t>&   // NOLINT [runtime/references]
      obuf                             // output encoded zero-points
    ) {
  const_tensor_iterator_t<pix_t, 2, xbuffer_t> iit(ipd);
  tensor_iterator_t<ixpix_t, 1, xbuffer_t>               oit(obuf.ptns);
  int gs;
  int gp;
  int sub_gp = 1;
  switch (impl_spec.conv_mode) {
  case NINO(conv_mode_3x3dws1):
  case NINO(conv_mode_3x3dws1dl2):
  case NINO(conv_mode_2x3dws2):
  case NINO(conv_mode_8x1dws1):
  case NINO(conv_mode_4x1dws1):
    gp = 1;     // groups
    gs = ipd.get_tens_size();  // group size
    break;
  case NINO(conv_mode_2x1g2s2):
  case NINO(conv_mode_4x1g2s1):
  case NINO(conv_mode_4x1g2s1dl2):
    sub_gp = 2;           // 2 sub-groups for a ixpix_t
    gp     = grp/sub_gp;  // groups
    gs     = ipd.get_tens_size() / gp;  // group size
    assert(gs <= ISIZE);
    break;
  default:
    gs = ipd.get_tens_size();  // group size
    gp = 1;  // groups
    break;
  }
  ixpix_t v;
  pix_t tv;
  for (int g=0; g < gp; g++) {
    int i = 0;
    while (i < gs) {
      for (int sg=0; sg < sub_gp; sg++) {
        for (int c=0; c < ISIZE/sub_gp; c++) {
          if (i < gs) {
            tv = iit.read();
            iit.next();
            i++;
          } else {
            tv = 0;
          }
          v[sg*ISIZE/sub_gp+c] = tv;
        }  // c
      }  // sg

      oit.write(v);
      oit.next();
    }  // while(i<gs)
  }  // g

  LDBGV(cout << "pad_enc: base=" << obuf.ptns.get_base()
      << " size=" << obuf.ptns.get_size() << endl;)
}

// floating-point pad encoding
template<template<typename> class B>
void conv_params<B>::pad_enc(const tensor_t<fp_e5m10_t,1,xbuffer_t>&  ipd,    // fp16 input feature-map zero-points [Cin/Grp]
                             // outputs, buffers preallocated by caller
                             conv_params_impl_pad<xbuffer_t>&         obuf    // output encoded zero-points
                             ) {
  assert(cf_tp == cf_cfg_fp16_e);
  tensor_t<pix_t,1,xbuffer_t> tpd = static_cast<tensor_t<pix_t,1,xbuffer_t> >(ipd);
  pad_enc(tpd.split(0, ipd.get_dim(0)), obuf);
}
template<template<typename> class B>
void conv_params<B>::pad_enc(const tensor_t<fp_e8m7_t,1,xbuffer_t>&  ipd,     // bf16 input feature-map zero-points [Cin/Grp]
                             // outputs, buffers preallocated by caller
                             conv_params_impl_pad<xbuffer_t>&        obuf    // output encoded zero-points
                             ) {
  assert(cf_tp == cf_cfg_bf16_e);
  tensor_t<pix_t,1,xbuffer_t> tpd = static_cast<tensor_t<pix_t,1,xbuffer_t> >(ipd);
  pad_enc(tpd.split(0, ipd.get_dim(0)), obuf);
}

}  // namespace tensor::v200
#undef LDBGV

#endif  // NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_CONV_INLINE_HPP_
