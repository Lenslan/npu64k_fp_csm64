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
 * tensor_gtoa_wmean_inline.hpp
 *
 * File defining a tensor level global average pool API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_WMEAN_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_WMEAN_INLINE_HPP_

#define HLAPI gtoa_params<B>::hlapi

// constructor
template <template <typename> class B>
gtoa_wmean_params<B>::gtoa_wmean_params(
      aoffset_t       noi,      // number output channels (not vectors)
      const shape<3>& ishpi,    // input shape, output inner is 1
      const shape<2>& padlim,   // padding window
      size_t num,               // number of elements to be pooled
      act_dtype_t in0tp,        // 16b input feature-map
      act_dtype_t outtp,        // 16b output feature-map
      bool useAcc,              // use previous accumulator value
      bool bfp32scl):
  gtoa_params<B>() {

  this->bfp32scl = bfp32scl;
// enable accumulator input and accumulator/feature-map output
  HLAPI.i.u.op.bf = ACT_BF_OP_IN1FP32_MASK;
  HLAPI.i.u.op.io_en = ACT_IO_EN_AC1;

  bool i0dbl = (in0tp == dtype_int16) || (in0tp == dtype_fp16) || (in0tp == dtype_bf16);
  bool odbl  = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  bool keepAcc = (outtp == dtype_int32) || (outtp == dtype_fp32);

  HLAPI.i.u.op.bf |= (i0dbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                    (odbl ? 1 << ACT_BF_OP_OUTDBL_START : 0);
  
  switch (in0tp) {
    case dtype_int8:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_fp16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf |= ACT_BF_OP_IN0FP16_MASK;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM0;
      HLAPI.i.u.op.bf |= ACT_BF_OP_IN0BF16_MASK;
      break;
    default: assert(0 && "unsupported output datatype!");
  }

  switch (outtp) {
    case dtype_int8:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_fp16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf |= ACT_BF_OP_OUTFP16_MASK;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf |= ACT_BF_OP_OUTBF16_MASK;
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

  // enable padding with zero
  HLAPI.i.u.op.bf |= (ACT_BF_OP_IN0PEN_MASK);
  // set padding window
  HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
  HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
  HLAPI.i.u.op.padlim[SPATIAL_W] = padlim[0];
  HLAPI.i.u.op.padlim[SPATIAL_H] = padlim[1];
  cmax = noi;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(ishpi[SPATIAL_W], TNSVSIZE);
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.ishape = {(aoffset_t)(i0dbl ? 2 * c : c),
                   1,
                   (aoffset_t)(w * TNSVSIZE),
                   ishpi[SPATIAL_H],
                   ishpi[SPATIAL_D]};
  // input1 accumulator in vyixacc_t [C] format
  shapes.i1shape = {1, 1, 1, 1, (aoffset_t)c};

  // output accumulator in vyixacc_t [C] format
    if (keepAcc)
    shapes.oshape = {1, 1, 1, 1, (aoffset_t)c};
  else
    shapes.oshape = {(aoffset_t)(odbl ? 2 * c : c), 1, (aoffset_t)TNSVSIZE, 1, 1};

  // parameter dimension
  // per tensor parameter
  shapes.pshape = {(aoffset_t)(4*WMEAN_PER_CHAN)};

  HLAPI.i.u.op.bnum      = 4*WMEAN_PER_CHAN*sizeof(uint32_t)/sizeof(ixpix_t);

  // set padding window
  HLAPI.i.u.op.pad_stride = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = (1 - w) * TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 1 - ishpi[SPATIAL_H];
  init_wmean(HLAPI, useAcc, keepAcc, alayo16, bfp32scl);
  set_wmean_params();

  float recip = 1.0/(float)num;
  fp_e8m23_t frecip(recip);
  HLAPI.i.u.op.scl[2] = frecip.data;
}

// set iterators
template <template <typename> class B>
void gtoa_wmean_params<B>::set_wmean_params() {
  int fmidbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmodbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  bool ifm_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool iac_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0;
  bool ofm_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0;
  bool oac_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0;

  int i_c = oac_en ? shapes.oshape[4] : shapes.oshape[0]/fmodbl;
  int i_spatial;
  if (ifm_en) {
    i_spatial = RDIV_UP(shapes.ishape[2], TNSVSIZE) * shapes.ishape[3] * shapes.ishape[4];
  } else {
    i_spatial = shapes.ishape[1] * shapes.ishape[2] * shapes.ishape[3];
  }
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = 1;                    // channel loop
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = i_c;                  // spatial loop
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = i_spatial;            // inner loop is 1
  // primary feature-map input
  if (ifm_en) {
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = fmidbl;                            // mlsb
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = shapes.ishape[3];                  // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = RDIV_UP(shapes.ishape[2], TNSVSIZE);  // W/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.ishape[4];                  // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.ishape[0] / fmidbl;         // C
  }
  // primary accumulator input
  if (iac_en) {
    for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 1] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 2] = shapes.ishape[1];           // H
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 3] = shapes.ishape[2];           // W
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 4] = shapes.ishape[3] *
                                                          shapes.ishape[4];           // D*C
  }
  // secondary accumulator input
  for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
    HLAPI.i.u.op.secondary.acc_agu.offsets[i] = 1;
    HLAPI.i.u.op.secondary.acc_agu.iter[i] = 1;
  }
  HLAPI.i.u.op.secondary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
  HLAPI.i.u.op.secondary.acc_agu.iter[ACT_AM_LOOPS-1] = i_c;
  // feature-map output
  if (ofm_en) {
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i] = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1] = fmodbl;                       // mlsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = 1;                            // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = 1;                            // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = 1;                            // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.oshape[0]/fmodbl;      // C
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf = 0;  // disable maxpooling
    // writeback one line
    HLAPI.i.u.op.out.fm.enable = (int8_t)0x1;
  }
  // accumulator output
  if (oac_en) {
    for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
      HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS - 1] = i_c;
  }
}

// initialize the input tensors
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_wmean_params<B>::init_l1_input(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
  const impl_spec_container_t<BD> &p) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);

  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5])); // c --> c/mlsb|msb
  tensor_t<ixpix_t, 7, BD> t1(t0.split(3, p.data.get_dim(2)/TNSVSIZE)); //w --> w/8 | w8
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, BD> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = t2.get_offset(0);                    // stride = offset W8
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(2)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(5)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP
}

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_wmean_params<B>::init_l1_output(
  // structure with allocated buffers and tensors in L1 memory
  const impl_spec_container_t<BD>& p) {
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
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = t1.get_offset(0);   // mlsb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] = t1.get_offset(1) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // H
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] = t1.get_offset(2) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // W
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] = t1.get_offset(3) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // D
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 5] = t1.get_offset(4) +
    (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // Grp*C
}

template <template <typename> class B>
inline void gtoa_wmean_params<B>::get_shapes(
    gtoa_act_params_impl_shapes& s  // structure with implementation specific minimum buffer sizes
) {
  s = shapes;
}

// change the function microcode
template <template <typename> class B>
inline void gtoa_wmean_params<B>::modif_func(bool keepAcc, gtoa_params_impl_modif& m) {  // NOLINT [runtime/references]
  act_hlapi_t h;
  init_wmean(h, false, keepAcc, alayo16, bfp32scl);
  m = h.i.u.op.act_prog;
}

// change the paramters required by the feature-map output type
template <template <typename> class B>
template <template <typename> class BD>
inline void gtoa_wmean_params<B>::modif_out_fm(
  aoffset_t                        noi,      // number output channels
  act_dtype_t                      outtp,  // 16b output feature-map
  bool                             sati,     // saturate output
  bool                             use_opt_vm_layout, // use layout opt
  gtoa_params_impl_alt_fm&         a) {      // NOLINT [runtime/references]
  int c = RDIV_UP(noi, ISIZE);
  // enable one lane for wmean output
  a.enable = 0x1;
  // clear acc output bit and set fm output bit
  a.io_en = (HLAPI.i.u.op.io_en & ~ACT_IO_EN_OAC) | ACT_IO_EN_OFM;

  bool fmodbli = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  // clear and set dbl/sat bits
  a.bf = (HLAPI.i.u.op.bf & ~(ACT_BF_OP_OUTSAT_MASK | ACT_BF_OP_OUTDBL_MASK))
                          | (fmodbli ? ACT_BF_OP_OUTDBL_MASK : 0)
                          | (sati    ? ACT_BF_OP_OUTSAT_MASK : 0);

    switch (outtp) {
    case dtype_int8:

      a.bf = (a.bf & ~(ACT_BF_OP_OUTINT32_MASK|ACT_BF_OP_OUTFP16_MASK|ACT_BF_OP_OUTBF16_MASK))
         | ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_int16:
      a.bf = (a.bf & ~(ACT_BF_OP_OUTINT32_MASK|ACT_BF_OP_OUTFP16_MASK|ACT_BF_OP_OUTBF16_MASK))
         | ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_fp16:
      a.bf = (a.bf & ~(ACT_BF_OP_OUTINT32_MASK|ACT_BF_OP_OUTFP16_MASK|ACT_BF_OP_OUTBF16_MASK))
         | ACT_BF_OP_OUTFP16_MASK;
      break;
    case dtype_bf16:
      a.bf = (a.bf & ~(ACT_BF_OP_OUTINT32_MASK|ACT_BF_OP_OUTFP16_MASK|ACT_BF_OP_OUTBF16_MASK))
         | ACT_BF_OP_OUTBF16_MASK;
      break;
    default: assert(0 && "unsupported output datatype!");
  }

  // set output feature-map AGU
  for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
    a.fm_agu.iter[i] = 1;
    a.fm_agu.offsets[i] = 0;
  }
  a.fm_agu.iter[ACT_FM_LOOPS - 1] = fmodbli ? 2 : 1;
  a.fm_agu.iter[ACT_FM_LOOPS - 2] = 1;
  a.fm_agu.iter[ACT_FM_LOOPS - 3] = 1;
  a.fm_agu.iter[ACT_FM_LOOPS - 4] = 1;
  a.fm_agu.iter[ACT_FM_LOOPS - 5] = c;
  impl_spec_container_t<BD> p(nullptr, {(aoffset_t)(fmodbli ? 2 * c : c), 1, 1, 1, 1}, use_opt_vm_layout);
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/mlsb][mlsb]
  tensor_t<ixpix_t, 6, B> t0(p.data.split(0, a.fm_agu.iter[ACT_FM_LOOPS - 5]));
  // transpose to [Grp][C][D=1][W=1][H=1][mlsb]
  tensor_t<ixpix_t, 6, B> t1(t0.transpose({0, 4, 3, 5, 1, 2}));
  // fill the HLAPI offset parameters
  a.fm_agu.stride   = 1;
  a.fm_agu.offsets[ACT_FM_LOOPS - 1] = t1.get_offset(0);   // mlsb
  a.fm_agu.offsets[ACT_FM_LOOPS - 2] = t1.get_offset(1) +
    (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // H
  a.fm_agu.offsets[ACT_FM_LOOPS - 3] = t1.get_offset(2) +
    (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // W
  a.fm_agu.offsets[ACT_FM_LOOPS - 4] = t1.get_offset(3) +
    (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // D
  a.fm_agu.offsets[ACT_FM_LOOPS - 5] = t1.get_offset(4) +
    (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t1.get_offset(0);  // Grp*C
  // set pointer and buffer (dummy)
  a.fm_agu.ptr      = localptr_t<ixpix_t>(t1.get_ptr());
  a.fm_agu.buf.base = localptr_t<ixpix_t>(t1.get_base());
  a.fm_agu.buf.len  = t1.get_size();
}

// change the parameters required by the accumulator output type
template <template <typename> class B>
inline void gtoa_wmean_params<B>::modif_out_acc(
  aoffset_t                 noi,  // number output channels
  gtoa_params_impl_alt_acc& a) {  // NOLINT [runtime/references]
  int c = RDIV_UP(noi, ISIZE);
  // clear fm output bit and set acc output bit
  a.io_en = (HLAPI.i.u.op.io_en & ~ACT_IO_EN_OFM) | ACT_IO_EN_OAC;
  for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
    a.acc_agu.offsets[i] = 1;
    a.acc_agu.iter[i] = 1;
  }
  a.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
  a.acc_agu.iter[ACT_AM_LOOPS - 1] = c;
  // set pointer (dummy)
  a.acc_agu.ptr = 0;
}

// initialize the scale and shift parameters for global average pooling
template <template <typename> class B>
void gtoa_wmean_params<B>::init_wmean_scale(
  int16_t scale,     // common scaling factor for all channels
  uint8_t shift) {   // common shift left amount for all channels
  float f = scl_fix2flt(scale, shift);
  int32_t val = *(int32_t*)(void*)&f;
  
  HLAPI.i.u.op.scl[2] = val;  // put in SR2
}

//
// Parameter encoding functions
//
// BRB0: prescale fp8
// BRW1: bias fp32
template<template<typename> class B>
inline void gtoa_wmean_params<B>::param_enc(
                                  const tensor_t<prescale_t,1,xbuffer_t>&      prescale,    // Input tensor scale value.
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&      bias,        // nput tensor bias value (used for both asym and bias).
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&           obuf         // output encoded parameters
                                  ) {
  
  assert(!bfp32scl && "Prescale should be 8bit");

  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRC values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;

  for (short i = 0; i < ISIZE; i++) {
    auto svalue = prescale.read({j}).data;        // BRW0 prescale
    auto bvalue = bias.read({j}).data;            // BRW1 bias 0

    bparsc[i] = svalue;                           // BRB0 scale
    bparsw[ISIZE+i] = bvalue;                     // BRW1 bias
    if (prescale.get_dim(0) > 1) j++;
  }
}

//
// Parameter encoding functions
//
// BRW0: prescale fp32
// BRW1: bias fp32
template<template<typename> class B>
inline void gtoa_wmean_params<B>::param_enc(
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&      prescale,    // Input tensor scale value.
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&      bias,        // nput tensor bias value (used for both asym and bias).
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&           obuf         // output encoded parameters
                                  ) {
  assert(bfp32scl && "Prescale should be 32bit");

  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;

  for (short i = 0; i < ISIZE; i++) {
      auto svalue = prescale.read({j}).data;      // BRW0 prescale
      auto bvalue = bias.read({j}).data;          // BRW1 bias
      bparsw[i] = svalue;                         // BRW0 scale
      bparsw[ISIZE+i] = bvalue;                   // BRW1 bias
      if (prescale.get_dim(0) > 1) j++;
  }
}

#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_WMEAN_INLINE_HPP_
