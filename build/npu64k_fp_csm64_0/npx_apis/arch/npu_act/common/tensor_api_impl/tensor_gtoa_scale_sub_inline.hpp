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
 * tensor_gtoa_scale_sub_inline.hpp
 *
 * File defining a tensor level binary API base on the generic tensor operation API
 *
 */

#define HLAPI gtoa_params<B>::hlapi

// constructors
// floating point extensions
template<template<typename> class B>
gtoa_scale_sub_params<B>::gtoa_scale_sub_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     act_dtype_t                in0tp,         // type of primary input
                                     act_dtype_t                in1tp,         // type of secondary input
                                     act_dtype_t                outtp,         // type of output
                                     bool                       bfp32scl,      // whether use fp32 prescale format
                                     bool                       sati,          // do saturation on output
                                     broadcast_t                brdc_f
                                     ) : gtoa_params<B>() {
  cmax = noi;
  this->bfp32scl = bfp32scl;
  this->brdc_f = brdc_f;
  bool i0dbl = (in0tp == dtype_int16) || (in0tp == dtype_fp16) || (in0tp == dtype_bf16);
  bool i1dbl = (in1tp == dtype_int16) || (in1tp == dtype_fp16) || (in1tp == dtype_bf16);
  bool odbl  = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  HLAPI.i.u.op.bf = (i0dbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                    (i1dbl ? 1 << ACT_BF_OP_IN1DBL_START : 0) |
                    (odbl  ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                    (sati  ? 1 << ACT_BF_OP_OUTSAT_START : 0);
  // update mask and floating mode field based on input/output type
  switch (in0tp) {
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
    case dtype_int32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0INT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC0;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN0FP32_MASK;
      break;
    default: assert(0 && "unsupported input datatype!");
  }
  switch (in1tp) {
    case dtype_int8:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1INT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1INT32_MASK;
      break;
    case dtype_fp16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1FP16_MASK;
      break;
    case dtype_bf16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_FM1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1BF16_MASK;
      break;
    case dtype_int32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1INT32_MASK;
      break;
    case dtype_fp32:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_AC1;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_IN1FP32_MASK;
      break;
    default: assert(0 && "unsupported input datatype!");
  }
  switch (outtp) {
    case dtype_int8:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
      HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
      break;
    case dtype_int16:
      HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
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
  int c = (noi+ISIZE-1)/ISIZE;
  int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;

  // iter number of in0 is same as the full tensor
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // input0 feature-map in ixpix_t [D][H][W][C] format
    shapes.ishape = { (aoffset_t)(i0dbl  ? 2*c : c),
                      (aoffset_t)1,
                      (aoffset_t)(w*TNSVSIZE),
                      oshpi[SPATIAL_H],
                      oshpi[SPATIAL_D] };
  } else {
    // input0 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/VSIZE][H][ONN/lsb/msb] format
    shapes.ishape = { (aoffset_t)1, 
                      oshpi[SPATIAL_H],
                      (aoffset_t)w,
                      oshpi[SPATIAL_D],
                      (aoffset_t)c };
  }
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0) {
    // input1 feature-map in ixpix_t [D][H][W][C] format
    shapes.i1shape = { brdc_f.in1_c ? (aoffset_t)(i1dbl  ? 2*1 : 1) : (aoffset_t)(i1dbl  ? 2*c : c), 
                       (aoffset_t)1,
                       brdc_f.in1_w ? (aoffset_t)TNSVSIZE : (aoffset_t)(w*TNSVSIZE),
                       brdc_f.in1_h ? (aoffset_t)1 : oshpi[SPATIAL_H],
                       oshpi[SPATIAL_D] };
  } else {
    // input1 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/VSIZE][H][ONN/lsb/msb] format
    shapes.i1shape = { (aoffset_t)1,
      brdc_f.in1_h ? (aoffset_t)1 : oshpi[SPATIAL_H],
      brdc_f.in1_w ? (aoffset_t)1 : (aoffset_t)w,
      oshpi[SPATIAL_D],
      brdc_f.in1_c ? (aoffset_t)1 : (aoffset_t)c};
  }
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // output feature-map in ixpix_t [D][H][W][C] format
    shapes.oshape = { (aoffset_t)(odbl  ? 2*c : c), (aoffset_t)1,
                      (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  } else {
    // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/VSIZE][H][ONN] format
    shapes.oshape = { (aoffset_t)1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  }
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*SCALE_BINARY_PER_CHAN) };
  HLAPI.i.u.op.bnum      = 4*SCALE_BINARY_PER_CHAN;

  gtoa_params<B>::onn = 1;

  set_binary_params();

  // only prescale, no post scale, per tensor pars
  scale_config_t scl(bfp32scl ? scl_cfg_t::scl_s32b32 : scl_cfg_t::scl_s8b32, scl_none, 0);

  init_binary_rr_scale_fp(HLAPI, op_fsub, gtoa_params<B>::onn == 2 ? alayo32 : alayo16, scl, brdc_f);
}

// set/get implementation specific parameters (dummy)
template<template<typename> class B>
void  gtoa_scale_sub_params<B>::set_binary_params() {
  int fmi0dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmi1dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN1DBL_MASK) != 0 ? 2 : 1;
  int fmodbl  = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  bool ifm0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool ifm1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0;
  bool iac0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0;
  bool iac1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC1) != 0;
  bool ofm_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0;
  bool oac_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0;

  bool cbrd = brdc_f.in0_c || brdc_f.in1_c;
  bool sbrd = brdc_f.in0_w || brdc_f.in0_h || brdc_f.in1_w || brdc_f.in1_h;

  assert((!cbrd || !sbrd) && "Do not support broadcasting for both input0 and input1");

  // iterators
 
  if (ofm_en) {
    if (cbrd) {
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.oshape[0]/fmodbl; // inner
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.oshape[2]
                                              *shapes.oshape[3]*shapes.oshape[4]/TNSVSIZE;
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.oshape[1];
    } else { // w broadcast and  other case
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.oshape[2]
                                            *shapes.oshape[3]*shapes.oshape[4]/TNSVSIZE; // inner
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.oshape[0]/fmodbl;
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.oshape[1];
    }
  } else if (oac_en) {
    if (cbrd) {
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.oshape[4];
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.oshape[1]*shapes.oshape[2]*shapes.oshape[3];
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.oshape[0];
    } else {
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.oshape[1]*shapes.oshape[2]*shapes.oshape[3];
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.oshape[4];
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.oshape[0];
    }    
  }

  // primary feature-map input
  if (ifm0_en) {
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    if (cbrd) {
      HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]    = fmi0dbl;            // mlsb
      HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.ishape[0] / (fmi0dbl);  // C
      HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.ishape[3];  // H
      HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.ishape[2]/TNSVSIZE;  // W/8
      HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.ishape[4];  // D
    } else {
      HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]    = fmi0dbl;            // mlsb
      HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.ishape[3];  // H
      HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.ishape[2]/TNSVSIZE;   // W/8
      HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.ishape[4];  // D
      HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.ishape[0] / (fmi0dbl);  // C
    }
  }
  // primary accumulator input
  if (iac0_en) {
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.ishape);
  }
  // secondary feature-map input
  if (ifm1_en) {
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.secondary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.secondary.fm_agu.offsets[i] = 0;
    }
    if (cbrd) {
      HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1]    = fmi1dbl;            // mlsb
      HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.i1shape[0] / (fmi1dbl);  // C
      HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.i1shape[3];  // H
      HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.i1shape[2]/TNSVSIZE;  // W/8
      HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.i1shape[4];  // D
    } else {
      HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1]    = fmi1dbl;            // mlsb
      HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.i1shape[3];  // H
      HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.i1shape[2]/TNSVSIZE;  // W/8
      HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.i1shape[4];  // D
      HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.i1shape[0] / (fmi1dbl);  // C
    }
  }
  // secondary accumulator input
  if (iac1_en) {
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.secondary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.secondary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.secondary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.secondary.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.i1shape);
  }
  // feature-map output
  if (ofm_en) {
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    if (cbrd) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = fmodbl;               // mlsb
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.oshape[0] / (fmodbl);   // C
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.oshape[3];    // H
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.oshape[2]/TNSVSIZE;   // W/8
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.oshape[4];    // D
    } else {
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = fmodbl;               // mlsb
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.oshape[3];    // H
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.oshape[2]/TNSVSIZE;   // W/8
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.oshape[4];    // D
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.oshape[0] / (fmodbl);   // C
    }
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable        = (int8_t)((1 << TNSVSIZE)-1);
  }
  // accumulator output
  if (oac_en) {
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.oshape);
  }
}

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void  gtoa_scale_sub_params<B>::init_l1_output(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  bool cbrd = brdc_f.in0_c || brdc_f.in1_c;

  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, p.data.get_dim(0)/HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]));
  tensor_t<ixpix_t, 7, BD> t1(t0.split(3, p.data.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, BD> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

    // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t2.get_offset(0);                    // W8

  
  if (cbrd) {
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(5)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(2)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(5)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(3)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(5)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(4)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(3)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(5)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
  } else {
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(2)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(3)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(4)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
    HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(5)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(4)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP
  }
}

// initialize the primary input tensors
template<template<typename> class B>
template<template<typename> class BD>
void  gtoa_scale_sub_params<B>::init_l1_input0(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  bool cbrd = brdc_f.in0_c || brdc_f.in1_c;

  shape<6> msb_shape = {
    (aoffset_t)HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1],                    //msb
    (aoffset_t)(shapes.ishape[0]/HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]), //c/msb
    (aoffset_t)shapes.ishape[1],  //g
    (aoffset_t)shapes.ishape[2],  //w
    (aoffset_t)shapes.ishape[3],  //h
    (aoffset_t)shapes.ishape[4]}; //d

  auto &t = reinterpret_cast<const impl_spec_container_t<B>*>(&p)->data;
    // [D][H][W][Grp][C] --> [D][H][W][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, B> t0(t.split(0, aoffset_t(t.get_dim(0)/HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])));
  tensor_t<ixpix_t, 6, B> tb = t0.broadcast(msb_shape);
  //[D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 7, B> t1(tb.split(3, tb.get_dim(3)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, B> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = brdc_f.in0_w ? 1 : t2.get_offset(0); // W8 (don't use 0 here in case of w-bcast, use 1)

  if (cbrd) {
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(5)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(2)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(5)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(3)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(5)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(4)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(3)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(5)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
  } else {
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
}

// initialize the secondary input tensors
template<template<typename> class B>
template<template<typename> class BD>
void  gtoa_scale_sub_params<B>::init_l1_input1(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                const impl_spec_container_t<BD>&  p
                                ) {
  bool cbrd = brdc_f.in0_c || brdc_f.in1_c;

  shape<6> msb_shape = {
    (aoffset_t)HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1],
    (aoffset_t)(shapes.i1shape[0]/HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1]),
    (aoffset_t)shapes.i1shape[1],
    (aoffset_t)shapes.i1shape[2],
    (aoffset_t)shapes.i1shape[3],
    (aoffset_t)shapes.i1shape[4]};

  //tensor_t<ixpix_t,5,B> t = reinterpret_cast<const impl_spec_container_t<B>*>(&p)->data.broadcast(shapes.i1shape);
  auto &t = reinterpret_cast<const impl_spec_container_t<B>*>(&p)->data;
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, B> t0(t.split(0, aoffset_t(t.get_dim(0)/HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])));
  tensor_t<ixpix_t, 6, B> tb = t0.broadcast(msb_shape);
  //[D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 7, B> t1(tb.split(3, tb.get_dim(3)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, B> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

  // fill the HLAPI offset parameters msb c h w d
  HLAPI.i.u.op.secondary.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.secondary.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.secondary.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.secondary.fm_agu.stride   = brdc_f.in1_w ? 1 : t2.get_offset(0); // W8 (don't use 0 here in case of w-bcast, use 1)

  if (cbrd) {
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(5)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP = off(c) + (1-on)*off(onn)
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(2)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(5)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H 
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(3)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(5)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(4)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(3)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(5)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
  } else {
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(2)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(3)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W 
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(4)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(5)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(4)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP = off(c) + (1-on)*off(onn)
  }
}

//
// Parameter encoding functions
//
// BRB0: prescale
// BRW1: bias
template<template<typename> class B>
inline void gtoa_scale_sub_params<B>::param_enc(
                                  const tensor_t<prescale_t,1,xbuffer_t>&   prescale,    // Input tensor scale value.
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&      bias,        // nput tensor bias value (used for both asym and bias).
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  // only prescale, no post scale, per tensor pars
  scale_config_t scl(scl_cfg_t::scl_s8b32, scl_none, 0);

  init_binary_rr_scale_fp(HLAPI, op_fsub, gtoa_params<B>::onn == 2 ? alayo32 : alayo16, scl, brdc_f);
  
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int8_t*  bparsc  = (int8_t*)bpars;                    // pointer to start of BRB values
  int32_t* bparsw  = (int32_t*)bpars;                   // pointer to start of BRW values
  aoffset_t j = 0;
  for (short i = 0; i < ISIZE; i++) {
      bparsc[0+i] = prescale.read({j}).data;            // BRC0 prescale
      bparsw[ISIZE+i] = bias.read({j}).data;            // BRW1 bias 0
      if (prescale.get_dim(0) > 1) j++;
  }
}

//
// Parameter encoding functions
//
// BRB0: prescale
// BRW1: bias
template<template<typename> class B>
inline void gtoa_scale_sub_params<B>::param_enc(
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   prescale,    // Input tensor scale value.
                                  const tensor_t<fp_e8m23_t,1,xbuffer_t>&   bias,        // nput tensor bias value (used for both asym and bias).
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  // only prescale, no post scale, per tensor pars
  scale_config_t scl(scl_cfg_t::scl_s32b32, scl_none, 0);

  init_binary_rr_scale_fp(HLAPI, op_fsub, gtoa_params<B>::onn == 2 ? alayo32 : alayo16, scl, brdc_f);

  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  int32_t* bparsw  = (int32_t*)bpars;                 // pointer to start of BRW values
  aoffset_t j = 0;

  for (short i = 0; i < ISIZE; i++) {
      auto svalue = prescale.read({j}).data;      // BRW0 prescale
      auto bvalue = bias.read({j}).data;          // BRW1 bias

      bparsw[i] = svalue;            // BRW0 prescale
      bparsw[ISIZE+i] = bvalue;          // BRW1 bias 0
      if (prescale.get_dim(0) > 1) j++;
    }
}

template<template<typename> class B>
inline void  gtoa_scale_sub_params<B>::get_shapes(
  // structure with implementation specific minimum buffer sizes
                      gtoa_act_params_impl_shapes& s
                      ) {
  s = shapes;
  bool ifm0_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool ifm1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0;
  int fmi0dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmi1dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN1DBL_MASK) != 0 ? 2 : 1;

  if (brdc_f.in0_h) s.ishape[ifm0_en ? 3 : 1] = 1;
  if (brdc_f.in0_w) s.ishape[ifm0_en ? 2 : 2] = 1;
  if (brdc_f.in0_c) s.ishape[ifm0_en ? 0 : 4] = fmi0dbl;
  if (brdc_f.in1_h) s.i1shape[ifm1_en ? 3 : 1] = 1;
  if (brdc_f.in1_w) s.i1shape[ifm1_en ? 2 : 2] = 1;
  if (brdc_f.in1_c) s.i1shape[ifm1_en ? 0 : 4] = fmi1dbl;
}

template<template<typename> class B>
inline void  gtoa_scale_sub_params<B>::set_broadcast_flags(
                      broadcast_t bc_flags
                      ) {
  brdc_f = bc_flags;
}

#undef HLAPI
