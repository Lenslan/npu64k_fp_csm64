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
 * tensor_gtoa_pad_inline.hpp
 *
 * File defining a tensor level padding API base on the generic tensor operation API
 *
 */
#define HLAPI gtoa_params<B>::hlapi

// constructors
template<template<typename> class B>
gtoa_pad_params<B>::gtoa_pad_params(
                                        aoffset_t                  noi,           // number output channels (not vectors)
                                        const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                        aoffset_t                  padstri,       // padding stride
                                        const shape<2>&            padposi,       // input padding position
                                        const shape<2>&            padlimi,       // input padding boundaries
                                        act_pmode_t                padmodei,      // padding mode
                                        //act_pinc_t               padinci,       // padding increment mode, use default value pinc_i16
                                        bool                       keepint,       // keep integer input when padding
                                        act_dtype_t                intp,          // type of primary input
                                        act_dtype_t                outtp          // type of output
                  ) {  
  // round parameters
  cmax = noi;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);
  int pinc=1;
  act_pinc_t padinci=pinc_i16;

  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0PEN_MASK;  // enable input padding
  switch (padmodei) {
  case pmode_min:   HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PMIN_MASK;  break;
  case pmode_max:   HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PMAX_MASK;  break;
  case pmode_mone:  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PMONE_MASK; break;
  default:          HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PZERO_MASK; break;
  }
  switch (padinci) {
  case pinc_v2i8:   HLAPI.i.u.op.bf |= ACT_BF_OP_PADV2I8_MASK;  pinc = 2; break;
  case pinc_v4i4:   HLAPI.i.u.op.bf |= ACT_BF_OP_PADV4I4_MASK;  pinc = 4; break;
  default:          HLAPI.i.u.op.bf |= ACT_BF_OP_PADI16_MASK;   pinc = 1; break;
  }
  switch (intp) {
  case dtype_int48:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 2, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)c, 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_fp32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP32 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  default:
    assert(0 && "unsupported input type");
  }

  switch (outtp) {
  case dtype_int32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OAC;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)c, 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_fp32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OAC;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP32 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  default:
    assert(0 && "unsupported output type");
  }
  // no parameters
  HLAPI.i.u.op.bnum = 0;
  int fmidbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmodbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.ishape[4];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.ishape[1]*shapes.ishape[2]*shapes.ishape[3];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.ishape[0]/fmidbl;
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // W/8 for feature-map input
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]/TNSVSIZE;
  }
  if((HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0) {
    // accumulator input AGU
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 1] = shapes.ishape[0];                     // mlsb
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 2] = shapes.ishape[1];                     // H
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 3] = shapes.ishape[2];                     // W
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 4] = shapes.ishape[3] * shapes.ishape[4];  // D*C
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
  }
  else if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // feature-map input AGU
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]    = fmidbl;                       // mlsb
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.ishape[3];             // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.ishape[2]/TNSVSIZE;       // W/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.ishape[4];             // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.ishape[0] / (fmidbl);  // C
  }
  if((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // feature-map output AGU
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = fmodbl;                       // mlsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.oshape[3];             // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.oshape[2]/TNSVSIZE;       // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.oshape[4];             // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.oshape[0] / (fmodbl);  // C
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable        = (int8_t)((1<<TNSVSIZE)-1);
  } else if((HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0) {
    // accumulator output AGU
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.oshape);
  }

  // set padding window
  HLAPI.i.u.op.pad_stride        = padstri;
  HLAPI.i.u.op.padpos[SPATIAL_W] = padposi[SPATIAL_W];
  HLAPI.i.u.op.padpos[SPATIAL_H] = padposi[SPATIAL_H];
  HLAPI.i.u.op.padlim[SPATIAL_W] = padlimi[SPATIAL_W];
  HLAPI.i.u.op.padlim[SPATIAL_H] = padlimi[SPATIAL_H];
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = TNSVSIZE * padstri * pinc;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = -(TNSVSIZE * padstri * (w - 1)) * pinc;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = -(TNSVSIZE * padstri * (w - 1)) * pinc;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - shapes.ishape[3];
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[3];
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - shapes.ishape[3];
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
  } else {
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = TNSVSIZE * padstri * pinc;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE * padstri * pinc;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - shapes.ishape[1];
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[1];
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
  }

  init_pad(HLAPI, keepint);
}

template<template<typename> class B>
gtoa_pad_params<B>::gtoa_pad_params(
                                        aoffset_t                  noi,           // number output channels (not vectors)
                                        const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                        aoffset_t                  padstri,       // padding stride
                                        const shape<2>&            padposi,       // input padding position
                                        const shape<2>&            padlimi,       // input padding boundaries
                                        act_pmode_t                padmodei,      // padding mode
                                        act_pinc_t                 padinci,       // padding increment mode
                                        bool                       keepint,       // keep integer input when padding
                                        act_dtype_t                intp,          // type of primary input
                                        act_dtype_t                outtp          // type of output
                  ) {  
  // round parameters
  cmax = noi;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);
  int pinc=1;

  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0PEN_MASK;  // enable input padding
  switch (padmodei) {
  case pmode_min:   HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PMIN_MASK;  break;
  case pmode_max:   HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PMAX_MASK;  break;
  case pmode_mone:  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PMONE_MASK; break;
  default:          HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PZERO_MASK; break;
  }
  switch (padinci) {
  case pinc_v2i8:   HLAPI.i.u.op.bf |= ACT_BF_OP_PADV2I8_MASK;  pinc = 2; break;
  case pinc_v4i4:   HLAPI.i.u.op.bf |= ACT_BF_OP_PADV4I4_MASK;  pinc = 4; break;
  default:          HLAPI.i.u.op.bf |= ACT_BF_OP_PADI16_MASK;   pinc = 1; break;
  }
  switch (intp) {
  case dtype_int48:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 2, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)c, 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_fp32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP32 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, oshpi[SPATIAL_W], oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  default:
    assert(0 && "unsupported input type");
  }

  switch (outtp) {
  case dtype_int32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OAC;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)c, 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_fp32:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OAC;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP32 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    break;
  default:
    assert(0 && "unsupported output type");
  }
  // no parameters
  HLAPI.i.u.op.bnum = 0;
  int fmidbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmodbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.ishape[4];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.ishape[1]*shapes.ishape[2]*shapes.ishape[3];
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.ishape[0]/fmidbl;
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // W/8 for feature-map input
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]/TNSVSIZE;
  }
  if((HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0) {
    // accumulator input AGU
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 1] = shapes.ishape[0];                     // mlsb
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 2] = shapes.ishape[1];                     // H
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 3] = shapes.ishape[2];                     // W
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 4] = shapes.ishape[3] * shapes.ishape[4];  // D*C
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
  }
  else if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    // feature-map input AGU
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]    = fmidbl;                       // mlsb
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.ishape[3];             // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.ishape[2]/TNSVSIZE;       // W/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.ishape[4];             // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.ishape[0] / (fmidbl);  // C
  }
  if((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
    // feature-map output AGU
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = fmodbl;                       // mlsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.oshape[3];             // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.oshape[2]/TNSVSIZE;       // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.oshape[4];             // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.oshape[0] / (fmodbl);  // C
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable        = (int8_t)((1<<TNSVSIZE)-1);
  } else if((HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0) {
    // accumulator output AGU
    for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
      HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.oshape);
  }

  // set padding window
  HLAPI.i.u.op.pad_stride        = padstri;
  HLAPI.i.u.op.padpos[SPATIAL_W] = padposi[SPATIAL_W];
  HLAPI.i.u.op.padpos[SPATIAL_H] = padposi[SPATIAL_H];
  HLAPI.i.u.op.padlim[SPATIAL_W] = padlimi[SPATIAL_W];
  HLAPI.i.u.op.padlim[SPATIAL_H] = padlimi[SPATIAL_H];
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = TNSVSIZE * padstri * pinc;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = -(TNSVSIZE * padstri * (w - 1)) * pinc;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = -(TNSVSIZE * padstri * (w - 1)) * pinc;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - shapes.ishape[3];
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[3];
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - shapes.ishape[3];
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
  } else {
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = TNSVSIZE * padstri * pinc;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE * padstri * pinc;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - shapes.ishape[1];
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[1];
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 0;
    HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
  }

  init_pad(HLAPI, keepint);
}

//template<template<typename> class B>
//gtoa_pad_params<B>::gtoa_pad_params(
//                                        aoffset_t                  noi,           // number output channels (not vectors)
//                                        const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
//                                        aoffset_t                  padstri,       // padding stride
//                                        const shape<2>&            padposi,       // input padding position
//                                        const shape<2>&            padlimi,       // input padding boundaries
//                                        act_pmode_t                padmodei,      // padding mode
//                                        //act_pinc_t               padinci,       // padding increment mode, use default value pinc_i16
//                                        bool                       keepint,       // keep integer input when padding
//                                        act_dtype_t                intp,          // type of primary input
//                                        act_dtype_t                outtp          // type of output
//                  ) : gtoa_pad_params(noi, oshpi, padstri, padposi, padlimi, padmodei, pinc_i16/*padinci*/,keepint,intp,outtp) {}

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_pad_params<B>::init_l1_output(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t,6,BD> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t,7,BD> t1(t0.split(3, p.data.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t,7,BD> t2(t1.transpose({3,0,5,4,6,1,2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t2.get_offset(0);                    // W8
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

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_pad_params<B>::init_l1_input(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t,6,BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t,7,BD> t1(t0.split(3, p.data.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t,7,BD> t2(t1.transpose({3,0,5,4,6,1,2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = t2.get_offset(0);                    // W8
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

template<template<typename> class B>
inline void gtoa_pad_params<B>::get_shapes(
                      gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                      ) {
  s = shapes;
}


#undef HLAPI

