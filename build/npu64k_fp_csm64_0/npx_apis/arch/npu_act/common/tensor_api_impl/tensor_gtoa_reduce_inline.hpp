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
 * tensor_gtoa_reduce_inline.hpp
 *
 * File defining a tensor level reduce API base on the generic tensor operation API
 *
 */
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_REDUCE_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_REDUCE_INLINE_HPP_
#include "./legacy/tensor_gtoa_reduce_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi

// constructor


// reduce operation from feature-map (8b/16b) to feature-map (8b/16b)
template <template <typename> class B>
gtoa_reduce_params<B>::gtoa_reduce_params(
    aoffset_t noi,          // number output channels (not vectors)
    const shape<3> &ishpi,  // input shape, output inner is 1
    act_dtype_t itp,        // input type
    act_dtype_t otp,        // output type
    act_red_op_t opi,       // reduction operation to perform
    const int dimi) :       // spatial dimensions to reduce
    gtoa_params<B>() {
      // enable accumulator input and accumulator output
      HLAPI.i.bf            = 0;       // function, not LUT init
      HLAPI.i.u.op.io_en    = 0;
      bool idbl = (itp == dtype_int16) || (itp == dtype_fp16) || (itp == dtype_bf16);
      bool odbl = (otp == dtype_int16) || (otp == dtype_fp16) || (otp == dtype_bf16);
      HLAPI.i.u.op.bf = (idbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                        (odbl ? 1 << ACT_BF_OP_OUTDBL_START : 0);
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
      cmax = noi;
      red_dim = dimi;
      red_accum = false;
      assert((dimi >= 1 && dimi <= 3) && "dimi out of supported range");
      int c = (noi + ISIZE - 1) / ISIZE;
      int w = (ishpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
      if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
        // input feature-map in ixpix_t [D][H][W][C] format
        shapes.ishape = {(aoffset_t)(idbl ? 2 * c : c),
                        1,
                        (aoffset_t)(w * TNSVSIZE),
                        ishpi[SPATIAL_H],
                        ishpi[SPATIAL_D]};
      } else {
        // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
        shapes.ishape = {1,
                        ishpi[SPATIAL_H],
                        (aoffset_t)w,
                        ishpi[SPATIAL_D],
                        (aoffset_t)c};
      }
      if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
        // output feature-map in ixpix_t [D][H][W][C] format
        shapes.oshape = {(aoffset_t)(odbl ? 2 * c : c),
                        1,
                        (aoffset_t)TNSVSIZE,
                        (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                        (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D]};
      } else {
        // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
        shapes.oshape = {1,
                         (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                         1,
                         (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                         (aoffset_t)c};
      }
      // parameter dimension ixpix_t [C]
      shapes.pshape = {noi};
      // set padding window
      HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
      HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
      HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W] - 1;
      HLAPI.i.u.op.padlim[SPATIAL_H] = 0x7fff;
      if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = TNSVSIZE;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = -(TNSVSIZE * (w - 1));
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = -(TNSVSIZE * (w - 1));
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = -(TNSVSIZE * (w - 1));
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[3];
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - shapes.ishape[3];
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      } else {
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = TNSVSIZE;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - shapes.ishape[1];
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[1];
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      }
      init_reduce_i(opi, false);
      set_reduce_params();
}

// reduce operation for feature-map/accumulator input
// secondary input is accumulator (32b) if useAcc = true; 0 if useAcc = false
// output to VM (8b/16b) if keepAcc = false; to AM (32b) if keepAcc = true
template <template <typename> class B>
gtoa_reduce_params<B>::gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3>& ishpi,    // input shape, output inner is 1
    const shape<2>& padlimi,  // padding shape
    act_dtype_t i0tp,         // primary input type
    act_dtype_t i1tp,         // secondary input type
    act_dtype_t otp,          // output type
    act_red_op_t opi,         // reduction operation to perform
    bool useAcc,              // use accumulator input
    bool keepAcc,             // keep result in accumulator
    const int dimi) :         // spatial dimensions to reduce
    gtoa_params<B>() {
      // enable accumulator input and accumulator output
      HLAPI.i.bf            = 0;       // function, not LUT init
      HLAPI.i.u.op.io_en    = 0;
      bool idbl = (i0tp == dtype_int16) || (i0tp == dtype_fp16) || (i0tp == dtype_bf16);
      bool odbl = (otp  == dtype_int16) || (otp  == dtype_fp16) || (otp  == dtype_bf16);
      HLAPI.i.u.op.bf = (idbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                        (odbl ? 1 << ACT_BF_OP_OUTDBL_START : 0);
      // update mask and floating mode field based on input/output type
      switch (i0tp) {
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
      switch (i1tp) {
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
      switch (otp) {
        case dtype_int8:
          HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
          HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTSAT_MASK;
          HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
          assert(!keepAcc);
        case dtype_int16:
          HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
          HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTSAT_MASK;
          HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
          assert(!keepAcc);
          break;
        case dtype_fp16:
          HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
          HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTFP16_MASK;
          assert(!keepAcc);
          break;
        case dtype_bf16:
          HLAPI.i.u.op.io_en |= ACT_IO_EN_OFM;
          HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTBF16_MASK;
          assert(!keepAcc);
          break;
        case dtype_int32:
          HLAPI.i.u.op.io_en |= ACT_IO_EN_OAC;
          HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTINT32_MASK;
          assert(keepAcc);
          break;
        case dtype_fp32:
          HLAPI.i.u.op.io_en |= ACT_IO_EN_OAC;
          HLAPI.i.u.op.bf    |= ACT_BF_OP_OUTFP32_MASK;
          assert(keepAcc);
          break;
        default: assert(0 && "unsupported output datatype!");
      }
      cmax = noi;
      red_dim = dimi;
      red_accum = true;
      assert((dimi >= 1 && dimi <= 3) && "dimi out of supported range");
      int c = (noi + ISIZE - 1) / ISIZE;
      int w = (ishpi[SPATIAL_W] + TNSVSIZE - 1) / TNSVSIZE;
      if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
        // input feature-map in ixpix_t [D][H][W][C] format
        shapes.ishape = {(aoffset_t)(idbl ? 2 * c : c),
                        1,
                        (aoffset_t)(w * TNSVSIZE),
                        ishpi[SPATIAL_H],
                        ishpi[SPATIAL_D]};
      } else {
        // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
        shapes.ishape = {1,
                        ishpi[SPATIAL_H],
                        (aoffset_t)w,
                        ishpi[SPATIAL_D],
                        (aoffset_t)c};
      }
      // input1 accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
      shapes.i1shape = {1,
                       (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                       1,
                       (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                       (aoffset_t)c};
      if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
        // output feature-map in ixpix_t [D][H][W][C] format
        shapes.oshape = {(aoffset_t)(odbl ? 2 * c : c),
                        1,
                        (aoffset_t)TNSVSIZE,
                        (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                        (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D]};
      } else {
        // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
        shapes.oshape = {1,
                         (dimi >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                         1,
                         (dimi >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                         (aoffset_t)c};
      }
      // parameter dimension ixpix_t [C]
      shapes.pshape = {noi};
      // set padding windo
      HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
      HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
      HLAPI.i.u.op.padlim[SPATIAL_W] = padlimi[0];
      HLAPI.i.u.op.padlim[SPATIAL_H] = padlimi[1];
      if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = TNSVSIZE;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = -(TNSVSIZE * (w - 1));
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = -(TNSVSIZE * (w - 1));
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = -(TNSVSIZE * (w - 1));
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[3];
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 1 - shapes.ishape[3];
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      } else {
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_W] = TNSVSIZE;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_W] = (1 - shapes.ishape[2]) * TNSVSIZE;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_W] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_W] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 1][SPATIAL_H] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 2][SPATIAL_H] = 1;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 3][SPATIAL_H] = 1 - shapes.ishape[1];
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 4][SPATIAL_H] = 1 - shapes.ishape[1];
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 5][SPATIAL_H] = 0;
        HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS - 6][SPATIAL_H] = 0;
      }
      init_reduce_i(opi, useAcc);
      set_reduce_params();
}

template<template<typename> class B>
void gtoa_reduce_params<B>::set_pack_mode(
                                      pack_mode_t pmi
                                      ) {
#if NPU_VER_IS_VIC2_GA
  int pinc;
  switch (pmi) {
  case pack_mode_i8_e:   HLAPI.i.u.op.bf |= ACT_BF_OP_PADV2I8_MASK;  pinc = 2; break;
  case pack_mode_i4_e:   HLAPI.i.u.op.bf |= ACT_BF_OP_PADV4I4_MASK;  pinc = 4; break;
  default:               HLAPI.i.u.op.bf |= ACT_BF_OP_PADI16_MASK;   pinc = 1; break;
  }
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.pad_offs[i][SPATIAL_W] = HLAPI.i.u.op.pad_offs[i][SPATIAL_W] * pinc;
  }
#else
  assert(0);
#endif
}

template <template <typename> class B>
void gtoa_reduce_params<B>::init_reduce_i(act_red_op_t opi, bool useAcc) {
  /*
  HLAPI.i.u.op.bf  |= ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PMIN_MASK; // enable input padding, pad value to MININT for argmax and RMIN
  HLAPI.i.u.op.bf  |= ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PZERO_MASK; // enable input padding, pad value to 0 for ROR and RADD
  HLAPI.i.u.op.bf  |= ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PONES_MASK; // enable input padding, pad value to -1 for RAND
  */
  HLAPI.i.u.op.pad_stride = 1;
  switch (opi) {
  case gtoa_red_and:
    // enable input padding, pad value to -1 for RAND
    HLAPI.i.u.op.bf |= (ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PMONE_MASK);
    if (red_accum)
      init_reduce_accum(HLAPI, op_band, useAcc, TNSVSIZE==2);
    else
      init_reduce(HLAPI, op_band, TNSVSIZE==2);
    break;
  case gtoa_red_or:
    // enable input padding, pad value to 0 for ROR and RADD
    HLAPI.i.u.op.bf |= (ACT_BF_OP_IN0PEN_MASK);
    if (red_accum)
      init_reduce_accum(HLAPI, op_bor, useAcc, TNSVSIZE==2);
    else
      init_reduce(HLAPI, op_bor, TNSVSIZE==2);
    break;
  case gtoa_red_min:
    // enable input padding, pad value to max 0x7ffff
    HLAPI.i.u.op.bf |= (ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PMAX_MASK);
    if (red_accum)
      init_reduce_accum(HLAPI, op_min, useAcc, TNSVSIZE==2);
    else
      init_reduce(HLAPI, op_min, TNSVSIZE==2);
    break;
  case gtoa_red_max:
    // enable input padding, pad value to max 0x80000
    HLAPI.i.u.op.bf |= (ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PMIN_MASK);
    if (red_accum)
      init_reduce_accum(HLAPI, op_max, useAcc, TNSVSIZE==2);
    else
      init_reduce(HLAPI, op_max, TNSVSIZE==2);
    break;
  case gtoa_red_add:
    // enable input padding, pad value to 0 for ROR and RADD
    HLAPI.i.u.op.bf |= (ACT_BF_OP_IN0PEN_MASK);
    if (red_accum)
      init_reduce_accum(HLAPI, op_add, useAcc, TNSVSIZE==2);
    else
      init_reduce(HLAPI, op_add, TNSVSIZE==2);
    break;
  default:
    assert(0 && "unknown reduction instruction");
  }
}

// set/get implementation specific parameters (dummy)
template <template <typename> class B>
void gtoa_reduce_params<B>::set_reduce_params() {
  int fmidbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN0DBL_MASK) != 0 ? 2 : 1;
  int fmi1dbl = (HLAPI.i.u.op.bf & ACT_BF_OP_IN1DBL_MASK) != 0 ? 2 : 1;
  int fmodbl = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
  bool ifm_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0;
  bool ifm1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_FM1) != 0;
  bool iac_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC0) != 0;
  bool iac1_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_AC1) != 0;
  bool ofm_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0;
  bool oac_en = (HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0;

  // iterators
  if (red_dim == 1) {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = shapes.ishape[4];
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = shapes.ishape[1] * shapes.ishape[3];
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = shapes.ishape[2];
  } else if (red_dim == 2) {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = shapes.ishape[4];
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = shapes.ishape[3];
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = shapes.ishape[2] * shapes.ishape[1];
  } else {  // (red_dim == 3)
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = shapes.ishape[4];
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = 1;
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = shapes.ishape[2] * shapes.ishape[1]
                                                              * shapes.ishape[3];
  }
  if ((HLAPI.i.u.op.io_en & ACT_IO_EN_FM0) != 0) {
    if (red_dim == 1) {
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = shapes.ishape[0] / fmidbl;
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = shapes.ishape[3] * shapes.ishape[4];
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = shapes.ishape[2] / TNSVSIZE;
    } else if (red_dim == 2) {
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = shapes.ishape[0] / fmidbl;
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = shapes.ishape[4];
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = (shapes.ishape[2] / TNSVSIZE) *
                                               shapes.ishape[3];
    } else {  // (red_dim == 3)
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 3] = shapes.ishape[0] / fmidbl;
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 2] = 1;
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS - 1] = (shapes.ishape[2] / TNSVSIZE) *
                                               shapes.ishape[3] * shapes.ishape[4];
    }
  }
  // primary feature-map input
  if (ifm_en) {
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i] = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1] = fmidbl;                        // mlsb
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2] = shapes.ishape[2] / TNSVSIZE;      // W/8
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3] = shapes.ishape[3];              // H
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.ishape[4];              // D
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.ishape[0] / (fmidbl);   // C
  }
  // secondary feature-map input
  if (ifm1_en) {
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.secondary.fm_agu.iter[i] = 1;
      HLAPI.i.u.op.secondary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1] = fmi1dbl;                        // mlsb
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 2] = shapes.i1shape[2] / TNSVSIZE;      // W/8
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 3] = shapes.i1shape[3];              // H
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.i1shape[4];              // D
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.i1shape[0] / (fmi1dbl);  // C
  }
  // primary accumulator input
  if (iac_en) {
    for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
      HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.primary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 1] = shapes.ishape[2];           // W
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 2] = shapes.ishape[1];           // H
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 3] = shapes.ishape[3];           // D
    HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS - 4] = shapes.ishape[4];           // C
    // offset for vyixacc_t [C][D][W][H] format input
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS - 1] = shapes.ishape[1];
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS - 2] = 1
        + (1 - shapes.ishape[2]) * shapes.ishape[1];
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS - 3] = 1;
    HLAPI.i.u.op.primary.acc_agu.offsets[ACT_AM_LOOPS - 4] = 1;
  }
  // primary accumulator input
  if (iac1_en) {
    for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
      HLAPI.i.u.op.secondary.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.secondary.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.secondary.acc_agu.iter[ACT_AM_LOOPS - 1] = shapes.i1shape[2];           // W
    HLAPI.i.u.op.secondary.acc_agu.iter[ACT_AM_LOOPS - 2] = shapes.i1shape[1];           // H
    HLAPI.i.u.op.secondary.acc_agu.iter[ACT_AM_LOOPS - 3] = shapes.i1shape[3];           // D
    HLAPI.i.u.op.secondary.acc_agu.iter[ACT_AM_LOOPS - 4] = shapes.i1shape[4];           // C
    HLAPI.i.u.op.secondary.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
  }
  // feature-map output
  if (ofm_en) {
    for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
      HLAPI.i.u.op.out.fm.fm_agu.iter[i] = 1;
      HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1] = fmodbl;                       // mlsb
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2] = shapes.oshape[3];             // H
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3] = 1;                            // W/8
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4] = shapes.oshape[4];             // D
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5] = shapes.oshape[0] / (fmodbl);  // C
    // pooling parameters
    HLAPI.i.u.op.out.fm.pool.bf = 0;  // disable maxpooling
    // writeback all lines
    HLAPI.i.u.op.out.fm.enable = (int8_t)((1 << TNSVSIZE) - 1);
  }
  // accumulator output
  if (oac_en) {
    for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
      HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    }
    HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
    HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS - 1] = get_shape_size(shapes.oshape);
  }
}

// initialize the output tensors
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_reduce_params<B>::init_l1_output(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
  const impl_spec_container_t<BD> &p) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 5]));
  tensor_t<ixpix_t, 7, BD> t1(t0.split(3, p.data.get_dim(2) / TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, BD> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr = t2.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len = t2.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride = t2.get_offset(0);                     // W8
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 1] = t2.get_offset(1);  // ONN
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 2] =
      t2.get_offset(2) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);   // H
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 3] =
      t2.get_offset(3) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);   // W
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 4] =
      t2.get_offset(4) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]) * t2.get_offset(3) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);   // D
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS - 5] =
      t2.get_offset(5) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 4]) * t2.get_offset(4) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 3]) * t2.get_offset(3) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);   // C*GRP
}

// initialize the primary input tensors
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_reduce_params<B>::init_l1_input(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
    const impl_spec_container_t<BD> &p ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 5]));
  tensor_t<ixpix_t, 7, BD> t1(t0.split(3, p.data.get_dim(2) / TNSVSIZE));
  // transpose to [Grp][C][D][H][W/8][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, BD> t2(t1.transpose({3, 0, 4, 5, 6, 1, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr = t2.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len = t2.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride = t2.get_offset(0);                      // W8
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 1] = t2.get_offset(1);   // ONN
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 2] =
      t2.get_offset(2) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);  // W
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 3] =
      t2.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);  // H
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 4] =
      t2.get_offset(4) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * t2.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);  // D
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS - 5] =
      t2.get_offset(5) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 4]) * t2.get_offset(4) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 3]) * t2.get_offset(3) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);  // C*GRP
}

// initialize the secondary input tensors
template <template <typename> class B>
template <template <typename> class BD>
void gtoa_reduce_params<B>::init_l1_input1(
  // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
    const impl_spec_container_t<BD> &p ) {
  gtoa_params<B>::i1tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t, 7, BD> t1(t0.split(3, p.data.get_dim(2) / TNSVSIZE));
  // transpose to [Grp][C][D][H][W/8][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, BD> t2(t1.transpose({3, 0, 4, 5, 6, 1, 2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.secondary.fm_agu.ptr = t2.get_ptr();
  HLAPI.i.u.op.secondary.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.secondary.fm_agu.buf.len = t2.get_size();
  HLAPI.i.u.op.secondary.fm_agu.stride = t2.get_offset(0);                      // W8
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 1] = t2.get_offset(1);   // ONN
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 2] =
      t2.get_offset(2) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);  // W
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 3] =
      t2.get_offset(3) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);  // H
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 4] =
      t2.get_offset(4) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 3]) * t2.get_offset(3) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);  // D
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS - 5] =
      t2.get_offset(5) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 4]) * t2.get_offset(4) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 3]) * t2.get_offset(3) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);  // C*GRP
}

template <template <typename> class B>
inline void gtoa_reduce_params<B>::get_shapes(
    gtoa_act_params_impl_shapes& s  // structure with implementation specific minimum buffer sizes
) {
  s = shapes;
}

// change the paramters required by the feature-map output type
template <template <typename> class B>
template <template <typename> class BD>
inline void gtoa_reduce_params<B>::modif_out_fm(
  aoffset_t                        noi,      // number output channels
  const shape<3>&                  ishpi,    // input shape
  bool                             fmodbli,  // 16b output feature-map
  bool                             sati,     // saturate output
  gtoa_params_impl_alt_fm&         a) {      // NOLINT [runtime/references]
  int c = RDIV_UP(noi, ISIZE);
  shape<5> oshp({(aoffset_t)(fmodbli ? 2 * c : c),
                 1,
                 aoffset_t(TNSVSIZE),
                 (red_dim >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                 (red_dim >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D]});
  a.enable = (int8_t)((1 << TNSVSIZE) - 1);
  // clear acc output bit and set fm output bit
  a.io_en = (HLAPI.i.u.op.io_en & ~ACT_IO_EN_OAC) | ACT_IO_EN_OFM;
  // clear and set dbl/sat bits
  a.bf = (HLAPI.i.u.op.bf & ~(ACT_BF_OP_OUTSAT_MASK | ACT_BF_OP_OUTDBL_MASK))
                          | (fmodbli ? ACT_BF_OP_OUTDBL_MASK : 0)
                          | (sati    ? ACT_BF_OP_OUTSAT_MASK : 0);
  // set output feature-map AGU
  for (int i = 0; i < ACT_FM_LOOPS - 5; i++) {
    a.fm_agu.iter[i] = 1;
    a.fm_agu.offsets[i] = 0;
  }
  a.fm_agu.iter[ACT_FM_LOOPS - 1] = fmodbli ? 2 : 1;
  a.fm_agu.iter[ACT_FM_LOOPS - 2] = oshp[3];
  a.fm_agu.iter[ACT_FM_LOOPS - 3] = 1;
  a.fm_agu.iter[ACT_FM_LOOPS - 4] = oshp[4];
  a.fm_agu.iter[ACT_FM_LOOPS - 5] = c;
  impl_spec_container_t<BD> p(nullptr, oshp);
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t, 6, BD> t0(p.data.split(0, a.fm_agu.iter[ACT_FM_LOOPS - 5]));
  tensor_t<ixpix_t, 7, BD> t1(t0.split(3, p.data.get_dim(2) / TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t, 7, BD> t2(t1.transpose({3, 0, 5, 4, 6, 1, 2}));
  // fill the HLAPI offset parameters
  a.fm_agu.stride = t2.get_offset(0);                     // W8
  a.fm_agu.offsets[ACT_FM_LOOPS - 1] = t2.get_offset(1);  // ONN
  a.fm_agu.offsets[ACT_FM_LOOPS - 2] = t2.get_offset(2) +
      (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);   // H
  a.fm_agu.offsets[ACT_FM_LOOPS - 3] = t2.get_offset(3) +
      (1 - a.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);   // W
  a.fm_agu.offsets[ACT_FM_LOOPS - 4] = t2.get_offset(4) +
      (1 - a.fm_agu.iter[ACT_FM_LOOPS - 3]) * t2.get_offset(3) +
      (1 - a.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);   // D
  a.fm_agu.offsets[ACT_FM_LOOPS - 5] = t2.get_offset(5) +
      (1 - a.fm_agu.iter[ACT_FM_LOOPS - 4]) * t2.get_offset(4) +
      (1 - a.fm_agu.iter[ACT_FM_LOOPS - 3]) * t2.get_offset(3) +
      (1 - a.fm_agu.iter[ACT_FM_LOOPS - 2]) * t2.get_offset(2) +
      (1 - a.fm_agu.iter[ACT_FM_LOOPS - 1]) * t2.get_offset(1);   // C*GRP
  // set pointer and buffer (dummy)
  a.fm_agu.ptr      = localptr_t<ixpix_t>(t2.get_ptr());
  a.fm_agu.buf.base = localptr_t<ixpix_t>(t2.get_base());
  a.fm_agu.buf.len  = t2.get_size();
}

// change the parameters required by the accumulator output type
template <template <typename> class B>
inline void gtoa_reduce_params<B>::modif_out_acc(
  aoffset_t                 noi,    // number output channels
  const shape<3>&           ishpi,  // input shape
  gtoa_params_impl_alt_acc& a) {    // NOLINT [runtime/references]
  int c = RDIV_UP(noi, ISIZE);
  shape<5> oshp({1,
                 (red_dim >= 2) ? (aoffset_t)1 : ishpi[SPATIAL_H],
                 1,
                 (red_dim >= 3) ? (aoffset_t)1 : ishpi[SPATIAL_D],
                 (aoffset_t)c});
  // clear fm output bit and set acc output bit
  a.io_en = (HLAPI.i.u.op.io_en & ~ACT_IO_EN_OFM) | ACT_IO_EN_OAC;
  for (int i = 0; i < ACT_AM_LOOPS - 1; i++) {
    a.acc_agu.offsets[i] = 1;
    a.acc_agu.iter[i] = 1;
  }
  a.acc_agu.offsets[ACT_AM_LOOPS - 1] = 1;
  a.acc_agu.iter[ACT_AM_LOOPS - 1] = get_shape_size(oshp);
  // set pointer (dummy)
  a.acc_agu.ptr = 0;
}
#undef HLAPI
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_REDUCE_INLINE_HPP_
