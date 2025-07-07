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
 * tensor_gtoa_eltop_fc_act_inline_legacy.hpp
 *
 * File defining a tensor level elementwise operation + activation function API
 * following FC layer base on the generic tensor operation API
 *
 */

#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_ELTOP_FC_ACT_INLINE_LEGACY_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_ELTOP_FC_ACT_INLINE_LEGACY_HPP_

//
// Constructors
//
// AM32/48 to VM8/16
#define HLAPI gtoa_params<B>::hlapi
template<template<typename> class B>
gtoa_eltop_fc_act_params<B>::gtoa_eltop_fc_act_params(
    aoffset_t                  noi,           // number output channels (not vectors)
    bool                       fmidbli,       // 16b input feature-map
    bool                       fmodbli,       // 16b output feature-map
    act_bin_op_t               opi,           // eltwise binary operation to perform
    bool                       eltact,        // first eltop then activ
    bool                       inastri)       // if true then input stream
    : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  op = opi;
  ea_ord = eltact;
  HLAPI.i.bf = 0;       // function, not LUT init
  if (inastri) {
    // input from streaming FIFO
    HLAPI.i.u.op.io_en    = ACT_IO_EN_ASTR0 | ACT_IO_EN_FM1 | ACT_IO_EN_OFM;
  } else {
    // input from AM
    HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_FM1 | ACT_IO_EN_OFM;
  }
  HLAPI.i.u.op.bf       = (fmidbli ? 1 << ACT_BF_OP_IN1DBL_START : 0) |
                          (fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                          (1 << ACT_BF_OP_OUTSAT_START);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  fp16scl = true;
  cmax = noi;
  // input number in vyixacc_t
  int c_in = RDIV_UP(noi, ISIZE*TNSVSIZE);
  // output number in ixpix_t
  int c_out = RDIV_UP(noi, ISIZE);
  // output number padded to multiples of TNSVSIZE
  int c_out_up = ROUND_UP(c_out, TNSVSIZE);
  // input 0 accumulator in vyixacc_t [C][1][1][1][1] format
  shapes.ishape = { 1, 1, 1, 1, (aoffset_t)c_in };
  // input 1 feature-map in ixpix_t [1][1][1][C] format
  shapes.i1shape = { (aoffset_t)(fmidbli  ? 2*c_out_up : c_out_up), 1, 1, 1, 1};
  // output feature-map in ixpix_t [1][1][1][C] format
  shapes.oshape = { (aoffset_t)(fmodbli  ? 2*c_out_up : c_out_up), 1, 1, 1, 1};
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c_out_up) };
  // default onn and pooling
  gtoa_params<B>::onn = 1;
}
#undef HLAPI
#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_LEGACY_TENSOR_GTOA_ELTOP_FC_ACT_INLINE_LEGACY_HPP_
