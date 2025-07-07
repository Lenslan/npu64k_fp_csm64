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
 * tensor_gtoa_fc_act_inline_legacy.hpp
 *
 * File defining a tensor level activation function API following FC layer base on the generic tensor operation API
 *
 */

//
// Constructors
//
// AM32/48 to VM8/16
#define HLAPI gtoa_params<B>::hlapi
template<template<typename> class B>
gtoa_fc_act_params<B>::gtoa_fc_act_params(
                                 aoffset_t                  noi,           // number output channels (not vectors)
                                 bool                       fmdbli,        // 16b output feature-map
                                 bool                       inastri        // if true then input stream
                                 ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  if (inastri) {
    // input from streaming FIFO
    HLAPI.i.u.op.io_en    = ACT_IO_EN_ASTR0 | ACT_IO_EN_OFM;
  } else {
    // input from AM
    HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_OFM;
  }
  HLAPI.i.u.op.bf       = (fmdbli  ? 1<<ACT_BF_OP_OUTDBL_START : 0) |
                          (          1<<ACT_BF_OP_OUTSAT_START    );
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  fp16scl = true;
  cmax = noi;
  // input number in vyixacc_t
  int c_in = RDIV_UP(noi, ISIZE*TNSVSIZE);
  // output number in ixpix_t
  int c_out = RDIV_UP(noi, ISIZE);
  // output number padded to multiples of TNSVSIZE
  int c_out_up = ROUND_UP(c_out, TNSVSIZE);
  // input accumulator in vyixacc_t [C][1][1][1][1] format
  shapes.ishape = { 1, 1, 1, 1, (aoffset_t)c_in };
  // output feature-map in ixpix_t [1][1][1][C] format
  shapes.oshape = { (aoffset_t)(fmdbli  ? 2*c_out_up : c_out_up), 1, 1, 1, 1};
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c_out_up) };
  // maxpool overlap buffer set by zero as a  [No_Pool]
  shapes.mpshape = {(aoffset_t)(0)};
  // default onn and pooling
  gtoa_params<B>::onn = 1;
}

#undef HLAPI
