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
 * tensor_gtoa_act_inline_legacy.hpp
 *
 * File defining a tensor level activation function API base on the generic tensor operation API
 *
 */

//
// Constructors
//
// to VM8/16
#define HLAPI gtoa_params<B>::hlapi
template<template<typename> class B>
gtoa_eltop_act_params<B>::gtoa_eltop_act_params(
                                 aoffset_t                  noi,           // number output channels (not vectors)
                                 const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                 const shape<3>&            ostr,          // output stride
                                 act_bin_op_t               opi,           // eltwise binary operation to perform
                                 bool                       accidbli,      // double wide input accumulator
                                 bool                       fmidbli,       // 16b input feature-map
                                 bool                       fmodbli,       // 16b output feature-map
                                 bool                       eltact,        // if true then first eltop then activ, else first activ then eltop 
                                 bool                       inastri        // if true then input stream
                                 ) : gtoa_params<B>() {
  // enable accumulator input and accumulator output
  op = opi;
  ea_ord = eltact;
  HLAPI.i.bf            = 0;       // function, not LUT init
  if (inastri) {
    // input from streaming FIFO
    HLAPI.i.u.op.io_en  = ACT_IO_EN_ASTR0 | ACT_IO_EN_FM1 | ACT_IO_EN_OFM;
  } else {
    // input from AM
    HLAPI.i.u.op.io_en  = ACT_IO_EN_AC0 | ACT_IO_EN_FM1 | ACT_IO_EN_OFM;
  }
  HLAPI.i.u.op.bf       = (accidbli ? 1<<ACT_BF_OP_IN0DBL_START : 0) |
                          (fmidbli  ? 1<<ACT_BF_OP_IN1DBL_START : 0) |
                          (fmodbli  ? 1<<ACT_BF_OP_OUTDBL_START : 0) |
                          (           1<<ACT_BF_OP_OUTSAT_START    );
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  fp16scl = true;
  cmax  = noi;
  mpstr = 1;
  str   = ostr;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);
  // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { (aoffset_t)(accidbli ? 2 : 1), oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.i1shape = { (aoffset_t)(fmidbli ? 2*c:c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // output feature-map in ixpix_t [D][H][W][C] format
  shapes.oshape = { (aoffset_t)(fmodbli ? 2*c:c), 1, (aoffset_t)(w*TNSVSIZE*str[SPATIAL_W]), (aoffset_t)(oshpi[SPATIAL_H]*str[SPATIAL_H]), (aoffset_t)(oshpi[SPATIAL_D]*str[SPATIAL_D]) };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  // maxpool overlap buffer ixpix_t [stash_sz]
  shapes.mpshape = {(aoffset_t)(2*c*(oshpi[SPATIAL_H]))};
  // default onn and pooling
  gtoa_params<B>::onn = 1;
  pmode = pnone;
}
// to AM32
template<template<typename> class B>
gtoa_eltop_act_params<B>::gtoa_eltop_act_params(
                                 aoffset_t                  noi,           // number output channels (not vectors)
                                 const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                 act_bin_op_t               opi,           // eltwise binary operation to perform
                                 bool                       accidbli,      // double wide input accumulator
                                 bool                       fmidbli,       // 16b input feature-map
                                 bool                       eltact,        // if true then first eltop then activ, else first activ then eltop 
                                 bool                       inastri        // if true then input stream
                                 ) : gtoa_params<B>() {
  op = opi;
  ea_ord = eltact;
  // enable accumulator input and accumulator output
  HLAPI.i.bf            = 0;       // function, not LUT init
  if (inastri) {
    // input from streaming FIFO
    HLAPI.i.u.op.io_en  = ACT_IO_EN_ASTR0 | ACT_IO_EN_FM1 | ACT_IO_EN_OAC;
  } else {
    // input from AM
    HLAPI.i.u.op.io_en  = ACT_IO_EN_AC0 | ACT_IO_EN_FM1 | ACT_IO_EN_OAC;
  }
  HLAPI.i.u.op.bf       = (accidbli ? 1<<ACT_BF_OP_IN0DBL_START : 0) | 
                          (fmidbli  ? 1<<ACT_BF_OP_IN1DBL_START : 0);

  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  fp16scl = true;
  cmax  = noi;
  mpstr = 1;
  str   = {1,1,1};
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);
  // input accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN/lsb/msb] format
  shapes.ishape = { (aoffset_t)(accidbli ? 2 : 1), oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // input feature-map in ixpix_t [D][H][W][C] format
  shapes.i1shape = { (aoffset_t)(fmidbli ? 2*c:c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
  // output accumulator shape
  shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
  // parameter dimension ixpix_t [C]
  shapes.pshape = { (aoffset_t)(4*c) };
  // maxpool overlap buffer ixpix_t [stash_sz]
  shapes.mpshape = {(aoffset_t)(2*c*(oshpi[SPATIAL_H]))};
  // default onn and pooling
  gtoa_params<B>::onn = 1;
  pmode = pnone;
}
#undef HLAPI
