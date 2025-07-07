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
 * tensor_gtoa_intfp_inline.hpp
 *
 * File defining a tensor level API to split integer and fractional part
 *
 */
#define HLAPI gtoa_params<B>::hlapi

// constructors
template<template<typename> class B>
gtoa_intfp_params<B>::gtoa_intfp_params(
                                        aoffset_t                  noi,           // number output channels (not vectors)
                                        const shape<3>&            ishpi          // output shape, indexed by spatial_axis_t
                  ) {  
  // round parameters
  cmax = noi;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(ishpi[SPATIAL_W], TNSVSIZE);

  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  // FP32 input
  HLAPI.i.u.op.io_en    |= ACT_IO_EN_AC0;
  HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
  HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP32 << ACT_BF_OP_IN0FMODE_START;
  shapes.ishape          = { 1, ishpi[SPATIAL_H], (aoffset_t)w, ishpi[SPATIAL_D], (aoffset_t)c };
  // FP16 and INT16 output
  HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
  HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_OUTFMODE_START;
  shapes.oshape          = { (aoffset_t)(2*c), 2, (aoffset_t)(w*TNSVSIZE), ishpi[SPATIAL_H], ishpi[SPATIAL_D] };
  // init microcode
  // start of activation program
  ACT_START(HLAPI);
  ACT_INST(HLAPI, fpopin0(PALWAYS, VR0), 0);
  ACT_INST(HLAPI, ftoi(PALWAYS, VR1, VR0), 4);
  ACT_INST(HLAPI, fract(PALWAYS, VR2, VR0), 6);
  ACT_INST(HLAPI, pushout(PALWAYS, VR1), 7);
  ACT_INST(HLAPI, fpushout(PALWAYS, VR2), 8);
  ACT_END(HLAPI);
  // end of program
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = 1;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = 1;
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = c*w*ishpi[SPATIAL_H]*ishpi[SPATIAL_D];
  // accumulator input AGU
  for (int i = 0; i < ACT_AM_LOOPS; i++) {
    HLAPI.i.u.op.primary.acc_agu.offsets[i] = 1;
    HLAPI.i.u.op.primary.acc_agu.iter[i]    = 1;
  }
  HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-1]    = c;
  HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-2]    = w;
  HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-3]    = ishpi[SPATIAL_H];
  HLAPI.i.u.op.primary.acc_agu.iter[ACT_AM_LOOPS-4]    = ishpi[SPATIAL_D];
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = 2;                            // mlsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = 2;                            // G
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = ishpi[SPATIAL_H];
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = w;                            // W/8
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = ishpi[SPATIAL_D];
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-6]    = c;                            // C
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
  // writeback all lines
  HLAPI.i.u.op.out.fm.enable        = (int8_t)((1<<TNSVSIZE)-1);
}

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_intfp_params<B>::init_l1_output(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                ) {
  tensor_t<ixpix_t,5,BD> t2(p.data);
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t2.get_offset(2);                      // W
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(0);       // mlsb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(1);       // G
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(3);       // H
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(2)*TNSVSIZE; // W8
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(4);       // D
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-6] = 2*t2.get_offset(0);     // C
  // convert to relative to end of line
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    int os = HLAPI.i.u.op.out.fm.fm_agu.offsets[i];
    for (int j = i+1; j < ACT_FM_LOOPS; j++) {
      os += (1-HLAPI.i.u.op.out.fm.fm_agu.iter[j])*HLAPI.i.u.op.out.fm.fm_agu.offsets[j];
    }
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = os;
  }
}

template<template<typename> class B>
inline void gtoa_intfp_params<B>::get_shapes(
                      gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                      ) {
  s = shapes;
}


#undef HLAPI
