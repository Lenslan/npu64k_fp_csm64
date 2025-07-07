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
 * tensor_gtoa_norm_inline.hpp
 *
 * File defining a tensor level norm API based on the generic tensor operation API
 *
 */
#define HLAPI gtoa_params<B>::hlapi

//
// L1 normalization methods
//
template<template<typename> class B>
gtoa_l1norm_params<B>::gtoa_l1norm_params(
                                          aoffset_t                noi,         // number output channels (not vectors)
                                          const shape<3>&          ishpi,       // input shape, indexed by spatial_axis_t
                                          bool                     fmdbli       // 16b input/output feature-map
                                         ) {
  // copy parameters
  fmdbl = fmdbli;
  // divide and round up channels and width by ISIZE
  int ich = (fmdbl?2:1)*((noi+ISIZE-1)/ISIZE);
  // divide and round up channels and width by ISIZE, output is [4][chan]
  int och = 4*((noi+ISIZE-1)/ISIZE);
  // input width rounded to vector size
  int iw = (ishpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // set shapes
  shapes.ishape = {(aoffset_t)ich, 1, (aoffset_t)(iw*TNSVSIZE), ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  shapes.oshape = {(aoffset_t)och, 1, 1, 1, 1};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf            = 0;       // function, not LUT init
  // input and output is feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  // input/output attributes
  HLAPI.i.u.op.bf  = 0; // no padding
  // enable zero padding
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PEN_MASK;                                     // enable input padding, pad to zero
  // double or single width inputs&outputs, output always double
  HLAPI.i.u.op.bf |= fmdbl ? ACT_BF_OP_IN0DBL_MASK | ACT_BF_OP_OUTDBL_MASK : ACT_BF_OP_OUTDBL_MASK;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = iw*ishpi[SPATIAL_H]*ishpi[SPATIAL_D]; // inner loop over spatial dimension
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = ich/(fmdbl?2:1);                      // outer loop over channels
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = 1;                                    // dummy loop 
  // primary feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = fmdbl?2:1;               // lsb/msb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = iw;                      // width/8
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = ishpi[SPATIAL_D];        // depth
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]   = ich/(fmdbl?2:1);         // channels/16
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS-1; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = och;                     // 16b per output and two outputs per channel: mantissa, exponent
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback one column
  HLAPI.i.u.op.out.fm.enable        = 1;
  // set padding window
  HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W]-1;
  HLAPI.i.u.op.padlim[SPATIAL_H] = ishpi[SPATIAL_H]-1;
  HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
  HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
  // input padding settings
  HLAPI.i.u.op.pad_stride                          = 1;
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.pad_offs[i][SPATIAL_W] = (1-iw)*TNSVSIZE;
    HLAPI.i.u.op.pad_offs[i][SPATIAL_H] = 1-ishpi[SPATIAL_H];
  }
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_H] = 1;
  // initialize L1 normalization microcode
  init_l1norm(HLAPI);
}

//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_l1norm_params<B>::init_l1_output(
                                          const impl_spec_container_t<BD>&    p           // structure with allocated buffers and tensors in L1 memory
                                          ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp=2][C]
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = 1;
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_l1norm_params<B>::init_l1_input(
                                         const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                         ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C]
  // fill the primary HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                       // unit stride in W dimension
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);        // msb/lsb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IW
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // ID
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = (fmdbl?2:1)*p.data.get_offset(0)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*p.data.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IC
}

//
// L2 normalization methods
//
template<template<typename> class B>
gtoa_l2norm_params<B>::gtoa_l2norm_params(
                                       aoffset_t                noi,         // number output channels (not vectors)
                                       const shape<3>&          ishpi,       // input shape, indexed by spatial_axis_t
                                       bool                     fmdbli       // 16b input/output feature-map
                                       ) {
  // copy parameters
  fmdbl = fmdbli;
  // divide and round up channels and width by ISIZE
  int ich = (fmdbl?2:1)*((noi+ISIZE-1)/ISIZE);
  // divide and round up channels and width by ISIZE, output is [4][chan]
  int och = 4*((noi+ISIZE-1)/ISIZE);
  // input width rounded to vector size
  int iw = (ishpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // set shapes
  shapes.ishape = {(aoffset_t)ich, 1, (aoffset_t)(iw*TNSVSIZE), ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  shapes.oshape = {(aoffset_t)och, 1, 1, 1, 1};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf            = 0;       // function, not LUT init
  // input and output is feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  // input/output attributes
  HLAPI.i.u.op.bf  = 0; // no padding
  // enable zero padding
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PEN_MASK;                                     // enable input padding, pad to zero
  // double or single width inputs&outputs, output always double
  HLAPI.i.u.op.bf |= fmdbl ? ACT_BF_OP_IN0DBL_MASK | ACT_BF_OP_OUTDBL_MASK : ACT_BF_OP_OUTDBL_MASK;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = iw*ishpi[SPATIAL_H]*ishpi[SPATIAL_D]; // inner loop over spatial dimension
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = ich/(fmdbl?2:1);                      // outer loop over channels
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = 1;                                    // dummy loop 
  // primary feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = fmdbl?2:1;               // lsb/msb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = iw;                      // width/8
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = ishpi[SPATIAL_D];        // depth
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]   = ich/(fmdbl?2:1);         // channels/16
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS-1; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = och;                     // 16b per output and two outputs per channel: mantissa, exponent
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback one column
  HLAPI.i.u.op.out.fm.enable        = 1;
  // set padding window
  HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W]-1;
  HLAPI.i.u.op.padlim[SPATIAL_H] = ishpi[SPATIAL_H]-1;
  HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
  HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
  // input padding settings
  HLAPI.i.u.op.pad_stride                          = 1;
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.pad_offs[i][SPATIAL_W] = (1-iw)*TNSVSIZE;
    HLAPI.i.u.op.pad_offs[i][SPATIAL_H] = 1-ishpi[SPATIAL_H];
  }
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_H] = 1;
  // initialize L1 normalization microcode
  init_l2norm(HLAPI);
}

//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_l2norm_params<B>::init_l1_output(
                                         const impl_spec_container_t<BD>&    p           // structure with allocated buffers and tensors in L1 memory
                                         ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp=2][C]
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = 1;
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_l2norm_params<B>::init_l1_input(
                                        const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C]
  // fill the primary HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                       // unit stride in W dimension
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);        // msb/lsb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IW
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // ID
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = (fmdbl?2:1)*p.data.get_offset(0)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*p.data.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IC
}

//
// Scaling methods
//

template<template<typename> class B> const int32_t gtoa_scale_params<B>::l1scale_16to16 = 13;
template<template<typename> class B> const int32_t gtoa_scale_params<B>::l1scale_16to8  = 13+8;
template<template<typename> class B> const int32_t gtoa_scale_params<B>::l1scale_8to16  = 13;   //?
template<template<typename> class B> const int32_t gtoa_scale_params<B>::l1scale_8to8   = 13+8; //?
template<template<typename> class B> const int32_t gtoa_scale_params<B>::l2scale_16to16 = 7;
template<template<typename> class B> const int32_t gtoa_scale_params<B>::l2scale_16to8  = 7+8;
template<template<typename> class B> const int32_t gtoa_scale_params<B>::l2scale_8to16  = 7;    //?
template<template<typename> class B> const int32_t gtoa_scale_params<B>::l2scale_8to8   = 7+8;  //?

template<template<typename> class B>
gtoa_scale_params<B>::gtoa_scale_params(
                                        aoffset_t                noi,                      // number output channels (not vectors)
                                        const shape<3>&          ishpi,                    // input shape, indexed by spatial_axis_t
                                        bool                     ifmdbli,                  // 8b or 16b input feature-map
                                        bool                     ofmdbli,                  // 8b or 16b output feature-map
                                        int32_t                  scale                     // output downscale type
                                       ) {
  // copy parameters
  ifmdbl = ifmdbli;
  ofmdbl = ofmdbli;
  // divide and round up channels and width by ISIZE
  int ich = (ifmdbl?2:1)*((noi+ISIZE-1)/ISIZE);
  int och = (ofmdbl?2:1)*((noi+ISIZE-1)/ISIZE);
  // divide and round up channels and width by ISIZE, recipt input is [4][chan]
  int tch = 4*((noi+ISIZE-1)/ISIZE);
  // input width rounded to vector size
  int iw = (ishpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
  // set shapes, input, secondary input, output
  shapes.ishape  = {(aoffset_t)ich, 1, (aoffset_t)(iw*TNSVSIZE), ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  shapes.i1shape = {(aoffset_t)tch, 1, 1, 1, 1};
  shapes.oshape  = {(aoffset_t)och, 1, (aoffset_t)(iw*TNSVSIZE), ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf            = 0;       // function, not LUT init
  // input and output is feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_FM1 | ACT_IO_EN_OFM;
  // input/output attributes
  HLAPI.i.u.op.bf  = 0; // no padding
  // enable zero padding
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PEN_MASK;                                     // enable input padding, pad to zero
  // double or single width inputs&outputs, output always double
  HLAPI.i.u.op.bf |= ifmdbl ? ACT_BF_OP_IN0DBL_MASK : 0;
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN1DBL_MASK;
  HLAPI.i.u.op.bf |= ofmdbl ? ACT_BF_OP_OUTDBL_MASK | ACT_BF_OP_OUTSAT_MASK : ACT_BF_OP_OUTSAT_MASK;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = iw*ishpi[SPATIAL_H]*ishpi[SPATIAL_D]; // inner loop over spatial dimension
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = ich/(ifmdbl?2:1);                    // outer loop over channels
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = 1;                                   // dummy loop 
  // primary feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = ifmdbl?2:1;              // lsb/msb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = iw;                      // width/8
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = ishpi[SPATIAL_D];        // depth
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]   = ich/(ifmdbl?2:1);        // channels/16
  // secondary inut: reciprocal scale
  for (int i = 0; i < ACT_FM_LOOPS-1; i++) {
    HLAPI.i.u.op.secondary.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.secondary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1] = tch;                     // 16b per output and two outputs per channel: mantissa, exponent
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]   = ofmdbl?2:1;              // lsb/msb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]   = iw;                      // width/8
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]   = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]   = ishpi[SPATIAL_D];        // depth
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]   = och/(ofmdbl?2:1);        // channels/16
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback one column
  HLAPI.i.u.op.out.fm.enable        = (1<<TNSVSIZE)-1;
  // set padding window
  HLAPI.i.u.op.padlim[SPATIAL_W] = ishpi[SPATIAL_W]-1;
  HLAPI.i.u.op.padlim[SPATIAL_H] = ishpi[SPATIAL_H]-1;
  HLAPI.i.u.op.padpos[SPATIAL_W] = 0;
  HLAPI.i.u.op.padpos[SPATIAL_H] = 0;
  // input padding settings
  HLAPI.i.u.op.pad_stride                          = 1;
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.pad_offs[i][SPATIAL_W] = (1-iw)*TNSVSIZE;
    HLAPI.i.u.op.pad_offs[i][SPATIAL_H] = 1-ishpi[SPATIAL_H];
  }
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_W] = TNSVSIZE;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_H] = 1;
  // initialize scale microcode
  init_scale(HLAPI);
  // the additional shift amount for different outputs goes into scalar 1
  HLAPI.i.u.op.scl[1] = scale;
}

//
// Assign scale memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_scale_params<B>::init_l1_input0(
                                       const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                       ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C]
  // fill the primary HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                       // unit stride in W dimension
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);        // msb/lsb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IW
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // ID
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = (ifmdbl?2:1)*p.data.get_offset(0)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*p.data.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IC
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_scale_params<B>::init_l1_input1(
                                         const impl_spec_container_t<BD>&    p           // structure with allocated buffers and tensors in L1 memory
                                         ) {
  gtoa_params<B>::i1tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp=2][C]
  // fill the HLAPI offset parameters
  HLAPI.i.u.op.secondary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.secondary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.secondary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.secondary.fm_agu.stride   = 1;
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_scale_params<B>::init_l1_output(
                                       const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                       ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C]
  // fill the primary HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = p.data.get_offset(2);                       // unit stride in W dimension
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);        // msb/lsb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IW
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IH
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // ID
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-5] = (ofmdbl?2:1)*p.data.get_offset(0)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4])*p.data.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // IC
}


template<template<typename> class B>
inline void gtoa_l1norm_params<B>::get_shapes(
                                            gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                                            ) {
  s = shapes;
}

template<template<typename> class B>
inline void gtoa_l2norm_params<B>::get_shapes(
                                            gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                                            ) {
  s = shapes;
}

template<template<typename> class B>
inline void gtoa_scale_params<B>::get_shapes(
                                          gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                                          ) {
  s = shapes;
}

#undef HLAPI

