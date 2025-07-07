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
 * tensor_gtoa_transpose_inline.hpp
 *
 * File defining a tensor level transpose API based on the generic tensor operation API
 *
 */
#define HLAPI gtoa_params<B>::hlapi

// transpose
template<template<typename> class B>
gtoa_transpose_params<B>::gtoa_transpose_params(
                                             aoffset_t                noi,         // number output channels (not vectors)
                                             const shape<3>&          ishpi,       // input shape, indexed by spatial_axis_t
                                             bool                     fmdbli       // 16b input/output feature-map
                                             ) {
  // copy parameters
  fmdbl = fmdbli;
  // divide and round up channels and width by ISIZE
  int ich = ((fmdbl?2*noi:noi)+ISIZE-1)/ISIZE;
  int iw;
  if (TNSVSIZE == 8) {
    iw  = (ishpi[SPATIAL_W]+ISIZE-1)/ISIZE;
  } else {
    iw  = 4*(ishpi[SPATIAL_W]+ISIZE-1)/ISIZE;
  }
  int ow  = (ishpi[SPATIAL_W]+ISIZE-1)/ISIZE;
  // set shapes
  shapes.ishape = {(aoffset_t)ich, 1, ishpi[SPATIAL_W],  ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  shapes.oshape = {(aoffset_t)ow,  1, (aoffset_t)(ich*ISIZE), ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf            = 0;       // function, not LUT init
  // input and output is feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_FM1 | ACT_IO_EN_OFM;
  // input/output attributes
  HLAPI.i.u.op.bf  = 0; // no padding
  // double or single width inputs, output always double
  // HLAPI.i.u.op.bf |= fmdbl ? ACT_BF_OP_IN0DBL_MASK | ACT_BF_OP_OUTDBL_MASK : ACT_BF_OP_OUTDBL_MASK;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = ich;                                // inner loop over channels
  if (TNSVSIZE == 8) {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = iw;                                 // middle loop over width
  } else {
    HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = iw/4;                               // middle loop over width
  }
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = ishpi[SPATIAL_H]*ishpi[SPATIAL_D];  // outer loop over height&depth
  if (TNSVSIZE == 8) {
    // primary feature-map input AGU
    for (int i = 0; i < ACT_FM_LOOPS-4; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = ich;                     // i16 channel blocks
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = iw;                      // width/16
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = ishpi[SPATIAL_H];        // height
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = ishpi[SPATIAL_D];        // depth
    // secondary feature-map input AGU, same as primary
    for (int i = 0; i < ACT_FM_LOOPS-4; i++) {
      HLAPI.i.u.op.secondary.fm_agu.iter[i]    = 1;
      HLAPI.i.u.op.secondary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1] = ich;                     // i16 channel blocks
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2] = iw;                      // width/16
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3] = ishpi[SPATIAL_H];        // height
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-4] = ishpi[SPATIAL_D];        // depth
  } else {
    // primary feature-map input AGU
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
      HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = 4;                       // 4*v2
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = ich;                     // i16 channel blocks
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = iw/4;                    // width/16
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = ishpi[SPATIAL_H];        // height
    HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]   = ishpi[SPATIAL_D];        // depth
    // secondary feature-map input AGU, same as primary
    for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
      HLAPI.i.u.op.secondary.fm_agu.iter[i]    = 1;
      HLAPI.i.u.op.secondary.fm_agu.offsets[i] = 0;
    }
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1] = 4;                       // 4*v2
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2] = ich;                     // i16 channel blocks
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3] = iw/4;                    // width/16
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-4] = ishpi[SPATIAL_H];        // height
    HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-5] = ishpi[SPATIAL_D];        // depth
  }
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS-4; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  if (TNSVSIZE == 8) {
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = ich*2;                   // width/16
  } else {
    HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = ich*8;                   // width/4
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = ow;                      // i16 channels
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = ishpi[SPATIAL_D];        // depth
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback al columns
  HLAPI.i.u.op.out.fm.enable        = static_cast<int8_t>((1<<TNSVSIZE)-1);
  // initialize microcode
  init_transpose(HLAPI, TNSVSIZE == 2);
}

//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_transpose_params<B>::init_l1_output(
                                         const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                         ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W=ich*ISIZE][Grp=1][C=iw]

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = p.data.get_offset(2);                       // unit stride in W dimension
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(2)*TNSVSIZE;  // OW
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(0)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(2)*TNSVSIZE; // OC
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(0)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(2)*TNSVSIZE; // OH
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(0)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(2)*TNSVSIZE; // OD
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_transpose_params<B>::init_l1_input(
                                             const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                             ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  if (TNSVSIZE == 8) {
    // [D][H][W=iw*ISIZE][Grp][C=ich]
    // fill the primary HLAPI offset parameters
    HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
    HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
    HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
    HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                    // unit stride in W dimension
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);     // ich
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);    // OW
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(3)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);    // OH
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(4)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);    // OD

    // fill the secondary HLAPI offset parameters, shift tensor by TNSVSIZE in width dimension
    tensor_t<ixpix_t,5,BD> t1(p.data);
    t1.shift(2, TNSVSIZE);
    HLAPI.i.u.op.secondary.fm_agu.ptr      = t1.get_ptr();
    HLAPI.i.u.op.secondary.fm_agu.buf.base = t1.get_base();
    HLAPI.i.u.op.secondary.fm_agu.buf.len  = t1.get_size();
    HLAPI.i.u.op.secondary.fm_agu.stride   = t1.get_offset(2);                  // unit spatial element in W dimension
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-1] = t1.get_offset(0);   // ich
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-2] = t1.get_offset(2)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);  // OW
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-3] = t1.get_offset(3)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t1.get_offset(2)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);  // OH
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-4] = t1.get_offset(4)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3])*t1.get_offset(3)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*t1.get_offset(2)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);  // OD
  } else {
    tensor_t<ixpix_t,5,BD> t0(p.data);
    t0.resize(2, ROUND_UP(t0.get_dim(2),ISIZE));  // align input width on ISIZE, since 1K inner width loop is 4x unrolled
    // [D][H][W=iw*ISIZE][Grp][C=ich] --> [D][H][W/4][vi=4][Grp][C=ich]
    tensor_t<ixpix_t, 6, BD> ts0(t0.split(2, (t0.get_dim(2)/4)));
    // transpose to [D][H][W/4][Grp][C=ich][vi=4]
    tensor_t<ixpix_t, 6, BD> tt0(ts0.transpose({2, 0, 1, 3, 4, 5}));
    // fill the primary HLAPI offset parameters
    HLAPI.i.u.op.primary.fm_agu.ptr      = tt0.get_ptr();
    HLAPI.i.u.op.primary.fm_agu.buf.base = tt0.get_base();
    HLAPI.i.u.op.primary.fm_agu.buf.len  = tt0.get_size();
    HLAPI.i.u.op.primary.fm_agu.stride   = tt0.get_offset(0);                    // unit stride in W dimension
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = tt0.get_offset(0)*2*TNSVSIZE;  // vi=4
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = tt0.get_offset(1)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*tt0.get_offset(0)*2*TNSVSIZE; // ich
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = tt0.get_offset(3)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*tt0.get_offset(1)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*tt0.get_offset(0)*2*TNSVSIZE; // OW
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = tt0.get_offset(4)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*tt0.get_offset(3)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*tt0.get_offset(1)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*tt0.get_offset(0)*2*TNSVSIZE; // OH
    HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = tt0.get_offset(5)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*tt0.get_offset(4)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*tt0.get_offset(3)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*tt0.get_offset(1)+
      (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*tt0.get_offset(0)*2*TNSVSIZE; // OD

    // fill the secondary HLAPI offset parameters, shift tensor by TNSVSIZE in width dimension
    tensor_t<ixpix_t,5,BD> t1(p.data);
    t1.resize(2, ROUND_UP(t1.get_dim(2),ISIZE));  // align input width on ISIZE, since 1K inner width loop is 4x unrolled
    t1.shift(2, TNSVSIZE);
    // [D][H][W=iw*ISIZE][Grp][C=ich] --> [D][H][W/4][vi=4][Grp][C=ich]
    tensor_t<ixpix_t, 6, BD> ts1(t1.split(2, (t1.get_dim(2)/4)));
    // transpose to [D][H][W/4][Grp][C=ich][vi=4]
    tensor_t<ixpix_t, 6, BD> tt1(ts1.transpose({2, 0, 1, 3, 4, 5}));
    HLAPI.i.u.op.secondary.fm_agu.ptr      = tt1.get_ptr();
    HLAPI.i.u.op.secondary.fm_agu.buf.base = tt1.get_base();
    HLAPI.i.u.op.secondary.fm_agu.buf.len  = tt1.get_size();
    HLAPI.i.u.op.secondary.fm_agu.stride   = tt1.get_offset(0);                  // unit spatial element in W dimension
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-1] = tt1.get_offset(0)*2*TNSVSIZE;  // vi=4
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-2] = tt1.get_offset(1)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*tt1.get_offset(0)*2*TNSVSIZE; // ich
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-3] = tt1.get_offset(3)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*tt1.get_offset(1)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*tt1.get_offset(0)*2*TNSVSIZE; // OW
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-4] = tt1.get_offset(4)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3])*tt1.get_offset(3)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*tt1.get_offset(1)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*tt1.get_offset(0)*2*TNSVSIZE; // OH
    HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-5] = tt1.get_offset(5)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-4])*tt1.get_offset(4)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-3])*tt1.get_offset(3)*2*TNSVSIZE+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2])*tt1.get_offset(1)+
      (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*tt1.get_offset(0)*2*TNSVSIZE; // OD
  }
}

template<template<typename> class B>
inline void gtoa_transpose_params<B>::get_shapes(
                                            gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                                            ) {
  s = shapes;
}

#undef HLAPI
