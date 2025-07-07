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
 * tensor_gtoa_shuffle_inline.hpp
 *
 * File defining a tensor level shuffle API based on the generic tensor operation API
 *
 */
#define HLAPI gtoa_params<B>::hlapi

//
// shuffle
//
template<template<typename> class B>
gtoa_shuffle_params<B>::gtoa_shuffle_params(
                                             aoffset_t                noi,         // number output channels (not vectors)
                                             const shape<3>&          ishpi,       // input shape, indexed by spatial_axis_t
                                             aoffset_t                grpi,        // number of groups
                                             bool                     fmdbli       // 16b input/output feature-map
                                             ) {
  // copy parameters
  fmdbl = fmdbli;
  grp = grpi;
  // compute group size and round up to multiples of TNSVSIZE 
  gs = TNSVSIZE*((ishpi[SPATIAL_W]+grp*TNSVSIZE-1)/(grp*TNSVSIZE));
  // input width rounded up to multiples of group size
  int iw = gs*grp;
  // divide and round up channels and width by ISIZE
  int ich = fmdbl? 2*RDIV_UP(noi, ISIZE) : RDIV_UP(noi, ISIZE);
  // set shapes
  shapes.ishape = {(aoffset_t)ich, 1, (aoffset_t)iw, ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  shapes.oshape = {(aoffset_t)ich, 1, (aoffset_t)iw, ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf            = 0;       // function, not LUT init
  // input and output is feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  // input/output attributes
  HLAPI.i.u.op.bf  = 0; // no padding
  // double or single width inputs&outputs
  HLAPI.i.u.op.bf |= fmdbl ? ACT_BF_OP_IN0DBL_MASK | ACT_BF_OP_OUTDBL_MASK : 0;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = fmdbl ? (ich/2) : ich;              // inner loop over channels
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = iw/TNSVSIZE;                           // middle loop over width
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = ishpi[SPATIAL_H]*ishpi[SPATIAL_D];  // outer loop over height&depth
  // primary feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-4; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = ich;                     // i16 channel blocks
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = iw/TNSVSIZE;                // width/16
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = ishpi[SPATIAL_D];        // depth
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = ich;                     // width/16
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = gs/TNSVSIZE;                // iterate over output groups (= input groups size)
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = iw/gs;                   // iterate over groups size (input groups)
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = ishpi[SPATIAL_D];        // depth
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback al columns
  HLAPI.i.u.op.out.fm.enable        = (1<<TNSVSIZE)-1;
  // initialize microcode = unary move = binary add with 2nd arg 0
  init_unary(HLAPI, op_add);
}

//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_shuffle_params<B>::init_l1_output(
                                         const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                         ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp=1][C]
  assert ((p.data.get_dim(2)%(grp*TNSVSIZE)) == 0 && "shuffle output feature-map W needs to be a multiple of grp*TNSVSIZE");

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = p.data.get_offset(2)*grp;                   // group size stride in W dimension
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);        // OC
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)*grp*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // next set in input channel group
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*grp*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // next input group, back to start of line +1
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*grp*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // OH
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-5] = p.data.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*grp*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);       // OD
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_shuffle_params<B>::init_l1_input(
                                        const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  assert ((p.data.get_dim(2)%(grp*TNSVSIZE)) == 0 && "shuffle input feature-map W needs to be a multiple of grp*TNSVSIZE");
  // [D][H][W][Grp][C]
  // fill the primary HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                    // unit stride in W dimension
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);     // ich
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);    // OW
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);    // OH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);    // OD
}


template<template<typename> class B>
inline void gtoa_shuffle_params<B>::get_shapes(
                                            gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                                            ) {
  s = shapes;
}


//
// shuffle optimized for group 2
//
template<template<typename> class B>
gtoa_shuffle_g2_params<B>::gtoa_shuffle_g2_params(
                                             aoffset_t                noi,         // number output channels (not vectors)
                                             const shape<3>&          ishpi,       // input shape, indexed by spatial_axis_t
                                             bool                     oddi,        // even or odd outputs
                                             bool                     fmdbli       // 16b input/output feature-map
                                             ) {
  // copy parameters
  fmdbl = fmdbli;
  odd   = oddi;
  // divide and round up channels and width by ISIZE
  int ich = fmdbl? 2*RDIV_UP(noi, ISIZE) : RDIV_UP(noi, ISIZE);
  int ow  = NRND_UP(ishpi[SPATIAL_W], TNSVSIZE);
  // set shapes
  shapes.ishape = {(aoffset_t)ich, 1, ishpi[SPATIAL_W], ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  shapes.oshape = {(aoffset_t)ich, 2, (aoffset_t)ow, ishpi[SPATIAL_H], ishpi[SPATIAL_D]};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf            = 0;       // function, not LUT init
  // input and output is feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  // input/output attributes
  HLAPI.i.u.op.bf  = 0; // no padding
  // double or single width inputs&outputs
  HLAPI.i.u.op.bf |= fmdbl ? ACT_BF_OP_IN0DBL_MASK | ACT_BF_OP_OUTDBL_MASK : 0;
  // no per-channel parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = fmdbl ? (ich/2) : ich;              // inner loop over channels
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = ow/TNSVSIZE;                           // middle loop over width
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = ishpi[SPATIAL_H]*ishpi[SPATIAL_D];  // outer loop over height&depth
  // primary feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-4; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = ich;                     // i16 channel blocks
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = ow/TNSVSIZE;                // width/8
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = ishpi[SPATIAL_D];        // depth
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = fmdbl?2:1;               // msb/lsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = 2;                       // even/odd
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = ich/(fmdbl?2:1);         // channels
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = ow/TNSVSIZE;                // width/8
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = ishpi[SPATIAL_H];        // height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-6]    = ishpi[SPATIAL_D];        // depth
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback al columns
  HLAPI.i.u.op.out.fm.enable        = (1<<TNSVSIZE)-1;
  // initialize microcode = unary move = binary add with 2nd arg 0
  init_shuffle(HLAPI, fmdbl, odd);
}

//
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_shuffle_g2_params<B>::init_l1_output(
                                         const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                         ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][G][C]

  // split and transpose channels to: [D][H][W][C][G2][lmsb]
  tensor_t<ixpix_t,6,B> t0(p.data.split(0, p.data.get_dim(0)/(fmdbl?2:1)));
  tensor_t<ixpix_t,6,B> t1(t0.transpose({0,2,1,3,4,5}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t1.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t1.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t1.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t1.get_offset(3);                       // unit stride in W dimension
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t1.get_offset(0);        // mlsb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t1.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);       // even/odd groups
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = t1.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t1.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);       // OC
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = t1.get_offset(3)*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t1.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t1.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);       // OW
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-5] = t1.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4])*t1.get_offset(3)*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t1.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t1.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);       // OH
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-6] = t1.get_offset(5)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5])*t1.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4])*t1.get_offset(3)*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t1.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t1.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t1.get_offset(0);       // OD
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_shuffle_g2_params<B>::init_l1_input(
                                        const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][G][C]

  // fill the primary HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = p.data.get_offset(2);                    // unit stride in W dimension
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(0);     // ich
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);    // OW
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);    // OH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = p.data.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*p.data.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*p.data.get_offset(2)*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(0);    // OD
}


template<template<typename> class B>
inline void gtoa_shuffle_g2_params<B>::get_shapes(
                                            gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                                            ) {
  s = shapes;
}

#undef HLAPI
