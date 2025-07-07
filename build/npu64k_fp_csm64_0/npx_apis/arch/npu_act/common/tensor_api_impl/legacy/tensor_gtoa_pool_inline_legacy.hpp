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
 * tensor_gtoa_pool_inline_legacy.hpp
 *
 * File defining a tensor level pooling API based on the generic tensor operation API
 *
 */
#define HLAPI gtoa_params<B>::hlapi


//
// Maxpooling functions
//
template<template<typename> class B>
gtoa_maxpool_params<B>::gtoa_maxpool_params(
                                         aoffset_t                noi,         // number output channels (not vectors)
                                         const shape<2>&          oshpi,       // output shape, indexed by spatial_axis_t
                                         const shape<2>&          kshpi,       // kernel shape, indexed by spatial_axis_t
                                         const shape<2>&          kstri,       // kernel stride, indexed by spatial_axis_t
                                         const shape<2>&          padlimi,     // input padding boundaries
                                         bool                     fmdbli       // 16b input/output feature-map
                                         ) {
  // copy parameters
  fmdbl = fmdbli;
  str   = kstri;
  // derive shapes
  int iw = kshpi[SPATIAL_W]+kstri[SPATIAL_W]*(oshpi[SPATIAL_W]-1);
  int ih = kshpi[SPATIAL_H]+kstri[SPATIAL_H]*(oshpi[SPATIAL_H]-1);
  // round up width to TNSVSIZE
  int owrnd = TNSVSIZE*((oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE);
  // divide and round up channels by ISIZE
  int ich = (noi+ISIZE-1)/ISIZE;
  // set shapes
  shapes.ishape = {(aoffset_t)(fmdbl ? 2*ich : ich), 1, (aoffset_t)   iw,    (aoffset_t)ih, 1};
  shapes.oshape = {(aoffset_t)(fmdbl ? 2*ich : ich), 1, (aoffset_t)owrnd, oshpi[SPATIAL_H], 1};
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf            = 0;       // function, not LUT init
  // input and output is feature-map
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  // input/output attributes
  HLAPI.i.u.op.bf  = ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PMIN_MASK;            // enable input padding, pad to minint
  HLAPI.i.u.op.bf |= fmdbl ? ACT_BF_OP_IN0DBL_MASK | ACT_BF_OP_OUTDBL_MASK : 0; // double or single width inputs
  HLAPI.i.u.op.bf |= ACT_BF_OP_OUTSAT_MASK;                                     // saturate output feature-map
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  // no parameters
  HLAPI.i.u.op.bnum = 0;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = get_shape_size(kshpi);               // inner loop over the kernel
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = fmdbl ? get_shape_size(shapes.oshape)/(2*TNSVSIZE*ich) : get_shape_size(shapes.oshape)/(TNSVSIZE*ich); // middle loop spatial output
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = ich;                                 // outer loop channel
  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-6; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = fmdbl ? 2 : 1;           // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = kshpi[SPATIAL_W];        // kernel width
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = kshpi[SPATIAL_H];        // kernel height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = oshpi[SPATIAL_H];        // output height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]   = owrnd/TNSVSIZE;             // output width in vectors
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-6]   = ich;                     // channel vectors
  // input padding settings
  HLAPI.i.u.op.pad_stride                          = str[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_W] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_W] = 1-kshpi[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-4][SPATIAL_W] = 1-kshpi[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-5][SPATIAL_W] = 1-kshpi[SPATIAL_W]+TNSVSIZE*str[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-6][SPATIAL_W] = 1-kshpi[SPATIAL_W]-(owrnd-TNSVSIZE)*str[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_H] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-4][SPATIAL_H] = 1-kshpi[SPATIAL_H]+str[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-5][SPATIAL_H] = 1-kshpi[SPATIAL_H]+(1-oshpi[SPATIAL_H])*str[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-6][SPATIAL_H] = 1-kshpi[SPATIAL_H]+(1-oshpi[SPATIAL_H])*str[SPATIAL_H];
  // feature-map output AGU
  for (int i = 0; i < ACT_FM_LOOPS-4; i++) {
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = fmdbl ? 2 : 1;           // mlsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = oshpi[SPATIAL_H];        // output height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = owrnd/TNSVSIZE;             // output width in vectors
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = ich;                     // channel vectors
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback all lines
  HLAPI.i.u.op.out.fm.enable        = (1<<TNSVSIZE)-1;
  // set padding window
  HLAPI.i.u.op.padlim = padlimi;
  // initialize microcode
  init_maxpool(HLAPI);
}

//
// Sumpooling functions
//
// VM(8b/16b) to AM(32b)
template<template<typename> class B>
gtoa_sumpool_params<B>::gtoa_sumpool_params(
                                         aoffset_t                noi,         // number output channels (not vectors)
                                         const shape<2>&          oshpi,       // output shape, indexed by spatial_axis_t
                                         const shape<2>&          kshpi,       // kernel shape
                                         const shape<2>&          kstri,       // kernel stride
                                         const shape<2>&          padlimi,     // input padding boundaries
                                         bool                     fmdbli      // 16b input feature-map
                                         ) {
  // copy parameters
  ifmdbl = fmdbli;
  str   = kstri;
  cmax  = noi;
  // derive shapes
  int iw = kshpi[SPATIAL_W]+kstri[SPATIAL_W]*(oshpi[SPATIAL_W]-1);
  int ih = kshpi[SPATIAL_H]+kstri[SPATIAL_H]*(oshpi[SPATIAL_H]-1);
  // round up width to TNSVSIZE
  int w = ((oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE);
  int owrnd = TNSVSIZE*w;
  // divide and round up channels by ISIZE
  int ich = (noi+ISIZE-1)/ISIZE;
  // set shapes
  shapes.ishape = {(aoffset_t)(ifmdbl ? 2*ich : ich), 1, (aoffset_t)   iw,    (aoffset_t)ih, 1};
  shapes.oshape = {1, oshpi[SPATIAL_H], (aoffset_t)w, 1, (aoffset_t)ich};
  shapes.pshape = {(aoffset_t)(4*ich)};
  //
  // fill HLAPI parameters
  //
  // input is feature-map, and output is AM
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OAC;
  // input/output attributes
  HLAPI.i.u.op.bf  = ACT_BF_OP_IN0PEN_MASK;            // enable input padding, pad to minint
  HLAPI.i.u.op.bf |= ifmdbl ? ACT_BF_OP_IN0DBL_MASK : 0; // double or single width inputs
  HLAPI.i.u.op.bf |= ACT_BF_OP_OUTDBL_MASK;                                     // saturate output feature-map
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1] = get_shape_size(kshpi);               // inner loop over the kernel
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2] = get_shape_size(shapes.oshape);       // middle loop spatial output
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3] = ich;                                 // outer loop channel
  // feature-map input AGU
  for (int i = 0; i < ACT_FM_LOOPS-6; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]    = 1;
    HLAPI.i.u.op.primary.fm_agu.offsets[i] = 0;
  }
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = ifmdbl ? 2 : 1;          // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = kshpi[SPATIAL_W];        // kernel width
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = kshpi[SPATIAL_H];        // kernel height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = oshpi[SPATIAL_H];        // output height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]   = owrnd/TNSVSIZE;             // output width in vectors
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-6]   = ich;                     // channel vectors
  // input padding settings
  HLAPI.i.u.op.pad_stride                          = str[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_W] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_W] = 1-kshpi[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-4][SPATIAL_W] = 1-kshpi[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-5][SPATIAL_W] = 1-kshpi[SPATIAL_W]+TNSVSIZE*str[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-6][SPATIAL_W] = 1-kshpi[SPATIAL_W]-(owrnd-TNSVSIZE)*str[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_H] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-4][SPATIAL_H] = 1-kshpi[SPATIAL_H]+str[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-5][SPATIAL_H] = 1-kshpi[SPATIAL_H]+(1-oshpi[SPATIAL_H])*str[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-6][SPATIAL_H] = 1-kshpi[SPATIAL_H]+(1-oshpi[SPATIAL_H])*str[SPATIAL_H];
  // accumulator output AGU
  for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
    HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
    HLAPI.i.u.op.out.acc_agu.offsets[i] = 1; 
  }
  HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-1]    = 1;                       // mlsb
  HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-2]    = oshpi[SPATIAL_H];        // output height
  HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-3]    = w;                       // output width in vectors
  HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-4]    = ich;                     // channel vectors
  // set padding window
  HLAPI.i.u.op.padlim = padlimi;
  // initialize microcode
  init_sumpool(HLAPI);
}

//
// Averagepooling functions
//
// VM(8b/16b) to VM(8b/16b)
// processing loops outer to inner: W,H,C,Fh,Fw
template<template<typename> class B>
gtoa_avgpool_params<B>::gtoa_avgpool_params(
                                         aoffset_t                noi,         // number output channels (not vectors)
                                         const shape<2>&          oshpi,       // output shape, indexed by spatial_axis_t
                                         const shape<2>&          kshpi,       // kernel shape
                                         const shape<2>&          kstri,       // kernel stride
                                         const shape<2>&          padlimi,     // input padding boundaries
                                         bool                     fmdbli       // 16b input feature-map
                                         ) {
  // copy parameters
  ifmdbl = fmdbli;
  str    = kstri;
  cmax   = noi;
  // derive shapes
  int iw = kshpi[SPATIAL_W]+kstri[SPATIAL_W]*(oshpi[SPATIAL_W]-1);
  int ih = kshpi[SPATIAL_H]+kstri[SPATIAL_H]*(oshpi[SPATIAL_H]-1);
  // round up width to TNSVSIZE
  int w     = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);
  int owrnd = TNSVSIZE*w;
  // divide and round up channels by ISIZE
  int ich = RDIV_UP(noi, ISIZE);
  // set shapes
  shapes.ishape  = {(aoffset_t)(ifmdbl ? 2*ich : ich), 1, (aoffset_t)   iw,    (aoffset_t)ih, 1};
  shapes.i1shape = {                                1, 1, (aoffset_t)    w, oshpi[SPATIAL_H], 1};
  shapes.oshape  = {(aoffset_t)(ifmdbl ? 2*ich : ich), 1, (aoffset_t)owrnd, oshpi[SPATIAL_H], 1};
  shapes.pshape  = {0}; // no parameters
  HLAPI.i.u.op.bnum = 0;
  
  //
  // fill HLAPI parameters
  //
  HLAPI.i.bf            = 0;       // function, not LUT init
  // input is feature-map, and output is AM
  HLAPI.i.u.op.io_en = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  // input/output attributes
  HLAPI.i.u.op.bf  = ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PZERO_MASK; // enable input padding, pad to zero
  HLAPI.i.u.op.bf |= ifmdbl ? ACT_BF_OP_IN0DBL_MASK : 0;              // double or single width inputs
  HLAPI.i.u.op.bf |= ifmdbl ? ACT_BF_OP_OUTDBL_MASK : 0;              // double or single width outputs
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = get_shape_size(kshpi);                     // inner loop over the kernel
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = ich;                                       // middle loop channel
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = get_shape_size(shapes.oshape)/(TNSVSIZE*shapes.oshape[0]); // outer loop spatial output
  // default iterator values 1
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.secondary.fm_agu.iter[i] = 1;
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]    = 1;
  }
  // feature-map input AGU
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = ifmdbl ? 2 : 1;          // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = kshpi[SPATIAL_W];        // kernel width
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = kshpi[SPATIAL_H];        // kernel height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = ich;                     // channel vectors
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]   = oshpi[SPATIAL_H];        // output height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-6]   = w;                       // output width in vectors
  // feature-map input AGU
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1] = oshpi[SPATIAL_H];        // output height
  HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-2] = w;                       // output width
  // input padding settings
  HLAPI.i.u.op.pad_stride                          = str[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_W] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_W] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_W] = 1-kshpi[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-4][SPATIAL_W] = 1-kshpi[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-5][SPATIAL_W] = 1-kshpi[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-6][SPATIAL_W] = 1-kshpi[SPATIAL_W]+TNSVSIZE*str[SPATIAL_W];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-1][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-2][SPATIAL_H] = 0;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-3][SPATIAL_H] = 1;
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-4][SPATIAL_H] = 1-kshpi[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-5][SPATIAL_H] = 1-kshpi[SPATIAL_H]+str[SPATIAL_H];
  HLAPI.i.u.op.pad_offs[ACT_FM_LOOPS-6][SPATIAL_H] = 1-kshpi[SPATIAL_H]+(1-oshpi[SPATIAL_H])*str[SPATIAL_H];
  // accumulator output AGU
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = ifmdbl ? 2 : 1;          // mlsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = ich;                     // channel vectors
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = oshpi[SPATIAL_H];        // output height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = w;                       // output width in vectors
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback all lines
  HLAPI.i.u.op.out.fm.enable        = (1<<TNSVSIZE)-1;
  // set padding window
  HLAPI.i.u.op.padlim = padlimi;
  // initialize microcode
  init_avgpool(HLAPI, true);
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_avgpool_params<B>::init_l1_input1(
                                        const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                        ) {
  gtoa_params<B>::i1tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // fill the HLAPI offset parameters for the scaling
  HLAPI.i.u.op.secondary.fm_agu.ptr      = p.data.get_ptr();
  HLAPI.i.u.op.secondary.fm_agu.buf.base = p.data.get_base();
  HLAPI.i.u.op.secondary.fm_agu.buf.len  = p.data.get_size();
  HLAPI.i.u.op.secondary.fm_agu.stride   = 0;
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-1] = p.data.get_offset(3);         // H offset
  HLAPI.i.u.op.secondary.fm_agu.offsets[ACT_FM_LOOPS-2] = p.data.get_offset(2)+
    (1-HLAPI.i.u.op.secondary.fm_agu.iter[ACT_FM_LOOPS-1])*p.data.get_offset(3);        // W offset
}


// Transcode scaling parameters per spatial [H][W] to a tensor of ixpix_t [W/8][H]
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_avgpool_params<B>::scale_enc(
                   const tensor_t<uint16_t,2,xbuffer_t>&    scale,      // per channel scaling factor [H][W]
                   // outputs, buffers preallocated by caller
                   impl_spec_container_t<BD>&               scales      // output encoded parameters as tensor ixpix_t [W/8][H]
                   ) {
  assert(scales.data.get_dim(0) == 1 && "inner scales dimensions should be 1 i.e. 16 channel data");
  assert(scales.data.get_dim(1) == 1 && "inner scales dimensions should be 1 i.e. 16 channel data");
  assert(scales.data.get_dim(2) == RDIV_UP(scale.get_dim(0),(aoffset_t)TNSVSIZE) && "input scale and scales W dimension mismatch");
  assert(scales.data.get_dim(3) == scale.get_dim(1) && "input scale and scales H dimension mismatch");
  // transcode to array of 8*16b scale value and 8*16b shift values after transposing H and W
  const_tensor_iterator_t<uint16_t,2,xbuffer_t> sct(scale);
  tensor_iterator_t<ixpix_t,5,BD> tit(scales.data);
  int w = 0;
  do {
    ixpix_t v;
    // encode 8*uint16 scales
    for (int i = 0; i < (int)TNSVSIZE; i++) {
      if (w < scale.get_dim(0)) {
        int16_t sc = sct.read();
        fp_e5m10_t fsc(scl_fix2flt(sc, 47-16));
        v[i+0]     = (pix_t)(int)fsc.data;      // lsb in low part
        v[i+TNSVSIZE] = (pix_t)(int)(fsc.data>>8); // msb in high part
        sct.next();
      }
      w++;
    }
    tit.write(v);
    if (w >= scale.get_dim(0)) {
      w = 0;
    }
  } while (tit.next());
}

// Set fixed shift amounts
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_avgpool_params<B>::param_enc(
                                       // outputs, buffers preallocated by caller
                                       gtoa_params_impl_pchan<BD>&       obuf         // output encoded parameters
                                       ) {
  int16_t* bpars = reinterpret_cast<int16_t*>(obuf.tns.get_ptr());
  for (int i = 0; i < ISIZE; i++) {
    mem_write(bpars+i      , (int16_t)8);
  }
}

#undef HLAPI
