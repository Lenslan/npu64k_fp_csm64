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
 * tensor_gtoa_pool_inline.hpp
 *
 * File defining a tensor level pooling API based on the generic tensor operation API
 *
 */
#include "./legacy/tensor_gtoa_pool_inline_legacy.hpp"
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
                                         act_dtype_t              intp,        // input feature-map type
                                         act_dtype_t              outtp        // output feature-map type
                                         ) {
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  bool idbl = (intp  == dtype_int16) || (intp  == dtype_fp16) || (intp  == dtype_bf16);
  bool odbl = (outtp == dtype_int16) || (outtp == dtype_fp16) || (outtp == dtype_bf16);
  assert(idbl == odbl && "input/output double mode should be the same for pooling");
  HLAPI.i.u.op.bf = (idbl ? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                    (odbl ? 1 << ACT_BF_OP_OUTDBL_START : 0);
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PMIN_MASK;            // enable input padding, pad to minint
  switch (intp) {
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
    default: assert(0 && "unsupported input datatype!");
  }
  switch (outtp) {
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
    default: assert(0 && "unsupported output datatype!");
  }
  // copy parameters
  fmdbl = idbl;
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
// Assign L1 memory buffer addresses
//
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_maxpool_params<B>::init_l1_output(
                                         const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                         ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/mlsb][mlsb]
  tensor_t<ixpix_t,6,BD> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t0.get_offset(3);                    // unit stride
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t0.get_offset(0);     // msb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t0.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OH
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = t0.get_offset(3)*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OW
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = t0.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(3)*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OC
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_maxpool_params<B>::init_l1_input(
                                        const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/mlsb][mlsb]
  tensor_t<ixpix_t,6,BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-6]));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = t0.get_offset(3)*str[SPATIAL_W];     // offset to spatial element in W dimension
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = t0.get_offset(0);     // msb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // kw
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // kh
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = t0.get_offset(4)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = t0.get_offset(3)*str[SPATIAL_W]*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*t0.get_offset(4)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OW
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-6] = t0.get_offset(1)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5])*t0.get_offset(3)*str[SPATIAL_W]*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*t0.get_offset(4)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OC
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
                                         act_dtype_t              intp,        // type of input
                                         act_dtype_t              outtp        // type of output
                                         ) {
  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  bool idbl = (intp  == dtype_int16) || (intp  == dtype_fp16) || (intp  == dtype_bf16);
  HLAPI.i.u.op.bf = (idbl ? 1 << ACT_BF_OP_IN0DBL_START : 0);
  HLAPI.i.u.op.bf |= ACT_BF_OP_IN0PEN_MASK;            // enable input padding, pad to minint
  switch (intp) {
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
    default: assert(0 && "unsupported input datatype!");
  }
  switch (outtp) {
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
  // copy parameters
  ifmdbl = idbl;
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
// Average pooling functions
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
                                         act_dtype_t              in0tp,       // type of input 0
                                         act_dtype_t              outtp,       // type of output
                                         bool                     excl_pad     // exclude padding
                                         ) {
  assert (get_shape_size(kshpi) <= 16 && "fast average pooling requires filters kw*kh<=16");
  // round parameters
  cmax = noi;
  int c = RDIV_UP(noi, ISIZE);
  int w = RDIV_UP(oshpi[SPATIAL_W], TNSVSIZE);
  str = kstri;

  HLAPI.i.bf            = 0;       // function, not LUT init
  HLAPI.i.u.op.io_en    = 0;
  switch (in0tp) {
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, (aoffset_t)(kshpi[SPATIAL_W]+(oshpi[SPATIAL_W]-1)*kstri[SPATIAL_W]), (aoffset_t)(kshpi[SPATIAL_H]+(oshpi[SPATIAL_H]-1)*kstri[SPATIAL_H]), 1};
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)c, 1, (aoffset_t)(kshpi[SPATIAL_W]+(oshpi[SPATIAL_W]-1)*kstri[SPATIAL_W]), (aoffset_t)(kshpi[SPATIAL_H]+(oshpi[SPATIAL_H]-1)*kstri[SPATIAL_H]), 1 };
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, (aoffset_t)(kshpi[SPATIAL_W]+(oshpi[SPATIAL_W]-1)*kstri[SPATIAL_W]), (aoffset_t)(kshpi[SPATIAL_H]+(oshpi[SPATIAL_H]-1)*kstri[SPATIAL_H]), 1};
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_FM0;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_IN0DBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_IN0FMODE_START;
    shapes.ishape          = { (aoffset_t)(2*c), 1, (aoffset_t)(kshpi[SPATIAL_W]+(oshpi[SPATIAL_W]-1)*kstri[SPATIAL_W]), (aoffset_t)(kshpi[SPATIAL_H]+(oshpi[SPATIAL_H]-1)*kstri[SPATIAL_H]), 1};
    break;
  default:
    assert(0 && "unsupported input type");
  }

  switch (outtp) {
  case dtype_int16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], 1 };
    break;
  case dtype_int8:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 0<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_INT << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)c, 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], 1 };
    break;
  case dtype_fp16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_FP16 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], 1 };
    break;
  case dtype_bf16:
    HLAPI.i.u.op.io_en    |= ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       |= 1<<ACT_BF_OP_OUTDBL_START;
    HLAPI.i.u.op.bf       |= ACT_BF_OP_FMODE_BF16 << ACT_BF_OP_OUTFMODE_START;
    shapes.oshape          = { (aoffset_t)(2*c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], 1 };
    break;
  default:
    assert(0 && "unsupported output type");
  }
  shapes.pshape = {0};  // no parameters
  HLAPI.i.u.op.bnum = 0;

  // iterators
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = get_shape_size(kshpi);                   // inner loop over the kernel
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = c;                                       // middle loop channel
  HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = get_shape_size(shapes.oshape)/(TNSVSIZE*c*(((HLAPI.i.u.op.bf&(1<<ACT_BF_OP_OUTDBL_START)) != 0) ? 2 : 1)); // outer loop spatial output
  // default iterator values 1
  for (int i = 0; i < ACT_FM_LOOPS; i++) {
    HLAPI.i.u.op.primary.fm_agu.iter[i]   = 1;
    HLAPI.i.u.op.out.fm.fm_agu.iter[i]    = 1;
  }
  // feature-map input AGU
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1]   = ((HLAPI.i.u.op.bf&(1<<ACT_BF_OP_IN0DBL_START)) != 0) ? 2 : 1;  // mlsb
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2]   = kshpi[SPATIAL_W];        // kernel width
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3]   = kshpi[SPATIAL_H];        // kernel height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]   = c;                       // channel vectors
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5]   = oshpi[SPATIAL_H];        // output height
  HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-6]   = w;                       // output width in vectors
  // input padding settings, pad by zero
  HLAPI.i.u.op.bf |=   ACT_BF_OP_IN0PEN_MASK | ACT_BF_OP_IN0PZERO_MASK;
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
  // feature-map output AGU
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]   = ((HLAPI.i.u.op.bf&(1<<ACT_BF_OP_OUTDBL_START)) != 0) ? 2 : 1;   // mlsb
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]   = c;                       // channel vectors
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]   = oshpi[SPATIAL_H];        // output height
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]   = w;                       // output width in vectors
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]   = 1;
  HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-6]   = 1;
  // pooling parameters
  HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable fused maxpooling
  // writeback all lines
  HLAPI.i.u.op.out.fm.enable        = (1<<TNSVSIZE)-1;
  // set padding window
  HLAPI.i.u.op.padlim               = padlimi;
  // initialize microcode
  init_avgpool(HLAPI, excl_pad);
  // set scalar value to 1/F
  fp_e8m23_t scale((float)(1.0f/get_shape_size(kshpi)));
  HLAPI.i.u.op.scl[0] = static_cast<uint32_t>(scale);
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_avgpool_params<B>::init_l1_input0(
                                        const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/mlsb][mlsb]
  tensor_t<ixpix_t,6,BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4]));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = t0.get_offset(3)*str[SPATIAL_W];     // offset to spatial element in W dimension
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = t0.get_offset(0);     // msb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // kw
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // kh
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = t0.get_offset(1)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OC
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = t0.get_offset(4)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*t0.get_offset(1)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-6] = t0.get_offset(3)*str[SPATIAL_W]*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5])*t0.get_offset(4)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*t0.get_offset(1)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OW
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_avgpool_params<B>::init_l1_output(
                                        const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                        ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W][Grp][C/mlsb][mlsb]
  tensor_t<ixpix_t,6,BD> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t0.get_offset(3);                    // offset to spatial element in W dimension
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t0.get_offset(0);     // msb
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t0.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OC
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = t0.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OH
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = t0.get_offset(3)*TNSVSIZE+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(1)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OW
}

template<template<typename> class B>
template<template<typename> class BD>
void gtoa_sumpool_params<B>::init_l1_input(
                                        const impl_spec_container_t<BD>&    p            // structure with allocated buffers and tensors in L1 memory
                                        ) {
  gtoa_params<B>::itens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
 
 // [D][H][W][Grp][C] --> [D][H][W][Grp][C/mlsb][mlsb]
  tensor_t<ixpix_t,6,BD> t0(p.data.split(0, HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-6]));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.primary.fm_agu.ptr      = t0.get_ptr();
  HLAPI.i.u.op.primary.fm_agu.buf.base = t0.get_base();
  HLAPI.i.u.op.primary.fm_agu.buf.len  = t0.get_size();
  HLAPI.i.u.op.primary.fm_agu.stride   = t0.get_offset(3)*str[SPATIAL_W];     // offset to spatial element in W dimension
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-1] = t0.get_offset(0);     // msb
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-2] = t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // kw
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-3] = t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // kh
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-4] = t0.get_offset(4)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OH
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-5] = t0.get_offset(3)*str[SPATIAL_W]*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*t0.get_offset(4)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OW
  HLAPI.i.u.op.primary.fm_agu.offsets[ACT_FM_LOOPS-6] = t0.get_offset(1)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-5])*t0.get_offset(3)*str[SPATIAL_W]*TNSVSIZE+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-4])*t0.get_offset(4)*str[SPATIAL_H]+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-3])*t0.get_offset(4)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-2])*t0.get_offset(3)+
    (1-HLAPI.i.u.op.primary.fm_agu.iter[ACT_FM_LOOPS-1])*t0.get_offset(0);    // OC
}

//
// Shape functions
//
template<template<typename> class B>
inline void gtoa_maxpool_params<B>::get_shapes(
                                          gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                                          ) {
  s = shapes;
}

template<template<typename> class B>
inline void gtoa_sumpool_params<B>::get_shapes(
                                          gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                                          ) {
  s = shapes;
}

template<template<typename> class B>
inline void gtoa_avgpool_params<B>::get_shapes(
                                          gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                                          ) {
  s = shapes;
}

//
// packing mode
//
template<template<typename> class B>
void gtoa_maxpool_params<B>::set_pack_mode(
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

template<template<typename> class B>
void gtoa_sumpool_params<B>::set_pack_mode(
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

template<template<typename> class B>
void gtoa_avgpool_params<B>::set_pack_mode(
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

#undef HLAPI

