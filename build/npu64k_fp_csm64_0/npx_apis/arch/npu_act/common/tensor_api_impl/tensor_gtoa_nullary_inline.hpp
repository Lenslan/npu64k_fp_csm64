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
 * tensor_gtoa_nullary_inline.hpp
 *
 * File defining a tensor level nullary API base on the generic tensor operation API
 *
 */
#include "./legacy/tensor_gtoa_nullary_inline_legacy.hpp"
#define HLAPI gtoa_params<B>::hlapi

  // constructor
  template<template<typename> class B>
  gtoa_nullary_params<B>::gtoa_nullary_params(
                                       aoffset_t                  noi,           // number output channels (not vectors)
                                       const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                       act_nula_op_t              opi,           // nullary operation to perform
                                       act_dtype_t                tp             // output type
                                       ) : gtoa_params<B>() {
    // enable accumulator input and accumulator output
    HLAPI.i.bf            = 0;       // function, not LUT init
    HLAPI.i.u.op.io_en    = 0;
    bool odbl = (tp == dtype_int16) || (tp == dtype_fp16) || (tp == dtype_bf16);
    HLAPI.i.u.op.bf = (odbl ? 1 << ACT_BF_OP_OUTDBL_START : 0);
    // update mask and floating mode field based on input/output type
    switch (tp) {
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
    int c = (noi+ISIZE-1)/ISIZE;
    int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;
    if ((HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0) {
      // output feature-map in ixpix_t [D][H][W][C] format
      shapes.oshape = { (aoffset_t)(odbl  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    } else {
      // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
      shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    }
    // parameter dimension ixpix_t [C]
    shapes.pshape = { noi };
    switch (opi) {
      case op_null_getid :   init_nullary_fp(HLAPI, op_getid); break;
      case op_null_strv :    init_nullary_fp(HLAPI, op_strv);  break;
      case op_null_strc :    init_nullary_fp(HLAPI, op_strc);  break;
      default: assert(0 && "unknown nullary instruction");
    }
    set_nullary_params();
  }

  // set/get implementation specific parameters (dummy)
  template<template<typename> class B>
  void gtoa_nullary_params<B>::set_nullary_params()
  {
    int fmodbl  = (HLAPI.i.u.op.bf & ACT_BF_OP_OUTDBL_MASK) != 0 ? 2 : 1;
    bool ofm_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OFM) != 0;
    bool oac_en  = (HLAPI.i.u.op.io_en & ACT_IO_EN_OAC) != 0;

    // iterators
    if(ofm_en) {
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.oshape[0]/fmodbl;
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.oshape[2]*shapes.oshape[3]*shapes.oshape[4]/TNSVSIZE;
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.oshape[1];
    }
    else if(oac_en) {
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-3]   = shapes.oshape[4];
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-2]   = shapes.oshape[1]*shapes.oshape[2]*shapes.oshape[3];
      HLAPI.i.u.op.iter[ACT_HLAPI_LOOPS-1]   = shapes.oshape[0];
    }

    // feature-map output
    if(ofm_en) {
      for (int i = 0; i < ACT_FM_LOOPS-5; i++) {
        HLAPI.i.u.op.out.fm.fm_agu.iter[i]   = 1;
        HLAPI.i.u.op.out.fm.fm_agu.offsets[i] = 0;
      }
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1]    = fmodbl;            // mlsb
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2]    = shapes.oshape[3];  // H
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3]    = shapes.oshape[2]/TNSVSIZE;  // W/8
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4]    = shapes.oshape[4];  // D
      HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]    = shapes.oshape[0] / (fmodbl); // C
      // pooling parameters
      HLAPI.i.u.op.out.fm.pool.bf       = 0;  // disable maxpooling
      // writeback all lines
      HLAPI.i.u.op.out.fm.enable        = (int8_t)((1<<TNSVSIZE)-1);
    }
    // accumulator output
    if (oac_en) {
      for (int i = 0; i < ACT_AM_LOOPS-1; i++) {
        HLAPI.i.u.op.out.acc_agu.offsets[i] = 1;
        HLAPI.i.u.op.out.acc_agu.iter[i] = 1;
      }
      HLAPI.i.u.op.out.acc_agu.offsets[ACT_AM_LOOPS-1] = 1;
      HLAPI.i.u.op.out.acc_agu.iter[ACT_AM_LOOPS-1] = get_shape_size(shapes.oshape);
    }
  }

// initialize the output tensors
template<template<typename> class B>
template<template<typename> class BD>
void gtoa_nullary_params<B>::init_l1_output(
                                const impl_spec_container_t<BD>&  p            // structure with allocated buffers and tensors in L1 memory [D][H][W][Grp][C]
                                ) {
  gtoa_params<B>::tens = *reinterpret_cast<const impl_spec_container_t<B>*>(&p);
  // [D][H][W][Grp][C] --> [D][H][W/8][W8][Grp][C/(mlsb*onn)][mlsb*onn]
  tensor_t<ixpix_t,6,BD> t0(p.data.split(0, HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-5]));
  tensor_t<ixpix_t,7,BD> t1(t0.split(3, p.data.get_dim(2)/TNSVSIZE));
  // transpose to [Grp][C][D][W/8][H][ONN|msb|lsb][W8]
  tensor_t<ixpix_t,7,BD> t2(t1.transpose({3,0,5,4,6,1,2}));

  // fill the HLAPI offset parameters
  HLAPI.i.u.op.out.fm.fm_agu.ptr      = t2.get_ptr();
  HLAPI.i.u.op.out.fm.fm_agu.buf.base = t2.get_base();
  HLAPI.i.u.op.out.fm.fm_agu.buf.len  = t2.get_size();
  HLAPI.i.u.op.out.fm.fm_agu.stride   = t2.get_offset(0);                    // W8
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-1] = t2.get_offset(1);     // ONN
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-2] = t2.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // H
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-3] = t2.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // W
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-4] = t2.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // D
  HLAPI.i.u.op.out.fm.fm_agu.offsets[ACT_FM_LOOPS-5] = t2.get_offset(5)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-4])*t2.get_offset(4)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-3])*t2.get_offset(3)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-2])*t2.get_offset(2)+
    (1-HLAPI.i.u.op.out.fm.fm_agu.iter[ACT_FM_LOOPS-1])*t2.get_offset(1);    // C*GRP
}


template<template<typename> class B>
inline void gtoa_nullary_params<B>::get_shapes(
                      gtoa_act_params_impl_shapes& s            // structure with implementation specific minimum buffer sizes
                      ) {
  s = shapes;
}

#undef HLAPI
