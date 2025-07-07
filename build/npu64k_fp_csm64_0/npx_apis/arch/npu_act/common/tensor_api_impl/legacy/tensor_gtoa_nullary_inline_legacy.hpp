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
 * tensor_gtoa_nullary_inline_legacy.hpp
 *
 * File defining a tensor level nullary API base on the generic tensor operation API
 *
 */
#define HLAPI gtoa_params<B>::hlapi

  // constructor
  // nullary operation to feature-map (8b/16b)
  template<template<typename> class B>
  gtoa_nullary_params<B>::gtoa_nullary_params(
                                       aoffset_t                  noi,           // number output channels (not vectors)
                                       const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                       bool                       fmdbli,        // 16b output feature-map
                                       act_nula_op_t              opi            // nullary operation to perform
                                       ) : gtoa_params<B>() {
    // enable feature-map output
    HLAPI.i.bf            = 0;       // function, not LUT init
    HLAPI.i.u.op.io_en    = ACT_IO_EN_OFM;
    HLAPI.i.u.op.bf       = (fmdbli  ? 1<<ACT_BF_OP_OUTDBL_START : 0) |
                            (          0<<ACT_BF_OP_OUTSAT_START    );
    cmax = noi;
    int c = (noi+ISIZE-1)/ISIZE;
    int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;

    // output feature-map in ixpix_t [D][H][W][C] format
    shapes.oshape = { (aoffset_t)(fmdbli  ? 2*c : c), 1, (aoffset_t)(w*TNSVSIZE), oshpi[SPATIAL_H], oshpi[SPATIAL_D] };
    // parameter dimension ixpix_t [C]
    shapes.pshape = { noi };
    switch (opi) {
      case op_null_getid :   init_nullary(HLAPI, op_getid); break;
      case op_null_strv :    init_nullary(HLAPI, op_strv);  break;
      case op_null_strc :    init_nullary(HLAPI, op_strc);  break;
      default: assert(0 && "unknown nullary instruction");
    }
    set_nullary_params();
  }

  // nullary operation to accumulator (32b)
  template<template<typename> class B>
  gtoa_nullary_params<B>::gtoa_nullary_params(
                                       aoffset_t                  noi,           // number output channels (not vectors)
                                       const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                       act_nula_op_t              opi            // nullary operation to perform
                                       ) : gtoa_params<B>() {
    // enable accumulator input and accumulator output
    HLAPI.i.bf            = 0;       // function, not LUT init
    HLAPI.i.u.op.io_en    = ACT_IO_EN_OAC;
    HLAPI.i.u.op.bf       = (          0<<ACT_BF_OP_OUTDBL_START    ) |
                            (          0<<ACT_BF_OP_OUTSAT_START    );
    cmax = noi;
    int c = (noi+ISIZE-1)/ISIZE;
    int w = (oshpi[SPATIAL_W]+TNSVSIZE-1)/TNSVSIZE;

    // output accumulator in vyixacc_t [C/ONN*ISIZE][D][W/TNSVSIZE][H][ONN] format
    shapes.oshape = { 1, oshpi[SPATIAL_H], (aoffset_t)w, oshpi[SPATIAL_D], (aoffset_t)c };
    
    shapes.pshape = { noi };
    switch (opi) {
      case op_null_getid :   init_nullary(HLAPI, op_getid); break;
      case op_null_strv :    init_nullary(HLAPI, op_strv);  break;
      case op_null_strc :    init_nullary(HLAPI, op_strc);  break;
      default: assert(0 && "unknown nullary instruction");
    }
    set_nullary_params();
  }
#undef HLAPI
