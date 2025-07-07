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
 * tensor_gtoa_eltop_eltmul_inline_legacy.hpp
 *
 * File defining a tensor level eltwise operation fused with subsequent eltmul API base on the generic tensor operation API
 *
 */

#define HLAPI gtoa_params<B>::hlapi

// constructors

// input0 feature-map (8b/16b) + input1 feature-map (8b/16b) to output feature-map (8b/16b)
template<template<typename> class B>
gtoa_eltmul_params<B>::gtoa_eltmul_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmi0dbli,      // 16b input feature-map 0
                                     bool                       fmi1dbli,      // 16b input feature-map 1
                                     bool                       fmodbli        // 16b output feature-map
                                     ) : gtoa_binary_params<B>(noi, oshpi, fmi0dbli, fmi1dbli, fmodbli, op_mpyh, true) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_FM1 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (fmi0dbli? 1<<ACT_BF_OP_IN0DBL_START : 0) |
                          (fmi1dbli? 1<<ACT_BF_OP_IN1DBL_START : 0) |
                          (fmodbli ? 1<<ACT_BF_OP_OUTDBL_START : 0) |
                          (1<<ACT_BF_OP_OUTSAT_START);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
  fp16scl = true;
  gtoa_binary_params<B>::set_per_channel(ELTOP_ELTMUL_SCALE_PAR_PER_CHAN);
  poscl = true;
  spodd = (RDIV_UP(oshpi[SPATIAL_W],TNSVSIZE)*oshpi[SPATIAL_H]*oshpi[SPATIAL_D])%2;
}

// input0 feature-map (8b/16b) + input1 feature-map (8b/16b) to output accumulator (32b)
template<template<typename> class B>
gtoa_eltmul_params<B>::gtoa_eltmul_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmi0dbli,      // 16b input feature-map 0
                                     bool                       fmi1dbli       // 16b input feature-map 1
                                     ) : gtoa_binary_params<B>(noi, oshpi, fmi0dbli, fmi1dbli, op_mpyh) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_FM1 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = (fmi0dbli? 1<<ACT_BF_OP_IN0DBL_START : 0) |
                          (fmi1dbli? 1<<ACT_BF_OP_IN1DBL_START : 0);
  gtoa_binary_params<B>::set_per_channel(ELTOP_ELTMUL_SCALE_PAR_PER_CHAN);
  poscl = true;
}

//
// Parameter encoding functions
//
// BRH0: asymmetric output offset
// BRH1: posscale+posshift
// BRW1: asymmi0
// BRW2: asymmi1

template<template<typename> class B>
void gtoa_eltmul_params<B>::param_enc(
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymmi0,     // per channel zpa [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymmi1,     // per channel zpb [Cout]
                                  const tensor_t<int8_t,1,xbuffer_t>&       asymmo,      // per channel output quantization offset [Cout]
                                  const tensor_t<int16_t,1,xbuffer_t>&      scale,       // per channel positive scaling factor [Cout]
                                  const tensor_t<uint8_t,1,xbuffer_t>&      shift,       // per channel positive shift right amount [Cout]
                                  // outputs, buffers preallocated by caller
                                  gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
                                  ) {
  int8_t*  bpars   = (int8_t*)obuf.tns.get_ptr();
  // int8_t*  bparsc  = (int8_t*)bpars;              // pointer to start of BRB values
  int16_t* bparsh  = (int16_t*)bpars;             // pointer to start of BRH values
  int32_t* bparsw  = (int32_t*)bpars;             // pointer to start of BRW values
  aoffset_t j = 0;
  int ci = (gtoa_eltmul_params<B>::cmax+ISIZE-1)/ISIZE;
  for (int c = 0; c < ci; c++) {
    for (int i = 0; i < ISIZE; i++) {
      if (j < gtoa_eltmul_params<B>::cmax) {
        // calculate floating parameter
        fp_e8m23_t fasymmi0((float)(-asymmi0.read({j})));
        fp_e8m23_t fasymmi1((float)(-asymmi1.read({j})));
        int32_t    iasymm(asymmo.read({j}));
        int16_t    ipost((iasymm<<8) | prescale_t().data);
        fp_e5m10_t fposscale(scl_fix2flt(scale.read({j}), shift.read({j})));
        bparsh[2*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+0*ISIZE+i] = ipost;                // BRH0 postscale + offset
        bparsh[2*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fposscale.data;       // BRH1 scale
        bparsw[1*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+1*ISIZE+i] = fasymmi0.data;        // BRW1 bias 0
        bparsw[1*c*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN*ISIZE+2*ISIZE+i] = fasymmi1.data;        // BRW2 bias 1
        j++;
      }
    }
  }
}

