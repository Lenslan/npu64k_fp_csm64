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
 * tensor_gtoa_binary_ms_inline_legacy.hpp
 *
 * File defining a tensor level binary API base on the generic tensor operation API
 *
 */

#define HLAPI gtoa_params<B>::hlapi

// constructors
// input0 accumulator (32b) + input1 scalar register 0 to output feature-map (8b/16b)
template<template<typename> class B>
gtoa_binary_ms_params<B>::gtoa_binary_ms_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmodbli,       // 16b output feature-map
                                     act_bin_op_t               opi,           // binary operation to perform
                                     bool                       sati           // saturate output
                                     ) : gtoa_binary_params<B>(noi, oshpi, fmodbli, opi, sati) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (          0<<ACT_BF_OP_IN0DBL_START    ) |
                          (fmodbli ? 1<<ACT_BF_OP_OUTDBL_START : 0) |
                          (sati    ? 1<<ACT_BF_OP_OUTSAT_START : 0);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
}
// input0 feature-map (8b/16b) + input1 scalar register 0 to output feature-map (8b/16b)
template<template<typename> class B>
gtoa_binary_ms_params<B>::gtoa_binary_ms_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmidbli,       // 16b input feature-map
                                     bool                       fmodbli,       // 16b output feature-map
                                     act_bin_op_t               opi,           // binary operation to perform
                                     bool                       sati           // saturate output
                                     ) : gtoa_binary_params<B>(noi, oshpi, fmidbli, fmodbli, opi, sati) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (fmidbli?  1<<ACT_BF_OP_IN0DBL_START : 0) |
                          (          0<<ACT_BF_OP_IN1DBL_START    ) |
                          (fmodbli ? 1<<ACT_BF_OP_OUTDBL_START : 0) |
                          (sati    ? 1<<ACT_BF_OP_OUTSAT_START : 0);
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
}
// input0 accumulator (32b) + input1 scalar register 0 to output accumulator (32b)
template<template<typename> class B>
gtoa_binary_ms_params<B>::gtoa_binary_ms_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     act_bin_op_t               opi            // binary operation to perform
                                     ) : gtoa_binary_params<B>(noi, oshpi, opi) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = (          0<<ACT_BF_OP_IN0DBL_START    ) |
                          (          0<<ACT_BF_OP_OUTDBL_START    ) |
                          (          0<<ACT_BF_OP_OUTSAT_START    );
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
}
// input0 feature-map (8b/16b) + input1 scalar register 0 to output accumulator (32b)
template<template<typename> class B>
gtoa_binary_ms_params<B>::gtoa_binary_ms_params(
                                     aoffset_t                  noi,           // number output channels (not vectors)
                                     const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                                     bool                       fmidbli,       // 16b input feature-map
                                     act_bin_op_t               opi            // binary operation to perform
                                     ) : gtoa_binary_params<B>(noi, oshpi, fmidbli, opi) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = (fmidbli?  1<<ACT_BF_OP_IN0DBL_START : 0) |
                          (          0<<ACT_BF_OP_IN1DBL_START    ) |
                          (          0<<ACT_BF_OP_OUTDBL_START    ) |
                          (          0<<ACT_BF_OP_OUTSAT_START    );
  HLAPI.i.u.op.bf      |= ACT_BF_OP_IN0INT32_MASK | ACT_BF_OP_IN1INT32_MASK | ACT_BF_OP_OUTINT32_MASK;
}

#undef HLAPI
