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
#ifndef NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_BINARY_SEL_MM_INLINE_HPP_
#define NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_BINARY_SEL_MM_INLINE_HPP_
/*
 * tensor_gtoa_binary_sel_mm_inline.hpp
 *
 * File defining a tensor level binary API base on the generic tensor operation API
 *
 */

#define HLAPI gtoa_params<B>::hlapi

// constructors
// input0 accumulator (32b) + input1 accumulator (32b) to output feature-map (8b/16b)
template<template<typename> class B>
gtoa_binary_sel_mm_params<B>::gtoa_binary_sel_mm_params(
           aoffset_t               noi,      // number output channels (not vectors)
           const shape<3>&         oshpi,    // output shape, indexed by spatial_axis_t
           bool                    fmodbli,  // 16b output feature-map
           act_bin_op_t            opi,      // binary operation to perform
           bool                    sati)     // saturate output
           : gtoa_binary_params<B>(noi, oshpi, fmodbli, opi, sati) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_AC1 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       =           (0 << ACT_BF_OP_IN0DBL_START)     |
                          (fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                          (sati    ? 1 << ACT_BF_OP_OUTSAT_START : 0);
}
// input0 feature-map (8b/16b) + input1 accumulator (32b) to output feature-map (8b/16b)
template<template<typename> class B>
gtoa_binary_sel_mm_params<B>::gtoa_binary_sel_mm_params(
           aoffset_t               noi,      // number output channels (not vectors)
           const shape<3>&         oshpi,    // output shape, indexed by spatial_axis_t
           bool                    fmidbli,  // 16b input feature-map
           bool                    fmodbli,  // 16b output feature-map
           act_bin_op_t            opi,      // binary operation to perform
           bool                    sati)     // saturate output
           : gtoa_binary_params<B>(noi, oshpi, fmidbli, fmodbli, opi, sati) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_AC1 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (fmidbli?  1 << ACT_BF_OP_IN0DBL_START : 0) |
                                    (0 << ACT_BF_OP_IN1DBL_START)     |
                          (fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                          (sati    ? 1 << ACT_BF_OP_OUTSAT_START : 0);
}
// input0 feature-map (8b/16b) + input1 feature-map (8b/16b) to output feature-map (8b/16b)
template<template<typename> class B>
gtoa_binary_sel_mm_params<B>::gtoa_binary_sel_mm_params(
           aoffset_t               noi,       // number output channels (not vectors)
           const shape<3>&         oshpi,     // output shape, indexed by spatial_axis_t
           bool                    fmi0dbli,  // 16b input feature-map 0
           bool                    fmi1dbli,  // 16b input feature-map 1
           bool                    fmodbli,   // 16b output feature-map
           act_bin_op_t            opi,       // binary operation to perform
           bool                    sati)      // saturate output
           : gtoa_binary_params<B>(noi, oshpi, fmi0dbli, fmi1dbli, fmodbli, opi, sati) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_FM1 | ACT_IO_EN_OFM;
  HLAPI.i.u.op.bf       = (fmi0dbli? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                          (fmi1dbli? 1 << ACT_BF_OP_IN1DBL_START : 0) |
                          (fmodbli ? 1 << ACT_BF_OP_OUTDBL_START : 0) |
                          (sati    ? 1 << ACT_BF_OP_OUTSAT_START : 0);
}
// input0 accumulator (32b) + input1 accumulator (32b) to output accumulator (32b)
template<template<typename> class B>
gtoa_binary_sel_mm_params<B>::gtoa_binary_sel_mm_params(
           aoffset_t               noi,    // number output channels (not vectors)
           const shape<3>&         oshpi,  // output shape, indexed by spatial_axis_t
           act_bin_op_t            opi)    // binary operation to perform
           : gtoa_binary_params<B>(noi, oshpi, opi) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_AC0 | ACT_IO_EN_AC1 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = (0 << ACT_BF_OP_IN0DBL_START) |
                          (0 << ACT_BF_OP_OUTDBL_START) |
                          (0 << ACT_BF_OP_OUTSAT_START);
}
// input0 feature-map (8b/16b) + input1 accumulator (32b) to output accumulator (32b)
template<template<typename> class B>
gtoa_binary_sel_mm_params<B>::gtoa_binary_sel_mm_params(
           aoffset_t               noi,      // number output channels (not vectors)
           const shape<3>&         oshpi,    // output shape, indexed by spatial_axis_t
           bool                    fmidbli,  // 16b input feature-map
           act_bin_op_t            opi)      // binary operation to perform
           : gtoa_binary_params<B>(noi, oshpi, fmidbli, opi) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_AC1 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = (fmidbli?  1 << ACT_BF_OP_IN0DBL_START : 0) |
                                    (0 << ACT_BF_OP_IN1DBL_START)     |
                                    (0 << ACT_BF_OP_OUTDBL_START)     |
                                    (0 << ACT_BF_OP_OUTSAT_START);
}
// input0 feature-map (8b/16b) + input1 feature-map (8b/16b) to output accumulator (32b)
template<template<typename> class B>
gtoa_binary_sel_mm_params<B>::gtoa_binary_sel_mm_params(
           aoffset_t               noi,       // number output channels (not vectors)
           const shape<3>&         oshpi,     // output shape, indexed by spatial_axis_t
           bool                    fmi0dbli,  // 16b input feature-map 0
           bool                    fmi1dbli,  // 16b input feature-map 1
           act_bin_op_t            opi)       // binary operation to perform
           : gtoa_binary_params<B>(noi, oshpi, fmi0dbli, fmi1dbli, opi) {
  HLAPI.i.u.op.io_en    = ACT_IO_EN_FM0 | ACT_IO_EN_FM1 | ACT_IO_EN_OAC;
  HLAPI.i.u.op.bf       = (fmi0dbli? 1 << ACT_BF_OP_IN0DBL_START : 0) |
                          (fmi1dbli? 1 << ACT_BF_OP_IN1DBL_START : 0) |
                                    (0 << ACT_BF_OP_OUTDBL_START)     |
                                    (0 << ACT_BF_OP_OUTSAT_START);
}
template<template<typename> class B>
void gtoa_binary_sel_mm_params<B>::init_bin_prog(act_bin_op_t opi, broadcast_t brdc_f) {
  // initialize the binary_sel_mm microcode
  init_binary_sel_rr(HLAPI, opi);
}

#undef HLAPI

#endif  // NPU_ACT_COMMON_TENSOR_API_IMPL_TENSOR_GTOA_BINARY_SEL_MM_INLINE_HPP_
