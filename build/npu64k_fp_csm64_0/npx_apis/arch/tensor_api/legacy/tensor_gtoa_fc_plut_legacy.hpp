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
 * tensor_gtoa_fc_plut_legacy.hpp
 *
 * File defining a tensor level prelu API base on the generic tensor operation API
 *
 */

#ifndef TENSOR_API_LEGACY_TENSOR_GTOA_FC_PLUT_LEGACY_HPP_
#define TENSOR_API_LEGACY_TENSOR_GTOA_FC_PLUT_LEGACY_HPP_

//
// Constructor
//
// Input AM32/48, output FM8/16
gtoa_fc_plut_params(
    aoffset_t noi,              // number output channels (not vectors)
    bool      fmdbli,           // 16b output feature-map
    bool      inastri = false,  // if true then stream directly from convolution
    bool      poscli = false);  // if true then do post scaling

//
// Parameter encoding functions
//
// 32b/48b input, 8b output, no post-scaling
void param_enc(
    const tensor_t<int32_t, 1, xbuffer_t>&  bias,     // per channel bias
    const tensor_t<int8_t, 1, xbuffer_t>&   asymm,    // per channel output quantization offset
    // outputs, buffers preallocated by caller
    gtoa_params_impl_pchan<xbuffer_t>&      obuf);    // NOLINT [runtime/references]
// 32b/48b input, 16b output, no post-scaling
void param_enc(
    const tensor_t<int32_t, 1, xbuffer_t>&  bias,     // per channel bias
    // outputs, buffers preallocated by caller
    gtoa_params_impl_pchan<xbuffer_t>&      obuf);    // NOLINT [runtime/references]
// 32b/48b input, 8b output, with post-scaling
void param_enc(
    const tensor_t<int32_t, 1, xbuffer_t>&  bias,     // per channel bias
    const tensor_t<int16_t, 1, xbuffer_t>&  scale,    // per channel scaling factor
    const tensor_t<uint8_t, 1, xbuffer_t>&  shift,    // per channel shift right amount
    const tensor_t<int8_t, 1, xbuffer_t>&   asymm,    // per channel output quantization offset
    // outputs, buffers preallocated by caller
    gtoa_params_impl_pchan<xbuffer_t>&      obuf);    // NOLINT [runtime/references]
// 32b/48b input, 16b output, with post-scaling
void param_enc(
    const tensor_t<int32_t, 1, xbuffer_t>&  bias,     // per channel bias
    const tensor_t<int16_t, 1, xbuffer_t>&  scale,    // per channel scaling factor
    const tensor_t<uint8_t, 1, xbuffer_t>&  shift,    // per channel shift right amount
    // outputs, buffers preallocated by caller
    gtoa_params_impl_pchan<xbuffer_t>&      obuf);    // NOLINT [runtime/references]
#endif    // TENSOR_API_LEGACY_TENSOR_GTOA_FC_PLUT_LEGACY_HPP_
