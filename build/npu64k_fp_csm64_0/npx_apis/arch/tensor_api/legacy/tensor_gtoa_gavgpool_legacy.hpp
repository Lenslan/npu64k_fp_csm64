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
 * tensor_gtoa_gavgpool_legacy.hpp
 *
 * File defining a tensor level reduce API base on the generic tensor operation API
 *
 */

#ifndef TENSOR_API_LEGACY_TENSOR_GTOA_GAVGPOOL_LEGACY_HPP_
#define TENSOR_API_LEGACY_TENSOR_GTOA_GAVGPOOL_LEGACY_HPP_

//
// Constructor
//
// AM(32b) to AM(32b) or VM(8b/16b)
gtoa_gavgpool_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3>& ishpi,    // input shape, output inner is 1
    bool fmodbli,             // 16b output feature-map
    bool sati,                // do saturation
    bool useAcc,              // use previous accumulator value
    bool keepAcc);            // keep result in accumulator instead of output to VM

gtoa_gavgpool_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3>& ishpi,    // input shape, output inner is 1
    bool fmidbli,             // 16b input feature-map
    bool fmodbli,             // 16b output feature-map
    bool sati,                // do saturation
    bool useAcc,              // use previous accumulator value
    bool keepAcc);            // keep result in accumulator instead of output to VM

// multi-tile global average pool with VM input and intermediate and average output to AM
gtoa_gavgpool_params(
    aoffset_t       noi,      // number output channels (not vectors)
    const shape<3>& ishpi,    // input shape, output inner is 1
    const shape<2>& padlim,   // padding window
    size_t num,               // number of elements to be pooled
    bool fmidbli,             // 16b input feature-map
    bool useAcc,              // use previous accumulator value
    bool keepAcc);            // keep result in accumulator instead of output to VM

//
// Switch to feature-map output
//
template <template <typename> class BD = B>
void modif_out_fm(
                  aoffset_t                        noi,      // number output channels
                  bool                             fmodbli,  // 16b output feature-map
                  bool                             sati,     // saturate output
                  gtoa_params_impl_alt_fm&         a);       // NOLINT [runtime/references]

//
// Switch to accumulator output
//
void modif_out_acc(
                   aoffset_t                        noi,      // number output channels
                   gtoa_params_impl_alt_acc&        a);       // NOLINT [runtime/references]

//
// initialize the scale and shift parameters for global average pooling
//
void init_gavgpool_scale(
                         int16_t  scale,     // common scaling factor for all channels
                         uint8_t  shift);    // common shift left amount for all channels

//
// Switch function between initial tile accumulations (keepAcc=true)
// and final tile average (keepAcc=false)
//
void modif_func(bool keepAcc, gtoa_params_impl_modif&);

#endif    // TENSOR_API_LEGACY_TENSOR_GTOA_GAVGPOOL_LEGACY_HPP_
