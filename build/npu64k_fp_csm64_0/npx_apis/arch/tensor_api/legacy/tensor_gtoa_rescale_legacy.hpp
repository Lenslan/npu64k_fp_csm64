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
 * tensor_gtoa_rescale_legacy.hpp
 *
 * File defining a tensor level rescale API base on the generic tensor operation API
 *
 */


#ifndef TENSOR_API_LEGACY_TENSOR_GTOA_RESCALE_LEGACY_HPP_
#define TENSOR_API_LEGACY_TENSOR_GTOA_RESCALE_LEGACY_HPP_

    //
    // Constructor
    //
    // Input AM32/48, output FM8/16
    gtoa_rescale_params(
                      aoffset_t                  noi,     // number output channels (not vectors)
                      const shape<3>&            oshpi,   // output shape, indexed by spatial_axis_t
                      const shape<3>&            ostr,    // output stride
                      bool                       accdbli,  // double wide input accumulator
                      bool                       fmdbli,  // 16b output feature-map
                      bool                       inastri = false);
                                                  // if true then stream directly from convolution
    // Input AM32/48, output AM32
    gtoa_rescale_params(
                      aoffset_t                  noi,     // number output channels (not vectors)
                      const shape<3>&            oshpi,   // output shape, indexed by spatial_axis_t
                      bool                       accdbli,  // double wide input accumulator
                      bool                       inastri = false);
                                                    // if true then stream directly from convolution
    //
    // Parameter encoding functions
    //
    // 32b input, 8b output

    void param_enc(
                   const tensor_t<int32_t, 1, xbuffer_t>& in_bias,
                                                                        // per channel bias [Cout]
                   const tensor_t<int16_t, 1, xbuffer_t>& scale,
                                                     // per channel positive scaling factor [Cout]
                   const tensor_t<uint8_t, 1, xbuffer_t>& shift,
                                                 // per channel positive shift right amount [Cout]
                   const tensor_t<int8_t, 1, xbuffer_t>& out_bias,
                                                  // per channel output quantization offset [Cout]
                                                  // outputs, buffers preallocated by caller
                   const gtoa_params_impl_pchan<xbuffer_t>& obuf);
                                                                      // output encoded parameters
    // 48b input, 8b output
    void param_enc(
                   const tensor_t<prescale_t, 1, xbuffer_t>&   prescale,
                                  // per channel 2b+6b prescale for scaling down wide accumulators
                   const tensor_t<int32_t, 1, xbuffer_t>&      in_bias,
                                                                        // per channel bias [Cout]
                   const tensor_t<int16_t, 1, xbuffer_t>&      scale,
                                                     // per channel positive scaling factor [Cout]
                   const tensor_t<uint8_t, 1, xbuffer_t>&      shift,
                                                 // per channel positive shift right amount [Cout]
                   const tensor_t<int8_t, 1, xbuffer_t>&       out_bias,
                                                  // per channel output quantization offset [Cout]
                                                  // outputs, buffers preallocated by caller
                   const gtoa_params_impl_pchan<xbuffer_t>&  obuf);
                                                                      // output encoded parameters

#endif  // TENSOR_API_LEGACY_TENSOR_GTOA_RESCALE_LEGACY_HPP_
