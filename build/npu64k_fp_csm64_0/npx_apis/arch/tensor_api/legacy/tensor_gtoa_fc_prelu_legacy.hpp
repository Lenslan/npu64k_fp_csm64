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
 * tensor_gtoa_fc_prelu_legacy.hpp
 *
 * File defining a tensor level prelu API base on the generic tensor operation API
 *
 */


#ifndef TENSOR_GTOA_FC_PRELU_LEGACY_INCLUDED
#define TENSOR_GTOA_FC_PRELU_LEGACY_INCLUDED


//
// All identifiers related to the tensor API go into namespace tensor::v200
//

//
// Constructor
//
// Input AM32/48, output FM8/16
gtoa_fc_prelu_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  bool                       fmdbli,        // 16b output feature-map
                  bool                       inastri=false  // if true then stream directly from convolution
                  );

//
// Parameter encoding functions
//
// 32b/48b input, 8b output
void param_enc(const tensor_t<int32_t,1,xbuffer_t>&      bias,        // per channel bias [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      negscale,    // per channel negative scaling factor [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      posshift,    // per channel positive shift right amount [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      negshift,    // per channel negative shift right amount [Cout]
               const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
               // outputs, buffers preallocated by caller
               gtoa_params_impl_pchan<xbuffer_t>&         obuf         // output encoded parameters
               );
// 32b/48b input, 16b output
void param_enc(const tensor_t<int32_t,1,xbuffer_t>&      bias,        // per channel bias [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      negscale,    // per channel negative scaling factor [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      posshift,    // per channel positive shift right amount [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      negshift,    // per channel negative shift right amount [Cout]
               // outputs, buffers preallocated by caller
               gtoa_params_impl_pchan<xbuffer_t>&         obuf         // output encoded parameters
               );
#endif
