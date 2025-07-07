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
 * tensor_gtoa_eltop_fc_prelu_legacy.hpp
 *
 * File defining a tensor level fused element-wise add and prelu API base on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_ELTOP_FC_PRELU_LEGACY_INCLUDED
#define TENSOR_GTOA_ELTOP_FC_PRELU_LEGACY_INCLUDED

//
// All identifiers related to the tensor API go into namespace tensor::v200
//
//
// Constructor
//
gtoa_eltop_fc_prelu_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  bool                       fmidbli,       // 16b input secondary feature-map
                  bool                       fmodbli,       // 16b output feature-map
                  act_bin_op_t               opi,           // eltwise binary operation to perform
                  bool                       eltact=true,   // if true then first eltop then activ, else first activ then elto
                  bool                       inastri=false  // if true then stream directly from convolution
                  );

//
// Parameter encoding functions
//
void param_enc(const tensor_t<int32_t,1,xbuffer_t>&      bias,        // per channel bias [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      negscale,    // per channel negative scaling factor [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      posshift,    // per channel positive shift right amount [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      negshift,    // per channel negative shift right amount [Cout]
               const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
               // outputs, buffers preallocated by caller
               gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
               );
void param_enc(const tensor_t<int32_t,1,xbuffer_t>&      bias,        // per channel bias [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      negscale,    // per channel negative scaling factor [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      posshift,    // per channel positive shift right amount [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      negshift,    // per channel negative shift right amount [Cout]
               // outputs, buffers preallocated by caller
               gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
               );
#endif
