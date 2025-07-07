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
 * tensor_gtoa_eltop_prelu_legacy.hpp
 *
 * File defining a tensor level fused element-wise add and prelu API base on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_ELTOP_PRELU_LEGACY_INCLUDED
#define TENSOR_GTOA_ELTOP_PRELU_LEGACY_INCLUDED

//
// All identifiers related to the tensor API go into namespace tensor::v200
//
//
// Constructor
//
// Input AM32/48, output FM8/16
gtoa_eltop_prelu_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                  const shape<3>&            ostr,          // output stride
                  act_bin_op_t               opi,           // eltwise binary operation to perform
                  bool                       accdbli,       // double wide input accumulator
                  bool                       fmidbli,       // 16b input secondary feature-map
                  bool                       fmodbli,       // 16b output feature-map
                  bool                       eltact=true,   // if true then first eltop then activ, else first activ then elto
                  bool                       inastri=false  // if true then stream directly from convolution
                  );
// Input AM32/48, output AM32
gtoa_eltop_prelu_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                  act_bin_op_t               opi,           // eltwise binary binary operation to perform
                  bool                       accdbli,       // double wide input accumulator
                  bool                       fmidbli,       // 16b input secondary feature-map
                  bool                       eltact=true,   // if true then first eltop then activ, else first activ then elto
                  bool                       inastri=false  // if true then stream directly from convolution
                  );
//
// Parameter encoding functions
//
void param_enc(const tensor_t<prescale_t,1,xbuffer_t>&   prescale0,   // per channel 2b+6b prescale for scaling input accum
               const tensor_t<prescale_t,1,xbuffer_t>&   prescale1,   // per channel 2b+6b prescale for scaling input feature-map
               const tensor_t<int32_t,1,xbuffer_t>&      bias,        // per channel bias [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      negscale,    // per channel negative scaling factor [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      posshift,    // per channel positive shift right amount [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      negshift,    // per channel negative shift right amount [Cout]
               const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
               // outputs, buffers preallocated by caller
               gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
               );
void param_enc(const tensor_t<int16_t,1,xbuffer_t>&      prescale0,   // per channel 2b+6b prescale for scaling input accum
               const tensor_t<int16_t,1,xbuffer_t>&      prescale1,   // per channel 2b+6b prescale for scaling input feature-map
               const tensor_t<int8_t,1,xbuffer_t>&       preshift0,   // per channel 2b+6b preshift for scaling input accum
               const tensor_t<int8_t,1,xbuffer_t>&       preshift1,   // per channel 2b+6b preshift for scaling input feature-map
               const tensor_t<int32_t,1,xbuffer_t>&      bias0,       // per channel bias [Cout]
               const tensor_t<int32_t,1,xbuffer_t>&      bias1,       // per channel bias [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      negscale,    // per channel negative scaling factor [Cout]
               const tensor_t<int8_t,1,xbuffer_t>&       posshift,    // per channel positive shift right amount [Cout]
               const tensor_t<int8_t,1,xbuffer_t>&       negshift,    // per channel negative shift right amount [Cout]
               const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
               // outputs, buffers preallocated by caller
               gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
               );
void param_enc(const tensor_t<int16_t,1,xbuffer_t>&      prescale0,   // per channel 2b+6b prescale for scaling input accum
               const tensor_t<int16_t,1,xbuffer_t>&      prescale1,   // per channel 2b+6b prescale for scaling input feature-map
               const tensor_t<int8_t,1,xbuffer_t>&       preshift0,   // per channel 2b+6b preshift for scaling input accum
               const tensor_t<int8_t,1,xbuffer_t>&       preshift1,   // per channel 2b+6b preshift for scaling input feature-map
               const tensor_t<int32_t,1,xbuffer_t>&      bias0,       // per channel bias [Cout]
               const tensor_t<int32_t,1,xbuffer_t>&      bias1,       // per channel bias [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      posscale,    // per channel positive scaling factor [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      negscale,    // per channel negative scaling factor [Cout]
               const tensor_t<int8_t,1,xbuffer_t>&       posshift,    // per channel positive shift right amount [Cout]
               const tensor_t<int8_t,1,xbuffer_t>&       negshift,    // per channel negative shift right amount [Cout]
               const tensor_t<int8_t,1,xbuffer_t>&       asymm,       // per channel output quantization offset [Cout]
               const tensor_t<int16_t,1,xbuffer_t>&      scale,       // per channel scaling factor [Cout]
               const tensor_t<uint8_t,1,xbuffer_t>&      shift,       // per channel shift right amount [Cout]
               // outputs, buffers preallocated by caller
               gtoa_params_impl_pchan<xbuffer_t>&        obuf         // output encoded parameters
               );
#endif
