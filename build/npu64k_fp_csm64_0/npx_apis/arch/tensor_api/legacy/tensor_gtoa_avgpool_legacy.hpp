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
 * tensor_gtoa_avgpool_legacy.hpp
 *
 * File defining a tensor level pooling operations on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_AVGPOOL_LEGACY_INCLUDED
#define TENSOR_GTOA_AVGPOOL_LEGACY_INCLUDED


//
// Constructor
//
// VM(8b/16b) to VM(8b/16b)
gtoa_avgpool_params(
                    aoffset_t                noi,         // number output channels (not vectors)
                    const shape<2>&          oshpi,       // output shape, indexed by spatial_axis_t
                    const shape<2>&          kshpi,       // kernel shape
                    const shape<2>&          kstri,       // kernel stride
                    const shape<2>&          padlimi,     // input padding boundaries
                    bool                     fmdbli       // 16b input feature-map
                    );

//
// Legacy transcode scaling parameters per spatial [H][W] to a tensor of ixpix_t [W/8][H]
//
template<template<typename> class BD=B>
void scale_enc(
               const tensor_t<uint16_t,2,xbuffer_t>&   scale, // per channel scaling factor [H][W]; [0,1.0> quantized as 16b unsigned values
               // outputs, buffers preallocated by caller
               impl_spec_container_t<BD>&              scales // output encoded parameters as tensor
               );

//
// Legacy param enc, just encoding {16,24}
//
template<template<typename> class BD=B>
void param_enc(
               // outputs, buffers preallocated by caller
               gtoa_params_impl_pchan<BD>&       obuf         // output encoded parameters
               );

//
// Legacy assign L1 memory buffer offsets for scales, from scale_enc
//
template<template<typename> class BD=B>
void init_l1_input1(
                    const impl_spec_container_t<BD>&    scales       // structure with allocated buffers and tensors in L1 memory
                    );

#endif
