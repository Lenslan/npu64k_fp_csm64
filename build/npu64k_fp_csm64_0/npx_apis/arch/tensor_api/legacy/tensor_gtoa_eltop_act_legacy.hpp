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
 * tensor_gtoa_eltop_act_legacy.hpp
 *
 * File defining a tensor level base class for all activation functions
 *
 */

#ifndef TENSOR_GTOA_ELTOP_ACT_LEGACY_INCLUDED
#define TENSOR_GTOA_ELTOP_ACT_LEGACY_INCLUDED
//
// All identifiers related to the tensor API go into namespace tensor::v200
//
//
// Constructors
//
// AM32/48 to VM8/16
gtoa_eltop_act_params(
        aoffset_t                  noi,           // number output channels (not vectors)
        const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
        const shape<3>&            ostr,          // output stride
        act_bin_op_t               opi,           // eltwise binary operation to perform
        bool                       accidbli,      // double wide input accumulator
        bool                       fmidbli,       // 16b input feature-map
        bool                       fmodbli,       // 16b output feature-map
        bool                       eltact,        // if true then first eltop then activ, else first activ then elto
        bool                       inastri        // if true then stream directly from convolution
        );
// AM32/48 to AM32
gtoa_eltop_act_params(
        aoffset_t                  noi,           // number output channels (not vectors)
        const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
        act_bin_op_t               opi,           // eltwise binary operation to perform
        bool                       accidbli,      // double wide input accumulator
        bool                       fmidbli,       // 16b input feature-map
        bool                       eltact,        // if true then first eltop then activ, else first activ then elto
        bool                       inastri        // if true then stream directly from convolution
        );
#endif
