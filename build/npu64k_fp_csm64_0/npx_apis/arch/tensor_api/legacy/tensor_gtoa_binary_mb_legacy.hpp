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
 * tensor_gtoa_binary_mb_legacy.hpp
 *
 * File defining a tensor level binary API base on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_BINARY_MB_LEGACY_INCLUDED
#define TENSOR_GTOA_BINARY_MB_LEGACY_INCLUDED


// include interface datatypes
#include "tensor_gtoa_binary.hpp"
//
// Constructor
//
// AM(32b) + B -> VM(8b/16b)
gtoa_binary_mb_params(
              aoffset_t                  noi,           // number output channels (not vectors)
              const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
              bool                       fmodbli,       // 16b output feature-map
              act_bin_op_t               opi,           // binary operation to perform
              bool                       sati           // do saturation
              );
// VM(8b/16b) + B -> VM(8b/16b)
gtoa_binary_mb_params(
              aoffset_t                  noi,           // number output channels (not vectors)
              const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
              bool                       fmidbli,       // 16b input feature-map
              bool                       fmodbli,       // 16b output feature-map
              act_bin_op_t               opi,           // binary operation to perform
              bool                       sati           // do saturation
              );
// AM(32b) + B -> AM(32b)
gtoa_binary_mb_params(
              aoffset_t                  noi,           // number output channels (not vectors)
              const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
              act_bin_op_t               opi            // binary operation to perform
              );
// VM(8b/16b) + B -> AM(32b)
gtoa_binary_mb_params(
              aoffset_t                  noi,           // number output channels (not vectors)
              const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
              bool                       fmidbli,       // 16b input feature-map
              act_bin_op_t               opi            // binary operation to perform
              );
#endif
