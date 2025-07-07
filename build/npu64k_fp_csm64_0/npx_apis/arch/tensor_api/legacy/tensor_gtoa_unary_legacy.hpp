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
 * tensor_gtoa_unary_legacy.hpp
 *
 * File defining a tensor level unary API base on the generic tensor operation API
 *
 */
#ifndef TENSOR_GTOA_UNARY_LEGACY_INCLUDED
#define TENSOR_GTOA_UNARY_LEGACY_INCLUDED

//
// Constructor
//
// AM(32b) to VM(8b/16b)
gtoa_unary_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                  bool                       fmdbli,        // 16b output feature-map
                  act_una_op_t               opi,           // unary operation to perform
                  bool                       sati           // do saturation
                  );
// AM(32b) to AM(32b)
gtoa_unary_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                  act_una_op_t               opi            // unary operation to perform
                  );
// VM(8b/16b) to VM(8b/16b)
gtoa_unary_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                  bool                       fmidbli,       // 16b input/output feature-map
                  bool                       fmodbli,       // 16b input/output feature-map
                  act_una_op_t               opi,           // unary operation to perform
                  bool                       sati           // do saturation
                  );
// VM(8b/16b) to AM(32b)
gtoa_unary_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                  bool                       fmdbli,        // 16b input/output feature-map
                  act_una_op_t               opi            // unary operation to perform
                  );
// AM(32b) to VM(8b/16b)
gtoa_unary_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                  bool                       fmdbli,        // 16b output feature-map
                  act_bin_op_t               opi,           // unary operation to perform
                  bool                       sati           // do saturation
                  );
// AM(32b) to AM(32b)
gtoa_unary_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                  act_bin_op_t               opi            // unary operation to perform
                  );
// VM(8b/16b) to VM(8b/16b)
gtoa_unary_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                  bool                       fmidbli,       // 16b input/output feature-map
                  bool                       fmodbli,       // 16b input/output feature-map
                  act_bin_op_t               opi,           // unary operation to perform
                  bool                       sati           // do saturation
                  );
// VM(8b/16b) to AM(32b)
gtoa_unary_params(
                  aoffset_t                  noi,           // number output channels (not vectors)
                  const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
                  bool                       fmdbli,        // 16b input/output feature-map
                  act_bin_op_t               opi            // unary operation to perform
                  );
#endif
