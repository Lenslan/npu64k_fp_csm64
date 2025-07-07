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
 * tensor_gtoa_binary_ms_legacy.hpp
 *
 * File defining a tensor level binary API base on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_BINARY_MS_LEGACY_INCLUDED
#define TENSOR_GTOA_BINARY_MS_LEGACY_INCLUDED
// Constructor
//
// AM(32b) + SR -> VM(8b/16b)
gtoa_binary_ms_params(
	      aoffset_t                  noi,           // number output channels (not vectors)
	      const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
	      bool                       fmodbli,       // 16b output feature-map
	      act_bin_op_t               opi,           // binary operation to perform
	      bool                       sati           // do saturation
	      );
// VM(8b/16b) + SR -> VM(8b/16b)
gtoa_binary_ms_params(
	      aoffset_t                  noi,           // number output channels (not vectors)
	      const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
	      bool                       fmidbli,       // 16b input feature-map
	      bool                       fmodbli,       // 16b output feature-map
	      act_bin_op_t               opi,           // binary operation to perform
	      bool                       sati           // do saturation
	      );
// AM(32b) + SR -> AM(32b)
gtoa_binary_ms_params(
	      aoffset_t                  noi,           // number output channels (not vectors)
	      const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
	      act_bin_op_t               opi            // binary operation to perform
	      );
// VM(8b/16b) + SR -> AM(32b)
gtoa_binary_ms_params(
	      aoffset_t                  noi,           // number output channels (not vectors)
	      const shape<3>&            oshpi,         // output shape, indexed by spatial_axis_t
	      bool                       fmidbli,       // 16b input feature-map
	      act_bin_op_t               opi            // binary operation to perform
	      );
#endif
