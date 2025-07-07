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
 * tensor_gtoa_sumpool_legacy.hpp
 *
 * File defining a tensor level pooling operations on the generic tensor operation API
 *
 */

#ifndef TENSOR_GTOA_SUMPOOL_LEGACY_INCLUDED
#define TENSOR_GTOA_SUMPOOL_LEGACY_INCLUDED


//
// Constructor
//
// VM(8b/16b) to AM(32b)
gtoa_sumpool_params(
                    aoffset_t                noi,         // number output channels (not vectors)
                    const shape<2>&          oshpi,       // output shape, indexed by spatial_axis_t
                    const shape<2>&          kshpi,       // kernel shape
                    const shape<2>&          kstri,       // kernel stride
                    const shape<2>&          padlimi,     // input padding boundaries
                    bool                     fmdbli       // 16b input feature-map
                    );
#endif
