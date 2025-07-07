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
 * tensor_gtoa_reduce_legacy.hpp
 *
 * File defining a tensor level reduce API base on the generic tensor operation API
 *
 */
#ifndef TENSOR_API_LEGACY_TENSOR_GTOA_REDUCE_LEGACY_HPP_
#define TENSOR_API_LEGACY_TENSOR_GTOA_REDUCE_LEGACY_HPP_
//
// Constructor
//
// AM(32b) to VM(8b/16b)
gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3> &ishpi,    // input shape, output inner is 1
    bool fmdbli,              // 16b output feature-map
    bool sati,                // do saturation
    act_red_op_t opi,         // reduction operation to perform
    const int dimi = 1);      // spatial dimensions to reduce
// AM(32b) to AM(32b)
gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3> &ishpi,    // input shape, output inner is 1
    act_red_op_t opi,         // reduction operation to perform
    const int dimi = 1);      // spatial dimensions to reduce
// VM(8b/16b) to VM(8b/16b)
gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3> &ishpi,    // input shape, output inner is 1
    bool fmidbli,             // 8b/16b input feature-map
    bool fmodbli,             // 8b/16b output feature-map
    bool sati,                // do saturation
    act_red_op_t opi,         // reduction operation to perform
    const int dimi = 1);      // spatial dimensions to reduce
// AM(32b) to VM(8b/16b)
gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3> &ishpi,    // input shape, output inner is 1
    bool fmdbli,              // 8b/16b input feature-map
    act_red_op_t opi,         // reduction operation to perform
    const int dimi = 1);      // spatial dimensions to reduce
// VM(8b/16b) input with useAcc/keepAcc
gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3> &ishpi,    // input shape, output inner is 1
    const shape<2> &padlimi,  // padding shape
    bool fmidbli,             // 8b/16b input feature-map
    bool fmodbli,             // 8b/16b output feature-map
    bool sati,                // do saturation
    act_red_op_t opi,         // reduction operation to perform
    bool useAcc,              // use accumulator input
    bool keepAcc,             // keep result in accumulator
    const int dimi = 1);      // spatial dimensions to reduce
// AM(32b) input with useAcc/keepAcc
gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3> &ishpi,    // input shape, output inner is 1
    const shape<2> &padlimi,  // padding shape
    bool fmodbli,             // 8b/16b output feature-map
    bool sati,                // do saturation
    act_red_op_t opi,         // reduction operation to perform
    bool useAcc,              // use accumulator input
    bool keepAcc,             // keep result in accumulator
    const int dimi = 1);      // spatial dimensions to reduce
// VM(8b/16b) input with useAcc/keepAcc, secondary input from feature-map
gtoa_reduce_params(
    aoffset_t noi,            // number output channels (not vectors)
    const shape<3> &ishpi,    // input shape, output inner is 1
    const shape<2> &padlimi,  // padding shape
    bool fmidbli,             // 8b/16b input feature-map
    bool fmodbli,             // 8b/16b output feature-map
    bool sati,                // do saturation
    act_red_op_t opi,         // reduction operation to perform
    bool fmi1dbli,            // 8b/16b secondary input feature-map
    bool useAcc,              // use accumulator input
    bool keepAcc,             // keep result in accumulator
    const int dimi);      // spatial dimensions to reduce
#endif    // TENSOR_API_LEGACY_TENSOR_GTOA_REDUCE_LEGACY_HPP_
