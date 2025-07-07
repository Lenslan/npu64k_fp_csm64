/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021-2023 Synopsys, Inc.                                   **/
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
 * tensor_gtoa_nullary_legacy.hpp
 *
 * File defining a tensor level nullary API base on the generic tensor operation API
 * The GTOA supports generic tensor nullary operations without source operands, only having output operands.
 */

#ifndef TENSOR_GTOA_NULLARY_LEGACY_INCLUDED
#define TENSOR_GTOA_NULLARY_LEGACY_INCLUDED
//
// Constructor
//
// to VM(8b/16b)
gtoa_nullary_params(
                    aoffset_t                  noi,           // number output channels (not vectors)
                    const shape<3>&            oshpi,         // output shape
                    bool                       fmodbli,       // 16b output feature-map
                    act_nula_op_t               opi            // nulary operation to perform
                    );
// to AM(32b)
gtoa_nullary_params(
                    aoffset_t                  noi,           // number output channels (not vectors)
                    const shape<3>&            oshpi,         // output shape
                    act_nula_op_t               opi            // nulary operation to perform
                    );
#endif
