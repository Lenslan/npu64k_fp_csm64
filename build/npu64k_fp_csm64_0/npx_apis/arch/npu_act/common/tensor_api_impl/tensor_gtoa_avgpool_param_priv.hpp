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

#ifndef AVGPOOL_PARAM_PRIV_HPP_     // [NOLINT]
#define AVGPOOL_PARAM_PRIV_HPP_     // [NOLINT]

gtoa_act_params_impl_shapes shapes;  // buffer shapes
aoffset_t                   cmax;    // number of channels
bool                        ifmdbl;
shape<2>                    str;     // kernel stride

#endif  // AVGPOOL_PARAM_PRIV_HPP_  // [NOLINT]
