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
 * tensor_conv_conv_priv.hpp
 *
 * File defining the native specific inline functions for the tensor convolution objects
 *
 */

#ifndef NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_CONV_PRIV_HPP_
#define NPU_CONV_COMMON_TENSOR_API_IMPL_TENSOR_CONV_CONV_PRIV_HPP_
private:
using conv_base<B>::impl_spec;
using conv_base<B>::tens;
using conv_base<B>::tensb;
using conv_base<B>::shapes;
using conv_base<B>::hlapi;
using conv_base<B>::use_acc;
using conv_base<B>::keep_acc;
using conv_base<B>::fm_tp;
using conv_base<B>::cf_tp;
using conv_base<B>::pck_mpy;
// input parameters
int                            grp;            // groups
int                            ni;             // number of input channels per group
int                            no;             // number of output channels per group
shape<3>                       oshp;           // output spatial shape
shape<3>                       filter;         // filter dimension
shape<3>                       stride;         // filter stride
shape<3>                       dil;            // filter dilation
shape<3>                       padlim;         // right&bottom&back limits of padding window
pack_mode_t                    pck;            // 8b packing mode
// private functions
void set_default_params();
void quad_enc();
#endif
