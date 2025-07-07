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


#include "npu_act_lut_coefs.hpp"    // [NOLINT] [build/include_subdir]

// lookup-table coefficients
// [0..7] are negative ranges
// [8..15] are positive ranges


// EXP interpolation lookup-table coefficients
fp_ue4m4_t exp_table_lim[ACT_LUT_SIZE] = {fp_ue4m4_t((uint8_t)0x5b),fp_ue4m4_t((uint8_t)0x6d),fp_ue4m4_t((uint8_t)0x78),fp_ue4m4_t((uint8_t)0x81),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x91),fp_ue4m4_t((uint8_t)0x9a),fp_ue4m4_t((uint8_t)0xa4)
,fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00)};
fp_e8m15_t exp_table_coef0[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3f7feb00),fp_e8m15_t((uint32_t)0x3f792800),fp_e8m15_t((uint32_t)0x3f628000),fp_e8m15_t((uint32_t)0x3f3bce00),fp_e8m15_t((uint32_t)0x3f09a600),fp_e8m15_t((uint32_t)0x3e9ee200),fp_e8m15_t((uint32_t)0x3de0b500),fp_e8m15_t((uint32_t)0x3c7c1e00)
,fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000)};
fp_e8m15_t exp_table_coef1[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3f7c6700),fp_e8m15_t((uint32_t)0x3f5cca00),fp_e8m15_t((uint32_t)0x3f2b0b00),fp_e8m15_t((uint32_t)0x3eeda400),fp_e8m15_t((uint32_t)0x3e8fa200),fp_e8m15_t((uint32_t)0x3e03a500),fp_e8m15_t((uint32_t)0x3d0a2a00),fp_e8m15_t((uint32_t)0x3b584200)
,fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t exp_table_coef2[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3ed04700),fp_e8m15_t((uint32_t)0x3e849500),fp_e8m15_t((uint32_t)0x3e1b2500),fp_e8m15_t((uint32_t)0x3da8de00),fp_e8m15_t((uint32_t)0x3d211800),fp_e8m15_t((uint32_t)0x3c635200),fp_e8m15_t((uint32_t)0x3b2cb500),fp_e8m15_t((uint32_t)0x3939e700)
,fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t exp_table_lin_offs[2]  = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x3f800000)};
fp_e8m15_t exp_table_lin_deriv[2] = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x00000000)};

// TANH interpolation lookup-table coefficients
fp_ue4m4_t tanh_table_lim[ACT_LUT_SIZE] = {fp_ue4m4_t((uint8_t)0x52),fp_ue4m4_t((uint8_t)0x66),fp_ue4m4_t((uint8_t)0x72),fp_ue4m4_t((uint8_t)0x78),fp_ue4m4_t((uint8_t)0x7f),fp_ue4m4_t((uint8_t)0x84),fp_ue4m4_t((uint8_t)0x8c),fp_ue4m4_t((uint8_t)0x99)
,fp_ue4m4_t((uint8_t)0x52),fp_ue4m4_t((uint8_t)0x66),fp_ue4m4_t((uint8_t)0x72),fp_ue4m4_t((uint8_t)0x78),fp_ue4m4_t((uint8_t)0x7f),fp_ue4m4_t((uint8_t)0x84),fp_ue4m4_t((uint8_t)0x8c),fp_ue4m4_t((uint8_t)0x99)};
fp_e8m15_t tanh_table_coef0[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x395e6400),fp_e8m15_t((uint32_t)0x3c8e3200),fp_e8m15_t((uint32_t)0x3b5bbb00),fp_e8m15_t((uint32_t)0xbe1daa00),fp_e8m15_t((uint32_t)0xbec67800),fp_e8m15_t((uint32_t)0xbf245000),fp_e8m15_t((uint32_t)0xbf5d3800),fp_e8m15_t((uint32_t)0xbf7c7000)
,fp_e8m15_t((uint32_t)0xb95e6400),fp_e8m15_t((uint32_t)0xbc8e3200),fp_e8m15_t((uint32_t)0xbb5bba00),fp_e8m15_t((uint32_t)0x3e1daa00),fp_e8m15_t((uint32_t)0x3ec67800),fp_e8m15_t((uint32_t)0x3f245000),fp_e8m15_t((uint32_t)0x3f5d3800),fp_e8m15_t((uint32_t)0x3f7c7000)};
fp_e8m15_t tanh_table_coef1[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3f81c600),fp_e8m15_t((uint32_t)0x3f912300),fp_e8m15_t((uint32_t)0x3f8df800),fp_e8m15_t((uint32_t)0x3f542300),fp_e8m15_t((uint32_t)0x3f045c00),fp_e8m15_t((uint32_t)0x3e81fa00),fp_e8m15_t((uint32_t)0x3d9c0400),fp_e8m15_t((uint32_t)0x3ba96400)
,fp_e8m15_t((uint32_t)0x3f81c600),fp_e8m15_t((uint32_t)0x3f912300),fp_e8m15_t((uint32_t)0x3f8df800),fp_e8m15_t((uint32_t)0x3f542300),fp_e8m15_t((uint32_t)0x3f045c00),fp_e8m15_t((uint32_t)0x3e81fa00),fp_e8m15_t((uint32_t)0x3d9c0400),fp_e8m15_t((uint32_t)0x3ba96400)};
fp_e8m15_t tanh_table_coef2[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3e0a0c00),fp_e8m15_t((uint32_t)0x3eb35e00),fp_e8m15_t((uint32_t)0x3eb01f00),fp_e8m15_t((uint32_t)0x3e5fe800),fp_e8m15_t((uint32_t)0x3deab800),fp_e8m15_t((uint32_t)0x3d3e1800),fp_e8m15_t((uint32_t)0x3c31a300),fp_e8m15_t((uint32_t)0x39f95700)
,fp_e8m15_t((uint32_t)0xbe0a0c00),fp_e8m15_t((uint32_t)0xbeb35e00),fp_e8m15_t((uint32_t)0xbeb01f00),fp_e8m15_t((uint32_t)0xbe5fe800),fp_e8m15_t((uint32_t)0xbdeab800),fp_e8m15_t((uint32_t)0xbd3e1800),fp_e8m15_t((uint32_t)0xbc31a300),fp_e8m15_t((uint32_t)0xb9f95700)};
fp_e8m15_t tanh_table_lin_offs[2]  = {fp_e8m15_t((uint32_t)0xbf800000),fp_e8m15_t((uint32_t)0x3f800000)};
fp_e8m15_t tanh_table_lin_deriv[2] = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x00000000)};

// SIGMOID interpolation lookup-table coefficients
fp_ue4m4_t sigmoid_table_lim[ACT_LUT_SIZE] = {fp_ue4m4_t((uint8_t)0x62),fp_ue4m4_t((uint8_t)0x76),fp_ue4m4_t((uint8_t)0x82),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x8f),fp_ue4m4_t((uint8_t)0x94),fp_ue4m4_t((uint8_t)0x9c),fp_ue4m4_t((uint8_t)0xa8)
,fp_ue4m4_t((uint8_t)0x62),fp_ue4m4_t((uint8_t)0x76),fp_ue4m4_t((uint8_t)0x82),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x8f),fp_ue4m4_t((uint8_t)0x94),fp_ue4m4_t((uint8_t)0x9c),fp_ue4m4_t((uint8_t)0xa8)};
fp_e8m15_t sigmoid_table_coef0[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3f000600),fp_e8m15_t((uint32_t)0x3f023800),fp_e8m15_t((uint32_t)0x3f006d00),fp_e8m15_t((uint32_t)0x3ed89500),fp_e8m15_t((uint32_t)0x3e9cc300),fp_e8m15_t((uint32_t)0x3e375e00),fp_e8m15_t((uint32_t)0x3d8b1e00),fp_e8m15_t((uint32_t)0x3bf90c00)
,fp_e8m15_t((uint32_t)0x3efff200),fp_e8m15_t((uint32_t)0x3efb8e00),fp_e8m15_t((uint32_t)0x3eff2400),fp_e8m15_t((uint32_t)0x3f13b500),fp_e8m15_t((uint32_t)0x3f319e00),fp_e8m15_t((uint32_t)0x3f522800),fp_e8m15_t((uint32_t)0x3f6e9c00),fp_e8m15_t((uint32_t)0x3f7e0d00)};
fp_e8m15_t sigmoid_table_coef1[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3e81c600),fp_e8m15_t((uint32_t)0x3e912300),fp_e8m15_t((uint32_t)0x3e8df800),fp_e8m15_t((uint32_t)0x3e542300),fp_e8m15_t((uint32_t)0x3e045c00),fp_e8m15_t((uint32_t)0x3d81fa00),fp_e8m15_t((uint32_t)0x3c9c0400),fp_e8m15_t((uint32_t)0x3abd2000)
,fp_e8m15_t((uint32_t)0x3e81c600),fp_e8m15_t((uint32_t)0x3e912300),fp_e8m15_t((uint32_t)0x3e8df800),fp_e8m15_t((uint32_t)0x3e542300),fp_e8m15_t((uint32_t)0x3e045c00),fp_e8m15_t((uint32_t)0x3d81fa00),fp_e8m15_t((uint32_t)0x3c9c0400),fp_e8m15_t((uint32_t)0x3abd2000)};
fp_e8m15_t sigmoid_table_coef2[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3c8a0c00),fp_e8m15_t((uint32_t)0x3d335e00),fp_e8m15_t((uint32_t)0x3d301f00),fp_e8m15_t((uint32_t)0x3cdfe800),fp_e8m15_t((uint32_t)0x3c6ab800),fp_e8m15_t((uint32_t)0x3bbe1800),fp_e8m15_t((uint32_t)0x3ab1a300),fp_e8m15_t((uint32_t)0x388eb100)
,fp_e8m15_t((uint32_t)0xbc8a0c00),fp_e8m15_t((uint32_t)0xbd335e00),fp_e8m15_t((uint32_t)0xbd301f00),fp_e8m15_t((uint32_t)0xbcdfe800),fp_e8m15_t((uint32_t)0xbc6ab800),fp_e8m15_t((uint32_t)0xbbbe1800),fp_e8m15_t((uint32_t)0xbab1a300),fp_e8m15_t((uint32_t)0xb88eb100)};
fp_e8m15_t sigmoid_table_lin_offs[2]  = {fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x3f800000)};
fp_e8m15_t sigmoid_table_lin_deriv[2] = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x00000000)};

// SWISH interpolation lookup-table coefficients
fp_ue4m4_t swish_table_lim[ACT_LUT_SIZE] = {fp_ue4m4_t((uint8_t)0x66),fp_ue4m4_t((uint8_t)0x74),fp_ue4m4_t((uint8_t)0x7d),fp_ue4m4_t((uint8_t)0x84),fp_ue4m4_t((uint8_t)0x93),fp_ue4m4_t((uint8_t)0x9a),fp_ue4m4_t((uint8_t)0xa3),fp_ue4m4_t((uint8_t)0xa8)
,fp_ue4m4_t((uint8_t)0x66),fp_ue4m4_t((uint8_t)0x74),fp_ue4m4_t((uint8_t)0x7d),fp_ue4m4_t((uint8_t)0x84),fp_ue4m4_t((uint8_t)0x92),fp_ue4m4_t((uint8_t)0x98),fp_ue4m4_t((uint8_t)0xa1),fp_ue4m4_t((uint8_t)0xa8)};
fp_e8m15_t swish_table_coef0[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0xb98e8700),fp_e8m15_t((uint32_t)0xbd1b9e00),fp_e8m15_t((uint32_t)0xbe277900),fp_e8m15_t((uint32_t)0xbeb84e00),fp_e8m15_t((uint32_t)0xbf0dd700),fp_e8m15_t((uint32_t)0xbea7b300),fp_e8m15_t((uint32_t)0xbdccdc00),fp_e8m15_t((uint32_t)0xbc775e00)
,fp_e8m15_t((uint32_t)0xb98e8700),fp_e8m15_t((uint32_t)0xbd1b9e00),fp_e8m15_t((uint32_t)0xbe277900),fp_e8m15_t((uint32_t)0xbeb84e00),fp_e8m15_t((uint32_t)0xbf0dd700),fp_e8m15_t((uint32_t)0xbec27e00),fp_e8m15_t((uint32_t)0xbe18b300),fp_e8m15_t((uint32_t)0xbcc57400)};
fp_e8m15_t swish_table_coef1[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3efcf700),fp_e8m15_t((uint32_t)0x3ec61400),fp_e8m15_t((uint32_t)0x3e3e0200),fp_e8m15_t((uint32_t)0xbd015800),fp_e8m15_t((uint32_t)0xbe400900),fp_e8m15_t((uint32_t)0xbdbc2400),fp_e8m15_t((uint32_t)0xbcb03c00),fp_e8m15_t((uint32_t)0xbb256400)
,fp_e8m15_t((uint32_t)0x3f018400),fp_e8m15_t((uint32_t)0x3f1cf500),fp_e8m15_t((uint32_t)0x3f507f00),fp_e8m15_t((uint32_t)0x3f840a00),fp_e8m15_t((uint32_t)0x3f980100),fp_e8m15_t((uint32_t)0x3f8e4400),fp_e8m15_t((uint32_t)0x3f847100),fp_e8m15_t((uint32_t)0x3f808900)};
fp_e8m15_t swish_table_coef2[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3e6eba00),fp_e8m15_t((uint32_t)0x3e1f9300),fp_e8m15_t((uint32_t)0x3d993300),fp_e8m15_t((uint32_t)0x3c702400),fp_e8m15_t((uint32_t)0xbc893100),fp_e8m15_t((uint32_t)0xbbd8db00),fp_e8m15_t((uint32_t)0xba98f400),fp_e8m15_t((uint32_t)0xb8de7400)
,fp_e8m15_t((uint32_t)0x3e6eba00),fp_e8m15_t((uint32_t)0x3e1f9300),fp_e8m15_t((uint32_t)0x3d993300),fp_e8m15_t((uint32_t)0x3c702400),fp_e8m15_t((uint32_t)0xbc893100),fp_e8m15_t((uint32_t)0xbc0a5400),fp_e8m15_t((uint32_t)0xbb061100),fp_e8m15_t((uint32_t)0xb940c200)};
fp_e8m15_t swish_table_lin_offs[2]  = {fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t swish_table_lin_deriv[2] = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x3f800000)};

// HSWISH interpolation lookup-table coefficients
fp_ue4m4_t hswish_table_lim[ACT_LUT_SIZE] = {fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88)
,fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x88)};
fp_e8m15_t hswish_table_coef0[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000)
,fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t hswish_table_coef1[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000)
,fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000),fp_e8m15_t((uint32_t)0x3f000000)};
fp_e8m15_t hswish_table_coef2[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00)
,fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00),fp_e8m15_t((uint32_t)0x3e2aaa00)};
fp_e8m15_t hswish_table_lin_offs[2]  = {fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t hswish_table_lin_deriv[2] = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x3f800000)};

// MISH interpolation lookup-table coefficients
fp_ue4m4_t mish_table_lim[ACT_LUT_SIZE] = {fp_ue4m4_t((uint8_t)0x64),fp_ue4m4_t((uint8_t)0x72),fp_ue4m4_t((uint8_t)0x7b),fp_ue4m4_t((uint8_t)0x83),fp_ue4m4_t((uint8_t)0x92),fp_ue4m4_t((uint8_t)0x99),fp_ue4m4_t((uint8_t)0xa4),fp_ue4m4_t((uint8_t)0xa4)
,fp_ue4m4_t((uint8_t)0x61),fp_ue4m4_t((uint8_t)0x70),fp_ue4m4_t((uint8_t)0x79),fp_ue4m4_t((uint8_t)0x88),fp_ue4m4_t((uint8_t)0x92),fp_ue4m4_t((uint8_t)0xa0),fp_ue4m4_t((uint8_t)0xa0),fp_ue4m4_t((uint8_t)0xa0)};
fp_e8m15_t mish_table_coef0[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0xb9906d00),fp_e8m15_t((uint32_t)0xbd29cc00),fp_e8m15_t((uint32_t)0xbe386400),fp_e8m15_t((uint32_t)0xbecbfd00),fp_e8m15_t((uint32_t)0xbf183500),fp_e8m15_t((uint32_t)0xbebc8500),fp_e8m15_t((uint32_t)0xbdce4d00),fp_e8m15_t((uint32_t)0xbdce4d00)
,fp_e8m15_t((uint32_t)0xb996c700),fp_e8m15_t((uint32_t)0xbd195400),fp_e8m15_t((uint32_t)0xbe267500),fp_e8m15_t((uint32_t)0xbe974100),fp_e8m15_t((uint32_t)0xbdf1c200),fp_e8m15_t((uint32_t)0xbc0fcd00),fp_e8m15_t((uint32_t)0xbc0fcd00),fp_e8m15_t((uint32_t)0xbc0fcd00)};
fp_e8m15_t mish_table_coef1[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3f180f00),fp_e8m15_t((uint32_t)0x3eee3700),fp_e8m15_t((uint32_t)0x3e616d00),fp_e8m15_t((uint32_t)0xbd23c000),fp_e8m15_t((uint32_t)0xbe53cb00),fp_e8m15_t((uint32_t)0xbdda5200),fp_e8m15_t((uint32_t)0xbcaf6b00),fp_e8m15_t((uint32_t)0xbcaf6b00)
,fp_e8m15_t((uint32_t)0x3f1bca00),fp_e8m15_t((uint32_t)0x3f3eaf00),fp_e8m15_t((uint32_t)0x3f7e8500),fp_e8m15_t((uint32_t)0x3f95e300),fp_e8m15_t((uint32_t)0x3f86c900),fp_e8m15_t((uint32_t)0x3f805400),fp_e8m15_t((uint32_t)0x3f805400),fp_e8m15_t((uint32_t)0x3f805400)};
fp_e8m15_t mish_table_coef2[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3e9c2b00),fp_e8m15_t((uint32_t)0x3e4fe600),fp_e8m15_t((uint32_t)0x3dc0e000),fp_e8m15_t((uint32_t)0x3c872800),fp_e8m15_t((uint32_t)0xbc9c3b00),fp_e8m15_t((uint32_t)0xbc023200),fp_e8m15_t((uint32_t)0xba95df00),fp_e8m15_t((uint32_t)0xba95df00)
,fp_e8m15_t((uint32_t)0x3e91f300),fp_e8m15_t((uint32_t)0x3e21c500),fp_e8m15_t((uint32_t)0x3d079100),fp_e8m15_t((uint32_t)0xbcd29400),fp_e8m15_t((uint32_t)0xbbc56d00),fp_e8m15_t((uint32_t)0xb943fc00),fp_e8m15_t((uint32_t)0xb943fc00),fp_e8m15_t((uint32_t)0xb943fc00)};
fp_e8m15_t mish_table_lin_offs[2]  = {fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t mish_table_lin_deriv[2] = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x3f800000)};

// GELU interpolation lookup-table coefficients
fp_ue4m4_t gelu_table_lim[ACT_LUT_SIZE] = {fp_ue4m4_t((uint8_t)0x5e),fp_ue4m4_t((uint8_t)0x6a),fp_ue4m4_t((uint8_t)0x73),fp_ue4m4_t((uint8_t)0x7a),fp_ue4m4_t((uint8_t)0x84),fp_ue4m4_t((uint8_t)0x8a),fp_ue4m4_t((uint8_t)0x94),fp_ue4m4_t((uint8_t)0x9c)
,fp_ue4m4_t((uint8_t)0x5e),fp_ue4m4_t((uint8_t)0x6a),fp_ue4m4_t((uint8_t)0x73),fp_ue4m4_t((uint8_t)0x7a),fp_ue4m4_t((uint8_t)0x84),fp_ue4m4_t((uint8_t)0x8a),fp_ue4m4_t((uint8_t)0x94),fp_ue4m4_t((uint8_t)0x9c)};
fp_e8m15_t gelu_table_coef0[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0xb9496e00),fp_e8m15_t((uint32_t)0xbcd3e700),fp_e8m15_t((uint32_t)0xbdef7d00),fp_e8m15_t((uint32_t)0xbe909400),fp_e8m15_t((uint32_t)0xbed5b000),fp_e8m15_t((uint32_t)0xbe694c00),fp_e8m15_t((uint32_t)0xbcccf600),fp_e8m15_t((uint32_t)0xb8157c00)
,fp_e8m15_t((uint32_t)0xb9496e00),fp_e8m15_t((uint32_t)0xbcd3e700),fp_e8m15_t((uint32_t)0xbdef7d00),fp_e8m15_t((uint32_t)0xbe909400),fp_e8m15_t((uint32_t)0xbed5b000),fp_e8m15_t((uint32_t)0xbe694c00),fp_e8m15_t((uint32_t)0xbcccf600),fp_e8m15_t((uint32_t)0xb8157c00)};
fp_e8m15_t gelu_table_coef1[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3efcde00),fp_e8m15_t((uint32_t)0x3ec56400),fp_e8m15_t((uint32_t)0x3e278200),fp_e8m15_t((uint32_t)0xbdecab00),fp_e8m15_t((uint32_t)0xbe92c100),fp_e8m15_t((uint32_t)0xbe0c0000),fp_e8m15_t((uint32_t)0xbc391300),fp_e8m15_t((uint32_t)0xb740ce00)
,fp_e8m15_t((uint32_t)0x3f019000),fp_e8m15_t((uint32_t)0x3f1d4d00),fp_e8m15_t((uint32_t)0x3f561f00),fp_e8m15_t((uint32_t)0x3f8eca00),fp_e8m15_t((uint32_t)0x3fa4b000),fp_e8m15_t((uint32_t)0x3f918000),fp_e8m15_t((uint32_t)0x3f817200),fp_e8m15_t((uint32_t)0x3f800000)};
fp_e8m15_t gelu_table_coef2[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3ebf3b00),fp_e8m15_t((uint32_t)0x3e83e500),fp_e8m15_t((uint32_t)0x3df99200),fp_e8m15_t((uint32_t)0x3b7bd100),fp_e8m15_t((uint32_t)0xbd4e5500),fp_e8m15_t((uint32_t)0xbca98200),fp_e8m15_t((uint32_t)0xbaa5f700),fp_e8m15_t((uint32_t)0xb576e000)
,fp_e8m15_t((uint32_t)0x3ebf3b00),fp_e8m15_t((uint32_t)0x3e83e500),fp_e8m15_t((uint32_t)0x3df99200),fp_e8m15_t((uint32_t)0x3b7bd000),fp_e8m15_t((uint32_t)0xbd4e5500),fp_e8m15_t((uint32_t)0xbca98200),fp_e8m15_t((uint32_t)0xbaa5f700),fp_e8m15_t((uint32_t)0xb576e000)};
fp_e8m15_t gelu_table_lin_offs[2]  = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t gelu_table_lin_deriv[2] = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x3f800000)};

// ELU interpolation lookup-table coefficients
fp_ue4m4_t elu_table_lim[ACT_LUT_SIZE] = {fp_ue4m4_t((uint8_t)0x59),fp_ue4m4_t((uint8_t)0x6b),fp_ue4m4_t((uint8_t)0x76),fp_ue4m4_t((uint8_t)0x80),fp_ue4m4_t((uint8_t)0x86),fp_ue4m4_t((uint8_t)0x8f),fp_ue4m4_t((uint8_t)0x96),fp_ue4m4_t((uint8_t)0xa4)
,fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00),fp_ue4m4_t((uint8_t)0x00)};
fp_e8m15_t elu_table_coef0[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0xb9864800),fp_e8m15_t((uint32_t)0xbcb59f00),fp_e8m15_t((uint32_t)0xbdc62c00),fp_e8m15_t((uint32_t)0xbe6e9300),fp_e8m15_t((uint32_t)0xbed4fd00),fp_e8m15_t((uint32_t)0xbf21b100),fp_e8m15_t((uint32_t)0xbf55f000),fp_e8m15_t((uint32_t)0xbf78fd00)
,fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t elu_table_coef1[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3f7ce000),fp_e8m15_t((uint32_t)0x3f60ae00),fp_e8m15_t((uint32_t)0x3f338200),fp_e8m15_t((uint32_t)0x3f00a900),fp_e8m15_t((uint32_t)0x3ea33c00),fp_e8m15_t((uint32_t)0x3e267700),fp_e8m15_t((uint32_t)0x3d663400),fp_e8m15_t((uint32_t)0x3bcc0700)
,fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000),fp_e8m15_t((uint32_t)0x3f800000)};
fp_e8m15_t elu_table_coef2[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3ed36a00),fp_e8m15_t((uint32_t)0x3e8ad700),fp_e8m15_t((uint32_t)0x3e2a1500),fp_e8m15_t((uint32_t)0x3dbf5a00),fp_e8m15_t((uint32_t)0x3d414c00),fp_e8m15_t((uint32_t)0x3c9a2c00),fp_e8m15_t((uint32_t)0x3ba18600),fp_e8m15_t((uint32_t)0x39b8b700)
,fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t elu_table_lin_offs[2]  = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t elu_table_lin_deriv[2] = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x3f800000)};

// Softplus interpolation lookup-table coefficients
fp_ue4m4_t softplus_table_lim[ACT_LUT_SIZE] = {fp_ue4m4_t((uint8_t)0x6a),fp_ue4m4_t((uint8_t)0x77),fp_ue4m4_t((uint8_t)0x80),fp_ue4m4_t((uint8_t)0x86),fp_ue4m4_t((uint8_t)0x8d),fp_ue4m4_t((uint8_t)0x93),fp_ue4m4_t((uint8_t)0x9b),fp_ue4m4_t((uint8_t)0xa2)
,fp_ue4m4_t((uint8_t)0x6a),fp_ue4m4_t((uint8_t)0x77),fp_ue4m4_t((uint8_t)0x80),fp_ue4m4_t((uint8_t)0x86),fp_ue4m4_t((uint8_t)0x8d),fp_ue4m4_t((uint8_t)0x93),fp_ue4m4_t((uint8_t)0x9b),fp_ue4m4_t((uint8_t)0xa2)};
fp_e8m15_t softplus_table_coef0[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3f316900),fp_e8m15_t((uint32_t)0x3f2cd400),fp_e8m15_t((uint32_t)0x3f1e5600),fp_e8m15_t((uint32_t)0x3f03d800),fp_e8m15_t((uint32_t)0x3ebb4e00),fp_e8m15_t((uint32_t)0x3e5a4800),fp_e8m15_t((uint32_t)0x3da70000),fp_e8m15_t((uint32_t)0x3c8d6d00)
,fp_e8m15_t((uint32_t)0x3f316900),fp_e8m15_t((uint32_t)0x3f2cd400),fp_e8m15_t((uint32_t)0x3f1e5600),fp_e8m15_t((uint32_t)0x3f03d800),fp_e8m15_t((uint32_t)0x3ebb4e00),fp_e8m15_t((uint32_t)0x3e5a4800),fp_e8m15_t((uint32_t)0x3da70000),fp_e8m15_t((uint32_t)0x3c8d6d00)};
fp_e8m15_t softplus_table_coef1[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3efebd00),fp_e8m15_t((uint32_t)0x3ee88400),fp_e8m15_t((uint32_t)0x3ebff300),fp_e8m15_t((uint32_t)0x3e8b8f00),fp_e8m15_t((uint32_t)0x3e279d00),fp_e8m15_t((uint32_t)0x3da1fa00),fp_e8m15_t((uint32_t)0x3cc20e00),fp_e8m15_t((uint32_t)0x3b7c1500)
,fp_e8m15_t((uint32_t)0x3f00a100),fp_e8m15_t((uint32_t)0x3f0bbd00),fp_e8m15_t((uint32_t)0x3f200600),fp_e8m15_t((uint32_t)0x3f3a3800),fp_e8m15_t((uint32_t)0x3f561800),fp_e8m15_t((uint32_t)0x3f6bc000),fp_e8m15_t((uint32_t)0x3f79ef00),fp_e8m15_t((uint32_t)0x3f7f0300)};
fp_e8m15_t softplus_table_coef2[ACT_LUT_SIZE] = {fp_e8m15_t((uint32_t)0x3df3e300),fp_e8m15_t((uint32_t)0x3dbd3e00),fp_e8m15_t((uint32_t)0x3d844100),fp_e8m15_t((uint32_t)0x3d20b000),fp_e8m15_t((uint32_t)0x3c9e5300),fp_e8m15_t((uint32_t)0x3bf8b200),fp_e8m15_t((uint32_t)0x3ae52d00),fp_e8m15_t((uint32_t)0x39629400)
,fp_e8m15_t((uint32_t)0x3df3e300),fp_e8m15_t((uint32_t)0x3dbd3e00),fp_e8m15_t((uint32_t)0x3d844100),fp_e8m15_t((uint32_t)0x3d20b000),fp_e8m15_t((uint32_t)0x3c9e5300),fp_e8m15_t((uint32_t)0x3bf8b200),fp_e8m15_t((uint32_t)0x3ae52d00),fp_e8m15_t((uint32_t)0x39629400)};
fp_e8m15_t softplus_table_lin_offs[2]  = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x00000000)};
fp_e8m15_t softplus_table_lin_deriv[2] = {fp_e8m15_t((uint32_t)0x80000000),fp_e8m15_t((uint32_t)0x3f800000)};
