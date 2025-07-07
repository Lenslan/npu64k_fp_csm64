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

#ifndef NPU_ACT_COMMON_NPU_ACT_LUT_COEFS_HPP_
#define NPU_ACT_COMMON_NPU_ACT_LUT_COEFS_HPP_

#include "tensor_basic_types.hpp"           // [NOLINT] [build/include_subdir]

using namespace tensor::v200;

// EXP interpolation lookup-table coefficients
extern fp_ue4m4_t exp_table_lim[ACT_LUT_SIZE];
extern fp_e8m15_t exp_table_coef0[ACT_LUT_SIZE];
extern fp_e8m15_t exp_table_coef1[ACT_LUT_SIZE];
extern fp_e8m15_t exp_table_coef2[ACT_LUT_SIZE];
extern fp_e8m15_t exp_table_lin_offs[2];
extern fp_e8m15_t exp_table_lin_deriv[2];

// TANH interpolation lookup-table coefficients
extern fp_ue4m4_t tanh_table_lim[ACT_LUT_SIZE];
extern fp_e8m15_t tanh_table_coef0[ACT_LUT_SIZE];
extern fp_e8m15_t tanh_table_coef1[ACT_LUT_SIZE];
extern fp_e8m15_t tanh_table_coef2[ACT_LUT_SIZE];
extern fp_e8m15_t tanh_table_lin_offs[2];
extern fp_e8m15_t tanh_table_lin_deriv[2];

// SIGMOID interpolation lookup-table coefficients
extern fp_ue4m4_t sigmoid_table_lim[ACT_LUT_SIZE];
extern fp_e8m15_t sigmoid_table_coef0[ACT_LUT_SIZE];
extern fp_e8m15_t sigmoid_table_coef1[ACT_LUT_SIZE];
extern fp_e8m15_t sigmoid_table_coef2[ACT_LUT_SIZE];
extern fp_e8m15_t sigmoid_table_lin_offs[2];
extern fp_e8m15_t sigmoid_table_lin_deriv[2];

// SWISH interpolation lookup-table coefficients
extern fp_ue4m4_t swish_table_lim[ACT_LUT_SIZE];
extern fp_e8m15_t swish_table_coef0[ACT_LUT_SIZE];
extern fp_e8m15_t swish_table_coef1[ACT_LUT_SIZE];
extern fp_e8m15_t swish_table_coef2[ACT_LUT_SIZE];
extern fp_e8m15_t swish_table_lin_offs[2];
extern fp_e8m15_t swish_table_lin_deriv[2];

// HSWISH interpolation lookup-table coefficients
extern fp_ue4m4_t hswish_table_lim[ACT_LUT_SIZE];
extern fp_e8m15_t hswish_table_coef0[ACT_LUT_SIZE];
extern fp_e8m15_t hswish_table_coef1[ACT_LUT_SIZE];
extern fp_e8m15_t hswish_table_coef2[ACT_LUT_SIZE];
extern fp_e8m15_t hswish_table_lin_offs[2];
extern fp_e8m15_t hswish_table_lin_deriv[2];

// MISH interpolation lookup-table coefficients
extern fp_ue4m4_t mish_table_lim[ACT_LUT_SIZE];
extern fp_e8m15_t mish_table_coef0[ACT_LUT_SIZE];
extern fp_e8m15_t mish_table_coef1[ACT_LUT_SIZE];
extern fp_e8m15_t mish_table_coef2[ACT_LUT_SIZE];
extern fp_e8m15_t mish_table_lin_offs[2];
extern fp_e8m15_t mish_table_lin_deriv[2];

// GELU interpolation lookup-table coefficients
extern fp_ue4m4_t gelu_table_lim[ACT_LUT_SIZE];
extern fp_e8m15_t gelu_table_coef0[ACT_LUT_SIZE];
extern fp_e8m15_t gelu_table_coef1[ACT_LUT_SIZE];
extern fp_e8m15_t gelu_table_coef2[ACT_LUT_SIZE];
extern fp_e8m15_t gelu_table_lin_offs[2];
extern fp_e8m15_t gelu_table_lin_deriv[2];

// ELU interpolation lookup-table coefficients
extern fp_ue4m4_t elu_table_lim[ACT_LUT_SIZE];
extern fp_e8m15_t elu_table_coef0[ACT_LUT_SIZE];
extern fp_e8m15_t elu_table_coef1[ACT_LUT_SIZE];
extern fp_e8m15_t elu_table_coef2[ACT_LUT_SIZE];
extern fp_e8m15_t elu_table_lin_offs[2];
extern fp_e8m15_t elu_table_lin_deriv[2];

// Softplus interpolation lookup-table coefficients
extern fp_ue4m4_t softplus_table_lim[ACT_LUT_SIZE];
extern fp_e8m15_t softplus_table_coef0[ACT_LUT_SIZE];
extern fp_e8m15_t softplus_table_coef1[ACT_LUT_SIZE];
extern fp_e8m15_t softplus_table_coef2[ACT_LUT_SIZE];
extern fp_e8m15_t softplus_table_lin_offs[2];
extern fp_e8m15_t softplus_table_lin_deriv[2];

#endif    // NPU_ACT_COMMON_NPU_ACT_LUT_COEFS_HPP_
