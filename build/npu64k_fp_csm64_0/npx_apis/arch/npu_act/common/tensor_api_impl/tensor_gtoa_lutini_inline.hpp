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
 * tensor_gtoa_plut_inline.hpp
 *
 * File defining a tensor level programmable LUT API base on the generic tensor operation API
 *
 */


#define HLAPI gtoa_params<B>::hlapi

//
// All identifiers related to the convolution engine go into namespace npu_conv
//
// constructor
template<template<typename> class B>
gtoa_lutini_params<B>::gtoa_lutini_params(
                                     gtoa_lut_type_t                    lut_type
                             ) : gtoa_params<B>() {
  // enable LUT initialize
  HLAPI.i.bf     = 1;
  // select LUT tables, note bias of 47 on shift amounts
  switch (lut_type) {
  case gtoa_lut_tanh:
    for (int i = 0; i < ACT_LUT_SIZE; i++) {
      HLAPI.i.u.lut.limf[i]   = tanh_table_lim[i];
      HLAPI.i.u.lut.coeff0[i] = tanh_table_coef0[i];
      HLAPI.i.u.lut.coeff1[i] = tanh_table_coef1[i];
      HLAPI.i.u.lut.coeff2[i] = tanh_table_coef2[i];
    }
    for (int i = 0; i < 2; i++) {
      HLAPI.i.u.lut.lin_offs[i]  = tanh_table_lin_offs[i];
      HLAPI.i.u.lut.lin_deriv[i] = tanh_table_lin_deriv[i];
    }
    break;
  case gtoa_lut_sigmoid:
    for (int i = 0; i < ACT_LUT_SIZE; i++) {
      HLAPI.i.u.lut.limf[i]   = sigmoid_table_lim[i];
      HLAPI.i.u.lut.coeff0[i] = sigmoid_table_coef0[i];
      HLAPI.i.u.lut.coeff1[i] = sigmoid_table_coef1[i];
      HLAPI.i.u.lut.coeff2[i] = sigmoid_table_coef2[i];
    }
    for (int i = 0; i < 2; i++) {
      HLAPI.i.u.lut.lin_offs[i]  = sigmoid_table_lin_offs[i];
      HLAPI.i.u.lut.lin_deriv[i] = sigmoid_table_lin_deriv[i];
    }
    break;
  case gtoa_lut_mish:
    for (int i = 0; i < ACT_LUT_SIZE; i++) {
      HLAPI.i.u.lut.limf[i]   = mish_table_lim[i];
      HLAPI.i.u.lut.coeff0[i] = mish_table_coef0[i];
      HLAPI.i.u.lut.coeff1[i] = mish_table_coef1[i];
      HLAPI.i.u.lut.coeff2[i] = mish_table_coef2[i];
    }
    for (int i = 0; i < 2; i++) {
      HLAPI.i.u.lut.lin_offs[i]  = mish_table_lin_offs[i];
      HLAPI.i.u.lut.lin_deriv[i] = mish_table_lin_deriv[i];
    }
    break;
  case gtoa_lut_swish:
    for (int i = 0; i < ACT_LUT_SIZE; i++) {
      HLAPI.i.u.lut.limf[i]   = swish_table_lim[i];
      HLAPI.i.u.lut.coeff0[i] = swish_table_coef0[i];
      HLAPI.i.u.lut.coeff1[i] = swish_table_coef1[i];
      HLAPI.i.u.lut.coeff2[i] = swish_table_coef2[i];
    }
    for (int i = 0; i < 2; i++) {
      HLAPI.i.u.lut.lin_offs[i]  = swish_table_lin_offs[i];
      HLAPI.i.u.lut.lin_deriv[i] = swish_table_lin_deriv[i];
    }
    break;
  case gtoa_lut_hswish:
    for (int i = 0; i < ACT_LUT_SIZE; i++) {
      HLAPI.i.u.lut.limf[i]   = hswish_table_lim[i];
      HLAPI.i.u.lut.coeff0[i] = hswish_table_coef0[i];
      HLAPI.i.u.lut.coeff1[i] = hswish_table_coef1[i];
      HLAPI.i.u.lut.coeff2[i] = hswish_table_coef2[i];
    }
    for (int i = 0; i < 2; i++) {
      HLAPI.i.u.lut.lin_offs[i]  = hswish_table_lin_offs[i];
      HLAPI.i.u.lut.lin_deriv[i] = hswish_table_lin_deriv[i];
    }
    break;
  case gtoa_lut_gelu:
    for (int i = 0; i < ACT_LUT_SIZE; i++) {
      HLAPI.i.u.lut.limf[i]   = gelu_table_lim[i];
      HLAPI.i.u.lut.coeff0[i] = gelu_table_coef0[i];
      HLAPI.i.u.lut.coeff1[i] = gelu_table_coef1[i];
      HLAPI.i.u.lut.coeff2[i] = gelu_table_coef2[i];
    }
    for (int i = 0; i < 2; i++) {
      HLAPI.i.u.lut.lin_offs[i]  = gelu_table_lin_offs[i];
      HLAPI.i.u.lut.lin_deriv[i] = gelu_table_lin_deriv[i];
    }
    break;
  default: assert(0 && "not supported yet");
  }
}

