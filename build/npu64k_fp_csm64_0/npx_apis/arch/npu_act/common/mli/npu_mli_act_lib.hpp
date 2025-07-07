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
 * npu_mli_act_lib.h
 *
 * File defining a MLI library of predefined activation functions
 *
 */
#ifndef NPU_ACT_COMMON_NPU_MLI_ACT_LIB_HPP_
#define NPU_ACT_COMMON_NPU_MLI_ACT_LIB_HPP_

//
// channelwise reduce operations
//
void init_creduce(act_hlapi_t&, act_bin_op_t);

//
// Mean
//
#define CMEAN_PER_CHAN 2
void init_mean(act_hlapi_t&, act_alay_t, bool, int); // chnpad =-1 will disable chnpad

//
// channel wise mean squared error
//
void init_cmse(act_hlapi_t&, int);// chnpad =-1 will disable chnpad

//
// in0 * rsqrt(in1 + epsilon).broadcast(c)
//
#define MBRSQRT_PER_CHAN 2
void init_add_rsqrt_scale(act_hlapi_t& h, float epsilon, bool biasdbl);

#define SCALE_BINARY_PER_CHAN 2
void init_binary_rr_scale_fp(act_hlapi_t&, act_bin_op_t, act_alay_t, scale_config_t, broadcast_t);


//
// w dim wise mean squared error
//
void init_wmse(act_hlapi_t& h, bool useAcc, bool keepAcc);


//
// in0 * rsqrt(in1 + epsilon).broadcast(w)
//
#define MBRSQRTW_PER_CHAN 2
void init_add_rsqrt_scale_w(act_hlapi_t& h, float epsilon, bool biasdbl);

//
// Mean and Spatial Dim, since GAP do not have prescale
//
#define WMEAN_PER_CHAN 2
void init_wmean(act_hlapi_t& h, bool useAcc, bool keepAcc, act_alay_t l, bool fp32scl);

void init_chan_pad(act_hlapi_t& h, int ch_pad);

//
// Gridsample operations
//
void init_gridsample(act_hlapi_t&);

//
// Prepare grid for Gridsample's padding
//
void init_grid_pad(act_hlapi_t&, act_pad_t, float, float);

//
// Bilinear interpolation of grid (gathered by iDMA)
//
void init_grid_blnr(act_hlapi_t&, bool);

//
// Make 16b int indexes for gather iDMA and 16b fractional
// weights for bilinear interpolation from 16b float grid
//
void init_grid_decomp(act_hlapi_t&);

//
// Make 16b int indexes for gather iDMA from 16b float grid
//
void init_grid_dmaidx(act_hlapi_t&);

#define BMUL_PER_CHAN 2
void init_bmul_scale(act_hlapi_t& h, act_alay_t l, bool biasdbl, broadcast_t brdc_f, bool spodd);
//
// Bilinear interpolation of grid (gathered by iDMA)
//
void init_grid_blnr(act_hlapi_t&, bool);

//
// Make 16b int indexes for gather iDMA and 16b fractional
// weights for bilinear interpolation from 16b float grid
//
void init_grid_decomp(act_hlapi_t&);

//
// Make 16b int indexes for gather iDMA from 16b float grid
//
void init_grid_dmaidx(act_hlapi_t&);

#endif  // NPU_ACT_COMMON_NPU_MLI_ACT_LIB_HPP_
