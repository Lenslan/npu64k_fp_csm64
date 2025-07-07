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
 * tensor_gtoa.cpp
 *
 * File implementing non-inline methods from the gtoa tensor classes
 *
 */

#include "tensor_gtoa_rescale.hpp"
#include "tensor_gtoa_prelu.hpp"
#include "tensor_gtoa_relu6.hpp"
#include "tensor_gtoa_relu1.hpp"
#include "tensor_gtoa_relu.hpp"
#include "tensor_gtoa_fc_prelu.hpp"
#include "tensor_gtoa_fc_plut.hpp"
#include "tensor_gtoa_clip.hpp"
#include "tensor_gtoa_ninline.hpp"
#include "tensor_gtoa_act_ninline.hpp"
#include "tensor_gtoa_eltop_act_ninline.hpp"
#include "tensor_gtoa_fc_act_ninline.hpp"
#include "tensor_gtoa_rescale_ninline.hpp"
#include "tensor_gtoa_prelu_ninline.hpp"
#include "tensor_gtoa_relu6_ninline.hpp"
#include "tensor_gtoa_relu1_ninline.hpp"
#include "tensor_gtoa_relu_ninline.hpp"
#include "tensor_gtoa_eltop_prelu_ninline.hpp"
#include "tensor_gtoa_fc_prelu_ninline.hpp"
#include "tensor_gtoa_fc_plut_ninline.hpp"
#include "tensor_gtoa_clip_ninline.hpp"
#include "tensor_gtoa_eltmul.hpp"
#include "tensor_gtoa_eltmul_ninline.hpp"
#include "tensor_gtoa_unary.hpp"
#include "tensor_gtoa_unary_ninline.hpp"
#include "tensor_gtoa_binary_mm.hpp"
#include "tensor_gtoa_binary_mb.hpp"
#include "tensor_gtoa_binary_ms.hpp"
#include "tensor_gtoa_nullary.hpp"
#include "tensor_gtoa_nullary_ninline.hpp"
#include "tensor_gtoa_reduce.hpp"
#include "tensor_gtoa_reduce_ninline.hpp"
#include "tensor_gtoa_gavgpool.hpp"
#include "tensor_gtoa_gavgpool_ninline.hpp"
#include "tensor_gtoa_binary.hpp"
#include "tensor_gtoa_binary_ninline.hpp"
#include "tensor_gtoa_binary_mm_ninline.hpp"
#include "tensor_gtoa_binary_mb_ninline.hpp"
#include "tensor_gtoa_binary_ms_ninline.hpp"
#include "tensor_gtoa_lutini.hpp"
#include "tensor_gtoa_lutini_ninline.hpp"
#include "tensor_gtoa_plut.hpp"
#include "tensor_gtoa_plut_ninline.hpp"
#include "./mli/tensor_gtoa_flut.hpp"
#include "tensor_gtoa_flut_ninline.hpp"
#include "tensor_gtoa_exp.hpp"
#include "tensor_gtoa_exp_ninline.hpp"
#include "tensor_gtoa_pool.hpp"
#include "tensor_gtoa_pool_ninline.hpp"
#include "tensor_gtoa_argmax.hpp"
#include "tensor_gtoa_argmax_ninline.hpp"
#include "tensor_gtoa_transpose.hpp"
#include "tensor_gtoa_transpose_ninline.hpp"
#include "tensor_gtoa_shuffle.hpp"
#include "tensor_gtoa_shuffle_ninline.hpp"
//#include "tensor_gtoa_norm.hpp"
//#include "tensor_gtoa_norm_ninline.hpp"
#include "tensor_gtoa_upsample.hpp"
#include "tensor_gtoa_upsample_ninline.hpp"
#include "tensor_gtoa_interp.hpp"
#include "tensor_gtoa_interp_ninline.hpp"
#include "tensor_gtoa_corner_aligned_interp.hpp"
#include "tensor_gtoa_corner_aligned_interp_ninline.hpp"
//#include "tensor_gtoa_softmax.hpp"
//#include "tensor_gtoa_softmax_ninline.hpp"
#include "tensor_gtoa_pad.hpp"
#include "tensor_gtoa_pad_ninline.hpp"
#if NPU_FINST_VERIF
#include "tensor_gtoa_binary_sel_mm.hpp"
#include "tensor_gtoa_binary_movf_mm.hpp"
#include "tensor_gtoa_binary_sel_mm_ninline.hpp"
#include "tensor_gtoa_binary_movf_mm_ninline.hpp"
#endif
