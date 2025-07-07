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
 * npu_act_lib.h
 *
 * File defining a library of predefined activation functions
 *
 */
#ifndef NPU_ACT_COMMON_NPU_ACT_LIB_HPP_
#define NPU_ACT_COMMON_NPU_ACT_LIB_HPP_

#include "npu_act_hlapi.hpp"      // [NOLINT] [build/include_subdir]
#include "tensor_gtoa_types.hpp"

//
// some macros to make code more readable
//
// start of an activation program, takes the HLAPI as argument X
#define ACT_START(X)   { int slot = 0; array<act_inst_t, ACT_PROG_LEN> p; bool sidx[32]; for (int i = 0; i < 32; i++) sidx[i] = false;
// add instuction Y into the program for HLAPI X and execute in cycle Z
#define ACT_INST(X, Y, Z) p[slot] = act_inst_##Y; assert(slot < ACT_PROG_LEN && "too many instructions in ucode"); assert((Z < 32) && (!sidx[Z]) && "ucode slot should be unique <=32"); p[slot++].pc = Z; sidx[Z] = true
// end of the program for HLAPI X, pad remaining instructions with nop
#define ACT_END(X)     while (slot < ACT_PROG_LEN) p[slot++] = act_inst_nop(); \
uint8_t* cptr(reinterpret_cast<uint8_t*>(&X.i.u.op.act_prog[0])); \
for (slot = 0; slot < ACT_PROG_LEN; slot++) cptr = p[slot].serialize(cptr); }

namespace npu_act::uc::v200 {
//
// Generic unary operation
//
void init_unary(act_hlapi_t&, act_una_op_t);
void init_unary(act_hlapi_t&, act_bin_op_t);   // binary op with second operand 0
void init_unary_fp(act_hlapi_t&, act_una_op_t);
void init_unary_fp(act_hlapi_t&, act_bin_op_t);   // binary op with second operand 0


//
// Generic nullary operation
//
void init_nullary(act_hlapi_t&, act_una_op_t);    // zifu modified
void init_nullary_fp(act_hlapi_t&, act_una_op_t);

//
// Generic reduce operation
//
// void init_reduce(act_hlapi_t&, act_una_op_t);    //zifu modified
// void init_reduce(act_hlapi_t&, act_bin_op_t);    //zifu modified

//
// Generic binary operations
//
void init_binary_rr(act_hlapi_t&, act_bin_op_t);
void init_binary_rr_fp(act_hlapi_t&, act_bin_op_t);
#if NPU_FINST_VERIF
void init_binary_sel_rr(act_hlapi_t&, act_bin_op_t);
void init_binary_movf_rr(act_hlapi_t&, act_bin_op_t);
#endif
void init_binary_rs(act_hlapi_t&, act_bin_op_t);
void init_binary_rs_fp(act_hlapi_t&, act_bin_op_t);
// the operations below assume spatial dimension first iteration
#define BINARY_PAR_PER_CHAN 1
void init_binary_rw(act_hlapi_t&, act_bin_op_t);
void init_binary_rh(act_hlapi_t&, act_bin_op_t);
void init_binary_rb(act_hlapi_t&, act_bin_op_t);
void init_binary_rw_fp(act_hlapi_t&, act_bin_op_t);
void init_binary_rh_fp(act_hlapi_t&, act_bin_op_t);
void init_binary_rb_fp(act_hlapi_t&, act_bin_op_t);


//
// Exponent with optional sum output and max input selection from SR0 or VR7
//
void init_exp(act_hlapi_t&, bool, bool);

//
// LUT function
//
#define PLUT_PAR_PER_CHAN 3
// BRB0: prescale
// BRH1: optional scale
// BRW1: bias
// BRW2: post-scale + asymmetric offset
// non-saturating
void init_lut(act_hlapi_t&, act_alay_t l, bool, bool);

#define ELTOP_PLUT_PAR_PER_CHAN 2
  // BRB0: prescale0
  // BRB1: prescale1
  // BRH1: postscale + asymmetric offset
  // BRW1: bias
  // non-saturating
  void init_eltop_lut(act_hlapi_t&, act_alay_t, act_bin_op_t, bool, broadcast_t);

//
// Fixed LUT functions
//
#define FLUT_PAR_PER_CHAN 3
// BRB0: prescale
// BRH1: optional scale
// BRW1: bias
// BRW2: post-scale + asymmetric offset
// non-saturating
void init_flut(act_hlapi_t&, act_una_op_t op, act_alay_t l, bool, bool);

#define ELTOP_FLUT_PAR_PER_CHAN 2
  // BRB0: prescale0
  // BRB1: prescale1
  // BRH1: postscale + asymmetric offset
  // BRW1: bias
  // non-saturating
  void init_eltop_flut(act_hlapi_t&, act_una_op_t, act_alay_t, act_bin_op_t, bool, broadcast_t);

//
// ReLU activation programs
//
#define RELU_PAR_PER_CHAN 3
  // BRB0: prescale
  // BRH1: scale
  // BRH2: postscale + asymmetric offset
  // BRW2: bias
  void init_relu(act_hlapi_t&, act_alay_t, bool);
  //
  // Eltwise-operation and ReLU activation program
  //
#define ELTOP_RELU_PAR_PER_CHAN 3
  // BRB0: prescale for convolution result
  // BRB1: prescale for eltwise add input
  // BRH1: scale and shift(positive only)
  // BRW1: bias
  // BRW2: postscale + asymmetric offset

  void init_eltop_relu(act_hlapi_t&, act_alay_t, act_bin_op_t, bool, bool);

//
// PReLU activation programs
//
#define PRELU_PAR_PER_CHAN 3
// PReLU activation program
// BRB0: prescale
// BRH1: post-scale + asymmetric offset
// BRW1: positive scale/negative scale
// BRW2: bias
void init_prelu(act_hlapi_t&, act_alay_t, bool);

//
// Fused eltwise-op and PReLU activation
//
#define ELTOP_PRELU_PAR_PER_CHAN 6
// BRB0: prescale for convolution result
// BRB1: prescale for eltwise add input
// BRH1: postscale + asymmetric offset
// BRW1: positive/negative scale
// BRW2: bias for in1
// BRW3: bias for in2
// BRW4: post scale and shift
void init_eltop_prelu(act_hlapi_t&, act_alay_t, act_bin_op_t, bool, bool, broadcast_t);
// Rescale activation programs
//
#define RESCALE_PAR_PER_CHAN 3
// BRB0: prescale
// BRH1: scale
// BRH2: postscale + asymmetric offset
// BRW2: bias
void init_rescale(act_hlapi_t&, act_alay_t, bool);

#define ELTOP_RESCALE_PAR_PER_CHAN 3
// BRB0: prescale0
// BRB1: prescale1
// BRH1: scale
// BRH2: postscale + asymmetric offset
// BRW2: bias
  void init_eltop_rescale(act_hlapi_t&, act_alay_t, act_bin_op_t, bool, bool, broadcast_t);

  //
  // ReLU6 activation programs
  //
#define RELU6_PAR_PER_CHAN 4
  // BRB0: prescale
  // BRH1: scale
  // BRH2: postscale + asymmetric offset
  // BRW2: clipmax
  // BRW3: bias
  void init_relu6(act_hlapi_t&, act_alay_t, bool);

#define ELTOP_RELU6_PAR_PER_CHAN 6
  // BRB0: prescale0
  // BRB1: prescale1
  // BRH1: posscale
  // BRH2: postscale + asymmetric offset
  // BRW2: clipmax
  // BRW3: bias for in1
  // BRW4: bias for in2
  // BRW5: post scale and shift
  void init_eltop_relu6(act_hlapi_t&, act_alay_t, act_bin_op_t, bool, bool, broadcast_t);

  //
  // ReLU1 activation programs
  //
#define RELU1_PAR_PER_CHAN 4
  // BRB0: prescale
  // BRH1: scale
  // BRH2: postscale + asymmetric offset
  // BRW2: clipmax
  // BRW3: bias
  void init_relu1(act_hlapi_t&, act_alay_t, bool);

  //
  // Fused eltwise-op and ReLU1 activation
  //
#define ELTOP_RELU1_PAR_PER_CHAN 6
  // BRB0: prescale0
  // BRB1: prescale1
  // BRH1: posscale
  // BRH2: postscale + asymmetric offset
  // BRW2: clipmax
  // BRW3: bias for in1
  // BRW4: bias for in2
  // BRW5: post scale and shift
  void init_eltop_relu1(act_hlapi_t&, act_alay_t, act_bin_op_t, bool, bool, broadcast_t);
  //
  // FC-PReLU activation programs
  //
#define FC_PRELU_PAR_PER_CHAN 3
// BRH0: positive/negative scale
// BRW1: bias
// BRW2: postscale + asymmetric offset
void init_fc_prelu(act_hlapi_t&, bool);

#define FC_PLUT_PAR_PER_CHAN 2
// BRH0: optional post scale
// BRH1: postscale + asymmetric offset
// BRW1: bias
void init_fc_lut(act_hlapi_t&, bool, bool);

#define ELTOP_FC_PRELU_PAR_PER_CHAN 3
// BRH0: empty
// BRH1: postscale + asymmetric offset
// BRW1: scale
// BRW2: bias
void init_eltop_fc_prelu(act_hlapi_t&, act_bin_op_t, bool, bool);

#define ELTOP_FC_PLUT_PAR_PER_CHAN 2
// BRH0: optional scale
// BRH1: postscale + asymmetric offset
// BRW1: bias
void init_eltop_fc_lut(act_hlapi_t&, act_bin_op_t, bool, bool, bool);

//
// Clip1 activation programs
//
#define CLIP_PAR_PER_CHAN 3
// BRB0: prescale
// BRW1: clipmax
// BRW2: clipmin
void init_clip(act_hlapi_t&, act_alay_t);

#define ELTOP_CLIP_PAR_PER_CHAN 3
// BRB0: prescale0
// BRB1: prescale1
// BRW1: clipmax
// BRW2: clipmin
  void init_eltop_clip(act_hlapi_t&, act_alay_t, act_bin_op_t, bool);


//
// Standalone maxpooling
//
#define MAXPOOL_PAR_PER_CHAN 0
void init_maxpool(act_hlapi_t&);

//
// Standalone average pooling
//
#define AVGPOOL_PAR_PER_CHAN 0
void init_avgpool(act_hlapi_t&);
void init_avgpool(act_hlapi_t&,bool);

//
// Standalone global average pooling
//
#define GAVGPOOL_PAR_PER_CHAN 0
void init_gavgpool(act_hlapi_t&, bool, bool);
void init_gavgpool_new(act_hlapi_t&, bool, bool);
void init_gavgpool_v2(act_hlapi_t&, float);

//
// Standalone sumpooling
//
#define SUMPOOL_PAR_PER_CHAN 0
void init_sumpool(act_hlapi_t&);

//
// Argmax
//
// across channel, return index in SR0 and max in VR7
#define ARGGMAX_C_PAR_PER_CHAN 0
void init_argmax_c0(act_hlapi_t&);
void init_argmax_c1(act_hlapi_t&);
// across width, return tensor index
#define ARGGMAX_PAR_PER_CHAN 0
void init_argmax(act_hlapi_t&, bool);

//
// Reduce in W dimension
//
#define REDUCE_PAR_PER_CHAN 0
void init_reduce(act_hlapi_t&, act_bin_op_t, bool);
void init_reduce_accum(act_hlapi_t&, act_bin_op_t, bool, bool);

//
// Transpose channel and width
//
#define TRANSPOSE_PAR_PER_CHAN 0
void init_transpose(act_hlapi_t&, bool);

#if 0
//
// Normalization
//
#define L1NORM_PAR_PER_CHAN 0
void init_l1norm(act_hlapi_t&);
#define L2NORM_PAR_PER_CHAN 0
void init_l2norm(act_hlapi_t&);
#define SCALE_PAR_PER_CHAN 0
void init_scale(act_hlapi_t&);
#define RECIP_SCALE_PAR_PER_CHAN 0
void init_recip_scale(act_hlapi_t&);
#endif  // removed integer norm

//
// Upsample
//
void init_upsample(act_hlapi_t&);
void init_upsample(act_hlapi_t&, float, float);

//
// Shuffle
//
void init_shuffle(act_hlapi_t&, bool fmdbl, bool odd);

//
// Elementwise multiply
//
#define ELTOP_ELTMUL_SCALE_PAR_PER_CHAN 3
void init_eltmul(act_hlapi_t&, act_alay_t, bool, broadcast_t, bool, bool);

//
// Corner aligned linear 1D interpolation
//
#define CORNER_INTERP1D_PAR_PER_CHAN 0
void init_interp1d(act_hlapi_t&, int32_t, int32_t);

//
// Gather operations
//
void init_gather2d(act_hlapi_t&);

//
// Standalone padding
//
void init_pad(act_hlapi_t&, bool);

#if NPU_MLI_TAPI_EN
#include "./mli/npu_mli_act_lib.hpp"
#endif

}  // namespace npu_act


#endif  // NPU_ACT_COMMON_NPU_ACT_LIB_HPP_
