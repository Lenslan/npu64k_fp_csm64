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
 * npu_act_types.hpp
 *
 * File defining the activation HLAPI structure
 *
 */
#ifndef NPU_ACT_COMMON_NPU_ACT_TYPES_HPP_
#define NPU_ACT_COMMON_NPU_ACT_TYPES_HPP_

namespace npu_act {
//
// import global NPU types
//
using namespace tensor::v200;  // [NOLINT]

// register indices
enum act_sidx_t { sr0, sr1, sr2, sr3, sr4, sr5, sr6, sr7 };
enum act_vidx_t { vr0, vr1, vr2, vr3, vr4, vr5, vr6, vr7 };
enum act_widx_t { brw0, brw1, brw2, brw3, brw4, brw5, brw6, brw7 };
enum act_hidx_t { brh0, brh1, brh2, brh3, brh4, brh5, brh6, brh7 };
enum act_bidx_t { brb0, brb1, brb2, brb3, brb4, brb5, brb6, brb7 };


// predication conditions
enum act_pred_t {
  pred_never = 0,   // never execute
  pred_first0,  // enable at first iteration of outer loop
  pred_first1,  // enable at first iteration of middle loop
  pred_first2,  // enable at first iteration of inner loop
  pred_last2,   // enable in last iteration of inner loop
  pred_last1,   // enable in last iteration of middle loop
  pred_last0,   // enable in unless last iteration of outer loop
  pred_nfirst0, // enable at unless first iteration of outer loop
  pred_nfirst1, // enable at unless first iteration of middle loop
  pred_nfirst2, // enable at unless first iteration of inner loop
  pred_nlast2,  // enable in unless last iteration of inner loop
  pred_nlast1,  // enable in unless last iteration of middle loop
  pred_nlast0,  // enable in unless last iteration of outer loop
  pred_even,    // enable in even iterations
  pred_odd,     // enable in odd iterations
  pred_always   // always enable
};


// scalar registers
#define SR0 act_sidx_t::sr0
#define SR1 act_sidx_t::sr1
#define SR2 act_sidx_t::sr2
#define SR3 act_sidx_t::sr3

// vector registers
#define VR0 act_vidx_t::vr0
#define VR1 act_vidx_t::vr1
#define VR2 act_vidx_t::vr2
#define VR3 act_vidx_t::vr3
#define VR4 act_vidx_t::vr4
#define VR5 act_vidx_t::vr5
#define VR6 act_vidx_t::vr6
#define VR7 act_vidx_t::vr7

// parameter registers
#define BRW0 act_widx_t::brw0
#define BRW1 act_widx_t::brw1
#define BRW2 act_widx_t::brw2
#define BRW3 act_widx_t::brw3
#define BRW4 act_widx_t::brw4
#define BRW5 act_widx_t::brw5
#define BRW6 act_widx_t::brw6
#define BRW7 act_widx_t::brw7
#define BRH0 act_hidx_t::brh0
#define BRH1 act_hidx_t::brh1
#define BRH2 act_hidx_t::brh2
#define BRH3 act_hidx_t::brh3
#define BRH4 act_hidx_t::brh4
#define BRH5 act_hidx_t::brh5
#define BRH6 act_hidx_t::brh6
#define BRH7 act_hidx_t::brh7
#define BRB0 act_bidx_t::brb0
#define BRB1 act_bidx_t::brb1
#define BRB2 act_bidx_t::brb2
#define BRB3 act_bidx_t::brb3
#define BRB4 act_bidx_t::brb4
#define BRB5 act_bidx_t::brb5
#define BRB6 act_bidx_t::brb6
#define BRB7 act_bidx_t::brb7

// predidate conditions
#define PNEVER   act_pred_t::pred_never
#define PFIRST0  act_pred_t::pred_first0
#define PFIRST1  act_pred_t::pred_first1
#define PFIRST2  act_pred_t::pred_first2
#define PLAST2   act_pred_t::pred_last2
#define PLAST1   act_pred_t::pred_last1
#define PLAST0   act_pred_t::pred_last0
#define PNFIRST0 act_pred_t::pred_nfirst0
#define PNFIRST1 act_pred_t::pred_nfirst1
#define PNFIRST2 act_pred_t::pred_nfirst2
#define PNLAST2  act_pred_t::pred_nlast2
#define PNLAST1  act_pred_t::pred_nlast1
#define PNLAST0  act_pred_t::pred_nlast0
#define PEVEN    act_pred_t::pred_even
#define PODD     act_pred_t::pred_odd
#define PALWAYS  act_pred_t::pred_always


///////////////////////////////////////////////////////////////////////////////////////////////////
//
// Activation HLAPI data-types
//
///////////////////////////////////////////////////////////////////////////////////////////////////

// accumulator layout
enum act_alay_t { alayo16, alayo32 };
// floating mode data format
enum act_ffmt_t { ffmt_int32, ffmt_fp32, ffmt_fp16, ffmt_bf16};


///////////////////////////////////////////////////////////////////////////////////////////////////
//
// look-up table
//
///////////////////////////////////////////////////////////////////////////////////////////////////
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
struct act_lut_t {
  // interpolation look-up steps on fp32 input x:
  // step 1: is x negative? use idx 0..7, or positive? use idx 8..15
  // step 1: search for first idx for which  abs(x)<abs(lim[idx])
  // step 2: return coef0/1/2 parameters and x in scale0, scale1
  // step 3: compute mac0 : t = (coef1 + coef2 * x)
  // step 4: compute mac1 : out  = (coef0 + t * x)
  array<fp_e8m15_t,2>              lin_offs;  // offset for linear interpolation beyond 
                                              // interval [0] negative [1] positive
  array<fp_e8m15_t,2>              lin_deriv; // derivative for linear interpolation beyond 
                                              // interval [0] negative [1] positive
  array<fp_e8m15_t, ACT_LUT_SIZE>  coeff0;
  array<fp_e8m15_t, ACT_LUT_SIZE>  coeff1;
  array<fp_e8m15_t, ACT_LUT_SIZE>  coeff2;
  array<fp_ue4m4_t, ACT_LUT_SIZE>  limf;   // define interval boundaries:
                                     // first +ve interval 0,lim[8]
                                     // second +ve interval lim[8],lim[9]
                                     // ..
                                     // last +ve interval lim[14],lim[15]
                                     // +ve linear region x>=lim[15]
                                     // first -ve interval lim[0],0]
                                     // second -ve interval lim[1],lim[0]
                                     // .. last -ve interval lim[7],lim[6]
                                     // .. last -ve interval lim[7],lim[6]
                                     // -ve linear region x<=lim[7]
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif


// scalar activation program type
typedef int32_t act_scalar_t;

// scaling parameters
// scaling operations will do y = (ofs+mul*x)>>shf
typedef enum { cmd_normal_e, cmd_nan_e, cmd_exp_repl_e,  cmd_exp_repl_neg_e } act_lut_cmd_t;
struct act_scale_t {
  fp_e8m23_t    ofs;
  fp_e8m23_t    mul;
  int8_t        exp_offset;
  act_lut_cmd_t command;
};

}  // namespace npu_act
#endif  // NPU_ACT_COMMON_NPU_ACT_TYPES_HPP_
