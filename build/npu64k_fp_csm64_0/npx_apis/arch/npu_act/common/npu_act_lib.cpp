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
 * npu_act_lib.c
 *
 * File defining a library of predefined activation functions
 *
 */

#include "npu_act_lib.hpp"  // [NOLINT]

namespace npu_act::uc::v200 {


/////////////////////////////////////////////////////////////////
//
// Generic nullary operation, integer only
//
/////////////////////////////////////////////////////////////////

void init_nullary(
                  act_hlapi_t& h, 
                  act_una_op_t op
                  ) {
  // start of activation program
  ACT_START(h);
  switch (op) {
    case op_getid:    ACT_INST(h, getid(PALWAYS, VR0), 2);   break;
    case op_strv:     ACT_INST(h, strv(PALWAYS, VR0), 2);    break;
    case op_strc:     ACT_INST(h, strc(PALWAYS, VR0), 2);    break;
    default:          assert(0 && "unsupported nullary operation");
  }
  ACT_INST(h, pushout(PALWAYS, VR0), 4);
  ACT_END(h);
  // end of program
}

/////////////////////////////////////////////////////////////////
//
// Generic nullary operation, floating-point
//
/////////////////////////////////////////////////////////////////

void init_nullary_fp(
                  act_hlapi_t& h, 
                  act_una_op_t op
                  ) {
  // start of activation program
  ACT_START(h);
  switch (op) {
    case op_getid:    ACT_INST(h, getid(PALWAYS, VR0), 2);   break;
    case op_strv:     ACT_INST(h, strv(PALWAYS, VR0), 2);    break;
    case op_strc:     ACT_INST(h, strc(PALWAYS, VR0), 2);    break;
    default:          assert(0 && "unsupported nullary operation");
  }
  ACT_INST(h, itof(PALWAYS, VR1, VR0), 4);
  ACT_INST(h, fpushout(PALWAYS, VR1), 6);
  ACT_END(h);
  // end of program
}


/////////////////////////////////////////////////////////////////
//
// Generic unary operations, integer
//
/////////////////////////////////////////////////////////////////

void init_unary(
                act_hlapi_t& h,
                act_una_op_t op
                ) {
  // start of activation program
  ACT_START(h);
  ACT_INST(h, popin0(PALWAYS, VR0), 0);
  switch (op) {
    case op_bcc:    ACT_INST(h, bcc(PALWAYS, VR1, VR0), 4);    break;
    case op_bcv:    ACT_INST(h, bcv(PALWAYS, VR1, VR0), 4);    break;
    case op_abs:    ACT_INST(h, abs(PALWAYS, VR1, VR0), 4);    break;
    case op_bnot:   ACT_INST(h, bnot(PALWAYS, VR1, VR0), 4);   break;
    case op_sat8:   ACT_INST(h, sat8(PALWAYS, VR1, VR0), 4);   break;
    case op_sat16:  ACT_INST(h, sat16(PALWAYS, VR1, VR0), 4);  break;
    case op_shv:    ACT_INST(h, shv(PALWAYS, VR1, VR0), 4);    break;
    case op_shc:    ACT_INST(h, shc(PALWAYS, VR1, VR0), 4);    break;
    case op_shrc:   ACT_INST(h, shrc(PALWAYS, VR1, VR0), 4);   break;
    case op_randv:  ACT_INST(h, randv(PALWAYS, VR1, VR0), 4);  break;
    case op_rorv:   ACT_INST(h, rorv(PALWAYS, VR1, VR0), 4);   break;
    default: assert(0 && "unsupported unary operation");
  }
  ACT_INST(h, pushout(PALWAYS, VR1), 6);
  ACT_END(h);
  // end of program
}

void init_unary(
                act_hlapi_t& h, 
                act_bin_op_t op
                ) {
  // start of activation program
  ACT_START(h);
  ACT_INST(h, popin0(PALWAYS, VR0), 0);
  switch (op) {
    case op_eq:    ACT_INST(h, eq(PALWAYS, VR1, VR0), 4);    break;
    case op_neq:   ACT_INST(h, neq(PALWAYS, VR1, VR0), 4);   break;
    case op_gt:    ACT_INST(h, gt(PALWAYS, VR1, VR0), 4);    break;
    case op_gte:   ACT_INST(h, gte(PALWAYS, VR1, VR0), 4);   break;
    case op_lt:    ACT_INST(h, lt(PALWAYS, VR1, VR0), 4);    break;
    case op_lte:   ACT_INST(h, lte(PALWAYS, VR1, VR0), 4);   break;
    case op_add:   ACT_INST(h, add(PALWAYS, VR1, VR0), 4);   break;  // = move
    case op_rsub:  ACT_INST(h, rsub(PALWAYS, VR1, VR0), 4);  break;  // = negate
    case op_min:   ACT_INST(h, min(PALWAYS, VR1, VR0), 4);   break;
    case op_max:   ACT_INST(h, max(PALWAYS, VR1, VR0), 4);   break;
    default: assert(0 && "unsupported unary operation");
  }
  if (op == op_add || op == op_rsub) {
    ACT_INST(h, pushout(PALWAYS, VR1), 6);
  } else {
    // compare returns flags
    ACT_INST(h, movf(PALWAYS, VR2), 6);
    ACT_INST(h, pushout(PALWAYS, VR2), 8);
  }
  ACT_END(h);
  // end of activation program
}

/////////////////////////////////////////////////////////////////
//
// Generic unary operations, floating-point
//
/////////////////////////////////////////////////////////////////

void init_unary_fp(
                   act_hlapi_t& h, 
                   act_una_op_t op
                   ) {
  // start of activation program
  ACT_START(h);
  ACT_INST(h, fpopin0(PALWAYS, VR0), 0);
  switch (op) {
    case op_fabs:    ACT_INST(h, fabs(PALWAYS, VR1, VR0), 4);    break;
    case op_raddv:   ACT_INST(h, raddv(PALWAYS, VR1, VR0), 4);    break;
    case op_rminv:   ACT_INST(h, rminv(PALWAYS, VR1, VR0), 4);    break;
    case op_rmaxv:   ACT_INST(h, rmaxv(PALWAYS, VR1, VR0), 4);   break;
    default: assert(0 && "unsupported unary operation");
  }
  ACT_INST(h, fpushout(PALWAYS, VR1), 6);
  ACT_END(h);
  // end of program
}

void init_unary_fp(
                   act_hlapi_t& h,
                   act_bin_op_t op
                   ) {
  // unary floating-point, 2nd binary operand 0
  
  // start of activation program
  ACT_START(h);
  ACT_INST(h, fpopin0(PALWAYS, VR0), 0);
  switch (op) {
    case op_feq:    ACT_INST(h, feq(PALWAYS, VR1, VR0), 4);    break;
    case op_fneq:   ACT_INST(h, fneq(PALWAYS, VR1, VR0), 4);   break;
    case op_fgt:    ACT_INST(h, fgt(PALWAYS, VR1, VR0), 4);    break;
    case op_fgte:   ACT_INST(h, fgte(PALWAYS, VR1, VR0), 4);   break;
    case op_flt:    ACT_INST(h, flt(PALWAYS, VR1, VR0), 4);    break;
    case op_flte:   ACT_INST(h, flte(PALWAYS, VR1, VR0), 4);   break;
    case op_fadd:   ACT_INST(h, fadd(PALWAYS, VR1, VR0), 4);   break;  // = move
    case op_frsub:  ACT_INST(h, frsub(PALWAYS, VR1, VR0), 4);  break;  // = negate
    case op_fmin:   ACT_INST(h, fmin(PALWAYS, VR1, VR0), 4);   break;
    case op_fmax:   ACT_INST(h, fmax(PALWAYS, VR1, VR0), 4);   break;
    default: assert(0 && "unsupported unary operation");
  }
  if (op == op_fadd || op == op_frsub) {
    ACT_INST(h, fpushout(PALWAYS, VR1), 6);
  } else {
    ACT_INST(h, movf(PALWAYS, VR2), 6);
    ACT_INST(h, fpushout(PALWAYS, VR2), 8);
  }
  ACT_END(h);
  // end of activation program
}

/////////////////////////////////////////////////////////////////
//
// Generic binary operations, integer
//
/////////////////////////////////////////////////////////////////
void init_binary_rr(
                    act_hlapi_t& h, 
                    act_bin_op_t op
                    ) {
  // start of activation program
  ACT_START(h);
  ACT_INST(h, popin0(PALWAYS, VR0), 0); ACT_INST(h, popin1(PALWAYS, VR1), 1);  // in same slot
  switch (op) {
    case op_add:   ACT_INST(h, add(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_sub:   ACT_INST(h, sub(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_rsub:  ACT_INST(h, rsub(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_min:   ACT_INST(h, min(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_max:   ACT_INST(h, max(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_relun: ACT_INST(h, relun(PALWAYS, VR2, VR0, VR1), 4); break;
    case op_eq:    ACT_INST(h, eq(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_neq:   ACT_INST(h, neq(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_gt:    ACT_INST(h, gt(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_gte:   ACT_INST(h, gte(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_lt:    ACT_INST(h, lt(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_lte:   ACT_INST(h, lte(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_band:  ACT_INST(h, band(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_bor:   ACT_INST(h, bor(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_bxor:  ACT_INST(h, bxor(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_asr:   ACT_INST(h, asr(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_lsr:   ACT_INST(h, lsr(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_sl:    ACT_INST(h, sl(PALWAYS, VR2, VR0, VR1), 4);    break;
    default: assert(0 && "unsupported binary_rr operation");
  }
  if (op == op_eq || op == op_neq || op == op_lt || op == op_lte || op == op_gt || op == op_gte) {
    ACT_INST(h, movf(PALWAYS, VR3), 6);
    ACT_INST(h, pushout(PALWAYS, VR3), 8);
  } else {
    ACT_INST(h, pushout(PALWAYS, VR2), 6);
  }
  ACT_END(h);
  // end of activation program
}

void init_binary_rs(
                    act_hlapi_t& h, 
                    act_bin_op_t op
                    ) {
  // SR0 has the second operand
  // start of activation program
  ACT_START(h);
  // broadcast scalar to vector
  ACT_INST(h, add(PFIRST0, VR1, SR0), 0);
  ACT_INST(h, popin0(PALWAYS, VR0), 1);
  switch (op) {
    case op_add:   ACT_INST(h, add(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_sub:   ACT_INST(h, sub(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_rsub:  ACT_INST(h, rsub(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_min:   ACT_INST(h, min(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_max:   ACT_INST(h, max(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_relun: ACT_INST(h, relun(PALWAYS, VR2, VR0, VR1), 4); break;
    case op_eq:    ACT_INST(h, eq(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_neq:   ACT_INST(h, neq(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_gt:    ACT_INST(h, gt(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_gte:   ACT_INST(h, gte(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_lt:    ACT_INST(h, lt(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_lte:   ACT_INST(h, lte(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_band:  ACT_INST(h, band(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_bor:   ACT_INST(h, bor(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_bxor:  ACT_INST(h, bxor(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_asr:   ACT_INST(h, asr(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_lsr:   ACT_INST(h, lsr(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_sl:    ACT_INST(h, sl(PALWAYS, VR2, VR0, VR1), 4);    break;
    default: assert(0 && "unsupported binary_rr operation");
  }
  if (op == op_eq || op == op_neq || op == op_lt || op == op_lte || op == op_gt || op == op_gte) {
    ACT_INST(h, movf(PALWAYS, VR3), 6);
    ACT_INST(h, pushout(PALWAYS, VR3), 8);
  } else {
    ACT_INST(h, pushout(PALWAYS, VR2), 6);
  }
  ACT_END(h);
  // end of activation program
}

void init_binary_rw(
                    act_hlapi_t& h, 
                    act_bin_op_t op
                    ) {
  // one 32b per channel
  h.i.u.op.scl[1] = 1;
  // start of activation program
  ACT_START(h);
  // outer loop
  // get new set of per channel parameters on first iteration of spatial loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);
  // inner loop
  ACT_INST(h, popin0(PALWAYS, VR0), 1);
  switch (op) {
    case op_add:   ACT_INST(h, add(PALWAYS, VR1, VR0, BRW0), 4);   break;
    case op_sub:   ACT_INST(h, sub(PALWAYS, VR1, VR0, BRW0), 4);   break;
    case op_rsub:  ACT_INST(h, rsub(PALWAYS, VR1, VR0, BRW0), 4);  break;
    case op_min:   ACT_INST(h, min(PALWAYS, VR1, VR0, BRW0), 4);   break;
    case op_max:   ACT_INST(h, max(PALWAYS, VR1, VR0, BRW0), 4);   break;
    case op_relun: ACT_INST(h, relun(PALWAYS, VR1, VR0, BRW0), 4); break;
    case op_eq:    ACT_INST(h, eq(PALWAYS, VR1, VR0, BRW0), 4);    break;
    case op_neq:   ACT_INST(h, neq(PALWAYS, VR1, VR0, BRW0), 4);   break;
    case op_gt:    ACT_INST(h, gt(PALWAYS, VR1, VR0, BRW0), 4);    break;
    case op_gte:   ACT_INST(h, gte(PALWAYS, VR1, VR0, BRW0), 4);   break;
    case op_lt:    ACT_INST(h, lt(PALWAYS, VR1, VR0, BRW0), 4);    break;
    case op_lte:   ACT_INST(h, lte(PALWAYS, VR1, VR0, BRW0), 4);   break;
    case op_band:  ACT_INST(h, band(PALWAYS, VR1, VR0, BRW0), 4);  break;
    case op_bor:   ACT_INST(h, bor(PALWAYS, VR1, VR0, BRW0), 4);   break;
    case op_bxor:  ACT_INST(h, bxor(PALWAYS, VR1, VR0, BRW0), 4);  break;
    default: assert(0 && "unsupported binary_rw operation");
  }
  if (op == op_eq || op == op_neq || op == op_lt || op == op_lte || op == op_gt || op == op_gte) {
    ACT_INST(h, movf(PALWAYS, VR2), 6);
    ACT_INST(h, pushout(PALWAYS, VR2), 8);
  } else {
    ACT_INST(h, pushout(PALWAYS, VR1), 6);
  }
  ACT_END(h);
  // end of activation program
}

void init_binary_rh(
                    act_hlapi_t& h, 
                    act_bin_op_t op
                    ) {
  // one 32b per channel
  h.i.u.op.scl[1] = 1;

  // start of activation program
  ACT_START(h);
  // outer loop
  // get new set of per channel parameters on first iteration of spatial loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);
  // inner loop
  ACT_INST(h, popin0(PALWAYS, VR0), 1);
  switch (op) {
    case op_add:   ACT_INST(h, add(PALWAYS, VR1, VR0, BRH0), 4);   break;
    case op_sub:   ACT_INST(h, sub(PALWAYS, VR1, VR0, BRH0), 4);   break;
    case op_rsub:  ACT_INST(h, rsub(PALWAYS, VR1, VR0, BRH0), 4);  break;
    case op_min:   ACT_INST(h, min(PALWAYS, VR1, VR0, BRH0), 4);   break;
    case op_max:   ACT_INST(h, max(PALWAYS, VR1, VR0, BRH0), 4);   break;
    case op_relun: ACT_INST(h, relun(PALWAYS, VR1, VR0, BRH0), 4); break;
    case op_eq:    ACT_INST(h, eq(PALWAYS, VR1, VR0, BRH0), 4);    break;
    case op_neq:   ACT_INST(h, neq(PALWAYS, VR1, VR0, BRH0), 4);   break;
    case op_gt:    ACT_INST(h, gt(PALWAYS, VR1, VR0, BRH0), 4);    break;
    case op_gte:   ACT_INST(h, gte(PALWAYS, VR1, VR0, BRH0), 4);   break;
    case op_lt:    ACT_INST(h, lt(PALWAYS, VR1, VR0, BRH0), 4);    break;
    case op_lte:   ACT_INST(h, lte(PALWAYS, VR1, VR0, BRH0), 4);   break;
    case op_band:  ACT_INST(h, band(PALWAYS, VR1, VR0, BRH0), 4);  break;
    case op_bor:   ACT_INST(h, bor(PALWAYS, VR1, VR0, BRH0), 4);   break;
    case op_bxor:  ACT_INST(h, bxor(PALWAYS, VR1, VR0, BRH0), 4);  break;
    default: assert(0 && "unsupported binary_rh operation");
  }
  if (op == op_eq || op == op_neq || op == op_lt || op == op_lte || op == op_gt || op == op_gte) {
    ACT_INST(h, movf(PALWAYS, VR2), 6);
    ACT_INST(h, pushout(PALWAYS, VR2), 8);
  } else {
    ACT_INST(h, pushout(PALWAYS, VR1), 6);
  }
  ACT_END(h);
  // end of activation program
}

void init_binary_rb(
                    act_hlapi_t& h, 
                    act_bin_op_t op
                    ) {
  // SR1 has number of per channel parameters to pop
  h.i.u.op.scl[1] = 1;

  // start of activation program
  ACT_START(h);
  // outer loop
  // get new set of per channel parameters on first iteration of spatial loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);
  // inner loop
  ACT_INST(h, popin0(PALWAYS, VR0), 1);
  switch (op) {
    case op_add:   ACT_INST(h, add(PALWAYS, VR1, VR0, BRB0), 4);   break;
    case op_sub:   ACT_INST(h, sub(PALWAYS, VR1, VR0, BRB0), 4);   break;
    case op_rsub:  ACT_INST(h, rsub(PALWAYS, VR1, VR0, BRB0), 4);  break;
    case op_min:   ACT_INST(h, min(PALWAYS, VR1, VR0, BRB0), 4);   break;
    case op_max:   ACT_INST(h, max(PALWAYS, VR1, VR0, BRB0), 4);   break;
    case op_relun: ACT_INST(h, relun(PALWAYS, VR1, VR0, BRB0), 4); break;
    case op_eq:    ACT_INST(h, eq(PALWAYS, VR1, VR0, BRB0), 4);    break;
    case op_neq:   ACT_INST(h, neq(PALWAYS, VR1, VR0, BRB0), 4);   break;
    case op_gt:    ACT_INST(h, gt(PALWAYS, VR1, VR0, BRB0), 4);    break;
    case op_gte:   ACT_INST(h, gte(PALWAYS, VR1, VR0, BRB0), 4);   break;
    case op_lt:    ACT_INST(h, lt(PALWAYS, VR1, VR0, BRB0), 4);    break;
    case op_lte:   ACT_INST(h, lte(PALWAYS, VR1, VR0, BRB0), 4);   break;
    case op_band:  ACT_INST(h, band(PALWAYS, VR1, VR0, BRB0), 4);  break;
    case op_bor:   ACT_INST(h, bor(PALWAYS, VR1, VR0, BRB0), 4);   break;
    case op_bxor:  ACT_INST(h, bxor(PALWAYS, VR1, VR0, BRB0), 4);  break;
    case op_asr:   ACT_INST(h, asr(PALWAYS, VR1, VR0, BRB0), 4);   break;
    case op_lsr:   ACT_INST(h, lsr(PALWAYS, VR1, VR0, BRB0), 4);   break;
    case op_sl:    ACT_INST(h, sl(PALWAYS, VR1, VR0, BRB0), 4);    break;
    default: assert(0 && "unsupported binary_rb operation");
  }
  if (op == op_eq || op == op_neq || op == op_lt || op == op_lte || op == op_gt || op == op_gte) {
    ACT_INST(h, movf(PALWAYS, VR2), 6);
    ACT_INST(h, pushout(PALWAYS, VR2), 8);
  } else {
    ACT_INST(h, pushout(PALWAYS, VR1), 6);
  }
  ACT_END(h);
  // end of activation program
}


/////////////////////////////////////////////////////////////////
//
// Generic binary operations (floating point)
//
/////////////////////////////////////////////////////////////////

void init_binary_rr_fp(
                       act_hlapi_t& h, 
                       act_bin_op_t op
                       ) {
  // start of activation program
  ACT_START(h);
  ACT_INST(h, fpopin0(PALWAYS, VR0), 0); ACT_INST(h, fpopin1(PALWAYS, VR1), 1); // in same slot
  int l = 6;
  switch (op) {
    case op_fadd:   ACT_INST(h, fadd(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_fsub:   ACT_INST(h, fsub(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_frsub:  ACT_INST(h, frsub(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_fmin:   ACT_INST(h, fmin(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_fmax:   ACT_INST(h, fmax(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_faddf:  ACT_INST(h, faddf(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_fsubf:  ACT_INST(h, fsubf(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_frsubf: ACT_INST(h, frsubf(PALWAYS, VR2, VR0, VR1), 4); break;
    case op_fminf:  ACT_INST(h, fminf(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_fmaxf:  ACT_INST(h, fmaxf(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_frelun: ACT_INST(h, frelun(PALWAYS, VR2, VR0, VR1), 4); break;
    case op_feq:    ACT_INST(h, feq(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_fneq:   ACT_INST(h, fneq(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_fgt:    ACT_INST(h, fgt(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_fgte:   ACT_INST(h, fgte(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_flt:    ACT_INST(h, flt(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_flte:   ACT_INST(h, flte(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_mpy:    ACT_INST(h, mpy(PALWAYS, VR2, VR0, VR1), 4);  l = 8; break;
    case op_mpyh:   ACT_INST(h, mpyh(PALWAYS, VR2, VR0, VR1), 4); l = 8; break;
    case op_mpyb:   ACT_INST(h, mpyb(PALWAYS, VR2, VR0, VR1), 4); l = 8; break;
    default: assert(0 && "unsupported binary_rr operation");
  }
  if (op == op_feq || op == op_fneq || op == op_flt || op == op_flte || op == op_fgt || op == op_fgte) {
    // move implicit compare falgs to explicit register
    ACT_INST(h, movf(PALWAYS, VR3), 6);
    ACT_INST(h, fpushout(PALWAYS, VR3), 8);
  } else {
    ACT_INST(h, fpushout(PALWAYS, VR2), l);
  }
  ACT_END(h);
  // end of activation program
}

void init_binary_rs_fp(act_hlapi_t& h, act_bin_op_t op) {  // [NOLINT]
  // SR0 has the second operand
  // start of activation program
  ACT_START(h);
  ACT_INST(h, add(PFIRST0, VR1, SR0), 0);
  ACT_INST(h, fpopin0(PALWAYS, VR0), 1);
  switch (op) {
    case op_fadd:   ACT_INST(h, fadd(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_fsub:   ACT_INST(h, fsub(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_frsub:  ACT_INST(h, frsub(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_fmin:   ACT_INST(h, fmin(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_fmax:   ACT_INST(h, fmax(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_faddf:  ACT_INST(h, faddf(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_fsubf:  ACT_INST(h, fsubf(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_frsubf: ACT_INST(h, frsubf(PALWAYS, VR2, VR0, VR1), 4); break;
    case op_fminf:  ACT_INST(h, fminf(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_fmaxf:  ACT_INST(h, fmaxf(PALWAYS, VR2, VR0, VR1), 4);  break;
    case op_frelun: ACT_INST(h, frelun(PALWAYS, VR2, VR0, VR1), 4); break;
    case op_feq:    ACT_INST(h, feq(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_fneq:   ACT_INST(h, fneq(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_fgt:    ACT_INST(h, fgt(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_fgte:   ACT_INST(h, fgte(PALWAYS, VR2, VR0, VR1), 4);   break;
    case op_flt:    ACT_INST(h, flt(PALWAYS, VR2, VR0, VR1), 4);    break;
    case op_flte:   ACT_INST(h, flte(PALWAYS, VR2, VR0, VR1), 4);   break;
    default: assert(0 && "unsupported binary_rs_fp operation");
  }
  if (op == op_feq || op == op_fneq || op == op_flt || op == op_flte || op == op_fgt || op == op_fgte) {
    ACT_INST(h, movf(PALWAYS, VR3), 6);
    ACT_INST(h, fpushout(PALWAYS, VR3), 8);
  } else {
    ACT_INST(h, fpushout(PALWAYS, VR2), 6);
  }
  ACT_END(h);
  // end of activation program
}

void init_binary_rw_fp(act_hlapi_t& h, act_bin_op_t op) {  // [NOLINT]
  // one 32b per channel
  h.i.u.op.scl[1] = 1;
  h.i.u.op.scl[2] = 1;
  // start of activation program
  ACT_START(h);
  // outer loop
  // get new set of per channel parameters on first iteration of spatial loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);
  // inner loop
  ACT_INST(h, fpopin0(PALWAYS, VR0), 2);
  int l = 8;
  switch (op) {
    case op_fadd:   ACT_INST(h, fadd(PALWAYS, VR1, VR0, BRW0), 6);   break;
    case op_fsub:   ACT_INST(h, fsub(PALWAYS, VR1, VR0, BRW0), 6);   break;
    case op_frsub:  ACT_INST(h, frsub(PALWAYS, VR1, VR0, BRW0), 6);  break;
    case op_fmin:   ACT_INST(h, fmin(PALWAYS, VR1, VR0, BRW0), 6);   break;
    case op_fmax:   ACT_INST(h, fmax(PALWAYS, VR1, VR0, BRW0), 6);   break;
    case op_faddf:  ACT_INST(h, faddf(PALWAYS, VR1, VR0, BRW0), 6);  break;
    case op_fsubf:  ACT_INST(h, fsubf(PALWAYS, VR1, VR0, BRW0), 6);  break;
    case op_frsubf: ACT_INST(h, frsubf(PALWAYS, VR1, VR0, BRW0), 6); break;
    case op_fminf:  ACT_INST(h, fminf(PALWAYS, VR1, VR0, BRW0), 6);  break;
    case op_fmaxf:  ACT_INST(h, fmaxf(PALWAYS, VR1, VR0, BRW0), 6);  break;
    case op_frelun: ACT_INST(h, frelun(PALWAYS, VR1, VR0, BRW0), 6); break;
    case op_feq:    ACT_INST(h, feq(PALWAYS, VR1, VR0, BRW0), 6);    break;
    case op_fneq:   ACT_INST(h, fneq(PALWAYS, VR1, VR0, BRW0), 6);   break;
    case op_fgt:    ACT_INST(h, fgt(PALWAYS, VR1, VR0, BRW0), 6);    break;
    case op_fgte:   ACT_INST(h, fgte(PALWAYS, VR1, VR0, BRW0), 6);   break;
    case op_flt:    ACT_INST(h, flt(PALWAYS, VR1, VR0, BRW0), 6);    break;
    case op_flte:   ACT_INST(h, flte(PALWAYS, VR1, VR0, BRW0), 6);   break;
    case op_mpy:    ACT_INST(h, mpy(PALWAYS, VR1, VR0, BRW0), 6); l = 10; break;
    default: assert(0 && "unsupported binary_rw operation");
  }
  if (op == op_feq || op == op_fneq || op == op_flt || op == op_flte || op == op_fgt || op == op_fgte) {
    ACT_INST(h, select(PALWAYS, VR2, SR2), 8);
    ACT_INST(h, fpushout(PALWAYS, VR2), 10);
  } else {
    ACT_INST(h, fpushout(PALWAYS, VR1), l);
  }
  ACT_END(h);
  // end of activation program
}

void init_binary_rh_fp(act_hlapi_t& h, act_bin_op_t op) {  // [NOLINT]
  // one 32b per channel
  h.i.u.op.scl[1] = 1;
  h.i.u.op.scl[2] = 1;

  // start of activation program
  ACT_START(h);
  // outer loop
  // get new set of per channel parameters on first iteration of spatial loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);
  // inner loop
  ACT_INST(h, fpopin0(PALWAYS, VR0), 2);
  int l = 8;
  switch (op) {
    case op_fadd:   ACT_INST(h, fadd(PALWAYS, VR1, VR0, BRH0), 6);   break;
    case op_fsub:   ACT_INST(h, fsub(PALWAYS, VR1, VR0, BRH0), 6);   break;
    case op_frsub:  ACT_INST(h, frsub(PALWAYS, VR1, VR0, BRH0), 6);  break;
    case op_fmin:   ACT_INST(h, fmin(PALWAYS, VR1, VR0, BRH0), 6);   break;
    case op_fmax:   ACT_INST(h, fmax(PALWAYS, VR1, VR0, BRH0), 6);   break;
    case op_faddf:  ACT_INST(h, faddf(PALWAYS, VR1, VR0, BRH0), 6);  break;
    case op_fsubf:  ACT_INST(h, fsubf(PALWAYS, VR1, VR0, BRH0), 6);  break;
    case op_frsubf: ACT_INST(h, frsubf(PALWAYS, VR1, VR0, BRH0), 6); break;
    case op_fminf:  ACT_INST(h, fminf(PALWAYS, VR1, VR0, BRH0), 6);  break;
    case op_fmaxf:  ACT_INST(h, fmaxf(PALWAYS, VR1, VR0, BRH0), 6);  break;
    case op_frelun: ACT_INST(h, frelun(PALWAYS, VR1, VR0, BRH0), 6); break;
    case op_feq:    ACT_INST(h, feq(PALWAYS, VR1, VR0, BRH0), 6);    break;
    case op_fneq:   ACT_INST(h, fneq(PALWAYS, VR1, VR0, BRH0), 6);   break;
    case op_fgt:    ACT_INST(h, fgt(PALWAYS, VR1, VR0, BRH0), 6);    break;
    case op_fgte:   ACT_INST(h, fgte(PALWAYS, VR1, VR0, BRH0), 6);   break;
    case op_flt:    ACT_INST(h, flt(PALWAYS, VR1, VR0, BRH0), 6);    break;
    case op_flte:   ACT_INST(h, flte(PALWAYS, VR1, VR0, BRH0), 6);   break;
    case op_mpyh:   ACT_INST(h, mpyh(PALWAYS, VR1, VR0, BRH0), 6); l = 10; break;
    case op_mpyb:   ACT_INST(h, mpyb(PALWAYS, VR1, VR0, BRH0), 6); l = 10; break;
    default: assert(0 && "unsupported binary_rh operation");
  }
  if (op == op_feq || op == op_fneq || op == op_flt || op == op_flte || op == op_fgt || op == op_fgte) {
    ACT_INST(h, select(PALWAYS, VR2, SR2), 8);
    ACT_INST(h, fpushout(PALWAYS, VR2), 10);
  } else {
    ACT_INST(h, fpushout(PALWAYS, VR1), l);
  }
  ACT_END(h);
  // end of activation program
}

void init_binary_rb_fp(act_hlapi_t& h, act_bin_op_t op, act_alay_t l) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  h.i.u.op.scl[1] = 1;
  h.i.u.op.scl[2] = 1;

  // start of activation program
  ACT_START(h);
  // outer loop
  // get new set of per channel parameters on first iteration of spatial loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);
  // inner loop
  ACT_INST(h, fpopin0(PALWAYS, VR0), 2);
  switch (op) {
    case op_fadd:   ACT_INST(h, fadd(PALWAYS, VR1, VR0, BRB0), 6);   break;
    case op_fsub:   ACT_INST(h, fsub(PALWAYS, VR1, VR0, BRB0), 6);   break;
    case op_frsub:  ACT_INST(h, frsub(PALWAYS, VR1, VR0, BRB0), 6);  break;
    case op_fmin:   ACT_INST(h, fmin(PALWAYS, VR1, VR0, BRB0), 6);   break;
    case op_fmax:   ACT_INST(h, fmax(PALWAYS, VR1, VR0, BRB0), 6);   break;
    case op_faddf:  ACT_INST(h, faddf(PALWAYS, VR1, VR0, BRB0), 6);  break;
    case op_fsubf:  ACT_INST(h, fsubf(PALWAYS, VR1, VR0, BRB0), 6);  break;
    case op_frsubf: ACT_INST(h, frsubf(PALWAYS, VR1, VR0, BRB0), 6); break;
    case op_fminf:  ACT_INST(h, fminf(PALWAYS, VR1, VR0, BRB0), 6);  break;
    case op_fmaxf:  ACT_INST(h, fmaxf(PALWAYS, VR1, VR0, BRB0), 6);  break;
    case op_frelun: ACT_INST(h, frelun(PALWAYS, VR1, VR0, BRB0), 6); break;
    case op_feq:    ACT_INST(h, feq(PALWAYS, VR1, VR0, BRB0), 6);    break;
    case op_fneq:   ACT_INST(h, fneq(PALWAYS, VR1, VR0, BRB0), 6);   break;
    case op_fgt:    ACT_INST(h, fgt(PALWAYS, VR1, VR0, BRB0), 6);    break;
    case op_fgte:   ACT_INST(h, fgte(PALWAYS, VR1, VR0, BRB0), 6);   break;
    case op_flt:    ACT_INST(h, flt(PALWAYS, VR1, VR0, BRB0), 6);    break;
    case op_flte:   ACT_INST(h, flte(PALWAYS, VR1, VR0, BRB0), 6);   break;
    default: assert(0 && "unsupported binary_rb operation");
  }
  if (op == op_feq || op == op_fneq || op == op_flt || op == op_flte || op == op_fgt || op == op_fgte) {
    ACT_INST(h, select(PALWAYS, VR2, SR2), 8);
    ACT_INST(h, fpushout(PALWAYS, VR2), 10);
  } else {
    ACT_INST(h, fpushout(PALWAYS, VR1), 8);
  }
  ACT_END(h);
  // end of activation program
}


//
// Exponent: compute
//
void init_exp(act_hlapi_t& h, bool sum, bool scl) {  // [NOLINT]
  h.i.u.op.scl[1] = 0;
  // start of activation program
  ACT_START(h);

  if (sum) {
    assert(0 && "program/pc size issue");
    // either input SR0 or VR7 have input maximum
    // output SR0 and VR7 have sum of exp(x-max)

    // negate max and broadcast to vector
    if (!scl) {
      // use scalar input
      ACT_INST(h, add(PFIRST0, SR0, VR7), 0);
    }
    // start of inner loop

    // pop input with bias in VR7
    ACT_INST(h, fpopin0(PALWAYS, VR5), 1);
    ACT_INST(h, frsub(PALWAYS, VR5, SR0, VR5), 4);

    // set sum to 0
    ACT_INST(h, add(PFIRST0, VR0, SR1), 6);

    // do lookup
    ACT_INST(h, exp0(PALWAYS,      VR5), 8);
    ACT_INST(h, exp1(PALWAYS, VR6, VR5), 10);
    // interpolation
    ACT_INST(h, mac0(PALWAYS, VR2, VR6), 12);
    ACT_INST(h, mac1(PALWAYS, VR3, VR2), 16);
    // write result and accumulate
    ACT_INST(h, fpushout(PALWAYS, VR3), 20);
    ACT_INST(h, fadd(PALWAYS, VR0, VR0, VR3), 21);

    // end of inner loop
    // final reduction
    ACT_INST(h, trnsp(PLAST2, VR0, VR1), 22);
    ACT_INST(h, add(PLAST2, VR1, VR0, VR1), 24);
    ACT_INST(h, raddv(PLAST2, VR7, VR1), 26);
    ACT_INST(h, raddv(PLAST2, VR7, VR7), 28);
    ACT_INST(h, raddv(PLAST2, VR7, VR7), 30);
    ACT_INST(h, add(PLAST2, SR0, VR7), 32);
  } else {
    // input SR0 or VR7 has input maximum
    // output has stream of exponents as accumulators

    // broadcast scalar to vector
    if (scl) {
      ACT_INST(h, add(PFIRST0, VR7, SR0), 2);
    } else {
      ACT_INST(h, bcc(PFIRST0, VR7, VR7), 0);
      ACT_INST(h, bcv(PFIRST0, VR7, VR7), 2);
    }

    // start of inner loop

    // pop input with bias
    ACT_INST(h, fpopin0(PALWAYS, VR0), 4);
    ACT_INST(h, fadd(PALWAYS, VR1, VR0, VR7), 8);

    // do lookup
    ACT_INST(h, exp0(PALWAYS,      VR1), 10);
    ACT_INST(h, exp1(PALWAYS, VR2, VR1), 12);

    // interpolation, use even/odd to avoid schedule conflicts
    ACT_INST(h, mac0(PODD, VR3, VR2), 14);
    ACT_INST(h, mac0(PEVEN, VR4, VR2), 16);
    ACT_INST(h, mac1(PODD, VR5, VR3), 18);
    ACT_INST(h, mac1(PEVEN, VR6, VR4), 20);
    ACT_INST(h, fpushout(PODD, VR5), 22);
    ACT_INST(h, fpushout(PEVEN, VR6), 24);
  }
  ACT_END(h);
  // end of activation program
}

//
// Look-up table functions
// BRB0: prescale
// BRH1: optional scale
// BRH2: post-scale + asymmetric offset
// BRW2: bias
//
void init_lut(act_hlapi_t& h, act_alay_t l, bool ps, bool fp16scl) {  // [NOLINT]
  // no per channel parameters
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*PLUT_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*PLUT_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // get new set of per channel parameters on first iteration of spatial loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  // inner loop for every input vector
  // pop input
  ACT_INST(h, fpopin0(PALWAYS, VR0, BRW2, BRB0), 2);
  // do lookup
  ACT_INST(h, lutq0(PALWAYS,      VR0), 6);
  ACT_INST(h, lutq1(PALWAYS, VR1, VR0), 8);
  // interpolation
  ACT_INST(h, mac0(PEVEN, VR2, VR1), 10);
  ACT_INST(h, mac1(PEVEN, VR3, VR2), 14);
  ACT_INST(h, mac0(PODD,  VR4, VR1), 12);
  ACT_INST(h, mac1(PODD,  VR5, VR4), 16);
  if (ps) {
    // optional scaling
    if (fp16scl) {
      ACT_INST(h, mpyh(PEVEN, VR6, VR3, BRH1), 18);
      ACT_INST(h, mpyh(PODD,  VR7, VR5, BRH1), 20);
    } else {
      ACT_INST(h, mpyb(PEVEN, VR6, VR3, BRH1), 18);
      ACT_INST(h, mpyb(PODD,  VR7, VR5, BRH1), 20);
    }
    // push to output
    ACT_INST(h, fpushout(PEVEN, VR6, BRH2), 22);
    ACT_INST(h, fpushout(PODD,  VR7, BRH2), 24);
  } else {
    // push to output
    ACT_INST(h, fpushout(PEVEN, VR3, BRH2), 18);
    ACT_INST(h, fpushout(PODD,  VR5, BRH2), 20);
  }

  ACT_END(h);
  // end of activation program
}

//
// Fixed look-up table functions
// BRB0: prescale
// BRH1: optional scale
// BRH2: post-scale + asymmetric offset
// BRW2: bias
//
void init_flut(act_hlapi_t& h, act_una_op_t op, act_alay_t l, bool ps, bool fp16scl) {  // [NOLINT]
  // no per channel parameters
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*FLUT_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*FLUT_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // get new set of per channel parameters on first iteration of spatial loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  // inner loop for every input vector
  // pop input
  ACT_INST(h, fpopin0(PALWAYS, VR0, BRW2, BRB0), 2);
  // do lookup
  switch (op) {
  case op_exp0:
    ACT_INST(h, exp0(PALWAYS,      VR0), 6);
    ACT_INST(h, exp1(PALWAYS, VR1, VR0), 8);
    break;
  case op_recip0:
    ACT_INST(h, recip0(PALWAYS,      VR0), 6);
    ACT_INST(h, recip1(PALWAYS, VR1, VR0), 8);
    break;
  case op_rsqrt0:
    ACT_INST(h, rsqrt0(PALWAYS,      VR0), 6);
    ACT_INST(h, rsqrt1(PALWAYS, VR1, VR0), 8);
    break;
  default:
    assert(0 && "unsupported flut op");
  }
  // interpolation
  ACT_INST(h, mac0(PEVEN, VR2, VR1), 10);
  ACT_INST(h, mac1(PEVEN, VR3, VR2), 14);
  ACT_INST(h, mac0(PODD,  VR4, VR1), 12);
  ACT_INST(h, mac1(PODD,  VR5, VR4), 16);
  if (ps) {
    // optional scaling
    if (fp16scl) {
      ACT_INST(h, mpyh(PEVEN, VR6, VR3, BRH1), 18);
      ACT_INST(h, mpyh(PODD,  VR7, VR5, BRH1), 20);
    } else {
      ACT_INST(h, mpyb(PEVEN, VR6, VR3, BRH1), 18);
      ACT_INST(h, mpyb(PODD,  VR7, VR5, BRH1), 20);
    }
    // push to output
    ACT_INST(h, fpushout(PEVEN, VR6, BRH2), 22);
    ACT_INST(h, fpushout(PODD,  VR7, BRH2), 24);
  } else {
    // push to output
    ACT_INST(h, fpushout(PEVEN, VR3, BRH2), 18);
    ACT_INST(h, fpushout(PODD,  VR5, BRH2), 20);
  }

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-operation and PLUT activation program
// BRB0: prescale0
// BRB1: prescale1
// BRH1: postscale + asymmetric offset
// BRW1: bias
//
void init_eltop_lut(act_hlapi_t& h, act_alay_t l, act_bin_op_t op, bool ea, broadcast_t brdc_f) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*ELTOP_PLUT_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*ELTOP_PLUT_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  if (ea) {
    // first eltwise then activation

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRW1, BRB0), 2);

    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR1, BRB1), 3);

    int l = 6;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    // check broadcasting in w and ch dimensions for input 2
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR1, VR1), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR1, VR1), l);
      l += 2;
    }

    // select an element-wise op
    switch (op) {
      // add/sub/rsub set flags on negative results
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR2, VR0, VR1), l); break;
      // min/max set incorrect flags so do explicit gte
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR2, VR0, VR1), l);  break;
      default: assert(0 && "unsupported eltwise operation");
    }
    l += 2;

    // do lookup
    ACT_INST(h, lutq0(PALWAYS,      VR2), l);
    ACT_INST(h, lutq1(PALWAYS, VR3, VR2), (l + 2));
    // interpolation
    ACT_INST(h, mac0(PALWAYS, VR4, VR3), (l + 4));
    ACT_INST(h, mac1(PALWAYS, VR5, VR4), (l + 8));
    // push to output
    ACT_INST(h, fpushout(PALWAYS, VR5, BRH1), (l + 12));
  } else {
    // first activation then eltwise

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRW1, BRB0), 2);

    int l = 6;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
      l += 2;
    }

    // Do lookup
    ACT_INST(h, lutq0(PALWAYS,      VR0), l);
    ACT_INST(h, lutq1(PALWAYS, VR1, VR0), (l + 2));

    // interpolation
    ACT_INST(h, mac0(PALWAYS, VR2, VR1), (l + 4));
    ACT_INST(h, mac1(PALWAYS, VR3, VR2), (l + 8));
    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR4, BRB1), (l + 10));

    l += 14;
    // check broadcasting in w and ch dimensions for input 2
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR4, VR4), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR4, VR4), l);
      l += 2;
    }

    // select an element-wise op
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR5, VR3, VR4), l);  break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR5, VR3, VR4), l);  break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR5, VR3, VR4), l); break;
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR5, VR3, VR4), l);  break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR5, VR3, VR4), l);  break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // push to output with offfset
    ACT_INST(h, fpushout(PALWAYS,  VR5, BRH1), (l + 2));
  }

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-operation and FLUT activation program
// BRB0: prescale0
// BRB1: prescale1
// BRH1: postscale + asymmetric offset
// BRW1: bias
//
void init_eltop_flut(act_hlapi_t& h, act_una_op_t fop, act_alay_t l, act_bin_op_t op, bool ea, broadcast_t brdc_f) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*ELTOP_FLUT_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*ELTOP_FLUT_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  if (ea) {
    // first eltwise then activation
    int l;
#if ACT_HAS_ALU_1
    if ((brdc_f.in1_c && !brdc_f.in1_w && !brdc_f.in0_w && !brdc_f.in0_c) ||
        (brdc_f.in1_w && !brdc_f.in1_c && !brdc_f.in0_w && !brdc_f.in0_c)) {
      // load input feature-map from in1 stream, no bias
      ACT_INST(h, fpopin1(PALWAYS, VR0, BRB1), 2);
      // load input accumulator from in0 stream
      ACT_INST(h, fpopin0(PALWAYS, VR1, BRW1, BRB0), 6);
      if (brdc_f.in1_c)
        ACT_INST(h, bcc(PALWAYS, VR2, VR0), 7);
      else // brdc_f.in1_w
        ACT_INST(h, bcv(PALWAYS, VR2, VR0), 7);
      // select an element-wise op
      switch (op) {
        // add/sub/rsub set flags on negative results
        case op_add:   ACT_INST(h, fadd(PALWAYS, VR3, VR1, VR2), 10);  break;
        case op_sub:   ACT_INST(h, fsub(PALWAYS, VR3, VR1, VR2), 10);  break;
        case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR3, VR1, VR2), 10); break;
        // min/max set incorrect flags so do explicit gte
        case op_min:   ACT_INST(h, fmin(PALWAYS, VR3, VR1, VR2), 10);  break;
        case op_max:   ACT_INST(h, fmax(PALWAYS, VR3, VR1, VR2), 10);  break;
        default: assert(0 && "unsupported eltwise operation");
      }
      l = 14;
    } else
    if ((brdc_f.in0_c && !brdc_f.in0_w && !brdc_f.in1_w && !brdc_f.in1_c) ||
        (brdc_f.in0_w && !brdc_f.in0_c && !brdc_f.in1_w && !brdc_f.in1_c)) {
      // load input feature-map from in0 stream
      ACT_INST(h, fpopin0(PALWAYS, VR0, BRW1, BRB0), 2);
      // load input accumulator from in1 stream, no bias
      ACT_INST(h, fpopin1(PALWAYS, VR1, BRB1), 6);
      if (brdc_f.in0_c)
        ACT_INST(h, bcc(PALWAYS, VR2, VR0), 7);
      else // brdc_f.in0_w
        ACT_INST(h, bcv(PALWAYS, VR2, VR0), 7);
      // select an element-wise op
      switch (op) {
        // add/sub/rsub set flags on negative results
        case op_add:   ACT_INST(h, fadd(PALWAYS, VR3, VR2, VR1), 10);  break;
        case op_sub:   ACT_INST(h, fsub(PALWAYS, VR3, VR2, VR1), 10);  break;
        case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR3, VR2, VR1), 10); break;
        // min/max set incorrect flags so do explicit gte
        case op_min:   ACT_INST(h, fmin(PALWAYS, VR3, VR2, VR1), 10);  break;
        case op_max:   ACT_INST(h, fmax(PALWAYS, VR3, VR2, VR1), 10);  break;
        default: assert(0 && "unsupported eltwise operation");
      }
      l = 14;
    } else {
#endif
      // load input accumulator from in0 stream
      ACT_INST(h, fpopin0(PALWAYS, VR0, BRW1, BRB0), 2);
      // load input feature-map from in1 stream, no bias
      ACT_INST(h, fpopin1(PALWAYS, VR1, BRB1), 3);
      l = 6;
      // check broadcasting in w and ch dimensions for input 0
      if (brdc_f.in0_w) {
        ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
        l += 2;
      }
      if (brdc_f.in0_c) {
        ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
        l += 2;
      }
      // check broadcasting in w and ch dimensions for input 1
      if (brdc_f.in1_w) {
        ACT_INST(h, bcv(PALWAYS, VR1, VR1), l);
        l += 2;
      }
      if (brdc_f.in1_c) {
        ACT_INST(h, bcc(PALWAYS, VR1, VR1), l);
        l += 2;
      }
      // select an element-wise op
      switch (op) {
        // add/sub/rsub set flags on negative results
        case op_add:   ACT_INST(h, fadd(PALWAYS, VR3, VR0, VR1), l);  break;
        case op_sub:   ACT_INST(h, fsub(PALWAYS, VR3, VR0, VR1), l);  break;
        case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR3, VR0, VR1), l); break;
        // min/max set incorrect flags so do explicit gte
        case op_min:   ACT_INST(h, fmin(PALWAYS, VR3, VR0, VR1), l);  break;
        case op_max:   ACT_INST(h, fmax(PALWAYS, VR3, VR0, VR1), l);  break;
        default: assert(0 && "unsupported eltwise operation");
      }
      l += 2;
#if ACT_HAS_ALU_1
    }
#endif
    // do lookup
    switch (fop) {
    case op_exp0:
      ACT_INST(h, exp0(PALWAYS,      VR3), l);
      ACT_INST(h, exp1(PALWAYS, VR4, VR3), (l + 2));
      break;
    case op_recip0:
      ACT_INST(h, recip0(PALWAYS,      VR3), l);
      ACT_INST(h, recip1(PALWAYS, VR4, VR3), (l + 2));
      break;
    case op_rsqrt0:
      ACT_INST(h, rsqrt0(PALWAYS,      VR3), l);
      ACT_INST(h, rsqrt1(PALWAYS, VR4, VR3), (l + 2));
      break;
    default:
      assert(0 && "unsupported flut op");
    }
    // interpolation
    ACT_INST(h, mac0(PALWAYS, VR5, VR4), (l + 4));
    ACT_INST(h, mac1(PALWAYS, VR6, VR5), (l + 8));
    // push to output
    ACT_INST(h, fpushout(PALWAYS, VR6, BRH1), (l + 12));
  } else {
    // first activation then eltwise

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRW1, BRB0), 2);

    int l = 6;
    // check broadcasting in w and ch dimensions for input 0
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
      l += 2;
    }

    // Do lookup
    switch (fop) {
    case op_exp0:
      ACT_INST(h, exp0(PALWAYS,      VR0), l);
      ACT_INST(h, exp1(PALWAYS, VR1, VR0), (l + 2));
      break;
    case op_recip0:
      ACT_INST(h, recip0(PALWAYS,      VR0), l);
      ACT_INST(h, recip1(PALWAYS, VR1, VR0), (l + 2));
      break;
    case op_rsqrt0:
      ACT_INST(h, rsqrt0(PALWAYS,      VR0), l);
      ACT_INST(h, rsqrt1(PALWAYS, VR1, VR0), (l + 2));
      break;
    default:
      assert(0 && "unsupported flut op");
    }

    // interpolation
    ACT_INST(h, mac0(PALWAYS, VR2, VR1), (l + 4));
    ACT_INST(h, mac1(PALWAYS, VR3, VR2), (l + 8));
    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR4, BRB1), (l + 10));

    l += 14;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR4, VR4), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR4, VR4), l);
      l += 2;
    }

    // select an element-wise op
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR5, VR3, VR4), l);  break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR5, VR3, VR4), l);  break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR5, VR3, VR4), l); break;
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR5, VR3, VR4), l);  break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR5, VR3, VR4), l);  break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // push to output with offfset
    ACT_INST(h, fpushout(PALWAYS,  VR5, BRH1), (l + 2));
  }

  ACT_END(h);
  // end of activation program
}

//
// ReLU activation program
// BRB0: prescale
// BRH1: scale
// BRH2: postscale + asymmetric offset
// BRW2: bias
//
void init_relu(act_hlapi_t& h, act_alay_t l, bool fp16scl) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*RELU_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*RELU_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  // inner loop, toggle even/odd to avoid hazard
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PALWAYS, VR0, BRW2, BRB0), 2);

  // compare with zero
  ACT_INST(h, frelu(PALWAYS, VR1, VR0), 6);

  // multiply from scale on mul0
  if (fp16scl) {
    ACT_INST(h, mpyh(PEVEN, VR2, VR1, BRH1), 8);
    ACT_INST(h, mpyh(PODD,  VR3, VR1, BRH1), 9);
  } else {
    ACT_INST(h, mpyb(PEVEN, VR2, VR1, BRH1), 8);
    ACT_INST(h, mpyb(PODD,  VR3, VR1, BRH1), 9);
  }

  // push VR2 to output
  ACT_INST(h, fpushout(PEVEN, VR2, BRH2), 12);
  ACT_INST(h, fpushout(PODD,  VR3, BRH2), 13);

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-operation and ReLU activation program
// BRB0: prescale for convolution result
// BRB1: prescale for eltwise add input
// BRH1: scale and shift(positive only)
// BRH2: postscale + asymmetric offset
// BRW2: bias
//
void init_eltop_relu(act_hlapi_t& h, act_alay_t l, act_bin_op_t op, bool ea, bool fp16scl) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*ELTOP_RELU_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*ELTOP_RELU_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  if (ea) {
    // first eltwise then activation

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRW2, BRB0), 2);

    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR1, BRB1), 3);

    // select an element-wise op
    switch (op) {
      // add/sub/rsub set flags on negative results
      case op_add:   ACT_INST(h, faddf(PALWAYS, VR2, VR0, VR1), 6);  break;
      case op_sub:   ACT_INST(h, fsubf(PALWAYS, VR2, VR0, VR1), 6);  break;
      case op_rsub:  ACT_INST(h, frsubf(PALWAYS, VR2, VR0, VR1), 6); break;
      // min/max set incorrect flags so do explicit gte
      case op_min:   ACT_INST(h, fminf(PALWAYS, VR2, VR0, VR1), 6);  break;
      case op_max:   ACT_INST(h, fmaxf(PALWAYS, VR2, VR0, VR1), 6);  break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // compare with zero
    ACT_INST(h, frelu(PALWAYS, VR3, VR2), 8);
    // multiply from scale on mul0
    if (fp16scl) {
      ACT_INST(h, mpyh(PEVEN, VR4, VR3, BRH1), 10);
      ACT_INST(h, mpyh(PODD,  VR5, VR3, BRH1), 11);
    } else {
      ACT_INST(h, mpyb(PEVEN, VR4, VR3, BRH1), 10);
      ACT_INST(h, mpyb(PODD,  VR5, VR3, BRH1), 11);
    }

    // push VR4/VR5 to output
    ACT_INST(h, fpushout(PEVEN, VR4, BRH2), 14);
    ACT_INST(h, fpushout(PODD,  VR5, BRH2), 15);

  } else {
    // first activation then eltwise

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRW2, BRB0), 2);
    // compare with zero
    ACT_INST(h, frelu(PALWAYS, VR1, VR0), 6);
    // multiply from scale on mul0
    if (fp16scl) {
      ACT_INST(h, mpyh(PEVEN, VR2, VR1, BRH1), 8);
      ACT_INST(h, mpyh(PODD, VR3, VR1, BRH1), 9);
    } else {
      ACT_INST(h, mpyb(PEVEN, VR2, VR1, BRH1), 8);
      ACT_INST(h, mpyb(PODD, VR3, VR1, BRH1), 9);
    }
    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR5, BRB1), 10);
    // select an element-wise op
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PEVEN, VR6, VR2, VR5), 14);
                     ACT_INST(h, fadd(PODD, VR6, VR3, VR5), 15);  break;
      case op_sub:   ACT_INST(h, fsub(PEVEN, VR6, VR2, VR5), 14);
                     ACT_INST(h, fsub(PODD, VR6, VR3, VR5), 15);  break;
      case op_rsub:  ACT_INST(h, frsub(PEVEN, VR6, VR2, VR5), 14);
                     ACT_INST(h, frsub(PODD, VR6, VR3, VR5), 15); break;
      case op_min:   ACT_INST(h, fmin(PEVEN, VR6, VR2, VR5), 14);
                     ACT_INST(h, fmin(PODD, VR6, VR3, VR5), 15);  break;
      case op_max:   ACT_INST(h, fmax(PEVEN, VR6, VR2, VR5), 14);
                     ACT_INST(h, fmax(PODD, VR6, VR3, VR5), 15);  break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // push to output with offfset
    ACT_INST(h, fpushout(PALWAYS, VR6, BRH2), 16);
  }

  ACT_END(h);
  // end of activation program
}

//
// PReLU activation program
// BRB0: prescale
// BRH1: post-scale + asymmetric offset
// BRW1: positive/negative scale
// BRW2: bias
//
void init_prelu(act_hlapi_t& h, act_alay_t l, bool fp16scl) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*PRELU_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*PRELU_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  // inner loop, toggle even/odd to avoid hazard
  // load input accumulator from in0 stream
  // set flag if result is not negative after adding bias
  ACT_INST(h, fpopinf0(PEVEN, VR0, BRW2, BRB0), 2);
  ACT_INST(h, fpopinf0(PODD,  VR1, BRW2, BRB0), 3);

  // select a scale based on ALU state
  if (fp16scl) {
    ACT_INST(h, selecth(PALWAYS, VR2, BRW1), 6);
  } else {
    ACT_INST(h, selectb(PALWAYS, VR2, BRW1), 6);
  }

  // multiply from scale on mul0
  ACT_INST(h, mpy(PEVEN, VR3, VR0, VR2), 8);
  ACT_INST(h, mpy(PODD,  VR4, VR1, VR2), 9);

  // push VR2 to output
  ACT_INST(h, fpushout(PEVEN, VR3, BRH1), 12);
  ACT_INST(h, fpushout(PODD,  VR4, BRH1), 13);

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-operation and PReLU activation program
// BRB0: prescale for convolution result
// BRB1: prescale for eltwise add input
// BRH1: postscale + asymmetric offset
// BRW1: positive/negative scale
// BRW2: bias for in1
// BRW3: bias for in2
// BRW4: post scale and shift
void init_eltop_prelu(act_hlapi_t& h, act_alay_t l, act_bin_op_t op, bool ea, bool fp16scl, broadcast_t brdc_f) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*ELTOP_PRELU_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*ELTOP_PRELU_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  if (ea) {
    // first eltwise then activation

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRW2, BRB0), 2);

    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR1, BRW3, BRB1), 3);

    int l = 6;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    // check broadcasting in w and ch dimensions for input 2
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR1, VR1), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR1, VR1), l);
      l += 2;
    }

    l += 2;
    // select an element-wise op
    switch (op) {
      // add/sub/rsub set flags on negative results
      case op_add:   ACT_INST(h, faddf(PEVEN, VR2, VR0, VR1), (l-2));
                     ACT_INST(h, faddf(PODD,  VR6, VR0, VR1), (l-1)); break;
      case op_sub:   ACT_INST(h, fsubf(PEVEN, VR2, VR0, VR1), (l-2));
                     ACT_INST(h, fsubf(PODD,  VR6, VR0, VR1), (l-1)); break;
      case op_rsub:  ACT_INST(h, frsubf(PEVEN, VR2, VR0, VR1), (l-2));
                     ACT_INST(h, frsubf(PODD,  VR6, VR0, VR1), (l-1)); break;
      // min/max set incorrect flags so do explicit gte
      case op_min:   ACT_INST(h, fminf(PEVEN, VR2, VR0, VR1), (l-2));
                     ACT_INST(h, fminf(PODD,  VR6, VR0, VR1), (l-1));
                     ACT_INST(h, fgte(PEVEN, VR2, VR2), l);
                     ACT_INST(h, fgte(PODD,  VR6, VR6), (l+1)); l += 2; break;
      case op_max:   ACT_INST(h, fmaxf(PEVEN, VR2, VR0, VR1), (l-2));
                     ACT_INST(h, fmaxf(PODD,  VR6, VR0, VR1), (l-1));
                     ACT_INST(h, fgte(PEVEN, VR2, VR2), l);
                     ACT_INST(h, fgte(PODD,  VR6, VR6), (l+1)); l += 2; break;
      default: assert(0 && "unsupported eltwise operation");
    }
    

    // select a scale and shift based on ALU state
    if (fp16scl) {
      ACT_INST(h, selecth(PALWAYS, VR3, BRW1), (l+0));
    } else {
      ACT_INST(h, selectb(PALWAYS, VR3, BRW1), (l+0));
    }

    // multiply from scale on mul0
    ACT_INST(h, mpy(PEVEN, VR4, VR2, VR3), (l+2));
    ACT_INST(h, mpy(PODD,  VR4, VR6, VR3), (l+3));

    // push to output with offfset
    ACT_INST(h, fpushout(PALWAYS, VR4, BRH1), (l+6));
  } else {
    // first activation then eltwise

    // load input accumulator from in0 stream
    ACT_INST(h, fpopinf0(PEVEN, VR0, BRW2, BRB0), 2);
    ACT_INST(h, fpopinf0(PODD, VR1, BRW2, BRB0), 3);

    int l = 6;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PEVEN, VR0, VR0), l);
      ACT_INST(h, bcv(PODD, VR1, VR1), (l + 1));
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PEVEN, VR0, VR0), l);
      ACT_INST(h, bcc(PODD, VR1, VR1), (l + 1));
      l += 2;
    }

    // select a scale and shift based on ALU state
    if (fp16scl) {
      ACT_INST(h, selecth(PALWAYS, VR2, BRW1), l);
    } else {
      ACT_INST(h, selectb(PALWAYS, VR2, BRW1), l);
    }

    // multiply from scale on mul0
    ACT_INST(h, mpy(PEVEN, VR3, VR0, VR2), (l + 2));
    ACT_INST(h, mpy(PODD, VR4, VR1, VR2), (l + 3));

    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR5, BRB1), (l + 4));

    l += 8;
    // check broadcasting in w and ch dimensions for input 2
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR5, VR5), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR5, VR5), l);
      l += 2;
    }

    // select an element-wise op
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fadd(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_sub:   ACT_INST(h, fsub(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fsub(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_rsub:  ACT_INST(h, frsub(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, frsub(PODD, VR6, VR4, VR5), (l + 1)); break;
      case op_min:   ACT_INST(h, fmin(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fmin(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_max:   ACT_INST(h, fmax(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fmax(PODD, VR6, VR4, VR5), (l + 1));  break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // push to output with offset
    ACT_INST(h, fpushout(PALWAYS, VR6, BRH1), (l + 2));
  }

  ACT_END(h);
  // end of activation program
}

//
// Rescale activation program
// BRB0: prescale
// BRH1: scale
// BRH4: postscale + asymmetric offset
// BRW2: bias
//
void init_rescale(act_hlapi_t& h, act_alay_t l, bool fp16scl) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*RESCALE_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*RESCALE_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  // inner loop, toggle even/odd to avoid hazard
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PEVEN, VR0, BRW2, BRB0), 2);
  ACT_INST(h, fpopin0(PODD,  VR1, BRW2, BRB0), 3);

  // multiply from scale on mul0
  if (fp16scl) {
    ACT_INST(h, mpyh(PEVEN, VR3, VR0, BRH1), 6);
    ACT_INST(h, mpyh(PODD,  VR3, VR1, BRH1), 7);
  } else {
    ACT_INST(h, mpyb(PEVEN, VR3, VR0, BRH1), 6);
    ACT_INST(h, mpyb(PODD,  VR3, VR1, BRH1), 7);
  }

  // push VR2 to output
  ACT_INST(h, fpushout(PALWAYS, VR3, BRH2), 10);

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-operation and RESCALE activation program
// BRB0: prescale0
// BRB1: prescale1
// BRH1: scale
// BRH2: postscale + asymmetric offset
// BRW2: bias
//
void init_eltop_rescale(act_hlapi_t& h, act_alay_t l, act_bin_op_t op, bool ea, bool fp16scl, broadcast_t brdc_f) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*ELTOP_RESCALE_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*ELTOP_RESCALE_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);
  if (ea) {
    // first eltwise then activation

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRW2, BRB0), 2);
    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR1, BRB1), 3);

    int l = 6;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    // check broadcasting in w and ch dimensions for input 2
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR1, VR1), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR1, VR1), l);
      l += 2;
    }

    // select an element-wise op
    switch (op) {
      // add/sub/rsub set flags on negative results
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR2, VR0, VR1), l); break;
      // min/max set incorrect flags so do explicit gte
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR2, VR0, VR1), l);  break;
      default: assert(0 && "unsupported eltwise operation");
    }
    l += 2;

    // multiply from scale on mul0
    if (fp16scl) {
      ACT_INST(h, mpyh(PEVEN, VR3, VR2, BRH1), l);
      ACT_INST(h, mpyh(PODD,  VR3, VR2, BRH1), (l + 1));
    } else {
      ACT_INST(h, mpyb(PEVEN, VR3, VR2, BRH1), l);
      ACT_INST(h, mpyb(PODD,  VR3, VR2, BRH1), (l + 1));
    }

    // push VR2 to output
    ACT_INST(h, fpushout(PALWAYS, VR3, BRH2), (l + 4));

  } else {
    // first activation then eltwise

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PEVEN, VR0, BRW2, BRB0), 2);
    ACT_INST(h, fpopin0(PODD,  VR1, BRW2, BRB0), 3);

    int l = 6;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PEVEN, VR0, VR0), l);
      ACT_INST(h, bcv(PODD, VR1, VR1), (l + 1));
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PEVEN, VR0, VR0), l);
      ACT_INST(h, bcc(PODD, VR1, VR1), (l + 1));
      l += 2;
    }

    // multiply from scale on mul0
    if (fp16scl) {
      ACT_INST(h, mpyh(PEVEN, VR3, VR0, BRH1), l);
      ACT_INST(h, mpyh(PODD,  VR4, VR1, BRH1), (l + 1));
    } else {
      ACT_INST(h, mpyb(PEVEN, VR3, VR0, BRH1), l);
      ACT_INST(h, mpyb(PODD,  VR4, VR1, BRH1), (l + 1));
    }

    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR5, BRB1), (l + 2));

    l += 6;
    // check broadcasting in w and ch dimensions for input 2
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR5, VR5), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR5, VR5), l);
      l += 2;
    }

    // select an element-wise op
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fadd(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_sub:   ACT_INST(h, fsub(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fsub(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_rsub:  ACT_INST(h, frsub(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, frsub(PODD, VR6, VR4, VR5), (l + 1)); break;
      case op_min:   ACT_INST(h, fmin(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fmin(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_max:   ACT_INST(h, fmax(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fmax(PODD, VR6, VR4, VR5), (l + 1));  break;
      default: assert(0 && "unsupported eltwise operation");
    }
    // push VR6 to output with offset
    ACT_INST(h, fpushout(PALWAYS, VR6, BRH2), (l + 2));
  }

  ACT_END(h);
  // end of activation program
}

//
// ReLU6 activation program
// BRB0: prescale
// BRH1: scale
// BRH2: postscale + asymmetric offset
// BRW2: clipmax
// BRW3: bias
//
void init_relu6(act_hlapi_t& h, act_alay_t l, bool fp16scl) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*RELU6_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*RELU6_PAR_PER_CHAN;
      break;
  }

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  // inner loop, toggle even/odd to avoid hazard
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PALWAYS, VR0, BRW3, BRB0), 2);

  // multiply from scale on mul0
  if (fp16scl) {
    ACT_INST(h, mpyh(PEVEN, VR1, VR0, BRH1), 6);
    ACT_INST(h, mpyh(PODD,  VR2, VR0, BRH1), 7);
  } else {
    ACT_INST(h, mpyb(PEVEN, VR1, VR0, BRH1), 6);
    ACT_INST(h, mpyb(PODD,  VR2, VR0, BRH1), 7);
  }

  // TODO:- replace the max/min once frelu issue is resolved
  // ACT_INST(h, frelun(PALWAYS, VR2, VR0, BRW2), 6);

  // compare with zero and clipmax
  ACT_INST(h, frelun(PEVEN, VR3, VR1, BRW2), 10);
  ACT_INST(h, frelun(PODD, VR4, VR2, BRW2), 11);

  // push VR2 to output
  ACT_INST(h, fpushout(PEVEN, VR3, BRH2), 12);
  ACT_INST(h, fpushout(PODD,  VR4, BRH2), 13);

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-operation and ReLU6 activation program
// BRB0: prescale0
// BRB1: prescale1
// BRH1: posscale
// BRH2: postscale + asymmetric offset
// BRW2: clipmax
// BRW3: bias for in1
// BRW4: bias for in2
// BRW5: post scale and shift
void init_eltop_relu6(act_hlapi_t& h, act_alay_t l, act_bin_op_t op, bool ea, bool fp16scl, broadcast_t brdc_f) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*ELTOP_RELU6_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*ELTOP_RELU6_PAR_PER_CHAN;
      break;
  }
  // h.i.u.op.scl[2] = 0;

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);
  if (ea) {
    // first eltwise then activation

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRW3, BRB0), 2);
    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR1, BRW4, BRB1), 3);

    int l = 6;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    // check broadcasting in w and ch dimensions for input 2
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR1, VR1), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR1, VR1), l);
      l += 2;
    }

    // select an element-wise op
    switch (op) {
      // add/sub/rsub set flags on negative results
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR2, VR0, VR1), l); break;
      // min/max set incorrect flags so do explicit gte
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR2, VR0, VR1), l);  break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // multiply from scale on mul0
    if (fp16scl) {
      ACT_INST(h, mpyh(PEVEN, VR3, VR2, BRH1), (l + 2));
      ACT_INST(h, mpyh(PODD,  VR4, VR2, BRH1), (l + 3));
    } else {
      ACT_INST(h, mpyb(PEVEN, VR3, VR2, BRH1), (l + 2));
      ACT_INST(h, mpyb(PODD,  VR4, VR2, BRH1), (l + 3));
    }

    // compare with zero and clipmax
    ACT_INST(h, fmax(PEVEN, VR5, VR3), (l + 7));
    ACT_INST(h, fmax(PODD, VR6, VR4), (l + 8));


    // TODO:- replace the fmax/fmin once frelu issue is resolved
    // compare with zero and clipmax
    ACT_INST(h, fmin(PEVEN, VR1, VR5, BRW2), (l + 9));
    ACT_INST(h, fmin(PODD, VR2, VR6, BRW2), (l + 10));

    // push to output with offfset
    ACT_INST(h, fpushout(PEVEN, VR1, BRH2), (l + 11));
    ACT_INST(h, fpushout(PODD,  VR2, BRH2), (l + 12));

  } else {
    // first activation then eltwise

    // load input accumulator from in0 stream
    ACT_INST(h, fpopinf0(PALWAYS, VR0, BRW2, BRB0), 2);

    int l = 6;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
      l += 2;
    }

    // compare with zero and clipmax
    ACT_INST(h, frelun(PALWAYS, VR2, VR0, BRW1), l);
    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR5, BRB1), (l + 1));

    // multiply from scale on mul0
    if (fp16scl) {
      ACT_INST(h, mpyh(PEVEN, VR3, VR2, BRH1), (l + 2));
      ACT_INST(h, mpyh(PODD,  VR4, VR2, BRH1), (l + 3));
    } else {
      ACT_INST(h, mpyb(PEVEN, VR3, VR2, BRH1), (l + 2));
      ACT_INST(h, mpyb(PODD,  VR4, VR2, BRH1), (l + 3));
    }

    l += 6;
    // check broadcasting in w and ch dimensions for input 2
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR5, VR5), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR5, VR5), l);
      l += 2;
    }

    // select an element-wise op
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fadd(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_sub:   ACT_INST(h, fsub(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fsub(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_rsub:  ACT_INST(h, frsub(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, frsub(PODD, VR6, VR4, VR5), (l + 1)); break;
      case op_min:   ACT_INST(h, fmin(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fmin(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_max:   ACT_INST(h, fmax(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fmax(PODD, VR6, VR4, VR5), (l + 1));  break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // push to output with offfset
    ACT_INST(h, fpushout(PALWAYS, VR6, BRH6), (l + 2));
  }

  ACT_END(h);
  // end of activation program
}



//
// ReLU1 activation program
// BRB0: prescale
// BRH1: scale
// BRH2: postscale + asymmetric offset
// BRW2: clipmax
// BRW3: bias
//
void init_relu1(act_hlapi_t& h, act_alay_t l, bool fp16scl) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*RELU1_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*RELU1_PAR_PER_CHAN;
      break;
  }
  h.i.u.op.scl[2] = 0;

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);
  ACT_INST(h, fsub(PFIRST1, VR5, /*0,*/ BRW2), 2);  // negate BRW2

  // inner loop, toggle even/odd to avoid hazard
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PALWAYS, VR0, BRW3, BRB0), 4);

  // multiply from scale on mul0
  if (fp16scl) {
    ACT_INST(h, mpyh(PEVEN, VR1, VR0, BRH1), 8);
    ACT_INST(h, mpyh(PODD,  VR2, VR0, BRH1), 9);
  } else {
    ACT_INST(h, mpyb(PEVEN, VR1, VR0, BRH1), 8);
    ACT_INST(h, mpyb(PODD,  VR2, VR0, BRH1), 9);
  }

  // compare with -clipmax and clipmax
  ACT_INST(h, fmax(PEVEN, VR3, VR1, VR5), 12);
  ACT_INST(h, fmax(PODD, VR6, VR2, VR5), 13);

  ACT_INST(h, fmin(PEVEN, VR4, VR3, BRW2), 14);
  ACT_INST(h, fmin(PODD, VR7, VR6, BRW2), 15);
  
  // push VR6 to output
  ACT_INST(h, fpushout(PEVEN, VR4, BRH2), 16);
  ACT_INST(h, fpushout(PODD,  VR7, BRH2), 17);

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-operation and ReLU1 activation program
// BRB0: prescale0
// BRB1: prescale1
// BRH1: posscale
// BRH2: postscale + asymmetric offset
// BRW2: clipmax
// BRW3: bias
//
void init_eltop_relu1(act_hlapi_t& h, act_alay_t l, act_bin_op_t op, bool ea, bool fp16scl, broadcast_t brdc_f) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*ELTOP_RELU1_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*ELTOP_RELU1_PAR_PER_CHAN;
      break;
  }
  h.i.u.op.scl[2] = 0;

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);
  ACT_INST(h, fsub(PFIRST1, VR7, BRW2), 2);  // negate BRH2
  if (ea) {
    // first eltwise then activation

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRW3, BRB0), 4);
    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR1, BRW4, BRB1), 5);

    int l = 8;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    // check broadcasting in w and ch dimensions for input 2
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR1, VR1), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR1, VR1), l);
      l += 2;
    }

    // select an element-wise op
    switch (op) {
      // add/sub/rsub set flags on negative results
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR2, VR0, VR1), l); break;
      // min/max set incorrect flags so do explicit gte
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR2, VR0, VR1), l);  break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR2, VR0, VR1), l);  break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // compare with -clipmax and clipmax
    ACT_INST(h, fmax(PALWAYS, VR3, VR2, VR7), (l + 2));
    ACT_INST(h, fmin(PALWAYS, VR4, VR3, BRW2), (l + 4));

    // multiply from scale on mul0
    if (fp16scl) {
      ACT_INST(h, mpyh(PEVEN, VR5, VR4, BRH1), (l + 6));
      ACT_INST(h, mpyh(PODD,  VR6, VR4, BRH1), (l + 7));
    } else {
      ACT_INST(h, mpyb(PEVEN, VR5, VR4, BRH1), (l + 6));
      ACT_INST(h, mpyb(PODD,  VR6, VR4, BRH1), (l + 7));
    }

    // push to output with offfset
    ACT_INST(h, fpushout(PEVEN, VR5, BRH2), (l + 10));
    ACT_INST(h, fpushout(PODD,  VR6, BRH2), (l + 11));

  } else {
    // first activation then eltwise

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRW3, BRB0), 4);

    int l = 8;
    // check broadcasting in w and ch dimensions for input 1
    if (brdc_f.in0_w) {
      ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
      l += 2;
    }
    if (brdc_f.in0_c) {
      ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
      l += 2;
    }

    // compare with -clipmax and clipmax
    ACT_INST(h, fmax(PALWAYS, VR1, VR0, VR7), l);
    ACT_INST(h, fmin(PALWAYS, VR2, VR1, BRW2), (l + 2));

    // multiply from scale on mul0
    if (fp16scl) {
      ACT_INST(h, mpyh(PEVEN, VR3, VR2, BRH1), (l + 4));
      ACT_INST(h, mpyh(PODD,  VR4, VR2, BRH1), (l + 5));
    } else {
      ACT_INST(h, mpyb(PEVEN, VR3, VR2, BRH1), (l + 4));
      ACT_INST(h, mpyb(PODD,  VR4, VR2, BRH1), (l + 5));
    }

    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR5, BRB1), (l + 6));

    l += 10;
    // check broadcasting in w and ch dimensions for input 2
    if (brdc_f.in1_w) {
      ACT_INST(h, bcv(PALWAYS, VR5, VR5), l);
      l += 2;
    }
    if (brdc_f.in1_c) {
      ACT_INST(h, bcc(PALWAYS, VR5, VR5), l);
      l += 2;
    }

    // select an element-wise op
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fadd(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_sub:   ACT_INST(h, fsub(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fsub(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_rsub:  ACT_INST(h, frsub(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, frsub(PODD, VR6, VR4, VR5), (l + 1)); break;
      case op_min:   ACT_INST(h, fmin(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fmin(PODD, VR6, VR4, VR5), (l + 1));  break;
      case op_max:   ACT_INST(h, fmax(PEVEN, VR6, VR3, VR5), l);
                     ACT_INST(h, fmax(PODD, VR6, VR4, VR5), (l + 1));  break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // push to output with offfset
    ACT_INST(h, fpushout(PALWAYS, VR6, BRH2), (l + 2));
  }

  ACT_END(h);
  // end of activation program
}

// Clip activation program
// BRB0: prescale
// BRW1: clipmax
// BRW2: clipmin
//
void init_clip(act_hlapi_t& h, act_alay_t l) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*CLIP_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*CLIP_PAR_PER_CHAN;
      break;
  }
  h.i.u.op.scl[2] = 0;

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  // inner loop, toggle even/odd to avoid hazard
  // load input accumulator from in0 stream
  ACT_INST(h, fpopinf0(PALWAYS, VR0, BRB0), 2);

  // clipping using BRW1, BRW2
  ACT_INST(h, fmin(PALWAYS, VR1, VR0, BRW1), 6);
  ACT_INST(h, fmax(PALWAYS, VR2, VR1, BRW2), 8);

  // push VR6 to output
  ACT_INST(h, fpushout(PALWAYS, VR2), 10);

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-operation and clip activation program
// BRB0: prescale0
// BRB1: prescale1
// BRW1: clipmax
// BRW2: clipmin
//
void init_eltop_clip(act_hlapi_t& h, act_alay_t l, act_bin_op_t op, bool ea) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*ELTOP_CLIP_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*ELTOP_CLIP_PAR_PER_CHAN;
      break;
  }
  h.i.u.op.scl[2] = 0;
  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  if (ea) {
    // first eltwise then activation

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR0, BRB0), 2);
    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR1, BRB1), 3);
    // select an element-wise op
    switch (op) {
      // add/sub/rsub set flags on negative results
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR2, VR0, VR1), 6);  break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR2, VR0, VR1), 6);  break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR2, VR0, VR1), 6); break;
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR2, VR0, VR1), 6);  break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR2, VR0, VR1), 6);  break;
      default: assert(0 && "unsupported eltwise operation");
    }
    // clipping using BRW1, BRW2
    ACT_INST(h, fmin(PALWAYS, VR4, VR2, BRW1), 8);
    ACT_INST(h, fmax(PALWAYS, VR5, VR4, BRW2), 10);
    // push VR5 to output
    ACT_INST(h, fpushout(PALWAYS, VR5), 12);
  } else {
    // first activation then eltwise

    // load input accumulator from in0 stream
    ACT_INST(h, fpopin0(PALWAYS, VR3, BRB0), 2);
    // clipping using BRW1, BRW2
    ACT_INST(h, fmin(PALWAYS, VR4, VR3, BRW1), 6);
    ACT_INST(h, fmax(PALWAYS, VR5, VR4, BRW2), 8);
    // load input feature-map from in1 stream, no bias
    ACT_INST(h, fpopin1(PALWAYS, VR6, BRB1), 9);
    // select an element-wise op
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR7, VR5, VR6), 12);   break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR7, VR5, VR6), 12);   break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR7, VR5, VR6), 12);  break;
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR7, VR5, VR6), 12);   break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR7, VR5, VR6), 12);   break;
      default: assert(0 && "unsupported eltwise operation");
    }
    // push to output with offfset
    ACT_INST(h, fpushout(PALWAYS, VR7), 14);
  }

  ACT_END(h);
  // end of activation program
}

//
// PReLU activation program following fully-connected convolution
// BRW0: positive/negative scale
// BRW1: bias
// BRH4: postscale + asymmetric offset
//
void init_fc_prelu(act_hlapi_t& h, bool fp16scl) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  h.i.u.op.scl[1] = 1*FC_PRELU_PAR_PER_CHAN;

  // start of activation program
  ACT_START(h);

  // outer loop
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PFIRST2, VR0), 0);

  // inner loop: fixed 8 iterations for 8*v1 processing
  // get new set of per channel parameters
  ACT_INST(h, poppars(PALWAYS, SR1), 1);

  // shift over spatial dimension
  ACT_INST(h, shv(PNFIRST2, VR0, VR0), 4);

  // adding bias, set flag on positive results
  ACT_INST(h, faddf(PALWAYS, VR2, VR0, BRW1), 6);

  // select a scale and shift based on ALU state
  if (fp16scl) {
    ACT_INST(h, selecth(PALWAYS, VR3, BRW0), 8);
  } else {
    ACT_INST(h, selectb(PALWAYS, VR3, BRW0), 8);
  }

  // multiply from scale on mul0
  ACT_INST(h, mpy(PALWAYS, VR4, VR2, VR3), 10);

  // push VR4 to output
  ACT_INST(h, fpushout(PALWAYS, VR4, BRH4), 14);

  ACT_END(h);
  // end of activation program
}

//
// PLUT activation program following fully-connected convolution
// BRH0: optional post scale
// BRH1: postscale + asymmetric offset
// BRW1: bias
//
void init_fc_lut(act_hlapi_t& h, bool ps, bool fp16scl) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  h.i.u.op.scl[1] = 1*FC_PLUT_PAR_PER_CHAN;

  // start of activation program
  ACT_START(h);

  // outer loop
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PFIRST2, VR0), 0);

  // inner loop: fixed 8 iterations for 8*v1 processing
  // get new set of per channel parameters
  ACT_INST(h, poppars(PALWAYS, SR1), 1);

  // shift over spatial dimension
  ACT_INST(h, shv(PNFIRST2, VR0, VR0), 4);

  // adding bias
  ACT_INST(h, fadd(PALWAYS, VR1, VR0, BRW1), 6);

  // do lookup
  ACT_INST(h, lutq0(PALWAYS,      VR1), 8);
  ACT_INST(h, lutq1(PALWAYS, VR2, VR1), 10);

  // interpolation
  ACT_INST(h, mac0(PALWAYS, VR3, VR2), 12);
  ACT_INST(h, mac1(PALWAYS, VR4, VR3), 16);
  if (ps) {
    // optional post-scaling
    if (fp16scl) {
      ACT_INST(h, mpyh(PALWAYS, VR5, VR4, BRH0), 20);
    } else {
      ACT_INST(h, mpyb(PALWAYS, VR5, VR4, BRH0), 20);
    }
    // push to output
    ACT_INST(h, fpushout(PALWAYS, VR5, BRH1), 24);
  } else {
    // push to output
    ACT_INST(h, fpushout(PALWAYS, VR4, BRH1), 20);
  }

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-operation and PReLU activation program following fully-connected convolution
// BRH0: empty
// BRH1: postscale + asymmetric offset
// BRW1: scale
// BRW2: bias
//
void init_eltop_fc_prelu(act_hlapi_t& h, act_bin_op_t op, bool ea, bool fp16scl) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  h.i.u.op.scl[1] = 1*ELTOP_FC_PRELU_PAR_PER_CHAN;

  // start of activation program
  ACT_START(h);

  // outer loop
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PFIRST2, VR0), 0);

  // inner loop: fixed 8 iterations for 8*v1 processing
  // get new set of per channel parameters
  ACT_INST(h, poppars(PALWAYS, SR1), 1);

  // shift over spatial dimension
  ACT_INST(h, shv(PNFIRST2, VR0, VR0), 4);

  if (ea) {
    // adding bias
    ACT_INST(h, fadd(PALWAYS, VR2, VR0, BRW2), 6);

    // get input 1
    ACT_INST(h, fpopin1(PFIRST2, VR1), 8);

    // Shift over spatial dimension
    ACT_INST(h, shv(PNFIRST2, VR1, VR1), 10);

    // element-wise op with input 0, set flags
    int l = 14;
    switch (op) {
      // add/sub/rsub set flags on negative results
      case op_add:   ACT_INST(h, faddf(PALWAYS, VR3, VR2, VR1), 12); break;
      case op_sub:   ACT_INST(h, fsubf(PALWAYS, VR3, VR2, VR1), 12); break;
      case op_rsub:  ACT_INST(h, frsubf(PALWAYS, VR3, VR2, VR1), 12); break;
      // min/max set incorrect flags so do explicit gte
      case op_min:   ACT_INST(h, fminf(PALWAYS, VR3, VR2, VR1), 12);
                     ACT_INST(h, fgte(PALWAYS, VR3, VR3), 14); l = 16; break;
      case op_max:   ACT_INST(h, fmaxf(PALWAYS, VR3, VR2, VR1), 12);
                     ACT_INST(h, fgte(PALWAYS, VR3, VR3), 14); l = 16; break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // select a scale and shift based on ALU state

    if (fp16scl) {
      ACT_INST(h, selecth(PALWAYS, VR4, BRW1), (l+0));
    } else {
      ACT_INST(h, selectb(PALWAYS, VR4, BRW1), (l+0));
    }

    // multiply from scale on mul0
    ACT_INST(h, mpy(PALWAYS, VR5, VR3, VR4), l+2);

    // push to output
    ACT_INST(h, fpushout(PALWAYS, VR5, BRH1), l+6);
  } else {
    // adding bias, set flag
    ACT_INST(h, faddf(PALWAYS, VR2, VR0, BRW2), 6);

    // select a scale and shift based on ALU state
    if (fp16scl) {
      ACT_INST(h, selecth(PALWAYS, VR3, BRW1), 8);
    } else {
      ACT_INST(h, selectb(PALWAYS, VR3, BRW1), 8);
    }

    // multiply from scale on mul0
    ACT_INST(h, mpy(PALWAYS, VR4, VR2, VR3), 10);

    // get input 1
    ACT_INST(h, fpopin1(PFIRST2, VR1), 14);

    // Shift over spatial dimension
    ACT_INST(h, shv(PNFIRST2, VR1, VR1), 16);

    // element-wise op with scaled input 0
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR5, VR4, VR1), 18); break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR5, VR4, VR1), 18); break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR5, VR4, VR1), 18); break;
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR5, VR4, VR1), 18); break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR5, VR4, VR1), 18); break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // push to output
    ACT_INST(h, fpushout(PALWAYS, VR5, BRH1), 20);
  }

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-operation and PLUT activation program following fully-connected convolution
// BRH0: optional scale
// BRH1: postscale + asymmetric offset
// BRW1: bias
//
//
void init_eltop_fc_lut(act_hlapi_t& h, act_bin_op_t op, bool ea, bool ps, bool fp16scl) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  h.i.u.op.scl[1] = 1*ELTOP_FC_PLUT_PAR_PER_CHAN;

  // start of activation program
  ACT_START(h);

  // outer loop
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PFIRST2, VR0), 0);

  // inner loop: fixed 8 iterations for 8*v1 processing
  // get new set of per channel parameters
  ACT_INST(h, poppars(PALWAYS, SR1), 1);

  // shift over spatial dimension
  ACT_INST(h, shv(PNFIRST2, VR0, VR0), 4);

  // adding bias
  ACT_INST(h, fadd(PALWAYS, VR2, VR0, BRW1), 6);

  if (ea) {
    // get input 1
    ACT_INST(h, fpopin1(PFIRST2, VR1), 8);

    // Shift over spatial dimension
    ACT_INST(h, shv(PNFIRST2, VR1, VR1), 10);

    // element-wise op with input 0
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR3, VR2, VR1), 12); break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR3, VR2, VR1), 12); break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR3, VR2, VR1), 12); break;
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR3, VR2, VR1), 12); break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR3, VR2, VR1), 12); break;
      default: assert(0 && "unsupported eltwise operation");
    }

    // do lookup
    ACT_INST(h, lutq0(PALWAYS,      VR3), 14);
    ACT_INST(h, lutq1(PALWAYS, VR4, VR3), 16);

    // interpolation
    ACT_INST(h, mac0(PALWAYS, VR5, VR4), 18);
    ACT_INST(h, mac1(PALWAYS, VR6, VR5), 22);
    if (ps) {
      // optional post-scaling
      if (fp16scl) {
        ACT_INST(h, mpyh(PALWAYS, VR7, VR6, BRH0), 26);
      } else {
        ACT_INST(h, mpyb(PALWAYS, VR7, VR6, BRH0), 26);
      }
      // push to output
      ACT_INST(h, fpushout(PALWAYS, VR7, BRH1), 30);
    } else {
      // push to output
      ACT_INST(h, fpushout(PALWAYS, VR6, BRH1), 26);
    }
  } else {
    // do lookup
    ACT_INST(h, lutq0(PALWAYS,      VR2), 8);
    ACT_INST(h, lutq1(PALWAYS, VR3, VR2), 10);

    // interpolation
    ACT_INST(h, mac0(PALWAYS, VR4, VR3), 12);
    ACT_INST(h, mac1(PALWAYS, VR5, VR4), 16);

    // get input 1
    ACT_INST(h, fpopin1(PFIRST2, VR1), 20);

    // Shift over spatial dimension
    ACT_INST(h, shv(PNFIRST2, VR1, VR1), 22);

    // element-wise op with scaled input 0
    switch (op) {
      case op_add:   ACT_INST(h, fadd(PALWAYS, VR6, VR5, VR1), 24); break;
      case op_sub:   ACT_INST(h, fsub(PALWAYS, VR6, VR5, VR1), 24); break;
      case op_rsub:  ACT_INST(h, frsub(PALWAYS, VR6, VR5, VR1), 24); break;
      case op_min:   ACT_INST(h, fmin(PALWAYS, VR6, VR5, VR1), 24); break;
      case op_max:   ACT_INST(h, fmax(PALWAYS, VR6, VR5, VR1), 24); break;
      default: assert(0 && "unsupported eltwise operation");
    }

    if (ps) {
      // optional post-scaling
      if (fp16scl) {
        ACT_INST(h, mpyh(PALWAYS, VR7, VR6, BRH0), 26);
      } else {
        ACT_INST(h, mpyb(PALWAYS, VR7, VR6, BRH0), 26);
      }
      // push to output
      ACT_INST(h, fpushout(PALWAYS, VR7, BRH1), 30);
    } else {
      // push to output
      ACT_INST(h, fpushout(PALWAYS, VR6, BRH1), 26);
    }
  }

  ACT_END(h);
  // end of activation program
}

//
// Maxpooling, no per channel parameters
//
void init_maxpool(act_hlapi_t& h) {  // [NOLINT]
  // no per channel parameters
  h.i.u.op.scl[1] = 0;

  // start of activation program
  ACT_START(h);
  ACT_INST(h, fpopin0(PALWAYS, VR0), 0);
  ACT_INST(h, fadd(PFIRST2, VR1, VR0), 4);
  ACT_INST(h, fmax(PNFIRST2, VR1, VR1, VR0), 5);
  ACT_INST(h, fpushout(PLAST2, VR1), 6);
  ACT_END(h);
  // end of activation program
}

//
// Average-pooling, per spatial scaling
//
void init_avgpool(act_hlapi_t& h) {  // [NOLINT]
  // single set of per channel scale parameters
  // BRH0 = 8
  h.i.u.op.scl[1] = 1;
  // mask
  h.i.u.op.scl[2] = 0xff;
  // initial 0
  h.i.u.op.scl[3] = 0;

  // start of activation program
  ACT_START(h);
  // load shifts once
  ACT_INST(h, poppars(PFIRST0, SR1), 0);
  // load per spatial scaling
  ACT_INST(h, popin1(PFIRST1, VR0), 1);
  ACT_INST(h, add(PFIRST1, VR1, SR3), 2);
  ACT_INST(h, trnsp(PFIRST1, VR0, VR1), 4);
  ACT_INST(h, band(PFIRST1, VR0, SR2, VR0), 6);
  ACT_INST(h, sl(PFIRST1, VR1, VR1, BRH0), 8);
  ACT_INST(h, bor(PFIRST1, VR2, VR1, VR0), 10);
  ACT_INST(h, bcc(PFIRST1, VR2, VR2), 12);
  // accumulate and scale
  ACT_INST(h, fpopin0(PALWAYS, VR3), 14);
  ACT_INST(h, fadd(PFIRST2, VR4, VR3), 18);
  ACT_INST(h, fadd(PNFIRST2, VR4, VR4, VR3), 19);
  ACT_INST(h, mpyh(PLAST2, VR5, VR4, VR2), 20);
  ACT_INST(h, fpushout(PLAST2, VR5), 24);
  ACT_END(h);
  // end of activation program
}
void init_avgpool(act_hlapi_t& h,  bool excl_pad) {  // [NOLINT]
  // start of activation program
  ACT_START(h);
  if (!excl_pad) {
    // inclusive padding, broadcast scalar SR0 to vector
    ACT_INST(h, add(PFIRST0, VR0, SR0), 0);
  }
  // read, accumulate, scale, write
  ACT_INST(h, fpopin0(PALWAYS, VR1), 1);
  if (excl_pad) {
    // exclusive padding
    ACT_INST(h, fpoprecip(PLAST2, VR0), 2);
  }
  ACT_INST(h, fadd(PFIRST2, VR2, VR1), 4);
  ACT_INST(h, fadd(PNFIRST2, VR2, VR2, VR1), 5);
  ACT_INST(h, mpy(PLAST2, VR3, VR2, VR0), 6);
  ACT_INST(h, fpushout(PLAST2, VR3), 10);
  ACT_END(h);
  // end of activation program
}

void init_gavgpool_v2(act_hlapi_t& h, float scale) {  // [NOLINT]
  h.i.u.op.scl[0] = fp_e8m23_t(scale).data;
  
  // start of activation program
  ACT_START(h);
  ACT_INST(h, add(PFIRST0, VR5, SR0), 0);             // broadcast scale once
  ACT_INST(h, fpopin0(PALWAYS, VR0), 1);              // pop input layer data into VR0
  ACT_INST(h, fadd(PFIRST2, VR1, VR0), 4);            // move to accumulator
  ACT_INST(h, fadd(PNFIRST2, VR1, VR1, VR0), 5);      // add to accumulator
  ACT_INST(h, raddv(PLAST2, VR2, VR1), 6);            // reduce and accumulate stage 0
  ACT_INST(h, raddv(PLAST2, VR3, VR2), 8);            // reduce and accumulate stage 1
  ACT_INST(h, raddv(PLAST2, VR4, VR3), 10);           // reduce and accumulate stage 2
  ACT_INST(h, mpy(PLAST2, VR6, VR4, VR5), 12);        // scale down
  ACT_INST(h, fpushout(PLAST2, VR6), 16);             // push result
  ACT_END(h);
  // end of activation program
}

void init_gavgpool_new(act_hlapi_t& h, bool useAcc, bool keepAcc) {  // [NOLINT]
  // no per channel parameter
  h.i.u.op.scl[0] = useAcc ? 1 : 0;

  // start of activation program
  ACT_START(h);
  ACT_INST(h, neq(PFIRST0, VR0, SR0), 0);             // compare SR0!=0 and set flags
  ACT_INST(h, fpopin1(PFIRST1, VR1), 1);              // pop channel accumulator value into VR1
  ACT_INST(h, select(PFIRST1, VR2, VR1), 4);          // select 0 or accumulator value
  ACT_INST(h, fpopin0(PALWAYS, VR3), 5);              // pop input layer data into VR0
  ACT_INST(h, fadd(PALWAYS, VR2, VR3, VR2),8);        // add with accumulator
  ACT_INST(h, raddv(PLAST1, VR4, VR2), 10);           // reduce and accumulate stage 0
  ACT_INST(h, raddv(PLAST1, VR4, VR4), 12);           // reduce and accumulate stage 1
  ACT_INST(h, raddv(PLAST1, VR4, VR4), 14);           // reduce and accumulate stage 2
  if (keepAcc) {
    // keep the intermediate output
    ACT_INST(h, fpushout(PLAST1, VR4), 16);           // keepAcc in AM
  } else {
    // final output --> divide accumulator by number of inputs
    //ACT_INST(h, norm(PLAST1, VR4, VR2), 12);          // normalize
    //ACT_INST(h, asrw(PLAST1, VR5, VR2, VR4), 14);     // shift to 16b
    //ACT_INST(h, add(PLAST1, VR6, SR2), 16);           // broadcast scale
    //ACT_INST(h, mpyh(PLAST1, VR5, VR5, VR6), 18);     // 16b*16b scale
    //ACT_INST(h, sub(PLAST1, VR6, SR3, VR4), 19);      // final shift amount
    //ACT_INST(h, asrr(PLAST1, VR5, VR5, VR6), 22);     // shift
    //ACT_INST(h, pushout(PLAST1, VR5), 24);            // push result to AM
    ACT_INST(h, add(PLAST1, VR5, SR2), 16);           // broadcast scale
    ACT_INST(h, mpy(PLAST1, VR6, VR4, VR5), 18);      // 16b*16b scale
    ACT_INST(h, fpushout(PLAST1, VR6), 22);           // push result to AM
  }
  ACT_END(h);
  // end of activation program
}

//
// Global Average-pooling
//
void init_gavgpool(act_hlapi_t& h, bool useAcc, bool keepAcc) {  // [NOLINT]
  // no per channel parameter
  h.i.u.op.scl[1] = useAcc ? 1 : 0;

  // start of activation program
  ACT_START(h);
  ACT_INST(h, neq(PFIRST0, VR0, SR1), 0);             // compare SR1 to 0 and set flags
  ACT_INST(h, fpopin1(PFIRST1, VR1), 1);              // pop channel accumulator value into VR1
  ACT_INST(h, select(PFIRST1, VR2, VR1), 4);          // select 0 or accumulator value
  ACT_INST(h, fpopin0(PALWAYS, VR3), 5);              // pop input layer data into VR0
  ACT_INST(h, fadd(PALWAYS, VR2, VR2, VR3), 8);       // accumulate on VR2
  if (keepAcc) {
    ACT_INST(h, fpushout(PLAST1, VR2), 10);           // keepAcc in AM
  } else {
    ACT_INST(h, raddv(PLAST1, VR4, VR2), 10);         // reduce stage 0
    ACT_INST(h, raddv(PLAST1, VR5, VR4), 12);         // reduce stage 1
    ACT_INST(h, raddv(PLAST1, VR6, VR5), 14);         // reduce stage 2
    ACT_INST(h, add(PLAST1, VR7, SR2), 16);           // broadcast SR2 to VR7
    ACT_INST(h, mpy(PLAST1, VR6, VR7, VR6), 18);      // scale down result by reciprocal multiply
    ACT_INST(h, fpushout(PLAST1, VR6), 22);           // push result to VM if not keepAcc
  }
  ACT_END(h);
  // end of activation program
}

//
// Sum-pooling,  no per channel parameters
//
void init_sumpool(act_hlapi_t& h) {  // [NOLINT]
  // no per channel parameters
  h.i.u.op.scl[1] = 0;

  // start of activation program
  ACT_START(h);
  ACT_INST(h, fpopin0(PALWAYS, VR0), 0);
  ACT_INST(h, fadd(PFIRST2, VR1, VR0), 4);
  ACT_INST(h, fadd(PNFIRST2, VR1, VR1, VR0), 5);
  ACT_INST(h, fpushout(PLAST2, VR1), 6);
  ACT_END(h);
  // end of activation program
}

//
// Argmax over channel dimension, split into two APIs
// 1: eltwise [H][W][C] -> [H][W][2][16], [2] for maxvalue,maxindex, result in AM
// 2: reduction [H][W][2][16] to [H][W][1]
// 
//
// SR0: ISIZE
// loops: [H][W][C]
void init_argmax_c0(act_hlapi_t& h) {  // [NOLINT]
  h.i.u.op.scl[0] = ISIZE;  // immediate value 16
  
  // start of program
  ACT_START(h);
  
  // create v16 channel index and increment per iteration
  ACT_INST(h, strc(PFIRST2, VR0), 0);                   // VR0 = index = 0..15
  
  // inner loop
  ACT_INST(h, fpopin0(PALWAYS, VR1), 1);                // input value i16
  ACT_INST(h, add(PNFIRST2, VR0, SR0, VR0), 3);         // VR0 = VR0 + ISIZE
  ACT_INST(h, add(PFIRST2, VR2, VR1), 4);               // VR2 is maxval
  ACT_INST(h, fmaxf(PNFIRST2, VR2, VR2, VR1), 5);       // update maxval and keep selection bits
  ACT_INST(h, add(PFIRST2, VR3, VR0), 6);               // VR3 is maxidx
  ACT_INST(h, select(PNFIRST2, VR3, VR3, VR0), 7);      // update maxidx based on kept selection bits
  
  // write result
  ACT_INST(h, fpushout(PLAST2, VR2), 8);                 // write-back maxval as raw fp32
  ACT_INST(h, pushout(PLAST2, VR3), 10);                // write-back index as raw int32
  ACT_END(h);
  // end of activation program
}

// loops: [H][W][1]
void init_argmax_c1(act_hlapi_t& h) {  // [NOLINT]
  // start of program
  ACT_START(h);
  
  // read input
  ACT_INST(h, fpopin0(PALWAYS, VR0), 0);                 // read maxval as fp32
  ACT_INST(h, popin0(PALWAYS, VR1), 2);                 // read index as int32

  // reduce result to i16->i8->i4->i2->i1
  ACT_INST(h, rmaxc(PALWAYS, VR2, VR0), 4);             // rmax stage 0
  ACT_INST(h, select(PALWAYS, VR3, VR1), 6);            // index select stage 0
  ACT_INST(h, rorc(PALWAYS, VR4, VR3), 8);              // index reduce stage 0
  ACT_INST(h, rmaxc(PALWAYS, VR5, VR2), 10);            // rmax stage 1
  ACT_INST(h, select(PALWAYS, VR6, VR4), 12);           // index select stage 1
  ACT_INST(h, rorc(PALWAYS, VR7, VR6), 14);             // index reduce stage 1
  ACT_INST(h, rmaxc(PALWAYS, VR5, VR5), 16);            // rmax stage 2
  ACT_INST(h, select(PALWAYS, VR6, VR7), 18);           // index select stage 2
  ACT_INST(h, rorc(PALWAYS, VR7, VR6), 20);             // index reduce stage 2
  ACT_INST(h, rmaxc(PALWAYS, VR5, VR5), 22);            // rmax stage 3
  ACT_INST(h, select(PALWAYS, VR6, VR7), 24);           // index select stage 3
  ACT_INST(h, rorc(PALWAYS, VR7, VR6), 26);             // index reduce stage 3
  
  // write result as integer
  ACT_INST(h, pushout(PALWAYS, VR7), 28);               // write-back, only i0 is meaningfull

  ACT_END(h);
  // end of activation program
}

//
// Argmax over inner spatial dimension
//
// loops: [D][H][C][W]
void init_argmax(act_hlapi_t& h, bool vsize2) {  // [NOLINT]
  // start of program
  ACT_START(h);

  // pop an input
  ACT_INST(h, fpopin0(PALWAYS, VR0), 0);                // input value
  ACT_INST(h, popidx(PALWAYS, VR1), 1);                 // input index in parallel

  // initialize the max value in first inner iteration
  // else compare and select max
  ACT_INST(h, add(PFIRST2, VR2, VR0), 4);               // VR2 is maxval
  ACT_INST(h, fmaxf(PNFIRST2, VR2, VR2, VR0), 5);       // update maxval and keep selection bits
  ACT_INST(h, add(PFIRST2, VR3, VR1), 6);               // VR3 is maxidx
  ACT_INST(h, select(PNFIRST2, VR3, VR3, VR1), 7);      // update maxidx based on kept selection bits

  // reduce result
  if (!vsize2) {
    ACT_INST(h, rmaxv(PLAST2, VR2, VR2), 8);              // VR2 is max reduced to an index vector
    ACT_INST(h, select(PLAST2, VR3, VR3), 10);            // VR3 is max reduced to an index vector
    ACT_INST(h, rorv(PLAST2, VR4, VR3), 12);              // VR4 is reduced result in vlane 0
    ACT_INST(h, rmaxv(PLAST2, VR2, VR2), 14);             // rmax stage 1
    ACT_INST(h, select(PLAST2, VR4, VR4), 16);            // index select stage 1
    ACT_INST(h, rorv(PLAST2, VR5, VR4), 18);              // index reduce stage 1
    ACT_INST(h, rmaxv(PLAST2, VR2, VR2), 20);             // rmax stage 2
    ACT_INST(h, select(PLAST2, VR5, VR5), 22);            // index select stage 2
    ACT_INST(h, rorv(PLAST2, VR6, VR5), 24);              // index reduce stage 2

    // write result
    ACT_INST(h, pushout(PLAST2, VR6), 26);                // write-back only vlane 0
  } else {
    ACT_INST(h, rmaxv(PLAST2, VR2, VR2), 8);              // VR2 is max reduced to an index vector
    ACT_INST(h, select(PLAST2, VR3, VR3), 10);            // VR3 is max reduced to an index vector
    ACT_INST(h, rorv(PLAST2, VR4, VR3), 12);              // VR4 is reduced result in vlane 0

    // write result
    ACT_INST(h, pushout(PLAST2, VR4), 14);                // write-back only vlane 0
  }

  ACT_END(h);
  // end of activation program
}


//
// Reduce in W dimension
//
void init_reduce(act_hlapi_t& h, act_bin_op_t op, bool vsize2) {  // [NOLINT]
  // no per channel parameters
  h.i.u.op.scl[1] = 0;

  // start of program
  ACT_START(h);
  // pop an input
  if (op == op_band || op == op_bor) {
    ACT_INST(h, popin0(PALWAYS, VR0), 0);                 // input value
  } else {
    ACT_INST(h, fpopin0(PALWAYS, VR0), 0);                 // input value
  }

  // initialize the vector result in first inner iteration
  // else do vector operation based on reduction op
  ACT_INST(h, add(PFIRST2, VR1, VR0), 4);
  if (!vsize2) {
    switch (op) {
    case op_band: ACT_INST(h, band(PNFIRST2, VR1, VR0, VR1), 5);
      ACT_INST(h, randv(PLAST2, VR2, VR1), 6);
      ACT_INST(h, randv(PLAST2, VR3, VR2), 8);
      ACT_INST(h, randv(PLAST2, VR4, VR3), 10); break;
    case op_bor:  ACT_INST(h, bor(PNFIRST2, VR1, VR0, VR1), 5);
      ACT_INST(h, rorv(PLAST2, VR2, VR1), 6);
      ACT_INST(h, rorv(PLAST2, VR3, VR2), 8);
      ACT_INST(h, rorv(PLAST2, VR4, VR3), 10);  break;
    case op_min:  ACT_INST(h, min(PNFIRST2, VR1, VR0, VR1), 5);
      ACT_INST(h, rminv(PLAST2, VR2, VR1), 6);
      ACT_INST(h, rminv(PLAST2, VR3, VR2), 8);
      ACT_INST(h, rminv(PLAST2, VR4, VR3), 10); break;
    case op_max:  ACT_INST(h, max(PNFIRST2, VR1, VR0, VR1), 5);
      ACT_INST(h, rmaxv(PLAST2, VR2, VR1), 6);
      ACT_INST(h, rmaxv(PLAST2, VR3, VR2), 8);
      ACT_INST(h, rmaxv(PLAST2, VR4, VR3), 10); break;
    case op_add:  ACT_INST(h, add(PNFIRST2, VR1, VR0, VR1), 5);
      ACT_INST(h, raddv(PLAST2, VR2, VR1), 6);
      ACT_INST(h, raddv(PLAST2, VR3, VR2), 8);
      ACT_INST(h, raddv(PLAST2, VR4, VR3), 10); break;
    default: assert(0 && "unsupported reduction operation");
    }
    // write the result
    if (op == op_band || op == op_bor) {
      ACT_INST(h, pushout(PLAST2, VR4), 12);
    } else {
      ACT_INST(h, fpushout(PLAST2, VR4), 12);
    }
  } else {
    switch (op) {
    case op_band: ACT_INST(h, band(PNFIRST2, VR1, VR0, VR1), 5);
      ACT_INST(h, randv(PLAST2, VR2, VR1), 6); break;
    case op_bor:  ACT_INST(h, bor(PNFIRST2, VR1, VR0, VR1), 5);
      ACT_INST(h, rorv(PLAST2, VR2, VR1), 6);  break;
    case op_min:  ACT_INST(h, min(PNFIRST2, VR1, VR0, VR1), 5);
      ACT_INST(h, rminv(PLAST2, VR2, VR1), 6); break;
    case op_max:  ACT_INST(h, max(PNFIRST2, VR1, VR0, VR1), 5);
      ACT_INST(h, rmaxv(PLAST2, VR2, VR1), 6); break;
    case op_add:  ACT_INST(h, add(PNFIRST2, VR1, VR0, VR1), 5);
      ACT_INST(h, raddv(PLAST2, VR2, VR1), 6); break;
    default: assert(0 && "unsupported reduction operation");
    }
    // write the result
    if (op == op_band || op == op_bor) {
      ACT_INST(h, pushout(PLAST2, VR2), 8);
    } else {
      ACT_INST(h, fpushout(PLAST2, VR2), 8);
    }
  }

  ACT_END(h);
  // end of activation program
}

//
// Reduce with useAcc
//
void init_reduce_accum(act_hlapi_t& h, act_bin_op_t op, bool useAcc, bool vsize2) {  // [NOLINT]
  // no per channel parameters
  h.i.u.op.scl[1] = 0;
  h.i.u.op.scl[2] = useAcc ? 1 : 0;
  switch (op) {
    case op_band: h.i.u.op.scl[3] = 0xffffffff; break;
    case op_bor:  h.i.u.op.scl[3] = 0x00000000; break;
    case op_min:  h.i.u.op.scl[3] = 0x7fffffff; break;
    case op_max:  h.i.u.op.scl[3] = 0xffffffff; break;
    case op_add:  h.i.u.op.scl[3] = 0x00000000; break;
    default: assert(0 && "unsupported reduction operation");
  }

  // start of program
  ACT_START(h);
  // pop an input
  if (op == op_band || op == op_bor) {
    ACT_INST(h, popin0(PALWAYS, VR0), 0);                 // input value
    ACT_INST(h, popin1(PLAST2, VR4), 1);                  // accumulator value
  } else {
    ACT_INST(h, fpopin0(PALWAYS, VR0), 0);                 // input value
    ACT_INST(h, fpopin1(PLAST2, VR4), 1);                  // accumulator value
  }
  // compare SR2 to 0 and set flags
  ACT_INST(h, neq(PLAST2, VR7, SR2), 4);
  ACT_INST(h, add(PLAST2, VR5, SR3), 6);
  ACT_INST(h, select(PLAST2, VR6, VR4, VR5), 8);

  // initialize the vector result in first inner iteration
  // else do vector operation based on reduction op
  ACT_INST(h, add(PFIRST2, VR1, VR0), 10);
  if (!vsize2) {
    switch (op) {
    case op_band: ACT_INST(h, band(PNFIRST2, VR1, VR0, VR1), 11);
      ACT_INST(h, randv(PLAST2, VR2, VR1), 12);
      ACT_INST(h, randv(PLAST2, VR2, VR2), 14);
      ACT_INST(h, randv(PLAST2, VR2, VR2), 16);
      ACT_INST(h, band(PLAST2, VR3, VR2, VR6), 18); break;
    case op_bor:  ACT_INST(h, bor(PNFIRST2, VR1, VR0, VR1), 11);
      ACT_INST(h, rorv(PLAST2, VR2, VR1), 12);
      ACT_INST(h, rorv(PLAST2, VR2, VR2), 14);
      ACT_INST(h, rorv(PLAST2, VR2, VR2), 16);
      ACT_INST(h, bor(PLAST2, VR3, VR2, VR6), 18); break;
    case op_min:  ACT_INST(h, fmin(PNFIRST2, VR1, VR0, VR1), 11);
      ACT_INST(h, rminv(PLAST2, VR2, VR1), 12);
      ACT_INST(h, rminv(PLAST2, VR2, VR2), 14);
      ACT_INST(h, rminv(PLAST2, VR2, VR2), 16);
      ACT_INST(h, fmin(PLAST2, VR3, VR2, VR6), 18); break;
    case op_max:  ACT_INST(h, fmax(PNFIRST2, VR1, VR0, VR1), 11);
      ACT_INST(h, rmaxv(PLAST2, VR2, VR1), 12);
      ACT_INST(h, rmaxv(PLAST2, VR2, VR2), 14);
      ACT_INST(h, rmaxv(PLAST2, VR2, VR2), 16);
      ACT_INST(h, fmax(PLAST2, VR3, VR2, VR6), 18); break;
    case op_add:  ACT_INST(h, fadd(PNFIRST2, VR1, VR0, VR1), 11);
      ACT_INST(h, raddv(PLAST2, VR2, VR1), 12);
      ACT_INST(h, raddv(PLAST2, VR2, VR2), 14);
      ACT_INST(h, raddv(PLAST2, VR2, VR2), 16);
      ACT_INST(h, fadd(PLAST2, VR3, VR2, VR6), 18); break;
    default: assert(0 && "unsupported reduction operation");
    }
    // write the result
    if (op == op_band || op == op_bor) {
      ACT_INST(h, pushout(PLAST2, VR3), 20);
    } else {
      ACT_INST(h, fpushout(PLAST2, VR3), 20);
    }
  } else {
    switch (op) {
    case op_band: ACT_INST(h, band(PNFIRST2, VR1, VR0, VR1), 11);
      ACT_INST(h, randv(PLAST2, VR2, VR1), 12);
      ACT_INST(h, band(PLAST2, VR3, VR2, VR6), 14); break;
    case op_bor:  ACT_INST(h, bor(PNFIRST2, VR1, VR0, VR1), 11);
      ACT_INST(h, rorv(PLAST2, VR2, VR1), 12);
      ACT_INST(h, bor(PLAST2, VR3, VR2, VR6), 14); break;
    case op_min:  ACT_INST(h, fmin(PNFIRST2, VR1, VR0, VR1), 11);
      ACT_INST(h, rminv(PLAST2, VR2, VR1), 12);
      ACT_INST(h, fmin(PLAST2, VR3, VR2, VR6), 14); break;
    case op_max:  ACT_INST(h, fmax(PNFIRST2, VR1, VR0, VR1), 11);
      ACT_INST(h, rmaxv(PLAST2, VR2, VR1), 12);
      ACT_INST(h, fmax(PLAST2, VR3, VR2, VR6), 14); break;
    case op_add:  ACT_INST(h, fadd(PNFIRST2, VR1, VR0, VR1), 11);
      ACT_INST(h, raddv(PLAST2, VR2, VR1), 12);
      ACT_INST(h, fadd(PLAST2, VR3, VR2, VR6), 14); break;
    default: assert(0 && "unsupported reduction operation");
    }
    // write the result
    if (op == op_band || op == op_bor) {
      ACT_INST(h, pushout(PLAST2, VR3), 16);
    } else {
      ACT_INST(h, fpushout(PLAST2, VR3), 16);
    }
  }

  ACT_END(h);
  // end of activation program
}

//
// Transpose
void init_transpose(act_hlapi_t& h, bool vsize2) {  // [NOLINT]
  if (vsize2) {
    // start of program 1K
    ACT_START(h);
    // pop 8 inputs
    ACT_INST(h, popin0(PALWAYS, VR0), 0);               // input v0.v1i16
    ACT_INST(h, popin1(PALWAYS, VR1), 1);               // input v2.v3i16
    ACT_INST(h, popin0(PALWAYS, VR2), 2);               // input v4.v5i16
    ACT_INST(h, popin1(PALWAYS, VR3), 3);               // input v6.v7i16
    ACT_INST(h, popin0(PALWAYS, VR4), 4);               // input v8.v9i16
    ACT_INST(h, popin1(PALWAYS, VR5), 5);               // input v10.v11i16
    ACT_INST(h, popin0(PALWAYS, VR6), 6);               // input v12.v13i16
    ACT_INST(h, popin1(PALWAYS, VR7), 7);               // input v14.v15i16
    // transpose
    ACT_INST(h, trnsp(PALWAYS, VR0, VR1), 10);          // transpose on VR0/1/2/3/4/5/6/7
    // Push 8 outputs
    ACT_INST(h, pushout(PALWAYS, VR0), 12);             // write-back
    ACT_INST(h, pushout(PALWAYS, VR1), 14);             // write-back
    ACT_INST(h, pushout(PALWAYS, VR2), 16);             // write-back
    ACT_INST(h, pushout(PALWAYS, VR3), 18);             // write-back
    ACT_INST(h, pushout(PALWAYS, VR4), 20);             // write-back
    ACT_INST(h, pushout(PALWAYS, VR5), 22);             // write-back
    ACT_INST(h, pushout(PALWAYS, VR6), 24);             // write-back
    ACT_INST(h, pushout(PALWAYS, VR7), 26);             // write-back

    ACT_END(h);
    // end of activation program
  } else {    
    // start of program for 4k
    ACT_START(h);
    // pop two inputs in parallel
    ACT_INST(h, popin0(PALWAYS, VR0), 0);                 // input v0..7i16
    ACT_INST(h, popin1(PALWAYS, VR1), 1);                 // input v8..15i16

    // transpose
    ACT_INST(h, trnsp(PALWAYS, VR0, VR1), 4);             // transpose on VR0 and VR1
    ACT_INST(h, pushout(PALWAYS, VR0), 6);                // write-back
    ACT_INST(h, add(PALWAYS, VR2, VR1), 7);               // move VR1 to VR2
    ACT_INST(h, pushout(PALWAYS, VR2), 8);                // write-back

    ACT_END(h);
    // end of activation program
  }
}


#ifdef DISABLE_BLOCK
//
// Normalization
//
// FIXME: Update is incomplete. Reached max program size, but still need to calculate shift amount
void init_l1norm(act_hlapi_t& h) {  // [NOLINT]
  h.i.u.op.scl[0] = 0x807fffff;
  h.i.u.op.scl[1] = 0x3f000000;
  // start of program
  ACT_START(h);
  // pop input
  ACT_INST(h, fpopin0(PALWAYS, VR0), 0);              // input to VR0
  ACT_INST(h, fabs(PALWAYS, VR1, VR0), 4);            // absolute value
  ACT_INST(h, fadd(PFIRST2, VR2, VR1), 6);            // initial summation into VR2
  ACT_INST(h, fadd(PNFIRST2, VR2, VR1, VR2), 7);      // subsequent summation into VR2
  ACT_INST(h, raddv(PLAST2, VR2, VR2), 8);            // final reduction stage 0
  ACT_INST(h, raddv(PLAST2, VR2, VR2), 10);           // final reduction stage 1
  ACT_INST(h, raddv(PLAST2, VR3, VR2), 12);           // final reduction stage 2

  // replace exponent by 126, to normalize reduction result to [0.5,1)
  ACT_INST(h, band(PLAST2, VR3, SR0, VR3), 14);
  ACT_INST(h, bor(PLAST2, VR4, SR1, VR3), 16);

  // reciprocal computation
  ACT_INST(h, recip0(PLAST2, VR4), 18);               // first LUT cycle
  ACT_INST(h, recip1(PLAST2, VR5, VR4), 20);          // second LUT cycle
  ACT_INST(h, mac0(PLAST2, VR6, VR5), 22);            // Quadratic interpolation
  ACT_INST(h, mac1(PLAST2, VR7, VR6), 26);
  //ACT_INST(h, fpushout(PLAST2, VR3), 28);             // write-back to element [0]
  ACT_INST(h, fpushout(PLAST2, VR7), 28);             // write-back to element [1]

  ACT_END(h);
  // end of activation program
}
void init_l2norm(act_hlapi_t& h) {  // [NOLINT]
  // SR1 fixed to 1 for shift amount immediate
  h.i.u.op.scl[1] = 1;
  // start of program
  ACT_START(h);

  // pop input
  ACT_INST(h, popin0(PALWAYS, VR0), 0);                 // input to VR0
  ACT_INST(h, add(PFIRST0, VR7, SR1), 1);               // fixed 1 broadcasted once
  ACT_INST(h, mpy(PALWAYS, VR1, VR0, VR0), 2);         // square of input
  ACT_INST(h, raddv(PFIRST2, VR2, VR1), 6);             // initial reduction into VR2
  ACT_INST(h, raddv(PNFIRST2, VR2, VR1, VR2), 7);       // subsequent reduction into VR2

  // normalization of the accumulator
  // get the even shift amount to normalize the accumulator to 16b
  ACT_INST(h, norm2(PLAST2, VR3, VR2), 8);
  ACT_INST(h, asrw(PLAST2, VR4, VR2, VR3), 10);         // wide shift right to normalize to 16b
  ACT_INST(h, asr(PLAST2, VR3, VR3, VR7), 12);          // divide shift amount by 2

  // reciprocal square-root computation
  ACT_INST(h, rsqrt0(PLAST2, VR4), 15);                 // first LUT cycle
  ACT_INST(h, rsqrt1(PLAST2, VR5, VR4), 16);            // second LUT cycle
  ACT_INST(h, mac0(PLAST2, VR6, VR5), 18);             // Quadratic interpolation
  ACT_INST(h, mac1(PLAST2, VR6, VR6), 22);
  ACT_INST(h, pushout(PLAST2, VR3), 24);                // write-back to element [0]
  ACT_INST(h, pushout(PLAST2, VR6), 26);                // write-back to element [1]

  ACT_END(h);
  // end of activation program
}

void init_scale(act_hlapi_t& h) {  // [NOLINT]
  // start of program
  ACT_START(h);

  // pop input
  ACT_INST(h, popin1(PFIRST2, VR1), 0);                 // shift amount input to VR1
  ACT_INST(h, add(PFIRST2, VR1, SR1, VR1), 2);          // offset on shift amount
  // broadcast shift amount over vector dimension
  ACT_INST(h, bcv(PFIRST2, VR1, VR1), 4);
  ACT_INST(h, popin1(PFIRST2, VR2), 5);                 // factor input to VR2
  ACT_INST(h, bcv(PFIRST2, VR2, VR2), 6);               // broadcast factor over vector dimension
  ACT_INST(h, popin0(PALWAYS, VR0), 7);                 // feature-map input to VR0
  ACT_INST(h, mpy(PALWAYS, VR3, VR0, VR2), 8);         // multiply input by scaling factor
  ACT_INST(h, asrr(PALWAYS, VR4, VR3, VR1), 12);        // shift by exponent
  ACT_INST(h, pushout(PALWAYS, VR4), 14);               // write-back

  ACT_END(h);
  // end of activation program
}

// reciprocal scaling, scaling factor in VR7
void init_recip_scale(act_hlapi_t& h) {  // [NOLINT]
  // start of program
  ACT_START(h);

  // compute reciprocal
  // get the shift amount to normalize the accumulator to 16b
  ACT_INST(h, norm(PFIRST2, VR0, VR7), 0);
  ACT_INST(h, asrw(PFIRST2, VR1, VR7, VR0), 2);         // wide shift right to normalize to 16b
  ACT_INST(h, add(PFIRST2, VR0, SR1, VR0), 4);          // offset on shift amount
  ACT_INST(h, recip0(PFIRST2, VR1), 6);                 // first LUT cycle
  ACT_INST(h, recip1(PFIRST2, VR1, VR1), 8);            // second LUT cycle
  ACT_INST(h, mac0(PFIRST2, VR1, VR1), 10);            // Quadratic interpolation
  ACT_INST(h, mac1(PFIRST2, VR1, VR1), 14);
  // broadcast scale and shift
  ACT_INST(h, bcc(PFIRST2, VR0, VR0), 11);
  ACT_INST(h, bcv(PFIRST2, VR0, VR0), 13);
  ACT_INST(h, bcc(PFIRST2, VR1, VR1), 18);
  ACT_INST(h, bcv(PFIRST2, VR1, VR1), 20);

  // inner loop
  ACT_INST(h, popin0(PALWAYS, VR2), 21);                // feature-map input to VR0
  ACT_INST(h, mpy(PALWAYS, VR3, VR1, VR2), 22);        // multiply input by scaling factor
  ACT_INST(h, asrr(PALWAYS, VR4, VR3, VR0), 26);        // shift by exponent
  ACT_INST(h, pushout(PALWAYS, VR4), 28);               // write-back

  ACT_END(h);
  // end of activation program
}
#endif  // DISABLE_BLOCK

// integer ratio upsample
void init_upsample(act_hlapi_t& h) {  // [NOLINT]
  // integer upsample feature-map
  // start of activation program
  ACT_START(h);
  ACT_INST(h, popin0(PFIRST2, VR0), 0);
  ACT_INST(h, add(PFIRST2, VR1, VR0), 4);
  ACT_INST(h, pushout(PALWAYS, VR1), 6);
  ACT_END(h);
  // end of activation program
}

// float up/down sample
void init_upsample(act_hlapi_t& h, float offset, float delta) {  // [NOLINT]
  // sr0=offset, sr1=delta
  h.i.u.op.scl[0] = fp_e8m23_t(offset).data;
  h.i.u.op.scl[1] = fp_e8m23_t(delta).data;
  h.i.u.op.scl[2] = fp_e8m23_t(0.5f).data;

  // start of activation program
  ACT_START(h);
  // do once
  ACT_INST(h, add(PFIRST0, vr0, sr0), 0);          // vr0 = offset
  ACT_INST(h, add(PFIRST0, vr0, sr2, vr0), 2);     // vr0 += offset
  // loops
  // For H
  ACT_INST(h, ftoi(PFIRST1, vr7, vr0), 4);         // vr7 = gather index
  ACT_INST(h, gather(PFIRST1), 6);                 // start gather
  ACT_INST(h, fadd(PFIRST1, vr0, sr1, vr0), 8);    // vr7 += delta
  // for DWC
  ACT_INST(h, popin0(PALWAYS, vr1), 16);           // vr1 = input
  ACT_INST(h, pushout(PALWAYS, vr1), 20);          // output = vr1
  ACT_END(h);
  // end of activation program
}

void init_shuffle(act_hlapi_t& h, bool fmdbl, bool odd) {  // [NOLINT]
  // shuffle for group 2
  if (fmdbl) {
    if (odd) {
      // odd 16b
      h.i.u.op.cmaskn = 0x3333;
    } else {
      // even 16b
      h.i.u.op.cmaskn = 0xcccc;
    }
  } else {
    if (odd) {
      // odd 8b
      h.i.u.op.cmaskn = 0x5555;
    } else {
      // even 8b
      h.i.u.op.cmaskn = 0xaaaa;
    }
  }
  // start of activation program
  ACT_START(h);
  if (odd) {
    ACT_INST(h, popin0(PALWAYS, VR0), 0);
    ACT_INST(h, shrc(PALWAYS, VR1, VR0), 4);
    ACT_INST(h, pushout(PALWAYS, VR1), 6);
    ACT_INST(h, add(PALWAYS, VR2, VR0), 7);
    ACT_INST(h, pushout(PALWAYS, VR2), 8);
  } else {
    ACT_INST(h, popin0(PALWAYS, VR0), 0);
    ACT_INST(h, pushout(PALWAYS, VR0), 4);
    ACT_INST(h, shc(PALWAYS, VR1, VR0), 5);
    ACT_INST(h, pushout(PALWAYS, VR1), 6);
  }

  ACT_END(h);
  // end of activation program
}

//
// Eltwise-multiplication and scale program (unrolled on 2 ixpix_t)
// BRH0: postscale + asymmetric output offset
// BRH1: optional scale and shift(positive only)
// BRW1: zpa
// BRW2: zpb
//
void init_eltmul(act_hlapi_t& h, act_alay_t l, bool fp16scl, broadcast_t brdc_f, bool spodd, bool ps) {  // [NOLINT]
  // SR1 has number of per channel parameters to pop
  switch (l) {
    case alayo16:
      h.i.u.op.scl[1] = 1*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN;
      break;
    case alayo32:
      h.i.u.op.scl[1] = 2*ELTOP_ELTMUL_SCALE_PAR_PER_CHAN;
      break;
  }

  #define PALWAYSX (spodd ? PNLAST1 : PALWAYS)

  // start of activation program
  ACT_START(h);

  // outer loop
  // get new set of per channel parameters on first iteration of inner loop
  ACT_INST(h, poppars(PFIRST1, SR1), 0);

  // first eltwise multiplication then scale
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PALWAYS, VR0, BRW1), 2);
  // load input accumulator from in1 stream
  ACT_INST(h, fpopin1(PALWAYS, VR1, BRW2), 3);
  // load input accumulator from in0 stream
  ACT_INST(h, fpopin0(PALWAYSX, VR4, BRW1), 4);
  // load input accumulator from in1 stream
  ACT_INST(h, fpopin1(PALWAYSX, VR5, BRW2), 5);

  int l = 6;
  // check broadcasting in w and ch dimensions for input 1
  if (brdc_f.in0_w) {
    ACT_INST(h, bcv(PALWAYS, VR0, VR0), l);
    ACT_INST(h, bcv(PALWAYSX, VR4, VR4), (l + 2));
    l += 4;
  }
  if (brdc_f.in0_c) {
    ACT_INST(h, bcc(PALWAYS, VR0, VR0), l);
    ACT_INST(h, bcc(PALWAYSX, VR4, VR4), (l + 2));
    l += 4;
  }
  // check broadcasting in w and ch dimensions for input 2
  if (brdc_f.in1_w) {
    ACT_INST(h, bcv(PALWAYS, VR1, VR1), l);
    ACT_INST(h, bcv(PALWAYSX, VR5, VR5), (l + 2));
    l += 4;
  }
  if (brdc_f.in1_c) {
    ACT_INST(h, bcc(PALWAYS, VR1, VR1), l);
    ACT_INST(h, bcc(PALWAYSX, VR5, VR5), (l + 2));
    l += 4;
  }
  // eltwise multiply
  // multiply (a[h][w][c] - zpa[c]) * (b[h][w][c] - zpb[c])
  if (l > 6) { // broadcast is used
    l -= 2;
    ACT_INST(h, mpy(PALWAYS, VR2, VR1, VR0), (l + 1));
  } else {
    ACT_INST(h, mpy(PALWAYS, VR2, VR1, VR0), l);
  }
  // multiply (a[h][w][c] - zpa[c]) * (b[h][w][c] - zpb[c])
  ACT_INST(h, mpy(PALWAYSX, VR6, VR5, VR4), (l + 2));
  // scale on mul0
  if (ps) {
    if (fp16scl) {
      ACT_INST(h, mpyh(PALWAYS, VR3, VR2, BRH1), (l + 4));         // scaled = (tmp * scl[c]) >> shft[c]
      ACT_INST(h, mpyh(PALWAYSX, VR7, VR6, BRH1), (l + 6));
    } else {
      ACT_INST(h, mpyb(PALWAYS, VR3, VR2, BRH1), (l + 4));         // scaled = (tmp * scl[c]) >> shft[c]
      ACT_INST(h, mpyb(PALWAYSX, VR7, VR6, BRH1), (l + 6));
    }
    // push to output
    ACT_INST(h, fpushout(PALWAYS, VR3, BRH0), (l + 8));           // out[h][w][c] = sat(scaled+asymm[c])
    ACT_INST(h, fpushout(PALWAYSX, VR7, BRH0), (l + 10));
  } else {
    // push to output
    ACT_INST(h, fpushout(PALWAYS, VR2, BRH0), (l + 4));           // out[h][w][c] = sat(scaled+asymm[c])
    ACT_INST(h, fpushout(PALWAYSX, VR6, BRH0), (l + 6));
  }
  ACT_END(h);
  // end of activation program
  #undef PALWAYSX
}

//
// corner aligned linear interpolation
//
void init_interp1d(act_hlapi_t& h, int32_t offset, int32_t delta) {  // [NOLINT]
  // sr0=offset, sr1=delta
  h.i.u.op.scl[0] = offset;
  h.i.u.op.scl[1] = delta;
  h.i.u.op.scl[2] = 0;

  // start of activation program
  ACT_START(h);
  // do once
  ACT_INST(h, add(PFIRST0, vr0, sr0), 0);          // vr0 = offset
  // loops
  // For H
  ACT_INST(h, fadd(PFIRST1, vr7, sr2, vr0), 2);    // vr2 = vr0 - sr2
  ACT_INST(h, ftoi(PFIRST1, vr7, vr7), 4);         // vr7 = gather index
  ACT_INST(h, fract(PFIRST1, vr1, vr0), 6);        // vr1 = fraction
  ACT_INST(h, gather(PFIRST1), 7);                 // start gather
  ACT_INST(h, fsub(PFIRST1, vr2, sr6, vr1), 8);    // vr2  = 1.0-vr1
  ACT_INST(h, fadd(PFIRST1, vr0, sr1, vr0), 10);    // vr0 += delta

  // for DWC
  ACT_INST(h, fpopin0(PALWAYS, vr3), 18);          // vr3 = left 
  ACT_INST(h, fpopin0(PALWAYS, vr4), 20);          // vr4 = right
  ACT_INST(h, mpy(PALWAYS, vr5, vr2, vr3), 22);    // vr5 = vr2 * vr3
  ACT_INST(h, mpy(PALWAYS, vr6, vr1, vr4), 24);    // vr6 = vr1 * vr4
  ACT_INST(h, fadd(PALWAYS, vr6, vr5, vr6), 28);   // vr6 = vr5 + vr6
  ACT_INST(h, fpushout(PALWAYS, vr6), 30);         // output

  ACT_END(h);
  // end of activation program
}


void init_gather2d(act_hlapi_t& h) {
  ACT_START(h);
  // only at start of inner loop
  ACT_INST(h, popin1(PFIRST2, vr7), 0);           // vr7 = x&y index converted to float
  ACT_INST(h, gather2d(PFIRST2), 4);              // gather uses vr7 implicitly

  // inner loop with some delay to compensate for gather delay
  ACT_INST(h, popin0(PALWAYS, vr6), 16);          // vr6=in
  ACT_INST(h, pushout(PALWAYS, vr6), 20);         // out=vr6
  ACT_END(h);
  // end of activation program
}

//
// Standalone padding
//
void init_pad(act_hlapi_t& h, bool keepint) {
  // start of activation program
  ACT_START(h);
  if (keepint) {
    ACT_INST(h, popin0(PALWAYS, VR0), 0);
    ACT_INST(h, pushout(PALWAYS, VR0), 4);
  } else {
    ACT_INST(h, fpopin0(PALWAYS, VR0), 0);
    ACT_INST(h, fpushout(PALWAYS, VR0), 4);
  }
  ACT_END(h);
}

//
// MLI functions
//
#if NPU_MLI_TAPI_EN
#include "./mli/npu_mli_act_lib.cpp"
#endif

}  // namespace npu_act::uc::v200
