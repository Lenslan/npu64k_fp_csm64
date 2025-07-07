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
 * npu_act_isa.hpp
 *
 * File defining activation ISA
 *
 */
#ifndef NPU_ACT_COMMON_NPU_ACT_ISA_HPP_
#define NPU_ACT_COMMON_NPU_ACT_ISA_HPP_

#include <string>
#include <iostream>
#include "npu_act_types.hpp"


namespace npu_act::uc::v200 {
using namespace std;      // [NOLINT]

// instruction encoding
enum act_fu_t {fu_in0, fu_in1, fu_out, fu_alu0, fu_alu1, fu_mul0, fu_bpar, fu_none};   // functional unit
enum act_ot_t {ot_no, ot_op, ot_s, ot_v, ot_w, ot_h, ot_b};   // operand type
enum act_bin_op_t {op_add, op_sub, op_rsub, op_eadd,
                   op_min, op_max,
                   op_relun, op_mirror, op_replic, op_renorm,
                   op_eq, op_neq, op_gt, op_gte, op_lt, op_lte,
                   op_band, op_bor, op_bxor,
                   op_select, 
                   op_asr, op_lsr, op_sl,
                   op_fadd, op_fsub, op_frsub, op_fmin, op_fmax,
                   op_faddf, op_fsubf, op_frsubf, op_fminf, op_fmaxf,
                   op_feq, op_fneq, op_fgt, op_fgte, op_flt, op_flte,
                   op_frelun, op_frelunf, 
                   op_balu_spare0, op_balu_spare1, op_balu_spare2, op_balu_spare3,
                   op_fpopin, op_fpopinf, op_bin_spare0, op_bin_spare1, op_fpushout, 
                   op_mpyh, op_mpyb, op_mpy};
enum act_una_op_t {op_getid, op_strv, op_strc, op_movf,
                   op_bcc, op_bcv,
                   op_abs, op_bnot, op_sat8, op_sat16, op_shv, op_shc, op_shrc,
                   op_andf, op_orf, op_xorf,
                   op_fabs, op_frelu, op_ftoi, op_itof, op_trunc, op_fract,
                   op_trnsp, op_selecth, op_selectb,
                   op_raddv, op_randv, op_rorv, op_rmaxv, op_rminv,
                   op_raddc, op_randc, op_rorc, op_rmaxc, op_rminc,
                   op_lutq0, op_exp0, op_recip0, op_rsqrt0,
                   op_lutq1, op_exp1, op_recip1, op_rsqrt1,
                   op_ualu_spare0, op_ualu_spare1, op_ualu_spare2, op_ualu_spare3,
                   op_mac0, op_mac1, op_rmpyv, op_umpy_spare0, op_umpy_spare1, 
                   op_popin, op_popidx, op_poppad, op_fpoprecip, op_gather, op_gather2d, op_uin_spare0, op_pushout,
                   op_poppars,
                   op_dbgprint};  // unary and nullary

// program counter type
typedef int8_t act_pc_t;

// broadcasting type
struct broadcast_t {
  broadcast_t() : in0_w(false), in0_c(false), in1_w(false), in1_c(false), in0_h(false), in1_h(false) {}
  broadcast_t(bool in0_w,
              bool in0_c,
              bool in1_w,
              bool in1_c,
              bool in0_h = false,
              bool in1_h = false)
    : in0_w{in0_w},
      in0_c{in0_c},
      in1_w{in1_w},
      in1_c{in1_c},
      in0_h{in0_h},
      in1_h{in1_h} {}

  broadcast_t& operator=(const broadcast_t& other) {
    if (this != &other) {
      in0_w = other.in0_w;
      in0_c = other.in0_c;
      in1_w = other.in1_w;
      in1_c = other.in1_c;
      in0_h = other.in0_h;
      in1_h = other.in1_h;
    }
    return *this;
  }

  bool in0_w;
  bool in0_c;
  bool in1_w;
  bool in1_c;
  bool in0_h = false;
  bool in1_h = false;
};

// s16: scaling=fp16, sb16: scaling=bf16, b8: bias 8bits
enum scl_cfg_t {
  scl_none = 0,
  scl_s8, scl_s16, scl_sb16, scl_s32, scl_b8, scl_b16, scl_b32,
  scl_s8b32, scl_s16b32, scl_sb16b32, scl_s32b32,
  scl_s8b16, scl_s16b16, scl_sb16b16, scl_s32b16,
  scl_s8b8,  scl_s16b8, scl_sb16b8, scl_s32b8
};

struct scale_config_t {
  scale_config_t() : pre(scl_none), post(scl_none), loop_idx(0) {}
  scale_config_t(scl_cfg_t prec, scl_cfg_t postc, uint8_t l) : pre(prec), post(postc), loop_idx(l) {}

  scale_config_t& operator=(const scale_config_t& other) {
    if (this != &other) {
      pre = other.pre;
      post = other.post;
      loop_idx = other.loop_idx;
    }
    return *this;
  }

  scl_cfg_t pre;
  scl_cfg_t post;
  uint8_t loop_idx;   // which loop of tapi, 0, 1, 2
};

struct act_inst_t;
ostream& operator<<(ostream& os, const act_inst_t& d);

struct act_inst_t {
  // instruction width: 5+4+3+9+3+3+6+6=39b --> pad to 40b
  // pc                        :  5 bits
  act_pc_t       pc;
  // predicates                :  4 bits
  act_pred_t     pred;
  // mapping to functional unit:  3 bits
  act_fu_t       fu;
  // operand types 3*3b        :  9 bits
  act_ot_t       fmt[3];
  // destination               :  3 bits
  union {
    act_sidx_t   s;
    act_vidx_t   v;
  } dst;
  // source 0                  :  3 bits
  union {
    act_sidx_t   s;
    act_vidx_t   v;
    act_widx_t   w;
    act_hidx_t   h;
    act_bidx_t   b;
  } src0;
  // source 1 or unary opcode  :  6 bits
  union {
    act_una_op_t una;
    // no scalar
    act_vidx_t   v;
    act_widx_t   w;
    act_hidx_t   h;
    act_bidx_t   b;
  } src1;
  // source 2 or binary opcode :  6 bits
  union {
    act_bin_op_t bin;
  } src2;
  // pad to 40b
  inline act_inst_t() = default;
  inline act_inst_t(act_pred_t p, act_fu_t f) {
    pred = p;
    fu   = f;
    // set argument format to none
    for (int i = 0; i < 3; i++) {
      fmt[i] = ot_no;
    }
  }
  inline act_inst_t(uint8_t*& p) {        // [NOLINT]
    uint64_t v = 0;
    for (int i = 0; i < 5; i++) {
      v |= ((uint64_t)(*p++)) << (i*8);
    }
    pc     = (v >> 0)  & 0x1fLL;
    pred   = act_pred_t((v >> 5)  & 0x0fLL);
    fu     = act_fu_t((v >> 9)  & 0x07LL);
    fmt[0] = act_ot_t((v >> 12) & 0x07LL);
    fmt[1] = act_ot_t((v >> 15) & 0x07LL);
    fmt[2] = act_ot_t((v >> 18) & 0x07LL);
    dst.v   = act_vidx_t((v >> 21) & 0x07LL);
    src0.v  = act_vidx_t((v >> 24) & 0x07LL);
    src1.una = act_una_op_t((v >> 27) & 0x3fLL);
    src2.bin = act_bin_op_t((v >> 33) & 0x3fLL);
  }
  inline uint8_t* serialize(uint8_t* p) const {
    uint64_t v = 0x00LL;
    assert((pred == pred_never || (pc >= 0 && pc < 32)) && "Micro-code exceeds maximum slots");
    v = ((pc     & 0x1fLL) << 0) |
        ((pred   & 0x0fLL) << 5) |
        ((fu     & 0x07LL) << 9) |
        ((fmt[0] & 0x07LL) << 12) |
        ((fmt[1] & 0x07LL) << 15) |
        ((fmt[2] & 0x07LL) << 18) |
        ((dst.v  & 0x07LL) << 21) |
        ((src0.v & 0x07LL) << 24) |
        ((src1.una & 0x3fLL) << 27) |
        ((src2.bin & 0x3fLL) << 33);
    for (int i = 0; i < 5; i++) {
      *p++ = (v>>(i*8)) & 0xff;
    }
    return p;
  }
  inline uint8_t* deserialize(uint8_t* p) {
    uint64_t v;
    uint8_t* vp(reinterpret_cast<uint8_t*>(&v));
    v  = 0;
    for (int i = 0; i < 5; i++) {
      *vp++ = *p++;
    }
    pc       = (v >>  0) & 0x1fLL;
    pred     = (act_pred_t)((v >>  5) & 0x0fLL);
    fu       = (act_fu_t)((v >>  9) & 0x07LL);
    fmt[0]   = (act_ot_t)((v >> 12) & 0x07LL);
    fmt[1]   = (act_ot_t)((v >> 15) & 0x07LL);
    fmt[2]   = (act_ot_t)((v >> 18) & 0x07LL);
    dst.v    = (act_vidx_t)((v >> 21) & 0x07LL);
    src0.v   = (act_vidx_t)((v >> 24) & 0x07LL);
    src1.una = (act_una_op_t)((v >> 27) & 0x3fLL);
    src2.bin = (act_bin_op_t)((v >> 33) & 0x3fLL);
    return p+5;
  }
};
inline ostream& operator<<(ostream& os, const act_inst_t& d) {
  if (d.pred == pred_never) {
    os << "nop";
    return os;
  }
  string s;
  if (d.fmt[2] != ot_op) {
    switch (d.src2.bin) {
    case op_add:      os << "add"; s = "     "; break;
    case op_sub:      os << "sub"; s = "     "; break;
    case op_rsub:     os << "rsub"; s = "    "; break;
    case op_min:      os << "min"; s = "     "; break;
    case op_max:      os << "max"; s = "     "; break;
    case op_relun:    os << "relun"; s = "   "; break;
    case op_eq:       os << "eq"; s = "      "; break;
    case op_neq:      os << "neq"; s = "     "; break;
    case op_gt:       os << "gt"; s = "      "; break;
    case op_gte:      os << "gte"; s = "     "; break;
    case op_lt:       os << "lt"; s = "      "; break;
    case op_lte:      os << "lte"; s = "     "; break;
    case op_band:     os << "band"; s = "    "; break;
    case op_bor:      os << "bor"; s = "     "; break;
    case op_bxor:     os << "bxor"; s = "    "; break;
    case op_select:   os << "select"; s = "  "; break;
    case op_asr:      os << "asr"; s = "     "; break;
    case op_lsr:      os << "lsr"; s = "     "; break;
    case op_sl:       os << "sl"; s = "      "; break;
    case op_fadd:     os << "fadd"; s = "    "; break;
    case op_fsub:     os << "fsub"; s = "    "; break;
    case op_frsub:    os << "frsub"; s = "   "; break;
    case op_fmin:     os << "fmin"; s = "    "; break;
    case op_fmax:     os << "fmax"; s = "    "; break;
    case op_faddf:    os << "faddf"; s = "   "; break;
    case op_fsubf:    os << "fsubf"; s = "   "; break;
    case op_frsubf:   os << "frsubf"; s = "  "; break;
    case op_fminf:    os << "fminf"; s = "   "; break;
    case op_fmaxf:    os << "fmaxf"; s = "   "; break;
    case op_feq:      os << "feq"; s = "     "; break;
    case op_fneq:     os << "fneq"; s = "    "; break;
    case op_fgt:      os << "fgt"; s = "     "; break;
    case op_fgte:     os << "fgte"; s = "    "; break;
    case op_flt:      os << "flt"; s = "     "; break;
    case op_flte:     os << "flte"; s = "    "; break;
    case op_frelun:   os << "frelun"; s = "  "; break;
    case op_frelunf:  os << "frelunf"; s = " "; break;
    case op_eadd:     os << "eadd"; s = "    "; break;
    case op_mirror:   os << "mirror"; s = "  "; break;
    case op_replic:   os << "replic"; s = "  "; break;
    case op_renorm:   os << "renorm"; s = "  "; break;
    case op_fpopin:   os << "fpopin"; s = "  "; break;
    case op_fpopinf:  os << "fpopinf"; s = " "; break;
    case op_fpushout: os << "fpushout"; s = ""; break;
    case op_mpyh:     os << "mpyh"; s = "    "; break;
    case op_mpyb:     os << "mpyb"; s = "    "; break;
    case op_mpy:      os << "mpy"; s = "     "; break;
    default: assert(0 && "unknown binary instruction");
    }
  } else if (d.fmt[1] != ot_op) {
    bool alu1 = false; // if true then on alu1
    bool alu0 = false; // if true then on alu0
    bool nulla = false; // if true then nullary
    switch (d.src1.una) {
    case op_getid:     os << "getid"; s = "    "; alu0 = true; nulla = true; break;
    case op_strv:      os << "strv"; s = "     "; alu0 = true; nulla = true; break;
    case op_strc:      os << "strc"; s = "     "; alu0 = true; nulla = true; break;
    case op_movf:      os << "movf"; s = "     "; alu0 = true; break;
    case op_bcc:       os << "bcc"; s = "      "; alu1 = true; break;
    case op_bcv:       os << "bcv"; s = "      "; alu1 = true; break;
    case op_abs:       os << "abs"; s = "      "; alu0 = true; break;
    case op_bnot:      os << "bnot"; s = "     "; alu0 = true; break;
    case op_sat8:      os << "sat8"; s = "     "; alu0 = true; break;
    case op_sat16:     os << "sat16"; s = "    "; alu0 = true; break;
    case op_shv:       os << "shv"; s = "      "; alu1 = true; break;
    case op_shc:       os << "shc"; s = "      "; alu1 = true; break;
    case op_shrc:      os << "shrc"; s = "     "; alu1 = true; break;
    case op_andf:      os << "andf"; s = "     "; alu0 = true; break;
    case op_orf:       os << "orf"; s = "      "; alu0 = true; break;
    case op_xorf:      os << "xorf"; s = "     "; alu0 = true; break;
    case op_frelu:     os << "frelu"; s = "    "; alu1 = true; break;
    case op_fabs:      os << "fabs"; s = "     "; alu0 = true; break;
    case op_trnsp:     os << "trnsp"; s = "    "; alu0 = true; break;
    case op_selecth:   os << "selecth"; s = "  "; alu1 = true; break;
    case op_selectb:   os << "selectb"; s = "  "; alu1 = true; break;
    case op_raddv:     os << "raddv"; s = "    "; alu0 = true; break;
    case op_rmpyv:     os << "rmpyv"; s = "    "; break;
    case op_randv:     os << "randv"; s = "    "; alu0 = true; break;
    case op_rorv:      os << "rorv"; s = "     "; alu0 = true; break;
    case op_rmaxv:     os << "rmaxv"; s = "    "; alu0 = true; break;
    case op_rminv:     os << "rminv"; s = "    "; alu0 = true; break;
    case op_raddc:     os << "raddc"; s = "    "; alu0 = true; break;
    case op_randc:     os << "randc"; s = "    "; alu0 = true; break;
    case op_rorc:      os << "rorc"; s = "     "; alu0 = true; break;
    case op_rmaxc:     os << "rmaxc"; s = "    "; alu0 = true; break;
    case op_rminc:     os << "rminc"; s = "    "; alu0 = true; break;
    case op_lutq0:     os << "lutq0"; s = "    "; alu1 = true; break;
    case op_exp0:      os << "exp0"; s = "     "; alu1 = true; break;
    case op_recip0:    os << "recip0"; s = "   "; alu1 = true; break;
    case op_rsqrt0:    os << "rsqrt0"; s = "   "; alu1 = true; break;
    case op_lutq1:     os << "lutq1"; s = "    "; alu1 = true; break;
    case op_exp1:      os << "exp1"; s = "     "; alu1 = true; break;
    case op_recip1:    os << "recip1"; s = "   "; alu1 = true; break;
    case op_rsqrt1:    os << "rsqrt1"; s = "   "; alu1 = true; break;
    case op_ftoi:      os << "ftoi"; s = "     "; alu0 = true; break;
    case op_itof:      os << "itof"; s = "     "; alu0 = true; break;
    case op_trunc:     os << "trunc"; s = "    "; alu0 = true; break;
    case op_fract:     os << "fract"; s = "    "; alu0 = true; break;
    case op_mac0:      os << "mac0"; s = "     "; break;
    case op_mac1:      os << "mac1"; s = "     "; break;
    case op_popin:     os << "popin"; s = "    "; break;
    case op_popidx:    os << "popidx"; s = "   "; break;
    case op_poppad:    os << "poppad"; s = "   "; break;
    case op_fpoprecip: os << "fpoprecip"; s = ""; break;
    case op_gather:    os << "gather"; s = "   "; break;
    case op_gather2d:  os << "gather2d"; s = " "; break;
    case op_poppars:   os << "poppars"; s = "  "; break;
    case op_pushout:   os << "pushout"; s = "  "; break;
    case op_dbgprint:  os << "dbgprint"; s = " "; break;
    default: assert(0 && "unknown unary instruction");
    }
    if (alu1)
      assert ((d.fmt[1] == ot_v || d.fmt[1] == ot_w) && "unary ALU1 instruction can only take VR, BRW");
    else if (alu0 && !nulla)
      assert ((d.fmt[1] == ot_v || d.fmt[1] == ot_s) && "unary ALU0 instruction can only take VR, SR");
  } else {
    assert(0 && "unknown instruction");
  }
  switch (d.pred) {
  case pred_first0:  os << ".first0"; s = s + " "; break;
  case pred_first1:  os << ".first1"; s = s + " "; break;
  case pred_first2:  os << ".first2"; s = s + " "; break;
  case pred_last2:   os << ".last2"; s = s + "  "; break;
  case pred_last1:   os << ".last1"; s = s + "  "; break;
  case pred_last0:   os << ".last0"; s = s + "  "; break;
  case pred_nfirst0: os << ".nfirst0"; s = s + ""; break;
  case pred_nfirst1: os << ".nfirst1"; s = s + ""; break;
  case pred_nfirst2: os << ".nfirst2"; s = s + ""; break;
  case pred_nlast2:  os << ".nlast2"; s = s + " "; break;
  case pred_nlast1:  os << ".nlast1"; s = s + " "; break;
  case pred_nlast0:  os << ".nlast0"; s = s + " "; break;
  case pred_even:    os << ".even"; s = s + "   "; break;
  case pred_odd:     os << ".odd"; s = s + "    "; break;
  case pred_always:  os << ".always"; s = s + " "; break;
  default: assert(0 && "unknown predicate");
  }
  switch (d.fu) {
  case fu_in0:     os << ".in0"; s = s + "  "; break;
  case fu_in1:     os << ".in1"; s = s + "  "; break;
  case fu_out:     os << ".out"; s = s + "  "; break;
  case fu_alu0:    os << ".alu0"; s = s + " "; break;
  case fu_alu1:    os << ".alu1"; s = s + " "; break;
  case fu_mul0:    os << ".mul0"; s = s + " "; break;
  case fu_bpar:    os << ".bpar"; s = s + " "; break;
  case fu_none:    os << ".none"; s = s + " "; break;
  default: assert(0 && "unknown function unit");
  }
  // align operands
  os << s;
  s = "";
  switch (d.fmt[0]) {
    case ot_s: os << s << "sr" << d.dst.s << " "; s = ","; break;
    case ot_v: os << s << "vr" << d.dst.v << " "; s = ","; break;
    case ot_no:                                            break;
    default: assert(0 &&"unexpected dst format");
  }
  switch (d.fmt[1]) {
    case ot_s: os << s << "sr" << d.src0.s << " "; s = ","; break;
    case ot_v: os << s << "vr" << d.src0.v << " "; s = ","; break;
    case ot_w: os << s << "brw" << d.src0.w << ""; s = ","; break;
    case ot_h: os << s << "brh" << d.src0.h << ""; s = ","; break;
    case ot_b: os << s << "brb" << d.src0.b << ""; s = ","; break;
    case ot_no:                                             break;
    default: assert(0 &&"unexpected src0 format");
  }
  switch (d.fmt[2]) {
    case ot_v: os << s << "vr" << d.src1.v << " "; s = ","; break;
    case ot_w: os << s << "brw" << d.src1.w << ""; s = ","; break;
    case ot_h: os << s << "brh" << d.src1.h << ""; s = ","; break;
    case ot_b: os << s << "brb" << d.src1.b << ""; s = ","; break;
    case ot_op:
    case ot_no:                                             break;
    default: assert(0 &&"unexpected src1 format");
  }
  return os;
}

//
// Derived unary instructions
//
struct act_inst_dbgprint : public act_inst_t {
  inline act_inst_dbgprint(act_pred_t p, act_sidx_t s) : act_inst_t(p, fu_none) {
    fmt[2]   = ot_op;
    fmt[1]   = ot_s;
    src1.una = op_dbgprint;
    src0.s   = s;
  }
  inline act_inst_dbgprint(act_pred_t p, act_vidx_t s) : act_inst_t(p, fu_none) {
    fmt[2]   = ot_op;
    fmt[1]   = ot_v;
    src1.una = op_dbgprint;
    src0.v   = s;
  }
  inline act_inst_dbgprint(act_pred_t p, act_widx_t s) : act_inst_t(p, fu_none) {
    fmt[2]   = ot_op;
    fmt[1]   = ot_w;
    src1.una = op_dbgprint;
    src0.w   = s;
  }
  inline act_inst_dbgprint(act_pred_t p, act_hidx_t s) : act_inst_t(p, fu_none) {
    fmt[2]   = ot_op;
    fmt[1]   = ot_h;
    src1.una = op_dbgprint;
    src0.h   = s;
  }
  inline act_inst_dbgprint(act_pred_t p, act_bidx_t s) : act_inst_t(p, fu_none) {
    fmt[2]   = ot_op;
    fmt[1]   = ot_b;
    src1.una = op_dbgprint;
    src0.b   = s;
  }
};
struct act_inst_nop : public act_inst_t {
  inline act_inst_nop() : act_inst_t(PNEVER, fu_none) {
  }
};
struct act_inst_poppars : public act_inst_t {
  inline act_inst_poppars(act_pred_t p, act_sidx_t s) : act_inst_t(p, fu_bpar) {
    fmt[2]   = ot_op;
    fmt[1]   = ot_s;
    src1.una = op_poppars;
    src0.s   = s;
  }
};
struct act_inst_getid : public act_inst_t {
  inline act_inst_getid(act_pred_t p, act_sidx_t d) : act_inst_t(p, fu_alu0) {
    fmt[2]   = ot_op;
    fmt[0]   = ot_s;
    src1.una = op_getid;
    dst.s    = d;
  }
  inline act_inst_getid(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_alu0) {
    fmt[2]   = ot_op;
    fmt[0]   = ot_v;
    src1.una = op_getid;
    dst.v    = d;
  }
};
struct act_inst_fpopin0 : public act_inst_t {
  inline act_inst_fpopin0(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_in0) {
    // no bias nor scale
    fmt[2]   = ot_no;
    fmt[1]   = ot_no;
    fmt[0]   = ot_v;
    src2.bin = op_fpopin;
    dst.v    = d;
  }
  inline act_inst_fpopin0(act_pred_t p, act_vidx_t d, act_bidx_t s1) : act_inst_t(p, fu_in0) {
    // with scale only
    fmt[2]   = ot_b;
    fmt[0]   = ot_v;
    src2.bin = op_fpopin;
    src1.b   = s1;
    dst.v    = d;
  }
  inline act_inst_fpopin0(act_pred_t p, act_vidx_t d, act_widx_t s0) : act_inst_t(p, fu_in0) {
    // with bias only
    fmt[1]   = ot_w;
    fmt[0]   = ot_v;
    src2.bin = op_fpopin;
    src0.w   = s0;
    dst.v    = d;
  }
  inline act_inst_fpopin0(act_pred_t p, act_vidx_t d, act_widx_t s0, act_bidx_t s1)
    : act_inst_t(p, fu_in0) {
    // with bias and scale
    fmt[2]   = ot_b;
    fmt[1]   = ot_w;
    fmt[0]   = ot_v;
    src2.bin = op_fpopin;
    src1.b   = s1;
    src0.w   = s0;
    dst.v    = d;
  }
};
struct act_inst_fpopin1 : public act_inst_t {
  inline act_inst_fpopin1(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_in1) {
    // no bias nor scale
    fmt[2]   = ot_no;
    fmt[1]   = ot_no;
    fmt[0]   = ot_v;
    src2.bin = op_fpopin;
    dst.v    = d;
  }
  inline act_inst_fpopin1(act_pred_t p, act_vidx_t d, act_widx_t s0) : act_inst_t(p, fu_in1) {
    // with bias only
    fmt[2]   = ot_no;
    fmt[1]   = ot_w;
    fmt[0]   = ot_v;
    src2.bin = op_fpopin;
    src0.w   = s0;
    dst.v    = d;
  }
  inline act_inst_fpopin1(act_pred_t p, act_vidx_t d, act_bidx_t s1) : act_inst_t(p, fu_in1) {
    // with scale only
    fmt[2]   = ot_b;
    fmt[0]   = ot_v;
    src2.bin = op_fpopin;
    src1.b   = s1;
    dst.v    = d;
  }
  inline act_inst_fpopin1(act_pred_t p, act_vidx_t d, act_widx_t s0, act_bidx_t s1)
    : act_inst_t(p, fu_in1) {
    // with bias and scale
    fmt[2]   = ot_b;
    fmt[1]   = ot_w;
    fmt[0]   = ot_v;
    src2.bin = op_fpopin;
    src1.b   = s1;
    src0.w   = s0;
    dst.v    = d;
  }
};
struct act_inst_fpopinf0 : public act_inst_t {
  inline act_inst_fpopinf0(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_in0) {
    // no bias nor scale
    fmt[2]   = ot_no;
    fmt[1]   = ot_no;
    fmt[0]   = ot_v;
    src2.bin = op_fpopinf;
    dst.v    = d;
  }
  inline act_inst_fpopinf0(act_pred_t p, act_vidx_t d, act_widx_t s0) : act_inst_t(p, fu_in0) {
    // with bias only
    fmt[2]   = ot_no;
    fmt[1]   = ot_w;
    fmt[0]   = ot_v;
    src2.bin = op_fpopinf;
    src0.w   = s0;
    dst.v    = d;
  }
  inline act_inst_fpopinf0(act_pred_t p, act_vidx_t d, act_bidx_t s1) : act_inst_t(p, fu_in0) {
    // with scale only
    fmt[2]   = ot_b;
    fmt[0]   = ot_v;
    src2.bin = op_fpopinf;
    src1.b   = s1;
    dst.v    = d;
  }
  inline act_inst_fpopinf0(act_pred_t p, act_vidx_t d, act_widx_t s0, act_bidx_t s1)
    : act_inst_t(p, fu_in0) {
    // with bias and scale
    fmt[2]   = ot_b;
    fmt[1]   = ot_w;
    fmt[0]   = ot_v;
    src2.bin = op_fpopinf;
    src1.b   = s1;
    src0.w   = s0;
    dst.v    = d;
  }
};
struct act_inst_popin0 : public act_inst_t {
  inline act_inst_popin0(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_in0) {
    fmt[2]   = ot_op;
    fmt[1]   = ot_no;
    fmt[0]   = ot_v;
    src1.una = op_popin;
    dst.v    = d;
  }
};
struct act_inst_popin1 : public act_inst_t {
  inline act_inst_popin1(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_in1) {
    fmt[2]   = ot_op;
    fmt[1]   = ot_no;
    fmt[0]   = ot_v;
    src1.una = op_popin;
    dst.v    = d;
  }
};
struct act_inst_popidx : public act_inst_t {
  inline act_inst_popidx(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_in1) {
    fmt[2]   = ot_op;
    fmt[0]   = ot_v;
    src1.una = op_popidx;
    dst.v    = d;
  }
};
struct act_inst_poppad : public act_inst_t {
  inline act_inst_poppad(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_in1) {
    fmt[2]   = ot_op;
    fmt[0]   = ot_v;
    src1.una = op_poppad;
    dst.v    = d;
  }
};
struct act_inst_fpoprecip : public act_inst_t {
  inline act_inst_fpoprecip(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_in0) {
    fmt[2]   = ot_op;
    fmt[0]   = ot_v;
    src1.una = op_fpoprecip;
    dst.v    = d;
  }
};
struct act_inst_gather : public act_inst_t {
  inline act_inst_gather(act_pred_t p) : act_inst_t(p, fu_in0) {
    fmt[2]   = ot_op;
    src1.una = op_gather;
  }
};
struct act_inst_gather2d : public act_inst_t {
  inline act_inst_gather2d(act_pred_t p) : act_inst_t(p, fu_in0) {
    fmt[2]   = ot_op;
    src1.una = op_gather2d;
  }
};
struct act_inst_pushout : public act_inst_t {
  inline act_inst_pushout(act_pred_t p, act_vidx_t s) : act_inst_t(p, fu_out) {
    // simple
    fmt[2]   = ot_op;
    fmt[1]   = ot_v;
    src1.una = op_pushout;
    src0.v   = s;
  }
};
struct act_inst_fpushout : public act_inst_t {
  inline act_inst_fpushout(act_pred_t p, act_vidx_t s) : act_inst_t(p, fu_out) {
    // simple
    fmt[1]   = ot_v;
    src2.bin = op_fpushout;
    src0.v   = s;
  }
  inline act_inst_fpushout(act_pred_t p, act_vidx_t s0, act_bidx_t s1) : act_inst_t(p, fu_out) {
    // output scale only
    fmt[2]   = ot_b;
    fmt[1]   = ot_v;
    src2.bin = op_fpushout;
    src1.b   = s1;
    src0.v   = s0;
  }
  inline act_inst_fpushout(act_pred_t p, act_vidx_t s0, act_hidx_t s1) : act_inst_t(p, fu_out) {
    // output scale and offset
    fmt[2]   = ot_h;
    fmt[1]   = ot_v;
    src2.bin = op_fpushout;
    src1.h   = s1;
    src0.v   = s0;
  }
};
//
// Derived unary instructions
//
struct act_inst_strv : public act_inst_t {
  // stride in vector dimension
  inline act_inst_strv(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_alu0) {
    fmt[2]   = ot_op;
    fmt[0]   = ot_v;
    src1.una = op_strv;
    dst.v    = d;
  }
};
struct act_inst_strc : public act_inst_t {
  // stride in vector dimension
  inline act_inst_strc(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_alu0) {
    fmt[2]   = ot_op;
    fmt[0]   = ot_v;
    src1.una = op_strc;
    dst.v    = d;
  }
};
struct act_inst_movf : public act_inst_t {
  // move alu_state to register
  inline act_inst_movf(act_pred_t p, act_vidx_t d) : act_inst_t(p, fu_alu0) {
    fmt[2]   = ot_op;
    fmt[0]   = ot_v;
    src1.una = op_movf;
    dst.v    = d;
  }
};
// ALU unary operations
#define UNARY_ALU0(X, Y, Z) \
  struct X : public act_inst_t {\
    inline X(act_pred_t p, act_vidx_t d, act_vidx_t s) : act_inst_t(p, Y) { \
      fmt[2]   = ot_op;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_v;\
      src1.una = Z;\
      src0.v   = s;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_sidx_t s) : act_inst_t(p, Y) { \
      fmt[2]   = ot_op;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_v;\
      src1.una = Z;\
      src0.s   = s;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_vidx_t s) : act_inst_t(p, Y) { \
      fmt[2]   = ot_op;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_s;\
      src1.una = Z;\
      src0.v   = s;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_sidx_t s) : act_inst_t(p, Y) { \
      fmt[2]   = ot_op;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_s;\
      src1.una = Z;\
      src0.s   = s;\
      dst.s    = d;\
    }\
  };
UNARY_ALU0(act_inst_abs, fu_alu0, op_abs)
UNARY_ALU0(act_inst_andf, fu_alu0, op_andf)
UNARY_ALU0(act_inst_orf, fu_alu0, op_orf)
UNARY_ALU0(act_inst_xorf, fu_alu0, op_xorf)
UNARY_ALU0(act_inst_fabs, fu_alu0, op_fabs)
UNARY_ALU0(act_inst_bnot, fu_alu0, op_bnot)
UNARY_ALU0(act_inst_sat8, fu_alu0, op_sat8)
UNARY_ALU0(act_inst_sat16, fu_alu0, op_sat16)
UNARY_ALU0(act_inst_trnsp, fu_alu0, op_trnsp)
UNARY_ALU0(act_inst_ftoi, fu_alu0, op_ftoi)
UNARY_ALU0(act_inst_itof, fu_alu0, op_itof)
UNARY_ALU0(act_inst_trunc, fu_alu0, op_trunc)
UNARY_ALU0(act_inst_fract, fu_alu0, op_fract)
#undef UNARY_ALU0
#define FU_ALUX fu_alu1
#define UNARY_ALU1(X, Y, Z) \
  struct X : public act_inst_t {\
    inline X(act_pred_t p, act_vidx_t d, act_vidx_t s) : act_inst_t(p, Y) { \
      fmt[2]   = ot_op;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_v;\
      src1.una = Z;\
      src0.v   = s;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_widx_t s) : act_inst_t(p, Y) { \
      fmt[2]   = ot_op;\
      fmt[1]   = ot_w;\
      fmt[0]   = ot_v;\
      src1.una = Z;\
      src0.w   = s;\
      dst.v    = d;\
    }\
  };
// ALU1 operations, VR or BRW
UNARY_ALU1(act_inst_bcc, FU_ALUX, op_bcc)
UNARY_ALU1(act_inst_bcv, FU_ALUX, op_bcv)
UNARY_ALU1(act_inst_shv, FU_ALUX, op_shv)
UNARY_ALU1(act_inst_shc, FU_ALUX, op_shc)
UNARY_ALU1(act_inst_shrc, FU_ALUX, op_shrc)
UNARY_ALU1(act_inst_frelu, FU_ALUX, op_frelu)
UNARY_ALU1(act_inst_selecth, FU_ALUX, op_selecth)
UNARY_ALU1(act_inst_selectb, FU_ALUX, op_selectb)
// look-up tables
UNARY_ALU1(act_inst_lutq1, FU_ALUX, op_lutq1)
UNARY_ALU1(act_inst_exp1, FU_ALUX, op_exp1)
UNARY_ALU1(act_inst_recip1, FU_ALUX, op_recip1)
UNARY_ALU1(act_inst_rsqrt1, FU_ALUX, op_rsqrt1)
#undef UNARY_ALU1
#define UNARY_NODST1(X, Y, Z) \
  struct X : public act_inst_t {\
    inline X(act_pred_t p, act_vidx_t s) : act_inst_t(p, Y) { \
      fmt[2]   = ot_op;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_no;\
      src1.una = Z;    \
      src0.v   = s;\
    }\
  };
// look-up tables
UNARY_NODST1(act_inst_lutq0, FU_ALUX, op_lutq0)
UNARY_NODST1(act_inst_exp0, FU_ALUX, op_exp0)
UNARY_NODST1(act_inst_recip0, FU_ALUX, op_recip0)
UNARY_NODST1(act_inst_rsqrt0, FU_ALUX, op_rsqrt0)
#undef UNARY_NODST1
#undef FU_ALUX
// MAC
#define UNARY_MAC(X, Y, Z) \
  struct X : public act_inst_t {\
    inline X(act_pred_t p, act_vidx_t d, act_vidx_t s) : act_inst_t(p, Y) { \
      fmt[2]   = ot_op;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_v;\
      src1.una = Z;\
      src0.v   = s;\
      dst.v    = d;\
    }\
  };
UNARY_MAC(act_inst_mac0, fu_mul0, op_mac0)
UNARY_MAC(act_inst_mac1, fu_mul0, op_mac1)
#undef UNARY_MAC
#define BINARY(X, Y, Z) \
  struct X : public act_inst_t {\
    inline X(act_pred_t p, act_vidx_t d, act_vidx_t s0, act_vidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_v;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src1.v   = s1;\
      src0.v   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_vidx_t s0, act_widx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_w;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src1.w   = s1;\
      src0.v   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_vidx_t s0, act_hidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_h;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src1.h   = s1;\
      src0.v   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_vidx_t s0, act_bidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_b;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src1.b   = s1;\
      src0.v   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_vidx_t s0) : act_inst_t(p, Y) { \
      fmt[2]   = ot_no;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src0.v   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_sidx_t s0, act_vidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_v;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src1.v   = s1;\
      src0.s   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_sidx_t s0, act_widx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_w;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src1.w   = s1;\
      src0.s   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_sidx_t s0, act_hidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_h;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src1.h   = s1;\
      src0.s   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_sidx_t s0, act_bidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_b;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src1.b   = s1;\
      src0.s   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_sidx_t s0) : act_inst_t(p, Y) { \
      fmt[2]   = ot_no;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src0.s   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_vidx_t s0, act_vidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_v;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.v   = s1;\
      src0.v   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_vidx_t s0, act_widx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_w;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.w   = s1;\
      src0.v   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_vidx_t s0, act_hidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_h;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.h   = s1;\
      src0.v   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_vidx_t s0, act_bidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_b;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.b   = s1;\
      src0.v   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_vidx_t s0) : act_inst_t(p, Y) { \
      fmt[2]   = ot_no;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src0.v   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_sidx_t s0, act_vidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_v;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.v   = s1;\
      src0.s   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_sidx_t s0, act_widx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_w;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.w   = s1;\
      src0.s   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_sidx_t s0, act_hidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_h;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.h   = s1;\
      src0.s   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_sidx_t s0, act_bidx_t s1) : act_inst_t(p, Y) { \
      fmt[2]   = ot_b;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.b   = s1;\
      src0.s   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_sidx_t s0) : act_inst_t(p, Y) { \
      fmt[2]   = ot_no;\
      fmt[1]   = ot_s;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src0.s   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_widx_t s0) : act_inst_t(p, Y) { \
      fmt[2]   = ot_w;\
      fmt[1]   = ot_no;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src1.w   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_hidx_t s0) : act_inst_t(p, Y) { \
      fmt[2]   = ot_h;\
      fmt[1]   = ot_no;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src1.h   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_vidx_t d, act_bidx_t s0) : act_inst_t(p, Y) { \
      fmt[2]   = ot_b;\
      fmt[1]   = ot_no;\
      fmt[0]   = ot_v;\
      src2.bin = Z;\
      src0.b   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_widx_t s0) : act_inst_t(p, Y) { \
      fmt[2]   = ot_w;\
      fmt[1]   = ot_no;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.w   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_hidx_t s0) : act_inst_t(p, Y) { \
      fmt[2]   = ot_h;\
      fmt[1]   = ot_no;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.h   = s0;\
      dst.s    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_bidx_t s0) : act_inst_t(p, Y) { \
      fmt[2]   = ot_b;\
      fmt[1]   = ot_no;\
      fmt[0]   = ot_s;\
      src2.bin = Z;\
      src1.b   = s0;\
      dst.s    = d;\
    }\
  };
BINARY(act_inst_add, fu_alu0, op_add)
BINARY(act_inst_sub, fu_alu0, op_sub)
BINARY(act_inst_rsub, fu_alu0, op_rsub)
BINARY(act_inst_min, fu_alu0, op_min)
BINARY(act_inst_max, fu_alu0, op_max)
BINARY(act_inst_relun, fu_alu0, op_relun)
BINARY(act_inst_eq, fu_alu0, op_eq)
BINARY(act_inst_neq, fu_alu0, op_neq)
BINARY(act_inst_gt, fu_alu0, op_gt)
BINARY(act_inst_gte, fu_alu0, op_gte)
BINARY(act_inst_lt, fu_alu0, op_lt)
BINARY(act_inst_lte, fu_alu0, op_lte)
BINARY(act_inst_band, fu_alu0, op_band)
BINARY(act_inst_bor, fu_alu0, op_bor)
BINARY(act_inst_bxor, fu_alu0, op_bxor)
BINARY(act_inst_select, fu_alu0, op_select)
BINARY(act_inst_asr, fu_alu0, op_asr)
BINARY(act_inst_lsr, fu_alu0, op_lsr)
BINARY(act_inst_sl, fu_alu0, op_sl)
BINARY(act_inst_fadd, fu_alu0, op_fadd)
BINARY(act_inst_fsub, fu_alu0, op_fsub)
BINARY(act_inst_frsub, fu_alu0, op_frsub)
BINARY(act_inst_fmin, fu_alu0, op_fmin)
BINARY(act_inst_fmax, fu_alu0, op_fmax)
BINARY(act_inst_faddf, fu_alu0, op_faddf)
BINARY(act_inst_fsubf, fu_alu0, op_fsubf)
BINARY(act_inst_frsubf, fu_alu0, op_frsubf)
BINARY(act_inst_fminf, fu_alu0, op_fminf)
BINARY(act_inst_fmaxf, fu_alu0, op_fmaxf)
BINARY(act_inst_feq, fu_alu0, op_feq)
BINARY(act_inst_fneq, fu_alu0, op_fneq)
BINARY(act_inst_fgt, fu_alu0, op_fgt)
BINARY(act_inst_fgte, fu_alu0, op_fgte)
BINARY(act_inst_flt, fu_alu0, op_flt)
BINARY(act_inst_flte, fu_alu0, op_flte)
BINARY(act_inst_frelun, fu_alu0, op_frelun)
BINARY(act_inst_frelunf, fu_alu0, op_frelunf)
BINARY(act_inst_eadd, fu_alu0, op_eadd)
BINARY(act_inst_mirror, fu_alu0, op_mirror)
BINARY(act_inst_replic, fu_alu0, op_replic)
BINARY(act_inst_renorm, fu_alu0, op_renorm)
#undef BINARY
#define REDUCE(X, Y) \
  struct X : public act_inst_t {\
    inline X(act_pred_t p, act_vidx_t d, act_vidx_t s0) : act_inst_t(p, fu_alu0) { \
      fmt[2]   = ot_op;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_v;\
      src1.una = Y;\
      src0.v   = s0;\
      dst.v    = d;\
    }\
    inline X(act_pred_t p, act_sidx_t d, act_vidx_t s0) : act_inst_t(p, fu_alu0) { \
      fmt[2]   = ot_op;\
      fmt[1]   = ot_v;\
      fmt[0]   = ot_s;\
      src1.una = Y;\
      src0.v   = s0;\
      dst.s    = d;\
    }\
  };
REDUCE(act_inst_raddv,  op_raddv)
REDUCE(act_inst_randv,  op_randv)
REDUCE(act_inst_rorv,   op_rorv)
REDUCE(act_inst_rmaxv,  op_rmaxv)
REDUCE(act_inst_rminv,  op_rminv)
REDUCE(act_inst_rmpyv,  op_rmpyv)
REDUCE(act_inst_raddc,  op_raddc)
REDUCE(act_inst_randc,  op_randc)
REDUCE(act_inst_rorc,   op_rorc)
REDUCE(act_inst_rmaxc,  op_rmaxc)
REDUCE(act_inst_rminc,  op_rminc)
#undef REDUCE
struct act_inst_mpyh : public act_inst_t {
  inline act_inst_mpyh(act_pred_t p, act_vidx_t d, act_vidx_t s0, act_vidx_t s1)
    : act_inst_t(p, fu_mul0) {
    fmt[2]   = ot_v;
    fmt[1]   = ot_v;
    fmt[0]   = ot_v;
    src2.bin = op_mpyh;
    src1.v   = s1;
    src0.v   = s0;
    dst.v    = d;
  }
  inline act_inst_mpyh(act_pred_t p, act_vidx_t d, act_vidx_t s0, act_hidx_t s1)
    : act_inst_t(p, fu_mul0) {
    fmt[2]   = ot_h;
    fmt[1]   = ot_v;
    fmt[0]   = ot_v;
    src2.bin = op_mpyh;
    src1.h   = s1;
    src0.v   = s0;
    dst.v    = d;
  }
};
struct act_inst_mpyb : public act_inst_t {
  inline act_inst_mpyb(act_pred_t p, act_vidx_t d, act_vidx_t s0, act_vidx_t s1)
    : act_inst_t(p, fu_mul0) {
    fmt[2]   = ot_v;
    fmt[1]   = ot_v;
    fmt[0]   = ot_v;
    src2.bin = op_mpyb;
    src1.v   = s1;
    src0.v   = s0;
    dst.v    = d;
  }
  inline act_inst_mpyb(act_pred_t p, act_vidx_t d, act_vidx_t s0, act_hidx_t s1)
    : act_inst_t(p, fu_mul0) {
    fmt[2]   = ot_h;
    fmt[1]   = ot_v;
    fmt[0]   = ot_v;
    src2.bin = op_mpyb;
    src1.h   = s1;
    src0.v   = s0;
    dst.v    = d;
  }
};
struct act_inst_mpy : public act_inst_t {
  inline act_inst_mpy(act_pred_t p, act_vidx_t d, act_vidx_t s0, act_vidx_t s1)
    : act_inst_t(p, fu_mul0) {
    fmt[2]   = ot_v;
    fmt[1]   = ot_v;
    fmt[0]   = ot_v;
    src2.bin = op_mpy;
    src1.v   = s1;
    src0.v   = s0;
    dst.v    = d;
  }
  inline act_inst_mpy(act_pred_t p, act_vidx_t d, act_vidx_t s0, act_widx_t s1)
    : act_inst_t(p, fu_mul0) {
    fmt[2]   = ot_w;
    fmt[1]   = ot_v;
    fmt[0]   = ot_v;
    src2.bin = op_mpy;
    src1.w   = s1;
    src0.v   = s0;
    dst.v    = d;
  }
};
}  // namespace npu_act::uc::v200
#endif  // NPU_ACT_COMMON_NPU_ACT_ISA_HPP_
