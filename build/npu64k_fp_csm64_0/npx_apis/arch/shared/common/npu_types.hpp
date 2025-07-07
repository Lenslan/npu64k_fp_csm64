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
 * npu_types.h
 *
 * File defining global datatypes for the NPU
 *
 */

#ifndef SHARED_COMMON_NPU_TYPES_HPP_
#define SHARED_COMMON_NPU_TYPES_HPP_

#include <assert.h>
#include <list>
#include <iostream>
#include <array>
#include <string>

// include configuration
#include "npu_config.hpp"  // NOLINT [build/include_subdir]
#include "npu_defines.hpp"  // NOLINT [build/include_subdir]

// tensor API
#include "tensor.hpp"  // NOLINT [build/include_subdir]

//
// All identifiers related to the NPU go into namespace npu
//
namespace npu {

using namespace tensor::v200;  // NOLINT [build/namespaces]

// shallow packing mode
typedef enum { 
  pack_mode_i16_e = 0, // no spatial packing, i16
  pack_mode_i8_e  = 1, // v2i8 spatial packing
  pack_mode_i4_e  = 2  // v4i4 spatial packing
} pack_mode_t;


// trace timestamp
typedef uint32_t timestamp_t;

// local physical ptr in memories
typedef uint16_t lptr_t;
typedef struct {
  lptr_t   base;
  uint16_t len;
} __PACKED lbuf_t;


//
// Task masks
//
typedef int16_t tmask_t;

//
// Wrap the offset
//
inline aoffset_t vbuf_wrap(aoffset_t ofs, aoffset_t sz) {
  int32_t wsz = (uint16_t)sz;
  if (ofs < 0) {
    while (ofs <= -wsz) {
      // negative offset beyond size
      ofs += wsz;
    }
  } else {
    while (ofs >= wsz) {
      // positive offset beyond size
      ofs -= wsz;
    }
  }
  return ofs;
}
inline poffset_t pbuf_wrap(poffset_t ofs, poffset_t sz) {
  if (ofs < 0) {
    while (ofs <= -sz) {
      // negative offset beyond size
      ofs += sz;
    }
  } else {
    while (ofs >= sz) {
      // positive offset beyond size
      ofs -= sz;
    }
  }
  return ofs;
}

//
// Sign/zero extension of feature-maps and coefficients
//
const int sextshamt = 8*sizeof(int16_t)-8;
const int uextmask  = 0x00ff;
inline int16_t ext(bool sgn, bool mode8b, tensor::v200::pix_t p) {
  return sgn ? ((int16_t)(p << sextshamt)) >> sextshamt
            : ((int16_t)p & uextmask);
}
inline int16_t ext(bool sgn, tensor::v200::coef_t p) {
  return sgn ? ((int16_t)(p << sextshamt)) >> sextshamt
             : ((int16_t)p & uextmask);
}

//
// VM Feature-map buffer descriptor
//
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
template<typename T> struct buf_t {
  buf_t() = default;
  buf_t(const buf_t&) = default;
  inline buf_t(tensor::v200::localptr_t<T> b, tensor::v200::aoffset_t l) {
    base = b;
    len  = l;
  }
  template <bool neg_check_only = false>
  inline tensor::v200::localptr_t<T> incr_wrap(tensor::v200::localptr_t<T> p, tensor::v200::aoffset_t o) const {
    if (neg_check_only) {
      int32_t pi = ((uint32_t)p.get_raw())+o;
      if (pi < (int32_t)base.get_raw()) {
        pi += len;
      }
      tensor::v200::localptr_t<T> r((uint16_t)pi);
      return r;
    } else {
      uint32_t en = ((uint32_t)base.get_raw())+len-1;
      uint32_t pi = ((uint32_t)p.get_raw())+o;
      tensor::v200::localptr_t<T> r((uint16_t)pi);
      if (pi < base.get_raw() || pi > en) {
        if (o >= 0) {
          r -= len;
        } else {
          r += len;
        }
      }
      return r;
    }
  }
  tensor::v200::localptr_t<T> base;
  uint16_t      len;
} __PALIGNED(2);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

//
// XM Feature-map buffer descriptor
//
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
template<typename T> struct xm_buf_t {
  xm_buf_t() = default;
  inline xm_buf_t(globalptr_t<T> b, tensor::v200::poffset_t l) {
    base = b;
    len  = l;
  }
  template <bool neg_check_only = false>
  inline globalptr_t<T> incr_wrap(globalptr_t<T> p, tensor::v200::poffset_t o) const {
    if (neg_check_only) {
      int64_t pi = (p.get_raw())+o;
      if (pi < (int64_t)base.get_raw()) {
        pi += (uint32_t)len;
      }
      globalptr_t<T> r((uint64_t)pi);
      return r;
    } else {
      globalptr_t<T> en = base+(uint32_t)len-1;
      p+=o;
      if (p < base || p > en) {
        if (o >= 0) {
          return p - (uint32_t)len;
        } else {
          return p + (uint32_t)len;
        }
      }
      return p;
    }
  }
  inline globalptr_t<T> get_base() const {
    return base;
  }
  inline unsigned get_size() const {
    return len;
  }
  globalptr_t<T> base;
  tensor::v200::poffset_t      len;
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

//
// Generic accelerator memory mapped I/O interface
//

// IP tag register
typedef enum {
  id_type_conv,
  id_type_act,
  id_type_idma,
  id_type_odma,
  id_type_stu=0x07,
  id_type_conv_flt=0x08,
  id_type_act_alu2=0x0a,
  id_type_act_str0=0x0b,
  id_type_act_alu2_str0=0x0c
} id_type_t;

struct id_reg_t {
  uint8_t    min;   // minor revision
  uint8_t    maj;   // major revision
  uint16_t   tp;    // accelerator type as in above enum
};

// struct definiting the accelerator memory mapped registers
template<typename T> struct ctrl_dma_regs {
  // 00: IP tag, read-only
  id_reg_t             id;
  // 04: Halt, soft-reset, power management control (L1 clock gating)
  uint32_t             ctrl;
  // 08: Activity status, read-only
  uint32_t             status;
  // 0c: interrupt enable
  uint32_t             int_enable;
  // 10: interrupt status (level), read-only
  uint32_t             int_status;
  // 14: set interrupt status, auto clear
  uint32_t             int_set;
  // 18: clear interrupt status, auto clear
  uint32_t             int_clear;
  // 1c:
  uint32_t             reserved0;
  // 20: count successful HLAPI descriptor reads
  uint32_t             cnt_issue;
  // 24: count successful HLAPI completions
  uint32_t             cnt_finish;
  // 28-2c:
  uint64_t             reserved1;
  // 30: start accelerator
  uint32_t             issue;
  // 34:
  uint32_t             reserved2;
  // 38: tail of descriptor queue, read-only
  globalptr_t<T>       tail;
  // 40: add single descriptor, write-only
  globalptr_t<T>       single;
  // 48: head of list to be appended to queue
  globalptr_t<T>       concat_head;
  // 50: tail of list to be appended to queue
  globalptr_t<T>       concat_tail;
  // 58: prefetch descriptor
  globalptr_t<T>       prefetch;
  // 60: HLAPI specific registers NR= sizeof(hlapi.i)/4
  //   60: hlapi_i_common.next
  //   68: hlapi_i_common.ctrl
  //   6c: hlapi_i_common.id
  //   70..70+(4*(NR-1)): hlapi_i_w32[1..NR-1]
  // 70+4*NR: hlapi_io_cycles
  // 74+4*NR: hlapi_io_count
  // 78+4*NR: hlapi_o_res
  // 7c+4*NR: hlapi_o_status
  T                    hlapi;
  inline ctrl_dma_regs() {
    // reset
    status      = 0;
    ctrl        = 0;
    int_enable  = 0;
    int_status  = 0;
    int_clear   = 0;
    int_set     = 0;
    cnt_issue   = 0;
    cnt_finish  = 0;
    issue       = 0;
    tail        = globalptr_t<T>(nullptr);
    single      = globalptr_t<T>(nullptr);
    prefetch    = globalptr_t<T>(nullptr);
    concat_head = globalptr_t<T>(nullptr);
    concat_tail = globalptr_t<T>(nullptr);
  }
};

template<typename T> struct packed_ctrl_dma_regs {
  // 00: IP tag, read-only
  id_reg_t             id;
  // 04: Halt, soft-reset, power management control (L1 clock gating)
  uint32_t             ctrl;
  // 08: Activity status, read-only
  uint32_t             status;
  // 0c: interrupt enable
  uint32_t             int_enable;
  // 10: interrupt status (level), read-only
  uint32_t             int_status;
  // 14: set interrupt status, auto clear
  uint32_t             int_set;
  // 18: clear interrupt status, auto clear
  uint32_t             int_clear;
  // 1c:
  uint32_t             reserved0;
  // 20: count successful HLAPI descriptor reads
  uint32_t             cnt_issue;
  // 24: count successful HLAPI completions
  uint32_t             cnt_finish;
  // 28-2c:
  uint64_t             reserved1;
  // 30: start accelerator
  uint32_t             issue;
  // 34:
  uint32_t             reserved2;
  // 38: tail of descriptor queue, read-only
  globalptr_t<T>       tail;
  // 40: add single descriptor, write-only
  globalptr_t<T>       single;
  // 48: head of list to be appended to queue
  globalptr_t<T>       concat_head;
  // 50: tail of list to be appended to queue
  globalptr_t<T>       concat_tail;
  // 58: prefetch descriptor
  globalptr_t<T>       prefetch;
  // 60: HLAPI specific registers NR= sizeof(hlapi.i)/4
  //   60: hlapi_i_common.next
  //   68: hlapi_i_common.ctrl
  //   6c: hlapi_i_common.id
  //   70..70+(4*(NR-1)): hlapi_i_w32[1..NR-1]
  // 70+4*NR: hlapi_io_cycles
  // 74+4*NR: hlapi_io_count
  // 78+4*NR: hlapi_o_res
  // 7c+4*NR: hlapi_o_status
  T                    hlapi;
} __PACKED;

//
// Tensor reporting
//
template<size_t R, template<typename> class B = tensor::v200::xbuffer_t>
void report(ostream& os, const tensor::v200::tensor_t<tensor::v200::vyixacc_t, R, B>& t) {
  tensor::v200::const_tensor_iterator_t<tensor::v200::vyixacc_t, R, B> it(t);
  tensor::v200::shape<R> idx;
  for (int r = 0; r < static_cast<int>(R); r++) idx[r] = 0;
  do {
    os << "REPORT [";
    for (int r = static_cast<int>(R) - 1; r > 0; r--)
      os << idx[r] << ",";
    os << idx[0] << "]" << it.read() << std::endl;;
    for (int r = 0; r < static_cast<int>(R); r++) {
      idx[r]++;
      if (idx[r] == t.get_dim(r)) {
        idx[r] = 0;
      } else {
        break;
      }
    }
  } while (it.next());
}

template<size_t R, template<typename> class B = tensor::v200::xbuffer_t>
void report(ostream& os, const tensor::v200::tensor_t<tensor::v200::ixpix_t, R, B>& t) {
  tensor::v200::const_tensor_iterator_t<tensor::v200::ixpix_t, R, B> it(t);
  bool busy;
  do {
    os << "REPORT (";
    for (int i = static_cast<int>(R) - 1; i > 0; i--)
      os << it.get_index(i) << ",";
    os << it.get_index(0) << ") ";
    os << " " << it.read();
    busy = it.next();
    os << std::endl;
  } while (busy);
}
}  // namespace npu
#endif  // SHARED_COMMON_NPU_TYPES_HPP_
