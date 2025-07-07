/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2021 Synopsys, Inc.                                   **/
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
 * tensor_mem.hpp
 *
 * File defining tensor memory instance data type
 *
 */

#ifndef SHARED_COMMON_TENSOR_API_IMPL_TENSOR_MEM_HPP_
#define SHARED_COMMON_TENSOR_API_IMPL_TENSOR_MEM_HPP_

#ifdef SYSTEMC
#include <cstring>
#include <memory>
#include <vector>
#endif
#ifdef RTL_DPI
  #ifndef NPU_RTL_SIMULATOR
    #define NPU_RTL_SIMULATOR 0
  #endif
  #if NPU_RTL_SIMULATOR==1
    #include "xrun_hdrs.h"
  #elif NPU_RTL_SIMULATOR==2
    #include "sv2c.h"
  #else 
    #include "vc_hdrs.h"              // NOLINT [build/include_subdir]
  #endif
#endif
#ifdef RTL_ARC
#include <arc/arc_intrinsics.h>
#endif

#include <iomanip>
#include <ostream>

#include "arc_program.hpp"  // NOLINT [build/include_subdir]

namespace npu {
//
// Global physical memory pointer class used for accessing global memory
//
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
template<typename T>
class globalptr_t {
 public:
  globalptr_t() = default;
  globalptr_t(const globalptr_t<T>&) = default;
  inline globalptr_t(T* p) {  // NOLINT [runtime/explicit]
    ptr = reinterpret_cast<uint64_t>(p);
  }
  inline globalptr_t(uint64_t p) {  // NOLINT [runtime/explicit]
    ptr = p;
  }
  inline T* get_ptr() const {
    // return a byte pointer
    return reinterpret_cast<T*>(ptr);
  }
  inline uint64_t get_raw() const {
    // return a 64b raw pointer
    return ptr;
  }
  inline void set_raw(uint64_t v) {
    // update the 64b raw pointer
    ptr = v;
  }
  /*
  volatile globalptr_t& operator=(const globalptr_t& lhs) volatile {
    ptr = lhs.ptr;
    return *this;
  }
  */
  inline globalptr_t<T>& operator++() {
    // pre-increment
    ptr += sizeof(T);
    return *this;
  }
  inline globalptr_t<T> operator++(int) {
    // post-increment
    globalptr_t<T> r(*this);
    ptr += sizeof(T);
    return r;
  }
  inline globalptr_t<T>& operator+=(tensor::v200::poffset_t o) {
    // in-place add
    ptr += (int64_t)o*sizeof(T);
    return *this;
  }
  inline globalptr_t<T> operator+(tensor::v200::poffset_t o) const {
    // add
    globalptr_t<T> r(*this);
    r.ptr += (int64_t)o*sizeof(T);
    return r;
  }
  inline globalptr_t<T>& operator+=(uint32_t o) {
    // in-place add
    ptr += (int64_t)o*sizeof(T);
    return *this;
  }
  inline globalptr_t<T> operator+(uint32_t o) const {
    // add
    globalptr_t<T> r(*this);
    r.ptr += o*sizeof(T);
    return r;
  }
  inline globalptr_t<T>& operator--() {
    // pre-decrement
    ptr -= sizeof(T);
    return *this;
  }
  inline globalptr_t<T> operator--(int) {
    // post-decrement
    globalptr_t<T> r(*this);
    ptr -= sizeof(T);
    return r;
  }
  inline globalptr_t<T>& operator-=(tensor::v200::poffset_t o) {
    // in-place subtract
    ptr -= (int64_t)o*sizeof(T);
    return *this;
  }
  inline globalptr_t<T> operator-(tensor::v200::poffset_t o) const {
    // add
    globalptr_t<T> r(*this);
    r.ptr -= (int64_t)o*sizeof(T);
    return r;
  }
  inline globalptr_t<T>& operator-=(uint32_t o) {
    // in-place subtract
    ptr -= o*sizeof(T);
    return *this;
  }
  inline globalptr_t<T> operator-(uint32_t o) const {
    // add
    globalptr_t<T> r(*this);
    r.ptr -= o*sizeof(T);
    return r;
  }
  inline bool operator<(const globalptr_t<T>& p) const {
    return ptr < p.ptr;
  }
  inline bool operator>(const globalptr_t<T>& p) const {
    return ptr > p.ptr;
  }

 private:
  uint64_t ptr;
} __PALIGNED(__AN);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif
template<typename T>
inline std::ostream& operator<<(std::ostream &os, const globalptr_t<T>& p) {
  std::ios state0(nullptr);
  state0.copyfmt(os);
  os << std::noshowbase << std::internal << std::hex << std::setfill('0')
     << std::setw(16) << p.get_raw();
  os.copyfmt(state0);
  return os;
}
}  // namespace npu

namespace tensor::v200 {
//
// Local memory pointer class used for accessing a local memory
//
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(push, 1)
#endif
template<typename T>
class localptr_t {
 public:
  localptr_t() = default;
  localptr_t(const localptr_t<T>&) = default;
  inline localptr_t(T* p) {  // NOLINT [runtime/explicit]
    ptr = reinterpret_cast<uint64_t>(p) / sizeof(T);
  }
  inline explicit localptr_t(uint16_t p) {
    ptr = p;
  }
  inline uint64_t get_ptr() const {
    // return a 64b byte pointer, relative to the memory base
    return ((uint64_t)ptr)*sizeof(T);
  }
  inline uint16_t get_raw() const {
    // return a 16b raw pointer
    return ptr;
  }
  inline localptr_t<T>& operator++() {
    // pre-increment
    ++ptr;
    return *this;
  }
  inline localptr_t<T> operator++(int) {
    // post-increment
    localptr_t<T> r(*this);
    ptr++;
    return r;
  }
  inline localptr_t<T>& operator+=(aoffset_t o) {
    // in-place add
    ptr += o;
    return *this;
  }
  inline localptr_t<T> operator+(aoffset_t o) const {
    // add
    localptr_t<T> r(*this);
    r += o;
    return r;
  }
  inline localptr_t<T>& operator--() {
    // pre-decrement
    --ptr;
    return *this;
  }
  inline localptr_t<T> operator--(int) {
    // post-decrement
    localptr_t<T> r(*this);
    ptr--;
    return r;
  }
  inline localptr_t<T>& operator-=(aoffset_t o) {
    // in-place subtract
    ptr -= o;
    return *this;
  }
  inline localptr_t<T> operator-(aoffset_t o) const {
    // sub
    localptr_t<T> r(*this);
    r -= o;
    return r;
  }

 private:
  uint16_t ptr;
} __PALIGNED(2);
#ifdef NPU_TAPI_ST_PACK_PRAGMA
#pragma pack(pop)
#endif

template<typename T>
inline std::ostream& operator<<(std::ostream &os, const localptr_t<T>& p) {
  std::ios state0(nullptr);
  state0.copyfmt(os);
  os << std::noshowbase << std::internal << std::hex << std::setfill('0')
     << std::setw(4) << p.get_raw();
  os.copyfmt(state0);
  return os;
}
#ifdef SYSTEMC
// functions to operate on modelled memory
template<typename T> inline T mem_read(const T* ptr) {
  T v{};
  npu::mem_read(reinterpret_cast<unsigned char*>(&v),
                reinterpret_cast<const unsigned char*>(ptr), sizeof(T));
  return v;
}

template<typename T> inline T* mem_read(T* ptr_dest, const T* ptr_src, size_t nmemb) {
  return npu::mem_read(reinterpret_cast<unsigned char*>(ptr_dest),
                       reinterpret_cast<const unsigned char*>(ptr_src), nmemb * sizeof(T));
}

template<typename T> inline void mem_write(T* ptr, const T& v) {
  npu::mem_write(reinterpret_cast<unsigned char*>(ptr),
                 reinterpret_cast<const unsigned char*>(&v), sizeof(T));
}

template<typename T> inline void mem_write(T* ptr_dest, const T* ptr_src, size_t nmemb) {
  npu::mem_write(reinterpret_cast<unsigned char*>(ptr_dest),
                 reinterpret_cast<const unsigned char*>(ptr_src), nmemb * sizeof(T));
}

template<typename T> inline T* mem_get_ptr(T* ptr) {
  return reinterpret_cast<T*>(npu::dget_ptr(reinterpret_cast<unsigned char*>(ptr)));
}

template<typename T> inline void dealloc(T* ptr) {
}

//
// MMIO read&write from/to modelled memory
//
template<typename T> inline T mmio_read(T* p) {
  npu::run_cycles(1);
  return *p;
}

template<typename T> inline void mmio_write(T* p, const T& d) {
  *p = d;
  npu::run_cycles(1);
}
#endif  // SYSTEMC

#if defined(RTL_DPI) || defined(HOST_ARC) || defined(HOST_SYSTEMC)
  //
  // Memory read&write
  //
  template<typename T> T mem_read(const T* p);
  template<typename T> void mem_write(T* p, const T& d);
  void mem_barrier();

  //
  // MMIO read&write
  //
  template<typename T> inline T mmio_read(T* p) {
    return mem_read(p);
  }
  template<typename T> inline void mmio_write(T* p, const T& d) {
    mem_write(p, d);
  }
#endif

#ifdef RTL_ARC
  //
  // Memory read&write
  //
  template<typename T> T mem_read(const T* p) {
    return *p;
  }
  template<typename T> T* mem_read(T* dest, const T* src, size_t nmemb) {
    return memcpy(dest, src, sizeof(T) * nmemb);
  }

  template<typename T> void mem_write(T* p, const T& d) {
#if defined(NPU_MLI_TAPI_V2)
    memcpy(p, &d, sizeof(d));
#else
    *p = d;
#endif
  }
  template<typename T> void mem_write(T* dest, const T* src, size_t nmemb) {
    memcpy(dest, src, sizeof(T) * nmemb);
  }

  inline void mem_barrier() {
    // data memory barrier instruction, to order write operations
    _dmb(6);
  }

  //
  // MMIO read&write from/to modelled memory
  //
  template<typename T> inline T mmio_read(T* p) {
    _Uncached volatile T* pv = reinterpret_cast<_Uncached volatile T*>(p);
    return *pv;
  }
  template<typename T> inline npu::globalptr_t<T> mmio_read(npu::globalptr_t<T>* p) {
    npu::globalptr_t<T> gp_d;
    gp_d.set_raw(_ldd_di(p));  // LDD.di : Load Double, direct (uncached);
    return gp_d;
  }
  template<> inline uint64_t mmio_read(uint64_t* p) {
    // LDD.di : Load Double, direct (uncached)
    return _ldd_di(reinterpret_cast<_Uncached uint64_t*>(p));
  }
  template<> inline uint32_t mmio_read(uint32_t* p) {
    uint32_t res;
    __asm__ __volatile__("    ld.di %0, [%1]" :"=r"(res) :"r"(p));
    return res;
  }

  //template<typename T> inline void mmio_write(T* p, const T& d) {
  //  _Uncached uint32_t* pu(reinterpret_cast<_Uncached uint32_t* >(p));
  //  const uint32_t *pd(reinterpret_cast<const uint32_t *>(&d));
  //  mem_barrier();
  //  for (int i=0; i<sizeof(T); i+=4) { //FIXME:
  //      *pu++ = *pd++;
  //  }
  //  //*pu = d;
  //}

  template<typename T> inline void mmio_write(T* p, const T& d) {
    _Uncached volatile T* pv = reinterpret_cast<_Uncached volatile T*>(p);
    // cout << "mmio_write<T> " << std::hex << p << " = 0x" << d << endl;
    mem_barrier();
    *pv = d;
  }
  template<typename T> inline void mmio_write(
      npu::globalptr_t<T>* gp_p,
      const npu::globalptr_t<T>& gp_d
      ) {
    // Specialized function for globalptr_t since it doesn't support
    // a cast to volatile + force STD instruction
    _Uncached uint64_t* p = reinterpret_cast<_Uncached uint64_t*>(gp_p);
    uint64_t  d = gp_d.get_raw();
    // cout << "mmio_write<globalptr_t> " << std::hex << p << " = 0x" << d << endl;
    mem_barrier();
    _std_di(d, p);
  }
  template<> inline void mmio_write(uint64_t* p, const uint64_t& d) {
    // cout << "mmio_write<uint64_t> " << std::hex << p << " = 0x" << d << endl;
    mem_barrier();
    // STD.di : Store Double, direct (uncached)
    _std_di(d, reinterpret_cast<_Uncached uint64_t*>(p));
  }
  template<> inline void mmio_write(uint32_t* p, const uint32_t& d) {
    // cout << "mmio_write<uint32_t> " << std::hex << p << " = 0x" << d << endl;
    mem_barrier();
    __asm__ __volatile__("    st.di %0, [%1]" : :"r"(d), "r"(p));
  }
  /*
  template<typename T> inline void mmio_write(localptr_t<T>* lp_p, const localptr_t<T>& lp_d) {
    uint64_t* p = reinterpret_cast<uint64_t*>(lp_p);
    uint64_t  d = lp_d.get_ptr();
    cout << "mmio_write<localptr_t> " << std::hex << p << " = 0x" << d << endl;
    mem_barrier();
    _std_di(d,p);
  }
  */

  // template<typename T> T dmem_read(const T* p)           { return *p; }
  // template<typename T> void dmem_write(T* p, const T& d) { *p = d;    }
  // template<typename T> inline T* dmem_get_ptr(T* ptr)    { return ptr;}
  // template<typename T> inline void ddealloc(T* ptr)      {            }
#endif  // RTL_ARC
}  // namespace tensor::v200

#endif  // SHARED_COMMON_TENSOR_API_IMPL_TENSOR_MEM_HPP_
