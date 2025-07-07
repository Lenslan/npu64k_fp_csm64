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
 * tensor_buffer_inline.hpp
 *
 * File defining the implementation specific tensor buffer types
 *
 */

#ifndef SHARED_COMMON_TENSOR_API_IMPL_TENSOR_BUFFER_INLINE_HPP_
#define SHARED_COMMON_TENSOR_API_IMPL_TENSOR_BUFFER_INLINE_HPP_
namespace tensor::v200 {
  // buffer_t
  // constructors
  template<typename T> inline buffer_t<T>::buffer_t() {
    len  = 0;
    base = nullptr;
  }
  template<typename T> inline buffer_t<T>::buffer_t(const buffer_t<T>& b) = default;
  template<typename T> inline buffer_t<T>& buffer_t<T>::operator=(const buffer_t<T>& b) = default;
  template<typename T> inline buffer_t<T>::buffer_t(T* b, size_t s) {
    base = b;
    len = s;
  }
  // buffer pointer increment
  template<typename T> inline T* buffer_t<T>::incr_wrap(T* p, poffset_t o) const {
    // increment
    p += o;
    // wrap
    if (p < base || p > (base+len-1)) {
      p += o >= 0 ? -len : len;
    }
    return p;
  }
  // access attributes
  template<typename T> inline T* buffer_t<T>::get_base() const {
    return base;
  }
  template<typename T> inline void buffer_t<T>::set_base(T* b) {
    base = b;
  }
  template<typename T> inline size_t buffer_t<T>::get_size() const {
    return len;
  }
  template<typename T> inline void buffer_t<T>::set_size(size_t l) {
    len = l;
  }
  template<typename T> inline T buffer_t<T>::read(T * ptr, int o) const {
    auto dp = incr_wrap(ptr, o);
    return mem_read(dp);
  }

  template<typename T> inline T* buffer_t<T>::read(T * ptr_dest, int o, T * ptr_src, size_t l) {
    auto dp = incr_wrap(ptr_src, o);
    return mem_read(ptr_dest, dp, l);
  }

  template<typename T> inline void buffer_t<T>::write(T * ptr, int o, const T & v) {
    auto dp = incr_wrap(ptr, o);
    mem_write(dp, v);
  }

  template<typename T> inline void buffer_t<T>::write(T * ptr_dest, int o
                                                                  , const T * ptr_src, size_t l) {
    auto dp = incr_wrap(ptr_dest, o);
    mem_write(dp, ptr_src, l);
  }

  template<typename T>
  template<template<typename> class BD>
  inline void buffer_t<T>::deep_copy(BD<T>& d) const {  // NOLINT [runtime/references]
    size_t d_sz = d.get_size(); (void)d_sz;
    size_t s_sz = get_size();
    assert(d_sz == s_sz);

    T v;
    T *pd = d.get_base();
    T *ps = get_base();
    for (size_t i=0; i < s_sz; i++) {
      v = read(ps, i);
      d.write(pd, i, v);
    }
  }

  template<typename T>
  template<typename TD>
  inline buffer_t<TD> buffer_t<T>::split(size_t l) {
    buffer_t<TD>    r;
    T*      b = get_base();
    size_t sz = get_size();
    size_t a_sz = l;
    // size_t a_sz = (l+15)/16;
    assert((a_sz < sz) && (0 == (l&0x0f)));

    // the new buffer from the head
    r.set_base(reinterpret_cast<TD *>(b));
    r.set_size(a_sz);

    // remain buffer
    uint8_t *pnew_base = reinterpret_cast<uint8_t *>(b)+a_sz;
    set_base(reinterpret_cast<T *>(pnew_base));
    set_size(sz-a_sz);

    return r;
  }

  // xbuffer_t
  // constructors
  template<typename T> inline xbuffer_t<T>::xbuffer_t() {
    len  = 0;
    base = nullptr;
  }
  template<typename T> inline xbuffer_t<T>::xbuffer_t(const xbuffer_t<T>& b) = default;
  template<typename T> inline xbuffer_t<T>& xbuffer_t<T>::operator=(const xbuffer_t<T>& b)
                                                                                      = default;
  template<typename T> inline xbuffer_t<T>::xbuffer_t(T* b, size_t s) {
    base = b;
    len = s;
  }
  // buffer pointer increment
  template<typename T> inline T* xbuffer_t<T>::incr_wrap(T* p, poffset_t o) const {
    // increment
    p += o;
    // wrap
    if (p < base || p > (base+len-1)) {
      p += o >= 0 ? -len : len;
    }
    return p;
  }
  // access attributes
  template<typename T> inline T* xbuffer_t<T>::get_base() const {
    return base;
  }
  template<typename T> inline void xbuffer_t<T>::set_base(T* b) {
    base = b;
  }
  template<typename T> inline size_t xbuffer_t<T>::get_size() const {
    return len;
  }
  template<typename T> inline void xbuffer_t<T>::set_size(size_t l) {
    len = l;
  }
  template<typename T> inline T xbuffer_t<T>::read(T * ptr, int o) const {
    auto dp = incr_wrap(ptr, o);
    return *dp;
  }
  template<typename T> inline void xbuffer_t<T>::write(T * ptr, int o, const T & v) {
    auto dp = incr_wrap(ptr, o);
    // cout << "ptr: " << std::noshowbase << std::internal << std::hex << std::setfill('0')
    //      << "0x" << std::setw(8) << reinterpret_cast<uint64_t>(ptr) << " dp: 0x" << std::setw(8)
    //      << reinterpret_cast<uint64_t>(dp) << "\n";
    *dp = v;
  }

  template<typename T>
  template<template<typename> class BD>
  inline void xbuffer_t<T>::deep_copy(BD<T>& d) const {  // NOLINT [runtime/references]
    size_t d_sz = d.get_size(); (void)d_sz;
    size_t s_sz = get_size();
    assert(d_sz >= s_sz);
    // assert(d_sz==s_sz);

    T v;
    T *pd = d.get_base();
    T *ps = get_base();
    for (size_t i=0; i < s_sz; i++) {
      v = read(ps, i);
      d.write(pd, i, v);
    }
  }

  template<typename T>
  template<typename TD>
  inline xbuffer_t<TD> xbuffer_t<T>::split(size_t l) {
    xbuffer_t<TD>    r;
    T*      b = get_base();
    size_t sz = get_size();
    // size_t a_sz = l;
    size_t a_sz = ((l+15)/16) * 16;  // FIXME(jlrao): alloc always aligned to 16
    // cout << "a_sz=" << a_sz << " sz=" << sz << " l=" << l << endl;
    assert((a_sz < sz) && (0 == (a_sz&0x0f)));

    // the new buffer from the head
    r.set_base(reinterpret_cast<TD *>(b));
    r.set_size(a_sz);

    // remain buffer
    uint8_t *pnew_base = reinterpret_cast<uint8_t *>(b)+a_sz;
    set_base(reinterpret_cast<T *>(pnew_base));
    set_size(sz-a_sz);

    return r;
  }

  #if 0
  // utility functions
  template<typename T, template<typename> class BD = buffer_t
    , template<typename> class BS = buffer_t> inline void
    copy_buffer(BD<T>& d, const BS<T>& s) {  // NOLINT [runtime/references]
    size_t d_sz = d.get_size(); (void)d_sz;
    size_t s_sz = s.get_size();
    assert(d_sz >= s_sz);

    T v;
    T *pd = d.get_base();
    T *ps = s.get_base();
    for (size_t i=0; i < s_sz; i++) {
      v = s.read(ps, i);
      d.write(pd, i, v);
    }
  }

  template<typename TD, typename TS = TD, template<typename> class BD = xbuffer_t
    , template<typename> class BS = xbuffer_t>
    inline BD<TD> split_buffer(BS<TS>& s, size_t l) {  NOLINT [runtime/references]
    BD<TD>    r;
    TS*     b = s.get_base();
    size_t sz = s.get_size();
    size_t a_sz = l;
    // size_t a_sz = (l+15)/16;
    assert(a_sz < sz);

    // the new buffer from the head
    r.set_base(reinterpret_cast<TD *>(b));
    r.set_size(a_sz);

    // remain buffer
    uint8_t *pnew_base = reinterpret_cast<uint8_t *>(b)+a_sz;
    s.set_base(reinterpret_cast<TS *>(pnew_base));
    s.set_size(sz-a_sz);

    return r;
  }
  #endif

}  // namespace tensor::v200

#endif  // SHARED_COMMON_TENSOR_API_IMPL_TENSOR_BUFFER_INLINE_HPP_
