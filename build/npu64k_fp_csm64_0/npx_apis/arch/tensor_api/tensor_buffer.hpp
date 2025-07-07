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
 * tensor_buffer.hpp
 *
 * File defining tensor buffer data type
 *
 */

#ifndef TENSOR_BUFFER_INCLUDED
#define TENSOR_BUFFER_INCLUDED

namespace tensor::v200 {
  template<typename T> class buffer_t {
  public:
    // constructors
    buffer_t();
    buffer_t(const buffer_t&);
    buffer_t& operator=(const buffer_t&);
    buffer_t(T*, size_t);
    // buffer pointer increment
    T* incr_wrap(T* p, poffset_t o) const;
    // attributes
    T* get_base() const;
    void set_base(T*);
    size_t get_size() const;
    void set_size(size_t);
    // read from an offset
    T read(T* ptr, int o) const;
    T* read(T * ptr_dest, int o, T * ptr_src, size_t l);
    // write to an offset
    void write(T * ptr, int o, const T & v);
    void write(T * ptr_dest, int o, const T * ptr_src, size_t l);
    // deep_copy a buffer's contents to another one
    template<template<typename> class BD>
    void deep_copy(BD<T>& d) const;
    // split a buffer
    template<typename TD=T> buffer_t<TD> split(size_t l);
  private:
#include "tensor_buffer_private.hpp"
  };

  template<typename T> class xbuffer_t{
  public:
    // constructors
    xbuffer_t();
    xbuffer_t(const xbuffer_t&);
    xbuffer_t& operator=(const xbuffer_t&);
    xbuffer_t(T*, size_t);
    // xbuffer_t pointer increment
    T* incr_wrap(T* p, poffset_t o) const;
    // attributes
    T* get_base() const;
    void set_base(T*);
    size_t get_size() const;
    void set_size(size_t);
    // read from an offset
    T read(T* ptr, int o) const;
    // write to an offset
    void write(T * ptr, int o, const T & v);
    // deep_copy a buffer's contents to another one
    template<template<typename> class BD>
    void deep_copy(BD<T>& d) const;
    // split a buffer
    template<typename TD=T> xbuffer_t<TD> split(size_t l);
  private:
#include "tensor_buffer_private.hpp"
  };

}

//
// Include implementation specific datatypes
//
#include "tensor_buffer_inline.hpp"
#endif
