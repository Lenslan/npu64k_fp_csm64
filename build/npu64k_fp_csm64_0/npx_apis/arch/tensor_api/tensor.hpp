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
 * tensor.hpp
 *
 * File defining tensor type and iterators
 *
 */

#ifndef TENSOR_INCLUDED
#define TENSOR_INCLUDED

#include "tensor_basic_types.hpp"
#include "tensor_mem.hpp"
#include "tensor_buffer.hpp"
#include "tensor_mem_alloc.hpp"


namespace tensor::v200 {
  //
  // define a tensor of rank R mapped on a memory buffer of data type T
  //
  template<typename T, size_t R, template<typename> class B=buffer_t> class tensor_t {
  public:
    template<typename T1, size_t R1, template<typename> class B1> friend ostream& operator<<(ostream&, const tensor_t<T1, R1, B1>&);
    //template<typename, size_t> friend class tensor_t;
    inline tensor_t() = default;
    inline tensor_t(const tensor_t<T,R,B>& c) = default;
    inline tensor_t(const B<T>& b) {
      // try to create a linear tensor
      size_t sz = b.get_size();
      buf = b;
      ptr = b.get_base();
      for (int r = 1; r < (int)R; r++) {
        dims[r] = 1;
        offs[r] = 0;
      }
      if (sz >= (32*1024)) {
        // risk of overflow, split into groups (of 16)
        assert (R > 1);
        size_t sz0 = 1;
        size_t sz1 = sz;
        if (sz % 16 == 0) { // Branch for the weights blob, which is always modulo 16
          sz0 = 16;
          sz1 = sz / 16;
        }
        if (sz1 >= (32*1024)) {
          // check remainder of prime or power of 2 numbers
          int primes[] = {2,3,5,7,8,11,13,16,17,19,23,29,31,32,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173};
          int idx = 39;
          do {
            if ((sz1%primes[idx]) == 0) {
              break;
            }
            idx--;
          } while (idx > 0);
          assert((sz1%primes[idx]) == 0);
          sz0 *= primes[idx];
          sz1 /= primes[idx];
        }
        dims[0] = sz0;
        dims[1] = sz1;
        offs[0] = 1;
        offs[1] = dims[0];
      } else {
        dims[0] = sz;
        offs[0] = 1;
      }
    }
    inline tensor_t(const B<T>& b, const shape<R>& d) {
      // create a tensor mapped onto buffer b with dimensions d
      buf  = b;
      dims = d;
      int l = 1;
      for (int r = 0; r < (int)R; r++) {
        offs[r] = l;
        l *= d[r];
      }
      ptr = buf.get_base();
      assert_size();
    }
    inline tensor_t(const B<T>& b, const shape<R>& d, const array<poffset_t,R>& o) {
      // create a tensor mapped onto buffer b with dimensions d with custom offsets e.g. to minimize bank conflicts
      buf  = b;
      dims = d;
      offs = o;
      ptr = buf.get_base();
      assert_size();
    }
    inline tensor_t(const shape<R>& d, const array<poffset_t,R>& o) {
      // create a tensor with dimensions d with custom offsets
      dims = d;
      offs = o;
    }
    // explicit cast to other datatype
    template <typename NT>
    explicit operator tensor_t<NT,R,B>() const {
      assert((offs[0] == 1 || sizeof(NT) == sizeof(T)) && "inner dimension must have unit stride");
      tensor_t<NT,R,B> r;
      r.buf  = *(B<NT>*)(void*)&buf;
      r.ptr  = (NT*)(void*)ptr;
      r.dims = dims;
      r.offs = offs;
      if (sizeof(NT) > sizeof(T)) {
        assert(sizeof(NT) % sizeof(T) == 0);
        assert(r.dims[0] % sizeof(NT) == 0);
        int f = sizeof(NT) / sizeof(T);
        r.dims[0] = r.dims[0] / f;
        for (int i = 0; i < R; i++) {
          r.offs[i] = r.offs[i] * f;
        }
        r.buf.set_size(r.buf.get_size() / f);
      } else if (sizeof(NT) < sizeof(T)) {
        assert(sizeof(T) % sizeof(NT) == 0);
        int f = sizeof(T) / sizeof(NT);
        r.buf.set_size(r.buf.get_size() * f);
        r.dims[0] = r.dims[0] * f;
        for (int i = 1; i < (int)R; i++) {
          r.offs[i] = r.offs[i] * f;
        }
      }
      return r;
    }
    inline void reset() {
      ptr = get_base();
    }
    inline void shift(axis_t a, aoffset_t o) {
      // shift a slice over the underlying buffer
      assert(a < (int)R);
      assert_buf();
      int t = offs[a] * o;
      ptr = buf.incr_wrap(ptr, t);
    }
    inline void shift(const shape<R>& s) {
      // shift a slice over the underlying buffer
      ptr = buf.incr_wrap(ptr, get_offset(s));
    }
    inline tensor_t<T,R,B> slice(const shape<R>& b, const shape<R>& d) const {
      // create a tensor slice from a base coordinate b with dimensions d
      assert_buf();
      tensor_t<T,R,B> v(buf);
      // determine pointer offset to base of new buffer
      v.offs = offs;                       // keep per axis offset to next element
      int o = 0;
      for (int r = 0; r < (int)R; r++) {
        assert(b[r] >= 0);                 // axis base should be within tensor
        assert(d[r] >= 0);                 // axis size should be positive or 0
        o += ((int)b[r]) * ((int)offs[r]);
        v.dims[r] = d[r];                  // per axis size
      }
      // fields in new tensor
      v.ptr  = buf.incr_wrap(ptr, o);      // pointer to base of slice
      return v;
    }
    inline tensor_t<T,R,B> transpose(const shape<R>& s) const {
      assert_buf();
      // create a transposed tensor, reordering the dimensions
      tensor_t<T,R,B> v(buf);
      // change order of axes
      int c = 0;                           // just for checking
      for (int r = 0; r < (int)R; r++) {
        assert(s[r] >= 0 && s[r] < (int)R);    // s selects an axis
        assert((c & (1<<s[r])) == 0);     // axis can only be selected once
        c |= (1<<s[r]);
        v.dims[r] = dims[s[r]];            // reorder dimension
        v.offs[r] = offs[s[r]];            // reorder offset per axis
      }
      // keep pointer
      v.ptr  = ptr;                        // same base pointer
      return v;
    }
    inline tensor_t<T,R,B> reverse(axis_t a) const {
      assert_buf();
      // reverse the ordering across the selected axis
      tensor_t<T,R,B> v(buf);
      assert(a < (int)R);
      // fields in new tensor
      int o = offs[a] * ((uint16_t)(dims[a]-1));
      v.ptr  = buf.incr_wrap(ptr, o);     // move pointer to last element in selected axis
      v.dims = dims;                       // same per axis size
      v.offs = offs;                       // keep per axis offset to next element
      v.offs[a] = -offs[a];                // negate offset in selected axis
      return v;
    }
    inline tensor_t<T,R,B> broadcast(const shape<R>& s) const {
      // broadcast a tensor so axes with dimension 1 get replicated to match the input shape s
      tensor_t<T,R,B> v(*this);
      for (int r = 0; r < (int)R; r++) {
        assert((dims[r] == 1 || dims[r] == s[r]) && "cannot broadcast if axis is > 1");
        if (dims[r] == 1 && s[r] > 1) {
          // broadcast
          v.dims[r] = s[r];
          v.offs[r] = 0;
        }
      }
      return v;
    }
    template<size_t A> tensor_t<T,A,B> reshape(const shape<A>& d) const {
      assert_buf();
      return tensor_t<T,A,B>(*this, d);
    }
    inline tensor_t<T,R+1,B> split(axis_t a, aoffset_t d) const {
      // return a new tensor with an extra dimension, splitting axis a into d chunks
      assert(a < (int)R);
      assert_buf();
      tensor_t<T,R+1,B> v(buf);
      v.ptr = ptr;
      int s = 0;
      for (int r = 0; r < (int)R; r++) {
        if (r < a || r > a) {
          // copy lower or higher dimensions
          v.dims[s] = dims[r];
          v.offs[s] = offs[r];
          s++;
        } else { // r == a
          // split axis in 2, [dim]=[d][dim/d]
          assert(dims[r]%d == 0);
          v.dims[s] = dims[r]/d;
          v.offs[s] = offs[r];
          s++;
          v.dims[s] = d;
          v.offs[s] = (dims[r]/d)*offs[r];
          s++;
        }
      }
      return v;
    }
    inline tensor_t<T,R-1,B> join(axis_t a) const {
      // join axis a and a+1, inverse of split, only works if offset is adjacent
      assert(a < (int)R);
      assert_buf();
      tensor_t<T,R-1,B> v(buf);
      v.ptr = ptr;
      int s = 0;
      assert(a<(R-1) && "cannot join last dimension");
      assert(offs[a+1] == (offs[a]*dims[a]) && "offsets non contiguous");
      for (int r = 0; r < (int)R; r++) {
        if (r != a && r != a+1) {
          // copy lower or higher dimensions
          v.dims[s] = dims[r];
          v.offs[s] = offs[r];
          s++;
        } else if (r == a) {
          v.dims[a] = dims[a] * dims[a+1];
          v.offs[a] = offs[a];
          s++;
        }
      }
      return v;
      
    }
    inline tensor_t<T,R-1,B> reduce(axis_t a) const {
      // return a new tensor of rank R-1, remove axis a
      assert(a < (int)R);
      assert_buf();
      tensor_t<T,R-1,B> v(buf);
      v.ptr = ptr;
      int s = 0;
      for (int r = 0; r < (int)R; r++) {
        if (r != a) {
          // copy lower or higher dimensions
          v.dims[s] = dims[r];
          v.offs[s] = offs[r];
          s++;
        } else { // r == a
          assert(dims[r] == 1);
        }
      }
      return v;
    }
    inline void next(shape<R>& p) const {
      // update multi-dimensional iterator
      for (int r = 0; r < (int)R; r++) {
        p[r]++;
        if (p[r] == dims[r]) {
          // end of axis, reset axis iterator to 0 and continue with next axis
          p[r] = 0;
        } else {
          // not at end of axis, break
          break;
        }
      }
    }
    inline T read(const shape<R>& p) const {
      // determine offset from pointer
      assert_buf();
      int o = 0;
      for (int r = 0; r < (int)R; r++) {
        assert(p[r] >= 0 && p[r] < (uint16_t)dims[r]);
        o += p[r] * offs[r];
      }
      return buf.read(ptr, o);
    }
    inline void write(const shape<R>& p, const T& d) {
      // determine offset from pointer
      assert_buf();
      int o = 0;
      for (int r = 0; r < (int)R; r++) {
        assert(p[r] >= 0 && p[r] < (uint16_t)dims[r]);
        o += p[r] * offs[r];
      }
      buf.write(ptr, o, d);
    }
    inline poffset_t get_offset_last(axis_t a) const {
      // return pointer offset from last element on axis a-1 to first element on axis a
      assert(a < (int)R);
      int l = 0;
      for (int r = 0; r < a; r++) {
        l -= offs[r] * ((uint16_t)(dims[r]-1));
      }
      return l + offs[a];
    }
    inline poffset_t get_offset(axis_t a) const {
      // return pointer offset on axis a
      assert(a < (int)R);
      return offs[a];
    }
    inline poffset_t get_offset(const shape<R>& o) const {
      // get the pointer offset for a position
      int l = 0;
      for (int r = 0; r < (int)R; r++) {
        l += o[r] * offs[r];
      }
      return l;
    }
    inline void resize(axis_t a, aoffset_t v) {
      assert(a < (int)R);
      dims[a] = v;
      assert_size();
    }
    inline aoffset_t get_dim(axis_t a) const {
      // return dimension size
      assert(a < (int)R);
      return dims[a];
    }
    inline T* get_ptr() const {
      return ptr;
    }
    inline void incr_ptr(poffset_t o) {
      ptr = buf.incr_wrap(ptr, o);
    }
    inline T* get_base() const {
      assert_buf();
      return buf.get_base();
    }
    inline const shape<R>& get_shape() const {
      return dims;
    }
    inline size_t get_tens_size() const {
      return get_shape_size<R>(dims);
    }
    inline size_t get_size() const {
      assert_buf();
      return buf.get_size();
    }
    inline void set_buffer(const B<T>& b) {
      buf = b;
      ptr = buf.get_base();
    }
    inline B<T> get_buffer() const {
      return buf;
    }
  protected:
    inline void assert_buf() const {
      assert(buf.get_size() != 0);
    }
    inline void assert_size() const {
#ifdef ENABLE_SIZE_ASSERT
      // disabled because dimensions may be bigger than size in case of broadcast
      int l = 1;
      for (int r = 0; r < (int)R; r++) {
        l *= (uint16_t)get_dim(r);
      }
      assert(l >= 0 && l <= (int)buf.get_size());
      for (int r = 0; r < (int)R; r++) {
        assert(offs[r] >= -(int)buf.get_size() && offs[r] <= (int)buf.get_size());
      }
#endif
    }
  public: //NOTE: change to public for easy debugging
    template<size_t S> tensor_t(const tensor_t<T,S,B>& c, const shape<R>& d) {
      // reshaping constructor, can only work if all dimensions are contiguous in memory
      buf = c.buf;
      assert_buf();
      int ls = 1;
      for (int s = 0; s < (int)S; s++) {
        assert((c.dims[s] == 1 && c.offs[s] == 0) || (/*c.dims[s] != 1 && */c.offs[s] == ls));
        ls *= (uint16_t)c.dims[s];
      }
      (void)ls;
      int lr = 1;
      for (int r = 0; r < (int)R; r++) {
        offs[r] = lr;
        dims[r] = d[r];
        lr *= d[r];
      }
      ptr = c.ptr;
      assert(ls == lr);
      assert_size();
    }
    B<T>               buf;  // associated cyclic buffer
    T*                 ptr;  // pointer to base of the cyclic buffer
    shape<R>           dims; // per axis size
    array<poffset_t,R> offs; // per axis offset to next element
  };


  //
  // Iterate over tensor
  //
  template<typename T, size_t R, template<typename> class B=buffer_t> class tensor_iterator_t {
  public:
    inline tensor_iterator_t(tensor_t<T,R,B>& t) : tens(t) {
      for (int r = 0; r < (int)R; r++) {
        pos[r] = 0;
      }
    }
    inline iter_mask_t isbusy() const {
      int d = 0;
      for (int r = 0; r < (int)R; r++) {
        d |= pos[r] != 0 ? 1<<r : 0;
      }
      return d;
    }
    inline bool next() {
      tens.next(pos);
      return isbusy() != 0;
    }
    inline T read() const {
      return tens.read(pos);
    }
    inline void write(const T& d) {
      return tens.write(pos, d);
    }
    inline aoffset_t get_index(axis_t i) const {
      assert(i < (int)R);
      return pos[i];
    }
    inline iter_mask_t first() const {
      int r = 0;
      for (int i = 0; i < (int)R; i++) {
        if (pos[i] == 0) {
          r |= (1<<i);
        }
      }
      return r;
    }
    inline iter_mask_t last() const {
      int r = 0;
      for (int i = 0; i < (int)R; i++) {
        if (pos[i] == (tens.get_dim(i)-1)) {
          r |= (1<<i);
        }
      }
      return r;
    }
  private:
    tensor_t<T,R,B>& tens; // associated tensor
    shape<R>         pos;  // position in tensor
  };


  //
  // Iterate over const tensor
  //
  template<typename T, size_t R, template<typename> class B=buffer_t> class const_tensor_iterator_t {
  public:
    inline const_tensor_iterator_t(const tensor_t<T,R,B>& t) : tens(t) {
      for (int r = 0; r < (int)R; r++) {
        pos[r] = 0;
      }
    }
    inline iter_mask_t isbusy() const {
      int d = 0;
      for (int r = 0; r < (int)R; r++) {
        d |= pos[r] != 0 ? 1<<r : 0;
      }
      return d;
    }
    inline bool next() {
      tens.next(pos);
      return isbusy() != 0;
    }
    inline T read() const {
      return tens.read(pos);
    }
    inline aoffset_t get_index(axis_t i) const {
      assert(i >= 0 && i < (int)R);
      return pos[i];
    }
    inline iter_mask_t first() const {
      int r = 0;
      for (int i = 0; i < (int)R; i++) {
        if (pos[i] == 0) {
          r |= (1<<i);
        }
      }
      return r;
    }
    inline iter_mask_t last() const {
      int r = 0;
      for (int i = 0; i < (int)R; i++) {
        if (pos[i] == (tens.get_dim(i)-1)) {
          r |= (1<<i);
        }
      }
      return r;
    }
  private:
    const tensor_t<T,R,B>& tens; // associated tensor
    shape<R>               pos;  // position in tensor
  };


  ///////////////////////////////////////////////////////////////////////////////
  //
  // SW convenience functions
  //
  ///////////////////////////////////////////////////////////////////////////////

  //
  // Padding
  //
  template<typename T,int R> T do_pad(
                                      const T&        vl,   // non-padded value
                                      const T&        pd,   // padded value
                                      const shape<R>& lim,  // padding limits
                                      const shape<R>& pos   // padding position
                                      ) {
    bool b = false;
    for (int r = 0; r < R; r++) {
      b |= (pos[r] < 0) || (pos[r] > lim[r]);
    }
    return b ? pd : vl;
  }

  //
  // Software tensor copy with optional reshape
  //
  template<typename T, size_t D, size_t S, template<typename> class BD=buffer_t, template<typename> class BS=buffer_t> void copy(tensor_t<T,D,BD>& d, const tensor_t<T,S,BS>& s) {
    tensor_iterator_t<T,D,BD>       di(d);
    const_tensor_iterator_t<T,S,BS> si(s);
    bool done;
    do {
      di.write(si.read());
      done  = di.next();
      done |= si.next();
    } while(done);
    assert(!(di.isbusy() || si.isbusy())); // size should be the same
  }

  //
  // Report tensor
  //
  template<typename T, size_t R, template<typename> class B=buffer_t> ostream& operator<<(ostream& os, const tensor_t<T,R,B>& a) {
    os << "{ptr:" << a.ptr << ",[";
    for (int r = (int)R-1; r >= 1; r--) {
      os << a.dims[r] << ",";
    }
    os << a.dims[0] << "],[";
    for (int r = (int)R-1; r >= 1; r--) {
      os << a.offs[r] << "+";
    }
    os << a.offs[0] << "]}";
    return os;
  }
  template<typename T, size_t R, template<typename> class B=buffer_t> void report(ostream& os, const tensor_t<T,R,B>& a, int npl=0) {
    // print to output stream with a given number of elements per line
    const_tensor_iterator_t<T,R,B> it(a);
    npl = npl <= 0 ? a.get_dim(0) : npl;
    int c = npl;
    do {
      if (c == npl) {
        c = 0;
        os << "REPORT (";
        for (int i = 0; i < (int)R-1; i++)
          os << it.get_index(i) << ",";
        os << it.get_index(R-1) << ") ";
      }
      os << " " << it.read();
      c++;
      if (c == npl) {
        os << endl;
      }
    } while (it.next());
  }
}

//
// Include implementation specific datatypes
//
#include "tensor_inline.hpp"

//
// Some convernience functions
//
namespace tensor::v200 {
// convert feature-map opaque array to standard pix_t [D][H][W][Grp*C] layout
template<template<typename> class BD=buffer_t, template<typename> class BS=buffer_t>
void convertfrom(tensor_t<pix_t,4,BD>& o, const impl_spec_container_t<BS>& b);

// convert feature-map opaque array to standard int16_t [D][H][W][Grp*C] layout
template<template<typename> class BD, template<typename> class BS>
void convertfrom(tensor_t<int16_t, 4, BD>& o  // NOLINT [runtime/references]
                 , const impl_spec_container_t<BS>& b);

// convert feature-map opaque array to standard fp16_t [D][H][W][Grp*C] layout
template<template<typename> class BD, template<typename> class BS>
void convertfrom(tensor_t<fp_e5m10_t, 4, BD>& o  // NOLINT [runtime/references]
                 , const impl_spec_container_t<BS>& b);

// convert feature-map opaque array to standard bf16_t [D][H][W][Grp*C] layout
template<template<typename> class BD, template<typename> class BS>
void convertfrom(tensor_t<fp_e8m7_t, 4, BD>& o  // NOLINT [runtime/references]
                 , const impl_spec_container_t<BS>& b);

// convert from implementation dependent to acc_t [d][h][w][no][msb/lsb] tensor
template<template<typename> class BD=buffer_t, template<typename> class BS=buffer_t>
void convertfrom(tensor_t<acc_t,5,BD>&, const acc_buf_impl_t<BS>&);

// convert accumutalor to floating-point
template<template<typename> class BD=buffer_t, template<typename> class BS=buffer_t>
void convertfrom(tensor_t<fp_e8m23_t, 4, BD>& o, const acc_buf_impl_t<BS>& b);

// convert from implementation dependent fully-connected to acc_t [no][msb/lsb] tensor
template<template<typename> class BD=buffer_t, template<typename> class BS=buffer_t>
void convertfrom(tensor_t<acc_t,2,BD>&, const acc_buf_impl_t<BS>&);

// convert feature-map opaque array from standard pix_t [D][H][W][Grp*C] layout
template<template<typename> class BD=buffer_t, template<typename> class BS=buffer_t>
void convertto(impl_spec_container_t<BD>& b, const tensor_t<pix_t,4,BS>& o);

// convert from acc_t [d][h][w][no][msb/lsb] tensor to impl dependent
template<template<typename> class BD=buffer_t, template<typename> class BS=buffer_t>
void convertto(acc_buf_impl_t<BD>& o, const tensor_t<acc_t,5,BS>& b);

// convert from fp_e8m23_t [d][h][w][no] tensor to impl dependent
template<template<typename> class BD=buffer_t, template<typename> class BS=buffer_t>
void convertto(acc_buf_impl_t<BD>& o, const tensor_t<fp_e8m23_t,4,BS>& b);

template<template<typename> class BD, template<typename> class BS>
void convertto(impl_spec_container_t<BD>& b, const tensor_t<fp_e5m10_t, 4, BS>& o);

template<template<typename> class BD, template<typename> class BS>
void convertto(impl_spec_container_t<BD>& b, const tensor_t<fp_e8m7_t, 4, BS>& o);
}
#endif
