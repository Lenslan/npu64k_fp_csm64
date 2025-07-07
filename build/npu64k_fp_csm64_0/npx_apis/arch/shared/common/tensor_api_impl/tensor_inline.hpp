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
 * tensor_inline.hpp
 *
 * File defining the implementation specific tensor types
 *
 */

#ifndef SHARED_COMMON_TENSOR_API_IMPL_TENSOR_INLINE_HPP_
#define SHARED_COMMON_TENSOR_API_IMPL_TENSOR_INLINE_HPP_

#include "tensor_hw_config.hpp"

//
// All identifiers related to the tensor API go into namespace tensor::v200
//
namespace tensor::v200 {

// convert fixed point {fract, shamt} to floating point scale
inline float scl_fix2flt(int16_t fract, uint8_t shamt) {
  int32_t s = (int32_t)shamt - 47;
  float r = (float)fract;
  if (s > 0) {
    while (s != 0) {
      r = r * 2.0;
      s--;
    }
  }
  else if (s < 0) {
    while (s != 0) {
      r = r / 2.0;
      s++;
    }
  }
  return r;
}


//
// Accumulator data type
//
template<template<typename> class B = buffer_t>
struct acc_buf_data_t : public tensor_t<ixacc_t,6,B> {
  // constructors
  inline acc_buf_data_t() = default;
  inline acc_buf_data_t(const acc_buf_data_t<B>&) = default;
  // tensor assign
  acc_buf_data_t operator=(const tensor_t<ixacc_t,6,B>& d) {
    *static_cast<tensor_t<ixacc_t,6,B>*> (this) = d;
    return *this;
  }
  // assignment from vyixacc_t tensor (deprecated)
  acc_buf_data_t operator=(const tensor_t<vyixacc_t,5,B>& d) {
    B<ixacc_t> b(reinterpret_cast<ixacc_t*>(d.get_base()), d.get_size()<<TNSVSIZEL2);
    shape<5> s(d.get_shape());
    shape<6> s0;
    s0[0] = TNSVSIZE;
    for (int i = 0; i < 5; i++) {
      s0[i+1] = s[i];
    }
    *this = tensor_t<ixacc_t,5,B>(b,s0);
    return *this;
  }
  // cast to vyixacc_t (deprecated)
  inline operator tensor_t<vyixacc_t,5,B>() const {
    B<vyixacc_t> b(reinterpret_cast<vyixacc_t*>(tensor_t<ixacc_t,6,B>::get_base()), tensor_t<ixacc_t,6,B>::get_size()>>TNSVSIZEL2);
    shape<6> s(tensor_t<ixacc_t,6,B>::get_shape());
    shape<5> s0;
    for (int i = 0; i < 5; i++) {
      s0[i] = s[i+1];
    }
    return tensor_t<vyixacc_t,5,B>(b, s0);
  }
  inline operator tensor_t<vyixacc_t,5,B>() {
    B<vyixacc_t> b(reinterpret_cast<vyixacc_t*>(tensor_t<ixacc_t,6,B>::get_base()), tensor_t<ixacc_t,6,B>::get_size()>>TNSVSIZEL2);
    shape<6> s(tensor_t<ixacc_t,6,B>::get_shape());
    shape<5> s0;
    for (int i = 0; i < 5; i++) {
      s0[i] = s[i+1];
    }
    return tensor_t<vyixacc_t,5,B>(b, s0);
  }
};

//
// Implementation specific accumulator tensor type ixacc_t [C][D][W][H][onn/msb/lsb][VSIZE] in AM
//
template<template<typename> class B = buffer_t> struct acc_buf_impl_t {
  inline acc_buf_impl_t() = default;
  inline acc_buf_impl_t(const acc_buf_impl_t<B>&) = default;
  inline acc_buf_impl_t(mem_alloc_t& v, const shape<5>& s) {  // NOLINT [runtime/references]
    shape<6> s0;
    s0[0] = TNSVSIZE;
    for (int i = 0; i < 5; i++) {
      s0[i+1] = s[i];
    }
    B<ixacc_t> buf;
    v.alloc(buf, get_shape_size(s0));
    data = tensor_t<ixacc_t,6,B>(buf, s0);
  }
  localptr_t<ixacc_t> get_ptr() const {
    return data.get_ptr();
  }
  amptr_t get_vptr() const {
    localptr_t<ixacc_t> lp(data.get_ptr());
    assert ((lp.get_raw()%TNSVSIZE) == 0 && "unaligned pointer");
    return lp.get_raw()>>TNSVSIZEL2;
  }
  // deprecated vector read function
  inline vyixacc_t vread(const shape<5>& s) {
    vyixacc_t r;
    for (aoffset_t v = 0; v < aoffset_t(TNSVSIZE); v++) {
      r[v] = data.read({v, s[0],s[1],s[2],s[3],s[4]});
    }
    return r;
  }
  acc_buf_data_t<B> data;
};

//
// Optimize the tensor layout in L1 memory and select btween CHW or HCW layout
//
inline void optimize_shape(const shape<4>& shp,
                           shape<4>& offsets,  // NOLINT [runtime/references]
                           size_t& sz,         // NOLINT [runtime/references]
                           double max_over_alloc = 0.3) {
  // default is max 30% overallocation to resolve bank conflicts
  size_t max_cost    = NRND_UP(static_cast<size_t>((1.0+max_over_alloc)*get_shape_size(shp)), 32);
  int    min_overlap = 0x7fffffff;  // default overlapping banks
  sz = 0x7fffffff;
  // W is inner with offset 1, by definition W16 is conflict free
  offsets[1] = 1;

  //
  // Optimize HCW layout
  //
  // C starts after W with tail up to 32
  for (int c = shp[1]; c < shp[1]+32; c++) {
    // channel offset should be odd, so C2W8 stride 2 is conflict free
    if ((shp[0] == 1) || ((c&1) == 1)) {
      // H starts after C with tail up to 32
      for (int h = shp[0]*c; h < shp[0]*c+32; h++) {
        // Starts at odd bank, so R2W8 stride 2 is conflict free
        if ((shp[2] == 1) || ((h&1) == 1)) {
          bool     ok = true;
          uint32_t b  = 0x0;
          // conflict free C4 for DMA
          for (int c4 = 0; c4 < (shp[0] < 4 ? shp[0] : 4); c4++) {
            int o = c4*c;
            int m = 1 << (o%32);
            if ((b&m) != 0)
              ok = false;
            b |= m;
          }
          // conflict free C2W8 for i32o16
          b = 0x0;
          for (int c2 = 0; c2 < (shp[0] < 2 ? shp[0] : 2); c2++) {
            for (int w8 = 0; w8 < (shp[1] < 8 ? shp[1] : 8); w8++) {
              int o = c2*c+w8;
              int m = 1 << (o%32);
              if ((b&m) != 0)
                ok = false;
              b |= m;
            }
          }
          if (ok) {
            // valid configuration
            size_t cost = NRND_UP(h*shp[2]*shp[3], 32);
            // minimize overlap R0C2W8 and R1C2W8
            int overlap = 0;
            for (int c2 = 0; c2 < (shp[0] < 2 ? shp[0] : 2); c2++) {
              for (int w8 = 0; w8 < (shp[1] < 8 ? shp[1] : 8); w8++) {
                int o = h+c2*c+w8;
                int m = 1 << (o%32);
                if ((b&m) != 0)
                  overlap++;
              }
            }
            // weight overlap by number of rows
            overlap *= (shp[2]-1);
            if (shp[0] > 2) {
              // minimize overlap at end of row to next C2
              for (int c2 = 0; c2 < (shp[0] < 2 ? shp[0] : 2); c2++) {
                for (int w8 = 0; w8 < (shp[1] < 8 ? shp[1] : 8); w8++) {
                  int o = 2*c+c2*c+(1-shp[2])*h+w8;
                  int m = 1 << (o%32);
                  if ((b&m) != 0)
                    overlap++;
                }
              }
            }
            if (((cost < sz) || (cost < max_cost)) && (overlap < min_overlap)) {
              // best solution, but max_cost is more important than overlap
              min_overlap = (cost > max_cost) ? 0x7fffffff : overlap;
              offsets[0]  = c;
              offsets[2]  = h;
              offsets[3]  = h*shp[2];
              sz          = cost;
            }
          }
        }
      }
    }
  }
#ifdef ALLOC_DEBUG
  cout << "opt_alloc_hcw: " << shp[0] << "," << shp[1] << "," << shp[2] << "," << shp[3] << " " <<
    offsets[0] << "," << offsets[1] << "," << offsets[2] << "," << offsets[3] << " " <<
    sz << " " << min_overlap << " " << (100*sz)/get_shape_size(shp) << endl;
#endif

  //
  // Optimize CHW layout
  //
  // H starts after W with tail up to 32
  for (int h = shp[1]; h < shp[1]+32; h++) {
    // Starts at odd bank, so R2W8 stride 2 is conflict free
    if ((shp[2] == 1) || ((h&1) == 1)) {
      // C starts after H with tail up to 32
      for (int c = h*shp[2]; c < h*shp[2]+32; c++) {
        // channel offset should be odd, so C2W8 stride 2 is conflict free
        if ((shp[0] == 1) || ((c&1) == 1)) {
          bool     ok = true;
          uint32_t b  = 0x0;
          // conflict free C4 for DMA
          for (int c4 = 0; c4 < (shp[0] < 4 ? shp[0] : 4); c4++) {
            int o = c4*c;
            int m = 1 << (o%32);
            if ((b&m) != 0)
              ok = false;
            b |= m;
          }
          // conflict free C2W8 for i32o16
          b = 0x0;
          for (int c2 = 0; c2 < (shp[0] < 2 ? shp[0] : 2); c2++) {
            for (int w8 = 0; w8 < (shp[1] < 8 ? shp[1] : 8); w8++) {
              int o = c2*c+w8;
              int m = 1 << (o%32);
              if ((b&m) != 0)
                ok = false;
              b |= m;
            }
          }
          if (ok) {
            // valid configuration
            size_t cost = NRND_UP(c*shp[0]*shp[3], 32);
            // minimize overlap R0C2W8 and R1C2W8
            int overlap = 0;
            for (int c2 = 0; c2 < (shp[0] < 2 ? shp[0] : 2); c2++) {
              for (int w8 = 0; w8 < (shp[1] < 8 ? shp[1] : 8); w8++) {
                int o = h+c2*c+w8;
                int m = 1 << (o%32);
                if ((b&m) != 0)
                  overlap++;
              }
            }
            // weight overlap by number of rows
            overlap *= (shp[2]-1);
            if (shp[0] > 2) {
              // minimize overlap at end of row to next C2
              for (int c2 = 0; c2 < (shp[0] < 2 ? shp[0] : 2); c2++) {
                for (int w8 = 0; w8 < (shp[1] < 8 ? shp[1] : 8); w8++) {
                  int o = 2*c+c2*c+(1-shp[2])*h+w8;
                  int m = 1 << (o%32);
                  if ((b&m) != 0)
                    overlap++;
                }
              }
            }
            if (((cost < sz) || (cost < max_cost)) && (overlap < min_overlap)) {
              // best solution, but max_cost is more important than overlap
              min_overlap = (cost > max_cost) ? 0x7fffffff : overlap;
              offsets[0]  = c;
              offsets[2]  = h;
              offsets[3]  = c*shp[0];
              sz          = cost;
            }
          }
        }
      }
    }
  }
#ifdef ALLOC_DEBUG
  cout << "opt_alloc_chw: " << shp[0] << "," << shp[1] << "," << shp[2] << "," << shp[3] << " " <<
    offsets[0] << "," << offsets[1] << "," << offsets[2] << "," << offsets[3] << " " <<
    sz << " " << min_overlap << " " << (100*sz)/get_shape_size(shp) << endl;
#endif

  assert(sz != 0x7fffffff);
}

//
// Opaque container datatype ixpix_t [D][H][W][Grp][C] in VM
//
template<template<typename> class B = buffer_t> struct impl_spec_container_t {
  inline impl_spec_container_t() = default;
  inline impl_spec_container_t(const impl_spec_container_t<B> &) = default;
  inline impl_spec_container_t(mem_alloc_t&    vm,  // feature-map memory NOLINT[runtime/references]
                               const shape<5>& shp,          // shapes
                               bool            opt = false) {  // if true then optimize shape to minimize VM conflicts
    if (opt) {
      // optimize layout
      size_t   opt_size;
      shape<4> req_shp({(aoffset_t)(shp[0]*shp[1]), shp[2], shp[3], shp[4]});
      shape<4> offsets;
      optimize_shape(req_shp, offsets, opt_size);
      B<ixpix_t> buf;
      vm.alloc(buf, opt_size);
      // the tensor is mapped with the W dimension as inner, to minimize conflicts in v8 L1 accesses
      tensor_t<ixpix_t, 5, B> ttns(buf, {shp[2], shp[0], shp[1], shp[3], shp[4]},
                                   {offsets[1], offsets[0], shp[0]*offsets[0], offsets[2], offsets[3]});
      // transpose the dimensions so SW has C as the inner dimension
      data = ttns.transpose({1, 2, 0, 3, 4});                     // data[dep][row][col][grp][chn]
    } else {
      // unoptimized layout
      size_t   eff_size(get_shape_size(shp));
      shape<5> eff_shp(shp);
      B<ixpix_t> buf;
      vm.alloc(buf, eff_size);
      // the tensor is mapped with the W dimension as inner, to minimize conflicts in v8 L1 accesses
      tensor_t<ixpix_t, 5, B> ttns(buf, {eff_shp[2], eff_shp[0], eff_shp[1]
                                       , eff_shp[3], eff_shp[4]});  // ttns[dep][row][grp][chn][col]
      // reduce to requested size
      tensor_t<ixpix_t, 5, B> ttns1(ttns.slice({0, 0, 0, 0, 0}
                                               , {shp[2], shp[0], shp[1], shp[3], shp[4]}));
      // transpose the dimensions so SW has C as the inner dimension
      data = ttns1.transpose({1, 2, 0, 3, 4});                     // data[dep][row][col][grp][chn]
    }
  }
  inline impl_spec_container_t(ixpix_t*        p,           // preallocated memory buffer pointer
                               const shape<5>& shp,          // shapes
                               bool            opt = false) {  // if true then optimize shape to minimize VM conflicts
    if (opt) {
      // optimize layout
      size_t   opt_size;
      shape<4> req_shp({(aoffset_t)(shp[0]*shp[1]), shp[2], shp[3], shp[4]});
      shape<4> offsets;
      optimize_shape(req_shp, offsets, opt_size);
      B<ixpix_t> buf(p, opt_size);
      // the tensor is mapped with the W dimension as inner, to minimize conflicts in v8 L1 accesses
      tensor_t<ixpix_t, 5, B> ttns(buf, {shp[2], shp[0], shp[1], shp[3], shp[4]},
                                   {offsets[1], offsets[0], shp[0]*offsets[0], offsets[2], offsets[3]});
      // transpose the dimensions so SW has C as the inner dimension
      data = ttns.transpose({1, 2, 0, 3, 4});                     // data[dep][row][col][grp][chn]
    } else {
      // unoptimized layout
      size_t   eff_size(get_shape_size(shp));
      shape<5> eff_shp(shp);
      // set preallocated buffer
      B<ixpix_t> buf(p, eff_size);
      // the tensor is mapped with the W dimension as inner, to minimize conflicts in v8 L1 accesses
      tensor_t<ixpix_t, 5, B> ttns(buf, {eff_shp[2], eff_shp[0], eff_shp[1]
                                       , eff_shp[3], eff_shp[4]});  // ttns[dep][row][grp][chn][col]
      // reduce to requested size
      tensor_t<ixpix_t, 5, B> ttns1(ttns.slice({0, 0, 0, 0, 0}
                                               , {shp[2], shp[0], shp[1], shp[3], shp[4]}));
      // transpose the dimensions so SW has C as the inner dimension
      data = ttns1.transpose({1, 2, 0, 3, 4});                     // data[dep][row][col][grp][chn]
    }
  }
  inline impl_spec_container_t slice(const shape<5>& b, const shape<5>& d) const {
    impl_spec_container_t r;
    r.data = data.slice(b, d);
    return r;
  }
  tensor_t<ixpix_t, 5, B> data;         // input tensor   [D][H][W][Grp][C]
};
inline shape<4> impl_spec_shape(const shape<4>& i) {
  shape<4> r(i);
  r[0] = (i[0] + ISIZE - 1) / ISIZE;
  return r;
}

template<typename T, size_t R, template<typename> class BD, template<typename> class BS>
inline void deep_copy_tensor(tensor_t<T, R, BD>&         d  // NOLINT [runtime/references]
                             , const tensor_t<T, R, BS>& s) {
  s.buf.deep_copy(d.buf);
  d.ptr = d.buf.get_base();
  d.dims = s.dims;
  d.offs = s.offs;
}
inline void deep_copy(acc_buf_impl_t<buffer_t>& d  // NOLINT [runtime/references]
                      , const acc_buf_impl_t<xbuffer_t>& s) {
  deep_copy_tensor(d.data, s.data);
}
inline void deep_copy(impl_spec_container_t<buffer_t>& d  // NOLINT [runtime/references]
                      , const impl_spec_container_t<xbuffer_t>& s) {
  deep_copy_tensor(d.data, s.data);
}

//
// Convenience function to convert feature-map opaque array ixpix_t [Grp][C][D][H][W]
// to standard pix_t [D][H][W][Grp*C] layout
//
template<template<typename> class BD, template<typename> class BS>
void convertfrom(tensor_t<pix_t, 4, BD>&            o  // NOLINT [runtime/references]
                 , const impl_spec_container_t<BS>& b) {
  bool active = false;
  const_tensor_iterator_t<ixpix_t, 5, BS> bit(b.data);
  tensor_iterator_t<pix_t, 4, BD> oit(o);
  do {
    for (int w = 0; w < b.data.get_dim(2); w++) {
      aoffset_t c = 0;
      for (int n = 0; n < b.data.get_dim(0)*b.data.get_dim(1); n++) {
        ixpix_t v(bit.read());
        bit.next();
        for (int i = 0; i < ISIZE; i++) {
          if (c < o.get_dim(0) && w < o.get_dim(1)) {
            oit.write(v[i]);
            active = oit.next();
            c++;
          }
        }
      }
    }
  } while (active);
}

//
// Convenience function to convert feature-map opaque array ixpix_t [Grp][C][D][H][W]
// to standard int16_t [D][H][W][Grp*C] layout
//
template<template<typename> class BD, template<typename> class BS>
void convertfrom(tensor_t<int16_t, 4, BD>& o  // NOLINT [runtime/references]
                 , const impl_spec_container_t<BS>& b) {
  bool active = false;
  const_tensor_iterator_t<ixpix_t, 5, BS> bit(b.data);
  tensor_iterator_t<int16_t, 4, BD> oit(o);
  do {
    for (int w = 0; w < b.data.get_dim(2); w++) {
      aoffset_t c = 0;
      for (int n = 0; n < b.data.get_dim(0)*b.data.get_dim(1); n++) {
        ixpix_t v(bit.read());
        bit.next();
        for (int i = 0; i < ISIZE/2; i++) {
          if (c < o.get_dim(0) && w < o.get_dim(1)) {
            int16_t val((int16_t(int8_t(v[2*i+1]))<<8)|uint16_t(uint8_t(v[2*i])));
            oit.write(val);
            active = oit.next();
            c++;
          }
        }
      }
    }
  } while (active);
}

//
// Convenience function to convert feature-map opaque array ixpix_t [Grp][C][D][H][W]
// to standard fp_e5m10_t [D][H][W][Grp*C] layout
//
template<template<typename> class BD, template<typename> class BS>
void convertfrom(tensor_t<fp_e5m10_t, 4, BD>&       o  // NOLINT [runtime/references]
                 , const impl_spec_container_t<BS>& b) {
  bool active = false;
  const_tensor_iterator_t<ixpix_t, 5, BS> bit(b.data);
  tensor_iterator_t<fp_e5m10_t, 4, BD> oit(o);
  do {
    for (int w = 0; w < b.data.get_dim(2); w++) {
      aoffset_t c = 0;
      for (int n = 0; n < b.data.get_dim(0)*b.data.get_dim(1); n++) {
        ixpix_t v(bit.read());
        bit.next();
        for (int i = 0; i < ISIZE/2; i++) {
          if (c < o.get_dim(0) && w < o.get_dim(1)) {
            fp_e5m10_t val((uint16_t)v[2*i+1], (uint16_t)v[2*i]);
            oit.write(val);
            active = oit.next();
            c++;
          }
        }
      }
    }
  } while (active);
}

//
// Convenience function to convert feature-map opaque array ixpix_t [Grp][C][D][H][W]
// to standard fp_e8m7_t [D][H][W][Grp*C] layout
//
template<template<typename> class BD, template<typename> class BS>
void convertfrom(tensor_t<fp_e8m7_t, 4, BD>&        o  // NOLINT [runtime/references]
                 , const impl_spec_container_t<BS>& b) {
  bool active = false;
  const_tensor_iterator_t<ixpix_t, 5, BS> bit(b.data);
  tensor_iterator_t<fp_e8m7_t, 4, BD> oit(o);
  do {
    for (int w = 0; w < b.data.get_dim(2); w++) {
      aoffset_t c = 0;
      for (int n = 0; n < b.data.get_dim(0)*b.data.get_dim(1); n++) {
        ixpix_t v(bit.read());
        bit.next();
        for (int i = 0; i < ISIZE/2; i++) {
          if (c < o.get_dim(0) && w < o.get_dim(1)) {
            fp_e8m7_t val((uint16_t)v[2*i+1], (uint16_t)v[2*i]);
            oit.write(val);
            active = oit.next();
            c++;
          }
        }
      }
    }
  } while (active);
}

//
// Convenience function to convert accumulator opaque array ixacc_t [C][D][W][H][msb/lsb/onn][VSIZE]
// to standard acc_t [D][H][W][C][msb/lsb] layout
//
template<template<typename> class BD, template<typename> class BS>
void convertfrom(tensor_t<acc_t, 5, BD>&     o   // NOLINT [runtime/references]
                 , const acc_buf_impl_t<BS>& b) {
  if (o.get_dim(0) == 2) {
    // double acc
    //  ixacc_t [C][D][W][H][l/msb][VSIZE] --> ixacc_t [D][H][W][VSIZE][l/msb][C]
    tensor_t<ixacc_t, 6, BS> b0(b.data.transpose({5, 1, 0, 3, 2, 4}));
    // output [D][H][W][C][msb/lsb] --> [D][H][W][msb/lsb][C]
    tensor_t<acc_t, 5, BD> o0(o.transpose({1, 0, 2, 3, 4}));
    const_tensor_iterator_t<ixacc_t, 6, BS> iit(b0);
    tensor_iterator_t<acc_t, 5, BD> oit(o0);
    // copy
    for (aoffset_t d = 0; d < b0.get_dim(5); d++) {                     // [D] dimension
      for (aoffset_t h = 0; h < b0.get_dim(4); h++) {                   // [H] dimension
        for (aoffset_t w = 0; w < b0.get_dim(3)*b0.get_dim(2); w++) {   // [W] dimension
          for (aoffset_t mlsb = 0; mlsb < b0.get_dim(1); mlsb++) {      // msb/lsb
            for (aoffset_t c = 0; c < b0.get_dim(0) ; c++) {            // [C]
              ixacc_t v = iit.read();  //  Read the acc vector
              iit.next();
              if (d < o0.get_dim(4) && h < o0.get_dim(3) && w < o0.get_dim(2) && mlsb < o0.get_dim(1)) {
                for (int i = 0; i < ISIZE; i++) {
                  if ((c*ISIZE+i) < o0.get_dim(0)) {
                    oit.write(v[i]);
                    oit.next();
                  }
                }
              }
            }
          }
        }
      }
    }
  } else {
    // onn=1|2
    //   ixacc_t [C][D][W][H][onn][VSIZE] --> ixacc_t [D][H][W][VSIZE][C][onn]
    tensor_t<ixacc_t, 6, BS> b0(b.data.transpose({1, 5, 0, 3, 2, 4}));
    // output [D][H][W][C][1]
    tensor_t<acc_t, 5, BD> o0(o.transpose({1, 0, 2, 3, 4}));
    const_tensor_iterator_t<ixacc_t, 6, BS> iit(b0);
    tensor_iterator_t<acc_t, 5, BD> oit(o);
    // copy
    for (aoffset_t d = 0; d < b0.get_dim(5); d++) {                        // [D] dimension
      for (aoffset_t h = 0; h < b0.get_dim(4); h++) {                      // [H] dimension
        for (aoffset_t w = 0; w < b0.get_dim(3)*b0.get_dim(2); w++) {      // [W] dimension
          for (aoffset_t c = 0; c < b0.get_dim(0)*b0.get_dim(1); c++) {    // [C][onn]
            ixacc_t v = iit.read();  //  Read the acc vector
            iit.next();
            if (d < o0.get_dim(4) && h < o0.get_dim(3) && w < o0.get_dim(2)) {
              for (int i = 0; i < ISIZE; i++) {
                if ((c*ISIZE+i) < o0.get_dim(0)) {
                  oit.write(v[i]);
                  oit.next();
                }
              }
            }
          }
        }
      }
    }
  }
}

//
// Convenience function to convert float accumulator opaque array ixacc_t [C][D][W][H][1][VSIZE]
// to standard float [D][H][W][C] layout
//
template<template<typename> class BD, template<typename> class BS>
void convertfrom(tensor_t<fp_e8m23_t, 4, BD>& o  // NOLINT [runtime/references]
                 , const acc_buf_impl_t<BS>&  b) {
  // 32b accumulator
  // ixacc_t [C][D][W][H][1][VSIZE] --> [1][D][H][W][VSIZE][C]
  tensor_t<ixacc_t,6,BS> b0(b.data.transpose({5, 0, 3, 2, 4, 1}));
  const_tensor_iterator_t<ixacc_t, 6, BS> iit(b0);
  tensor_iterator_t<fp_e8m23_t, 4, BD>    oit(o);
  for (aoffset_t d = 0; d < b0.get_dim(4); d++) {
    for (aoffset_t h = 0; h < b0.get_dim(3); h++) {
      for (aoffset_t w = 0; w < b0.get_dim(2)*b0.get_dim(1); w++) {
        for (aoffset_t c = 0; c < b0.get_dim(0); c++) {
          ixacc_t v = iit.read();
          iit.next();
          if (d < o.get_dim(3) && h < o.get_dim(2) && w < o.get_dim(1)) {
            for (int i = 0; i < ISIZE; i++) {
              if ((c*ISIZE+i) < o.get_dim(0)) {
                fp_e8m23_t a((uint32_t)v[i]);
                oit.write(a);
                oit.next();
              }
            }
          }
        }
      }
    }
  }
}

//
// Convenience function to convert fully connected layer accumulator opaque array
// ixacc_t [C][D=1][W=1][H=1][mlsb][VSIZE] to standard acc_t [C][VSIZE][ISIZE][msb/lsb] layout
//
template<template<typename> class BD, template<typename> class BS>
void convertfrom(tensor_t<acc_t, 2, BD>&       o   // NOLINT [runtime/references]
                 , const acc_buf_impl_t<BS>&   b) {
  // aoffset_t no = o.get_dim(1);
  if (o.get_dim(0) == 2) {
    // 48b accumulator, inner dim is msb/lsb
    // ixacc_t [C][D=1][W=1][H=1][mlsb][VSIZE] -> [D=1][W=1][H=1][mlsb][C][VSIZE]
    // output [C][msb/lsb] -> [msb/lsb][C]
    const_tensor_iterator_t<ixacc_t, 6, BS> iit(b.data.transpose({0, 5, 1, 2, 3, 4}));
    tensor_t<acc_t, 2, BD> oi(o.transpose({1, 0}));
    tensor_iterator_t<acc_t, 2, BD> oit(oi);
    for (aoffset_t mlsb = 0; mlsb < 2; mlsb++) {
      for (aoffset_t c = 0; c < b.data.get_dim(0)*b.data.get_dim(5); c++) {
        ixacc_t v = iit.read();
        iit.next();
        for (int i = 0; i < ISIZE; i++) {
          if ((c*ISIZE+i) < o.get_dim(1)) {
            oit.write(v[i]);
            oit.next();
          }
        }
      }
    }
  } else {
    // onn = 1|2
    const_tensor_iterator_t<ixacc_t, 6, BS> iit(b.data);
    tensor_iterator_t<acc_t, 2, BD> oit(o);
    for (aoffset_t c = 0; c < b.data.get_dim(0)*b.data.get_dim(1)*b.data.get_dim(5); c++) {
      ixacc_t v = iit.read();
      iit.next();
      for (int i = 0; i < ISIZE; i++) {
        if ((c*ISIZE+i) < o.get_dim(1)) {
          oit.write(v[i]);
          oit.next();
        }
      }
    }
  }
}


//
// Convenience function to convert feature-map opaque array ixpix_t [D][H][W][Grp][C]
// from standard pix_t [D][H][W][Grp*C] layout
//
template<template<typename> class BD, template<typename> class BS>
void convertto(impl_spec_container_t<BD>&      b  // NOLINT [runtime/references]
               , const tensor_t<pix_t, 4, BS>& o) {
  bool active = false;
  const_tensor_iterator_t<pix_t, 4, BS> oit(o);
  tensor_iterator_t<ixpix_t, 5, BD> bit(b.data);
  ixpix_t v;
  do {
    for (int w = 0; w < b.data.get_dim(2); w++) {
      aoffset_t c = 0;
      for (int g = 0; g < b.data.get_dim(1); g++) {
        for (int n = 0; n < b.data.get_dim(0); n++) {
          for (int i = 0; i < ISIZE; i++) {
            if (c < o.get_dim(0) && w < o.get_dim(1)) {
              v[i] = oit.read();
              active = oit.next();
              c++;
            } else {
              v[i] = 0;
            }
          }
          bit.write(v);
          bit.next();
        }
      }
    }
  } while (active);
}
template<template<typename> class BD, template<typename> class BS>
void convertto(impl_spec_container_t<BD>&           b  // NOLINT [runtime/references]
               , const tensor_t<fp_e5m10_t, 4, BS>& o) {
  bool active = false;
  const_tensor_iterator_t<fp_e5m10_t, 4, BS> oit(o);
  tensor_iterator_t<ixpix_t, 5, BD> bit(b.data);
  ixpix_t v;
  do {
    for (int w = 0; w < b.data.get_dim(2); w++) {
      aoffset_t c = 0;
      for (int g = 0; g < b.data.get_dim(1); g++) {
        for (int n = 0; n < b.data.get_dim(0); n++) {
          for (int i = 0; i < ISIZE; i+=2) {
            if (c < o.get_dim(0) && w < o.get_dim(1)) {
              fp_e5m10_t t(oit.read());
              v[i] = t.data;
              v[i+1] = t.data>>8;
              active = oit.next();
              c++;
            } else {
              v[i] = 0;
              v[i+1] = 0;
            }
          }
          bit.write(v);
          bit.next();
        }
      }
    }
  } while (active);
}
template<template<typename> class BD, template<typename> class BS>
void convertto(impl_spec_container_t<BD>&          b  // NOLINT [runtime/references]
               , const tensor_t<fp_e8m7_t, 4, BS>& o) {
  bool active = false;
  const_tensor_iterator_t<fp_e8m7_t, 4, BS> oit(o);
  tensor_iterator_t<ixpix_t, 5, BD> bit(b.data);
  ixpix_t v;
  do {
    for (int w = 0; w < b.data.get_dim(2); w++) {
      aoffset_t c = 0;
      for (int g = 0; g < b.data.get_dim(1); g++) {
        for (int n = 0; n < b.data.get_dim(0); n++) {
          for (int i = 0; i < ISIZE; i+=2) {
            if (c < o.get_dim(0) && w < o.get_dim(1)) {
              fp_e8m7_t t(oit.read());
              v[i] = t.data;
              v[i+1] = t.data>>8;
              active = oit.next();
              c++;
            } else {
              v[i] = 0;
              v[i+1] = 0;
            }
          }
          bit.write(v);
          bit.next();
        }
      }
    }
  } while (active);
}

//
// Convenience function to convert accumulator opaque array ixacc_t [C][D][W][H][msb/lsb/onn][VSIZE]
// from standard acc_t [D][H][W][C][msb/lsb] layout
//
template<template<typename> class BD, template<typename> class BS>
void convertto(acc_buf_impl_t<BD>&             b  // NOLINT [runtime/references]
               , const tensor_t<acc_t, 5, BS>& o) {
  // zero value
  ixacc_t vz;
  for (int i = 0; i < ISIZE; i++) {
    vz[i] = 0;
  }
  if (o.get_dim(0) == 2) {
    // double acc
    //  ixacc_t [C][D][W][H][l/msb][VSIZE] --> ixacc_t [D][H][W][VSIZE][l/msb][C]
    tensor_t<ixacc_t, 6, BD> b0(b.data.transpose({5, 1, 0, 3, 2, 4}));
    // output [D][H][W][C][msb/lsb] --> [D][H][W][msb/lsb][C]
    tensor_t<acc_t, 5, BS> o0(o.transpose({1, 0, 2, 3, 4}));
    tensor_iterator_t<ixacc_t, 6, BD>     oit(b0);
    const_tensor_iterator_t<acc_t, 5, BS> iit(o0);
    // copy
    for (aoffset_t d = 0; d < b0.get_dim(5); d++) {                     // [D] dimension
      for (aoffset_t h = 0; h < b0.get_dim(4); h++) {                   // [H] dimension
        for (aoffset_t w = 0; w < b0.get_dim(3)*b0.get_dim(2); w++) {   // [W] dimension
          for (aoffset_t mlsb = 0; mlsb < b0.get_dim(1); mlsb++) {      // msb/lsb
            for (aoffset_t c = 0; c < b0.get_dim(0) ; c++) {            // [C]
              ixacc_t v = vz;
              if (d < o0.get_dim(4) && h < o0.get_dim(3) && w < o0.get_dim(2) && mlsb < o0.get_dim(1)) {
                for (int i = 0; i < ISIZE; i++) {
                  if ((c*ISIZE+i) < o0.get_dim(0)) {
                    v[i] = iit.read();
                    iit.next();
                  }
                }
              }
              oit.write(v);  //  Write the acc vector
              oit.next();
            }
          }
        }
      }
    }
  } else {
    // onn=1|2
    //   ixacc_t [C][D][W][H][onn][VSIZE] --> ixacc_t [D][H][W][VSIZE][C][onn]
    tensor_t<ixacc_t, 6, BD> b0(b.data.transpose({1, 5, 0, 3, 2, 4}));
    // output [D][H][W][C][1]
    tensor_t<acc_t, 5, BS> o0(o.transpose({1, 0, 2, 3, 4}));
    tensor_iterator_t<ixacc_t, 6, BD>     oit(b0);
    const_tensor_iterator_t<acc_t, 5, BS> iit(o);
    // copy
    for (aoffset_t d = 0; d < b0.get_dim(5); d++) {                        // [D] dimension
      for (aoffset_t h = 0; h < b0.get_dim(4); h++) {                      // [H] dimension
        for (aoffset_t w = 0; w < b0.get_dim(3)*b0.get_dim(2); w++) {      // [W] dimension
          for (aoffset_t c = 0; c < b0.get_dim(0)*b0.get_dim(1); c++) {  // [C][onn]
            ixacc_t v = vz;
            if (d < o0.get_dim(4) && h < o0.get_dim(3) && w < o0.get_dim(2)) {
              for (int i = 0; i < ISIZE; i++) {
                if ((c*ISIZE+i) < o0.get_dim(0)) {
                  v[i] = iit.read();
                  iit.next();
                }
              }
            }
            oit.write(v);  //  Write
            oit.next();
          }
        }
      }
    }
  }
}


// from standard fp_e8m23_t [D][H][W][C] layout
//
template<template<typename> class BD, template<typename> class BS>
void convertto(acc_buf_impl_t<BD>&                  b  // NOLINT [runtime/references]
               , const tensor_t<fp_e8m23_t, 4, BS>& o) {
  // zero value
  ixacc_t vz;
  for (int i = 0; i < ISIZE; i++) {
    vz[i] = 0;
  }
  // 32b accumulator
  // ixacc_t [C][D][W][H][1][VSIZE] --> [1][D][H][W][VSIZE][C]
  tensor_t<ixacc_t,6,BD> b0(b.data.transpose({5, 0, 3, 2, 4, 1}));
  tensor_iterator_t<ixacc_t, 6, BD>             oit(b0);
  const_tensor_iterator_t<fp_e8m23_t, 4, BS>    iit(o);
  for (aoffset_t d = 0; d < b0.get_dim(4); d++) {
    for (aoffset_t h = 0; h < b0.get_dim(3); h++) {
      for (aoffset_t w = 0; w < b0.get_dim(2)*b0.get_dim(1); w++) {
        for (aoffset_t c = 0; c < b0.get_dim(0); c++) {
          ixacc_t v = vz;
          if (d < o.get_dim(3) && h < o.get_dim(2) && w < o.get_dim(1)) {
            for (int i = 0; i < ISIZE; i++) {
              if ((c*ISIZE+i) < o.get_dim(0)) {
                fp_e8m23_t a;
                a = iit.read();
                iit.next();
                v[i] = static_cast<uint32_t>(a);
              }
            }
          }
          oit.write(v);
          oit.next();
        }
      }
    }
  }
}

};  // namespace tensor::v200
#endif  // SHARED_COMMON_TENSOR_API_IMPL_TENSOR_INLINE_HPP_
