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
 * tensor_basic_types.hpp
 *
 * File defining global datatypes for the NPU
 *
 */

#ifndef TENSOR_API_BASIC_TYPES_HPP_
#define TENSOR_API_BASIC_TYPES_HPP_

#include <array>
#include <cmath>
#include <cstdint>
#include <iostream>
#include "npu_config.hpp"     // NOLINT [build/include_subdir]
#include "npu_defines.hpp"    // NOLINT [build/include_subdir]


#define NPU_STRONG_TYPEDEF(T, D)                                                 \
struct D                                                                         \
{                                                                                \
  T t;                                                                           \
  explicit D(const T& t_) : t(t_) {}                                             \
  D() : t() {}                                                                   \
  D(const D & t_) : t(t_.t) {}                                                   \
  D& operator=(const D& rhs) {t = rhs.t; return *this;}                          \
  D& operator=(const T& rhs) {t = rhs; return *this;}                            \
  operator const T&() const {return t;}                                          \
  operator T&() {return t;}                                                      \
  bool operator==(const D& rhs) const {return t == rhs.t;}                       \
  bool operator<(const D& rhs) const {return t < rhs.t;}                         \
};


namespace tensor::v200 {
using namespace std;
//
// Data-types for feature-maps, coefficients and accumulators
//
// FIXME: error for acc_t in CCAC compilation: initializer element is not a compile-time constant
NPU_STRONG_TYPEDEF(int8_t, pix_t)
NPU_STRONG_TYPEDEF(int8_t, coef_t)
#ifdef RTL_ARC
typedef int32_t acc_t;
#else
NPU_STRONG_TYPEDEF(int32_t, acc_t)
#endif
typedef uint16_t vmptr_t;
typedef uint16_t amptr_t;


/////////////////////////////////////////////////////////////////////////////////
//
// floating point format types
//
/////////////////////////////////////////////////////////////////////////////////
struct fp_e8m23_t;
struct fp_e8m7_t;
struct fp_e5m10_t;


// fp32 (1b sign, 8b exponent, 23b mantissa)
struct fp_e8m23_t {
  uint32_t data;
  inline fp_e8m23_t() = default;
  inline fp_e8m23_t(const fp_e8m23_t&) = default;
  inline explicit fp_e8m23_t(uint32_t d) {
    data = d;
  }
  inline explicit fp_e8m23_t(float f) {
    data = *(uint32_t*)(void*)&f;
    uint32_t e = data&0x7f800000;
    if (e == 0x7f800000) {
      data |= 0x7fffffff; // +/- nan and inf become +/- nan
    } else if (e == 0){
      data &= 0x80000000; // no subnormal support
    }
  }
  inline explicit operator float() const {
    return *(float*)(void*)&data;
  }
  inline explicit operator uint32_t() const {
    return data;
  }
  explicit operator fp_e8m7_t() const;
  explicit operator fp_e5m10_t() const;
  explicit operator int32_t() const;
  float to_float_no_min_zero() const {
    // convert -0.0 to 0.0
    uint32_t r(data==0x80000000?0x0:data);
    return *(float*)(void*)&r;
  }
  // arithmetic operators
  inline fp_e8m23_t operator+(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    // inf becomes nan
    if ((d0 & 0x7fffffff) == 0x7f800000)
      d0 = d0 | 0x7fffffff;
    if ((d1 & 0x7fffffff) == 0x7f800000)
      d1 = d1 | 0x7fffffff;
    fp_e8m23_t r((*(float*)(void*)&d0)+(*(float*)(void*)&d1));
    return r;
  }
  inline fp_e8m23_t operator-(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    // inf becomes nan
    if ((d0 & 0x7fffffff) == 0x7f800000)
      d0 = d0 | 0x7fffffff;
    if ((d1 & 0x7fffffff) == 0x7f800000)
      d1 = d1 | 0x7fffffff;
    fp_e8m23_t r((*(float*)(void*)&d0)-(*(float*)(void*)&d1));
    return r;
  }
  inline fp_e8m23_t operator-() const {
    uint32_t r = data^0x80000000;
    fp_e8m23_t f(*(float*)(void*)&r);
    return f;
  }
  inline fp_e8m23_t operator*(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    // inf becomes nan
    if ((d0 & 0x7fffffff) == 0x7f800000)
      d0 = d0 | 0x7fffffff;
    if ((d1 & 0x7fffffff) == 0x7f800000)
      d1 = d1 | 0x7fffffff;
    fp_e8m23_t r((*(float*)(void*)&d0)*(*(float*)(void*)&d1));
    return r;
  }
  inline fp_e8m23_t abs() const {
    uint32_t d0 = (data & 0x7f800000) == 0 ? (data & 0x80000000) : data;
    fp_e8m23_t r;
    r.data = d0 & 0x7fffffff;
    return r;
  }
  inline uint8_t get_exp() const {
    return data>>23;
  }
  // comparison
  inline bool gte0() const {
    uint32_t d0 = (data & 0x7f800000) == 0 ? (data & 0x80000000) : data;
    if ((d0 & 0x7f800000) == 0x7f800000) {
      return false;
    } else {
      return (*(float*)(void*)&d0)>=0.0;
    }
  }
  inline bool operator<(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    if ((d0 & 0x7f800000) == 0x7f800000) {
      return false;
    } else if ((d1 & 0x7f800000) == 0x7f800000) {
      return true;
    } else {
      return (*(float*)(void*)&d0)< (*(float*)(void*)&d1);
    }
  }
  inline bool operator<=(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    if ((d0 & 0x7f800000) == 0x7f800000) {
      return false;
    } else if ((d1 & 0x7f800000) == 0x7f800000) {
      return true;
    } else {
      return (*(float*)(void*)&d0)<=(*(float*)(void*)&d1);
    }
  }
  inline bool operator>(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    if ((d0 & 0x7f800000) == 0x7f800000) {
      return false;
    } else if ((d1 & 0x7f800000) == 0x7f800000) {
      return true;
    } else {
      return (*(float*)(void*)&d0)> (*(float*)(void*)&d1);
    }
  }
  inline bool operator>=(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    if ((d0 & 0x7f800000) == 0x7f800000) {
      return false;
    } else if ((d1 & 0x7f800000) == 0x7f800000) {
      return true;
    } else {
      return (*(float*)(void*)&d0)>=(*(float*)(void*)&d1);
    }
  }
  inline bool operator==(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    return (*(float*)(void*)&d0)==(*(float*)(void*)&d1);
  }
  inline bool operator!=(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    return (*(float*)(void*)&d0)!=(*(float*)(void*)&d1);
  }
  inline fp_e8m23_t max(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    fp_e8m23_t r0(d0);
    fp_e8m23_t r1(d1);
    if ((data & 0x7f800000) == 0x7f800000) {
      // this is nan, return a
      return r1;
    } else if ((a.data & 0x7f800000) == 0x7f800000) {
      // a is nan
      return r0;
    } else if (*this > a) {
      // a is smaller
      return r0;
    } else {
      // a is bigger
      return r1;
    }
  }
  inline fp_e8m23_t min(const fp_e8m23_t& a) const {
    uint32_t d0 =   (data & 0x7f800000) == 0 ?   (data & 0x80000000) : data;
    uint32_t d1 = (a.data & 0x7f800000) == 0 ? (a.data & 0x80000000) : a.data;
    fp_e8m23_t r0(d0);
    fp_e8m23_t r1(d1);
    if ((data & 0x7f800000) == 0x7f800000) {
      // this is nan, return a
      return r1;
    } else if ((a.data & 0x7f800000) == 0x7f800000) {
      // a is nan
      return r0;
    } else if (*this < a) {
      // a is nan bigger
      return r0;
    } else {
      // a is smaller
      return r1;
    }
  }
  inline fp_e8m23_t trunc() const {
    // truncate towards zero
    uint32_t d0 = (data & 0x7f800000) == 0 ? (data & 0x80000000) : data;
    return fp_e8m23_t(truncf(*(float*)(void*)&d0));
  }
  inline fp_e8m23_t round() const {
    // round ties to nearest even
    uint32_t d0 = (data & 0x7f800000) == 0 ? (data & 0x80000000) : data;
    return fp_e8m23_t(rintf(*(float*)(void*)&d0));
  }
};


// fp24 (1b sign, 8b exponent, 15b mantissa)
struct fp_e8m15_t {
  array<uint8_t,3> data;
  inline fp_e8m15_t() = default;
  inline fp_e8m15_t(const fp_e8m15_t&) = default;
  inline explicit fp_e8m15_t(float f) {
    uint32_t i = *(uint32_t*)(void*)&f;
    if ((i & 0x7f800000) == 0) {
      i &= 0x80000000;
    } else if ((i & 0x7f800000) == 0x7f800000) {
      i |= 0x7fffffff;
    }
    data[0] = (i>>8)&0xff;
    data[1] = (i>>16)&0xff;
    data[2] = (i>>24)&0xff;
  }
  inline explicit fp_e8m15_t(uint32_t i) {
    data[0] = (i>>8)&0xff;
    data[1] = (i>>16)&0xff;
    data[2] = (i>>24)&0xff;
  }
  inline explicit operator float() const {
    uint32_t i = 0;
    i |= data[2]<<24;
    i |= data[1]<<16;
    i |= data[0]<<8;
    return *(float*)(void*)&i;
  }
  inline explicit operator uint32_t() const {
    uint32_t i = 0;
    i |= data[2]<<24;
    i |= data[1]<<16;
    i |= data[0]<<8;
    return i;
  }
  inline explicit operator fp_e8m23_t() const {
    uint32_t v = (((uint32_t)data[2])<<24)+(((uint32_t)data[1])<<16)+(((uint32_t)data[0])<<8);
    return fp_e8m23_t(v);
  }
  float to_float_no_min_zero() const {
    // convert -0.0 to 0.0
    uint32_t i = 0;
    i |= data[2]<<24;
    i |= data[1]<<16;
    i |= data[0]<<8;
    i = i == 0x80000000 ? 0 : i;
    return *(float*)(void*)&i;
  }
};


// bf16 (1b sign, 8b exponent, 7b mantissa)
struct fp_e8m7_t {
  uint16_t data;
  inline fp_e8m7_t() = default;
  inline fp_e8m7_t(const fp_e8m7_t&) = default;
  inline explicit fp_e8m7_t(uint16_t d) {
    data = d;
  }
  inline fp_e8m7_t(uint8_t msb, uint8_t lsb) {
    data = (((uint16_t)msb)<<8) | lsb;
  }
  inline explicit fp_e8m7_t(float f) {
    uint32_t i = *(uint32_t*)(void*)&f;
    if ((i & 0x7f800000) == 0) {
      i &= 0x80000000;
    } else if ((i & 0x7f800000) == 0x7f800000) {
      i |= 0x7fffffff;
    }
    data = i>>16;
  }
  inline explicit operator float() const {
    uint32_t i;
    i = ((uint32_t)data)<<16;
    return *(float*)(void*)&i;
  }
  inline explicit operator uint16_t() const {
    return data;
  }
  inline explicit operator fp_e8m23_t() const {
    uint32_t v = ((uint32_t)data)<<16;
    return fp_e8m23_t(v);
  }
  float to_float_no_min_zero() const {
    uint32_t i;
    i = ((uint32_t)data)<<16;
    i = i == 0x80000000 ? 0 : i;
    return *(float*)(void*)&i;
  }
};


// fp16 (1b sign, 5b exponent, 16b mantissa)
struct fp_e5m10_t {
  uint16_t data;
  inline fp_e5m10_t() = default;
  inline fp_e5m10_t(const fp_e5m10_t&) = default;
  inline explicit fp_e5m10_t(uint16_t d) {
    data = d;
  }
  inline fp_e5m10_t(uint8_t msb, uint8_t lsb) {
    data = (((uint16_t)msb)<<8) | lsb;
  }
  inline explicit fp_e5m10_t(float f) {
    //uint16_t v;
    uint32_t i = *(uint32_t*)(void*)&f;
    uint16_t m = (i>>13)&0x3ff;
    int16_t  e = ((i>>23)&0xff)-127+15;
    // saturate exponent
    if (e <= 0) {
      e = 0;
      m = 0;
    } else if (e > 31) {
      e = 31;
    }
    data = ((i&0x80000000)>>16)|(e<<10)|m;
  }
  inline explicit operator float() const {
    uint32_t v = data;
    uint32_t i;
    uint32_t e = ((v>>10)&0x1f);
    uint32_t m = v&0x3ff;
    if (e == 0x1f) {
      // nan
      e = 0xff;
    } else if (e == 0x00) {
      m = 0;
    } else {
      // bias change
      e = e - 15 + 127;
    }
    i = ((v&0x8000)<<16) | (e<<23) | (m<<13);
    return *(float*)(void*)&i;
  }
  inline explicit operator uint16_t() const {
    return data;
  }
  inline explicit operator fp_e8m23_t() const {
    uint32_t v = data;
    uint32_t i;
    uint32_t e = ((v>>10)&0x1f);
    uint32_t m = v&0x3ff;
    if (e == 0x1f) {
      // nan
      e = 0xff;
    } else if (e == 0x00) {
      m = 0;
    } else {
      // bias change
      e = e - 15 + 127;
    }
    i = ((v&0x8000)<<16) | (e<<23) | (m<<13);
    return fp_e8m23_t(i);
  }
  float to_float_no_min_zero() const {
    uint32_t v = data;
    uint32_t i;
    uint32_t e = ((v>>10)&0x1f);
    uint32_t m = v&0x3ff;
    if (e == 0x1f) {
      // nan
      e = 0xff;
    } else if (e == 0x00) {
      m = 0;
    } else {
      // bias change
      e = e - 15 + 127;
    }
    i = ((v&0x8000)<<16) | (e<<23) | (m<<13);
    i = i == 0x80000000 ? 0 : i;
    return *(float*)(void*)&i;
  }
};


// LUT limit type (no sign, 4b exponent, bias 7, 4b mantissa), zero cannot be represented
struct fp_ue4m4_t {
  uint8_t data;
  inline fp_ue4m4_t() = default;
  inline fp_ue4m4_t(const fp_ue4m4_t&) = default;
  inline explicit fp_ue4m4_t(uint8_t d) {
    data = d;
  }
  inline fp_ue4m4_t(uint8_t e, uint8_t m) {
    data = ((e<<4)&0xf0)|(m&0x0f);
  }
  inline explicit fp_ue4m4_t(float f) {
    uint32_t i = *(uint32_t*)(void*)&f;
    uint8_t  m = (i>>19)&0x0f;
    int16_t  e = ((i>>23)&0xff)-127+7;
    // saturate exponent
    if (e < 0 || ((i&0x80000000) != 0)) {
      e = 0;
      m = 0;
    } else if (e > 15) {
      e = 15;
      m = 0xf;
    }
    data = (e<<4)|m;
  }
  inline explicit operator float() const {
    uint32_t e = (data>>4)&0x0f;
    uint32_t m = data&0x0f;
    e+=127-7;
    uint32_t i = (e<<23) | (m<<19);
    return *(float*)(void*)&i;
  }
  inline explicit operator uint8_t() const {
    return data;
  }
  inline explicit operator fp_e8m23_t() const {
    uint32_t e = (data>>4)&0x0f;
    uint32_t m = data&0x0f;
    e+=127-7;
    uint32_t i = (e<<23) | (m<<19);
    return fp_e8m23_t(i);
  }
  float to_float_no_min_zero() const {
    uint32_t e = (data>>4)&0x0f;
    uint32_t m = data&0x0f;
    e+=127-7;
    uint32_t i = (e<<23) | (m<<19);
    i = i == 0x80000000 ? 0 : i;
    return *(float*)(void*)&i;
  }
};


// prescale_t (no sign, 6b exponent, 2b mantissa)
struct fp_ue6m2_t {
  uint8_t data;
  inline fp_ue6m2_t() {
    // default is 1
    data = 0x7c;
  }
  inline fp_ue6m2_t(const fp_ue6m2_t&) = default;
  inline explicit fp_ue6m2_t(uint8_t d) {
    data = d;
  }
  inline fp_ue6m2_t(uint8_t e, uint8_t m) {
    data = ((e<<2)&0xfc)|(m&3);
  }
  inline explicit fp_ue6m2_t(float f) {
    uint32_t i = *(uint32_t*)(void*)&f;
    uint8_t  m = (i>>21)&0x3;
    int16_t  e = ((i>>23)&0xff)-127+31;
    // saturate exponent
    if (e < 0 || ((i&0x80000000) != 0)) {
      e = 0;
      m = 0;
    } else if (e > 63) {
      e = 63;
    }
    data = (e<<2)|m;
  }
  inline explicit operator float() const {
    uint32_t e = ((data>>2)&0x3f)+127-31;
    uint32_t m = data&3;
    uint32_t i = (e<<23) | (m<<21);
    return *(float*)(void*)&i;
  }
  inline explicit operator uint8_t() const {
    return data;
  }
  inline explicit operator fp_e8m23_t() const {
    uint32_t e = ((data>>2)&0x3f)+127-31;
    uint32_t m = data&3;
    uint32_t i = (e<<23) | (m<<21);
    return fp_e8m23_t(i);
  }
  float to_float_no_min_zero() const {
    return float(*this);
  }
};
typedef fp_ue6m2_t prescale_t;
#define SET_PRESCALE_FRAC(Y,X) prescale_t(X>>2,Y)
#define GET_PRESCALE_FRAC(X)   ((int)(X.data&3))
#define GET_PRESCALE_FRAC1(X)  ((int)(X.data&3)|4)
#define SET_PRESCALE_EXP(Y,X)  prescale_t(X,Y)
#define GET_PRESCALE_EXP(X)    ((X.data>>2)&0x3f)
#define PRESCALE_ONE           prescale_t((uint8_t)0xbc)
#define FP_PRESCALE_ONE        prescale_t()
#define FP_POSTSCALE_ONE       ((int32_t)(0x7c<<24))

// implement forward declared casting operators
inline fp_e8m23_t::operator fp_e8m7_t() const {
  uint16_t m   = (data>>16)&0x007f;
  uint16_t e   = (data>>23)&0x00ff;
  // convergent rounding
  bool     lsb = (data&0x10000) != 0;
  bool     rnd = (data&0x08000) != 0;
  bool     stk = (data&0x07fff) != 0;
  if (rnd&(lsb|stk)) {
    // add lsb for rounding
    m++;
    if ((m&0x0080) != 0) {
      // overflow
      e++;
      m=(m&0x7f)>>1;
    }
  }
  if (e>=0xff) {
    // nan
    e = 0xff;
    m = 0x3ff;
  }
  uint16_t v=((data>>16)&0x8000)|(e<<7)|m;
  return fp_e8m7_t(v);
}

inline fp_e8m23_t::operator fp_e5m10_t() const {
  uint16_t m   = (data>>13)&0x03ff;
  int16_t  e   = (data>>23)&0x00ff;
  // convergent rounding
  bool     lsb = (data&0x2000) != 0;
  bool     rnd = (data&0x1000) != 0;
  bool     stk = (data&0x0fff) != 0;
  if (rnd&(lsb|stk)) {
    // add lsb for rounding
    m++;
    if ((m&0x0400) != 0) {
      // overflow
      e++;
      m=(m&0x3ff)>>1;
    }
  }
  e = e - 127 + 15;
  if (e>=0x1f) {
    // nan
    e = 0x1f;
    m = 0x3ff;
  } else if (e <= 0) {
    e = 0;
    m = 0;
  }
  uint16_t v=((data>>16)&0x8000)|(e<<10)|m;
  return fp_e5m10_t(v);
}
inline fp_e8m23_t::operator int32_t() const {
  float f=static_cast<float>(*this);
  // assume rounding mode is round ties to even AKA convergent
  return std::nearbyint(f);
}


//
// Vector datatypes
//
typedef array<pix_t, ISIZE>        ixpix_t;
typedef array<ixpix_t, VSIZE>      vyixpix_t;
typedef array<acc_t, ISIZE>        ixacc_t;
typedef array<ixacc_t, VSIZE>      vyixacc_t;
typedef array<fp_e8m23_t, ISIZE>   ixfp32_t;
typedef array<ixfp32_t, VSIZE>     vyixfp32_t; 

// convert between vyixacc and vyixfp32 types
vyixfp32_t vyixacc2fp32(const vyixacc_t&);

//
// Axis index, used to select an axis in a shape
//
typedef uint8_t  axis_t;

//
// Iterator first/last/busy mask type, bits correspond to loop levels, 0 is inner, R-1 is outer
//
typedef uint16_t iter_mask_t;

//
// Spatial dimension indices, width, height, depth
//
typedef enum {SPATIAL_W=0, SPATIAL_H=1, SPATIAL_D=2} spatial_idx_t;


//
// Axis dimension/position, used to define the length of an axis or the position on an axis
// as well as increments/decrements on an axis position
//
typedef int16_t  aoffset_t;

//
// Pointer offset type, used to define increments/decrements on a tensor pointer
//
typedef int32_t  poffset_t;

//
// Shape array
//
template<size_t R> using shape = array<aoffset_t, R>;
template<size_t R> inline size_t get_shape_size(const shape<R>& s) {
  size_t sz = 1;
  for (int r = 0; r < (int)R; r++) {
    sz *= s[r];
  }
  return sz;
}
template<size_t R> inline void report(ostream& os, const shape<R>& dt) {
  os << "{";
  for (int r = 0; r < (int)R-1; r++) {
    os << (int)dt[r] << ",";
  }
  os << (int)dt[R-1] << "}";
}

//
// Printing
//
ostream& pix_stream(ostream&, const pix_t&);
ostream& coef_stream(ostream&, const coef_t&);
ostream& acc_stream(ostream&, const acc_t&);
ostream& operator<<(ostream&, const pix_t&);
ostream& operator<<(ostream&, const coef_t&);
#ifndef RTL_ARC
ostream& operator<<(ostream&, const acc_t&);
#endif
inline ostream& operator<<(ostream& os, const fp_e8m23_t& d) {
  os << d.to_float_no_min_zero();
  return os;
}
inline ostream& operator<<(ostream& os, const fp_e8m15_t& d) {
  os << d.to_float_no_min_zero();
  return os;
}
inline ostream& operator<<(ostream& os, const fp_e8m7_t& d) {
  os << d.to_float_no_min_zero();
  return os;
}
inline ostream& operator<<(ostream& os, const fp_e5m10_t& d) {
  os << d.to_float_no_min_zero();
  return os;
}
inline ostream& operator<<(ostream& os, const fp_ue6m2_t& d) {
  os << d.to_float_no_min_zero();
  return os;
}
inline ostream& operator<<(ostream& os, const fp_ue4m4_t& d) {
  os << d.to_float_no_min_zero();
  return os;
}
ostream& operator<<(ostream&, const ixpix_t&);
ostream& operator<<(ostream&, const ixacc_t&);
ostream& operator<<(ostream&, const ixfp32_t&);
ostream& operator<<(ostream&, const vyixpix_t&);
ostream& operator<<(ostream&, const vyixacc_t&);
ostream& operator<<(ostream&, const vyixfp32_t&);
}
#endif  // TENSOR_API_BASIC_TYPES_HPP_
