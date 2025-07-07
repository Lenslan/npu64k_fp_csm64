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
 * tensor_basic_types.cpp
 *
 * File defining global datatypes for the NPU
 *
 */

#include <iomanip>
#include "tensor_basic_types.hpp"


namespace tensor::v200 {

ostream& pix_stream(ostream& os, const pix_t& dt) {
  std::ios state0(nullptr);
  state0.copyfmt(os);
  os << "0x" << std::noshowbase << std::internal << std::hex << std::setfill('0')
     << std::setw(2) << (((int16_t)dt)&0xff);
  os.copyfmt(state0);
  return os;
}

ostream& coef_stream(ostream& os, const coef_t& dt) {
  std::ios state0(nullptr);
  state0.copyfmt(os);
  os << "0x" << std::noshowbase << std::internal << std::hex << std::setfill('0')
     << std::setw(2) << (((int16_t)dt)&0xff);
  os.copyfmt(state0);
  return os;
}

ostream& acc_stream(ostream& os, const acc_t& dt) {
  std::ios state0(nullptr);
  state0.copyfmt(os);
  os << "0x" << std::noshowbase << std::internal << std::hex << std::setfill('0')
     << std::setw(8) << ((int32_t)dt);
  os.copyfmt(state0);
  return os;
}

ostream& operator<<(ostream& os, const pix_t& dt) {
  os << "(pix_t):";
  return pix_stream(os, dt);
}

ostream& operator<<(ostream& os, const coef_t& dt) {
  os << "(coef_t):";
  return coef_stream(os, dt);
}

#ifndef RTL_ARC
ostream& operator<<(ostream& os, const acc_t& dt) {
  os << "(acc_t):";
  return acc_stream(os, dt);
}
#endif

ostream& operator<<(ostream& os, const ixpix_t& dt) {
  os << "(ixpix_t):{";
  for (int i = 0; i < ISIZE; i++) {
    if (i != 0) os << ",";
    pix_stream(os, dt[i]);
  }
  os << "}";
  return os;
}

ostream& operator<<(ostream& os, const ixacc_t& dt) {
  os << "(ixacc_t):{";
  for (int i = 0; i < ISIZE; i++) {
    if (i != 0) os << ",";
    acc_stream(os, dt[i]);
  }
  os << "}";
  return os;
}

// convert between vyixacc and vyixfp32 types
vyixfp32_t vyixacc2fp32(const vyixacc_t& in) {
  vyixfp32_t out;
  for (int v = 0; v < VSIZE; v++) {
    for (int i = 0; i < ISIZE; i++) {
      out[v][i] = fp_e8m23_t((uint32_t)in[v][i]);
    }
  }
  return(out);
}

ostream& operator<<(ostream& os, const vyixpix_t& dt) {
  os << "(vyixpix_t):{";
  for (int v = 0; v < VSIZE; v++) {
    if (v != 0) os << ",";
    os << "{";
    for (int i = 0; i < ISIZE; i++) {
      if (i != 0) os << ",";
      pix_stream(os, dt[v][i]);
    }
    os << "}";
  }
  os << "}";
  return os;
}

ostream& operator<<(ostream& os, const vyixacc_t& dt) {
  os << "(vyixacc_t):{";
  for (int v = 0; v < VSIZE; v++) {
    if (v != 0) os << ",";
    os << "{";
    for (int i = 0; i < ISIZE; i++) {
      if (i != 0) os << ",";
      acc_stream(os, dt[v][i]);
    }
    os << "}";
  }
  os << "}";
  return os;
}

ostream& operator<<(ostream& os, const vyixfp32_t& dt) {
  os << "(vyixfp32_t):{";
  for (int v = 0; v < VSIZE; v++) {
    if (v != 0) os << ",";
    os << "{";
    for (int i = 0; i < ISIZE; i++) {
      if (i != 0) os << ",";
      os << dt[v][i];
    }
    os << "}";
  }
  os << "}";
  return os;
}

} // namespace tensor::v200
