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
 * npu_conv_types.c
 *
 * File implementing global datatypes
 *
 */

#include <iomanip>
#include "npu_conv_types.hpp"  // NOLINT [build/include_subdir]

namespace npu_conv {
  ostream& operator<<(ostream& os, const quadrant_t& dt) {
    std::ios state0(nullptr);
    state0.copyfmt(os);

    os << "(quadrant_t):{" <<
      std::noshowbase << std::internal << std::hex << std::setfill('0')
                      << "0x" << std::setw(4) << (static_cast<int>(dt.doffs & 0x0ffff)) << ","
                      << "0x" << std::setw(4) << (static_cast<int>(dt.pdoffs[0] & 0x0ffff)) << ","
                      << "0x" << std::setw(4) << (static_cast<int>(dt.pdoffs[1] & 0x0ffff)) << ","
                      << "0x" << std::setw(4) << (static_cast<int>(dt.pdoffs[2] & 0x0ffff))
                      << "}";
    os.copyfmt(state0);
    return os;
  }

  ostream& operator<<(ostream& os, const sparse_coef_t& dt) {
    coef_t z = (coef_t)0;
    os << "(coef_atom_t):{{";
    for (int j = 0; j < 16; j++) {
      switch (dt.ctrl[j]) {
      case selfix0: os << "selfix0"; break;
      case selfm01: os << "selfm01"; break;
      case selfm12: os << "selfm12"; break;
      case selfm23: os << "selfm23"; break;
      }
      if (j != 15) os << ",";
    }
    os << "},{";
    for (int j = 0; j < 15; j++) {
      if (dt.ctrl[j] == selfix0) {
        os << z << ",";
      } else {
        os << dt.coef[j] << ",";
      }
    }
    if (dt.ctrl[15] == selfix0) {
      os << z << "}}";
    } else {
      os << dt.coef[15] << "}}";
    }
    return os;
  }

}  // namespace npu_conv
