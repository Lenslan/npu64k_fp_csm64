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
 * npu_conv_types.h
 *
 * File defining the NPU convolution engine specific datatypes
 * only datatypes shared between high-level and cycle-based model
 *
 */

#ifndef NPU_CONV_TYPES_INCLUDED
#define NPU_CONV_TYPES_INCLUDED

// include global datatypes
#include "npu_types.hpp"

//
// All identifiers related to the convolution engine go into namepsace npu_conv
//
#define DINO(name) name##i32o16
#define NINO(name) name##i16o16
#define VIVO(name) name##v2i8o8
#define FC(name)   name##i16o
// alias for VSIZE=8
#define conv_mode_fci16o128 conv_mode_fci16o
// alias for VSIZE=2
#define conv_mode_fci16o32  conv_mode_fci16o

namespace npu_conv {
  // include global types
  using namespace npu;

  // Main convolution modes
  enum conv_mode_t {
    // 4K config
    // grouped layers
    NINO(conv_mode_4x1g2s1),
    NINO(conv_mode_4x1g2s1dl2),
    NINO(conv_mode_2x1g2s2),
    // convolutions
    DINO(conv_mode_1x1),
    NINO(conv_mode_1x1),
    NINO(conv_mode_2x1s1),
    NINO(conv_mode_2x1s2),
    NINO(conv_mode_2x1s1dl2),
    // depthwise
    NINO(conv_mode_3x3dws1),
    NINO(conv_mode_2x3dws2),
    NINO(conv_mode_3x3dws1dl2),
    NINO(conv_mode_8x1dws1),
    NINO(conv_mode_4x1dws1),
    VIVO(conv_mode_3x3dws1),
    // fully connected
    FC(conv_mode_fc)
  };

  // Coefficient compression modes
  enum coef_mode_t {
    coef_mode_uncompressed,
    coef_mode_compressed,
    coef_mode_sparse,
    coef_mode_fm      
  };

  enum fm_cfg_t {
    fm_cfg_8b_e,
    fm_cfg_16b_e,
    fm_cfg_bf16_e,
    fm_cfg_fp16_e
  };

  enum cf_cfg_t {
    /*0*/ cf_cfg_4b_zp_e,
    /*1*/ cf_cfg_4b_nozp_e,
    /*2*/ cf_cfg_8b_zp_e,
    /*3*/ cf_cfg_8b_nozp_e,
    /*4*/ cf_cfg_16b_e,
    /*5*/ cf_cfg_bf16_e,
    /*6*/ cf_cfg_fp16_e
  };


  //
  // Quadrant offset datatype
  //
  // Padding indices
  const uint32_t CONV_PAD_COL = 0;
  const uint32_t CONV_PAD_ROW = 1;
  const uint32_t CONV_PAD_DEP = 2;
  struct quadrant_t {
    shape<3>  pdoffs; // Column/row/depth padding offset
    aoffset_t doffs;  // pointer offset
  };
  ostream& operator<<(ostream&, const quadrant_t&);


  //
  // Coefficient datatypes
  //
  // MUX selectors for convolution datapath, used for groups of 4 multipliers
  enum coef_sel_t {
    selfix0,  // multiplier selects fixed 0
    selfm01,  // multiplier selects feature-map 0/1
    selfm12,  // multiplier selects feature-map 1/2
    selfm23   // multiplier selects feature-map 2/3
  };
  // sparse coefficient structure
  struct sparse_coef_t {
    std::array<coef_sel_t,16> ctrl;
    std::array<coef_t,16>     coef;
  };
  ostream& operator<<(ostream&s, const sparse_coef_t&);
}
#endif
