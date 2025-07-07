/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

`ifndef NPU_ECC_TYPES_INCLUDED
`define NPU_ECC_TYPES_INCLUDED

`include "npu_defines.v"
package npu_ecc_types;
  import npu_types::*;
  //
  // Ecc parameters
  //
  localparam int VM_ECC_UNIT_CW = 8;  // vm ecc protection unit check bit width
  localparam int VM_ECC_UNIT_DW = 64; // vm ecc protection unit data bit width
  localparam int VM_SYN_UNIT_W = 7;   // am syndrome bit width per ecc unit
  localparam int VM_NUM_ECC = ($bits(ixpix_t))/VM_ECC_UNIT_DW; // number of ecc unit per vm data

  localparam int AM_ECC_UNIT_CW = 8;  // am ecc protection unit check bit width
  localparam int AM_ECC_UNIT_DW = 64; // am ecc protection unit data bit width
  localparam int AM_SYN_UNIT_W = 7;   // am syndrome bit width per ecc unit
  localparam int AM_NUM_ECC = ($bits(vyixacc_t))/AM_ECC_UNIT_DW; // number of ecc unit per am data

  //
  // Ecc data types
  //
  typedef logic [VM_ECC_UNIT_CW-1:0] vm_ecc_unit_c_t; // vm ecc protection unit check bit data type
  typedef logic [VM_ECC_UNIT_DW-1:0] vm_ecc_unit_d_t; // vm ecc protection unit data bit data type
  typedef logic [VM_SYN_UNIT_W-1:0]  vm_s_unit_t;     // am syndrome bit per unit data type
  typedef vm_ecc_unit_c_t [VM_NUM_ECC-1:0] vm_ecc_c_t; // vm check bit data type
  typedef struct packed {
  vm_ecc_c_t  ecc;
  ixpix_t     data;
  } vm_ecc_t; // vm check+data bit data type
  typedef vm_s_unit_t [VM_NUM_ECC-1:0] vm_ecc_s_t; //vm sydrome data type

  typedef logic [AM_ECC_UNIT_CW-1:0] am_ecc_unit_c_t; // am ecc protection unit check bit data type
  typedef logic [AM_ECC_UNIT_DW-1:0] am_ecc_unit_d_t; // am ecc protection unit data bit data type
  typedef logic [AM_SYN_UNIT_W-1:0]  am_s_unit_t;     // am syndrome bit per unit data type
  typedef am_ecc_unit_c_t [AM_NUM_ECC-1:0] am_ecc_c_t; // vm check bit data type
  typedef struct packed {
  am_ecc_c_t  ecc;
  vyixacc_t   data;
  } am_ecc_t; // vm check+data bit data type
  typedef am_s_unit_t [AM_NUM_ECC-1:0] am_ecc_s_t; //am sydrome data type


endpackage : npu_ecc_types
`endif
