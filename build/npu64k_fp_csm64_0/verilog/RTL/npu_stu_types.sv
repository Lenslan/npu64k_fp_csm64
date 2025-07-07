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


package npu_stu_types;

  import npu_types::*;
  
  // ID field in the MMIO ID registers
  localparam int ISTU_ID = 4;
  localparam int OSTU_ID = 5;
  localparam int USTU_ID = 7;
  // MAJOR version field in the MMIO ID register
  localparam int ISTU_MAJ = 2; 
  localparam int OSTU_MAJ = 2; 
  localparam int USTU_MAJ = 2;
  // MINOR version field in the MMIO ID register
  localparam int ISTU_MIN = 0;
  localparam int OSTU_MIN = 0;
  localparam int USTU_MIN = 0;

  // NPU i/oSTU Input Type
  typedef struct packed {
    hlapi_xm_agu_t        xmo_seq;     // Struct specifying the Input XM access sequence 
    hlapi_xm_agu_t        xmi_seq;     // Struct specifying the Output XM access sequence
    hlapi_i_t common;                  // Common Input field
  } stu_hlapi_i_t;

  // NPU i/oSTU HLAPI Type 
  typedef struct packed {
    hlapi_o_t      o;
    hlapi_io_t     io;
    stu_hlapi_i_t  i;
  } stu_hlapi_t;
  
  //  Unified STU HLAPI Input Type
  typedef struct packed {
    hlapi_stu_agu_t      xmo_seq;      // Struct specifying the destination XM access sequence
    hlapi_stu_agu_t      xmi_seq;      // Struct specifying the source XM access sequence
    hlapi_i_t common;                  // Common Input field
  } unified_stu_hlapi_i_t;

  // Unified STU HLAPI Type 
  typedef struct packed {
    hlapi_o_t      o;
    hlapi_io_t     io;
    unified_stu_hlapi_i_t i;
  } unified_stu_hlapi_t;
  
endpackage : npu_stu_types
