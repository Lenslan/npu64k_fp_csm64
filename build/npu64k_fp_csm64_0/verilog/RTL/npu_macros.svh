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

`ifndef NPU_MACROS_INCLUDED
`define NPU_MACROS_INCLUDED

// TRACE Interface
//
// NPU trace wire declaration
//
`define TRCWIRES(TRCPREF, N) \
  logic [N-1:0]         TRCPREF``valid;     // trace valid \
  logic [N-1:0]         TRCPREF``accept;    // trace accept \
  logic [N-1:0][31:0]   TRCPREF``id         // ID for tracing (from HLAPI), msb = 0 start, msb = 1 end

//
// NPU trace instance port list
//
// Batch Port
`define TRCINST_B(TRCPREF,TRCWPREF) \
  .TRCPREF``valid   (TRCWPREF``valid  ), \
  .TRCPREF``accept  (TRCWPREF``accept ), \
  .TRCPREF``id      (TRCWPREF``id     )  

// Single Port
`define TRCINST_S(TRCPREF,TRCWPREF,N) \
  .TRCPREF``valid   (TRCWPREF``valid[N]  ), \
  .TRCPREF``accept  (TRCWPREF``accept[N] ), \
  .TRCPREF``id      (TRCWPREF``id[N]     )  

// Multi Port
`define TRCINST_MN(TRCPREF,TRCWPREF,M,N) \
  .TRCPREF``valid   (TRCWPREF``valid[N:M]  ), \
  .TRCPREF``accept  (TRCWPREF``accept[N:M] ), \
  .TRCPREF``id      (TRCWPREF``id[N:M]     )  

//
// NPU trace module master port list
//
`define TRCMST(TRCPREF, N) \
  output logic [N-1:0]         TRCPREF``valid,     // trace valid \
  input  logic [N-1:0]         TRCPREF``accept,    // trace accept \
  output logic [N-1:0][31:0]   TRCPREF``id         // ID for tracing (from HLAPI), msb = 0 start, msb = 1 end

//
// NPU trace module slave port list
//
`define TRCSLV(TRCPREF, N) \
  input  logic [N-1:0]         TRCPREF``valid,     // trace valid \
  output logic [N-1:0]         TRCPREF``accept,    // trace accept \
  input  logic [N-1:0][31:0]   TRCPREF``id         // ID for tracing (from HLAPI), msb = 0 start, msb = 1 end


// STREAM Interface
//
// NPU stream wire declaration
//
`define STRWIRES(STRPREF, TYPE) \
   logic     STRPREF``str_valid; \
   logic     STRPREF``str_accept; \
   TYPE      STRPREF``str_data 

//
// NPU streaminstance port list
//
`define STRINST(STRPREF,STRWPREF) \
  .STRPREF``str_valid   (STRWPREF``str_valid ), \
  .STRPREF``str_accept  (STRWPREF``str_accept), \
  .STRPREF``str_data    (STRWPREF``str_data  )  

//
// NPU stream module master port list
//
`define STRMST(STRPREF, TYPE) \
   output  logic     STRPREF``str_valid, \
   input   logic     STRPREF``str_accept, \
   output  TYPE      STRPREF``str_data 

//
// NPU stream module slave port list
//
`define STRSLV(STRPREF, TYPE) \
   input   logic     STRPREF``str_valid, \
   output  logic     STRPREF``str_accept, \
   input   TYPE      STRPREF``str_data

`define FCHUNK 32
`define NUM_FLANES(X) ((X+`FCHUNK-1)/`FCHUNK)
`define FRANGE(X)     (X)*`FCHUNK+:`FCHUNK
`define FRANGELAST(X) X-1:(`NUM_FLANES(X)-1)*`FCHUNK

//
// FOR assignments for two dimensional registers
//
`define FOR_ASSIGN_EN(IBEGIN, IEND, REGEN, REGR, REGNXT) \
  for (int i = IBEGIN; i < IEND; i++) begin \
    if (REGEN[i]) begin \
      REGR[i] <= REGNXT[i]; \
    end \
  end

`endif //  `ifndef NPU_MACROS_INCLUDED
