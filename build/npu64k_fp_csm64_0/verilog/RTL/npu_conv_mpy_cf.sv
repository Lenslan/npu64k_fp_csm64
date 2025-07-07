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

//
// convolution multiplier array module
// vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv npu_conv_types.sv npu_conv_mpy_cf.sv
// analyze -format sverilog [list ../../../shared/RTL/npu_types.sv ../npu_conv_types.sv ../npu_conv_mpy_cf.sv]
//


`include "npu_defines.v"
`include "npu_conv_macros.svh"

module npu_conv_mpy_cf 
  import npu_types::*;
  import npu_conv_types::*;
  #(parameter logic NPU_HAS_FLOAT = 1)
  (
   // Clock and reset
   input  logic                                             clk,          // Clock, all logic clocked at posedge
   input  logic                                             rst_a,        // Asynchronous reset, active high
   // HLAPI attributes
   input  mpy_cfg_t                                         mpy_cfg,      // mpy format
   input  conv_mode_t                                       conv_mode,    // Convolution mode attribute
   input  logic                                             coef_mode_fm, // Matrix*Matrix indication
   input  logic                                             onn,          // if true then two input outer loops
   // Dynamic input & outputs
   input  logic                                             cf_en,        // enable pipeline
   input  logic                                             ctrl_tgl,     // toggle control register
   input  logic        [1:0]                                ctrl_sel,     // control register select
   input  logic                                             cf_first,     // true if first coefficient block in convolution
   input  coef_data_t                                       coef_data,    // data from coefficient loading
   output mpy_cf_t     [1:0][ISIZE-1:0][ISIZE-1:0]          cf_out,       // feature-map array output
   output logic                        [ISIZE-1:0][ISIZE-1:0][2:0]     ctrla_out,    // even feature-map selector
   output logic                        [ISIZE-1:0][ISIZE-1:0][2:0]     ctrlb_out     // odd feature-map selector
   );
  // local wires
  mpy_cf_t       [1:0][ISIZE-1:0][ISIZE-1:0]        c_r;           // coefficient register
  mpy_cf_t       [1:0][ISIZE-1:0][ISIZE-1:0]        c_nxt;         // coefficient register next value
  logic          [1:0][ISIZE-1:0][ISIZE-1:0][1:0]   c_en;          // coefficient register enables even/odd
  logic          [1:0][ISIZE-1:0][ISIZE-1:0][2:0]   ctrla_r;       // even pair feature-map selector
  logic          [1:0][ISIZE-1:0][ISIZE-1:0][2:0]   ctrlb_r;       // odd pair feature-map selector
  logic          [1:0][ISIZE-1:0][ISIZE-1:0][2:0]   ctrla_nxt;     // decoded feature-map selector
  logic          [1:0][ISIZE-1:0][ISIZE-1:0][2:0]   ctrlb_nxt;     // decoded feature-map selector
  logic                                             ctrl_out_en;   // enable control regs
  logic               [ISIZE-1:0][ISIZE-1:0][2:0]   ctrla_out_nxt; // even pair feature-map selector, preselected
  logic               [ISIZE-1:0][ISIZE-1:0][2:0]   ctrlb_out_nxt; // odd pair feature-map selector, preselected
  logic               [ISIZE-1:0][ISIZE/2-1:0][1:0][2:0]   ctrla_sel; // even pair feature-map selector, preselected
  logic               [ISIZE-1:0][ISIZE/2-1:0][1:0][2:0]   ctrlb_sel; // odd pair feature-map selector, preselected
  logic                                             fm_dbl;        // double wide feature-map
  logic                                             cf_dbl;        // double wide coefficients
  logic                                             sparse;        // if true then sparse mode

  // local functions
  function automatic logic [2:0] decode_a(input coef_sela_t i);
    logic [2:0] r;
    case (i)
    selafm0: r = 3'b001;
    selafm1: r = 3'b010;
    selafm2: r = 3'b100;
    default: r = 3'b000; // fix0
    endcase // case (i)
    return r;
  endfunction : decode_a
  function automatic logic [2:0] decode_b(input coef_selb_t i);
    logic [2:0] r;
    case (i)
    selbfm1: r = 3'b001;
    selbfm2: r = 3'b010;
    selbfm3: r = 3'b100;
    default: r = 3'b000; // fix0
    endcase // case (i)
    return r;
  endfunction : decode_b

  // simple assigments
  assign cf_out    = c_r;
  assign ctrla_out = ctrla_sel;
  assign ctrlb_out = ctrlb_sel;
  assign fm_dbl    = isfmdbl(mpy_cfg);
  assign cf_dbl    = iscfdbl(mpy_cfg);
  assign sparse    = issparse(mpy_cfg);

// spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression
//SJ :Ignore
  // function for sign extension
  function automatic coef9_t sext(coef_t a);
    return {a[7],a};
  endfunction : sext

// spyglass disable_block W499
//SMD:Mismatch between function cal argument and input
//SJ :Ignore odd
// spyglass disable_block STARC05-2.1.3.1
//SMD:Not all bits in function are used
//SJ :Ignore
  // map coefficients for dw modes, 16b feature-map and 8b coefficients
  function automatic void
    dw_fm16cf8(
               input conv_mode_t                       cm,
               input coef_atom_t                       ca,
               inout coef_t      [1:0][ISIZE-1:0][1:0] cin,
               inout logic       [1:0][ISIZE-1:0][1:0] nav,
               inout logic       [1:0][ISIZE-1:0][1:0] ce
               );
      for (int odd = 0; odd < 2; odd++) begin
        dw_fm8cf8(cm, ca, cin, nav, ce, odd);
      end // for (int odd = 0; odd < 2; odd++)
  endfunction : dw_fm16cf8
// spyglass enable_block STARC05-2.1.3.1
  
  // map coefficients for dw modes, 8b feature-map and coefficients
  function automatic void
    dw_fm8cf8(
              input conv_mode_t                       cm,
              input coef_atom_t                       ca,
              inout coef_t      [1:0][ISIZE-1:0][1:0] cin,
              inout logic       [1:0][ISIZE-1:0][1:0] nav,
              inout logic       [1:0][ISIZE-1:0][1:0] ce,
              input logic                             idx
              );
    for (int c = 0; c < 2; c++)
    begin
      cin[c][0][idx]   |= ca.coef[8*c+0];
      cin[c][2][idx]   |= ca.coef[8*c+2];
      cin[c][5][idx]   |= ca.coef[8*c+5];
      cin[c][7][idx]   |= ca.coef[8*c+7];
      nav[c][0][idx]   &= ca.nav[8*c+0];
      nav[c][2][idx]   &= ca.nav[8*c+2];
      nav[c][5][idx]   &= ca.nav[8*c+5];
      nav[c][7][idx]   &= ca.nav[8*c+7];
      ce[c][0][idx]    |= 1'b1;
      ce[c][2][idx]    |= 1'b1;
      ce[c][5][idx]    |= 1'b1;
      ce[c][7][idx]    |= 1'b1;
      case (cm)
      `VIVO(conv_mode_3x3dws1),
      `NINO(conv_mode_3x3dws1):
        begin
          cin[c][1][idx]   |= ca.coef[8*c+1];
          cin[c][6][idx]   |= ca.coef[8*c+6];
          cin[c][10][idx]  |= ca.coef[8*c+3];
          cin[c][11][idx]  |= ca.coef[8*c+4];
          cin[c][12][idx]  |= ca.spare[c];
          nav[c][1][idx]   &= ca.nav[8*c+1];
          nav[c][6][idx]   &= ca.nav[8*c+6];
          nav[c][10][idx]  &= ca.nav[8*c+3];
          nav[c][11][idx]  &= ca.nav[8*c+4];
          nav[c][12][idx]  &= ca.nav[16+c];
          ce[c][1][idx]    |= 1'b1;
          ce[c][6][idx]    |= 1'b1;
          ce[c][10][idx]   |= 1'b1;
          ce[c][11][idx]   |= 1'b1;
          ce[c][12][idx]   |= 1'b1;
        end
      `NINO(conv_mode_2x3dws2):
        begin
          cin[c][1][idx]   |= ca.coef[8*c+1];
          cin[c][6][idx]   |= ca.coef[8*c+6];
          nav[c][1][idx]   &= ca.nav[8*c+1];
          nav[c][6][idx]   &= ca.nav[8*c+6];
          ce[c][1][idx]    |= 1'b1;
          ce[c][6][idx]    |= 1'b1;
        end
      `NINO(conv_mode_3x3dws1dl2):
        begin
          cin[c][4][idx]   |= ca.coef[8*c+4];
          cin[c][9][idx]   |= ca.coef[8*c+6];
          cin[c][10][idx]  |= ca.coef[8*c+3];
          cin[c][12][idx]  |= ca.spare[c];
          cin[c][14][idx]  |= ca.coef[8*c+1];
          nav[c][4][idx]   &= ca.nav[8*c+4];
          nav[c][9][idx]   &= ca.nav[8*c+6];
          nav[c][10][idx]  &= ca.nav[8*c+3];
          nav[c][12][idx]  &= ca.nav[16+c];
          nav[c][14][idx]  &= ca.nav[8*c+1];
          ce[c][4][idx]    |= 1'b1;
          ce[c][9][idx]    |= 1'b1;
          ce[c][10][idx]   |= 1'b1;
          ce[c][12][idx]   |= 1'b1;
          ce[c][14][idx]   |= 1'b1;
        end
      default: //  `NINO(conv_mode_8x1dws1)
        begin
          cin[c][1][idx]   |= ca.coef[8*c+1];
          cin[c][3][idx]   |= ca.coef[8*c+3];
          cin[c][4][idx]   |= ca.coef[8*c+4];
          cin[c][6][idx]   |= ca.coef[8*c+6];
          nav[c][1][idx]   &= ca.nav[8*c+1];
          nav[c][3][idx]   &= ca.nav[8*c+3];
          nav[c][4][idx]   &= ca.nav[8*c+4];
          nav[c][6][idx]   &= ca.nav[8*c+6];
          ce[c][1][idx]    |= 1'b1;
          ce[c][3][idx]    |= 1'b1;
          ce[c][4][idx]    |= 1'b1;
          ce[c][6][idx]    |= 1'b1;
        end
      endcase // case (conv_mode)
    end // for (int c = 0; c < 2; c++)
  endfunction : dw_fm8cf8
// spyglass enable_block W499
  
  // Decode coefficients depending on mode
  // outputs: c_nxt, c_en, ctrla_nxt, ctrlb_nxt
  coef_t    [1:0][ISIZE-1:0][ISIZE-1:0][1:0] c_int;   // mapped coefficients
  always_comb
  begin : cf_nxt_PROC
    logic     [1:0][ISIZE-1:0][ISIZE-1:0][1:0] c_nav;   // not avail bits to force coefficient to 0
    coef_t    [1:0][ISIZE-1:0]           [1:0] zof;     // zero offsets per output
    // default outputs
    c_int     = '0;
    c_nav     = '1;                 // set all coefficients as not available
    c_en      = cf_first ? '1 : '0; // reset coefficients to 0 in first no loop
    zof       = '0;
    ctrla_nxt = '0;
    ctrlb_nxt = '0;
    c_nxt     = '0;
    // default feature-map routing
    for (int v = 0; v < 2; v++)
    begin
      for (int o = 0; o < ISIZE; o++)
      begin
        for (int i = 0; i < ISIZE/2; i++)
        begin
          ctrla_nxt[v][o][i*2+0] = 3'b001; // fm0
          ctrla_nxt[v][o][i*2+1] = 3'b010; // fm1
          ctrlb_nxt[v][o][i*2+0] = 3'b010; // fm2
          ctrlb_nxt[v][o][i*2+1] = 3'b100; // fm3
        end
      end
    end
    // mode dependent switch
    casez ({conv_mode,fm_dbl,cf_dbl})
    {`NINO(conv_mode_8x1dws1),1'b0,1'b1},
    {`NINO(conv_mode_3x3dws1dl2),1'b0,1'b1},
    {`NINO(conv_mode_2x3dws2),1'b0,1'b1},
    {`NINO(conv_mode_3x3dws1),1'b0,1'b1}:
      begin
        // double coefficients, use 8b format with 2 set
        // fm8cf16 only use MAC EVEN
        // input coefficients as: [v2][i1][o2][o4][o2][i9]
        for (int v = 0; v < 2; v++) // v1/i1
        begin
          for (int oodd = 0; oodd < 2; oodd++) // o2
          begin
            for (int o = 0; o < 4; o++) // o4
            begin
              // o2
              coef_t    [1:0][ISIZE-1:0][1:0] ci;
              logic     [1:0][ISIZE-1:0][1:0] ni;
              logic     [1:0][ISIZE-1:0][1:0] ce;
              ci = {c_int[v][2*o+oodd*8+1], c_int[v][2*o+oodd*8+0]};
              ni = {c_nav[v][2*o+oodd*8+1], c_nav[v][2*o+oodd*8+0]};
              ce = {c_en [v][2*o+oodd*8+1], c_en [v][2*o+oodd*8+0]};
// spyglass disable_block W499
//SMD:Mismatch between function cal argument and input
//SJ :Ignore odd
              dw_fm8cf8(conv_mode, coef_data.c[v*8+oodd*4+o], ci, ni, ce, 0);
// spyglass enable_block W499
              {c_int[v][2*o+oodd*8+1], c_int[v][2*o+oodd*8+0]} = ci;
              {c_nav[v][2*o+oodd*8+1], c_nav[v][2*o+oodd*8+0]} = ni;
              {c_en [v][2*o+oodd*8+1], c_en[ v][2*o+oodd*8+0]} = ce;
            end // for (int o = 0; o < 4; o++)
          end // for (int oodd = 0; oodd < 2; oodd++)
        end // for (int v = 0; v < 1; v++)
      end
    {`NINO(conv_mode_8x1dws1),1'b1,1'b1},
    {`NINO(conv_mode_3x3dws1dl2),1'b1,1'b1},
    {`NINO(conv_mode_2x3dws2),1'b1,1'b1},
    {`NINO(conv_mode_3x3dws1),1'b1,1'b1}:
      begin
        // double coefficients, use 8b format with 2 set
        // fm16cf16 use both MAC EVEN/ODD
        // input coefficients as: [v2][i1][o2][o4][o2][i9]
        for (int v = 0; v < 2; v++) // v1/i1
        begin
          for (int oodd = 0; oodd < 2; oodd++) // o2
          begin
            for (int o = 0; o < 4; o++) // o4
            begin
              // o2
              coef_t    [1:0][ISIZE-1:0][1:0] ci;
              logic     [1:0][ISIZE-1:0][1:0] ni;
              logic     [1:0][ISIZE-1:0][1:0] ce;
              ci = {c_int[v][2*o+oodd*8+1], c_int[v][2*o+oodd*8+0]};
              ni = {c_nav[v][2*o+oodd*8+1], c_nav[v][2*o+oodd*8+0]};
              ce = {c_en [v][2*o+oodd*8+1], c_en [v][2*o+oodd*8+0]};
// spyglass disable_block W499
//SMD:Mismatch between function cal argument and input
//SJ :Ignore odd
              dw_fm16cf8(conv_mode, coef_data.c[v*8+oodd*4+o], ci, ni, ce);
// spyglass enable_block W499
              {c_int[v][2*o+oodd*8+1], c_int[v][2*o+oodd*8+0]} = ci;
              {c_nav[v][2*o+oodd*8+1], c_nav[v][2*o+oodd*8+0]} = ni;
              {c_en [v][2*o+oodd*8+1], c_en[ v][2*o+oodd*8+0]} = ce;
            end // for (int o = 0; o < 4; o++)
          end // for (int oodd = 0; oodd < 2; oodd++)
        end // for (int v = 0; v < 1; v++)
      end
    {`NINO(conv_mode_8x1dws1),1'b1,1'b0},
    {`NINO(conv_mode_3x3dws1dl2),1'b1,1'b0},
    {`NINO(conv_mode_2x3dws2),1'b1,1'b0},
    {`NINO(conv_mode_3x3dws1),1'b1,1'b0}:
      begin
        // double feature-map no double coefficients, replicate over odd outputs, no batching support
        // input coefficients as: [v1][i1][o1][o4][o2][i9]
        for (int v = 0; v < 1; v++)
        begin
          for (int oodd = 0; oodd < 2; oodd++)
          begin
            for (int o = 0; o < 4; o++)
            begin
              coef_t    [1:0][ISIZE-1:0][1:0] ci;
              logic     [1:0][ISIZE-1:0][1:0] ni;
              logic     [1:0][ISIZE-1:0][1:0] ce;
              ci = {c_int[v][2*o+oodd*8+1], c_int[v][2*o+oodd*8+0]};
              ni = {c_nav[v][2*o+oodd*8+1], c_nav[v][2*o+oodd*8+0]};
              ce = {c_en [v][2*o+oodd*8+1], c_en [v][2*o+oodd*8+0]};
// spyglass disable_block W499
//SMD:Mismatch between function cal argument and input
//SJ :Ignore odd
              dw_fm16cf8(conv_mode, coef_data.c[v*8+oodd*4+o], ci, ni, ce);
// spyglass enable_block W499
              {c_int[v][2*o+oodd*8+1], c_int[v][2*o+oodd*8+0]} = ci;
              {c_nav[v][2*o+oodd*8+1], c_nav[v][2*o+oodd*8+0]} = ni;
              {c_en [v][2*o+oodd*8+1], c_en[ v][2*o+oodd*8+0]} = ce;
            end // for (int o = 0; o < 4; o++)
          end // for (int oodd = 0; oodd < 2; oodd++)
        end // for (int v = 0; v < 1; v++)
      end
    {`NINO(conv_mode_8x1dws1),1'b0,1'b0},
    {`VIVO(conv_mode_3x3dws1),1'b0,1'b0},
    {`NINO(conv_mode_3x3dws1dl2),1'b0,1'b0},
    {`NINO(conv_mode_2x3dws2),1'b0,1'b0},
    {`NINO(conv_mode_3x3dws1),1'b0,1'b0}:
      begin
        if (isfp(mpy_cfg))
        begin
          // floating-point coefficients
          for (int v = 0; v < 2; v++) // v1/i1
          begin
            for (int oodd = 0; oodd < 2; oodd++) // o2
            begin
              for (int o = 0; o < 4; o++) // o4
              begin
                // o2
                coef_t    [1:0][ISIZE-1:0][1:0] ci;
                logic     [1:0][ISIZE-1:0][1:0] ni;
                logic     [1:0][ISIZE-1:0][1:0] ce;
                ci = {c_int[0][2*o+oodd*8+1], c_int[0][2*o+oodd*8+0]};
                ni = {c_nav[0][2*o+oodd*8+1], c_nav[0][2*o+oodd*8+0]};
                ce = {c_en [0][2*o+oodd*8+1], c_en [0][2*o+oodd*8+0]};
// spyglass disable_block W499
//SMD:Mismatch between function cal argument and input
//SJ :Ignore odd
                dw_fm8cf8(conv_mode, coef_data.c[v*8+oodd*4+o], ci, ni, ce, v);
// spyglass enable_block W499
                {c_int[0][2*o+oodd*8+1], c_int[0][2*o+oodd*8+0]} = ci;
                {c_nav[0][2*o+oodd*8+1], c_nav[0][2*o+oodd*8+0]} = ni;
                {c_en [0][2*o+oodd*8+1], c_en [0][2*o+oodd*8+0]} = ce;
              end // for (int o = 0; o < 4; o++)
            end // for (int oodd = 0; oodd < 2; oodd++)
          end // for (int v = 0; v < 2; v++)
        end
        else 
        begin
          // no double feature-map or coefficients ISIZE*9 per output group v, no batching support
          // input coefficients as: [v1][i1][o2][o4][o2][i9]
          for (int v = 0; v < 1; v++) // v1/i1
          begin
            for (int oodd = 0; oodd < 2; oodd++) // o2
            begin
              for (int o = 0; o < 4; o++) // o4
              begin
                // o2
                coef_t    [1:0][ISIZE-1:0][1:0] ci;
                logic     [1:0][ISIZE-1:0][1:0] ni;
                logic     [1:0][ISIZE-1:0][1:0] ce;
                ci = {c_int[v][2*o+oodd*8+1], c_int[v][2*o+oodd*8+0]};
                ni = {c_nav[v][2*o+oodd*8+1], c_nav[v][2*o+oodd*8+0]};
                ce = {c_en [v][2*o+oodd*8+1], c_en [v][2*o+oodd*8+0]};
// spyglass disable_block W499
//SMD:Mismatch between function cal argument and input
//SJ :Ignore odd
                dw_fm8cf8(conv_mode, coef_data.c[v*8+oodd*4+o], ci, ni, ce, 0);
// spyglass enable_block W499
                {c_int[v][2*o+oodd*8+1], c_int[v][2*o+oodd*8+0]} = ci;
                {c_nav[v][2*o+oodd*8+1], c_nav[v][2*o+oodd*8+0]} = ni;
                {c_en [v][2*o+oodd*8+1], c_en[ v][2*o+oodd*8+0]} = ce;
              end // for (int o = 0; o < 4; o++)
            end // for (int oodd = 0; oodd < 2; oodd++)
          end // for (int v = 0; v < 1; v++)
        end
      end
    {`NINO(conv_mode_4x1g2s1dl2),1'b1,1'b?},
    {`NINO(conv_mode_4x1g2s1),1'b1,1'b?},
    {`NINO(conv_mode_2x1s1),1'b1,1'b?},
    {`NINO(conv_mode_2x1s2),1'b1,1'b?},
    {`NINO(conv_mode_2x1s1dl2),1'b1,1'b?},
    {`DINO(conv_mode_1x1),1'b1,1'b?}:
      begin
        // double feature-map, replicate coefficients, use full multiplier array
        if (coef_mode_fm)
        begin
          // matrix*matrix mode, coefficient is also double
          // input : [i2][o16][i8][v2mlsb]
          // output: [v2mlsb][o16][i2*8+i8][copy]
          for (int v=0; v<2; v++)
          begin
            for (int o16=0; o16<16; o16++)
            begin
              for (int i2=0; i2<2; i2++)
              begin
                for (int i8=0; i8<8; i8++)
                begin
                  c_int[v][o16][i2*8+i8] |= {2{coef_data.c[i2*16+o16].coef[i8*2+v]}};
                  c_nav[v][o16][i2*8+i8] &= {2{coef_data.c[i2*16+o16].nav[i8*2+v]}};
                  c_en [v][o16][i2*8+i8] |= 2'b11;
                end
              end
            end
          end
        end
        else
        begin
          // 1*1*ISIZE*ISIZE coefficients per output group v, replicate even/odd, two batches
          // input : [v2mlsb][i2][o8][o2][i8]
          // output: [v2mlsb][o8*2+o2][i2*8+i8][copy]
          for (int v = 0; v < 2; v++)
          begin
            for (int o8 = 0; o8 < 8; o8++)
            begin
              for (int i2 = 0; i2 < 2; i2++)
              begin
                for (int o2 = 0; o2 < 2; o2++)
                begin
                  for (int i8 = 0; i8 < 8; i8++)
                  begin
                    c_int[v][o8*2+o2][i2*8+i8] |= {2{coef_data.c[v*16+i2*8+o8].coef[8*o2+i8]}};
                    c_nav[v][o8*2+o2][i2*8+i8] &= {2{coef_data.c[v*16+i2*8+o8].nav[8*o2+i8]}};
                    c_en [v][o8*2+o2][i2*8+i8] |= 2'b11;
                  end
                end
              end
            end
          end
        end // else: !if(coef_mode_fm)
      end // case: {`NINO(conv_mode_4x1g2s1dl2),1'b1,1'b?},...
    {`NINO(conv_mode_4x1g2s1dl2),1'b0,1'b?},
    {`NINO(conv_mode_4x1g2s1),1'b0,1'b?},
    {`NINO(conv_mode_2x1s1),1'b0,1'b?},
    {`NINO(conv_mode_2x1s2),1'b0,1'b?},
    {`NINO(conv_mode_2x1s1dl2),1'b0,1'b?},
    {`DINO(conv_mode_1x1),1'b0,1'b?}: 
      begin
        if (coef_mode_fm)
        begin
          // matrix*matrix mode, coefficient is also single
          // input:  [i2][o16][2*i8+iodd2]
          // output: [o16][i2*8+i8][iodd2]
          for (int o16=0; o16<16; o16++)
          begin
            for (int i2=0; i2<2; i2++)
            begin
              for (int i8=0; i8<8; i8++)
              begin
                for (int iodd=0; iodd<2; iodd++)
                begin
                  c_int[0][o16][i2*8+i8][iodd] |= coef_data.c[i2*16+o16].coef[i8*2+iodd];
                  c_nav[0][o16][i2*8+i8][iodd] &= coef_data.c[i2*16+o16].nav [i8*2+iodd];
                  c_en [0][o16][i2*8+i8][iodd] |= 1'b1;
                end
              end
            end
          end
        end
        else
        begin
          // input: [onn|inn|cmlsb][iodd2][i2][o8][o2][i8]
          // output:[onn|inn|cmlsb][o8*2+o2][8*i2+i8][iodd2]
          for (int v=0; v<2; v++)
          begin
            for (int o8=0; o8<8; o8++)
            begin
              for (int o2=0; o2<2; o2++)
              begin
                for (int b=0; b<2; b++)
                begin
                  for (int i8=0; i8<8; i8++)
                  begin
                    for (int oodd=0; oodd<2; oodd++)
                    begin
                      c_int    [v][o8*2+o2][b*8+i8][oodd] |= coef_data.c[v*32+oodd*2*8+b*8+o8].coef[o2*8+i8];
                      c_nav    [v][o8*2+o2][b*8+i8][oodd] &= coef_data.c[v*32+oodd*2*8+b*8+o8].nav [o2*8+i8];
                      c_en     [v][o8*2+o2][b*8+i8][oodd] |= 1'b1;
                    end
                  end
                end
              end
            end
          end
        end
        // reorder control bits for sparse mode
        if (sparse)
        begin
          for (int v=0; v<2; v++)
          begin
            for (int o8=0; o8<8; o8++)
            begin
              for (int b=0; b<2; b++)
              begin
                for (int i8=0; i8<8; i8++)
                begin
                  ctrla_nxt[v][o8*2  ][b*8+i8]        = decode_a(coef_data.c[v*32+b*8+o8].ctrla[i8]);
                  ctrla_nxt[v][o8*2+1][b*8+i8]        = decode_b(coef_data.c[v*32+b*8+o8].ctrlb[i8]);
                  ctrlb_nxt[v][o8*2  ][b*8+i8]        = decode_a(coef_data.c[v*32+2*8+b*8+o8].ctrla[i8]);
                  ctrlb_nxt[v][o8*2+1][b*8+i8]        = decode_b(coef_data.c[v*32+2*8+b*8+o8].ctrlb[i8]);
                end
              end
            end
          end
        end

      end
    {`FC(conv_mode_fc),1'b1,1'b?}:
      begin
        // ISIZE*ISIZE/2 coefficients per output group v, replicate col even/odd, no inn/onn support
        // input coefficients as: [v1][i1][o8][o2][i8]
        for (int v=0; v<2; v++)
        begin
          for (int o = 0; o < 8; o++)
          begin
            for (int r = 0; r < 2; r++)
            begin
              for (int j = 0; j < 8; j++)
              begin
                c_int[v][o*2+r][j] |= {2{coef_data.c[v*8+o].coef[8*r+j]}};
                c_nav[v][o*2+r][j] &= {2{coef_data.c[v*8+o].nav[8*r+j]}};
                c_en [v][o*2+r][j] |= 2'b11;
              end
            end
          end
        end
      end
    default:
      // {`FC(conv_mode_fc),1'b0,1'b?},
      // {`NINO(conv_mode_1x1),1'b0,1'b0}
      // {`NINO(conv_mode_2x1g2s2),1'b?,1'b?},
      begin
        // input coefficients as: [cmlsb][i2][o8][o2][i8]
        for (int v=0; v<2; v++)
        begin
          for (int o8=0; o8<8; o8++)
          begin
            for (int o2=0; o2<2; o2++)
            begin
              for (int i8=0; i8<8; i8++)
              begin
                for (int i2=0; i2<2; i2++)
                begin
                  c_int    [v][o8*2+o2][i8][i2] |= coef_data.c[v*16+i2*8+o8].coef [o2*8+i8];
                  c_nav    [v][o8*2+o2][i8][i2] &= coef_data.c[v*16+i2*8+o8].nav  [o2*8+i8];
                  c_en     [v][o8*2+o2][i8][i2] |= 1'b1;
                end
              end
            end
          end
        end
        // reorder control bits for sparse mode
        if (sparse)
        begin
          for (int v=0; v<2; v++)
          begin
            for (int o8=0; o8<8; o8++)
            begin
                for (int i8=0; i8<8; i8++)
                begin
                  ctrla_nxt[v][o8*2  ][i8]        = decode_a(coef_data.c[v*16+o8].ctrla[i8]);
                  ctrla_nxt[v][o8*2+1][i8]        = decode_b(coef_data.c[v*16+o8].ctrlb[i8]);
                  ctrlb_nxt[v][o8*2  ][i8]        = decode_a(coef_data.c[v*16+8+o8].ctrla[i8]);
                  ctrlb_nxt[v][o8*2+1][i8]        = decode_b(coef_data.c[v*16+8+o8].ctrlb[i8]);
                end
            end
          end
        end

      end
    endcase // casez ({conv_mode,fm_dbl,cf_dbl})
    //
    // Decode zero-offset
    //
    // feature-map, can be sparse or onn=2
    if (onn)
    begin
      // two output sets
      for (int v = 0; v < 2; v++)
      begin
        for (int o = 0; o < ISIZE; o++)
        begin
          for (int eo = 0; eo < 2; eo++)
          begin
            zof[v][o][eo] |= coef_data.zp[v*16+o];
          end
        end
      end
    end
    else if (sparse)
    begin
      // two output sets, interleaved
      for (int v = 0; v < 2; v++)
      begin
        for (int o = 0; o < ISIZE; o++)
        begin
          for (int eo = 0; eo < 2; eo++)
          begin
            zof[v][o][eo] |= coef_data.zp[o+eo*16];
          end
        end
      end
    end
    else
    begin
      // two set of outputs, same zero-points
      for (int v = 0; v < 2; v++)
      begin
        for (int o = 0; o < ISIZE; o++)
        begin
          for (int eo = 0; eo < 2; eo++)
          begin
            zof[v][o][eo] |= coef_data.zp[o];
          end
        end
      end
    end
    //
    // If not available then force input feature-map to 0, process in groups of 4
    //
    for (int v = 0; v < 2; v++) 
    begin
      for (int o = 0; o < ISIZE; o++) 
      begin
        for (int i = 0; i < ISIZE/2; i++) 
        begin
          if (c_nav[v][o][i*2+0][0])
          begin
            ctrla_nxt[v][o][i*2+0] = 3'd0;
          end
          if (c_nav[v][o][i*2+0][1])
          begin
            ctrla_nxt[v][o][i*2+1] = 3'd0;
          end
          if (c_nav[v][o][i*2+1][0])
          begin
            ctrlb_nxt[v][o][i*2+0] = 3'd0;
          end
          if (c_nav[v][o][i*2+1][1])
          begin
            ctrlb_nxt[v][o][i*2+1] = 3'd0;
          end
        end
      end
    end
    //
    // Apply zero offset
    //
    for (int v = 0; v < 2; v++)
    begin
      for (int o = 0; o < ISIZE; o++)
      begin
        for (int i = 0; i < ISIZE; i++)
        begin

          c_nxt[v][o][i].sgn = c_int[v][o][i][1][7];
          if (NPU_HAS_FLOAT && isfp16(mpy_cfg))
          begin
            logic [4:0] e;
            // uint5 exponent, recode to 8b, adjust bias
            e = c_int[v][o][i][1][6:2];
            c_nxt[v][o][i].int9[8:0]      = {4'b000,e} - 9'd15;
            c_nxt[v][o][i].nan        = &e;
            c_nxt[v][o][i].zero       = ~|e;
            // int10 mantissa
            c_nxt[v][o][i].int10      = {c_int[v][o][i][1][1:0], c_int[v][o][i][0][7:0]};
          end
          else if (NPU_HAS_FLOAT && isbf16(mpy_cfg))
          begin
            logic [7:0] e;
            // uint8 exponent
            e = {c_int[v][o][i][1][6:0], c_int[v][o][i][0][7]};
            c_nxt[v][o][i].int9[8:0]    = {1'b0,e} - 9'd127;
            c_nxt[v][o][i].nan        = &e;
            c_nxt[v][o][i].zero       = ~|e;
            // even has mantissa
            c_nxt[v][o][i].int10      = {c_int[v][o][i][0][6:0],3'b000};
          end // if (isbf16(mpy_cfg))
          else
          begin
            c_nxt[v][o][i].sgn=0;
            c_nxt[v][o][i].nan=0;
            c_nxt[v][o][i].zero=0;
            // 0
            if ((cf_dbl && (v == 0)))
            begin
              // lsb part of double coefficient, zero extend (no zero-point)
              c_nxt[v][o][i].int10 = {2'b00, c_int[0][o][i][0]};
            end
            else
            begin
              // subtract signed zero-point with sign extension
              c_nxt[v][o][i].int10 = {{2{c_int[v][o][i][0][7]}},c_int[v][o][i][0]} - {{2{zof[v][o][0][7]}},zof[v][o][0]};
              c_nxt[v][o][i].sgn = c_nxt[v][o][i].int10[9];
            end
            // 1
            if ((cf_dbl && (v == 0)))
            begin
              // lsb part of double coefficient, zero extend (no zero-point)
              c_nxt[v][o][i].int9 = {2'b00, c_int[0][o][i][1]};
            end
            else
            begin
              // subtract signed zero-point with sign extension
              c_nxt[v][o][i].int9 = {c_int[v][o][i][1][7],c_int[v][o][i][1]} - {zof[v][o][1][7],zof[v][o][1]};
            end
          end
        end
      end
    end
    if (!cf_en)
    begin
      c_en = '0;
    end
  end : cf_nxt_PROC


  // do preselection on feature-map control bits
  // outputs: ctrl_out_en, ctrla_out_nxt, ctrlb_out_nxt
  always_comb
  begin : cf_presel_PROC
    // default
    ctrl_out_en        = 1'b0;
    ctrla_out_nxt      = '0;
    ctrlb_out_nxt      = '0;
    if (cf_en)
    begin
      // select first set
      ctrl_out_en      = 1'b1;
      ctrla_out_nxt   |= ctrla_nxt[0];
      ctrlb_out_nxt   |= ctrlb_nxt[0];
    end
    else 
    begin
      ctrl_out_en      = ctrl_tgl;
      // toggle even/odd sets
      if (ctrl_sel[0])
      begin
        ctrla_out_nxt |= ctrla_r[0];
        ctrlb_out_nxt |= ctrlb_r[0];
      end
      if (ctrl_sel[1])
      begin
        ctrla_out_nxt |= ctrla_r[1];
        ctrlb_out_nxt |= ctrlb_r[1];
      end
    end
  end : cf_presel_PROC


  // do sparse swap logic here!
  always_comb
  begin : sparse_sw_PROC

    ctrla_sel = ctrla_out_nxt;
    ctrlb_sel = ctrlb_out_nxt;
    if (sparse)
    begin
      for (int o=0;o<ISIZE;o++)
      begin
        for (int i=0;i<ISIZE/2;i++)
        begin
          logic [2:0] ca;
          logic [2:0] cb;
          // sparse swap!
          ca = ctrla_sel[o][i][1];
          cb = ctrlb_sel[o][i][0];
          ctrla_sel[o][i][1] = cb;
          ctrlb_sel[o][i][0] = ca;
        end
      end
    end

  end : sparse_sw_PROC
    

  
  // Coefficients register
  // outputs: c_r, ctrla_r, ctrlb_r, ctrla_out_r, ctrlb_out_r
  always_ff @(posedge clk or posedge rst_a)
  begin : cf_reg_PROC
    if (rst_a == 1'b1)
    begin
      c_r         <= '0;
      ctrla_r     <= '0;
      ctrlb_r     <= '0;
    end
    else
    begin
      // two output groups
      for (int b = 0; b < 2; b++)
      begin
        // ISIZE outputs per group
        for (int o = 0; o < ISIZE; o++)
        begin
          // 2*ISIZE inputs per group
          for (int i = 0; i < ISIZE/2; i++)
          begin
            if (c_en[b][o][2*i+0][0])
            begin
              ctrla_r[b][o][2*i+0] <= ctrla_nxt[b][o][2*i+0];
            end
            if (c_en[b][o][2*i+0][1])
            begin
              ctrla_r[b][o][2*i+1] <= ctrla_nxt[b][o][2*i+1];
            end
            if (c_en[b][o][2*i+1][0])
            begin
              ctrlb_r[b][o][2*i+0] <= ctrlb_nxt[b][o][2*i+0];
            end
            if (c_en[b][o][2*i+1][1])
            begin
              ctrlb_r[b][o][2*i+1] <= ctrlb_nxt[b][o][2*i+1];
            end
            if (|c_en[b][o][2*i+0])  // capture the reg when either en are set now!!!
            begin
              c_r[b][o][2*i+0] <= c_nxt[b][o][2*i+0];
            end
            if (|c_en[b][o][2*i+1])  // capture the reg when either en are set now!!!
            begin
              c_r[b][o][2*i+1] <= c_nxt[b][o][2*i+1];
            end
          end
        end
      end
    end // else: !if(rst_a == 1'b1)
  end : cf_reg_PROC
// spyglass enable_block SelfDeterminedExpr-ML  

endmodule : npu_conv_mpy_cf
