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
// File defining the convolution specific datatypes in a package
//

`include "npu_conv_macros.svh"


package npu_conv_types;

  import npu_types::*;

  // ID field in the MMIO ID registers
  localparam int CONV_ID_INT = 0; // Int8 and int16 support only
  localparam int CONV_ID_FLT = 8; // Add also FP16 and BF 16 support (on top of int8/int16)
  // MAJOR version field in the MMIO ID register
  localparam int CONV_MAJ = 2;
  // MINOR version field in the MMIO ID register
  localparam int CONV_MIN = 0;

  // convolution mode
  typedef enum logic [3:0] {
    // grouped layers
    /* 0*/`NINO(conv_mode_4x1g2s1),
    /* 1*/`NINO(conv_mode_4x1g2s1dl2),
    /* 2*/`NINO(conv_mode_2x1g2s2),
    // convolutions
    /* 3*/`DINO(conv_mode_1x1),
    /* 4*/`NINO(conv_mode_1x1),
    /* 5*/`NINO(conv_mode_2x1s1),
    /* 6*/`NINO(conv_mode_2x1s2),
    /* 7*/`NINO(conv_mode_2x1s1dl2),
    // depthwise
    /* 8*/`NINO(conv_mode_3x3dws1),
    /* 9*/`NINO(conv_mode_2x3dws2),
    /*10*/`NINO(conv_mode_3x3dws1dl2),
    /*11*/`NINO(conv_mode_8x1dws1),
    /*12*/`NINO(conv_mode_4x1dws1),
    /*13*/`VIVO(conv_mode_3x3dws1),
    // fully connected
    /*14*/`FC(conv_mode_fc)
  } conv_mode_t;

  // coefficient mode
  typedef enum logic [1:0] {
    /*0*/coef_mode_uncompressed,
    /*1*/coef_mode_compressed,
    /*2*/coef_mode_sparse,
    /*3*/coef_mode_fm
  } coef_mode_t;

  typedef enum logic [1:0] {
                            /*0*/ fm_cfg_8b_e,
                            /*1*/ fm_cfg_16b_e,
                            /*2*/ fm_cfg_bf16_e,
                            /*3*/ fm_cfg_fp16_e
                            } fm_cfg_t;

  typedef enum logic [2:0] {
                            /*0*/ cf_cfg_4b_zp_e,
                            /*1*/ cf_cfg_4b_nozp_e,
                            /*2*/ cf_cfg_8b_zp_e,
                            /*3*/ cf_cfg_8b_nozp_e,
                            /*4*/ cf_cfg_16b_e,
                            /*5*/ cf_cfg_bf16_e,
                            /*6*/ cf_cfg_fp16_e
                            } cf_cfg_t;
  
  // quadrant information
  typedef struct packed {
    offset_t       doffs;  // VM data address offset
    offset_t [2:0] pdoffs; // Column/row/depth padding offset
  } quadrant_t;

  // scalar information
  typedef struct packed {
    vm_addr_t      ptr;    // Start of column in VM memory
    offset_t [2:0] ppos;   // Column/row/depth padding position
  } vm_scalar_t;

  // padding information and row/chan/fm last bits
  typedef struct packed {
    logic [NUM_FM_QUEUE-1:0][3:0] pad;    // pad per lanes
    logic                         flast;  // last in feature-map
    logic                         clast;  // last in channel
    logic                         rlast;  // last in row
  } stash_pad_t;

  // data from stash to multiplier array
  typedef ixpix_t [NUM_FM_QUEUE-1:0] stash_data_t;

  typedef struct packed {
    stash_data_t               data;  // VM data
    stash_pad_t                pad;   // padding bits and pos info
  } vm_vector_t;

  //
  // Convolution HLAPI input type
  //
  typedef struct packed {
    // r31
    logic       [5:0]      pd7;         //  6b: pad to 32b
    pack_mode_t            pack_mode;   //  2b: spatial packing padding mode
    logic       [1:0]      pd6;         //  2b: pad to 24b
    logic                  keep_acc;    //  1b: use input accumulator
    logic                  use_acc;     //  1b: use input accumulator
    logic       [0:0]      pd5;         //  1b: pad to 20b
    cf_cfg_t               cf_cfg;      //  3b: coefficient mode config
    logic       [1:0]      pd4;         //  1b: pad to 16b
    fm_cfg_t               fm_cfg;      //  2b: feature mode config
    logic       [1:0]      pd3;         //  2b: pad to 12b
    coef_mode_t            cf_mode;     //  2b: coefficient compression mode, 2b
    logic       [3:0]      pd2;         //  4b: pad to 8b
    conv_mode_t            conv_mode;   //  4b: convolution mode, 4b
    // r26-30: 160b
    logic       [5:0]      pd1;         //   6b: pad to 32b
    am_addr_t              acc_ptr;     //  10b: accumulator start pointer, 10b
    vm_addr_t              cf_ptr;      //  16b: coefficient buffer pointer, 16b
    offset_t    [3:0]      cf_offset;   //  64b: coefficient offset from end of one axis to start of next, 4*16b
    offset_t    [3:0]      cf_iter;     //  64b: coefficient iterator, 4*16b
    //r16-25: 320b
    logic       [15:0]     pd0;         //  16b: pad to 32b
    quadrant_t  [3:0]      quad_data;   // 256b: quadrant offsets
    offset_t    [2:0]      quad_iter;   //  48b: quadrant iteration
    // r8-15: 256b
    vm_addr_t              pad_ptr;     //  16b: Padding buffer pointer, 16b
    offset_t    [2:0]      fm_offsets;  //  48b: pointer offset from one element to next per dimension, 3*16b
    offset_t    [2:0]      fm_poffsets; //  48b: padding offset from one element to next per dimension, 3*16b
    offset_t    [2:0]      fm_padpos;   //  48b: padding start position, 3*16b
    offset_t    [2:0]      fm_padlim;   //  48b: padding window limits, 3*16b
    offset_t               fm_buf_len;  //  16b: Feature-map buffer length, 16b
    vm_addr_t              fm_buf_base; //  16b: Feature-map buffer descriptor base address, 16b
    vm_addr_t              fm_ptr;      //  16b: Feature-map buffer pointer, 16b
    // r4-7: 128b
    offset_t    [7:0]      iter;        // 128b: [grp][no][ni][qd][col][row][inn][onn], 8*16b
    // r0-3: 128b
    hlapi_i_t              common;      // 128b: common attributes
  } conv_hlapi_i_t;


  //
  // Convolution HLAPI type
  //
  typedef struct packed {
    hlapi_o_t      o;
    hlapi_io_t     io;
    conv_hlapi_i_t i;
  } conv_hlapi_t;


  //
  // Implementation types
  //

  // 9b coefficient
  typedef logic [8:0] coef9_t;


    // convolution input feature-map data
  typedef struct packed {
    logic       sgn;   // fp sign, don't care in int mode
    logic       zero;  // fp zero, don't care in int mode
    logic       nan;   // fp nan, don't care in int mode
    logic [7:0] int8;  // int8 msb, uint8 fp exponent
    logic [9:0] int10; // int9 lsb or uint10 fp mantissa
  } mpy_fm_t;
  
  // convolution input feature-map data
  typedef struct packed {
    logic       sgn;   // fp sign, don't care in int mode
    logic       zero;  // fp zero, don't care in int mode
    logic       nan;   // fp nan, don't care in int mode
    logic [8:0] int9;  // int9 msb, uint8 fp exponent
    logic [9:0] int10; // int9 lsb or uint10 fp mantissa
  } mpy_cf_t;

  typedef union packed {
    struct packed {
      logic [6:0] pad;    // pad to 17b
      logic       sgn;    // sign of result
      logic       zero;   // result is 0
      logic [7:0] e;      // exponent add rslt
    } f;                  // floating point mode struct
    logic [16:0]  i;      // integer mode product
  } prodb_t;

  typedef struct packed {
    logic                        nan;      // aggregated nan
    logic   [ISIZE-1:0][21:0]    proda;    // FP product or INT lsb product
    prodb_t [ISIZE-1:0]          prodb;    // INT msb product or exponent delta in FP mode
    logic   [7:0]                maxexp;   // max exponent in FP mode  
  } out_prods_t;


  
  typedef struct packed {
    logic   [20:0]         sum_lower;      // lsb sum  for INT or FP
    logic   [20:0]         sum_upper;      // msb sum  for INT or FP
    logic   [7:0]          maxexp;         // max exponent in FP mode
    logic                  nan;            // aggregated nan
  } out_sums_t;

  
  typedef struct packed {
    logic   [30:0]         lo;             // lo sum
    logic   [20:0]         hi;             // hi sum
    logic   [7:0]          maxexp;         // max exponent in FP mode
    logic                  nan;            // aggregated nan
  } out_sns_t;

  
  
  typedef union packed {
    struct packed {
      logic [31:0] pad2;
      logic sgn;
      logic [7:0] e;
      logic [22:0] m;
    } f;
    struct packed {
      logic [31:0] sum1;
      logic [31:0] sum0;
    } i;
  } out_norms_t;



  
  // MUX selectors for convolution datapath, used for groups of 4 multipliers
  typedef enum logic [1:0] {
    selafix0, // even multiplier selects fixed 0       (decompression)
    selafm0,  // even multiplier selects feature-map 0 (sparse mode or lsb of 16b FM)
    selafm1,  // even multiplier selects feature-map 1 (sparse mode only)
    selafm2   // even multiplier selects feature-map 2 (sparse mode or lsb of 16b FM)
  } coef_sela_t;
  typedef enum logic [1:0] {
    selbfix0, // odd multiplier selects fixed 0       (decompression)
    selbfm1,  // odd multiplier selects feature-map 1 (sparse mode or msb of 16b FM)
    selbfm2,  // odd multiplier selects feature-map 2 (sparse mode only)
    selbfm3   // odd multiplier selects feature-map 3 (sparse mode or msb of 16b FM)
  } coef_selb_t;
  // group of 8+1 coefficients and (4+4) MUX selectors (decompression atom)
  typedef struct packed {
    coef_sela_t [7:0]  ctrla;   // even sparse feature-map selector
    coef_selb_t [7:0]  ctrlb;   // odd sparse feature-map selector
    coef_t      [15:0] coef;    // coefficient
    coef_t      [1:0]  spare;   // spare coefficients for 3x3dw modes
    logic       [17:0] nav;     // force coefficient zero-point in compressed mode
  } coef_atom_t;

  // coefficients from decoder to multiplier array
  typedef struct packed {
    coef_atom_t [4*ISIZE*ISIZE/16-1:0] c;
    coef_t      [2*ISIZE-1:0]          zp;
  } coef_data_t;

  // multiplier type: one hot
  typedef enum  logic [6:0] {
                              i_8b8b_e     = 7'b0000001,
                              i_8b16b_e    = 7'b0000010,
                              i_16b8b_e    = 7'b0000100,
                              i_16b16b_e   = 7'b0001000,
                              i_sparse_e   = 7'b0010000,
                              f_bfloat16_e = 7'b0100000,
                              f_fp16_e     = 7'b1000000
                              } mpy_cfg_t;

  function automatic logic isfp16(input mpy_cfg_t c);
    return c[6];
  endfunction : isfp16
  function automatic logic isbf16(input mpy_cfg_t c);
    return c[5];
  endfunction : isbf16
  function automatic logic isfp(input mpy_cfg_t c);
    return c[5] | c[6];
  endfunction : isfp

  

  function automatic logic issparse(input mpy_cfg_t c);
    return c[4];
  endfunction : issparse
  function automatic logic isfmdblcfdbl(input mpy_cfg_t c);
    return c[3];
  endfunction : isfmdblcfdbl
  function automatic logic isfmdblcfdblorsparse(input mpy_cfg_t c);
    return c[4] | c[3];
  endfunction : isfmdblcfdblorsparse
  function automatic logic isfmdbl(input mpy_cfg_t c);
    return c[2] | c[3];
  endfunction : isfmdbl
  function automatic logic iscfdbl(input mpy_cfg_t c);
    return c[1] | c[3];
  endfunction : iscfdbl
  function automatic logic isfm8b(input mpy_cfg_t c);
    return c[0] | c[1];
  endfunction : isfm8b
   
   // structs for visibility of float formats in waves
   typedef struct packed {
      logic       sign;
      logic [7:0] exp;
      logic [6:0] frac;
   } bfloat_t;
   typedef struct packed {
      logic       sign;
      logic [4:0] exp;
      logic [9:0] frac;
   } fp16_t;


  // multiplier data types
  typedef logic [16:0]                       prod_t;    // multiplier product output
  typedef logic [20:0]                       sum_t;     // 16* 17b signed prod yields signed 21b

  // Shared Size
  localparam int OFF_SZ = $bits(offset_t);
  localparam int STR_SZ = OFF_SZ * NUM_FM_QUEUE;
  localparam int BUF_SZ = $bits(buf_t);
  localparam int FMO_C=0; localparam int FMO_W=1; localparam int FMO_H=2;
  localparam int CFO_C=0; localparam int CFO_H=1;
endpackage : npu_conv_types
