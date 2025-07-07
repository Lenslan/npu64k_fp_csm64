// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//  ####            #       ###
//  #   #     #     #      #   #
//  #   #           #      #
//  #   #    ##    ####    #       ####    ####   # ###
//  ####      #     #       ###   #    #       #  ##   #
//  #   #     #     #          #  #        #####  #    #
//  #   #     #     #          #  #       #    #  #    #
//  #   #     #     #  #   #   #  #    #  #   ##  #    #
//  ####    #####    ##     ###    ####    ### #  #    #
//
// ===========================================================================
//
// Description:
//
//  The bitscan module is used to find the first 1 or 0 bit in the
//  source operand.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Global constants and timescales
//
`include "const.def"

// ===========================================================================
// The following four signals are used to control operations within
// the bitscan group, which includes NORM, NORMW, FFS and FLS
//
//  Instruction    norm_op    signed_op   half_size   byte_size
//  ------------------------------------------------------------
//     NORM          1            1          0            0
//     NORMW         1            1          1            0
//     FFS           1            0          0            0
//     FLS           1            0          0            1
//
// ===========================================================================

module npuarc_alb_bitscan (
  input                       norm_op,      // any of NORM, NORMW, FFS, FLS
  input   [`npuarc_DATA_RANGE]       src2_val,     // single input operand
  input                       signed_op,    // operation is NORM or NORMW
  input                       half_size,    // source is 16-bit signed
  input                       byte_size,    // 1 => fls, 0 => ffs

  output  [4:0]               scan_result,  // bitscan output
  output                      zero,         // source is zero
  output                      negative      // source is negative
);


//////////////////////////////////////////////////////////////////////////////
// Connectivity signal declaration                                          //
//////////////////////////////////////////////////////////////////////////////

wire    [30:0]       ffs_src;
wire    [30:0]       fls_src;

wire    [30:0]              src31;
wire    [14:0]              src15;
wire    [14:0]              word_hi;
wire    [14:0]              word_lo;
wire    [3:0]               result_hi;
wire    [3:0]               result_lo;
wire                        no_hit_hi;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused signal from standard module
// spyglass disable_block W528
// SMD: signal set but not read
// SJ:  unused in this module but standard in other modules
wire                        no_hit_lo;
// leda NTL_CON13A on
// spyglass enable_block W528
wire                        sel_lo;
wire                        sel_pos;
wire                        sel_neg;
wire                        sel_ffs;
wire                        sel_fls;

wire    [4:0]               distance;

// To compute the 'find-first-set' (FFS) instruction, the input operand
// bits have to be reversed, and the most-significant bit set to zero.
//
assign ffs_src = {
                src2_val[0],  src2_val[1],  src2_val[2],
  src2_val[3],  src2_val[4],  src2_val[5],  src2_val[6],
  src2_val[7],  src2_val[8],  src2_val[9],  src2_val[10],
  src2_val[11], src2_val[12], src2_val[13], src2_val[14],
  src2_val[15], src2_val[16], src2_val[17], src2_val[18],
  src2_val[19], src2_val[20], src2_val[21], src2_val[22],
  src2_val[23], src2_val[24], src2_val[25], src2_val[26],
  src2_val[27], src2_val[28], src2_val[29], src2_val[30]
};

// To compute the 'find-last-set' (FLS) instruction, the input bits must be
// shifted to the right by one bit-position.
//
assign fls_src = src2_val[31:1];

//////////////////////////////////////////////////////////////////////////////
// Connectivity assignments                                                 //
//                                                                          //
//  Note: all inputs are gated with norm_op to prevent unwanted transitions //
//  in the bitscan logic when not performing one of the NORM_OPTION insns   //
//////////////////////////////////////////////////////////////////////////////

assign sel_pos = norm_op &   src2_val[31]  &  signed_op;
assign sel_neg = norm_op & (~src2_val[31]) &  signed_op;
assign sel_ffs = norm_op & (~byte_size)    & (~signed_op);
assign sel_fls = norm_op &   byte_size     & (~signed_op);

assign src31 = ((~src2_val[30:0]) & {31{sel_pos}})
             | (  src2_val[30:0]  & {31{sel_neg}})
             | (  ffs_src[30:0]   & {31{sel_ffs}})
             | (  fls_src[30:0]   & {31{sel_fls}})
             ;

assign src15 = ((~src2_val[14:0]) & {15{norm_op & src2_val[15] & signed_op}})
             | ( src2_val[14:0] & {15{norm_op & (~src2_val[15]) & signed_op}})
             ;

assign word_hi = src31[30:16]  & {15{(~half_size)}};

assign word_lo = ( src15       & {15{ half_size}})
               | ( src31[14:0] & {15{(~half_size)}});

assign sel_lo  = half_size | no_hit_hi;

//////////////////////////////////////////////////////////////////////////////
// Sub-module instantiation                                                 //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_bitscan_16b u_alb_bitscan_16b_hi(
  .din     (word_hi     ),
  .dout    (result_hi   ),
  .no_hit  (no_hit_hi   )
);

npuarc_alb_bitscan_16b u_alb_bitscan_16b_lo(
  .din     (word_lo     ),
  .dout    (result_lo   ),
  .no_hit  (no_hit_lo   )
);

//////////////////////////////////////////////////////////////////////////////
// Output assignments                                                       //
//////////////////////////////////////////////////////////////////////////////

assign negative = norm_op & (half_size ? src2_val[15] : src2_val[31]);

assign zero     = ( (src2_val == 32'd0)       & (~half_size) & norm_op)
                | ( (src2_val[15:0] == 16'd0) &  half_size & norm_op);

assign distance[4]   = (1'b0 & half_size)
                     | (no_hit_hi & (~src31[15]) & (~half_size));

assign distance[3:0] = (result_hi & {4{(~sel_lo)}})
                     | (   (result_lo | {4{(~half_size) & src31[15]}})
                         & {4{ sel_lo}}
                       )
                     ;

 assign scan_result = {5{byte_size}} ^ distance;

endmodule
