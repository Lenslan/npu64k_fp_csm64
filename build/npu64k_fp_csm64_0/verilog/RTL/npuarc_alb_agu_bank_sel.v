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
//  
//  
//  AGU_BANK_SEL
//  
//  
//  
//
// ===========================================================================
//
// Description: 
//
//
//  This module constains no state elements.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_agu_bank_sel (
  /////////// Inputs //////////////////////////////////////////////////
  //
  input                  x1_byte_size_r,     
  input                  x1_half_size_r,     
  input                  x1_double_size_r,

  input [3:0]            x1_src1,
  input [3:0]            x1_src2,
  
  /////////// Outputs /////////////////////////////////////////////
  //
  output [3:0]           x1_bank_sel
);

// Local Declarations
//

reg [3:0]   s0;
reg [2:0]   c0;
reg [3:0]   s1;
reg [2:0]   c1;
reg [3:0]   s2;
reg [2:0]   c2;
reg [3:0]   s3;
reg [2:0]   c3;
reg [3:0]   s4;
reg [2:0]   c4;
reg [3:0]   s5;
reg [2:0]   c5;
reg [3:0]   s6;
reg [2:0]   c6;
reg [3:0]   s7;
reg [2:0]   c7;
reg [3:0]   s8;
reg [2:0]   c8;
reg [3:0]   s9;
reg [2:0]   c9;
reg [3:0]   s10;
reg [2:0]   c10;
reg [3:0]   s11;
reg [2:0]   c11;
reg [3:0]   s12;
reg [2:0]   c12;
reg [3:0]   s13;
reg [2:0]   c13;
reg [3:0]   s14;
reg [2:0]   c14;
reg [3:0]   s15;
reg [2:0]   c15;
reg [15:0]  z;

reg [15:0]  hword_vec;
reg [15:0]  word_vec; 
reg [15:0]  dword_vec;
reg [15:0]  byte_sel;
// leda NTL_CON13A off
//LMD:Unused MSB
//LJ: Ignore this bit
reg         unused_bit;
// leda NTL_CON13A on
//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic defining  bit vector          
// Optimized logic to detect when (src1 + src2 == Ki)  
//////////////////////////////////////////////////////////////////////////
always @*
begin : z_bit_vector_PROC
  s0   = x1_src1  ^ x1_src2 ^ 4'd15;
  {unused_bit, c0}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd15) | (x1_src2 & 4'd15);
  z[0] = &(s0 ^ {c0,1'b0});
  
  s1   = x1_src1  ^ x1_src2 ^ 4'd14;
  {unused_bit, c1}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd14) | (x1_src2 & 4'd14);
  z[1] = &(s1 ^ {c1,1'b0});
  
  s2   = x1_src1  ^ x1_src2 ^ 4'd13;
  {unused_bit, c2}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd13) | (x1_src2 & 4'd13);
  z[2] = &(s2 ^ {c2,1'b0});
  
  s3   = x1_src1  ^ x1_src2 ^ 4'd12;
  {unused_bit, c3}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd12) | (x1_src2 & 4'd12);
  z[3] = &(s3 ^ {c3,1'b0});
  
  s4   = x1_src1  ^ x1_src2 ^ 4'd11;
  {unused_bit, c4}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd11) | (x1_src2 & 4'd11);
  z[4] = &(s4 ^ {c4,1'b0});
  
  s5   = x1_src1  ^ x1_src2 ^ 4'd10;
  {unused_bit, c5}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd10) | (x1_src2 & 4'd10);
  z[5] = &(s5 ^ {c5,1'b0});
  
  s6   = x1_src1  ^ x1_src2 ^ 4'd9;
  {unused_bit, c6}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd9) | (x1_src2 & 4'd9);
  z[6] = &(s6 ^ {c6,1'b0});
  
  s7   = x1_src1  ^ x1_src2 ^ 4'd8;
  {unused_bit, c7}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd8) | (x1_src2 & 4'd8);
  z[7] = &(s7 ^ {c7,1'b0});
  
  s8   = x1_src1  ^ x1_src2 ^ 4'd7;
  {unused_bit, c8}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd7) | (x1_src2 & 4'd7);
  z[8] = &(s8 ^ {c8,1'b0});
  
  s9   = x1_src1  ^ x1_src2 ^ 4'd6;
  {unused_bit, c9}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd6) | (x1_src2 & 4'd6);
  z[9] = &(s9 ^ {c9,1'b0});
  
  s10   = x1_src1  ^ x1_src2 ^ 4'd5;
  {unused_bit, c10}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd5) | (x1_src2 & 4'd5);
  z[10] = &(s10 ^ {c10,1'b0});
  
  s11   = x1_src1  ^ x1_src2 ^ 4'd4;
  {unused_bit, c11}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd4) | (x1_src2 & 4'd4);
  z[11] = &(s11 ^ {c11,1'b0});
  
  s12   = x1_src1  ^ x1_src2 ^ 4'd3;
  {unused_bit, c12}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd3) | (x1_src2 & 4'd3);
  z[12] = &(s12 ^ {c12,1'b0});
  
  s13   = x1_src1  ^ x1_src2 ^ 4'd2;
  {unused_bit, c13}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd2) | (x1_src2 & 4'd2);
  z[13] = &(s13 ^ {c13,1'b0});
  
  s14   = x1_src1  ^ x1_src2 ^ 4'd1;
  {unused_bit, c14}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd1) | (x1_src2 & 4'd1);
  z[14] = &(s14 ^ {c14,1'b0});
  
  s15   = x1_src1  ^ x1_src2 ^ 4'd0;
  {unused_bit, c15}   = (x1_src1 & x1_src2) | (x1_src1 & 4'd0) | (x1_src2 & 4'd0);
  z[15] = &(s15 ^ {c15,1'b0});
  
end


//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic rotating vectors         
//                                                                        
//////////////////////////////////////////////////////////////////////////
always @*
begin : vec_rotate_PROC
  hword_vec = {z[14:0], z[15]};    // rotate by 1
  word_vec  = {z[12:0], z[15:13]}; // rotate by 3
  dword_vec = {z[8:0],  z[15:9]};  // rotate by 7
end

//////////////////////////////////////////////////////////////////////////
//                                                                        
//    
//                                                                        
//////////////////////////////////////////////////////////////////////////
wire    x1_word_or_dword;
assign  x1_word_or_dword  =  ((!x1_byte_size_r) & (!x1_half_size_r))
                            | x1_double_size_r
                            ;
always @*
begin : byte_sel_PROC
  byte_sel  =   z
              | (hword_vec & {16{x1_half_size_r}}  )
              | (word_vec  & {16{x1_word_or_dword}})
              | (dword_vec & {16{x1_double_size_r}})
              ;
end

//////////////////////////////////////////////////////////////////////////
//                                                                        
// Output drivers        
//                                                                        
//////////////////////////////////////////////////////////////////////////
assign x1_bank_sel  =  { (| byte_sel[15:12]),
                         (| byte_sel[11:8]),
                         (| byte_sel[7:4]),
                         (| byte_sel[3:0])
                       };

endmodule // alb_agu_bank_sel

