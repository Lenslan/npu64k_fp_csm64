// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2014 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//
//  +    1    +    2    +    3    +    4    +    5    +    6    +    7    +    8
module npuarc_csa_4_2_64 (
  input  [64:0] di0,
  input  [64:0] di1,
  input  [64:0] di2,
  input  [64:0] di3,
  
  output [64:0] sum,
  output [64:0] carry
 );

wire     [64:0] carry3;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  upper guard bit unused in this implementation
//      not corrected because block was 100% verified (all input permutations)
wire     [65:0] carry3_66;
wire     [65:0] carry_66; 
// leda NTL_CON13A on

// leda NTL_CON16 off
// LMD: Nets or cell pins should not be tied to logic 0 / logic 1
// LJ:  structural description of a shift of the carry component
//      not corrected because block was 100% verified (all input permutations)
assign  carry3_66 = {di0 & di1 | di0 & di2 | di1 & di2, 1'b0};
assign  carry3    = carry3_66[64:0];

assign  sum       =   (di0^di1^di2^di3) ^ carry3 ;      
assign  carry_66  = { (di0^di1^di2^di3) & carry3 |
                     ~(di0^di1^di2^di3) & di3,   1'b0}; 
assign  carry     = carry_66[64:0];
// leda NTL_CON16 on


endmodule
