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
// int11*int11 multiplier
//

`include "npu_defines.v"

module npu_conv_mpy_prim_12
  (
   input  logic [9:0]  a,    // feature-map
   input  logic [9:0]  b,    // weight
   input  logic        fp,   // true if float
   output logic [21:0] z     // result
   );

  always_comb 
  begin : mul_12_PROC
    logic              fpi;
    logic [10:0][21:0] pp; // sext 
    logic [10:0]       t1;
    logic [10:0]       t0;
    fpi = fp;
    t1 = {fpi ,a[9],a[8]^~fpi,a[7:0]};
    t0 = {1'b0,1'b0,     ~fpi, 8'h00};
    pp = '0;
    for (int i = 0; i < 8; i++)
    begin
      pp[i][i+:11] = b[i] ? t1 : t0;
    end
    pp[8][8+:11]   = b[8] ? {1'b1,a[9],a[8],a[7:0]^{8{~fpi}}} : {1'b0,1'b0,~fpi,8'h00};
    pp[9][9+:11]   = b[9] ? {1'b1,a} : 11'h000; // b[9] can only be set in fp mode
    pp[9][8]       = b[8]&~fpi;
    pp[10][10+:11] = fpi ? {1'b1,a} : 11'h000;
    pp[10][8]      = ~fpi;
    // override fields not used for integer
    pp[7][17]      = b[7];
    pp[8][17+:2]   = {b[8],b[8]&a[9]};
    pp[10][17+:4]  = {1'b1,a[9:7]};    
    // sum up the partial products
    z = 0;
    for (int i = 0; i < 11; i++)
    begin
      z += pp[i];
    end
  end : mul_12_PROC
  
endmodule : npu_conv_mpy_prim_12
