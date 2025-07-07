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
// 8b*9b signed multiplier
//

module npu_conv_mpy_prim
  import npu_types::*;
  import npu_conv_types::*;
  (
   input  logic [7:0]  a,
   input  logic [8:0]  b,
   output logic [16:0] z
   );

  always_comb 
    begin : mul_PROC
      // inferred multiply with sign extension
      z = $signed(a) * $signed(b);
    end : mul_PROC
  
endmodule : npu_conv_mpy_prim
