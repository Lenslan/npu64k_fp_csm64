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

/*
 * NPU padding logic, pads input data and returns the column index of the data
 * The GTOA padding logic start applies 2D padding if enabled
 * padding can be done by the MININT or 0 value
 * As a sideband signal padding will return the column padding index for ARGMAX applications
 * Even if padding is disabled the padding index is updated
 * Padding iterators and associated 2D offsets and column stride are passed as input signals
 */
module npu_gtoa_fu_pad
  import npu_types::*;
  import npu_gtoa_types::*;
  // interface signals
  (
   // padding iterator interface
   input  logic                                    paden,         // enable padding
   input  logic                                    padval,        // valid padding instruction
   input  pad_mode_t                               padmode,       // padding mode
   input  pad_inc_t                                padinc,        // padding increment mode
   input  logic        [ISIZE/4-1:0]               padi4,         // padding bit per i4 channels
   // data stream from input 0
   input  ixacc_t                                  in_acc,        // input value
   // padding outputs
   output logic        [ISIZE/4-1:0]               padflag,       // data is padded
   output ixacc_t                                  out_acc        // padded accumulator
   );
  // local wires
  logic                [ISIZE/4-1:0]                 p;             // padding flags

  // determine which should be padded
  assign padflag = padi4;
  assign p = (paden&padval) ? padflag : 4'h0;

  // actual padding
  // outputs: out_acc
  always_comb
  begin : pad1_PROC
    acc_t pv;
    case (padmode)
    pad_mode_mone_e:   pv = 32'hbf800000;
    pad_mode_maxint_e: pv = 32'h7fffffff;
    pad_mode_minint_e: pv = 32'hffffffff;
    default:           pv = 32'h00000000;
    endcase
    // apply padding
    for (int i = 0; i < 4; i++)
    begin
      out_acc[i*4+:4] = p[i] ? {4{pv}} : in_acc[i*4+:4];
    end
  end : pad1_PROC
  
endmodule : npu_gtoa_fu_pad
