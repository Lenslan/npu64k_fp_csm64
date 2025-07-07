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

// AXI configurable register slice


`include "npu_defines.v"
`include "npu_axi_macros.svh"


module npu_axi_slice
  import npu_types::*;
  #(
    parameter int AXIIDW       = 4,
    parameter int AXIDW        = 128,
    parameter int AXIAWUW      = 1,
    parameter int AXIWUW       = 1,
    parameter int AXIBUW       = 1,
    parameter int AXIARUW      = 1,
    parameter int AXIRUW       = 1,
    parameter int NUMSLC       = 1,
    // FIFO depth specification
    parameter int AWFIFO_DEPTH = 1,
    parameter int WFIFO_DEPTH  = 2,
    parameter int BFIFO_DEPTH  = 1,
    parameter int ARFIFO_DEPTH = 1,
    parameter int RFIFO_DEPTH  = 2
  )
  (
   // clock and reset
   input logic clk,
   input logic rst_a,
   // AXI slave interface
   `AXISLV(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_slv_),
   // AXI master interface
   `AXIMST(AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_mst_)
   );
  

if (NUMSLC == 0)
begin : feedthrough_GEN
  `AXIASG(axi_slv_,axi_mst_);
end : feedthrough_GEN
else
begin : loop_GEN
  `AXIWIRESN(NUMSLC+1,AXIIDW,AXIDW,AXIAWUW,AXIWUW,AXIBUW,AXIARUW,AXIRUW,axi_int_);

  // assign input to 0
  `AXIASGN(0,axi_int_,axi_slv_);
  // assign output from NUMSLC
  `AXIASGM(NUMSLC,axi_int_,axi_mst_);

// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self-determin expression
// SJ: Reviewed
  // loop
  for (genvar gs = 0; gs < NUMSLC; gs++)
  begin : gen_GEN
    npu_axi_slice_sub
    #(
      .AXIIDW       ( AXIIDW       ),
      .AXIDW        ( AXIDW        ),
      .AXIAWUW      ( AXIAWUW      ),
      .AXIWUW       ( AXIWUW       ),
      .AXIBUW       ( AXIBUW       ),
      .AXIARUW      ( AXIARUW      ),
      .AXIRUW       ( AXIRUW       ),
      .AWFIFO_DEPTH ( AWFIFO_DEPTH ),
      .WFIFO_DEPTH  ( WFIFO_DEPTH  ),
      .BFIFO_DEPTH  ( BFIFO_DEPTH  ),
      .ARFIFO_DEPTH ( ARFIFO_DEPTH ),
      .RFIFO_DEPTH  ( RFIFO_DEPTH  )
    )
    u_slc_inst
    (
      .clk ( clk ),
      .rst_a ( rst_a ),
      `AXIINSTM(gs,axi_slv_,axi_int_),
      `AXIINSTM(gs+1,axi_mst_,axi_int_)
    );
  end : gen_GEN
end : loop_GEN
// spyglass enable_block SelfDeterminedExpr-ML

endmodule : npu_axi_slice
