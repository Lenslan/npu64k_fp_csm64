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
//   ALB_DMP_LQ_RROBIN                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements a round robin scheme for acceptance of read data.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_lq_rrobin.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_lq_rrobin (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                           clk,               // clock
  input                           rst_a,             // reset

  ////////// Outstanding loads /////////////////////////////////////////////
  //
  input [4:0]                     lq_pending,       // outstanding loads
  input                           lq_toggle,        // rotate
  
  ////////// Grannted target /////////////////////////////////////////////
  //
  output reg [4:0]                lq_gnt_r         // one-hot-encoded          
);


// Local Declarations
//
reg        lq_gnt_cg0;
reg [4:0]  lq_gnt_nxt;

// leda W175 off
// LMD: Parameter defined but not used
// LJ:  Code more readable
localparam LQ_TARGET_MEM  = 0;
localparam LQ_TARGET_PER  = 1;
localparam LQ_TARGET_ICCM = 2;
localparam LQ_TARGET_VMEM = 3;
localparam LQ_TARGET_PER2 = 4;
// leda W175 on

//////////////////////////////////////////////////////////////////////////////
// @Arbitration
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : lq_gnt_arb_PROC
  
  // Clock gate. Toggle arbitration when there is more than one target pending
  // in the load queue, e.g.: one outstanding load from MEM and one from ICCM
  //
  lq_gnt_cg0 = (| lq_pending) & lq_toggle;
  
  // Default assignment
  //
  lq_gnt_nxt = lq_gnt_r;
  
  casez (lq_gnt_r)
  5'b00001:
  begin
    // MEM target
    //
    if (lq_pending[LQ_TARGET_PER])        lq_gnt_nxt = 5'b00010;
    else if (lq_pending[LQ_TARGET_ICCM])  lq_gnt_nxt = 5'b00100;
    else if (lq_pending[LQ_TARGET_VMEM])  lq_gnt_nxt = 5'b01000;
    else if (lq_pending[LQ_TARGET_PER2])  lq_gnt_nxt = 5'b10000;  
    else                                  lq_gnt_cg0 = 1'b0;
  end
  
  
  

// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept  
  default:
    ;
  endcase
end
// spyglass enable_block W193
//////////////////////////////////////////////////////////////////////////////
// Synchronous process
// 
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin: lq_gnt_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq_gnt_r  <= 5'b00001;
  end
  else
  begin
    if (lq_gnt_cg0 == 1'b1)
    begin
      lq_gnt_r <= lq_gnt_nxt;
    end
  end
end

endmodule // alb_dmp_lq_rrobin
