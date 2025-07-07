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
// ===========================================================================
//
// Description: 
//  
//  The reset_sync module provides synchronous deassertion of the
//  asynchronous reset input. This is to ensure that the global
//  async reset out meets the reset recovery time of the FFs to avoid
//  metastability. The reset output is fully asynchrounous in test mode
//  as the FFs are bypassed.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a
//  command line such as:
//
//   vpp +q +o alb_reset_ctrl.vpp
//
//  This file is indented with 2 characters per tab.
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_wdt_reset_ctrl (
  ////////// General input signals /////////////////////////////////////////
  //
  input                       clk,        // Processor clock
  input                       rst_a,      // Async reset
  input                       test_mode,  // test mode to bypass FFs

  ////////// Conditioned output signal /////////////////////////////////////
  //
  output                      rst      // reset with synchronized deassertion
);

  ////////////////////////////////////////////////////////////////////////////
  //                                                                        //
  // Synchronizing flip-flops (with async clear function)                   //
  //                                                                        //
  ////////////////////////////////////////////////////////////////////////////
// spyglass disable_block Reset_check07
// SMD: Multiple resets in the module
// SJ:  it is indeed hasing sveral rst input 
reg rst_sync1_n;  // active low reset output of 1st sync FF
reg rst_n;        // active low reset output of 2nd sync FF


// leda NTL_RST06 off
// LMD: Avoid internally generated resets
// LJ: Safe as long as all inputs (test_mode, mmb_core_test_enable 
//     and incoming reset signals) to rsts_a are glitch-free
// spyglass disable_block Reset_info09a
// SMD: reset net unconstrained
// SJ:  Safe as long as all inputs (test_mode, mmb_core_test_enable 
//      and incoming reset signals) to rsts_a are glitch-free
wire rsts_a;
// spyglass enable_block Reset_info09a
assign rsts_a = test_mode ? rst_a : (
                rst_a
 );
// leda NTL_RST06 on
// spyglass disable_block STARC05-1.3.1.3 Reset_sync02 Reset_sync04 
// SMD: asynchronous reset signal being used as synchronous or other use
// SJ:  used as asynchronous
// SMD: Reset signal rsts_a used to reset signal rst_n' (domain 'archipelago.clk') 
//      is generated from domain 'archipelago.mcip_clk'
// SJ:  rsts_a used as asynchronous
// SMD: Asynchronous reset signal synchronized twice relative to achipelago.clk
// SJ:  resets can be independent (offset by 1 clock) in HS core and cc_top
// SMD: Clear pin of sequential element is driven by combinational logic
// SJ:  for test_mode
always @(posedge clk or posedge rsts_a)
  begin : reset_sync_PROC
    if (rsts_a == 1'b1)
    begin
      rst_sync1_n <= 1'b0;
      rst_n       <= 1'b0;
    end
    else 
    begin
      rst_sync1_n <= 1'b1;
      rst_n       <= rst_sync1_n;
    end
  end
// spyglass enable_block STARC05-1.3.1.3 Reset_sync02 Reset_sync04 
// spyglass enable_block Reset_check07

assign rst = test_mode ? rst_a : 
                         (~rst_n)
                         ;
  
endmodule // alb_wdt_reset_ctrl
