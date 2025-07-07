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


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_reset_ctrl (
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
wire rst_n;        // active low reset output of 2nd sync FF


// leda NTL_RST06 off
// LMD: Avoid internally generated resets
// LJ: Safe as long as all inputs (test_mode, mmb_core_test_enable 
//     and incoming reset signals) to rsts_a are glitch-free
//      and incoming reset signals) to rsts_a are glitch-free
wire rsts_a;
assign rsts_a = test_mode 
              ? rst_a
              : (
                rst_a
                );
                
// leda NTL_RST06 on
npuarc_cdc_sync u_cdc_sync_reset (
  .clk        (clk),
  .rst_a      (rsts_a),
  .din        (1'b1),
  .dout       (rst_n)
);
// spyglass enable_block Reset_check07

assign rst = test_mode ? rst_a : 
                         (~rst_n)
                         ;
  




endmodule // alb_reset_ctrl
