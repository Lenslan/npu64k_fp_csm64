// Library ARCv2CC-3.2.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2014 Synopsys, Inc. All rights reserved.
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
//  The cc_reset_ctrl module provides synchronous deassertion of the
//  asynchronous reset inputs for the cc_aux module. This is to ensure that
//  the global async reset out meets the reset recovery time of the FFs to avoid
//  metastability. The reset outputs are fully asynchrounous in test mode
//  as the FFs are bypassed.
//
// ===========================================================================
`include "npuarc_cc_exported_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_cc_reset_ctrl (
  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,            // clock
  input                       cc_rst_a,       // async CC reset
  input                       test_mode,      // test mode to bypass FFs

  ////////// Synchronized output signal //////////////////////////////////////
  //
  output                      cc_rst          // CC reset
);

//////////////////////////////////////////////////////////////////////////////
//
// Synchronizing flip-flops (with async clear function)
//
//////////////////////////////////////////////////////////////////////////////


wire rst_n;
assign cc_rst = test_mode ? cc_rst_a : !rst_n;

npuarc_cc_cdc_sync #(.SYNC_FF_LEVELS(`npuarc_CC_SYNC_CDC_LEVELS)
             ) u_cc_reset_ctrl_cdc_sync (
                                       .clk   (clk),
                                       .rst_a (cc_rst_a),
                                       .din   (1'b1),
                                       .dout  (rst_n)
                                      );

endmodule // cc_reset_ctrl

