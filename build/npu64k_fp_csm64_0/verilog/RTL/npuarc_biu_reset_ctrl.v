// Library ARCv2CC-3.2.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2013 Synopsys, Inc. All rights reserved.
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
// #####   ######   ####   ######   #####           ####    #####  #####   #
// #    #  #       #       #          #            #    #     #    #    #  #
// #    #  #####    ####   #####      #            #          #    #    #  #
// #####   #            #  #          #            #          #    #####   #
// #   #   #       #    #  #          #            #    #     #    #   #   #
// #    #  ######   ####   ######     #   #######   ####      #    #    #  ######
// ===========================================================================
//
// Description:
//  The biu_reset_ctrl module provides synchronous deassertion of the
//  asynchronous reset input. This is to ensure that the global asyn reset
//  meets the reset revovery time of the FFs to avoid metastability.
//  The reset output is fully asynchronous in test mode as the FFs are bypassed
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"
`include "npuarc_cc_exported_defines.v"

// Set simulation timescale
//
`include "const.def"


// leda NTL_RST06 off
// LMD: Avoid internally generated resets
// LJ: We do need to synchronize the rst_a
module npuarc_biu_reset_ctrl (
input  clk,            // clock
output rst, // reset
output sync_rst_r, // reset
input  rst_a, // External reset
input  test_mode       // test mode to bypass FFs
);


//////////////////////////////////////////////////////////////////
// Synchronizing flip-flops (with async clear function) 

wire rst_n;

npuarc_cc_cdc_sync #(.SYNC_FF_LEVELS(`npuarc_CC_SYNC_CDC_LEVELS)
             ) u_biu_reset_ctrl_cdc_sync (
                                       .clk   (clk),
                                       .rst_a (rst_a),
                                       .din   (1'b1),
                                       .dout  (rst_n)
                                      );
assign rst = test_mode ? rst_a : ~rst_n;

reg sync_rst_n_r; // This signal will be a functional signal used for regular
                  // logics to stop accept some external transactions (e.g., AHB transactions)
                  // when the reset is applying

// spyglass disable_block Ar_glitch01 
// SMD: clear pin has glitch 
// SJ: this mux on clear pin path is wished to be here
always @(posedge clk or posedge rst)
begin:sync_rst_n_PROC
  if(rst == 1'b1)
    begin
      sync_rst_n_r<= 1'b0;
    end
  else
    begin
      sync_rst_n_r<= 1'b1;
    end
end
// spyglass enable_block Ar_glitch01

assign sync_rst_r = (~sync_rst_n_r);


endmodule
// leda NTL_RST06 on

