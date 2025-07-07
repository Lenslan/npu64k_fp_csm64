// Library ARC_Trace-3.0.999999999
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

// Set simulation timescale
//
`include "const.def"

// leda NTL_RST06 off
// LMD: Avoid internally generated resets
// LJ: We do need to synchronize the rst_a

// spyglass disable_block Reset_sync04, Reset_check04
// SMD: Asynchronous reset signal 'rst_a' is synchronized at least twice
// SJ:  We do need to synchronize the rst_a

// spyglass disable_block Reset_check07
// SMD: Clear pin of sequential element 'rst_n' is driven by combinational logic
// SJ:  Converting active high rst_a to active low rst_n

// spyglass disable_block Ac_unsync01
// SMD: Unsychronised clock crossing reported
// SJ: Source clock and capture clock are actually synchronous

// spyglass disable_block STARC05-1.3.1.3
// SMD: asynchronous reset signal being used as synchronous or other use
// SJ:  used as asynchronous

module npuarc_rtt_atb_rst_ctrl (
// spyglass disable_block FlopDataConstant LogicDepth MergeFlops-ML
input  clk,            // clock
input  rst_a,          // global reset
input  rst_in,         // Reset in
output rst_out,        // Reset out
input  test_mode       // test mode to bypass FFs
);

//////////////////////////////////////////////////////////////////
// Synchronizing flip-flops (with async clear function)
wire rst_n;        // active low reset output of 2nd sync FF

npuarc_rtt_cdc_sync u_atb_rst_cdc_sync_r (
                                   .clk   (clk),
                                   .rst_a (rst_a),
                                   .din   (rst_in),
                                   .dout  (rst_n)
                                  );
// spyglass enable_block FlopDataConstant LogicDepth MergeFlops-ML
assign rst_out = test_mode ? ~rst_a : rst_n;

endmodule
// leda NTL_RST06 on

// spyglass enable_block STARC05-1.3.1.3
// spyglass enable_block Reset_sync04
// spyglass enable_block Reset_check04
// spyglass enable_block Reset_check07
// spyglass enable_block Ac_unsync01
