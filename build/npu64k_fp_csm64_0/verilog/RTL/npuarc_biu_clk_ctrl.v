// Library ARCv2CC-3.2.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2015 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2012, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
// biu_clk_ctrl
// ===========================================================================
//
// Description:
//  The biu_clk_ctrl module is used for all main sub-bridge modules under biu_top
//
// ===========================================================================
// Configuration-dependent macro definitions
//
// Use vpp as below in order to only keep one copy of source file
`include   "npuarc_biu_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_biu_clk_ctrl
  (
  output clk_gated,
  input  clkctrl_en,
  input  clk,              // free-runing clock
  input  nmi_restart_r,    // NMI reset signal
  input  rst_a             // Reset
  );


  reg clkctrl_en_r  ;
  reg clkctrl_en_r_r;

// spyglass disable_block Ar_unsync01
// SMD: reset is unsynchronized
// SJ: The rst_a is synced by biu_reset_ctrl module
  always @ (posedge clk or posedge rst_a)
    begin : clkctrl_en_PROC
       if (rst_a == 1'b1)
         begin
           clkctrl_en_r   <= 1'b1;
           clkctrl_en_r_r <= 1'b1;
         end
       else if (nmi_restart_r == 1'b1)
         begin
           clkctrl_en_r   <= 1'b1;
           clkctrl_en_r_r <= 1'b1;
         end         
       else
         begin
           clkctrl_en_r   <= clkctrl_en;
           clkctrl_en_r_r <= clkctrl_en_r;
         end
    end
// spyglass enable_block Ar_unsync01

  wire clkctrl_enable =  clkctrl_en
                              | clkctrl_en_r
                              | clkctrl_en_r_r;

  npuarc_biu_clkgate u_biu_clkgate
    (
     // clk
     .clk_in               (clk                             ),
     .clock_enable         (clkctrl_enable           ),
     .clk_out              (clk_gated                  )
    );

endmodule // biu_clk_ctrl
