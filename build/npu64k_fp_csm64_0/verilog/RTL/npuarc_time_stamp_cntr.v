// Library ARC_Trace-3.0.999999999
// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   time_stamp_cntr
//
// ===========================================================================
//
// Description:
//
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o time_stamp_cntr.vpp
//
// ===========================================================================


`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_time_stamp_cntr (
rtt_clk,
rst_a,
pr0_time_stamp
);
  input rtt_clk;
  input rst_a;
  output [`npuarc_RTT_TIME_STMP-1:0] pr0_time_stamp;
  reg  [`npuarc_RTT_TIME_STMP_CNTR_BITS-1:0] time_stamp;
  reg  [`npuarc_RTT_TIME_STMP-1:0] pr0_time_stamp;


//leda BTTF_D002 off
// spyglass disable_block SelfDeterminedExpr-ML

  always@(posedge rtt_clk or posedge rst_a)
    if (rst_a == 1'b1)
    begin
      time_stamp <= {`npuarc_RTT_TIME_STMP_CNTR_BITS{1'b0}};
      pr0_time_stamp <= {`npuarc_RTT_TIME_STMP{1'b0}};
    end
    else
    begin
      time_stamp <= {time_stamp + {{(`npuarc_RTT_TIME_STMP_CNTR_BITS-1){1'b0}},1'b1}};
      pr0_time_stamp <= time_stamp[`npuarc_RTT_TIME_STMP-1:0];
    end

//leda BTTF_D002 on
// spyglass enable_block SelfDeterminedExpr-ML


endmodule
