// Library ARC_Trace-3.0.999999999

// Copyright (C) 2019 Synopsys, Inc. All rights reserved.
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
//   arct_programming_if
//
// ===========================================================================
//
// Description:
//  This is the Real Time Trace programming interface file.
//  In multicore builds the multriple programming interfaces are connected to
//  the rtt. only one core gets the access to the programming registers .
//  priority : cr0: highest crN: Lowest (Nth core number)
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o arct_programming_if.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
// Removed by Shafee. No matching on pragma found. leda VER_1_6_4_1 off
// LMD: Do not include glue logic at top level
// LJ: RTT is not the top level. It is provisionally being run as top level

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_programming_if (

    // Replicate the signals for each core we're connected to that has RTT.

    input                     rtt_write_a,
    input                     rtt_read_a,
    input  [`npuarc_RTT_ADDR-1:0]    rtt_addr_r,
    input  [`npuarc_RTT_DATA-1:0]    rtt_dwr_r,

    output  reg                   pif_arct0_rtt_write_a,
    output  reg                   pif_arct0_rtt_read_a,
    output  reg [`npuarc_RTT_ADDR-1:0]   pif_arct0_rtt_addr_r,
    output  reg [`npuarc_RTT_DATA-1:0]   pif_arct0_rtt_dwr_r,



    input                     arct_rtt_write_a,
    input                     arct_rtt_read_a,
    input  [`npuarc_RTT_ADDR-1:0]    arct_rtt_addr_r,
    input  [`npuarc_RTT_DATA-1:0]    arct_rtt_dwr_r
);





always @*
begin
  if (rtt_write_a || rtt_read_a) begin
    pif_arct0_rtt_write_a = rtt_write_a;
    pif_arct0_rtt_addr_r  = rtt_addr_r;
    pif_arct0_rtt_dwr_r   = rtt_dwr_r;
    pif_arct0_rtt_read_a  = rtt_read_a;
  end
  else if ((arct_rtt_write_a || arct_rtt_read_a) && (arct_rtt_addr_r[21:16] == 6'd0)) begin
    pif_arct0_rtt_write_a = arct_rtt_write_a;
    pif_arct0_rtt_addr_r  = arct_rtt_addr_r;
    pif_arct0_rtt_dwr_r   = arct_rtt_dwr_r;
    pif_arct0_rtt_read_a  = arct_rtt_read_a;
  end  
  else begin
    pif_arct0_rtt_write_a = 1'b0;
    pif_arct0_rtt_addr_r  = 32'b0;
    pif_arct0_rtt_dwr_r   = 32'b0;
    pif_arct0_rtt_read_a  = 1'b0;
  end  
end


endmodule
