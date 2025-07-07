//  ------------------------------------------------------------------------------
//                    Copyright Message
//  ------------------------------------------------------------------------------
//
//  CONFIDENTIAL and PROPRIETARY
//  COPYRIGHT (c) Synopsys 2010
//
//  All rights are reserved. Reproduction in whole or in part is
//  prohibited without the written consent of the copyright owner.
//
//  ------------------------------------------------------------------------------
//                    Design Information
//  ------------------------------------------------------------------------------
//
//  File           : rtt_ck_gen_mapped.v
//
//  Author         : ARC
//
//  Organisation   : Synopsys / Solutions Group / Processor Solutions
//
//  Date           : $Date: 2012-05-24 10:16:58 +0200 (Thu, 24 May 2012) $
//
//  Revision       : $Revision: 164933 $
//
//  Project        : ABBA : ARC Benchmarking
//
//  Description    : Configurable, technology mapped implementation.
//
//  ------------------------------------------------------------------------------
//  Verilog compiler directives (applied through stdcelldef.v):
//    CellLibraryClockGate : Name of std.cell clock-gate.
//  ------------------------------------------------------------------------------
`include "npuarc_stdcelldef.v"


module npuarc_clock_gate (
  input   clk_in,
  input   clock_enable_r,
  
  output  clk_out
);

   `CellLibraryClockGate npuarc_clk_gate0 (.Q(clk_out),.CK(clk_in), .EN(clock_enable_r),.SE(1'b0));


endmodule // clkgate
