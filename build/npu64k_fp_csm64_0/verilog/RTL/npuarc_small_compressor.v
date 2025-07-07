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
//   compressor
//
// ===========================================================================
//
// Description:
//   Compressor module will compress the data to meet the RTT bandwidth requirements.
//   The compressor will present for all producer sources except core write source.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_rtt_rst.vpp
//
// ==========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_small_compressor(
  rtt_clk,
  rst_a,
  rtt_inst_addr,
  pr0_filter_pc,
  pr0_filter_branch_taddr,
  ptm_dropped,
  pt_sync_msg,
  pt_msg_valid,
  pc_msg_valid,
  pr0_cmpr_under_run,
  pr0_cmpr_ptm_taddr,
  unfiltered_relative_pc
);
  input                          rtt_clk;
  input                          rst_a;
  input  [31-1:0]               rtt_inst_addr;
  input  [31-1:0]               pr0_filter_pc;
  input  [31-1:0]               pr0_filter_branch_taddr ;
  input                          ptm_dropped;
  input                          pt_sync_msg;
  input                          pt_msg_valid;
  input                          pc_msg_valid;

 //output declarations
  output                         pr0_cmpr_under_run;
  output  [31-1:0]              pr0_cmpr_ptm_taddr;
  output  [31-1:0]              unfiltered_relative_pc;

  //net declarations
  reg   [31-1:0]                pr0_cmpr_taddr_r;
  wire                           pr0_cmpr_ptm_vld;
  wire                           ptm_cmpr_en;
  wire                           pr0_cmpr_under_run;

  //compressor enables
  assign ptm_cmpr_en = (pt_msg_valid || pc_msg_valid);

  //ptm taddress compression logic
  always @ (posedge rtt_clk or posedge rst_a)
  begin : PTM_CMPR_PROC
    if (rst_a == 1'b1 ) begin
      pr0_cmpr_taddr_r <= 31'b0;
    end
    else if (ptm_dropped == 1'b1) begin
      pr0_cmpr_taddr_r <= 31'b0;
    end
    else if (pt_msg_valid == 1'b1) begin
      pr0_cmpr_taddr_r  <=  pr0_filter_branch_taddr;
     end
    else if (pc_msg_valid == 1'b1) begin
      pr0_cmpr_taddr_r  <=  pr0_filter_pc;
     end
  end // end ptm taddress

  assign unfiltered_relative_pc = pt_msg_valid ? (rtt_inst_addr ^ pr0_filter_branch_taddr) :
                                                 pc_msg_valid ? (rtt_inst_addr ^ pr0_filter_pc) :
                                                                (rtt_inst_addr ^ pr0_cmpr_taddr_r) ;
  assign pr0_cmpr_ptm_taddr = (pc_msg_valid && (!pt_sync_msg)) ? (pr0_filter_branch_taddr ^ pr0_filter_pc) : (pt_sync_msg) ? pr0_filter_branch_taddr : (pr0_filter_branch_taddr ^ pr0_cmpr_taddr_r);

  assign pr0_cmpr_ptm_vld   = ptm_cmpr_en;

  //dtm memory address compressor
assign pr0_cmpr_under_run =
pr0_cmpr_ptm_vld;

endmodule // compressor
