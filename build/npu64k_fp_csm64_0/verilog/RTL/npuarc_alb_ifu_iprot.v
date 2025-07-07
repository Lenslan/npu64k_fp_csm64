// Library ARCv2HS-3.5.999999999
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
// Description:
// @p
//  Instruction Fetch Protection (IFP) Regions:
//  The automatic region based fetch protection scheme inhibits speculative 
//  fetch from memory regions that have not been confirmed to be code regions.
//
// @e
// ===========================================================================

// Configuration-dependent macro definitions
//

// Set simulation timescale
//
// synopsys translate_off

///////////////////////////////////////////////////////////////////////////
// Common Verilog definitions
///////////////////////////////////////////////////////////////////////////

// Verilog simulator timescale definition for all modules
//
`timescale 1 ns / 10 ps

// synopsys translate_on

module npuarc_alb_ifu_iprot (
  // =========================================================================
  // Lookup Interface
  //
  input [31:28]       fa_ifp_rgn,  // region to be checked
  output reg                   fa_ifp_viol, // disallow fetch

  // =========================================================================
  // Update Interface
  //
  // addr region of speculative instr which reached commit (sets region bit)
  input [31:28]       fch_restart_rgn,
  input                        fch_restart, 
  input                        fch_restart_vec, 
  input                        fch_iprot_replay, // qualifier to enable rgn
  // clear all allow-bits on BPU flush
  input                        wa_ifp_clear_all,

  input                        mmu_en_r,       // Enable TLB lookups
  // =========================================================================
  // General input signals
  //
  input                        clk,            // Processor clock
  input                        rst_a           // Global reset
);

reg [15:0]   ifp_rgns_1h_nxt;
reg [15:0]   ifp_rgns_1h_r;
reg                     ifp_confirm;
reg                     ifp_rgn_cross;
reg                     ifp_rgns_1h_cg0;
  
reg [15:0]   set_fch_rgn1_1h;
reg [15:0]   set_fch_rgn2_1h;

  // lookup region result
always @*
begin :  i_lookup_PROC
  fa_ifp_viol = (~ifp_rgns_1h_r[fa_ifp_rgn])  // select rgn bit
              &  ( ~mmu_en_r                  // inhibit viol if fa chked by mmu
                  | fa_ifp_rgn[31]) // (mmu chks 0-2G only if en)
              ;
end

// update region bits (comb)
always @*
begin :  i_ifp_rgns_1h_nxt_PROC

  //==========================================================================
  // Compute additional bit that will be set if a region
  // becomes enabled by a fetch restart.
  //
  set_fch_rgn1_1h = 16'd0;
  set_fch_rgn1_1h[fch_restart_rgn] = 1'b1;
  
  //==========================================================================
  // Compute additional bit that will be set if a replay
  // occurs on a region that is already enabled. This indicates
  // that the replay is for the region after the region indicated
  // by the fch_restart region. To avoid an addition operation
  // on the region number we rotate the bits of the set_fch_rgn1_1h
  // vector. This has no cost, either in time or gates.
  //
  set_fch_rgn2_1h = {set_fch_rgn1_1h[14:0], set_fch_rgn1_1h[15]};
  
   //==========================================================================
 // Detect fetch restart due to iprot replay
  //
  ifp_confirm   = fch_restart & (fch_iprot_replay | fch_restart_vec);
  
  //==========================================================================
  // Detect fetch restart on a region-crossing instruction
  //
  ifp_rgn_cross = ifp_confirm
                & ifp_rgns_1h_r[fch_restart_rgn]
                & (~fch_restart_vec)
                ;
  
  //==========================================================================
  // Define the next ifp_rgn_1h protection register.
  // 
  // (a) The result is always zeros if wa_ifp_clear_all is asserted.
  //     Otherwise:
  // (b) the set_fch_rgn1_1h bit is ORed into the result if
  //     the ifp_confirm signal is asserted, and also:
  // (c) the set_fch_rgn2_1h bit is ORed into the result if the
  //     ifp_rgn_cross signal is asserted.
  //
  ifp_rgns_1h_nxt = {16{~wa_ifp_clear_all}}
                  & (  ifp_rgns_1h_r
                      | (  {16{ifp_confirm}}
                          & set_fch_rgn1_1h)
                      | (  {16{ifp_rgn_cross}}
                          & set_fch_rgn2_1h)
                    )
                  ;

  //==========================================================================
  // Enable update of region protection bits
  //
  ifp_rgns_1h_cg0 = ifp_confirm || wa_ifp_clear_all;

end

always @(posedge clk or posedge rst_a)
begin : ifp_rgns_1h_PROC
  if (rst_a == 1'b1)
  begin
    ifp_rgns_1h_r <= 16'd0;
  end
  else if (ifp_rgns_1h_cg0)
  begin
    ifp_rgns_1h_r <= ifp_rgns_1h_nxt;
  end
end

endmodule // alb_ifu_rgn_prot

