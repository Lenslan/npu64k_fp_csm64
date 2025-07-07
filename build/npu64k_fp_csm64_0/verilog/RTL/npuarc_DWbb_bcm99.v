// Library ARCv2CC-3.2.999999999
////////////////////////////////////////////////////////////////////////////////
//
//                  (C) COPYRIGHT 2015 - 2020 SYNOPSYS, INC.
//                            ALL RIGHTS RESERVED
//
//  This software and the associated documentation are confidential and
//  proprietary to Synopsys, Inc.  Your use or disclosure of this
//  software is subject to the terms and conditions of a written
//  license agreement between you, or your company, and Synopsys, Inc.
//
//  The entire notice above must be reproduced on all authorized copies.
//
// Filename    : DWbb_bcm99.v
// Revision    : $Id: $
// Author      : Liming SU    06/19/15
// Description : DWbb_bcm99.v Verilog module for DWbb
//
// DesignWare IP ID: bc6934e8
//
////////////////////////////////////////////////////////////////////////////////
// spyglass disable_block Ar_glitch01
// SMD: Signal driving clear pin of the flop has glitch
// SJ: source is coming from the recirculation stage of the synchronizer, this warning can be ignored.
module npuarc_DWbb_bcm99 (
  clk_d,
  rst_d_n,
  data_s,
  data_d
);

parameter ACCURATE_MISSAMPLING = 0; // RANGE 0 to 1

input  clk_d;      // clock input from destination domain
input  rst_d_n;    // active low asynchronous reset from destination domain
input  data_s;     // data to be synchronized from source domain
output data_d;     // data synchronized to destination domain

`ifdef SYNTHESIS
//######################### NOTE ABOUT TECHNOLOGY CELL MAPPING ############################
// Replace code between "DOUBLE FF SYNCHRONIZER BEGIN" and "DOUBLE FF SYNCHRONIZER END"
// with one of the following two options of customized register cell(s):
//   Option 1: One instance of a 2-FF cell
//     Macro cell must have an instance name of "sample_meta".
//
//     Example: (TECH_SYNC_2FF is example name of a synchronizer macro cell found in a technology library)
//         TECH_SYNC_2FF sample_meta ( .D(data_s), .CP(clk_d), .RSTN(rst_d_n), .Q(data_d) );
//     
//   Option 2: Two instances of single-FF cells connected serially 
//     The first stage synchronizer cell must have an instance name of "sample_meta".
//     The second stage synchronizer cell must have an instance name of "sample_syncl".
//
//     Example: (in GTECH)
//         wire n9;
//         GTECH_FD2 sample_meta ( .D(data_s), .CP(clk_d), .CD(rst_d_n), .Q(n9) );
//         GTECH_FD2 sample_syncl ( .D(n9), .CP(clk_d), .CD(rst_d_n), .Q(data_d) );
//
//####################### END NOTE ABOUT TECHNOLOGY CELL MAPPING ##########################
// DOUBLE FF SYNCHRONIZER BEGIN
  reg sample_meta;
  reg sample_syncl;
  always @(posedge clk_d or negedge rst_d_n) begin : a1000_PROC
// spyglass disable_block STARC05-1.3.1.3
// SMD: Do not use asynchronous reset/preset signals as non-reset/preset or synchronous reset/preset signals
// SJ: Core may use sync'd reset as data signal
// spyglass disable_block Reset_check07
// SMD: Reports asynchronous reset pins driven by a combinational logic or a mux
// SJ: Combinational logic is caused by NMI reset and this is
// intentional.Hence this rule is waived  
    if (!rst_d_n) begin
// spyglass enable_block Reset_check07
// spyglass enable_block STARC05-1.3.1.3
      sample_meta <= 1'b0;
      sample_syncl <= 1'b0;
    end else begin
// spyglass disable_block Reset_check04 Clock_check10 STARC05-1.4.3.4
// SMD: Reset/Clock signals that are used asynchronously as well as synchronously for different flip-flops
// SJ:  Resets/Clocks are used as data in the synchronizer & not as synchronous resets
// spyglass disable_block Reset_sync04 
// SMD: Asynchronous resets that are synchronized more than once in the same clock domain
// SJ: Spyglass recognizes every multi-flop synchronizer as a reset synchronizer, hence any design with a reset that feeds more than one synchronizer gets reported as violating this rule. This rule is waivered temporarily.
// spyglass disable_block Ar_converge02
// SMD: reset signal converges on reset and data pins
// SJ:  Path from mcip rst req to edc aggregate is safe
// spyglass disable_block Ac_glitch03
// SMD: Flop can glitch due to domain crossing
// SJ:  No issues, designed on purpose
      sample_meta <= data_s;
// spyglass enable_block Reset_sync04
// spyglass enable_block Reset_check04 Clock_check10 STARC05-1.4.3.4
// spyglass enable_block Ar_converge02
// spyglass enable_block Ac_glitch03
// spyglass disable_block W402b
// SMD: Asynchronous set/reset signal is not an input to the module
// SJ: This module is expected to generate reset for its parent module
// spyglass disable_block Ar_resetcross01
// SMD: unsync reset crossing
// SJ:  crossing from cc is safe, causes no issues
// spyglass disable_block Ac_glitch01
// SMD: Flop can glitch due to domain crossing
// SJ:  No issues, designed on purpose
      sample_syncl <= sample_meta;
// spyglass enable_block Ac_glitch01
// spyglass enable_block W402b
// spyglass enable_block Ar_resetcross01
    end
  end
  assign data_d = sample_syncl;
// DOUBLE FF SYNCHRONIZER END
`else
//#####################################################################################
// NOTE: This section is for zero-time delay functional simulation
//#####################################################################################
  reg sample_meta;
  reg sample_syncl;
  always @(posedge clk_d or negedge rst_d_n) begin : a1001_PROC
    if (!rst_d_n) begin
      sample_meta <= 1'b0;
      sample_syncl <= 1'b0;
    end else begin
// spyglass disable_block Reset_check04
// SMD: Reset signals that are used asynchronously as well as synchronously for different flip-flops
// SJ:  Resets are used as data in the synchronizer & not as synchronous resets
// spyglass disable_block Reset_sync04 
// SMD: Asynchronous resets that are synchronized more than once in the same clock domain
// SJ: Spyglass recognizes every multi-flop synchronizer as a reset synchronizer, hence any design with a reset that feeds more than one synchronizer gets reported as violating this rule. This rule is waivered temporarily.
      sample_meta <= data_s;
// spyglass enable_block Reset_sync04
// spyglass enable_block Reset_check04
      sample_syncl <= sample_meta;
    end
  end
  assign data_d = sample_syncl;
`endif

endmodule
// spyglass enable_block Ar_glitch01
