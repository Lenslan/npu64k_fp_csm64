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
`ifndef DWbb_bcm99_v
`define DWbb_bcm99_v

`include "npu_rdf_defines.sv"

// spyglass disable_block Ar_glitch01
// SMD: Signal driving clear pin of the flop has glitch
// SJ: source is coming from the recirculation stage of the synchronizer, this warning can be ignored.

module npu_DWbb_bcm99 (
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

// spyglass disable_block STARC05-1.3.1.3 Reset_check07 Reset_check04 Clock_check10 STARC05-1.4.3.4 Reset_sync04 Ar_converge02 Ac_glitch03 Ar_glitch01 W402b Ar_resetcross01
`CellLibrarySync2Gate sample_meta (.SI(1'b0), .SE(1'b0), .D(data_s), .CK(clk_d), .RD(rst_d_n), .Q(data_d) );
// spyglass enable_block STARC05-1.3.1.3 Reset_check07 Reset_check04 Clock_check10 STARC05-1.4.3.4 Reset_sync04 Ar_converge02 Ac_glitch03 Ar_glitch01 W402b Ar_resetcross01

// DOUBLE FF SYNCHRONIZER END

endmodule
// spyglass enable_block Ar_glitch01
`endif
