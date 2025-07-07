/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

//
// 3D AM write interface, nested loops: [grp*no][ni*qd][col*row*onn]
// vcs -sverilog ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_fifo.sv npu_gtoa_types.sv npu_gtoa_am_agu.sv npu_gtoa_am_write.sv +incdir+../../shared/RTL
// analyze -format sverilog -vcs "../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../npu_gtoa_types.sv ../npu_gtoa_am_agu.sv ../npu_gtoa_am_write.sv +incdir+../../../shared/RTL"
//

`include "npu_defines.v"
`include "npu_am_macros.svh"


module npu_gtoa_am_write
  import npu_types::*;
  import npu_gtoa_types::*;
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
// spyglass disable_block W240
//SMD:Unread input
//SJ :macro packed signal can be ignored
   input  act_hlapi_am_agu_t       in_pars,             // AGU parameters
// spyglass enable_block W240
   input  logic                    out_valid,           // Accumulator is valid
   output logic                    out_accept,          // Accumulator is accepted
   input  vyixacc_t                out_acc,             // Write accumulator
   `AMWMST(am_wr_,1)                                    // Write interface
   );
  //
  // Internal wires
  //
  // AGU outputs
  logic                    a_valid;           // output address is valid
  logic                    a_accept;          // output address is accepted

  //
  // Instantiate AM AGU
  //
  npu_gtoa_am_agu
    #(
      .R ( ACT_AM_LOOPS ) 
    )
  u_agu_inst
    (
   .clk        ( clk               ),
   .rst_a      ( rst_a             ),
   .in_valid   ( in_valid          ),
   .in_accept  ( in_accept         ),
   .iter       ( in_pars.iter      ),
   .offset     ( in_pars.offsets   ),
   .ptr        ( in_pars.ptr       ),
   .out_valid  ( a_valid           ),
   .out_accept ( a_accept          ),
   .out_addr   ( am_wr_cmd_addr[0] )
     );

  // Drive memory write request
  assign am_wr_cmd_valid = a_valid & out_valid;
  assign a_accept        = out_valid & am_wr_cmd_accept;
  assign out_accept      = a_valid & am_wr_cmd_accept;
  assign am_wr_wdata     = out_acc;

endmodule : npu_gtoa_am_write
