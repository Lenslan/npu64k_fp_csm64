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
// 3D AM read interface, nested loops: [grp*no][ni*qd][col*row*onn]
//

`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_am_macros.svh"


module npu_am_write
  import npu_types::*;
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
   input  am_agu_t                 in_pars,             // AM AGU parameters
   input  logic                    in_use_acc,          // if true then initialize from AM else to 0
   input  logic                    in_keep_acc,         // if true then keep accumulator in AM else stream
   input  logic                    out_valid,           // Accumulator is valid
   output logic                    out_accept,          // Accumulator is accepted
   input  vyixacc_t                out_acc,             // Write accumulator
   `STRMST(acc_,vyixacc_t),                             // Streaming interface  
   `AMWMST(am_wr_,1)                                    // AM write interface
   );
  //
  // Internal wires
  //
  logic                    usekeep;           // use_acc or keep_acc
  logic                    keep_acc_r;        // stored keep_acc
  // AGU outputs
  logic                    a_valid;           // output address is valid
  logic                    a_accept;          // output address is accepted
  logic                    a_last;            // last accumulation iteration
  
  
  // store HLAPI keep attribute
  always_ff @(posedge clk or posedge rst_a)
  begin : keep_reg_PROC
    if (rst_a == 1'b1)
    begin
      keep_acc_r <= 1'b0;
    end
    else if (in_valid & in_accept)
    begin
      keep_acc_r <= in_keep_acc;
    end
  end : keep_reg_PROC

// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected  
  //
  // Instantiate AM AGU
  //
  assign usekeep = in_use_acc | in_keep_acc;
  npu_am_agu
  u_agu_inst
  (
   .clk          ( clk               ),
   .rst_a        ( rst_a             ),
   .in_valid     ( in_valid          ),
   .in_accept    ( in_accept         ),
   .in_pars      ( in_pars           ),
   .in_usekeep   ( usekeep           ),
   .out_valid    ( a_valid           ),
   .out_accept   ( a_accept          ),
   .out_addr     ( am_wr_cmd_addr[0] ),
   .out_init_acc (                   ), // intentionally left open, only used for AM read
   .out_last_acc ( a_last            )  // if true then final write
   );
// spyglass enable_block W287b
  
  //
  // Drive memory write request
  //
  assign am_wr_cmd_valid[0] = a_valid & out_valid & (keep_acc_r || (!a_last));
  assign acc_str_valid      = a_valid & out_valid & a_last & (!keep_acc_r);
  assign out_accept         = a_valid & ((keep_acc_r || (!a_last)) ? am_wr_cmd_accept[0] : acc_str_accept);
  assign a_accept           = out_valid & out_accept;
  assign am_wr_wdata[0]     = out_acc;
  assign acc_str_data       = out_acc;

endmodule : npu_am_write
