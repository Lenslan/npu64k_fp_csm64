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
// vcs -sverilog ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_fifo.sv npu_gtoa_types.sv npu_gtoa_am_agu.sv npu_gtoa_am_read.sv +incdir+../../shared/RTL
// analyze -format sverilog -vcs "../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_fifo.sv ../npu_gtoa_types.sv ../npu_gtoa_am_agu.sv ../npu_gtoa_am_read.sv +incdir+../../../shared/RTL"
//

`include "npu_defines.v"
`include "npu_am_macros.svh"

module npu_gtoa_am_read
  import npu_types::*;
  import npu_gtoa_types::*;
  (
   input  logic                    clk,                 // clock, all logic clocked at posedge
   input  logic                    rst_a,               // asynchronous reset, active high
   input  logic                    in_valid,            // new command valid
   output logic                    in_accept,           // new command accept
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore
   input  act_hlapi_am_agu_t       in_pars,             // AGU parameters
// spyglass enable_block W240
   `AMRMST(am_rd_,1),                                   // AM read interface
// AM read interface
   output logic                    out_valid,           // Accumulator is valid
   input  logic                    out_accept,          // Accumulator is accepted
   output vyixacc_t                out_acc              // Read accumulator
   );
  localparam int D = 4;
  //
  // Internal wires
  //
  // AGU outputs
  logic                    a_valid;           // output address is valid
  logic                    a_accept;          // output address is accepted
  // other
  logic                    can_rd;
  logic                    lvl_en;
  logic     [2:0]          lvl_r;
  logic     [2:0]          lvl_nxt;
  logic                    wout_accept;
  vyixacc_t                wout_acc;
  
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
   .out_addr   ( am_rd_cmd_addr[0] )
     );


  //
  // Drive memory read request
  //
  assign can_rd             = lvl_r != unsigned'(D);
  assign am_rd_cmd_valid    = a_valid & can_rd;
  assign a_accept           = am_rd_cmd_accept & can_rd;

  
  //
  // FIFO storing AM read data
  //
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :intentionally unconnected
  npu_fifo
  #(.SIZE   ( D                ),
    .DWIDTH ( $bits(vyixacc_t) ),
    .FRCVAL ( 1'b0             ),
    .FRCACC ( 1'b1             ) // FIFO can always accept, guarded by the use_acc FIFO
    )
  u_dfifo_inst
    (
     .clk          ( clk          ),
     .rst_a        ( rst_a        ),
     .valid_write  ( am_rd_rvalid ),
     .accept_write (              ), // intentionally unconnected
     .data_write   ( am_rd_rdata  ),
     .valid_read   ( out_valid    ),
     .accept_read  ( wout_accept  ),
     .data_read    ( wout_acc     )
     );
// spyglass enable_block W287b

  // drive outputs depending on config
  assign out_acc     = wout_acc;
  assign wout_accept = out_accept;
  
  //
  // Level
  //
  // outputs: lvl_en, lvl_nxt
  always_comb
  begin : lvl_nxt_PROC
    // defaults
    lvl_en = 1'b0;
    lvl_nxt = lvl_r;
    if (a_valid & a_accept)
    begin
      lvl_en  = 1'b1;
      lvl_nxt = lvl_nxt + 'd1;
    end
    if (out_valid & wout_accept)
    begin
      lvl_en  = 1'b1;
      lvl_nxt= lvl_nxt - 'd1;
    end
  end : lvl_nxt_PROC

  // outputs lvl_r
  always_ff @(posedge clk or posedge rst_a)
  begin : lvl_reg_PROC
    if (rst_a == 1'b1)
    begin
      lvl_r <= '0;
    end
    else 
    begin
      if (lvl_en)
      begin
        lvl_r <= lvl_nxt;
      end
    end
  end : lvl_reg_PROC

endmodule : npu_gtoa_am_read
