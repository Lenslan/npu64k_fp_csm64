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
// convolution stash module quadrant loader
//  vcs -sverilog +incdir+../../shared/RTL ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_iterator.sv ../../shared/RTL/npu_fifo.sv npu_conv_types.sv npu_conv_stash_quad_load.sv
// analyze -format sverilog -vcs "+incdir+../../../shared/RTL ../../../shared/RTL/npu_types.sv ../../../shared/RTL/npu_iterator.sv ../../../shared/RTL/npu_fifo.sv ../npu_conv_types.sv ../npu_conv_stash_quad_load.sv"
//

`include "npu_axi_macros.svh"
`include "npu_vm_macros.svh"

module npu_conv_stash_quad_load
  import npu_types::*;
  import npu_conv_types::*;
  (
   // Clock and reset
   input  logic          clk,                          // Clock, all logic clocked at posedge
   input  logic          rst_a,                        // Asynchronous reset, active high
   // HLAPI interface
   input  logic          hlapi_valid,                  // Request new HLAPI start
   output logic          hlapi_accept,                 // Acknowledge new HLAPI start
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input  conv_hlapi_i_t hlapi_i,                      // HLAPI parameters
// spyglass enable_block W240
   // External interfaces
   // Quadrant output interface
   output logic          quad_valid,                   // Quadrant information is valid
   input  logic          quad_accept,                  // Quadrant information is accepted
   output quadrant_t     quad_data                     // Quadrant information
   );
  // local wires
  logic                it_req;     // iterator output valid
  logic                it_ack;     // iterator output acknowledge
  logic          [5:0] it_first;   // iterator first flags
  logic          [5:0] it_last;    // iterator last flags
  logic                it_vald;    // iterator last/first flags valid
  logic                pend_en;    // enable pending command counter
  logic          [1:0] pend_r;     // pending command counter
  logic          [1:0] pend_nxt;
  logic                can_issue;  // if true then can issue a new AXI command
  logic          [1:0] quad_dim;   // 0:W, 1:H 2:D 3:next IC
  quadrant_t           quad_in;    // quadrant read data
  logic                quad_in_valid; //quadrant data valid
  offset_t       [5:0] quad_it;      //{qdw,qdh,qdd,ni,no,grp=0}
  quadrant_t     [3:0] quad_data_r;  // buf quad data from hlapi init
  quadrant_t     [3:0] quad_data_nxt; // buf quad data from hlapi init

  //-Convolution Iteration Loop(CIT) ONN(7) --> INN --> ROW --> COL --> QD --> NI --> NO --> GRP
  localparam int CIT_GRP=0; localparam int CIT_NO=1;  localparam int CIT_NI=2;  localparam int CIT_QD=3;
  localparam int CIT_COL=4; localparam int CIT_ROW=5; localparam int CIT_INN=6; localparam int CIT_ONN=7;
  localparam int CIT_QDW=0; localparam int CIT_QDH=1; localparam int CIT_QDD=2; localparam int CIT_QDNI=3;


  //
  // Quadrant iterator
  //

  //npu_iterator
  //  #(
  //    .N ( 4 ) // number of nested loops, [grp][no][ni][qd]
  //    )
  //u_iter_inst_old
  //  (
  // .clk      ( clk               ),
  // .rst_a    ( rst_a             ),
  // .soft_rst ( 1'b0              ),
  // .in_req   ( hlapi_valid       ),
  // .in_ack   ( hlapi_accept      ),
  // .in_shp   ( hlapi_i.iter[3:0] ),
  // .it_req   ( it_req            ),
  // .it_ack   ( it_ack            ),
  // .it_first ( it_first          ),
  // .it_last  ( it_last           ),
  // .it_vald  ( it_vald           )
  // );


  assign quad_it = {hlapi_i.quad_iter[CIT_QDW],hlapi_i.quad_iter[CIT_QDH],hlapi_i.quad_iter[CIT_QDD],hlapi_i.iter[2:0]/*{ni,no,grp}*/};
  npu_iterator
    #(
      .N ( 6 ) // number of nested loops, {qdw,qdh,qdd,ni,no,grp=0}
      )
  u_iter_inst
    (
   .clk      ( clk               ),
   .rst_a    ( rst_a             ),
   .soft_rst ( 1'b0              ),
   .in_req   ( hlapi_valid       ),
   .in_ack   ( hlapi_accept      ),
   .in_shp   ( quad_it           ),
   .it_req   ( it_req            ),
   .it_ack   ( it_ack            ),
   .it_first ( it_first          ),
   .it_last  ( it_last           ),
   .it_vald  ( it_vald           )
   );



  //
  // Next state of address registers and drive AXI command
  //
  assign can_issue          = ~(&pend_r);
  assign it_ack             = can_issue;

  // outputs: pend_nxt
  always_comb
  begin : axi_nxt_PROC
    // defaults
    pend_en  = 1'b0;
    pend_nxt = pend_r;
    quad_data_nxt = quad_data_r;
    // update register
    if (hlapi_valid && hlapi_accept)
    begin
      // start a new sequence
      quad_data_nxt = hlapi_i.quad_data;
    end
    // update pending counter
    if ((it_req & it_ack) != (quad_valid & quad_accept))
    begin
      pend_en = 1'b1;
      if (quad_valid & quad_accept)
      begin
        pend_nxt -= $unsigned(1);
      end
      else
      begin
        pend_nxt += $unsigned(1);
      end
    end
  end : axi_nxt_PROC


  // track state
  // outputs: pend_r
  always_ff @(posedge clk or posedge rst_a)
  begin : state_reg_PROC
    if (rst_a == 1'b1)
    begin
      pend_r <= '0;
      quad_data_r <= '0;
    end
    else
    begin
      quad_data_r <= quad_data_nxt;
      if (pend_en)
      begin
        pend_r <= pend_nxt;
      end
    end
  end : state_reg_PROC



  // outputs: quad_in_valid, quad_in
  assign quad_in_valid = it_req & it_ack;
  always_comb
  begin : quad_in_PROC
    quad_in       = 'b0;
    if (quad_in_valid)
    begin
      casez (it_last[5:3]) //{qdw,qdh,qdd,ni,no,grp=0}
      3'b111: //go to next NI
        begin
          quad_in = quad_data_nxt[CIT_QDNI];
        end
      3'b110: //go to next QDD
        begin
          quad_in = quad_data_nxt[CIT_QDD];
        end
      3'b10?: //go to next QDH
        begin
          quad_in = quad_data_nxt[CIT_QDH];
        end
      default: //go to next QDW
        begin
          quad_in = quad_data_nxt[CIT_QDW];
        end
      endcase
    end
  end : quad_in_PROC

  //
  // FIFO storing quadrant read data from AXI
  //
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentional open
  npu_fifo
    #(
    .SIZE   ( 3                 ),
    .DWIDTH ( $bits(quadrant_t) ),
    .FRCVAL ( 1'b0              ),
    .FRCACC ( 1'b1              ) // FIFO can always accept, guarded by the pend_r counter
      )
  u_dfifo_inst
    (
     .clk          ( clk             ),
     .rst_a        ( rst_a           ),
     .valid_write  ( quad_in_valid   ),
     .accept_write (                 ), // intentionally unconnected
     .data_write   ( quad_in         ),
     .valid_read   ( quad_valid      ),
     .accept_read  ( quad_accept     ),
     .data_read    ( quad_data       )
     );
// spyglass enable_block W287b

endmodule : npu_conv_stash_quad_load
