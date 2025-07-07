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

// compile: vcs -sverilog ../../shared/RTL/npu_types.sv ../../shared/RTL/npu_slice_int.sv ../../shared/RTL/npu_iterator.sv npu_gtoa_types.sv npu_gtoa_pcu_iter.sv npu_gtoa_pcu_issue.sv npu_gtoa_pcu.sv +incdir+../../shared/RTL
`include "npu_defines.v"

module npu_gtoa_pcu
  import npu_types::*;
  import npu_gtoa_types::*;
  // parameters
  #(
    parameter int PROG_LEN    = 12,  // maximum number of instructions in the HLAPI
    parameter int NUM_LOOPS   = 3,   // number of loops in the HLAPI
    parameter int ISS_SIZE    = 32,  // issue table size
    parameter int NUM_FU      = 7,   // number of outputs to functional units
    parameter int NRD         = 12   // number of register file read ports
    )
  // interface signals
  (
   // clock and reset
   input  logic                                       clk,              // clock
   input  logic                                       rst_a,            // asynchronous reset, active high
  
   // interface from HLAPI
   input  logic                                       iter_req,         // request start iterations
   output logic                                       iter_ack,         // acknowledge iteration start
   input  offset_t        [NUM_LOOPS-1:0]             iter_shp,         // shape of the iterator
   input  act_inst_t      [PROG_LEN-1:0]              iter_prog,        // iteration program
   input  logic                                       iter_lay,         // accumulator layout

   // interface to functional units
   output logic           [NUM_FU-1:0]                fu_valid,         // instruction valid per functional unit
   output act_dec_inst_t  [VSIZE-1:0][NUM_FU-1:0]     fu_inst,          // instruction to be executed per functional units per lane

   // register file read ports
   output logic           [NRD-1:0]                   rd_ren,           // read enable
   output act_op_sel_t    [NRD-1:0]                   rd_vad,           // vector read operand select
   output logic           [NRD-1:0][ACT_SREG_NUM-1:0] rd_sad_oh,        // scalar read operand address
   output logic           [NRD-1:0]                   rd_b_oh,          // if true then parameter read
   output logic           [NRD-1:0][ISIZE-1:0]        rd_b_hi,          // if true then read upper half parameter
   output logic           [NRD-1:0][ACT_BREG_NUM-1:0] rd_wad_oh,        // word parameter read operand address
   output logic           [NRD-1:0][ACT_BREG_NUM-1:0] rd_had_oh,        // half-word parameter read operand address
   output logic           [NRD-1:0][ACT_BREG_NUM-1:0] rd_bad_oh,        // byte parameter read operand address

   // 
   input  logic                                       stall             // if true then stall pipeline
   );
  // local wires
  logic                          seq_req;          // request to start a new sequence
  logic                          seq_ack;          // acknowledge start of new sequence
  logic          [ISS_SIZE-1:0]  seq_pred;         // per instruction predicate bits
  act_haz_inst_t [ISS_SIZE-1:0]  seq_inst;         // activation program
  logic                          seq_idle;         // sequencer busy

  
  //
  // Iterator instance
  //
  npu_gtoa_pcu_iter
    #(
      .PROG_LEN  ( PROG_LEN   ),
      .NUM_LOOPS ( NUM_LOOPS  ), 
      .NUM_FU    ( NUM_FU     ),
      .ISS_SIZE  ( ISS_SIZE   )
      )
  u_iter_inst
    (
     .clk        ( clk        ),
     .rst_a      ( rst_a      ), 
     .iter_req   ( iter_req   ),
     .iter_ack   ( iter_ack   ),
     .iter_shp   ( iter_shp   ),
     .iter_prog  ( iter_prog  ),
     .iter_lay   ( iter_lay   ),
     .seq_req    ( seq_req    ),
     .seq_ack    ( seq_ack    ), 
     .seq_pred   ( seq_pred   ),
     .seq_inst   ( seq_inst   ),
     .idle       ( seq_idle   )
     );

  
  //
  // Issue instructions
  //
  npu_gtoa_pcu_issue
    #(
      .ISS_SIZE ( ISS_SIZE ),
      .NUM_FU   ( NUM_FU   ),
      .NRD      ( NRD      )
      )
  u_issue_inst
    (
     .clk         ( clk         ),
     .rst_a       ( rst_a       ),
     .seq_req     ( seq_req     ),
     .seq_ack     ( seq_ack     ),
     .seq_pred    ( seq_pred    ),
     .seq_inst    ( seq_inst    ),
     .seq_idle    ( seq_idle    ),
     .fu_valid    ( fu_valid    ),
     .fu_inst     ( fu_inst     ),
     .rd_ren      ( rd_ren      ),
     .rd_vad      ( rd_vad      ),
     .rd_sad_oh   ( rd_sad_oh   ),
     .rd_b_oh     ( rd_b_oh     ),
     .rd_b_hi     ( rd_b_hi     ),
     .rd_wad_oh   ( rd_wad_oh   ),
     .rd_had_oh   ( rd_had_oh   ),
     .rd_bad_oh   ( rd_bad_oh   ),
     .stall       ( stall       )
     );

endmodule : npu_gtoa_pcu

