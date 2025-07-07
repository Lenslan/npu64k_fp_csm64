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

/*
 * This module implements the per channel parameter loading
 * the module:
 * - pops a block of parameters
 */
module npu_gtoa_fu_bpar
  import npu_types::*;
  import npu_gtoa_types::*;
  (
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore clk and rst_a are not read, and fu_inst is packed signal can be also ignored, some bits of rd_data are not read and can be ignored as well 
   input  logic                       clk,           // clock
   input  logic                       rst_a,         // asynchronous reset, active high
   // instruction
   input  logic                       fu_valid,      // instruction valid per functional unit
   input  act_dec_inst_t              fu_inst,       // instruction to be executed per functional units
   // one register read interface
   input  acc_t                       rd_data,       // read data
// spyglass enable_block W240
   // input parameters
   input  logic             [5:0]     par_q_lvl,     // parameter level
   output logic                       pop_q,         // if true then pop parameters from the queue
   output logic             [3:0]     pop_q_num,     // number of parameters to pop from queue
   // write parameters
   output logic                       bpar_we,       // write next block of per channel parameters
   // flow control
   output logic                       ostall,        // stall output
   input  logic                       stall          // stall input
   );
  // local wires
  logic canpop;
  
  // pop parameters into register
  assign pop_q_num = rd_data[3:0];
  assign canpop    = par_q_lvl >= {2'b0,pop_q_num};
  assign pop_q     = bpar_we;
  assign bpar_we   = fu_valid & ~stall;
  assign ostall    = fu_valid & (~canpop);
  
endmodule : npu_gtoa_fu_bpar
