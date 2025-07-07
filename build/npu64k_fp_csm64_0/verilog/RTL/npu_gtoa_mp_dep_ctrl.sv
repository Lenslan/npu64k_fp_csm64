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
 * This module implements the read/write dependency control for maxpool stash
 * the module:
 * - pops a block of parameters
 */
module npu_gtoa_mp_dep_ctrl
  import npu_types::*;
  import npu_gtoa_types::*;
  (
   input  logic                         clk,           // clock
   input  logic                         rst_a,         // asynchronous reset, active high
   input  logic                         rd_in_en,      // new input enable
   input  logic                         wr_in_en,      // new input enable
   // input parameter
// spyglass disable_block W240
//SMD:Unread input
//SJ :Ignore packed signal
   input  offset_t [ACT_POOL_LOOPS-1:0] iter,          // maximum rows
// spyglass enable_block W240
   // input read and write handshake
   input  logic                         rd_hs,         // read handshake
   input  logic                         wr_hs,         // write handshake
   input  logic                         wr_nopend,     // no pending write on vm
   // output read and write gate signal
   output logic                         canrd,         // maxpool stash can read
   output logic                         canwr          // maxpool stash can write
   );
  // local wires
  offset_t       rd_rcnt_r;    // maxpool stash read row counter
  offset_t       rd_rcnt_nxt;  // maxpool stash read row counter next
  offset_t       wr_rcnt_r;    // maxpool stash write row counter
  offset_t       wr_rcnt_nxt;  // maxpool stash write row counter next
  logic          rd_codd_r;    // maxpool stash read col odd
  logic          rd_codd_nxt;  // maxpool stash read col odd next
  logic          wr_codd_r;    // maxpool stash write col odd
  logic          wr_codd_nxt;  // maxpool stash write col odd next
  logic          rdcnt_upd_en; // maxpool stash read counter update enable
  logic          wrcnt_upd_en; // maxpool stash write counter update enable
  offset_t       rd_iter_row;
  offset_t       rd_iter_onn;
  offset_t       rd_rows;
  offset_t [ACT_POOL_LOOPS-1:0] rd_iter_r;
  offset_t       wr_iter_row;
  offset_t       wr_iter_onn;
  offset_t       wr_rows;
  offset_t [ACT_POOL_LOOPS-1:0] wr_iter_r;

  assign canrd = ((rd_codd_r == wr_codd_r)
               | ((rd_codd_r != wr_codd_r) && (rd_rcnt_r != wr_rcnt_r)))
               & wr_nopend;
  assign canwr = 1'b1; // write dependency is already granted by pooling pipeline
  assign rd_iter_row = rd_iter_r[2];
  assign rd_iter_onn = rd_iter_r[3];
  assign rd_rows     = rd_iter_onn[2] ? (rd_iter_row << 'd2) : (rd_iter_onn[1] ? (rd_iter_row << 'd1) : rd_iter_row);
  assign wr_iter_row = wr_iter_r[2];
  assign wr_iter_onn = wr_iter_r[3];
  assign wr_rows     = wr_iter_onn[2] ? (wr_iter_row << 'd2) : (wr_iter_onn[1] ? (wr_iter_row << 'd1) : wr_iter_row);
  
  // stash counter update
  always_comb
  begin : pool_cntr_PROC
    // update read pointer for each read handshake
    rdcnt_upd_en = rd_hs;
    rd_rcnt_nxt = rd_rcnt_r + 1'd1;
    rd_codd_nxt = rd_codd_r;
    if(rd_rcnt_nxt == rd_rows) begin
      rd_rcnt_nxt = '0;
      rd_codd_nxt = ~rd_codd_r;
    end
    // update write pointer for each write handshake
    wrcnt_upd_en = wr_hs;
    wr_rcnt_nxt = wr_rcnt_r + 1'd1;
    wr_codd_nxt = wr_codd_r;
    if(wr_rcnt_nxt == wr_rows) begin
      wr_rcnt_nxt = '0;
      wr_codd_nxt = ~wr_codd_r;
    end
  end :  pool_cntr_PROC

  // register
  always_ff @(posedge clk or
              posedge rst_a)
  begin : reg_PROC
    if (rst_a == 1'b1) begin
      rd_rcnt_r       <= '0;
      wr_rcnt_r       <= '0;
      rd_codd_r       <= '0;
      wr_codd_r       <= '0;
      rd_iter_r       <= '0;
      wr_iter_r       <= '0;
    end
    else begin
      if (rdcnt_upd_en) begin
        rd_rcnt_r     <= rd_rcnt_nxt;
        rd_codd_r     <= rd_codd_nxt;
      end
      if (wrcnt_upd_en) begin
        wr_rcnt_r    <= wr_rcnt_nxt;
        wr_codd_r    <= wr_codd_nxt;
      end
      if (rd_in_en) begin
        rd_iter_r    <= iter;
      end
      if (wr_in_en) begin
        wr_iter_r    <= iter;
      end
    end
  end : reg_PROC

endmodule : npu_gtoa_mp_dep_ctrl
