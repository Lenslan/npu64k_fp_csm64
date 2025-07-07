// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
// ===========================================================================
//
// Description:
// This file implements BPU control registers
//----------------------------------------------------------------------------

`include "npuarc_defines.v"
// Set simulation timescale
//
`include "const.def"

//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_bpu_aux (
  input clk,
  input rst_a,
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  standard aux interface
  input [`npuarc_DATA_RANGE] sr_wdata_r, 
// leda NTL_CON13C on
  input aux_read,                  //to enable register read status when aux_bpu_ren_r=1
  input aux_bpu_ren_r,             //actual read
  input aux_bpu_wen_r,             //actual write
  input [3:0] aux_bpu_raddr_r,     //read address
  input [3:0] aux_bpu_waddr_r,     //write address
 
  output reg [`npuarc_DATA_RANGE] bpu_aux_rdata,
  output reg bpu_aux_illegal,      //not allowed to access (depending on aux_write or aux_read)
  output reg bpu_aux_k_rd,         //kernal readable (when aux_read?) 
  output reg bpu_aux_k_wr,         //kernal writable (when aux_write?)
  output reg bpu_aux_unimpl,       //not implemented (not depneding on aux_write or aux_read)
  output reg bpu_aux_serial_sr,    //serialized access for sr (
  output reg bpu_aux_strict_sr,    //strictly serialized access for sr

  output bpu_flush,
  input        start_prediction,   // update bpu_ctrl at new prediction (2cyc start-point)
  output [2:0] bpu_ctrl,           // BPU_CTRL AUX register with single cycle timing
  output [2:0] bpu_ctrl_2cyc,      // BPU_CTRL AUX register with 2-cycle timing
  input  bpu_flush_ack

);




  wire     bpu_flush_start;
  assign bpu_flush_start = aux_bpu_wen_r && (aux_bpu_waddr_r == 4'b0);
  reg       bpu_flush_r;
  reg       bpu_flush_next;
  reg [2:0] bpu_ctrl_r_2cyc;
  reg [2:0] bpu_ctrl_r;
  reg [2:0] bpu_ctrl_next;
  reg [2:0] bpu_ctrl_r_r;
  assign bpu_flush = bpu_flush_start | bpu_flush_r;

  // BPU_CTRL output with single-cycle timing and extra pipeline register to relax timing.
  assign bpu_ctrl = bpu_ctrl_r_r;

  // BPU_CTRL_2cyc has 2-cycle timing
  npuarc_alb_2cyc_checker #(.WIDTH(3)) u_alb_2cyc_checker 
     (
      .data_in  (
                  bpu_ctrl_r_2cyc 
                 ),
      .data_out (
                  bpu_ctrl_2cyc 
                 ),
      .clk (clk));


always @(posedge clk or posedge rst_a)
begin: bpu_ctrl_PROC
  if (rst_a == 1'b1) begin
    bpu_ctrl_r_2cyc  <= 3'd0;
  end
  else if (start_prediction)
  begin
    bpu_ctrl_r_2cyc  <= bpu_ctrl_r;
  end 
end

always @(posedge clk or posedge rst_a)
begin: reg_wr_PROC
  if (rst_a == 1'b1) begin
    bpu_flush_r <= 1'b0;
    bpu_ctrl_r  <= 3'd0;
    bpu_ctrl_r_r  <= 3'd0;
  end
  else begin
    bpu_flush_r <= bpu_flush_next;
    bpu_ctrl_r <= bpu_ctrl_next;
    // BPU_CTRL_r_r provides an additional pipeline register for bpu_ctrl_r.
    // The only purpose of this register is to make it easier to meet timing.
    // This register can be placed anywhere in the layout.
    bpu_ctrl_r_r  <= bpu_ctrl_r;

  end 
end //block: reg_wr_PROC

always@ (*)
begin: bpu_ctrl_update_PROC
  bpu_ctrl_next = bpu_ctrl_r;
  if (aux_bpu_wen_r & (aux_bpu_waddr_r ==  4'b1)) begin
     // value of 5 is reserved and ignored on write
     if (sr_wdata_r[2:0] != 3'd5) 
        bpu_ctrl_next = sr_wdata_r[2:0];
  end
end // bpu_ctrl_update_PROC

always@ (*)
begin: bpu_flush_PROC
  bpu_flush_next = bpu_flush_r;
  if (bpu_flush_start & (~bpu_flush_ack)) begin
    bpu_flush_next = 1'b1;
  end
  else if (bpu_flush_ack) begin
    bpu_flush_next = 1'b0;
  end
end // bpu_flush_PROC


//read
always @(*) 
begin: reg_rd_PROC
  bpu_aux_rdata = {`npuarc_DATA_SIZE{1'b0}};
  bpu_aux_illegal = 1'b0;
  bpu_aux_k_rd = 1'b0;
  bpu_aux_k_wr = 1'b0;
  bpu_aux_unimpl = 1'b1;
  bpu_aux_serial_sr = 1'b0;
  bpu_aux_strict_sr = 1'b0;
  if (aux_bpu_ren_r) begin
    if (aux_bpu_raddr_r == 4'b0) begin
      bpu_aux_illegal = aux_read;
      bpu_aux_k_rd = 1'b0;
      bpu_aux_k_wr = 1'b1;
      bpu_aux_unimpl = 1'b0;
      bpu_aux_serial_sr = 1'b1;
      bpu_aux_strict_sr = 1'b1;
    end
    else if (aux_bpu_raddr_r == 4'b1) begin
      bpu_aux_unimpl  = 1'b0;
      bpu_aux_illegal = 1'b0;
      bpu_aux_k_rd    = 1'b1;
      bpu_aux_k_wr    = 1'b1;
      bpu_aux_serial_sr = 1'b1;
      bpu_aux_strict_sr = 1'b1;
      bpu_aux_rdata = {{(`npuarc_DATA_SIZE-3){1'b0}}, bpu_ctrl_r};
    end
    else if (aux_bpu_raddr_r == `npuarc_LPB_CTRL_ADDR_AUX) begin
      bpu_aux_illegal = 1'b1;
    end
    else begin
      bpu_aux_unimpl = 1'b1;
    end
  end
end //block: reg_rd_PROC


endmodule
