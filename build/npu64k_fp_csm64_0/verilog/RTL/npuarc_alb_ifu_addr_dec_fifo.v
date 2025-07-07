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
//


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }





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
//  This module if a generic FIFO design used by IFU. 
//  
//  The module allows concurrent read and write of the FIFO. 
//  It detects overflow and underflow for simulation but does not include them in final logic.
//  In addition to async. reset, there is a restart signal that does reset of the flops synchronously. 
//  This design is a paramerterized design and doesn't need defines.vpp
// ===========================================================================



`include "npuarc_defines.v"

module npuarc_alb_ifu_addr_dec_fifo 
  ( 
  input                    clk,
  input                    rst_a,
  input                    restart,
  input                    wr,
  input [2:0]     wdata,
  input                        rd,
  output reg [2:0]    rdata,
  output [2:2] rdata_flop,
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs 
// LJ:  standard fifo signal
  output reg              full,
  output reg              empty,
// leda NTL_CON32 on

  output                  afull,
  output                  aempty
  );



// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs 
// LJ:  standard fifo signal
reg [2:0] cnt;
reg [2:0] cnt_nxt;

reg [2:0] mem0;
reg [2:0] mem0_nxt;
reg [2:0] mem1;
reg [2:0] mem1_nxt;
reg [2:0] mem2;
reg [2:0] mem2_nxt;
reg [2:0] mem3;
reg [2:0] mem3_nxt;

reg [1:0] wr_ptr;
reg [1:0] wr_ptr_nxt;
reg [1:0] rd_ptr;
reg [1:0] rd_ptr_nxt;

reg full_nxt;
reg empty_nxt;

reg [1:0]  rd_ptr_nxt_tmp;
reg [2:0] cnt_nxt_tmp;
reg                   empty_nxt_tmp;
reg                   full_nxt_tmp;

// initialize fifo registers to random values
// leda FM_2_33D off
// LMD: Do not use translate_on/off or synthesis_on/off pragmas
// LJ:  Initialization replacing X with random values to avoid X propagation
// synopsys translate_off
integer i;

initial
begin
  // use random numbers; must be wider than the widest possible mem width
    mem0 = {$random,$random,$random,$random,$random,$random,$random,$random};
    mem1 = {$random,$random,$random,$random,$random,$random,$random,$random};
    mem2 = {$random,$random,$random,$random,$random,$random,$random,$random};
    mem3 = {$random,$random,$random,$random,$random,$random,$random,$random};
end

//synopsys translate_on
// leda FM_2_33D on

// leda NTL_CON32 on
always @(*) 
begin: fifo_PROC 
  wr_ptr_nxt = wr_ptr;
  rd_ptr_nxt = rd_ptr;
  cnt_nxt = cnt;
  empty_nxt = empty;
  full_nxt = full;
// leda W484 off
// leda B_3200 off
// leda B_3219 off
// LMD: Unequal length LHS and RHS in srithmetic assignment 
// LJ:  pointer arithmetic with wraparound (dont_care overflow bit)
//leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS : x, RHS : y
// LJ:  single bit 1 addition is intentional
  case ({wr, rd})
    2'b01: begin
      if (rd_ptr == $unsigned(4-1)) begin
        rd_ptr_nxt = {2{1'b0}};
      end
      else begin
        rd_ptr_nxt = rd_ptr + 1;
      end
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs 
// LJ:  standard fifo signal
      full_nxt = 1'b0;
      if (rd_ptr_nxt == wr_ptr) begin
        empty_nxt = 1'b1;
      end

      cnt_nxt = cnt - 1;
    end
    2'b10: begin
      if (wr_ptr == $unsigned(4-1)) begin
        wr_ptr_nxt = {2{1'b0}};
      end
      else begin
        wr_ptr_nxt = wr_ptr + 1;
      end
      empty_nxt = 1'b0;
      if (wr_ptr_nxt == rd_ptr) begin
        full_nxt = 1'b1;
      end
      cnt_nxt = cnt + 1;
    end
    2'b11: begin
      if (rd_ptr == $unsigned(4-1)) begin
        rd_ptr_nxt = {2{1'b0}};
      end
      else begin
        rd_ptr_nxt = rd_ptr + 1;
      end
      if (wr_ptr == $unsigned(4-1)) begin
        wr_ptr_nxt = {2{1'b0}};
      end
      else begin
        wr_ptr_nxt = wr_ptr + 1;
      end
    end
    default: begin
// spyglass disable_block Ac_conv01
// SMD: Synchronizers converging on flop
// SJ:  Synchronized conv signals are independent
      cnt_nxt = cnt;
// spyglass enable_block Ac_conv01
    end
  endcase
//leda BTTF_D002 on
//leda B_3200 on
//leda B_3219 on
// leda W484 on
// leda NTL_CON32 on
end


always @ * 
begin: fifo_regs_nxt_PROC
  if (restart) begin
    rd_ptr_nxt_tmp = wr_ptr;
    if (wr == 1'b1) begin
      cnt_nxt_tmp = { {(2){1'b0}}, 1'b1};
      empty_nxt_tmp = 1'b0;
      full_nxt_tmp = (4 == 1);
    end
    else begin  
      cnt_nxt_tmp = {(2+1){1'b0}};
      empty_nxt_tmp = 1'b1;
      full_nxt_tmp = 1'b0;
    end
  end
  else begin
    rd_ptr_nxt_tmp = rd_ptr_nxt;
    cnt_nxt_tmp = cnt_nxt;
    empty_nxt_tmp = empty_nxt;
    full_nxt_tmp = full_nxt;
  end
end //block: fifo_regs_PROC


always @(posedge clk or posedge rst_a) 
begin: fifo_regs_PROC
  if (rst_a == 1'b1) begin
    wr_ptr <= {2{1'b0}};
    rd_ptr <= {2{1'b0}};
    cnt <= {(2+1){1'b0}};
    empty <= 1'b1;
    full <= 1'b0;
  end
  else begin
    wr_ptr <= wr_ptr_nxt;
// spyglass disable_block Clock_info03a
// SMD: clock-net unconstrained
// SJ:  constrained
      rd_ptr <= rd_ptr_nxt_tmp;
      cnt <= cnt_nxt_tmp;
      empty <= empty_nxt_tmp;
      full <= full_nxt_tmp;
  end
end //block: fifo_regs_PROC
// spyglass enable_block Clock_info03a

// spyglass disable_block WRN_1024
// SMD: unsigned argument passed to $unsigned function call
// SJ:  arguments unsigned by default

//leda B_3219 off
//leda B_3212 off
assign afull = ($unsigned(cnt) >= 3);
assign aempty = ($unsigned(cnt) <= 1);
//leda B_3219 on
//leda B_3212 on

// spyglass enable_block WRN_1024

//mem rd/wr

// leda FM_2_22 off
// LMD: Possible range overflow
// LJ:  the range is parameterized and is not out of the range 
// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  memory element has no need to reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset

// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  signal from mem model
reg [2:0] rdata_erly;
// leda NTL_CON13A on

always @ *
begin : rdata_early_PROC
  rdata_erly  = mem0;
  case (rd_ptr_nxt)
     2'd0 : rdata_erly  = mem0;
     2'd1 : rdata_erly  = mem1;
     2'd2 : rdata_erly  = mem2;
     2'd3 : rdata_erly  = mem3;
  default: rdata_erly  = mem0;
  endcase   
end
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  configubility issue, parameter is used as mux condition
reg [2:2] rdata_r; 
reg [2:2] rdata_r_nxt; 
// leda NTL_CON13A on

always @(posedge clk) 
begin: fifo_mem_wr_PROC
     mem0 <= mem0_nxt;
     mem1 <= mem1_nxt;
     mem2 <= mem2_nxt;
     mem3 <= mem3_nxt;
end //block: fifo_mem_PROC

// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty default kept
always @ * 
begin: fifo_mem_wr_nxt_PROC
  mem0_nxt = mem0;
  mem1_nxt = mem1;
  mem2_nxt = mem2;
  mem3_nxt = mem3;
  if (wr == 1'b1) begin
     case(wr_ptr)
      2'd0: mem0_nxt = wdata;
      2'd1: mem1_nxt = wdata;
      2'd2: mem2_nxt = wdata;
      2'd3: mem3_nxt = wdata;
       default: ;
     endcase
  end
end //block: fifo_mem_PROC
// spyglass enable_block W193

always @(posedge clk) 
begin: fifo_mem_rd_PROC
  rdata_r <= rdata_r_nxt; 
end //block: fifo_mem_PROC

always @ * 
begin: fifo_mem_rd_nxt_PROC
  if (wr && (cnt_nxt == { {2{1'b0}}, 1'b1 })) begin //bypass input
    rdata_r_nxt = wdata[2: 2]; 
  end
  else begin
    rdata_r_nxt = rdata_erly[2: 2]; 
  end
end //block: fifo_mem_PROC



always @ *
begin : rdata_out_PROC
  rdata  = mem0;
  case (rd_ptr)
     2'd0 : rdata  = mem0;
     2'd1 : rdata  = mem1;
     2'd2 : rdata  = mem2;
     2'd3 : rdata  = mem3;
  default: rdata  = mem0;
  endcase   
end

assign rdata_flop = {(2-2+1){1'b0}}; 
// leda NTL_RST03 on
// leda FM_2_22 on
// leda S_1C_R on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01


endmodule

