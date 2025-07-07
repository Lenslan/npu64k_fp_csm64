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
//  This module is the fetch buffer FIFO design
//  It allows read and write concurrently.
//  write can write 1 to 2 words that is from 1 or 2 of the memory banks
//  read  can also read 1 to 2 words 
//  total 4 consecutive words are output pointed by the read pointer
//  It supports restart that is synchronous reset to reset the pointer and counter
// ===========================================================================
//
// Set simulation timescale
//
`include "const.def"

`include "npuarc_defines.v"


module npuarc_alb_fetch_buf_br_fifo 
  (
  input clk,
  input rst_a,
  input restart,
  input [1:0] wr,
  input [30:0] wdata0,
  input [30:0] wdata1,
  input [1:0] rd,
  output reg [30:0] rdata0,
  output reg [30:0] rdata1,
  output reg [30:0] rdata_next0,
  output reg [30:0] rdata_next1,
  output     [2:0] fifo_cnt,
  output     [2:0] fifo_cnt_nxt 
);


// leda BTTF_D002 off
// LMD: Unequal length LHS and RHS in assignment LHS: x, RHS : y
// LJ: addition to a less bit constant is intentional

// leda B_3208_A off
// LMD: Unequal length  operand in conditional expression
// LJ:  pointer arithmetic, overflow is dont_care

// leda W484 off
// leda B_3200 off
// leda B_3219 off
// LMD: Unequal length operand in bit/arithmetic operator
// LJ:  pointer arithmetic, overflow is dont_care

reg [30:0] mem0;
reg [30:0] mem0_nxt;
reg [30:0] mem1;
reg [30:0] mem1_nxt;
reg [0:0] wr_ptr;
reg [0:0] wr_ptr_nxt;
reg [0:0] rd_ptr;
reg [0:0] rd_ptr_nxt;
reg [0:0] wr_ptr0;
reg [0:0] wr_ptr1;
reg [0:0] rd_ptr0;
reg [0:0] rd_ptr1;
reg [0:0] rd_ptr2;
reg [0:0] rd_ptr3;
reg [2:0] cnt;
reg [2:0] cnt_nxt;
reg [2:0] cnt_nxt_after_rd;
wire [0:0] rd_ptr_inc1;

reg [0:0] wr_ptr_nxt_tmp;
reg [0:0] rd_ptr_nxt_tmp;
reg [2:0] cnt_nxt_tmp;

assign rd_ptr_inc1 = (rd_ptr == $unsigned(2-1)) ? 0 : rd_ptr + 1;
wire [0:0] rd_ptr_inc2;
assign rd_ptr_inc2 = (2==1) ?                          0 : 
                     (2==2) ?                     rd_ptr :
                     (rd_ptr == $unsigned(2-1)) ?      1 : 
                     (rd_ptr == $unsigned(2-2)) ?      0 : 
                                                   rd_ptr + 2;
wire [0:0] wr_ptr_inc1;
assign wr_ptr_inc1 = (wr_ptr == $unsigned(2-1)) ? {1{1'b0}} : wr_ptr + 1;
wire [0:0] wr_ptr_inc2;
assign wr_ptr_inc2 = (2==1) ?                          0 : 
                     (2==2) ?                     wr_ptr :
                     (wr_ptr == $unsigned(2-1)) ?      1 : 
                     (wr_ptr == $unsigned(2-2)) ?      0 : 
                                                   wr_ptr + 2;

always @(*) 
begin: ptr_ctl_PROC
  wr_ptr_nxt           = wr_ptr;
  rd_ptr_nxt           = rd_ptr;
  cnt_nxt              = cnt;
  case (rd)
    2'b01: begin
      rd_ptr_nxt       = rd_ptr_inc1;
      cnt_nxt_after_rd = cnt - 1;
    end
    2'b11: begin
      rd_ptr_nxt       = rd_ptr_inc2;
      cnt_nxt_after_rd = cnt - 2;
    end
    default: begin
      cnt_nxt_after_rd = cnt;
    end
  endcase
  case (wr)
    2'b01,
    2'b10: begin
      wr_ptr_nxt       = wr_ptr_inc1;
      cnt_nxt          = cnt_nxt_after_rd + 1;
    end
    2'b11: begin
      wr_ptr_nxt       = wr_ptr_inc2;
      cnt_nxt          = cnt_nxt_after_rd + 2;
    end
    default: begin
      cnt_nxt          = cnt_nxt_after_rd;
    end
  endcase
end //block: ptr_ctl_PROC

always @(*) 
begin: ptr_ctl_tmp_PROC
  wr_ptr_nxt_tmp = wr_ptr_nxt;
  rd_ptr_nxt_tmp = rd_ptr_nxt;
  cnt_nxt_tmp    = cnt_nxt;
  if (restart)
  begin
    wr_ptr_nxt_tmp = {1{1'b0}};
    rd_ptr_nxt_tmp = {1{1'b0}};
    cnt_nxt_tmp    = {(1+2){1'b0}};
  end
end //block: ptr_ctl_tmp_PROC

always @(posedge clk or posedge rst_a) 
begin: reg_PROC
  if (rst_a == 1'b1)
  begin
    wr_ptr   <= {1{1'b0}};
    rd_ptr   <= {1{1'b0}};
    cnt      <= {(1+2){1'b0}};
  end
  else
  begin
      wr_ptr <= wr_ptr_nxt_tmp;
      rd_ptr <= rd_ptr_nxt_tmp;
      cnt    <= cnt_nxt_tmp;
  end
end //reg_PROC

assign fifo_cnt = cnt;
assign fifo_cnt_nxt = cnt_nxt;
//mem rd/wr
always @(*) 
begin: wr_ptr_gen_PROC
  wr_ptr0 = wr_ptr;
  wr_ptr1 = {1{1'b0}};
  if (wr==2'b11) begin
    if (wr_ptr == $unsigned(2-1)) begin
      wr_ptr1 = {1{1'b0}};
    end
    else begin
      wr_ptr1 = wr_ptr + 1;
    end
  end
end 
//block: wr_ptr_gen_PROC
// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  mem is a memory element and two different elements are updated at same time
// leda S_1C_R off
// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ:  memory element has no need to reset 
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset


always @(posedge clk) 
begin: mem_wr_PROC
     mem0 <= mem0_nxt;
     mem1 <= mem1_nxt;
end //block: mem_wr_PROC


always @ * 
begin: mem_wr_nxt_PROC
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty default kept
// leda G_551_1_C off
// LMD: Use 'if(wr == 'b0)' or 'if(wr == 'b1)' for synchronous reset/set/load expressions
// LJ:  memory element has no need to reset 
  mem0_nxt = mem0;
  mem1_nxt = mem1;
  case (wr)
    2'b01: begin
             case(wr_ptr0)
            1'd0: mem0_nxt = wdata0;
            1'd1: mem1_nxt = wdata0;
             default: ;
             endcase     
           end
    2'b10: begin
             case(wr_ptr0)
            1'd0: mem0_nxt = wdata1;
            1'd1: mem1_nxt = wdata1;
             default: ;
             endcase     
           end
    2'b11: begin
             case(wr_ptr0)
            1'd0: mem0_nxt = wdata0;
            1'd1: mem1_nxt = wdata0;
             default: ;
             endcase     
             case(wr_ptr1)
            1'd0: mem0_nxt = wdata1;
            1'd1: mem1_nxt = wdata1;
             default: ;
             endcase     
           end
    default: ;
  endcase
// spyglass enable_block W193
// leda G_551_1_C on
end //block: mem_wr_PROC

// leda S_1C_R on
// leda NTL_RST03 on
// leda FM_1_7 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

always @(*) 
begin: rd_ptr_gen_PROC
  rd_ptr0 = rd_ptr;
  if (rd_ptr0==$unsigned(2-1)) 
     rd_ptr1 = {1{1'b0}};
  else 
     rd_ptr1 =  rd_ptr0 + 1;
  if (rd_ptr1==$unsigned(2-1)) 
     rd_ptr2 = {1{1'b0}};
  else 
     rd_ptr2 = rd_ptr1 + 1;
  if (rd_ptr2==$unsigned(2-1)) 
     rd_ptr3 = {1{1'b0}};
  else 
     rd_ptr3 = rd_ptr2 + 1;
end //block: rd_ptr_gen_PROC

always @ *
begin : rdata_out_PROC
  rdata0  = mem0;
  rdata1  = mem0;
  rdata_next0 = mem0;
  rdata_next1 = mem0;
  case (rd_ptr0)
     0 : rdata0  = mem0;
     1 : rdata0  = mem1;
  default: rdata0  = mem0;
  endcase   
   
  case (rd_ptr1)
     0 : rdata1  = mem0;
     1 : rdata1  = mem1;
  default: rdata1  = mem0;
  endcase     
 
  case (rd_ptr2)
     0 : rdata_next0  = mem0;
     1 : rdata_next0  = mem1;
  default: rdata_next0  = mem0;
  endcase    
  
  case (rd_ptr3)
     0 : rdata_next1  = mem0;
     1 : rdata_next1  = mem1;
  default: rdata_next1  = mem0;
  endcase      
end


// leda W484 on
// leda B_3200 on
// leda B_3219 on
// leda B_3208_A on
// leda BTTF_D002 on

endmodule

