// Library ARCv2HS-3.5.999999999
///---------------------------------------------------------------------------
///
/// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
///
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
/// work of Synopsys, Inc., and is fully protected under copyright and 
/// trade secret laws. You may not view, use, disclose, copy, or distribute 
/// this file or any information contained herein except pursuant to a 
/// valid written license from Synopsys, Inc.
///
/// The entire notice above must be reproduced on all authorized copies.
///
///---------------------------------------------------------------------------


// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_bpu_write_queue4 
  #(
    parameter WIDTH = 4
    )
    (
     input [WIDTH-1:0] din,  // data input
     input write,          // write to fifo control
     output reg full,      // indicates fifo is full
     
     input read,           // read from fifo control
     output reg [WIDTH-1:0] dout, // data output
     output reg empty,     // indicates fifo is empty
     output reg high_priority,  // indicates fifo is half full, so priority is raised

     input init,
     input clk,
     input rst_a
     );

//parameter WIDTH = 4; // bit width of data 

reg [1:0] rd_ptr;
reg [1:0] wr_ptr;
reg [1:0] rd_ptr_inc;
reg [1:0] wr_ptr_inc;
//reg [1:0] wr_ptr_inc2;
reg [1:0] rd_ptr_next;
reg [1:0] wr_ptr_next;

reg rd_done;
reg wr_done;
reg [2:0] count;
reg [2:0] count_inc;
reg [2:0] count_dec;
reg count_up;
reg count_down;
reg [2:0] count_next;

reg [WIDTH-1:0] ff0;
reg [WIDTH-1:0] ff1;
reg [WIDTH-1:0] ff2;
reg [WIDTH-1:0] ff3;

reg [WIDTH-1:0] ff0_next;
reg [WIDTH-1:0] ff1_next;
reg [WIDTH-1:0] ff2_next;
reg [WIDTH-1:0] ff3_next;
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused carry bit
reg [WIDTH-1:0] rd_data;

reg             unused_carry0;
reg             unused_carry1;
reg             unused_carry2;
reg             unused_carry3;
// leda NTL_CON13A on
// spyglass disable_block Clock_info03a
// SMD: Clock-net unconstrained
// SJ:  is constrained
always @(posedge clk or posedge rst_a)
begin: bpu_wr_queue_regs_PROC
  if (rst_a == 1'b1)
  begin
    wr_ptr <= 2'b00;
    rd_ptr <= 2'b00;
    count  <= 3'b000;
  end
  else 
  begin
    wr_ptr <= wr_ptr_next;
    rd_ptr <= rd_ptr_next;
    count  <= count_next;
  end // else: !if(rst_a == 1'b1)
end // block: bpu_wr_queue_regs_PROC
// spyglass enable_block Clock_info03a

always@ (*)
begin: bpu_wr_queue_regs_logic_PROC
  rd_ptr_next = rd_ptr;
  wr_ptr_next = wr_ptr;
  count_next  = count;

  if (init)
  begin
    wr_ptr_next = 2'b00;
    rd_ptr_next = 2'b00;
    count_next  = 3'b000;
  end
  else
  begin
    if (rd_done)
      rd_ptr_next = rd_ptr_inc;
  
    if (wr_done)
      wr_ptr_next = wr_ptr_inc;
  
    if (count_up)
      count_next  = count_inc;
    else if (count_down)
      count_next  = count_dec;
  end
end // bpu_wr_queue_regs_logic_PROC

// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin: bpu_wr_queue_ff_PROC
// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ: stack registerfile registers that don't need a reset
    ff0 <= ff0_next;
    ff1 <= ff1_next;
    ff2 <= ff2_next;
    ff3 <= ff3_next;
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01
end

always@(*)
begin: bpu_wr_queue_ff_logic_PROC
  ff0_next = ff0;
  ff1_next = ff1;
  ff2_next = ff2;
  ff3_next = ff3;

  if (wr_done) 
  begin
    case(wr_ptr)
      0: ff0_next = din;
      1: ff1_next = din;
      2: ff2_next = din;
      3: ff3_next = din;
    endcase
  end
end // bpu_wr_queue_ff_logic_PROC

always @*
begin: bpu_wr_queue_logic_PROC
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment 
// LJ:  pointer arithmetic with wraparound (dont_care overflow bit)
  {unused_carry0, wr_ptr_inc} = wr_ptr+1;
  {unused_carry1, rd_ptr_inc} = rd_ptr+1;
  {unused_carry2, count_inc} = count+1;
  {unused_carry3, count_dec} = count-1;
// leda B_3208 on
  empty = (count == 0);
  full = (count == 4);
  rd_done = read & (~empty);
  wr_done = write & (~full);
  count_up = wr_done & (~rd_done);
  count_down = rd_done & (~wr_done);

  high_priority = (count > 1);

  case(rd_ptr)
  0: rd_data = ff0;
  1: rd_data = ff1;
  2: rd_data = ff2;
  3: rd_data = ff3;
  endcase

  dout = rd_data;

end

endmodule


