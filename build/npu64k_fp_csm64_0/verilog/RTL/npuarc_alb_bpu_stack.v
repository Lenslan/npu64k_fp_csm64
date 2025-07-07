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

module npuarc_alb_bpu_stack (
  input write_tos,    // write 'din' to the stack
  input write_tosp,   // write 'tosp_new' to the stack pointer
  input push_tosp,    // increment stack pointer
  input pop_tosp,     // decrement stack pointer

  input [`npuarc_BR_RS_RANGE] tosp_new,  // new value written to TOSP
  input [`npuarc_BR_BC_BTA_RANGE] tos_new,  // data input written to new top of stack
  output [`npuarc_BR_BC_BTA_RANGE] top_of_stack, // top of stack value
  output [`npuarc_BR_RS_RANGE] stack_ptr_r, // stack pointer

  input stack_freeze, // freeze the return stack, depending on BPU_CTRL
  input init,
  input clk,
  input rst_a

);

  
reg [`npuarc_BR_BC_BTA_RANGE] top_of_stack_2c;  
reg [`npuarc_BR_RS_RANGE] stack_ptr_r_2cyc;

wire [`npuarc_BR_RS_RANGE] stack_ptr_next;
wire [`npuarc_BR_RS_RANGE] stack_ptr_new;
wire [`npuarc_BR_RS_RANGE] stack_mod_val;

reg [`npuarc_BR_BC_BTA_RANGE] ff_r_2cyc[0:`npuarc_BR_RS_ENTRIES_MINUS_1];
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused carry
wire unused_carry;
// leda NTL_CON13A on

always @(posedge clk or posedge rst_a)
begin: alb_bpu_stack_PROC
if (rst_a == 1'b1)
begin
  stack_ptr_r_2cyc <= {`npuarc_BR_RS_ADDR_BITS{1'b0}};

// initialize the stack to a defined value
  ff_r_2cyc[0] <= {`npuarc_BR_BC_BTA_SIZE{1'b0}};
  ff_r_2cyc[1] <= {`npuarc_BR_BC_BTA_SIZE{1'b0}};
  ff_r_2cyc[2] <= {`npuarc_BR_BC_BTA_SIZE{1'b0}};
  ff_r_2cyc[3] <= {`npuarc_BR_BC_BTA_SIZE{1'b0}};

end
else if (init)
begin
  stack_ptr_r_2cyc <= {`npuarc_BR_RS_ADDR_BITS{1'b0}};

  ff_r_2cyc[0] <= {`npuarc_BR_BC_BTA_SIZE{1'b0}};
  ff_r_2cyc[1] <= {`npuarc_BR_BC_BTA_SIZE{1'b0}};
  ff_r_2cyc[2] <= {`npuarc_BR_BC_BTA_SIZE{1'b0}};
  ff_r_2cyc[3] <= {`npuarc_BR_BC_BTA_SIZE{1'b0}};

end
else
begin
 
  if (~stack_freeze)
  begin
    stack_ptr_r_2cyc <= stack_ptr_next;
  end

  // write TOS using the new value of stack pointer
  if (write_tos & ~stack_freeze)
  begin
    ff_r_2cyc[stack_ptr_next] <= tos_new;
  end

end
end // alb_bpu_stack_PROC

always @*
begin: alb_bpu_stack_read_PROC
  // read the top of stack at the current stack pointer
  top_of_stack_2c = ff_r_2cyc[stack_ptr_r_2cyc];
//  tos_commit = ff[tosp_commit];
end

////////////////////////////////////////////////////////////////////////////////
// determine new value of stack pointer
// on a TOSP write replace the current value with the new value
//
assign stack_ptr_new = (write_tosp) ? tosp_new :
                                      stack_ptr_r_2cyc;


////////////////////////////////////////////////////////////////////////////////
// optionally increment or decrement the stack pointer
// The value to be added to stack pointer: 1, 0 or -1
//

assign stack_mod_val = (push_tosp) ? `npuarc_BR_RS_ADDR_BITS'd1:       // +1 
                       (pop_tosp ) ? {`npuarc_BR_RS_ADDR_BITS{1'b1}}:  // -1
                                     `npuarc_BR_RS_ADDR_BITS'd0;       // 0

////////////////////////////////////////////////////////////////////////////////
// New stack pointer value after push or pop
//
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ: arithmetic calculation has a potential dont_care carry bit
// spyglass disable_block W164b
// SMD: LHS > RHS in assignment
// SJ:  arithmetic calculation has a potential dont_care carry bit
assign {unused_carry, stack_ptr_next} = stack_ptr_new + stack_mod_val;
// leda B_3208 on
// spyglass enable_block W164b
  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_PC_BITS)) u0_alb_2cyc_checker 
     (
      .data_in  (top_of_stack_2c),
      .data_out (top_of_stack),
      .clk (clk));
  npuarc_alb_2cyc_checker #(.WIDTH(`npuarc_BR_RS_ADDR_BITS)) u1_alb_2cyc_checker 
     (
      .data_in  (stack_ptr_r_2cyc),
      .data_out (stack_ptr_r),
      .clk (clk));



endmodule

