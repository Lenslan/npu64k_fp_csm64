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
//                     
//                     
//   ALB_DMP_LQ_CMD_TRACK                 
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module tracks the number of pending commands on a IBP channel
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_lq_cmd_track.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_lq_cmd_track 
  #(
    parameter D_W = 3
   )
   (
  ////////// General input signals ///////////////////////////////////////////
  //
  input                    clk,               // clock
  input                    rst_a,             // reset

  ////////// Command push/pop //////////////////////////////////////////////
  //
  input                    cmd_push, 
  input                    cmd_pop,  
  
  /////////// Outstanding commands //////////////////////////////////////////
  //
  output reg [D_W-1:0]     cmd_pending_r
);

// Local Declarations
//
reg                   cmd_pending_cg0;
reg [D_W-1:0]         cmd_pending_nxt;
reg                   cmd_pending_incr;
reg                   cmd_pending_decr;


// leda BTTF_D002 off
// leda B_3200 off
// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ:  One bit incrementor. Never overflows by design

//////////////////////////////////////////////////////////////////////////////
// @ Tracks pending commands
//
////////////////////////////////////////////////////////////////////////////// 
always @*
begin : cmd_pending_PROC
  // Clock gate
  //
  cmd_pending_cg0  = cmd_push | cmd_pop;
  
  // Command sent out on the bus: increment
  //
  cmd_pending_incr = cmd_push;
  
  // Load retired: decrement
  //
  cmd_pending_decr = cmd_pop;
  
  case ({cmd_pending_incr, cmd_pending_decr})
  2'b10:   cmd_pending_nxt = cmd_pending_r + 1'b1;
  2'b01:   cmd_pending_nxt = cmd_pending_r - 1'b1;
  default: cmd_pending_nxt = cmd_pending_r;
  endcase
end
// leda BTTF_D002 on
// leda B_3200 on
// leda W484 on

//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
//
////////////////////////////////////////////////////////////////////////////// 
always @(posedge clk or posedge rst_a)
begin : cmd_pending_reg_PROC
  if (rst_a == 1'b1)
  begin
    cmd_pending_r       <= {D_W{1'b0}};
  end
  else
  begin
    if (cmd_pending_cg0 == 1'b1)
    begin
      cmd_pending_r    <= cmd_pending_nxt;
    end  
  end  
end

endmodule // alb_dmp_lq_cmd_track
