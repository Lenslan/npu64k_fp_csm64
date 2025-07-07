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
//   ALB_DMP_WQ_PORT                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Write Queue interface to ICCM/MEM/PER.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_wq_port.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_wq_port (
  ////////// General input signals ///////////////////////////////////////////
  //
  input                          clk,               // clock
  input                          rst_a,             // reset


  ////////// Interface with FIFO ///////////////////////////////////////////
  //
  input                          wq_valid,         // top of FIFO
  input                          wq_target,        // target
  input                          wq_bufferable,    // posted
  input                          wq_unaligned,     // burst transfer
  input [`npuarc_DOUBLE_BE_RANGE]       wq_mask_bank1,    // mask for second transfer
  input [`npuarc_DOUBLE_RANGE]          wq_data_bank1,    // data for second transfer
  input                          wq_empty,
  
  ////////// Command handhake ///////////////////////////////////////////
  //
  output reg                     wq_cmd_valid,     // IBP
  output reg                     wq_cmd_cache,     // IBP - only bufferable bit
  input                          wq_cmd_accept,    // IBP
  input [`npuarc_DOUBLE_BE_RANGE]       wq_wr_mask_prel,  // mask for first xfer
  input [`npuarc_DOUBLE_RANGE]          wq_wr_data_prel,  // data for first xfer 
  output reg                     wq_wr_valid,      // IBP
  output reg                     wq_wr_last,       // IBP
  output reg [`npuarc_DOUBLE_BE_RANGE]  wq_wr_mask,       // IBP
  output reg [`npuarc_DOUBLE_RANGE]     wq_wr_data,       // IBP
  
  input                          wq_wr_accept,     // IBP
  
  ////////// Popping  WQ  FIFO ///////////////////////////////////////////
  //
  output reg                     wq_read
);

// Local Declarations
//
reg         wq_sec_wr_r;
reg         wq_sec_wr_nxt;

reg         wq_state_cg0;
reg [1:0]   wq_state_r;
reg [1:0]   wq_state_nxt;


parameter WQ_DEFAULT        = 2'b00;
parameter WQ_SECOND_WRITE   = 2'b01;
parameter WQ_WAIT_WR_ACCEPT = 2'b10;

//////////////////////////////////////////////////////////////////////////////
// FSM 
// 
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_port_fsm_PROC

  // Default
  //
  wq_cmd_valid  = wq_valid  & wq_target;
  wq_cmd_cache  = wq_bufferable;
  wq_wr_valid   = wq_valid  & wq_target;
  wq_wr_last    = !wq_unaligned;
  wq_wr_mask    = wq_wr_mask_prel;
  wq_wr_data    = wq_wr_data_prel;

  wq_read       = 1'b0;
  
  wq_sec_wr_nxt = wq_sec_wr_r;
  wq_state_cg0  = !wq_empty;
  
  wq_state_nxt  = wq_state_r;
  
  case (wq_state_r)  
  WQ_DEFAULT:
  begin
    if (wq_wr_valid)
    begin
      // We can not have a wr_accept before the cmd_accept
      // 
      wq_sec_wr_nxt = wq_unaligned;
      
      if (wq_wr_accept)
      begin
        // This data tranfer is completed
        //
        wq_read      = ~wq_unaligned;
        
        if (wq_unaligned)
        begin
          // We are done with the first write. Lets handle the second write
          //
          wq_state_nxt  = WQ_SECOND_WRITE;
        end
      end
      else if (wq_cmd_accept)
      begin
        // Lets make sure the command is transferred before we wait for the
        // wr_accept
        //
        wq_state_nxt    = WQ_WAIT_WR_ACCEPT;
      end
    end
  end
  
  WQ_SECOND_WRITE:
  begin
    wq_cmd_valid    = 1'b0;
    wq_wr_last      = 1'b1;

    // Unaligned accesses always crom from bank even to bank odd.
    //
    wq_wr_mask      = wq_mask_bank1;     
    wq_wr_data      = wq_data_bank1;
    
    if (wq_wr_accept)
    begin
      wq_sec_wr_nxt  = 1'b0;
      wq_read        = 1'b1;
      wq_state_nxt   = WQ_DEFAULT;
    end
  end
  
  default: // WQ_WAIT_WR_ACCEPT:
  begin
    // Do not initiate another command transfer before the data for the previous
    // command is accepted
    //
    wq_cmd_valid     = 1'b0;
    wq_wr_last       = !wq_sec_wr_r;
    
    casez ({wq_wr_accept, wq_sec_wr_r})
    2'b10:
    begin
      // We are done
      //
      wq_sec_wr_nxt  = 1'b0;
      wq_read        = 1'b1;
      wq_state_nxt   = WQ_DEFAULT;
    end
    
    2'b11:
    begin
      // The first write transfer is complete. Need to perform the second one
      //
      wq_state_nxt = WQ_SECOND_WRITE;
    end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept    
    default:
      ;
    endcase
  end
  endcase
end
// spyglass enable_block W193
//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
// 
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : wq_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_state_r    <= WQ_DEFAULT;
    wq_sec_wr_r   <= 1'b0;
  end
  else
  begin
    if (wq_state_cg0)
    begin
      wq_state_r  <= wq_state_nxt;
      wq_sec_wr_r <= wq_sec_wr_nxt;
    end
  end
end


endmodule // alb_dmp_wq_port
