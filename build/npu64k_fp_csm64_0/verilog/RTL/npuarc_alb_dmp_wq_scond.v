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
//   ALB_DMP_WQ_SCOND                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
// This module is responsible for the retirement of Store Conditional (SCOND) 
// instructions. It keeps track of SCOND instructions that graduated and 
// request the result bus when the SCOND is ready to retire. 
//  
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_wq.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_wq_scond (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                         clk,           // clock
  input                         rst_a,         // reset
  
  ////////// Interface with CA: Entry  ///////////////////////////////////////
  //
  input                         ca_store_r,   // CA store  
  input                         ca_pass,      // CA pass
  input                         ca_locked_r,  // CA SCOND
  input [`npuarc_GRAD_TAG_RANGE]       ca_grad_tag,  // CA grad tag     

  input                         dc4_grad_req, // DC4 DMP graduating instruction
  

  ////////// Interface to external memory //////////////////////////////////////
  //
  input                         wq_mem_scond,        // SCOND instruction
  input                         wq_mem_wr_done,      // Write has finished
  input                         wq_mem_wr_excl_done, // SCOND success
  input                         wq_mem_err_wr,       // Bus error


  ////////// Interface to the result bus //////////////////////////////////////
  //
  output reg                    wq_scond_rb_req,  // Request retirement
  output reg [`npuarc_GRAD_TAG_RANGE]  wq_scond_rb_tag,  // Retiremnt tag
  output reg                    wq_scond_rb_flag, // Retireemt data  (z flag)
  
  input                         wq_scond_rb_ack   // Retirement ack
  
);

// Local Declarations
//  
reg                   wq_scond_valid_r;
reg                   wq_scond_success_r;
reg                   wq_scond_finished_r;
reg [`npuarc_GRAD_TAG_RANGE] wq_scond_tag_r;

reg                   wq_scond_valid_nxt;
reg                   wq_scond_success_nxt;
reg                   wq_scond_finished_nxt;
reg [`npuarc_GRAD_TAG_RANGE] wq_scond_tag_nxt;

reg                   wq_scond_write;
reg                   wq_scond_update;
reg                   wq_scond_status;
reg                   wq_scond_retire;

reg                   wq_scond_cg0;
reg                   wq_scond_state_r;
reg                   wq_scond_state_nxt;
  
reg                   wq_scond_uncached;
reg                   wq_scond_wr_done;
reg                   wq_scond_wr_excl_done;

//////////////////////////////////////////////////////////////////////////////
// Entry, update and removal
// 
////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_scond_PROC
  // Write the SCOND buffer when we graduate a SCOND instruction
  //
  wq_scond_write =  ca_store_r
                  & ca_locked_r
                  & dc4_grad_req
                  & ca_pass;

  // An uncached SCOND instruction targets mem or per 
  //
  wq_scond_uncached =   1'b0
                      | wq_mem_scond
                      ;
  
  // There are no multiple outstanding SCOND instructions: WAW hazard on Z flag
  //
  wq_scond_wr_done  =   1'b0
                      | (  wq_mem_scond 
                         & (wq_mem_wr_done | wq_mem_wr_excl_done | wq_mem_err_wr))
                      ;
  
  // There are no multiple outstanding SCOND instructions
  //
  wq_scond_wr_excl_done  =   1'b0
                      | (wq_mem_scond & wq_mem_wr_excl_done)
                      ;
  // Figure out the status of the scond when it completes
  //
  wq_scond_update = (   wq_scond_uncached 
                      & wq_scond_wr_done)
                  ;
  
  wq_scond_status = (   wq_scond_uncached 
                      & wq_scond_wr_excl_done) 
                  ;
  
  // Remove entry when upon retirement 
  //
  wq_scond_retire = wq_scond_rb_req & wq_scond_rb_ack;
end


//////////////////////////////////////////////////////////////////////////////
// Asynchronous process to request the result bus
// 
////////////////////////////////////////////////////////////////////////////
parameter WQ_SCOND_DEFAULT  = 1'b0;
parameter WQ_SCOND_WAIT_ACK = 1'b1;

always @*
begin : wq_scond_fsm_PROC
  
  wq_scond_rb_req    = 1'b0;                
  wq_scond_rb_tag    = wq_scond_tag_r;      
  wq_scond_rb_flag   = wq_scond_success_r;  
  
  wq_scond_cg0       = wq_scond_valid_r;
  wq_scond_state_nxt = wq_scond_state_r;
  
  case (wq_scond_state_r)
  WQ_SCOND_DEFAULT:
  begin
    if (  wq_scond_valid_r 
        & wq_scond_finished_r)
    begin
      wq_scond_rb_req = 1'b1;
      
      if (wq_scond_rb_ack == 1'b0)
      begin
        // Didnt get result bus
        //
        wq_scond_state_nxt = WQ_SCOND_WAIT_ACK;
      end
    end    
  end
  
  default: // WQ_SCOND_WAIT_ACK
  begin
    wq_scond_rb_req = 1'b1;
    
    if (wq_scond_rb_ack)
    begin
      wq_scond_state_nxt = WQ_SCOND_DEFAULT;
    end
  end
  endcase
end


always @*
begin : wq_scond_nxt_PROC
  // 
  // Default value
  
  wq_scond_valid_nxt    = wq_scond_valid_r;
  wq_scond_success_nxt  = wq_scond_success_r;
  wq_scond_finished_nxt = wq_scond_finished_r;
  wq_scond_tag_nxt      = wq_scond_tag_r; 
  
  if (wq_scond_write)
  begin
    wq_scond_valid_nxt   = 1'b1;
    wq_scond_success_nxt = 1'b1;  
    wq_scond_finished_nxt= 1'b0;
    wq_scond_tag_nxt     = ca_grad_tag;
  end
  
  // Update entry
  //
  if (wq_scond_update)
  begin
    wq_scond_finished_nxt = 1'b1;
    wq_scond_success_nxt  = wq_scond_status;  
  end
  
  // Remove entry
  //
  if (wq_scond_retire)
  begin
    wq_scond_valid_nxt   = 1'b0;
  end
end

//////////////////////////////////////////////////////////////////////////////
// Synchronous process 
//
//////////////////////////////////////////////////////////////////////////////
// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  conflict covered by assertions
//
// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
//
// spyglass disable_block STARC05-2.2.3.3
// SMD: Flipflop value assigned more than once over same signal in always construct
// SJ:  Conflit covered by assertions
//
always @(posedge clk or posedge rst_a)
begin : wq_scond_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_scond_valid_r    <= 1'b0;
    wq_scond_success_r  <= 1'b0;  
    wq_scond_finished_r <= 1'b0;
    wq_scond_tag_r      <= {`npuarc_GRAD_TAG_BITS{1'b0}};
  end
  else
  begin
    wq_scond_valid_r    <= wq_scond_valid_nxt;
    wq_scond_success_r  <= wq_scond_success_nxt;  
    wq_scond_finished_r <= wq_scond_finished_nxt;
    wq_scond_tag_r      <= wq_scond_tag_nxt;
  end
end
//leda NTL_RST03 on
//leda FM_1_7 on
// spyglass enable_block STARC05-2.2.3.3

always @(posedge clk or posedge rst_a)
begin : wq_scond_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_scond_state_r   <= WQ_SCOND_DEFAULT;
  end
  else
  begin
    if (wq_scond_cg0)
    begin
      wq_scond_state_r <= wq_scond_state_nxt;
    end
  end
end

endmodule // alb_dmp_wq_scond 
