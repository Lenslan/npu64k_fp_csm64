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
//   ALB_DMP_WQ_ERR                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module handles bus errors.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_wq_err.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_wq_err (
  ////////// General input signals ///////////////////////////////////////////
  //
  input                         clk,                 // clock
  input                         rst_a,               // reset

  ////////// Mem IBP write response ///////////////////////////////////////////
  //
  input                         wq_mem_err_wr,
  input [`npuarc_PADDR_RANGE]          wq_mem_addr,  
  input                         wq_mem_user_mode,
  input                         wq_mem_debug,






  ////////// Error reporting///////////////////////////////////////////////
  //
  output reg                    wq_err_r,
  output reg                    wq_err_user_mode_r,
  output reg  [`npuarc_PADDR_RANGE]    wq_err_addr_r,
  input                         wq_err_ack
);


reg                wq_err_cg0;     
reg                wq_err_nxt;     
reg [`npuarc_PADDR_RANGE] wq_err_addr_nxt;     
reg                wq_err_user_mode_nxt;

reg                wq_err_state_nxt;    
reg                wq_err_state_r;    

reg                wq_mem_bus_err;
reg                wq_per_bus_err;
reg                wq_per2_bus_err;
reg                wq_iccm_bus_err;
reg                wq_vec_mem_bus_err;
reg                wq_cu_bus_err;

//////////////////////////////////////////////////////////////////////////////
// Qualify errors
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : wq_bus_err_PROC
  wq_mem_bus_err =   1'b0
                   | (wq_mem_err_wr & (~wq_mem_debug))
                   ;
  
  wq_per_bus_err =   1'b0
                   ;
  wq_per2_bus_err =   1'b0                
                   ;
  
  wq_iccm_bus_err =   1'b0
                   ;
  
  wq_vec_mem_bus_err =   1'b0
                   ;

  wq_cu_bus_err   =  1'b0
                   ;  
                   
end

//////////////////////////////////////////////////////////////////////////////
//  FSM for error reporting
//
//////////////////////////////////////////////////////////////////////////////

parameter WQ_ERR_DEFAULT     = 1'b0;
parameter WQ_ERR_WAIT_ACK    = 1'b1;

always @*
begin : wq_err_state_fsm_PROC

  // Default values
  //
  wq_err_cg0             = 1'b0;
  wq_err_nxt             = wq_err_r;
  wq_err_addr_nxt        = wq_err_addr_r;
  wq_err_user_mode_nxt   = wq_err_user_mode_r;
  wq_err_state_nxt       = wq_err_state_r;
  
  case (wq_err_state_r)
  WQ_ERR_DEFAULT:
  begin
    
    casez ({wq_mem_bus_err,
            wq_per_bus_err,
            wq_per2_bus_err,
            wq_iccm_bus_err,
            wq_vec_mem_bus_err,
            wq_cu_bus_err})
    
    6'b1?????:
    begin
      // Memory target
      //
      wq_err_cg0           = 1'b1;
      wq_err_nxt           = 1'b1;
      wq_err_addr_nxt      = wq_mem_addr;    
      wq_err_user_mode_nxt = wq_mem_user_mode;
      wq_err_state_nxt     = WQ_ERR_WAIT_ACK;
    end
    
    

    
    
    default:
    begin
      wq_err_cg0            = 1'b0;
      wq_err_nxt            = wq_err_r;
      wq_err_addr_nxt       = wq_err_addr_r;
      wq_err_user_mode_nxt  = wq_err_user_mode_r;
      wq_err_state_nxt      = wq_err_state_r;
    end
    endcase            
  end
  


  default: // WQ_ERR_WAIT_ACK:
  begin
    wq_err_cg0             = 1'b1;
    
    if (wq_err_ack)
    begin
      wq_err_nxt           = 1'b0;
      wq_err_state_nxt     = WQ_ERR_DEFAULT;
    end
  end
  endcase
end

/////////////////////////////////////////////////////////////////////////////
// Synchronous processess
//
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : wq_err_fsm_reg_PROC
  if (rst_a == 1'b1)
  begin
    wq_err_r       <= 1'b0;
    wq_err_state_r <= WQ_ERR_DEFAULT;
  end
  else
  begin
    if (wq_err_cg0 == 1'b1)
    begin
      wq_err_r       <= wq_err_nxt;
      wq_err_state_r <= wq_err_state_nxt;
    end
  end
end

// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin : wq_err_user_mode_reg_PROC
  if (wq_err_cg0 == 1'b1)
  begin
    wq_err_user_mode_r  <= wq_err_user_mode_nxt;
    wq_err_addr_r       <= wq_err_addr_nxt;
  end
end
// leda NTL_RST03 on
// leda S_1C_R on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01


endmodule // alb_dmp_wq_err 
