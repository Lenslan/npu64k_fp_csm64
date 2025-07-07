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
//                    
//   ALB_DMP_GRAD                 
//                    
//                    
//
// ===========================================================================
//
// Description:
//  This module is responsible for LD graduation.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_grad.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_grad (
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some inputs are not used in certain configurations
  ////////// General input signals //////////////////////////////////////////
  //
  input                        clk,             // clock
  input                        rst_a,           // reset

  input                        db_active_r,     // debug inserted instruction
  input                        x3_db_exception, // X3 signal

  ////////// Interface to the X3 stage /////////////////////////////////////
  //
  input                       x3_load_r,        // X3 load  
  input                       x3_pref_r,        // X3 pref   
  input                       x3_store_r,       // X3 store
  input                       x3_locked_r,      // X3 LLOCK/SCOND
  input                       x3_pass,          // X3 passing on instruction
  input                       dc3_fwd_req,      // DC3 uncached load to st fwd  
  input [`npuarc_DMP_TARGET_RANGE]   dc3_target_r,     // DC3 target  
  
  ////////// Interface to the CA stage /////////////////////////////////////
  //
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                       ca_load_r,              // CA load
  input                       ca_pref_r,              // CA pref
// spyglass enable_block W240
  input                       ca_enable,              // CA accepts new instruction
  input                       dc4_scond_go,           // CA scond shall proceed
  input                       dc4_dt_miss_r,          // DC4 cache miss  
  input                       dc4_mq_replay_r,        // DC4 MQ replay 
  input                       dc4_lsmq_replay_r,      // DC4 LSMQ replay 

  ////////// Graduation Interface //////////////////////////////////////////
  //
  output reg                  dc4_grad_req       // DC4 graduation
// leda NTL_CON13C on
);


// Local declarations
// 
reg  dc3_grad_prel;
reg  dc3_grad;

reg  dc4_grad_prel_cg0;
reg  dc4_grad_prel_nxt;
reg  dc4_grad_prel_r;

//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic defining  dc3 state signals            
//                                                                        
//////////////////////////////////////////////////////////////////////////
always @*
begin : dc3_grad_PROC
  // The following load target need to request graduation in the next cycle,
  // provided there is no store to load forwarding
  //
  dc3_grad_prel  =  (dc3_target_r == `npuarc_DMP_TARGET_MEM)
                  ; 

  // Qualify dc3 graduation request. Uncached EX and SCOND always graduate
  //
  dc3_grad       =  dc3_grad_prel
                  & (~dc3_fwd_req);
  
end

reg dc4_scond_uncached_cg0;
reg dc4_scond_uncached_r;
reg dc4_scond_uncached_nxt;
//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic defining  dc3 state signals            
//                                                                        
//////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_scond_uncached_PROC
  dc4_scond_uncached_cg0  = (x3_load_r | x3_store_r) & x3_pass;
  
  dc4_scond_uncached_nxt  =  x3_store_r 
                          &  x3_locked_r 
                          & (  (dc3_target_r == `npuarc_DMP_TARGET_MEM)
                             )
                         ;
end
//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic defining  dc4 next state signals            
//                                                                        
//////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_grad_prel_nxt_PROC
  // Clock gate enable
  //
  dc4_grad_prel_cg0 = ca_enable;
  
  // Uncached loads always graduate
  //
  dc4_grad_prel_nxt =  x3_load_r 
                     & ( (~x3_pref_r) | db_active_r)
                     & (~x3_db_exception)
                     & x3_pass 
                     & dc3_grad; 
end

reg dc4_ld_target_dc_nxt;
reg dc4_ld_target_dc_r;
//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic defining  dc4 next state signals            
//                                                                        
//////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_ld_target_dc_nxt_PROC

  dc4_ld_target_dc_nxt = x3_load_r & x3_pass & (dc3_target_r == `npuarc_DMP_TARGET_DC);
end
reg dc4_dc_grad_req;
reg dc4_scond_grad_req;
//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic defining  dc4 grad          
//                                                                        
//////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_grad_req_PROC
  // Cache misses graduate when we are not replaying
  //
  dc4_dc_grad_req =    (ca_load_r          & (~ca_pref_r))
                    &  (dc4_ld_target_dc_r & dc4_dt_miss_r)
                    & (~(dc4_mq_replay_r    | dc4_lsmq_replay_r))
                    ;
  
  // Graduate uncached SCOND that got a go and it is either uncached or
  // there it hits on a shared line (SMP)
  //
  dc4_scond_grad_req = (     dc4_scond_go 
                        & (  dc4_scond_uncached_r
                          )
                        )
                        ;

  // DC4 graduation request
  //
  dc4_grad_req  =   dc4_grad_prel_r 
                 |  dc4_dc_grad_req
                 |  dc4_scond_grad_req
                 ; 
end

//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
// 
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : dc4_grad_prel_req_PROC
  if (rst_a == 1'b1)
  begin
    dc4_grad_prel_r   <= 1'b0;
  end
  else
  begin
    if (dc4_grad_prel_cg0)
    begin
      dc4_grad_prel_r <= dc4_grad_prel_nxt;
    end
  end
end
always @(posedge clk or posedge rst_a)
begin : dc4_ld_target_dc_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_ld_target_dc_r <= 1'b0;
  end
  else
  begin
    if (dc4_grad_prel_cg0)
    begin
      dc4_ld_target_dc_r <= dc4_ld_target_dc_nxt;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_scond_uncached_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_scond_uncached_r  <= 1'b0;
  end
  else
  begin
    if (dc4_scond_uncached_cg0)
    begin
      dc4_scond_uncached_r <= dc4_scond_uncached_nxt;
    end  
  end
end

endmodule // alb_dmp_grad
