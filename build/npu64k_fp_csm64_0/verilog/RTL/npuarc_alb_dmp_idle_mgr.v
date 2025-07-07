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
//   ALB_DMP_IDLE_MGR                   
//                      
//                      
//                      
//
// ===========================================================================
//
// Description:
//  This module indicates the dmp idle information.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_idle_mgr.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_idle_mgr (
  ////////// General input signals ///////////////////////////////////////////
  //
  input                        clk,            // clock
  input                        rst_a,          // reset
  
  ////////// Interface to the DMP sub-modules /////////////////////////////////
  //
  input                        wq_empty,
  input                        lq_empty,
  input                        rb_empty,

  input                        dmu_empty,
  input                        dmu_wr_pending,
  input                        aux_dc_busy,
  ////////// Output status ///////////////////////////////////////////////
  //
  output reg                   dmp_idle_r,  
  output reg                   dmp_idle1_r,  // DMP idle (ignore excpn)
  output                       dmp_queue_empty,
  output reg                   dmp_wr_pending_r,
  output reg                   dmp_aux_pending_r  
);

// Local declarations
// 
reg       dmp_idle_nxt;
reg       dmp_idle1_nxt;
reg       dmp_wr_pending_nxt;
reg       dmp_aux_pending_nxt;
reg       dmp_queue_empty_nxt;

wire      dmp_no_pend_trans;

//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic          
//                                                                        
//////////////////////////////////////////////////////////////////////////
// spyglass disable_block Ac_conv01
// SMD:  synchronizers converge
assign  dmp_no_pend_trans =  wq_empty
                 & lq_empty
                 & dmu_empty
                 & (~aux_dc_busy)
                  ;
always @*
begin : dmp_idle_nxt_PROC
  dmp_idle_nxt =    dmp_no_pend_trans
                 & rb_empty
                 ;

  dmp_idle1_nxt =    dmp_no_pend_trans
                 & rb_empty
                 ;
  dmp_queue_empty_nxt =  dmp_no_pend_trans
                   ;
// spyglass enable_block Ac_conv01               
end

always @*
begin : dmp_dmb_nxt_PROC
  // Post-commit memory write
  //
  dmp_wr_pending_nxt =    (~wq_empty)
                        | (dmu_wr_pending)
                        ;               
  // Post-commit cache control operation
  //
  dmp_aux_pending_nxt =   1'b0
                        | (aux_dc_busy == 1'b1)
                        ;               
end
//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
// 
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : dmp_idle_reg_PROC
  if (rst_a == 1'b1)
  begin
    dmp_idle_r        <= 1'b1;
    dmp_idle1_r       <= 1'b1;
    dmp_wr_pending_r  <= 1'b0;
    dmp_aux_pending_r <= 1'b0;
  end
  else
  begin
    dmp_idle_r        <= dmp_idle_nxt;
    dmp_idle1_r       <= dmp_idle1_nxt;
    dmp_wr_pending_r  <= dmp_wr_pending_nxt;
    dmp_aux_pending_r <= dmp_aux_pending_nxt;
  end
end

assign dmp_queue_empty = dmp_queue_empty_nxt;

endmodule // alb_dmp_idle_mgr
