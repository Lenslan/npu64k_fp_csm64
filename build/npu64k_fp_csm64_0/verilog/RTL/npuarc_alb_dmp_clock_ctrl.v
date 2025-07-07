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
//   ALB_DMP_CLOCK_CTRL                   
//                      
//                      
//                      
//
// ===========================================================================
//
// Description:
//  This module implements the unit level clock gating for all the dmp modules.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_clock_ctrl.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_clock_ctrl (
  ////////// Interface to the SA stage //////////////////////////////////////
  //
  input                       sa_load_r,
  input                       sa_store_r,
  
  ////////// Interface to the X1 stage //////////////////////////////////////
  //
  input                       x1_load_r,
  input                       x1_store_r,
  
  ////////// Interface to the X2 stage //////////////////////////////////////
  //
  input                       x2_load_r,
  input                       x2_store_r,
  input [`npuarc_DMP_TARGET_RANGE]   dc2_target_r,
  input                       dc2_stall,
  
  ////////// Interface to the X3 stage //////////////////////////////////////
  //
  input                       x3_load_r,
  input                       x3_store_r,
  input [`npuarc_DMP_TARGET_RANGE]   dc3_target_r,
  input                       dc3_dt_miss_fast,
  ////////// Interface to the CA stage //////////////////////////////////////
  //
  input                       ca_load_r,
  input                       ca_store_r,
  input                       ca_dmp_aux_sr_op,
  input [`npuarc_DMP_TARGET_RANGE]   dc4_target_r,
  input                       dc4_dt_miss_r,
  ////////// Interface to the DMP queues /////////////////////////////////////////
  //
  input                       wq_empty,
  input                       wq_err_r,
  input                       lq_empty_r,
  input                       rb_empty,
  input                       lq_err,
  input                       dmu_empty,
  input                       dc_skid_active,
  input                       mq_rd_err,
  input                       mq_wr_err,
  input                       aux_dc_busy,
  ////////// MMU status ///////////////////////////////////////////////////
  //
  input                       dtlb_active,

input                         ecc_sbe_dmp_clr,
  ////////// Pending bus error /////////////////////////////////////////////
  //
  input                       dc4_excpn,
  
  ////// Unit-level clock-gating output control signal to clock_ctrl /////////
  //
  output reg                  dmp_dmu_unit_enable,
  output reg                  dmp_lq_unit_enable,

  output reg                  dmp_unit_enable
);

// Unit-level clock-gating control signal declarations
//
reg                     sa_dmp_wakeup;   // re-enable dmp_clk if DMP op in SA
reg                     dc1_dmp_active;  // keep dmp_clk active if DMP op in X1
reg                     dc2_dmp_active;  // keep dmp_clk active if DMP op in X2
reg                     dc3_dmp_active;  // keep dmp_clk active if DMP op in X3
reg                     dc4_dmp_active;  // keep dmp_clk active if DMP op in X3
reg                     dmp_pipe_active; 
reg                     dmp_queue_empty;
reg                     dmp_queue_error;
reg                     dmp_state_active;
reg                     dc3_dmu_miss;
reg                     dc4_dmu_miss;
reg                     dmp_dmu_cache_miss;
reg                     dc2_uncached;
reg                     dc3_ld_uncached;
reg                     dc4_ld_uncached;
////////////////////////////////////////////////////////////////////////////
//                                                                          
// Combinational logic to determine when the clock can be turned off to the 
// DMP (dmp_unit_idle) and when it must be turned on again  
// (dmp_unit_enable).                                                       
//                                                                          
////////////////////////////////////////////////////////////////////////////
always @*
begin : dmp_clk_ctrl_PROC

  sa_dmp_wakeup   = sa_load_r | sa_store_r;
  
  dc1_dmp_active  = x1_load_r | x1_store_r;
  dc2_dmp_active  = x2_load_r | x2_store_r;
  dc3_dmp_active  = x3_load_r | x3_store_r;
  dc4_dmp_active  = ca_load_r | ca_store_r;
  
  dmp_pipe_active =  dc1_dmp_active
                   | dc2_dmp_active
                   | dc3_dmp_active
                   | dc4_dmp_active
                   ;
  dmp_queue_empty =  wq_empty
                   & lq_empty_r
                   & rb_empty
                   & dmu_empty
                   ;
 
  dmp_queue_error =  wq_err_r
                   | lq_err
                   | (mq_rd_err | mq_wr_err)   
                   ;

  dmp_state_active =  dc2_stall
                    | dc_skid_active
                    | aux_dc_busy    
                    ;
  // Wait until there is no error exceptions before disabling
  //  
  dmp_unit_enable =  sa_dmp_wakeup
                   | dmp_pipe_active
                   | (~dmp_queue_empty)
                   | dmp_queue_error
                   | dmp_state_active   
                   | ca_dmp_aux_sr_op
                   | dtlb_active
                   | ecc_sbe_dmp_clr
                   | dc4_excpn
                   ;                   
  
  // Unit enable for DMU
  //                                                                          
  dc3_dmu_miss        = (x3_load_r | x3_store_r)
                      & (  (dc3_dt_miss_fast && (dc3_target_r == `npuarc_DMP_TARGET_DC))
                        )
                      ;   
  
  dc4_dmu_miss        = (ca_load_r | ca_store_r)
                      & (   (  dc4_dt_miss_r 
                             )
                          & (dc4_target_r == `npuarc_DMP_TARGET_DC)
                        )
                      ;
  
  dmp_dmu_cache_miss  = dc3_dmu_miss
                      | dc4_dmu_miss 
                      ;
                       
  dmp_dmu_unit_enable = (~dmu_empty)
                      | (mq_rd_err | mq_wr_err)   
                      | ca_dmp_aux_sr_op
                      | aux_dc_busy
                      | dmp_dmu_cache_miss
                      
                      ;
  
  // Unit enable for LQ
  //                                                                          
  dc2_uncached       = (x2_load_r | x2_store_r)
                     & (dc2_target_r != `npuarc_DMP_TARGET_DC)
                     & (dc2_target_r != `npuarc_DMP_TARGET_DCCM)
                     ;
  dc3_ld_uncached    = x3_load_r 
                     & (dc3_target_r != `npuarc_DMP_TARGET_DC)
                     & (dc3_target_r != `npuarc_DMP_TARGET_DCCM)
                     ;
  dc4_ld_uncached    = ca_load_r 
                     & (dc4_target_r != `npuarc_DMP_TARGET_DC)
                     & (dc4_target_r != `npuarc_DMP_TARGET_DCCM)
                     ;
  
  dmp_lq_unit_enable = dc2_uncached
                     | dc3_ld_uncached
                     | dc4_ld_uncached
                     | (~lq_empty_r)
                     | (~rb_empty)
                     | lq_err
                     ;
  

end


endmodule // alb_dmp_clock_ctrl
