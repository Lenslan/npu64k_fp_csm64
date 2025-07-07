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
//   ####    ####   #####   ######
//  #    #  #    #  #    #  #
//  #       #    #  #    #  #####
//  #       #    #  #####   #
//  #    #  #    #  #   #   #
//   ####    ####   #    #  ###### #######
// 
// 
//      #####   ######   ####    #   #  #    #   ####            #    #    #
//      #    #  #       #         # #   ##   #  #    #           #    ##   #
//      #    #  #####    ####      #    # #  #  #                #    # #  #
//      #####   #            #     #    #  # #  #                #    #  # #
//      #   #   #       #    #     #    #   ##  #    #           #    #   ##
//      #    #  ######   ####      #    #    #   ####  #######   #    #    #
//
// ===========================================================================
//
// Description:
//
//  This module synchronizes all asynchronous interrupt lines to the CPU
//  clock. This is to reduce the possibility of metastability when
//  asynchronous inputs are sampled on the rising edge of the CPU clock.
//  Effectively a full clock cycle is provided to allow any metastability
//  to settle out of the circuit before the synchronized signals are used.
//
//  This .vpp source file may be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o core_resync_in.vpp
//
// ==========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

`include "const.def"

module npuarc_alb_resync_in (
  ////////// General input signals /////////////////////////////////////////
  //
  input                       clk,            // Processor clock
  input                       rst_a,          // Async reset

  ////////// Asynchronous input signals ////////////////////////////////////
  //
  input                       arc_halt_req_a,   // Async. halt req
  input                       arc_run_req_a,    // Async. run  req
  input                       presetdbgn,
  input                       irq_sync_req_a,   // Async. IRQ resync req 
  input                       arc_event_a,      // Async. event signal
  input                       dbg_cache_rst_disable, // cache behavior at reset
  input                       dccm_dmi_priority,     // DCCM DMI priority
  
  ////////// Synchronous output signals ////////////////////////////////////
  //
  output                      cpu_resync_clk_enable,

  output                      irq_sync_req,    // Synchronized resync req 
  output  reg                 arc_halt_req,    // Synchronized halt req
  output  reg                 arc_run_req,     // Synchronized run req
  output                      dbg_cache_rst_disable_r, 
  output                      dccm_dmi_priority_r,
  output                      arc_event_r      // synchronized event signal
);

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronizing flip-flops                                               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

wire                          synch_arc_halt_req_2_r;
wire                          synch_arc_run_req_2_r;
wire                          synch_irq_sync_req_2_r;

wire                          sync_arc_event_2_r;
reg                          sync_dbg_cache_rst_disable_1_r;
reg                          sync_dbg_cache_rst_disable_2_r;
reg                          sync_dccm_dmi_priority_1_r;     
wire                         sync_dccm_dmi_priority_2_r;     


// Instantiate CDC synchronizer wrappers so that the synthesis flow can 
// replace it with the proper synchronizer cell of the target library.
//

// spyglass disable_block STARC05-1.4.3.4
// SMD: clock signal used as non-clock
npuarc_cdc_sync u_cdc_sync_0 (
  .clk        (clk),
  .rst_a      (rst_a),
  .din        (arc_halt_req_a),
  .dout       (synch_arc_halt_req_2_r)
);

npuarc_cdc_sync u_cdc_sync_1 (
  .clk        (clk),
  .rst_a      (rst_a),
  .din        (arc_run_req_a),
  .dout       (synch_arc_run_req_2_r)
);

npuarc_cdc_sync u_cdc_sync_3 (
  .clk        (clk),
  .rst_a      (rst_a),
  .din        (irq_sync_req_a),
  .dout       (synch_irq_sync_req_2_r)
);

npuarc_cdc_sync u_cdc_sync_4 (
  .clk        (clk),
  .rst_a      (rst_a),
  .din        (arc_event_a),
  .dout       (sync_arc_event_2_r)
);

// spyglass enable_block STARC05-1.4.3.4

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Output drives                                                          //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(*)
begin: halt_run_out_PROC
  arc_halt_req = synch_arc_halt_req_2_r;
  arc_run_req  = synch_arc_run_req_2_r;
end


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous process                                                        
//                                                                        //
////////////////////////////////////////////////////////////////////////////
// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  This signal should not have a reset. It is used to control the cache behavior at reset
always @(posedge clk)
begin : dbg_cache_sync_PROC
  sync_dbg_cache_rst_disable_1_r   <= dbg_cache_rst_disable;
  sync_dbg_cache_rst_disable_2_r   <= sync_dbg_cache_rst_disable_1_r;
end 
// leda S_1C_R on
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01


npuarc_cdc_sync u_cdc_sync_9 (
  .clk        (clk),
  .rst_a      (rst_a),
  .din        (dccm_dmi_priority),
  .dout       (sync_dccm_dmi_priority_2_r)
);

 
assign irq_sync_req = synch_irq_sync_req_2_r;
assign arc_event_r = sync_arc_event_2_r ;
assign dbg_cache_rst_disable_r = sync_dbg_cache_rst_disable_2_r;
assign dccm_dmi_priority_r     = sync_dccm_dmi_priority_2_r;

// collect raw async inputs to request a level 1 clock
//
// spyglass disable_block Ac_conv02
// SMD: Syncs converging
// SJ:  Expected and causes no issues
assign cpu_resync_clk_enable = arc_halt_req_a    // Async. halt req
                            || arc_run_req_a     // Async. run  req
                            || (~presetdbgn)
                            || irq_sync_req_a    // Async. IRQ resync req 
                            || arc_event_a       // Async. event signal
                            ;
// spyglass enable_block Ac_conv02

endmodule // core_resync_in
