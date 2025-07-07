// Library ARCv2CC-3.2.999999999
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
//   ####   #       ####    ####   #    #         ####    #####  #####   #
//  #    #  #      #    #  #    #  #   #         #    #     #    #    #  #
//  #       #      #    #  #       ####          #          #    #    #  #
//  #       #      #    #  #       #  #          #          #    #####   #
//  #    #  #      #    #  #    #  #   #         #    #     #    #   #   #
//   ####   #####   ####    ####   #    # #####   ####      #    #    #  #####
//
// ===========================================================================
//
// @f:clock_ctrl
//
// Description:
// @p
//  The |clock_ctrl| module instantiates the architectural clock gates, which
//  gates off clocks as necessary, when in sleep/halt mode
// @e
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o cc_clock_ctrl.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_cc_exported_defines.v"
`include "npuarc_cc_defines.v"








// spyglass disable_block STARC05-1.3.1.3
// SMD: Asynchronous preset signal used as non-preset/synchronous-preset
// SJ: this a synchronizer to avoid metastability and false path!

module npuarc_cc_clock_ctrl (


  output                      cc_misc_l1_clk,


  input                       cc_aux_l1_clk_enable,
  output                      cc_aux_accept_en,
  //////////  gated clock generation for pd power domains //////////////////////////////
  //
  //
  output                      cc_pd1_clk,




  ////////// BIU Level-1 clock gate interface ///////////////////////////////
  //
  input                       biu_l1_clk_enable,
  output                      biu_accept_en,
  output                      biu_l1_clk,



  ////////// Core Level-1 clock gate interface ///////////////////////////////
  //
  input                       l1_clk_enable,
  output                      l1_accept_en,
  output                      l1_clk,

  ////////// Core Level-1 clock gate interface ///////////////////////////////
  //
  input                       nmi_restart_r,
  input                       clk,               // Ungated clock
  input                       rst_a              // Asynchronous reset

);







reg                     biu_l1_clk_enable_resync_r;
wire                    biu_l1_clk_ctrl;
wire                    biu_l1_clk_accept;
reg                     biu_l1_clk_accept_r;
reg                     biu_l1_clk_ctrl_r0;
reg                     biu_l1_clk_ctrl_r1;
wire                    biu_l1_clkgate_en;


reg                     cc_aux_l1_clk_enable_resync_r;
wire                    cc_aux_accept;
reg                     cc_aux_accept_r;

wire                    cc_misc_l1_clk_ctrl;
reg                     cc_misc_l1_clk_ctrl_r0;
reg                     cc_misc_l1_clk_ctrl_r1;
wire                    cc_misc_l1_clkgate_en;








//1 flip-flop sync from timing perspective
always @(posedge clk or posedge rst_a)
begin : cc_aux_l1_clk_enable_resync_r_PROC
  if (rst_a == 1'b1) begin
    cc_aux_l1_clk_enable_resync_r <= 1'b1;
  end 
  else if(nmi_restart_r == 1'b1) begin
    cc_aux_l1_clk_enable_resync_r <= 1'b1;
  end 
  else begin
    cc_aux_l1_clk_enable_resync_r <= cc_aux_l1_clk_enable;
  end
end

assign cc_aux_accept =     1'b1
                          &  cc_aux_l1_clk_enable_resync_r
                          ;

always @(posedge clk or posedge rst_a)
begin : cc_aux_accept_r_PROC
  if (rst_a == 1'b1) begin
    cc_aux_accept_r <= 1'b1;
  end 
  else if(nmi_restart_r == 1'b1) begin
    cc_aux_accept_r <= 1'b1;
  end 
  else begin
    cc_aux_accept_r <= cc_aux_accept;
  end
end

assign cc_aux_accept_en = cc_aux_accept_r;


assign cc_misc_l1_clk_ctrl = 1'b1
                          & (1'b0
                          | cc_aux_l1_clk_enable_resync_r
                          | biu_l1_clk_enable_resync_r // for vccm_arb misc_clk
                          )
                          ;

//2 flip-flop clock control signal
always @(posedge clk or posedge rst_a)
begin : cc_misc_l1_clk_ctrl_r_PROC
  if (rst_a == 1'b1) begin
    cc_misc_l1_clk_ctrl_r0 <= 1'b1;
    cc_misc_l1_clk_ctrl_r1 <= 1'b1;
  end 
  else if(nmi_restart_r == 1'b1) begin
    cc_misc_l1_clk_ctrl_r0 <= 1'b1;
    cc_misc_l1_clk_ctrl_r1 <= 1'b1;
  end 
  else begin
    cc_misc_l1_clk_ctrl_r0 <= cc_misc_l1_clk_ctrl;
    cc_misc_l1_clk_ctrl_r1 <= cc_misc_l1_clk_ctrl_r0;
  end
end

assign cc_misc_l1_clkgate_en = cc_misc_l1_clk_ctrl_r0 | cc_misc_l1_clk_ctrl_r1;


//1 flip-flop sync from timing perspective
always @(posedge clk or posedge rst_a)
begin : biu_l1_clk_enable_resync_r_PROC
  if (rst_a == 1'b1) begin
    biu_l1_clk_enable_resync_r <= 1'b1;
  end 
  else if(nmi_restart_r == 1'b1) begin
    biu_l1_clk_enable_resync_r <= 1'b1;
  end 
  else begin
    biu_l1_clk_enable_resync_r <= biu_l1_clk_enable;
  end
end
assign biu_l1_clk_ctrl =   1'b1
                         & (   biu_l1_clk_enable_resync_r
                           )
                         ;

assign biu_l1_clk_accept = 1'b1
                         & biu_l1_clk_enable_resync_r
                         ;

//2 flip-flop clock control signal
always @(posedge clk or posedge rst_a)
begin : biu_l1_clk_ctrl_r_PROC
  if (rst_a == 1'b1) begin
    biu_l1_clk_ctrl_r0  <= 1'b1;
    biu_l1_clk_ctrl_r1  <= 1'b1;
    biu_l1_clk_accept_r <= 1'b1;
  end 
  else if(nmi_restart_r == 1'b1) begin
    biu_l1_clk_ctrl_r0  <= 1'b1;
    biu_l1_clk_ctrl_r1  <= 1'b1;
    biu_l1_clk_accept_r <= 1'b1;
  end 
  else begin
    biu_l1_clk_ctrl_r0  <= biu_l1_clk_ctrl;
    biu_l1_clk_ctrl_r1  <= biu_l1_clk_ctrl_r0;
    biu_l1_clk_accept_r <= biu_l1_clk_accept;
  end
end

assign biu_l1_clkgate_en = biu_l1_clk_ctrl_r0 | biu_l1_clk_ctrl_r1;
assign biu_accept_en = biu_l1_clk_accept_r;








reg                     l1_clk_ctrl_r0;
reg                     l1_clk_ctrl_r1;
wire                    l1_clkgate_en;

wire l1_clk_enable_resync_n;
npuarc_cc_cdc_sync #(.SYNC_FF_LEVELS(`npuarc_CC_SYNC_CDC_LEVELS)
             ) u_l1_clk_enable_cdc_sync (
                                       .clk   (clk),
                                       .rst_a (rst_a),
                                       .din   (~l1_clk_enable),
                                       .dout  (l1_clk_enable_resync_n)
                                      );

// 2 flip-flop clock control signal (This is not for metastability!)
always @(posedge clk or posedge rst_a)
begin : l1_clk_ctrl_r_PROC
  if (rst_a == 1'b1) begin
    l1_clk_ctrl_r0 <= 1'b1;
    l1_clk_ctrl_r1 <= 1'b1;
  end 
  else if(nmi_restart_r == 1'b1) begin
    l1_clk_ctrl_r0 <= 1'b1;
    l1_clk_ctrl_r1 <= 1'b1;
  end 
  else begin
    l1_clk_ctrl_r0 <= ~l1_clk_enable_resync_n;
    l1_clk_ctrl_r1 <= l1_clk_ctrl_r0;
  end
end

assign l1_clkgate_en = l1_clk_ctrl_r0
                            | l1_clk_ctrl_r1
                            ;
assign l1_accept_en  = l1_clk_ctrl_r0;



  ///////////////////////////////////////////////////////////////////////////////
  // Instantiate a clock gate wrapper so that the synthesis flow can replace it
  // with the proper clkgate cell of the target library
  ///////////////////////////////////////////////////////////////////////////////
  //each core clock gate

  npuarc_cc_clkgate u_l1_clkgate (
    .clk_in            (clk),
    .clock_enable_r    (l1_clkgate_en),
    .clk_out           (l1_clk)
  );

assign cc_pd1_clk = clk;

  // cc misc module clock gate
  npuarc_cc_clkgate u_cc_misc_clkgate (
    .clk_in            (clk),
    .clock_enable_r    (cc_misc_l1_clkgate_en),
    .clk_out           (cc_misc_l1_clk)
  );

  npuarc_cc_clkgate u_biu_l1_clkgate (
    .clk_in            (clk),
    .clock_enable_r    (biu_l1_clkgate_en),
    .clk_out           (biu_l1_clk)
  );





endmodule // cc_clock_ctrl

// spyglass enable_block STARC05-1.3.1.3

