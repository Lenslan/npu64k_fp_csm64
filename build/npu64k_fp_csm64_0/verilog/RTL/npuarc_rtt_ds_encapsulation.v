// Library ARC_Trace-3.0.999999999
//----------------------------------------------------------------------------
//
// Copyright 2010-2015 Synopsys, Inc. All rights reserved.
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
// ===========================================================================
//
// Description:
//
//  This module implements message formation logic for debug status  messages. This module
//  has configurable capacity.
//
//  This .vpp source file must be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o rtt_ds_encapsulation.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_ds_encapsulation (

rtt_clk,

sys_reset,

dsm_en,
pr_num,

rtt_ss_halt,
rtt_sw_bp,
rtt_hw_bp,
rtt_hwe,
rtt_enter_sleep,
rtt_dbg_halt,
core_rst,
rtt_wp_val,

timestamp,

ds_msg_valid,
ds_msg

);


input rtt_clk;

input sys_reset;
input [`npuarc_PRNUM_WDT-1:0] pr_num;

input [`npuarc_TSTAMP_WDT-1:0]timestamp;

input dsm_en;
input rtt_ss_halt;
input rtt_sw_bp;
input rtt_hw_bp;
input rtt_hwe;
input rtt_enter_sleep;
input rtt_dbg_halt;
input core_rst;
input [7:0] rtt_wp_val;

output ds_msg_valid;
output [`npuarc_DSM_WDT-1:0] ds_msg;

reg ds_msg_valid;
reg [`npuarc_DSM_WDT-1:0] ds_msg;
wire [5:0] tcode;
wire [`npuarc_PRNUM_WDT-1:0]src;
wire [`npuarc_TSTAMP_WDT-1:0] time_stamp;

wire [7:0] ds_mdo_nons [6:0];
wire [1:0] ds_mseo_nons[6:0];
wire [31:0] status_i;
reg [1:0] rdy_r;
reg [31:0] status;
reg rtt_hwe_r;
reg rtt_enter_sleep_r;
reg rtt_dbg_halt_r;
wire ds_msg_valid_i;

wire rtt_hwe_as;
//wire rtt_hwe_deas;
wire rtt_enter_sleep_as;
wire rtt_enter_sleep_deas;
wire rtt_dbg_halt_as;
wire rtt_dbg_halt_deas;

//Ignore as/deas transitions out of reset until pipeline flops are filled
always @ (posedge rtt_clk or posedge sys_reset)
  begin : RTT_RDY_PROC
    if(sys_reset == 1'b1)
      rdy_r <= 2'b0;
    else if (~rdy_r[1])
      rdy_r <= {rdy_r[0],1'b1};
  end

//Registered signal for Harware-error status from core
always @ (posedge rtt_clk or posedge sys_reset)
  begin : RTT_HWE_R_PROC
    if(sys_reset == 1'b1)
      rtt_hwe_r <= 1'b0;
    else
      rtt_hwe_r <= rtt_hwe;
  end

//Registered signal for sleep enter status from core
always @ (posedge rtt_clk or posedge sys_reset)
  begin : RTT_ENTER_SLEEP_R_PROC
    if(sys_reset == 1'b1)
      rtt_enter_sleep_r <= 1'b0;
    else
      rtt_enter_sleep_r <= rtt_enter_sleep;
  end

//Registered signal for debug halt status from core
always @ (posedge rtt_clk or posedge sys_reset)
  begin : RTT_DBG_HALT_R_PROC
    if(sys_reset == 1'b1)
      rtt_dbg_halt_r <= 1'b0;
    else
      rtt_dbg_halt_r <= rtt_dbg_halt;
  end

//Assert and de-assert pulses for hwe, sleep and halt status from core
assign rtt_hwe_as = (~rtt_hwe_r) && rtt_hwe;
//assign rtt_hwe_deas = rtt_hwe_r && (~rtt_hwe);
assign rtt_enter_sleep_as = (~rtt_enter_sleep_r) && rtt_enter_sleep;
assign rtt_enter_sleep_deas = rtt_enter_sleep_r && (~rtt_enter_sleep);
assign rtt_dbg_halt_as = (~rtt_dbg_halt_r) && rtt_dbg_halt;
assign rtt_dbg_halt_deas = rtt_dbg_halt_r && (~rtt_dbg_halt);

//Message valid signal combinational
assign ds_msg_valid_i = dsm_en && (rtt_ss_halt ||
                      rtt_sw_bp || rtt_hw_bp || 
                      (rdy_r[1] && (rtt_hwe_as ||
                      rtt_enter_sleep_as || rtt_enter_sleep_deas ||
                      rtt_dbg_halt_as || rtt_dbg_halt_deas )));
//Message type encoding
assign tcode = 6'd0;

//Core/Producer number in multi-core configuration
assign src = pr_num;
assign time_stamp = timestamp;

//Debug status bus
assign status_i = {
16'b0,
rtt_wp_val,
1'b0,
core_rst,
rtt_dbg_halt,
rtt_enter_sleep,
rtt_hwe,
rtt_hw_bp,
rtt_sw_bp,
rtt_ss_halt

};

//Message valid signal registered version
always @ (posedge rtt_clk or posedge sys_reset )
  begin : DS_MSG_VALID_PROC
    if(sys_reset == 1'b1)
      ds_msg_valid <= 1'b0;
    else
      ds_msg_valid <= ds_msg_valid_i;
  end

//Debug status bus registered version
always @ (posedge rtt_clk or posedge sys_reset )
  begin : STATUS_PROC
    if(sys_reset == 1'b1)
      status <= 32'b0;
    else
      status <= status_i;
  end

/**************************************************/
//Message encoding in 8-bit data format to place in ds_mdo_nons array for DEBUG-STATUS messages
/**************************************************/
assign ds_mdo_nons[0] = {status[1:0],tcode[5:0]};
assign ds_mdo_nons[1] = status[9:2];
assign ds_mdo_nons[2] = status[17:10];
assign ds_mdo_nons[3] = status[25:18];
assign ds_mdo_nons[4] = {time_stamp[1:0],status[31:26]};
assign ds_mdo_nons[5] = {2'b0,time_stamp[7:2]};
assign ds_mdo_nons[6] = 8'b0;

/****************************s**********************/
//Control information to place in ds_mseo_nons array for DEBUG-STATUS messages
/**************************************************/
assign ds_mseo_nons[0] = 2'b00;
assign ds_mseo_nons[1] = 2'b00;
assign ds_mseo_nons[2] = 2'b00;
assign ds_mseo_nons[3] = 2'b00;
assign ds_mseo_nons[4] = |time_stamp[7:2] ? 2'b00 : 2'b11;
assign ds_mseo_nons[5] = |time_stamp[7:2] ? 2'b11 : 2'b00;
assign ds_mseo_nons[6] = 2'b00;


/**************************************************/
//Assigning DEBUG-STATUS message bus with data & control arrays
/**************************************************/
always @ *
  begin : DS_MSG_PROC
    ds_msg [7:0] = ds_mdo_nons[0];
    ds_msg [17:10] = ds_mdo_nons[1];
    ds_msg [27:20] = ds_mdo_nons[2];
    ds_msg [37:30] = ds_mdo_nons[3];
    ds_msg [47:40] = ds_mdo_nons[4];
    ds_msg [57:50] = ds_mdo_nons[5];
    ds_msg [67:60] = ds_mdo_nons[6];
    ds_msg [9:8] = ds_mseo_nons[0];
    ds_msg [19:18] = ds_mseo_nons[1];
    ds_msg [29:28] = ds_mseo_nons[2];
    ds_msg [39:38] = ds_mseo_nons[3];
    ds_msg [49:48] = ds_mseo_nons[4];
    ds_msg [59:58] = ds_mseo_nons[5];
    ds_msg [69:68] = ds_mseo_nons[6];
  end

endmodule
