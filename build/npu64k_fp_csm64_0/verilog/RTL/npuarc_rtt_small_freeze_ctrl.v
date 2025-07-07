// Library ARC_Trace-3.0.999999999


// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   rtt_freeze_ctrl
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_freeze_ctrl.vpp
//
// ===========================================================================


`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_small_freeze_ctrl
(
rtt_clk,
rst_a,

freeze_ctrl,

pc_sbuf_num_fill,
ptc_sbuf_num_fill,
pt_sbuf_num_fill,
vdspm_sbuf_num_fill,
vdspm_sbuf_freeze,
errm_sbuf_num_fill,
otm_sbuf_num_fill,
rfm_sbuf_num_fill,
wpm_sbuf_num_fill,
ds_sbuf_num_fill,
flush_done,

freeze_status,
freeze

);

input rtt_clk;
input rst_a;

input       freeze_ctrl;

input [`npuarc_PCM_BUF_DEPTH:0]  pc_sbuf_num_fill;
input [`npuarc_PTCM_BUF_DEPTH:0] ptc_sbuf_num_fill;
input [`npuarc_PTM_BUF_DEPTH:0]  pt_sbuf_num_fill;
input [`npuarc_VDSPM_BUF_DEPTH:0]  vdspm_sbuf_num_fill;
output vdspm_sbuf_freeze;
input [`npuarc_ERRM_BUF_DEPTH:0] errm_sbuf_num_fill;
input [`npuarc_OTM_BUF_DEPTH:0]  otm_sbuf_num_fill;
input [`npuarc_RFM_BUF_DEPTH:0]  rfm_sbuf_num_fill;
input [`npuarc_WPM_BUF_DEPTH:0]  wpm_sbuf_num_fill;
input [`npuarc_DSM_BUF_DEPTH:0]  ds_sbuf_num_fill;
input flush_done;

output [`npuarc_FR_STATUS-1:0] freeze_status;
output freeze;

reg pc_sbuf_freeze;
reg ptc_sbuf_freeze;
reg pt_sbuf_freeze;
reg errm_sbuf_freeze;
reg otm_sbuf_freeze;
reg rfm_sbuf_freeze;
reg wpm_sbuf_freeze;
reg ds_sbuf_freeze;
reg vdspm_sbuf_freeze;

wire ocm_freeze_i;
assign ocm_freeze_i = 1'b0;
assign freeze = freeze_ctrl && (!ocm_freeze_i) && (|freeze_status[`npuarc_FR_STATUS-1:0]);
assign freeze_status =
{
1'b0,
vdspm_sbuf_freeze,
ds_sbuf_freeze,
wpm_sbuf_freeze ,
rfm_sbuf_freeze ,
otm_sbuf_freeze ,
errm_sbuf_freeze ,
1'b0 ,
1'b0 ,
1'b0 ,
pt_sbuf_freeze ,
ptc_sbuf_freeze ,
pc_sbuf_freeze};


// spyglass disable_block SelfDeterminedExpr-ML
// SMD: Self determined expression
// SJ: values passed as defines
always @ (posedge rtt_clk or posedge rst_a)
  begin : PC_SBUF_FREEZE_PROC
    if(rst_a == 1'b1)
      pc_sbuf_freeze <= 1'b0;
    else if(((((`npuarc_PCM_BUF_LOCS) - pc_sbuf_num_fill) >= (1 + (`npuarc_PCM_BUF_LOCS)/2))) || flush_done)
      pc_sbuf_freeze <= 1'b0;
    else if(((`npuarc_PCM_BUF_LOCS) - pc_sbuf_num_fill) <= `npuarc_PCM_FREEZE_LEVEL)
      pc_sbuf_freeze <= 1'b1;
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : PTC_SBUF_FREEZE_PROC
    if(rst_a == 1'b1)
      ptc_sbuf_freeze <= 1'b0;
    else if(((((`npuarc_PTCM_BUF_LOCS) - ptc_sbuf_num_fill) >= (1+(`npuarc_PTCM_BUF_LOCS)/2))) || flush_done)
      ptc_sbuf_freeze <= 1'b0;
    else if(((`npuarc_PTCM_BUF_LOCS) - ptc_sbuf_num_fill) <= `npuarc_PTCM_FREEZE_LEVEL)
      ptc_sbuf_freeze <= 1'b1;
  end


always @ (posedge rtt_clk or posedge rst_a)
  begin : PT_SBUF_FREEZE_PROC
    if(rst_a == 1'b1)
      pt_sbuf_freeze <= 1'b0;
    else if(((((`npuarc_PTM_BUF_LOCS) - pt_sbuf_num_fill) >= (1+(`npuarc_PTM_BUF_LOCS)/2))) || flush_done)
      pt_sbuf_freeze <= 1'b0;
    else if(((`npuarc_PTM_BUF_LOCS) - pt_sbuf_num_fill) <= `npuarc_PTM_FREEZE_LEVEL)
      pt_sbuf_freeze <= 1'b1;
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : VDSP_SBUF_FREEZE_PROC
    if(rst_a == 1'b1)
      vdspm_sbuf_freeze <= 1'b0;
    else if(((((`npuarc_VDSPM_BUF_LOCS) - vdspm_sbuf_num_fill) >= (1+(`npuarc_VDSPM_BUF_LOCS)/2))) || flush_done)
      vdspm_sbuf_freeze <= 1'b0;
    else if(((`npuarc_VDSPM_BUF_LOCS) - vdspm_sbuf_num_fill) <= `npuarc_VDSPM_FREEZE_LEVEL)
      vdspm_sbuf_freeze <= 1'b1;
  end


always @ (posedge rtt_clk or posedge rst_a)
  begin : ERRM_SBUF_FREEZE_PROC
    if(rst_a == 1'b1)
      errm_sbuf_freeze <= 1'b0;
    else if(((((`npuarc_ERRM_BUF_LOCS) - errm_sbuf_num_fill) >= (1+(`npuarc_ERRM_BUF_LOCS)/2))) || flush_done)
      errm_sbuf_freeze <= 1'b0;
    else if(((`npuarc_ERRM_BUF_LOCS) - errm_sbuf_num_fill) <= `npuarc_ERRM_FREEZE_LEVEL)
      errm_sbuf_freeze <= 1'b1;
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : OTM_SBUF_FREEZE_PROC
    if(rst_a == 1'b1)
      otm_sbuf_freeze <= 1'b0;
    else if(((((`npuarc_OTM_BUF_LOCS) - otm_sbuf_num_fill) >= (1+(`npuarc_OTM_BUF_LOCS)/2))) || flush_done)
      otm_sbuf_freeze <= 1'b0;
    else if(((`npuarc_OTM_BUF_LOCS) - otm_sbuf_num_fill) <= `npuarc_OTM_FREEZE_LEVEL)
      otm_sbuf_freeze <= 1'b1;
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : RFM_SBUF_FREEZE_PROC
    if(rst_a == 1'b1)
      rfm_sbuf_freeze <= 1'b0;
    else if(((((`npuarc_RFM_BUF_LOCS) - rfm_sbuf_num_fill) >= (1+(`npuarc_RFM_BUF_LOCS)/2))) || flush_done)
      rfm_sbuf_freeze <= 1'b0;
    else if(((`npuarc_RFM_BUF_LOCS) - rfm_sbuf_num_fill) <= `npuarc_RFM_FREEZE_LEVEL)
      rfm_sbuf_freeze <= 1'b1;
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : WPM_SBUF_FREEZE_PROC
    if(rst_a == 1'b1)
      wpm_sbuf_freeze <= 1'b0;
    else if(((((`npuarc_WPM_BUF_LOCS) - wpm_sbuf_num_fill) >= (1+(`npuarc_WPM_BUF_LOCS)/2))) || flush_done)
      wpm_sbuf_freeze <= 1'b0;
    else if(((`npuarc_WPM_BUF_LOCS) - wpm_sbuf_num_fill) <= `npuarc_WPM_FREEZE_LEVEL)
      wpm_sbuf_freeze <= 1'b1;
  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : DSM_SBUF_FREEZE_PROC
    if(rst_a == 1'b1)
      ds_sbuf_freeze <= 1'b0;
    else if(((((`npuarc_DSM_BUF_LOCS) - ds_sbuf_num_fill) >= (1+(`npuarc_DSM_BUF_LOCS)/2))) || flush_done)
      ds_sbuf_freeze <= 1'b0;
    else if(((`npuarc_DSM_BUF_LOCS) - ds_sbuf_num_fill) <= `npuarc_DSM_FREEZE_LEVEL)
      ds_sbuf_freeze <= 1'b1;
  end
// spyglass enable_block SelfDeterminedExpr-ML


endmodule
