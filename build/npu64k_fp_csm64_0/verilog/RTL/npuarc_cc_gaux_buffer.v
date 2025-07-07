// Library ARCv2CC-3.2.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2015 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2012, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   cc_gaux_buffer: single-stage buffer for GAUX handshake transfers
//
// ===========================================================================
//
// Description:
//  Verilog module defining a single-stage buffer for registered GAUX interfaces
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_cc_exported_defines.v"
`include "npuarc_cc_defines.v"

module npuarc_cc_gaux_buffer (
  ////////// Receive data interface //////////////////////////////////////////
  //
  input  wire                            i_gaux_cmd_valid,
  output wire                            i_gaux_cmd_accept,
  input  wire [`npuarc_CC_GAUX_CMD_WIDTH-1:0]   i_gaux_cmd,
  output wire                            i_gaux_res_valid,
  input  wire                            i_gaux_res_accept,
  output wire [`npuarc_CC_GAUX_RES_WIDTH-1:0]   i_gaux_res_data,
  input  wire                            i_gaux_wen_valid,
  output wire                            i_gaux_wen_accept,
  input  wire [`npuarc_CC_GAUX_WADDR_WIDTH-1:0] i_gaux_wen_addr,
  input  wire [`npuarc_CC_GAUX_WDATA_WIDTH-1:0] i_gaux_wen_data,
  input  wire [`npuarc_CC_GAUX_CORE_ID_RANGE]   i_gaux_wen_core_id,


  ////////// Transmit data interface /////////////////////////////////////////
  //
  output wire                            o_gaux_cmd_valid,
  input  wire                            o_gaux_cmd_accept,
  output wire [`npuarc_CC_GAUX_CMD_WIDTH-1:0]   o_gaux_cmd,
  input  wire                            o_gaux_res_valid,
  output wire                            o_gaux_res_accept,
  input  wire [`npuarc_CC_GAUX_RES_WIDTH-1:0]   o_gaux_res_data,
  output wire                            o_gaux_wen_valid,
  input  wire                            o_gaux_wen_accept,
  output wire [`npuarc_CC_GAUX_WADDR_WIDTH-1:0] o_gaux_wen_addr,
  output wire [`npuarc_CC_GAUX_WDATA_WIDTH-1:0] o_gaux_wen_data,
  output wire [`npuarc_CC_GAUX_CORE_ID_RANGE]   o_gaux_wen_core_id,

  ////////// General input signals ///////////////////////////////////////////
  //
  input                                  nmi_restart_r,
  input                                  clk,                  // clock signal
  input                                  rst_a                 // reset signal
  );

  //////////////////////////////////////////////////////////////////////////////
  //                                                                          //
  // Internal signals                                                         //
  //                                                                          //
  //////////////////////////////////////////////////////////////////////////////
  reg                                   gaux_cmd_valid_r;
  reg [`npuarc_CC_GAUX_CMD_WIDTH-1:0]          gaux_cmd_r;
  reg                                   gaux_res_valid_r;
  reg [`npuarc_CC_GAUX_RES_WIDTH-1:0]          gaux_res_data_r;
  reg                                   gaux_wen_valid_r;
  reg [`npuarc_CC_GAUX_WADDR_WIDTH-1:0]        gaux_wen_addr_r;
  reg [`npuarc_CC_GAUX_WDATA_WIDTH-1:0]        gaux_wen_data_r;
  reg [`npuarc_CC_GAUX_CORE_ID_RANGE]          gaux_wen_core_id_r;


  //////////////////////////////////////////////////////////////////////////////
  //                                                                          //
  // GAUX single-stage buffer logic                                           //
  //                                                                          //
  //////////////////////////////////////////////////////////////////////////////
  // cmd channel buffer
  wire   gaux_cmd_valid_set  = i_gaux_cmd_valid & i_gaux_cmd_accept;
  wire   gaux_cmd_valid_clr  = gaux_cmd_valid_r & o_gaux_cmd_accept;
  wire   gaux_cmd_valid_ena  = gaux_cmd_valid_set | gaux_cmd_valid_clr;
  wire   gaux_cmd_valid_nxt  = gaux_cmd_valid_set | (~gaux_cmd_valid_clr);

  assign i_gaux_cmd_accept   = (~gaux_cmd_valid_r);
  assign o_gaux_cmd_valid    = gaux_cmd_valid_r;
  assign o_gaux_cmd          = gaux_cmd_r;

  always @(posedge clk or posedge rst_a)
  begin : gaux_cmd_valid_DFFEAR_PROC
// spyglass disable_block Reset_check07
// SMD: Reset/preset driven by combinational logic
// SJ: combinational logic caused by testmode
    if (rst_a == 1'b1)
// spyglass enable_block Reset_check07        
      begin
         gaux_cmd_valid_r <= 1'b0;
      end
    else if (nmi_restart_r == 1'b1)
      begin
         gaux_cmd_valid_r <= 1'b0;
      end
    else
      begin
        if (gaux_cmd_valid_ena == 1'b1)
          begin
            gaux_cmd_valid_r <= gaux_cmd_valid_nxt;
          end
      end
  end

  always @(posedge clk or posedge rst_a)
  begin : gaux_cmd_DFFEAR_PROC
    if (rst_a == 1'b1)
      begin
         gaux_cmd_r <= {`npuarc_CC_GAUX_CMD_WIDTH{1'b0}};
      end
    else if (nmi_restart_r == 1'b1)
      begin
         gaux_cmd_r <= {`npuarc_CC_GAUX_CMD_WIDTH{1'b0}};
      end
    else
      begin
        if (gaux_cmd_valid_set == 1'b1)
          begin
            gaux_cmd_r <= i_gaux_cmd;
          end
      end
  end

// resp channel buffer
wire   gaux_res_valid_set  = o_gaux_res_valid & o_gaux_res_accept;
wire   gaux_res_valid_clr  = gaux_res_valid_r & i_gaux_res_accept;
wire   gaux_res_valid_ena  = gaux_res_valid_set | gaux_res_valid_clr;
wire   gaux_res_valid_nxt  = gaux_res_valid_set | (~gaux_res_valid_clr);

assign o_gaux_res_accept   = (~gaux_res_valid_r);
assign i_gaux_res_valid    = gaux_res_valid_r;
assign i_gaux_res_data     = gaux_res_data_r;

  always @(posedge clk or posedge rst_a)
  begin : gaux_res_valid_DFFEAR_PROC
    if (rst_a == 1'b1)
      begin
         gaux_res_valid_r <= 1'b0;
      end
    else if (nmi_restart_r == 1'b1)
      begin
         gaux_res_valid_r <= 1'b0;
      end
    else
      begin
        if (gaux_res_valid_ena == 1'b1)
          begin
            gaux_res_valid_r <= gaux_res_valid_nxt;
          end
      end
  end

  always @(posedge clk or posedge rst_a)
  begin : gaux_res_data_DFFEAR_PROC
    if (rst_a == 1'b1)
      begin
         gaux_res_data_r <= {`npuarc_CC_GAUX_RES_WIDTH{1'b0}};
      end
    else
      begin
        if (gaux_res_valid_set == 1'b1)
          begin
            gaux_res_data_r <= o_gaux_res_data;
          end
      end
  end

  // write data channel buffer
  wire   gaux_wen_valid_set  = i_gaux_wen_valid & i_gaux_wen_accept;
  wire   gaux_wen_valid_clr  = gaux_wen_valid_r & o_gaux_wen_accept;
  wire   gaux_wen_valid_ena  = gaux_wen_valid_set | gaux_wen_valid_clr;
  wire   gaux_wen_valid_nxt  = gaux_wen_valid_set | (~gaux_wen_valid_clr);

  assign i_gaux_wen_accept   = (~gaux_wen_valid_r);
  assign o_gaux_wen_valid    = gaux_wen_valid_r;
  assign o_gaux_wen_addr     = gaux_wen_addr_r;
  assign o_gaux_wen_data     = gaux_wen_data_r;
  assign o_gaux_wen_core_id  = gaux_wen_core_id_r;

  always @(posedge clk or posedge rst_a)
  begin : gaux_wen_valid_DFFEAR_PROC
    if (rst_a == 1'b1)
      begin
         gaux_wen_valid_r <= 1'b0;
      end
    else if (nmi_restart_r == 1'b1)
      begin
         gaux_wen_valid_r <= 1'b0;
      end      
    else
      begin
        if (gaux_wen_valid_ena == 1'b1)
          begin
            gaux_wen_valid_r <= gaux_wen_valid_nxt;
          end
      end
  end

  always @(posedge clk or posedge rst_a)
  begin : gaux_wen_chnl_DFFEAR_PROC
    if (rst_a == 1'b1)
      begin
         gaux_wen_addr_r    <= {`npuarc_CC_GAUX_WADDR_WIDTH{1'b0}};
         gaux_wen_data_r    <= {`npuarc_CC_GAUX_WDATA_WIDTH{1'b0}};
         gaux_wen_core_id_r <= {`npuarc_CC_GAUX_CORE_ID_WIDTH{1'b0}};
      end
    else if (nmi_restart_r == 1'b1)
      begin
         gaux_wen_core_id_r <= {`npuarc_CC_GAUX_CORE_ID_WIDTH{1'b0}};
      end            
    else
      begin
        if (gaux_wen_valid_set == 1'b1)
          begin
            gaux_wen_addr_r    <= i_gaux_wen_addr;
            gaux_wen_data_r    <= i_gaux_wen_data;
            gaux_wen_core_id_r <= i_gaux_wen_core_id;
          end
      end
  end


endmodule // cc_gaux_buffer
