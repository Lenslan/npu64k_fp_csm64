// Library ARCv2CC-3.2.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2013 Synopsys, Inc. All rights reserved.
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
// ===========================================================================
//
// Description:
//  The cc_top_aon_regs implement the cc-top relevant registers, e.g.,
//      LLM_ENABLE
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include   "npuarc_cc_exported_defines.v"
`include   "npuarc_cc_defines.v"








// Set simulation timescale
//
`include "const.def"

module npuarc_cc_top_aon_regs (

  input                                cc_top_cg_en_gaux_cmd_valid,
  output                               cc_top_cg_en_gaux_cmd_accept,
  input [`npuarc_CC_GAUX_CMD_WIDTH-1:0]       cc_top_cg_en_gaux_cmd,

  output                               cc_top_cg_en_gaux_res_valid,
  input                                cc_top_cg_en_gaux_res_accept,
  output [`npuarc_CC_GAUX_RES_WIDTH-1:0]      cc_top_cg_en_gaux_res_data,

  input                                cc_top_cg_en_gaux_wen_valid,
  input [`npuarc_CC_GAUX_WADDR_WIDTH-1:0]     cc_top_cg_en_gaux_wen_addr,
  input [`npuarc_CC_GAUX_WDATA_WIDTH-1:0]     cc_top_cg_en_gaux_wen_data,

  output                               cc_top_l1_cg_dis,//1 disable L1 clock gate, 0 enable
  output                               cc_biu_l1_cg_dis,


  output                               l1_cg_dis,



  input          nmi_restart_r,
  // global signals
  input          clk,
  input          rst_a
);


// For cc level 1 clock control register
reg cc_top_cg_en_gaux_res_valid_r;
reg [`npuarc_CC_GAUX_RES_WIDTH-1:0]   cc_top_cg_en_gaux_res_r;
assign cc_top_cg_en_gaux_res_data = cc_top_cg_en_gaux_res_r;
assign cc_top_cg_en_gaux_res_valid = cc_top_cg_en_gaux_res_valid_r;

assign cc_top_cg_en_gaux_cmd_accept = (~cc_top_cg_en_gaux_res_valid_r);

wire cc_top_cg_en_gaux_res_valid_set = cc_top_cg_en_gaux_cmd_valid & cc_top_cg_en_gaux_cmd_accept;
wire cc_top_cg_en_gaux_res_valid_clr = cc_top_cg_en_gaux_res_valid & cc_top_cg_en_gaux_res_accept;
wire cc_top_cg_en_gaux_res_valid_ena = cc_top_cg_en_gaux_res_valid_set | cc_top_cg_en_gaux_res_valid_clr;
wire cc_top_cg_en_gaux_res_valid_nxt = cc_top_cg_en_gaux_res_valid_set | (~cc_top_cg_en_gaux_res_valid_clr);

always @(posedge clk or posedge rst_a)
begin : cc_top_cg_en_valid_DFFEAR_PROC
  if (rst_a == 1'b1)
    cc_top_cg_en_gaux_res_valid_r <= 1'b0;
  else if (nmi_restart_r == 1'b1)
    begin
    cc_top_cg_en_gaux_res_valid_r <= 1'b0;
    end
  else if (cc_top_cg_en_gaux_res_valid_ena == 1'b1)
    cc_top_cg_en_gaux_res_valid_r <= cc_top_cg_en_gaux_res_valid_nxt;
end

wire [`npuarc_CC_GAUX_RES_WIDTH-1:0]   cc_top_cg_en_gaux_res;

always @(posedge clk or posedge rst_a)
begin : cc_top_cg_enres_DFFEAR_PROC
  if (rst_a == 1'b1)
    cc_top_cg_en_gaux_res_r <= `npuarc_CC_GAUX_CMD_WIDTH'b0;
  else if (cc_top_cg_en_gaux_res_valid_set == 1'b1)
    cc_top_cg_en_gaux_res_r <= cc_top_cg_en_gaux_res;
end

//////////////////////////////////////////////////////////////////////////////
// CC_TOP_CLOCKGATE_EN register
// spyglass disable_block FlopEConst
// SMD: Enable pin tie to constant
// SJ: disable level 1 clock gate aux register write enable
wire cc_top_cg_enable_set = cc_top_cg_en_gaux_wen_valid & (cc_top_cg_en_gaux_wen_addr == `npuarc_AUX_ADDR_CG_ENABLE);
reg [11:0] cc_top_cg_enable_r;
always @(posedge clk or posedge rst_a)
begin : cc_top_cg_enable_DFFEAR_PROC
  if (rst_a == 1'b1)
    cc_top_cg_enable_r <= 12'h18f;
  else if (nmi_restart_r == 1'b1)
    cc_top_cg_enable_r <= 12'h18f;
  else if (cc_top_cg_enable_set == 1'b1)
    cc_top_cg_enable_r <= {3'b0,cc_top_cg_en_gaux_wen_data[8:7],3'b0,cc_top_cg_en_gaux_wen_data[3:0]};
end
assign cc_top_l1_cg_dis = cc_top_cg_enable_r[7];
assign cc_biu_l1_cg_dis = cc_top_cg_enable_r[1];

assign l1_cg_dis = cc_top_cg_enable_r[8];

// spyglass enable_block FlopEConst

///////////////////////////////////////////////////////////
// The read data path
//////////////////////////////////////////////////////////////////////////
// When accessing an unimplemented address out of the range of this auxiliary
// register space, the aux_unimpl signal should be asserted, and
// the the rdata should be all zeros.
wire cc_top_cg_en_gaux_cg_enable_sel = (cc_top_cg_en_gaux_cmd[`npuarc_CC_GAUX_CMD_ADDR] == `npuarc_AUX_ADDR_CG_ENABLE);
wire cc_top_cg_en_gaux_cg_enable_rd = cc_top_cg_en_gaux_cmd[`npuarc_CC_GAUX_CMD_REN] & cc_top_cg_en_gaux_cg_enable_sel;

assign cc_top_cg_en_gaux_res[`npuarc_CC_GAUX_RES_DATA] =
               32'b0
               | {32{cc_top_cg_en_gaux_cg_enable_rd}} & {20'b0, cc_top_cg_enable_r}
               ;


wire cc_top_cg_en_gaux_res_unimpl = (~cc_top_cg_en_gaux_cmd_valid) |
                                    (cc_top_cg_en_gaux_cmd_valid & (~(cc_top_cg_en_gaux_cg_enable_sel)));

assign cc_top_cg_en_gaux_res[`npuarc_CC_GAUX_RES_UNIMPL  ] = cc_top_cg_en_gaux_res_unimpl;

// CC_TOP_CLOCKGATE_EN auxiliary reg is K_RW, non-strict, serializing
assign cc_top_cg_en_gaux_res [`npuarc_CC_GAUX_RES_K_RD    ] = ~cc_top_cg_en_gaux_res_unimpl;
assign cc_top_cg_en_gaux_res [`npuarc_CC_GAUX_RES_K_WR    ] = ~cc_top_cg_en_gaux_res_unimpl;
assign cc_top_cg_en_gaux_res [`npuarc_CC_GAUX_RES_SERIAL  ] = (cc_top_cg_en_gaux_cmd[`npuarc_CC_GAUX_CMD_WEN]) & cc_top_cg_en_gaux_cg_enable_sel;
assign cc_top_cg_en_gaux_res [`npuarc_CC_GAUX_RES_STRICT  ] = 1'b0;
assign cc_top_cg_en_gaux_res [`npuarc_CC_GAUX_RES_ILLEGAL ] = 1'b0;


//////////////////////////////////////////////////////////////////////////////////
// qos register for vccm arbiter
//







endmodule // cc_top_aon_regs
