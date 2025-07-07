// Library ARCv2CC-3.2.999999999

//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2014 Synopsys, Inc. All rights reserved.
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
// ===========================================================================
//
// Description:
//  Verilog module to response the IBP protocol
//  The IBP is standard IBP protocol, besides, this module
//  have some limitation or extention to standard IBP protocol
//     * Support narrow transfer: the data-size can be narrower than the
//       data bus width
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_biu_defines.v"

// Set simulation timescale
//
`include "const.def"


module npuarc_biu_ccm_ibp_slv
  #(
    // ADDR_W indicate the width of address
        // It can be any value
    parameter ADDR_W = 32,
    // DATA_W indicate the width of data
        // It can be any value
    parameter DATA_W = 32

) (
  ////////////
  // The "ibp_xxx" bus is the one IBP to be converted
  //
  // command channel
  // This module Do not support the id and snoop
  input  i_ibp_cmd_valid,
  output i_ibp_cmd_accept,
  input  i_ibp_cmd_read,
  input  [ADDR_W-1:0] i_ibp_cmd_addr,
  input  i_ibp_cmd_wrap,
  input  [2:0] i_ibp_cmd_data_size,
  input  [3:0] i_ibp_cmd_burst_size,
  input  i_ibp_cmd_lock,
  input  i_ibp_cmd_excl,
  input  [1:0] i_ibp_cmd_prot,
  input  [3:0] i_ibp_cmd_cache,
  //
  // read data channel
  // This module do not support id, snoop rd_resp, rd_ack and rd_abort
  output i_ibp_rd_valid,
  input  i_ibp_rd_accept,
  output [DATA_W-1:0] i_ibp_rd_data,
  output i_ibp_rd_last,
  output i_ibp_err_rd,
  output i_ibp_rd_excl_ok,
  //
  // write data channel
  input  i_ibp_wr_valid,
  output i_ibp_wr_accept,
  input  [DATA_W-1:0] i_ibp_wr_data,
  input  [(DATA_W/8)-1:0] i_ibp_wr_mask,
  input  i_ibp_wr_last,
  //
  // write response channel
  // This module do not support id
  output i_ibp_wr_done,
  output i_ibp_wr_excl_done,
  output i_ibp_err_wr,
  input  i_ibp_wr_resp_accept,

  ////////////
  // The "ibp_xxx" bus is the one IBP to be converted
  //
  // command channel
  // This module Do not support the id and snoop
  output  o_ibp_cmd_valid,
  input o_ibp_cmd_accept,
  output  o_ibp_cmd_read,
  output  [ADDR_W-1:0] o_ibp_cmd_addr,
  output  o_ibp_cmd_wrap,
  output  [2:0] o_ibp_cmd_data_size,
  output  [3:0] o_ibp_cmd_burst_size,
  output  o_ibp_cmd_lock,
  output  o_ibp_cmd_excl,
  output  [1:0] o_ibp_cmd_prot,
  output  [3:0] o_ibp_cmd_cache,
  //
  // read data channel
  // This module do not support id, snoop rd_resp, rd_ack and rd_abort
  input  o_ibp_rd_valid,
  output o_ibp_rd_accept,
  input  [DATA_W-1:0] o_ibp_rd_data,
  input  o_ibp_rd_last,
  input  o_ibp_err_rd,
  input  o_ibp_rd_excl_ok,
  //
  // write data channel
  output  o_ibp_wr_valid,
  input   o_ibp_wr_accept,
  output  [DATA_W-1:0] o_ibp_wr_data,
  output  [(DATA_W/8)-1:0] o_ibp_wr_mask,
  output  o_ibp_wr_last,
  //
  // write response channel
  // This module do not support id
  input  o_ibp_wr_done,
  input  o_ibp_wr_excl_done,
  input  o_ibp_err_wr,
  output o_ibp_wr_resp_accept,

  ////////
  input  clk,  // clock signal
  input  nmi_restart_r, // NMI reset signal
  input  rst_a // reset signal
  );


assign o_ibp_cmd_valid = i_ibp_cmd_valid;
assign i_ibp_cmd_accept = o_ibp_cmd_accept;
assign o_ibp_cmd_read = i_ibp_cmd_read;
assign o_ibp_cmd_addr = i_ibp_cmd_addr;
assign o_ibp_cmd_wrap = i_ibp_cmd_wrap;
assign o_ibp_cmd_data_size = i_ibp_cmd_data_size;
assign o_ibp_cmd_burst_size = i_ibp_cmd_burst_size;
assign o_ibp_cmd_prot = i_ibp_cmd_prot;
assign o_ibp_cmd_cache = i_ibp_cmd_cache;
assign o_ibp_cmd_lock = i_ibp_cmd_lock;
assign o_ibp_cmd_excl = i_ibp_cmd_excl;

assign i_ibp_rd_valid = o_ibp_rd_valid;
assign i_ibp_rd_excl_ok = o_ibp_rd_excl_ok;
assign o_ibp_rd_accept = i_ibp_rd_accept;
assign i_ibp_err_rd = o_ibp_err_rd;
assign i_ibp_rd_data = o_ibp_rd_data;
assign i_ibp_rd_last = o_ibp_rd_last;

assign o_ibp_wr_valid = i_ibp_wr_valid;
assign i_ibp_wr_accept = o_ibp_wr_accept;
assign o_ibp_wr_data = i_ibp_wr_data;
assign o_ibp_wr_mask = i_ibp_wr_mask;
assign o_ibp_wr_last = i_ibp_wr_last;

assign i_ibp_wr_done = o_ibp_wr_done;
assign i_ibp_wr_excl_done = o_ibp_wr_excl_done;
assign i_ibp_err_wr = o_ibp_err_wr;
assign o_ibp_wr_resp_accept = i_ibp_wr_resp_accept;


endmodule // biu_ccm_ibp_slv

