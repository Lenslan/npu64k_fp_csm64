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
//   rtt_swe_encapsulation_top
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_swe_encapsulation_top.vpp
//
// ===========================================================================


`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"

module npuarc_rtt_swe_encapsulation_top (

  input  wire                  rtt_clk,
// spyglass disable_block W240
// SMD: Input 'rtt_pd' declared but not read
// SJ:  Placeholder for PD integration
// spyglass enable_block W240
  input  wire                  rst_a,

  input  wire [`npuarc_RTT_TIME_STMP-1:0] time_stamp,   // Time stamp
  input  wire [63:0]               cstimestamp,
  input  wire                  rtt_time_stamp_en,
  input  wire                  flush_cmd,
  input  wire                  flush_done,
  input  wire [`npuarc_RTT_NUM_SWE_PORTS-1:0] swe_pr_sel,
  input  wire                  swe_csts_en,
  input  wire                  atb_syncreq,
  input  wire [32:0]           sl0_alt_rtt_swe_data,
  input  wire                  sl0_alt_rtt_swe_val,
  input  wire [7:0]            sl0_alt_rtt_swe_ext,
  input  wire [32:0]           sl1_alt_rtt_swe_data,
  input  wire                  sl1_alt_rtt_swe_val,
  input  wire [7:0]            sl1_alt_rtt_swe_ext,
  input  wire [32:0]           sl2_alt_rtt_swe_data,
  input  wire                  sl2_alt_rtt_swe_val,
  input  wire [7:0]            sl2_alt_rtt_swe_ext,
  input  wire [32:0]           sl3_alt_rtt_swe_data,
  input  wire                  sl3_alt_rtt_swe_val,
  input  wire [7:0]            sl3_alt_rtt_swe_ext,
  input  wire [32:0]           sl4_alt_rtt_swe_data,
  input  wire                  sl4_alt_rtt_swe_val,
  input  wire [7:0]            sl4_alt_rtt_swe_ext,
  input  wire [32:0]           sl5_alt_rtt_swe_data,
  input  wire                  sl5_alt_rtt_swe_val,
  input  wire [7:0]            sl5_alt_rtt_swe_ext,
  input  wire [32:0]           sl6_alt_rtt_swe_data,
  input  wire                  sl6_alt_rtt_swe_val,
  input  wire [7:0]            sl6_alt_rtt_swe_ext,
  input  wire [32:0]           sl7_alt_rtt_swe_data,
  input  wire                  sl7_alt_rtt_swe_val,
  input  wire [7:0]            sl7_alt_rtt_swe_ext,
  input  wire [32:0]           sl8_alt_rtt_swe_data,
  input  wire                  sl8_alt_rtt_swe_val,
  input  wire [7:0]            sl8_alt_rtt_swe_ext,
  input  wire [32:0]           sl9_alt_rtt_swe_data,
  input  wire                  sl9_alt_rtt_swe_val,
  input  wire [7:0]            sl9_alt_rtt_swe_ext,
  input  wire [32:0]           sl10_alt_rtt_swe_data,
  input  wire                  sl10_alt_rtt_swe_val,
  input  wire [7:0]            sl10_alt_rtt_swe_ext,
  input  wire [32:0]           sl11_alt_rtt_swe_data,
  input  wire                  sl11_alt_rtt_swe_val,
  input  wire [7:0]            sl11_alt_rtt_swe_ext,
  input  wire [32:0]           sl12_alt_rtt_swe_data,
  input  wire                  sl12_alt_rtt_swe_val,
  input  wire [7:0]            sl12_alt_rtt_swe_ext,
  input  wire [32:0]           sl13_alt_rtt_swe_data,
  input  wire                  sl13_alt_rtt_swe_val,
  input  wire [7:0]            sl13_alt_rtt_swe_ext,
  input  wire [32:0]           sl14_alt_rtt_swe_data,
  input  wire                  sl14_alt_rtt_swe_val,
  input  wire [7:0]            sl14_alt_rtt_swe_ext,
  input  wire [32:0]           sl15_alt_rtt_swe_data,
  input  wire                  sl15_alt_rtt_swe_val,
  input  wire [7:0]            sl15_alt_rtt_swe_ext,
  input  wire [32:0]           sl16_alt_rtt_swe_data,
  input  wire                  sl16_alt_rtt_swe_val,
  input  wire [7:0]            sl16_alt_rtt_swe_ext,
  output wire                  p0_req,
  input  wire                  p0_ack,
  output wire                  para_done,

  output wire                  sbuf_empty,
  output wire                  encapsulation_top_busy,

  output wire [120-1:0] p0_wdata
);


wire sl0_swe_sbuf_wr_en;
wire sl0_swe_sbuf_rd_en;
wire sl0_swe_sbuf_rd_vld;
wire sl0_swe_sbuf_full;
wire sl0_swe_sbuf_empty;
wire sl0_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl0_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl0_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl0_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl0_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl0_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl0_swe_msg;
  wire                    sl0_swe_msg_valid;
wire sl1_swe_sbuf_wr_en;
wire sl1_swe_sbuf_rd_en;
wire sl1_swe_sbuf_rd_vld;
wire sl1_swe_sbuf_full;
wire sl1_swe_sbuf_empty;
wire sl1_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl1_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl1_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl1_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl1_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl1_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl1_swe_msg;
  wire                    sl1_swe_msg_valid;
wire sl2_swe_sbuf_wr_en;
wire sl2_swe_sbuf_rd_en;
wire sl2_swe_sbuf_rd_vld;
wire sl2_swe_sbuf_full;
wire sl2_swe_sbuf_empty;
wire sl2_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl2_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl2_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl2_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl2_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl2_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl2_swe_msg;
  wire                    sl2_swe_msg_valid;
wire sl3_swe_sbuf_wr_en;
wire sl3_swe_sbuf_rd_en;
wire sl3_swe_sbuf_rd_vld;
wire sl3_swe_sbuf_full;
wire sl3_swe_sbuf_empty;
wire sl3_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl3_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl3_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl3_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl3_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl3_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl3_swe_msg;
  wire                    sl3_swe_msg_valid;
wire sl4_swe_sbuf_wr_en;
wire sl4_swe_sbuf_rd_en;
wire sl4_swe_sbuf_rd_vld;
wire sl4_swe_sbuf_full;
wire sl4_swe_sbuf_empty;
wire sl4_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl4_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl4_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl4_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl4_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl4_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl4_swe_msg;
  wire                    sl4_swe_msg_valid;
wire sl5_swe_sbuf_wr_en;
wire sl5_swe_sbuf_rd_en;
wire sl5_swe_sbuf_rd_vld;
wire sl5_swe_sbuf_full;
wire sl5_swe_sbuf_empty;
wire sl5_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl5_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl5_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl5_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl5_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl5_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl5_swe_msg;
  wire                    sl5_swe_msg_valid;
wire sl6_swe_sbuf_wr_en;
wire sl6_swe_sbuf_rd_en;
wire sl6_swe_sbuf_rd_vld;
wire sl6_swe_sbuf_full;
wire sl6_swe_sbuf_empty;
wire sl6_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl6_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl6_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl6_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl6_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl6_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl6_swe_msg;
  wire                    sl6_swe_msg_valid;
wire sl7_swe_sbuf_wr_en;
wire sl7_swe_sbuf_rd_en;
wire sl7_swe_sbuf_rd_vld;
wire sl7_swe_sbuf_full;
wire sl7_swe_sbuf_empty;
wire sl7_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl7_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl7_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl7_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl7_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl7_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl7_swe_msg;
  wire                    sl7_swe_msg_valid;
wire sl8_swe_sbuf_wr_en;
wire sl8_swe_sbuf_rd_en;
wire sl8_swe_sbuf_rd_vld;
wire sl8_swe_sbuf_full;
wire sl8_swe_sbuf_empty;
wire sl8_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl8_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl8_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl8_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl8_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl8_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl8_swe_msg;
  wire                    sl8_swe_msg_valid;
wire sl9_swe_sbuf_wr_en;
wire sl9_swe_sbuf_rd_en;
wire sl9_swe_sbuf_rd_vld;
wire sl9_swe_sbuf_full;
wire sl9_swe_sbuf_empty;
wire sl9_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl9_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl9_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl9_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl9_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl9_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl9_swe_msg;
  wire                    sl9_swe_msg_valid;
wire sl10_swe_sbuf_wr_en;
wire sl10_swe_sbuf_rd_en;
wire sl10_swe_sbuf_rd_vld;
wire sl10_swe_sbuf_full;
wire sl10_swe_sbuf_empty;
wire sl10_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl10_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl10_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl10_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl10_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl10_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl10_swe_msg;
  wire                    sl10_swe_msg_valid;
wire sl11_swe_sbuf_wr_en;
wire sl11_swe_sbuf_rd_en;
wire sl11_swe_sbuf_rd_vld;
wire sl11_swe_sbuf_full;
wire sl11_swe_sbuf_empty;
wire sl11_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl11_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl11_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl11_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl11_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl11_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl11_swe_msg;
  wire                    sl11_swe_msg_valid;
wire sl12_swe_sbuf_wr_en;
wire sl12_swe_sbuf_rd_en;
wire sl12_swe_sbuf_rd_vld;
wire sl12_swe_sbuf_full;
wire sl12_swe_sbuf_empty;
wire sl12_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl12_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl12_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl12_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl12_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl12_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl12_swe_msg;
  wire                    sl12_swe_msg_valid;
wire sl13_swe_sbuf_wr_en;
wire sl13_swe_sbuf_rd_en;
wire sl13_swe_sbuf_rd_vld;
wire sl13_swe_sbuf_full;
wire sl13_swe_sbuf_empty;
wire sl13_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl13_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl13_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl13_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl13_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl13_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl13_swe_msg;
  wire                    sl13_swe_msg_valid;
wire sl14_swe_sbuf_wr_en;
wire sl14_swe_sbuf_rd_en;
wire sl14_swe_sbuf_rd_vld;
wire sl14_swe_sbuf_full;
wire sl14_swe_sbuf_empty;
wire sl14_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl14_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl14_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl14_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl14_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl14_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl14_swe_msg;
  wire                    sl14_swe_msg_valid;
wire sl15_swe_sbuf_wr_en;
wire sl15_swe_sbuf_rd_en;
wire sl15_swe_sbuf_rd_vld;
wire sl15_swe_sbuf_full;
wire sl15_swe_sbuf_empty;
wire sl15_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl15_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl15_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl15_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl15_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl15_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl15_swe_msg;
  wire                    sl15_swe_msg_valid;
wire sl16_swe_sbuf_wr_en;
wire sl16_swe_sbuf_rd_en;
wire sl16_swe_sbuf_rd_vld;
wire sl16_swe_sbuf_full;
wire sl16_swe_sbuf_empty;
wire sl16_lost;

wire [`npuarc_SWEM_WDT-1:0]                     sl16_swe_sbuf_wr_data;
wire [`npuarc_SWEM_WDT-1:0]                     sl16_swe_sbuf_rd_data;
wire [`npuarc_SWEM_BUF_DEPTH:0]                 sl16_swe_sbuf_num_fill;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl16_swe_sbuf_rd_ptr;
wire [`npuarc_SWEM_BUF_DEPTH-1:0]               sl16_swe_sbuf_wr_ptr;


  wire [`npuarc_SWEM_WDT-1:0]    sl16_swe_msg;
  wire                    sl16_swe_msg_valid;

  wire                     rfm_sbuf_wr_en;
  wire                     rfm_sbuf_rd_en;
  wire                     rfm_sbuf_rd_vld;
  wire [`npuarc_RFM_WDT-1:0]      rfm_sbuf_wr_data;
  wire [`npuarc_RFM_WDT-1:0]      rfm_sbuf_rd_data;
  wire [`npuarc_RFM_BUF_DEPTH-1:0]               rfm_sbuf_rd_ptr;
  wire [`npuarc_RFM_BUF_DEPTH-1:0]               rfm_sbuf_wr_ptr;
  wire                     rfm_sbuf_full;
  wire                     rfm_sbuf_empty;
  wire [`npuarc_RFM_BUF_DEPTH:0]  rfm_sbuf_num_fill;
  wire                     rf_msg_valid;
  wire [`npuarc_RFM_WDT-1:0]      rf_msg;

  wire                     errm_sbuf_wr_en;
  wire                     errm_sbuf_rd_en;
  wire                     errm_sbuf_rd_vld;
  wire [`npuarc_ERRM_WDT-1:0]     errm_sbuf_wr_data;
  wire [`npuarc_ERRM_WDT-1:0]     errm_sbuf_rd_data;
  wire [`npuarc_ERRM_BUF_DEPTH-1:0]              errm_sbuf_rd_ptr;
  wire [`npuarc_ERRM_BUF_DEPTH-1:0]              errm_sbuf_wr_ptr;
  wire                     errm_sbuf_full;
  wire                     errm_sbuf_empty;
  wire [`npuarc_ERRM_BUF_DEPTH:0] errm_sbuf_num_fill;
  wire                     err_msg_valid;
  wire [`npuarc_ERRM_WDT-1:0]     err_msg;

  wire [`npuarc_MSG_TYPE_LOST_WDT-1:0] msg_type_lost_r;
  wire [11:0]              msg_buf_full_sts;
  wire [11:0]              msg_type_recovered;
  wire                     vd_lost1;
  wire                     sbuf_msg_processing;


  wire                    cst_msg_valid;
  wire [`npuarc_CSTM_WDT-1:0]    cst_msg;
  wire [`npuarc_RCODE_WDT-1:0]   rfm_rcode;

  wire cstm_sbuf_wr_en;
  wire cstm_sbuf_rd_en;
  wire cstm_sbuf_rd_vld;
  wire cstm_sbuf_empty;
  wire cstm_sbuf_full;
  wire [`npuarc_CSTM_WDT -1:0] cstm_sbuf_wr_data;
  wire [`npuarc_CSTM_WDT -1:0] cstm_sbuf_rd_data;

  wire [180-1:0] data_in0;
  wire [180-1:0] data_in1;
  wire [180-1:0] data_in2;
  wire [180-1:0] data_in3;
  wire [180-1:0] data_in4;
  wire [180-1:0] data_in5;
  wire [180-1:0] data_in6;
  wire [180-1:0] data_in7;
  wire [180-1:0] data_in8;
  wire [180-1:0] data_in9;
  wire [180-1:0] data_in10;
  wire [180-1:0] data_in11;
  wire [180-1:0] data_in12;
  wire [180-1:0] data_in13;
  wire [180-1:0] data_in14;
  wire [180-1:0] data_in15;
  wire [180-1:0] data_in16;
  wire [180-1:0] data_in17;
  wire [180-1:0] data_in18;
  wire [180-1:0] data_in19;
 wire [20-1:0] sbuf_empty_i;

  wire any_msg_valid;
  wire any_sbuf_wr_en;
  wire sbuf_empty_done;
  wire ptcm_done;


 wire rfm_enable;

 wire [180-1:0] arb_src0, arb_src1, arb_src2;
 wire [2:0] swe_sbuf_ack;
 wire [2:0] arb_val;
 wire [20-1:0] swe_sbuf_rden;
 wire sbarb_done;

 wire  [9-1:0]   msg_seq_order_q_wr_ptr;
 wire  [9-1:0]   msg_seq_order_q_rd_ptr;
 wire  [20-1:0]  msg_seq_order_q_wdata;
 wire  [20-1:0]  msg_seq_order_q_rdata;
 wire            msg_seq_order_q_wr_en;
 wire            msg_seq_order_q_rd_en;
 wire            msg_seq_order_q_empty;
 wire            msg_seq_order_q_full;

 wire para_busy;
 wire arb_busy;

 assign vd_lost1 = sl0_lost
                   || sl1_lost
                   || sl2_lost
                   || sl3_lost
                   || sl4_lost
                   || sl5_lost
                   || sl6_lost
                   || sl7_lost
                   || sl8_lost
                   || sl9_lost
                   || sl10_lost
                   || sl11_lost
                   || sl12_lost
                   || sl13_lost
                   || sl14_lost
                   || sl15_lost
                   || sl16_lost
                   ;

 assign msg_buf_full_sts = {6'b0,vd_lost1,5'b0};
 assign msg_type_recovered = {6'b0,1'b1,5'b0};

 assign arb_busy = |arb_val;
 assign encapsulation_top_busy =
                                 flush_cmd ||
                                 any_msg_valid || (~sbuf_empty_done) ||
                                 arb_busy || para_busy;


assign any_sbuf_wr_en =
                         sl0_swe_sbuf_wr_en ||
                         sl1_swe_sbuf_wr_en ||
                         sl2_swe_sbuf_wr_en ||
                         sl3_swe_sbuf_wr_en ||
                         sl4_swe_sbuf_wr_en ||
                         sl5_swe_sbuf_wr_en ||
                         sl6_swe_sbuf_wr_en ||
                         sl7_swe_sbuf_wr_en ||
                         sl8_swe_sbuf_wr_en ||
                         sl9_swe_sbuf_wr_en ||
                         sl10_swe_sbuf_wr_en ||
                         sl11_swe_sbuf_wr_en ||
                         sl12_swe_sbuf_wr_en ||
                         sl13_swe_sbuf_wr_en ||
                         sl14_swe_sbuf_wr_en ||
                         sl15_swe_sbuf_wr_en ||
                         sl16_swe_sbuf_wr_en ||
                         cstm_sbuf_wr_en ||
                         errm_sbuf_wr_en || rfm_sbuf_wr_en;

assign any_msg_valid =
                         sl0_swe_msg_valid ||
                         sl1_swe_msg_valid ||
                         sl2_swe_msg_valid ||
                         sl3_swe_msg_valid ||
                         sl4_swe_msg_valid ||
                         sl5_swe_msg_valid ||
                         sl6_swe_msg_valid ||
                         sl7_swe_msg_valid ||
                         sl8_swe_msg_valid ||
                         sl9_swe_msg_valid ||
                         sl10_swe_msg_valid ||
                         sl11_swe_msg_valid ||
                         sl12_swe_msg_valid ||
                         sl13_swe_msg_valid ||
                         sl14_swe_msg_valid ||
                         sl15_swe_msg_valid ||
                         sl16_swe_msg_valid ||
                         cst_msg_valid ||
                         err_msg_valid || rf_msg_valid;

assign sbuf_empty_i =   {
                         cstm_sbuf_empty,
                         sl16_swe_sbuf_empty,
                         sl15_swe_sbuf_empty,
                         sl14_swe_sbuf_empty,
                         sl13_swe_sbuf_empty,
                         sl12_swe_sbuf_empty,
                         sl11_swe_sbuf_empty,
                         sl10_swe_sbuf_empty,
                         sl9_swe_sbuf_empty,
                         sl8_swe_sbuf_empty,
                         sl7_swe_sbuf_empty,
                         sl6_swe_sbuf_empty,
                         sl5_swe_sbuf_empty,
                         sl4_swe_sbuf_empty,
                         sl3_swe_sbuf_empty,
                         sl2_swe_sbuf_empty,
                         sl1_swe_sbuf_empty,
                         sl0_swe_sbuf_empty,
                         errm_sbuf_empty,rfm_sbuf_empty};

assign sbuf_empty =
                         sl0_swe_sbuf_empty &&
                         sl1_swe_sbuf_empty &&
                         sl2_swe_sbuf_empty &&
                         sl3_swe_sbuf_empty &&
                         sl4_swe_sbuf_empty &&
                         sl5_swe_sbuf_empty &&
                         sl6_swe_sbuf_empty &&
                         sl7_swe_sbuf_empty &&
                         sl8_swe_sbuf_empty &&
                         sl9_swe_sbuf_empty &&
                         sl10_swe_sbuf_empty &&
                         sl11_swe_sbuf_empty &&
                         sl12_swe_sbuf_empty &&
                         sl13_swe_sbuf_empty &&
                         sl14_swe_sbuf_empty &&
                         sl15_swe_sbuf_empty &&
                         sl16_swe_sbuf_empty &&
                         cstm_sbuf_empty &&
                         errm_sbuf_empty && rfm_sbuf_empty;

assign sbuf_empty_done = sbuf_empty && (~p0_req);

assign sbuf_msg_processing =
                         sl0_swe_sbuf_rd_vld ||
                         sl1_swe_sbuf_rd_vld ||
                         sl2_swe_sbuf_rd_vld ||
                         sl3_swe_sbuf_rd_vld ||
                         sl4_swe_sbuf_rd_vld ||
                         sl5_swe_sbuf_rd_vld ||
                         sl6_swe_sbuf_rd_vld ||
                         sl7_swe_sbuf_rd_vld ||
                         sl8_swe_sbuf_rd_vld ||
                         sl9_swe_sbuf_rd_vld ||
                         sl10_swe_sbuf_rd_vld ||
                         sl11_swe_sbuf_rd_vld ||
                         sl12_swe_sbuf_rd_vld ||
                         sl13_swe_sbuf_rd_vld ||
                         sl14_swe_sbuf_rd_vld ||
                         sl15_swe_sbuf_rd_vld ||
                         sl16_swe_sbuf_rd_vld ||
                         cstm_sbuf_rd_vld ||
                         errm_sbuf_rd_vld || rfm_sbuf_rd_vld;

assign ptcm_done = sbuf_empty_done && (~sbuf_msg_processing); // && ptc_msg_valid_r;



assign rfm_enable = |swe_pr_sel;

npuarc_rtt_swe_rfm_encapsulation u_rtt_swe_rfm_encapsulation(
.rfm_en(rfm_enable),
.rtt_time_stamp_en(rtt_time_stamp_en),
.timestamp(time_stamp),
.rcode(rfm_rcode),
.rf_msg_valid(rf_msg_valid),
.rf_msg(rf_msg)
);

// spyglass disable_block UnloadedOutTerm-ML
// MD: msg_type_lost_r design reuse
npuarc_rtt_errm_encapsulation u_rtt_swe_errm_encapsulation (

.rtt_clk(rtt_clk),

.sys_reset(rst_a),
.pr_num(6'd1),
.msg_type_lost(msg_buf_full_sts),
.msg_type_lost_r(msg_type_lost_r),
.msg_type_recovered(msg_type_recovered),
.timestamp(time_stamp),
.err_msg_valid(err_msg_valid),
.err_msg(err_msg)
);
// spyglass enable_block UnloadedOutTerm-ML

assign rfm_sbuf_wr_en = rf_msg_valid && (~rfm_sbuf_full);
assign rfm_sbuf_wr_data = rf_msg;
assign rfm_sbuf_rd_en = swe_sbuf_rden[0];

assign errm_sbuf_wr_en = err_msg_valid && (~errm_sbuf_full);
assign errm_sbuf_wr_data = err_msg;
assign errm_sbuf_rd_en = swe_sbuf_rden[1];

///////////////////////////
//     RFM
//////////////////////////
npuarc_rtt_rfm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_RFM_WDT),
       .FIFO_SIZE(`npuarc_RFM_BUF_DEPTH)
      )
u_rfm_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(rfm_sbuf_wr_en),
.rd_en(rfm_sbuf_rd_en),
.rd_vld(rfm_sbuf_rd_vld),

.rd_ptr(rfm_sbuf_rd_ptr),
.wr_ptr(rfm_sbuf_wr_ptr),
.full(rfm_sbuf_full),
.empty(rfm_sbuf_empty),
.num_fill(rfm_sbuf_num_fill)
);

npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_RFM_WDT ),
       .FIFO_SIZE(`npuarc_RFM_BUF_DEPTH)
      )
u_rfm_array_17 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(rfm_sbuf_wr_en),
.rd_en(rfm_sbuf_rd_en),
.wr_data(rfm_sbuf_wr_data),
.rd_data(rfm_sbuf_rd_data),
.wr_ptr(rfm_sbuf_wr_ptr),
.rd_ptr(rfm_sbuf_rd_ptr)

);

assign data_in0 = {{(180-(`npuarc_RFM_WDT)){1'b0}},rfm_sbuf_rd_data[`npuarc_RFM_WDT-1:0]};

///////////////////////////
//     ERRM
//////////////////////////
npuarc_rtt_errm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_ERRM_WDT),
       .FIFO_SIZE(`npuarc_ERRM_BUF_DEPTH)
      )
u_errm_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(errm_sbuf_wr_en),
.rd_en(errm_sbuf_rd_en),
.rd_vld(errm_sbuf_rd_vld),

.rd_ptr(errm_sbuf_rd_ptr),
.wr_ptr(errm_sbuf_wr_ptr),
.full(errm_sbuf_full),
.empty(errm_sbuf_empty),
.num_fill(errm_sbuf_num_fill)
);

npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_ERRM_WDT ),
       .FIFO_SIZE(`npuarc_ERRM_BUF_DEPTH)
      )
u_errm_array_17 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(errm_sbuf_wr_en),
.rd_en(errm_sbuf_rd_en),
.wr_data(errm_sbuf_wr_data),
.rd_data(errm_sbuf_rd_data),
.wr_ptr(errm_sbuf_wr_ptr),
.rd_ptr(errm_sbuf_rd_ptr)

);

assign data_in1 = {{(180-(`npuarc_ERRM_WDT)){1'b0}},errm_sbuf_rd_data[`npuarc_ERRM_WDT-1:0]};




assign sl0_swe_sbuf_rd_en = swe_sbuf_rden[2];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl0_swe_encapsulation (
.p0_msg_en(swe_pr_sel[0]),
.ext_num(sl0_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl0_alt_rtt_swe_val),
.datain (sl0_alt_rtt_swe_data),

.msg_valid(sl0_swe_msg_valid),
.msg(sl0_swe_msg)
);


assign sl0_swe_sbuf_wr_data = sl0_swe_msg;
assign sl0_swe_sbuf_wr_en = sl0_swe_msg_valid && (~sl0_swe_sbuf_full);
assign sl0_lost = (sl0_swe_msg_valid && sl0_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl0rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl0_swe_sbuf_wr_en),
.rd_en(sl0_swe_sbuf_rd_en),
.rd_vld(sl0_swe_sbuf_rd_vld),

.wr_ptr(sl0_swe_sbuf_wr_ptr),
.rd_ptr(sl0_swe_sbuf_rd_ptr),
.full(sl0_swe_sbuf_full),
.empty(sl0_swe_sbuf_empty),
.num_fill(sl0_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_0 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl0_swe_sbuf_wr_en),
.rd_en(sl0_swe_sbuf_rd_en),
.wr_data(sl0_swe_sbuf_wr_data),
.rd_data(sl0_swe_sbuf_rd_data),
.wr_ptr(sl0_swe_sbuf_wr_ptr),
.rd_ptr(sl0_swe_sbuf_rd_ptr)
);

assign data_in2 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl0_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl1_swe_sbuf_rd_en = swe_sbuf_rden[3];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl1_swe_encapsulation (
.p0_msg_en(swe_pr_sel[1]),
.ext_num(sl1_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl1_alt_rtt_swe_val),
.datain (sl1_alt_rtt_swe_data),

.msg_valid(sl1_swe_msg_valid),
.msg(sl1_swe_msg)
);


assign sl1_swe_sbuf_wr_data = sl1_swe_msg;
assign sl1_swe_sbuf_wr_en = sl1_swe_msg_valid && (~sl1_swe_sbuf_full);
assign sl1_lost = (sl1_swe_msg_valid && sl1_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl1rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl1_swe_sbuf_wr_en),
.rd_en(sl1_swe_sbuf_rd_en),
.rd_vld(sl1_swe_sbuf_rd_vld),

.wr_ptr(sl1_swe_sbuf_wr_ptr),
.rd_ptr(sl1_swe_sbuf_rd_ptr),
.full(sl1_swe_sbuf_full),
.empty(sl1_swe_sbuf_empty),
.num_fill(sl1_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_1 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl1_swe_sbuf_wr_en),
.rd_en(sl1_swe_sbuf_rd_en),
.wr_data(sl1_swe_sbuf_wr_data),
.rd_data(sl1_swe_sbuf_rd_data),
.wr_ptr(sl1_swe_sbuf_wr_ptr),
.rd_ptr(sl1_swe_sbuf_rd_ptr)
);

assign data_in3 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl1_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl2_swe_sbuf_rd_en = swe_sbuf_rden[4];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl2_swe_encapsulation (
.p0_msg_en(swe_pr_sel[2]),
.ext_num(sl2_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl2_alt_rtt_swe_val),
.datain (sl2_alt_rtt_swe_data),

.msg_valid(sl2_swe_msg_valid),
.msg(sl2_swe_msg)
);


assign sl2_swe_sbuf_wr_data = sl2_swe_msg;
assign sl2_swe_sbuf_wr_en = sl2_swe_msg_valid && (~sl2_swe_sbuf_full);
assign sl2_lost = (sl2_swe_msg_valid && sl2_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl2rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl2_swe_sbuf_wr_en),
.rd_en(sl2_swe_sbuf_rd_en),
.rd_vld(sl2_swe_sbuf_rd_vld),

.wr_ptr(sl2_swe_sbuf_wr_ptr),
.rd_ptr(sl2_swe_sbuf_rd_ptr),
.full(sl2_swe_sbuf_full),
.empty(sl2_swe_sbuf_empty),
.num_fill(sl2_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_2 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl2_swe_sbuf_wr_en),
.rd_en(sl2_swe_sbuf_rd_en),
.wr_data(sl2_swe_sbuf_wr_data),
.rd_data(sl2_swe_sbuf_rd_data),
.wr_ptr(sl2_swe_sbuf_wr_ptr),
.rd_ptr(sl2_swe_sbuf_rd_ptr)
);

assign data_in4 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl2_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl3_swe_sbuf_rd_en = swe_sbuf_rden[5];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl3_swe_encapsulation (
.p0_msg_en(swe_pr_sel[3]),
.ext_num(sl3_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl3_alt_rtt_swe_val),
.datain (sl3_alt_rtt_swe_data),

.msg_valid(sl3_swe_msg_valid),
.msg(sl3_swe_msg)
);


assign sl3_swe_sbuf_wr_data = sl3_swe_msg;
assign sl3_swe_sbuf_wr_en = sl3_swe_msg_valid && (~sl3_swe_sbuf_full);
assign sl3_lost = (sl3_swe_msg_valid && sl3_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl3rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl3_swe_sbuf_wr_en),
.rd_en(sl3_swe_sbuf_rd_en),
.rd_vld(sl3_swe_sbuf_rd_vld),

.wr_ptr(sl3_swe_sbuf_wr_ptr),
.rd_ptr(sl3_swe_sbuf_rd_ptr),
.full(sl3_swe_sbuf_full),
.empty(sl3_swe_sbuf_empty),
.num_fill(sl3_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_3 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl3_swe_sbuf_wr_en),
.rd_en(sl3_swe_sbuf_rd_en),
.wr_data(sl3_swe_sbuf_wr_data),
.rd_data(sl3_swe_sbuf_rd_data),
.wr_ptr(sl3_swe_sbuf_wr_ptr),
.rd_ptr(sl3_swe_sbuf_rd_ptr)
);

assign data_in5 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl3_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl4_swe_sbuf_rd_en = swe_sbuf_rden[6];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl4_swe_encapsulation (
.p0_msg_en(swe_pr_sel[4]),
.ext_num(sl4_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl4_alt_rtt_swe_val),
.datain (sl4_alt_rtt_swe_data),

.msg_valid(sl4_swe_msg_valid),
.msg(sl4_swe_msg)
);


assign sl4_swe_sbuf_wr_data = sl4_swe_msg;
assign sl4_swe_sbuf_wr_en = sl4_swe_msg_valid && (~sl4_swe_sbuf_full);
assign sl4_lost = (sl4_swe_msg_valid && sl4_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl4rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl4_swe_sbuf_wr_en),
.rd_en(sl4_swe_sbuf_rd_en),
.rd_vld(sl4_swe_sbuf_rd_vld),

.wr_ptr(sl4_swe_sbuf_wr_ptr),
.rd_ptr(sl4_swe_sbuf_rd_ptr),
.full(sl4_swe_sbuf_full),
.empty(sl4_swe_sbuf_empty),
.num_fill(sl4_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_4 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl4_swe_sbuf_wr_en),
.rd_en(sl4_swe_sbuf_rd_en),
.wr_data(sl4_swe_sbuf_wr_data),
.rd_data(sl4_swe_sbuf_rd_data),
.wr_ptr(sl4_swe_sbuf_wr_ptr),
.rd_ptr(sl4_swe_sbuf_rd_ptr)
);

assign data_in6 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl4_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl5_swe_sbuf_rd_en = swe_sbuf_rden[7];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl5_swe_encapsulation (
.p0_msg_en(swe_pr_sel[5]),
.ext_num(sl5_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl5_alt_rtt_swe_val),
.datain (sl5_alt_rtt_swe_data),

.msg_valid(sl5_swe_msg_valid),
.msg(sl5_swe_msg)
);


assign sl5_swe_sbuf_wr_data = sl5_swe_msg;
assign sl5_swe_sbuf_wr_en = sl5_swe_msg_valid && (~sl5_swe_sbuf_full);
assign sl5_lost = (sl5_swe_msg_valid && sl5_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl5rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl5_swe_sbuf_wr_en),
.rd_en(sl5_swe_sbuf_rd_en),
.rd_vld(sl5_swe_sbuf_rd_vld),

.wr_ptr(sl5_swe_sbuf_wr_ptr),
.rd_ptr(sl5_swe_sbuf_rd_ptr),
.full(sl5_swe_sbuf_full),
.empty(sl5_swe_sbuf_empty),
.num_fill(sl5_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_5 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl5_swe_sbuf_wr_en),
.rd_en(sl5_swe_sbuf_rd_en),
.wr_data(sl5_swe_sbuf_wr_data),
.rd_data(sl5_swe_sbuf_rd_data),
.wr_ptr(sl5_swe_sbuf_wr_ptr),
.rd_ptr(sl5_swe_sbuf_rd_ptr)
);

assign data_in7 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl5_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl6_swe_sbuf_rd_en = swe_sbuf_rden[8];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl6_swe_encapsulation (
.p0_msg_en(swe_pr_sel[6]),
.ext_num(sl6_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl6_alt_rtt_swe_val),
.datain (sl6_alt_rtt_swe_data),

.msg_valid(sl6_swe_msg_valid),
.msg(sl6_swe_msg)
);


assign sl6_swe_sbuf_wr_data = sl6_swe_msg;
assign sl6_swe_sbuf_wr_en = sl6_swe_msg_valid && (~sl6_swe_sbuf_full);
assign sl6_lost = (sl6_swe_msg_valid && sl6_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl6rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl6_swe_sbuf_wr_en),
.rd_en(sl6_swe_sbuf_rd_en),
.rd_vld(sl6_swe_sbuf_rd_vld),

.wr_ptr(sl6_swe_sbuf_wr_ptr),
.rd_ptr(sl6_swe_sbuf_rd_ptr),
.full(sl6_swe_sbuf_full),
.empty(sl6_swe_sbuf_empty),
.num_fill(sl6_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_6 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl6_swe_sbuf_wr_en),
.rd_en(sl6_swe_sbuf_rd_en),
.wr_data(sl6_swe_sbuf_wr_data),
.rd_data(sl6_swe_sbuf_rd_data),
.wr_ptr(sl6_swe_sbuf_wr_ptr),
.rd_ptr(sl6_swe_sbuf_rd_ptr)
);

assign data_in8 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl6_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl7_swe_sbuf_rd_en = swe_sbuf_rden[9];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl7_swe_encapsulation (
.p0_msg_en(swe_pr_sel[7]),
.ext_num(sl7_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl7_alt_rtt_swe_val),
.datain (sl7_alt_rtt_swe_data),

.msg_valid(sl7_swe_msg_valid),
.msg(sl7_swe_msg)
);


assign sl7_swe_sbuf_wr_data = sl7_swe_msg;
assign sl7_swe_sbuf_wr_en = sl7_swe_msg_valid && (~sl7_swe_sbuf_full);
assign sl7_lost = (sl7_swe_msg_valid && sl7_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl7rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl7_swe_sbuf_wr_en),
.rd_en(sl7_swe_sbuf_rd_en),
.rd_vld(sl7_swe_sbuf_rd_vld),

.wr_ptr(sl7_swe_sbuf_wr_ptr),
.rd_ptr(sl7_swe_sbuf_rd_ptr),
.full(sl7_swe_sbuf_full),
.empty(sl7_swe_sbuf_empty),
.num_fill(sl7_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_7 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl7_swe_sbuf_wr_en),
.rd_en(sl7_swe_sbuf_rd_en),
.wr_data(sl7_swe_sbuf_wr_data),
.rd_data(sl7_swe_sbuf_rd_data),
.wr_ptr(sl7_swe_sbuf_wr_ptr),
.rd_ptr(sl7_swe_sbuf_rd_ptr)
);

assign data_in9 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl7_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl8_swe_sbuf_rd_en = swe_sbuf_rden[10];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl8_swe_encapsulation (
.p0_msg_en(swe_pr_sel[8]),
.ext_num(sl8_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl8_alt_rtt_swe_val),
.datain (sl8_alt_rtt_swe_data),

.msg_valid(sl8_swe_msg_valid),
.msg(sl8_swe_msg)
);


assign sl8_swe_sbuf_wr_data = sl8_swe_msg;
assign sl8_swe_sbuf_wr_en = sl8_swe_msg_valid && (~sl8_swe_sbuf_full);
assign sl8_lost = (sl8_swe_msg_valid && sl8_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl8rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl8_swe_sbuf_wr_en),
.rd_en(sl8_swe_sbuf_rd_en),
.rd_vld(sl8_swe_sbuf_rd_vld),

.wr_ptr(sl8_swe_sbuf_wr_ptr),
.rd_ptr(sl8_swe_sbuf_rd_ptr),
.full(sl8_swe_sbuf_full),
.empty(sl8_swe_sbuf_empty),
.num_fill(sl8_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_8 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl8_swe_sbuf_wr_en),
.rd_en(sl8_swe_sbuf_rd_en),
.wr_data(sl8_swe_sbuf_wr_data),
.rd_data(sl8_swe_sbuf_rd_data),
.wr_ptr(sl8_swe_sbuf_wr_ptr),
.rd_ptr(sl8_swe_sbuf_rd_ptr)
);

assign data_in10 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl8_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl9_swe_sbuf_rd_en = swe_sbuf_rden[11];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl9_swe_encapsulation (
.p0_msg_en(swe_pr_sel[9]),
.ext_num(sl9_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl9_alt_rtt_swe_val),
.datain (sl9_alt_rtt_swe_data),

.msg_valid(sl9_swe_msg_valid),
.msg(sl9_swe_msg)
);


assign sl9_swe_sbuf_wr_data = sl9_swe_msg;
assign sl9_swe_sbuf_wr_en = sl9_swe_msg_valid && (~sl9_swe_sbuf_full);
assign sl9_lost = (sl9_swe_msg_valid && sl9_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl9rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl9_swe_sbuf_wr_en),
.rd_en(sl9_swe_sbuf_rd_en),
.rd_vld(sl9_swe_sbuf_rd_vld),

.wr_ptr(sl9_swe_sbuf_wr_ptr),
.rd_ptr(sl9_swe_sbuf_rd_ptr),
.full(sl9_swe_sbuf_full),
.empty(sl9_swe_sbuf_empty),
.num_fill(sl9_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_9 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl9_swe_sbuf_wr_en),
.rd_en(sl9_swe_sbuf_rd_en),
.wr_data(sl9_swe_sbuf_wr_data),
.rd_data(sl9_swe_sbuf_rd_data),
.wr_ptr(sl9_swe_sbuf_wr_ptr),
.rd_ptr(sl9_swe_sbuf_rd_ptr)
);

assign data_in11 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl9_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl10_swe_sbuf_rd_en = swe_sbuf_rden[12];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl10_swe_encapsulation (
.p0_msg_en(swe_pr_sel[10]),
.ext_num(sl10_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl10_alt_rtt_swe_val),
.datain (sl10_alt_rtt_swe_data),

.msg_valid(sl10_swe_msg_valid),
.msg(sl10_swe_msg)
);


assign sl10_swe_sbuf_wr_data = sl10_swe_msg;
assign sl10_swe_sbuf_wr_en = sl10_swe_msg_valid && (~sl10_swe_sbuf_full);
assign sl10_lost = (sl10_swe_msg_valid && sl10_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl10rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl10_swe_sbuf_wr_en),
.rd_en(sl10_swe_sbuf_rd_en),
.rd_vld(sl10_swe_sbuf_rd_vld),

.wr_ptr(sl10_swe_sbuf_wr_ptr),
.rd_ptr(sl10_swe_sbuf_rd_ptr),
.full(sl10_swe_sbuf_full),
.empty(sl10_swe_sbuf_empty),
.num_fill(sl10_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_10 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl10_swe_sbuf_wr_en),
.rd_en(sl10_swe_sbuf_rd_en),
.wr_data(sl10_swe_sbuf_wr_data),
.rd_data(sl10_swe_sbuf_rd_data),
.wr_ptr(sl10_swe_sbuf_wr_ptr),
.rd_ptr(sl10_swe_sbuf_rd_ptr)
);

assign data_in12 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl10_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl11_swe_sbuf_rd_en = swe_sbuf_rden[13];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl11_swe_encapsulation (
.p0_msg_en(swe_pr_sel[11]),
.ext_num(sl11_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl11_alt_rtt_swe_val),
.datain (sl11_alt_rtt_swe_data),

.msg_valid(sl11_swe_msg_valid),
.msg(sl11_swe_msg)
);


assign sl11_swe_sbuf_wr_data = sl11_swe_msg;
assign sl11_swe_sbuf_wr_en = sl11_swe_msg_valid && (~sl11_swe_sbuf_full);
assign sl11_lost = (sl11_swe_msg_valid && sl11_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl11rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl11_swe_sbuf_wr_en),
.rd_en(sl11_swe_sbuf_rd_en),
.rd_vld(sl11_swe_sbuf_rd_vld),

.wr_ptr(sl11_swe_sbuf_wr_ptr),
.rd_ptr(sl11_swe_sbuf_rd_ptr),
.full(sl11_swe_sbuf_full),
.empty(sl11_swe_sbuf_empty),
.num_fill(sl11_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_11 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl11_swe_sbuf_wr_en),
.rd_en(sl11_swe_sbuf_rd_en),
.wr_data(sl11_swe_sbuf_wr_data),
.rd_data(sl11_swe_sbuf_rd_data),
.wr_ptr(sl11_swe_sbuf_wr_ptr),
.rd_ptr(sl11_swe_sbuf_rd_ptr)
);

assign data_in13 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl11_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl12_swe_sbuf_rd_en = swe_sbuf_rden[14];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl12_swe_encapsulation (
.p0_msg_en(swe_pr_sel[12]),
.ext_num(sl12_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl12_alt_rtt_swe_val),
.datain (sl12_alt_rtt_swe_data),

.msg_valid(sl12_swe_msg_valid),
.msg(sl12_swe_msg)
);


assign sl12_swe_sbuf_wr_data = sl12_swe_msg;
assign sl12_swe_sbuf_wr_en = sl12_swe_msg_valid && (~sl12_swe_sbuf_full);
assign sl12_lost = (sl12_swe_msg_valid && sl12_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl12rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl12_swe_sbuf_wr_en),
.rd_en(sl12_swe_sbuf_rd_en),
.rd_vld(sl12_swe_sbuf_rd_vld),

.wr_ptr(sl12_swe_sbuf_wr_ptr),
.rd_ptr(sl12_swe_sbuf_rd_ptr),
.full(sl12_swe_sbuf_full),
.empty(sl12_swe_sbuf_empty),
.num_fill(sl12_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_12 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl12_swe_sbuf_wr_en),
.rd_en(sl12_swe_sbuf_rd_en),
.wr_data(sl12_swe_sbuf_wr_data),
.rd_data(sl12_swe_sbuf_rd_data),
.wr_ptr(sl12_swe_sbuf_wr_ptr),
.rd_ptr(sl12_swe_sbuf_rd_ptr)
);

assign data_in14 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl12_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl13_swe_sbuf_rd_en = swe_sbuf_rden[15];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl13_swe_encapsulation (
.p0_msg_en(swe_pr_sel[13]),
.ext_num(sl13_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl13_alt_rtt_swe_val),
.datain (sl13_alt_rtt_swe_data),

.msg_valid(sl13_swe_msg_valid),
.msg(sl13_swe_msg)
);


assign sl13_swe_sbuf_wr_data = sl13_swe_msg;
assign sl13_swe_sbuf_wr_en = sl13_swe_msg_valid && (~sl13_swe_sbuf_full);
assign sl13_lost = (sl13_swe_msg_valid && sl13_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl13rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl13_swe_sbuf_wr_en),
.rd_en(sl13_swe_sbuf_rd_en),
.rd_vld(sl13_swe_sbuf_rd_vld),

.wr_ptr(sl13_swe_sbuf_wr_ptr),
.rd_ptr(sl13_swe_sbuf_rd_ptr),
.full(sl13_swe_sbuf_full),
.empty(sl13_swe_sbuf_empty),
.num_fill(sl13_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_13 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl13_swe_sbuf_wr_en),
.rd_en(sl13_swe_sbuf_rd_en),
.wr_data(sl13_swe_sbuf_wr_data),
.rd_data(sl13_swe_sbuf_rd_data),
.wr_ptr(sl13_swe_sbuf_wr_ptr),
.rd_ptr(sl13_swe_sbuf_rd_ptr)
);

assign data_in15 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl13_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl14_swe_sbuf_rd_en = swe_sbuf_rden[16];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl14_swe_encapsulation (
.p0_msg_en(swe_pr_sel[14]),
.ext_num(sl14_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl14_alt_rtt_swe_val),
.datain (sl14_alt_rtt_swe_data),

.msg_valid(sl14_swe_msg_valid),
.msg(sl14_swe_msg)
);


assign sl14_swe_sbuf_wr_data = sl14_swe_msg;
assign sl14_swe_sbuf_wr_en = sl14_swe_msg_valid && (~sl14_swe_sbuf_full);
assign sl14_lost = (sl14_swe_msg_valid && sl14_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl14rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl14_swe_sbuf_wr_en),
.rd_en(sl14_swe_sbuf_rd_en),
.rd_vld(sl14_swe_sbuf_rd_vld),

.wr_ptr(sl14_swe_sbuf_wr_ptr),
.rd_ptr(sl14_swe_sbuf_rd_ptr),
.full(sl14_swe_sbuf_full),
.empty(sl14_swe_sbuf_empty),
.num_fill(sl14_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_14 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl14_swe_sbuf_wr_en),
.rd_en(sl14_swe_sbuf_rd_en),
.wr_data(sl14_swe_sbuf_wr_data),
.rd_data(sl14_swe_sbuf_rd_data),
.wr_ptr(sl14_swe_sbuf_wr_ptr),
.rd_ptr(sl14_swe_sbuf_rd_ptr)
);

assign data_in16 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl14_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl15_swe_sbuf_rd_en = swe_sbuf_rden[17];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl15_swe_encapsulation (
.p0_msg_en(swe_pr_sel[15]),
.ext_num(sl15_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl15_alt_rtt_swe_val),
.datain (sl15_alt_rtt_swe_data),

.msg_valid(sl15_swe_msg_valid),
.msg(sl15_swe_msg)
);


assign sl15_swe_sbuf_wr_data = sl15_swe_msg;
assign sl15_swe_sbuf_wr_en = sl15_swe_msg_valid && (~sl15_swe_sbuf_full);
assign sl15_lost = (sl15_swe_msg_valid && sl15_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl15rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl15_swe_sbuf_wr_en),
.rd_en(sl15_swe_sbuf_rd_en),
.rd_vld(sl15_swe_sbuf_rd_vld),

.wr_ptr(sl15_swe_sbuf_wr_ptr),
.rd_ptr(sl15_swe_sbuf_rd_ptr),
.full(sl15_swe_sbuf_full),
.empty(sl15_swe_sbuf_empty),
.num_fill(sl15_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_15 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl15_swe_sbuf_wr_en),
.rd_en(sl15_swe_sbuf_rd_en),
.wr_data(sl15_swe_sbuf_wr_data),
.rd_data(sl15_swe_sbuf_rd_data),
.wr_ptr(sl15_swe_sbuf_wr_ptr),
.rd_ptr(sl15_swe_sbuf_rd_ptr)
);

assign data_in17 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl15_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

assign sl16_swe_sbuf_rd_en = swe_sbuf_rden[18];
npuarc_rtt_swe_daqm_encapsulation u_rtt_sl16_swe_encapsulation (
.p0_msg_en(swe_pr_sel[16]),
.ext_num(sl16_alt_rtt_swe_ext),
.timestamp(time_stamp),
.datain_val(sl16_alt_rtt_swe_val),
.datain (sl16_alt_rtt_swe_data),

.msg_valid(sl16_swe_msg_valid),
.msg(sl16_swe_msg)
);


assign sl16_swe_sbuf_wr_data = sl16_swe_msg;
assign sl16_swe_sbuf_wr_en = sl16_swe_msg_valid && (~sl16_swe_sbuf_full);
assign sl16_lost = (sl16_swe_msg_valid && sl16_swe_sbuf_full);
npuarc_rtt_daqm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_sl16rtt_daqm_swe_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl16_swe_sbuf_wr_en),
.rd_en(sl16_swe_sbuf_rd_en),
.rd_vld(sl16_swe_sbuf_rd_vld),

.wr_ptr(sl16_swe_sbuf_wr_ptr),
.rd_ptr(sl16_swe_sbuf_rd_ptr),
.full(sl16_swe_sbuf_full),
.empty(sl16_swe_sbuf_empty),
.num_fill(sl16_swe_sbuf_num_fill)
);

///////////////////////////
//     SWEM
//////////////////////////
npuarc_rtt_sbuf_array
#(
       .FIFO_DATA_WIDTH(`npuarc_SWEM_WDT ),
       .FIFO_SIZE(`npuarc_SWEM_BUF_DEPTH)
      )
u_swe_array_16 (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(sl16_swe_sbuf_wr_en),
.rd_en(sl16_swe_sbuf_rd_en),
.wr_data(sl16_swe_sbuf_wr_data),
.rd_data(sl16_swe_sbuf_rd_data),
.wr_ptr(sl16_swe_sbuf_wr_ptr),
.rd_ptr(sl16_swe_sbuf_rd_ptr)
);

assign data_in18 = {{(180-(`npuarc_SWEM_WDT)){1'b0}},sl16_swe_sbuf_rd_data[`npuarc_SWEM_WDT-1:0]};

///////////////////////////
//     SYTM
//////////////////////////

assign cstm_sbuf_wr_data = cst_msg;
assign cstm_sbuf_wr_en = cst_msg_valid && ((cstm_sbuf_rd_en && cstm_sbuf_full) || cstm_sbuf_empty);
assign cstm_sbuf_full = ~cstm_sbuf_empty;
assign cstm_sbuf_rd_en = swe_sbuf_rden[19];

npuarc_rtt_swe_cstm_encapsulation u_rtt_cstm_encapsulation(
.cstm_en(swe_csts_en),
.atb_syncreq(atb_syncreq),
.p0_csts_en(|swe_pr_sel),
.resource_full(rf_msg_valid),
.rfm_rcode(rfm_rcode),
.timestamp(time_stamp),
.cstimestamp(cstimestamp),

.cst_msg_valid(cst_msg_valid),
.cst_msg(cst_msg)
);

npuarc_rtt_cstm_sbuf #(
               .FIFO_DATA_WIDTH(`npuarc_CSTM_WDT ),
               .FIFO_SIZE(`npuarc_CSTM_BUF_DEPTH)
               ) u_cstm_source_buf (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(cstm_sbuf_wr_en),
.rd_en(cstm_sbuf_rd_en),
.rd_vld(cstm_sbuf_rd_vld),
.wr_data(cstm_sbuf_wr_data),

.rd_data(cstm_sbuf_rd_data),
.empty(cstm_sbuf_empty)
);
assign data_in19 = {{(180-(`npuarc_CSTM_WDT)){1'b0}},cstm_sbuf_rd_data[`npuarc_CSTM_WDT -1:0]};

assign msg_seq_order_q_wr_en = any_sbuf_wr_en && (~msg_seq_order_q_full); 
assign msg_seq_order_q_wdata = {
                                cstm_sbuf_wr_en,
                                sl16_swe_sbuf_wr_en,
                                sl15_swe_sbuf_wr_en,
                                sl14_swe_sbuf_wr_en,
                                sl13_swe_sbuf_wr_en,
                                sl12_swe_sbuf_wr_en,
                                sl11_swe_sbuf_wr_en,
                                sl10_swe_sbuf_wr_en,
                                sl9_swe_sbuf_wr_en,
                                sl8_swe_sbuf_wr_en,
                                sl7_swe_sbuf_wr_en,
                                sl6_swe_sbuf_wr_en,
                                sl5_swe_sbuf_wr_en,
                                sl4_swe_sbuf_wr_en,
                                sl3_swe_sbuf_wr_en,
                                sl2_swe_sbuf_wr_en,
                                sl1_swe_sbuf_wr_en,
                                sl0_swe_sbuf_wr_en,
                                errm_sbuf_wr_en,rfm_sbuf_wr_en};

npuarc_rtt_swe_msg_seq_queue u_rtt_swe_msg_seq_queue (
         .rtt_clk  (rtt_clk),
         .rst_a    (rst_a),
         .wr_en    (msg_seq_order_q_wr_en),
         .rd_en    (msg_seq_order_q_rd_en & ~msg_seq_order_q_empty),
         .wr_data  (msg_seq_order_q_wdata),
         .rd_data  (msg_seq_order_q_rdata),
         .wr_ptr   (msg_seq_order_q_wr_ptr),
         .rd_ptr   (msg_seq_order_q_rd_ptr),
         .empty    (msg_seq_order_q_empty),
         .full     (msg_seq_order_q_full)
         );


// spyglass disable_block UnloadedOutTerm-ML
npuarc_rtt_swe_source_buf_arbitrator u_rtt_swe_source_buf_arbitrator (
        .rtt_clk(rtt_clk),
        .rst_a(rst_a),

        .rtt_time_stamp_en(rtt_time_stamp_en),
        .flush_done(flush_done),
        .ptcm_done(ptcm_done),
        .sbarb_done(sbarb_done),

        .sbuf_empty(sbuf_empty_i),

        .data_in0(data_in0),
        .data_in1(data_in1),
        .data_in2(data_in2),
        .data_in3(data_in3),
        .data_in4(data_in4),
        .data_in5(data_in5),
        .data_in6(data_in6),
        .data_in7(data_in7),
        .data_in8(data_in8),
        .data_in9(data_in9),
        .data_in10(data_in10),
        .data_in11(data_in11),
        .data_in12(data_in12),
        .data_in13(data_in13),
        .data_in14(data_in14),
        .data_in15(data_in15),
        .data_in16(data_in16),
        .data_in17(data_in17),
        .data_in18(data_in18),
        .data_in19(data_in19),
        
        .msg_seq_order_q_rd_en(msg_seq_order_q_rd_en),
        .msg_seq_order_q_rdata(msg_seq_order_q_rdata),

        .arb_src0(arb_src0),
        .arb_src1(arb_src1),
        .arb_src2(arb_src2),
        .arb_val(arb_val),

        .atb_sbuf_ack(swe_sbuf_ack),
        .atb_sbuf_rden(swe_sbuf_rden)
        );
// spyglass enable_block UnloadedOutTerm-ML

npuarc_rtt_swe_msg_parallelize #(.BUMP_WDT(9)
              ) u_rtt_atb_msg_parallelize (
        .rtt_clk(rtt_clk),
        .rst_a(rst_a),

        .flush_cmd(flush_cmd),
        .flush_done(flush_done),
        .sbarb_done(sbarb_done),
        .para_done(para_done),
        .para_busy(para_busy),

        .sbuf_ack0(swe_sbuf_ack[0]),
        .sbuf_valid0(arb_val[0]),
        .sbuf_rdata0(arb_src0),
        .sbuf_ack1(swe_sbuf_ack[1]),
        .sbuf_valid1(arb_val[1]),
        .sbuf_rdata1(arb_src1),
        .sbuf_ack2(swe_sbuf_ack[2]),
        .sbuf_valid2(arb_val[2]),
        .sbuf_rdata2(arb_src2),

        .atb_fifo_req(p0_req),
        .atb_fifo_wdata(p0_wdata),
        .atb_fifo_ack(p0_ack)
        );

endmodule
