// Library ARC_Trace-3.0.999999999
// Copyright (C) 2012-2019 Synopsys, Inc. All rights reserved.
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
//   rtt_swe_prdcr_top
//
// ===========================================================================
//
// Description:
//
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_swe_prdcr_top.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"

module npuarc_rtt_swe_prdcr_top 
(
///I/O declarations
//global signals

  input  wire                    rtt_clk,
  input  wire                    rst_a,
  input  wire                    rtt_write_a,
  input  wire [32:0]             sl0_alt_rtt_swe_data,
  input  wire                    sl0_alt_rtt_swe_val,
  input  wire [7:0]              sl0_alt_rtt_swe_ext,
  input  wire [32:0]             sl1_alt_rtt_swe_data,
  input  wire                    sl1_alt_rtt_swe_val,
  input  wire [7:0]              sl1_alt_rtt_swe_ext,
  input  wire [32:0]             sl2_alt_rtt_swe_data,
  input  wire                    sl2_alt_rtt_swe_val,
  input  wire [7:0]              sl2_alt_rtt_swe_ext,
  input  wire [32:0]             sl3_alt_rtt_swe_data,
  input  wire                    sl3_alt_rtt_swe_val,
  input  wire [7:0]              sl3_alt_rtt_swe_ext,
  input  wire [32:0]             sl4_alt_rtt_swe_data,
  input  wire                    sl4_alt_rtt_swe_val,
  input  wire [7:0]              sl4_alt_rtt_swe_ext,
  input  wire [32:0]             sl5_alt_rtt_swe_data,
  input  wire                    sl5_alt_rtt_swe_val,
  input  wire [7:0]              sl5_alt_rtt_swe_ext,
  input  wire [32:0]             sl6_alt_rtt_swe_data,
  input  wire                    sl6_alt_rtt_swe_val,
  input  wire [7:0]              sl6_alt_rtt_swe_ext,
  input  wire [32:0]             sl7_alt_rtt_swe_data,
  input  wire                    sl7_alt_rtt_swe_val,
  input  wire [7:0]              sl7_alt_rtt_swe_ext,
  input  wire [32:0]             sl8_alt_rtt_swe_data,
  input  wire                    sl8_alt_rtt_swe_val,
  input  wire [7:0]              sl8_alt_rtt_swe_ext,
  input  wire [32:0]             sl9_alt_rtt_swe_data,
  input  wire                    sl9_alt_rtt_swe_val,
  input  wire [7:0]              sl9_alt_rtt_swe_ext,
  input  wire [32:0]             sl10_alt_rtt_swe_data,
  input  wire                    sl10_alt_rtt_swe_val,
  input  wire [7:0]              sl10_alt_rtt_swe_ext,
  input  wire [32:0]             sl11_alt_rtt_swe_data,
  input  wire                    sl11_alt_rtt_swe_val,
  input  wire [7:0]              sl11_alt_rtt_swe_ext,
  input  wire [32:0]             sl12_alt_rtt_swe_data,
  input  wire                    sl12_alt_rtt_swe_val,
  input  wire [7:0]              sl12_alt_rtt_swe_ext,
  input  wire [32:0]             sl13_alt_rtt_swe_data,
  input  wire                    sl13_alt_rtt_swe_val,
  input  wire [7:0]              sl13_alt_rtt_swe_ext,
  input  wire [32:0]             sl14_alt_rtt_swe_data,
  input  wire                    sl14_alt_rtt_swe_val,
  input  wire [7:0]              sl14_alt_rtt_swe_ext,
  input  wire [32:0]             sl15_alt_rtt_swe_data,
  input  wire                    sl15_alt_rtt_swe_val,
  input  wire [7:0]              sl15_alt_rtt_swe_ext,
  input  wire [32:0]             sl16_alt_rtt_swe_data,
  input  wire                    sl16_alt_rtt_swe_val,
  input  wire [7:0]              sl16_alt_rtt_swe_ext,

  output wire [120-1:0] prdcr_data,
  output wire                      para_done,
 // programming IP inputs
  input  [`npuarc_RTT_NUM_SWE_PORTS-1:0] swe_pr_sel,
  input  wire                      swe_csts_en,
  input  wire                      atb_syncreq,
  input  wire                      rtt_flush_command,
  input  wire                      rtt_time_stamp_en,

  input  wire                      flush_done,
  input  wire [`npuarc_RTT_TIME_STMP-1:0] time_stamp,
  input  wire [63:0]               cstimestamp,

 //inputs to transport
  output wire                     prdcr_req,
  input  wire                     prdcr_ack,

  output wire                     prdcr_busy
  );

  //nets declarations
  wire                            encapsulation_top_busy;



assign prdcr_busy = encapsulation_top_busy ||
                       rtt_write_a;

wire                  sbuf_empty;

//time stamp for all the messages

npuarc_rtt_swe_encapsulation_top u_rtt_encapsulation_top(
  .rtt_clk (rtt_clk),
  .rst_a (rst_a),
  .sl0_alt_rtt_swe_data (sl0_alt_rtt_swe_data),
  .sl0_alt_rtt_swe_val  (sl0_alt_rtt_swe_val),
  .sl0_alt_rtt_swe_ext  (sl0_alt_rtt_swe_ext),
  .sl1_alt_rtt_swe_data (sl1_alt_rtt_swe_data),
  .sl1_alt_rtt_swe_val  (sl1_alt_rtt_swe_val),
  .sl1_alt_rtt_swe_ext  (sl1_alt_rtt_swe_ext),
  .sl2_alt_rtt_swe_data (sl2_alt_rtt_swe_data),
  .sl2_alt_rtt_swe_val  (sl2_alt_rtt_swe_val),
  .sl2_alt_rtt_swe_ext  (sl2_alt_rtt_swe_ext),
  .sl3_alt_rtt_swe_data (sl3_alt_rtt_swe_data),
  .sl3_alt_rtt_swe_val  (sl3_alt_rtt_swe_val),
  .sl3_alt_rtt_swe_ext  (sl3_alt_rtt_swe_ext),
  .sl4_alt_rtt_swe_data (sl4_alt_rtt_swe_data),
  .sl4_alt_rtt_swe_val  (sl4_alt_rtt_swe_val),
  .sl4_alt_rtt_swe_ext  (sl4_alt_rtt_swe_ext),
  .sl5_alt_rtt_swe_data (sl5_alt_rtt_swe_data),
  .sl5_alt_rtt_swe_val  (sl5_alt_rtt_swe_val),
  .sl5_alt_rtt_swe_ext  (sl5_alt_rtt_swe_ext),
  .sl6_alt_rtt_swe_data (sl6_alt_rtt_swe_data),
  .sl6_alt_rtt_swe_val  (sl6_alt_rtt_swe_val),
  .sl6_alt_rtt_swe_ext  (sl6_alt_rtt_swe_ext),
  .sl7_alt_rtt_swe_data (sl7_alt_rtt_swe_data),
  .sl7_alt_rtt_swe_val  (sl7_alt_rtt_swe_val),
  .sl7_alt_rtt_swe_ext  (sl7_alt_rtt_swe_ext),
  .sl8_alt_rtt_swe_data (sl8_alt_rtt_swe_data),
  .sl8_alt_rtt_swe_val  (sl8_alt_rtt_swe_val),
  .sl8_alt_rtt_swe_ext  (sl8_alt_rtt_swe_ext),
  .sl9_alt_rtt_swe_data (sl9_alt_rtt_swe_data),
  .sl9_alt_rtt_swe_val  (sl9_alt_rtt_swe_val),
  .sl9_alt_rtt_swe_ext  (sl9_alt_rtt_swe_ext),
  .sl10_alt_rtt_swe_data (sl10_alt_rtt_swe_data),
  .sl10_alt_rtt_swe_val  (sl10_alt_rtt_swe_val),
  .sl10_alt_rtt_swe_ext  (sl10_alt_rtt_swe_ext),
  .sl11_alt_rtt_swe_data (sl11_alt_rtt_swe_data),
  .sl11_alt_rtt_swe_val  (sl11_alt_rtt_swe_val),
  .sl11_alt_rtt_swe_ext  (sl11_alt_rtt_swe_ext),
  .sl12_alt_rtt_swe_data (sl12_alt_rtt_swe_data),
  .sl12_alt_rtt_swe_val  (sl12_alt_rtt_swe_val),
  .sl12_alt_rtt_swe_ext  (sl12_alt_rtt_swe_ext),
  .sl13_alt_rtt_swe_data (sl13_alt_rtt_swe_data),
  .sl13_alt_rtt_swe_val  (sl13_alt_rtt_swe_val),
  .sl13_alt_rtt_swe_ext  (sl13_alt_rtt_swe_ext),
  .sl14_alt_rtt_swe_data (sl14_alt_rtt_swe_data),
  .sl14_alt_rtt_swe_val  (sl14_alt_rtt_swe_val),
  .sl14_alt_rtt_swe_ext  (sl14_alt_rtt_swe_ext),
  .sl15_alt_rtt_swe_data (sl15_alt_rtt_swe_data),
  .sl15_alt_rtt_swe_val  (sl15_alt_rtt_swe_val),
  .sl15_alt_rtt_swe_ext  (sl15_alt_rtt_swe_ext),
  .sl16_alt_rtt_swe_data (sl16_alt_rtt_swe_data),
  .sl16_alt_rtt_swe_val  (sl16_alt_rtt_swe_val),
  .sl16_alt_rtt_swe_ext  (sl16_alt_rtt_swe_ext),
  .swe_pr_sel (swe_pr_sel),
  .swe_csts_en (swe_csts_en),
  .atb_syncreq(atb_syncreq),
  .time_stamp (time_stamp),
  .cstimestamp (cstimestamp),
  .rtt_time_stamp_en (rtt_time_stamp_en),
  .flush_cmd(rtt_flush_command),
  .flush_done(flush_done),
  .p0_req(prdcr_req),
  .p0_ack(prdcr_ack),
  .p0_wdata (prdcr_data),
  .para_done(para_done),
  .sbuf_empty(sbuf_empty),
  .encapsulation_top_busy (encapsulation_top_busy)
);

endmodule
