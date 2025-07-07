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
//   rtt_prdcr_cgm
//
// ===========================================================================
//
// Description:
//    RTT clock gating module to generate the gates clocks to producer front
//   end modules, transport modules and register block
//
//   vpp +q +o rtt_prdcr_cgm.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"


module npuarc_rtt_prdcr_cgm (

rtt_clk,
rst_a,
rtt_write_a,
atb_ctrl_busy,
prdcr_clk_en,
prdcr_en,
prdcr_clk
);


//global signals
  input                     rtt_clk;
  input                     rst_a;

  input                     rtt_write_a;
  input                     prdcr_clk_en;
  input                     atb_ctrl_busy;
  
  input                     prdcr_en;
  output                    prdcr_clk;

  reg        rtt_write_a_r;
  reg        rtt_write_a_2r;
  reg        prdcr_clk_en_r;
  wire       prdcr_clk_disable;
  reg        prdcr_clk_disable_r;


  always @(posedge rtt_clk or posedge rst_a)
  begin : CLOCK_DELAY_PROC

          if (rst_a == 1'b 1)
          begin
            rtt_write_a_r <= 1'b0;
            rtt_write_a_2r <= 1'b0;
          end
          else
          begin
            rtt_write_a_r <= rtt_write_a;
            rtt_write_a_2r <=rtt_write_a_r ;
          end

  end

always @ (posedge rtt_clk or posedge rst_a)
  begin : CLOCK_GATE_PROC
    if(rst_a == 1'b1) begin
      prdcr_clk_en_r <= 1'b0;
    end
    else begin
      prdcr_clk_en_r <= prdcr_clk_en;
    end
  end

  assign prdcr_clk_disable =   prdcr_clk_en || prdcr_en || prdcr_clk_en_r ||rtt_write_a_r ||rtt_write_a_2r || rtt_write_a
                                || atb_ctrl_busy
                               ;

always @ (posedge rtt_clk or posedge rst_a)
  begin : CLOCK_DISABLE_PROC
    if(rst_a == 1'b1) begin
      prdcr_clk_disable_r <= 1'b0;
    end
    else begin
      prdcr_clk_disable_r <= prdcr_clk_disable;
    end
  end


//gate clock for producer block
  npuarc_clock_gate u_clkgate_prdcr (
  .clk_in            (rtt_clk),
  .clock_enable_r    (prdcr_clk_disable_r),
//  .clock_enable_r    (1'b1),
  .clk_out           (prdcr_clk)
);

endmodule


