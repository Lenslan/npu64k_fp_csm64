// Library ARCv2CC-3.2.999999999
////////////////////////////////////////////////////////////////////////////////
//
//                  (C) COPYRIGHT 2005 - 2020 SYNOPSYS, INC.
//                            ALL RIGHTS RESERVED
//
//  This software and the associated documentation are confidential and
//  proprietary to Synopsys, Inc.  Your use or disclosure of this
//  software is subject to the terms and conditions of a written
//  license agreement between you, or your company, and Synopsys, Inc.
//
//  The entire notice above must be reproduced on all authorized copies.
//
// Filename    : DWbb_bcm21.v
// Revision    : $Id: $
// Author      : Doug Lee    2/20/05
// Description : DWbb_bcm21.v Verilog module for DWbb
//
// DesignWare IP ID: 26c0f7d3
//
////////////////////////////////////////////////////////////////////////////////



module npuarc_DWbb_bcm21 (
    clk_d,
    rst_d_n,
    data_s,
    data_d
    );

parameter WIDTH        = 1;  // RANGE 1 to 1024
parameter F_SYNC_TYPE  = 2;  // RANGE 0 to 4
parameter VERIF_EN     = 1;  // RANGE 0 to 5
parameter SVA_TYPE     = 1;

localparam SVA_TYPE_BIT3 = SVA_TYPE&4'b1000;
localparam SVA_TYPE_BIT2 = SVA_TYPE&4'b0100;
localparam SVA_TYPE_BIT1BIT0 = SVA_TYPE&4'b0011;


input                   clk_d;      // clock input from destination domain
input                   rst_d_n;    // active low asynchronous reset from destination domain
input  [WIDTH-1:0]      data_s;     // data to be synchronized from source domain
output [WIDTH-1:0]      data_d;     // data synchronized to destination domain


localparam TECH_MAPPING_LAM = (VERIF_EN==5) ? 1 : 0;  // Latency Accurate Missampling decode for Technology Mapping cells

wire   [WIDTH-1:0]      data_s_int;

`ifndef SYNTHESIS
`endif


`ifndef SYNTHESIS
`ifndef DWC_DISABLE_CDC_METHOD_REPORTING
  initial begin
    if ((F_SYNC_TYPE > 0)&&(F_SYNC_TYPE < 8))
       $display("Information: *** Instance %m module is using the <Double Register Synchronizer (1)> Clock Domain Crossing Method ***");
  end

`endif
`endif



`ifdef SYNTHESIS
  assign data_s_int = data_s;
`else
  assign data_s_int = data_s;
`endif


// spyglass disable_block Ac_conv04
// SMD: Checks all the control-bus clock domain crossings which do not follow gray encoding
// SJ: The clock domain crossing bus is between the register file and the read-mux of a RAM, which do not need a gray encoding.

generate
    if ((F_SYNC_TYPE & 7) == 0) begin : GEN_FST0
      assign data_d  =  data_s;
    end
    if ((F_SYNC_TYPE & 7) == 1) begin : GEN_FST1
      DWbb_bcm99_n U_SAMPLE_META_2_N[WIDTH-1:0] (
        .clk_d(clk_d),
        .rst_d_n(rst_d_n),
        .data_s(data_s_int),
        .data_d(data_d)
      );
    end
    if ((F_SYNC_TYPE & 7) == 2) begin : GEN_FST2
      wire   [WIDTH-1:0]      next_sample_meta;
      wire   [WIDTH-1:0]      sample_syncl;

      assign next_sample_meta      = data_s_int;

      npuarc_DWbb_bcm99 #(TECH_MAPPING_LAM) U_SAMPLE_META_2[WIDTH-1:0] (
        .clk_d(clk_d),
        .rst_d_n(rst_d_n),
        .data_s(next_sample_meta),
        .data_d(sample_syncl)
      );

      assign data_d = sample_syncl;

    end
    if ((F_SYNC_TYPE & 7) == 3) begin : GEN_FST3
      wire   [WIDTH-1:0]      next_sample_meta;
      wire   [WIDTH-1:0]      sample_syncl;

      assign next_sample_meta      = data_s_int;

      DWbb_bcm99_3 #(0) U_SAMPLE_META_3[WIDTH-1:0] (
        .clk_d(clk_d),
        .rst_d_n(rst_d_n),
        .data_s(next_sample_meta),
        .data_d(sample_syncl)
      );

      assign data_d = sample_syncl;

    end
    if ((F_SYNC_TYPE & 7) == 4) begin : GEN_FST4
      wire   [WIDTH-1:0]      next_sample_meta;
      wire   [WIDTH-1:0]      sample_syncl;

      assign next_sample_meta      = data_s_int;

      DWbb_bcm99_4 #(0) U_SAMPLE_META_4[WIDTH-1:0] (
        .clk_d(clk_d),
        .rst_d_n(rst_d_n),
        .data_s(next_sample_meta),
        .data_d(sample_syncl)
      );
      assign data_d = sample_syncl;

    end
endgenerate



// spyglass enable_block Ac_conv04

`ifndef SYNTHESIS
`endif


endmodule
