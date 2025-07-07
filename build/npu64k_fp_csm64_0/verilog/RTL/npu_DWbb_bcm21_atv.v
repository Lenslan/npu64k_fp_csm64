////////////////////////////////////////////////////////////////////////////////
//
//                  (C) COPYRIGHT 2017 - 2020 SYNOPSYS, INC.
//                            ALL RIGHTS RESERVED
//
//  This software and the associated documentation are confidential and
//  proprietary to Synopsys, Inc.  Your use or disclosure of this
//  software is subject to the terms and conditions of a written
//  license agreement between you, or your company, and Synopsys, Inc.
//
//  The entire notice above must be reproduced on all authorized copies.
//
// Filename    : npu_DWbb_bcm21_atv.v
// Revision    : $Id: $
// Author      : Doug Lee      February 14, 2017
// Description : npu_DWbb_bcm21_atv.v Verilog module for npu_DWbb
//
// DesignWare IP ID: cc56da0c
//
////////////////////////////////////////////////////////////////////////////////
module npu_DWbb_bcm21_atv (
    clk_d,
    rst_d_n,
    data_s,
    data_d
             );

parameter WIDTH        = 1;  // RANGE 1 to 1024
parameter F_SYNC_TYPE  = 2;  // RANGE 0 to 4
parameter VERIF_EN     = 1;  // RANGE 0 to 5
parameter SVA_TYPE     = 1;
parameter TMR_CDC      = 0;  // RANGE 0 or 1
 
localparam F_SYNC_TYPE_P8 = F_SYNC_TYPE + 8;
localparam DATA_S_WIDTH  = (TMR_CDC == 0) ? WIDTH : (WIDTH * 3);

input                   clk_d;      // clock input from destination domain
input                   rst_d_n;    // active low asynchronous reset from destination domain
input  [DATA_S_WIDTH-1:0] data_s;     // data to be synchronized from source domain
output [WIDTH-1:0]      data_d;     // data synchronized to destination domain



`ifndef SYNTHESIS
`ifndef DWC_DISABLE_CDC_METHOD_REPORTING
  initial begin
    if ((F_SYNC_TYPE > 0)&&(F_SYNC_TYPE < 8))
       $display("Information: *** Instance %m module is using the <Double Register Synchronizer (1)> Clock Domain Crossing Method ***");
  end

`endif
`endif

wire [WIDTH-1:0] data_d_int;

generate
  if (TMR_CDC == 0) begin : GEN_TMR_EQ_0
    npu_DWbb_bcm21 #(WIDTH, F_SYNC_TYPE_P8, VERIF_EN, SVA_TYPE)
        U_SYNC(
        .clk_d(clk_d),
        .rst_d_n(rst_d_n),
        .data_s(data_s),
        .data_d(data_d_int) );
  end else begin : GEN_TMR_NE_0
    wire [WIDTH-1:0] data_s_0;
    wire [WIDTH-1:0] data_s_1;
    wire [WIDTH-1:0] data_s_2;
 
    wire [WIDTH-1:0] dw_sync_0;
    wire [WIDTH-1:0] dw_sync_1;
    wire [WIDTH-1:0] dw_sync_2;

    assign {data_s_2, data_s_1, data_s_0} = data_s;

    npu_DWbb_bcm21 #(WIDTH, F_SYNC_TYPE_P8, VERIF_EN, SVA_TYPE)
        U_CDC0(
        .clk_d(clk_d),
        .rst_d_n(rst_d_n),
        .data_s(data_s_0),
        .data_d(dw_sync_0) );
    npu_DWbb_bcm21 #(WIDTH, F_SYNC_TYPE_P8, VERIF_EN, SVA_TYPE)
        U_CDC1(
        .clk_d(clk_d),
        .rst_d_n(rst_d_n),
        .data_s(data_s_1),
        .data_d(dw_sync_1) );
    npu_DWbb_bcm21 #(WIDTH, F_SYNC_TYPE_P8, VERIF_EN, SVA_TYPE)
        U_CDC2(
        .clk_d(clk_d),
        .rst_d_n(rst_d_n),
        .data_s(data_s_2),
        .data_d(dw_sync_2) );

    if ((F_SYNC_TYPE&7) == 0) begin : GEN_SYNC_TYPE_EQ_0
        assign data_d_int = (dw_sync_0 & dw_sync_1) | (dw_sync_0 & dw_sync_2) | (dw_sync_1 & dw_sync_2);
    end else begin : GEN_SYNC_TYPE_GT_0
      if ((F_SYNC_TYPE&7) <= 2) begin : GEN_SYNC_TYPE_EQ_1_2
// spyglass disable_block Ac_conv02
// SMD: Synchronizers converge on combinational logic
// SJ: The single-bit signals converging into the combinational logic are triplicated from the same signal at the source and run through parallel paths of synchronizers with the identical number of stages.  This synchronized convergence is intentional as the combinational logic produces a majority vote result which is immune to non-gray code transitions.
        assign data_d_int = (dw_sync_0 & dw_sync_1) | (dw_sync_0 & dw_sync_2) | (dw_sync_1 & dw_sync_2);
// spyglass enable_block Ac_conv02
      end else begin : GEN_SYNC_TYPE_GE_3
// spyglass disable_block Ac_conv01
// SMD: Synchronized sequential element(s) converge on combinational logic
// SJ: The single-bit signals converging into sequential elements are triplicated from the same signal at the source and run through parallel paths of synchronizers with the identical number of stages.  This synchronized convergence is intentional and directly supplies combinational logic that produces a majority vote result which is immune to non-gray code transitions.
        assign data_d_int = (dw_sync_0 & dw_sync_1) | (dw_sync_0 & dw_sync_2) | (dw_sync_1 & dw_sync_2);
// spyglass enable_block Ac_conv01
      end
    end

  end
endgenerate

  // Assign to output
  assign data_d = data_d_int;

endmodule
