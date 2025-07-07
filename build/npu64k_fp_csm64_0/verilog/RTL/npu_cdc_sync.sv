/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

//----------------------------------------------------------------------------
// synchronizer
// ===========================================================================
//
// Description:
//
// Synchronizer for a clock-domain crossing input signal (async input).
// The number synchronizing FF levels is controlled by SYNC_FF_LEVELS.
//
// Note: This is a behavioral block that may be replaced by the RDF flow before
// synthesis. The replacement block instantiates the proper synchronizer cell
// of the synthesis library
//
// ===========================================================================

`include "npu_defines.v"

module npu_cdc_sync
  #(
  parameter int SYNC_FF_LEVELS = 2,     // Allowed values: 2, 3, 4
  parameter int WIDTH = 1,
  parameter int TMR_CDC = 0,
  localparam int DATA_S_WIDTH  = (TMR_CDC == 0) ? WIDTH : (WIDTH * 3)
  )
  (
  input  logic              clk,        // target (receiving) clock domain clk
  input  logic              rst_a,
  input  logic  [DATA_S_WIDTH-1:0] din,        // async input
  output logic  [WIDTH-1:0] dout        // synchronized output
  );
 
`ifndef NPU_NO_DWBB_CDC_SYNC //  Use DesignWare building block by default

  // Use CDC Sync from npu_DWbb - may be replaced with
  // specialized cells during synthesis
  npu_DWbb_bcm21_atv #(
      .WIDTH(WIDTH),
      .F_SYNC_TYPE(SYNC_FF_LEVELS),
      .VERIF_EN(0),
      .SVA_TYPE(0),
      .TMR_CDC(TMR_CDC)
  ) u_sync_wrp (
    .rst_d_n        (~rst_a),
    .data_s         (din),
    .clk_d          (clk),
    .data_d         (dout)
  );

`else // CDC through serial FF

  // spyglass disable_block Ac_unsync01
  // spyglass disable_block Ac_unsync02
  // SMD: Unsynchronized Crossing

  logic [WIDTH-1:0] sample_meta;
  logic [WIDTH-1:0] sample_syncl;

  // spyglass disable_block W402b
  //SMD:Self generated reset
  //SJ :Ignore
  generate
    if (SYNC_FF_LEVELS==2) begin : GEN_FF2
      always_ff @(posedge clk or posedge rst_a) begin : cdc_sync_PROC
        if (rst_a == 1'b1) begin
          sample_meta  <= '0;
          sample_syncl <= '0;
        end
        else begin
          sample_meta <= (TMR_CDC == 0) ? din : din[WIDTH-1:0];
          sample_syncl <= sample_meta;
        end
      end : cdc_sync_PROC
    end : GEN_FF2
  // spyglass enable_block W402b

    else if (SYNC_FF_LEVELS==3) begin : GEN_FF3
      logic [WIDTH-1:0] sample_d1;
      always_ff @(posedge clk or posedge rst_a) begin : cdc_sync_PROC
        if (rst_a == 1'b1) begin
          sample_meta  <= '0;
          sample_syncl <= '0;
          sample_d1    <= '0;
        end
        else begin
          sample_meta  <= (TMR_CDC == 0) ? din : din[WIDTH-1:0];
          sample_d1    <= sample_meta;
          sample_syncl <= sample_d1;
        end
      end : cdc_sync_PROC
    end : GEN_FF3

    else if (SYNC_FF_LEVELS==4) begin : GEN_FF4
      logic [WIDTH-1:0] sample_d1;
      logic [WIDTH-1:0] sample_d2;
      always_ff @(posedge clk or posedge rst_a) begin : cdc_sync_PROC
        if (rst_a == 1'b1) begin
          sample_meta  <= '0;
          sample_syncl <= '0;
          sample_d1    <= '0;
          sample_d2    <= '0;
        end
        else begin
          sample_meta  <= (TMR_CDC == 0) ? din : din[WIDTH-1:0];
          sample_d1    <= sample_meta;
          sample_d2    <= sample_d1;
          sample_syncl <= sample_d2;
        end
      end : cdc_sync_PROC
    end : GEN_FF4

  endgenerate


  assign dout = sample_syncl;

  // spyglass enable_block Ac_unsync02
  // spyglass enable_block Ac_unsync01

`endif

endmodule
