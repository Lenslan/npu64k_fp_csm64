/*
 * Copyright (C) 2021-2022 Synopsys, Inc. All rights reserved.
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

`include "clk_rst_pkt.sv"

module npu_clk_rst_gen
(
  output logic        npu_core_clk,
  output logic        npu_core_rst_a,
  output logic        npu_noc_clk,
  output logic        npu_noc_rst_a,
  output logic        npu_cfg_clk,
  output logic        npu_cfg_rst_a,
  output logic        arcsync_axi_clk,
  output logic        arcsync_axi_rst_a,
  output logic        arcsync_clk,
  output logic        arcsync_rst_a,  
  output logic [31:0] l1_core_clk,
  output logic [31:0] l1_wdt_clk,
  output logic [1:0]  l2_wdt_clk,
  output logic        pclkdbg,
  output logic        presetdbgn,
  output logic        test_mode,
  output logic [31:0] cycle
);

  logic rand_rst_en;
  logic dis_kpi_clk;    
  logic wdt_clk_sel;
  
  npu_clk_rst_intf clk_rst_if();
  clk_rst_pkt pkt;

  initial 
  begin
    pkt = new(clk_rst_if);
    pkt.randomize() with {
      npu_core_clk_period == 1000; //npu_core_clk: 1000ps i.e. 1 GHz 
    };
    pkt.run();
  end

  assign npu_core_clk      = clk_rst_if.npu_core_clk;
  assign npu_core_rst_a    = clk_rst_if.npu_core_rst;
  assign npu_noc_clk       = clk_rst_if.noc_axi_clk;
  assign npu_noc_rst_a     = clk_rst_if.noc_axi_rst;
  assign npu_cfg_clk       = clk_rst_if.cfg_axi_clk;
  assign npu_cfg_rst_a     = clk_rst_if.cfg_axi_rst;
  assign arcsync_axi_clk   = clk_rst_if.arcsync_axi_clk;
  assign arcsync_axi_rst_a = clk_rst_if.arcsync_axi_rst;
  assign arcsync_clk       = clk_rst_if.arcsync_clk;
  assign arcsync_rst_a     = clk_rst_if.arcsync_rst;
  assign pclkdbg           = clk_rst_if.debug_clk;
  assign presetdbgn        = ~clk_rst_if.debug_rst;
  assign l2_wdt_clk[0]     = l1_wdt_clk[4];
  assign l2_wdt_clk[1]     = l1_wdt_clk[5];

  genvar i;
  generate
    for(i=0; i<32; i++) begin
      assign #(i%6) l1_core_clk[i] = clk_rst_if.npu_l1_clk;
      assign #(i%6) l1_wdt_clk[i]  = clk_rst_if.wdt_clk;
    end
  endgenerate

  initial
  begin
    rand_rst_en=0;
    dis_kpi_clk=0;
    test_mode = 0;
    wdt_clk_sel=$urandom_range(0, 1);;
    $value$plusargs("RAND_RST_EN=%d", rand_rst_en);
    $value$plusargs("DIS_KPI_CLK=%d", dis_kpi_clk);

    if(rand_rst_en)begin
      int cnt=$urandom_range(100, 1000);
      repeat(cnt) @(npu_core_clk);
      repeat (200) @(npu_core_clk);
      test_mode = 1'b1;
      repeat (200) @(npu_core_clk);
      test_mode = 1'b0;
    end
  end

  always @(posedge npu_core_clk or npu_core_rst_a) begin
    if(npu_core_rst_a) 
      cycle <= 'd0;
    else      
      cycle <= cycle + 1;
  end

endmodule
