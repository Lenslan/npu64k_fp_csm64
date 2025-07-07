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

module clk_rst_gen
  #(
    parameter CYCYLE = 10,
    parameter RST_DELAY = 50
   )
(
    output logic clk,
  `ifndef IS_NPU_SLICE_TB  
    output logic clk_h1, // half frequency of clk
    output logic clk_h2, // half frequency of clk
    output logic        npu_core_clk,
    output logic        npu_core_rst_a,
    output logic        npu_noc_clk,
    output logic        npu_noc_rst_a,
    output logic        npu_cfg_clk,
    output logic        npu_cfg_rst_a,
    output logic [31:0] slc_clk,
    output logic [31:0] slc_wdt_clk,
    output logic        nl2arc0_wdt_clk,
    output logic        nl2arc1_wdt_clk,
  `endif
    output logic rst_a,
    output logic rst_n,
    output logic test_mode,
    output logic jtag_clk,
    output logic jtag_rst_n,
    output logic [31:0] cycle
);

    logic rand_rst_en;
    logic dis_kpi_clk;    
    logic cycle_clk, clk_div2, clk_div3, clk_div4;


    always #(CYCYLE*1.0/2) clk = ~clk;
    always #(CYCYLE*2.0/2) clk_div2 = ~clk_div2;
    always #(CYCYLE*3.0/2) clk_div3 = ~clk_div3;
    always #(CYCYLE*4.0/2) clk_div4 = ~clk_div4;
    
  `ifndef IS_NPU_SLICE_TB  
    assign cycle_clk = slc_clk[0];
    assign #(0.1*CYCYLE) clk_h1 = clk_div2;
    assign #(0.3*CYCYLE) clk_h2 = clk_div2;

    assign #(0.2*CYCYLE) npu_core_clk = clk;
    assign /*#3*/ npu_cfg_clk  = clk;
    assign /*#4*/ npu_noc_clk  = clk;
    assign #(0.5*CYCYLE) nl2arc0_wdt_clk = clk;
    assign #(0.5*CYCYLE) nl2arc1_wdt_clk = clk;

    assign    npu_core_rst_a = rst_a;
    assign    npu_cfg_rst_a  = rst_a;
    assign    npu_noc_rst_a  = rst_a;
   
    genvar i;
    generate
      for(i=0; i<32; i++) begin
        assign #((i%6)    *0.1*CYCYLE) slc_clk[i]     = dis_kpi_clk ? clk_div2 : clk;
        assign #(((i+3)%7)*0.1*CYCYLE) slc_wdt_clk[i] = dis_kpi_clk ? clk_div3 : clk;
      end
    endgenerate

  `else
    assign cycle_clk = clk;
  `endif


    initial
    begin
        rand_rst_en=0;
        dis_kpi_clk=0;
        $value$plusargs("RAND_RST_EN=%d", rand_rst_en);
        $value$plusargs("DIS_KPI_CLK=%d", dis_kpi_clk);
        
        clk = 0;
        clk_div2 = 0;
        clk_div3 = 0;
        clk_div4 = 0;
        rst_a = 0;
        test_mode = 0;

        rst_a = 1;
        repeat (RST_DELAY) @(clk);
        rst_a = 1'b0;
       
        if(rand_rst_en)begin
            int cnt=$urandom_range(100, 1000);
            repeat(cnt) @(clk);
            rst_a = 1'b1;
            repeat (RST_DELAY) @(clk);
            rst_a = 1'b0;
            repeat (200) @(clk);
            test_mode = 1'b1;
            repeat (200) @(clk);
            test_mode = 1'b0;
        end
    end
    assign rst_n = ~rst_a;


    //JTAG clk & reset
    always #(CYCYLE*2+2) jtag_clk = ~jtag_clk;

    logic jtag_rst_a;
    initial
    begin
        jtag_clk =0;
        jtag_rst_a = 0;
        #1 jtag_rst_a =1;
        repeat (RST_DELAY) @(jtag_clk);
        jtag_rst_a = 1'b0;
    end

    assign jtag_rst_n = ~jtag_rst_a;


    always @(posedge cycle_clk or rst_a) begin
        if(rst_a) cycle <= 'd0;
        else      cycle <= cycle + 1;
    end
endmodule
