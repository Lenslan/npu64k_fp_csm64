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

// CLN wrapper including burst converters
// vcs -sverilog -f ../../shared/RTL/npu_shared_manifest npu_cln_wrap.sv

`include "nl2_cln_defines.v"
`include "npu_defines.v"

`include "npu_axi_macros.svh"

module npu_cln_wrap
  import npu_types::*;
  #(
    parameter int DBANK  = 8,  // CSM BANKS 
    parameter int BOTIDW = 5   // bottom link ID width
  )
  (

    input      logic                          clk,
    input      logic                          rst_a,
    input      logic                          test_mode,
    input      logic                          grp_pd_mem,   
    output logic                              scm_dbank_ecc_irq,
   // report dbank sbe/dbe: to NPX top
    output logic                              scm_dbank_sbe,
    output logic                              scm_dbank_dbe,
    // configuration device port
    `AXISLV(1,32,1,1,1,1,1,axi_cfg_),
    // ingress links from other groups
    `AXISLVN(DBANK,BOTIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_cln_)
  );


  localparam int CLN_AXIDW = VSIZE*64;
  localparam int CLN_AXIAW = 40;
  localparam int CLN_NOC_IIDW = 2;
  localparam int CLN_NOC_AXIDW = 64;
  localparam int CLN_ID_NUM = 1<<BOTIDW;
  //
  // Synchronize reset
  //
  logic              rst_sync;         // synchronous reset
  npu_reset_ctrl
  u_reset_ctrl_main
  (
   .clk        ( clk       ),
   .rst_a      ( rst_a     ),
   .test_mode  ( test_mode ),
   .rst        ( rst_sync  )
  );


//    // AXI interfaces
//    `CLN_AXIMST_INST(40, dev0_axi_, axi_cfg_),
  `AXIWIRES_FLAT(1,40,32,NPU_AXI_REGION_W,NPU_AXI_LEN_W,1,1,1,1,1,iaxi_cfg_);
  `AXIASGS_EXT(iaxi_cfg_,axi_cfg_);

logic dbnk_ecc_en;
logic dbnk_scrub_en;
logic dbnk_init;
logic dbnk_init_done0;
logic dbnk_e2e_err0;
logic dbnk_sbe0;
logic dbnk_dbe0;
logic dbnk_init_done1;
logic dbnk_e2e_err1;
logic dbnk_sbe1;
logic dbnk_dbe1;
logic dbnk_init_done2;
logic dbnk_e2e_err2;
logic dbnk_sbe2;
logic dbnk_dbe2;
logic dbnk_init_done3;
logic dbnk_e2e_err3;
logic dbnk_sbe3;
logic dbnk_dbe3;
logic dbnk_init_done4;
logic dbnk_e2e_err4;
logic dbnk_sbe4;
logic dbnk_dbe4;
logic dbnk_init_done5;
logic dbnk_e2e_err5;
logic dbnk_sbe5;
logic dbnk_dbe5;
logic dbnk_init_done6;
logic dbnk_e2e_err6;
logic dbnk_sbe6;
logic dbnk_dbe6;
logic dbnk_init_done7;
logic dbnk_e2e_err7;
logic dbnk_sbe7;
logic dbnk_dbe7;
npu_grp_sfty_monitor u_npu_grp_sfty_monitor(
    `AXIINST_EXT(sfty_cfg_axi_,iaxi_cfg_),
   // dbank_top ctrl and status
    .dbnk_ecc_en(dbnk_ecc_en),
    .dbnk_scrub_en(dbnk_scrub_en),
    .dbnk_init(dbnk_init),
    .dbnk_init_done0(dbnk_init_done0),
    .dbnk_sbe0(dbnk_sbe0),
    .dbnk_dbe0(dbnk_dbe0), // fatal error consist of dbe/addr/unknown
    .dbnk_init_done1(dbnk_init_done1),
    .dbnk_sbe1(dbnk_sbe1),
    .dbnk_dbe1(dbnk_dbe1), // fatal error consist of dbe/addr/unknown
    .dbnk_init_done2(dbnk_init_done2),
    .dbnk_sbe2(dbnk_sbe2),
    .dbnk_dbe2(dbnk_dbe2), // fatal error consist of dbe/addr/unknown
    .dbnk_init_done3(dbnk_init_done3),
    .dbnk_sbe3(dbnk_sbe3),
    .dbnk_dbe3(dbnk_dbe3), // fatal error consist of dbe/addr/unknown
    .dbnk_init_done4(dbnk_init_done4),
    .dbnk_sbe4(dbnk_sbe4),
    .dbnk_dbe4(dbnk_dbe4), // fatal error consist of dbe/addr/unknown
    .dbnk_init_done5(dbnk_init_done5),
    .dbnk_sbe5(dbnk_sbe5),
    .dbnk_dbe5(dbnk_dbe5), // fatal error consist of dbe/addr/unknown
    .dbnk_init_done6(dbnk_init_done6),
    .dbnk_sbe6(dbnk_sbe6),
    .dbnk_dbe6(dbnk_dbe6), // fatal error consist of dbe/addr/unknown
    .dbnk_init_done7(dbnk_init_done7),
    .dbnk_sbe7(dbnk_sbe7),
    .dbnk_dbe7(dbnk_dbe7), // fatal error consist of dbe/addr/unknown
    .scm_dbank_ecc_irq(scm_dbank_ecc_irq),  
    .scm_dbank_sbe(scm_dbank_sbe),
    .scm_dbank_dbe(scm_dbank_dbe),
   // System interface
    .clk      (clk),      // always-on clock
    .rst_a    (rst_sync)   // asynchronous reset, active high, synchronous deassertion

);
 
// spyglass disable_block W287b
//SMD:Unconnect output
//SJ :Intentionally unconnected 
nl2_new_dbank_top_layer
   #( 
    .N_CMD_IDS(CLN_ID_NUM),
    .N_WR_IDS(CLN_ID_NUM),
    .CMD_ADDR_SIZE(CLN_AXIAW)
   ) u_dbank0_top (
    .ds(1'b0),
    .sd(grp_pd_mem),
    `CLN_AXIMST_NOUSR_INSTN(40, axi_, axi_cln_, 0),
    .mem_dbnk_sbe_err(dbnk_sbe0),
    .mem_dbnk_dbe_err(dbnk_dbe0),
    .mem_ecc_enb(dbnk_ecc_en),
    .mem_scrub_enb(dbnk_scrub_en),
    .mem_init(dbnk_init),
    .mem_init_done(dbnk_init_done0),
    .disable_rst_init('0),
    .dbnk_clk  (clk),
    .rst_a     (rst_sync)
  );
nl2_new_dbank_top_layer
   #( 
    .N_CMD_IDS(CLN_ID_NUM),
    .N_WR_IDS(CLN_ID_NUM),
    .CMD_ADDR_SIZE(CLN_AXIAW)
   ) u_dbank1_top (
    .ds(1'b0),
    .sd(grp_pd_mem),
    `CLN_AXIMST_NOUSR_INSTN(40, axi_, axi_cln_, 1),
    .mem_dbnk_sbe_err(dbnk_sbe1),
    .mem_dbnk_dbe_err(dbnk_dbe1),
    .mem_ecc_enb(dbnk_ecc_en),
    .mem_scrub_enb(dbnk_scrub_en),
    .mem_init(dbnk_init),
    .mem_init_done(dbnk_init_done1),
    .disable_rst_init('0),
    .dbnk_clk  (clk),
    .rst_a     (rst_sync)
  );
nl2_new_dbank_top_layer
   #( 
    .N_CMD_IDS(CLN_ID_NUM),
    .N_WR_IDS(CLN_ID_NUM),
    .CMD_ADDR_SIZE(CLN_AXIAW)
   ) u_dbank2_top (
    .ds(1'b0),
    .sd(grp_pd_mem),
    `CLN_AXIMST_NOUSR_INSTN(40, axi_, axi_cln_, 2),
    .mem_dbnk_sbe_err(dbnk_sbe2),
    .mem_dbnk_dbe_err(dbnk_dbe2),
    .mem_ecc_enb(dbnk_ecc_en),
    .mem_scrub_enb(dbnk_scrub_en),
    .mem_init(dbnk_init),
    .mem_init_done(dbnk_init_done2),
    .disable_rst_init('0),
    .dbnk_clk  (clk),
    .rst_a     (rst_sync)
  );
nl2_new_dbank_top_layer
   #( 
    .N_CMD_IDS(CLN_ID_NUM),
    .N_WR_IDS(CLN_ID_NUM),
    .CMD_ADDR_SIZE(CLN_AXIAW)
   ) u_dbank3_top (
    .ds(1'b0),
    .sd(grp_pd_mem),
    `CLN_AXIMST_NOUSR_INSTN(40, axi_, axi_cln_, 3),
    .mem_dbnk_sbe_err(dbnk_sbe3),
    .mem_dbnk_dbe_err(dbnk_dbe3),
    .mem_ecc_enb(dbnk_ecc_en),
    .mem_scrub_enb(dbnk_scrub_en),
    .mem_init(dbnk_init),
    .mem_init_done(dbnk_init_done3),
    .disable_rst_init('0),
    .dbnk_clk  (clk),
    .rst_a     (rst_sync)
  );
nl2_new_dbank_top_layer
   #( 
    .N_CMD_IDS(CLN_ID_NUM),
    .N_WR_IDS(CLN_ID_NUM),
    .CMD_ADDR_SIZE(CLN_AXIAW)
   ) u_dbank4_top (
    .ds(1'b0),
    .sd(grp_pd_mem),
    `CLN_AXIMST_NOUSR_INSTN(40, axi_, axi_cln_, 4),
    .mem_dbnk_sbe_err(dbnk_sbe4),
    .mem_dbnk_dbe_err(dbnk_dbe4),
    .mem_ecc_enb(dbnk_ecc_en),
    .mem_scrub_enb(dbnk_scrub_en),
    .mem_init(dbnk_init),
    .mem_init_done(dbnk_init_done4),
    .disable_rst_init('0),
    .dbnk_clk  (clk),
    .rst_a     (rst_sync)
  );
nl2_new_dbank_top_layer
   #( 
    .N_CMD_IDS(CLN_ID_NUM),
    .N_WR_IDS(CLN_ID_NUM),
    .CMD_ADDR_SIZE(CLN_AXIAW)
   ) u_dbank5_top (
    .ds(1'b0),
    .sd(grp_pd_mem),
    `CLN_AXIMST_NOUSR_INSTN(40, axi_, axi_cln_, 5),
    .mem_dbnk_sbe_err(dbnk_sbe5),
    .mem_dbnk_dbe_err(dbnk_dbe5),
    .mem_ecc_enb(dbnk_ecc_en),
    .mem_scrub_enb(dbnk_scrub_en),
    .mem_init(dbnk_init),
    .mem_init_done(dbnk_init_done5),
    .disable_rst_init('0),
    .dbnk_clk  (clk),
    .rst_a     (rst_sync)
  );
nl2_new_dbank_top_layer
   #( 
    .N_CMD_IDS(CLN_ID_NUM),
    .N_WR_IDS(CLN_ID_NUM),
    .CMD_ADDR_SIZE(CLN_AXIAW)
   ) u_dbank6_top (
    .ds(1'b0),
    .sd(grp_pd_mem),
    `CLN_AXIMST_NOUSR_INSTN(40, axi_, axi_cln_, 6),
    .mem_dbnk_sbe_err(dbnk_sbe6),
    .mem_dbnk_dbe_err(dbnk_dbe6),
    .mem_ecc_enb(dbnk_ecc_en),
    .mem_scrub_enb(dbnk_scrub_en),
    .mem_init(dbnk_init),
    .mem_init_done(dbnk_init_done6),
    .disable_rst_init('0),
    .dbnk_clk  (clk),
    .rst_a     (rst_sync)
  );
nl2_new_dbank_top_layer
   #( 
    .N_CMD_IDS(CLN_ID_NUM),
    .N_WR_IDS(CLN_ID_NUM),
    .CMD_ADDR_SIZE(CLN_AXIAW)
   ) u_dbank7_top (
    .ds(1'b0),
    .sd(grp_pd_mem),
    `CLN_AXIMST_NOUSR_INSTN(40, axi_, axi_cln_, 7),
    .mem_dbnk_sbe_err(dbnk_sbe7),
    .mem_dbnk_dbe_err(dbnk_dbe7),
    .mem_ecc_enb(dbnk_ecc_en),
    .mem_scrub_enb(dbnk_scrub_en),
    .mem_init(dbnk_init),
    .mem_init_done(dbnk_init_done7),
    .disable_rst_init('0),
    .dbnk_clk  (clk),
    .rst_a     (rst_sync)
  );
// spyglass enable_block W287b

//Connect User
always_comb
begin
  integer i;
  for (i=0; i<`NPU_CSM_BANKS_PER_GRP; i++)
  begin
    axi_cln_ruser[i] = '0;
    axi_cln_buser[i] = '0;
  end
end

endmodule : npu_cln_wrap
