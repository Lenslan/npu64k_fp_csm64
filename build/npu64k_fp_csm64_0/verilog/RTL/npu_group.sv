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

// CLN group hierarchy
// vcs -sverilog -f ../../shared/RTL/npu_shared_manifest npu_cln_wrap.sv npu_cln_group.sv npu_cln_1p5.sv

`include "npu_macros.svh"
`include "npu_defines.v"

`include "npu_axi_macros.svh"



module npu_group
  import npu_types::*;
  #(
    parameter int NUMGRP  = 4,  // number of groups, power of 2
    parameter int NUMSLC  = 4,  // number of slices connected to group
    parameter int NUMSTU  = 2,  // number of STU channels connected to group
    parameter int DEVIDW  = 1,  // device port attributes
    parameter int LNKIDW  = 3,  // link ID width = DEVIDW+clog2(NUMGRP)
    parameter int L2IDW   = 3,  // L2 ID width
    parameter int CCMIDW  = 1,  // CCM ID width
    parameter int NOCIDW  = 5,  // NoC ID width
    parameter TOP_CFG_DECBASE_RST_VAL  = 0,
    parameter TOP_CFG_DECSIZE_RST_VAL  = 0,
    parameter TOP_CFG_DECMST_RST_VAL   = 0,
    parameter BOT_CFG_DECBASE_RST_VAL  = 0,
    parameter BOT_CFG_DECSIZE_RST_VAL  = 0,
    parameter BOT_CFG_DECMST_RST_VAL   = 0,
    parameter CCM_CFG_DECBASE_RST_VAL  = 0,
    parameter CCM_CFG_DECSIZE_RST_VAL  = 0,
    parameter CCM_CFG_DECMST_RST_VAL   = 0,
    parameter REMP_CFG_DECBASE_RST_VAL = 0,
    parameter REMP_CFG_DECSIZE_RST_VAL = 0,
    parameter REMP_CFG_DECMST_RST_VAL  = 0
  )
  (
    input  logic [64-1: 0]     vmid,
  // Trace
    input      logic            sl0_rtt_swe_val,
    input      logic [32:0]     sl0_rtt_swe_data,
    input      logic [7:0]      sl0_rtt_swe_ext,
    input      logic            sl1_rtt_swe_val,
    input      logic [32:0]     sl1_rtt_swe_data,
    input      logic [7:0]      sl1_rtt_swe_ext,
    input      logic            sl2_rtt_swe_val,
    input      logic [32:0]     sl2_rtt_swe_data,
    input      logic [7:0]      sl2_rtt_swe_ext,
    input      logic            sl3_rtt_swe_val,
    input      logic [32:0]     sl3_rtt_swe_data,
    input      logic [7:0]      sl3_rtt_swe_ext,
    output     logic            rtt_swe_val,
    output     logic [32:0]     rtt_swe_data,
    output     logic [7:0]      rtt_swe_ext,
    input      logic            rtt_swe_prdcr_en,
    input      logic                          grp_pwr_dwn_a,      // power-down a group and return err response
    input      logic                          slice0_pwr_dwn_a, 
    input      logic                          slice1_pwr_dwn_a, 
    input      logic                          slice2_pwr_dwn_a, 
    input      logic                          slice3_pwr_dwn_a, 
    input      logic                          grp_isolate,  
    input      logic                          grp_isolate_n,
    input      logic                          grp_pd_mem,   
    input      logic                          grp_pd_logic,
    output logic                              scm_dbank_ecc_irq,
   // report dbank sbe/dbe: to NPX top
    output logic                              scm_dbank_sbe,
    output logic                              scm_dbank_dbe,
    // STU events and interrupts
    output     logic [NUMSTU-1:0]             stu_done_evt,
    output     logic [NUMSTU-1:0]             stu_issue_evt,
    output     logic [NUMSTU-1:0]             stu_done_irq_a,
    output     logic [NUMSTU-1:0]             stu_err_irq_a,
    //dev and ccm ports
    input  logic                                                                                                        sl0_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl0_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl0_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl0_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl0_dev_axi_gals_aw_rpnt,
  input  logic [(64*VSIZE)+(64*VSIZE)/8+SLICE_DMA_WUW:0]                                                           sl0_dev_axi_gals_w_data,
  output logic [`NUM_FLANES((64*VSIZE)+(64*VSIZE)/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl0_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl0_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl0_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl0_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl0_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl0_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl0_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl0_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl0_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl0_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl0_dev_axi_gals_ar_rpnt,
  output logic [1+(64*VSIZE)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl0_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+(64*VSIZE)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl0_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl0_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl0_dev_axi_gals_r_rpnt_a,
        output logic                                                                                                        sl0_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl0_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl0_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl0_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl0_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl0_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl0_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl0_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl0_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl0_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl0_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl0_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl0_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl0_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl0_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl0_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl0_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl0_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl0_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl0_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl0_ccm_axi_gals_r_rpnt,
    input  logic                                                                                                        sl1_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl1_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl1_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl1_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl1_dev_axi_gals_aw_rpnt,
  input  logic [(64*VSIZE)+(64*VSIZE)/8+SLICE_DMA_WUW:0]                                                           sl1_dev_axi_gals_w_data,
  output logic [`NUM_FLANES((64*VSIZE)+(64*VSIZE)/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl1_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl1_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl1_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl1_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl1_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl1_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl1_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl1_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl1_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl1_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl1_dev_axi_gals_ar_rpnt,
  output logic [1+(64*VSIZE)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl1_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+(64*VSIZE)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl1_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl1_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl1_dev_axi_gals_r_rpnt_a,
        output logic                                                                                                        sl1_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl1_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl1_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl1_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl1_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl1_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl1_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl1_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl1_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl1_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl1_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl1_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl1_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl1_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl1_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl1_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl1_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl1_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl1_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl1_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl1_ccm_axi_gals_r_rpnt,
    input  logic                                                                                                        sl2_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl2_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl2_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl2_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl2_dev_axi_gals_aw_rpnt,
  input  logic [(64*VSIZE)+(64*VSIZE)/8+SLICE_DMA_WUW:0]                                                           sl2_dev_axi_gals_w_data,
  output logic [`NUM_FLANES((64*VSIZE)+(64*VSIZE)/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl2_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl2_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl2_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl2_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl2_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl2_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl2_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl2_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl2_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl2_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl2_dev_axi_gals_ar_rpnt,
  output logic [1+(64*VSIZE)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl2_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+(64*VSIZE)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl2_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl2_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl2_dev_axi_gals_r_rpnt_a,
        output logic                                                                                                        sl2_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl2_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl2_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl2_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl2_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl2_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl2_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl2_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl2_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl2_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl2_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl2_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl2_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl2_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl2_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl2_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl2_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl2_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl2_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl2_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl2_ccm_axi_gals_r_rpnt,
    input  logic                                                                                                        sl3_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl3_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl3_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl3_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl3_dev_axi_gals_aw_rpnt,
  input  logic [(64*VSIZE)+(64*VSIZE)/8+SLICE_DMA_WUW:0]                                                           sl3_dev_axi_gals_w_data,
  output logic [`NUM_FLANES((64*VSIZE)+(64*VSIZE)/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl3_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl3_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl3_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl3_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl3_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl3_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl3_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl3_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl3_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl3_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl3_dev_axi_gals_ar_rpnt,
  output logic [1+(64*VSIZE)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl3_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+(64*VSIZE)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl3_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl3_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl3_dev_axi_gals_r_rpnt_a,
        output logic                                                                                                        sl3_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl3_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl3_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl3_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl3_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl3_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl3_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl3_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl3_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl3_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl3_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl3_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl3_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl3_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl3_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl3_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl3_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl3_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl3_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl3_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl3_ccm_axi_gals_r_rpnt,

    // configuration device ports
    input  logic                                                                                            axi_cfg_grp_sync_clk_req,
  input  logic [1+1+$bits(npu_axi_cmd_t)-1:0]                                    axi_cfg_grp_sync_aw_data,
  output logic [`NUM_FLANES(1+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_cfg_grp_sync_aw_rdpnt,
  input  logic [0:0]                                                                           axi_cfg_grp_sync_aw_wpnt,
  output logic [0:0]                                                                           axi_cfg_grp_sync_aw_rpnt,
  input  logic [32+32/8+1:0]                                               axi_cfg_grp_sync_w_data,
  output logic [`NUM_FLANES(32+32/8+1+1)-1:0][(1<<0)-1:0]          axi_cfg_grp_sync_w_rdpnt,
  input  logic [0:0]                                                                            axi_cfg_grp_sync_w_wpnt,
  output logic [0:0]                                                                            axi_cfg_grp_sync_w_rpnt,
  output logic [1+1+$bits(npu_axi_resp_t)-1:0]                                    axi_cfg_grp_sync_b_data,
  input  logic [`NUM_FLANES(1+1+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]   axi_cfg_grp_sync_b_rdpnt,
  output logic [0:0]                                                                            axi_cfg_grp_sync_b_wpnt,
  input  logic [0:0]                                                                            axi_cfg_grp_sync_b_rpnt,
  input  logic [1+1+$bits(npu_axi_cmd_t)-1:0]                                    axi_cfg_grp_sync_ar_data,
  output logic [`NUM_FLANES(1+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_cfg_grp_sync_ar_rdpnt,
  input  logic [0:0]                                                                           axi_cfg_grp_sync_ar_wpnt,
  output logic [0:0]                                                                           axi_cfg_grp_sync_ar_rpnt,
  output logic [1+32+$bits(npu_axi_resp_t)+1:0]                          axi_cfg_grp_sync_r_data,
  input  logic [`NUM_FLANES(1+32+$bits(npu_axi_resp_t)+1+1)-1:0][(1<<0)-1:0] axi_cfg_grp_sync_r_rdpnt,
  output logic [0:0]                                                                            axi_cfg_grp_sync_r_wpnt,
  input  logic [0:0]                                                                            axi_cfg_grp_sync_r_rpnt,

    // L2 device port
        input  logic                                                                                            axi_mst_sync_clk_req,
  input  logic [L2IDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_mst_sync_aw_data,
  output logic [`NUM_FLANES(L2IDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_mst_sync_aw_rdpnt,
  input  logic [0:0]                                                                           axi_mst_sync_aw_wpnt,
  output logic [0:0]                                                                           axi_mst_sync_aw_rpnt,
  input  logic [(VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW:0]                                               axi_mst_sync_w_data,
  output logic [`NUM_FLANES((VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]          axi_mst_sync_w_rdpnt,
  input  logic [1:0]                                                                            axi_mst_sync_w_wpnt,
  output logic [1:0]                                                                            axi_mst_sync_w_rpnt,
  output logic [L2IDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                    axi_mst_sync_b_data,
  input  logic [`NUM_FLANES(L2IDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]   axi_mst_sync_b_rdpnt,
  output logic [0:0]                                                                            axi_mst_sync_b_wpnt,
  input  logic [0:0]                                                                            axi_mst_sync_b_rpnt,
  input  logic [L2IDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_mst_sync_ar_data,
  output logic [`NUM_FLANES(L2IDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_mst_sync_ar_rdpnt,
  input  logic [0:0]                                                                           axi_mst_sync_ar_wpnt,
  output logic [0:0]                                                                           axi_mst_sync_ar_rpnt,
  output logic [L2IDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                          axi_mst_sync_r_data,
  input  logic [`NUM_FLANES(L2IDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_mst_sync_r_rdpnt,
  output logic [1:0]                                                                            axi_mst_sync_r_wpnt,
  input  logic [1:0]                                                                            axi_mst_sync_r_rpnt,

    // L2 CCM port
        output logic                                                                                                  axi_ccm_sync_clk_req,
  output logic [CCMIDW+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_ccm_sync_aw_data,
  input  logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_ccm_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_ccm_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_ccm_sync_aw_rpnt,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                     axi_ccm_sync_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<0)-1:0]                axi_ccm_sync_w_rdpnt,
  output logic [0:0]                                                                                  axi_ccm_sync_w_wpnt,
  input  logic [0:0]                                                                                  axi_ccm_sync_w_rpnt,
  input  logic [CCMIDW+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                          axi_ccm_sync_b_data,
  output logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_ccm_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_ccm_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_ccm_sync_b_rpnt,
  output logic [CCMIDW+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_ccm_sync_ar_data,
  input  logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_ccm_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_ccm_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_ccm_sync_ar_rpnt,
  input  logic [CCMIDW+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                axi_ccm_sync_r_data,
  output logic [`NUM_FLANES(CCMIDW+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<0)-1:0] axi_ccm_sync_r_rdpnt,
  input  logic [0:0]                                                                                  axi_ccm_sync_r_wpnt,
  output logic [0:0]                                                                                  axi_ccm_sync_r_rpnt,

    // NoC port
    output logic                                                                                                        npu_grp_noc_axi_gals_clk_req,
  output logic [5+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                npu_grp_noc_axi_gals_aw_data,
  input  logic [`NUM_FLANES(5+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              npu_grp_noc_axi_gals_aw_rdpnt,
  output logic [1:0]                                                                                       npu_grp_noc_axi_gals_aw_wpnt,
  input  logic [1:0]                                                                                       npu_grp_noc_axi_gals_aw_rpnt_a,
  output logic [(VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW:0]                                                           npu_grp_noc_axi_gals_w_data,
  input  logic [`NUM_FLANES((VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      npu_grp_noc_axi_gals_w_rdpnt,
  output logic [3:0]                                                                                        npu_grp_noc_axi_gals_w_wpnt,
  input  logic [3:0]                                                                                        npu_grp_noc_axi_gals_w_rpnt_a,
  input  logic [5+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                npu_grp_noc_axi_gals_b_data,
  output logic [`NUM_FLANES(5+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               npu_grp_noc_axi_gals_b_rdpnt,
  input  logic [1:0]                                                                                        npu_grp_noc_axi_gals_b_wpnt_a,
  output logic [1:0]                                                                                        npu_grp_noc_axi_gals_b_rpnt,
  output logic [5+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                npu_grp_noc_axi_gals_ar_data,
  input  logic [`NUM_FLANES(5+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              npu_grp_noc_axi_gals_ar_rdpnt,
  output logic [1:0]                                                                                       npu_grp_noc_axi_gals_ar_wpnt,
  input  logic [1:0]                                                                                       npu_grp_noc_axi_gals_ar_rpnt_a,
  input  logic [5+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      npu_grp_noc_axi_gals_r_data,
  output logic [`NUM_FLANES(5+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] npu_grp_noc_axi_gals_r_rdpnt,
  input  logic [3:0]                                                                                        npu_grp_noc_axi_gals_r_wpnt_a,
  output logic [3:0]                                                                                        npu_grp_noc_axi_gals_r_rpnt,

    // egress links to from groups
    // -egress link0
    output logic                                                                                                  axi_egress0_sync_clk_req,
  output logic [LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_egress0_sync_aw_data,
  input  logic [`NUM_FLANES(LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_egress0_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_egress0_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_egress0_sync_aw_rpnt,
  output logic [(VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW:0]                                                     axi_egress0_sync_w_data,
  input  logic [`NUM_FLANES((VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]                axi_egress0_sync_w_rdpnt,
  output logic [1:0]                                                                                  axi_egress0_sync_w_wpnt,
  input  logic [1:0]                                                                                  axi_egress0_sync_w_rpnt,
  input  logic [LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                          axi_egress0_sync_b_data,
  output logic [`NUM_FLANES(LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_egress0_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_egress0_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_egress0_sync_b_rpnt,
  output logic [LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_egress0_sync_ar_data,
  input  logic [`NUM_FLANES(LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_egress0_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_egress0_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_egress0_sync_ar_rpnt,
  input  logic [LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                axi_egress0_sync_r_data,
  output logic [`NUM_FLANES(LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_egress0_sync_r_rdpnt,
  input  logic [1:0]                                                                                  axi_egress0_sync_r_wpnt,
  output logic [1:0]                                                                                  axi_egress0_sync_r_rpnt,

    // -egress link1
    output logic                                                                                                  axi_egress1_sync_clk_req,
  output logic [LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_egress1_sync_aw_data,
  input  logic [`NUM_FLANES(LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_egress1_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_egress1_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_egress1_sync_aw_rpnt,
  output logic [(VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW:0]                                                     axi_egress1_sync_w_data,
  input  logic [`NUM_FLANES((VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]                axi_egress1_sync_w_rdpnt,
  output logic [1:0]                                                                                  axi_egress1_sync_w_wpnt,
  input  logic [1:0]                                                                                  axi_egress1_sync_w_rpnt,
  input  logic [LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                          axi_egress1_sync_b_data,
  output logic [`NUM_FLANES(LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_egress1_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_egress1_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_egress1_sync_b_rpnt,
  output logic [LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_egress1_sync_ar_data,
  input  logic [`NUM_FLANES(LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_egress1_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_egress1_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_egress1_sync_ar_rpnt,
  input  logic [LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                axi_egress1_sync_r_data,
  output logic [`NUM_FLANES(LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_egress1_sync_r_rdpnt,
  input  logic [1:0]                                                                                  axi_egress1_sync_r_wpnt,
  output logic [1:0]                                                                                  axi_egress1_sync_r_rpnt,

    // -egress link2
    output logic                                                                                                  axi_egress2_sync_clk_req,
  output logic [LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_egress2_sync_aw_data,
  input  logic [`NUM_FLANES(LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_egress2_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_egress2_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_egress2_sync_aw_rpnt,
  output logic [(VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW:0]                                                     axi_egress2_sync_w_data,
  input  logic [`NUM_FLANES((VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]                axi_egress2_sync_w_rdpnt,
  output logic [1:0]                                                                                  axi_egress2_sync_w_wpnt,
  input  logic [1:0]                                                                                  axi_egress2_sync_w_rpnt,
  input  logic [LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                          axi_egress2_sync_b_data,
  output logic [`NUM_FLANES(LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_egress2_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_egress2_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_egress2_sync_b_rpnt,
  output logic [LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_egress2_sync_ar_data,
  input  logic [`NUM_FLANES(LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_egress2_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_egress2_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_egress2_sync_ar_rpnt,
  input  logic [LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                axi_egress2_sync_r_data,
  output logic [`NUM_FLANES(LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_egress2_sync_r_rdpnt,
  input  logic [1:0]                                                                                  axi_egress2_sync_r_wpnt,
  output logic [1:0]                                                                                  axi_egress2_sync_r_rpnt,


     input      logic                   inter_grp_0_pwr_dwn_a,
     input      logic                   inter_grp_1_pwr_dwn_a,
     input      logic                   inter_grp_2_pwr_dwn_a,
    // ingress links from other groups
    //-ingress link0
    input  logic                                                                                            axi_ingress0_sync_clk_req,
  input  logic [LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ingress0_sync_aw_data,
  output logic [`NUM_FLANES(LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ingress0_sync_aw_rdpnt,
  input  logic [0:0]                                                                           axi_ingress0_sync_aw_wpnt,
  output logic [0:0]                                                                           axi_ingress0_sync_aw_rpnt,
  input  logic [(VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW:0]                                               axi_ingress0_sync_w_data,
  output logic [`NUM_FLANES((VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]          axi_ingress0_sync_w_rdpnt,
  input  logic [1:0]                                                                            axi_ingress0_sync_w_wpnt,
  output logic [1:0]                                                                            axi_ingress0_sync_w_rpnt,
  output logic [LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                    axi_ingress0_sync_b_data,
  input  logic [`NUM_FLANES(LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]   axi_ingress0_sync_b_rdpnt,
  output logic [0:0]                                                                            axi_ingress0_sync_b_wpnt,
  input  logic [0:0]                                                                            axi_ingress0_sync_b_rpnt,
  input  logic [LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ingress0_sync_ar_data,
  output logic [`NUM_FLANES(LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ingress0_sync_ar_rdpnt,
  input  logic [0:0]                                                                           axi_ingress0_sync_ar_wpnt,
  output logic [0:0]                                                                           axi_ingress0_sync_ar_rpnt,
  output logic [LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                          axi_ingress0_sync_r_data,
  input  logic [`NUM_FLANES(LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_ingress0_sync_r_rdpnt,
  output logic [1:0]                                                                            axi_ingress0_sync_r_wpnt,
  input  logic [1:0]                                                                            axi_ingress0_sync_r_rpnt,

    //-ingress link1
    input  logic                                                                                            axi_ingress1_sync_clk_req,
  input  logic [LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ingress1_sync_aw_data,
  output logic [`NUM_FLANES(LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ingress1_sync_aw_rdpnt,
  input  logic [0:0]                                                                           axi_ingress1_sync_aw_wpnt,
  output logic [0:0]                                                                           axi_ingress1_sync_aw_rpnt,
  input  logic [(VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW:0]                                               axi_ingress1_sync_w_data,
  output logic [`NUM_FLANES((VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]          axi_ingress1_sync_w_rdpnt,
  input  logic [1:0]                                                                            axi_ingress1_sync_w_wpnt,
  output logic [1:0]                                                                            axi_ingress1_sync_w_rpnt,
  output logic [LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                    axi_ingress1_sync_b_data,
  input  logic [`NUM_FLANES(LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]   axi_ingress1_sync_b_rdpnt,
  output logic [0:0]                                                                            axi_ingress1_sync_b_wpnt,
  input  logic [0:0]                                                                            axi_ingress1_sync_b_rpnt,
  input  logic [LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ingress1_sync_ar_data,
  output logic [`NUM_FLANES(LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ingress1_sync_ar_rdpnt,
  input  logic [0:0]                                                                           axi_ingress1_sync_ar_wpnt,
  output logic [0:0]                                                                           axi_ingress1_sync_ar_rpnt,
  output logic [LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                          axi_ingress1_sync_r_data,
  input  logic [`NUM_FLANES(LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_ingress1_sync_r_rdpnt,
  output logic [1:0]                                                                            axi_ingress1_sync_r_wpnt,
  input  logic [1:0]                                                                            axi_ingress1_sync_r_rpnt,

    //-ingress link2
    input  logic                                                                                            axi_ingress2_sync_clk_req,
  input  logic [LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ingress2_sync_aw_data,
  output logic [`NUM_FLANES(LNKIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ingress2_sync_aw_rdpnt,
  input  logic [0:0]                                                                           axi_ingress2_sync_aw_wpnt,
  output logic [0:0]                                                                           axi_ingress2_sync_aw_rpnt,
  input  logic [(VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW:0]                                               axi_ingress2_sync_w_data,
  output logic [`NUM_FLANES((VSIZE*64)+(VSIZE*64)/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]          axi_ingress2_sync_w_rdpnt,
  input  logic [1:0]                                                                            axi_ingress2_sync_w_wpnt,
  output logic [1:0]                                                                            axi_ingress2_sync_w_rpnt,
  output logic [LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                    axi_ingress2_sync_b_data,
  input  logic [`NUM_FLANES(LNKIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]   axi_ingress2_sync_b_rdpnt,
  output logic [0:0]                                                                            axi_ingress2_sync_b_wpnt,
  input  logic [0:0]                                                                            axi_ingress2_sync_b_rpnt,
  input  logic [LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ingress2_sync_ar_data,
  output logic [`NUM_FLANES(LNKIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ingress2_sync_ar_rdpnt,
  input  logic [0:0]                                                                           axi_ingress2_sync_ar_wpnt,
  output logic [0:0]                                                                           axi_ingress2_sync_ar_rpnt,
  output logic [LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                          axi_ingress2_sync_r_data,
  input  logic [`NUM_FLANES(LNKIDW+(VSIZE*64)+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_ingress2_sync_r_rdpnt,
  output logic [1:0]                                                                            axi_ingress2_sync_r_wpnt,
  input  logic [1:0]                                                                            axi_ingress2_sync_r_rpnt,



    // general interface
    input      logic                          grp_clk,            // clock per group
    input      logic                          grp_clk_en_a,       // clock enable per group
    input      logic                          grp_rst_a,          // Asynchronous reset per group
    input      logic [1:0]                    ptidx_a,
    input      logic                          test_mode
  );

    localparam NUM_TRACE_SRC = `NPU_NUM_STU_PER_GRP+`NPU_NUM_SLC_PER_GRP;
// spyglass disable_block W401
// SMD: Clock is not input
// SJ: Internal gated clock
    logic [64-1: 0]            vmid_del;
    logic                          grp_clk_gated;    // clock per group
// spyglass enable_block W401
    logic                          grp_clk_en;       // clock enable per group
    logic                          grp_rst;          // Asynchronous reset per group
    logic                          grp_pwr_dwn;      // power-down a group and return err response
    logic                          grp_clk_en_sync;
    logic                          axi_ingrs_tgt_clk_req0;
    logic                          axi_ingrs_tgt_clk_req0_sync;
    logic                          axi_ingrs_tgt_clk_req1;
    logic                          axi_ingrs_tgt_clk_req1_sync;
    logic                          axi_ingrs_tgt_clk_req2;
    logic                          axi_ingrs_tgt_clk_req2_sync;
    logic                          axi_tgt_clk_req0;
    logic                          axi_tgt_clk_req0_sync;
    logic                          axi_tgt_clk_req1;
    logic                          axi_tgt_clk_req1_sync;
    logic                          axi_tgt_clk_req2;
    logic                          axi_tgt_clk_req2_sync;
    logic                          axi_tgt_clk_req3;
    logic                          axi_tgt_clk_req3_sync;
    logic                          axi_dmi_mst_tgt_clk_req;
    logic                          axi_dmi_mst_tgt_clk_req_sync;
    logic                          axi_cfg_mst_tgt_clk_req;
    logic                          axi_cfg_mst_tgt_clk_req_sync;
    logic                          grp_clk_en_auto;   // autonomous clock enable

    `TRCWIRES(stu_trace_,`NPU_NUM_STU_PER_GRP);
    `AXIWIRES(1,32,1,1,1,1,1,axi_cfg_);
    `AXIWIRES(CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_l2_);
    `AXIWIRES(L2IDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_dev_l2_);
    `AXIWIRESN(NUMGRP-1,LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_egress_);
    `AXIWIRESN(NUMGRP-1,LNKIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_ingress_);
    // slice device ports
    `AXIWIRESN(NUMSLC,DEVIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_dev_slice_);
    // slice CCM ports
    `AXIWIRESN(NUMSLC,CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_slice_);
  
    // STU device ports
    `AXIWIRESN(NUMSTU,DEVIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_dev_stu_);
    // STU MMIO CCM ports
    `AXIWIRESN(NUMSTU,CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_stu_);
    // NoC port
    `AXIWIRES(NOCIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_noc_);

  npu_reset_ctrl 
  u_sync_grp_rst
  (
    .clk        ( grp_clk   ),
    .rst_a      ( grp_rst_a ),
    .test_mode  ( test_mode ),
    .rst        ( grp_rst   )
  );

  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_grp_clken_en_cdc_sync
  (
    .clk   ( grp_clk         ),
    .rst_a ( grp_rst         ),
    .din   ( {1{grp_clk_en_a}}    ),
    .dout  ( grp_clk_en_sync )
  );

  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_axi_ingrs_tgt_clk_req0_cdc_sync
  (
    .clk   ( grp_clk         ),
    .rst_a ( grp_rst         ),
    .din   ( {1{axi_ingrs_tgt_clk_req0}} ),
    .dout  ( axi_ingrs_tgt_clk_req0_sync )
  );
  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_axi_ingrs_tgt_clk_req1_cdc_sync
  (
    .clk   ( grp_clk         ),
    .rst_a ( grp_rst         ),
    .din   ( {1{axi_ingrs_tgt_clk_req1}} ),
    .dout  ( axi_ingrs_tgt_clk_req1_sync )
  );
  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_axi_ingrs_tgt_clk_req2_cdc_sync
  (
    .clk   ( grp_clk         ),
    .rst_a ( grp_rst         ),
    .din   ( {1{axi_ingrs_tgt_clk_req2}} ),
    .dout  ( axi_ingrs_tgt_clk_req2_sync )
  );
    
  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_axi_tgt_clk_req0_cdc_sync
  (
    .clk   ( grp_clk         ),
    .rst_a ( grp_rst         ),
    .din   ( {1{axi_tgt_clk_req0}} ),
    .dout  ( axi_tgt_clk_req0_sync )
  );
  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_axi_tgt_clk_req1_cdc_sync
  (
    .clk   ( grp_clk         ),
    .rst_a ( grp_rst         ),
    .din   ( {1{axi_tgt_clk_req1}} ),
    .dout  ( axi_tgt_clk_req1_sync )
  );
  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_axi_tgt_clk_req2_cdc_sync
  (
    .clk   ( grp_clk         ),
    .rst_a ( grp_rst         ),
    .din   ( {1{axi_tgt_clk_req2}} ),
    .dout  ( axi_tgt_clk_req2_sync )
  );
  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_axi_tgt_clk_req3_cdc_sync
  (
    .clk   ( grp_clk         ),
    .rst_a ( grp_rst         ),
    .din   ( {1{axi_tgt_clk_req3}} ),
    .dout  ( axi_tgt_clk_req3_sync )
  );

  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_axi_dmi_mst_tgt_clk_req_cdc_sync
  (
    .clk   ( grp_clk         ),
    .rst_a ( grp_rst         ),
    .din   ( {1{axi_dmi_mst_tgt_clk_req}} ),
    .dout  ( axi_dmi_mst_tgt_clk_req_sync )
  );

  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_axi_cfg_mst_tgt_clk_req_cdc_sync
  (
    .clk   ( grp_clk         ),
    .rst_a ( grp_rst         ),
    .din   ( {1{axi_cfg_mst_tgt_clk_req}} ),
    .dout  ( axi_cfg_mst_tgt_clk_req_sync )
  );

  assign grp_clk_en = grp_clk_en_sync |
                      axi_ingrs_tgt_clk_req0_sync |
                      axi_ingrs_tgt_clk_req1_sync |
                      axi_ingrs_tgt_clk_req2_sync |
                      axi_tgt_clk_req0_sync |
                      axi_tgt_clk_req1_sync |
                      axi_tgt_clk_req2_sync |
                      axi_tgt_clk_req3_sync |
                      axi_dmi_mst_tgt_clk_req_sync |
                      axi_cfg_mst_tgt_clk_req_sync;

  npu_clkgate
  u_clkgate_grp
  (
    .clk_in       ( grp_clk    ),
    .clock_enable ( grp_clk_en ),
    .clk_out      ( grp_clk_gated)
  );

  //
  // Async AXI split bridges on NoC interface
  //
  npu_axi_async_ini
  #(
    .AXIIDW         ( 5                 ),
    .AXIDW          ( 64*VSIZE          ),
    .AXIAWUW        ( SLICE_DMA_AWUW    ),
    .AXIWUW         ( SLICE_DMA_WUW     ),
    .AXIBUW         ( SLICE_DMA_BUW     ),
    .AXIARUW        ( SLICE_DMA_ARUW    ),
    .AXIRUW         ( SLICE_DMA_RUW     ),
    .AWFIFO_DEPTHL2 ( 1                 ),
    .WFIFO_DEPTHL2  ( 3                 ),
    .BFIFO_DEPTHL2  ( 1                 ),
    .ARFIFO_DEPTHL2 ( 1                 ),
    .RFIFO_DEPTHL2  ( 3                 )
  )
  u_noc_axi_ini
  (
    .axi_slv_clk   ( grp_clk_gated ), 
    .axi_slv_rst_a ( grp_rst_a     ),
    .tgt_pwr_dwn_a ( 1'b0          ),  //always-on
    .test_mode     ( test_mode     ),
    `AXIINST(axi_slv_,axi_noc_),
    `AXIASYNCMSUB(axi_async_mst_,npu_grp_noc_axi_gals_)
   );  

  //
  // Async AXI split bridges on slice interface
  //
  npu_axi_async_tgt
  #(
    .AXIIDW         ( 1                ),
    .AXIDW          ( 64*VSIZE         ),
    .AXIAWUW        ( SLICE_DMA_AWUW   ),
    .AXIWUW         ( SLICE_DMA_WUW    ),
    .AXIBUW         ( SLICE_DMA_BUW    ),
    .AXIARUW        ( SLICE_DMA_ARUW   ),
    .AXIRUW         ( SLICE_DMA_RUW    ),
    .AWFIFO_DEPTHL2 ( 1                ),
    .WFIFO_DEPTHL2  ( 3                ),
    .BFIFO_DEPTHL2  ( 1                ),
    .ARFIFO_DEPTHL2 ( 1                ),
    .RFIFO_DEPTHL2  ( 3                )
  )
  u_axi_tgt0
  (
    .axi_mst_clk   ( grp_clk_gated ), 
    .axi_mst_rst_a ( grp_rst_a     ),
    .ini_pwr_dwn_a ( slice0_pwr_dwn_a),
    .test_mode     ( test_mode     ),
    .clk_req_a     ( axi_tgt_clk_req0  ),  
    `AXIINSTM(0,axi_mst_,axi_dev_slice_),
    `AXIASYNCSSUB(axi_async_slv_,sl0_dev_axi_gals_)
  );

  npu_axi_async_ini
  #(
    .AXIIDW         ( 1                 ),
    .AXIDW          ( 64                ),
    .AXIAWUW        ( SLICE_MMIO_AWUW   ),
    .AXIWUW         ( SLICE_MMIO_WUW    ),
    .AXIBUW         ( SLICE_MMIO_BUW    ),
    .AXIARUW        ( SLICE_MMIO_ARUW   ),
    .AXIRUW         ( SLICE_MMIO_RUW    ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_ini0
  (
    .axi_slv_clk   ( grp_clk_gated       ), 
    .axi_slv_rst_a ( grp_rst_a           ),
    .tgt_pwr_dwn_a ( slice0_pwr_dwn_a ), 
    .test_mode     ( test_mode           ),
    `AXIINSTM(0,axi_slv_,axi_ccm_slice_),
    `AXIASYNCMSUB(axi_async_mst_,sl0_ccm_axi_gals_)
   );  
  npu_axi_async_tgt
  #(
    .AXIIDW         ( 1                ),
    .AXIDW          ( 64*VSIZE         ),
    .AXIAWUW        ( SLICE_DMA_AWUW   ),
    .AXIWUW         ( SLICE_DMA_WUW    ),
    .AXIBUW         ( SLICE_DMA_BUW    ),
    .AXIARUW        ( SLICE_DMA_ARUW   ),
    .AXIRUW         ( SLICE_DMA_RUW    ),
    .AWFIFO_DEPTHL2 ( 1                ),
    .WFIFO_DEPTHL2  ( 3                ),
    .BFIFO_DEPTHL2  ( 1                ),
    .ARFIFO_DEPTHL2 ( 1                ),
    .RFIFO_DEPTHL2  ( 3                )
  )
  u_axi_tgt1
  (
    .axi_mst_clk   ( grp_clk_gated ), 
    .axi_mst_rst_a ( grp_rst_a     ),
    .ini_pwr_dwn_a ( slice1_pwr_dwn_a),
    .test_mode     ( test_mode     ),
    .clk_req_a     ( axi_tgt_clk_req1  ),  
    `AXIINSTM(1,axi_mst_,axi_dev_slice_),
    `AXIASYNCSSUB(axi_async_slv_,sl1_dev_axi_gals_)
  );

  npu_axi_async_ini
  #(
    .AXIIDW         ( 1                 ),
    .AXIDW          ( 64                ),
    .AXIAWUW        ( SLICE_MMIO_AWUW   ),
    .AXIWUW         ( SLICE_MMIO_WUW    ),
    .AXIBUW         ( SLICE_MMIO_BUW    ),
    .AXIARUW        ( SLICE_MMIO_ARUW   ),
    .AXIRUW         ( SLICE_MMIO_RUW    ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_ini1
  (
    .axi_slv_clk   ( grp_clk_gated       ), 
    .axi_slv_rst_a ( grp_rst_a           ),
    .tgt_pwr_dwn_a ( slice1_pwr_dwn_a ), 
    .test_mode     ( test_mode           ),
    `AXIINSTM(1,axi_slv_,axi_ccm_slice_),
    `AXIASYNCMSUB(axi_async_mst_,sl1_ccm_axi_gals_)
   );  
  npu_axi_async_tgt
  #(
    .AXIIDW         ( 1                ),
    .AXIDW          ( 64*VSIZE         ),
    .AXIAWUW        ( SLICE_DMA_AWUW   ),
    .AXIWUW         ( SLICE_DMA_WUW    ),
    .AXIBUW         ( SLICE_DMA_BUW    ),
    .AXIARUW        ( SLICE_DMA_ARUW   ),
    .AXIRUW         ( SLICE_DMA_RUW    ),
    .AWFIFO_DEPTHL2 ( 1                ),
    .WFIFO_DEPTHL2  ( 3                ),
    .BFIFO_DEPTHL2  ( 1                ),
    .ARFIFO_DEPTHL2 ( 1                ),
    .RFIFO_DEPTHL2  ( 3                )
  )
  u_axi_tgt2
  (
    .axi_mst_clk   ( grp_clk_gated ), 
    .axi_mst_rst_a ( grp_rst_a     ),
    .ini_pwr_dwn_a ( slice2_pwr_dwn_a),
    .test_mode     ( test_mode     ),
    .clk_req_a     ( axi_tgt_clk_req2  ),  
    `AXIINSTM(2,axi_mst_,axi_dev_slice_),
    `AXIASYNCSSUB(axi_async_slv_,sl2_dev_axi_gals_)
  );

  npu_axi_async_ini
  #(
    .AXIIDW         ( 1                 ),
    .AXIDW          ( 64                ),
    .AXIAWUW        ( SLICE_MMIO_AWUW   ),
    .AXIWUW         ( SLICE_MMIO_WUW    ),
    .AXIBUW         ( SLICE_MMIO_BUW    ),
    .AXIARUW        ( SLICE_MMIO_ARUW   ),
    .AXIRUW         ( SLICE_MMIO_RUW    ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_ini2
  (
    .axi_slv_clk   ( grp_clk_gated       ), 
    .axi_slv_rst_a ( grp_rst_a           ),
    .tgt_pwr_dwn_a ( slice2_pwr_dwn_a ), 
    .test_mode     ( test_mode           ),
    `AXIINSTM(2,axi_slv_,axi_ccm_slice_),
    `AXIASYNCMSUB(axi_async_mst_,sl2_ccm_axi_gals_)
   );  
  npu_axi_async_tgt
  #(
    .AXIIDW         ( 1                ),
    .AXIDW          ( 64*VSIZE         ),
    .AXIAWUW        ( SLICE_DMA_AWUW   ),
    .AXIWUW         ( SLICE_DMA_WUW    ),
    .AXIBUW         ( SLICE_DMA_BUW    ),
    .AXIARUW        ( SLICE_DMA_ARUW   ),
    .AXIRUW         ( SLICE_DMA_RUW    ),
    .AWFIFO_DEPTHL2 ( 1                ),
    .WFIFO_DEPTHL2  ( 3                ),
    .BFIFO_DEPTHL2  ( 1                ),
    .ARFIFO_DEPTHL2 ( 1                ),
    .RFIFO_DEPTHL2  ( 3                )
  )
  u_axi_tgt3
  (
    .axi_mst_clk   ( grp_clk_gated ), 
    .axi_mst_rst_a ( grp_rst_a     ),
    .ini_pwr_dwn_a ( slice3_pwr_dwn_a),
    .test_mode     ( test_mode     ),
    .clk_req_a     ( axi_tgt_clk_req3  ),  
    `AXIINSTM(3,axi_mst_,axi_dev_slice_),
    `AXIASYNCSSUB(axi_async_slv_,sl3_dev_axi_gals_)
  );

  npu_axi_async_ini
  #(
    .AXIIDW         ( 1                 ),
    .AXIDW          ( 64                ),
    .AXIAWUW        ( SLICE_MMIO_AWUW   ),
    .AXIWUW         ( SLICE_MMIO_WUW    ),
    .AXIBUW         ( SLICE_MMIO_BUW    ),
    .AXIARUW        ( SLICE_MMIO_ARUW   ),
    .AXIRUW         ( SLICE_MMIO_RUW    ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_ini3
  (
    .axi_slv_clk   ( grp_clk_gated       ), 
    .axi_slv_rst_a ( grp_rst_a           ),
    .tgt_pwr_dwn_a ( slice3_pwr_dwn_a ), 
    .test_mode     ( test_mode           ),
    `AXIINSTM(3,axi_slv_,axi_ccm_slice_),
    `AXIASYNCMSUB(axi_async_mst_,sl3_ccm_axi_gals_)
   );  

  //
  // Instances of cln groups
  //
  npu_cln_group
  #(
    .NUMGRP  ( NUMGRP  ),
    .NUMSLC  ( NUMSLC  ),
    .NUMSTU  ( NUMSTU  ),
    .DEVIDW  ( DEVIDW  ),
    .LNKIDW  ( LNKIDW  ),
    .L2IDW   ( L2IDW   ),
    .CCMIDW  ( CCMIDW  ),
    .NOCIDW  ( NOCIDW  ),
    .TOP_CFG_DECBASE_RST_VAL  (TOP_CFG_DECBASE_RST_VAL),
    .TOP_CFG_DECSIZE_RST_VAL  (TOP_CFG_DECSIZE_RST_VAL),
    .TOP_CFG_DECMST_RST_VAL   (TOP_CFG_DECMST_RST_VAL),
    .BOT_CFG_DECBASE_RST_VAL  (BOT_CFG_DECBASE_RST_VAL),
    .BOT_CFG_DECSIZE_RST_VAL  (BOT_CFG_DECSIZE_RST_VAL),
    .BOT_CFG_DECMST_RST_VAL   (BOT_CFG_DECMST_RST_VAL),
    .CCM_CFG_DECBASE_RST_VAL  (CCM_CFG_DECBASE_RST_VAL),
    .CCM_CFG_DECSIZE_RST_VAL  (CCM_CFG_DECSIZE_RST_VAL),
    .CCM_CFG_DECMST_RST_VAL   (CCM_CFG_DECMST_RST_VAL),
    .REMP_CFG_DECBASE_RST_VAL (REMP_CFG_DECBASE_RST_VAL),
    .REMP_CFG_DECSIZE_RST_VAL (REMP_CFG_DECSIZE_RST_VAL),
    .REMP_CFG_DECMST_RST_VAL  (REMP_CFG_DECMST_RST_VAL)
  )
  u_cln_grp_inst
  (
    .clk       ( grp_clk_gated ),
    .rst_a     ( grp_rst_a     ),
    .test_mode ( test_mode     ),
    .ptidx_a   ( ptidx_a       ),
    .grp_pd_mem( grp_pd_mem    ),
    .scm_dbank_ecc_irq(scm_dbank_ecc_irq),  
    .scm_dbank_sbe(scm_dbank_sbe),
    .scm_dbank_dbe(scm_dbank_dbe),
    `AXIINST(axi_cfg_,axi_cfg_),
    `AXIINST(axi_dev_slice_,axi_dev_slice_),
    `AXIINST(axi_dev_stu_,axi_dev_stu_),
    `AXIINST(axi_dev_l2_,axi_dev_l2_),
    `AXIINST(axi_ccm_slice_,axi_ccm_slice_),
    `AXIINST(axi_ccm_stu_,axi_ccm_stu_),
    `AXIINST(axi_ccm_l2_,axi_ccm_l2_),
    `AXIINST(axi_egress_,axi_egress_),
    `AXIINST(axi_ingress_,axi_ingress_),
    `AXIINST(axi_noc_,axi_noc_)
   );

  //
  // STU channels
  //
  npu_stu_top  
  u_l2ustu0
  (
    .clk       ( grp_clk_gated      ),
    .rst       ( grp_rst            ),
    .done_evt  ( stu_done_evt[0]   ),
    .issue_evt ( stu_issue_evt[0]  ),
    .done_irq  ( stu_done_irq_a[0] ),
    .test_mode ( test_mode          ),
    .err_irq   ( stu_err_irq_a[0]  ),
    `TRCINST_S(stu_trace_,stu_trace_,0),
    .vmid      ( vmid_del           ),
    `AXIINSTM(0,dev_axi_,axi_dev_stu_),
    `AXIINSTM(0,ccm_axi_,axi_ccm_stu_)
  );

  npu_stu_top  
  u_l2ustu1
  (
    .clk       ( grp_clk_gated      ),
    .rst       ( grp_rst            ),
    .done_evt  ( stu_done_evt[1]   ),
    .issue_evt ( stu_issue_evt[1]  ),
    .done_irq  ( stu_done_irq_a[1] ),
    .test_mode ( test_mode          ),
    .err_irq   ( stu_err_irq_a[1]  ),
    `TRCINST_S(stu_trace_,stu_trace_,1),
    .vmid      ( vmid_del           ),
    `AXIINSTM(1,dev_axi_,axi_dev_stu_),
    `AXIINSTM(1,ccm_axi_,axi_ccm_stu_)
  );


  //
  // Synchronous bridges
  //
  npu_axi_sync_ini
  #(
    .AXIIDW         ( CCMIDW            ),
    .AXIDW          ( 64                ),
    .AXIAWUW        ( SLICE_MMIO_AWUW   ),
    .AXIWUW         ( SLICE_MMIO_WUW    ),
    .AXIBUW         ( SLICE_MMIO_BUW    ),
    .AXIARUW        ( SLICE_MMIO_ARUW   ),
    .AXIRUW         ( SLICE_MMIO_RUW    ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 0                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 0                 )
  )
  u_axi_ccm_ini
  (
    .axi_slv_clk   ( grp_clk_gated  ), 
    .axi_slv_rst_a ( grp_rst_a      ),
    .tgt_pwr_dwn_a ( 1'b0           ),
    .test_mode     ( test_mode      ),
    `AXIINST(axi_slv_,axi_ccm_l2_),
    `AXISYNCINST(axi_sync_mst_,axi_ccm_sync_)
   );  

  npu_axi_sync_tgt
  #(
    .AXIIDW         ( L2IDW             ),
    .AXIDW          ( 64*VSIZE          ),
    .AXIAWUW        ( SLICE_DMA_AWUW    ),
    .AXIWUW         ( SLICE_DMA_WUW     ),
    .AXIBUW         ( SLICE_DMA_BUW     ),
    .AXIARUW        ( SLICE_DMA_ARUW    ),
    .AXIRUW         ( SLICE_DMA_RUW     ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_mst_tgt
  (
    .axi_mst_clk   ( grp_clk_gated  ), 
    .axi_mst_rst_a ( grp_rst_a      ),
    .ini_pwr_dwn_a ( 1'b0           ),
    .test_mode     ( test_mode      ),
    .clk_req       ( axi_dmi_mst_tgt_clk_req ),
    `AXIINST(axi_mst_,axi_dev_l2_),
    `AXISYNCINST(axi_sync_slv_,axi_mst_sync_)
   );  

  npu_axi_sync_tgt
  #(
    .AXIIDW         ( 1                ),
    .AXIDW          ( 32               ),
    .AXIAWUW        ( 1                ),
    .AXIWUW         ( 1                ),
    .AXIBUW         ( 1                ),
    .AXIARUW        ( 1                ),
    .AXIRUW         ( 1                ),
    .AWFIFO_DEPTHL2 ( 0                ),
    .WFIFO_DEPTHL2  ( 0                ),
    .BFIFO_DEPTHL2  ( 0                ),
    .ARFIFO_DEPTHL2 ( 0                ),
    .RFIFO_DEPTHL2  ( 0                )
  )
  u_axi_cfg_sync_tgt
  (
    .axi_mst_clk   ( grp_clk_gated  ), 
    .axi_mst_rst_a ( grp_rst_a      ),
    .ini_pwr_dwn_a ( 1'b0           ),
    .test_mode     ( test_mode      ),
    .clk_req       ( axi_cfg_mst_tgt_clk_req ),
    `AXIINST(axi_mst_,axi_cfg_),
    `AXISYNCINST(axi_sync_slv_,axi_cfg_grp_sync_)
   );  

  //
  // Synchronous bridges
  //
  npu_axi_sync_ini
  #(
    .AXIIDW         ( LNKIDW            ),
    .AXIDW          ( 64*VSIZE          ),
    .AXIAWUW        ( SLICE_DMA_AWUW    ),
    .AXIWUW         ( SLICE_DMA_WUW     ),
    .AXIBUW         ( SLICE_DMA_BUW     ),
    .AXIARUW        ( SLICE_DMA_ARUW    ),
    .AXIRUW         ( SLICE_DMA_RUW     ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_egrs_ini0
  (
    .axi_slv_clk   ( grp_clk_gated  ), 
    .axi_slv_rst_a ( grp_rst_a      ),
    .tgt_pwr_dwn_a ( inter_grp_0_pwr_dwn_a),
    .test_mode     ( test_mode      ),
    `AXIINSTM(0,axi_slv_,axi_egress_),
    `AXISYNCINST(axi_sync_mst_,axi_egress0_sync_)
   );  

  npu_axi_sync_tgt
  #(
    .AXIIDW         ( LNKIDW            ),
    .AXIDW          ( 64*VSIZE          ),
    .AXIAWUW        ( SLICE_DMA_AWUW    ),
    .AXIWUW         ( SLICE_DMA_WUW     ),
    .AXIBUW         ( SLICE_DMA_BUW     ),
    .AXIARUW        ( SLICE_DMA_ARUW    ),
    .AXIRUW         ( SLICE_DMA_RUW     ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_ingrs_tgt0
  (
    .axi_mst_clk   ( grp_clk_gated  ), 
    .axi_mst_rst_a ( grp_rst_a      ),
    .ini_pwr_dwn_a ( inter_grp_0_pwr_dwn_a),
    .test_mode     ( test_mode      ),
    .clk_req       ( axi_ingrs_tgt_clk_req0),
    `AXIINSTM(0,axi_mst_,axi_ingress_),
    `AXISYNCINST(axi_sync_slv_,axi_ingress0_sync_)
   );  
  //
  // Synchronous bridges
  //
  npu_axi_sync_ini
  #(
    .AXIIDW         ( LNKIDW            ),
    .AXIDW          ( 64*VSIZE          ),
    .AXIAWUW        ( SLICE_DMA_AWUW    ),
    .AXIWUW         ( SLICE_DMA_WUW     ),
    .AXIBUW         ( SLICE_DMA_BUW     ),
    .AXIARUW        ( SLICE_DMA_ARUW    ),
    .AXIRUW         ( SLICE_DMA_RUW     ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_egrs_ini1
  (
    .axi_slv_clk   ( grp_clk_gated  ), 
    .axi_slv_rst_a ( grp_rst_a      ),
    .tgt_pwr_dwn_a ( inter_grp_1_pwr_dwn_a),
    .test_mode     ( test_mode      ),
    `AXIINSTM(1,axi_slv_,axi_egress_),
    `AXISYNCINST(axi_sync_mst_,axi_egress1_sync_)
   );  

  npu_axi_sync_tgt
  #(
    .AXIIDW         ( LNKIDW            ),
    .AXIDW          ( 64*VSIZE          ),
    .AXIAWUW        ( SLICE_DMA_AWUW    ),
    .AXIWUW         ( SLICE_DMA_WUW     ),
    .AXIBUW         ( SLICE_DMA_BUW     ),
    .AXIARUW        ( SLICE_DMA_ARUW    ),
    .AXIRUW         ( SLICE_DMA_RUW     ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_ingrs_tgt1
  (
    .axi_mst_clk   ( grp_clk_gated  ), 
    .axi_mst_rst_a ( grp_rst_a      ),
    .ini_pwr_dwn_a ( inter_grp_1_pwr_dwn_a),
    .test_mode     ( test_mode      ),
    .clk_req       ( axi_ingrs_tgt_clk_req1),
    `AXIINSTM(1,axi_mst_,axi_ingress_),
    `AXISYNCINST(axi_sync_slv_,axi_ingress1_sync_)
   );  
  //
  // Synchronous bridges
  //
  npu_axi_sync_ini
  #(
    .AXIIDW         ( LNKIDW            ),
    .AXIDW          ( 64*VSIZE          ),
    .AXIAWUW        ( SLICE_DMA_AWUW    ),
    .AXIWUW         ( SLICE_DMA_WUW     ),
    .AXIBUW         ( SLICE_DMA_BUW     ),
    .AXIARUW        ( SLICE_DMA_ARUW    ),
    .AXIRUW         ( SLICE_DMA_RUW     ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_egrs_ini2
  (
    .axi_slv_clk   ( grp_clk_gated  ), 
    .axi_slv_rst_a ( grp_rst_a      ),
    .tgt_pwr_dwn_a ( inter_grp_2_pwr_dwn_a),
    .test_mode     ( test_mode      ),
    `AXIINSTM(2,axi_slv_,axi_egress_),
    `AXISYNCINST(axi_sync_mst_,axi_egress2_sync_)
   );  

  npu_axi_sync_tgt
  #(
    .AXIIDW         ( LNKIDW            ),
    .AXIDW          ( 64*VSIZE          ),
    .AXIAWUW        ( SLICE_DMA_AWUW    ),
    .AXIWUW         ( SLICE_DMA_WUW     ),
    .AXIBUW         ( SLICE_DMA_BUW     ),
    .AXIARUW        ( SLICE_DMA_ARUW    ),
    .AXIRUW         ( SLICE_DMA_RUW     ),
    .AWFIFO_DEPTHL2 ( 0                 ),
    .WFIFO_DEPTHL2  ( 1                 ),
    .BFIFO_DEPTHL2  ( 0                 ),
    .ARFIFO_DEPTHL2 ( 0                 ),
    .RFIFO_DEPTHL2  ( 1                 )
  )
  u_axi_ingrs_tgt2
  (
    .axi_mst_clk   ( grp_clk_gated  ), 
    .axi_mst_rst_a ( grp_rst_a      ),
    .ini_pwr_dwn_a ( inter_grp_2_pwr_dwn_a),
    .test_mode     ( test_mode      ),
    .clk_req       ( axi_ingrs_tgt_clk_req2),
    `AXIINSTM(2,axi_mst_,axi_ingress_),
    `AXISYNCINST(axi_sync_slv_,axi_ingress2_sync_)
   );  

  //    

  // delay trace data
  always_ff @(posedge grp_clk_gated or
              posedge grp_rst)
  begin : vmid_del_PROC
    if (grp_rst == 1'b1)
      vmid_del <= '0;
    else
      vmid_del <= vmid;
  end : vmid_del_PROC


  logic rst_trace_sync;
  // combined trace SWE ext + data
  logic [NUM_TRACE_SRC-1:0][40:0] i_rtt_swe_data_comb;
  logic [NUM_TRACE_SRC-1:0] i_rtt_swe_val;
  npu_reset_ctrl
  u_reset_trace_inst
  (
    .clk        ( grp_clk_gated ),
    .rst_a      ( grp_rst_a     ),
    .test_mode  ( test_mode     ),
    .rst        ( rst_trace_sync )
  );
  // internal assignments
  assign i_rtt_swe_val[0] = sl0_rtt_swe_val;
  assign i_rtt_swe_data_comb[0] = {sl0_rtt_swe_ext, sl0_rtt_swe_data};
  assign i_rtt_swe_val[1] = sl1_rtt_swe_val;
  assign i_rtt_swe_data_comb[1] = {sl1_rtt_swe_ext, sl1_rtt_swe_data};
  assign i_rtt_swe_val[2] = sl2_rtt_swe_val;
  assign i_rtt_swe_data_comb[2] = {sl2_rtt_swe_ext, sl2_rtt_swe_data};
  assign i_rtt_swe_val[3] = sl3_rtt_swe_val;
  assign i_rtt_swe_data_comb[3] = {sl3_rtt_swe_ext, sl3_rtt_swe_data};
  assign i_rtt_swe_val[`NPU_NUM_SLC_PER_GRP+0] = stu_trace_valid[0];
  assign i_rtt_swe_data_comb[`NPU_NUM_SLC_PER_GRP+0] = {8'h00, stu_trace_id[0][31], 1'b0, stu_trace_id[0][30:0]};
  // delayed accept for STU SWE valid
  logic stu0_trace_valid_d0_r;
  assign stu0_trace_valid_d0_r = stu_trace_valid[0];
  logic stu0_trace_valid_d1_r;
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : stu0_trc_del1_PROC
    if (rst_trace_sync == 1'b1)
      stu0_trace_valid_d1_r <= 1'b0;
    else
      stu0_trace_valid_d1_r <= stu0_trace_valid_d0_r;
  end : stu0_trc_del1_PROC
  logic stu0_trace_valid_d2_r;
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : stu0_trc_del2_PROC
    if (rst_trace_sync == 1'b1)
      stu0_trace_valid_d2_r <= 1'b0;
    else
      stu0_trace_valid_d2_r <= stu0_trace_valid_d1_r;
  end : stu0_trc_del2_PROC
  logic stu0_trace_valid_d3_r;
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : stu0_trc_del3_PROC
    if (rst_trace_sync == 1'b1)
      stu0_trace_valid_d3_r <= 1'b0;
    else
      stu0_trace_valid_d3_r <= stu0_trace_valid_d2_r;
  end : stu0_trc_del3_PROC
  logic stu0_trace_valid_d4_r;
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : stu0_trc_del4_PROC
    if (rst_trace_sync == 1'b1)
      stu0_trace_valid_d4_r <= 1'b0;
    else
      stu0_trace_valid_d4_r <= stu0_trace_valid_d3_r;
  end : stu0_trc_del4_PROC
  assign stu_trace_accept[0] = stu_trace_valid[0]
                              & stu0_trace_valid_d1_r
                              & stu0_trace_valid_d2_r
                              & stu0_trace_valid_d3_r
                              & stu0_trace_valid_d4_r
                              ;
  assign i_rtt_swe_val[`NPU_NUM_SLC_PER_GRP+1] = stu_trace_valid[1];
  assign i_rtt_swe_data_comb[`NPU_NUM_SLC_PER_GRP+1] = {8'h00, stu_trace_id[1][31], 1'b0, stu_trace_id[1][30:0]};
  // delayed accept for STU SWE valid
  logic stu1_trace_valid_d0_r;
  assign stu1_trace_valid_d0_r = stu_trace_valid[1];
  logic stu1_trace_valid_d1_r;
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : stu1_trc_del1_PROC
    if (rst_trace_sync == 1'b1)
      stu1_trace_valid_d1_r <= 1'b0;
    else
      stu1_trace_valid_d1_r <= stu1_trace_valid_d0_r;
  end : stu1_trc_del1_PROC
  logic stu1_trace_valid_d2_r;
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : stu1_trc_del2_PROC
    if (rst_trace_sync == 1'b1)
      stu1_trace_valid_d2_r <= 1'b0;
    else
      stu1_trace_valid_d2_r <= stu1_trace_valid_d1_r;
  end : stu1_trc_del2_PROC
  logic stu1_trace_valid_d3_r;
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : stu1_trc_del3_PROC
    if (rst_trace_sync == 1'b1)
      stu1_trace_valid_d3_r <= 1'b0;
    else
      stu1_trace_valid_d3_r <= stu1_trace_valid_d2_r;
  end : stu1_trc_del3_PROC
  logic stu1_trace_valid_d4_r;
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : stu1_trc_del4_PROC
    if (rst_trace_sync == 1'b1)
      stu1_trace_valid_d4_r <= 1'b0;
    else
      stu1_trace_valid_d4_r <= stu1_trace_valid_d3_r;
  end : stu1_trc_del4_PROC
  assign stu_trace_accept[1] = stu_trace_valid[1]
                              & stu1_trace_valid_d1_r
                              & stu1_trace_valid_d2_r
                              & stu1_trace_valid_d3_r
                              & stu1_trace_valid_d4_r
                              ;

  // multi-cycle checker for SWE
  logic rtt_swe_prdcr_en_mc2;
  logic [NUM_TRACE_SRC-1:0][40:0] i_rtt_swe_data_comb_mc2;
  logic [NUM_TRACE_SRC-1:0] i_rtt_swe_val_mc2;

  npu_2cyc_checker
  #(
    .WIDTH (1),
    .DISABLE_OPTION (1'b1)
  )
  u_prdcr_en_mc2_inst
  (
    .clk      ( grp_clk_gated          ),
    .rst_a    ( rst_trace_sync         ),
    .valid    ( 1'b1                   ),
    .data_in  ( rtt_swe_prdcr_en       ),
    .data_out ( rtt_swe_prdcr_en_mc2   )
  );

  for (genvar gd = 0; gd < NUM_TRACE_SRC; gd++)
  begin : trc_val_mc2_GEN
    npu_2cyc_checker
    #(
      .WIDTH (1),
      .DISABLE_OPTION (1'b1)
    )
    u_swe_val_mc2_inst
    (
      .clk      ( grp_clk_gated         ),
      .rst_a    ( rst_trace_sync        ),
      .valid    ( 1'b1                  ),
      .data_in  ( i_rtt_swe_val[gd]     ),
      .data_out ( i_rtt_swe_val_mc2[gd] )
    );
  end : trc_val_mc2_GEN

  for (genvar gd = 0; gd < NUM_TRACE_SRC; gd++)
  begin : trc_dat_mc2_GEN
    npu_2cyc_checker
    #(
      .WIDTH (41)
    )
    u_swe_data_comb_mc2_inst
    (
      .clk      ( grp_clk_gated               ),
      .rst_a    ( rst_trace_sync              ),
      .valid    ( i_rtt_swe_val[gd]           ),
      .data_in  ( i_rtt_swe_data_comb[gd]     ),
      .data_out ( i_rtt_swe_data_comb_mc2[gd] )
    );
  end : trc_dat_mc2_GEN

  // synchronize the trace valid
  logic [NUM_TRACE_SRC-1:0] trace_valid_sync;

  for (genvar gd = 0; gd < NUM_TRACE_SRC; gd++)
  begin : cdc_v_GEN
    npu_cdc_sync
    #(
      .SYNC_FF_LEVELS ( 2 ),
      .WIDTH          ( 1 ),
      .TMR_CDC        ( 0 )
    )
    u_trace_valid_cdc_sync
    (
      .clk        ( grp_clk_gated         ),
      .rst_a      ( rst_trace_sync        ),
      .din        ( {1{i_rtt_swe_val_mc2[gd]}} ),
      .dout       ( trace_valid_sync[gd]  )
    );
  end : cdc_v_GEN

  // valid edge detection
  logic [NUM_TRACE_SRC-1:0] trace_valid_rise;

  for (genvar gd = 0; gd < NUM_TRACE_SRC; gd++)
  begin : val_e_GEN
    npu_trace_edge_detect
    u_trace_valid_edge_detect
    (
      .clk        ( grp_clk_gated        ),
      .rst_a      ( rst_trace_sync       ),
      .din        ( trace_valid_sync[gd] ),
      .dout       ( trace_valid_rise[gd] )
    );
  end : val_e_GEN

  // skid buffers
  logic [NUM_TRACE_SRC-1:0] trace_skid_valid;
  logic [NUM_TRACE_SRC-1:0] trace_skid_accept;
  logic [NUM_TRACE_SRC-1:0][40:0] trace_skid_data;

  for (genvar gd = 0; gd < NUM_TRACE_SRC; gd++)
  begin : trc_skid_GEN
    npu_skid
    #(
      .W (41)
    )
    u_trace_swe_skid
    (
      .clk         (grp_clk_gated               ),
      .rst_a       (rst_trace_sync              ),
      .in_valid    (trace_valid_rise[gd]        ),
      .in_accept   (                            ),  // intentionally unconnected
      .in_data     (i_rtt_swe_data_comb_mc2[gd] ),
      .int_valid   (                            ),  // intentionally unconnected
      .out_valid   (trace_skid_valid[gd]        ),
      .out_accept  (trace_skid_accept[gd]       ),
      .out_data    (trace_skid_data[gd]         )
    );
  end : trc_skid_GEN

  // gate skid buffer accept with prdcr_en
  logic [NUM_TRACE_SRC-1:0] trace_skid_accepti;
  logic [NUM_TRACE_SRC-1:0] trace_skid_validi;
  assign trace_skid_validi = trace_skid_valid   & {NUM_TRACE_SRC{rtt_swe_prdcr_en_mc2}};
  assign trace_skid_accept = trace_skid_accepti & {NUM_TRACE_SRC{rtt_swe_prdcr_en_mc2}};

  // SWE arbitration
  logic        trace_arb_out_valid;
  logic [40:0] trace_arb_out_data;
  npu_trace_arb
  #(
    .NUM ( NUM_TRACE_SRC ),
    .DW  ( 41            )
  )
  u_grp_trace_arb
  (
    .clk             ( grp_clk_gated       ),
    .rst_a           ( rst_trace_sync      ),
    .in_valid        ( trace_skid_validi   ),
    .in_accept       ( trace_skid_accepti  ),
    .in_data         ( trace_skid_data     ),
    .out_valid       ( trace_arb_out_valid ),
    .out_data        ( trace_arb_out_data  )
  );

  logic        trace_arb_out_valid_d0_r;
  logic [40:0] trace_arb_out_data_d0_r;
  // delay trace valid
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : val_del_PROC
    if (rst_trace_sync == 1'b1)
      trace_arb_out_valid_d0_r <= 1'b0;
    else
      trace_arb_out_valid_d0_r <= trace_arb_out_valid;
  end : val_del_PROC

  // delay trace data
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : dat_del_PROC
    if (rst_trace_sync == 1'b1)
      trace_arb_out_data_d0_r <= '0;
    else if (trace_arb_out_valid)
      trace_arb_out_data_d0_r <= trace_arb_out_data;
  end : dat_del_PROC

  logic        trace_arb_out_valid_d1_r;
  logic [40:0] trace_arb_out_data_d1_r;
  // delay trace valid
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : val_del1_PROC
    if (rst_trace_sync == 1'b1)
      trace_arb_out_valid_d1_r <= 1'b0;
    else
      trace_arb_out_valid_d1_r <= trace_arb_out_valid_d0_r;
  end : val_del1_PROC

  // delay trace data
  always_ff @(posedge grp_clk_gated or
              posedge rst_trace_sync)
  begin : dat_del1_PROC
    if (rst_trace_sync == 1'b1)
      trace_arb_out_data_d1_r <= '0;
    else if (trace_arb_out_valid_d0_r)
      trace_arb_out_data_d1_r <= trace_arb_out_data_d0_r;
  end : dat_del1_PROC
  // connect trace output
  assign rtt_swe_val  = trace_arb_out_valid_d1_r;
  assign rtt_swe_data = trace_arb_out_data_d1_r[32:0];
  assign rtt_swe_ext  = trace_arb_out_data_d1_r[40:33];
  //    

endmodule : npu_group
