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

// L2ARC group
// vcs -sverilog -f ../../shared/RTL/npu_shared_manifest ../../npu_arc/model/npuarc_hs_cluster_top.sv npu_l2arc_group.sv


`include "npu_defines.v"
`include "arcsync_exported_defines.v"
`include "npu_macros.svh"

`include "npu_axi_macros.svh"
`include "npu_apb_macros.svh"




module npu_l2arc_group
  import npu_types::*;
  #(
    parameter int NUMGRP  = 4,  // number of groups, power of 2
    parameter int NUMDMI  = 1,  // number of DMI ports
    parameter int NUMSLC  = 16, // number of NPX cores
    parameter int NUMSTU  = 8,  // number of STU channel
    parameter int CFGIDW  = 1,  // Configuration interface ID width
    parameter int DMIIDW  = 1,  // DMI interface attributes
    parameter int CCMIDW  = 1,  // CCM interface attributes
    parameter int MSTIDW  = 3,  // master interface attributes 2+clog2(numdmi+1)
    parameter int L2MIDW  = 1   // IDW before MST Matrix to balence L2 and NPU Group
  )
  (
   input      logic                          clk,
   input      logic                          rst_a,
   input      logic                          test_mode,

   // Config slave port
   input  logic                                                                                                        cfg_axi_gals_clk_req_a,
  input  logic [16+1+$bits(npu_axi_cmd_t)-1:0]                                                cfg_axi_gals_aw_data,
  output logic [`NUM_FLANES(16+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              cfg_axi_gals_aw_rdpnt,
  input  logic [0:0]                                                                                       cfg_axi_gals_aw_wpnt_a,
  output logic [0:0]                                                                                       cfg_axi_gals_aw_rpnt,
  input  logic [32+32/8+1:0]                                                           cfg_axi_gals_w_data,
  output logic [`NUM_FLANES(32+32/8+1+1)-1:0][(1<<0)-1:0]                      cfg_axi_gals_w_rdpnt,
  input  logic [0:0]                                                                                        cfg_axi_gals_w_wpnt_a,
  output logic [0:0]                                                                                        cfg_axi_gals_w_rpnt,
  output logic [16+1+$bits(npu_axi_resp_t)-1:0]                                                cfg_axi_gals_b_data,
  input  logic [`NUM_FLANES(16+1+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               cfg_axi_gals_b_rdpnt,
  output logic [0:0]                                                                                        cfg_axi_gals_b_wpnt,
  input  logic [0:0]                                                                                        cfg_axi_gals_b_rpnt_a,
  input  logic [16+1+$bits(npu_axi_cmd_t)-1:0]                                                cfg_axi_gals_ar_data,
  output logic [`NUM_FLANES(16+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              cfg_axi_gals_ar_rdpnt,
  input  logic [0:0]                                                                                       cfg_axi_gals_ar_wpnt_a,
  output logic [0:0]                                                                                       cfg_axi_gals_ar_rpnt,
  output logic [16+32+$bits(npu_axi_resp_t)+1:0]                                      cfg_axi_gals_r_data,
  input  logic [`NUM_FLANES(16+32+$bits(npu_axi_resp_t)+1+1)-1:0][(1<<0)-1:0] cfg_axi_gals_r_rdpnt,
  output logic [0:0]                                                                                        cfg_axi_gals_r_wpnt,
  input  logic [0:0]                                                                                        cfg_axi_gals_r_rpnt_a,

   // Config master port per group
   output logic                                                                                                  axi_cfg_grp0_sync_clk_req,
  output logic [1+1+$bits(npu_axi_cmd_t)-1:0]                                          axi_cfg_grp0_sync_aw_data,
  input  logic [`NUM_FLANES(1+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_cfg_grp0_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_cfg_grp0_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_cfg_grp0_sync_aw_rpnt,
  output logic [32+32/8+1:0]                                                     axi_cfg_grp0_sync_w_data,
  input  logic [`NUM_FLANES(32+32/8+1+1)-1:0][(1<<0)-1:0]                axi_cfg_grp0_sync_w_rdpnt,
  output logic [0:0]                                                                                  axi_cfg_grp0_sync_w_wpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp0_sync_w_rpnt,
  input  logic [1+1+$bits(npu_axi_resp_t)-1:0]                                          axi_cfg_grp0_sync_b_data,
  output logic [`NUM_FLANES(1+1+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_cfg_grp0_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp0_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_cfg_grp0_sync_b_rpnt,
  output logic [1+1+$bits(npu_axi_cmd_t)-1:0]                                          axi_cfg_grp0_sync_ar_data,
  input  logic [`NUM_FLANES(1+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_cfg_grp0_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_cfg_grp0_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_cfg_grp0_sync_ar_rpnt,
  input  logic [1+32+$bits(npu_axi_resp_t)+1:0]                                axi_cfg_grp0_sync_r_data,
  output logic [`NUM_FLANES(1+32+$bits(npu_axi_resp_t)+1+1)-1:0][(1<<0)-1:0] axi_cfg_grp0_sync_r_rdpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp0_sync_r_wpnt,
  output logic [0:0]                                                                                  axi_cfg_grp0_sync_r_rpnt,
   output logic                                                                                                  axi_cfg_grp1_sync_clk_req,
  output logic [1+1+$bits(npu_axi_cmd_t)-1:0]                                          axi_cfg_grp1_sync_aw_data,
  input  logic [`NUM_FLANES(1+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_cfg_grp1_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_cfg_grp1_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_cfg_grp1_sync_aw_rpnt,
  output logic [32+32/8+1:0]                                                     axi_cfg_grp1_sync_w_data,
  input  logic [`NUM_FLANES(32+32/8+1+1)-1:0][(1<<0)-1:0]                axi_cfg_grp1_sync_w_rdpnt,
  output logic [0:0]                                                                                  axi_cfg_grp1_sync_w_wpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp1_sync_w_rpnt,
  input  logic [1+1+$bits(npu_axi_resp_t)-1:0]                                          axi_cfg_grp1_sync_b_data,
  output logic [`NUM_FLANES(1+1+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_cfg_grp1_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp1_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_cfg_grp1_sync_b_rpnt,
  output logic [1+1+$bits(npu_axi_cmd_t)-1:0]                                          axi_cfg_grp1_sync_ar_data,
  input  logic [`NUM_FLANES(1+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_cfg_grp1_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_cfg_grp1_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_cfg_grp1_sync_ar_rpnt,
  input  logic [1+32+$bits(npu_axi_resp_t)+1:0]                                axi_cfg_grp1_sync_r_data,
  output logic [`NUM_FLANES(1+32+$bits(npu_axi_resp_t)+1+1)-1:0][(1<<0)-1:0] axi_cfg_grp1_sync_r_rdpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp1_sync_r_wpnt,
  output logic [0:0]                                                                                  axi_cfg_grp1_sync_r_rpnt,
   output logic                                                                                                  axi_cfg_grp2_sync_clk_req,
  output logic [1+1+$bits(npu_axi_cmd_t)-1:0]                                          axi_cfg_grp2_sync_aw_data,
  input  logic [`NUM_FLANES(1+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_cfg_grp2_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_cfg_grp2_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_cfg_grp2_sync_aw_rpnt,
  output logic [32+32/8+1:0]                                                     axi_cfg_grp2_sync_w_data,
  input  logic [`NUM_FLANES(32+32/8+1+1)-1:0][(1<<0)-1:0]                axi_cfg_grp2_sync_w_rdpnt,
  output logic [0:0]                                                                                  axi_cfg_grp2_sync_w_wpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp2_sync_w_rpnt,
  input  logic [1+1+$bits(npu_axi_resp_t)-1:0]                                          axi_cfg_grp2_sync_b_data,
  output logic [`NUM_FLANES(1+1+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_cfg_grp2_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp2_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_cfg_grp2_sync_b_rpnt,
  output logic [1+1+$bits(npu_axi_cmd_t)-1:0]                                          axi_cfg_grp2_sync_ar_data,
  input  logic [`NUM_FLANES(1+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_cfg_grp2_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_cfg_grp2_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_cfg_grp2_sync_ar_rpnt,
  input  logic [1+32+$bits(npu_axi_resp_t)+1:0]                                axi_cfg_grp2_sync_r_data,
  output logic [`NUM_FLANES(1+32+$bits(npu_axi_resp_t)+1+1)-1:0][(1<<0)-1:0] axi_cfg_grp2_sync_r_rdpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp2_sync_r_wpnt,
  output logic [0:0]                                                                                  axi_cfg_grp2_sync_r_rpnt,
   output logic                                                                                                  axi_cfg_grp3_sync_clk_req,
  output logic [1+1+$bits(npu_axi_cmd_t)-1:0]                                          axi_cfg_grp3_sync_aw_data,
  input  logic [`NUM_FLANES(1+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_cfg_grp3_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_cfg_grp3_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_cfg_grp3_sync_aw_rpnt,
  output logic [32+32/8+1:0]                                                     axi_cfg_grp3_sync_w_data,
  input  logic [`NUM_FLANES(32+32/8+1+1)-1:0][(1<<0)-1:0]                axi_cfg_grp3_sync_w_rdpnt,
  output logic [0:0]                                                                                  axi_cfg_grp3_sync_w_wpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp3_sync_w_rpnt,
  input  logic [1+1+$bits(npu_axi_resp_t)-1:0]                                          axi_cfg_grp3_sync_b_data,
  output logic [`NUM_FLANES(1+1+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_cfg_grp3_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp3_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_cfg_grp3_sync_b_rpnt,
  output logic [1+1+$bits(npu_axi_cmd_t)-1:0]                                          axi_cfg_grp3_sync_ar_data,
  input  logic [`NUM_FLANES(1+1+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_cfg_grp3_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_cfg_grp3_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_cfg_grp3_sync_ar_rpnt,
  input  logic [1+32+$bits(npu_axi_resp_t)+1:0]                                axi_cfg_grp3_sync_r_data,
  output logic [`NUM_FLANES(1+32+$bits(npu_axi_resp_t)+1+1)-1:0][(1<<0)-1:0] axi_cfg_grp3_sync_r_rdpnt,
  input  logic [0:0]                                                                                  axi_cfg_grp3_sync_r_wpnt,
  output logic [0:0]                                                                                  axi_cfg_grp3_sync_r_rpnt,

   // DMI slave ports
   //-DMI slave port0
   input  logic                                                                                                        dmi0_axi_gals_clk_req_a,
  input  logic [16+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                dmi0_axi_gals_aw_data,
  output logic [`NUM_FLANES(16+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              dmi0_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       dmi0_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       dmi0_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           dmi0_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      dmi0_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        dmi0_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        dmi0_axi_gals_w_rpnt,
  output logic [16+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                dmi0_axi_gals_b_data,
  input  logic [`NUM_FLANES(16+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               dmi0_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        dmi0_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        dmi0_axi_gals_b_rpnt_a,
  input  logic [16+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                dmi0_axi_gals_ar_data,
  output logic [`NUM_FLANES(16+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              dmi0_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       dmi0_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       dmi0_axi_gals_ar_rpnt,
  output logic [16+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      dmi0_axi_gals_r_data,
  input  logic [`NUM_FLANES(16+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] dmi0_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        dmi0_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        dmi0_axi_gals_r_rpnt_a,

   // Master ports
   output logic                                                                                                  axi_mst0_sync_clk_req,
  output logic [MSTIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_mst0_sync_aw_data,
  input  logic [`NUM_FLANES(MSTIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_mst0_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_mst0_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_mst0_sync_aw_rpnt,
  output logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                     axi_mst0_sync_w_data,
  input  logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]                axi_mst0_sync_w_rdpnt,
  output logic [1:0]                                                                                  axi_mst0_sync_w_wpnt,
  input  logic [1:0]                                                                                  axi_mst0_sync_w_rpnt,
  input  logic [MSTIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                          axi_mst0_sync_b_data,
  output logic [`NUM_FLANES(MSTIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_mst0_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_mst0_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_mst0_sync_b_rpnt,
  output logic [MSTIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_mst0_sync_ar_data,
  input  logic [`NUM_FLANES(MSTIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_mst0_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_mst0_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_mst0_sync_ar_rpnt,
  input  logic [MSTIDW+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                axi_mst0_sync_r_data,
  output logic [`NUM_FLANES(MSTIDW+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_mst0_sync_r_rdpnt,
  input  logic [1:0]                                                                                  axi_mst0_sync_r_wpnt,
  output logic [1:0]                                                                                  axi_mst0_sync_r_rpnt,
   output logic                                                                                                  axi_mst1_sync_clk_req,
  output logic [MSTIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_mst1_sync_aw_data,
  input  logic [`NUM_FLANES(MSTIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_mst1_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_mst1_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_mst1_sync_aw_rpnt,
  output logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                     axi_mst1_sync_w_data,
  input  logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]                axi_mst1_sync_w_rdpnt,
  output logic [1:0]                                                                                  axi_mst1_sync_w_wpnt,
  input  logic [1:0]                                                                                  axi_mst1_sync_w_rpnt,
  input  logic [MSTIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                          axi_mst1_sync_b_data,
  output logic [`NUM_FLANES(MSTIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_mst1_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_mst1_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_mst1_sync_b_rpnt,
  output logic [MSTIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_mst1_sync_ar_data,
  input  logic [`NUM_FLANES(MSTIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_mst1_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_mst1_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_mst1_sync_ar_rpnt,
  input  logic [MSTIDW+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                axi_mst1_sync_r_data,
  output logic [`NUM_FLANES(MSTIDW+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_mst1_sync_r_rdpnt,
  input  logic [1:0]                                                                                  axi_mst1_sync_r_wpnt,
  output logic [1:0]                                                                                  axi_mst1_sync_r_rpnt,
   output logic                                                                                                  axi_mst2_sync_clk_req,
  output logic [MSTIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_mst2_sync_aw_data,
  input  logic [`NUM_FLANES(MSTIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_mst2_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_mst2_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_mst2_sync_aw_rpnt,
  output logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                     axi_mst2_sync_w_data,
  input  logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]                axi_mst2_sync_w_rdpnt,
  output logic [1:0]                                                                                  axi_mst2_sync_w_wpnt,
  input  logic [1:0]                                                                                  axi_mst2_sync_w_rpnt,
  input  logic [MSTIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                          axi_mst2_sync_b_data,
  output logic [`NUM_FLANES(MSTIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_mst2_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_mst2_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_mst2_sync_b_rpnt,
  output logic [MSTIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_mst2_sync_ar_data,
  input  logic [`NUM_FLANES(MSTIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_mst2_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_mst2_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_mst2_sync_ar_rpnt,
  input  logic [MSTIDW+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                axi_mst2_sync_r_data,
  output logic [`NUM_FLANES(MSTIDW+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_mst2_sync_r_rdpnt,
  input  logic [1:0]                                                                                  axi_mst2_sync_r_wpnt,
  output logic [1:0]                                                                                  axi_mst2_sync_r_rpnt,
   output logic                                                                                                  axi_mst3_sync_clk_req,
  output logic [MSTIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_mst3_sync_aw_data,
  input  logic [`NUM_FLANES(MSTIDW+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_mst3_sync_aw_rdpnt,
  output logic [0:0]                                                                                 axi_mst3_sync_aw_wpnt,
  input  logic [0:0]                                                                                 axi_mst3_sync_aw_rpnt,
  output logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                     axi_mst3_sync_w_data,
  input  logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<1)-1:0]                axi_mst3_sync_w_rdpnt,
  output logic [1:0]                                                                                  axi_mst3_sync_w_wpnt,
  input  logic [1:0]                                                                                  axi_mst3_sync_w_rpnt,
  input  logic [MSTIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                          axi_mst3_sync_b_data,
  output logic [`NUM_FLANES(MSTIDW+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]         axi_mst3_sync_b_rdpnt,
  input  logic [0:0]                                                                                  axi_mst3_sync_b_wpnt,
  output logic [0:0]                                                                                  axi_mst3_sync_b_rpnt,
  output logic [MSTIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                          axi_mst3_sync_ar_data,
  input  logic [`NUM_FLANES(MSTIDW+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]        axi_mst3_sync_ar_rdpnt,
  output logic [0:0]                                                                                 axi_mst3_sync_ar_wpnt,
  input  logic [0:0]                                                                                 axi_mst3_sync_ar_rpnt,
  input  logic [MSTIDW+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                axi_mst3_sync_r_data,
  output logic [`NUM_FLANES(MSTIDW+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<1)-1:0] axi_mst3_sync_r_rdpnt,
  input  logic [1:0]                                                                                  axi_mst3_sync_r_wpnt,
  output logic [1:0]                                                                                  axi_mst3_sync_r_rpnt,

   // CLN CCM ports
   input  logic                                                                                            axi_ccm0_sync_clk_req,
  input  logic [CCMIDW+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ccm0_sync_aw_data,
  output logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ccm0_sync_aw_rdpnt,
  input  logic [0:0]                                                                           axi_ccm0_sync_aw_wpnt,
  output logic [0:0]                                                                           axi_ccm0_sync_aw_rpnt,
  input  logic [64+64/8+SLICE_MMIO_WUW:0]                                               axi_ccm0_sync_w_data,
  output logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<0)-1:0]          axi_ccm0_sync_w_rdpnt,
  input  logic [0:0]                                                                            axi_ccm0_sync_w_wpnt,
  output logic [0:0]                                                                            axi_ccm0_sync_w_rpnt,
  output logic [CCMIDW+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                    axi_ccm0_sync_b_data,
  input  logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]   axi_ccm0_sync_b_rdpnt,
  output logic [0:0]                                                                            axi_ccm0_sync_b_wpnt,
  input  logic [0:0]                                                                            axi_ccm0_sync_b_rpnt,
  input  logic [CCMIDW+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ccm0_sync_ar_data,
  output logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ccm0_sync_ar_rdpnt,
  input  logic [0:0]                                                                           axi_ccm0_sync_ar_wpnt,
  output logic [0:0]                                                                           axi_ccm0_sync_ar_rpnt,
  output logic [CCMIDW+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                          axi_ccm0_sync_r_data,
  input  logic [`NUM_FLANES(CCMIDW+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<0)-1:0] axi_ccm0_sync_r_rdpnt,
  output logic [0:0]                                                                            axi_ccm0_sync_r_wpnt,
  input  logic [0:0]                                                                            axi_ccm0_sync_r_rpnt,
   input  logic                                                                                            axi_ccm1_sync_clk_req,
  input  logic [CCMIDW+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ccm1_sync_aw_data,
  output logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ccm1_sync_aw_rdpnt,
  input  logic [0:0]                                                                           axi_ccm1_sync_aw_wpnt,
  output logic [0:0]                                                                           axi_ccm1_sync_aw_rpnt,
  input  logic [64+64/8+SLICE_MMIO_WUW:0]                                               axi_ccm1_sync_w_data,
  output logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<0)-1:0]          axi_ccm1_sync_w_rdpnt,
  input  logic [0:0]                                                                            axi_ccm1_sync_w_wpnt,
  output logic [0:0]                                                                            axi_ccm1_sync_w_rpnt,
  output logic [CCMIDW+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                    axi_ccm1_sync_b_data,
  input  logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]   axi_ccm1_sync_b_rdpnt,
  output logic [0:0]                                                                            axi_ccm1_sync_b_wpnt,
  input  logic [0:0]                                                                            axi_ccm1_sync_b_rpnt,
  input  logic [CCMIDW+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ccm1_sync_ar_data,
  output logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ccm1_sync_ar_rdpnt,
  input  logic [0:0]                                                                           axi_ccm1_sync_ar_wpnt,
  output logic [0:0]                                                                           axi_ccm1_sync_ar_rpnt,
  output logic [CCMIDW+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                          axi_ccm1_sync_r_data,
  input  logic [`NUM_FLANES(CCMIDW+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<0)-1:0] axi_ccm1_sync_r_rdpnt,
  output logic [0:0]                                                                            axi_ccm1_sync_r_wpnt,
  input  logic [0:0]                                                                            axi_ccm1_sync_r_rpnt,
   input  logic                                                                                            axi_ccm2_sync_clk_req,
  input  logic [CCMIDW+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ccm2_sync_aw_data,
  output logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ccm2_sync_aw_rdpnt,
  input  logic [0:0]                                                                           axi_ccm2_sync_aw_wpnt,
  output logic [0:0]                                                                           axi_ccm2_sync_aw_rpnt,
  input  logic [64+64/8+SLICE_MMIO_WUW:0]                                               axi_ccm2_sync_w_data,
  output logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<0)-1:0]          axi_ccm2_sync_w_rdpnt,
  input  logic [0:0]                                                                            axi_ccm2_sync_w_wpnt,
  output logic [0:0]                                                                            axi_ccm2_sync_w_rpnt,
  output logic [CCMIDW+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                    axi_ccm2_sync_b_data,
  input  logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]   axi_ccm2_sync_b_rdpnt,
  output logic [0:0]                                                                            axi_ccm2_sync_b_wpnt,
  input  logic [0:0]                                                                            axi_ccm2_sync_b_rpnt,
  input  logic [CCMIDW+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ccm2_sync_ar_data,
  output logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ccm2_sync_ar_rdpnt,
  input  logic [0:0]                                                                           axi_ccm2_sync_ar_wpnt,
  output logic [0:0]                                                                           axi_ccm2_sync_ar_rpnt,
  output logic [CCMIDW+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                          axi_ccm2_sync_r_data,
  input  logic [`NUM_FLANES(CCMIDW+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<0)-1:0] axi_ccm2_sync_r_rdpnt,
  output logic [0:0]                                                                            axi_ccm2_sync_r_wpnt,
  input  logic [0:0]                                                                            axi_ccm2_sync_r_rpnt,
   input  logic                                                                                            axi_ccm3_sync_clk_req,
  input  logic [CCMIDW+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ccm3_sync_aw_data,
  output logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ccm3_sync_aw_rdpnt,
  input  logic [0:0]                                                                           axi_ccm3_sync_aw_wpnt,
  output logic [0:0]                                                                           axi_ccm3_sync_aw_rpnt,
  input  logic [64+64/8+SLICE_MMIO_WUW:0]                                               axi_ccm3_sync_w_data,
  output logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<0)-1:0]          axi_ccm3_sync_w_rdpnt,
  input  logic [0:0]                                                                            axi_ccm3_sync_w_wpnt,
  output logic [0:0]                                                                            axi_ccm3_sync_w_rpnt,
  output logic [CCMIDW+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                    axi_ccm3_sync_b_data,
  input  logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]   axi_ccm3_sync_b_rdpnt,
  output logic [0:0]                                                                            axi_ccm3_sync_b_wpnt,
  input  logic [0:0]                                                                            axi_ccm3_sync_b_rpnt,
  input  logic [CCMIDW+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                    axi_ccm3_sync_ar_data,
  output logic [`NUM_FLANES(CCMIDW+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]  axi_ccm3_sync_ar_rdpnt,
  input  logic [0:0]                                                                           axi_ccm3_sync_ar_wpnt,
  output logic [0:0]                                                                           axi_ccm3_sync_ar_rpnt,
  output logic [CCMIDW+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                          axi_ccm3_sync_r_data,
  input  logic [`NUM_FLANES(CCMIDW+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<0)-1:0] axi_ccm3_sync_r_rdpnt,
  output logic [0:0]                                                                            axi_ccm3_sync_r_wpnt,
  input  logic [0:0]                                                                            axi_ccm3_sync_r_rpnt,

   // L2 ARC NoC ports
   output logic                                                                                                        l2arc_noc_axi_gals_clk_req,
  output logic [5+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                l2arc_noc_axi_gals_aw_data,
  input  logic [`NUM_FLANES(5+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              l2arc_noc_axi_gals_aw_rdpnt,
  output logic [1:0]                                                                                       l2arc_noc_axi_gals_aw_wpnt,
  input  logic [1:0]                                                                                       l2arc_noc_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_DMA_WUW:0]                                                           l2arc_noc_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      l2arc_noc_axi_gals_w_rdpnt,
  output logic [3:0]                                                                                        l2arc_noc_axi_gals_w_wpnt,
  input  logic [3:0]                                                                                        l2arc_noc_axi_gals_w_rpnt_a,
  input  logic [5+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                l2arc_noc_axi_gals_b_data,
  output logic [`NUM_FLANES(5+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               l2arc_noc_axi_gals_b_rdpnt,
  input  logic [1:0]                                                                                        l2arc_noc_axi_gals_b_wpnt_a,
  output logic [1:0]                                                                                        l2arc_noc_axi_gals_b_rpnt,
  output logic [5+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                l2arc_noc_axi_gals_ar_data,
  input  logic [`NUM_FLANES(5+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              l2arc_noc_axi_gals_ar_rdpnt,
  output logic [1:0]                                                                                       l2arc_noc_axi_gals_ar_wpnt,
  input  logic [1:0]                                                                                       l2arc_noc_axi_gals_ar_rpnt_a,
  input  logic [5+64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      l2arc_noc_axi_gals_r_data,
  output logic [`NUM_FLANES(5+64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] l2arc_noc_axi_gals_r_rdpnt,
  input  logic [3:0]                                                                                        l2arc_noc_axi_gals_r_wpnt_a,
  output logic [3:0]                                                                                        l2arc_noc_axi_gals_r_rpnt,

   output     logic [64-1: 0]            npu_grp0_vmid,
   output     logic [64-1: 0]            npu_grp1_vmid,
   output     logic [64-1: 0]            npu_grp2_vmid,
   output     logic [64-1: 0]            npu_grp3_vmid,
   // HS Debug BVCI
   input      logic                          dbg_cmdval_a       ,
   input      logic [36:0]                   dbg_pack_a         , // dbg_wdata,i_bvci_addr,dbg_cmd
   output     logic [31:0]                   dbg_resp           , // rdata
   output     logic                          wdt_reset          ,
   output     logic                          wdt_reset_wdt_clk  ,
   input      logic                          arc1_dbg_cmdval_a  ,
   input      logic [36:0]                   arc1_dbg_pack_a    , // dbg_wdata,i_bvci_addr,dbg_cmd
   output     logic [31:0]                   arc1_dbg_resp      , // rdata
   output     logic                          arc1_wdt_reset        ,
   output     logic                          arc1_wdt_reset_wdt_clk,
  input  logic                               grp0_pwr_dwn_a,
  input  logic                               grp1_pwr_dwn_a,
  input  logic                               grp2_pwr_dwn_a,
  input  logic                               grp3_pwr_dwn_a,
   // npuarc_hs_cluster_top need to add the following power domain ports
   // power domain
   // -l2arc
     // Power status                                                                                                     
  input logic                       nl2arc0_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       nl2arc0_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       nl2arc0_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       nl2arc0_pd_logic,    // Power down of power domain logics                     
   input      logic                          nl2arc0_pwr_dwn_a,
   input      logic                          nl2arc0_rst_a,
   input      logic                          nl2arc0_clk_en_a,
   output     logic                          nl2arc0_evt_vm_irq,
   input      logic                          nl2arc1_pwr_dwn_a,
   input      logic                          nl2arc1_rst_a,
   input      logic                          nl2arc1_clk_en_a,
   output     logic                          nl2arc1_evt_vm_irq,
   input      logic                          grp0_evt_vm_irq_a,
   input      logic                          grp1_evt_vm_irq_a,
   input      logic                          grp2_evt_vm_irq_a,
   input      logic                          grp3_evt_vm_irq_a,
   input  logic                              ext_irq0_a, // From user-defined IRQ sources
   input  logic                              ext_irq1_a, // From user-defined IRQ sources
   // L2 ARC
   input      logic [7:0]                    clusternum,
   input      logic [7:0]                    arcnum,
   // Boot
   input      logic [21:0]                   intvbase_in,
   // Halt
   input      logic                          arc_halt_req_a,
   output     logic                          arc_halt_ack,
   // Run
   input      logic                          arc_run_req_a,
   output     logic                          arc_run_ack,
   // Status
   output     logic                          sys_sleep_r,
   output     logic [2:0]                    sys_sleep_mode_r,
   output     logic                          sys_halt_r,
   output     logic                          sys_tf_halt_r,
   input      logic [17:0]    arcsync_irq_a,
   input      logic [17:0]    arcsync_event_a,
   // L2 ARC
   input      logic [7:0]                    arc1_clusternum,
   input      logic [7:0]                    arc1_arcnum,
   // Boot
   input      logic [21:0]                   arc1_intvbase_in,
   // Halt
   input      logic                          arc1_arc_halt_req_a,
   output     logic                          arc1_arc_halt_ack,
   // Run
   input      logic                          arc1_arc_run_req_a,
   output     logic                          arc1_arc_run_ack,
   // Status
   output     logic                          arc1_sys_halt_r,
   output     logic                          arc1_sys_tf_halt_r,
   output     logic                          arc1_sys_sleep_r,
   output     logic [2:0]                    arc1_sys_sleep_mode_r,
   input      logic [17:0]    arc1_arcsync_irq_a,
   input      logic [17:0]    arc1_arcsync_event_a,

   //ARC_Trace
   // CoreSight interface global signals
   input      logic                          at_clk_en,
   input      logic                          at_rst_an,
   input      logic [63:0]                   atb_cstimestamp,
   // CoreSight interface of L2 core
   input      logic                          atready,
   output     logic [64-1:0]     atdata,
   output     logic [3-1:0]      atbytes,
   output     logic [6:0]                    atid,
   output     logic                          atvalid,
   input      logic                          afvalid,
   output     logic                          afready,
   input      logic                          syncreq,
   // CoreSight interface of NPU Slices
   input      logic                          swe_atready,
   output     logic [64-1:0] swe_atdata,
   output     logic [3-1:0]  swe_atbytes,
   output     logic [6:0]                    swe_atid,
   output     logic                          swe_atvalid,
   input      logic                          swe_afvalid,
   output     logic                          swe_afready,
   input      logic                          swe_syncreq,
   // CTI signalling
   output     logic [25:0]                   cti_rtt_filters,
   input      logic                          cti_trace_start,
   input      logic                          cti_trace_stop,

   // APB Interface to ARC_Trace
   `APBASYNCTGT(16,32,arct_),
   input      logic                          arct_dbgen,
   input      logic                          arct_niden,


   // Shared signals for APB Interface to ARC_Trace and to L2 debug port
   input      logic                          arct_dbg_prot_sel,
   input      logic                          arct_rst_an,

   // Software events
   input      logic                          grp0_rtt_swe_val,
   input      logic [32:0]                   grp0_rtt_swe_data,
   input      logic [7:0]                    grp0_rtt_swe_ext,
   output     logic                          grp0_rtt_swe_prdcr_en,
   input      logic                          grp1_rtt_swe_val,
   input      logic [32:0]                   grp1_rtt_swe_data,
   input      logic [7:0]                    grp1_rtt_swe_ext,
   output     logic                          grp1_rtt_swe_prdcr_en,
   input      logic                          grp2_rtt_swe_val,
   input      logic [32:0]                   grp2_rtt_swe_data,
   input      logic [7:0]                    grp2_rtt_swe_ext,
   output     logic                          grp2_rtt_swe_prdcr_en,
   input      logic                          grp3_rtt_swe_val,
   input      logic [32:0]                   grp3_rtt_swe_data,
   input      logic [7:0]                    grp3_rtt_swe_ext,
   output     logic                          grp3_rtt_swe_prdcr_en,
   input      logic                          grp4_rtt_swe_val,
   input      logic [32:0]                   grp4_rtt_swe_data,
   input      logic [7:0]                    grp4_rtt_swe_ext,
   output     logic                          grp4_rtt_swe_prdcr_en,
   input      logic                          grp5_rtt_swe_val,
   input      logic [32:0]                   grp5_rtt_swe_data,
   input      logic [7:0]                    grp5_rtt_swe_ext,
   output     logic                          grp5_rtt_swe_prdcr_en,
   input      logic                          grp6_rtt_swe_val,
   input      logic [32:0]                   grp6_rtt_swe_data,
   input      logic [7:0]                    grp6_rtt_swe_ext,
   output     logic                          grp6_rtt_swe_prdcr_en,
   input      logic                          grp7_rtt_swe_val,
   input      logic [32:0]                   grp7_rtt_swe_data,
   input      logic [7:0]                    grp7_rtt_swe_ext,
   output     logic                          grp7_rtt_swe_prdcr_en,
   input      logic                          grp8_rtt_swe_val,
   input      logic [32:0]                   grp8_rtt_swe_data,
   input      logic [7:0]                    grp8_rtt_swe_ext,
   output     logic                          grp8_rtt_swe_prdcr_en,
   input      logic                          grp9_rtt_swe_val,
   input      logic [32:0]                   grp9_rtt_swe_data,
   input      logic [7:0]                    grp9_rtt_swe_ext,
   output     logic                          grp9_rtt_swe_prdcr_en,
   input      logic                          grp10_rtt_swe_val,
   input      logic [32:0]                   grp10_rtt_swe_data,
   input      logic [7:0]                    grp10_rtt_swe_ext,
   output     logic                          grp10_rtt_swe_prdcr_en,
   input      logic                          grp11_rtt_swe_val,
   input      logic [32:0]                   grp11_rtt_swe_data,
   input      logic [7:0]                    grp11_rtt_swe_ext,
   output     logic                          grp11_rtt_swe_prdcr_en,
   input      logic                          grp12_rtt_swe_val,
   input      logic [32:0]                   grp12_rtt_swe_data,
   input      logic [7:0]                    grp12_rtt_swe_ext,
   output     logic                          grp12_rtt_swe_prdcr_en,
   input      logic                          grp13_rtt_swe_val,
   input      logic [32:0]                   grp13_rtt_swe_data,
   input      logic [7:0]                    grp13_rtt_swe_ext,
   output     logic                          grp13_rtt_swe_prdcr_en,
   input      logic                          grp14_rtt_swe_val,
   input      logic [32:0]                   grp14_rtt_swe_data,
   input      logic [7:0]                    grp14_rtt_swe_ext,
   output     logic                          grp14_rtt_swe_prdcr_en,
   input      logic                          grp15_rtt_swe_val,
   input      logic [32:0]                   grp15_rtt_swe_data,
   input      logic [7:0]                    grp15_rtt_swe_ext,
   output     logic                          grp15_rtt_swe_prdcr_en,
   input      logic                          grp16_rtt_swe_val,
   input      logic [32:0]                   grp16_rtt_swe_data,
   input      logic [7:0]                    grp16_rtt_swe_ext,
   output     logic                          grp16_rtt_swe_prdcr_en,
   // APB Interface to L2 ARC
   `APBASYNCTGT(16,32,nl2arc0_),
   input      logic                          nl2arc0_dbgen,
   input      logic                          nl2arc0_niden,
   `APBASYNCTGT(16,32,nl2arc1_),
   input      logic                          nl2arc1_dbgen,
   input      logic                          nl2arc1_niden,
   input      logic                          wdt_clk              ,
   input      logic                          arc1_wdt_clk              ,
   output     logic                          nl2arc0_ecc_sbe,
   output     logic                          nl2arc0_ecc_dbe,
   output     logic                          nl2arc1_ecc_sbe,
   output     logic                          nl2arc1_ecc_dbe,
   input      logic [3:0]       scm_dbank_ecc_irq,
   // IRQ and Event
   input      logic [NUMSTU-1:0]             stu_done_evt,
   input      logic [NUMSTU-1:0]             stu_issue_evt,
   input      logic [NUMSTU-1:0]             stu_done_irq_a,
   input      logic [NUMSLC-1:0][1:0]        child_events_a,
   output     logic [NUMSLC-1:0][1:0]        parent_events,
   input      logic [NPU_AXI_ADDR_W-1:24]    npu_csm_base
   );

  // localparams
  localparam int NUMAP          = 16; // number of master decoding apertures
  localparam int DMIDW          = CCMIDW+$clog2(NUMGRP+1); // ID of CCM after arbitration

  logic [NPU_AXI_ADDR_W-1:24]    npu_csm_base_r;
  logic [4:0]                    npu_csm_set_r;
  logic                          npu_csm_set;
  // local types
  typedef enum logic [1:0] {dbg_state_idle_e, dbg_state_val_e, dbg_state_resp_e} dbg_state_t;

   logic [NUMSLC-1:0][1:0]        parent_events_nxt;
   logic [NUMSLC-1:0][1:0]        parent_events_r;
   logic [NUMSLC-1:0][1:0]        child_events_r;
  logic [31: 0]       npu_grp0_sid;
  logic [31: 0]       npu_grp0_ssid;
  logic [31: 0]       npu_grp1_sid;
  logic [31: 0]       npu_grp1_ssid;
  logic [31: 0]       npu_grp2_sid;
  logic [31: 0]       npu_grp2_ssid;
  logic [31: 0]       npu_grp3_sid;
  logic [31: 0]       npu_grp3_ssid;

  `APBWIRES(16,32,arct_);
  `APBWIRES(16,32,nl2arc0_);
  `APBWIRES(16,32,nl2arc1_);

  logic              arc0_axi_sccm_tgt_clk_en;
  logic       [3:0]  arc0_vm_sel;
  logic              arc1_axi_sccm_tgt_clk_en;
  logic       [3:0]  arc1_vm_sel;
  // local wires
  logic              rst_sync;
  logic       [95:0] arc0_events_in_a;
  logic       [95:0] arc1_events_in_a;
  dbg_state_t        arc1_dbg_state_r;     // BVCI state
  dbg_state_t        arc1_dbg_state_nxt;
  logic              arc1_dbg_state_en;
  logic              arc1_dbg_cmdval_sync;
  logic              arc1_dbg_cmdval_r;
  logic              arc1_dbg_cmd_en;      // BVCI command register
  logic       [36:0] arc1_dbg_cmd_r;
  logic              arc1_dbg_rsp_en;
  logic       [31:0] arc1_dbg_rsp_r;       // BVCI response register
  logic       [63:0] arc1_event_send;
  logic              arc1_dbg_cmdval;
  logic              arc1_dbg_cmdack;
  logic       [31:0] arc1_dbg_address;
  logic       [1:0]  arc1_dbg_cmd;
  logic       [31:0] arc1_dbg_wdata;
  logic       [31:0] arc1_dbg_rdata;
  logic              arc1_dbg_rspval;
  logic              arc1_dbg_reset;
  logic       [63:0] arc0_event_send;
  dbg_state_t        dbg_state_r;     // BVCI state
  dbg_state_t        dbg_state_nxt;
  logic              dbg_state_en;
  logic              dbg_cmdval_sync;
  logic              dbg_cmdval_r;
  logic              dbg_cmd_en;      // BVCI command register
  logic       [36:0] dbg_cmd_r;
  logic              dbg_rsp_en;
  logic       [31:0] dbg_rsp_r;       // BVCI response register
  logic              dbg_cmdval;
  logic              dbg_cmdack;
  logic       [31:0] dbg_address;
  logic       [1:0]  dbg_cmd;
  logic       [31:0] dbg_wdata;
  logic       [31:0] dbg_rdata;
  logic              dbg_rspval;
  logic              dbg_reset;

  // ARC HS controller clock and reset
// spyglass disable_block W401
//SMD: Clock is not input
//SJ : Internal generated clock
  logic              nl2arc0_clk;
// spyglass enable_block W401
  logic              nl2arc0_rst_sync;
  logic              nl2arc0_clk_en;
// spyglass disable_block W401
//SMD: Clock is not input
//SJ : Internal generated clock
  logic              nl2arc1_clk;
// spyglass enable_block W401
  logic              nl2arc1_rst_sync;
  logic              nl2arc1_clk_en;

   //ARC_Trace
   logic [31:0]                   rtt_drd_r;
   logic                          rtt_prod_sel;
   logic                          rtt_freeze;
   logic [7:0]                    rtt_src_num;
   logic                          rtt_write_a;
   logic                          rtt_read_a;
   logic [31:0]                   rtt_addr_r;
   logic [31:0]                   rtt_dwr_r;
   logic                          rtt_ss_halt;
   logic                          rtt_hw_bp;
   logic                          rtt_hw_exc;
   logic                          rtt_dbg_halt;
   logic                          rtt_rst_applied;
   logic                          rtt_uop_is_leave;
   logic                          rtt_in_deslot;
   logic                          rtt_in_eslot;
   logic                          rtt_inst_commit;
   logic [31:1]                   rtt_inst_addr;
   logic                          rtt_cond_valid;
   logic                          rtt_cond_pass;
   logic                          rtt_branch;
   logic                          rtt_branch_indir;
   logic [31:1]                   rtt_branch_taddr;
   logic                          rtt_dslot;
   logic                          rtt_exception;
   logic                          rtt_exception_rtn;
   logic                          rtt_interrupt;
   logic                          rtt_sleep_mode;
   logic                          rtt_zd_loop;
   logic [7:0]                    rtt_wp_val;
   logic                          rtt_wp_hit;
   logic                          rtt_sw_bp;
   logic [7:0]                    rtt_process_id;
   logic                          rtt_pid_wr_en;
   logic [32:0]                   rtt_swe_data;
   logic                          rtt_swe_val;
   logic [2:0]                    grp0_rtt_swe_val_syn_r;
   logic                          grp0_rtt_swe_val_pulse;
   logic [2:0]                    grp1_rtt_swe_val_syn_r;
   logic                          grp1_rtt_swe_val_pulse;
   logic [2:0]                    grp2_rtt_swe_val_syn_r;
   logic                          grp2_rtt_swe_val_pulse;
   logic [2:0]                    grp3_rtt_swe_val_syn_r;
   logic                          grp3_rtt_swe_val_pulse;
   logic [2:0]                    grp4_rtt_swe_val_syn_r;
   logic                          grp4_rtt_swe_val_pulse;
   logic [2:0]                    grp5_rtt_swe_val_syn_r;
   logic                          grp5_rtt_swe_val_pulse;
   logic [2:0]                    grp6_rtt_swe_val_syn_r;
   logic                          grp6_rtt_swe_val_pulse;
   logic [2:0]                    grp7_rtt_swe_val_syn_r;
   logic                          grp7_rtt_swe_val_pulse;
   logic [2:0]                    grp8_rtt_swe_val_syn_r;
   logic                          grp8_rtt_swe_val_pulse;
   logic [2:0]                    grp9_rtt_swe_val_syn_r;
   logic                          grp9_rtt_swe_val_pulse;
   logic [2:0]                    grp10_rtt_swe_val_syn_r;
   logic                          grp10_rtt_swe_val_pulse;
   logic [2:0]                    grp11_rtt_swe_val_syn_r;
   logic                          grp11_rtt_swe_val_pulse;
   logic [2:0]                    grp12_rtt_swe_val_syn_r;
   logic                          grp12_rtt_swe_val_pulse;
   logic [2:0]                    grp13_rtt_swe_val_syn_r;
   logic                          grp13_rtt_swe_val_pulse;
   logic [2:0]                    grp14_rtt_swe_val_syn_r;
   logic                          grp14_rtt_swe_val_pulse;
   logic [2:0]                    grp15_rtt_swe_val_syn_r;
   logic                          grp15_rtt_swe_val_pulse;
   logic [2:0]                    grp16_rtt_swe_val_syn_r;
   logic                          grp16_rtt_swe_val_pulse;


   logic                          l2_watchdog_reset;
   logic                          arc1_l2_watchdog_reset;

   // ECC status of L2 ARC #0 memories
   logic                          fs_dc_tag_ecc_sb_error_r;
   logic                          fs_dc_tag_ecc_db_error_r;
   logic                          fs_dc_data_ecc_sb_error_r;
   logic                          fs_dc_data_ecc_db_error_r;
   logic                          fs_dccm_ecc_sb_error_r;
   logic                          fs_dccm_ecc_db_error_r;
   logic                          fs_itlb_ecc_sb_error_r;
   logic                          fs_itlb_ecc_db_error_r;
   logic                          fs_dtlb_ecc_sb_error_r;
   logic                          fs_dtlb_ecc_db_error_r;
   logic                          fs_ic_tag_ecc_sb_error_r;
   logic                          fs_ic_tag_ecc_db_error_r;
   logic                          fs_ic_data_ecc_sb_error_r;
   logic                          fs_ic_data_ecc_db_error_r;

   logic ecc_sbe_r, ecc_sbe_nxt;
   logic ecc_dbe_r, ecc_dbe_nxt;

   assign ecc_sbe_nxt =   fs_dc_tag_ecc_sb_error_r | fs_dc_data_ecc_sb_error_r
                        | fs_dccm_ecc_sb_error_r
                        | fs_ic_tag_ecc_sb_error_r | fs_ic_data_ecc_sb_error_r
                        | fs_itlb_ecc_sb_error_r | fs_dtlb_ecc_sb_error_r
                        ;
   assign ecc_dbe_nxt =  fs_dc_tag_ecc_db_error_r | fs_dc_data_ecc_db_error_r
                       | fs_dccm_ecc_db_error_r
                       | fs_ic_tag_ecc_db_error_r | fs_ic_data_ecc_db_error_r
                        | fs_itlb_ecc_db_error_r | fs_dtlb_ecc_db_error_r
                        ;

   // Register final ECC flags
   always_ff @(posedge nl2arc0_clk or posedge nl2arc0_rst_sync)
   begin : arc0_ecc_reg_PROC
     if (nl2arc0_rst_sync == 1'b1)
     begin
       ecc_sbe_r <= 1'b0;
       ecc_dbe_r <= 1'b0;
     end
     else // Always enabled ff
     begin
       ecc_sbe_r <= ecc_sbe_nxt;
       ecc_dbe_r <= ecc_dbe_nxt;
     end
   end : arc0_ecc_reg_PROC
   // ECC outputs
   assign nl2arc0_ecc_sbe = ecc_sbe_r;
   assign nl2arc0_ecc_dbe = ecc_dbe_r;

   // ECC status of L2 ARC #1 memories
   logic                          arc1_fs_dc_tag_ecc_sb_error_r;
   logic                          arc1_fs_dc_tag_ecc_db_error_r;
   logic                          arc1_fs_dc_data_ecc_sb_error_r;
   logic                          arc1_fs_dc_data_ecc_db_error_r;
   logic                          arc1_fs_dccm_ecc_sb_error_r;
   logic                          arc1_fs_dccm_ecc_db_error_r;
   logic                          arc1_fs_itlb_ecc_sb_error_r;
   logic                          arc1_fs_itlb_ecc_db_error_r;
   logic                          arc1_fs_dtlb_ecc_sb_error_r;
   logic                          arc1_fs_dtlb_ecc_db_error_r;
   logic                          arc1_fs_ic_tag_ecc_sb_error_r;
   logic                          arc1_fs_ic_tag_ecc_db_error_r;
   logic                          arc1_fs_ic_data_ecc_sb_error_r;
   logic                          arc1_fs_ic_data_ecc_db_error_r;

   logic arc1_ecc_sbe_r, arc1_ecc_sbe_nxt;
   logic arc1_ecc_dbe_r, arc1_ecc_dbe_nxt;

   assign arc1_ecc_sbe_nxt =  arc1_fs_dc_tag_ecc_sb_error_r | arc1_fs_dc_data_ecc_sb_error_r
                            | arc1_fs_dccm_ecc_sb_error_r
                            | arc1_fs_ic_tag_ecc_sb_error_r | arc1_fs_ic_data_ecc_sb_error_r
                            | arc1_fs_itlb_ecc_sb_error_r | arc1_fs_dtlb_ecc_sb_error_r
                            ;
   assign arc1_ecc_dbe_nxt =  arc1_fs_dc_tag_ecc_db_error_r | arc1_fs_dc_data_ecc_db_error_r
                            | arc1_fs_dccm_ecc_db_error_r
                            | arc1_fs_ic_tag_ecc_db_error_r | arc1_fs_ic_data_ecc_db_error_r
                            | arc1_fs_itlb_ecc_db_error_r | arc1_fs_dtlb_ecc_db_error_r
                            ;

   // Register final ECC flags
   always_ff @(posedge nl2arc1_clk or posedge nl2arc1_rst_sync)
   begin : arc1_ecc_reg_PROC
     if (nl2arc1_rst_sync == 1'b1)
     begin
       arc1_ecc_sbe_r <= 1'b0;
       arc1_ecc_dbe_r <= 1'b0;
     end
     else // Always enabled ff
     begin
       arc1_ecc_sbe_r <= arc1_ecc_sbe_nxt;
       arc1_ecc_dbe_r <= arc1_ecc_dbe_nxt;
     end
   end : arc1_ecc_reg_PROC
   // ECC outputs
   assign nl2arc1_ecc_sbe = arc1_ecc_sbe_r;
   assign nl2arc1_ecc_dbe = arc1_ecc_dbe_r;


//
// edge detect for all rtt_swe_val
  always_ff @(posedge clk or posedge rst_sync)
  begin
    if (rst_sync)
    begin
      grp0_rtt_swe_val_syn_r <= '0;
      grp1_rtt_swe_val_syn_r <= '0;
      grp2_rtt_swe_val_syn_r <= '0;
      grp3_rtt_swe_val_syn_r <= '0;
      grp4_rtt_swe_val_syn_r <= '0;
      grp5_rtt_swe_val_syn_r <= '0;
      grp6_rtt_swe_val_syn_r <= '0;
      grp7_rtt_swe_val_syn_r <= '0;
      grp8_rtt_swe_val_syn_r <= '0;
      grp9_rtt_swe_val_syn_r <= '0;
      grp10_rtt_swe_val_syn_r <= '0;
      grp11_rtt_swe_val_syn_r <= '0;
      grp12_rtt_swe_val_syn_r <= '0;
      grp13_rtt_swe_val_syn_r <= '0;
      grp14_rtt_swe_val_syn_r <= '0;
      grp15_rtt_swe_val_syn_r <= '0;
      grp16_rtt_swe_val_syn_r <= '0;
    end
    else
    begin
      grp0_rtt_swe_val_syn_r <= {grp0_rtt_swe_val_syn_r[1:0],grp0_rtt_swe_val};
      grp1_rtt_swe_val_syn_r <= {grp1_rtt_swe_val_syn_r[1:0],grp1_rtt_swe_val};
      grp2_rtt_swe_val_syn_r <= {grp2_rtt_swe_val_syn_r[1:0],grp2_rtt_swe_val};
      grp3_rtt_swe_val_syn_r <= {grp3_rtt_swe_val_syn_r[1:0],grp3_rtt_swe_val};
      grp4_rtt_swe_val_syn_r <= {grp4_rtt_swe_val_syn_r[1:0],grp4_rtt_swe_val};
      grp5_rtt_swe_val_syn_r <= {grp5_rtt_swe_val_syn_r[1:0],grp5_rtt_swe_val};
      grp6_rtt_swe_val_syn_r <= {grp6_rtt_swe_val_syn_r[1:0],grp6_rtt_swe_val};
      grp7_rtt_swe_val_syn_r <= {grp7_rtt_swe_val_syn_r[1:0],grp7_rtt_swe_val};
      grp8_rtt_swe_val_syn_r <= {grp8_rtt_swe_val_syn_r[1:0],grp8_rtt_swe_val};
      grp9_rtt_swe_val_syn_r <= {grp9_rtt_swe_val_syn_r[1:0],grp9_rtt_swe_val};
      grp10_rtt_swe_val_syn_r <= {grp10_rtt_swe_val_syn_r[1:0],grp10_rtt_swe_val};
      grp11_rtt_swe_val_syn_r <= {grp11_rtt_swe_val_syn_r[1:0],grp11_rtt_swe_val};
      grp12_rtt_swe_val_syn_r <= {grp12_rtt_swe_val_syn_r[1:0],grp12_rtt_swe_val};
      grp13_rtt_swe_val_syn_r <= {grp13_rtt_swe_val_syn_r[1:0],grp13_rtt_swe_val};
      grp14_rtt_swe_val_syn_r <= {grp14_rtt_swe_val_syn_r[1:0],grp14_rtt_swe_val};
      grp15_rtt_swe_val_syn_r <= {grp15_rtt_swe_val_syn_r[1:0],grp15_rtt_swe_val};
      grp16_rtt_swe_val_syn_r <= {grp16_rtt_swe_val_syn_r[1:0],grp16_rtt_swe_val};
    end
  end
  assign grp0_rtt_swe_val_pulse = !grp0_rtt_swe_val_syn_r[2] && grp0_rtt_swe_val_syn_r[1];
  assign grp1_rtt_swe_val_pulse = !grp1_rtt_swe_val_syn_r[2] && grp1_rtt_swe_val_syn_r[1];
  assign grp2_rtt_swe_val_pulse = !grp2_rtt_swe_val_syn_r[2] && grp2_rtt_swe_val_syn_r[1];
  assign grp3_rtt_swe_val_pulse = !grp3_rtt_swe_val_syn_r[2] && grp3_rtt_swe_val_syn_r[1];
  assign grp4_rtt_swe_val_pulse = !grp4_rtt_swe_val_syn_r[2] && grp4_rtt_swe_val_syn_r[1];
  assign grp5_rtt_swe_val_pulse = !grp5_rtt_swe_val_syn_r[2] && grp5_rtt_swe_val_syn_r[1];
  assign grp6_rtt_swe_val_pulse = !grp6_rtt_swe_val_syn_r[2] && grp6_rtt_swe_val_syn_r[1];
  assign grp7_rtt_swe_val_pulse = !grp7_rtt_swe_val_syn_r[2] && grp7_rtt_swe_val_syn_r[1];
  assign grp8_rtt_swe_val_pulse = !grp8_rtt_swe_val_syn_r[2] && grp8_rtt_swe_val_syn_r[1];
  assign grp9_rtt_swe_val_pulse = !grp9_rtt_swe_val_syn_r[2] && grp9_rtt_swe_val_syn_r[1];
  assign grp10_rtt_swe_val_pulse = !grp10_rtt_swe_val_syn_r[2] && grp10_rtt_swe_val_syn_r[1];
  assign grp11_rtt_swe_val_pulse = !grp11_rtt_swe_val_syn_r[2] && grp11_rtt_swe_val_syn_r[1];
  assign grp12_rtt_swe_val_pulse = !grp12_rtt_swe_val_syn_r[2] && grp12_rtt_swe_val_syn_r[1];
  assign grp13_rtt_swe_val_pulse = !grp13_rtt_swe_val_syn_r[2] && grp13_rtt_swe_val_syn_r[1];
  assign grp14_rtt_swe_val_pulse = !grp14_rtt_swe_val_syn_r[2] && grp14_rtt_swe_val_syn_r[1];
  assign grp15_rtt_swe_val_pulse = !grp15_rtt_swe_val_syn_r[2] && grp15_rtt_swe_val_syn_r[1];
  assign grp16_rtt_swe_val_pulse = !grp16_rtt_swe_val_syn_r[2] && grp16_rtt_swe_val_syn_r[1];
//


    localparam int NUM_MEMMAP          = NUMGRP + 3; // number of memory map aperture: Groups Config + L2ARC master matrix + CBU Matrix + REMAP Bridge

  `AXISYNCWIRES(16,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,1,3,1,1,3,arc0_axi_sccm_sync_);
  `AXISYNCWIRES(16,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,1,3,1,1,3,arc1_axi_sccm_sync_);
  `AXISYNCWIRES(2,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,arc0_axi_cbu_sync_);
  `AXISYNCWIRES(2,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,arc1_axi_cbu_sync_);

  `AXIWIRES(2,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,cbu_axi_);
  `AXIWIRES(2,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,int_cbu_axi_);
  `AXIWIRES(16,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,sccm_axi_);
  `AXIWIRESN(2,2,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,duo_cbu_axi_); // CBU before Matrix Deocder: 0->ARC0 1->ARC1
  `AXIWIRES(16,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,arc1_sccm_axi_);
  `AXIWIRES(2,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,arc1_cbu_axi_);
  `AXIWIRES(2,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,arc1_int_cbu_axi_);
  `AXIWIRES(L2MIDW,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_icbu_int_);
  `AXIWIRESN(2,3,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_cbu_int_); // CBU after Matrix Deocder: 0->Internal 1->NoC port
  `AXIWIRESN(NUMDMI+1,L2MIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_in_);     // collated input AXIs
  `AXIWIRESN(NUMDMI+1,L2MIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,iaxi_slc_);    // input AXI after reg slice
  `AXIWIRESN(NUMDMI+1,L2MIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_slc_);    // input AXI after reg slice
  `AXIWIRESN(NUMGRP,MSTIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_mst_);
  `AXIWIRESN(NUMGRP+1,MSTIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_int_); // group master outputs before slice, one extra to L2DCCM
  `AXIWIRESN(NUMGRP,CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_ccm_);
  `AXIWIRESN(NUMGRP+1,CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_cslc_);      // group ccm inputs after slice, one extra from L2DCCM
  `AXIWIRESN(2,DMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_dm_);                 // ccm inputs after arbitration
  `AXIWIRESN(2,16,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_dm_idw_);                // ccm inputs after arbitration
  //SFT_AXI
  //AXI CONFIG
  `AXICONFIGWIRES(NUMAP,2/*NUM_MST*/,cbu_cfg_);                                     // CBU decoder address map
  `AXICONFIGWIRES(NUMAP,1/*NUM_MST*/,remap_cfg_);                                   // Remap Bridge address map
  `AXICONFIGWIRES(NUMAP,1/*NUM_MST*/,remap_cfg_mc2_);                               // Remap Bridge address map
  `AXICONFIGWIRES(NUMAP,NUMGRP+1,mst_cfg_);                                         // group AXI decoder address map
  `AXIWIRES(1,32,1,1,1,1,1,axi_cfg_id_);                                            // configration interface after ID converter
  `AXIWIRES(1,32,1,1,1,1,1,axi_cfg_id_slc_);                                            // configration interface after ID converter
  `AXIWIRESN(NUMGRP,1,32,1,1,1,1,1,axi_cfg_grp_);
  `AXIWIRESN(NUM_MEMMAP,1,32,1,1,1,1,1,axi_cfg_split_);                             // configuration interface per group
  `AXIWIRESN(NUM_MEMMAP,1,32,1,1,1,1,1,axi_cfg_split_mid_);                             // configuration interface per group
  `AXIWIRES(1,32,1,1,1,1,1,axi_mst_cfg_);                                           // configuration interface for AXI master ports
  `AXIWIRES(1,32,1,1,1,1,1,axi_cbu_cfg_);                                           // configuration interface for CBU Matrix ports
  `AXIWIRES(1,32,1,1,1,1,1,axi_remap_cfg_);                                         // configuration interface for Remap Bridge ports
  `AXICONFIGWIRES(NUM_MEMMAP,NUM_MEMMAP,cfg_amap_);                                     // configuration interface address map
  //DCCM AXI wires
  `AXIWIRES(CCMIDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_dccm_wid_);
  `AXIWIRES(CCMIDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,axi_dccm_nar_);
  //L2ARC NoC
  `AXIWIRES(5,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_l2arc_noc_int_);
  `AXIWIRES(5,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_l2arc_noc_);
  `AXIWIRES(`NPU_AXI_TARGET_ID_WIDTH,32,1,1,1,1,1,axi_cfg_in_);
  `AXIWIRESN(`NPU_AXI_TARGETS,`NPU_AXI_TARGET_ID_WIDTH,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,axi_dmi_);


  //
  // Reset synchronizer
  //
  npu_reset_ctrl
  u_rst_inst
  (
    .clk       ( clk       ),
    .rst_a     ( rst_a     ),
    .rst       ( rst_sync  ),
    .test_mode ( test_mode )
  );


  //
  // Synchronize the debug interface command valid
  //

  npu_reset_ctrl
  u_sync_nl2arc0__rst
  (
    .clk        ( clk             ),
    .rst_a      ( nl2arc0_rst_a  ),
    .test_mode  ( test_mode       ),
    .rst        ( nl2arc0_rst_sync)
  );

  logic   nl2arc0_clk_en_mrg_a;
  assign  nl2arc0_clk_en_mrg_a = nl2arc0_clk_en_a | arc0_axi_sccm_tgt_clk_en;

  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_nl2arc0_clken_cdc_sync
  (
    .clk        ( clk                    ),
    .rst_a      ( nl2arc0_rst_sync  ),
    .din        ( {1{nl2arc0_clk_en_mrg_a}}),
    .dout       ( nl2arc0_clk_en)
  );

  npu_clkgate
  u_clkgate_nl2arc0_cg
  (
    .clk_in       ( clk             ),
    .clock_enable ( nl2arc0_clk_en ),
    .clk_out      ( nl2arc0_clk    )
  );

  npu_reset_ctrl
  u_sync_nl2arc1__rst
  (
    .clk        ( clk             ),
    .rst_a      ( nl2arc1_rst_a  ),
    .test_mode  ( test_mode       ),
    .rst        ( nl2arc1_rst_sync )
  );

  logic   nl2arc1_clk_en_mrg_a;
  assign  nl2arc1_clk_en_mrg_a = nl2arc1_clk_en_a | arc1_axi_sccm_tgt_clk_en;

  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ),
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  )
  u_nl2arc1__pwr_clken_cdc_sync
  (
    .clk        ( clk                   ),
    .rst_a      ( nl2arc1_rst_sync ),
    .din        ( {1{nl2arc1_clk_en_mrg_a}}),
    .dout       ( nl2arc1_clk_en   )
  );

  npu_clkgate
  u_clkgate_nl2arc1_cg
  (
    .clk_in       ( clk             ),
    .clock_enable ( nl2arc1_clk_en ),
    .clk_out      ( nl2arc1_clk    )
  );


  // ARC Trace APB bridge targets
  npu_apb_bridge_tgt
    #(
      .ADDR_WIDTH ( 16 ),
      .DATA_WIDTH ( 32 )
      )
  u_rtt_apb_bridge_inst
    (
     .pclk(clk),
     .rst_a(rst_a),
     .test_mode(test_mode),
     `APBINST(tgt_,arct_),
     `APBASYNCINST(brg_,arct_)
     );

  // L2 cores #0 APB Debug target
  npu_apb_bridge_tgt
    #(
      .ADDR_WIDTH ( 16 ),
      .DATA_WIDTH ( 32 )
      )
  u_arc0_apb_bridge_inst
    (
     .pclk(clk),
     .rst_a(rst_a),
     .test_mode(test_mode),
     `APBINST(tgt_,nl2arc0_),
     `APBASYNCINST(brg_,nl2arc0_)
     );

  // L2 cores #1 APB Debug target
  npu_apb_bridge_tgt
    #(
      .ADDR_WIDTH ( 16 ),
      .DATA_WIDTH ( 32 )
      )
  u_arc1_apb_bridge_inst
    (
     .pclk(clk),
     .rst_a(rst_a),
     .test_mode(test_mode),
     `APBINST(tgt_,nl2arc1_),
     `APBASYNCINST(brg_,nl2arc1_)
     );


  // BVCI debug interface not used (only APB)
  assign dbg_cmdval  = '0;
  assign dbg_address = '0;
  assign dbg_cmd     = '0;
  assign dbg_wdata   = '0;
  assign dbg_resp    = '0;

  // BVCI debug interface not used (only APB)
  assign arc1_dbg_cmdval  = '0;
  assign arc1_dbg_address = '0;
  assign arc1_dbg_cmd     = '0;
  assign arc1_dbg_wdata   = '0;
  assign arc1_dbg_resp    = '0;

  //
  // L2 ARC Instance
  //
  logic [31+`NPU_HAS_MMU*8:0] araddr;
  logic [31+`NPU_HAS_MMU*8:0] awaddr;
  // make 40b address
  always_comb
  begin : ar_PROC
    int_cbu_axi_ar.addr = '0;
    int_cbu_axi_ar.addr[31+`NPU_HAS_MMU*8:0] = araddr;
  end : ar_PROC
  always_comb
  begin : aw_PROC
    int_cbu_axi_aw.addr = '0;
    int_cbu_axi_aw.addr[31+`NPU_HAS_MMU*8:0] = awaddr;
  end : aw_PROC
  logic       int_cbudummyarlock;
  logic       int_cbudummyawlock;
  logic [1:0] int_cbudummyarid;
  logic [1:0] int_cbudummyawid;
  logic [3:0] int_cbudummywid;

  //
  // L2 ARC Instance
  //
  logic [31+`NPU_HAS_MMU*8:0] arc1_araddr;
  logic [31+`NPU_HAS_MMU*8:0] arc1_awaddr;
  // make 40b address
  always_comb
  begin : arc1_ar_PROC
    arc1_int_cbu_axi_ar.addr = '0;
    arc1_int_cbu_axi_ar.addr[31+`NPU_HAS_MMU*8:0] = arc1_araddr;
  end : arc1_ar_PROC
  always_comb
  begin : arc1_aw_PROC
    arc1_int_cbu_axi_aw.addr = '0;
    arc1_int_cbu_axi_aw.addr[31+`NPU_HAS_MMU*8:0] = arc1_awaddr;
  end : arc1_aw_PROC
  logic       arc1_int_cbudummyarlock;
  logic       arc1_int_cbudummyawlock;
  logic [1:0] arc1_int_cbudummyarid;
  logic [1:0] arc1_int_cbudummyawid;
  logic [3:0] arc1_int_cbudummywid;

  logic [`NPU_NUM_GRP-1:0]  grp_irqs;
  assign grp_irqs[0]  =   grp0_evt_vm_irq_a;
  assign grp_irqs[1]  =   grp1_evt_vm_irq_a;
  assign grp_irqs[2]  =   grp2_evt_vm_irq_a;
  assign grp_irqs[3]  =   grp3_evt_vm_irq_a;

// collate irq signals
  logic [54:21] arc1_arc_irqs_a;
  logic         arc1_arc_evm_event;
  always_comb
  begin : arc1_irq_PROC
    // default value
    arc1_arc_irqs_a = '0;
    // ARCsync physical (AC + EID)
    arc1_arc_irqs_a[22] = arc1_arcsync_irq_a[0];
    arc1_arc_irqs_a[23] = arc1_arcsync_irq_a[1];
    // ARCsync VM 0 (AC + EID)
    arc1_arc_irqs_a[24+:2] = arc1_arcsync_irq_a[2+:2];
    // ARCsync VM 1 (AC + EID)
    arc1_arc_irqs_a[26+:2] = arc1_arcsync_irq_a[4+:2];
    // ARCsync VM 2 (AC + EID)
    arc1_arc_irqs_a[28+:2] = arc1_arcsync_irq_a[6+:2];
    // ARCsync VM 3 (AC + EID)
    arc1_arc_irqs_a[30+:2] = arc1_arcsync_irq_a[8+:2];
    // ARCsync VM 4 (AC + EID)
    arc1_arc_irqs_a[32+:2] = arc1_arcsync_irq_a[10+:2];
    // ARCsync VM 5 (AC + EID)
    arc1_arc_irqs_a[34+:2] = arc1_arcsync_irq_a[12+:2];
    // ARCsync VM 6 (AC + EID)
    arc1_arc_irqs_a[36+:2] = arc1_arcsync_irq_a[14+:2];
    // ARCsync VM 7 (AC + EID)
    arc1_arc_irqs_a[38+:2] = arc1_arcsync_irq_a[16+:2];
    arc1_arc_irqs_a[40]  = grp_irqs[0]
                           | scm_dbank_ecc_irq[0]
                             ;
    arc1_arc_irqs_a[41]  = grp_irqs[1]
                           | scm_dbank_ecc_irq[1]
                             ;
    arc1_arc_irqs_a[42]  = grp_irqs[2]
                           | scm_dbank_ecc_irq[2]
                             ;
    arc1_arc_irqs_a[43]  = grp_irqs[3]
                           | scm_dbank_ecc_irq[3]
                             ;
    // STU channels (up to 8), irq44-51
    for (int i = 0; i < NUMSTU; i++)
    begin
      arc1_arc_irqs_a[44+i] = stu_done_irq_a[i];
    end
    arc1_arc_irqs_a[52] = ext_irq0_a;
    arc1_arc_irqs_a[53] = ext_irq1_a;
  end : arc1_irq_PROC

  logic [54:21] arc_irqs_a;
  logic         arc_evm_event;                // wake-up
  always_comb
  begin : irq_PROC
    // default value
    arc_irqs_a = '0;
    // ARCsync physical (AC + EID)
    arc_irqs_a[22] = arcsync_irq_a[0];
    arc_irqs_a[23] = arcsync_irq_a[1];
    // ARCsync VM 0 (AC + EID)
    arc_irqs_a[24+:2] = arcsync_irq_a[2+:2];
    // ARCsync VM 1 (AC + EID)
    arc_irqs_a[26+:2] = arcsync_irq_a[4+:2];
    // ARCsync VM 2 (AC + EID)
    arc_irqs_a[28+:2] = arcsync_irq_a[6+:2];
    // ARCsync VM 3 (AC + EID)
    arc_irqs_a[30+:2] = arcsync_irq_a[8+:2];
    // ARCsync VM 4 (AC + EID)
    arc_irqs_a[32+:2] = arcsync_irq_a[10+:2];
    // ARCsync VM 5 (AC + EID)
    arc_irqs_a[34+:2] = arcsync_irq_a[12+:2];
    // ARCsync VM 6 (AC + EID)
    arc_irqs_a[36+:2] = arcsync_irq_a[14+:2];
    // ARCsync VM 7 (AC + EID)
    arc_irqs_a[38+:2] = arcsync_irq_a[16+:2];
    arc_irqs_a[40]  = grp_irqs[0]
                       | scm_dbank_ecc_irq[0]
                         ;
    arc_irqs_a[41]  = grp_irqs[1]
                       | scm_dbank_ecc_irq[1]
                         ;
    arc_irqs_a[42]  = grp_irqs[2]
                       | scm_dbank_ecc_irq[2]
                         ;
    arc_irqs_a[43]  = grp_irqs[3]
                       | scm_dbank_ecc_irq[3]
                         ;
    // STU channels (up to 8), irq44-51
    for (int i = 0; i < NUMSTU; i++)
    begin
      arc_irqs_a[44+i] = stu_done_irq_a[i];
    end
    arc_irqs_a[52] = ext_irq0_a;
    arc_irqs_a[53] = ext_irq1_a;
  end : irq_PROC

  // collate input events
  always_comb
  begin : arc0_evt_PROC
    arc0_events_in_a = '0;
    // slice child events
    for (int i = 0; i < NUMSLC; i++)
    begin
      arc0_events_in_a[   i] = child_events_r[i][0]; // EVT 0..23
      arc0_events_in_a[24+i] = child_events_r[i][1]; // EVT 24..47
    end
    // stu events
    for (int i = 0; i < NUMSTU; i++)
    begin
      arc0_events_in_a[48+2*i+0] = stu_issue_evt[i]; // EVT 48,50,52, .. ,62
      arc0_events_in_a[48+2*i+1] = stu_done_evt[i];  // EVT 49,51,53, .. ,63
    end
    // ARCsync events
      arc0_events_in_a[64+:2] = arcsync_event_a[2+:2];
      arc0_events_in_a[68+:2] = arcsync_event_a[4+:2];
      arc0_events_in_a[72+:2] = arcsync_event_a[6+:2];
      arc0_events_in_a[76+:2] = arcsync_event_a[8+:2];
      arc0_events_in_a[80+:2] = arcsync_event_a[10+:2];
      arc0_events_in_a[84+:2] = arcsync_event_a[12+:2];
      arc0_events_in_a[88+:2] = arcsync_event_a[14+:2];
      arc0_events_in_a[92+:2] = arcsync_event_a[16+:2];
  end : arc0_evt_PROC

  always_comb
  begin : arc1_evt_PROC
    arc1_events_in_a = '0;
    // slice child events
    for (int i = 0; i < NUMSLC; i++)
    begin
      arc1_events_in_a[   i] = child_events_r[i][0];
      arc1_events_in_a[24+i] = child_events_r[i][1];
    end
    // stu events
    for (int i = 0; i < NUMSTU; i++)
    begin
      arc1_events_in_a[48+2*i+0] = stu_issue_evt[i];
      arc1_events_in_a[48+2*i+1] = stu_done_evt[i];
    end
    // AC events
      arc1_events_in_a[64+:2] = arc1_arcsync_event_a[2+:2];
      arc1_events_in_a[68+:2] = arc1_arcsync_event_a[4+:2];
      arc1_events_in_a[72+:2] = arc1_arcsync_event_a[6+:2];
      arc1_events_in_a[76+:2] = arc1_arcsync_event_a[8+:2];
      arc1_events_in_a[80+:2] = arc1_arcsync_event_a[10+:2];
      arc1_events_in_a[84+:2] = arc1_arcsync_event_a[12+:2];
      arc1_events_in_a[88+:2] = arc1_arcsync_event_a[14+:2];
      arc1_events_in_a[92+:2] = arc1_arcsync_event_a[16+:2];
  end : arc1_evt_PROC

  // Generate Parent Events
  always_comb
  begin : parent_evt_PROC
    parent_events_nxt = '0;
    // slice child events
    for (int i = 0; i < NUMSLC; i++)
    begin
      parent_events_nxt[i][0] |= (arc0_vm_sel=='h0) ? arc0_event_send[i] : 1'b0;
      parent_events_nxt[i][1] |= (arc0_vm_sel!='h0) ? arc0_event_send[i] : 1'b0;
    end
    for (int i = 0; i < NUMSLC; i++)
    begin
      parent_events_nxt[i][0] |= (arc1_vm_sel=='h0) ? arc1_event_send[i] : 1'b0;
      parent_events_nxt[i][1] |= (arc1_vm_sel!='h0) ? arc1_event_send[i] : 1'b0;
    end
  end : parent_evt_PROC

//
  always_ff @(posedge clk or posedge rst_sync)
  begin : buffer_evt_PROC
    if (rst_sync)
    begin
      parent_events_r <= '0;
      child_events_r  <= '0;
    end
    else
    begin
      parent_events_r <= parent_events_nxt;
      child_events_r  <= child_events_a;
    end
  end : buffer_evt_PROC
//

  assign parent_events = parent_events_r;


  // Unconnected CTI signals
  logic        cti_halt;
  logic        cti_break;
  logic        cti_sleep;
  logic        cti_ap_hit;
  logic [7:0]  cti_ap_status;

  
  // actual HS instance ARC0
  npuarc_hs_cluster_top
  u_npu_l2_arc0
  (
    // CBU (cache and LD/ST)
    .cbu_axi_arvalid          (int_cbu_axi_arvalid),
    .cbu_axi_arready          (int_cbu_axi_arready),
    .cbu_axi_arid             ({int_cbudummyarid,int_cbu_axi_arid}),
    .cbu_axi_arsize           (int_cbu_axi_ar.size ),
    .cbu_axi_arlock           ({int_cbudummyarlock,int_cbu_axi_ar.lock[0]} ),
    .cbu_axi_araddr           (araddr ),
    .cbu_axi_arcache          (int_cbu_axi_ar.cache),
    .cbu_axi_arprot           (int_cbu_axi_ar.prot ),
    .cbu_axi_arburst          (int_cbu_axi_ar.burst[1:0]),
    .cbu_axi_arlen            (int_cbu_axi_ar.len  ),

    .cbu_axi_rvalid           (int_cbu_axi_rvalid ),
    .cbu_axi_rready           (int_cbu_axi_rready ),
    .cbu_axi_rid              ({2'b00,int_cbu_axi_rid}),
    .cbu_axi_rdata            (int_cbu_axi_rdata  ),
    .cbu_axi_rresp            (int_cbu_axi_rresp[1:0]  ),
    .cbu_axi_rlast            (int_cbu_axi_rlast  ),

    .cbu_axi_awvalid          (int_cbu_axi_awvalid),
    .cbu_axi_awready          (int_cbu_axi_awready),
    .cbu_axi_awid             ({int_cbudummyawid,int_cbu_axi_awid}),
    .cbu_axi_awaddr           (awaddr ),
    .cbu_axi_awcache          (int_cbu_axi_aw.cache),
    .cbu_axi_awprot           (int_cbu_axi_aw.prot ),
    .cbu_axi_awlock           ({int_cbudummyawlock,int_cbu_axi_aw.lock[0]} ),
    .cbu_axi_awburst          (int_cbu_axi_aw.burst[1:0]),
    .cbu_axi_awlen            (int_cbu_axi_aw.len  ),
    .cbu_axi_awsize           (int_cbu_axi_aw.size ),

    .cbu_axi_wvalid           (int_cbu_axi_wvalid ),
    .cbu_axi_wready           (int_cbu_axi_wready ),
    .cbu_axi_wid              (int_cbudummywid    ),
    .cbu_axi_wdata            (int_cbu_axi_wdata  ),
    .cbu_axi_wstrb            (int_cbu_axi_wstrb  ),
    .cbu_axi_wlast            (int_cbu_axi_wlast  ),

    .cbu_axi_bid              ({2'b00,int_cbu_axi_bid}),
    .cbu_axi_bvalid           (int_cbu_axi_bvalid ),
    .cbu_axi_bresp            (int_cbu_axi_bresp[1:0]),
    .cbu_axi_bready           (int_cbu_axi_bready ),

    // DMI Access
    .sccm_axi_arvalid         (sccm_axi_arvalid),
    .sccm_axi_arready         (sccm_axi_arready),
    .sccm_axi_arid            (sccm_axi_arid   ),
    .sccm_axi_arsize          (sccm_axi_ar.size ),
    .sccm_axi_araddr          (sccm_axi_ar.addr[23:0] ),
    .sccm_axi_arburst         (sccm_axi_ar.burst[1:0]),
    .sccm_axi_arlen           (sccm_axi_ar.len  ),
    .sccm_axi_arregion        (2'b0),

    .sccm_axi_rvalid          (sccm_axi_rvalid ),
    .sccm_axi_rready          (sccm_axi_rready ),
    .sccm_axi_rid             (sccm_axi_rid    ),
    .sccm_axi_rdata           (sccm_axi_rdata  ),
    .sccm_axi_rresp           (sccm_axi_rresp[1:0]  ),
    .sccm_axi_rlast           (sccm_axi_rlast  ),

    .sccm_axi_awvalid         (sccm_axi_awvalid),
    .sccm_axi_awready         (sccm_axi_awready),
    .sccm_axi_awid            (sccm_axi_awid   ),
    .sccm_axi_awaddr          (sccm_axi_aw.addr[23:0] ),
    .sccm_axi_awburst         (sccm_axi_aw.burst[1:0]),
    .sccm_axi_awlen           (sccm_axi_aw.len  ),
    .sccm_axi_awsize          (sccm_axi_aw.size ),
    .sccm_axi_awregion        (2'b0),

    .sccm_axi_wvalid          (sccm_axi_wvalid ),
    .sccm_axi_wready          (sccm_axi_wready ),
    .sccm_axi_wdata           (sccm_axi_wdata  ),
    .sccm_axi_wstrb           (sccm_axi_wstrb  ),
    .sccm_axi_wlast           (sccm_axi_wlast  ),

    .sccm_axi_bid             (sccm_axi_bid    ),
    .sccm_axi_bvalid          (sccm_axi_bvalid ),
    .sccm_axi_bresp           (sccm_axi_bresp[1:0]  ),
    .sccm_axi_bready          (sccm_axi_bready ),

    // Clock and Reset
    .mbus_clk_en              (1'b1),
    .dbus_clk_en              (1'b1),
    .clk                      (nl2arc0_clk),
    .rst_a                    (nl2arc0_rst_sync),
    .test_mode                (test_mode   ),
    .watchdog_reset           (l2_watchdog_reset),
    .wdt_clk                  (wdt_clk              ),
    .wdt_ext_timeout_ack_r    (1'b1                 ),

    // Interrupts
    .irq17_a                  (1'b0),
    .irq19_a                  (1'b0),
    .irq21_a                  (arc_irqs_a[21]),
    .irq22_a                  (arc_irqs_a[22]),
    .irq23_a                  (arc_irqs_a[23]),
    .irq24_a                  (arc_irqs_a[24]),
    .irq25_a                  (arc_irqs_a[25]),
    .irq26_a                  (arc_irqs_a[26]),
    .irq27_a                  (arc_irqs_a[27]),
    .irq28_a                  (arc_irqs_a[28]),
    .irq29_a                  (arc_irqs_a[29]),
    .irq30_a                  (arc_irqs_a[30]),
    .irq31_a                  (arc_irqs_a[31]),
    .irq32_a                  (arc_irqs_a[32]),
    .irq33_a                  (arc_irqs_a[33]),
    .irq34_a                  (arc_irqs_a[34]),
    .irq35_a                  (arc_irqs_a[35]),
    .irq36_a                  (arc_irqs_a[36]),
    .irq37_a                  (arc_irqs_a[37]),
    .irq38_a                  (arc_irqs_a[38]),
    .irq39_a                  (arc_irqs_a[39]),
    .irq40_a                  (arc_irqs_a[40]),
    .irq41_a                  (arc_irqs_a[41]),
    .irq42_a                  (arc_irqs_a[42]),
    .irq43_a                  (arc_irqs_a[43]),
    .irq44_a                  (arc_irqs_a[44]),
    .irq45_a                  (arc_irqs_a[45]),
    .irq46_a                  (arc_irqs_a[46]),
    .irq47_a                  (arc_irqs_a[47]),
    .irq48_a                  (arc_irqs_a[48]),
    .irq49_a                  (arc_irqs_a[49]),
    .irq50_a                  (arc_irqs_a[50]),
    .irq51_a                  (arc_irqs_a[51]),
    .irq52_a                  (arc_irqs_a[52]),
    .irq53_a                  (arc_irqs_a[53]),
    .irq54_a                  (arc_irqs_a[54]),

    .wdt_ext_timeout_r        (                     ), // Unconnected
    .wdt_reset                (wdt_reset            ),
    .wdt_reset_wdt_clk        (wdt_reset_wdt_clk    ),
    .fs_dc_tag_ecc_sb_error_r (fs_dc_tag_ecc_sb_error_r),
    .fs_dc_tag_ecc_db_error_r (fs_dc_tag_ecc_db_error_r),
    .fs_dc_data_ecc_sb_error_r(fs_dc_data_ecc_sb_error_r),
    .fs_dc_data_ecc_db_error_r(fs_dc_data_ecc_db_error_r),
    .fs_dccm_ecc_sb_error_r   (fs_dccm_ecc_sb_error_r),
    .fs_dccm_ecc_db_error_r   (fs_dccm_ecc_db_error_r),
    .fs_itlb_ecc_sb_error_r   (fs_itlb_ecc_sb_error_r),
    .fs_itlb_ecc_db_error_r   (fs_itlb_ecc_db_error_r),
    .fs_dtlb_ecc_sb_error_r   (fs_dtlb_ecc_sb_error_r),
    .fs_dtlb_ecc_db_error_r   (fs_dtlb_ecc_db_error_r),
    .fs_ic_tag_ecc_sb_error_r (fs_ic_tag_ecc_sb_error_r),
    .fs_ic_tag_ecc_db_error_r (fs_ic_tag_ecc_db_error_r),
    .fs_ic_data_ecc_sb_error_r(fs_ic_data_ecc_sb_error_r),
    .fs_ic_data_ecc_db_error_r(fs_ic_data_ecc_db_error_r),
    .cc_idle                  ( ),                         // intentionally left unconnected

    // ARCsync
    .clusternum               (clusternum),                // input io_pad_ring
    .arc_event_a              (arc_evm_event),             // input io_pad_ring
    .arc_halt_req_a           (arc_halt_req_a),            // input io_pad_ring
    .arc_run_req_a            (arc_run_req_a),             // input io_pad_ring
    .intvbase_in              (intvbase_in),               // input io_pad_ring
    .arcnum                   (arcnum),                    // input io_pad_ring
    .arc_halt_ack             (arc_halt_ack),              // output
    .arc_run_ack              (arc_run_ack),               // output
    .sys_halt_r               (sys_halt_r),                // output
    .sys_tf_halt_r            (sys_tf_halt_r),             // output
    .sys_sleep_r              (sys_sleep_r),               // output
    .sys_sleep_mode_r         (sys_sleep_mode_r),          // output
    .dbg_cache_rst_disable    (1'b0),
    .dccm_dmi_priority        (1'b0),

    // ARC_Trace RTT interface
    .rtt_drd_r                (rtt_drd_r         ),
    .rtt_prod_sel             (rtt_prod_sel      ),
    .rtt_freeze               (rtt_freeze        ),
    .rtt_src_num              (rtt_src_num       ),
    .rtt_write_a              (rtt_write_a       ),
    .rtt_read_a               (rtt_read_a        ),
    .rtt_addr_r               (rtt_addr_r        ),
    .rtt_dwr_r                (rtt_dwr_r         ),
    .rtt_ss_halt              (rtt_ss_halt       ),
    .rtt_hw_bp                (rtt_hw_bp         ),
    .rtt_hw_exc               (rtt_hw_exc        ),
    .rtt_dbg_halt             (rtt_dbg_halt      ),
    .rtt_rst_applied          (rtt_rst_applied   ),
    .rtt_uop_is_leave         (rtt_uop_is_leave  ),
    .rtt_in_deslot            (rtt_in_deslot     ),
    .rtt_in_eslot             (rtt_in_eslot      ),
    .rtt_inst_commit          (rtt_inst_commit   ),
    .rtt_inst_addr            (rtt_inst_addr     ),
    .rtt_cond_valid           (rtt_cond_valid    ),
    .rtt_cond_pass            (rtt_cond_pass     ),
    .rtt_branch               (rtt_branch        ),
    .rtt_branch_indir         (rtt_branch_indir  ),
    .rtt_branch_taddr         (rtt_branch_taddr  ),
    .rtt_dslot                (rtt_dslot         ),
    .rtt_exception            (rtt_exception     ),
    .rtt_exception_rtn        (rtt_exception_rtn ),
    .rtt_interrupt            (rtt_interrupt     ),
    .rtt_sleep_mode           (rtt_sleep_mode    ),
    .rtt_zd_loop              (rtt_zd_loop       ),
    .rtt_wp_val               (rtt_wp_val        ),
    .rtt_wp_hit               (rtt_wp_hit        ),
    .rtt_sw_bp                (rtt_sw_bp         ),
    .rtt_process_id           (rtt_process_id    ),
    .rtt_pid_wr_en            (rtt_pid_wr_en     ),
    .rtt_swe_data             (rtt_swe_data      ),
    .rtt_swe_val              (rtt_swe_val       ),

    .cti_ap_status            (cti_ap_status     ),
    .cti_halt                 (cti_halt          ),
    .cti_break                (cti_break         ),
    .cti_sleep                (cti_sleep         ),
    .cti_ap_hit               (cti_ap_hit        ),

    // Debug interface
    .dbg_prot_sel             (arct_dbg_prot_sel ),
    .pclkdbg_en               (1'b1              ),
    .dbgen                    (nl2arc0_dbgen),
    .niden                    (nl2arc0_niden),
    .presetdbgn               (arct_rst_an       ),
    .paddrdbg                 ({16'h0,nl2arc0_paddr}),
    .pseldbg                  (nl2arc0_psel    ),
    .penabledbg               (nl2arc0_penable ),
    .pwritedbg                (nl2arc0_pwrite  ),
    .pwdatadbg                (nl2arc0_pwdata  ),
    .preadydbg                (nl2arc0_pready  ),
    .prdatadbg                (nl2arc0_prdata  ),
    .pslverrdbg               (nl2arc0_pslverr ),

    // Event manager
    .EventManager_evm_event_a (arc0_events_in_a),
    .EventManager_evm_sleep   (sys_sleep_r),
    .EventManager_evm_wakeup  (arc_evm_event),
    .EventManager_evm_send    (arc0_event_send),
    .EventManager_evt_vm_irq  (nl2arc0_evt_vm_irq),
    .EventManager_evt_vm_sel  (arc0_vm_sel),
    .EventManager_vm_grp0_sid (npu_grp0_sid ),
    .EventManager_vm_grp0_ssid(npu_grp0_ssid),
    .EventManager_vm_grp1_sid (npu_grp1_sid ),
    .EventManager_vm_grp1_ssid(npu_grp1_ssid),
    .EventManager_vm_grp2_sid (npu_grp2_sid ),
    .EventManager_vm_grp2_ssid(npu_grp2_ssid),
    .EventManager_vm_grp3_sid (npu_grp3_sid ),
    .EventManager_vm_grp3_ssid(npu_grp3_ssid),

    .mem_sd                   (nl2arc0_pd_mem  ),
    .mem_ds                   (1'b0                 ),
    // Debug
    .dbg_cmdval               (dbg_cmdval),
    .dbg_cmdack               (dbg_cmdack),
    .dbg_eop                  (1'b1),
    .dbg_address              (dbg_address),
    .dbg_be                   (4'b1111),
    .dbg_cmd                  (dbg_cmd),
    .dbg_wdata                (dbg_wdata),
    .dbg_rspval               (dbg_rspval),
    .dbg_rspack               (1'b1    ),
    .dbg_reop                 (        ), // intentionally unconnected
    .dbg_rerr                 (        ), // intentionally unconnected
    .dbg_rdata                (dbg_rdata),
    .debug_reset              (dbg_reset)
  );

  // Second L2 ARC core

  //ARC_Trace signals (stubbed for L2 ARC1)
  logic [31:0] arc1_rtt_drd_r;
  logic        arc1_rtt_prod_sel;
  logic        arc1_rtt_freeze;
  logic [7:0]  arc1_rtt_src_num;
  logic        arc1_rtt_write_a;
  logic        arc1_rtt_read_a;
  logic [31:0] arc1_rtt_addr_r;
  logic [31:0] arc1_rtt_dwr_r;
  logic        arc1_rtt_ss_halt;
  logic        arc1_rtt_hw_bp;
  logic        arc1_rtt_hw_exc;
  logic        arc1_rtt_dbg_halt;
  logic        arc1_rtt_rst_applied;
  logic        arc1_rtt_uop_is_leave;
  logic        arc1_rtt_in_deslot;
  logic        arc1_rtt_in_eslot;
  logic        arc1_rtt_inst_commit;
  logic [31:1] arc1_rtt_inst_addr;
  logic        arc1_rtt_cond_valid;
  logic        arc1_rtt_cond_pass;
  logic        arc1_rtt_branch;
  logic        arc1_rtt_branch_indir;
  logic [31:1] arc1_rtt_branch_taddr;
  logic        arc1_rtt_dslot;
  logic        arc1_rtt_exception;
  logic        arc1_rtt_exception_rtn;
  logic        arc1_rtt_interrupt;
  logic        arc1_rtt_sleep_mode;
  logic        arc1_rtt_zd_loop;
  logic [7:0]  arc1_rtt_wp_val;
  logic        arc1_rtt_wp_hit;
  logic        arc1_rtt_sw_bp;
  logic [7:0]  arc1_rtt_process_id;
  logic        arc1_rtt_pid_wr_en;
  logic [32:0] arc1_rtt_swe_data;
  logic        arc1_rtt_swe_val;
  logic [32:0] arc1_l1_swe_idata;
  logic        arc1_l1_swe_ivalid;

  // RTT producer on L2ARC #1 is not connected
  assign arc1_rtt_drd_r    = 32'b0;
  assign arc1_rtt_prod_sel = 1'b0;
  assign arc1_rtt_freeze   = 1'b0;
  assign arc1_rtt_src_num  = 8'b0;

  logic [7:0]  arc1_cti_ap_status;
  // Unconnected CTI signals
  logic        arc1_cti_halt;
  logic        arc1_cti_break;
  logic        arc1_cti_sleep;
  logic        arc1_cti_ap_hit;


  // actual HS instance ARC1
  npuarc_hs_cluster_top
  u_npu_l2_arc1
  (
    // CBU
    .cbu_axi_arvalid          (arc1_int_cbu_axi_arvalid),
    .cbu_axi_arready          (arc1_int_cbu_axi_arready),
    .cbu_axi_arid             ({arc1_int_cbudummyarid,arc1_int_cbu_axi_arid}),
    .cbu_axi_arsize           (arc1_int_cbu_axi_ar.size ),
    .cbu_axi_arlock           ({arc1_int_cbudummyarlock,arc1_int_cbu_axi_ar.lock[0]} ),
    .cbu_axi_araddr           (arc1_araddr ),
    .cbu_axi_arcache          (arc1_int_cbu_axi_ar.cache),
    .cbu_axi_arprot           (arc1_int_cbu_axi_ar.prot ),
    .cbu_axi_arburst          (arc1_int_cbu_axi_ar.burst[1:0]),
    .cbu_axi_arlen            (arc1_int_cbu_axi_ar.len  ),

    .cbu_axi_rvalid           (arc1_int_cbu_axi_rvalid ),
    .cbu_axi_rready           (arc1_int_cbu_axi_rready ),
    .cbu_axi_rid              ({2'b00,arc1_int_cbu_axi_rid}),
    .cbu_axi_rdata            (arc1_int_cbu_axi_rdata  ),
    .cbu_axi_rresp            (arc1_int_cbu_axi_rresp[1:0]  ),
    .cbu_axi_rlast            (arc1_int_cbu_axi_rlast  ),

    .cbu_axi_awvalid          (arc1_int_cbu_axi_awvalid),
    .cbu_axi_awready          (arc1_int_cbu_axi_awready),
    .cbu_axi_awid             ({arc1_int_cbudummyawid,arc1_int_cbu_axi_awid}),
    .cbu_axi_awaddr           (arc1_awaddr ),
    .cbu_axi_awcache          (arc1_int_cbu_axi_aw.cache),
    .cbu_axi_awprot           (arc1_int_cbu_axi_aw.prot ),
    .cbu_axi_awlock           ({arc1_int_cbudummyawlock,arc1_int_cbu_axi_aw.lock[0]} ),
    .cbu_axi_awburst          (arc1_int_cbu_axi_aw.burst[1:0]),
    .cbu_axi_awlen            (arc1_int_cbu_axi_aw.len  ),
    .cbu_axi_awsize           (arc1_int_cbu_axi_aw.size ),

    .cbu_axi_wvalid           (arc1_int_cbu_axi_wvalid ),
    .cbu_axi_wready           (arc1_int_cbu_axi_wready ),
    .cbu_axi_wid              (arc1_int_cbudummywid    ),
    .cbu_axi_wdata            (arc1_int_cbu_axi_wdata  ),
    .cbu_axi_wstrb            (arc1_int_cbu_axi_wstrb  ),
    .cbu_axi_wlast            (arc1_int_cbu_axi_wlast  ),

    .cbu_axi_bid              ({2'b00,arc1_int_cbu_axi_bid}),
    .cbu_axi_bvalid           (arc1_int_cbu_axi_bvalid ),
    .cbu_axi_bresp            (arc1_int_cbu_axi_bresp[1:0]),
    .cbu_axi_bready           (arc1_int_cbu_axi_bready ),

    // DMI Access
    .sccm_axi_arvalid         (arc1_sccm_axi_arvalid),
    .sccm_axi_arready         (arc1_sccm_axi_arready),
    .sccm_axi_arid            (arc1_sccm_axi_arid   ),
    .sccm_axi_arsize          (arc1_sccm_axi_ar.size ),
    .sccm_axi_araddr          (arc1_sccm_axi_ar.addr[23:0] ),
    .sccm_axi_arburst         (arc1_sccm_axi_ar.burst[1:0]),
    .sccm_axi_arlen           (arc1_sccm_axi_ar.len  ),
    .sccm_axi_arregion        (2'b0),

    .sccm_axi_rvalid          (arc1_sccm_axi_rvalid ),
    .sccm_axi_rready          (arc1_sccm_axi_rready ),
    .sccm_axi_rid             (arc1_sccm_axi_rid    ),
    .sccm_axi_rdata           (arc1_sccm_axi_rdata  ),
    .sccm_axi_rresp           (arc1_sccm_axi_rresp[1:0]  ),
    .sccm_axi_rlast           (arc1_sccm_axi_rlast  ),

    .sccm_axi_awvalid         (arc1_sccm_axi_awvalid),
    .sccm_axi_awready         (arc1_sccm_axi_awready),
    .sccm_axi_awid            (arc1_sccm_axi_awid   ),
    .sccm_axi_awaddr          (arc1_sccm_axi_aw.addr[23:0] ),
    .sccm_axi_awburst         (arc1_sccm_axi_aw.burst[1:0]),
    .sccm_axi_awlen           (arc1_sccm_axi_aw.len  ),
    .sccm_axi_awsize          (arc1_sccm_axi_aw.size ),
    .sccm_axi_awregion        (2'b0),

    .sccm_axi_wvalid          (arc1_sccm_axi_wvalid ),
    .sccm_axi_wready          (arc1_sccm_axi_wready ),
    .sccm_axi_wdata           (arc1_sccm_axi_wdata  ),
    .sccm_axi_wstrb           (arc1_sccm_axi_wstrb  ),
    .sccm_axi_wlast           (arc1_sccm_axi_wlast  ),

    .sccm_axi_bid             (arc1_sccm_axi_bid    ),
    .sccm_axi_bvalid          (arc1_sccm_axi_bvalid ),
    .sccm_axi_bresp           (arc1_sccm_axi_bresp[1:0]  ),
    .sccm_axi_bready          (arc1_sccm_axi_bready ),

    // CLK EN
    .mbus_clk_en              (1'b1),
    .dbus_clk_en              (1'b1),
    .clk                      (nl2arc1_clk),
    .rst_a                    (nl2arc1_rst_sync),
    .test_mode                (test_mode),
    .watchdog_reset           (arc1_l2_watchdog_reset),

    .irq17_a                  (1'b0),
    .irq19_a                  (1'b0),
    .irq21_a                  (arc1_arc_irqs_a[21]),
    .irq22_a                  (arc1_arc_irqs_a[22]),
    .irq23_a                  (arc1_arc_irqs_a[23]),
    .irq24_a                  (arc1_arc_irqs_a[24]),
    .irq25_a                  (arc1_arc_irqs_a[25]),
    .irq26_a                  (arc1_arc_irqs_a[26]),
    .irq27_a                  (arc1_arc_irqs_a[27]),
    .irq28_a                  (arc1_arc_irqs_a[28]),
    .irq29_a                  (arc1_arc_irqs_a[29]),
    .irq30_a                  (arc1_arc_irqs_a[30]),
    .irq31_a                  (arc1_arc_irqs_a[31]),
    .irq32_a                  (arc1_arc_irqs_a[32]),
    .irq33_a                  (arc1_arc_irqs_a[33]),
    .irq34_a                  (arc1_arc_irqs_a[34]),
    .irq35_a                  (arc1_arc_irqs_a[35]),
    .irq36_a                  (arc1_arc_irqs_a[36]),
    .irq37_a                  (arc1_arc_irqs_a[37]),
    .irq38_a                  (arc1_arc_irqs_a[38]),
    .irq39_a                  (arc1_arc_irqs_a[39]),
    .irq40_a                  (arc1_arc_irqs_a[40]),
    .irq41_a                  (arc1_arc_irqs_a[41]),
    .irq42_a                  (arc1_arc_irqs_a[42]),
    .irq43_a                  (arc1_arc_irqs_a[43]),
    .irq44_a                  (arc1_arc_irqs_a[44]),
    .irq45_a                  (arc1_arc_irqs_a[45]),
    .irq46_a                  (arc1_arc_irqs_a[46]),
    .irq47_a                  (arc1_arc_irqs_a[47]),
    .irq48_a                  (arc1_arc_irqs_a[48]),
    .irq49_a                  (arc1_arc_irqs_a[49]),
    .irq50_a                  (arc1_arc_irqs_a[50]),
    .irq51_a                  (arc1_arc_irqs_a[51]),
    .irq52_a                  (arc1_arc_irqs_a[52]),
    .irq53_a                  (arc1_arc_irqs_a[53]),
    .irq54_a                  (arc1_arc_irqs_a[54]),
    .wdt_clk                  (arc1_wdt_clk              ),
    .wdt_ext_timeout_ack_r    (1'b1                      ),
    .wdt_ext_timeout_r        (                          ), // Unconnected
    .wdt_reset                (arc1_wdt_reset            ),
    .wdt_reset_wdt_clk        (arc1_wdt_reset_wdt_clk    ),
    .fs_dc_tag_ecc_sb_error_r (arc1_fs_dc_tag_ecc_sb_error_r),
    .fs_dc_tag_ecc_db_error_r (arc1_fs_dc_tag_ecc_db_error_r),
    .fs_dc_data_ecc_sb_error_r(arc1_fs_dc_data_ecc_sb_error_r),
    .fs_dc_data_ecc_db_error_r(arc1_fs_dc_data_ecc_db_error_r),
    .fs_dccm_ecc_sb_error_r   (arc1_fs_dccm_ecc_sb_error_r),
    .fs_dccm_ecc_db_error_r   (arc1_fs_dccm_ecc_db_error_r),
    .fs_itlb_ecc_sb_error_r   (arc1_fs_itlb_ecc_sb_error_r),
    .fs_itlb_ecc_db_error_r   (arc1_fs_itlb_ecc_db_error_r),
    .fs_dtlb_ecc_sb_error_r   (arc1_fs_dtlb_ecc_sb_error_r),
    .fs_dtlb_ecc_db_error_r   (arc1_fs_dtlb_ecc_db_error_r),
    .fs_ic_tag_ecc_sb_error_r (arc1_fs_ic_tag_ecc_sb_error_r),
    .fs_ic_tag_ecc_db_error_r (arc1_fs_ic_tag_ecc_db_error_r),
    .fs_ic_data_ecc_sb_error_r(arc1_fs_ic_data_ecc_sb_error_r),
    .fs_ic_data_ecc_db_error_r(arc1_fs_ic_data_ecc_db_error_r),
    .cc_idle                  ( ),                         // intentionally left unconnected

    // ARCsync
    .clusternum               (arc1_clusternum),                // input io_pad_ring
    .arc_event_a              (arc1_arc_evm_event),             // input io_pad_ring
    .arc_halt_req_a           (arc1_arc_halt_req_a),            // input io_pad_ring
    .arc_run_req_a            (arc1_arc_run_req_a),             // input io_pad_ring
    .intvbase_in              (arc1_intvbase_in),               // input io_pad_ring
    .arcnum                   (arc1_arcnum),                    // input io_pad_ring
    .arc_halt_ack             (arc1_arc_halt_ack),              // output
    .arc_run_ack              (arc1_arc_run_ack),               // output
    .sys_halt_r               (arc1_sys_halt_r),                // output
    .sys_tf_halt_r            (arc1_sys_tf_halt_r),             // output
    .sys_sleep_r              (arc1_sys_sleep_r),               // output
    .sys_sleep_mode_r         (arc1_sys_sleep_mode_r),          // output
    .dbg_cache_rst_disable    (1'b0),
    .dccm_dmi_priority        (1'b0),

    //ARC_Trace
    .rtt_drd_r                (arc1_rtt_drd_r         ),
    .rtt_prod_sel             (arc1_rtt_prod_sel      ),
    .rtt_freeze               (arc1_rtt_freeze        ),
    .rtt_src_num              (arc1_rtt_src_num       ),
    .rtt_write_a              (arc1_rtt_write_a       ),
    .rtt_read_a               (arc1_rtt_read_a        ),
    .rtt_addr_r               (arc1_rtt_addr_r        ),
    .rtt_dwr_r                (arc1_rtt_dwr_r         ),
    .rtt_ss_halt              (arc1_rtt_ss_halt       ),
    .rtt_hw_bp                (arc1_rtt_hw_bp         ),
    .rtt_hw_exc               (arc1_rtt_hw_exc        ),
    .rtt_dbg_halt             (arc1_rtt_dbg_halt      ),
    .rtt_rst_applied          (arc1_rtt_rst_applied   ),
    .rtt_uop_is_leave         (arc1_rtt_uop_is_leave  ),
    .rtt_in_deslot            (arc1_rtt_in_deslot     ),
    .rtt_in_eslot             (arc1_rtt_in_eslot      ),
    .rtt_inst_commit          (arc1_rtt_inst_commit   ),
    .rtt_inst_addr            (arc1_rtt_inst_addr     ),
    .rtt_cond_valid           (arc1_rtt_cond_valid    ),
    .rtt_cond_pass            (arc1_rtt_cond_pass     ),
    .rtt_branch               (arc1_rtt_branch        ),
    .rtt_branch_indir         (arc1_rtt_branch_indir  ),
    .rtt_branch_taddr         (arc1_rtt_branch_taddr  ),
    .rtt_dslot                (arc1_rtt_dslot         ),
    .rtt_exception            (arc1_rtt_exception     ),
    .rtt_exception_rtn        (arc1_rtt_exception_rtn ),
    .rtt_interrupt            (arc1_rtt_interrupt     ),
    .rtt_sleep_mode           (arc1_rtt_sleep_mode    ),
    .rtt_zd_loop              (arc1_rtt_zd_loop       ),
    .rtt_wp_val               (arc1_rtt_wp_val        ),
    .rtt_wp_hit               (arc1_rtt_wp_hit        ),
    .rtt_sw_bp                (arc1_rtt_sw_bp         ),
    .rtt_process_id           (arc1_rtt_process_id    ),
    .rtt_pid_wr_en            (arc1_rtt_pid_wr_en     ),
    .rtt_swe_data             (arc1_rtt_swe_data      ),
    .rtt_swe_val              (arc1_rtt_swe_val       ),

    .cti_ap_status            (arc1_cti_ap_status     ),
    // CTI
    .cti_halt                 (arc1_cti_halt          ),
    .cti_break                (arc1_cti_break         ),
    .cti_sleep                (arc1_cti_sleep         ),
    .cti_ap_hit               (arc1_cti_ap_hit        ),

    // Debug
    .dbg_prot_sel             (arct_dbg_prot_sel      ),
    .dbgen                    (nl2arc1_dbgen     ),
    .niden                    (nl2arc1_niden     ),
    .pclkdbg_en               (1'b1                   ),
    .presetdbgn               (arct_rst_an            ),
    .paddrdbg                 ({16'h0,nl2arc1_paddr}),
    .pseldbg                  (nl2arc1_psel      ),
    .penabledbg               (nl2arc1_penable   ),
    .pwritedbg                (nl2arc1_pwrite    ),
    .pwdatadbg                (nl2arc1_pwdata    ),
    .preadydbg                (nl2arc1_pready    ),
    .prdatadbg                (nl2arc1_prdata    ),
    .pslverrdbg               (nl2arc1_pslverr   ),

    // Event manager
    .EventManager_evm_event_a (arc1_events_in_a),
    .EventManager_evm_sleep   (arc1_sys_sleep_r),
    .EventManager_evm_wakeup  (arc1_arc_evm_event),
    .EventManager_evm_send    (arc1_event_send),
    .EventManager_evt_vm_irq  (nl2arc1_evt_vm_irq),
    .EventManager_evt_vm_sel  (arc1_vm_sel),
    .EventManager_vm_grp0_sid (),
    .EventManager_vm_grp0_ssid(),
    .EventManager_vm_grp1_sid (),
    .EventManager_vm_grp1_ssid(),
    .EventManager_vm_grp2_sid (),
    .EventManager_vm_grp2_ssid(),
    .EventManager_vm_grp3_sid (),
    .EventManager_vm_grp3_ssid(),

    .mem_sd                   (nl2arc0_pd_mem  ),
    .mem_ds                   (1'b0                 ),
    // Debug
    .dbg_cmdval               (arc1_dbg_cmdval),
    .dbg_cmdack               (arc1_dbg_cmdack),
    .dbg_eop                  (1'b1),
    .dbg_address              (arc1_dbg_address),
    .dbg_be                   (4'b1111),
    .dbg_cmd                  (arc1_dbg_cmd),
    .dbg_wdata                (arc1_dbg_wdata),
    .dbg_rspval               (arc1_dbg_rspval),
    .dbg_rspack               (1'b1    ),
    .dbg_reop                 (        ), // intentionally unconnected
    .dbg_rerr                 (        ), // intentionally unconnected
    .dbg_rdata                (arc1_dbg_rdata),
    .debug_reset              (arc1_dbg_reset)
  );

  //
  // Synchronous bridges
  //
  npu_axi_sync_ini
  #(
    .AXIIDW         ( 2                 ),
    .AXIDW          ( 64                ),
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
  u_arc0_cbu_sync_ini
  (
    .axi_slv_clk   ( nl2arc0_clk     ),
    .axi_slv_rst_a ( nl2arc0_rst_a   ), //L2ARC0 reset
    .tgt_pwr_dwn_a ( 1'b0                 ), //L2ARC  group reset
    .test_mode     ( test_mode            ),
    `AXIINST(axi_slv_,int_cbu_axi_),
    `AXISYNCINST(axi_sync_mst_,arc0_axi_cbu_sync_)
   );

  npu_axi_sync_tgt
  #(
    .AXIIDW         ( 2                 ),
    .AXIDW          ( 64                ),
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
  u_arc0_cbu_sync_tgt
  (
    .axi_mst_clk   ( clk                   ),
    .axi_mst_rst_a ( rst_a                 ),
    .ini_pwr_dwn_a ( nl2arc0_pwr_dwn_a),
    .test_mode     ( test_mode             ),
    .clk_req       (                       ),  //Intended
    `AXIINST(axi_mst_,cbu_axi_),
    `AXISYNCINST(axi_sync_slv_,arc0_axi_cbu_sync_)
   );

  //
  // Synchronous bridges
  //
  npu_axi_sync_ini
  #(
    .AXIIDW         ( 2                 ),
    .AXIDW          ( 64                ),
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
  u_arc1_cbu_sync_ini
  (
    .axi_slv_clk   ( nl2arc1_clk     ),
    .axi_slv_rst_a ( nl2arc1_rst_a   ), //L2ARC1 reset
    .tgt_pwr_dwn_a ( rst_a                ), //L2ARC  group reset
    .test_mode     ( test_mode            ),
    `AXIINST(axi_slv_,arc1_int_cbu_axi_),
    `AXISYNCINST(axi_sync_mst_,arc1_axi_cbu_sync_)
   );

  npu_axi_sync_tgt
  #(
    .AXIIDW         ( 2                 ),
    .AXIDW          ( 64                ),
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
  u_arc1_cbu_sync_tgt
  (
    .axi_mst_clk   ( clk                   ),
    .axi_mst_rst_a ( rst_a                 ),
    .ini_pwr_dwn_a ( nl2arc1_pwr_dwn_a),
    .test_mode     ( test_mode             ),
    .clk_req       (                       ),  //Intended
    `AXIINST(axi_mst_,arc1_cbu_axi_),
    `AXISYNCINST(axi_sync_slv_,arc1_axi_cbu_sync_)
   );

  // Assign to Matrix AXI
  `AXIASGN(0,duo_cbu_axi_,cbu_axi_);
  `AXIASGN(1,duo_cbu_axi_,arc1_cbu_axi_);

  npu_axi_config
  #(
    .CFGIDW ( 1        ),
    .NUMAP  ( NUMAP    ),
    .DECBASE_RST_VAL (`L2_CBU_CFG_DECBASE_RST_VAL),
    .DECSIZE_RST_VAL (`L2_CBU_CFG_DECSIZE_RST_VAL),
    .DECMST_RST_VAL  (`L2_CBU_CFG_DECMST_RST_VAL),
    .NUMMST ( 2        )
  )
  u_cbu_cfg_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    .swit_base ('0),
    .swit_ena  ('0),
    `AXIINST(axi_slv_,axi_cbu_cfg_),
    `AXICONFIGINST(cbu_cfg_)
  );

  //
  // AXI matrix from L2 ARC CBU to Master Matrix or NoC
  //
  npu_axi_matrix
  #(
    .NUMSLV  ( 2               ),
    .AXIMIDW ( 3               ),
    .NUMMST  ( 2               ),
    .NUMAP   ( NUMAP           ),
    .AXIDW   ( 64              ),
    .AXISIDW ( 2               ),
    .AXIAWUW ( SLICE_DMA_AWUW  ),
    .AXIWUW  ( SLICE_DMA_WUW   ),
    .AXIBUW  ( SLICE_DMA_BUW   ),
    .AXIARUW ( SLICE_DMA_ARUW  ),
    .AXIRUW  ( SLICE_DMA_RUW   )
  )
  u_cbu_mat_inst
  (
    .clk    ( clk      ),
    .rst_a  ( rst_sync ),
    .ptidx_a( 2'b00    ),
    .decslv ( '1       ),
    `AXIINST(axi_slv_,duo_cbu_axi_),
    `AXIINST(axi_mst_,axi_cbu_int_),
    `AXICONFIGINST(cbu_cfg_)
  );


  //
  // Connect to MST Matrix //
  npu_axi_idtrack
  #(
    .SIZE    ( DMI_OST       ),
    .AXISIDW ( 3             ),
    .AXIMIDW ( L2MIDW        ),
    .AXIDW   ( 64            ),
    .AXIAWUW ( SLICE_DMA_AWUW),
    .AXIWUW  ( SLICE_DMA_WUW ),
    .AXIBUW  ( SLICE_DMA_BUW ),
    .AXIARUW ( SLICE_DMA_ARUW),
    .AXIRUW  ( SLICE_DMA_RUW )
  )
  u_arc_int_idc_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    `AXIINSTM(0,axi_slv_,axi_cbu_int_),
    `AXIINST(axi_mst_,axi_icbu_int_)
  );

  //
  // 64 to VSIZE*64 datawidth converter on CBU
  //
  npu_axi_bridge
  #(
    .AXIIDW   ( L2MIDW                 ),
    .AXISDW   ( 64                     ),
    .AXIMDW   ( VSIZE*64               ),
    .AXISAWUW ( SLICE_DMA_AWUW         ),
    .AXISWUW  ( SLICE_DMA_WUW          ),
    .AXISBUW  ( SLICE_DMA_BUW          ),
    .AXISARUW ( SLICE_DMA_ARUW         ),
    .AXISRUW  ( SLICE_DMA_RUW          ),
    .AXIMAWUW ( SLICE_DMA_AWUW         ),
    .AXIMWUW  ( SLICE_DMA_WUW          ),
    .AXIMBUW  ( SLICE_DMA_BUW          ),
    .AXIMARUW ( SLICE_DMA_ARUW         ),
    .AXIMRUW  ( SLICE_DMA_RUW          )
  )
  u_bridge_inst
  (
     .clk   ( clk   ),
     .rst_a ( rst_sync),
    `AXIINST(axi_slv_,axi_icbu_int_),
    `AXIINSTM(NUMDMI,axi_mst_,axi_in_)
  );

  //
  // ID convert on DMI ports
  //
  for (genvar gd = 0; gd < NUMDMI; gd++)
  begin : id_GEN
    npu_axi_idtrack
    #(
      .SIZE    ( DMI_OST        ),
      .AXISIDW ( `NPU_AXI_TARGET_ID_WIDTH),
      .AXIMIDW ( L2MIDW         ),
      .AXIDW   ( 64*VSIZE       ),
      .AXIAWUW ( SLICE_DMA_AWUW ),
      .AXIWUW  ( SLICE_DMA_WUW  ),
      .AXIBUW  ( SLICE_DMA_BUW  ),
      .AXIARUW ( SLICE_DMA_ARUW ),
      .AXIRUW  ( SLICE_DMA_RUW  )
    )
    u_track_inst
    (
      .clk   ( clk      ),
      .rst_a ( rst_sync ),
      `AXIINSTM(gd,axi_slv_,axi_dmi_),
      `AXIINSTM(gd,axi_mst_,axi_in_)
    );
  end : id_GEN


  //
  // AXI register slices
  //
  for (genvar gs = NUMDMI; gs < NUMDMI+1; gs++)
  begin : slc_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( L2MIDW         ),
      .AXIDW        ( 64*VSIZE       ),
      .AXIAWUW      ( SLICE_DMA_AWUW ),
      .AXIWUW       ( SLICE_DMA_WUW  ),
      .AXIBUW       ( SLICE_DMA_BUW  ),
      .AXIARUW      ( SLICE_DMA_ARUW ),
      .AXIRUW       ( SLICE_DMA_RUW  ),
      .NUMSLC       ( 1              ),
      .AWFIFO_DEPTH ( 1              ),
      .WFIFO_DEPTH  ( 2              ),
      .BFIFO_DEPTH  ( 1              ),
      .ARFIFO_DEPTH ( 1              ),
      .RFIFO_DEPTH  ( 2              )
    )
    u_slc_inst
    (
     .clk   ( clk      ),
     .rst_a ( rst_sync ),
     `AXIINSTM(gs,axi_slv_,axi_in_),
     `AXIINSTM(gs,axi_mst_,iaxi_slc_)
     );
  end : slc_GEN


  `AXIASGNM(axi_slc_,NUMDMI,iaxi_slc_,NUMDMI);
        //        aperture 0 own all address routine to group0
  //
  // AXI configuration
  //
  npu_axi_config
  #(
    .CFGIDW ( 1        ),
    .NUMAP  ( NUMAP    ),
    .DECBASE_RST_VAL (`L2_MST_CFG_DECBASE_RST_VAL),
    .DECSIZE_RST_VAL (`L2_MST_CFG_DECSIZE_RST_VAL),
    .DECMST_RST_VAL  (`L2_MST_CFG_DECMST_RST_VAL),
    .NUMMST ( NUMGRP+1 )
  )
  u_mst_cfg_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    .swit_base ('0),
    .swit_ena  ('0),
    `AXIINST(axi_slv_,axi_mst_cfg_),
    `AXICONFIGINST(mst_cfg_)
  );

  //
  // AXI matrix from DMI and CBU to groups
  //
  npu_axi_matrix
  #(
    .NUMSLV  ( NUMDMI+1        ),
    .NUMMST  ( NUMGRP+1        ),
    .NUMAP   ( NUMAP           ),
    .AXIDW   ( VSIZE*64        ),
    .AXISIDW ( L2MIDW          ),
    .AXIMIDW ( MSTIDW          ),
    .AXIAWUW ( SLICE_DMA_AWUW  ),
    .AXIWUW  ( SLICE_DMA_WUW   ),
    .AXIBUW  ( SLICE_DMA_BUW   ),
    .AXIARUW ( SLICE_DMA_ARUW  ),
    .AXIRUW  ( SLICE_DMA_RUW   )
  )
  u_mst_mat_inst
  (
    .clk    ( clk      ),
    .rst_a  ( rst_sync ),
    .ptidx_a( 2'b00    ),
    .decslv ( '1       ),
    `AXIINST(axi_slv_,axi_slc_),
    `AXIINST(axi_mst_,axi_int_),
    `AXICONFIGINST(mst_cfg_)
  );

  //
  // Output slices to groups
  //
  for (genvar go = 0; go < NUMGRP; go++)
  begin : oslc_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( MSTIDW         ),
      .AXIDW        ( 64*VSIZE       ),
      .AXIAWUW      ( SLICE_DMA_AWUW ),
      .AXIWUW       ( SLICE_DMA_WUW  ),
      .AXIBUW       ( SLICE_DMA_BUW  ),
      .AXIARUW      ( SLICE_DMA_ARUW ),
      .AXIRUW       ( SLICE_DMA_RUW  ),
      .NUMSLC       ( 1              ),
      .AWFIFO_DEPTH ( 1              ),
      .WFIFO_DEPTH  ( 2              ),
      .BFIFO_DEPTH  ( 1              ),
      .ARFIFO_DEPTH ( 1              ),
      .RFIFO_DEPTH  ( 2              )
    )
    u_slc_inst
    (
     .clk   ( clk      ),
     .rst_a ( rst_sync ),
     `AXIINSTM(go,axi_slv_,axi_int_),
     `AXIINSTM(go,axi_mst_,axi_mst_)
    );
  end : oslc_GEN

  //
  // Output slices to DM MUX //
  npu_axi_idtrack
  #(
    .SIZE    ( DMI_OST       ),
    .AXISIDW ( MSTIDW        ),
    .AXIMIDW ( CCMIDW        ),
    .AXIDW   ( VSIZE*64      ),
    .AXIAWUW ( SLICE_DMA_AWUW),
    .AXIWUW  ( SLICE_DMA_WUW ),
    .AXIBUW  ( SLICE_DMA_BUW ),
    .AXIARUW ( SLICE_DMA_ARUW),
    .AXIRUW  ( SLICE_DMA_RUW )
  )
  u_dccm_idc_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    `AXIINSTM(NUMGRP,axi_slv_,axi_int_),
    `AXIINST(axi_mst_,axi_dccm_wid_)
  );

  npu_axi_bridge
  #(
    .AXIIDW   ( CCMIDW          ),
    .AXISDW   ( VSIZE*64        ),
    .AXIMDW   ( 64              ),
    .AXISAWUW ( SLICE_DMA_AWUW  ),
    .AXISWUW  ( SLICE_DMA_WUW   ),
    .AXISBUW  ( SLICE_DMA_BUW   ),
    .AXISARUW ( SLICE_DMA_ARUW  ),
    .AXISRUW  ( SLICE_DMA_RUW   ),
    .AXIMAWUW ( SLICE_MMIO_AWUW ),
    .AXIMWUW  ( SLICE_MMIO_WUW  ),
    .AXIMBUW  ( SLICE_MMIO_BUW  ),
    .AXIMARUW ( SLICE_MMIO_ARUW ),
    .AXIMRUW  ( SLICE_MMIO_RUW  )
  )
  u_ccm_down_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    `AXIINST(axi_slv_,axi_dccm_wid_),
    `AXIINST(axi_mst_,axi_dccm_nar_)
  );

  localparam int CBUIDW = 3;
  localparam int NOCIDW = 5;

  `AXIASGMNID(1,axi_cbu_int_,axi_l2arc_noc_int_);
  assign axi_l2arc_noc_int_arid = {{(NOCIDW - CBUIDW){1'b0}},axi_cbu_int_arid[1]};
  assign axi_l2arc_noc_int_awid = {{(NOCIDW - CBUIDW){1'b0}},axi_cbu_int_awid[1]};
  assign axi_cbu_int_rid[1] = axi_l2arc_noc_int_rid[CBUIDW-1:0];
  assign axi_cbu_int_bid[1] = axi_l2arc_noc_int_bid[CBUIDW-1:0];


  npu_axi_slice
  #(
    .AXIIDW       ( 5              ),
    .AXIDW        ( 64             ),
    .AXIAWUW      ( SLICE_DMA_AWUW ),
    .AXIWUW       ( SLICE_DMA_WUW  ),
    .AXIBUW       ( SLICE_DMA_BUW  ),
    .AXIARUW      ( SLICE_DMA_ARUW ),
    .AXIRUW       ( SLICE_DMA_RUW  ),
    .NUMSLC       ( 1              ),
    .AWFIFO_DEPTH ( 1              ),
    .WFIFO_DEPTH  ( 2              ),
    .BFIFO_DEPTH  ( 1              ),
    .ARFIFO_DEPTH ( 1              ),
    .RFIFO_DEPTH  ( 2              )
  )
  u_l2arc_noc_slc_inst
  (
   .clk   ( clk      ),
   .rst_a ( rst_sync ),
   `AXIINST(axi_slv_,axi_l2arc_noc_int_),
   `AXIINST(axi_mst_,axi_l2arc_noc_)
  );

  //
  // Input slices on CCM interfaces
  //
  for (genvar gc = 0; gc < NUMGRP; gc++)
  begin : cslc_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( CCMIDW          ),
      .AXIDW        ( 64              ),
      .AXIAWUW      ( SLICE_MMIO_AWUW ),
      .AXIWUW       ( SLICE_MMIO_WUW  ),
      .AXIBUW       ( SLICE_MMIO_BUW  ),
      .AXIARUW      ( SLICE_MMIO_ARUW ),
      .AXIRUW       ( SLICE_MMIO_RUW  ),
      .NUMSLC       ( 1               ),
      .AWFIFO_DEPTH ( 1               ),
      .WFIFO_DEPTH  ( 2               ),
      .BFIFO_DEPTH  ( 1               ),
      .ARFIFO_DEPTH ( 1               ),
      .RFIFO_DEPTH  ( 2               )
    )
    u_slc_inst
    (
     .clk   ( clk      ),
     .rst_a ( rst_sync ),
     `AXIINSTM(gc,axi_slv_,axi_ccm_),
     `AXIINSTM(gc,axi_mst_,axi_cslc_)
     );
  end : cslc_GEN


  //
  // Input From DMI to DCCM Interface
  //
  `AXIASGN(NUMGRP,axi_cslc_,axi_dccm_nar_);

  `AXICONFIGWIRES(2,2,int_ccm_amap_);
  // AP0: 0xe6040000 -> 0xe607ffff Map to ARC1
  // AP0: 0xe6000000 -> 0xe603ffff Map to ARC0
  always_comb
  begin : int_ccm_amap_PROC
    int_ccm_amap_decbase = '0;
    int_ccm_amap_decsize = '0;
    int_ccm_amap_decmst  = '0;
    // Aperture0
    int_ccm_amap_decbase[0]   = 28'h00_e604_0;
    int_ccm_amap_decsize[0]   = 28'h00_fffc_0;
    int_ccm_amap_decmst[0]    = 'd2;
    // Aperture1
    int_ccm_amap_decbase[1]   = '0;
    int_ccm_amap_decsize[1]   = '0;
    int_ccm_amap_decmst[1]    = 'd1;
  end : int_ccm_amap_PROC
  //
  // AXI mux from CCM to SCCM
  //
  npu_axi_matrix
  #(
    .NUMSLV  ( NUMGRP+1         ),
    .NUMMST  ( 2               ),
    .NUMAP   ( 2                ),
    .AXIDW   ( 64               ),
    .AXISIDW ( CCMIDW           ),
    .AXIMIDW ( DMIDW            ),
    .AXIAWUW ( SLICE_MMIO_AWUW  ),
    .AXIWUW  ( SLICE_MMIO_WUW   ),
    .AXIBUW  ( SLICE_MMIO_BUW   ),
    .AXIARUW ( SLICE_MMIO_ARUW  ),
    .AXIRUW  ( SLICE_MMIO_RUW   )
  )
  u_ccm_mux_inst
  (
    .clk    ( clk      ),
    .rst_a  ( rst_sync ),
    .ptidx_a( 2'b00    ),
    .decslv ( '1       ),
    `AXIINST(axi_slv_,axi_cslc_),
    `AXIINST(axi_mst_,axi_dm_),
    `AXICONFIGINST(int_ccm_amap_)
  );

  //
  // Synchronous bridges
  //
  npu_axi_sync_tgt
  #(
    .AXIIDW         ( 16                ),
    .AXIDW          ( 64                ),
    .AXIAWUW        ( SLICE_MMIO_AWUW   ),
    .AXIWUW         ( SLICE_MMIO_WUW    ),
    .AXIBUW         ( SLICE_MMIO_BUW    ),
    .AXIARUW        ( SLICE_MMIO_ARUW   ),
    .AXIRUW         ( SLICE_MMIO_RUW    ),
    .AWFIFO_DEPTHL2 ( 1                 ),
    .WFIFO_DEPTHL2  ( 3                 ),
    .BFIFO_DEPTHL2  ( 1                 ),
    .ARFIFO_DEPTHL2 ( 1                 ),
    .RFIFO_DEPTHL2  ( 3                 )
  )
  u_arc0_sccm_sync_tgt
  (
    .axi_mst_clk   ( nl2arc0_clk     ),
    .axi_mst_rst_a ( nl2arc0_rst_a   ), //L2ARC0 reset
    .ini_pwr_dwn_a ( rst_a                ), //L2ARC  group reset
    .test_mode     ( test_mode            ),
    .clk_req       ( arc0_axi_sccm_tgt_clk_en),
    `AXIINST(axi_mst_,sccm_axi_),
    `AXISYNCINST(axi_sync_slv_,arc0_axi_sccm_sync_)
   );

  npu_axi_sync_ini
  #(
    .AXIIDW         ( 16                ),
    .AXIDW          ( 64                ),
    .AXIAWUW        ( SLICE_MMIO_AWUW   ),
    .AXIWUW         ( SLICE_MMIO_WUW    ),
    .AXIBUW         ( SLICE_MMIO_BUW    ),
    .AXIARUW        ( SLICE_MMIO_ARUW   ),
    .AXIRUW         ( SLICE_MMIO_RUW    ),
    .AWFIFO_DEPTHL2 ( 1                 ),
    .WFIFO_DEPTHL2  ( 3                 ),
    .BFIFO_DEPTHL2  ( 1                 ),
    .ARFIFO_DEPTHL2 ( 1                 ),
    .RFIFO_DEPTHL2  ( 3                 )
  )
  u_arc0_sccm_sync_ini
  (
    .axi_slv_clk   ( clk                   ),
    .axi_slv_rst_a ( rst_a                 ),
    .tgt_pwr_dwn_a ( nl2arc0_pwr_dwn_a),
    .test_mode     ( test_mode             ),
    `AXIINSTM(0,axi_slv_,axi_dm_idw_),
    `AXISYNCINST(axi_sync_mst_,arc0_axi_sccm_sync_)
   );

  //
  // Synchronous bridges
  //
  npu_axi_sync_tgt
  #(
    .AXIIDW         ( 16               ),
    .AXIDW          ( 64                ),
    .AXIAWUW        ( SLICE_MMIO_AWUW   ),
    .AXIWUW         ( SLICE_MMIO_WUW    ),
    .AXIBUW         ( SLICE_MMIO_BUW    ),
    .AXIARUW        ( SLICE_MMIO_ARUW   ),
    .AXIRUW         ( SLICE_MMIO_RUW    ),
    .AWFIFO_DEPTHL2 ( 1                 ),
    .WFIFO_DEPTHL2  ( 3                 ),
    .BFIFO_DEPTHL2  ( 1                 ),
    .ARFIFO_DEPTHL2 ( 1                 ),
    .RFIFO_DEPTHL2  ( 3                 )
  )
  u_arc1_sccm_sync_tgt
  (
    .axi_mst_clk   ( nl2arc1_clk     ),
    .axi_mst_rst_a ( nl2arc1_rst_a   ), //L2ARC1 reset
    .ini_pwr_dwn_a ( 1'b0                 ), //L2ARC  group reset
    .test_mode     ( test_mode            ),
    .clk_req       ( arc1_axi_sccm_tgt_clk_en),
    `AXIINST(axi_mst_,arc1_sccm_axi_),
    `AXISYNCINST(axi_sync_slv_,arc1_axi_sccm_sync_)
   );

  npu_axi_sync_ini
  #(
    .AXIIDW         ( 16                ),
    .AXIDW          ( 64                ),
    .AXIAWUW        ( SLICE_MMIO_AWUW   ),
    .AXIWUW         ( SLICE_MMIO_WUW    ),
    .AXIBUW         ( SLICE_MMIO_BUW    ),
    .AXIARUW        ( SLICE_MMIO_ARUW   ),
    .AXIRUW         ( SLICE_MMIO_RUW    ),
    .AWFIFO_DEPTHL2 ( 1                 ),
    .WFIFO_DEPTHL2  ( 3                 ),
    .BFIFO_DEPTHL2  ( 1                 ),
    .ARFIFO_DEPTHL2 ( 1                 ),
    .RFIFO_DEPTHL2  ( 3                 )
  )
  u_arc1_sccm_sync_ini
  (
    .axi_slv_clk   ( clk                   ),
    .axi_slv_rst_a ( rst_a                 ),
    .tgt_pwr_dwn_a ( nl2arc1_pwr_dwn_a),
    .test_mode     ( test_mode             ),
    `AXIINSTM(1,axi_slv_,axi_dm_idw_),
    `AXISYNCINST(axi_sync_mst_,arc1_axi_sccm_sync_)
   );

  // assign to sccm interface to widen ID bits
  `AXIASGNID(axi_dm_,axi_dm_idw_);
  assign axi_dm_idw_arid[0]   =   {{(16-DMIDW){1'b0}},axi_dm_arid[0]};
  assign axi_dm_idw_awid[0]   =   {{(16-DMIDW){1'b0}},axi_dm_awid[0]};
  assign axi_dm_rid[0]        =   axi_dm_idw_rid[0][0+:DMIDW];
  assign axi_dm_bid[0]        =   axi_dm_idw_bid[0][0+:DMIDW];
  assign axi_dm_idw_arid[1]   =   {{(16-DMIDW){1'b0}},axi_dm_arid[1]};
  assign axi_dm_idw_awid[1]   =   {{(16-DMIDW){1'b0}},axi_dm_awid[1]};
  assign axi_dm_rid[1]        =   axi_dm_idw_rid[1][0+:DMIDW];
  assign axi_dm_bid[1]        =   axi_dm_idw_bid[1][0+:DMIDW];


  //
  // Demultiplex configuration interface
  //
  // ID converter
  npu_axi_idtrack
  #(
    .SIZE    ( DMI_OST ),
    .AXISIDW ( `NPU_AXI_TARGET_ID_WIDTH),
    .AXIMIDW ( 1       ),
    .AXIDW   ( 32      ),
    .AXIAWUW ( 1       ),
    .AXIWUW  ( 1       ),
    .AXIBUW  ( 1       ),
    .AXIARUW ( 1       ),
    .AXIRUW  ( 1       )
  )
  u_cfg_idc_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    `AXIINST(axi_slv_,axi_cfg_in_),
    `AXIINST(axi_mst_,axi_cfg_id_)
  );

  npu_axi_slice
  #(
    .AXIIDW       ( 1  ),
    .AXIDW        ( 32 ),
    .AXIAWUW      ( 1  ),
    .AXIWUW       ( 1  ),
    .AXIBUW       ( 1  ),
    .AXIARUW      ( 1  ),
    .AXIRUW       ( 1  ),
    .NUMSLC       ( 1  ),
    .AWFIFO_DEPTH ( 1  ),
    .WFIFO_DEPTH  ( 2  ),
    .BFIFO_DEPTH  ( 1  ),
    .ARFIFO_DEPTH ( 1  ),
    .RFIFO_DEPTH  ( 2  )
  )
  u_cfg_slc_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    `AXIINST(axi_slv_,axi_cfg_id_),
    `AXIINST(axi_mst_,axi_cfg_id_slc_)
  );


  // decode address map for configuration interface
  // Aperture0: 0x0000_0000 to 0x0000_FFFF --> Group0 Config
  // Aperture1: 0x0001_0000 to 0x0001_FFFF --> Group1 Config
  // Aperture2: 0x0002_0000 to 0x0002_FFFF --> Group2 Config
  // Aperture3: 0x0003_0000 to 0x0003_FFFF --> Group3 Config
  // Aperture4: 0x0004_0000 to 0x0004_0FFF --> DMI Matrix in npu_axi_config
  always_comb
  begin : amap_PROC
    // fixed group address map max 4*64KB
    cfg_amap_decbase = '0;
    cfg_amap_decsize = '0;
    cfg_amap_decmst  = '0;
    for (int g = 0; g < NUMGRP; g++)
    begin
      cfg_amap_decbase[g]   = unsigned'(g*32);
      cfg_amap_decsize[g]   = 'he0;
      cfg_amap_decmst[g][g] = 1'b1;
    end
    // local configuration interface 4KB
    cfg_amap_decbase[NUMGRP]        = 'h80;
    cfg_amap_decsize[NUMGRP]        = 'hff;
    cfg_amap_decmst[NUMGRP][NUMGRP] = 1'b1;
    // CBU Matrix config interface 4KB
    cfg_amap_decbase[NUMGRP+1]          = 'h81;
    cfg_amap_decsize[NUMGRP+1]          = 'hff;
    cfg_amap_decmst[NUMGRP+1][NUMGRP+1] = 1'b1;
    // DMI remap bridge interface 4KB
    cfg_amap_decbase[NUMGRP+2]          = 'h82;
    cfg_amap_decsize[NUMGRP+2]          = 'hff;
    cfg_amap_decmst[NUMGRP+2][NUMGRP+2] = 1'b1;
  end : amap_PROC

  npu_axi_matrix
  #(
    .NUMSLV  ( 1          ),
    .NUMMST  ( NUM_MEMMAP ),
    .NUMAP   ( NUM_MEMMAP ),
    .AXIDW   ( 32         ),
    .AXISIDW ( 1          ),
    .AXIMIDW ( 1          ),
    .AXIAWUW ( 1          ),
    .AXIWUW  ( 1          ),
    .AXIBUW  ( 1          ),
    .AXIARUW ( 1          ),
    .AXIRUW  ( 1          )
  )
  u_cfg_demux_inst
  (
    .clk    ( clk      ),
    .rst_a  ( rst_sync ),
    .ptidx_a( 2'b00    ),
    .decslv ( '1       ),
    `AXIINST(axi_slv_,axi_cfg_id_slc_),
    `AXIINST(axi_mst_,axi_cfg_split_mid_),
    `AXICONFIGINST(cfg_amap_)
  );


  // DMI Input Remap
  npu_axi_config
  #(
    .CFGIDW ( 1        ),
    .NUMAP  ( NUMAP    ),
    .DECBASE_RST_VAL (`L2_REMP_CFG_DECBASE_RST_VAL),
    .DECSIZE_RST_VAL (`L2_REMP_CFG_DECSIZE_RST_VAL),
    .DECMST_RST_VAL  (`L2_REMP_CFG_DECMST_RST_VAL),
    .NUMMST ( 1        )
  )
  u_remap_cfg_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    .swit_base (npu_csm_base_r),
    .swit_ena  ({15'b0,{1{npu_csm_set}}}),
    `AXIINST(axi_slv_,axi_remap_cfg_),
    `AXICONFIGINST(remap_cfg_)
  );

  npu_2cyc_checker
  #(
    .WIDTH ((NUMAP*(NPU_AXI_ADDR_W-12)*2+NUMAP*1))
  )
  u_remap_cfg_mc2_inst
  (
   .clk      ( clk      ),
   .rst_a    ( rst_sync ),
   .valid    ( 1'b1     ),
   .data_in  ( {remap_cfg_decbase,
                remap_cfg_decsize,
                remap_cfg_decmst} ),
   .data_out ( {remap_cfg_mc2_decbase,
                remap_cfg_mc2_decsize,
                remap_cfg_mc2_decmst} )
   );

  for (genvar gc = 0; gc < NUMDMI; gc++)
  begin : dmi_remap_GEN
    npu_axi_remap
    #(
      .NUMMST  ( 1              ),
      .NUMAP   ( NUMAP          ),
      .AXIMDW  ( VSIZE*64       ),
      .AXISDW  ( VSIZE*64       ),
      .AXIIDW  ( L2MIDW         ),
      .AXIAWUW ( SLICE_DMA_AWUW ),
      .AXIWUW  ( SLICE_DMA_WUW  ),
      .AXIBUW  ( SLICE_DMA_BUW  ),
      .AXIARUW ( SLICE_DMA_ARUW ),
      .AXIRUW  ( SLICE_DMA_RUW  )
    )
    u_axi_dmi_remap_inst
    (
      .clk    ( clk      ),
      .rst_a  ( rst_sync ),
      `AXIINSTM(gc,axi_slv_,axi_in_),
      `AXIINSTM(gc,axi_mst_,iaxi_slc_),
      `AXICONFIGINST(remap_cfg_mc2_)
    );

    npu_axi_slice
    #(
      .AXIIDW       ( L2MIDW         ),
      .AXIDW        ( 64*VSIZE       ),
      .AXIAWUW      ( SLICE_DMA_AWUW ),
      .AXIWUW       ( SLICE_DMA_WUW  ),
      .AXIBUW       ( SLICE_DMA_BUW  ),
      .AXIARUW      ( SLICE_DMA_ARUW ),
      .AXIRUW       ( SLICE_DMA_RUW  ),
      .NUMSLC       ( 1              ),
      .AWFIFO_DEPTH ( 1              ),
      .WFIFO_DEPTH  ( 2              ),
      .BFIFO_DEPTH  ( 1              ),
      .ARFIFO_DEPTH ( 1              ),
      .RFIFO_DEPTH  ( 2              )
    )
    u_remap_slc_inst
    (
     .clk   ( clk      ),
     .rst_a ( rst_sync ),
     `AXIINSTM(gc,axi_slv_,iaxi_slc_),
     `AXIINSTM(gc,axi_mst_,axi_slc_)
     );
  end : dmi_remap_GEN

  `AXIASG(axi_cfg_split_mid_,axi_cfg_split_);

  // output slices
  for (genvar gg = 0; gg < NUMGRP; gg++)
  begin : axi_asg_GEN
    npu_axi_slice
    #(
      .AXIIDW       ( 1  ),
      .AXIDW        ( 32 ),
      .AXIAWUW      ( 1  ),
      .AXIWUW       ( 1  ),
      .AXIBUW       ( 1  ),
      .AXIARUW      ( 1  ),
      .AXIRUW       ( 1  ),
      .NUMSLC       ( 1  ),
      .AWFIFO_DEPTH ( 1  ),
      .WFIFO_DEPTH  ( 2  ),
      .BFIFO_DEPTH  ( 1  ),
      .ARFIFO_DEPTH ( 1  ),
      .RFIFO_DEPTH  ( 2  )
    )
    u_slc_inst
    (
      .clk   ( clk      ),
      .rst_a ( rst_sync ),
      `AXIINSTM(gg,axi_slv_,axi_cfg_split_),
      `AXIINSTM(gg,axi_mst_,axi_cfg_grp_)
    );
  end : axi_asg_GEN
  npu_axi_slice
  #(
    .AXIIDW       ( 1  ),
    .AXIDW        ( 32 ),
    .AXIAWUW      ( 1  ),
    .AXIWUW       ( 1  ),
    .AXIBUW       ( 1  ),
    .AXIARUW      ( 1  ),
    .AXIRUW       ( 1  ),
    .NUMSLC       ( 1  ),
    .AWFIFO_DEPTH ( 1  ),
    .WFIFO_DEPTH  ( 2  ),
    .BFIFO_DEPTH  ( 1  ),
    .ARFIFO_DEPTH ( 1  ),
    .RFIFO_DEPTH  ( 2  )
  )
  u_cslc_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    `AXIINSTM(NUMGRP,axi_slv_,axi_cfg_split_),
    `AXIINST(axi_mst_,axi_mst_cfg_)
  );

  npu_axi_slice
  #(
    .AXIIDW       ( 1  ),
    .AXIDW        ( 32 ),
    .AXIAWUW      ( 1  ),
    .AXIWUW       ( 1  ),
    .AXIBUW       ( 1  ),
    .AXIARUW      ( 1  ),
    .AXIRUW       ( 1  ),
    .NUMSLC       ( 1  ),
    .AWFIFO_DEPTH ( 1  ),
    .WFIFO_DEPTH  ( 2  ),
    .BFIFO_DEPTH  ( 1  ),
    .ARFIFO_DEPTH ( 1  ),
    .RFIFO_DEPTH  ( 2  )
  )
  u_cbu_ls_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    `AXIINSTM(NUMGRP+1,axi_slv_,axi_cfg_split_),
    `AXIINST(axi_mst_,axi_cbu_cfg_)
  );

  npu_axi_slice
  #(
    .AXIIDW       ( 1  ),
    .AXIDW        ( 32 ),
    .AXIAWUW      ( 1  ),
    .AXIWUW       ( 1  ),
    .AXIBUW       ( 1  ),
    .AXIARUW      ( 1  ),
    .AXIRUW       ( 1  ),
    .NUMSLC       ( 1  ),
    .AWFIFO_DEPTH ( 1  ),
    .WFIFO_DEPTH  ( 2  ),
    .BFIFO_DEPTH  ( 1  ),
    .ARFIFO_DEPTH ( 1  ),
    .RFIFO_DEPTH  ( 2  )
  )
  u_remap_slc_inst
  (
    .clk   ( clk      ),
    .rst_a ( rst_sync ),
    `AXIINSTM(NUMGRP+2,axi_slv_,axi_cfg_split_),
    `AXIINST(axi_mst_,axi_remap_cfg_)
  );


  assign    arc1_int_cbu_axi_aruser      = '0;
  assign    arc1_int_cbu_axi_ar.region   = '0;
  assign    arc1_int_cbu_axi_awuser      = '0;
  assign    arc1_int_cbu_axi_aw.region   = '0;
  assign    arc1_int_cbu_axi_wuser       = '0;
  assign    arc1_sccm_axi_ruser      = '0;
  assign    arc1_sccm_axi_buser      = '0;

  assign    int_cbu_axi_aruser      = '0;
  assign    int_cbu_axi_ar.region   = '0;
  assign    int_cbu_axi_awuser      = '0;
  assign    int_cbu_axi_aw.region   = '0;
  assign    int_cbu_axi_wuser       = '0;
  assign    sccm_axi_ruser      = '0;
  assign    sccm_axi_buser      = '0;


  //
  // Asynchronous bridges on NoC master ports, l2arc2noc
  //
  npu_axi_async_ini
  #(
    .AXIIDW         ( 5                 ),
    .AXIDW          ( 64                ),
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
  u_axi_l2arc_noc_ini
  (
    .axi_slv_clk   ( clk            ),
    .axi_slv_rst_a ( rst_a          ),
    .tgt_pwr_dwn_a ( 1'b0           ), // always-on
    .test_mode     ( test_mode      ),
    `AXIINST(axi_slv_,axi_l2arc_noc_),
    `AXIASYNCMSUB(axi_async_mst_,l2arc_noc_axi_gals_)
   );

  //
  // Asynchronous bridges on DMI slave ports, noc2core
  //
  npu_axi_async_tgt
  #(
    .AXIIDW         ( `NPU_AXI_TARGET_ID_WIDTH ),
    .AXIDW          ( 64*VSIZE                 ),
    .AXIAWUW        ( SLICE_DMA_AWUW           ),
    .AXIWUW         ( SLICE_DMA_WUW            ),
    .AXIBUW         ( SLICE_DMA_BUW            ),
    .AXIARUW        ( SLICE_DMA_ARUW           ),
    .AXIRUW         ( SLICE_DMA_RUW            ),
    .AWFIFO_DEPTHL2 ( 1                        ),
    .WFIFO_DEPTHL2  ( 3                        ),
    .BFIFO_DEPTHL2  ( 1                        ),
    .ARFIFO_DEPTHL2 ( 1                        ),
    .RFIFO_DEPTHL2  ( 3                        )
  )
  u_axi_dmi0_tgt
  (
    .axi_mst_clk   ( clk            ),
    .axi_mst_rst_a ( rst_a          ),
    .ini_pwr_dwn_a ( 1'b0           ), // always-on
    .test_mode     ( test_mode      ),
    .clk_req_a     (                ), // intentionally left open
    `AXIINSTM(0,axi_mst_,axi_dmi_),
    `AXIASYNCSSUB(axi_async_slv_,dmi0_axi_gals_)
  );

  //
  // Asynchronous bridge on configuration slave ports
  //
  npu_axi_async_tgt
  #(
    .AXIIDW         ( `NPU_AXI_TARGET_ID_WIDTH  ),
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
  u_axi_cfg_tgt
  (
    .axi_mst_clk   ( clk            ),
    .axi_mst_rst_a ( rst_a          ),
    .ini_pwr_dwn_a ( 1'b0           ), // always-on
    .test_mode     ( test_mode      ),
    .clk_req_a     (                ), // intentionally left open
    `AXIINST(axi_mst_,axi_cfg_in_),
    `AXIASYNCSSUB(axi_async_slv_,cfg_axi_gals_)
  );

  //
  // Synchronous bridges
  //
  npu_axi_sync_tgt
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
  u_axi_ccm_tgt0
  (
    .axi_mst_clk   ( clk            ),
    .axi_mst_rst_a ( rst_a          ),
    .ini_pwr_dwn_a ( grp0_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    .clk_req       (                ),
    `AXIINSTM(0,axi_mst_,axi_ccm_),
    `AXISYNCINST(axi_sync_slv_,axi_ccm0_sync_)
   );

  npu_axi_sync_ini
  #(
    .AXIIDW         ( MSTIDW            ),
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
  u_axi_mst_ini0
  (
    .axi_slv_clk   ( clk            ),
    .axi_slv_rst_a ( rst_a          ),
    .tgt_pwr_dwn_a ( grp0_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    `AXIINSTM(0,axi_slv_,axi_mst_),
    `AXISYNCINST(axi_sync_mst_,axi_mst0_sync_)
   );

  npu_axi_sync_ini
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
  u_axi_cfg_sync_ini0
  (
    .axi_slv_clk   ( clk            ),
    .axi_slv_rst_a ( rst_a          ),
    .tgt_pwr_dwn_a ( grp0_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    `AXIINSTM(0,axi_slv_,axi_cfg_grp_),
    `AXISYNCINST(axi_sync_mst_,axi_cfg_grp0_sync_)
  );

  npu_axi_sync_tgt
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
  u_axi_ccm_tgt1
  (
    .axi_mst_clk   ( clk            ),
    .axi_mst_rst_a ( rst_a          ),
    .ini_pwr_dwn_a ( grp1_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    .clk_req       (                ),
    `AXIINSTM(1,axi_mst_,axi_ccm_),
    `AXISYNCINST(axi_sync_slv_,axi_ccm1_sync_)
   );

  npu_axi_sync_ini
  #(
    .AXIIDW         ( MSTIDW            ),
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
  u_axi_mst_ini1
  (
    .axi_slv_clk   ( clk            ),
    .axi_slv_rst_a ( rst_a          ),
    .tgt_pwr_dwn_a ( grp1_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    `AXIINSTM(1,axi_slv_,axi_mst_),
    `AXISYNCINST(axi_sync_mst_,axi_mst1_sync_)
   );

  npu_axi_sync_ini
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
  u_axi_cfg_sync_ini1
  (
    .axi_slv_clk   ( clk            ),
    .axi_slv_rst_a ( rst_a          ),
    .tgt_pwr_dwn_a ( grp1_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    `AXIINSTM(1,axi_slv_,axi_cfg_grp_),
    `AXISYNCINST(axi_sync_mst_,axi_cfg_grp1_sync_)
  );

  npu_axi_sync_tgt
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
  u_axi_ccm_tgt2
  (
    .axi_mst_clk   ( clk            ),
    .axi_mst_rst_a ( rst_a          ),
    .ini_pwr_dwn_a ( grp2_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    .clk_req       (                ),
    `AXIINSTM(2,axi_mst_,axi_ccm_),
    `AXISYNCINST(axi_sync_slv_,axi_ccm2_sync_)
   );

  npu_axi_sync_ini
  #(
    .AXIIDW         ( MSTIDW            ),
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
  u_axi_mst_ini2
  (
    .axi_slv_clk   ( clk            ),
    .axi_slv_rst_a ( rst_a          ),
    .tgt_pwr_dwn_a ( grp2_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    `AXIINSTM(2,axi_slv_,axi_mst_),
    `AXISYNCINST(axi_sync_mst_,axi_mst2_sync_)
   );

  npu_axi_sync_ini
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
  u_axi_cfg_sync_ini2
  (
    .axi_slv_clk   ( clk            ),
    .axi_slv_rst_a ( rst_a          ),
    .tgt_pwr_dwn_a ( grp2_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    `AXIINSTM(2,axi_slv_,axi_cfg_grp_),
    `AXISYNCINST(axi_sync_mst_,axi_cfg_grp2_sync_)
  );

  npu_axi_sync_tgt
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
  u_axi_ccm_tgt3
  (
    .axi_mst_clk   ( clk            ),
    .axi_mst_rst_a ( rst_a          ),
    .ini_pwr_dwn_a ( grp3_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    .clk_req       (                ),
    `AXIINSTM(3,axi_mst_,axi_ccm_),
    `AXISYNCINST(axi_sync_slv_,axi_ccm3_sync_)
   );

  npu_axi_sync_ini
  #(
    .AXIIDW         ( MSTIDW            ),
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
  u_axi_mst_ini3
  (
    .axi_slv_clk   ( clk            ),
    .axi_slv_rst_a ( rst_a          ),
    .tgt_pwr_dwn_a ( grp3_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    `AXIINSTM(3,axi_slv_,axi_mst_),
    `AXISYNCINST(axi_sync_mst_,axi_mst3_sync_)
   );

  npu_axi_sync_ini
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
  u_axi_cfg_sync_ini3
  (
    .axi_slv_clk   ( clk            ),
    .axi_slv_rst_a ( rst_a          ),
    .tgt_pwr_dwn_a ( grp3_pwr_dwn_a ),
    .test_mode     ( test_mode      ),
    `AXIINSTM(3,axi_slv_,axi_cfg_grp_),
    `AXISYNCINST(axi_sync_mst_,axi_cfg_grp3_sync_)
  );


  // ARC_Trace
  npuarc_rtt
  u_rtt
  (
     .rtt_clk               (clk                 )
   , .atclken               (at_clk_en           )
   , .atresetn              (at_rst_an           )
   , .atb_cstimestamp       (atb_cstimestamp     )
   , .rtt_write_a           (rtt_write_a         )
   , .rtt_read_a            (rtt_read_a          )
   , .rtt_addr_r            (rtt_addr_r          )
   , .rtt_dwr_r             (rtt_dwr_r           )
   , .rtt_ss_halt           (rtt_ss_halt         )
   , .rtt_hw_bp             (rtt_hw_bp           )
   , .rtt_hw_exc            (rtt_hw_exc          )
   , .rtt_dbg_halt          (rtt_dbg_halt        )
   , .rtt_rst_applied       (rtt_rst_applied     )
   , .rtt_uop_is_leave      (rtt_uop_is_leave    )
   , .rtt_in_deslot         (rtt_in_deslot       )
   , .rtt_in_eslot          (rtt_in_eslot        )
   , .rtt_inst_commit       (rtt_inst_commit     )
   , .rtt_inst_addr         (rtt_inst_addr       )
   , .rtt_cond_valid        (rtt_cond_valid      )
   , .rtt_cond_pass         (rtt_cond_pass       )
   , .rtt_branch            (rtt_branch          )
   , .rtt_branch_indir      (rtt_branch_indir    )
   , .rtt_branch_taddr      (rtt_branch_taddr    )
   , .rtt_dslot             (rtt_dslot           )
   , .rtt_exception         (rtt_exception       )
   , .rtt_exception_rtn     (rtt_exception_rtn   )
   , .rtt_interrupt         (rtt_interrupt       )
   , .rtt_sleep_mode        (rtt_sleep_mode      )
   , .rtt_zd_loop           (rtt_zd_loop         )
   , .rtt_wp_val            (rtt_wp_val          )
   , .rtt_wp_hit            (rtt_wp_hit          )
   , .rtt_sw_bp             (rtt_sw_bp           )
   , .sys_halt_r            (sys_halt_r          )
   , .rtt_process_id        (rtt_process_id      )
   , .rtt_pid_wr_en         (rtt_pid_wr_en       )
   , .rtt_swe_data          (rtt_swe_data        )
   , .rtt_swe_val           (rtt_swe_val         )
   , .atready               (atready             )
   , .afvalid               (afvalid             )
   , .syncreq               (syncreq             )
   , .cti_trace_start       (cti_trace_start     )
   , .cti_trace_stop        (cti_trace_stop      )
   , .cti_rtt_filters       (cti_rtt_filters     )
   , .swe_atready           (swe_atready         )
   , .swe_afvalid           (swe_afvalid         )
   , .swe_syncreq           (swe_syncreq         )
   , .pclkdbg_en            (1'b1                )
   , .presetdbgn            (arct_rst_an         )
   , .arct0_dbgen           (arct_dbgen          )
   , .arct0_niden           (arct_niden          )
   , .arct0_paddrdbg        ({16'h0,arct_paddr}  )
   , .arct0_pseldbg         (arct_psel           )
   , .arct0_penabledbg      (arct_penable        )
   , .arct0_pwritedbg       (arct_pwrite         )
   , .arct0_pwdatadbg       (arct_pwdata         )
   , .sl0_alt_rtt_swe_data     (grp0_rtt_swe_data )
   , .sl0_alt_rtt_swe_val      (grp0_rtt_swe_val_pulse  )
   , .sl0_alt_rtt_swe_ext      (grp0_rtt_swe_ext  )
   , .sl0_alt_rtt_swe_prdcr_en (grp0_rtt_swe_prdcr_en  )
   , .sl1_alt_rtt_swe_data     (grp1_rtt_swe_data )
   , .sl1_alt_rtt_swe_val      (grp1_rtt_swe_val_pulse  )
   , .sl1_alt_rtt_swe_ext      (grp1_rtt_swe_ext  )
   , .sl1_alt_rtt_swe_prdcr_en (grp1_rtt_swe_prdcr_en  )
   , .sl2_alt_rtt_swe_data     (grp2_rtt_swe_data )
   , .sl2_alt_rtt_swe_val      (grp2_rtt_swe_val_pulse  )
   , .sl2_alt_rtt_swe_ext      (grp2_rtt_swe_ext  )
   , .sl2_alt_rtt_swe_prdcr_en (grp2_rtt_swe_prdcr_en  )
   , .sl3_alt_rtt_swe_data     (grp3_rtt_swe_data )
   , .sl3_alt_rtt_swe_val      (grp3_rtt_swe_val_pulse  )
   , .sl3_alt_rtt_swe_ext      (grp3_rtt_swe_ext  )
   , .sl3_alt_rtt_swe_prdcr_en (grp3_rtt_swe_prdcr_en  )
   , .sl4_alt_rtt_swe_data     (grp4_rtt_swe_data )
   , .sl4_alt_rtt_swe_val      (grp4_rtt_swe_val_pulse  )
   , .sl4_alt_rtt_swe_ext      (grp4_rtt_swe_ext  )
   , .sl4_alt_rtt_swe_prdcr_en (grp4_rtt_swe_prdcr_en  )
   , .sl5_alt_rtt_swe_data     (grp5_rtt_swe_data )
   , .sl5_alt_rtt_swe_val      (grp5_rtt_swe_val_pulse  )
   , .sl5_alt_rtt_swe_ext      (grp5_rtt_swe_ext  )
   , .sl5_alt_rtt_swe_prdcr_en (grp5_rtt_swe_prdcr_en  )
   , .sl6_alt_rtt_swe_data     (grp6_rtt_swe_data )
   , .sl6_alt_rtt_swe_val      (grp6_rtt_swe_val_pulse  )
   , .sl6_alt_rtt_swe_ext      (grp6_rtt_swe_ext  )
   , .sl6_alt_rtt_swe_prdcr_en (grp6_rtt_swe_prdcr_en  )
   , .sl7_alt_rtt_swe_data     (grp7_rtt_swe_data )
   , .sl7_alt_rtt_swe_val      (grp7_rtt_swe_val_pulse  )
   , .sl7_alt_rtt_swe_ext      (grp7_rtt_swe_ext  )
   , .sl7_alt_rtt_swe_prdcr_en (grp7_rtt_swe_prdcr_en  )
   , .sl8_alt_rtt_swe_data     (grp8_rtt_swe_data )
   , .sl8_alt_rtt_swe_val      (grp8_rtt_swe_val_pulse  )
   , .sl8_alt_rtt_swe_ext      (grp8_rtt_swe_ext  )
   , .sl8_alt_rtt_swe_prdcr_en (grp8_rtt_swe_prdcr_en  )
   , .sl9_alt_rtt_swe_data     (grp9_rtt_swe_data )
   , .sl9_alt_rtt_swe_val      (grp9_rtt_swe_val_pulse  )
   , .sl9_alt_rtt_swe_ext      (grp9_rtt_swe_ext  )
   , .sl9_alt_rtt_swe_prdcr_en (grp9_rtt_swe_prdcr_en  )
   , .sl10_alt_rtt_swe_data     (grp10_rtt_swe_data )
   , .sl10_alt_rtt_swe_val      (grp10_rtt_swe_val_pulse  )
   , .sl10_alt_rtt_swe_ext      (grp10_rtt_swe_ext  )
   , .sl10_alt_rtt_swe_prdcr_en (grp10_rtt_swe_prdcr_en  )
   , .sl11_alt_rtt_swe_data     (grp11_rtt_swe_data )
   , .sl11_alt_rtt_swe_val      (grp11_rtt_swe_val_pulse  )
   , .sl11_alt_rtt_swe_ext      (grp11_rtt_swe_ext  )
   , .sl11_alt_rtt_swe_prdcr_en (grp11_rtt_swe_prdcr_en  )
   , .sl12_alt_rtt_swe_data     (grp12_rtt_swe_data )
   , .sl12_alt_rtt_swe_val      (grp12_rtt_swe_val_pulse  )
   , .sl12_alt_rtt_swe_ext      (grp12_rtt_swe_ext  )
   , .sl12_alt_rtt_swe_prdcr_en (grp12_rtt_swe_prdcr_en  )
   , .sl13_alt_rtt_swe_data     (grp13_rtt_swe_data )
   , .sl13_alt_rtt_swe_val      (grp13_rtt_swe_val_pulse  )
   , .sl13_alt_rtt_swe_ext      (grp13_rtt_swe_ext  )
   , .sl13_alt_rtt_swe_prdcr_en (grp13_rtt_swe_prdcr_en  )
   , .sl14_alt_rtt_swe_data     (grp14_rtt_swe_data )
   , .sl14_alt_rtt_swe_val      (grp14_rtt_swe_val_pulse  )
   , .sl14_alt_rtt_swe_ext      (grp14_rtt_swe_ext  )
   , .sl14_alt_rtt_swe_prdcr_en (grp14_rtt_swe_prdcr_en  )
   , .sl15_alt_rtt_swe_data     (grp15_rtt_swe_data )
   , .sl15_alt_rtt_swe_val      (grp15_rtt_swe_val_pulse  )
   , .sl15_alt_rtt_swe_ext      (grp15_rtt_swe_ext  )
   , .sl15_alt_rtt_swe_prdcr_en (grp15_rtt_swe_prdcr_en  )
   , .sl16_alt_rtt_swe_data     (grp16_rtt_swe_data )
   , .sl16_alt_rtt_swe_val      (grp16_rtt_swe_val_pulse  )
   , .sl16_alt_rtt_swe_ext      (grp16_rtt_swe_ext  )
   , .sl16_alt_rtt_swe_prdcr_en (grp16_rtt_swe_prdcr_en  )
   , .test_mode             (test_mode           )
   , .rst_a                 (rst_a               )
   , .rtt_drd_r             (rtt_drd_r           )
   , .rtt_prod_sel          (rtt_prod_sel        )
   , .rtt_freeze            (rtt_freeze          )
   , .rtt_src_num           (rtt_src_num         )
   , .atdata                (atdata              )
   , .atbytes               (atbytes             )
   , .atid                  (atid                )
   , .atvalid               (atvalid             )
   , .afready               (afready             )
   , .swe_atdata            (swe_atdata          )
   , .swe_atbytes           (swe_atbytes         )
   , .swe_atid              (swe_atid            )
   , .swe_atvalid           (swe_atvalid         )
   , .swe_afready           (swe_afready         )
   , .arct0_preadydbg       (arct_pready         )
   , .arct0_prdatadbg       (arct_prdata         )
   , .arct0_pslverrdbg      (arct_pslverr        )
   );


  assign      npu_grp0_vmid  = {npu_grp0_sid, npu_grp0_ssid};
  assign      npu_grp1_vmid  = {npu_grp1_sid, npu_grp1_ssid};
  assign      npu_grp2_vmid  = {npu_grp2_sid, npu_grp2_ssid};
  assign      npu_grp3_vmid  = {npu_grp3_sid, npu_grp3_ssid};

  //
  always_ff @(posedge clk or posedge rst_sync)
  begin : csm_switch_PROC
    if (rst_sync == 1'b1) begin
      npu_csm_base_r <=  '0;
      npu_csm_set_r  <= 5'b1;
    end
    else
    begin
      npu_csm_base_r <= npu_csm_base;
      if (npu_csm_set_r != 5'b0) begin
        npu_csm_set_r  <= {npu_csm_set_r[3:0],1'b0};
      end
    end
  end : csm_switch_PROC
  //

  assign  npu_csm_set = (|npu_csm_set_r[4:1]);
`ifdef ABV_ON // {
  //
  // Assertions
  //
  property prop_cfg;
  @(rst_a) DMIDW <= 16;
  endproperty : prop_cfg
  assert property (prop_cfg) else $fatal(1, "Error: Too many CCM ID bits");
`endif       // }

endmodule : npu_l2arc_group
