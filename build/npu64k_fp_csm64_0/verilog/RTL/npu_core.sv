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

// NPU toplevel
// vcs -sverilog +define+DUMMY_SLICE -f ../../shared/RTL/npu_shared_manifest ../../npu_slice/RTL/npu_slice.sv npu_slice_top.sv npu_cln_wrap.sv npu_cln_group.sv npu_cln_1p5.sv npu_stu_top.sv dummy_modules/npuarc_hs_cluster_top.sv npu_l2arc_group.sv npu_debug_port.v  npu_jtag_port.v  npu_tap_controller.v npu_core.sv npu_top.sv


`include "npu_defines.v"
`include "arcsync_exported_defines.v"
`include "npu_macros.svh"
`include "npu_axi_macros.svh"
`include "npu_apb_macros.svh"



module npu_core
  import npu_types::*;
  import npu_ecc_types::*;
(
  input  logic                          nl2_rst_a,              // Configuration port clock and reset

  // per group clock enable, power-down and reset (at main clock)
  input  logic                          grp0_rst_a,
  input  logic                          grp0_clk_en_a,
  input  logic                          grp1_rst_a,
  input  logic                          grp1_clk_en_a,
  input  logic                          grp2_rst_a,
  input  logic                          grp2_clk_en_a,
  input  logic                          grp3_rst_a,
  input  logic                          grp3_clk_en_a,
  output logic [64-1: 0]            npu_grp0_vmid,
  output logic [64-1: 0]            npu_grp1_vmid,
  output logic [64-1: 0]            npu_grp2_vmid,
  output logic [64-1: 0]            npu_grp3_vmid,
  input  logic                         nl2arc0_rst_a,
  input  logic                         nl2arc0_clk_en_a,
  output logic                         nl2arc0_evt_vm_irq,

  input  logic                         nl2arc1_rst_a,
  input  logic                         nl2arc1_clk_en_a,
  output logic                         nl2arc1_evt_vm_irq,
  input  logic                         ext_irq0_a, // From user-defined IRQ sources
  input  logic                         ext_irq1_a, // From user-defined IRQ sources

  // power domain
  // -l2arc
  input logic                       nl2arc_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       nl2arc_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       nl2arc_pd_mem,      // Power down of power domain memories (SRAM)
  input logic                       nl2arc_pd_logic,    // Power down of power domain logics
    // NPU Group Power status
  input logic                       grp0_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp0_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp0_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp0_pd_logic,    // Power down of power domain logics                     
  // NPU Group Power status
  input logic                       grp1_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp1_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp1_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp1_pd_logic,    // Power down of power domain logics                     
  // NPU Group Power status
  input logic                       grp2_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp2_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp2_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp2_pd_logic,    // Power down of power domain logics                     
  // NPU Group Power status
  input logic                       grp3_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp3_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp3_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp3_pd_logic,    // Power down of power domain logics                     
  input logic                       grp0_pwr_dwn_a,
  input logic                       grp1_pwr_dwn_a,
  input logic                       grp2_pwr_dwn_a,
  input logic                       grp3_pwr_dwn_a,

  // Slice interfaces
  input  logic                                                                                                        sl0nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl0nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl0nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl0nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl0nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl0nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl0nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl0nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl0nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl0nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl0nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl0nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl0nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl0nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl0nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl0nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl0nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl0nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl0nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl0nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl0nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl0nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl0nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl0nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl0nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl0nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl0nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl0nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl0nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl0nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl0nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl0nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl0nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl0nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl0nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl0nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl0nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl0nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl0nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl0nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl0nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl0nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl1nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl1nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl1nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl1nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl1nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl1nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl1nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl1nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl1nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl1nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl1nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl1nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl1nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl1nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl1nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl1nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl1nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl1nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl1nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl1nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl1nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl1nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl1nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl1nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl1nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl1nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl1nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl1nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl1nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl1nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl1nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl1nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl1nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl1nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl1nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl1nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl1nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl1nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl1nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl1nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl1nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl1nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl2nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl2nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl2nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl2nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl2nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl2nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl2nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl2nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl2nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl2nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl2nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl2nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl2nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl2nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl2nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl2nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl2nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl2nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl2nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl2nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl2nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl2nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl2nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl2nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl2nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl2nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl2nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl2nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl2nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl2nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl2nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl2nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl2nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl2nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl2nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl2nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl2nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl2nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl2nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl2nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl2nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl2nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl3nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl3nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl3nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl3nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl3nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl3nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl3nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl3nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl3nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl3nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl3nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl3nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl3nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl3nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl3nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl3nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl3nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl3nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl3nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl3nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl3nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl3nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl3nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl3nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl3nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl3nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl3nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl3nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl3nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl3nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl3nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl3nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl3nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl3nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl3nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl3nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl3nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl3nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl3nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl3nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl3nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl3nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl4nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl4nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl4nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl4nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl4nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl4nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl4nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl4nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl4nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl4nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl4nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl4nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl4nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl4nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl4nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl4nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl4nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl4nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl4nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl4nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl4nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl4nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl4nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl4nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl4nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl4nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl4nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl4nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl4nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl4nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl4nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl4nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl4nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl4nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl4nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl4nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl4nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl4nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl4nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl4nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl4nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl4nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl5nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl5nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl5nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl5nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl5nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl5nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl5nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl5nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl5nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl5nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl5nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl5nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl5nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl5nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl5nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl5nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl5nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl5nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl5nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl5nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl5nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl5nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl5nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl5nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl5nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl5nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl5nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl5nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl5nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl5nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl5nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl5nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl5nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl5nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl5nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl5nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl5nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl5nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl5nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl5nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl5nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl5nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl6nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl6nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl6nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl6nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl6nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl6nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl6nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl6nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl6nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl6nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl6nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl6nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl6nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl6nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl6nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl6nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl6nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl6nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl6nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl6nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl6nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl6nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl6nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl6nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl6nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl6nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl6nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl6nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl6nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl6nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl6nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl6nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl6nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl6nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl6nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl6nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl6nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl6nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl6nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl6nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl6nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl6nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl7nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl7nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl7nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl7nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl7nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl7nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl7nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl7nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl7nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl7nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl7nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl7nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl7nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl7nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl7nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl7nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl7nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl7nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl7nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl7nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl7nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl7nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl7nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl7nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl7nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl7nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl7nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl7nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl7nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl7nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl7nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl7nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl7nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl7nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl7nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl7nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl7nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl7nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl7nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl7nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl7nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl7nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl8nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl8nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl8nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl8nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl8nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl8nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl8nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl8nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl8nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl8nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl8nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl8nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl8nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl8nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl8nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl8nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl8nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl8nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl8nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl8nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl8nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl8nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl8nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl8nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl8nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl8nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl8nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl8nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl8nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl8nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl8nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl8nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl8nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl8nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl8nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl8nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl8nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl8nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl8nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl8nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl8nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl8nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl9nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl9nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl9nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl9nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl9nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl9nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl9nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl9nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl9nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl9nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl9nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl9nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl9nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl9nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl9nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl9nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl9nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl9nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl9nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl9nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl9nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl9nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl9nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl9nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl9nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl9nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl9nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl9nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl9nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl9nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl9nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl9nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl9nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl9nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl9nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl9nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl9nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl9nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl9nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl9nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl9nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl9nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl10nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl10nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl10nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl10nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl10nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl10nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl10nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl10nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl10nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl10nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl10nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl10nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl10nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl10nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl10nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl10nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl10nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl10nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl10nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl10nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl10nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl10nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl10nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl10nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl10nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl10nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl10nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl10nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl10nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl10nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl10nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl10nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl10nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl10nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl10nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl10nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl10nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl10nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl10nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl10nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl10nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl10nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl11nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl11nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl11nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl11nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl11nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl11nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl11nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl11nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl11nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl11nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl11nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl11nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl11nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl11nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl11nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl11nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl11nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl11nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl11nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl11nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl11nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl11nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl11nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl11nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl11nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl11nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl11nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl11nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl11nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl11nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl11nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl11nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl11nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl11nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl11nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl11nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl11nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl11nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl11nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl11nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl11nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl11nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl12nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl12nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl12nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl12nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl12nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl12nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl12nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl12nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl12nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl12nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl12nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl12nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl12nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl12nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl12nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl12nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl12nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl12nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl12nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl12nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl12nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl12nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl12nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl12nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl12nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl12nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl12nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl12nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl12nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl12nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl12nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl12nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl12nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl12nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl12nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl12nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl12nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl12nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl12nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl12nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl12nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl12nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl13nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl13nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl13nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl13nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl13nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl13nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl13nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl13nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl13nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl13nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl13nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl13nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl13nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl13nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl13nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl13nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl13nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl13nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl13nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl13nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl13nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl13nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl13nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl13nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl13nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl13nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl13nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl13nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl13nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl13nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl13nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl13nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl13nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl13nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl13nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl13nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl13nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl13nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl13nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl13nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl13nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl13nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl14nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl14nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl14nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl14nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl14nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl14nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl14nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl14nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl14nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl14nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl14nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl14nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl14nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl14nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl14nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl14nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl14nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl14nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl14nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl14nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl14nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl14nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl14nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl14nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl14nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl14nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl14nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl14nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl14nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl14nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl14nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl14nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl14nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl14nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl14nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl14nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl14nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl14nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl14nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl14nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl14nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl14nl1arc_ccm_axi_gals_r_rpnt,


  input  logic                                                                                                        sl15nl1arc_dev_axi_gals_clk_req_a,
  input  logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl15nl1arc_dev_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl15nl1arc_dev_axi_gals_aw_rdpnt,
  input  logic [1:0]                                                                                       sl15nl1arc_dev_axi_gals_aw_wpnt_a,
  output logic [1:0]                                                                                       sl15nl1arc_dev_axi_gals_aw_rpnt,
  input  logic [VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW:0]                                                           sl15nl1arc_dev_axi_gals_w_data,
  output logic [`NUM_FLANES(VSIZE*64+VSIZE*64/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      sl15nl1arc_dev_axi_gals_w_rdpnt,
  input  logic [3:0]                                                                                        sl15nl1arc_dev_axi_gals_w_wpnt_a,
  output logic [3:0]                                                                                        sl15nl1arc_dev_axi_gals_w_rpnt,
  output logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl15nl1arc_dev_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               sl15nl1arc_dev_axi_gals_b_rdpnt,
  output logic [1:0]                                                                                        sl15nl1arc_dev_axi_gals_b_wpnt,
  input  logic [1:0]                                                                                        sl15nl1arc_dev_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl15nl1arc_dev_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              sl15nl1arc_dev_axi_gals_ar_rdpnt,
  input  logic [1:0]                                                                                       sl15nl1arc_dev_axi_gals_ar_wpnt_a,
  output logic [1:0]                                                                                       sl15nl1arc_dev_axi_gals_ar_rpnt,
  output logic [1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      sl15nl1arc_dev_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+VSIZE*64+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] sl15nl1arc_dev_axi_gals_r_rdpnt,
  output logic [3:0]                                                                                        sl15nl1arc_dev_axi_gals_r_wpnt,
  input  logic [3:0]                                                                                        sl15nl1arc_dev_axi_gals_r_rpnt_a,
  output logic                                                                                                        sl15nl1arc_ccm_axi_gals_clk_req,
  output logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                sl15nl1arc_ccm_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl15nl1arc_ccm_axi_gals_aw_rdpnt,
  output logic [0:0]                                                                                       sl15nl1arc_ccm_axi_gals_aw_wpnt,
  input  logic [0:0]                                                                                       sl15nl1arc_ccm_axi_gals_aw_rpnt_a,
  output logic [64+64/8+SLICE_MMIO_WUW:0]                                                           sl15nl1arc_ccm_axi_gals_w_data,
  input  logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      sl15nl1arc_ccm_axi_gals_w_rdpnt,
  output logic [1:0]                                                                                        sl15nl1arc_ccm_axi_gals_w_wpnt,
  input  logic [1:0]                                                                                        sl15nl1arc_ccm_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                sl15nl1arc_ccm_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               sl15nl1arc_ccm_axi_gals_b_rdpnt,
  input  logic [0:0]                                                                                        sl15nl1arc_ccm_axi_gals_b_wpnt_a,
  output logic [0:0]                                                                                        sl15nl1arc_ccm_axi_gals_b_rpnt,
  output logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                sl15nl1arc_ccm_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              sl15nl1arc_ccm_axi_gals_ar_rdpnt,
  output logic [0:0]                                                                                       sl15nl1arc_ccm_axi_gals_ar_wpnt,
  input  logic [0:0]                                                                                       sl15nl1arc_ccm_axi_gals_ar_rpnt_a,
  input  logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      sl15nl1arc_ccm_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] sl15nl1arc_ccm_axi_gals_r_rdpnt,
  input  logic [1:0]                                                                                        sl15nl1arc_ccm_axi_gals_r_wpnt_a,
  output logic [1:0]                                                                                        sl15nl1arc_ccm_axi_gals_r_rpnt,



  // L2 ARC0 signals
  input      logic [21:0]                   nl2arc0_intvbase_in,      //Boot
  input      logic                          nl2arc0_arc_halt_req_a,   //Halt
  output     logic                          nl2arc0_arc_halt_ack,
  input      logic                          nl2arc0_arc_run_req_a,    //Run
  output     logic                          nl2arc0_arc_run_ack,
  output     logic                          nl2arc0_sys_sleep_r,      //Status
  output     logic [2:0]                    nl2arc0_sys_sleep_mode_r,
  output     logic                          nl2arc0_sys_halt_r,
  output     logic                          nl2arc0_sys_tf_halt_r,
  input      logic [17:0]    nl2arc0_arc_irq_a,
  input      logic [17:0]    nl2arc0_arc_event_a,
  // L2 ARC1 signals
  input      logic [21:0]                   nl2arc1_intvbase_in,      //Boot
  input      logic                          nl2arc1_arc_halt_req_a,   //Halt
  output     logic                          nl2arc1_arc_halt_ack,
  input      logic                          nl2arc1_arc_run_req_a,    //Run
  output     logic                          nl2arc1_arc_run_ack,
  output     logic                          nl2arc1_sys_sleep_r,      //Status
  output     logic [2:0]                    nl2arc1_sys_sleep_mode_r,
  output     logic                          nl2arc1_sys_halt_r,
  output     logic                          nl2arc1_sys_tf_halt_r,
  input      logic [17:0]    nl2arc1_arc_irq_a,
  input      logic [17:0]    nl2arc1_arc_event_a,
  input      logic [`NPU_SLICE_NUM-1:0][1:0] l1_to_l2_event,
  output     logic [`NPU_SLICE_NUM-1:0][1:0] l2_to_l1_event,
  input      logic [NPU_AXI_ADDR_W-1:24]     npu_csm_base,
  //ARC_Trace
  // CoreSight interface global signals
  input      logic                          at_clk_en,
  input      logic                          at_rst_an,
  input      logic [63:0]                   atb_cstimestamp,
  // CoreSight interface of L2 core or L1 core in case of NPU HAS NO L2ARC
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
  input      logic                          arct0_dbgen,
  input      logic                          arct0_niden,


  // Shared signals for APB Interface to ARC_Trace and to L2 debug port
  input      logic                          arct_dbg_prot_sel,
  input      logic                          arct_rst_an,

  input      logic                          nl2arc0_dbgen,
  input      logic                          nl2arc0_niden,
  input      logic                          nl2arc1_dbgen,
  input      logic                          nl2arc1_niden,

  // Software trace events
  input      logic                          sl0_rtt_swe_val,
  input      logic [32:0]                   sl0_rtt_swe_data,
  input      logic [7:0]                    sl0_rtt_swe_ext,
  input      logic                          sl1_rtt_swe_val,
  input      logic [32:0]                   sl1_rtt_swe_data,
  input      logic [7:0]                    sl1_rtt_swe_ext,
  input      logic                          sl2_rtt_swe_val,
  input      logic [32:0]                   sl2_rtt_swe_data,
  input      logic [7:0]                    sl2_rtt_swe_ext,
  input      logic                          sl3_rtt_swe_val,
  input      logic [32:0]                   sl3_rtt_swe_data,
  input      logic [7:0]                    sl3_rtt_swe_ext,
  input      logic                          sl4_rtt_swe_val,
  input      logic [32:0]                   sl4_rtt_swe_data,
  input      logic [7:0]                    sl4_rtt_swe_ext,
  input      logic                          sl5_rtt_swe_val,
  input      logic [32:0]                   sl5_rtt_swe_data,
  input      logic [7:0]                    sl5_rtt_swe_ext,
  input      logic                          sl6_rtt_swe_val,
  input      logic [32:0]                   sl6_rtt_swe_data,
  input      logic [7:0]                    sl6_rtt_swe_ext,
  input      logic                          sl7_rtt_swe_val,
  input      logic [32:0]                   sl7_rtt_swe_data,
  input      logic [7:0]                    sl7_rtt_swe_ext,
  input      logic                          sl8_rtt_swe_val,
  input      logic [32:0]                   sl8_rtt_swe_data,
  input      logic [7:0]                    sl8_rtt_swe_ext,
  input      logic                          sl9_rtt_swe_val,
  input      logic [32:0]                   sl9_rtt_swe_data,
  input      logic [7:0]                    sl9_rtt_swe_ext,
  input      logic                          sl10_rtt_swe_val,
  input      logic [32:0]                   sl10_rtt_swe_data,
  input      logic [7:0]                    sl10_rtt_swe_ext,
  input      logic                          sl11_rtt_swe_val,
  input      logic [32:0]                   sl11_rtt_swe_data,
  input      logic [7:0]                    sl11_rtt_swe_ext,
  input      logic                          sl12_rtt_swe_val,
  input      logic [32:0]                   sl12_rtt_swe_data,
  input      logic [7:0]                    sl12_rtt_swe_ext,
  input      logic                          sl13_rtt_swe_val,
  input      logic [32:0]                   sl13_rtt_swe_data,
  input      logic [7:0]                    sl13_rtt_swe_ext,
  input      logic                          sl14_rtt_swe_val,
  input      logic [32:0]                   sl14_rtt_swe_data,
  input      logic [7:0]                    sl14_rtt_swe_ext,
  input      logic                          sl15_rtt_swe_val,
  input      logic [32:0]                   sl15_rtt_swe_data,
  input      logic [7:0]                    sl15_rtt_swe_ext,

  input      logic                          nl2arc0_wdt_clk              ,
  output     logic                          nl2arc0_wdt_reset_error    ,
  output     logic                          nl2arc0_wdt_reset_wdt_clk_error  ,
  input      logic                          nl2arc1_wdt_clk              ,
  output     logic                          nl2arc1_wdt_reset_error    ,
  output     logic                          nl2arc1_wdt_reset_wdt_clk_error  ,
  output logic                               grp0_scm_dbank_sbe,
  output logic                               grp0_scm_dbank_dbe,
  output logic                               grp1_scm_dbank_sbe,
  output logic                               grp1_scm_dbank_dbe,
  output logic                               grp2_scm_dbank_sbe,
  output logic                               grp2_scm_dbank_dbe,
  output logic                               grp3_scm_dbank_sbe,
  output logic                               grp3_scm_dbank_dbe,
  //L2 ARC0 memory ECC error signal
  output logic                               nl2arc0_ecc_sbe,
  output logic                               nl2arc0_ecc_dbe,
  output logic                               nl2arc1_ecc_sbe,
  output logic                               nl2arc1_ecc_dbe,

  input      logic [7:0]                     clusternum,
  output  logic  [7:0]                   sl0nl1arc_arcnum,
  input   logic                          sl0nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl0nl1arc_dbg_),
  output  logic  [7:0]                   sl1nl1arc_arcnum,
  input   logic                          sl1nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl1nl1arc_dbg_),
  output  logic  [7:0]                   sl2nl1arc_arcnum,
  input   logic                          sl2nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl2nl1arc_dbg_),
  output  logic  [7:0]                   sl3nl1arc_arcnum,
  input   logic                          sl3nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl3nl1arc_dbg_),
  output  logic  [7:0]                   sl4nl1arc_arcnum,
  input   logic                          sl4nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl4nl1arc_dbg_),
  output  logic  [7:0]                   sl5nl1arc_arcnum,
  input   logic                          sl5nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl5nl1arc_dbg_),
  output  logic  [7:0]                   sl6nl1arc_arcnum,
  input   logic                          sl6nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl6nl1arc_dbg_),
  output  logic  [7:0]                   sl7nl1arc_arcnum,
  input   logic                          sl7nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl7nl1arc_dbg_),
  output  logic  [7:0]                   sl8nl1arc_arcnum,
  input   logic                          sl8nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl8nl1arc_dbg_),
  output  logic  [7:0]                   sl9nl1arc_arcnum,
  input   logic                          sl9nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl9nl1arc_dbg_),
  output  logic  [7:0]                   sl10nl1arc_arcnum,
  input   logic                          sl10nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl10nl1arc_dbg_),
  output  logic  [7:0]                   sl11nl1arc_arcnum,
  input   logic                          sl11nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl11nl1arc_dbg_),
  output  logic  [7:0]                   sl12nl1arc_arcnum,
  input   logic                          sl12nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl12nl1arc_dbg_),
  output  logic  [7:0]                   sl13nl1arc_arcnum,
  input   logic                          sl13nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl13nl1arc_dbg_),
  output  logic  [7:0]                   sl14nl1arc_arcnum,
  input   logic                          sl14nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl14nl1arc_dbg_),
  output  logic  [7:0]                   sl15nl1arc_arcnum,
  input   logic                          sl15nl1arc_evt_vm_irq_a,
  `APBASYNCINI(16,32,sl15nl1arc_dbg_),
  input   logic                          arct_clk,
  `APBSLV(32,32,arct_),
// spyglass disable_block NoFeedThrus-ML
// SMD: No Feed Through
// SJ : The L1 peers event are shuffled only
  input   logic [`NPU_SLICE_NUM-1:0][`NPU_SLICE_NUM-1:0] l1_peer_event_out,
  output  logic [`NPU_SLICE_NUM-1:0][`NPU_SLICE_NUM-1:0] l1_peer_event_in,
// spyglass enable_block NoFeedThrus-ML
  // Async bridge && reset ctrl
  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst0_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst0_axi_arvalid, // read command valid
  input  logic                        npu_mst0_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst0_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst0_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst0_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst0_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst0_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst0_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst0_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst0_axi_arsize  ,      // read command
  // read data channel
  input  logic                        npu_mst0_axi_rvalid,  // read data valid
  output logic                        npu_mst0_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst0_axi_rid,     // read data id
  input  logic          [64-1:0]   npu_mst0_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst0_axi_rresp,   // read response
  input  logic                        npu_mst0_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst0_axi_awvalid, // write command valid
  input  logic                        npu_mst0_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst0_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst0_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst0_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst0_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst0_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst0_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst0_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst0_axi_awsize  ,      // read command
  // write data channel
  output logic                        npu_mst0_axi_wvalid,  // write data valid
  input  logic                        npu_mst0_axi_wready,  // write data accept
  output logic          [64-1:0]   npu_mst0_axi_wdata,   // write data
  output logic          [64/8-1:0] npu_mst0_axi_wstrb,   // write data strobe
  output logic                        npu_mst0_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst0_axi_bvalid,  // write response valid
  output logic                        npu_mst0_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst0_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst0_axi_bresp,    // write response
  //-slave dmi, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_dmi0_axi
  //axislv(1/*idw*/,`aw,`ISIZE*32/*dw*/,1/*argw*/,1/*awgw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/,0/*awcpl*/, npu_dmi0_axi_/*prefix*/)
  // read command channel
  input  logic                        npu_dmi0_axi_arvalid, // read command valid
  output logic                        npu_dmi0_axi_arready, // read command accept
  input  logic          [16-1:0]  npu_dmi0_axi_arid,    // read command ID
  input  logic          [40-1:0]   npu_dmi0_axi_araddr  ,      // read command
  input  logic          [3:0]         npu_dmi0_axi_arcache ,      // read command
  input  logic          [2:0]         npu_dmi0_axi_arprot  ,      // read command
  input  logic          [1-1:0]         npu_dmi0_axi_arlock  ,      // read command
  input  logic          [1:0]         npu_dmi0_axi_arburst ,      // read command
  input  logic          [3:0]         npu_dmi0_axi_arlen   ,      // read command
  input  logic          [2:0]         npu_dmi0_axi_arsize  ,      // read command
  // read data channel
  output logic                        npu_dmi0_axi_rvalid,  // read data valid
  input  logic                        npu_dmi0_axi_rready,  // read data accept
  output logic          [16-1:0]  npu_dmi0_axi_rid,     // read data id
  output logic          [512-1:0]   npu_dmi0_axi_rdata,   // read data
  output logic          [1:0]         npu_dmi0_axi_rresp,   // read response
  output logic                        npu_dmi0_axi_rlast,   // read last
  // write command channel
  input  logic                        npu_dmi0_axi_awvalid, // write command valid
  output logic                        npu_dmi0_axi_awready, // write command accept
  input  logic          [16-1:0]  npu_dmi0_axi_awid,    // write command ID
  input  logic          [40-1:0]   npu_dmi0_axi_awaddr  ,      // read command
  input  logic          [3:0]         npu_dmi0_axi_awcache ,      // read command
  input  logic          [2:0]         npu_dmi0_axi_awprot  ,      // read command
  input  logic          [1-1:0]         npu_dmi0_axi_awlock  ,      // read command
  input  logic          [1:0]         npu_dmi0_axi_awburst ,      // read command
  input  logic          [3:0]         npu_dmi0_axi_awlen   ,      // read command
  input  logic          [2:0]         npu_dmi0_axi_awsize  ,      // read command
  // write data channel
  input  logic                        npu_dmi0_axi_wvalid,  // write data valid
  output logic                        npu_dmi0_axi_wready,  // write data accept
  input  logic          [512-1:0]   npu_dmi0_axi_wdata,   // write data
  input  logic          [512/8-1:0] npu_dmi0_axi_wstrb,   // write data strobe
  input  logic                        npu_dmi0_axi_wlast,   // write data last
  // write response channel
  output logic                        npu_dmi0_axi_bvalid,  // write response valid
  input  logic                        npu_dmi0_axi_bready,  // write response accept
  output logic          [16-1:0]  npu_dmi0_axi_bid,     // write response id
  output logic          [1:0]         npu_dmi0_axi_bresp,   // write response
  input   logic                          npu_noc_clk,
  input   logic                          npu_noc_rst_a,
  input   logic                          npu_cfg_clk,
  input   logic                          npu_cfg_rst_a,
  input   logic                          sl0nl1arc_pwr_dwn_a,
  output  logic                          sl0nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl0nl1arc_dbg_pack,
  input   logic [31:0]                   sl0nl1arc_dbg_resp,
  input   logic                          sl1nl1arc_pwr_dwn_a,
  output  logic                          sl1nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl1nl1arc_dbg_pack,
  input   logic [31:0]                   sl1nl1arc_dbg_resp,
  input   logic                          sl2nl1arc_pwr_dwn_a,
  output  logic                          sl2nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl2nl1arc_dbg_pack,
  input   logic [31:0]                   sl2nl1arc_dbg_resp,
  input   logic                          sl3nl1arc_pwr_dwn_a,
  output  logic                          sl3nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl3nl1arc_dbg_pack,
  input   logic [31:0]                   sl3nl1arc_dbg_resp,
  input   logic                          sl4nl1arc_pwr_dwn_a,
  output  logic                          sl4nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl4nl1arc_dbg_pack,
  input   logic [31:0]                   sl4nl1arc_dbg_resp,
  input   logic                          sl5nl1arc_pwr_dwn_a,
  output  logic                          sl5nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl5nl1arc_dbg_pack,
  input   logic [31:0]                   sl5nl1arc_dbg_resp,
  input   logic                          sl6nl1arc_pwr_dwn_a,
  output  logic                          sl6nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl6nl1arc_dbg_pack,
  input   logic [31:0]                   sl6nl1arc_dbg_resp,
  input   logic                          sl7nl1arc_pwr_dwn_a,
  output  logic                          sl7nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl7nl1arc_dbg_pack,
  input   logic [31:0]                   sl7nl1arc_dbg_resp,
  input   logic                          sl8nl1arc_pwr_dwn_a,
  output  logic                          sl8nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl8nl1arc_dbg_pack,
  input   logic [31:0]                   sl8nl1arc_dbg_resp,
  input   logic                          sl9nl1arc_pwr_dwn_a,
  output  logic                          sl9nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl9nl1arc_dbg_pack,
  input   logic [31:0]                   sl9nl1arc_dbg_resp,
  input   logic                          sl10nl1arc_pwr_dwn_a,
  output  logic                          sl10nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl10nl1arc_dbg_pack,
  input   logic [31:0]                   sl10nl1arc_dbg_resp,
  input   logic                          sl11nl1arc_pwr_dwn_a,
  output  logic                          sl11nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl11nl1arc_dbg_pack,
  input   logic [31:0]                   sl11nl1arc_dbg_resp,
  input   logic                          sl12nl1arc_pwr_dwn_a,
  output  logic                          sl12nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl12nl1arc_dbg_pack,
  input   logic [31:0]                   sl12nl1arc_dbg_resp,
  input   logic                          sl13nl1arc_pwr_dwn_a,
  output  logic                          sl13nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl13nl1arc_dbg_pack,
  input   logic [31:0]                   sl13nl1arc_dbg_resp,
  input   logic                          sl14nl1arc_pwr_dwn_a,
  output  logic                          sl14nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl14nl1arc_dbg_pack,
  input   logic [31:0]                   sl14nl1arc_dbg_resp,
  input   logic                          sl15nl1arc_pwr_dwn_a,
  output  logic                          sl15nl1arc_dbg_cmdval,
  output  logic [36:0]                   sl15nl1arc_dbg_pack,
  input   logic [31:0]                   sl15nl1arc_dbg_resp,
  // configuration slave AXI
  //axislv(1/*idw*/,`aw,`ISIZE*32/*dw*/,1/*argw*/,1/*awgw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/,0/*awcpl*/, npu_cfg_axi_/*prefix*/)
  // read command channel
  input  logic                        npu_cfg_axi_arvalid, // read command valid
  output logic                        npu_cfg_axi_arready, // read command accept
  input  logic          [16-1:0]  npu_cfg_axi_arid,    // read command ID
  input  logic          [40-1:0]   npu_cfg_axi_araddr  ,      // read command
  input  logic          [3:0]         npu_cfg_axi_arcache ,      // read command
  input  logic          [2:0]         npu_cfg_axi_arprot  ,      // read command
  input  logic          [1-1:0]         npu_cfg_axi_arlock  ,      // read command
  input  logic          [1:0]         npu_cfg_axi_arburst ,      // read command
  input  logic          [3:0]         npu_cfg_axi_arlen   ,      // read command
  input  logic          [2:0]         npu_cfg_axi_arsize  ,      // read command
  // read data channel
  output logic                        npu_cfg_axi_rvalid,  // read data valid
  input  logic                        npu_cfg_axi_rready,  // read data accept
  output logic          [16-1:0]  npu_cfg_axi_rid,     // read data id
  output logic          [32-1:0]   npu_cfg_axi_rdata,   // read data
  output logic          [1:0]         npu_cfg_axi_rresp,   // read response
  output logic                        npu_cfg_axi_rlast,   // read last
  // write command channel
  input  logic                        npu_cfg_axi_awvalid, // write command valid
  output logic                        npu_cfg_axi_awready, // write command accept
  input  logic          [16-1:0]  npu_cfg_axi_awid,    // write command ID
  input  logic          [40-1:0]   npu_cfg_axi_awaddr  ,      // read command
  input  logic          [3:0]         npu_cfg_axi_awcache ,      // read command
  input  logic          [2:0]         npu_cfg_axi_awprot  ,      // read command
  input  logic          [1-1:0]         npu_cfg_axi_awlock  ,      // read command
  input  logic          [1:0]         npu_cfg_axi_awburst ,      // read command
  input  logic          [3:0]         npu_cfg_axi_awlen   ,      // read command
  input  logic          [2:0]         npu_cfg_axi_awsize  ,      // read command
  // write data channel
  input  logic                        npu_cfg_axi_wvalid,  // write data valid
  output logic                        npu_cfg_axi_wready,  // write data accept
  input  logic          [32-1:0]   npu_cfg_axi_wdata,   // write data
  input  logic          [32/8-1:0] npu_cfg_axi_wstrb,   // write data strobe
  input  logic                        npu_cfg_axi_wlast,   // write data last
  // write response channel
  output logic                        npu_cfg_axi_bvalid,  // write response valid
  input  logic                        npu_cfg_axi_bready,  // write response accept
  output logic          [16-1:0]  npu_cfg_axi_bid,     // write response id
  output logic          [1:0]         npu_cfg_axi_bresp,   // write response
  input   logic                          nl2arc_pwr_dwn_a,
   input      logic                      nl2arc0_pwr_dwn_a,
   input      logic                      nl2arc1_pwr_dwn_a,
  input   logic                          test_mode,


  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst1_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst1_axi_arvalid, // read command valid
  input  logic                        npu_mst1_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst1_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst1_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst1_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst1_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst1_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst1_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst1_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst1_axi_arsize  ,      // read command
  output logic          [32-1:0] npu_mst1_axi_arsid,   // read command SID field
  output logic          [32-1:0] npu_mst1_axi_arssid,  // read command SSID field
  // read data channel
  input  logic                        npu_mst1_axi_rvalid,  // read data valid
  output logic                        npu_mst1_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst1_axi_rid,     // read data id
  input  logic          [512-1:0]   npu_mst1_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst1_axi_rresp,   // read response
  input  logic                        npu_mst1_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst1_axi_awvalid, // write command valid
  input  logic                        npu_mst1_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst1_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst1_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst1_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst1_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst1_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst1_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst1_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst1_axi_awsize  ,      // read command
  output logic          [32-1:0] npu_mst1_axi_awsid,   // write command SID field
  output logic          [32-1:0] npu_mst1_axi_awssid,  // write command SSID field
  // write data channel
  output logic                        npu_mst1_axi_wvalid,  // write data valid
  input  logic                        npu_mst1_axi_wready,  // write data accept
  output logic          [512-1:0]   npu_mst1_axi_wdata,   // write data
  output logic          [512/8-1:0] npu_mst1_axi_wstrb,   // write data strobe
  output logic                        npu_mst1_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst1_axi_bvalid,  // write response valid
  output logic                        npu_mst1_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst1_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst1_axi_bresp,    // write response

  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst2_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst2_axi_arvalid, // read command valid
  input  logic                        npu_mst2_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst2_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst2_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst2_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst2_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst2_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst2_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst2_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst2_axi_arsize  ,      // read command
  output logic          [32-1:0] npu_mst2_axi_arsid,   // read command SID field
  output logic          [32-1:0] npu_mst2_axi_arssid,  // read command SSID field
  // read data channel
  input  logic                        npu_mst2_axi_rvalid,  // read data valid
  output logic                        npu_mst2_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst2_axi_rid,     // read data id
  input  logic          [512-1:0]   npu_mst2_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst2_axi_rresp,   // read response
  input  logic                        npu_mst2_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst2_axi_awvalid, // write command valid
  input  logic                        npu_mst2_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst2_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst2_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst2_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst2_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst2_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst2_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst2_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst2_axi_awsize  ,      // read command
  output logic          [32-1:0] npu_mst2_axi_awsid,   // write command SID field
  output logic          [32-1:0] npu_mst2_axi_awssid,  // write command SSID field
  // write data channel
  output logic                        npu_mst2_axi_wvalid,  // write data valid
  input  logic                        npu_mst2_axi_wready,  // write data accept
  output logic          [512-1:0]   npu_mst2_axi_wdata,   // write data
  output logic          [512/8-1:0] npu_mst2_axi_wstrb,   // write data strobe
  output logic                        npu_mst2_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst2_axi_bvalid,  // write response valid
  output logic                        npu_mst2_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst2_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst2_axi_bresp,    // write response

  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst3_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst3_axi_arvalid, // read command valid
  input  logic                        npu_mst3_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst3_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst3_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst3_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst3_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst3_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst3_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst3_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst3_axi_arsize  ,      // read command
  output logic          [32-1:0] npu_mst3_axi_arsid,   // read command SID field
  output logic          [32-1:0] npu_mst3_axi_arssid,  // read command SSID field
  // read data channel
  input  logic                        npu_mst3_axi_rvalid,  // read data valid
  output logic                        npu_mst3_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst3_axi_rid,     // read data id
  input  logic          [512-1:0]   npu_mst3_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst3_axi_rresp,   // read response
  input  logic                        npu_mst3_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst3_axi_awvalid, // write command valid
  input  logic                        npu_mst3_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst3_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst3_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst3_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst3_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst3_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst3_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst3_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst3_axi_awsize  ,      // read command
  output logic          [32-1:0] npu_mst3_axi_awsid,   // write command SID field
  output logic          [32-1:0] npu_mst3_axi_awssid,  // write command SSID field
  // write data channel
  output logic                        npu_mst3_axi_wvalid,  // write data valid
  input  logic                        npu_mst3_axi_wready,  // write data accept
  output logic          [512-1:0]   npu_mst3_axi_wdata,   // write data
  output logic          [512/8-1:0] npu_mst3_axi_wstrb,   // write data strobe
  output logic                        npu_mst3_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst3_axi_bvalid,  // write response valid
  output logic                        npu_mst3_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst3_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst3_axi_bresp,    // write response

  // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
  //-npu_mst_axi
  //aximst(1/*idw*/,32/*aw*/,`ISIZE*32/*dw*/,1/*argw*/,1/*argw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/, 0/*awcpl*/, npu_mst4_axi_/*pref*/)
  // read command channel
  output logic                        npu_mst4_axi_arvalid, // read command valid
  input  logic                        npu_mst4_axi_arready, // read command accept
  output logic          [5-1:0]  npu_mst4_axi_arid,    // read command ID
  output logic          [40-1:0]   npu_mst4_axi_araddr  ,      // read command
  output logic          [3:0]         npu_mst4_axi_arcache ,      // read command
  output logic          [2:0]         npu_mst4_axi_arprot  ,      // read command
  output logic          [1-1:0]         npu_mst4_axi_arlock  ,      // read command
  output logic          [1:0]         npu_mst4_axi_arburst ,      // read command
  output logic          [3:0]         npu_mst4_axi_arlen   ,      // read command
  output logic          [2:0]         npu_mst4_axi_arsize  ,      // read command
  output logic          [32-1:0] npu_mst4_axi_arsid,   // read command SID field
  output logic          [32-1:0] npu_mst4_axi_arssid,  // read command SSID field
  // read data channel
  input  logic                        npu_mst4_axi_rvalid,  // read data valid
  output logic                        npu_mst4_axi_rready,  // read data accept
  input  logic          [5-1:0]  npu_mst4_axi_rid,     // read data id
  input  logic          [512-1:0]   npu_mst4_axi_rdata,   // read data
  input  logic          [1:0]         npu_mst4_axi_rresp,   // read response
  input  logic                        npu_mst4_axi_rlast,   // read last
  // write command channel
  output logic                        npu_mst4_axi_awvalid, // write command valid
  input  logic                        npu_mst4_axi_awready, // write command accept
  output logic          [5-1:0]  npu_mst4_axi_awid,    // write command ID
  output logic          [40-1:0]   npu_mst4_axi_awaddr  ,      // read command
  output logic          [3:0]         npu_mst4_axi_awcache ,      // read command
  output logic          [2:0]         npu_mst4_axi_awprot  ,      // read command
  output logic          [1-1:0]         npu_mst4_axi_awlock  ,      // read command
  output logic          [1:0]         npu_mst4_axi_awburst ,      // read command
  output logic          [3:0]         npu_mst4_axi_awlen   ,      // read command
  output logic          [2:0]         npu_mst4_axi_awsize  ,      // read command
  output logic          [32-1:0] npu_mst4_axi_awsid,   // write command SID field
  output logic          [32-1:0] npu_mst4_axi_awssid,  // write command SSID field
  // write data channel
  output logic                        npu_mst4_axi_wvalid,  // write data valid
  input  logic                        npu_mst4_axi_wready,  // write data accept
  output logic          [512-1:0]   npu_mst4_axi_wdata,   // write data
  output logic          [512/8-1:0] npu_mst4_axi_wstrb,   // write data strobe
  output logic                        npu_mst4_axi_wlast,   // write data last
  // write response channel
  input  logic                        npu_mst4_axi_bvalid,  // write response valid
  output logic                        npu_mst4_axi_bready,  // write response accept
  input  logic          [5-1:0]  npu_mst4_axi_bid,     // write response id
  input  logic          [1:0]         npu_mst4_axi_bresp,    // write response
  input   logic                          npu_core_clk,
  input   logic                          npu_core_rst_a


);

  localparam int L2IDW  = 2+$clog2(`NPU_AXI_TARGETS+1);
  localparam int CCMIDW = 1;

  //NoC master
  `AXIASYNCWIRES(5,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,l2arc_noc_axi_gals_);
  `AXIASYNCWIRES(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp0_noc_axi_gals_);
  `AXIASYNCWIRES(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp1_noc_axi_gals_);
  `AXIASYNCWIRES(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp2_noc_axi_gals_);
  `AXIASYNCWIRES(5,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,npu_grp3_noc_axi_gals_);


  //DMI slave
  `AXIASYNCWIRES(`NPU_AXI_TARGET_ID_WIDTH,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,1,3,1,1,3,dmi0_axi_gals_);

  //Config AXI
  // configuration slave AXI
  `AXIASYNCWIRES(`NPU_AXI_TARGET_ID_WIDTH,32,1,1,1,1,1,0,0,0,0,0,cfg_axi_gals_);

  logic                       grp0_evt_vm_irq;
  logic                       grp1_evt_vm_irq;
  logic                       grp2_evt_vm_irq;
  logic                       grp3_evt_vm_irq;
  // STU events and interrupts
  logic [`NPU_STU_CHAN_NUM-1:0]           stu_err_irq_a;

  // L2 ARC0 debug interface
  logic                                          nl2arc0_dbg_cmdval;
  logic [36:0]                                   nl2arc0_dbg_pack;
  logic [31:0]                                   nl2arc0_dbg_resp;
  // L2 ARC1 debug interface
  logic                                          nl2arc1_dbg_cmdval;
  logic [36:0]                                   nl2arc1_dbg_pack;
  logic [31:0]                                   nl2arc1_dbg_resp;

  logic [7:0]                                    nl2arc0_arcnum;
  logic [7:0]                                    nl2arc1_arcnum;

  // ARC_Trace
  `APBASYNCWIRES(16,32,arct_syn_);
  logic                          grp4_rtt_swe_val;
  logic [32:0]                   grp4_rtt_swe_data;
  logic [7:0]                    grp4_rtt_swe_ext;
  logic                          grp4_rtt_swe_prdcr_en;
  logic                          grp5_rtt_swe_val;
  logic [32:0]                   grp5_rtt_swe_data;
  logic [7:0]                    grp5_rtt_swe_ext;
  logic                          grp5_rtt_swe_prdcr_en;
  logic                          grp6_rtt_swe_val;
  logic [32:0]                   grp6_rtt_swe_data;
  logic [7:0]                    grp6_rtt_swe_ext;
  logic                          grp6_rtt_swe_prdcr_en;
  logic                          grp7_rtt_swe_val;
  logic [32:0]                   grp7_rtt_swe_data;
  logic [7:0]                    grp7_rtt_swe_ext;
  logic                          grp7_rtt_swe_prdcr_en;
  logic                          grp8_rtt_swe_val;
  logic [32:0]                   grp8_rtt_swe_data;
  logic [7:0]                    grp8_rtt_swe_ext;
  logic                          grp8_rtt_swe_prdcr_en;
  logic                          grp9_rtt_swe_val;
  logic [32:0]                   grp9_rtt_swe_data;
  logic [7:0]                    grp9_rtt_swe_ext;
  logic                          grp9_rtt_swe_prdcr_en;
  logic                          grp10_rtt_swe_val;
  logic [32:0]                   grp10_rtt_swe_data;
  logic [7:0]                    grp10_rtt_swe_ext;
  logic                          grp10_rtt_swe_prdcr_en;
  logic                          grp11_rtt_swe_val;
  logic [32:0]                   grp11_rtt_swe_data;
  logic [7:0]                    grp11_rtt_swe_ext;
  logic                          grp11_rtt_swe_prdcr_en;
  logic                          grp12_rtt_swe_val;
  logic [32:0]                   grp12_rtt_swe_data;
  logic [7:0]                    grp12_rtt_swe_ext;
  logic                          grp12_rtt_swe_prdcr_en;
  logic                          grp13_rtt_swe_val;
  logic [32:0]                   grp13_rtt_swe_data;
  logic [7:0]                    grp13_rtt_swe_ext;
  logic                          grp13_rtt_swe_prdcr_en;
  logic                          grp14_rtt_swe_val;
  logic [32:0]                   grp14_rtt_swe_data;
  logic [7:0]                    grp14_rtt_swe_ext;
  logic                          grp14_rtt_swe_prdcr_en;
  logic                          grp15_rtt_swe_val;
  logic [32:0]                   grp15_rtt_swe_data;
  logic [7:0]                    grp15_rtt_swe_ext;
  logic                          grp15_rtt_swe_prdcr_en;
  logic                          grp16_rtt_swe_val;
  logic [32:0]                   grp16_rtt_swe_data;
  logic [7:0]                    grp16_rtt_swe_ext;
  logic                          grp16_rtt_swe_prdcr_en;

  `APBASYNCWIRES(16,32,nl2arc0_);
  `APBASYNCWIRES(16,32,nl2arc1_);

  //
  // NPU core instance
  //
  npu_core_pd
  u_npu_core_pd
  (
    // clock and reset
    .npu_core_clk                ( npu_core_clk              ),
    .nl2_rst_a                   ( nl2_rst_a                 ),
    .stu_err_irq_a               ( stu_err_irq_a             ),
    .grp0_scm_dbank_sbe                     (  grp0_scm_dbank_sbe        ),
    .grp0_scm_dbank_dbe                     (  grp0_scm_dbank_dbe        ),
    .grp1_scm_dbank_sbe                     (  grp1_scm_dbank_sbe        ),
    .grp1_scm_dbank_dbe                     (  grp1_scm_dbank_dbe        ),
    .grp2_scm_dbank_sbe                     (  grp2_scm_dbank_sbe        ),
    .grp2_scm_dbank_dbe                     (  grp2_scm_dbank_dbe        ),
    .grp3_scm_dbank_sbe                     (  grp3_scm_dbank_sbe        ),
    .grp3_scm_dbank_dbe                     (  grp3_scm_dbank_dbe        ),
    .nl2arc0_ecc_sbe                      ( nl2arc0_ecc_sbe ),
    .nl2arc0_ecc_dbe                      ( nl2arc0_ecc_dbe ),
    .nl2arc1_ecc_sbe                      ( nl2arc1_ecc_sbe ),
    .nl2arc1_ecc_dbe                      ( nl2arc1_ecc_dbe ),
    // per group clock enable, power-down and reset (at main clock)
    .grp0_rst_a               ( grp0_rst_a             ),
    .grp0_clk_en_a            ( grp0_clk_en_a          ),
    .grp0_evt_vm_irq          ( grp0_evt_vm_irq        ),
    .npu_grp0_vmid            ( npu_grp0_vmid          ),
    .grp1_rst_a               ( grp1_rst_a             ),
    .grp1_clk_en_a            ( grp1_clk_en_a          ),
    .grp1_evt_vm_irq          ( grp1_evt_vm_irq        ),
    .npu_grp1_vmid            ( npu_grp1_vmid          ),
    .grp2_rst_a               ( grp2_rst_a             ),
    .grp2_clk_en_a            ( grp2_clk_en_a          ),
    .grp2_evt_vm_irq          ( grp2_evt_vm_irq        ),
    .npu_grp2_vmid            ( npu_grp2_vmid          ),
    .grp3_rst_a               ( grp3_rst_a             ),
    .grp3_clk_en_a            ( grp3_clk_en_a          ),
    .grp3_evt_vm_irq          ( grp3_evt_vm_irq        ),
    .npu_grp3_vmid            ( npu_grp3_vmid          ),
    .nl2arc0_rst_a              ( nl2arc0_rst_a            ),
    .nl2arc0_clk_en_a           ( nl2arc0_clk_en_a         ),
    .nl2arc0_evt_vm_irq         ( nl2arc0_evt_vm_irq       ),
    .nl2arc0_pwr_dwn_a          ( nl2arc0_pwr_dwn_a        ),

    .nl2arc1_rst_a              ( nl2arc1_rst_a            ),
    .nl2arc1_clk_en_a           ( nl2arc1_clk_en_a         ),
    .nl2arc1_evt_vm_irq         ( nl2arc1_evt_vm_irq       ),
    .nl2arc1_pwr_dwn_a          ( nl2arc1_pwr_dwn_a        ),
    .ext_irq0_a                      ( ext_irq0_a                    ),
    .ext_irq1_a                      ( ext_irq1_a                    ),
    // per slice power-down and reset
    .sl0nl1arc_pwr_dwn_a   ( sl0nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl1nl1arc_pwr_dwn_a   ( sl1nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl2nl1arc_pwr_dwn_a   ( sl2nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl3nl1arc_pwr_dwn_a   ( sl3nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl4nl1arc_pwr_dwn_a   ( sl4nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl5nl1arc_pwr_dwn_a   ( sl5nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl6nl1arc_pwr_dwn_a   ( sl6nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl7nl1arc_pwr_dwn_a   ( sl7nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl8nl1arc_pwr_dwn_a   ( sl8nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl9nl1arc_pwr_dwn_a   ( sl9nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl10nl1arc_pwr_dwn_a   ( sl10nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl11nl1arc_pwr_dwn_a   ( sl11nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl12nl1arc_pwr_dwn_a   ( sl12nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl13nl1arc_pwr_dwn_a   ( sl13nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl14nl1arc_pwr_dwn_a   ( sl14nl1arc_pwr_dwn_a ),
    // per slice power-down and reset
    .sl15nl1arc_pwr_dwn_a   ( sl15nl1arc_pwr_dwn_a ),
    .grp0_pwr_dwn_a           ( grp0_pwr_dwn_a         ),
    .grp1_pwr_dwn_a           ( grp1_pwr_dwn_a         ),
    .grp2_pwr_dwn_a           ( grp2_pwr_dwn_a         ),
    .grp3_pwr_dwn_a           ( grp3_pwr_dwn_a         ),
    .nl2arc_isolate        ( nl2arc_isolate      ),
    .nl2arc_isolate_n      ( nl2arc_isolate_n    ),
    .nl2arc_pd_mem         ( nl2arc_pd_mem       ),
    .nl2arc_pd_logic       ( nl2arc_pd_logic     ),
    .grp0_isolate             ( grp0_isolate           ),
    .grp0_isolate_n           ( grp0_isolate_n         ),
    .grp0_pd_mem              ( grp0_pd_mem            ),
    .grp0_pd_logic            ( grp0_pd_logic          ),
    .grp1_isolate             ( grp1_isolate           ),
    .grp1_isolate_n           ( grp1_isolate_n         ),
    .grp1_pd_mem              ( grp1_pd_mem            ),
    .grp1_pd_logic            ( grp1_pd_logic          ),
    .grp2_isolate             ( grp2_isolate           ),
    .grp2_isolate_n           ( grp2_isolate_n         ),
    .grp2_pd_mem              ( grp2_pd_mem            ),
    .grp2_pd_logic            ( grp2_pd_logic          ),
    .grp3_isolate             ( grp3_isolate           ),
    .grp3_isolate_n           ( grp3_isolate_n         ),
    .grp3_pd_mem              ( grp3_pd_mem            ),
    .grp3_pd_logic            ( grp3_pd_logic          ),
    //-master axi
    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    `AXIASYNCMINST(l2arc_noc_axi_gals_,l2arc_noc_axi_gals_),
    `AXIASYNCMINST(npu_grp0_noc_axi_gals_,npu_grp0_noc_axi_gals_),
    `AXIASYNCMINST(npu_grp1_noc_axi_gals_,npu_grp1_noc_axi_gals_),
    `AXIASYNCMINST(npu_grp2_noc_axi_gals_,npu_grp2_noc_axi_gals_),
    `AXIASYNCMINST(npu_grp3_noc_axi_gals_,npu_grp3_noc_axi_gals_),

    //-slave dmi, clocked at npu_noc_clk, reset by npu_noc_rst_a
    `AXIASYNCSINST(dmi0_axi_gals_,dmi0_axi_gals_),

    // configuration slave AXI
    `AXIASYNCSINST(cfg_axi_gals_,cfg_axi_gals_),

    // async AXI interfaces
    `AXIASYNCSSUB(sl0nl1arc_dev_axi_gals_,sl0nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl0nl1arc_ccm_axi_gals_,sl0nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl1nl1arc_dev_axi_gals_,sl1nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl1nl1arc_ccm_axi_gals_,sl1nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl2nl1arc_dev_axi_gals_,sl2nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl2nl1arc_ccm_axi_gals_,sl2nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl3nl1arc_dev_axi_gals_,sl3nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl3nl1arc_ccm_axi_gals_,sl3nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl4nl1arc_dev_axi_gals_,sl4nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl4nl1arc_ccm_axi_gals_,sl4nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl5nl1arc_dev_axi_gals_,sl5nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl5nl1arc_ccm_axi_gals_,sl5nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl6nl1arc_dev_axi_gals_,sl6nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl6nl1arc_ccm_axi_gals_,sl6nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl7nl1arc_dev_axi_gals_,sl7nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl7nl1arc_ccm_axi_gals_,sl7nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl8nl1arc_dev_axi_gals_,sl8nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl8nl1arc_ccm_axi_gals_,sl8nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl9nl1arc_dev_axi_gals_,sl9nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl9nl1arc_ccm_axi_gals_,sl9nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl10nl1arc_dev_axi_gals_,sl10nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl10nl1arc_ccm_axi_gals_,sl10nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl11nl1arc_dev_axi_gals_,sl11nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl11nl1arc_ccm_axi_gals_,sl11nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl12nl1arc_dev_axi_gals_,sl12nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl12nl1arc_ccm_axi_gals_,sl12nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl13nl1arc_dev_axi_gals_,sl13nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl13nl1arc_ccm_axi_gals_,sl13nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl14nl1arc_dev_axi_gals_,sl14nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl14nl1arc_ccm_axi_gals_,sl14nl1arc_ccm_axi_gals_),
    // async AXI interfaces
    `AXIASYNCSSUB(sl15nl1arc_dev_axi_gals_,sl15nl1arc_dev_axi_gals_),
    `AXIASYNCMSUB(sl15nl1arc_ccm_axi_gals_,sl15nl1arc_ccm_axi_gals_),

    // Debug
    // L2 ARC0 debug interface
    .nl2arc0_dbg_cmdval_a       ( nl2arc0_dbg_cmdval       ),
    .nl2arc0_dbg_pack_a         ( nl2arc0_dbg_pack         ),
    .nl2arc0_dbg_resp           ( nl2arc0_dbg_resp         ),
    // L2 ARC1 debug interface
    .nl2arc1_dbg_cmdval_a       ( nl2arc1_dbg_cmdval       ),
    .nl2arc1_dbg_pack_a         ( nl2arc1_dbg_pack         ),
    .nl2arc1_dbg_resp           ( nl2arc1_dbg_resp         ),

    .l1_to_l2_event                  ( l1_to_l2_event            ),
    .l2_to_l1_event                  ( l2_to_l1_event            ),
    .npu_csm_base                    ( npu_csm_base              ),
    .grp4_rtt_swe_val             ( grp4_rtt_swe_val         ),
    .grp4_rtt_swe_data            ( grp4_rtt_swe_data        ),
    .grp4_rtt_swe_ext             ( grp4_rtt_swe_ext         ),
    .grp4_rtt_swe_prdcr_en        ( grp4_rtt_swe_prdcr_en    ),
    .grp5_rtt_swe_val             ( grp5_rtt_swe_val         ),
    .grp5_rtt_swe_data            ( grp5_rtt_swe_data        ),
    .grp5_rtt_swe_ext             ( grp5_rtt_swe_ext         ),
    .grp5_rtt_swe_prdcr_en        ( grp5_rtt_swe_prdcr_en    ),
    .grp6_rtt_swe_val             ( grp6_rtt_swe_val         ),
    .grp6_rtt_swe_data            ( grp6_rtt_swe_data        ),
    .grp6_rtt_swe_ext             ( grp6_rtt_swe_ext         ),
    .grp6_rtt_swe_prdcr_en        ( grp6_rtt_swe_prdcr_en    ),
    .grp7_rtt_swe_val             ( grp7_rtt_swe_val         ),
    .grp7_rtt_swe_data            ( grp7_rtt_swe_data        ),
    .grp7_rtt_swe_ext             ( grp7_rtt_swe_ext         ),
    .grp7_rtt_swe_prdcr_en        ( grp7_rtt_swe_prdcr_en    ),
    .grp8_rtt_swe_val             ( grp8_rtt_swe_val         ),
    .grp8_rtt_swe_data            ( grp8_rtt_swe_data        ),
    .grp8_rtt_swe_ext             ( grp8_rtt_swe_ext         ),
    .grp8_rtt_swe_prdcr_en        ( grp8_rtt_swe_prdcr_en    ),
    .grp9_rtt_swe_val             ( grp9_rtt_swe_val         ),
    .grp9_rtt_swe_data            ( grp9_rtt_swe_data        ),
    .grp9_rtt_swe_ext             ( grp9_rtt_swe_ext         ),
    .grp9_rtt_swe_prdcr_en        ( grp9_rtt_swe_prdcr_en    ),
    .grp10_rtt_swe_val             ( grp10_rtt_swe_val         ),
    .grp10_rtt_swe_data            ( grp10_rtt_swe_data        ),
    .grp10_rtt_swe_ext             ( grp10_rtt_swe_ext         ),
    .grp10_rtt_swe_prdcr_en        ( grp10_rtt_swe_prdcr_en    ),
    .grp11_rtt_swe_val             ( grp11_rtt_swe_val         ),
    .grp11_rtt_swe_data            ( grp11_rtt_swe_data        ),
    .grp11_rtt_swe_ext             ( grp11_rtt_swe_ext         ),
    .grp11_rtt_swe_prdcr_en        ( grp11_rtt_swe_prdcr_en    ),
    .grp12_rtt_swe_val             ( grp12_rtt_swe_val         ),
    .grp12_rtt_swe_data            ( grp12_rtt_swe_data        ),
    .grp12_rtt_swe_ext             ( grp12_rtt_swe_ext         ),
    .grp12_rtt_swe_prdcr_en        ( grp12_rtt_swe_prdcr_en    ),
    .grp13_rtt_swe_val             ( grp13_rtt_swe_val         ),
    .grp13_rtt_swe_data            ( grp13_rtt_swe_data        ),
    .grp13_rtt_swe_ext             ( grp13_rtt_swe_ext         ),
    .grp13_rtt_swe_prdcr_en        ( grp13_rtt_swe_prdcr_en    ),
    .grp14_rtt_swe_val             ( grp14_rtt_swe_val         ),
    .grp14_rtt_swe_data            ( grp14_rtt_swe_data        ),
    .grp14_rtt_swe_ext             ( grp14_rtt_swe_ext         ),
    .grp14_rtt_swe_prdcr_en        ( grp14_rtt_swe_prdcr_en    ),
    .grp15_rtt_swe_val             ( grp15_rtt_swe_val         ),
    .grp15_rtt_swe_data            ( grp15_rtt_swe_data        ),
    .grp15_rtt_swe_ext             ( grp15_rtt_swe_ext         ),
    .grp15_rtt_swe_prdcr_en        ( grp15_rtt_swe_prdcr_en    ),
    .grp16_rtt_swe_val             ( grp16_rtt_swe_val         ),
    .grp16_rtt_swe_data            ( grp16_rtt_swe_data        ),
    .grp16_rtt_swe_ext             ( grp16_rtt_swe_ext         ),
    .grp16_rtt_swe_prdcr_en        ( grp16_rtt_swe_prdcr_en    ),
    //ARC_Trace
    .at_clk_en                                 ( at_clk_en                     ),
    .at_rst_an                                 ( at_rst_an                     ),
    .atb_cstimestamp                           ( atb_cstimestamp               ),
    .atready                                   ( atready                       ),
    .atdata                                    ( atdata                        ),
    .atbytes                                   ( atbytes                       ),
    .atid                                      ( atid                          ),
    .atvalid                                   ( atvalid                       ),
    .afvalid                                   ( afvalid                       ),
    .afready                                   ( afready                       ),
    .syncreq                                   ( syncreq                       ),
    .swe_atready                               ( swe_atready                   ),
    .swe_atdata                                ( swe_atdata                    ),
    .swe_atbytes                               ( swe_atbytes                   ),
    .swe_atid                                  ( swe_atid                      ),
    .swe_atvalid                               ( swe_atvalid                   ),
    .swe_afvalid                               ( swe_afvalid                   ),
    .swe_afready                               ( swe_afready                   ),
    .swe_syncreq                               ( swe_syncreq                   ),
    .cti_rtt_filters                           ( cti_rtt_filters               ),
    .cti_trace_start                           ( cti_trace_start               ),
    .cti_trace_stop                            ( cti_trace_stop                ),
    `APBASYNCINST(arct_syn_,arct_syn_),
    .arct_dbgen                                ( arct0_dbgen                   ),
    .arct_niden                                ( arct0_niden                   ),
    .arct_dbg_prot_sel                         ( arct_dbg_prot_sel             ),
    .arct_rst_an                               ( arct_rst_an                   ),
    `APBASYNCINST(nl2arc0_,nl2arc0_),
    .nl2arc0_dbgen                        ( nl2arc0_dbgen            ),
    .nl2arc0_niden                        ( nl2arc0_niden            ),
    `APBASYNCINST(nl2arc1_,nl2arc1_),
    .nl2arc1_dbgen                        ( nl2arc1_dbgen            ),
    .nl2arc1_niden                        ( nl2arc1_niden            ),
    .sl0_rtt_swe_val                        ( sl0_rtt_swe_val            ),
    .sl0_rtt_swe_data                       ( sl0_rtt_swe_data           ),
    .sl0_rtt_swe_ext                        ( sl0_rtt_swe_ext            ),
    .sl1_rtt_swe_val                        ( sl1_rtt_swe_val            ),
    .sl1_rtt_swe_data                       ( sl1_rtt_swe_data           ),
    .sl1_rtt_swe_ext                        ( sl1_rtt_swe_ext            ),
    .sl2_rtt_swe_val                        ( sl2_rtt_swe_val            ),
    .sl2_rtt_swe_data                       ( sl2_rtt_swe_data           ),
    .sl2_rtt_swe_ext                        ( sl2_rtt_swe_ext            ),
    .sl3_rtt_swe_val                        ( sl3_rtt_swe_val            ),
    .sl3_rtt_swe_data                       ( sl3_rtt_swe_data           ),
    .sl3_rtt_swe_ext                        ( sl3_rtt_swe_ext            ),
    .sl4_rtt_swe_val                        ( sl4_rtt_swe_val            ),
    .sl4_rtt_swe_data                       ( sl4_rtt_swe_data           ),
    .sl4_rtt_swe_ext                        ( sl4_rtt_swe_ext            ),
    .sl5_rtt_swe_val                        ( sl5_rtt_swe_val            ),
    .sl5_rtt_swe_data                       ( sl5_rtt_swe_data           ),
    .sl5_rtt_swe_ext                        ( sl5_rtt_swe_ext            ),
    .sl6_rtt_swe_val                        ( sl6_rtt_swe_val            ),
    .sl6_rtt_swe_data                       ( sl6_rtt_swe_data           ),
    .sl6_rtt_swe_ext                        ( sl6_rtt_swe_ext            ),
    .sl7_rtt_swe_val                        ( sl7_rtt_swe_val            ),
    .sl7_rtt_swe_data                       ( sl7_rtt_swe_data           ),
    .sl7_rtt_swe_ext                        ( sl7_rtt_swe_ext            ),
    .sl8_rtt_swe_val                        ( sl8_rtt_swe_val            ),
    .sl8_rtt_swe_data                       ( sl8_rtt_swe_data           ),
    .sl8_rtt_swe_ext                        ( sl8_rtt_swe_ext            ),
    .sl9_rtt_swe_val                        ( sl9_rtt_swe_val            ),
    .sl9_rtt_swe_data                       ( sl9_rtt_swe_data           ),
    .sl9_rtt_swe_ext                        ( sl9_rtt_swe_ext            ),
    .sl10_rtt_swe_val                        ( sl10_rtt_swe_val            ),
    .sl10_rtt_swe_data                       ( sl10_rtt_swe_data           ),
    .sl10_rtt_swe_ext                        ( sl10_rtt_swe_ext            ),
    .sl11_rtt_swe_val                        ( sl11_rtt_swe_val            ),
    .sl11_rtt_swe_data                       ( sl11_rtt_swe_data           ),
    .sl11_rtt_swe_ext                        ( sl11_rtt_swe_ext            ),
    .sl12_rtt_swe_val                        ( sl12_rtt_swe_val            ),
    .sl12_rtt_swe_data                       ( sl12_rtt_swe_data           ),
    .sl12_rtt_swe_ext                        ( sl12_rtt_swe_ext            ),
    .sl13_rtt_swe_val                        ( sl13_rtt_swe_val            ),
    .sl13_rtt_swe_data                       ( sl13_rtt_swe_data           ),
    .sl13_rtt_swe_ext                        ( sl13_rtt_swe_ext            ),
    .sl14_rtt_swe_val                        ( sl14_rtt_swe_val            ),
    .sl14_rtt_swe_data                       ( sl14_rtt_swe_data           ),
    .sl14_rtt_swe_ext                        ( sl14_rtt_swe_ext            ),
    .sl15_rtt_swe_val                        ( sl15_rtt_swe_val            ),
    .sl15_rtt_swe_data                       ( sl15_rtt_swe_data           ),
    .sl15_rtt_swe_ext                        ( sl15_rtt_swe_ext            ),
    .nl2arc0_wdt_clk           ( nl2arc0_wdt_clk                   ),
    .nl2arc1_wdt_clk           ( nl2arc1_wdt_clk                   ),
    .nl2arc0_wdt_reset_error         ( nl2arc0_wdt_reset_error           ),
    .nl2arc0_wdt_reset_wdt_clk_error ( nl2arc0_wdt_reset_wdt_clk_error   ),
    .clusternum                           ( clusternum                    ),
    .nl2arc0_arcnum                  ( nl2arc0_arcnum           ),
    .nl2arc0_intvbase_in             ( nl2arc0_intvbase_in      ),
    .nl2arc0_arc_halt_req_a          ( nl2arc0_arc_halt_req_a   ),
    .nl2arc0_arc_halt_ack            ( nl2arc0_arc_halt_ack     ),
    .nl2arc0_arc_run_req_a           ( nl2arc0_arc_run_req_a    ),
    .nl2arc0_arc_run_ack             ( nl2arc0_arc_run_ack      ),
    .nl2arc0_sys_sleep_r             ( nl2arc0_sys_sleep_r      ),
    .nl2arc0_sys_sleep_mode_r        ( nl2arc0_sys_sleep_mode_r ),
    .nl2arc0_sys_halt_r              ( nl2arc0_sys_halt_r       ),
    .nl2arc0_sys_tf_halt_r           ( nl2arc0_sys_tf_halt_r    ),
    .nl2arc0_arc_irq_a               ( nl2arc0_arc_irq_a        ),
    .nl2arc0_arc_event_a             ( nl2arc0_arc_event_a      ),
    .nl2arc1_wdt_reset_error         ( nl2arc1_wdt_reset_error           ),
    .nl2arc1_wdt_reset_wdt_clk_error ( nl2arc1_wdt_reset_wdt_clk_error   ),
    .nl2arc1_arcnum                  ( nl2arc1_arcnum           ),
    .nl2arc1_intvbase_in             ( nl2arc1_intvbase_in      ),
    .nl2arc1_arc_halt_req_a          ( nl2arc1_arc_halt_req_a   ),
    .nl2arc1_arc_halt_ack            ( nl2arc1_arc_halt_ack     ),
    .nl2arc1_arc_run_req_a           ( nl2arc1_arc_run_req_a    ),
    .nl2arc1_arc_run_ack             ( nl2arc1_arc_run_ack      ),
    .nl2arc1_sys_sleep_r             ( nl2arc1_sys_sleep_r      ),
    .nl2arc1_sys_sleep_mode_r        ( nl2arc1_sys_sleep_mode_r ),
    .nl2arc1_sys_halt_r              ( nl2arc1_sys_halt_r       ),
    .nl2arc1_sys_tf_halt_r           ( nl2arc1_sys_tf_halt_r    ),
    .nl2arc1_arc_irq_a               ( nl2arc1_arc_irq_a        ),
    .nl2arc1_arc_event_a             ( nl2arc1_arc_event_a      ),

    .test_mode                              ( test_mode                 )
  );

  npu_core_aon
  u_npu_core_aon
   (
      .npu_core_clk                    ( npu_core_clk                )
    , .npu_core_rst_a                  ( npu_core_rst_a              )
    , .nl2arc0_arcnum             ( nl2arc0_arcnum         )
    , .nl2arc1_arcnum             ( nl2arc1_arcnum         )
    , .grp0_evt_vm_irq              ( grp0_evt_vm_irq          )
    , .grp1_evt_vm_irq              ( grp1_evt_vm_irq          )
    , .grp2_evt_vm_irq              ( grp2_evt_vm_irq          )
    , .grp3_evt_vm_irq              ( grp3_evt_vm_irq          )
    , `APBASYNCINST(sl0nl1arc_dbg_,sl0nl1arc_dbg_)
    , `APBASYNCINST(sl1nl1arc_dbg_,sl1nl1arc_dbg_)
    , `APBASYNCINST(sl2nl1arc_dbg_,sl2nl1arc_dbg_)
    , `APBASYNCINST(sl3nl1arc_dbg_,sl3nl1arc_dbg_)
    , `APBASYNCINST(sl4nl1arc_dbg_,sl4nl1arc_dbg_)
    , `APBASYNCINST(sl5nl1arc_dbg_,sl5nl1arc_dbg_)
    , `APBASYNCINST(sl6nl1arc_dbg_,sl6nl1arc_dbg_)
    , `APBASYNCINST(sl7nl1arc_dbg_,sl7nl1arc_dbg_)
    , `APBASYNCINST(sl8nl1arc_dbg_,sl8nl1arc_dbg_)
    , `APBASYNCINST(sl9nl1arc_dbg_,sl9nl1arc_dbg_)
    , `APBASYNCINST(sl10nl1arc_dbg_,sl10nl1arc_dbg_)
    , `APBASYNCINST(sl11nl1arc_dbg_,sl11nl1arc_dbg_)
    , `APBASYNCINST(sl12nl1arc_dbg_,sl12nl1arc_dbg_)
    , `APBASYNCINST(sl13nl1arc_dbg_,sl13nl1arc_dbg_)
    , `APBASYNCINST(sl14nl1arc_dbg_,sl14nl1arc_dbg_)
    , `APBASYNCINST(sl15nl1arc_dbg_,sl15nl1arc_dbg_)
    ,.arct_clk                         ( arct_clk                    )
    ,.arct_rst_an                      ( arct_rst_an                 )
    ,`APBINST(arct_,arct_)
    ,`APBASYNCINST(nl2arc0_,nl2arc0_)
    ,`APBASYNCINST(nl2arc1_,nl2arc1_)
    , .sl0nl1arc_arcnum           ( sl0nl1arc_arcnum       )
    , .sl0nl1arc_evt_vm_irq_a     ( sl0nl1arc_evt_vm_irq_a )
    , .sl0nl1arc_pwr_dwn_a        ( sl0nl1arc_pwr_dwn_a    )
    , .sl1nl1arc_arcnum           ( sl1nl1arc_arcnum       )
    , .sl1nl1arc_evt_vm_irq_a     ( sl1nl1arc_evt_vm_irq_a )
    , .sl1nl1arc_pwr_dwn_a        ( sl1nl1arc_pwr_dwn_a    )
    , .sl2nl1arc_arcnum           ( sl2nl1arc_arcnum       )
    , .sl2nl1arc_evt_vm_irq_a     ( sl2nl1arc_evt_vm_irq_a )
    , .sl2nl1arc_pwr_dwn_a        ( sl2nl1arc_pwr_dwn_a    )
    , .sl3nl1arc_arcnum           ( sl3nl1arc_arcnum       )
    , .sl3nl1arc_evt_vm_irq_a     ( sl3nl1arc_evt_vm_irq_a )
    , .sl3nl1arc_pwr_dwn_a        ( sl3nl1arc_pwr_dwn_a    )
    , .sl4nl1arc_arcnum           ( sl4nl1arc_arcnum       )
    , .sl4nl1arc_evt_vm_irq_a     ( sl4nl1arc_evt_vm_irq_a )
    , .sl4nl1arc_pwr_dwn_a        ( sl4nl1arc_pwr_dwn_a    )
    , .sl5nl1arc_arcnum           ( sl5nl1arc_arcnum       )
    , .sl5nl1arc_evt_vm_irq_a     ( sl5nl1arc_evt_vm_irq_a )
    , .sl5nl1arc_pwr_dwn_a        ( sl5nl1arc_pwr_dwn_a    )
    , .sl6nl1arc_arcnum           ( sl6nl1arc_arcnum       )
    , .sl6nl1arc_evt_vm_irq_a     ( sl6nl1arc_evt_vm_irq_a )
    , .sl6nl1arc_pwr_dwn_a        ( sl6nl1arc_pwr_dwn_a    )
    , .sl7nl1arc_arcnum           ( sl7nl1arc_arcnum       )
    , .sl7nl1arc_evt_vm_irq_a     ( sl7nl1arc_evt_vm_irq_a )
    , .sl7nl1arc_pwr_dwn_a        ( sl7nl1arc_pwr_dwn_a    )
    , .sl8nl1arc_arcnum           ( sl8nl1arc_arcnum       )
    , .sl8nl1arc_evt_vm_irq_a     ( sl8nl1arc_evt_vm_irq_a )
    , .sl8nl1arc_pwr_dwn_a        ( sl8nl1arc_pwr_dwn_a    )
    , .sl9nl1arc_arcnum           ( sl9nl1arc_arcnum       )
    , .sl9nl1arc_evt_vm_irq_a     ( sl9nl1arc_evt_vm_irq_a )
    , .sl9nl1arc_pwr_dwn_a        ( sl9nl1arc_pwr_dwn_a    )
    , .sl10nl1arc_arcnum           ( sl10nl1arc_arcnum       )
    , .sl10nl1arc_evt_vm_irq_a     ( sl10nl1arc_evt_vm_irq_a )
    , .sl10nl1arc_pwr_dwn_a        ( sl10nl1arc_pwr_dwn_a    )
    , .sl11nl1arc_arcnum           ( sl11nl1arc_arcnum       )
    , .sl11nl1arc_evt_vm_irq_a     ( sl11nl1arc_evt_vm_irq_a )
    , .sl11nl1arc_pwr_dwn_a        ( sl11nl1arc_pwr_dwn_a    )
    , .sl12nl1arc_arcnum           ( sl12nl1arc_arcnum       )
    , .sl12nl1arc_evt_vm_irq_a     ( sl12nl1arc_evt_vm_irq_a )
    , .sl12nl1arc_pwr_dwn_a        ( sl12nl1arc_pwr_dwn_a    )
    , .sl13nl1arc_arcnum           ( sl13nl1arc_arcnum       )
    , .sl13nl1arc_evt_vm_irq_a     ( sl13nl1arc_evt_vm_irq_a )
    , .sl13nl1arc_pwr_dwn_a        ( sl13nl1arc_pwr_dwn_a    )
    , .sl14nl1arc_arcnum           ( sl14nl1arc_arcnum       )
    , .sl14nl1arc_evt_vm_irq_a     ( sl14nl1arc_evt_vm_irq_a )
    , .sl14nl1arc_pwr_dwn_a        ( sl14nl1arc_pwr_dwn_a    )
    , .sl15nl1arc_arcnum           ( sl15nl1arc_arcnum       )
    , .sl15nl1arc_evt_vm_irq_a     ( sl15nl1arc_evt_vm_irq_a )
    , .sl15nl1arc_pwr_dwn_a        ( sl15nl1arc_pwr_dwn_a    )
    , .nl2arc_pwr_dwn_a           ( nl2arc_pwr_dwn_a       )
    // ARC_Trace
    , `APBASYNCINST(arct_syn_,arct_syn_)
    , .grp4_rtt_swe_val             ( grp4_rtt_swe_val         )
    , .grp4_rtt_swe_data            ( grp4_rtt_swe_data        )
    , .grp4_rtt_swe_ext             ( grp4_rtt_swe_ext         )
    , .grp5_rtt_swe_val             ( grp5_rtt_swe_val         )
    , .grp5_rtt_swe_data            ( grp5_rtt_swe_data        )
    , .grp5_rtt_swe_ext             ( grp5_rtt_swe_ext         )
    , .grp6_rtt_swe_val             ( grp6_rtt_swe_val         )
    , .grp6_rtt_swe_data            ( grp6_rtt_swe_data        )
    , .grp6_rtt_swe_ext             ( grp6_rtt_swe_ext         )
    , .grp7_rtt_swe_val             ( grp7_rtt_swe_val         )
    , .grp7_rtt_swe_data            ( grp7_rtt_swe_data        )
    , .grp7_rtt_swe_ext             ( grp7_rtt_swe_ext         )
    , .grp8_rtt_swe_val             ( grp8_rtt_swe_val         )
    , .grp8_rtt_swe_data            ( grp8_rtt_swe_data        )
    , .grp8_rtt_swe_ext             ( grp8_rtt_swe_ext         )
    , .grp9_rtt_swe_val             ( grp9_rtt_swe_val         )
    , .grp9_rtt_swe_data            ( grp9_rtt_swe_data        )
    , .grp9_rtt_swe_ext             ( grp9_rtt_swe_ext         )
    , .grp10_rtt_swe_val             ( grp10_rtt_swe_val         )
    , .grp10_rtt_swe_data            ( grp10_rtt_swe_data        )
    , .grp10_rtt_swe_ext             ( grp10_rtt_swe_ext         )
    , .grp11_rtt_swe_val             ( grp11_rtt_swe_val         )
    , .grp11_rtt_swe_data            ( grp11_rtt_swe_data        )
    , .grp11_rtt_swe_ext             ( grp11_rtt_swe_ext         )
    , .grp12_rtt_swe_val             ( grp12_rtt_swe_val         )
    , .grp12_rtt_swe_data            ( grp12_rtt_swe_data        )
    , .grp12_rtt_swe_ext             ( grp12_rtt_swe_ext         )
    , .grp13_rtt_swe_val             ( grp13_rtt_swe_val         )
    , .grp13_rtt_swe_data            ( grp13_rtt_swe_data        )
    , .grp13_rtt_swe_ext             ( grp13_rtt_swe_ext         )
    , .grp14_rtt_swe_val             ( grp14_rtt_swe_val         )
    , .grp14_rtt_swe_data            ( grp14_rtt_swe_data        )
    , .grp14_rtt_swe_ext             ( grp14_rtt_swe_ext         )
    , .grp15_rtt_swe_val             ( grp15_rtt_swe_val         )
    , .grp15_rtt_swe_data            ( grp15_rtt_swe_data        )
    , .grp15_rtt_swe_ext             ( grp15_rtt_swe_ext         )
    , .grp16_rtt_swe_val             ( grp16_rtt_swe_val         )
    , .grp16_rtt_swe_data            ( grp16_rtt_swe_data        )
    , .grp16_rtt_swe_ext             ( grp16_rtt_swe_ext         )
// spyglass disable_block NoFeedThrus-ML
// SMD: No Feed Through
// SJ : The L1 peers event are shuffled only
    , .l1_peer_event_out               ( l1_peer_event_out           )
    , .l1_peer_event_in                ( l1_peer_event_in            )
// spyglass enable_block NoFeedThrus-ML
    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst17_axi
    // read command channel
  , .npu_mst0_axi_arvalid            (npu_mst0_axi_arvalid)     // read command valid
  , .npu_mst0_axi_arready            (npu_mst0_axi_arready)     // read command accept
  , .npu_mst0_axi_arid               (npu_mst0_axi_arid   )     // read command ID
  , .npu_mst0_axi_araddr  (npu_mst0_axi_araddr  )   // read command
  , .npu_mst0_axi_arcache (npu_mst0_axi_arcache )   // read command
  , .npu_mst0_axi_arprot  (npu_mst0_axi_arprot  )   // read command
  , .npu_mst0_axi_arlock  (npu_mst0_axi_arlock  )   // read command
  , .npu_mst0_axi_arburst (npu_mst0_axi_arburst )   // read command
  , .npu_mst0_axi_arlen   (npu_mst0_axi_arlen   )   // read command
  , .npu_mst0_axi_arsize  (npu_mst0_axi_arsize  )   // read command
  , .npu_mst0_axi_rvalid  (npu_mst0_axi_rvalid )    // read data valid
  , .npu_mst0_axi_rready  (npu_mst0_axi_rready )    // read data accept
  , .npu_mst0_axi_rid     (npu_mst0_axi_rid    )    // read data id
  , .npu_mst0_axi_rdata   (npu_mst0_axi_rdata  )    // read data
  , .npu_mst0_axi_rresp   (npu_mst0_axi_rresp)    // read response
  , .npu_mst0_axi_rlast   (npu_mst0_axi_rlast  )    // read last
  , .npu_mst0_axi_awvalid (npu_mst0_axi_awvalid )   // write command valid
  , .npu_mst0_axi_awready (npu_mst0_axi_awready )   // write command accept
  , .npu_mst0_axi_awid    (npu_mst0_axi_awid    )   // write command ID
  , .npu_mst0_axi_awaddr  (npu_mst0_axi_awaddr  )   // read command
  , .npu_mst0_axi_awcache (npu_mst0_axi_awcache )   // read command
  , .npu_mst0_axi_awprot  (npu_mst0_axi_awprot  )   // read command
  , .npu_mst0_axi_awlock  (npu_mst0_axi_awlock  )   // read command
  , .npu_mst0_axi_awburst (npu_mst0_axi_awburst )   // read command
  , .npu_mst0_axi_awlen   (npu_mst0_axi_awlen   )   // read command
  , .npu_mst0_axi_awsize  (npu_mst0_axi_awsize  )   // read command
  , .npu_mst0_axi_wvalid  (npu_mst0_axi_wvalid  )   // write data valid
  , .npu_mst0_axi_wready  (npu_mst0_axi_wready  )   // write data accept
  , .npu_mst0_axi_wdata   (npu_mst0_axi_wdata   )   // write data
  , .npu_mst0_axi_wstrb   (npu_mst0_axi_wstrb   )   // write data strobe
  , .npu_mst0_axi_wlast   (npu_mst0_axi_wlast   )   // write data last
  , .npu_mst0_axi_bvalid  (npu_mst0_axi_bvalid  )   // write response valid
  , .npu_mst0_axi_bready  (npu_mst0_axi_bready  )   // write response accept
  , .npu_mst0_axi_bid     (npu_mst0_axi_bid     )   // write response id
  , .npu_mst0_axi_bresp   (npu_mst0_axi_bresp)    // read response
    //-slave dmi, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-npu_dmi0_axi
    //axislv(1/*idw*/,`aw,`ISIZE*32/*dw*/,1/*argw*/,1/*awgw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/,0/*awcpl*/, npu_dmi0_axi_/*prefix*/)
    // read command channel
  , .npu_dmi0_axi_arvalid            (npu_dmi0_axi_arvalid)     // read command valid
  , .npu_dmi0_axi_arready            (npu_dmi0_axi_arready)     // read command accept
  , .npu_dmi0_axi_arid               (npu_dmi0_axi_arid   )     // read command ID
  , .npu_dmi0_axi_araddr  (npu_dmi0_axi_araddr  )   // read command
  , .npu_dmi0_axi_arcache (npu_dmi0_axi_arcache )   // read command
  , .npu_dmi0_axi_arprot  (npu_dmi0_axi_arprot  )   // read command
  , .npu_dmi0_axi_arlock  (npu_dmi0_axi_arlock  )   // read command
  , .npu_dmi0_axi_arburst (npu_dmi0_axi_arburst )   // read command
  , .npu_dmi0_axi_arlen   (npu_dmi0_axi_arlen   )   // read command
  , .npu_dmi0_axi_arsize  (npu_dmi0_axi_arsize  )   // read command
  , .npu_dmi0_axi_rvalid  (npu_dmi0_axi_rvalid )    // read data valid
  , .npu_dmi0_axi_rready  (npu_dmi0_axi_rready )    // read data accept
  , .npu_dmi0_axi_rid     (npu_dmi0_axi_rid    )    // read data id
  , .npu_dmi0_axi_rdata   (npu_dmi0_axi_rdata  )    // read data
  , .npu_dmi0_axi_rresp   (npu_dmi0_axi_rresp)    // read response
  , .npu_dmi0_axi_rlast   (npu_dmi0_axi_rlast  )    // read last
  , .npu_dmi0_axi_awvalid (npu_dmi0_axi_awvalid )   // write command valid
  , .npu_dmi0_axi_awready (npu_dmi0_axi_awready )   // write command accept
  , .npu_dmi0_axi_awid    (npu_dmi0_axi_awid    )   // write command ID
  , .npu_dmi0_axi_awaddr  (npu_dmi0_axi_awaddr  )   // read command
  , .npu_dmi0_axi_awcache (npu_dmi0_axi_awcache )   // read command
  , .npu_dmi0_axi_awprot  (npu_dmi0_axi_awprot  )   // read command
  , .npu_dmi0_axi_awlock  (npu_dmi0_axi_awlock  )   // read command
  , .npu_dmi0_axi_awburst (npu_dmi0_axi_awburst )   // read command
  , .npu_dmi0_axi_awlen   (npu_dmi0_axi_awlen   )   // read command
  , .npu_dmi0_axi_awsize  (npu_dmi0_axi_awsize  )   // read command
  , .npu_dmi0_axi_wvalid  (npu_dmi0_axi_wvalid  )   // write data valid
  , .npu_dmi0_axi_wready  (npu_dmi0_axi_wready  )   // write data accept
  , .npu_dmi0_axi_wdata   (npu_dmi0_axi_wdata   )   // write data
  , .npu_dmi0_axi_wstrb   (npu_dmi0_axi_wstrb   )   // write data strobe
  , .npu_dmi0_axi_wlast   (npu_dmi0_axi_wlast   )   // write data last
  , .npu_dmi0_axi_bvalid  (npu_dmi0_axi_bvalid  )   // write response valid
  , .npu_dmi0_axi_bready  (npu_dmi0_axi_bready  )   // write response accept
  , .npu_dmi0_axi_bid     (npu_dmi0_axi_bid     )   // write response id
  , .npu_dmi0_axi_bresp   (npu_dmi0_axi_bresp)    // read response
    // Async bridge && reset ctrl
    , .npu_noc_clk                     ( npu_noc_clk                 )
    , .npu_noc_rst_a                   ( npu_noc_rst_a               )
    , .npu_cfg_clk                     ( npu_cfg_clk                 )
    , .npu_cfg_rst_a                   ( npu_cfg_rst_a               )
    , .stu_err_irq_a                   ( stu_err_irq_a               )
    , .sl0nl1arc_dbg_cmdval     ( sl0nl1arc_dbg_cmdval   )
    , .sl0nl1arc_dbg_pack       ( sl0nl1arc_dbg_pack     )
    , .sl0nl1arc_dbg_resp       ( sl0nl1arc_dbg_resp     )
    , .sl1nl1arc_dbg_cmdval     ( sl1nl1arc_dbg_cmdval   )
    , .sl1nl1arc_dbg_pack       ( sl1nl1arc_dbg_pack     )
    , .sl1nl1arc_dbg_resp       ( sl1nl1arc_dbg_resp     )
    , .sl2nl1arc_dbg_cmdval     ( sl2nl1arc_dbg_cmdval   )
    , .sl2nl1arc_dbg_pack       ( sl2nl1arc_dbg_pack     )
    , .sl2nl1arc_dbg_resp       ( sl2nl1arc_dbg_resp     )
    , .sl3nl1arc_dbg_cmdval     ( sl3nl1arc_dbg_cmdval   )
    , .sl3nl1arc_dbg_pack       ( sl3nl1arc_dbg_pack     )
    , .sl3nl1arc_dbg_resp       ( sl3nl1arc_dbg_resp     )
    , .sl4nl1arc_dbg_cmdval     ( sl4nl1arc_dbg_cmdval   )
    , .sl4nl1arc_dbg_pack       ( sl4nl1arc_dbg_pack     )
    , .sl4nl1arc_dbg_resp       ( sl4nl1arc_dbg_resp     )
    , .sl5nl1arc_dbg_cmdval     ( sl5nl1arc_dbg_cmdval   )
    , .sl5nl1arc_dbg_pack       ( sl5nl1arc_dbg_pack     )
    , .sl5nl1arc_dbg_resp       ( sl5nl1arc_dbg_resp     )
    , .sl6nl1arc_dbg_cmdval     ( sl6nl1arc_dbg_cmdval   )
    , .sl6nl1arc_dbg_pack       ( sl6nl1arc_dbg_pack     )
    , .sl6nl1arc_dbg_resp       ( sl6nl1arc_dbg_resp     )
    , .sl7nl1arc_dbg_cmdval     ( sl7nl1arc_dbg_cmdval   )
    , .sl7nl1arc_dbg_pack       ( sl7nl1arc_dbg_pack     )
    , .sl7nl1arc_dbg_resp       ( sl7nl1arc_dbg_resp     )
    , .sl8nl1arc_dbg_cmdval     ( sl8nl1arc_dbg_cmdval   )
    , .sl8nl1arc_dbg_pack       ( sl8nl1arc_dbg_pack     )
    , .sl8nl1arc_dbg_resp       ( sl8nl1arc_dbg_resp     )
    , .sl9nl1arc_dbg_cmdval     ( sl9nl1arc_dbg_cmdval   )
    , .sl9nl1arc_dbg_pack       ( sl9nl1arc_dbg_pack     )
    , .sl9nl1arc_dbg_resp       ( sl9nl1arc_dbg_resp     )
    , .sl10nl1arc_dbg_cmdval     ( sl10nl1arc_dbg_cmdval   )
    , .sl10nl1arc_dbg_pack       ( sl10nl1arc_dbg_pack     )
    , .sl10nl1arc_dbg_resp       ( sl10nl1arc_dbg_resp     )
    , .sl11nl1arc_dbg_cmdval     ( sl11nl1arc_dbg_cmdval   )
    , .sl11nl1arc_dbg_pack       ( sl11nl1arc_dbg_pack     )
    , .sl11nl1arc_dbg_resp       ( sl11nl1arc_dbg_resp     )
    , .sl12nl1arc_dbg_cmdval     ( sl12nl1arc_dbg_cmdval   )
    , .sl12nl1arc_dbg_pack       ( sl12nl1arc_dbg_pack     )
    , .sl12nl1arc_dbg_resp       ( sl12nl1arc_dbg_resp     )
    , .sl13nl1arc_dbg_cmdval     ( sl13nl1arc_dbg_cmdval   )
    , .sl13nl1arc_dbg_pack       ( sl13nl1arc_dbg_pack     )
    , .sl13nl1arc_dbg_resp       ( sl13nl1arc_dbg_resp     )
    , .sl14nl1arc_dbg_cmdval     ( sl14nl1arc_dbg_cmdval   )
    , .sl14nl1arc_dbg_pack       ( sl14nl1arc_dbg_pack     )
    , .sl14nl1arc_dbg_resp       ( sl14nl1arc_dbg_resp     )
    , .sl15nl1arc_dbg_cmdval     ( sl15nl1arc_dbg_cmdval   )
    , .sl15nl1arc_dbg_pack       ( sl15nl1arc_dbg_pack     )
    , .sl15nl1arc_dbg_resp       ( sl15nl1arc_dbg_resp     )
    // L2 ARC0 debug interface
    , .nl2arc0_dbg_cmdval         ( nl2arc0_dbg_cmdval     )
    , .nl2arc0_dbg_pack           ( nl2arc0_dbg_pack       )
    , .nl2arc0_dbg_resp           ( nl2arc0_dbg_resp       )
    // L2 ARC1 debug interface
    , .nl2arc1_dbg_cmdval         ( nl2arc1_dbg_cmdval     )
    , .nl2arc1_dbg_pack           ( nl2arc1_dbg_pack       )
    , .nl2arc1_dbg_resp           ( nl2arc1_dbg_resp       )
    // configuration slave AXI
    //axislv(1/*idw*/,`aw,`ISIZE*32/*dw*/,1/*argw*/,1/*awgw*/,1/*awuw*/,1/*wuw*/,1/*buw*/,1/*aruw*/,1/*ruw*/, 0/*arcpl*/,0/*awcpl*/, npu_cfg_axi_/*prefix*/)
    // read command channel
  , .npu_cfg_axi_arvalid            (npu_cfg_axi_arvalid)     // read command valid
  , .npu_cfg_axi_arready            (npu_cfg_axi_arready)     // read command accept
  , .npu_cfg_axi_arid               (npu_cfg_axi_arid   )     // read command ID
  , .npu_cfg_axi_araddr  (npu_cfg_axi_araddr  )   // read command
  , .npu_cfg_axi_arcache (npu_cfg_axi_arcache )   // read command
  , .npu_cfg_axi_arprot  (npu_cfg_axi_arprot  )   // read command
  , .npu_cfg_axi_arlock  (npu_cfg_axi_arlock  )   // read command
  , .npu_cfg_axi_arburst (npu_cfg_axi_arburst )   // read command
  , .npu_cfg_axi_arlen   (npu_cfg_axi_arlen   )   // read command
  , .npu_cfg_axi_arsize  (npu_cfg_axi_arsize  )   // read command
  , .npu_cfg_axi_rvalid  (npu_cfg_axi_rvalid )    // read data valid
  , .npu_cfg_axi_rready  (npu_cfg_axi_rready )    // read data accept
  , .npu_cfg_axi_rid     (npu_cfg_axi_rid    )    // read data id
  , .npu_cfg_axi_rdata   (npu_cfg_axi_rdata  )    // read data
  , .npu_cfg_axi_rresp   (npu_cfg_axi_rresp)    // read response
  , .npu_cfg_axi_rlast   (npu_cfg_axi_rlast  )    // read last
  , .npu_cfg_axi_awvalid (npu_cfg_axi_awvalid )   // write command valid
  , .npu_cfg_axi_awready (npu_cfg_axi_awready )   // write command accept
  , .npu_cfg_axi_awid    (npu_cfg_axi_awid    )   // write command ID
  , .npu_cfg_axi_awaddr  (npu_cfg_axi_awaddr  )   // read command
  , .npu_cfg_axi_awcache (npu_cfg_axi_awcache )   // read command
  , .npu_cfg_axi_awprot  (npu_cfg_axi_awprot  )   // read command
  , .npu_cfg_axi_awlock  (npu_cfg_axi_awlock  )   // read command
  , .npu_cfg_axi_awburst (npu_cfg_axi_awburst )   // read command
  , .npu_cfg_axi_awlen   (npu_cfg_axi_awlen   )   // read command
  , .npu_cfg_axi_awsize  (npu_cfg_axi_awsize  )   // read command
  , .npu_cfg_axi_wvalid  (npu_cfg_axi_wvalid  )   // write data valid
  , .npu_cfg_axi_wready  (npu_cfg_axi_wready  )   // write data accept
  , .npu_cfg_axi_wdata   (npu_cfg_axi_wdata   )   // write data
  , .npu_cfg_axi_wstrb   (npu_cfg_axi_wstrb   )   // write data strobe
  , .npu_cfg_axi_wlast   (npu_cfg_axi_wlast   )   // write data last
  , .npu_cfg_axi_bvalid  (npu_cfg_axi_bvalid  )   // write response valid
  , .npu_cfg_axi_bready  (npu_cfg_axi_bready  )   // write response accept
  , .npu_cfg_axi_bid     (npu_cfg_axi_bid     )   // write response id
  , .npu_cfg_axi_bresp   (npu_cfg_axi_bresp)    // read response
    ,
    `AXIASYNCSINST(l2arc_noc_axi_gals_,l2arc_noc_axi_gals_),
    `AXIASYNCMINST(dmi0_axi_gals_,dmi0_axi_gals_),
    `AXIASYNCMINST(cfg_axi_gals_,cfg_axi_gals_),
    .test_mode                        ( test_mode                 )
  , .grp0_rst_a          ( grp0_rst_a         )
  , .grp0_pwr_dwn_a      ( grp0_pwr_dwn_a         )

    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst1_axi_arvalid            (npu_mst1_axi_arvalid)     // read command valid
  , .npu_mst1_axi_arready            (npu_mst1_axi_arready)     // read command accept
  , .npu_mst1_axi_arid               (npu_mst1_axi_arid   )     // read command ID
  , .npu_mst1_axi_araddr  (npu_mst1_axi_araddr  )   // read command
  , .npu_mst1_axi_arcache (npu_mst1_axi_arcache )   // read command
  , .npu_mst1_axi_arprot  (npu_mst1_axi_arprot  )   // read command
  , .npu_mst1_axi_arlock  (npu_mst1_axi_arlock  )   // read command
  , .npu_mst1_axi_arburst (npu_mst1_axi_arburst )   // read command
  , .npu_mst1_axi_arlen   (npu_mst1_axi_arlen   )   // read command
  , .npu_mst1_axi_arsize  (npu_mst1_axi_arsize  )   // read command
  , .npu_mst1_axi_arsid(npu_mst1_axi_arsid)   // read command
  , .npu_mst1_axi_arssid(npu_mst1_axi_arssid)   // read command
  , .npu_mst1_axi_rvalid  (npu_mst1_axi_rvalid )    // read data valid
  , .npu_mst1_axi_rready  (npu_mst1_axi_rready )    // read data accept
  , .npu_mst1_axi_rid     (npu_mst1_axi_rid    )    // read data id
  , .npu_mst1_axi_rdata   (npu_mst1_axi_rdata  )    // read data
  , .npu_mst1_axi_rresp   (npu_mst1_axi_rresp)    // read response
  , .npu_mst1_axi_rlast   (npu_mst1_axi_rlast  )    // read last
  , .npu_mst1_axi_awvalid (npu_mst1_axi_awvalid )   // write command valid
  , .npu_mst1_axi_awready (npu_mst1_axi_awready )   // write command accept
  , .npu_mst1_axi_awid    (npu_mst1_axi_awid    )   // write command ID
  , .npu_mst1_axi_awaddr  (npu_mst1_axi_awaddr  )   // read command
  , .npu_mst1_axi_awcache (npu_mst1_axi_awcache )   // read command
  , .npu_mst1_axi_awprot  (npu_mst1_axi_awprot  )   // read command
  , .npu_mst1_axi_awlock  (npu_mst1_axi_awlock  )   // read command
  , .npu_mst1_axi_awburst (npu_mst1_axi_awburst )   // read command
  , .npu_mst1_axi_awlen   (npu_mst1_axi_awlen   )   // read command
  , .npu_mst1_axi_awsize  (npu_mst1_axi_awsize  )   // read command
  , .npu_mst1_axi_awsid(npu_mst1_axi_awsid)     // read command
  , .npu_mst1_axi_awssid(npu_mst1_axi_awssid)   // read command
  , .npu_mst1_axi_wvalid  (npu_mst1_axi_wvalid  )   // write data valid
  , .npu_mst1_axi_wready  (npu_mst1_axi_wready  )   // write data accept
  , .npu_mst1_axi_wdata   (npu_mst1_axi_wdata   )   // write data
  , .npu_mst1_axi_wstrb   (npu_mst1_axi_wstrb   )   // write data strobe
  , .npu_mst1_axi_wlast   (npu_mst1_axi_wlast   )   // write data last
  , .npu_mst1_axi_bvalid  (npu_mst1_axi_bvalid  )   // write response valid
  , .npu_mst1_axi_bready  (npu_mst1_axi_bready  )   // write response accept
  , .npu_mst1_axi_bid     (npu_mst1_axi_bid     )   // write response id
  , .npu_mst1_axi_bresp   (npu_mst1_axi_bresp)    // read response
   , `AXIASYNCSINST(npu_grp0_noc_axi_gals_,npu_grp0_noc_axi_gals_)
  , .grp1_rst_a          ( grp1_rst_a         )
  , .grp1_pwr_dwn_a      ( grp1_pwr_dwn_a         )

    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst2_axi_arvalid            (npu_mst2_axi_arvalid)     // read command valid
  , .npu_mst2_axi_arready            (npu_mst2_axi_arready)     // read command accept
  , .npu_mst2_axi_arid               (npu_mst2_axi_arid   )     // read command ID
  , .npu_mst2_axi_araddr  (npu_mst2_axi_araddr  )   // read command
  , .npu_mst2_axi_arcache (npu_mst2_axi_arcache )   // read command
  , .npu_mst2_axi_arprot  (npu_mst2_axi_arprot  )   // read command
  , .npu_mst2_axi_arlock  (npu_mst2_axi_arlock  )   // read command
  , .npu_mst2_axi_arburst (npu_mst2_axi_arburst )   // read command
  , .npu_mst2_axi_arlen   (npu_mst2_axi_arlen   )   // read command
  , .npu_mst2_axi_arsize  (npu_mst2_axi_arsize  )   // read command
  , .npu_mst2_axi_arsid(npu_mst2_axi_arsid)   // read command
  , .npu_mst2_axi_arssid(npu_mst2_axi_arssid)   // read command
  , .npu_mst2_axi_rvalid  (npu_mst2_axi_rvalid )    // read data valid
  , .npu_mst2_axi_rready  (npu_mst2_axi_rready )    // read data accept
  , .npu_mst2_axi_rid     (npu_mst2_axi_rid    )    // read data id
  , .npu_mst2_axi_rdata   (npu_mst2_axi_rdata  )    // read data
  , .npu_mst2_axi_rresp   (npu_mst2_axi_rresp)    // read response
  , .npu_mst2_axi_rlast   (npu_mst2_axi_rlast  )    // read last
  , .npu_mst2_axi_awvalid (npu_mst2_axi_awvalid )   // write command valid
  , .npu_mst2_axi_awready (npu_mst2_axi_awready )   // write command accept
  , .npu_mst2_axi_awid    (npu_mst2_axi_awid    )   // write command ID
  , .npu_mst2_axi_awaddr  (npu_mst2_axi_awaddr  )   // read command
  , .npu_mst2_axi_awcache (npu_mst2_axi_awcache )   // read command
  , .npu_mst2_axi_awprot  (npu_mst2_axi_awprot  )   // read command
  , .npu_mst2_axi_awlock  (npu_mst2_axi_awlock  )   // read command
  , .npu_mst2_axi_awburst (npu_mst2_axi_awburst )   // read command
  , .npu_mst2_axi_awlen   (npu_mst2_axi_awlen   )   // read command
  , .npu_mst2_axi_awsize  (npu_mst2_axi_awsize  )   // read command
  , .npu_mst2_axi_awsid(npu_mst2_axi_awsid)     // read command
  , .npu_mst2_axi_awssid(npu_mst2_axi_awssid)   // read command
  , .npu_mst2_axi_wvalid  (npu_mst2_axi_wvalid  )   // write data valid
  , .npu_mst2_axi_wready  (npu_mst2_axi_wready  )   // write data accept
  , .npu_mst2_axi_wdata   (npu_mst2_axi_wdata   )   // write data
  , .npu_mst2_axi_wstrb   (npu_mst2_axi_wstrb   )   // write data strobe
  , .npu_mst2_axi_wlast   (npu_mst2_axi_wlast   )   // write data last
  , .npu_mst2_axi_bvalid  (npu_mst2_axi_bvalid  )   // write response valid
  , .npu_mst2_axi_bready  (npu_mst2_axi_bready  )   // write response accept
  , .npu_mst2_axi_bid     (npu_mst2_axi_bid     )   // write response id
  , .npu_mst2_axi_bresp   (npu_mst2_axi_bresp)    // read response
   , `AXIASYNCSINST(npu_grp1_noc_axi_gals_,npu_grp1_noc_axi_gals_)
  , .grp2_rst_a          ( grp2_rst_a         )
  , .grp2_pwr_dwn_a      ( grp2_pwr_dwn_a         )

    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst3_axi_arvalid            (npu_mst3_axi_arvalid)     // read command valid
  , .npu_mst3_axi_arready            (npu_mst3_axi_arready)     // read command accept
  , .npu_mst3_axi_arid               (npu_mst3_axi_arid   )     // read command ID
  , .npu_mst3_axi_araddr  (npu_mst3_axi_araddr  )   // read command
  , .npu_mst3_axi_arcache (npu_mst3_axi_arcache )   // read command
  , .npu_mst3_axi_arprot  (npu_mst3_axi_arprot  )   // read command
  , .npu_mst3_axi_arlock  (npu_mst3_axi_arlock  )   // read command
  , .npu_mst3_axi_arburst (npu_mst3_axi_arburst )   // read command
  , .npu_mst3_axi_arlen   (npu_mst3_axi_arlen   )   // read command
  , .npu_mst3_axi_arsize  (npu_mst3_axi_arsize  )   // read command
  , .npu_mst3_axi_arsid(npu_mst3_axi_arsid)   // read command
  , .npu_mst3_axi_arssid(npu_mst3_axi_arssid)   // read command
  , .npu_mst3_axi_rvalid  (npu_mst3_axi_rvalid )    // read data valid
  , .npu_mst3_axi_rready  (npu_mst3_axi_rready )    // read data accept
  , .npu_mst3_axi_rid     (npu_mst3_axi_rid    )    // read data id
  , .npu_mst3_axi_rdata   (npu_mst3_axi_rdata  )    // read data
  , .npu_mst3_axi_rresp   (npu_mst3_axi_rresp)    // read response
  , .npu_mst3_axi_rlast   (npu_mst3_axi_rlast  )    // read last
  , .npu_mst3_axi_awvalid (npu_mst3_axi_awvalid )   // write command valid
  , .npu_mst3_axi_awready (npu_mst3_axi_awready )   // write command accept
  , .npu_mst3_axi_awid    (npu_mst3_axi_awid    )   // write command ID
  , .npu_mst3_axi_awaddr  (npu_mst3_axi_awaddr  )   // read command
  , .npu_mst3_axi_awcache (npu_mst3_axi_awcache )   // read command
  , .npu_mst3_axi_awprot  (npu_mst3_axi_awprot  )   // read command
  , .npu_mst3_axi_awlock  (npu_mst3_axi_awlock  )   // read command
  , .npu_mst3_axi_awburst (npu_mst3_axi_awburst )   // read command
  , .npu_mst3_axi_awlen   (npu_mst3_axi_awlen   )   // read command
  , .npu_mst3_axi_awsize  (npu_mst3_axi_awsize  )   // read command
  , .npu_mst3_axi_awsid(npu_mst3_axi_awsid)     // read command
  , .npu_mst3_axi_awssid(npu_mst3_axi_awssid)   // read command
  , .npu_mst3_axi_wvalid  (npu_mst3_axi_wvalid  )   // write data valid
  , .npu_mst3_axi_wready  (npu_mst3_axi_wready  )   // write data accept
  , .npu_mst3_axi_wdata   (npu_mst3_axi_wdata   )   // write data
  , .npu_mst3_axi_wstrb   (npu_mst3_axi_wstrb   )   // write data strobe
  , .npu_mst3_axi_wlast   (npu_mst3_axi_wlast   )   // write data last
  , .npu_mst3_axi_bvalid  (npu_mst3_axi_bvalid  )   // write response valid
  , .npu_mst3_axi_bready  (npu_mst3_axi_bready  )   // write response accept
  , .npu_mst3_axi_bid     (npu_mst3_axi_bid     )   // write response id
  , .npu_mst3_axi_bresp   (npu_mst3_axi_bresp)    // read response
   , `AXIASYNCSINST(npu_grp2_noc_axi_gals_,npu_grp2_noc_axi_gals_)
  , .grp3_rst_a          ( grp3_rst_a         )
  , .grp3_pwr_dwn_a      ( grp3_pwr_dwn_a         )

    // NoC Interface for NPU AXI master, clocked at npu_noc_clk, reset by npu_noc_rst_a
    //-master axi
    //-npu_mst_axi
    // read command channel
  , .npu_mst4_axi_arvalid            (npu_mst4_axi_arvalid)     // read command valid
  , .npu_mst4_axi_arready            (npu_mst4_axi_arready)     // read command accept
  , .npu_mst4_axi_arid               (npu_mst4_axi_arid   )     // read command ID
  , .npu_mst4_axi_araddr  (npu_mst4_axi_araddr  )   // read command
  , .npu_mst4_axi_arcache (npu_mst4_axi_arcache )   // read command
  , .npu_mst4_axi_arprot  (npu_mst4_axi_arprot  )   // read command
  , .npu_mst4_axi_arlock  (npu_mst4_axi_arlock  )   // read command
  , .npu_mst4_axi_arburst (npu_mst4_axi_arburst )   // read command
  , .npu_mst4_axi_arlen   (npu_mst4_axi_arlen   )   // read command
  , .npu_mst4_axi_arsize  (npu_mst4_axi_arsize  )   // read command
  , .npu_mst4_axi_arsid(npu_mst4_axi_arsid)   // read command
  , .npu_mst4_axi_arssid(npu_mst4_axi_arssid)   // read command
  , .npu_mst4_axi_rvalid  (npu_mst4_axi_rvalid )    // read data valid
  , .npu_mst4_axi_rready  (npu_mst4_axi_rready )    // read data accept
  , .npu_mst4_axi_rid     (npu_mst4_axi_rid    )    // read data id
  , .npu_mst4_axi_rdata   (npu_mst4_axi_rdata  )    // read data
  , .npu_mst4_axi_rresp   (npu_mst4_axi_rresp)    // read response
  , .npu_mst4_axi_rlast   (npu_mst4_axi_rlast  )    // read last
  , .npu_mst4_axi_awvalid (npu_mst4_axi_awvalid )   // write command valid
  , .npu_mst4_axi_awready (npu_mst4_axi_awready )   // write command accept
  , .npu_mst4_axi_awid    (npu_mst4_axi_awid    )   // write command ID
  , .npu_mst4_axi_awaddr  (npu_mst4_axi_awaddr  )   // read command
  , .npu_mst4_axi_awcache (npu_mst4_axi_awcache )   // read command
  , .npu_mst4_axi_awprot  (npu_mst4_axi_awprot  )   // read command
  , .npu_mst4_axi_awlock  (npu_mst4_axi_awlock  )   // read command
  , .npu_mst4_axi_awburst (npu_mst4_axi_awburst )   // read command
  , .npu_mst4_axi_awlen   (npu_mst4_axi_awlen   )   // read command
  , .npu_mst4_axi_awsize  (npu_mst4_axi_awsize  )   // read command
  , .npu_mst4_axi_awsid(npu_mst4_axi_awsid)     // read command
  , .npu_mst4_axi_awssid(npu_mst4_axi_awssid)   // read command
  , .npu_mst4_axi_wvalid  (npu_mst4_axi_wvalid  )   // write data valid
  , .npu_mst4_axi_wready  (npu_mst4_axi_wready  )   // write data accept
  , .npu_mst4_axi_wdata   (npu_mst4_axi_wdata   )   // write data
  , .npu_mst4_axi_wstrb   (npu_mst4_axi_wstrb   )   // write data strobe
  , .npu_mst4_axi_wlast   (npu_mst4_axi_wlast   )   // write data last
  , .npu_mst4_axi_bvalid  (npu_mst4_axi_bvalid  )   // write response valid
  , .npu_mst4_axi_bready  (npu_mst4_axi_bready  )   // write response accept
  , .npu_mst4_axi_bid     (npu_mst4_axi_bid     )   // write response id
  , .npu_mst4_axi_bresp   (npu_mst4_axi_bresp)    // read response
   , `AXIASYNCSINST(npu_grp3_noc_axi_gals_,npu_grp3_noc_axi_gals_)
  );


endmodule : npu_core
