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


`include "npu_defines.v"
`include "arcsync_exported_defines.v"
`include "npu_axi_macros.svh"
`include "npu_apb_macros.svh"
`include "npu_macros.svh"



module npu_slice_top_dummy
  import npu_types::*;
  import npu_ecc_types::*;
 (
   // 512b AXI GALS interface to core
  output logic                                                                                                        npu_axi_gals_clk_req,
  output logic [1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                npu_axi_gals_aw_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              npu_axi_gals_aw_rdpnt,
  output logic [1:0]                                                                                       npu_axi_gals_aw_wpnt,
  input  logic [1:0]                                                                                       npu_axi_gals_aw_rpnt_a,
  output logic [64*VSIZE+64*VSIZE/8+SLICE_DMA_WUW:0]                                                           npu_axi_gals_w_data,
  input  logic [`NUM_FLANES(64*VSIZE+64*VSIZE/8+SLICE_DMA_WUW+1)-1:0][(1<<3)-1:0]                      npu_axi_gals_w_rdpnt,
  output logic [3:0]                                                                                        npu_axi_gals_w_wpnt,
  input  logic [3:0]                                                                                        npu_axi_gals_w_rpnt_a,
  input  logic [1+SLICE_DMA_BUW+$bits(npu_axi_resp_t)-1:0]                                                npu_axi_gals_b_data,
  output logic [`NUM_FLANES(1+SLICE_DMA_BUW+$bits(npu_axi_resp_t))-1:0][(1<<1)-1:0]               npu_axi_gals_b_rdpnt,
  input  logic [1:0]                                                                                        npu_axi_gals_b_wpnt_a,
  output logic [1:0]                                                                                        npu_axi_gals_b_rpnt,
  output logic [1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                npu_axi_gals_ar_data,
  input  logic [`NUM_FLANES(1+SLICE_DMA_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<1)-1:0]              npu_axi_gals_ar_rdpnt,
  output logic [1:0]                                                                                       npu_axi_gals_ar_wpnt,
  input  logic [1:0]                                                                                       npu_axi_gals_ar_rpnt_a,
  input  logic [1+64*VSIZE+$bits(npu_axi_resp_t)+SLICE_DMA_RUW:0]                                      npu_axi_gals_r_data,
  output logic [`NUM_FLANES(1+64*VSIZE+$bits(npu_axi_resp_t)+SLICE_DMA_RUW+1)-1:0][(1<<3)-1:0] npu_axi_gals_r_rdpnt,
  input  logic [3:0]                                                                                        npu_axi_gals_r_wpnt_a,
  output logic [3:0]                                                                                        npu_axi_gals_r_rpnt,

  // 64b AXI GALS interface from core
  input  logic                                                                                                        mmio_axi_gals_clk_req_a,
  input  logic [1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t)-1:0]                                                mmio_axi_gals_aw_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_AWUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              mmio_axi_gals_aw_rdpnt,
  input  logic [0:0]                                                                                       mmio_axi_gals_aw_wpnt_a,
  output logic [0:0]                                                                                       mmio_axi_gals_aw_rpnt,
  input  logic [64+64/8+SLICE_MMIO_WUW:0]                                                           mmio_axi_gals_w_data,
  output logic [`NUM_FLANES(64+64/8+SLICE_MMIO_WUW+1)-1:0][(1<<1)-1:0]                      mmio_axi_gals_w_rdpnt,
  input  logic [1:0]                                                                                        mmio_axi_gals_w_wpnt_a,
  output logic [1:0]                                                                                        mmio_axi_gals_w_rpnt,
  output logic [1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t)-1:0]                                                mmio_axi_gals_b_data,
  input  logic [`NUM_FLANES(1+SLICE_MMIO_BUW+$bits(npu_axi_resp_t))-1:0][(1<<0)-1:0]               mmio_axi_gals_b_rdpnt,
  output logic [0:0]                                                                                        mmio_axi_gals_b_wpnt,
  input  logic [0:0]                                                                                        mmio_axi_gals_b_rpnt_a,
  input  logic [1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t)-1:0]                                                mmio_axi_gals_ar_data,
  output logic [`NUM_FLANES(1+SLICE_MMIO_ARUW+$bits(npu_axi_cmd_t))-1:0][(1<<0)-1:0]              mmio_axi_gals_ar_rdpnt,
  input  logic [0:0]                                                                                       mmio_axi_gals_ar_wpnt_a,
  output logic [0:0]                                                                                       mmio_axi_gals_ar_rpnt,
  output logic [1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW:0]                                      mmio_axi_gals_r_data,
  input  logic [`NUM_FLANES(1+64+$bits(npu_axi_resp_t)+SLICE_MMIO_RUW+1)-1:0][(1<<1)-1:0] mmio_axi_gals_r_rdpnt,
  output logic [1:0]                                                                                        mmio_axi_gals_r_wpnt,
  input  logic [1:0]                                                                                        mmio_axi_gals_r_rpnt_a,

  input  logic                         test_mode          ,
  output logic                         wdt_reset          ,
  output logic                         wdt_reset_wdt_clk  ,
  // ARCsync
  input  logic [7:0]                   clusternum         ,
  input  logic [7:0]                   arcnum             ,
  // Boot
  input  logic [21:0]                  intvbase_in        ,
  // CLK Enable
  input  logic                         clk_en_a           ,
  // Halt
  input  logic                         arc_halt_req_a     ,
  output logic                         arc_halt_ack       ,
  // Run
  input  logic                         arc_run_req_a      ,
  output logic                         arc_run_ack        ,
  // Status
  output logic                         sys_sleep_r        ,
  output logic [2:0]                   sys_sleep_mode_r   ,
  output logic                         sys_halt_r         ,
  output logic                         sys_tf_halt_r      ,
  // power domain
  input  logic                         isolate            ,
  input  logic                         isolate_n          ,
  input  logic                         pd_mem             ,
  input  logic                         pd_logic           ,
  // IRQ and Event
  input  logic [1:0]      arc_irq_a          ,
  output logic [1:0]                   l2_send_event      ,
  input  logic [1:0]                   l2_event_a         ,
  output logic [16-1:0]               l1_peer_send_event ,
  input  logic [16-1:0]               l1_peer_event_a    ,
  output logic                         evt_vm_irq         ,
   output logic                        ecc_sbe,
   output logic                        ecc_dbe,
  // Debug
  input  logic                         dbg_cmdval_a       ,
  input  logic [36:0]                  dbg_pack_a         , // eop,address,be,cmd,wdata-1   = 1+32+4+2+32-1 = 70
  output logic [31:0]                  dbg_resp           , // reop,rerr,rdata-1 = 1+1+32-1 = 33

  // Trace
  output logic                         rtt_swe_val        ,
  output logic [32:0]                  rtt_swe_data       ,
  output logic [7:0]                   rtt_swe_ext        ,
  // APB debug
  input  logic                         arct_dbg_prot_sel,
  input  logic                         arct_dbgen,
  input  logic                         arct_niden,
  input  logic                         arct_rst_an,
  `APBASYNCTGT(16,32,dbg_as_),

  input  logic [64-1: 0]           vmid,


  // clock and reset
  input  logic                         wdt_clk              ,
  input  logic                         clk                ,
  input  logic                         rst_a
  );



   assign    npu_axi_gals_clk_req    =  '0;
   assign    npu_axi_gals_aw_data    =  '0;
   assign    npu_axi_gals_aw_wpnt    =  '0;
   assign    npu_axi_gals_w_data     =  '0;
   assign    npu_axi_gals_w_wpnt     =  '0;
   assign    npu_axi_gals_b_rdpnt    =  'h1;
   assign    npu_axi_gals_b_rpnt     =  'h1;
   assign    npu_axi_gals_ar_data    =  '0;
   assign    npu_axi_gals_ar_wpnt    =  '0;
   assign    npu_axi_gals_r_rdpnt    =  {17{8'b1}};
   assign    npu_axi_gals_r_rpnt     =  'hC;
   assign    mmio_axi_gals_aw_rdpnt  =  'h3;
   assign    mmio_axi_gals_aw_rpnt   =  'h1;
   assign    mmio_axi_gals_w_rdpnt   =  {3{2'b1}};
   assign    mmio_axi_gals_w_rpnt    =  'h3;
   assign    mmio_axi_gals_b_data    =  '0;
   assign    mmio_axi_gals_b_wpnt    =  '0;
   assign    mmio_axi_gals_ar_rdpnt  =  'h3;
   assign    mmio_axi_gals_ar_rpnt   =  'h10;
   assign    mmio_axi_gals_r_data    =  '0;
   assign    mmio_axi_gals_r_wpnt    =  '0;




   assign    wdt_reset                     =  1'b0;
   assign    wdt_reset_wdt_clk             =  1'b0;
   assign    arc_halt_ack                  =  1'b1;
   assign    arc_run_ack                   =  1'b1;
   assign    sys_sleep_r                   =  1'b0;
   assign    sys_sleep_mode_r              =  3'b0;
   assign    sys_halt_r                    =  1'b0;
   assign    sys_tf_halt_r                 =  1'b0;
   assign    l2_send_event                 =  2'b0;
   assign    l1_peer_send_event            =  '0;
   assign    evt_vm_irq                    =  1'b0;
   assign    ecc_sbe                       = 1'b0;
   assign    ecc_dbe                       = 1'b0;
  // Debug
   assign    dbg_resp                      = '0;

  // Trace
   assign    rtt_swe_val                   = '0;
   assign    rtt_swe_data                  = '0;
   assign    rtt_swe_ext                   = '0;
  // APB debug
   assign    dbg_as_ack_a                  = 1'b1;
   assign    dbg_as_presp                  =  'b1;

endmodule : npu_slice_top_dummy
