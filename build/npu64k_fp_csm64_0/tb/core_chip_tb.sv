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
`include "tb_defines.sv"





module core_chip_tb
  import npu_tb_pkg::*;
  ();
    // clock and reset
    logic             clk;                     // clock, all logic clocked at posedge
    logic             clk_h1;                  // half_frequency of clk, all logic clocked at posedge
    logic             clk_h2;                  // half_frequency of clk, all logic clocked at posedge
    logic             rst_a;                   // asynchronous reset, active high
    logic             rst_n;
    logic  [31:0]     cycle;

    logic [31:0]      slc_clk;
    logic [31:0]      slc_wdt_clk;
    logic             nl2arc0_wdt_clk;
    logic             nl2arc1_wdt_clk;
    logic             npu_core_clk;
    logic             npu_core_rst_a;
    logic             npu_noc_clk;
    logic             npu_noc_rst_a;
    logic             nl2_rst_a;
    logic             npu_cfg_clk;
    logic             npu_cfg_rst_a;
    logic             arcsync_clk;
    logic             arcsync_rst_a;
    logic             arcsync_axi_clk;
    logic             arcsync_axi_rst_a;
    logic             mss_clk;
    logic             rtt_clk;
    logic             pclkdbg;
    logic [39:24]     npu_csm_base;
    assign mss_clk = clk;
    assign rtt_clk = clk;
    `ifndef DW_DBP_EN
    assign pclkdbg = rtt_clk;
    `endif

    logic  sys_cfg_done;

    logic [11:0] mst_rst_aperture_regid  ;// outside-of-hierarchy
    logic [31:0] mst_rst_aperture_addr   ;// outside-of-hierarchy
    logic [31:0] mst_rst_aperture_size   ;// outside-of-hierarchy
    logic [39:12] arcsync_sys_addr_base;
    logic [39:16] npu_sys_csm_addr_base;
    logic [39:16] npu_sys_periph_addr_base;


  bit [1:0] dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+(`NPU_NUM_GRP * `NPU_NUM_SLC_PER_GRP)]; // APBIC + TRACE + L2 CORE0 + L2 CORE1 + SLICES
  initial foreach (dbgen_niden[i]) dbgen_niden[i] = $urandom_range(0,3);
  // CoreSight interface global signals
   logic           atclken;
   logic           atresetn;
   logic [63:0]    atb_cstimestamp;
   initial begin
       atb_cstimestamp = 64'hf000_0000_0000_0000;
       forever begin
          atb_cstimestamp =   atb_cstimestamp + 1;
          @(posedge rtt_clk);
       end
   end
  // CoreSight interface of L2 core
   logic           atready;
   logic [64-1:0]    atdata;
   logic [3-1:0]     atbytes;
   logic [6:0]     atid;
   logic           atvalid;

   logic           afvalid;
   logic           afready;
   logic           syncreq;
  // CoreSight interface of NPU Slices
   logic           swe_atready;
   logic [64-1:0]   swe_atdata;
   logic [3-1:0]     swe_atbytes;
   logic [6:0]     swe_atid;
   logic           swe_atvalid;

   logic           swe_afvalid;
   logic           swe_afready;
   logic           swe_syncreq;
  // CTI signalling
   logic [25:0]    cti_rtt_filters;
   logic           cti_trace_start;
   logic           cti_trace_stop;


   // APB Interface for debugging and to ARC_Trace
   logic           presetdbgn;
   logic [31:2]    arct0_paddrdbg;
   logic           arct0_pseldbg;
   logic           arct0_penabledbg;
   logic           arct0_pwritedbg;
   logic [31:0]    arct0_pwdatadbg;

   logic           arct0_preadydbg;
   logic [31:0]    arct0_prdatadbg;
   logic           arct0_pslverrdbg;

   logic           arct0_dbgen;
   logic           arct0_niden;

    `ifndef DW_DBP_EN
    assign arct0_dbgen = 1'b1;
    assign arct0_niden = 1'b1;
    `endif

  // Isolation signals

  // APB Interface to L2 ARC
    logic          nl2arc_dbg_prot_sel;
    logic          nl2arc_pclkdbg_en;
    logic          nl2arc_presetdbgn;
    logic [31:2]   nl2arc_paddrdbg;
    logic          nl2arc_pseldbg;
    logic          nl2arc_penabledbg;
    logic          nl2arc_pwritedbg;
    logic [31:0]   nl2arc_pwdatadbg;
    logic          nl2arc_dbgen;
    logic          nl2arc_niden;
    logic          nl2arc_preadydbg;
    logic [31:0]   nl2arc_prdatadbg;
    logic          nl2arc_pslverrdbg;

    logic                         sl0nl1arc_niden      ;
    logic                         sl0nl1arc_dbgen      ;

    //assign                          sl0nl1arc_niden   = 0   ;
    //assign                          sl0nl1arc_dbgen   = 1   ;
    assign sl0nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+0][0];
    assign sl0nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+0][1];

    logic                         sl1nl1arc_niden      ;
    logic                         sl1nl1arc_dbgen      ;

    //assign                          sl1nl1arc_niden   = 0   ;
    //assign                          sl1nl1arc_dbgen   = 1   ;
    assign sl1nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+1][0];
    assign sl1nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+1][1];

    logic                         sl2nl1arc_niden      ;
    logic                         sl2nl1arc_dbgen      ;

    //assign                          sl2nl1arc_niden   = 0   ;
    //assign                          sl2nl1arc_dbgen   = 1   ;
    assign sl2nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+2][0];
    assign sl2nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+2][1];

    logic                         sl3nl1arc_niden      ;
    logic                         sl3nl1arc_dbgen      ;

    //assign                          sl3nl1arc_niden   = 0   ;
    //assign                          sl3nl1arc_dbgen   = 1   ;
    assign sl3nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+3][0];
    assign sl3nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+3][1];

    logic                         sl4nl1arc_niden      ;
    logic                         sl4nl1arc_dbgen      ;

    //assign                          sl4nl1arc_niden   = 0   ;
    //assign                          sl4nl1arc_dbgen   = 1   ;
    assign sl4nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+4][0];
    assign sl4nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+4][1];

    logic                         sl5nl1arc_niden      ;
    logic                         sl5nl1arc_dbgen      ;

    //assign                          sl5nl1arc_niden   = 0   ;
    //assign                          sl5nl1arc_dbgen   = 1   ;
    assign sl5nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+5][0];
    assign sl5nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+5][1];

    logic                         sl6nl1arc_niden      ;
    logic                         sl6nl1arc_dbgen      ;

    //assign                          sl6nl1arc_niden   = 0   ;
    //assign                          sl6nl1arc_dbgen   = 1   ;
    assign sl6nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+6][0];
    assign sl6nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+6][1];

    logic                         sl7nl1arc_niden      ;
    logic                         sl7nl1arc_dbgen      ;

    //assign                          sl7nl1arc_niden   = 0   ;
    //assign                          sl7nl1arc_dbgen   = 1   ;
    assign sl7nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+7][0];
    assign sl7nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+7][1];

    logic                         sl8nl1arc_niden      ;
    logic                         sl8nl1arc_dbgen      ;

    //assign                          sl8nl1arc_niden   = 0   ;
    //assign                          sl8nl1arc_dbgen   = 1   ;
    assign sl8nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+8][0];
    assign sl8nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+8][1];

    logic                         sl9nl1arc_niden      ;
    logic                         sl9nl1arc_dbgen      ;

    //assign                          sl9nl1arc_niden   = 0   ;
    //assign                          sl9nl1arc_dbgen   = 1   ;
    assign sl9nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+9][0];
    assign sl9nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+9][1];

    logic                         sl10nl1arc_niden      ;
    logic                         sl10nl1arc_dbgen      ;

    //assign                          sl10nl1arc_niden   = 0   ;
    //assign                          sl10nl1arc_dbgen   = 1   ;
    assign sl10nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+10][0];
    assign sl10nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+10][1];

    logic                         sl11nl1arc_niden      ;
    logic                         sl11nl1arc_dbgen      ;

    //assign                          sl11nl1arc_niden   = 0   ;
    //assign                          sl11nl1arc_dbgen   = 1   ;
    assign sl11nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+11][0];
    assign sl11nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+11][1];

    logic                         sl12nl1arc_niden      ;
    logic                         sl12nl1arc_dbgen      ;

    //assign                          sl12nl1arc_niden   = 0   ;
    //assign                          sl12nl1arc_dbgen   = 1   ;
    assign sl12nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+12][0];
    assign sl12nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+12][1];

    logic                         sl13nl1arc_niden      ;
    logic                         sl13nl1arc_dbgen      ;

    //assign                          sl13nl1arc_niden   = 0   ;
    //assign                          sl13nl1arc_dbgen   = 1   ;
    assign sl13nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+13][0];
    assign sl13nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+13][1];

    logic                         sl14nl1arc_niden      ;
    logic                         sl14nl1arc_dbgen      ;

    //assign                          sl14nl1arc_niden   = 0   ;
    //assign                          sl14nl1arc_dbgen   = 1   ;
    assign sl14nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+14][0];
    assign sl14nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+14][1];

    logic                         sl15nl1arc_niden      ;
    logic                         sl15nl1arc_dbgen      ;

    //assign                          sl15nl1arc_niden   = 0   ;
    //assign                          sl15nl1arc_dbgen   = 1   ;
    assign sl15nl1arc_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+15][0];
    assign sl15nl1arc_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC+`DUO_L2ARC+15][1];


  logic          nl2arc0_dbgen;
  logic          nl2arc0_niden;
  logic          nl2arc1_dbgen;
  logic          nl2arc1_niden;

  //assign           nl2arc0_dbgen = 1;
  //assign           nl2arc0_niden = 0;
  //assign           nl2arc1_dbgen = 1;
  //assign           nl2arc1_niden = 0;
  assign nl2arc0_dbgen = dbgen_niden[1+`NPU_ARC_TRACE][0];
  assign nl2arc0_niden = dbgen_niden[1+`NPU_ARC_TRACE][1];
  assign nl2arc1_dbgen = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC][0];
  assign nl2arc1_niden = dbgen_niden[1+`NPU_ARC_TRACE+`NPU_HAS_L2ARC][1];

  
  logic            nl2arc_irq0_a;
  logic            nl2arc_irq1_a;
  assign nl2arc_irq0_a = 0;
  assign nl2arc_irq1_a = 0;

    logic jtag_tck;
    logic jtag_trst_n;
    logic jtag_tms;
    logic jtag_tdi;
    logic jtag_tdo;
    logic jtag_tdo_oe;
    logic jtag_rtck;
    logic arct_dbg_prot_sel;
    logic nl2arc0_dbg_cache_rst_disable   ;// outside-of-hierarchy
    logic nl2arc0_dccm_dmi_priority       ;// outside-of-hierarchy
    logic nl2arc0_ext_arc_halt_req_a;
    logic nl2arc0_ext_arc_halt_ack;
    logic nl2arc0_ext_arc_run_req_a;
    logic nl2arc0_ext_arc_run_ack;
    logic nl2arc1_dbg_cache_rst_disable   ;// outside-of-hierarchy
    logic nl2arc1_dccm_dmi_priority       ;// outside-of-hierarchy
    logic nl2arc1_ext_arc_halt_req_a;
    logic nl2arc1_ext_arc_halt_ack;
    logic nl2arc1_ext_arc_run_req_a;
    logic nl2arc1_ext_arc_run_ack;
    logic sl0_clk ;// outside-of-hierarchy
    logic sl0nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl0nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl0nl1arc_ext_arc_halt_req_a;
    logic sl0nl1arc_ext_arc_halt_ack;
    logic sl0nl1arc_ext_arc_run_req_a;
    logic sl0nl1arc_ext_arc_run_ack;
    logic sl1_clk ;// outside-of-hierarchy
    logic sl1nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl1nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl1nl1arc_ext_arc_halt_req_a;
    logic sl1nl1arc_ext_arc_halt_ack;
    logic sl1nl1arc_ext_arc_run_req_a;
    logic sl1nl1arc_ext_arc_run_ack;
    logic sl2_clk ;// outside-of-hierarchy
    logic sl2nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl2nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl2nl1arc_ext_arc_halt_req_a;
    logic sl2nl1arc_ext_arc_halt_ack;
    logic sl2nl1arc_ext_arc_run_req_a;
    logic sl2nl1arc_ext_arc_run_ack;
    logic sl3_clk ;// outside-of-hierarchy
    logic sl3nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl3nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl3nl1arc_ext_arc_halt_req_a;
    logic sl3nl1arc_ext_arc_halt_ack;
    logic sl3nl1arc_ext_arc_run_req_a;
    logic sl3nl1arc_ext_arc_run_ack;
    logic sl4_clk ;// outside-of-hierarchy
    logic sl4nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl4nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl4nl1arc_ext_arc_halt_req_a;
    logic sl4nl1arc_ext_arc_halt_ack;
    logic sl4nl1arc_ext_arc_run_req_a;
    logic sl4nl1arc_ext_arc_run_ack;
    logic sl5_clk ;// outside-of-hierarchy
    logic sl5nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl5nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl5nl1arc_ext_arc_halt_req_a;
    logic sl5nl1arc_ext_arc_halt_ack;
    logic sl5nl1arc_ext_arc_run_req_a;
    logic sl5nl1arc_ext_arc_run_ack;
    logic sl6_clk ;// outside-of-hierarchy
    logic sl6nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl6nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl6nl1arc_ext_arc_halt_req_a;
    logic sl6nl1arc_ext_arc_halt_ack;
    logic sl6nl1arc_ext_arc_run_req_a;
    logic sl6nl1arc_ext_arc_run_ack;
    logic sl7_clk ;// outside-of-hierarchy
    logic sl7nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl7nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl7nl1arc_ext_arc_halt_req_a;
    logic sl7nl1arc_ext_arc_halt_ack;
    logic sl7nl1arc_ext_arc_run_req_a;
    logic sl7nl1arc_ext_arc_run_ack;
    logic sl8_clk ;// outside-of-hierarchy
    logic sl8nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl8nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl8nl1arc_ext_arc_halt_req_a;
    logic sl8nl1arc_ext_arc_halt_ack;
    logic sl8nl1arc_ext_arc_run_req_a;
    logic sl8nl1arc_ext_arc_run_ack;
    logic sl9_clk ;// outside-of-hierarchy
    logic sl9nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl9nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl9nl1arc_ext_arc_halt_req_a;
    logic sl9nl1arc_ext_arc_halt_ack;
    logic sl9nl1arc_ext_arc_run_req_a;
    logic sl9nl1arc_ext_arc_run_ack;
    logic sl10_clk ;// outside-of-hierarchy
    logic sl10nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl10nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl10nl1arc_ext_arc_halt_req_a;
    logic sl10nl1arc_ext_arc_halt_ack;
    logic sl10nl1arc_ext_arc_run_req_a;
    logic sl10nl1arc_ext_arc_run_ack;
    logic sl11_clk ;// outside-of-hierarchy
    logic sl11nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl11nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl11nl1arc_ext_arc_halt_req_a;
    logic sl11nl1arc_ext_arc_halt_ack;
    logic sl11nl1arc_ext_arc_run_req_a;
    logic sl11nl1arc_ext_arc_run_ack;
    logic sl12_clk ;// outside-of-hierarchy
    logic sl12nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl12nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl12nl1arc_ext_arc_halt_req_a;
    logic sl12nl1arc_ext_arc_halt_ack;
    logic sl12nl1arc_ext_arc_run_req_a;
    logic sl12nl1arc_ext_arc_run_ack;
    logic sl13_clk ;// outside-of-hierarchy
    logic sl13nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl13nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl13nl1arc_ext_arc_halt_req_a;
    logic sl13nl1arc_ext_arc_halt_ack;
    logic sl13nl1arc_ext_arc_run_req_a;
    logic sl13nl1arc_ext_arc_run_ack;
    logic sl14_clk ;// outside-of-hierarchy
    logic sl14nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl14nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl14nl1arc_ext_arc_halt_req_a;
    logic sl14nl1arc_ext_arc_halt_ack;
    logic sl14nl1arc_ext_arc_run_req_a;
    logic sl14nl1arc_ext_arc_run_ack;
    logic sl15_clk ;// outside-of-hierarchy
    logic sl15nl1arc_dbg_cache_rst_disable ;// outside-of-hierarchy
    logic sl15nl1arc_dccm_dmi_priority    ;// outside-of-hierarchy
    logic sl15nl1arc_ext_arc_halt_req_a;
    logic sl15nl1arc_ext_arc_halt_ack;
    logic sl15nl1arc_ext_arc_run_req_a;
    logic sl15nl1arc_ext_arc_run_ack;
    logic test_mode                      ;// outside-of-hierarchy
    logic arcsync_core_iso_override;          ;// outside-of-hierarchy

    logic [(`ARCSYNC_VIRT_MACHINES*(`ARCSYNC_NUM_EVT_PER_VPROC+1))-1:0] h0host_virt_evt_a;
    logic [(`ARCSYNC_VIRT_MACHINES*(`ARCSYNC_NUM_IRQ_PER_VPROC+1))-1:0] h0host_virt_irq_a;



  logic [1:0] h0host_irq;
  logic [1:0] h0host_event;


    logic [1-1:0] arcsync_axi_aruser     ;// outside-of-hierarchy
    logic [3:0] arcsync_axi_arcache      ;// outside-of-hierarchy
    logic [2:0] arcsync_axi_arprot       ;// outside-of-hierarchy
    logic [1:0] arcsync_axi_arlock       ;// outside-of-hierarchy
    logic [1-1:0] arcsync_axi_awuser     ;// outside-of-hierarchy
    logic [3:0] arcsync_axi_awcache      ;// outside-of-hierarchy
    logic [2:0] arcsync_axi_awprot       ;// outside-of-hierarchy
    logic [1:0] arcsync_axi_awlock       ;// outside-of-hierarchy
    logic [1-1:0] arcsync_axi_wuser      ;// outside-of-hierarchy
    logic [1-1:0] arcsync_axi_ruser     ;// npu_core_sys(arcsync_top)
    logic [1-1:0] arcsync_axi_buser     ;// npu_core_sys(arcsync_top)
    logic [1-1:0] npu_mst0_axi_aruser   ;// npu_core_sys(npu_top)
    logic [1-1:0] npu_mst0_axi_arregion ;// npu_core_sys(npu_top)
    logic [1-1:0] npu_mst0_axi_awuser   ;// npu_core_sys(npu_top)
    logic [1-1:0] npu_mst0_axi_awregion ;// npu_core_sys(npu_top)
    logic [1-1:0] npu_mst0_axi_wuser    ;// npu_core_sys(npu_top)
    logic [1-1:0] npu_dmi0_axi_ruser    ;// npu_core_sys(npu_top)
    logic [1-1:0] npu_dmi0_axi_buser    ;// npu_core_sys(npu_top)
    logic [1-1:0] stu0_dma_axi_aruser   ;// npu_core_sys(npu_top)
    logic [1-1:0] stu0_dma_axi_arregion ;// npu_core_sys(npu_top)
    logic [1-1:0] stu0_dma_axi_awuser   ;// npu_core_sys(npu_top)
    logic [1-1:0] stu0_dma_axi_awregion ;// npu_core_sys(npu_top)
    logic [1-1:0] stu0_dma_axi_wuser    ;// npu_core_sys(npu_top)

    logic mss_fab_mst0_clk_en            ;// outside-of-hierarchy
    logic mss_fab_mst1_clk_en            ;// outside-of-hierarchy
    logic mss_fab_mst2_clk_en            ;// outside-of-hierarchy
    logic mss_fab_mst3_clk_en            ;// outside-of-hierarchy
    logic mss_fab_mst4_clk_en            ;// outside-of-hierarchy
    logic mss_fab_mst5_clk_en            ;// outside-of-hierarchy
    logic mss_fab_mst6_clk_en            ;// outside-of-hierarchy
    logic mss_fab_slv0_clk_en            ;// outside-of-hierarchy
    logic mss_fab_slv1_clk_en            ;// outside-of-hierarchy
    logic mss_fab_slv2_clk_en            ;// outside-of-hierarchy
    logic mss_fab_slv3_clk_en            ;// outside-of-hierarchy
    logic [1*10-1:0] mss_mem_cfg_lat_w   ;// outside-of-hierarchy
    logic [1*10-1:0] mss_mem_cfg_lat_r   ;// outside-of-hierarchy


    logic nl2arc0_cc_idle;
    logic nl2arc0_evt_vm_irq;
    logic nl2arc0_wdt_reset_error;
    logic nl2arc0_wdt_reset_wdt_clk_error;
    logic nl2arc1_cc_idle;
    logic nl2arc1_evt_vm_irq;
    logic nl2arc1_wdt_reset_error;
    logic nl2arc1_wdt_reset_wdt_clk_error;
    logic sl0nl1arc_cc_idle;
    logic sl0nl1arc_wdt_reset_error;
    logic sl0nl1arc_wdt_reset_wdt_clk_error;
    logic sl1nl1arc_cc_idle;
    logic sl1nl1arc_wdt_reset_error;
    logic sl1nl1arc_wdt_reset_wdt_clk_error;
    logic sl2nl1arc_cc_idle;
    logic sl2nl1arc_wdt_reset_error;
    logic sl2nl1arc_wdt_reset_wdt_clk_error;
    logic sl3nl1arc_cc_idle;
    logic sl3nl1arc_wdt_reset_error;
    logic sl3nl1arc_wdt_reset_wdt_clk_error;
    logic sl4nl1arc_cc_idle;
    logic sl4nl1arc_wdt_reset_error;
    logic sl4nl1arc_wdt_reset_wdt_clk_error;
    logic sl5nl1arc_cc_idle;
    logic sl5nl1arc_wdt_reset_error;
    logic sl5nl1arc_wdt_reset_wdt_clk_error;
    logic sl6nl1arc_cc_idle;
    logic sl6nl1arc_wdt_reset_error;
    logic sl6nl1arc_wdt_reset_wdt_clk_error;
    logic sl7nl1arc_cc_idle;
    logic sl7nl1arc_wdt_reset_error;
    logic sl7nl1arc_wdt_reset_wdt_clk_error;
    logic sl8nl1arc_cc_idle;
    logic sl8nl1arc_wdt_reset_error;
    logic sl8nl1arc_wdt_reset_wdt_clk_error;
    logic sl9nl1arc_cc_idle;
    logic sl9nl1arc_wdt_reset_error;
    logic sl9nl1arc_wdt_reset_wdt_clk_error;
    logic sl10nl1arc_cc_idle;
    logic sl10nl1arc_wdt_reset_error;
    logic sl10nl1arc_wdt_reset_wdt_clk_error;
    logic sl11nl1arc_cc_idle;
    logic sl11nl1arc_wdt_reset_error;
    logic sl11nl1arc_wdt_reset_wdt_clk_error;
    logic sl12nl1arc_cc_idle;
    logic sl12nl1arc_wdt_reset_error;
    logic sl12nl1arc_wdt_reset_wdt_clk_error;
    logic sl13nl1arc_cc_idle;
    logic sl13nl1arc_wdt_reset_error;
    logic sl13nl1arc_wdt_reset_wdt_clk_error;
    logic sl14nl1arc_cc_idle;
    logic sl14nl1arc_wdt_reset_error;
    logic sl14nl1arc_wdt_reset_wdt_clk_error;
    logic sl15nl1arc_cc_idle;
    logic sl15nl1arc_wdt_reset_error;
    logic sl15nl1arc_wdt_reset_wdt_clk_error;




    logic [3:0]               bri4tb_bid;
    logic                     bri4tb_awready;
    logic                     bri4tb_wready;
    logic [1:0]               bri4tb_bresp;
    logic                     bri4tb_bvalid;
    logic [3:0]               bri4tb_rid;
    logic                     bri4tb_arready;
    logic [31:0]              bri4tb_rdata;
    logic                     bri4tb_rlast;
    logic                     bri4tb_rvalid;
    logic [1:0]               bri4tb_rresp;
    logic [3:0]               bri4tb_arid;
    logic                     bri4tb_arvalid;
    logic [39:0]            bri4tb_araddr;
    logic [1:0]               bri4tb_arburst;
    logic [2:0]               bri4tb_arsize;
    logic [3:0]               bri4tb_arlen;
    logic [3:0]               bri4tb_arcache;
    logic [2:0]               bri4tb_arprot;
    logic                     bri4tb_rready;
    logic [3:0]               bri4tb_awid;
    logic                     bri4tb_awvalid;
    logic [39:0]            bri4tb_awaddr;
    logic [1:0]               bri4tb_awburst;
    logic [2:0]               bri4tb_awsize;
    logic [3:0]               bri4tb_awlen;
    logic [3:0]               bri4tb_awcache;
    logic [2:0]               bri4tb_awprot;
    logic [3:0]               bri4tb_wid;
    logic                     bri4tb_wvalid;
    logic [31:0]              bri4tb_wdata;
    logic [3:0]               bri4tb_wstrb;
    logic                     bri4tb_wlast;
    logic                     bri4tb_bready;
    logic                     mbus_clk_en;
    logic                     nlarc_dbg_prot_sel;
    logic                     nlarc_pclkdbg_en;
    logic                     nlarc_presetdbgn;
    logic [31:2]              nlarc_paddrdbg;
    logic                     nlarc_pseldbg;
    logic                     nlarc_penabledbg;
    logic                     nlarc_pwritedbg;
    logic [31:0]              nlarc_pwdatadbg;
    logic                     nlarc_dbgen;
    logic                     nlarc_niden;

`ifdef TOP_E2E_ECC  //{
      top_e2e_ecc_tb i_top_e2e_tb(.clk(npu_core_clk), .rst_a(rst_a));
`endif

`ifdef TOP_BUS_ECC_CHECK  //{
      bus_ecc_tb i_bus_ecc_tb(.clk(clk), .rst_a(rst_a));
`endif //}
`ifdef SAFETY_MONITOR_CHECK  //{
safety_monitor_tb i_safety_monitor_tb(.clk(clk)
                                    , .rst_a(rst_a));
`endif // }
`ifdef TMR_CHECK  //{
tmr_tb i_tmr_tb(.clk(clk)
                , .rst_a(rst_a));
`endif // }

    assign nl2arc_dbg_prot_sel = 1'b0;
    assign nl2arc_pclkdbg_en   = 1'b0;
    assign nl2arc_presetdbgn   = 1'b0;
    assign nl2arc_paddrdbg     = 30'b0;
    assign nl2arc_pseldbg      = 1'b0;
    assign nl2arc_penabledbg   = 1'b0;
    assign nl2arc_pwritedbg    = 1'b0;
    assign nl2arc_pwdatadbg    = 32'b0;
    assign nl2arc_dbgen        = 1'b0;
    assign nl2arc_niden        = 1'b0;

  `ifndef DW_DBP_EN
    npu_rtt_tb
      i_rtt_tb (
        .*
    );
  `endif
    assign nl2arc0_ext_arc_run_req_a = 1'b0;
    assign nl2arc1_ext_arc_run_req_a = 1'b0;
    assign sl0nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl1nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl2nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl3nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl4nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl5nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl6nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl7nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl8nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl9nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl10nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl11nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl12nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl13nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl14nl1arc_ext_arc_run_req_a = 1'b0;
    assign sl15nl1arc_ext_arc_run_req_a = 1'b0;

    // Clock Generation
    logic jtag_clk_1;
    logic jtag_rst_n_1;
    clk_rst_gen #(
        .CYCYLE(0.05*`CLK_NS)
      , .RST_DELAY(2*`CLK_NS)
    ) u_clk_rst_gen (
        .jtag_clk(jtag_clk_1)
      , .jtag_rst_n(jtag_rst_n_1)
      , .*
    );

    assign arcsync_clk = clk;
    assign arcsync_rst_a = rst_a;
    assign arcsync_axi_clk = clk;
    assign arcsync_axi_rst_a = rst_a;
    assign presetdbgn = ~rst_a;

  generate
    begin
    if (32'hffffffff==`TB_SIM_MON_EN)
      begin
      npu_swe_tb u_npu_swe_tb();
      end
    end
  endgenerate

  `ifndef TB_MDB
    sim_monitor #(.TB_SIM_MON_EN(`TB_SIM_MON_EN))   u_sim_monitor (.cycle(cycle), .l1_clk(slc_clk[0]), .l2_clk(npu_core_clk), .rst_a(rst_a));
  `else
    // Connect RASCAL pipemons
    initial
      begin
      reg [3:0] pipemon_enabled = 4'b0001;
        //l2arc0
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`L2_CORE), 320 | (1<<6) | (1<< 24) | (1<<9) | (1<<11), // options
              "npu_l2_0",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l2_0_trace.txt"  // trace
          );
        //l2arc1
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`L2_1_CORE), 320 | (1<<6) | (2<< 24) | (1<<9) | (1<<11), // options
              "npu_l2_1",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l2_1_trace.txt"  // trace
          );
        //l1arc0
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL0_CORE), 320 | (1<<6) | (3<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_0",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_0_trace.txt"  // trace
          );
        //l1arc1
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL1_CORE), 320 | (1<<6) | (4<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_1",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_1_trace.txt"  // trace
          );
        //l1arc2
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL2_CORE), 320 | (1<<6) | (5<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_2",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_2_trace.txt"  // trace
          );
        //l1arc3
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL3_CORE), 320 | (1<<6) | (6<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_3",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_3_trace.txt"  // trace
          );
        //l1arc4
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL4_CORE), 320 | (1<<6) | (7<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_4",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_4_trace.txt"  // trace
          );
        //l1arc5
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL5_CORE), 320 | (1<<6) | (8<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_5",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_5_trace.txt"  // trace
          );
        //l1arc6
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL6_CORE), 320 | (1<<6) | (9<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_6",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_6_trace.txt"  // trace
          );
        //l1arc7
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL7_CORE), 320 | (1<<6) | (10<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_7",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_7_trace.txt"  // trace
          );
        //l1arc8
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL8_CORE), 320 | (1<<6) | (11<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_8",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_8_trace.txt"  // trace
          );
        //l1arc9
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL9_CORE), 320 | (1<<6) | (12<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_9",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_9_trace.txt"  // trace
          );
        //l1arc10
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL10_CORE), 320 | (1<<6) | (13<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_10",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_10_trace.txt"  // trace
          );
        //l1arc11
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL11_CORE), 320 | (1<<6) | (14<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_11",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_11_trace.txt"  // trace
          );
        //l1arc12
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL12_CORE), 320 | (1<<6) | (15<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_12",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_12_trace.txt"  // trace
          );
        //l1arc13
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL13_CORE), 320 | (1<<6) | (16<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_13",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_13_trace.txt"  // trace
          );
        //l1arc14
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL14_CORE), 320 | (1<<6) | (17<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_14",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_14_trace.txt"  // trace
          );
        //l1arc15
      $pipemon_arcv2(clk, pipemon_enabled, `STRING_DEF(`SL15_CORE), 320 | (1<<6) | (18<< 24) | (1<<9) | (1<<11), // options
              "npu_l1_15",   // unique name prefix provided for pipemon trace purposes.
              "undefined", // undef
              "npu_l1_15_trace.txt"  // trace
          );
    end
  `endif // TB_MDB!=1

    core_chip u_core_chip(
         .sl0_clk(slc_clk[0]) ,
         .sl0_wdt_clk(slc_wdt_clk[0]),
         .sl1_clk(slc_clk[1]) ,
         .sl1_wdt_clk(slc_wdt_clk[1]),
         .sl2_clk(slc_clk[2]) ,
         .sl2_wdt_clk(slc_wdt_clk[2]),
         .sl3_clk(slc_clk[3]) ,
         .sl3_wdt_clk(slc_wdt_clk[3]),
         .sl4_clk(slc_clk[4]) ,
         .sl4_wdt_clk(slc_wdt_clk[4]),
         .sl5_clk(slc_clk[5]) ,
         .sl5_wdt_clk(slc_wdt_clk[5]),
         .sl6_clk(slc_clk[6]) ,
         .sl6_wdt_clk(slc_wdt_clk[6]),
         .sl7_clk(slc_clk[7]) ,
         .sl7_wdt_clk(slc_wdt_clk[7]),
         .sl8_clk(slc_clk[8]) ,
         .sl8_wdt_clk(slc_wdt_clk[8]),
         .sl9_clk(slc_clk[9]) ,
         .sl9_wdt_clk(slc_wdt_clk[9]),
         .sl10_clk(slc_clk[10]) ,
         .sl10_wdt_clk(slc_wdt_clk[10]),
         .sl11_clk(slc_clk[11]) ,
         .sl11_wdt_clk(slc_wdt_clk[11]),
         .sl12_clk(slc_clk[12]) ,
         .sl12_wdt_clk(slc_wdt_clk[12]),
         .sl13_clk(slc_clk[13]) ,
         .sl13_wdt_clk(slc_wdt_clk[13]),
         .sl14_clk(slc_clk[14]) ,
         .sl14_wdt_clk(slc_wdt_clk[14]),
         .sl15_clk(slc_clk[15]) ,
         .sl15_wdt_clk(slc_wdt_clk[15]),
         .rst_b(rst_n),
        .*
    );

`ifdef TB_MDB
  `ifdef DW_DBP_EN
    jtag_model #(
      .JTAG_TCK_PERIOD(2*`CLK_NS)
    ) ijtag_model (
          .rst_a        (rst_a)                       // <   core_chip.io_pad_ring
        , .ejtag_tdo    (jtag_tdo)                    // <   core_chip.io_pad_ring
        , .ejtag_tck    (jtag_tck)                    //   > core_chip
        , .ejtag_trst_n (jtag_trst_n)                 //   > core_chip
        , .ejtag_tms    (jtag_tms)                    //   > core_chip
        , .ejtag_tdi    (jtag_tdi)                    //   > core_chip
    );

    dw_dbp idw_dbp(
          .clk            (clk)                          // <   alb_mss_clkctrl
        , .test_mode      (1'b0)                         // <   io_pad_ring
        , .jtag_tck       (jtag_tck)                     // <   io_pad_ring
        , .jtag_trst_n    (jtag_trst_n)                  // <   io_pad_ring
        , .jtag_tdi       (jtag_tdi)                     // <   io_pad_ring
        , .jtag_tms       (jtag_tms)                     // <   io_pad_ring
        , .presetdbgn     (presetdbgn)                   // <   clock_and_reset
        , .apb_preadydbg  (arct0_preadydbg)              // <   archipelago.apbic_wrapper
        , .apb_prdatadbg  (arct0_prdatadbg)              // <   archipelago.apbic_wrapper
        , .apb_pslverrdbg (arct0_pslverrdbg)             // <   archipelago.apbic_wrapper
        , .rst_a          (rst_a)                        // <   io_pad_ring
        , .apb_penabledbg (arct0_penabledbg)             //   > archipelago
        , .apb_paddrdbg   (arct0_paddrdbg)               //   > archipelago
        , .apb_pwritedbg  (arct0_pwritedbg)              //   > archipelago
        , .apb_pwdatadbg  (arct0_pwdatadbg)              //   > archipelago
        , .apb_pseldbg    (arct0_pseldbg)                //   > archipelago
        , .pclkdbg        (pclkdbg)                          //   > archipelago
        , .apb_dbgen      (arct0_dbgen)                  //   > archipelago
        , .apb_niden      (arct0_niden)                  //   > archipelago
        , .jtag_tdo       (jtag_tdo)                     //   > io_pad_ring
        , .jtag_tdo_oe    (jtag_tdo_oe)                  //   > io_pad_ring
    );

  `else
    // Instanciate BVCI/APB based fast RASCAL driver
    begin : fast_rascal
      `connect_fast_rascal(l2_arc0, 1, `L2_ALB_CPU)
      `connect_fast_rascal(l2_arc1, 2, `L2_1_ALB_CPU)
      `connect_fast_rascal(l1_arc_0, 3, `SL0_ALB_CPU)
      `connect_fast_rascal(l1_arc_1, 4, `SL1_ALB_CPU)
      `connect_fast_rascal(l1_arc_2, 5, `SL2_ALB_CPU)
      `connect_fast_rascal(l1_arc_3, 6, `SL3_ALB_CPU)
      `connect_fast_rascal(l1_arc_4, 7, `SL4_ALB_CPU)
      `connect_fast_rascal(l1_arc_5, 8, `SL5_ALB_CPU)
      `connect_fast_rascal(l1_arc_6, 9, `SL6_ALB_CPU)
      `connect_fast_rascal(l1_arc_7, 10, `SL7_ALB_CPU)
      `connect_fast_rascal(l1_arc_8, 11, `SL8_ALB_CPU)
      `connect_fast_rascal(l1_arc_9, 12, `SL9_ALB_CPU)
      `connect_fast_rascal(l1_arc_10, 13, `SL10_ALB_CPU)
      `connect_fast_rascal(l1_arc_11, 14, `SL11_ALB_CPU)
      `connect_fast_rascal(l1_arc_12, 15, `SL12_ALB_CPU)
      `connect_fast_rascal(l1_arc_13, 16, `SL13_ALB_CPU)
      `connect_fast_rascal(l1_arc_14, 17, `SL14_ALB_CPU)
      `connect_fast_rascal(l1_arc_15, 18, `SL15_ALB_CPU)
    end
    initial begin
      jtag_tms = 0;
      jtag_tdi = 0;
      arct_dbg_prot_sel = 1'b1; // APB mode
    end
  `endif
`endif

   initial
   begin
        //presetdbgn = 1;



        arcsync_axi_aruser = 0;
        arcsync_axi_arcache = 0;
        arcsync_axi_arprot = 0;
        arcsync_axi_arlock = 0;
        arcsync_axi_awuser = 0;
        arcsync_axi_awcache = 0;
        arcsync_axi_awprot = 0;
        arcsync_axi_awlock = 0;
        arcsync_axi_wuser = 0;

        mss_fab_mst0_clk_en = 1;
        mss_fab_mst1_clk_en = 1;
        mss_fab_mst2_clk_en = 1;
        mss_fab_mst3_clk_en = 1;
        mss_fab_mst4_clk_en = 1;
        mss_fab_mst5_clk_en = 1;
        mss_fab_mst6_clk_en = 1;
        mss_fab_slv0_clk_en = 1;
        mss_fab_slv1_clk_en = 1;
        mss_fab_slv2_clk_en = 1;
        mss_fab_slv3_clk_en = 1;
        mss_mem_cfg_lat_w = 0;
        mss_mem_cfg_lat_r = 0;



   end

npu_tb_intf     tb_if(.*);
top_pin_drive   i_pin_drv(.tb_if(tb_if));
host_model      i_host(.*);

`ifndef TB_MDB //{ (`TB_MDB != 1)
npu_mem_init    u_npu_mem_init(.clk(clk), .rst_a(rst_a));
sim_terminator  u_sim_terminator(.cycle(cycle), .clk(clk), .rst_a(rst_a));
`endif //}

generate
  if ('hffffffff==`TB_SIM_MON_EN)
    activity_recording u_activity_recording();
endgenerate



 

endmodule: core_chip_tb
