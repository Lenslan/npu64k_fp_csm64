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
`include "npu_macros.svh"
`include "npu_axi_macros.svh"
`include "npu_apb_macros.svh"
`include "npu_vm_macros.svh"
`include "npu_am_macros.svh"

`include "npu_vm_ecc_macros.sv"
`include "npu_am_ecc_macros.sv"



module npu_slice
  import npu_types::*;
  import npu_ecc_types::*;
#(parameter int NPU_HAS_FLOAT=1)
(
   input  logic [64-1: 0]     vmid,
   // slave interface for MMIO accesses, no ID bits
   `AXISLV(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,mmio_axi_),
   // master interface for DMA
   `AXIMST(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,npu_axi_),

  // power domain
   input  logic            pd_mem            ,
   input  logic            test_mode         ,
   output logic            wdt_reset          ,
   output logic            wdt_reset_wdt_clk  ,

   // ARCsync
   input  logic [7:0]      clusternum        ,
   input  logic [7:0]      arcnum            ,
   // Boot
   input  logic [21:0]     intvbase_in       ,
   // Halt
   input  logic            arc_halt_req_a    ,
   output logic            arc_halt_ack      ,
   // Run
   input  logic            arc_run_req_a     ,
   output logic            arc_run_ack       ,
   // Status
   output logic            sys_sleep_r       ,
   output logic [2:0]      sys_sleep_mode_r  ,
   output logic            sys_halt_r        ,
   output logic            sys_tf_halt_r     ,
   // IRQ and Event
   input  logic [1:0]      arc_irq_a         ,
   output logic [1:0]      l2_send_event     ,
   input  logic [1:0]      l2_event_a        ,
   output logic [16-1:0]  l1_peer_send_event,
   input  logic [16-1:0]  l1_peer_event_a   ,
   output logic            evt_vm_irq        ,

   output logic            ecc_sbe,  // Single bit error on any memory
   output logic            ecc_dbe,  // Double bit error on any memory
   // HS Debug BVCI
   input  logic            dbg_cmdval        ,
   output logic            dbg_cmdack        ,
   input  logic            dbg_eop           ,
   input  logic [31:0]     dbg_address       ,
   input  logic [3:0]      dbg_be            ,
   input  logic [1:0]      dbg_cmd           ,
   input  logic [31:0]     dbg_wdata         ,
   output logic            dbg_rspval        ,
   input  logic            dbg_rspack        ,
   output logic            dbg_reop          ,
   output logic            dbg_rerr          ,
   output logic [31:0]     dbg_rdata         ,
   output logic            debug_reset       ,

   // ARC Trace : only export SWE interface
   output logic            rtt_swe_val        ,
   output logic [32:0]     rtt_swe_data       ,
   output logic [7:0]      rtt_swe_ext        ,

   // APB debug
   input      logic                          arct_dbg_prot_sel,
   input      logic                          arct_dbgen,
   input      logic                          arct_niden,
   input      logic                          arct_rst_an,
  `APBSLV(16,32,dbg_),


   // clock and reset
   input  logic            wdt_clk              ,
   input logic             clk               ,      // clock, all logic clocked at posedge
   input logic             rst_a                    // asynchronous reset, active high
 );
  // memory ports
  localparam int AM_RPORTS            = 2;
  localparam int AM_WPORTS            = 2;
  localparam int VM_RPORTS            = (NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_BPAR_LD_LANES+GTOA_MPST_LANES+DMA_VM_LANES)+1;
  localparam int NUM_AM_BANKS         = 2;
  localparam int VM_WPORTS            = (VSIZE+GTOA_MPST_LANES+DMA_VM_LANES);
  localparam int NUM_VM_BANKS         = (8*VSIZE+32)/3;

  // VM READ
  localparam int RD_CONV_FM_IDX   = 0;
  localparam int RD_CONV_CF_IDX   = NUM_FM_QUEUE;
  localparam int RD_CONV_PAD_IDX  = NUM_FM_QUEUE+NUM_COEF_QUEUE;
  localparam int RD_GTOA_VM0_IDX  = NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES;
  //localparam int RD_GTOA_VM1_IDX  = CONV_PAD_LD_LANES+CONV_PAD_LD_LANES;
  localparam int RD_GTOA_MPST_IDX = NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE;
  localparam int RD_GTOA_BPAR_IDX = NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_MPST_LANES;
  localparam int RD_ODMA_VM_IDX   = NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_MPST_LANES+GTOA_BPAR_LD_LANES;
  localparam int RD_IDMA_VM_IDX   = NUM_FM_QUEUE+NUM_COEF_QUEUE+CONV_PAD_LD_LANES+VSIZE+GTOA_MPST_LANES+GTOA_BPAR_LD_LANES+DMA_VM_LANES;

  // VM WRITE
  localparam int WR_GTOA_VM_IDX   = 0;
  localparam int WR_GTOA_MPST_IDX = VSIZE;
  localparam int WR_IDMA_VM_IDX   = VSIZE+GTOA_MPST_LANES;

  // ID WIDTH
  localparam int AXI_ARC_IDW     = 2;               // ARC CBU ID width
  localparam int AXI_DESCR_IDW   = 1;               // Descriptor ID width
  localparam int AXI_DMA_IDW     = 1;               // DMA master ID width
  localparam int AXI_DATA_IDW    = 1;        // Data bus ID width
  localparam int AXI_CTRL_IDW    = AXI_ARC_IDW+1;   // Control ID width
  localparam int AXI_DCCM_IDW    = AXI_CTRL_IDW+3;  // DCCM ID width

  // Trace
  localparam int NUM_TRACE_SRC = 5; // TODO: 2 SWE will be added for l1arc, so total source will be 6

  // interrupt and event
  logic         irq_idma;                     // level interrupt to processor
  logic         err_irq_idma;                 // level interrupt to processor
  logic         ievt_idma;                    // event pulse to processor
  logic         devt_idma;                    // event pulse to processor

  logic         irq_odma;                     // level interrupt to processor
  logic         err_irq_odma;                 // level interrupt to processor
  logic         ievt_odma;                    // event pulse to processor
  logic         devt_odma;                    // event pulse to processor

  logic         irq_conv;                     // level interrupt to processor
  logic         err_irq_conv;                 // level interrupt to processor
  logic         ievt_conv;                    // event pulse to processor
  logic         devt_conv;                    // event pulse to processor

  logic         irq_gten;                     // level interrupt to processor
  logic         err_irq_gten;                 // level interrupt to processor
  logic         ievt_gten;                    // event pulse to processor
  logic         devt_gten;                    // event pulse to processor
  logic         mem_ecc_irq;                  // level interrupt to processor
  logic [54:21] arc_irqs_a;

  logic         arc_evm_event;                // wake-up
  logic [95:0]  events_in_a;
  logic [63:0]  event_send;
  logic [9:0]   dummy_rid;
  logic [9:0]   dummy_bid;
  logic [3:0]   cbu_dummy_wid;
  logic [1:0]   cbudummyarid;
  logic [1:0]   cbudummyawid;
  logic         cbudummyarlock;
  logic         cbudummyawlock;

  logic         rst_sync;
  logic [3:0]   vm_sel;


   // L1 ARC dbe/sbe err
   logic            fs_dc_tag_ecc_sb_error_r;
   logic            fs_dc_tag_ecc_db_error_r;
   logic            fs_dc_data_ecc_sb_error_r;
   logic            fs_dc_data_ecc_db_error_r;
   logic            fs_dccm_ecc_sb_error_r;
   logic            fs_dccm_ecc_db_error_r;
   logic            fs_itlb_ecc_sb_error_r;
   logic            fs_itlb_ecc_db_error_r;
   logic            fs_dtlb_ecc_sb_error_r;
   logic            fs_dtlb_ecc_db_error_r;
   logic            fs_ic_tag_ecc_sb_error_r;
   logic            fs_ic_tag_ecc_db_error_r;
   logic            fs_ic_data_ecc_sb_error_r;
   logic            fs_ic_data_ecc_db_error_r;
   // VM/AM dbe/sbe err
   logic            vm_ecc_dbe;
   logic            am_ecc_dbe;
   logic            vm_ecc_sbe;
   logic            am_ecc_sbe;

   logic ecc_sbe_r, ecc_sbe_nxt;
   logic ecc_dbe_r, ecc_dbe_nxt;

   // Combine all ECC SBE & DBE status
   assign ecc_sbe_nxt =   vm_ecc_sbe | am_ecc_sbe
                        | fs_dc_tag_ecc_sb_error_r | fs_dc_data_ecc_sb_error_r
                        | fs_dccm_ecc_sb_error_r
                        | fs_ic_tag_ecc_sb_error_r | fs_ic_data_ecc_sb_error_r
                        | fs_itlb_ecc_sb_error_r | fs_dtlb_ecc_sb_error_r
                        ;
   assign ecc_dbe_nxt =   vm_ecc_dbe | am_ecc_dbe
                        | fs_dc_tag_ecc_db_error_r | fs_dc_data_ecc_db_error_r
                        | fs_dccm_ecc_db_error_r
                        | fs_ic_tag_ecc_db_error_r | fs_ic_data_ecc_db_error_r
                        | fs_itlb_ecc_db_error_r | fs_dtlb_ecc_db_error_r
                        ;

  // Register final ECC flags
  always_ff @(posedge clk or posedge rst_sync)
  begin : ecc_reg_PROC
    if (rst_sync == 1'b1)
    begin
      ecc_sbe_r <= 1'b0;
      ecc_dbe_r <= 1'b0;
    end
    else // Always enabled ff
    begin
      ecc_sbe_r <= ecc_sbe_nxt;
      ecc_dbe_r <= ecc_dbe_nxt;
    end
  end : ecc_reg_PROC
  // ECC outputs
  assign ecc_sbe = ecc_sbe_r;
  assign ecc_dbe = ecc_dbe_r;


  logic         watchdog_reset  ;


  //
  // Local reset synchronizer
  //
  npu_reset_ctrl
  u_reset_ctrl_main
  (
    .clk        ( clk         ),
    .rst_a      ( rst_a       ),
    .test_mode  ( test_mode   ),
    .rst        ( rst_sync )
  );

  `STRWIRES(stri_,vyixacc_t);
  `STRWIRES(stro_,vyixacc_t);
  `STRWIRES(i_stro_,vyixacc_t);
  // Trace Wires
  `TRCWIRES(trace_,NUM_TRACE_SRC);

  // interfaces for DESC with DCCM
  `AXIWIRES(AXI_DCCM_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,i_descr_axi_);     // AXI descriptor read/write
  `AXIWIRES(AXI_DCCM_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,descr_axi_);       // AXI descriptor read/write
  assign descr_axi_ruser = '0;
  assign descr_axi_buser = '0;

  // interfaces for L1 ARC MMIO
  `AXIWIRES(AXI_ARC_IDW,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,cbu_mmio_axi_);    // AXI MMIO interface
  `AXIWIRES(AXI_ARC_IDW,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,icbu_mmio_axi_);    // AXI MMIO interface
  assign cbu_mmio_axi_aruser = '0;
  assign cbu_mmio_axi_awuser = '0;
  assign cbu_mmio_axi_wuser  = '0;
  assign cbu_mmio_axi_ar.region = '0;
  assign cbu_mmio_axi_aw.region = '0;
  // ARC interface after control and data split
  `AXIWIRESN(2,AXI_ARC_IDW,64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,arc_axi_);
  `AXIWIRES(AXI_ARC_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,arc_mmio_axi_);

  // AXI interface for MMIO & descr
  // with iDMA
  `AXIWIRES(AXI_CTRL_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,idma_mmio_axi_);    // AXI MMIO interface
  `AXIWIRES(AXI_DESCR_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,idma_descr_axi_);  // AXI descriptor read/write

  // with oDMA
  `AXIWIRES(AXI_CTRL_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,odma_mmio_axi_);    // AXI MMIO interface
  `AXIWIRES(AXI_DESCR_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,odma_descr_axi_);  // AXI descriptor read/write

  // with conv
  `AXIWIRES(AXI_CTRL_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,conv_mmio_axi_);    // AXI MMIO interface
  `AXIWIRES(AXI_DESCR_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,conv_descr_axi_);  // AXI descriptor read/write

  // with generic tensor operation
  `AXIWIRES(AXI_CTRL_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,gten_mmio_axi_);    // AXI MMIO interface
  `AXIWIRES(AXI_DESCR_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,gten_descr_axi_);  // AXI descriptor read/write

  // with VM bus
  `AXIWIRES(AXI_CTRL_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,vm_mmio_axi_);      // AXI MMIO interface

  // with AM bus
  `AXIWIRES(AXI_CTRL_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,am_mmio_axi_);      // AXI MMIO interface

  // with CtrlBus and DM Bus
  `AXIWIRES(AXI_CTRL_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,mmio_descr_axi_);

  // with data bus
  `AXIWIRES(AXI_DMA_IDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,metadata_data_axi_);
  `AXIWIRES(AXI_DMA_IDW,VSIZE*64,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,feature_map_data_axi_);

  // with safety
  `AXIWIRES(AXI_CTRL_IDW,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,sfty_mmio_axi_);

  //
  // interfaces for VM
  //
  `VMWWIRES(VM_WPORTS,nn_vm_wr_);
  `VMRWIRES(VM_RPORTS,nn_vm_rd_);
  `VMWWIRES(VM_WPORTS,i_nn_vm_wr_);
  `VMRWIRES(VM_RPORTS,i_nn_vm_rd_);
  //
  // interfaces for VM ECC
  //
  logic  vm_prot_en;
  `VMWIRES_ECC(NUM_VM_BANKS,vm_);
  logic  vm_sb_err;
  logic  vm_db_err;

  // VM Initialization
  logic vm_init;
  logic vm_init_end;

  // MUXED interface
  `VMWIRES(NUM_VM_BANKS,vm_);

  //
  // interfaces for AM
  //
  `AMWWIRES(nn_am_wr_,AM_WPORTS);
  `AMRWIRES(nn_am_rd_,AM_RPORTS);
  `AMWWIRES(i_nn_am_wr_,AM_WPORTS);
  `AMRWIRES(i_nn_am_rd_,AM_RPORTS);
  //
  // interfaces for AM ECC
  //
  logic  am_prot_en;
  `AMWIRES_ECC(2,am_);
  logic  am_sb_err;
  logic  am_db_err;

  // AM Initialization
  logic am_init;
  logic am_init_end;

  // MUXED interface
  `AMWIRES_MSK(2,am_);



  /////////////////////////////////////////////////////////////////////////////////
  //
  // Submodules
  //
  /////////////////////////////////////////////////////////////////////////////////


  //
  // iDMA
  //
  npu_idma_top
  #(
    .SAXIAWUW    (SLICE_MMIO_AWUW),
    .SAXIWUW     (SLICE_MMIO_WUW ),
    .SAXIBUW     (SLICE_MMIO_BUW ),
    .SAXIARUW    (SLICE_MMIO_ARUW),
    .SAXIRUW     (SLICE_MMIO_RUW ),
    .MAXIAWUW    (SLICE_MMIO_AWUW),
    .MAXIWUW     (SLICE_MMIO_WUW ),
    .MAXIBUW     (SLICE_MMIO_BUW ),
    .MAXIARUW    (SLICE_MMIO_ARUW),
    .MAXIRUW     (SLICE_MMIO_RUW ),
    .DMAXIAWUW   (SLICE_DMA_AWUW),
    .DMAXIWUW    (SLICE_DMA_WUW ),
    .DMAXIBUW    (SLICE_DMA_BUW ),
    .DMAXIARUW   (SLICE_DMA_ARUW),
    .DMAXIRUW    (SLICE_DMA_RUW ),
    .AXI_OST     (AXI_OST),
    .SAXIIDW     (AXI_CTRL_IDW)
  )
  u_npu_idma
  (
    `AXIINST(mmio_axi_,idma_mmio_axi_),
    `AXIINST(descr_axi_,idma_descr_axi_),
    `AXIRINST(metadata_data_axi_,metadata_data_axi_),
    `AXIRINST(feature_map_data_axi_,feature_map_data_axi_),
    `VMRINST_S(1,vm_rd_,i_nn_vm_rd_,RD_IDMA_VM_IDX),
    `VMWINST_S(DMA_VM_LANES,vm_wr_,i_nn_vm_wr_,WR_IDMA_VM_IDX),
    `TRCINST_S(trace_,trace_,0),
    .vmid                     (vmid),
    // Clock, Reset, Interrupt, Event
    .test_mode               (test_mode),
    .irq                     (irq_idma),
    .err_irq                 (err_irq_idma),
    .ievent                  (ievt_idma),
    .devent                  (devt_idma),
    .rst_a                   (rst_a),
    .clk                     (clk)
  );

  //
  // oDMA
  //
  npu_odma_top
  #(
    .SAXIAWUW    (SLICE_MMIO_AWUW),
    .SAXIWUW     (SLICE_MMIO_WUW ),
    .SAXIBUW     (SLICE_MMIO_BUW ),
    .SAXIARUW    (SLICE_MMIO_ARUW),
    .SAXIRUW     (SLICE_MMIO_RUW ),
    .MAXIAWUW    (SLICE_MMIO_AWUW),
    .MAXIWUW     (SLICE_MMIO_WUW ),
    .MAXIBUW     (SLICE_MMIO_BUW ),
    .MAXIARUW    (SLICE_MMIO_ARUW),
    .MAXIRUW     (SLICE_MMIO_RUW ),
    .DMAXIAWUW   (SLICE_DMA_AWUW),
    .DMAXIWUW    (SLICE_DMA_WUW ),
    .DMAXIBUW    (SLICE_DMA_BUW ),
    .DMAXIARUW   (SLICE_DMA_ARUW),
    .DMAXIRUW    (SLICE_DMA_RUW ),
    .AXI_OST     (AXI_OST),
    .SAXIIDW     (AXI_CTRL_IDW)
  )
  u_npu_odma
  (
    `AXIINST(mmio_axi_,odma_mmio_axi_),
    `AXIINST(descr_axi_,odma_descr_axi_) ,
    `AXIWINST(metadata_data_axi_,metadata_data_axi_),
    `AXIWINST(feature_map_data_axi_,feature_map_data_axi_),
    `VMRINST_S(DMA_VM_LANES,vm_rd_,i_nn_vm_rd_,RD_ODMA_VM_IDX), // dma_vm_rd_
    `TRCINST_S(trace_,trace_,1),
    .vmid                     (vmid),
    // Clock, Reset, Interrupt, Event
    .test_mode               (test_mode),
    .irq                     (irq_odma),
    .err_irq                 (err_irq_odma),
    .ievent                  (ievt_odma),
    .devent                  (devt_odma),
    .rst_a                   (rst_a),
    .clk                     (clk)
  );


  //
  // Conv
  //
  npu_conv_top
  #(
    .AXI_SLV_IDW (AXI_CTRL_IDW),
    .NPU_HAS_FLOAT (NPU_HAS_FLOAT)
  )
  u_npu_conv
  (
    // interfaces
    //
    `AXIINST(mmio_axi_,conv_mmio_axi_),
    `AXIINST(descr_axi_,conv_descr_axi_),
    `VMRINST_S(NUM_COEF_QUEUE+NUM_FM_QUEUE+CONV_PAD_LD_LANES,vm_rd_,i_nn_vm_rd_,RD_CONV_FM_IDX), // fm_rd_ + cf_rd_ + pad_rd_
    `AMRINST_S(am_rd_,i_nn_am_rd_,0), // conv_am_rd_
    `AMWINST_S(am_wr_,i_nn_am_wr_,0), // conv_am_wr_
    // Accumulator stream for fused convolution and activation
    `STRINST(acc_,stri_),
    `TRCINST_S(trace_,trace_,2),
    // Clock, Reset, Interrupt, Event
    .test_mode               (test_mode),
    .irq                     (irq_conv),
    .err_irq                 (err_irq_conv),
    .ievt                    (ievt_conv),
    .devt                    (devt_conv),
    .rst_a                   (rst_a),
    .clk                     (clk)
  );


  //
  // Streaming FIFO instance
  //
  npu_fifo
  #(
    .SIZE   ( 2                ),
    .DWIDTH ( $bits(vyixacc_t) ),
    .FRCVAL ( 1'b0             ),
    .FRCACC ( 1'b0             )
  )
  u_str_inst
  (
    .clk          ( clk               ),   // clock
    .rst_a        ( rst_sync     ),   // asynchronous reset, active high, synchronous deassertion
    .valid_write  ( stri_str_valid    ),   // input data valid
    .accept_write ( stri_str_accept   ),   // accept input data
    .data_write   ( stri_str_data     ),   // input data
    .valid_read   ( i_stro_str_valid  ),   // output data valid
    .accept_read  ( i_stro_str_accept ),   // accept output data
    .data_read    ( i_stro_str_data   )    // output data
  );

  // Activation
  //
  npu_gtoa_top
  #(
    .AXI_SLV_IDW (AXI_CTRL_IDW)
  )
  u_npu_gtoa
  (
    // interfaces
    //
    `AXIINST(mmio_axi_,gten_mmio_axi_),
    `AXIINST(descr_axi_,gten_descr_axi_),
    `VMRINST_S(VSIZE,vm_rd_,i_nn_vm_rd_,RD_GTOA_VM0_IDX), // vm0_rd_
    `AMRINST_S(am_rd_,i_nn_am_rd_,1), // am0_rd_
    // Primary accumulator input stream
    `STRINST(acc_,stro_),
    `AMWINST_S(am_wr_,i_nn_am_wr_,1), // gten_am_wr_
    `VMWINST_S(VSIZE,vm_wr_,i_nn_vm_wr_,WR_GTOA_VM_IDX), // gten_vm_wr_
    `VMRINST_S(GTOA_BPAR_LD_LANES,bpar_rd_,i_nn_vm_rd_,RD_GTOA_BPAR_IDX), // bpar_rd_
    `VMRINST_S(GTOA_MPST_LANES,mpst_rd_,i_nn_vm_rd_,RD_GTOA_MPST_IDX), // mpst_rd_
    `VMWINST_S(GTOA_MPST_LANES,mpst_wr_,i_nn_vm_wr_,WR_GTOA_MPST_IDX), // mpst_wr_
    // Trace
    `TRCINST_S(trace_,trace_,3),
    // Clock, Reset, Interrupt, Event
    .test_mode               (test_mode),
    .slc_id                  (arcnum),
    .irq                     (irq_gten),
    .err_irq                 (err_irq_gten),
    .ievt                    (ievt_gten),
    .devt                    (devt_gten),
    .rst_a                   (rst_a),
    .clk                     (clk)
  );


  //
  // L1 ARC
  //


  // ARC_Trace signals - stubbed for L1 core
  logic [31:0] rtt_drd_r;
  logic        rtt_freeze;
  logic [7:0]  rtt_src_num;
  logic        rtt_write_a;
  logic        rtt_read_a;
  logic [31:0] rtt_addr_r;
  logic [31:0] rtt_dwr_r;
  logic        rtt_ss_halt;
  logic        rtt_hw_bp;
  logic        rtt_hw_exc;
  logic        rtt_dbg_halt;
  logic        rtt_rst_applied;
  logic        rtt_uop_is_leave;
  logic        rtt_in_deslot;
  logic        rtt_in_eslot;
  logic        rtt_inst_commit;
  logic [31:1] rtt_inst_addr;
  logic        rtt_cond_valid;
  logic        rtt_cond_pass;
  logic        rtt_branch;
  logic        rtt_branch_indir;
  logic [31:1] rtt_branch_taddr;
  logic        rtt_dslot;
  logic        rtt_exception;
  logic        rtt_exception_rtn;
  logic        rtt_interrupt;
  logic        rtt_sleep_mode;
  logic        rtt_zd_loop;
  logic [7:0]  rtt_wp_val;
  logic        rtt_wp_hit;
  logic        rtt_sw_bp;
  logic [7:0]  rtt_process_id;
  logic        rtt_pid_wr_en;

  assign rtt_drd_r    = 32'b0;
  assign rtt_freeze   = 1'b0;
  assign rtt_src_num  = 8'b0;
  logic [32:0] l1_swe_idata;
  logic        l1_swe_ivalid;

  // CTI interface not used, stub out
  logic        cti_halt;
  logic        cti_break;
  logic        cti_sleep;
  logic        cti_ap_hit;
  logic [7:0]  cti_ap_status;

  assign events_in_a  = {
                        27'h0,           // reserved 69-95
                        l2_event_a[1],   // parent 68
                        3'b0,            // reserved 65-67
                        l2_event_a[0],   // parent 64
                        8'h0,            // reserved 56-63
                        devt_gten,       // gta done 55
                        ievt_gten,       // gta issue 54
                        devt_conv,       // convolution done 53
                        ievt_conv,       // convolution issue 52
                        devt_odma,       // odma done 51
                        ievt_odma,       // odma issue 50
                        devt_idma,       // idma done 49
                        ievt_idma,       // idma issue 48
                        24'h0,           // reserved 24~47
                        {(24-16){1'b0}},// reserved up to 23
                        l1_peer_event_a  // peer event 0-23

                         };
  assign l2_send_event       = ((vm_sel == 4'b0) ? {1'b0, event_send[40]} : {event_send[40], 1'b0});
  assign l1_peer_send_event  = event_send[0+:16];

  logic       err_irqs;
  assign      err_irqs  = err_irq_odma | err_irq_idma |
                          mem_ecc_irq |
                          err_irq_gten | err_irq_conv;
  // map interrupts
  assign arc_irqs_a   = {
                         7'h0,            // irq48-54, unused
                         irq_odma,        // irq47
                         irq_idma,        // irq46
                         irq_gten,        // irq45
                         irq_conv,        // irq44
                         3'h0,            // irq41-43, unused
                         err_irqs,        // irq40
                         16'h0,           // irq24-39, unused, Virtual IRQ of ARCsync (only for L2)
                         arc_irq_a[1],    // irq23, Phy ARCsync EID
                         arc_irq_a[0],    // irq22, Phy ARCsync AC
                         1'b0             // irq21, tie to 0
                        };

  npu_axi_inj_stall
  #(
    .AXIIDW (AXI_DCCM_IDW),
    .AXIAW  (NPU_AXI_ADDR_W),
    .AXIDW  (64),
    .AXIAWUW(1),
    .AXIWUW (1),
    .AXIBUW (1),
    .AXIARUW(1),
    .AXIRUW (1),
    .AXIRGN (NPU_AXI_REGION_W),
    .AXILEN (4)
  ) u_npu_axi_inj_stall (

     .clk                    (clk)
    ,.rst_a                  (rst_a)

    ,.axi_slv_arvalid        (i_descr_axi_arvalid)
    ,.axi_slv_arready        (i_descr_axi_arready)
    ,.axi_slv_arid           (i_descr_axi_arid)
    ,.axi_slv_aruser         (i_descr_axi_aruser)
    ,.axi_slv_araddr         (i_descr_axi_ar.addr)
    ,.axi_slv_arprot         (i_descr_axi_ar.prot)
    ,.axi_slv_arburst        (i_descr_axi_ar.burst[1:0])
    ,.axi_slv_arlen          (i_descr_axi_ar.len)
    ,.axi_slv_arsize         (i_descr_axi_ar.size)
    ,.axi_slv_arcache        (i_descr_axi_ar.cache)
    ,.axi_slv_arlock         (i_descr_axi_ar.lock[0])
    ,.axi_slv_arregion       (i_descr_axi_ar.region)

    ,.axi_slv_awvalid        (i_descr_axi_awvalid)
    ,.axi_slv_awready        (i_descr_axi_awready)
    ,.axi_slv_awid           (i_descr_axi_awid)
    ,.axi_slv_awuser         (i_descr_axi_awuser)
    ,.axi_slv_awaddr         (i_descr_axi_aw.addr)
    ,.axi_slv_awprot         (i_descr_axi_aw.prot)
    ,.axi_slv_awburst        (i_descr_axi_aw.burst[1:0])
    ,.axi_slv_awlen          (i_descr_axi_aw.len)
    ,.axi_slv_awsize         (i_descr_axi_aw.size)
    ,.axi_slv_awcache        (i_descr_axi_aw.cache)
    ,.axi_slv_awlock         (i_descr_axi_aw.lock[0])
    ,.axi_slv_awregion       (i_descr_axi_aw.region)

    ,.axi_slv_rvalid         (i_descr_axi_rvalid)
    ,.axi_slv_rready         (i_descr_axi_rready)
    ,.axi_slv_rdata          (i_descr_axi_rdata)
    ,.axi_slv_rid            (i_descr_axi_rid)
    ,.axi_slv_rresp          (i_descr_axi_rresp[1:0])
    ,.axi_slv_rlast          (i_descr_axi_rlast)
    ,.axi_slv_ruser          (i_descr_axi_ruser)

    ,.axi_slv_wvalid         (i_descr_axi_wvalid)
    ,.axi_slv_wready         (i_descr_axi_wready)
    ,.axi_slv_wdata          (i_descr_axi_wdata)
    ,.axi_slv_wstrb          (i_descr_axi_wstrb)
    ,.axi_slv_wlast          (i_descr_axi_wlast)
    ,.axi_slv_wuser          (i_descr_axi_wuser)

    ,.axi_slv_bvalid         (i_descr_axi_bvalid)
    ,.axi_slv_bready         (i_descr_axi_bready)
    ,.axi_slv_bresp          (i_descr_axi_bresp[1:0])
    ,.axi_slv_buser          (i_descr_axi_buser)
    ,.axi_slv_bid            (i_descr_axi_bid)

    ,.axi_mst_arvalid        (descr_axi_arvalid)
    ,.axi_mst_arready        (descr_axi_arready)
    ,.axi_mst_arid           (descr_axi_arid)
    ,.axi_mst_aruser         (descr_axi_aruser)
    ,.axi_mst_araddr         (descr_axi_ar.addr)
    ,.axi_mst_arprot         (descr_axi_ar.prot)
    ,.axi_mst_arburst        (descr_axi_ar.burst[1:0])
    ,.axi_mst_arlen          (descr_axi_ar.len)
    ,.axi_mst_arsize         (descr_axi_ar.size)
    ,.axi_mst_arcache        (descr_axi_ar.cache)
    ,.axi_mst_arlock         (descr_axi_ar.lock[0])
    ,.axi_mst_arregion       (descr_axi_ar.region)

    ,.axi_mst_awvalid        (descr_axi_awvalid)
    ,.axi_mst_awready        (descr_axi_awready)
    ,.axi_mst_awid           (descr_axi_awid)
    ,.axi_mst_awuser         (descr_axi_awuser)
    ,.axi_mst_awaddr         (descr_axi_aw.addr)
    ,.axi_mst_awprot         (descr_axi_aw.prot)
    ,.axi_mst_awburst        (descr_axi_aw.burst[1:0])
    ,.axi_mst_awlen          (descr_axi_aw.len)
    ,.axi_mst_awsize         (descr_axi_aw.size)
    ,.axi_mst_awcache        (descr_axi_aw.cache)
    ,.axi_mst_awlock         (descr_axi_aw.lock[0])
    ,.axi_mst_awregion       (descr_axi_aw.region)

    ,.axi_mst_rvalid         (descr_axi_rvalid)
    ,.axi_mst_rready         (descr_axi_rready)
    ,.axi_mst_rdata          (descr_axi_rdata)
    ,.axi_mst_rid            (descr_axi_rid)
    ,.axi_mst_rresp          (descr_axi_rresp[1:0])
    ,.axi_mst_rlast          (descr_axi_rlast)
    ,.axi_mst_ruser          (descr_axi_ruser)

    ,.axi_mst_wvalid         (descr_axi_wvalid)
    ,.axi_mst_wready         (descr_axi_wready)
    ,.axi_mst_wdata          (descr_axi_wdata)
    ,.axi_mst_wstrb          (descr_axi_wstrb)
    ,.axi_mst_wlast          (descr_axi_wlast)
    ,.axi_mst_wuser          (descr_axi_wuser)

    ,.axi_mst_bvalid         (descr_axi_bvalid)
    ,.axi_mst_bready         (descr_axi_bready)
    ,.axi_mst_bresp          (descr_axi_bresp[1:0])
    ,.axi_mst_buser          (descr_axi_buser)
    ,.axi_mst_bid            (descr_axi_bid)
  );

  // Instantiation of module hs_cluster_top : L1-ARC Controller
  npuarc_hs_cluster_top
  u_npu_l1_arc
  (
   // Access Memory
   .cbu_axi_arvalid          (cbu_mmio_axi_arvalid ),
   .cbu_axi_arready          (cbu_mmio_axi_arready ),
   .cbu_axi_arid             ({cbudummyarid,cbu_mmio_axi_arid}),
   .cbu_axi_arsize           (cbu_mmio_axi_ar.size ),
   .cbu_axi_arlock           ({cbudummyarlock,cbu_mmio_axi_ar.lock[0]}),
   .cbu_axi_araddr           (cbu_mmio_axi_ar.addr ),
   .cbu_axi_arcache          (cbu_mmio_axi_ar.cache),
   .cbu_axi_arprot           (cbu_mmio_axi_ar.prot ),
   .cbu_axi_arburst          (cbu_mmio_axi_ar.burst[1:0]),
   .cbu_axi_arlen            (cbu_mmio_axi_ar.len  ),
   .cbu_axi_rvalid           (cbu_mmio_axi_rvalid  ),
   .cbu_axi_rready           (cbu_mmio_axi_rready  ),
   .cbu_axi_rid              ({2'b00,cbu_mmio_axi_rid}),
   .cbu_axi_rdata            (cbu_mmio_axi_rdata   ),
   .cbu_axi_rresp            (cbu_mmio_axi_rresp[1:0]),
   .cbu_axi_rlast            (cbu_mmio_axi_rlast   ),
   .cbu_axi_awvalid          (cbu_mmio_axi_awvalid ),
   .cbu_axi_awready          (cbu_mmio_axi_awready ),
   .cbu_axi_awid             ({cbudummyawid,cbu_mmio_axi_awid}),
   .cbu_axi_awaddr           (cbu_mmio_axi_aw.addr ),
   .cbu_axi_awcache          (cbu_mmio_axi_aw.cache),
   .cbu_axi_awprot           (cbu_mmio_axi_aw.prot ),
   .cbu_axi_awlock           ({cbudummyawlock,cbu_mmio_axi_aw.lock[0]}),
   .cbu_axi_awburst          (cbu_mmio_axi_aw.burst[1:0]),
   .cbu_axi_awlen            (cbu_mmio_axi_aw.len  ),
   .cbu_axi_awsize           (cbu_mmio_axi_aw.size ),
   .cbu_axi_wvalid           (cbu_mmio_axi_wvalid  ),
   .cbu_axi_wready           (cbu_mmio_axi_wready  ),
   .cbu_axi_wid              (cbu_dummy_wid        ),
   .cbu_axi_wdata            (cbu_mmio_axi_wdata   ),
   .cbu_axi_wstrb            (cbu_mmio_axi_wstrb   ),
   .cbu_axi_wlast            (cbu_mmio_axi_wlast   ),
   .cbu_axi_bid              ({2'b00,cbu_mmio_axi_bid}),
   .cbu_axi_bvalid           (cbu_mmio_axi_bvalid  ),
   .cbu_axi_bresp            (cbu_mmio_axi_bresp[1:0]),
   .cbu_axi_bready           (cbu_mmio_axi_bready  ),
   // DMI Peripheral
   .sccm_axi_arvalid         (descr_axi_arvalid    ),
   .sccm_axi_arready         (descr_axi_arready    ),
   .sccm_axi_arid            ({10'b0,descr_axi_arid}),
   .sccm_axi_arsize          (descr_axi_ar.size    ),
   .sccm_axi_araddr          (descr_axi_ar.addr[23:0]),
   .sccm_axi_arburst         (descr_axi_ar.burst[1:0]),
   .sccm_axi_arlen           (descr_axi_ar.len     ),
   .sccm_axi_arregion        (descr_axi_ar.region[1:0]),
   .sccm_axi_rvalid          (descr_axi_rvalid     ),
   .sccm_axi_rready          (descr_axi_rready     ),
   .sccm_axi_rid             ({dummy_rid,descr_axi_rid}),
   .sccm_axi_rdata           (descr_axi_rdata      ),
   .sccm_axi_rresp           (descr_axi_rresp[1:0] ),
   .sccm_axi_rlast           (descr_axi_rlast      ),
   .sccm_axi_awvalid         (descr_axi_awvalid    ),
   .sccm_axi_awready         (descr_axi_awready    ),
   .sccm_axi_awid            ({10'b0,descr_axi_awid}),
   .sccm_axi_awaddr          (descr_axi_aw.addr[23:0]),
   .sccm_axi_awburst         (descr_axi_aw.burst[1:0]),
   .sccm_axi_awlen           (descr_axi_aw.len     ),
   .sccm_axi_awsize          (descr_axi_aw.size    ),
   .sccm_axi_awregion        (descr_axi_aw.region[1:0]),
   .sccm_axi_wvalid          (descr_axi_wvalid     ),
   .sccm_axi_wready          (descr_axi_wready     ),
   .sccm_axi_wdata           (descr_axi_wdata      ),
   .sccm_axi_wstrb           (descr_axi_wstrb      ),
   .sccm_axi_wlast           (descr_axi_wlast      ),
   .sccm_axi_bid             ({dummy_bid,descr_axi_bid}),
   .sccm_axi_bvalid          (descr_axi_bvalid     ),
   .sccm_axi_bresp           (descr_axi_bresp[1:0] ),
   .sccm_axi_bready          (descr_axi_bready     ),
   // clock reset interrupts
   .mbus_clk_en              (1'b1                 ),
   .dbus_clk_en              (1'b1                 ),
   .clk                      (clk                  ),
   .rst_a                    (rst_a                ),
   .test_mode                (test_mode            ),
   .watchdog_reset           (watchdog_reset       ),
   .irq17_a                  (1'b0                 ),
   .irq19_a                  (1'b0                 ),
   .irq21_a                  (arc_irqs_a[21]       ),
   .irq22_a                  (arc_irqs_a[22]       ),
   .irq23_a                  (arc_irqs_a[23]       ),
   .irq24_a                  (arc_irqs_a[24]       ),
   .irq25_a                  (arc_irqs_a[25]       ),
   .irq26_a                  (arc_irqs_a[26]       ),
   .irq27_a                  (arc_irqs_a[27]       ),
   .irq28_a                  (arc_irqs_a[28]       ),
   .irq29_a                  (arc_irqs_a[29]       ),
   .irq30_a                  (arc_irqs_a[30]       ),
   .irq31_a                  (arc_irqs_a[31]       ),
   .irq32_a                  (arc_irqs_a[32]       ),
   .irq33_a                  (arc_irqs_a[33]       ),
   .irq34_a                  (arc_irqs_a[34]       ),
   .irq35_a                  (arc_irqs_a[35]       ),
   .irq36_a                  (arc_irqs_a[36]       ),
   .irq37_a                  (arc_irqs_a[37]       ),
   .irq38_a                  (arc_irqs_a[38]       ),
   .irq39_a                  (arc_irqs_a[39]       ),
   .irq40_a                  (arc_irqs_a[40]       ),
   .irq41_a                  (arc_irqs_a[41]       ),
   .irq42_a                  (arc_irqs_a[42]       ),
   .irq43_a                  (arc_irqs_a[43]       ),
   .irq44_a                  (arc_irqs_a[44]       ),
   .irq45_a                  (arc_irqs_a[45]       ),
   .irq46_a                  (arc_irqs_a[46]       ),
   .irq47_a                  (arc_irqs_a[47]       ),
   .irq48_a                  (arc_irqs_a[48]       ),
   .irq49_a                  (arc_irqs_a[49]       ),
   .irq50_a                  (arc_irqs_a[50]       ),
   .irq51_a                  (arc_irqs_a[51]       ),
   .irq52_a                  (arc_irqs_a[52]       ),
   .irq53_a                  (arc_irqs_a[53]       ),
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
   .irq54_a                  (arc_irqs_a[54]       ),
   .wdt_clk                  (wdt_clk              ),
   .wdt_ext_timeout_ack_r    (1'b1                 ),
   .wdt_ext_timeout_r        (                     ), // intentionally left unconnected
   .wdt_reset                (wdt_reset            ),
   .wdt_reset_wdt_clk        (wdt_reset_wdt_clk    ),
   .cc_idle                  (                     ), // intentionally left unconnected

   // ARCsync
   .clusternum               (clusternum           ),
   .arc_halt_req_a           (arc_halt_req_a       ),
   .arc_run_req_a            (arc_run_req_a        ),
   .intvbase_in              (intvbase_in          ),
   .arcnum                   (arcnum               ),
   .arc_halt_ack             (arc_halt_ack         ),
   .arc_run_ack              (arc_run_ack          ),
   .sys_halt_r               (sys_halt_r           ),
   .sys_tf_halt_r            (sys_tf_halt_r        ),
   .sys_sleep_r              (sys_sleep_r          ),
   .sys_sleep_mode_r         (sys_sleep_mode_r     ),
   .dbg_cache_rst_disable    (1'b0                 ),
   .dccm_dmi_priority        (1'b0                 ),

   // Event manager
   .arc_event_a              (arc_evm_event        ),
   .EventManager_evm_event_a (events_in_a          ),
   .EventManager_evm_sleep   (sys_sleep_r          ),
   .EventManager_evm_wakeup  (arc_evm_event        ),
   .EventManager_evm_send    (event_send           ),
   .EventManager_vm_grp0_sid (                     ),
   .EventManager_vm_grp0_ssid(                     ),
   .EventManager_vm_grp1_sid (                     ),
   .EventManager_vm_grp1_ssid(                     ),
   .EventManager_vm_grp2_sid (                     ),
   .EventManager_vm_grp2_ssid(                     ),
   .EventManager_vm_grp3_sid (                     ),
   .EventManager_vm_grp3_ssid(                     ),
   .EventManager_evt_vm_irq  (evt_vm_irq           ),
   .EventManager_evt_vm_sel  (vm_sel               ),

    // ARC_Trace (RTT)
    .rtt_drd_r               (rtt_drd_r            ),
    .rtt_prod_sel            (1'b1                 ),
    .rtt_freeze              (rtt_freeze           ),
    .rtt_src_num             (rtt_src_num          ),
    .rtt_write_a             (rtt_write_a          ),
    .rtt_read_a              (rtt_read_a           ),
    .rtt_addr_r              (rtt_addr_r           ),
    .rtt_dwr_r               (rtt_dwr_r            ),
    .rtt_ss_halt             (rtt_ss_halt          ),
    .rtt_hw_bp               (rtt_hw_bp            ),
    .rtt_hw_exc              (rtt_hw_exc           ),
    .rtt_dbg_halt            (rtt_dbg_halt         ),
    .rtt_rst_applied         (rtt_rst_applied      ),
    .rtt_uop_is_leave        (rtt_uop_is_leave     ),
    .rtt_in_deslot           (rtt_in_deslot        ),
    .rtt_in_eslot            (rtt_in_eslot         ),
    .rtt_inst_commit         (rtt_inst_commit      ),
    .rtt_inst_addr           (rtt_inst_addr        ),
    .rtt_cond_valid          (rtt_cond_valid       ),
    .rtt_cond_pass           (rtt_cond_pass        ),
    .rtt_branch              (rtt_branch           ),
    .rtt_branch_indir        (rtt_branch_indir     ),
    .rtt_branch_taddr        (rtt_branch_taddr     ),
    .rtt_dslot               (rtt_dslot            ),
    .rtt_exception           (rtt_exception        ),
    .rtt_exception_rtn       (rtt_exception_rtn    ),
    .rtt_interrupt           (rtt_interrupt        ),
    .rtt_sleep_mode          (rtt_sleep_mode       ),
    .rtt_zd_loop             (rtt_zd_loop          ),
    .rtt_wp_val              (rtt_wp_val           ),
    .rtt_wp_hit              (rtt_wp_hit           ),
    .rtt_sw_bp               (rtt_sw_bp            ),
    .rtt_process_id          (rtt_process_id       ),
    .rtt_pid_wr_en           (rtt_pid_wr_en        ),
    .rtt_swe_data            (l1_swe_idata         ),
    .rtt_swe_val             (l1_swe_ivalid        ),
    // APB Debug Interface
    .dbg_prot_sel            (arct_dbg_prot_sel    ),
    .pclkdbg_en              (1'b1                 ),
    .presetdbgn              (arct_rst_an          ),
    .paddrdbg                ({16'h0,dbg_paddr}    ),
    .pseldbg                 (dbg_psel             ),
    .penabledbg              (dbg_penable          ),
    .pwritedbg               (dbg_pwrite           ),
    .pwdatadbg               (dbg_pwdata           ),
    .preadydbg               (dbg_pready           ),
    .prdatadbg               (dbg_prdata           ),
    .pslverrdbg              (dbg_pslverr          ),
    .dbgen                   (arct_dbgen           ),
    .niden                   (arct_niden           ),

    // Cross-trigger interface
    .cti_halt                (cti_halt             ),
    .cti_break               (cti_break            ),
    .cti_sleep               (cti_sleep            ),
    .cti_ap_hit              (cti_ap_hit           ),
    .cti_ap_status           (cti_ap_status        ),

    // SRAM power gating
    .mem_ds                  (1'b0                 ),
    .mem_sd                  (pd_mem               ),

   // BVCI Debug Interface
   .dbg_cmdval               (dbg_cmdval           ),
   .dbg_cmdack               (dbg_cmdack           ),
   .dbg_eop                  (dbg_eop              ),
   .dbg_address              (dbg_address          ),
   .dbg_be                   (dbg_be               ),
   .dbg_cmd                  (dbg_cmd              ),
   .dbg_wdata                (dbg_wdata            ),
   .dbg_rspval               (dbg_rspval           ),
   .dbg_rspack               (dbg_rspack           ),
   .dbg_reop                 (dbg_reop             ),
   .dbg_rerr                 (dbg_rerr             ),
   .dbg_rdata                (dbg_rdata            ),
   .debug_reset              (debug_reset          )
  );

  logic rst_trace_sync;
  npu_reset_ctrl
  u_reset_trace_inst
  (
    .clk        ( clk            ),
    .rst_a      ( rst_a          ),
    .test_mode  ( test_mode      ),
    .rst        ( rst_trace_sync )
  );

  // l1arc trace output goes through skid buffer
  // buffer output is accepted after 5 cycles
  npu_skid
  #(
    .W (32)
  )
  u_l1_swe_skid
  (
    .clk         (clk                   ),
    .rst_a       (rst_trace_sync        ),
    .in_valid    (l1_swe_ivalid         ),
    .in_accept   (                      ),  // intentionally unconnected
    .in_data     ({l1_swe_idata[32], l1_swe_idata[30:0]} ),
    .int_valid   (                      ),  // intentionally unconnected
    .out_valid   (trace_valid[4]        ),
    .out_accept  (trace_accept[4]       ),
    .out_data    (trace_id[4]           )
  );

  // multi-cycle path on trace valid and data
  logic [NUM_TRACE_SRC-1:0] trace_valid_mc2;
  logic [NUM_TRACE_SRC-1:0][31:0] trace_data_mc2;

  for (genvar gd = 0; gd < NUM_TRACE_SRC; gd++)
  begin : trc_val_mc2_GEN
    npu_2cyc_checker
    #(
      .WIDTH (1),
      .DISABLE_OPTION (1'b1)
    )
    u_trace_val_mc2_inst
    (
      .clk      ( clk                   ),
      .rst_a    ( rst_trace_sync        ),
      .valid    ( 1'b1                  ),
      .data_in  ( trace_valid[gd]       ),
      .data_out ( trace_valid_mc2[gd]   )
    );
  end : trc_val_mc2_GEN

  for (genvar gd = 0; gd < NUM_TRACE_SRC; gd++)
  begin : trc_dat_mc2_GEN
    npu_2cyc_checker
    #(
      .WIDTH (32)
    )
    u_trace_dat_mc2_inst
    (
      .clk      ( clk                   ),
      .rst_a    ( rst_trace_sync        ),
      .valid    ( trace_valid[gd]       ),
      .data_in  ( trace_id[gd]          ),
      .data_out ( trace_data_mc2[gd]    )
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
      .clk        ( clk                  ),
      .rst_a      ( rst_trace_sync       ),
      .din        ( {1{trace_valid_mc2[gd]}}  ),
      .dout       ( trace_valid_sync[gd] )
    );
  end : cdc_v_GEN

  // valid edge detection
  logic [NUM_TRACE_SRC-1:0] trace_valid_rise;

  for (genvar gd = 0; gd < NUM_TRACE_SRC; gd++)
  begin : val_e_GEN
    npu_trace_edge_detect
    u_trace_valid_edge_detect
    (
      .clk        ( clk                  ),
      .rst_a      ( rst_trace_sync       ),
      .din        ( trace_valid_sync[gd] ),
      .dout       ( trace_valid_rise[gd] )
    );
  end : val_e_GEN

  // skid buffers
  logic [NUM_TRACE_SRC-1:0] trace_skid_valid;
  logic [NUM_TRACE_SRC-1:0] trace_skid_accept;
  logic [NUM_TRACE_SRC-1:0][31:0] trace_skid_data;

  for (genvar gd = 0; gd < NUM_TRACE_SRC; gd++)
  begin : trc_skid_GEN
    npu_skid
    #(
      .W (32)
    )
    u_trace_swe_skid
    (
      .clk         (clk                   ),
      .rst_a       (rst_trace_sync        ),
      .in_valid    (trace_valid_rise[gd]  ),
      .in_accept   (                      ),  // intentionally unconnected
      .in_data     (trace_data_mc2[gd]    ),
      .int_valid   (                      ),  // intentionally unconnected
      .out_valid   (trace_skid_valid[gd]  ),
      .out_accept  (trace_skid_accept[gd] ),
      .out_data    (trace_skid_data[gd]   )
    );
  end : trc_skid_GEN

  // SWE arbitration
  logic        trace_arb_out_valid;
  logic [31:0] trace_arb_out_data;
  npu_trace_arb
  #(
    .NUM ( NUM_TRACE_SRC ),
    .DW  ( 32            )
  )
  u_slice_trace_arb
  (
    .clk             ( clk                 ),
    .rst_a           ( rst_trace_sync      ),
    .in_valid        ( trace_skid_valid    ),
    .in_accept       ( trace_skid_accept   ),
    .in_data         ( trace_skid_data     ),
    .out_valid       ( trace_arb_out_valid ),
    .out_data        ( trace_arb_out_data  )
  );

  logic        i_swe_val;
  logic [32:0] i_swe_data;
  logic [7:0]  i_swe_ext;
  assign rtt_swe_data = i_swe_data;
  assign rtt_swe_ext  = i_swe_ext;
  assign rtt_swe_val  = i_swe_val;

  // MEM_BUS/MEM_MUX
  npu_vm_inj_stall
  #(
    .RD_IDX       ( RD_CONV_PAD_IDX),
    .WR_IDX       ( 0            ),
    .VM_RPORTS    ( VM_RPORTS    ),
    .VM_WPORTS    ( VM_WPORTS    )
  )
  u_vm_inj_stall
  (
    // slave VM write request
    `VMWINST_B(slv_nn_vm_wr_,i_nn_vm_wr_),
    // slave VM read request
    `VMRINST_B(slv_nn_vm_rd_,i_nn_vm_rd_),
    // master VM write request
    `VMWINST_B(mst_nn_vm_wr_,nn_vm_wr_),
    // master VM read request
    `VMRINST_B(mst_nn_vm_rd_,nn_vm_rd_),
    // Clock, Reset
    .rst_a                   (rst_a),
    .clk                     (clk)
  );

  vm_bus
  #(
    .AXI_SLV_IDW  ( AXI_CTRL_IDW ),
    .VM_RPORTS    ( VM_RPORTS    ),
    .VM_WPORTS    ( VM_WPORTS    ),
    .NUM_VM_BANKS ( NUM_VM_BANKS )
  )
  u_vm_bus
    (
    // write request
    `VMWINST_B(nn_vm_wr_,nn_vm_wr_),
    // read request
    `VMRINST_B(nn_vm_rd_,nn_vm_rd_),

    // MMIO slave
    `AXIINST(vm_mmio_axi_,vm_mmio_axi_),

    // muxed request
    `VMINST(vm_,vm_),
    // VM ecc protection
    .vm_prot_en(vm_prot_en),
    `VMINST_ECC(vm_,vm_),
    .vm_sb_err                           (vm_sb_err),
    .vm_db_err                           (vm_db_err),
    // VM Init
    .vm_init(vm_init),
    .vm_init_end(vm_init_end),

    // Clock, Reset
    .rst_a                   (rst_a),
    .test_mode               (test_mode),
    .clk                     (clk)
  );

  npu_am_inj_stall
  #(
    .RD_IDX       ( 1            ), //Convolution read has highest priority
    .WR_IDX       ( 1            ), //Convolution wirte only can be blocked by convolution read, no extra stall need
    .AM_RPORTS    ( AM_RPORTS    ),
    .AM_WPORTS    ( AM_WPORTS    )
  )
  u_am_inj_stall
  (
    // slave write request
    `AMWINST_B(slv_nn_am_wr_,i_nn_am_wr_),
    // slave read request
    `AMRINST_B(slv_nn_am_rd_,i_nn_am_rd_),
    // master write request
    `AMWINST_B(mst_nn_am_wr_,nn_am_wr_),
    // master read request
    `AMRINST_B(mst_nn_am_rd_,nn_am_rd_),

    // Clock, Reset
    .rst_a                   (rst_a),
    .clk                     (clk)
  );

  am_bus
  #(
    .AXI_SLV_IDW ( AXI_CTRL_IDW ),
    .AM_RPORTS   ( AM_RPORTS    ),
    .AM_WPORTS   ( AM_WPORTS    )
  )
  u_am_bus
  (
    // write request
    `AMWINST_B(nn_am_wr_,nn_am_wr_),

    // read request
    `AMRINST_B(nn_am_rd_,nn_am_rd_),

    // MMIO slave
    `AXIINST(am_mmio_axi_,am_mmio_axi_),

    // MUXED request
    `AMINST_MSK(am_,am_),

    // AM ecc protection
    .am_prot_en(am_prot_en),
    `AMINST_ECC(am_,am_),
    .am_sb_err               (am_sb_err),
    .am_db_err               (am_db_err),
    // AM Init
    .am_init(am_init),
    .am_init_end(am_init_end),

    // Clock, Reset
    .rst_a                   (rst_a),
    .test_mode               (test_mode),
    .clk                     (clk)
  );

npu_sfty_top #(
    .SAXIIDW   (AXI_CTRL_IDW),
    .VM_RPORTS (VM_RPORTS+2),
    .AM_RPORTS (AM_RPORTS+1),
    .NUM_VM_BANKS (NUM_VM_BANKS),
    .NUM_AM_BANKS (NUM_AM_BANKS)
) u_npu_sfty (
 // System interface
    `AXIINST(mmio_axi_,sfty_mmio_axi_),
 // ECC result input interface
    .vm_sb_err(vm_sb_err),
    .vm_db_err(vm_db_err),
    .am_sb_err(am_sb_err),
    .am_db_err(am_db_err),

 // mmio ctrl interface
    .vm_init           (vm_init        ),
    .am_init           (am_init        ),
    .vm_init_end       (vm_init_end    ),
    .am_init_end       (am_init_end    ),
    .vm_prot_en        (vm_prot_en     ),
    .am_prot_en        (am_prot_en     ),
 // irq
    .mem_ecc_irq       (mem_ecc_irq    ),
    .vm_ecc_dbe        (vm_ecc_dbe),
    .am_ecc_dbe        (am_ecc_dbe),
    .vm_ecc_sbe        (vm_ecc_sbe),
    .am_ecc_sbe        (am_ecc_sbe),
    // Clock, Reset
    .rst_a             (rst_a          ),
    .test_mode         (test_mode      ),
    .clk               (clk            )
);

  // AXI bus component to split CBU and LBU
  `AXICONFIGWIRES(2,2,arc_axi_map_);
  assign arc_axi_map_decbase[0] = 28'h00_f000_0;    // secondary port is LBU
  assign arc_axi_map_decsize[0] = 28'hff_f000_0;
  assign arc_axi_map_decmst[0]  = 'd2;
  assign arc_axi_map_decbase[1] = '0;               // primary port is data port is default
  assign arc_axi_map_decsize[1] = '0;
  assign arc_axi_map_decmst[1]  = 'd1;

  logic rst_slc_sync;
  npu_reset_ctrl
  u_reset_slice
  (
    .clk        ( clk          ),
    .rst_a      ( rst_a        ),
    .test_mode  ( test_mode    ),
    .rst        ( rst_slc_sync )
  );
  npu_axi_slice
  #(
    .AXIIDW       ( AXI_ARC_IDW     ),
    .AXIDW        ( 64              ),
    .AXIAWUW      ( SLICE_DMA_AWUW  ),
    .AXIWUW       ( SLICE_DMA_WUW   ),
    .AXIBUW       ( SLICE_DMA_BUW   ),
    .AXIARUW      ( SLICE_DMA_ARUW  ),
    .AXIRUW       ( SLICE_DMA_RUW   ),
    .NUMSLC       ( 1               ),
    .AWFIFO_DEPTH ( 1               ),
    .WFIFO_DEPTH  ( 2               ),
    .BFIFO_DEPTH  ( 1               ),
    .ARFIFO_DEPTH ( 1               ),
    .RFIFO_DEPTH  ( 2               )
  )
  u_slc_cbu_inst
  (
   .clk   ( clk      ),
   .rst_a ( rst_slc_sync  ),
   `AXIINST(axi_slv_,cbu_mmio_axi_),
   `AXIINST(axi_mst_,icbu_mmio_axi_)
   );

  logic rst_matrix_sync;
  npu_reset_ctrl
  u_reset_matrix
  (
    .clk        ( clk             ),
    .rst_a      ( rst_a           ),
    .test_mode  ( test_mode       ),
    .rst        ( rst_matrix_sync )
  );

// spyglass disable_block WRN_1459
// SMD: Incompatible connection for rresp and bresp (emu type)
// SJ : Reviewed and already use TYPE Convert
  npu_axi_matrix
  #(
    .NUMSLV  ( 1    ),
    .NUMMST  ( 2    ),
    .NUMAP   ( 2    ),
    .AXIDW   ( 64   ),
    .AXISIDW ( AXI_ARC_IDW        ),
    .AXIMIDW ( AXI_ARC_IDW        ),
    .AXIAWUW ( SLICE_DMA_AWUW     ),
    .AXIWUW  ( SLICE_DMA_WUW      ),
    .AXIBUW  ( SLICE_DMA_BUW      ),
    .AXIARUW ( SLICE_DMA_ARUW     ),
    .AXIRUW  ( SLICE_DMA_RUW      )
  )
  u_axi_arc_routing
  (
    .clk    ( clk   ),
    .rst_a  ( rst_matrix_sync ),
    .ptidx_a( 2'b00       ),
    .decslv ( '1          ),
    `AXIINST(axi_slv_,icbu_mmio_axi_),
    `AXIINST(axi_mst_,arc_axi_),
    `AXICONFIGINST(arc_axi_map_)
  );
// spyglass enable_block WRN_1459

  npu_axi_bridge
  #(
    .AXIIDW   ( AXI_ARC_IDW     ),
    .AXISDW   ( 64              ),
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
  u_axi_cvt_inst
  (
    .clk   ( clk   ),
    .rst_a ( rst_sync ),
    `AXIINSTM(1,axi_slv_,arc_axi_),
    `AXIINST(axi_mst_,arc_mmio_axi_)
  );

  // AXI component
  axi_ctrl_rout
  #(
    .AXI_SLV_IDW ( 1               ),
    .AXI_ARC_IDW ( AXI_ARC_IDW     ),
    .AXI_MST_IDW ( AXI_CTRL_IDW    ),
    .AXIAWUW     ( SLICE_MMIO_AWUW ),
    .AXIWUW      ( SLICE_MMIO_WUW  ),
    .AXIBUW      ( SLICE_MMIO_BUW  ),
    .AXIARUW     ( SLICE_MMIO_ARUW ),
    .AXIRUW      ( SLICE_MMIO_RUW  )
  )
  u_ctrl_axi_routing
  (
    //MMIO Master Output
    `AXIINST(idma_mmio_axi_,idma_mmio_axi_),
    `AXIINST(odma_mmio_axi_,odma_mmio_axi_),
    `AXIINST(conv_mmio_axi_,conv_mmio_axi_),
    `AXIINST(gten_mmio_axi_,gten_mmio_axi_),
    `AXIINST(vm_mmio_axi_,vm_mmio_axi_),
    `AXIINST(am_mmio_axi_,am_mmio_axi_),
    `AXIINST(mmio_descr_axi_,mmio_descr_axi_),
    `AXIINST(sfty_mmio_axi_,sfty_mmio_axi_),
    //MMIO Slave Input
    `AXIINST(mmio_axi_,mmio_axi_),                // AXI MMIO interface from CLN
    `AXIINST(lbu_mmio_axi_,arc_mmio_axi_),        // AXI MMIO interface from ARC
    // Clock, Reset
    .test_mode               (test_mode),
    .rst_a                   (rst_a),
    .clk                     (clk)
  );

  // AXI component
  axi_dccm_rout
  #(
    .AXI_SLV_IDW ( AXI_CTRL_IDW    ),
    .AXI_MST_IDW ( AXI_DCCM_IDW    ),
    .AXIAWUW     ( SLICE_MMIO_AWUW ),
    .AXIWUW      ( SLICE_MMIO_WUW  ),
    .AXIBUW      ( SLICE_MMIO_BUW  ),
    .AXIARUW     ( SLICE_MMIO_ARUW ),
    .AXIRUW      ( SLICE_MMIO_RUW  )
  )
  u_dccm_axi_routing (
    // DESCR Master Output
    `AXIINST(descr_axi_,i_descr_axi_),           // AXI descriptor read/write
    // DESCR Slave Input
    `AXIINST(idma_descr_axi_,idma_descr_axi_),
    `AXIINST(odma_descr_axi_,odma_descr_axi_),
    `AXIINST(conv_descr_axi_,conv_descr_axi_),
    `AXIINST(gten_descr_axi_,gten_descr_axi_),
    `AXIINST(mmio_descr_axi_,mmio_descr_axi_),
    // Clock, Reset
    .test_mode               (test_mode),
    .rst_a                   (rst_a),
    .clk                     (clk)
  );


  // AXI bus component
  axi_data_bus
  #(
    .AXI_SLV_IDW ( AXI_DMA_IDW    ),
    .AXI_ARC_IDW ( AXI_ARC_IDW    ),
    .AXI_MST_IDW ( AXI_DATA_IDW   ),
    .AXIAWUW     ( SLICE_DMA_AWUW ),
    .AXIWUW      ( SLICE_DMA_WUW  ),
    .AXIBUW      ( SLICE_DMA_BUW  ),
    .AXIARUW     ( SLICE_DMA_ARUW ),
    .AXIRUW      ( SLICE_DMA_RUW  )
  )
  u_axi_data_routing
  (
    // Data Slave Input
    `AXIINSTM(0,cbu_mmio_axi_,arc_axi_),        // ARC CBU
    `AXIINST(metadata_data_axi_,metadata_data_axi_),
    `AXIINST(feature_map_data_axi_,feature_map_data_axi_),
    // Data Master Output
    `AXIINST(cln_dev_data_axi_,npu_axi_),
    // Clock, Reset
   .test_mode                (test_mode),
    .rst_a                   (rst_a),
    .clk                     (clk)
  );


  // SRAMs (VM/AM)
  npu_srams
  #(
    .NUM_VM_BANKS(NUM_VM_BANKS)
  )
  u_npu_srams
  (
    // VM Read/Write
    `VMINST(vm_,vm_),
    // AM Read/Write
    `AMINST_MSK(am_,am_),
    `VMINST_ECC(vm_,vm_),
    `AMINST_ECC(am_,am_),
    //
    // Clock, Reset
    .pd_mem                  (pd_mem),
    .rst_a                   (rst_a),
    .clk                     (clk)
  );



npu_slice_aggr #(
    .NUM_TRACE_SRC (NUM_TRACE_SRC)
) u_npu_slice_aggr
(
  .clusternum            (clusternum          ),
  .arcnum                (arcnum              ),
  .rst_trace_sync        (rst_trace_sync      ),
  .trace_valid_in        (trace_valid         ),
  .trace_accept_in       (trace_accept        ),
  .trace_valid_out       (trace_arb_out_valid ),
  .trace_id_out          (trace_arb_out_data  ),

  .i_swe_val             (i_swe_val           ),
  .i_swe_data            (i_swe_data          ),
  .i_swe_ext             (i_swe_ext           ),
  `STRINST(stro_,stro_),
  `STRINST(i_stro_,i_stro_),
  .rst_fifo_sync         (rst_sync),
  .clk                   (clk          )
);

endmodule : npu_slice
