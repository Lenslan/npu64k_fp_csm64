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



module npu_slice_top
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

   localparam logic SLC_HAS_FLOAT=1;
  //
  // local wires
  //
  logic              rst_sync;         // synchronous reset
  logic              dmi_clk_req_a;    // clock request from AXI DMI
  logic              dmi_clk_req_sync; // clock request from AXI DMI
  logic              clk_en_sync;      // synchronized clock enable
  logic              clk_en_eff;       // effective clock enable
// spyglass disable_block W401
// SMD:Clock is not an input
// SJ :intentional generate
  logic              clk_gated;        // gated clock
// spyglass enable_block W401
  logic              dbg_cmdval_sync;
  logic              dbg_cmdval;
  logic              dbg_cmdack;
  logic       [31:0] dbg_address;
  logic       [1:0]  dbg_cmd;
  logic       [31:0] dbg_wdata;
  logic              dbg_rspval;
  logic       [31:0] dbg_rdata;
  logic              debug_reset;
  // Synchronous AXI interface
  `AXIWIRES(1,64,SLICE_MMIO_AWUW,SLICE_MMIO_WUW,SLICE_MMIO_BUW,SLICE_MMIO_ARUW,SLICE_MMIO_RUW,mmio_axi_);
  `AXIWIRES(1,64*VSIZE,SLICE_DMA_AWUW,SLICE_DMA_WUW,SLICE_DMA_BUW,SLICE_DMA_ARUW,SLICE_DMA_RUW,dev_axi_);

  `APBWIRES(16,32,dbg_);
  npu_apb_bridge_tgt
  #(
    .ADDR_WIDTH ( 16 ),
    .DATA_WIDTH ( 32 )
  )
  u_apb_bridge_inst
  (
  .pclk(clk),
  .rst_a(rst_a),
  .test_mode(test_mode),
  `APBINST(tgt_,dbg_),
  `APBASYNCINST(brg_,dbg_as_)
  );



  //
  // Synchronize reset and gate clock at root
  //
  npu_reset_ctrl
  u_reset_ctrl_main
  (
   .clk        ( clk       ),
   .rst_a      ( rst_a     ),
   .test_mode  ( test_mode ),
   .rst        ( rst_sync  )
  );

  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_event_cdc_sync 
  (
    .clk        ( clk         ),
    .rst_a      ( rst_sync    ),
    .din        ( {1{clk_en_a}}    ),
    .dout       ( clk_en_sync )
  );

  npu_cdc_sync
  #(
    .SYNC_FF_LEVELS ( 2 ), 
    .WIDTH          ( 1 ),
    .TMR_CDC        ( 0 )
  ) 
  u_clk_req_cdc_sync 
  (
    .clk        ( clk              ),
    .rst_a      ( rst_sync         ),
    .din        ( {1{dmi_clk_req_a}}    ),
    .dout       ( dmi_clk_req_sync )
  );

  // enable clock from ARCSync or from incoming DMI
  npu_clkgate
  u_npu_slice_clkctrl_inst
  (
    .clk_in       ( clk        ),
    .clock_enable ( clk_en_eff ),
    .clk_out      ( clk_gated  )
  );

  assign  dbg_cmdval_sync = '0;





  //
  // NPU slice
  //
  npu_slice
  #(
    .NPU_HAS_FLOAT (SLC_HAS_FLOAT)
  )
  u_npu_slice
  (
    .vmid                        ( vmid                  ),

    .pd_mem                      ( pd_mem                ),
    .evt_vm_irq                  ( evt_vm_irq            ),
    .wdt_reset                   ( wdt_reset             ),
    .wdt_reset_wdt_clk           ( wdt_reset_wdt_clk     ),
    .clusternum                  ( clusternum            ),
    .arcnum                      ( arcnum                ),
    .intvbase_in                 ( intvbase_in           ),
    .arc_halt_req_a              ( arc_halt_req_a        ),
    .arc_run_req_a               ( arc_run_req_a         ),
    .arc_halt_ack                ( arc_halt_ack          ),
    .arc_run_ack                 ( arc_run_ack           ),
    .sys_halt_r                  ( sys_halt_r            ),
    .sys_tf_halt_r               ( sys_tf_halt_r         ),
    .sys_sleep_r                 ( sys_sleep_r           ),
    .sys_sleep_mode_r            ( sys_sleep_mode_r      ),
    .arc_irq_a                   ( arc_irq_a             ),
    .l2_send_event               ( l2_send_event         ),
    .l2_event_a                  ( l2_event_a            ),
    .l1_peer_send_event          ( l1_peer_send_event    ),
    .l1_peer_event_a             ( l1_peer_event_a       ),
    .dbg_cmdval                  ( dbg_cmdval            ),
    .dbg_cmdack                  ( dbg_cmdack            ),
    .dbg_eop                     ( 1'b1                  ),
    .dbg_address                 ( dbg_address           ),
    .dbg_be                      ( 4'b1111               ),
    .dbg_cmd                     ( dbg_cmd               ),
    .dbg_wdata                   ( dbg_wdata             ),
    .dbg_rspval                  ( dbg_rspval            ),
    .dbg_rspack                  ( 1'b1                  ),
    .dbg_reop                    (                       ), // intentionally unconnected
    .dbg_rerr                    (                       ), // intentionally unconnected
    .dbg_rdata                   ( dbg_rdata             ),
    .debug_reset                 ( debug_reset           ),
    .rtt_swe_val                 (rtt_swe_val            ),
    .rtt_swe_data                (rtt_swe_data           ),
// spyglass disable_block NoFeedThrus-ML
// SMD: Feed-Through
// SJ: The input arcnum and clusternum is constant
    .rtt_swe_ext                 (rtt_swe_ext            ),
// spyglass enable_block NoFeedThrus-ML

    // APB debug
    .arct_dbg_prot_sel           (arct_dbg_prot_sel      ),
    .arct_dbgen                  (arct_dbgen             ),
    .arct_niden                  (arct_niden             ),
    .arct_rst_an                 (arct_rst_an            ),
 
    `APBINST(dbg_,dbg_),
    .wdt_clk                     (wdt_clk                ),
    .ecc_sbe                     (ecc_sbe),
    .ecc_dbe                     (ecc_dbe),
    `AXIINST(mmio_axi_, mmio_axi_),
    `AXIINST(npu_axi_, dev_axi_),
    .clk                         ( clk_gated             ),
    .test_mode                   ( test_mode             ),
    .rst_a                       ( rst_a                 )
   );


  //
  // Convert AXI to GALS initiator interface
  //
  npu_axi_async_ini
  #(
    .AXIIDW         ( 1         ),
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
  u_ini_inst
  (
   .axi_slv_clk   ( clk_gated     ),
   .axi_slv_rst_a ( rst_a         ),
   .tgt_pwr_dwn_a ( 1'b0          ),
   .test_mode     ( test_mode     ),
   `AXIINST(axi_slv_, dev_axi_),
   `AXIASYNCMSUB(axi_async_mst_,npu_axi_gals_)
  );


  //
  // Convert GALS target interface to AXI
  //
  npu_axi_async_tgt
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
  u_tgt_inst
  (
   .axi_mst_clk   ( clk_gated     ),
   .axi_mst_rst_a ( rst_a         ),
   .ini_pwr_dwn_a ( 1'b0          ),
   .test_mode     ( test_mode     ),
   .clk_req_a     ( dmi_clk_req_a ),
   `AXIINST(axi_mst_, mmio_axi_),
   `AXIASYNCSSUB(axi_async_slv_,mmio_axi_gals_)
   );

  npu_slice_top_aggr u_npu_slice_top_aggr
  (
     .dmi_clk_req_sync (dmi_clk_req_sync)
   , .clk_en_sync      (clk_en_sync     )
   , .dbg_cmdval_sync  (dbg_cmdval_sync )
   , .dbg_cmdack       (dbg_cmdack      )
   , .dbg_rspval       (dbg_rspval      )
   , .dbg_rdata        (dbg_rdata       )
   , .dbg_pack_a       (dbg_pack_a      )
   , .debug_reset      (debug_reset     )
   , .clk_en_eff       (clk_en_eff      )
   , .dbg_cmdval       (dbg_cmdval      )
   , .dbg_address      (dbg_address     )
   , .dbg_cmd          (dbg_cmd         )
   , .dbg_wdata        (dbg_wdata       )
   , .dbg_resp         (dbg_resp        )
   , .clk              (clk             )
   , .rst_sync         (rst_sync        )
  );

endmodule : npu_slice_top
