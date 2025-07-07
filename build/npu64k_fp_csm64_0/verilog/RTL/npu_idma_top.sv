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

//
// Top-level file for the iDMA accelerator
//
 
`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_vm_macros.svh"
`include "npu_am_macros.svh"
`include "npu_axi_macros.svh"

// spyglass disable_block W240
// SMD: Declared but not read
// SJ: Reviewed
module npu_idma_top
  import npu_types::*;
  #(
    // MMIO attribute
    parameter SAXIIDW     = 1,
    parameter SAXIAWUW    = 1,
    parameter SAXIWUW     = 1,
    parameter SAXIBUW     = 1,
    parameter SAXIARUW    = 1,
    parameter SAXIRUW     = 1,
    parameter MAXIAWUW    = 1,
    parameter MAXIWUW     = 1,
    parameter MAXIBUW     = 1,
    parameter MAXIARUW    = 1,
    parameter MAXIRUW     = 1, 
    parameter DMAXIAWUW   = 1,
    parameter DMAXIWUW    = 1,
    parameter DMAXIBUW    = 1,
    parameter DMAXIARUW   = 1,
    parameter DMAXIRUW    = 1, 
    // AXI data with XM
    parameter AXI_MST_IDW = 1,
    parameter STU_D       = ISIZE*DMA_VM_LANES*8,
    parameter AXI_OST     = 16, //AXI outstanding number
    parameter AD_WID      = $clog2(DMA_VM_LANES*ISIZE),
    // Iteration Number
    parameter int  N      = NUM_FM_LOOPS
   )
  (
   // interfaces
   //
   `AXISLV(SAXIIDW,64,SAXIAWUW,SAXIWUW,SAXIBUW,SAXIARUW,SAXIRUW,mmio_axi_),                      // AXI MMIO interface
   `AXIMST(AXI_MST_IDW,64,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,descr_axi_),                 // AXI descriptor read/write
   `AXIRMST(AXI_MST_IDW,STU_D,DMAXIAWUW,DMAXIWUW,DMAXIBUW,DMAXIARUW,DMAXIRUW,metadata_data_axi_),     // AXI meta-data read transfer
   `AXIRMST(AXI_MST_IDW,STU_D,DMAXIAWUW,DMAXIWUW,DMAXIBUW,DMAXIARUW,DMAXIRUW,feature_map_data_axi_),  // AXI feature map read data transfer
   `VMWMST(DMA_VM_LANES,vm_wr_),                        // VM write
   `VMRMST(1,vm_rd_),                        // VM Read 
   // interrupt and event
   //
   output logic     irq,                    // level interrupt to processor
   output logic     err_irq,                // level interrupt to processor
   output logic     ievent,                 // issue event pulse to processor
   output logic     devent,                 // done event pulse to processor
   // trace interface
   `TRCMST(trace_,1),
   input  logic [64-1: 0]     vmid,
   //output logic          trace_valid,     // trace valid
   //input  logic          trace_accept,    // trace accept
   //output logic [31:0]   trace_id,        // ID for tracing (from HLAPI), msb = 0 start, msb = 1 end
   // clock and reset
   //
   input logic      test_mode,
   input logic      clk,                    // clock, all logic clocked at posedge
   input logic      rst_a                   // asynchronous reset, active high
   );
// spyglass enable_block W240

   // Local parameters
   typedef enum logic [1:0] { 
     idma_status_idle_e,  // iDMA state is idle
     idma_status_exec_e   // iDMA in-pgress
   } idma_state_t;

   idma_state_t                idma_state_r;
   idma_state_t                idma_state_nxt;
   logic                       idma_state_en;

   logic                       idma_axi_err_r;
   logic                       idma_axi_err_nxt;
   logic                       idma_axi_err_en;

   logic   [2-1:0]             hlapi_v_valid;
   logic   [2-1:0]             hlapi_v_accept;
   logic                       hlapi_i_valid_int;

   // HLAPIs related wires
   logic               clk_en        ;           // clock enable for the accelerator compute core
   logic               clk_gated     ;           // gated clock
   logic               rst           ;           // reset
   logic               rst_dp        ;           // reset compute datapath
   logic               hlapi_i_valid ;           // new HLAPI issue descriptor valid
   logic               hlapi_i_accept;           // new HLAPI issue descriptor accept
   dma_hlapi_i_t       hlapi_i       ;           // HLAPI input descriptor
   logic               hlapi_o_valid ;           // new HLAPI output descriptor valid
   logic               hlapi_o_accept;           // new HLAPI output descriptor accept
   logic [32-1:0]      hlapi_res     ;           // result from datapath to HLAPI
   logic [32-1:0]      hlapi_stat    ;           // AXI status from datapath to HLAPI

   // FM buffer
   logic               ifm_wr_valid;
   logic  [AD_WID-1:0] ifm_wr_num;
   logic  [AD_WID-1:0] ifm_wr_alsb;
   logic  [STU_D-1:0]  ifm_wr_data;
   logic               ifm_wr_accept;

   logic               ivm_rd_accept;
   logic [AD_WID-1:0]  ivm_rd_num;
   logic [AD_WID-1:0]  ivm_rd_alsb;
   logic [STU_D-1:0]   ivm_rd_data;
   logic [15:0]        ivm_vld_size;

   logic               ifm_read_idle;
   logic               ivm_write_idle;

   logic [31:0]        ifm_read_size;
   logic [31:0]        ivm_write_size;
   logic               axi_rd_err;


   //
   // Reset synchronizer
   //
   npu_reset_ctrl
   u_reset_ctrl_inst
     (
     .clk        ( clk       ),
     .rst_a      ( rst_a     ),
     .test_mode  ( test_mode ),
     .rst        ( rst       )
     );
   
   //
   // Clock gate control
   //
   npu_l1_clk_ctrl
   u_l1_clkctrl_inst
     (
     .clk_in       ( clk       ),
     .clock_enable ( clk_en    ),
     .clk_out      ( clk_gated )
     );

   //
   // Broadcast HLAPI handshake signals
   //
   npu_hs_broadcast
     #(.NUM (2))
   u_hs_inst
   (
    .clk        ( clk_gated      ),
    .rst_a      ( rst_dp         ), 
    .hsi_valid  ( hlapi_i_valid_int),
    .hsi_accept ( hlapi_i_accept ),
    .hso_valid  ( hlapi_v_valid  ),
    .hso_accept ( hlapi_v_accept )
   );


   npu_shared_hl_ctrl_dma 
   #(
     .ID(IDMA_ID ),
     .MAJ(IDMA_MAJ ),
     .MIN(IDMA_MIN ),
     .SAXIIDW(SAXIIDW ),
     .SAXIAWUW(SAXIAWUW),
     .SAXIWUW(SAXIWUW ),
     .SAXIBUW(SAXIBUW ),
     .SAXIARUW(SAXIARUW),
     .SAXIRUW(SAXIRUW ),
     .MAXIAWUW(MAXIAWUW),
     .MAXIWUW(MAXIWUW ),
     .MAXIBUW(MAXIBUW ),
     .MAXIARUW(MAXIARUW),
     .MAXIRUW(MAXIRUW ),
     .T (dma_hlapi_i_t)
    ) u_npu_idma_ctrl (
    .clk             (clk   ),
    .rst_a           (rst   ),
    .irq             (irq   ),
    .err_irq         (err_irq   ),
    .ievent          (ievent),
    .devent          (devent),
    .test_mode       (test_mode),
   
    // AXI MMIO interface 64b wide data
    `AXIINST(mmio_axi_,mmio_axi_),

    // AXI DMA master interface for reading/writing descriptors 64b wide data
    `AXIINST(mst_axi_,descr_axi_),

    // Signals to accelerator datapath, controlled by valid/accept handshake
    .clk_en          (clk_en        ),
// spyglass disable_block W402b
//SMD:Reset to flop
//SJ :Intentional generate for error reset
    .rst_dp          (rst_dp        ),
// spyglass enable_block W402b
    .hlapi_i_valid   (hlapi_i_valid ),
    .hlapi_i_accept  (hlapi_i_accept),
    .hlapi_i         (hlapi_i       ),
    .hlapi_o_valid   (hlapi_o_valid ),
    .hlapi_o_accept  (hlapi_o_accept),
    .hlapi_o_res     (hlapi_res     ),
    .hlapi_o_stat    (hlapi_stat    ),
   
    // trace interface
    `TRCINST_B(trace_,trace_)
   );

   npu_idma_fm_read
   #(
     .STU_D (STU_D),
     .MAXIAWUW(DMAXIAWUW),
     .MAXIWUW(DMAXIWUW ),
     .MAXIBUW(DMAXIBUW ),
     .MAXIARUW(DMAXIARUW),
     .MAXIRUW(DMAXIRUW ),
     .AXI_MST_IDW(AXI_MST_IDW),
     .AXI_OST(AXI_OST),
     .META_BUF_SIZE2(1),
     .XM_BUF_SIZE(IXM_BUF_SIZE),
     .N (N)
    ) u_npu_idma_fm_read (
    .hlapi_i_valid   (hlapi_v_valid[0] ),
    .hlapi_i_accept  (hlapi_v_accept[0]),
    .hlapi_i         (hlapi_i.xm_seq   ),
    .hlapi_i_init    (hlapi_i.cnst     ),
    .hlapi_i_gather  (hlapi_i.gather   ),
    .hlapi_i_zero    (hlapi_i.zero_point),
    .hlapi_i_bc      (hlapi_i.bc       ),

    `AXIRINST(idma_fm_axi_,feature_map_data_axi_),      // AXI data transfer, read-only
    `AXIRINST(idma_meta_axi_,metadata_data_axi_),  // AXI data transfer, read-only
    `VMRINST_B(vm_rd_,vm_rd_),
    .vmid            ( vmid            ),

    .fm_wr_valid     (ifm_wr_valid     ),
    .fm_wr_num       (ifm_wr_num       ),
    .fm_wr_alsb      (ifm_wr_alsb      ),
    .fm_wr_data      (ifm_wr_data      ),
    .fm_wr_accept    (ifm_wr_accept    ),

    .fm_rd_trans     (ifm_read_size    ),
    .axi_rd_err      (axi_rd_err       ),
    .idle            (ifm_read_idle    ),
    .rst_dp          (rst_dp           ),
    .clk             (clk_gated        )
    );


  npu_dma_buffer
  #(.SIZEL2 (IXM_BUF_SIZE2),
    .DMA_VM_LANES_L(DMA_VM_LANES)
   )  u_npu_idma_fm_buffer (
   .buffer_wr_valid  (ifm_wr_valid    ),
   .buffer_wr_num    (ifm_wr_num      ),
   .buffer_wr_alsb   (ifm_wr_alsb     ),
   .buffer_wr_data   (ifm_wr_data     ),
   .buffer_wr_accept (ifm_wr_accept   ),

   .buffer_rd_num    (ivm_rd_num      ),
   .buffer_rd_alsb   (ivm_rd_alsb     ),
   .buffer_rd_data   (ivm_rd_data     ),
   .buffer_rd_accept (ivm_rd_accept   ),

   .buffer_vld_size  (ivm_vld_size    ),
   .buffer_clr       (1'b0            ),
   .rst_a            (rst_dp          ),
   .clk              (clk_gated       )
  );

   npu_idma_fm_write
   #(
     .STU_D (STU_D),
     .DMA_S (DMA_VM_LANES),
     .N (N)
    ) u_npu_idma_fm_write (
    .hlapi_i_valid   (hlapi_v_valid[1] ),
    .hlapi_i_accept  (hlapi_v_accept[1]),
    .hlapi_i         (hlapi_i          ),

    `VMWINST_B(vm_wr_,vm_wr_),

    .fm_rd_num       (ivm_rd_num       ),
    .fm_rd_alsb      (ivm_rd_alsb      ),
    .fm_rd_data      (ivm_rd_data      ),
    .fm_rd_accept    (ivm_rd_accept    ),
    .fm_vld_size     (ivm_vld_size     ),

    .idle            (ivm_write_idle   ),
    .rst_dp          (rst_dp           ),
    .clk             (clk_gated        )
    );


  //
  // FSM 
  //
  always_comb
  begin : idma_state_nxt_PROC
    hlapi_o_valid        = 1'b0;
    hlapi_res            = 'b0;
    hlapi_stat           = 'b0;
    idma_axi_err_en      = 1'b0;
    idma_axi_err_nxt     = idma_axi_err_r;
    idma_state_en        = 1'b0;
    idma_state_nxt       = idma_state_r;
    casez (idma_state_r)
      idma_status_exec_e:
        begin
          if (axi_rd_err == 1'b1) begin
            // AXI read error set
            idma_axi_err_en    = 1'b1;
            idma_axi_err_nxt   = 1'b1;
          end
          if (ivm_write_idle && ifm_read_idle) begin
            hlapi_o_valid     = 1'b1;
            hlapi_res         = ifm_read_size;
            hlapi_stat        = {30'b0, idma_axi_err_r, idma_axi_err_r};
            if (hlapi_o_accept) begin
              idma_state_en      = 1'b1;
              idma_state_nxt     = idma_status_idle_e;
              idma_axi_err_en    = 1'b1;
              idma_axi_err_nxt   = 1'b0;
            end
          end
        end
      default: // idma_status_idle_e
        begin
          // idle, wait for next request
          if (hlapi_i_valid && hlapi_i_accept)
          begin
            idma_state_en  = 1'b1;
            idma_state_nxt = idma_status_exec_e;
          end
        end
    endcase // casez (idma_state_r)
  end : idma_state_nxt_PROC

  always_ff @(posedge clk or
              posedge rst_dp)
  begin : reg_pipe_PROC
    if (rst_dp == 1'b1)
    begin
      idma_state_r      <= idma_status_idle_e;
      idma_axi_err_r    <= 'b0;
    end
    else begin
      if (idma_state_en)
        idma_state_r       <= idma_state_nxt;
      if (idma_axi_err_en)
        idma_axi_err_r     <= idma_axi_err_nxt;
    end
  end : reg_pipe_PROC

  assign   hlapi_i_valid_int = (idma_state_r ==  idma_status_idle_e) && hlapi_i_valid;

endmodule : npu_idma_top
