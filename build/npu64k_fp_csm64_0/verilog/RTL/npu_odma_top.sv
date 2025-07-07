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
// Top-level file for the STU accelerator
//

`include "npu_defines.v"
`include "npu_macros.svh"
`include "npu_vm_macros.svh"
`include "npu_am_macros.svh"
`include "npu_axi_macros.svh"



// spyglass disable_block W240
// SMD: Declared but not read
// SJ: Reviewed
module npu_odma_top
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
    parameter STU_D       = DMA_VM_LANES*8*ISIZE,
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
   `AXIWMST(AXI_MST_IDW,STU_D,DMAXIAWUW,DMAXIWUW,DMAXIBUW,DMAXIARUW,DMAXIRUW,metadata_data_axi_),     // AXI metadata transfer
   `AXIWMST(AXI_MST_IDW,STU_D,DMAXIAWUW,DMAXIWUW,DMAXIBUW,DMAXIARUW,DMAXIRUW,feature_map_data_axi_),  // AXI feature map data transfer
   `VMRMST(DMA_VM_LANES,vm_rd_),             // VM read
// spyglass enable_block W240
   // interrupt and event
   //
   output logic     irq,                    // level interrupt to processor
   output logic     err_irq,                // level interrupt to processor
   output logic     ievent,                 // issue event pulse to processor
   output logic     devent,                 // done event pulse to processor
   // trace interface
   `TRCMST(trace_,1),
   //output logic          trace_valid,     // trace valid
   //input  logic          trace_accept,    // trace accept
   //output logic [31:0]   trace_id,        // ID for tracing (from HLAPI), msb = 0 start, msb = 1 end
   // clock and reset
   //
   input  logic [64-1: 0]        vmid,
   input logic      test_mode,
   input logic      clk,                    // clock, all logic clocked at posedge
   input logic      rst_a                   // asynchronous reset, active high
   );

   // Local parameters
   typedef enum logic [1:0] { 
     odma_status_idle_e,  // STU state is idle
     odma_status_exec_e   // STU in-pgress
   } odma_state_t;

   odma_state_t                odma_state_r;
   odma_state_t                odma_state_nxt;
   logic                       odma_state_en;

   logic                       odma_axi_err_r;
   logic                       odma_axi_err_nxt;
   logic                       odma_axi_err_en;

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
   logic               ivm_wr_valid;
   logic  [AD_WID-1:0] ivm_wr_num;
   logic  [AD_WID-1:0] ivm_wr_alsb;
   logic  [STU_D-1:0]  ivm_wr_data;   
   logic               ivm_wr_accept;

   logic               ifm_rd_accept;
   logic [AD_WID-1:0]  ifm_rd_num;
   logic [AD_WID-1:0]  ifm_rd_alsb;
   logic [STU_D-1:0]   ifm_rd_data; 
   logic [15:0]        ifm_vld_size;

   logic               ivm_read_idle;
   logic               ifm_write_idle;

   logic [31:0]        ifm_write_size;
   logic               axi_wr_err;



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
     .ID(ODMA_ID ),
     .MAJ(ODMA_MAJ ),
     .MIN(ODMA_MIN ),
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
    ) u_npu_dma_ctrl (
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

   npu_odma_fm_read
   #(
     .STU_D (STU_D),
     .DMA_S (DMA_VM_LANES),
     .N (N)
    ) u_npu_odma_fm_read (
    .hlapi_i_valid   (hlapi_v_valid[0] ),
    .hlapi_i_accept  (hlapi_v_accept[0]),
    .hlapi_i         (hlapi_i          ),

    .fm_wr_valid     (ivm_wr_valid     ),
    .fm_wr_num       (ivm_wr_num       ),
    .fm_wr_alsb      (ivm_wr_alsb      ),
    .fm_wr_data      (ivm_wr_data      ),
    .fm_wr_accept    (ivm_wr_accept    ),

    // VM access Interface
    `VMRINST_B(vm_rd_,vm_rd_),

    .idle            (ivm_read_idle    ),
    .rst_dp          (rst_dp           ),
    .clk             (clk_gated        )
    );


   //odma use half buffer for store
   npu_dma_buffer
   #(.SIZEL2 (2),
    .DMA_VM_LANES_L(DMA_VM_LANES)
    ) u_npu_odma_fm_buffer (
    .buffer_wr_valid  (ivm_wr_valid    ),
    .buffer_wr_num    (ivm_wr_num      ),
    .buffer_wr_alsb   (ivm_wr_alsb     ),
    .buffer_wr_data   (ivm_wr_data     ),
    .buffer_wr_accept (ivm_wr_accept   ),

    .buffer_rd_num    (ifm_rd_num      ),
    .buffer_rd_alsb   (ifm_rd_alsb     ),
    .buffer_rd_data   (ifm_rd_data     ),
    .buffer_rd_accept (ifm_rd_accept   ),

    .buffer_vld_size  (ifm_vld_size    ),
    .buffer_clr       (1'b0            ),
    .rst_a            (rst_dp          ),
    .clk              (clk_gated       )
   );

   npu_stu_fm_write
   #(
     .STU_D (STU_D),
     .DMA_VM_LANES_L(DMA_VM_LANES),
     .AXI_MST_IDW (AXI_MST_IDW),
     .META_BUF_SIZE2(1),
     .MAXIAWUW(DMAXIAWUW),
     .MAXIWUW(DMAXIWUW ),
     .MAXIBUW(DMAXIBUW ),
     .MAXIARUW(DMAXIARUW),
     .MAXIRUW(DMAXIRUW ),
     .XM_BUF_SIZE2(OXM_BUF_SIZE2),
     .XM_BUF_SIZE(OXM_BUF_SIZE),
     .AXI_OST     (AXI_OST),
     .N (N)
    ) u_npu_odma_fm_write (
    .hlapi_i_valid   (hlapi_v_valid[1] ),
    .hlapi_i_accept  (hlapi_v_accept[1]),
    .hlapi_i         (hlapi_i.xm_seq   ),
    .hlapi_i_zero    (hlapi_i.zero_point),

    `AXIWINST(stu_fm_axi_,feature_map_data_axi_),  // AXI data transfer, write-only
    `AXIWINST(stu_meta_axi_,metadata_data_axi_),  // AXI data transfer, read-only
    .fm_rd_num       (ifm_rd_num       ),
    .fm_rd_alsb      (ifm_rd_alsb      ),
    .fm_rd_data      (ifm_rd_data      ),
    .fm_rd_accept    (ifm_rd_accept    ),
    .fm_vld_size     (ifm_vld_size     ),

    .vmid            (vmid             ),
    .read_idle       (ivm_read_idle    ),
    .fm_wr_trans     (ifm_write_size   ),
    .axi_wr_err      (axi_wr_err       ),
    .idle            (ifm_write_idle   ),
    .rst_dp          (rst_dp           ),
    .clk             (clk_gated        )
    );

  //
  // FSM 
  //
  always_comb
  begin : odma_state_nxt_PROC
    hlapi_o_valid        = 1'b0;
    hlapi_res            = 'b0;
    hlapi_stat           = 'b0;
    odma_axi_err_en      = 1'b0;
    odma_axi_err_nxt     = odma_axi_err_r;
    odma_state_en        = 1'b0;
    odma_state_nxt       = odma_state_r;
    casez (odma_state_r)
      odma_status_exec_e:
        begin
          if (axi_wr_err == 1'b1) begin
            // AXI write error set
            odma_axi_err_en    = 1'b1;
            odma_axi_err_nxt   = 1'b1;
          end
          if (ifm_write_idle) begin
            hlapi_o_valid     = 1'b1;
            hlapi_res         = ifm_write_size;
            hlapi_stat        = {29'b0, odma_axi_err_r, 1'b0, odma_axi_err_r};
            if (hlapi_o_accept) begin
              odma_state_en      = 1'b1;
              odma_state_nxt     = odma_status_idle_e;
              odma_axi_err_en    = 1'b1;
              odma_axi_err_nxt   = 1'b0;
            end
          end
        end
      default: // odma_status_idle_e
        begin
          // idle, wait for next request
          if (hlapi_i_valid && hlapi_i_accept)
          begin
            odma_state_en  = 1'b1;
            odma_state_nxt = odma_status_exec_e;
          end
        end
    endcase // casez (odma_state_r)
  end : odma_state_nxt_PROC

  //
  always_ff @(posedge clk or
              posedge rst_dp)
  begin : reg_pipe_PROC
    if (rst_dp == 1'b1)
    begin
      odma_state_r      <= odma_status_idle_e;
      odma_axi_err_r    <= 'b0;
    end
    else begin
      if (odma_state_en)
        odma_state_r       <= odma_state_nxt;
      if (odma_axi_err_en)
        odma_axi_err_r  <= odma_axi_err_nxt;
    end
  end : reg_pipe_PROC
  //
  assign   hlapi_i_valid_int = (odma_state_r  ==  odma_status_idle_e) && hlapi_i_valid;


endmodule : npu_odma_top
