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


`include "npu_macros.svh"
`include "npu_axi_macros.svh"

module npu_ustu_top
  import npu_types::*;
  import npu_stu_types::*;
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
    // AXI data with XM
    parameter AXI_MST_IDW  = 1,
    parameter STU_D        = 512,
    parameter XM_BUF_SIZE2 = 5,
    parameter XM_BUF_SIZE  = 1024,
    parameter AXI_OST      = 16, //AXI outstanding number
    // Iteration Number
    parameter int  N      = NUM_FM_LOOPS
   )
  (
   // interfaces
   //
   `AXISLV(SAXIIDW,64,SAXIAWUW,SAXIWUW,SAXIBUW,SAXIARUW,SAXIRUW,mmio_axi_),            // AXI MMIO interface
   `AXIMST(AXI_MST_IDW,64,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,descr_axi_),           // AXI descriptor read/write
   `AXIMST(AXI_MST_IDW,STU_D,MAXIAWUW,MAXIWUW,MAXIBUW,MAXIARUW,MAXIRUW,stu_fm_axi_),   // AXI FM data transfer
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
   input logic [64-1: 0]     vmid,
   input logic      test_mode,
   input logic      clk,                    // clock, all logic clocked at posedge
   input logic      rst_a                   // asynchronous reset, active high
   );

   // Local parameters
   typedef enum logic [1:0] { 
     stu_status_idle_e,  // STU state is idle
     stu_status_exec_e   // STU in-pgress
   } stu_state_t;

   stu_state_t                stu_state_r;
   stu_state_t                stu_state_nxt;
   logic                      stu_state_en;

   logic [1:0]                stu_axi_err_r;
   logic [1:0]                stu_axi_err_nxt;
   logic [1:0]                stu_axi_err_en;

   logic   [2-1:0]            hlapi_v_valid;
   logic   [2-1:0]            hlapi_v_accept;
   logic                      hlapi_i_valid_int;

   // HLAPIs related wires
   logic                 clk_en        ;           // clock enable for the accelerator compute core
   logic                 clk_gated     ;           // gated clock
   logic                 rst           ;           // reset
   logic                 rst_dp        ;           // reset compute datapath
   logic                 hlapi_i_valid ;           // new HLAPI issue descriptor valid
   logic                 hlapi_i_accept;           // new HLAPI issue descriptor accept
   unified_stu_hlapi_i_t hlapi_i       ;           // HLAPI input descriptor
   logic                 hlapi_o_valid ;           // new HLAPI output descriptor valid
   logic                 hlapi_o_accept;           // new HLAPI output descriptor accept
   logic [32-1:0]        hlapi_res     ;           // result from datapath to HLAPI
   logic [32-1:0]        hlapi_stat    ;           // AXI status from datapath to HLAPI
   logic                 axi_rd_err    ;
   logic                 axi_wr_err    ;

   
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
     .ID(USTU_ID),
     .MAJ(USTU_MAJ),
     .MIN(USTU_MIN),
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
     .T (unified_stu_hlapi_i_t)
    ) u_npu_ustu_ctrl (
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
    .rst_dp          (rst_dp        ),
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

   // FM buffer
   logic               fm_wr_valid;
   logic  [5:0]        fm_wr_num;
   logic  [5:0]        fm_wr_alsb;
   logic  [511:0]      fm_wr_data;
   logic               fm_wr_accept;

   logic               fm_rd_accept;
   logic [5:0]         fm_rd_num;
   logic [5:0]         fm_rd_alsb;
   logic [511:0]       fm_rd_data;
   logic [15:0]        fm_vld_size;

   logic               fm_read_idle;
   logic               fm_write_idle;

   logic [31:0]        fm_read_size;
   logic [31:0]        fm_write_size;

   npu_ustu_fm_read
   #(
     .STU_D       (STU_D),
     .MAXIAWUW(MAXIAWUW),
     .MAXIWUW(MAXIWUW ),
     .MAXIBUW(MAXIBUW ),
     .MAXIARUW(MAXIARUW),
     .MAXIRUW(MAXIRUW ),
     .AXI_MST_IDW (AXI_MST_IDW),
     .BUFFER_SIZE (XM_BUF_SIZE),
     .AXI_OST     (AXI_OST),     
     .N (N)
    ) u_npu_ustu_fm_read (
    .hlapi_i_valid   (hlapi_v_valid[0] ),
    .hlapi_i_accept  (hlapi_v_accept[0]),
    .hlapi_i         (hlapi_i.xmi_seq  ),

    `AXIRINST(stu_fm_axi_,stu_fm_axi_),
    .fm_wr_valid     (fm_wr_valid      ),
    .fm_wr_num       (fm_wr_num        ),
    .fm_wr_alsb      (fm_wr_alsb       ),
    .fm_wr_data      (fm_wr_data       ),
    .fm_wr_accept    (fm_wr_accept     ),

    .buffer_rls_valid(fm_rd_accept     ),
    .buffer_rls      (fm_rd_num        ),
    .fm_rd_trans     (fm_read_size     ),
    .axi_rd_err      (axi_rd_err       ),
    .vmid            (vmid             ),
    .idle            (fm_read_idle     ),
    .rst_dp          (rst_dp           ),
    .clk             (clk_gated        )
    );

  npu_dma_buffer
  #(.SIZEL2 (XM_BUF_SIZE2))
  u_npu_ustu_buffer (
   .buffer_wr_valid  (fm_wr_valid    ),
   .buffer_wr_num    (fm_wr_num      ),
   .buffer_wr_alsb   (fm_wr_alsb     ),
   .buffer_wr_data   (fm_wr_data     ),
   .buffer_wr_accept (fm_wr_accept   ),

   .buffer_rd_num    (fm_rd_num      ),
   .buffer_rd_alsb   (fm_rd_alsb     ),
   .buffer_rd_data   (fm_rd_data     ),
   .buffer_rd_accept (fm_rd_accept   ),

   .buffer_vld_size  (fm_vld_size    ),
   .buffer_clr       (1'b0           ),
   .rst_a            (rst_dp         ),
   .clk              (clk_gated      )
  );

   npu_ustu_fm_write
   #(
     .STU_D       (STU_D),
     .MAXIAWUW(MAXIAWUW),
     .MAXIWUW(MAXIWUW ),
     .MAXIBUW(MAXIBUW ),
     .MAXIARUW(MAXIARUW),
     .MAXIRUW(MAXIRUW ),
     .AXI_MST_IDW (AXI_MST_IDW),
     .BUFFER_SIZE (XM_BUF_SIZE),
     .AXI_OST     (AXI_OST),
     .N (N)
    ) u_npu_ustu_fm_write (
    .hlapi_i_valid   (hlapi_v_valid[1] ),
    .hlapi_i_accept  (hlapi_v_accept[1]),
    .hlapi_i         (hlapi_i.xmo_seq  ),

    `AXIWINST(stu_fm_axi_,stu_fm_axi_),
    .fm_rd_num       (fm_rd_num        ),
    .fm_rd_alsb      (fm_rd_alsb       ),
    .fm_rd_data      (fm_rd_data       ),
    .fm_rd_accept    (fm_rd_accept     ),
    .fm_vld_size     (fm_vld_size      ),

    .vmid            (vmid             ),
    .fm_wr_trans     (fm_write_size    ),
    .axi_wr_err      (axi_wr_err       ),
    .idle            (fm_write_idle    ),
    .rst_dp          (rst_dp           ),
    .clk             (clk_gated        )
    );

  //
  // FSM 
  //
  always_comb
  begin : stu_state_nxt_PROC
    hlapi_o_valid       = 1'b0;
    hlapi_res           = 'b0;
    hlapi_stat          = 'b0;
    stu_axi_err_en      = 2'b0;
    stu_axi_err_nxt     = stu_axi_err_r;
    stu_state_en        = 1'b0;
    stu_state_nxt       = stu_state_r;
    casez (stu_state_r)
      stu_status_exec_e:
        begin
          if (axi_rd_err == 1'b1) begin
            // AXI read error set
            stu_axi_err_en[0]    = 1'b1;
            stu_axi_err_nxt[0]   = 1'b1;
          end
          if (axi_wr_err == 1'b1) begin
            // AXI write error set
            stu_axi_err_en[1]    = 1'b1;
            stu_axi_err_nxt[1]   = 1'b1;
          end
          if (fm_write_idle && fm_read_idle) begin
            hlapi_o_valid     = 1'b1;
// spyglass disable_block W164a
// SMD: RHS 33bits while LHS 32bits 
// SJ: Ignore Overflow 
            hlapi_res         = fm_write_size + fm_read_size;
// spyglass enable_block W164a
            hlapi_stat        = {29'b0, (stu_axi_err_r | {axi_wr_err, axi_rd_err}) , (|stu_axi_err_r | axi_rd_err | axi_wr_err)};
            if (hlapi_o_accept) begin
              stu_state_en      = 1'b1;
              stu_state_nxt     = stu_status_idle_e;
              stu_axi_err_en    = 2'b11;
              stu_axi_err_nxt   = 2'b00;
            end
          end
        end
      default: // stu_status_idle_e
        begin
          // idle, wait for next request
          if (hlapi_i_valid && hlapi_i_accept)
          begin
            stu_state_en  = 1'b1;
            stu_state_nxt = stu_status_exec_e;
          end
        end
    endcase // casez (stu_state_r)
  end : stu_state_nxt_PROC

  always_ff @(posedge clk or
              posedge rst_dp)
  begin : reg_pipe_PROC
    if (rst_dp == 1'b1)
    begin
      stu_state_r      <= stu_status_idle_e;
      stu_axi_err_r    <= 'b0;
    end
    else begin
      if (stu_state_en)
        stu_state_r       <= stu_state_nxt;
      if (stu_axi_err_en[0])
        stu_axi_err_r[0]  <= stu_axi_err_nxt[0];
      if (stu_axi_err_en[1])
        stu_axi_err_r[1]  <= stu_axi_err_nxt[1];
    end
  end : reg_pipe_PROC

  assign  hlapi_i_valid_int = (stu_state_r == stu_status_idle_e) && hlapi_i_valid;
endmodule : npu_ustu_top
