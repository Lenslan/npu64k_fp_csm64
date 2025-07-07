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

`include "arcsync_defines.v"
module arcsync_ac
#(
  parameter ADDR_WIDTH      = 32,
  parameter DATA_WIDTH      = 32,
  parameter logic [31:0] AC_NUM       = 32'd3,
  parameter AC_WIDTH        = 8,
  parameter logic [31:0] CORE_NUM     = 32'd1,
  parameter VIRT_MACHINES = 8,
  parameter CLUSTER_NUM = 4,
  parameter VIRT_PROC = CLUSTER_NUM, // It's specification.
  parameter EVT_DURATION    = 5
)
(
  input     logic       [CORE_NUM-1:0]    arcsync_core_exist,                 
  input     logic       [CORE_NUM-1:0]    arcsync_core_wr_enable,
    input     logic       [VIRT_PROC-1:0] arcsync_vm0_core_exist,
    input     logic       [VIRT_PROC-1:0] arcsync_vm0_core_wr_enable,
    input     logic       [VIRT_PROC-1:0] arcsync_vm1_core_exist,
    input     logic       [VIRT_PROC-1:0] arcsync_vm1_core_wr_enable,
    input     logic       [VIRT_PROC-1:0] arcsync_vm2_core_exist,
    input     logic       [VIRT_PROC-1:0] arcsync_vm2_core_wr_enable,
    input     logic       [VIRT_PROC-1:0] arcsync_vm3_core_exist,
    input     logic       [VIRT_PROC-1:0] arcsync_vm3_core_wr_enable,
    input     logic       [VIRT_PROC-1:0] arcsync_vm4_core_exist,
    input     logic       [VIRT_PROC-1:0] arcsync_vm4_core_wr_enable,
    input     logic       [VIRT_PROC-1:0] arcsync_vm5_core_exist,
    input     logic       [VIRT_PROC-1:0] arcsync_vm5_core_wr_enable,
    input     logic       [VIRT_PROC-1:0] arcsync_vm6_core_exist,
    input     logic       [VIRT_PROC-1:0] arcsync_vm6_core_wr_enable,
    input     logic       [VIRT_PROC-1:0] arcsync_vm7_core_exist,
    input     logic       [VIRT_PROC-1:0] arcsync_vm7_core_wr_enable,
  input     logic                         mmio_sel,   // select target register group, valid at the cycle when *en is high
  input     logic       [ADDR_WIDTH-1:0]  mmio_addr,  // register address, valid at the cycle when *en is high
  input     logic                         mmio_wen,   // write enable for register
  input     logic                         mmio_ren,   // read enable for register
  output    logic       [DATA_WIDTH-1:0]  mmio_rdata, // read data, valid at the cycle when ren is high
  input     logic       [DATA_WIDTH-1:0]  mmio_wdata, // write data, valid at the cycle when wen is high
  output    logic       [1:0]             mmio_resp,  // {err, ack} the response is received at the cycle when *en is high
  // IRQ and Event

      ///////////////// Non-VM mode IRQ/Event /////////////////
      output    logic       [CORE_NUM-1:0]    arcsync_core_irq,
      output    logic       [CORE_NUM-1:0]    arcsync_core_event,

      /////////////////  VM mode IRQ/Event /////////////////
      output    logic       [VIRT_PROC-1:0]    vm0_arcsync_core_irq,
      output    logic       [VIRT_PROC-1:0]    vm0_arcsync_core_event,

      output    logic       [VIRT_PROC-1:0]    vm1_arcsync_core_irq,
      output    logic       [VIRT_PROC-1:0]    vm1_arcsync_core_event,

      output    logic       [VIRT_PROC-1:0]    vm2_arcsync_core_irq,
      output    logic       [VIRT_PROC-1:0]    vm2_arcsync_core_event,

      output    logic       [VIRT_PROC-1:0]    vm3_arcsync_core_irq,
      output    logic       [VIRT_PROC-1:0]    vm3_arcsync_core_event,

      output    logic       [VIRT_PROC-1:0]    vm4_arcsync_core_irq,
      output    logic       [VIRT_PROC-1:0]    vm4_arcsync_core_event,

      output    logic       [VIRT_PROC-1:0]    vm5_arcsync_core_irq,
      output    logic       [VIRT_PROC-1:0]    vm5_arcsync_core_event,

      output    logic       [VIRT_PROC-1:0]    vm6_arcsync_core_irq,
      output    logic       [VIRT_PROC-1:0]    vm6_arcsync_core_event,

      output    logic       [VIRT_PROC-1:0]    vm7_arcsync_core_irq,
      output    logic       [VIRT_PROC-1:0]    vm7_arcsync_core_event,


  // Clock, reset and configuration
  input     logic               rst_a,      // Asynchronous reset, active high
  input     logic               clk         // Clock
);
localparam EVT_DUR_WIDTH=$clog2(EVT_DURATION);
localparam logic [31:0]  ADDR_AC_NOTIFY_SRC  =`ADDR_AC_NOTIFY_SRC;  
localparam logic [31:0]  ADDR_AC_ACK_IRQ     =`ADDR_AC_ACK_IRQ;     
localparam logic [31:0]  ADDR_AC_CONFIG      =`ADDR_AC_CONFIG;      
localparam logic [31:0]  ADDR_AC_CONTROL     =`ADDR_AC_CONTROL;     

  localparam logic [ADDR_WIDTH-1:0] ADDR_VM0_AC_NOTIFY_SRC = `ADDR_VM0_AC_NOTIFY_SRC;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM0_AC_ACK_IRQ    = `ADDR_VM0_AC_ACK_IRQ;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM0_AC_CONTROL    = `ADDR_VM0_AC_CONTROL;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM1_AC_NOTIFY_SRC = `ADDR_VM1_AC_NOTIFY_SRC;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM1_AC_ACK_IRQ    = `ADDR_VM1_AC_ACK_IRQ;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM1_AC_CONTROL    = `ADDR_VM1_AC_CONTROL;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM2_AC_NOTIFY_SRC = `ADDR_VM2_AC_NOTIFY_SRC;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM2_AC_ACK_IRQ    = `ADDR_VM2_AC_ACK_IRQ;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM2_AC_CONTROL    = `ADDR_VM2_AC_CONTROL;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM3_AC_NOTIFY_SRC = `ADDR_VM3_AC_NOTIFY_SRC;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM3_AC_ACK_IRQ    = `ADDR_VM3_AC_ACK_IRQ;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM3_AC_CONTROL    = `ADDR_VM3_AC_CONTROL;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM4_AC_NOTIFY_SRC = `ADDR_VM4_AC_NOTIFY_SRC;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM4_AC_ACK_IRQ    = `ADDR_VM4_AC_ACK_IRQ;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM4_AC_CONTROL    = `ADDR_VM4_AC_CONTROL;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM5_AC_NOTIFY_SRC = `ADDR_VM5_AC_NOTIFY_SRC;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM5_AC_ACK_IRQ    = `ADDR_VM5_AC_ACK_IRQ;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM5_AC_CONTROL    = `ADDR_VM5_AC_CONTROL;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM6_AC_NOTIFY_SRC = `ADDR_VM6_AC_NOTIFY_SRC;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM6_AC_ACK_IRQ    = `ADDR_VM6_AC_ACK_IRQ;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM6_AC_CONTROL    = `ADDR_VM6_AC_CONTROL;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM7_AC_NOTIFY_SRC = `ADDR_VM7_AC_NOTIFY_SRC;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM7_AC_ACK_IRQ    = `ADDR_VM7_AC_ACK_IRQ;
  localparam logic [ADDR_WIDTH-1:0] ADDR_VM7_AC_CONTROL    = `ADDR_VM7_AC_CONTROL;
//-------------------------------------------------------------------------------------------------------
// MMIO Registers
//-------------------------------------------------------------------------------------------------------
// Atomic Counter
//-------------------------------------------------------------------------------------------------------
  
    ///////////////// Non-VM mode signal declaration /////////////////
    logic [AC_NUM-1:0]                   [DATA_WIDTH-1:0]  AC_CONFIG;          // Initialize and configure an atomic counter to be used for barrier or semaphore. For each Atomic Counters
    logic             [CORE_NUM-1:0][DATA_WIDTH-1:0]  AC_NOTIFY_SRC;      // Get the AC ID that sent an interrupt
    logic             [CORE_NUM-1:0][DATA_WIDTH-1:0]  AC_ACK_IRQ;         // Acknowledge the interrupt received from the AC
    logic [AC_NUM-1:0][CORE_NUM-1:0][DATA_WIDTH-1:0]  AC_CONTROL;         // Request an increment/decrement and optional notification from the atomic counter for this core
    logic                                                  valid_req;
    logic             [CORE_NUM-1:0]                  ac_ack_irq_en;
    logic             [CORE_NUM-1:0]                  ac_ntf_src_en;
    logic [AC_NUM-1:0]                                     ac_config_en;
    logic [AC_NUM-1:0][CORE_NUM-1:0]                  ac_control_en;
    logic [AC_NUM-1:0]                                     ac_ctrl_per_ac_en;
    logic             [CORE_NUM-1:0]                  ac_ack_irq_wen;
    logic [AC_NUM-1:0]                                     ac_config_wen;
    logic [AC_NUM-1:0][CORE_NUM-1:0]                  ac_control_wen;
    logic [AC_NUM-1:0]                                     ac_control_per_ac_wen;
    logic             [CORE_NUM-1:0][EVT_DUR_WIDTH:0] evt_duration_r;
    logic             [CORE_NUM-1:0][EVT_DUR_WIDTH:0] evt_duration_nxt;
    logic             [CORE_NUM-1:0]                  evt_sending_r;
    logic             [CORE_NUM-1:0]                  evt_sending_nxt;
    logic                                                  irq_sending_r[CORE_NUM];
    logic                                                  irq_sending_nxt[CORE_NUM];
    logic             [CORE_NUM-1:0]                  notify_sending;
    logic             [CORE_NUM-1:0][15:0]            ac_notify_src_r; 
    logic             [CORE_NUM-1:0][15:0]            ac_notify_src_nxt; 
    logic             [CORE_NUM-1:0]                  ac_notify_reg_en; 

    logic                                 ctrl_decr;
    logic                                 ctrl_incr;
    logic                                 ctrl_wait;
    logic                                 ctrl_poll;
    logic [AC_NUM-1:0][CORE_NUM-1:0] ctrl_decr_req;
    logic [AC_NUM-1:0][CORE_NUM-1:0] ctrl_incr_req;
    logic [AC_NUM-1:0][CORE_NUM-1:0] ctrl_req_notify_r;
    logic [AC_NUM-1:0][CORE_NUM-1:0] ctrl_req_notify_nxt;
    logic [AC_NUM-1:0][CORE_NUM-1:0] ctrl_req_pending_r;
    logic [AC_NUM-1:0][CORE_NUM:0]   ctrl_req_pending_r_2s_comp;
    logic [AC_NUM-1:0][CORE_NUM-1:0] ctrl_req_pending_nxt;
    logic [AC_NUM-1:0][CORE_NUM-1:0] ctrl_notify_type_r;
    logic [AC_NUM-1:0][CORE_NUM-1:0] ctrl_notify_type_nxt;
    logic [AC_NUM-1:0][CORE_NUM-1:0] ctrl_cmp_res_r;
    logic [AC_NUM-1:0][CORE_NUM-1:0] ctrl_cmp_res_nxt;

    logic [AC_NUM-1:0][CORE_NUM-1:0] ac_first_pending_core; 
    logic [CORE_NUM-1:0][AC_NUM-1:0] core_notify;
    logic [CORE_NUM-1:0][AC_NUM-1:0] core_req_pending;
    logic [CORE_NUM-1:0][AC_NUM-1:0] core_irq_pending;

  
    /////////////////  VM mode signal declaration /////////////////
    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM0_AC_NOTIFY_SRC;      // Get the AC ID that sent an interrupt
    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM0_AC_ACK_IRQ;         // Acknowledge the interrupt received from the AC
    logic [AC_NUM-1:0][VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM0_AC_CONTROL;         // Request an increment/decrement and optional notification from the atomic counter for this core
    logic                                                  vm0_valid_req;
    logic             [VIRT_PROC-1:0]                  vm0_ac_ack_irq_en;
    logic             [VIRT_PROC-1:0]                  vm0_ac_ntf_src_en;
    logic [AC_NUM-1:0]                                     vm0_ac_config_en;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm0_ac_control_en;
    logic [AC_NUM-1:0]                                     vm0_ac_ctrl_per_ac_en;
    logic             [VIRT_PROC-1:0]                  vm0_ac_ack_irq_wen;
    logic [AC_NUM-1:0]                                     vm0_ac_config_wen;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm0_ac_control_wen;
    logic [AC_NUM-1:0]                                     vm0_ac_control_per_ac_wen;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm0_evt_duration_r;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm0_evt_duration_nxt;
    logic             [VIRT_PROC-1:0]                  vm0_evt_sending_r;
    logic             [VIRT_PROC-1:0]                  vm0_evt_sending_nxt;
    logic                                                  vm0_irq_sending_r[VIRT_PROC];
    logic                                                  vm0_irq_sending_nxt[VIRT_PROC];
    logic             [VIRT_PROC-1:0]                  vm0_notify_sending;
    logic             [VIRT_PROC-1:0][15:0]            vm0_ac_notify_src_r; 
    logic             [VIRT_PROC-1:0][15:0]            vm0_ac_notify_src_nxt; 
    logic             [VIRT_PROC-1:0]                  vm0_ac_notify_reg_en; 

    logic                                 vm0_ctrl_decr;
    logic                                 vm0_ctrl_incr;
    logic                                 vm0_ctrl_wait;
    logic                                 vm0_ctrl_poll;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ctrl_decr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ctrl_incr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ctrl_req_notify_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ctrl_req_notify_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ctrl_req_pending_r;
    logic [AC_NUM-1:0][VIRT_PROC:0]   vm0_ctrl_req_pending_r_2s_comp;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ctrl_req_pending_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ctrl_notify_type_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ctrl_notify_type_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ctrl_cmp_res_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ctrl_cmp_res_nxt;

    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm0_ac_first_pending_core; 
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm0_core_notify;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm0_core_req_pending;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm0_core_irq_pending;

    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM1_AC_NOTIFY_SRC;      // Get the AC ID that sent an interrupt
    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM1_AC_ACK_IRQ;         // Acknowledge the interrupt received from the AC
    logic [AC_NUM-1:0][VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM1_AC_CONTROL;         // Request an increment/decrement and optional notification from the atomic counter for this core
    logic                                                  vm1_valid_req;
    logic             [VIRT_PROC-1:0]                  vm1_ac_ack_irq_en;
    logic             [VIRT_PROC-1:0]                  vm1_ac_ntf_src_en;
    logic [AC_NUM-1:0]                                     vm1_ac_config_en;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm1_ac_control_en;
    logic [AC_NUM-1:0]                                     vm1_ac_ctrl_per_ac_en;
    logic             [VIRT_PROC-1:0]                  vm1_ac_ack_irq_wen;
    logic [AC_NUM-1:0]                                     vm1_ac_config_wen;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm1_ac_control_wen;
    logic [AC_NUM-1:0]                                     vm1_ac_control_per_ac_wen;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm1_evt_duration_r;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm1_evt_duration_nxt;
    logic             [VIRT_PROC-1:0]                  vm1_evt_sending_r;
    logic             [VIRT_PROC-1:0]                  vm1_evt_sending_nxt;
    logic                                                  vm1_irq_sending_r[VIRT_PROC];
    logic                                                  vm1_irq_sending_nxt[VIRT_PROC];
    logic             [VIRT_PROC-1:0]                  vm1_notify_sending;
    logic             [VIRT_PROC-1:0][15:0]            vm1_ac_notify_src_r; 
    logic             [VIRT_PROC-1:0][15:0]            vm1_ac_notify_src_nxt; 
    logic             [VIRT_PROC-1:0]                  vm1_ac_notify_reg_en; 

    logic                                 vm1_ctrl_decr;
    logic                                 vm1_ctrl_incr;
    logic                                 vm1_ctrl_wait;
    logic                                 vm1_ctrl_poll;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ctrl_decr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ctrl_incr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ctrl_req_notify_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ctrl_req_notify_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ctrl_req_pending_r;
    logic [AC_NUM-1:0][VIRT_PROC:0]   vm1_ctrl_req_pending_r_2s_comp;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ctrl_req_pending_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ctrl_notify_type_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ctrl_notify_type_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ctrl_cmp_res_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ctrl_cmp_res_nxt;

    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm1_ac_first_pending_core; 
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm1_core_notify;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm1_core_req_pending;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm1_core_irq_pending;

    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM2_AC_NOTIFY_SRC;      // Get the AC ID that sent an interrupt
    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM2_AC_ACK_IRQ;         // Acknowledge the interrupt received from the AC
    logic [AC_NUM-1:0][VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM2_AC_CONTROL;         // Request an increment/decrement and optional notification from the atomic counter for this core
    logic                                                  vm2_valid_req;
    logic             [VIRT_PROC-1:0]                  vm2_ac_ack_irq_en;
    logic             [VIRT_PROC-1:0]                  vm2_ac_ntf_src_en;
    logic [AC_NUM-1:0]                                     vm2_ac_config_en;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm2_ac_control_en;
    logic [AC_NUM-1:0]                                     vm2_ac_ctrl_per_ac_en;
    logic             [VIRT_PROC-1:0]                  vm2_ac_ack_irq_wen;
    logic [AC_NUM-1:0]                                     vm2_ac_config_wen;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm2_ac_control_wen;
    logic [AC_NUM-1:0]                                     vm2_ac_control_per_ac_wen;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm2_evt_duration_r;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm2_evt_duration_nxt;
    logic             [VIRT_PROC-1:0]                  vm2_evt_sending_r;
    logic             [VIRT_PROC-1:0]                  vm2_evt_sending_nxt;
    logic                                                  vm2_irq_sending_r[VIRT_PROC];
    logic                                                  vm2_irq_sending_nxt[VIRT_PROC];
    logic             [VIRT_PROC-1:0]                  vm2_notify_sending;
    logic             [VIRT_PROC-1:0][15:0]            vm2_ac_notify_src_r; 
    logic             [VIRT_PROC-1:0][15:0]            vm2_ac_notify_src_nxt; 
    logic             [VIRT_PROC-1:0]                  vm2_ac_notify_reg_en; 

    logic                                 vm2_ctrl_decr;
    logic                                 vm2_ctrl_incr;
    logic                                 vm2_ctrl_wait;
    logic                                 vm2_ctrl_poll;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ctrl_decr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ctrl_incr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ctrl_req_notify_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ctrl_req_notify_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ctrl_req_pending_r;
    logic [AC_NUM-1:0][VIRT_PROC:0]   vm2_ctrl_req_pending_r_2s_comp;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ctrl_req_pending_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ctrl_notify_type_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ctrl_notify_type_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ctrl_cmp_res_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ctrl_cmp_res_nxt;

    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm2_ac_first_pending_core; 
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm2_core_notify;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm2_core_req_pending;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm2_core_irq_pending;

    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM3_AC_NOTIFY_SRC;      // Get the AC ID that sent an interrupt
    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM3_AC_ACK_IRQ;         // Acknowledge the interrupt received from the AC
    logic [AC_NUM-1:0][VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM3_AC_CONTROL;         // Request an increment/decrement and optional notification from the atomic counter for this core
    logic                                                  vm3_valid_req;
    logic             [VIRT_PROC-1:0]                  vm3_ac_ack_irq_en;
    logic             [VIRT_PROC-1:0]                  vm3_ac_ntf_src_en;
    logic [AC_NUM-1:0]                                     vm3_ac_config_en;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm3_ac_control_en;
    logic [AC_NUM-1:0]                                     vm3_ac_ctrl_per_ac_en;
    logic             [VIRT_PROC-1:0]                  vm3_ac_ack_irq_wen;
    logic [AC_NUM-1:0]                                     vm3_ac_config_wen;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm3_ac_control_wen;
    logic [AC_NUM-1:0]                                     vm3_ac_control_per_ac_wen;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm3_evt_duration_r;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm3_evt_duration_nxt;
    logic             [VIRT_PROC-1:0]                  vm3_evt_sending_r;
    logic             [VIRT_PROC-1:0]                  vm3_evt_sending_nxt;
    logic                                                  vm3_irq_sending_r[VIRT_PROC];
    logic                                                  vm3_irq_sending_nxt[VIRT_PROC];
    logic             [VIRT_PROC-1:0]                  vm3_notify_sending;
    logic             [VIRT_PROC-1:0][15:0]            vm3_ac_notify_src_r; 
    logic             [VIRT_PROC-1:0][15:0]            vm3_ac_notify_src_nxt; 
    logic             [VIRT_PROC-1:0]                  vm3_ac_notify_reg_en; 

    logic                                 vm3_ctrl_decr;
    logic                                 vm3_ctrl_incr;
    logic                                 vm3_ctrl_wait;
    logic                                 vm3_ctrl_poll;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ctrl_decr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ctrl_incr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ctrl_req_notify_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ctrl_req_notify_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ctrl_req_pending_r;
    logic [AC_NUM-1:0][VIRT_PROC:0]   vm3_ctrl_req_pending_r_2s_comp;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ctrl_req_pending_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ctrl_notify_type_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ctrl_notify_type_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ctrl_cmp_res_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ctrl_cmp_res_nxt;

    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm3_ac_first_pending_core; 
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm3_core_notify;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm3_core_req_pending;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm3_core_irq_pending;

    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM4_AC_NOTIFY_SRC;      // Get the AC ID that sent an interrupt
    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM4_AC_ACK_IRQ;         // Acknowledge the interrupt received from the AC
    logic [AC_NUM-1:0][VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM4_AC_CONTROL;         // Request an increment/decrement and optional notification from the atomic counter for this core
    logic                                                  vm4_valid_req;
    logic             [VIRT_PROC-1:0]                  vm4_ac_ack_irq_en;
    logic             [VIRT_PROC-1:0]                  vm4_ac_ntf_src_en;
    logic [AC_NUM-1:0]                                     vm4_ac_config_en;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm4_ac_control_en;
    logic [AC_NUM-1:0]                                     vm4_ac_ctrl_per_ac_en;
    logic             [VIRT_PROC-1:0]                  vm4_ac_ack_irq_wen;
    logic [AC_NUM-1:0]                                     vm4_ac_config_wen;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm4_ac_control_wen;
    logic [AC_NUM-1:0]                                     vm4_ac_control_per_ac_wen;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm4_evt_duration_r;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm4_evt_duration_nxt;
    logic             [VIRT_PROC-1:0]                  vm4_evt_sending_r;
    logic             [VIRT_PROC-1:0]                  vm4_evt_sending_nxt;
    logic                                                  vm4_irq_sending_r[VIRT_PROC];
    logic                                                  vm4_irq_sending_nxt[VIRT_PROC];
    logic             [VIRT_PROC-1:0]                  vm4_notify_sending;
    logic             [VIRT_PROC-1:0][15:0]            vm4_ac_notify_src_r; 
    logic             [VIRT_PROC-1:0][15:0]            vm4_ac_notify_src_nxt; 
    logic             [VIRT_PROC-1:0]                  vm4_ac_notify_reg_en; 

    logic                                 vm4_ctrl_decr;
    logic                                 vm4_ctrl_incr;
    logic                                 vm4_ctrl_wait;
    logic                                 vm4_ctrl_poll;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ctrl_decr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ctrl_incr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ctrl_req_notify_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ctrl_req_notify_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ctrl_req_pending_r;
    logic [AC_NUM-1:0][VIRT_PROC:0]   vm4_ctrl_req_pending_r_2s_comp;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ctrl_req_pending_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ctrl_notify_type_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ctrl_notify_type_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ctrl_cmp_res_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ctrl_cmp_res_nxt;

    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm4_ac_first_pending_core; 
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm4_core_notify;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm4_core_req_pending;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm4_core_irq_pending;

    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM5_AC_NOTIFY_SRC;      // Get the AC ID that sent an interrupt
    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM5_AC_ACK_IRQ;         // Acknowledge the interrupt received from the AC
    logic [AC_NUM-1:0][VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM5_AC_CONTROL;         // Request an increment/decrement and optional notification from the atomic counter for this core
    logic                                                  vm5_valid_req;
    logic             [VIRT_PROC-1:0]                  vm5_ac_ack_irq_en;
    logic             [VIRT_PROC-1:0]                  vm5_ac_ntf_src_en;
    logic [AC_NUM-1:0]                                     vm5_ac_config_en;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm5_ac_control_en;
    logic [AC_NUM-1:0]                                     vm5_ac_ctrl_per_ac_en;
    logic             [VIRT_PROC-1:0]                  vm5_ac_ack_irq_wen;
    logic [AC_NUM-1:0]                                     vm5_ac_config_wen;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm5_ac_control_wen;
    logic [AC_NUM-1:0]                                     vm5_ac_control_per_ac_wen;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm5_evt_duration_r;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm5_evt_duration_nxt;
    logic             [VIRT_PROC-1:0]                  vm5_evt_sending_r;
    logic             [VIRT_PROC-1:0]                  vm5_evt_sending_nxt;
    logic                                                  vm5_irq_sending_r[VIRT_PROC];
    logic                                                  vm5_irq_sending_nxt[VIRT_PROC];
    logic             [VIRT_PROC-1:0]                  vm5_notify_sending;
    logic             [VIRT_PROC-1:0][15:0]            vm5_ac_notify_src_r; 
    logic             [VIRT_PROC-1:0][15:0]            vm5_ac_notify_src_nxt; 
    logic             [VIRT_PROC-1:0]                  vm5_ac_notify_reg_en; 

    logic                                 vm5_ctrl_decr;
    logic                                 vm5_ctrl_incr;
    logic                                 vm5_ctrl_wait;
    logic                                 vm5_ctrl_poll;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ctrl_decr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ctrl_incr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ctrl_req_notify_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ctrl_req_notify_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ctrl_req_pending_r;
    logic [AC_NUM-1:0][VIRT_PROC:0]   vm5_ctrl_req_pending_r_2s_comp;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ctrl_req_pending_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ctrl_notify_type_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ctrl_notify_type_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ctrl_cmp_res_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ctrl_cmp_res_nxt;

    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm5_ac_first_pending_core; 
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm5_core_notify;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm5_core_req_pending;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm5_core_irq_pending;

    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM6_AC_NOTIFY_SRC;      // Get the AC ID that sent an interrupt
    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM6_AC_ACK_IRQ;         // Acknowledge the interrupt received from the AC
    logic [AC_NUM-1:0][VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM6_AC_CONTROL;         // Request an increment/decrement and optional notification from the atomic counter for this core
    logic                                                  vm6_valid_req;
    logic             [VIRT_PROC-1:0]                  vm6_ac_ack_irq_en;
    logic             [VIRT_PROC-1:0]                  vm6_ac_ntf_src_en;
    logic [AC_NUM-1:0]                                     vm6_ac_config_en;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm6_ac_control_en;
    logic [AC_NUM-1:0]                                     vm6_ac_ctrl_per_ac_en;
    logic             [VIRT_PROC-1:0]                  vm6_ac_ack_irq_wen;
    logic [AC_NUM-1:0]                                     vm6_ac_config_wen;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm6_ac_control_wen;
    logic [AC_NUM-1:0]                                     vm6_ac_control_per_ac_wen;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm6_evt_duration_r;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm6_evt_duration_nxt;
    logic             [VIRT_PROC-1:0]                  vm6_evt_sending_r;
    logic             [VIRT_PROC-1:0]                  vm6_evt_sending_nxt;
    logic                                                  vm6_irq_sending_r[VIRT_PROC];
    logic                                                  vm6_irq_sending_nxt[VIRT_PROC];
    logic             [VIRT_PROC-1:0]                  vm6_notify_sending;
    logic             [VIRT_PROC-1:0][15:0]            vm6_ac_notify_src_r; 
    logic             [VIRT_PROC-1:0][15:0]            vm6_ac_notify_src_nxt; 
    logic             [VIRT_PROC-1:0]                  vm6_ac_notify_reg_en; 

    logic                                 vm6_ctrl_decr;
    logic                                 vm6_ctrl_incr;
    logic                                 vm6_ctrl_wait;
    logic                                 vm6_ctrl_poll;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ctrl_decr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ctrl_incr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ctrl_req_notify_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ctrl_req_notify_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ctrl_req_pending_r;
    logic [AC_NUM-1:0][VIRT_PROC:0]   vm6_ctrl_req_pending_r_2s_comp;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ctrl_req_pending_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ctrl_notify_type_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ctrl_notify_type_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ctrl_cmp_res_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ctrl_cmp_res_nxt;

    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm6_ac_first_pending_core; 
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm6_core_notify;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm6_core_req_pending;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm6_core_irq_pending;

    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM7_AC_NOTIFY_SRC;      // Get the AC ID that sent an interrupt
    logic             [VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM7_AC_ACK_IRQ;         // Acknowledge the interrupt received from the AC
    logic [AC_NUM-1:0][VIRT_PROC-1:0][DATA_WIDTH-1:0]  VM7_AC_CONTROL;         // Request an increment/decrement and optional notification from the atomic counter for this core
    logic                                                  vm7_valid_req;
    logic             [VIRT_PROC-1:0]                  vm7_ac_ack_irq_en;
    logic             [VIRT_PROC-1:0]                  vm7_ac_ntf_src_en;
    logic [AC_NUM-1:0]                                     vm7_ac_config_en;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm7_ac_control_en;
    logic [AC_NUM-1:0]                                     vm7_ac_ctrl_per_ac_en;
    logic             [VIRT_PROC-1:0]                  vm7_ac_ack_irq_wen;
    logic [AC_NUM-1:0]                                     vm7_ac_config_wen;
    logic [AC_NUM-1:0][VIRT_PROC-1:0]                  vm7_ac_control_wen;
    logic [AC_NUM-1:0]                                     vm7_ac_control_per_ac_wen;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm7_evt_duration_r;
    logic             [VIRT_PROC-1:0][EVT_DUR_WIDTH:0] vm7_evt_duration_nxt;
    logic             [VIRT_PROC-1:0]                  vm7_evt_sending_r;
    logic             [VIRT_PROC-1:0]                  vm7_evt_sending_nxt;
    logic                                                  vm7_irq_sending_r[VIRT_PROC];
    logic                                                  vm7_irq_sending_nxt[VIRT_PROC];
    logic             [VIRT_PROC-1:0]                  vm7_notify_sending;
    logic             [VIRT_PROC-1:0][15:0]            vm7_ac_notify_src_r; 
    logic             [VIRT_PROC-1:0][15:0]            vm7_ac_notify_src_nxt; 
    logic             [VIRT_PROC-1:0]                  vm7_ac_notify_reg_en; 

    logic                                 vm7_ctrl_decr;
    logic                                 vm7_ctrl_incr;
    logic                                 vm7_ctrl_wait;
    logic                                 vm7_ctrl_poll;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ctrl_decr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ctrl_incr_req;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ctrl_req_notify_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ctrl_req_notify_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ctrl_req_pending_r;
    logic [AC_NUM-1:0][VIRT_PROC:0]   vm7_ctrl_req_pending_r_2s_comp;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ctrl_req_pending_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ctrl_notify_type_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ctrl_notify_type_nxt;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ctrl_cmp_res_r;
    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ctrl_cmp_res_nxt;

    logic [AC_NUM-1:0][VIRT_PROC-1:0] vm7_ac_first_pending_core; 
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm7_core_notify;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm7_core_req_pending;
    logic [VIRT_PROC-1:0][AC_NUM-1:0] vm7_core_irq_pending;


logic [AC_NUM-1:0][AC_WIDTH-1:0] cfg_cnt_r;     
logic [AC_NUM-1:0][AC_WIDTH-1:0] cfg_cnt_nxt;     
logic [AC_NUM-1:0][AC_WIDTH-1:0] cfg_cnt_ini;
logic [AC_NUM-1:0][AC_WIDTH-1:0] cfg_bound_r;
logic [AC_NUM-1:0][AC_WIDTH-1:0] cfg_bound_nxt;
logic [AC_NUM-1:0][1:0]          cfg_bx_r;
logic [AC_NUM-1:0][1:0]          cfg_bx_nxt;
logic [AC_NUM-1:0]               cfg_bx_sem;
logic [AC_NUM-1:0]               cfg_bx_bar;
logic [AC_NUM-1:0]               cfg_bx_idx;

logic [AC_NUM-1:0]               ac_reg_en;

logic vm_ac_ack_irq_en;
logic vm_ac_ntf_src_en;
logic vm_ac_ack_irq_wen;
logic vm_ac_ctrl_per_ac_en;
logic vm_ac_control_per_ac_wen;
logic vm_ac_config_en;
logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ac_first_pending_core;
logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ctrl_req_notify_r;
logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ctrl_req_pending_r;
logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ctrl_notify_type_r;
logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ctrl_cmp_res_r;

logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ctrl_decr_req;
logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ctrl_incr_req;
logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ctrl_req_notify_nxt;
logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ctrl_req_pending_nxt;
logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ctrl_notify_type_nxt;
logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ctrl_cmp_res_nxt;

logic [AC_NUM-1:0][VIRT_PROC-1:0] vm_ac_control_wen;

//-------------------------------------------------------------------------------------------------------
// Output Assignment 
//-------------------------------------------------------------------------------------------------------
assign  mmio_resp = {(mmio_sel && !valid_req), mmio_sel};

always_comb  
begin: ac_output_PROC
  for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
  begin : ac_set_PROC   
    AC_CONFIG[j] = {{6{1'b0}}, cfg_bx_r[j], 
                    {12-AC_WIDTH{1'b0}}, cfg_bound_r[j],
                    {12-AC_WIDTH{1'b0}}, cfg_cnt_r[j]};

        /////////////////////////// Non-VM mode ///////////////////////////
        for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
        begin: clst0_ac_set_ctrl_PROC  
          AC_CONTROL[j][i] = {{28{1'b0}}, ctrl_req_pending_r[j][i],
                                       {1'b0}, ctrl_notify_type_r[j][i],
                                       ctrl_cmp_res_r[j][i]};
        end: clst0_ac_set_ctrl_PROC // for core_num/vproc }

          for (int unsigned i=18; i<((0+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
          begin: clst0_ac_set_ctrl_asign0_PROC
            AC_CONTROL[j][i] = 32'h0;
          end: clst0_ac_set_ctrl_asign0_PROC // for core_num }

        for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
        begin: clst1_ac_set_ctrl_PROC  
          AC_CONTROL[j][i] = {{28{1'b0}}, ctrl_req_pending_r[j][i],
                                       {1'b0}, ctrl_notify_type_r[j][i],
                                       ctrl_cmp_res_r[j][i]};
        end: clst1_ac_set_ctrl_PROC // for core_num/vproc }

          for (int unsigned i=36; i<((1+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
          begin: clst1_ac_set_ctrl_asign0_PROC
            AC_CONTROL[j][i] = 32'h0;
          end: clst1_ac_set_ctrl_asign0_PROC // for core_num }

        for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
        begin: clst2_ac_set_ctrl_PROC  
          AC_CONTROL[j][i] = {{28{1'b0}}, ctrl_req_pending_r[j][i],
                                       {1'b0}, ctrl_notify_type_r[j][i],
                                       ctrl_cmp_res_r[j][i]};
        end: clst2_ac_set_ctrl_PROC // for core_num/vproc }

          for (int unsigned i=65; i<((2+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
          begin: clst2_ac_set_ctrl_asign0_PROC
            AC_CONTROL[j][i] = 32'h0;
          end: clst2_ac_set_ctrl_asign0_PROC // for core_num }


        ///////////////////////////  VM mode ///////////////////////////
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm0_ac_set_ctrl_PROC  
          VM0_AC_CONTROL[j][i] = {{28{1'b0}}, vm0_ctrl_req_pending_r[j][i],
                                       {1'b0}, vm0_ctrl_notify_type_r[j][i],
                                       vm0_ctrl_cmp_res_r[j][i]};
        end: vm0_ac_set_ctrl_PROC // for core_num/vproc }

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm1_ac_set_ctrl_PROC  
          VM1_AC_CONTROL[j][i] = {{28{1'b0}}, vm1_ctrl_req_pending_r[j][i],
                                       {1'b0}, vm1_ctrl_notify_type_r[j][i],
                                       vm1_ctrl_cmp_res_r[j][i]};
        end: vm1_ac_set_ctrl_PROC // for core_num/vproc }

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm2_ac_set_ctrl_PROC  
          VM2_AC_CONTROL[j][i] = {{28{1'b0}}, vm2_ctrl_req_pending_r[j][i],
                                       {1'b0}, vm2_ctrl_notify_type_r[j][i],
                                       vm2_ctrl_cmp_res_r[j][i]};
        end: vm2_ac_set_ctrl_PROC // for core_num/vproc }

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm3_ac_set_ctrl_PROC  
          VM3_AC_CONTROL[j][i] = {{28{1'b0}}, vm3_ctrl_req_pending_r[j][i],
                                       {1'b0}, vm3_ctrl_notify_type_r[j][i],
                                       vm3_ctrl_cmp_res_r[j][i]};
        end: vm3_ac_set_ctrl_PROC // for core_num/vproc }

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm4_ac_set_ctrl_PROC  
          VM4_AC_CONTROL[j][i] = {{28{1'b0}}, vm4_ctrl_req_pending_r[j][i],
                                       {1'b0}, vm4_ctrl_notify_type_r[j][i],
                                       vm4_ctrl_cmp_res_r[j][i]};
        end: vm4_ac_set_ctrl_PROC // for core_num/vproc }

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm5_ac_set_ctrl_PROC  
          VM5_AC_CONTROL[j][i] = {{28{1'b0}}, vm5_ctrl_req_pending_r[j][i],
                                       {1'b0}, vm5_ctrl_notify_type_r[j][i],
                                       vm5_ctrl_cmp_res_r[j][i]};
        end: vm5_ac_set_ctrl_PROC // for core_num/vproc }

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm6_ac_set_ctrl_PROC  
          VM6_AC_CONTROL[j][i] = {{28{1'b0}}, vm6_ctrl_req_pending_r[j][i],
                                       {1'b0}, vm6_ctrl_notify_type_r[j][i],
                                       vm6_ctrl_cmp_res_r[j][i]};
        end: vm6_ac_set_ctrl_PROC // for core_num/vproc }

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm7_ac_set_ctrl_PROC  
          VM7_AC_CONTROL[j][i] = {{28{1'b0}}, vm7_ctrl_req_pending_r[j][i],
                                       {1'b0}, vm7_ctrl_notify_type_r[j][i],
                                       vm7_ctrl_cmp_res_r[j][i]};
        end: vm7_ac_set_ctrl_PROC // for core_num/vproc }


  end: ac_set_PROC // for AC_NUM }

      /////////////////////////// Non-VM mode ///////////////////////////
      for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
      begin: clst0_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        AC_NOTIFY_SRC[i]      ={{16'b0}, ac_notify_src_r[i]};
        AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|core_irq_pending[i]) || irq_sending_r[i])};  
        arcsync_core_irq[i]   = irq_sending_r[i]; 
        arcsync_core_event[i] = evt_sending_r[i];
        notify_sending[i]     = |core_notify[i] || arcsync_core_irq[i] || (evt_duration_r[i]!='b0);
      end: clst0_ntf_send_PROC // for core_num/vproc }

        for (int unsigned i=18; i<((0+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
        begin: clst0_ntf_send_asign0_PROC
          // set pending interrupt from the ctrl request coming to the interrupt acking
          AC_NOTIFY_SRC[i]      =32'h0;
          AC_ACK_IRQ[i]         =32'h0;  
          arcsync_core_irq[i]   = 1'h0; 
          arcsync_core_event[i] = 1'h0;
          notify_sending[i]     = 1'h0;
        end: clst0_ntf_send_asign0_PROC // for core_num }


      for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
      begin: clst1_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        AC_NOTIFY_SRC[i]      ={{16'b0}, ac_notify_src_r[i]};
        AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|core_irq_pending[i]) || irq_sending_r[i])};  
        arcsync_core_irq[i]   = irq_sending_r[i]; 
        arcsync_core_event[i] = evt_sending_r[i];
        notify_sending[i]     = |core_notify[i] || arcsync_core_irq[i] || (evt_duration_r[i]!='b0);
      end: clst1_ntf_send_PROC // for core_num/vproc }

        for (int unsigned i=36; i<((1+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
        begin: clst1_ntf_send_asign0_PROC
          // set pending interrupt from the ctrl request coming to the interrupt acking
          AC_NOTIFY_SRC[i]      =32'h0;
          AC_ACK_IRQ[i]         =32'h0;  
          arcsync_core_irq[i]   = 1'h0; 
          arcsync_core_event[i] = 1'h0;
          notify_sending[i]     = 1'h0;
        end: clst1_ntf_send_asign0_PROC // for core_num }


      for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
      begin: clst2_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        AC_NOTIFY_SRC[i]      ={{16'b0}, ac_notify_src_r[i]};
        AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|core_irq_pending[i]) || irq_sending_r[i])};  
        arcsync_core_irq[i]   = irq_sending_r[i]; 
        arcsync_core_event[i] = evt_sending_r[i];
        notify_sending[i]     = |core_notify[i] || arcsync_core_irq[i] || (evt_duration_r[i]!='b0);
      end: clst2_ntf_send_PROC // for core_num/vproc }

        for (int unsigned i=65; i<((2+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
        begin: clst2_ntf_send_asign0_PROC
          // set pending interrupt from the ctrl request coming to the interrupt acking
          AC_NOTIFY_SRC[i]      =32'h0;
          AC_ACK_IRQ[i]         =32'h0;  
          arcsync_core_irq[i]   = 1'h0; 
          arcsync_core_event[i] = 1'h0;
          notify_sending[i]     = 1'h0;
        end: clst2_ntf_send_asign0_PROC // for core_num }


    
      ///////////////////////////  VM mode ///////////////////////////
      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm0_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        VM0_AC_NOTIFY_SRC[i]      ={{16'b0}, vm0_ac_notify_src_r[i]};
        VM0_AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|vm0_core_irq_pending[i]) || vm0_irq_sending_r[i])};  
        vm0_arcsync_core_irq[i]   = vm0_irq_sending_r[i]; 
        vm0_arcsync_core_event[i] = vm0_evt_sending_r[i];
        vm0_notify_sending[i]     = |vm0_core_notify[i] || vm0_arcsync_core_irq[i] || (vm0_evt_duration_r[i]!='b0);
      end: vm0_ntf_send_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm1_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        VM1_AC_NOTIFY_SRC[i]      ={{16'b0}, vm1_ac_notify_src_r[i]};
        VM1_AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|vm1_core_irq_pending[i]) || vm1_irq_sending_r[i])};  
        vm1_arcsync_core_irq[i]   = vm1_irq_sending_r[i]; 
        vm1_arcsync_core_event[i] = vm1_evt_sending_r[i];
        vm1_notify_sending[i]     = |vm1_core_notify[i] || vm1_arcsync_core_irq[i] || (vm1_evt_duration_r[i]!='b0);
      end: vm1_ntf_send_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm2_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        VM2_AC_NOTIFY_SRC[i]      ={{16'b0}, vm2_ac_notify_src_r[i]};
        VM2_AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|vm2_core_irq_pending[i]) || vm2_irq_sending_r[i])};  
        vm2_arcsync_core_irq[i]   = vm2_irq_sending_r[i]; 
        vm2_arcsync_core_event[i] = vm2_evt_sending_r[i];
        vm2_notify_sending[i]     = |vm2_core_notify[i] || vm2_arcsync_core_irq[i] || (vm2_evt_duration_r[i]!='b0);
      end: vm2_ntf_send_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm3_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        VM3_AC_NOTIFY_SRC[i]      ={{16'b0}, vm3_ac_notify_src_r[i]};
        VM3_AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|vm3_core_irq_pending[i]) || vm3_irq_sending_r[i])};  
        vm3_arcsync_core_irq[i]   = vm3_irq_sending_r[i]; 
        vm3_arcsync_core_event[i] = vm3_evt_sending_r[i];
        vm3_notify_sending[i]     = |vm3_core_notify[i] || vm3_arcsync_core_irq[i] || (vm3_evt_duration_r[i]!='b0);
      end: vm3_ntf_send_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm4_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        VM4_AC_NOTIFY_SRC[i]      ={{16'b0}, vm4_ac_notify_src_r[i]};
        VM4_AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|vm4_core_irq_pending[i]) || vm4_irq_sending_r[i])};  
        vm4_arcsync_core_irq[i]   = vm4_irq_sending_r[i]; 
        vm4_arcsync_core_event[i] = vm4_evt_sending_r[i];
        vm4_notify_sending[i]     = |vm4_core_notify[i] || vm4_arcsync_core_irq[i] || (vm4_evt_duration_r[i]!='b0);
      end: vm4_ntf_send_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm5_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        VM5_AC_NOTIFY_SRC[i]      ={{16'b0}, vm5_ac_notify_src_r[i]};
        VM5_AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|vm5_core_irq_pending[i]) || vm5_irq_sending_r[i])};  
        vm5_arcsync_core_irq[i]   = vm5_irq_sending_r[i]; 
        vm5_arcsync_core_event[i] = vm5_evt_sending_r[i];
        vm5_notify_sending[i]     = |vm5_core_notify[i] || vm5_arcsync_core_irq[i] || (vm5_evt_duration_r[i]!='b0);
      end: vm5_ntf_send_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm6_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        VM6_AC_NOTIFY_SRC[i]      ={{16'b0}, vm6_ac_notify_src_r[i]};
        VM6_AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|vm6_core_irq_pending[i]) || vm6_irq_sending_r[i])};  
        vm6_arcsync_core_irq[i]   = vm6_irq_sending_r[i]; 
        vm6_arcsync_core_event[i] = vm6_evt_sending_r[i];
        vm6_notify_sending[i]     = |vm6_core_notify[i] || vm6_arcsync_core_irq[i] || (vm6_evt_duration_r[i]!='b0);
      end: vm6_ntf_send_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm7_ntf_send_PROC
        // set pending interrupt from the ctrl request coming to the interrupt acking
        VM7_AC_NOTIFY_SRC[i]      ={{16'b0}, vm7_ac_notify_src_r[i]};
        VM7_AC_ACK_IRQ[i]         ={{31{1'b0}}, ((|vm7_core_irq_pending[i]) || vm7_irq_sending_r[i])};  
        vm7_arcsync_core_irq[i]   = vm7_irq_sending_r[i]; 
        vm7_arcsync_core_event[i] = vm7_evt_sending_r[i];
        vm7_notify_sending[i]     = |vm7_core_notify[i] || vm7_arcsync_core_irq[i] || (vm7_evt_duration_r[i]!='b0);
      end: vm7_ntf_send_PROC // for core_num/vproc }


end: ac_output_PROC

//-------------------------------------------------------------------------------------------------------
// MMIO Handling 
//------------------------------------------------------------------------------------------------------
always_comb  
begin: ac_ntf_check_PROC
  logic [ADDR_WIDTH-1:0]  addr_ac_notify_src;
  logic [ADDR_WIDTH-1:0]  addr_ac_ack_irq;   

      /////////////////////////// Non-VM mode ///////////////////////////
      for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
      begin: clst0_irq_access_PROC
        addr_ac_ack_irq  = ADDR_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        ac_ack_irq_en[i]  = arcsync_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        ac_ack_irq_wen[i] = mmio_wen && arcsync_core_wr_enable[i] && ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        ac_ntf_src_en[i] = arcsync_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: clst0_irq_access_PROC // for core_num/vproc }

        for (int unsigned i=18; i<((0+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
        begin: clst0_irq_access_asign0_PROC
          ac_ack_irq_en[i]  = 1'h0;
          ac_ack_irq_wen[i] = 1'h0;
          ac_ntf_src_en[i] = 1'h0;
        end: clst0_irq_access_asign0_PROC // for core_num }

      for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
      begin: clst1_irq_access_PROC
        addr_ac_ack_irq  = ADDR_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        ac_ack_irq_en[i]  = arcsync_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        ac_ack_irq_wen[i] = mmio_wen && arcsync_core_wr_enable[i] && ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        ac_ntf_src_en[i] = arcsync_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: clst1_irq_access_PROC // for core_num/vproc }

        for (int unsigned i=36; i<((1+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
        begin: clst1_irq_access_asign0_PROC
          ac_ack_irq_en[i]  = 1'h0;
          ac_ack_irq_wen[i] = 1'h0;
          ac_ntf_src_en[i] = 1'h0;
        end: clst1_irq_access_asign0_PROC // for core_num }

      for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
      begin: clst2_irq_access_PROC
        addr_ac_ack_irq  = ADDR_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        ac_ack_irq_en[i]  = arcsync_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        ac_ack_irq_wen[i] = mmio_wen && arcsync_core_wr_enable[i] && ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        ac_ntf_src_en[i] = arcsync_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: clst2_irq_access_PROC // for core_num/vproc }

        for (int unsigned i=65; i<((2+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
        begin: clst2_irq_access_asign0_PROC
          ac_ack_irq_en[i]  = 1'h0;
          ac_ack_irq_wen[i] = 1'h0;
          ac_ntf_src_en[i] = 1'h0;
        end: clst2_irq_access_asign0_PROC // for core_num }

    
      ///////////////////////////  VM mode ///////////////////////////
      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm0_irq_access_PROC
        addr_ac_ack_irq  = ADDR_VM0_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_VM0_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        vm0_ac_ack_irq_en[i]  = arcsync_vm0_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        vm0_ac_ack_irq_wen[i] = mmio_wen && arcsync_vm0_core_wr_enable[i] && vm0_ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        vm0_ac_ntf_src_en[i] = arcsync_vm0_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: vm0_irq_access_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm1_irq_access_PROC
        addr_ac_ack_irq  = ADDR_VM1_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_VM1_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        vm1_ac_ack_irq_en[i]  = arcsync_vm1_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        vm1_ac_ack_irq_wen[i] = mmio_wen && arcsync_vm1_core_wr_enable[i] && vm1_ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        vm1_ac_ntf_src_en[i] = arcsync_vm1_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: vm1_irq_access_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm2_irq_access_PROC
        addr_ac_ack_irq  = ADDR_VM2_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_VM2_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        vm2_ac_ack_irq_en[i]  = arcsync_vm2_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        vm2_ac_ack_irq_wen[i] = mmio_wen && arcsync_vm2_core_wr_enable[i] && vm2_ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        vm2_ac_ntf_src_en[i] = arcsync_vm2_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: vm2_irq_access_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm3_irq_access_PROC
        addr_ac_ack_irq  = ADDR_VM3_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_VM3_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        vm3_ac_ack_irq_en[i]  = arcsync_vm3_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        vm3_ac_ack_irq_wen[i] = mmio_wen && arcsync_vm3_core_wr_enable[i] && vm3_ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        vm3_ac_ntf_src_en[i] = arcsync_vm3_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: vm3_irq_access_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm4_irq_access_PROC
        addr_ac_ack_irq  = ADDR_VM4_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_VM4_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        vm4_ac_ack_irq_en[i]  = arcsync_vm4_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        vm4_ac_ack_irq_wen[i] = mmio_wen && arcsync_vm4_core_wr_enable[i] && vm4_ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        vm4_ac_ntf_src_en[i] = arcsync_vm4_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: vm4_irq_access_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm5_irq_access_PROC
        addr_ac_ack_irq  = ADDR_VM5_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_VM5_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        vm5_ac_ack_irq_en[i]  = arcsync_vm5_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        vm5_ac_ack_irq_wen[i] = mmio_wen && arcsync_vm5_core_wr_enable[i] && vm5_ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        vm5_ac_ntf_src_en[i] = arcsync_vm5_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: vm5_irq_access_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm6_irq_access_PROC
        addr_ac_ack_irq  = ADDR_VM6_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_VM6_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        vm6_ac_ack_irq_en[i]  = arcsync_vm6_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        vm6_ac_ack_irq_wen[i] = mmio_wen && arcsync_vm6_core_wr_enable[i] && vm6_ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        vm6_ac_ntf_src_en[i] = arcsync_vm6_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: vm6_irq_access_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm7_irq_access_PROC
        addr_ac_ack_irq  = ADDR_VM7_AC_ACK_IRQ + 4*i;
        addr_ac_notify_src = ADDR_VM7_AC_NOTIFY_SRC + 4*i;
        // The request accesses AC_ACK_IRQ register
        vm7_ac_ack_irq_en[i]  = arcsync_vm7_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_ack_irq); 
        // write core_id to acknowledge the interrupt
        vm7_ac_ack_irq_wen[i] = mmio_wen && arcsync_vm7_core_wr_enable[i] && vm7_ac_ack_irq_en[i] && (mmio_wdata[15:0]==i);
        // The request accesses AC_NOTIFY_SRC register
        // write ignore
        vm7_ac_ntf_src_en[i] = arcsync_vm7_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_notify_src); 
      end: vm7_irq_access_PROC // for core_num/vproc }



end: ac_ntf_check_PROC  

always_comb  
begin: ac_addr_check_PROC
  logic [ADDR_WIDTH-1:0]  addr_ac_config;    
  logic [ADDR_WIDTH-1:0]  addr_ac_control;   

      /////////////////////////// Non-VM mode ///////////////////////////
    for (int unsigned j=0;j<AC_NUM; j++) // { for AC_NUM
    begin: ac_access_PROC
        addr_ac_config  = ADDR_AC_CONFIG + 4*j;
        // The request accesses AC_CONFIG register
        ac_config_en[j]  = mmio_sel && (mmio_addr==addr_ac_config);
        // write configurations of AC if there is no waiting core 
        // send error to the write request if there is a pending core 
        ac_config_wen[j] = mmio_wen && ac_config_en[j] && (~|ctrl_req_pending_r[j]) && (~|vm_ctrl_req_pending_r[j]);


        for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
        begin: clst0_ac_access_ctrl_PROC
          addr_ac_control = ADDR_AC_CONTROL + 4*CORE_NUM*(j%64) + 4*i;
          // The request accesses AC_CONTROL register
            ac_control_en[j][i] = arcsync_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          ac_control_wen[j][i] = mmio_wen && arcsync_core_wr_enable[i] && ac_control_en[j][i] && ((~|core_req_pending[i] || mmio_wdata[2]) && !notify_sending[i]);
        end: clst0_ac_access_ctrl_PROC // for core_num/vproc }
        
          for (int unsigned i=18; i<((0+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
          begin: clst0_ac_access_ctrl_asign0_PROC
            ac_control_en[j][i] = 1'b0;
            ac_control_wen[j][i] = 1'b0;
          end: clst0_ac_access_ctrl_asign0_PROC


        for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
        begin: clst1_ac_access_ctrl_PROC
          addr_ac_control = ADDR_AC_CONTROL + 4*CORE_NUM*(j%64) + 4*i;
          // The request accesses AC_CONTROL register
            ac_control_en[j][i] = arcsync_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          ac_control_wen[j][i] = mmio_wen && arcsync_core_wr_enable[i] && ac_control_en[j][i] && ((~|core_req_pending[i] || mmio_wdata[2]) && !notify_sending[i]);
        end: clst1_ac_access_ctrl_PROC // for core_num/vproc }
        
          for (int unsigned i=36; i<((1+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
          begin: clst1_ac_access_ctrl_asign0_PROC
            ac_control_en[j][i] = 1'b0;
            ac_control_wen[j][i] = 1'b0;
          end: clst1_ac_access_ctrl_asign0_PROC


        for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
        begin: clst2_ac_access_ctrl_PROC
          addr_ac_control = ADDR_AC_CONTROL + 4*CORE_NUM*(j%64) + 4*i;
          // The request accesses AC_CONTROL register
            ac_control_en[j][i] = arcsync_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          ac_control_wen[j][i] = mmio_wen && arcsync_core_wr_enable[i] && ac_control_en[j][i] && ((~|core_req_pending[i] || mmio_wdata[2]) && !notify_sending[i]);
        end: clst2_ac_access_ctrl_PROC // for core_num/vproc }
        
          for (int unsigned i=65; i<((2+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
          begin: clst2_ac_access_ctrl_asign0_PROC
            ac_control_en[j][i] = 1'b0;
            ac_control_wen[j][i] = 1'b0;
          end: clst2_ac_access_ctrl_asign0_PROC


        ac_ctrl_per_ac_en[j] = |ac_control_en[j];
        ac_control_per_ac_wen[j] = |ac_control_wen[j];

    end: ac_access_PROC // for AC_NUM }
    
      ///////////////////////////  VM mode ///////////////////////////
    for (int unsigned j=0;j<AC_NUM; j++) // { for AC_NUM
    begin: ac_access_PROC

          // VM_AC_CONFIG register is not exist
          vm0_ac_config_en[j]  = 1'b0;
          vm0_ac_config_wen[j] = 1'b0;

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm0_ac_access_ctrl_PROC
          addr_ac_control = ADDR_VM0_AC_CONTROL + 4*VIRT_PROC*(j%8) + 4*i;
          // The request accesses AC_CONTROL register
            vm0_ac_control_en[j][i] = arcsync_vm0_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control) & ((j/8)==0);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          vm0_ac_control_wen[j][i] = mmio_wen && arcsync_vm0_core_wr_enable[i] && vm0_ac_control_en[j][i] && ((~|vm0_core_req_pending[i] || mmio_wdata[2]) && !vm0_notify_sending[i]);
        end: vm0_ac_access_ctrl_PROC // for core_num/vproc }
        

          vm0_ac_ctrl_per_ac_en[j] = |vm0_ac_control_en[j];
          vm0_ac_control_per_ac_wen[j] = |vm0_ac_control_wen[j];
          // VM_AC_CONFIG register is not exist
          vm1_ac_config_en[j]  = 1'b0;
          vm1_ac_config_wen[j] = 1'b0;

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm1_ac_access_ctrl_PROC
          addr_ac_control = ADDR_VM1_AC_CONTROL + 4*VIRT_PROC*(j%8) + 4*i;
          // The request accesses AC_CONTROL register
            vm1_ac_control_en[j][i] = arcsync_vm1_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control) & ((j/8)==1);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          vm1_ac_control_wen[j][i] = mmio_wen && arcsync_vm1_core_wr_enable[i] && vm1_ac_control_en[j][i] && ((~|vm1_core_req_pending[i] || mmio_wdata[2]) && !vm1_notify_sending[i]);
        end: vm1_ac_access_ctrl_PROC // for core_num/vproc }
        

          vm1_ac_ctrl_per_ac_en[j] = |vm1_ac_control_en[j];
          vm1_ac_control_per_ac_wen[j] = |vm1_ac_control_wen[j];
          // VM_AC_CONFIG register is not exist
          vm2_ac_config_en[j]  = 1'b0;
          vm2_ac_config_wen[j] = 1'b0;

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm2_ac_access_ctrl_PROC
          addr_ac_control = ADDR_VM2_AC_CONTROL + 4*VIRT_PROC*(j%8) + 4*i;
          // The request accesses AC_CONTROL register
            vm2_ac_control_en[j][i] = arcsync_vm2_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control) & ((j/8)==2);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          vm2_ac_control_wen[j][i] = mmio_wen && arcsync_vm2_core_wr_enable[i] && vm2_ac_control_en[j][i] && ((~|vm2_core_req_pending[i] || mmio_wdata[2]) && !vm2_notify_sending[i]);
        end: vm2_ac_access_ctrl_PROC // for core_num/vproc }
        

          vm2_ac_ctrl_per_ac_en[j] = |vm2_ac_control_en[j];
          vm2_ac_control_per_ac_wen[j] = |vm2_ac_control_wen[j];
          // VM_AC_CONFIG register is not exist
          vm3_ac_config_en[j]  = 1'b0;
          vm3_ac_config_wen[j] = 1'b0;

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm3_ac_access_ctrl_PROC
          addr_ac_control = ADDR_VM3_AC_CONTROL + 4*VIRT_PROC*(j%8) + 4*i;
          // The request accesses AC_CONTROL register
            vm3_ac_control_en[j][i] = arcsync_vm3_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control) & ((j/8)==3);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          vm3_ac_control_wen[j][i] = mmio_wen && arcsync_vm3_core_wr_enable[i] && vm3_ac_control_en[j][i] && ((~|vm3_core_req_pending[i] || mmio_wdata[2]) && !vm3_notify_sending[i]);
        end: vm3_ac_access_ctrl_PROC // for core_num/vproc }
        

          vm3_ac_ctrl_per_ac_en[j] = |vm3_ac_control_en[j];
          vm3_ac_control_per_ac_wen[j] = |vm3_ac_control_wen[j];
          // VM_AC_CONFIG register is not exist
          vm4_ac_config_en[j]  = 1'b0;
          vm4_ac_config_wen[j] = 1'b0;

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm4_ac_access_ctrl_PROC
          addr_ac_control = ADDR_VM4_AC_CONTROL + 4*VIRT_PROC*(j%8) + 4*i;
          // The request accesses AC_CONTROL register
            vm4_ac_control_en[j][i] = arcsync_vm4_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control) & ((j/8)==4);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          vm4_ac_control_wen[j][i] = mmio_wen && arcsync_vm4_core_wr_enable[i] && vm4_ac_control_en[j][i] && ((~|vm4_core_req_pending[i] || mmio_wdata[2]) && !vm4_notify_sending[i]);
        end: vm4_ac_access_ctrl_PROC // for core_num/vproc }
        

          vm4_ac_ctrl_per_ac_en[j] = |vm4_ac_control_en[j];
          vm4_ac_control_per_ac_wen[j] = |vm4_ac_control_wen[j];
          // VM_AC_CONFIG register is not exist
          vm5_ac_config_en[j]  = 1'b0;
          vm5_ac_config_wen[j] = 1'b0;

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm5_ac_access_ctrl_PROC
          addr_ac_control = ADDR_VM5_AC_CONTROL + 4*VIRT_PROC*(j%8) + 4*i;
          // The request accesses AC_CONTROL register
            vm5_ac_control_en[j][i] = arcsync_vm5_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control) & ((j/8)==5);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          vm5_ac_control_wen[j][i] = mmio_wen && arcsync_vm5_core_wr_enable[i] && vm5_ac_control_en[j][i] && ((~|vm5_core_req_pending[i] || mmio_wdata[2]) && !vm5_notify_sending[i]);
        end: vm5_ac_access_ctrl_PROC // for core_num/vproc }
        

          vm5_ac_ctrl_per_ac_en[j] = |vm5_ac_control_en[j];
          vm5_ac_control_per_ac_wen[j] = |vm5_ac_control_wen[j];
          // VM_AC_CONFIG register is not exist
          vm6_ac_config_en[j]  = 1'b0;
          vm6_ac_config_wen[j] = 1'b0;

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm6_ac_access_ctrl_PROC
          addr_ac_control = ADDR_VM6_AC_CONTROL + 4*VIRT_PROC*(j%8) + 4*i;
          // The request accesses AC_CONTROL register
            vm6_ac_control_en[j][i] = arcsync_vm6_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control) & ((j/8)==6);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          vm6_ac_control_wen[j][i] = mmio_wen && arcsync_vm6_core_wr_enable[i] && vm6_ac_control_en[j][i] && ((~|vm6_core_req_pending[i] || mmio_wdata[2]) && !vm6_notify_sending[i]);
        end: vm6_ac_access_ctrl_PROC // for core_num/vproc }
        

          vm6_ac_ctrl_per_ac_en[j] = |vm6_ac_control_en[j];
          vm6_ac_control_per_ac_wen[j] = |vm6_ac_control_wen[j];
          // VM_AC_CONFIG register is not exist
          vm7_ac_config_en[j]  = 1'b0;
          vm7_ac_config_wen[j] = 1'b0;

        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm7_ac_access_ctrl_PROC
          addr_ac_control = ADDR_VM7_AC_CONTROL + 4*VIRT_PROC*(j%8) + 4*i;
          // The request accesses AC_CONTROL register
            vm7_ac_control_en[j][i] = arcsync_vm7_core_exist[i] && mmio_sel && (mmio_addr==addr_ac_control) & ((j/8)==7);
          // there is only one waiting request from one core
          // If the notification is sending, the core cannot sent new request
          // Otherwise, the condition is abnormal and return error. 
          // set write control to each AC from each core
          // Not to send error with a programming mistake 
          vm7_ac_control_wen[j][i] = mmio_wen && arcsync_vm7_core_wr_enable[i] && vm7_ac_control_en[j][i] && ((~|vm7_core_req_pending[i] || mmio_wdata[2]) && !vm7_notify_sending[i]);
        end: vm7_ac_access_ctrl_PROC // for core_num/vproc }
        

          vm7_ac_ctrl_per_ac_en[j] = |vm7_ac_control_en[j];
          vm7_ac_control_per_ac_wen[j] = |vm7_ac_control_wen[j];


    end: ac_access_PROC // for AC_NUM }
end: ac_addr_check_PROC

always_comb  
begin: vm_ac_en_PROC
  vm_ac_ack_irq_en = 1'b0
                    | (|vm0_ac_ack_irq_en)
                    | (|vm1_ac_ack_irq_en)
                    | (|vm2_ac_ack_irq_en)
                    | (|vm3_ac_ack_irq_en)
                    | (|vm4_ac_ack_irq_en)
                    | (|vm5_ac_ack_irq_en)
                    | (|vm6_ac_ack_irq_en)
                    | (|vm7_ac_ack_irq_en)
                    ;

  vm_ac_ntf_src_en = 1'b0
                    | (|vm0_ac_ntf_src_en)
                    | (|vm1_ac_ntf_src_en)
                    | (|vm2_ac_ntf_src_en)
                    | (|vm3_ac_ntf_src_en)
                    | (|vm4_ac_ntf_src_en)
                    | (|vm5_ac_ntf_src_en)
                    | (|vm6_ac_ntf_src_en)
                    | (|vm7_ac_ntf_src_en)
                    ;

  vm_ac_ack_irq_wen = 1'b0
                    | (|vm0_ac_ack_irq_wen)
                    | (|vm1_ac_ack_irq_wen)
                    | (|vm2_ac_ack_irq_wen)
                    | (|vm3_ac_ack_irq_wen)
                    | (|vm4_ac_ack_irq_wen)
                    | (|vm5_ac_ack_irq_wen)
                    | (|vm6_ac_ack_irq_wen)
                    | (|vm7_ac_ack_irq_wen)
                    ;

  vm_ac_ctrl_per_ac_en = 1'b0
                    | (|vm0_ac_ctrl_per_ac_en)
                    | (|vm1_ac_ctrl_per_ac_en)
                    | (|vm2_ac_ctrl_per_ac_en)
                    | (|vm3_ac_ctrl_per_ac_en)
                    | (|vm4_ac_ctrl_per_ac_en)
                    | (|vm5_ac_ctrl_per_ac_en)
                    | (|vm6_ac_ctrl_per_ac_en)
                    | (|vm7_ac_ctrl_per_ac_en)
                    ;

  vm_ac_control_per_ac_wen = 1'b0
                    | (|vm0_ac_control_per_ac_wen)
                    | (|vm1_ac_control_per_ac_wen)
                    | (|vm2_ac_control_per_ac_wen)
                    | (|vm3_ac_control_per_ac_wen)
                    | (|vm4_ac_control_per_ac_wen)
                    | (|vm5_ac_control_per_ac_wen)
                    | (|vm6_ac_control_per_ac_wen)
                    | (|vm7_ac_control_per_ac_wen)
                    ;

  vm_ac_config_en = 1'b0
                    | (|vm0_ac_config_en)
                    | (|vm1_ac_config_en)
                    | (|vm2_ac_config_en)
                    | (|vm3_ac_config_en)
                    | (|vm4_ac_config_en)
                    | (|vm5_ac_config_en)
                    | (|vm6_ac_config_en)
                    | (|vm7_ac_config_en)
                    ;

  for (int unsigned j=0; j<AC_NUM; j++) // { for AC_NUM
  begin
    vm_ctrl_req_notify_r[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                              | (|vm0_ctrl_req_notify_r[j])
                              | (|vm1_ctrl_req_notify_r[j])
                              | (|vm2_ctrl_req_notify_r[j])
                              | (|vm3_ctrl_req_notify_r[j])
                              | (|vm4_ctrl_req_notify_r[j])
                              | (|vm5_ctrl_req_notify_r[j])
                              | (|vm6_ctrl_req_notify_r[j])
                              | (|vm7_ctrl_req_notify_r[j])
                                ;

    vm_ctrl_req_pending_r[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                              | (vm0_ctrl_req_pending_r[j])
                              | (vm1_ctrl_req_pending_r[j])
                              | (vm2_ctrl_req_pending_r[j])
                              | (vm3_ctrl_req_pending_r[j])
                              | (vm4_ctrl_req_pending_r[j])
                              | (vm5_ctrl_req_pending_r[j])
                              | (vm6_ctrl_req_pending_r[j])
                              | (vm7_ctrl_req_pending_r[j])
                                ;

    vm_ac_first_pending_core[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                                 | vm0_ac_first_pending_core[j]
                                 | vm1_ac_first_pending_core[j]
                                 | vm2_ac_first_pending_core[j]
                                 | vm3_ac_first_pending_core[j]
                                 | vm4_ac_first_pending_core[j]
                                 | vm5_ac_first_pending_core[j]
                                 | vm6_ac_first_pending_core[j]
                                 | vm7_ac_first_pending_core[j]
                                  ;
    
    vm_ctrl_notify_type_r[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                              | vm0_ctrl_notify_type_r[j]
                              | vm1_ctrl_notify_type_r[j]
                              | vm2_ctrl_notify_type_r[j]
                              | vm3_ctrl_notify_type_r[j]
                              | vm4_ctrl_notify_type_r[j]
                              | vm5_ctrl_notify_type_r[j]
                              | vm6_ctrl_notify_type_r[j]
                              | vm7_ctrl_notify_type_r[j]
                               ;

    vm_ctrl_cmp_res_r[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                          | vm0_ctrl_cmp_res_r[j]
                          | vm1_ctrl_cmp_res_r[j]
                          | vm2_ctrl_cmp_res_r[j]
                          | vm3_ctrl_cmp_res_r[j]
                          | vm4_ctrl_cmp_res_r[j]
                          | vm5_ctrl_cmp_res_r[j]
                          | vm6_ctrl_cmp_res_r[j]
                          | vm7_ctrl_cmp_res_r[j]
                           ;

    vm_ctrl_decr_req[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                         | vm0_ctrl_decr_req[j]
                         | vm1_ctrl_decr_req[j]
                         | vm2_ctrl_decr_req[j]
                         | vm3_ctrl_decr_req[j]
                         | vm4_ctrl_decr_req[j]
                         | vm5_ctrl_decr_req[j]
                         | vm6_ctrl_decr_req[j]
                         | vm7_ctrl_decr_req[j]
                       ;

    vm_ctrl_incr_req[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                         | vm0_ctrl_incr_req[j]
                         | vm1_ctrl_incr_req[j]
                         | vm2_ctrl_incr_req[j]
                         | vm3_ctrl_incr_req[j]
                         | vm4_ctrl_incr_req[j]
                         | vm5_ctrl_incr_req[j]
                         | vm6_ctrl_incr_req[j]
                         | vm7_ctrl_incr_req[j]
                       ;

    vm_ctrl_req_notify_nxt[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                               | vm0_ctrl_req_notify_nxt[j]
                               | vm1_ctrl_req_notify_nxt[j]
                               | vm2_ctrl_req_notify_nxt[j]
                               | vm3_ctrl_req_notify_nxt[j]
                               | vm4_ctrl_req_notify_nxt[j]
                               | vm5_ctrl_req_notify_nxt[j]
                               | vm6_ctrl_req_notify_nxt[j]
                               | vm7_ctrl_req_notify_nxt[j]
                             ;

    vm_ctrl_req_pending_nxt[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                                | vm0_ctrl_req_pending_nxt[j]
                                | vm1_ctrl_req_pending_nxt[j]
                                | vm2_ctrl_req_pending_nxt[j]
                                | vm3_ctrl_req_pending_nxt[j]
                                | vm4_ctrl_req_pending_nxt[j]
                                | vm5_ctrl_req_pending_nxt[j]
                                | vm6_ctrl_req_pending_nxt[j]
                                | vm7_ctrl_req_pending_nxt[j]
                              ;

    vm_ctrl_notify_type_nxt[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                                | vm0_ctrl_notify_type_nxt[j]
                                | vm1_ctrl_notify_type_nxt[j]
                                | vm2_ctrl_notify_type_nxt[j]
                                | vm3_ctrl_notify_type_nxt[j]
                                | vm4_ctrl_notify_type_nxt[j]
                                | vm5_ctrl_notify_type_nxt[j]
                                | vm6_ctrl_notify_type_nxt[j]
                                | vm7_ctrl_notify_type_nxt[j]
                              ;

    vm_ctrl_cmp_res_nxt[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                            | vm0_ctrl_cmp_res_nxt[j]
                            | vm1_ctrl_cmp_res_nxt[j]
                            | vm2_ctrl_cmp_res_nxt[j]
                            | vm3_ctrl_cmp_res_nxt[j]
                            | vm4_ctrl_cmp_res_nxt[j]
                            | vm5_ctrl_cmp_res_nxt[j]
                            | vm6_ctrl_cmp_res_nxt[j]
                            | vm7_ctrl_cmp_res_nxt[j]
                          ;

    vm_ac_control_wen[j] = {`ARCSYNC_VIRT_PROC{1'b0}}
                          | vm0_ac_control_wen[j]
                          | vm1_ac_control_wen[j]
                          | vm2_ac_control_wen[j]
                          | vm3_ac_control_wen[j]
                          | vm4_ac_control_wen[j]
                          | vm5_ac_control_wen[j]
                          | vm6_ac_control_wen[j]
                          | vm7_ac_control_wen[j]
                                  ;

  end // for AC_NUM }
end

assign valid_req = (mmio_ren && ((|ac_ack_irq_en) || (|ac_ntf_src_en) || (|ac_ctrl_per_ac_en) || (|ac_config_en) || 
                                 (vm_ac_ack_irq_en) || (vm_ac_ntf_src_en) || (vm_ac_ctrl_per_ac_en)))
                || (mmio_wen && ((|ac_ack_irq_wen) || (|ac_ntf_src_en) || (|ac_control_per_ac_wen) || (|ac_config_wen) ||
                                 (vm_ac_ack_irq_wen) || (vm_ac_ntf_src_en) || (vm_ac_control_per_ac_wen)));

always_comb  
begin: mmio_intf_PROC
  mmio_rdata  = {DATA_WIDTH{1'b0}};
  if (mmio_ren)
  begin  
    // return the source of notification from AC_NOTIFY_SRC register
    if (|ac_ntf_src_en | vm_ac_ntf_src_en)
    begin  
          /////////////////////////// Non-VM mode ///////////////////////////
          for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
          begin: clst0_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{ac_ntf_src_en[i]}} & AC_NOTIFY_SRC[i];
          end: clst0_rd_ntf_src_PROC   // for core_num/vproc }
          for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
          begin: clst1_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{ac_ntf_src_en[i]}} & AC_NOTIFY_SRC[i];
          end: clst1_rd_ntf_src_PROC   // for core_num/vproc }
          for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
          begin: clst2_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{ac_ntf_src_en[i]}} & AC_NOTIFY_SRC[i];
          end: clst2_rd_ntf_src_PROC   // for core_num/vproc }
        
          ///////////////////////////  VM mode ///////////////////////////
          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm0_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{vm0_ac_ntf_src_en[i]}} & VM0_AC_NOTIFY_SRC[i];
          end: vm0_rd_ntf_src_PROC   // for core_num/vproc }
          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm1_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{vm1_ac_ntf_src_en[i]}} & VM1_AC_NOTIFY_SRC[i];
          end: vm1_rd_ntf_src_PROC   // for core_num/vproc }
          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm2_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{vm2_ac_ntf_src_en[i]}} & VM2_AC_NOTIFY_SRC[i];
          end: vm2_rd_ntf_src_PROC   // for core_num/vproc }
          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm3_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{vm3_ac_ntf_src_en[i]}} & VM3_AC_NOTIFY_SRC[i];
          end: vm3_rd_ntf_src_PROC   // for core_num/vproc }
          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm4_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{vm4_ac_ntf_src_en[i]}} & VM4_AC_NOTIFY_SRC[i];
          end: vm4_rd_ntf_src_PROC   // for core_num/vproc }
          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm5_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{vm5_ac_ntf_src_en[i]}} & VM5_AC_NOTIFY_SRC[i];
          end: vm5_rd_ntf_src_PROC   // for core_num/vproc }
          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm6_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{vm6_ac_ntf_src_en[i]}} & VM6_AC_NOTIFY_SRC[i];
          end: vm6_rd_ntf_src_PROC   // for core_num/vproc }
          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm7_rd_ntf_src_PROC
            mmio_rdata  = mmio_rdata | {32{vm7_ac_ntf_src_en[i]}} & VM7_AC_NOTIFY_SRC[i];
          end: vm7_rd_ntf_src_PROC   // for core_num/vproc }
    end
    // return the interrupt status from AC_ACK_IRQ register
    else if (|ac_ack_irq_en | vm_ac_ack_irq_en)
    begin  
          /////////////////////////// Non-VM mode ///////////////////////////
 

          for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
          begin: clst0_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{ac_ack_irq_en[i]}} & AC_ACK_IRQ[i];
          end: clst0_rd_ack_irq_PROC  // for core_num/vproc }

          for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
          begin: clst1_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{ac_ack_irq_en[i]}} & AC_ACK_IRQ[i];
          end: clst1_rd_ack_irq_PROC  // for core_num/vproc }

          for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
          begin: clst2_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{ac_ack_irq_en[i]}} & AC_ACK_IRQ[i];
          end: clst2_rd_ack_irq_PROC  // for core_num/vproc }
        
          ///////////////////////////  VM mode ///////////////////////////
 

          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm0_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{vm0_ac_ack_irq_en[i]}} & VM0_AC_ACK_IRQ[i];
          end: vm0_rd_ack_irq_PROC  // for core_num/vproc }

          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm1_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{vm1_ac_ack_irq_en[i]}} & VM1_AC_ACK_IRQ[i];
          end: vm1_rd_ack_irq_PROC  // for core_num/vproc }

          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm2_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{vm2_ac_ack_irq_en[i]}} & VM2_AC_ACK_IRQ[i];
          end: vm2_rd_ack_irq_PROC  // for core_num/vproc }

          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm3_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{vm3_ac_ack_irq_en[i]}} & VM3_AC_ACK_IRQ[i];
          end: vm3_rd_ack_irq_PROC  // for core_num/vproc }

          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm4_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{vm4_ac_ack_irq_en[i]}} & VM4_AC_ACK_IRQ[i];
          end: vm4_rd_ack_irq_PROC  // for core_num/vproc }

          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm5_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{vm5_ac_ack_irq_en[i]}} & VM5_AC_ACK_IRQ[i];
          end: vm5_rd_ack_irq_PROC  // for core_num/vproc }

          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm6_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{vm6_ac_ack_irq_en[i]}} & VM6_AC_ACK_IRQ[i];
          end: vm6_rd_ack_irq_PROC  // for core_num/vproc }

          for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
          begin: vm7_rd_ack_irq_PROC
            mmio_rdata      =  mmio_rdata | {32{vm7_ac_ack_irq_en[i]}} & VM7_AC_ACK_IRQ[i];
          end: vm7_rd_ack_irq_PROC  // for core_num/vproc }
    end
    // return the AC config status from AC_CONFIG register
    else if (|ac_config_en)
    begin  
      for (int unsigned j=0;j<AC_NUM; j++)
      begin: rd_cfg_PROC
        mmio_rdata      = mmio_rdata | {32{ac_config_en[j]}} & AC_CONFIG[j];
      end: rd_cfg_PROC  
    end
    else if (|ac_ctrl_per_ac_en | vm_ac_ctrl_per_ac_en) 
    begin
      for (int unsigned j=0;j<AC_NUM; j++)
      begin: rd_ac_ctrl_PROC
        // return the control status from AC_CONTROL register

            /////////////////////////// Non-VM mode ///////////////////////////
 

            for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
            begin: clst0_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{ac_control_en[j][i]}} & AC_CONTROL[j][i];
            end: clst0_rd_ctrl_PROC  // for core_num/vproc }

            for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
            begin: clst1_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{ac_control_en[j][i]}} & AC_CONTROL[j][i];
            end: clst1_rd_ctrl_PROC  // for core_num/vproc }

            for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
            begin: clst2_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{ac_control_en[j][i]}} & AC_CONTROL[j][i];
            end: clst2_rd_ctrl_PROC  // for core_num/vproc }
          
            ///////////////////////////  VM mode ///////////////////////////
 

            for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
            begin: vm0_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{vm0_ac_control_en[j][i]}} & VM0_AC_CONTROL[j][i];
            end: vm0_rd_ctrl_PROC  // for core_num/vproc }

            for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
            begin: vm1_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{vm1_ac_control_en[j][i]}} & VM1_AC_CONTROL[j][i];
            end: vm1_rd_ctrl_PROC  // for core_num/vproc }

            for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
            begin: vm2_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{vm2_ac_control_en[j][i]}} & VM2_AC_CONTROL[j][i];
            end: vm2_rd_ctrl_PROC  // for core_num/vproc }

            for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
            begin: vm3_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{vm3_ac_control_en[j][i]}} & VM3_AC_CONTROL[j][i];
            end: vm3_rd_ctrl_PROC  // for core_num/vproc }

            for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
            begin: vm4_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{vm4_ac_control_en[j][i]}} & VM4_AC_CONTROL[j][i];
            end: vm4_rd_ctrl_PROC  // for core_num/vproc }

            for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
            begin: vm5_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{vm5_ac_control_en[j][i]}} & VM5_AC_CONTROL[j][i];
            end: vm5_rd_ctrl_PROC  // for core_num/vproc }

            for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
            begin: vm6_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{vm6_ac_control_en[j][i]}} & VM6_AC_CONTROL[j][i];
            end: vm6_rd_ctrl_PROC  // for core_num/vproc }

            for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
            begin: vm7_rd_ctrl_PROC
              mmio_rdata      = mmio_rdata |  {32{vm7_ac_control_en[j][i]}} & VM7_AC_CONTROL[j][i];
            end: vm7_rd_ctrl_PROC  // for core_num/vproc }
      end: rd_ac_ctrl_PROC
    end  
  end
end: mmio_intf_PROC  

//-------------------------------------------------------------------------------------------------------
// AC_CFG and AC_CTRL Handling 
//-------------------------------------------------------------------------------------------------------
// With semaphore/index ac, the initial value==[0, bound value] 
// With the barrier ac, the initial value== bound value and >0
// If the AC_CONFIG is set improperly, the behavior is unpredictable
//
// With reseved bx ac, set the counter value as what it requests 
// This AC cannot be accessed by any AC_CONTROL request
always_comb  
begin: ac_cfg_PROC
  for (int unsigned j=0; j<AC_NUM; j=j+1)
  begin: cfg_per_ac_PROC  
    cfg_bx_sem[j]    = (cfg_bx_r[j]==2'b01); 
    cfg_bx_bar[j]    = (cfg_bx_r[j]==2'b10);
    cfg_bx_idx[j]    = (cfg_bx_r[j]==2'b11);
    cfg_cnt_ini[j]   = {AC_WIDTH{1'b0}};
    cfg_bound_nxt[j] = cfg_bound_r[j]; 
    cfg_bx_nxt[j]    = cfg_bx_r[j];    
    if (ac_config_wen[j])
    begin
      // With barrier ac counter, wrap back to its bound value if it's 0
      cfg_cnt_ini[j]   = (mmio_wdata[25:24]==2'b10 && (~|mmio_wdata[0+:AC_WIDTH]))? mmio_wdata[12+:AC_WIDTH] 
                                                                                  : mmio_wdata[0+:AC_WIDTH];
      cfg_bound_nxt[j] = mmio_wdata[12+:AC_WIDTH];
      cfg_bx_nxt[j]    = mmio_wdata[25:24];
    end  
  end: cfg_per_ac_PROC
end: ac_cfg_PROC

// find the first pending core for semaphore atomic counter
always_comb
begin: ac_pend_PROC

      /////////////////////////// Non-VM mode ///////////////////////////


        // default assignment for ctrl_req_pending_r_2s_comp
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: default_asign_PROC
          ctrl_req_pending_r_2s_comp[j] = {(CORE_NUM+1){1'b0}};
        end: default_asign_PROC

        // only update useful AC indexed ctrl_req_pending_r_2s_comp in each VM
        for (int unsigned j=0; j<64; j=j+1)
        begin: nonvm0_pend_per_ac_PROC
          ctrl_req_pending_r_2s_comp[j] = (~ctrl_req_pending_r[j]) + 1;
          ac_first_pending_core[j] = ctrl_req_pending_r[j] & (ctrl_req_pending_r_2s_comp[j][CORE_NUM-1:0]);
        end: nonvm0_pend_per_ac_PROC

    
    
      ///////////////////////////  VM mode ///////////////////////////

          //// VM0 ////
          // default assign 0
          for (int unsigned j=0; j<`ARCSYNC_NUM_ATOMIC_CNT; j++)
          begin: vm0_default_asign_ac_first_pending_core_AC_index_PROC
            for (int unsigned i=0; i<(3); i++)
            begin: vm0_default_asign_ac_first_pending_core_VPROC_index_PROC
              vm0_ac_first_pending_core[j][i] = 1'b0;
            end: vm0_default_asign_ac_first_pending_core_VPROC_index_PROC 
          end: vm0_default_asign_ac_first_pending_core_AC_index_PROC

        // default assignment for vm0_ctrl_req_pending_r_2s_comp
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: vm0_default_asign_PROC
          vm0_ctrl_req_pending_r_2s_comp[j] = {(VIRT_PROC+1){1'b0}};
        end: vm0_default_asign_PROC

        // only update useful AC indexed vm0_ctrl_req_pending_r_2s_comp in each VM
        for (int unsigned j=0; j<8; j=j+1)
        begin: vm0_pend_per_ac_PROC
          vm0_ctrl_req_pending_r_2s_comp[j] = (~vm0_ctrl_req_pending_r[j]) + 1;
          vm0_ac_first_pending_core[j] = vm0_ctrl_req_pending_r[j] & (vm0_ctrl_req_pending_r_2s_comp[j][VIRT_PROC-1:0]);
        end: vm0_pend_per_ac_PROC


          //// VM1 ////
          // default assign 0
          for (int unsigned j=0; j<`ARCSYNC_NUM_ATOMIC_CNT; j++)
          begin: vm1_default_asign_ac_first_pending_core_AC_index_PROC
            for (int unsigned i=0; i<(3); i++)
            begin: vm1_default_asign_ac_first_pending_core_VPROC_index_PROC
              vm1_ac_first_pending_core[j][i] = 1'b0;
            end: vm1_default_asign_ac_first_pending_core_VPROC_index_PROC 
          end: vm1_default_asign_ac_first_pending_core_AC_index_PROC

        // default assignment for vm1_ctrl_req_pending_r_2s_comp
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: vm1_default_asign_PROC
          vm1_ctrl_req_pending_r_2s_comp[j] = {(VIRT_PROC+1){1'b0}};
        end: vm1_default_asign_PROC

        // only update useful AC indexed vm1_ctrl_req_pending_r_2s_comp in each VM
        for (int unsigned j=8; j<16; j=j+1)
        begin: vm1_pend_per_ac_PROC
          vm1_ctrl_req_pending_r_2s_comp[j] = (~vm1_ctrl_req_pending_r[j]) + 1;
          vm1_ac_first_pending_core[j] = vm1_ctrl_req_pending_r[j] & (vm1_ctrl_req_pending_r_2s_comp[j][VIRT_PROC-1:0]);
        end: vm1_pend_per_ac_PROC


          //// VM2 ////
          // default assign 0
          for (int unsigned j=0; j<`ARCSYNC_NUM_ATOMIC_CNT; j++)
          begin: vm2_default_asign_ac_first_pending_core_AC_index_PROC
            for (int unsigned i=0; i<(3); i++)
            begin: vm2_default_asign_ac_first_pending_core_VPROC_index_PROC
              vm2_ac_first_pending_core[j][i] = 1'b0;
            end: vm2_default_asign_ac_first_pending_core_VPROC_index_PROC 
          end: vm2_default_asign_ac_first_pending_core_AC_index_PROC

        // default assignment for vm2_ctrl_req_pending_r_2s_comp
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: vm2_default_asign_PROC
          vm2_ctrl_req_pending_r_2s_comp[j] = {(VIRT_PROC+1){1'b0}};
        end: vm2_default_asign_PROC

        // only update useful AC indexed vm2_ctrl_req_pending_r_2s_comp in each VM
        for (int unsigned j=16; j<24; j=j+1)
        begin: vm2_pend_per_ac_PROC
          vm2_ctrl_req_pending_r_2s_comp[j] = (~vm2_ctrl_req_pending_r[j]) + 1;
          vm2_ac_first_pending_core[j] = vm2_ctrl_req_pending_r[j] & (vm2_ctrl_req_pending_r_2s_comp[j][VIRT_PROC-1:0]);
        end: vm2_pend_per_ac_PROC


          //// VM3 ////
          // default assign 0
          for (int unsigned j=0; j<`ARCSYNC_NUM_ATOMIC_CNT; j++)
          begin: vm3_default_asign_ac_first_pending_core_AC_index_PROC
            for (int unsigned i=0; i<(3); i++)
            begin: vm3_default_asign_ac_first_pending_core_VPROC_index_PROC
              vm3_ac_first_pending_core[j][i] = 1'b0;
            end: vm3_default_asign_ac_first_pending_core_VPROC_index_PROC 
          end: vm3_default_asign_ac_first_pending_core_AC_index_PROC

        // default assignment for vm3_ctrl_req_pending_r_2s_comp
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: vm3_default_asign_PROC
          vm3_ctrl_req_pending_r_2s_comp[j] = {(VIRT_PROC+1){1'b0}};
        end: vm3_default_asign_PROC

        // only update useful AC indexed vm3_ctrl_req_pending_r_2s_comp in each VM
        for (int unsigned j=24; j<32; j=j+1)
        begin: vm3_pend_per_ac_PROC
          vm3_ctrl_req_pending_r_2s_comp[j] = (~vm3_ctrl_req_pending_r[j]) + 1;
          vm3_ac_first_pending_core[j] = vm3_ctrl_req_pending_r[j] & (vm3_ctrl_req_pending_r_2s_comp[j][VIRT_PROC-1:0]);
        end: vm3_pend_per_ac_PROC


          //// VM4 ////
          // default assign 0
          for (int unsigned j=0; j<`ARCSYNC_NUM_ATOMIC_CNT; j++)
          begin: vm4_default_asign_ac_first_pending_core_AC_index_PROC
            for (int unsigned i=0; i<(3); i++)
            begin: vm4_default_asign_ac_first_pending_core_VPROC_index_PROC
              vm4_ac_first_pending_core[j][i] = 1'b0;
            end: vm4_default_asign_ac_first_pending_core_VPROC_index_PROC 
          end: vm4_default_asign_ac_first_pending_core_AC_index_PROC

        // default assignment for vm4_ctrl_req_pending_r_2s_comp
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: vm4_default_asign_PROC
          vm4_ctrl_req_pending_r_2s_comp[j] = {(VIRT_PROC+1){1'b0}};
        end: vm4_default_asign_PROC

        // only update useful AC indexed vm4_ctrl_req_pending_r_2s_comp in each VM
        for (int unsigned j=32; j<40; j=j+1)
        begin: vm4_pend_per_ac_PROC
          vm4_ctrl_req_pending_r_2s_comp[j] = (~vm4_ctrl_req_pending_r[j]) + 1;
          vm4_ac_first_pending_core[j] = vm4_ctrl_req_pending_r[j] & (vm4_ctrl_req_pending_r_2s_comp[j][VIRT_PROC-1:0]);
        end: vm4_pend_per_ac_PROC


          //// VM5 ////
          // default assign 0
          for (int unsigned j=0; j<`ARCSYNC_NUM_ATOMIC_CNT; j++)
          begin: vm5_default_asign_ac_first_pending_core_AC_index_PROC
            for (int unsigned i=0; i<(3); i++)
            begin: vm5_default_asign_ac_first_pending_core_VPROC_index_PROC
              vm5_ac_first_pending_core[j][i] = 1'b0;
            end: vm5_default_asign_ac_first_pending_core_VPROC_index_PROC 
          end: vm5_default_asign_ac_first_pending_core_AC_index_PROC

        // default assignment for vm5_ctrl_req_pending_r_2s_comp
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: vm5_default_asign_PROC
          vm5_ctrl_req_pending_r_2s_comp[j] = {(VIRT_PROC+1){1'b0}};
        end: vm5_default_asign_PROC

        // only update useful AC indexed vm5_ctrl_req_pending_r_2s_comp in each VM
        for (int unsigned j=40; j<48; j=j+1)
        begin: vm5_pend_per_ac_PROC
          vm5_ctrl_req_pending_r_2s_comp[j] = (~vm5_ctrl_req_pending_r[j]) + 1;
          vm5_ac_first_pending_core[j] = vm5_ctrl_req_pending_r[j] & (vm5_ctrl_req_pending_r_2s_comp[j][VIRT_PROC-1:0]);
        end: vm5_pend_per_ac_PROC


          //// VM6 ////
          // default assign 0
          for (int unsigned j=0; j<`ARCSYNC_NUM_ATOMIC_CNT; j++)
          begin: vm6_default_asign_ac_first_pending_core_AC_index_PROC
            for (int unsigned i=0; i<(3); i++)
            begin: vm6_default_asign_ac_first_pending_core_VPROC_index_PROC
              vm6_ac_first_pending_core[j][i] = 1'b0;
            end: vm6_default_asign_ac_first_pending_core_VPROC_index_PROC 
          end: vm6_default_asign_ac_first_pending_core_AC_index_PROC

        // default assignment for vm6_ctrl_req_pending_r_2s_comp
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: vm6_default_asign_PROC
          vm6_ctrl_req_pending_r_2s_comp[j] = {(VIRT_PROC+1){1'b0}};
        end: vm6_default_asign_PROC

        // only update useful AC indexed vm6_ctrl_req_pending_r_2s_comp in each VM
        for (int unsigned j=48; j<56; j=j+1)
        begin: vm6_pend_per_ac_PROC
          vm6_ctrl_req_pending_r_2s_comp[j] = (~vm6_ctrl_req_pending_r[j]) + 1;
          vm6_ac_first_pending_core[j] = vm6_ctrl_req_pending_r[j] & (vm6_ctrl_req_pending_r_2s_comp[j][VIRT_PROC-1:0]);
        end: vm6_pend_per_ac_PROC


          //// VM7 ////
          // default assign 0
          for (int unsigned j=0; j<`ARCSYNC_NUM_ATOMIC_CNT; j++)
          begin: vm7_default_asign_ac_first_pending_core_AC_index_PROC
            for (int unsigned i=0; i<(3); i++)
            begin: vm7_default_asign_ac_first_pending_core_VPROC_index_PROC
              vm7_ac_first_pending_core[j][i] = 1'b0;
            end: vm7_default_asign_ac_first_pending_core_VPROC_index_PROC 
          end: vm7_default_asign_ac_first_pending_core_AC_index_PROC

        // default assignment for vm7_ctrl_req_pending_r_2s_comp
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: vm7_default_asign_PROC
          vm7_ctrl_req_pending_r_2s_comp[j] = {(VIRT_PROC+1){1'b0}};
        end: vm7_default_asign_PROC

        // only update useful AC indexed vm7_ctrl_req_pending_r_2s_comp in each VM
        for (int unsigned j=56; j<64; j=j+1)
        begin: vm7_pend_per_ac_PROC
          vm7_ctrl_req_pending_r_2s_comp[j] = (~vm7_ctrl_req_pending_r[j]) + 1;
          vm7_ac_first_pending_core[j] = vm7_ctrl_req_pending_r[j] & (vm7_ctrl_req_pending_r_2s_comp[j][VIRT_PROC-1:0]);
        end: vm7_pend_per_ac_PROC

    

end: ac_pend_PROC

// Check whether a core has a pending request not handling yet
// if a core with pending req to an ac, it shouldn't send new request
always_comb
begin: ac_ntf_pend_PROC
      /////////////////////////// Non-VM mode ///////////////////////////
      for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
      begin: clst0_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: clst0_ntf_pend_per_core_PROC 
              core_notify[i][j]      = ctrl_req_notify_r[j][i]; 
              core_req_pending[i][j] = ctrl_req_pending_r[j][i]; 
              core_irq_pending[i][j] = (ctrl_req_pending_r[j][i] && ctrl_notify_type_r[j][i]); 

        end: clst0_ntf_pend_per_core_PROC // for AC_NUM }
      end: clst0_ntf_pend_PROC  // for core_num/vproc }

        for (int unsigned i=(0+18); i<((0+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
        begin: clst0_ntf_pend_asign0_PROC
          for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
          begin: ntf_pend_per_core_PROC 
            core_notify[i][j]      = 1'b0;
            core_req_pending[i][j] = 1'b0;
            core_irq_pending[i][j] = 1'b0; 
          end: ntf_pend_per_core_PROC // for AC_NUM }
        end: clst0_ntf_pend_asign0_PROC // for core_num }

      for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
      begin: clst1_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: clst1_ntf_pend_per_core_PROC 
              core_notify[i][j]      = ctrl_req_notify_r[j][i]; 
              core_req_pending[i][j] = ctrl_req_pending_r[j][i]; 
              core_irq_pending[i][j] = (ctrl_req_pending_r[j][i] && ctrl_notify_type_r[j][i]); 

        end: clst1_ntf_pend_per_core_PROC // for AC_NUM }
      end: clst1_ntf_pend_PROC  // for core_num/vproc }

        for (int unsigned i=(32+4); i<((1+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
        begin: clst1_ntf_pend_asign0_PROC
          for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
          begin: ntf_pend_per_core_PROC 
            core_notify[i][j]      = 1'b0;
            core_req_pending[i][j] = 1'b0;
            core_irq_pending[i][j] = 1'b0; 
          end: ntf_pend_per_core_PROC // for AC_NUM }
        end: clst1_ntf_pend_asign0_PROC // for core_num }

      for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
      begin: clst2_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: clst2_ntf_pend_per_core_PROC 
              core_notify[i][j]      = ctrl_req_notify_r[j][i]; 
              core_req_pending[i][j] = ctrl_req_pending_r[j][i]; 
              core_irq_pending[i][j] = (ctrl_req_pending_r[j][i] && ctrl_notify_type_r[j][i]); 

        end: clst2_ntf_pend_per_core_PROC // for AC_NUM }
      end: clst2_ntf_pend_PROC  // for core_num/vproc }

        for (int unsigned i=(64+1); i<((2+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1) // { for core_num
        begin: clst2_ntf_pend_asign0_PROC
          for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
          begin: ntf_pend_per_core_PROC 
            core_notify[i][j]      = 1'b0;
            core_req_pending[i][j] = 1'b0;
            core_irq_pending[i][j] = 1'b0; 
          end: ntf_pend_per_core_PROC // for AC_NUM }
        end: clst2_ntf_pend_asign0_PROC // for core_num }

    
      ///////////////////////////  VM mode ///////////////////////////
      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm0_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: vm0_ntf_pend_per_core_PROC 
            // default assign 0
            if ((j/8)!=0) // if { (j/8)!=0
            begin
              vm0_core_notify[i][j]      = 1'b0;
              vm0_core_req_pending[i][j] = 1'b0;
              vm0_core_irq_pending[i][j] = 1'b0;
            end
            else
            begin
              vm0_core_notify[i][j]      = vm0_ctrl_req_notify_r[j][i]; 
              vm0_core_req_pending[i][j] = vm0_ctrl_req_pending_r[j][i]; 
              vm0_core_irq_pending[i][j] = (vm0_ctrl_req_pending_r[j][i] && vm0_ctrl_notify_type_r[j][i]); 
            end // if (j/8)!=0 }

        end: vm0_ntf_pend_per_core_PROC // for AC_NUM }
      end: vm0_ntf_pend_PROC  // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm1_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: vm1_ntf_pend_per_core_PROC 
            // default assign 0
            if ((j/8)!=1) // if { (j/8)!=1
            begin
              vm1_core_notify[i][j]      = 1'b0;
              vm1_core_req_pending[i][j] = 1'b0;
              vm1_core_irq_pending[i][j] = 1'b0;
            end
            else
            begin
              vm1_core_notify[i][j]      = vm1_ctrl_req_notify_r[j][i]; 
              vm1_core_req_pending[i][j] = vm1_ctrl_req_pending_r[j][i]; 
              vm1_core_irq_pending[i][j] = (vm1_ctrl_req_pending_r[j][i] && vm1_ctrl_notify_type_r[j][i]); 
            end // if (j/8)!=1 }

        end: vm1_ntf_pend_per_core_PROC // for AC_NUM }
      end: vm1_ntf_pend_PROC  // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm2_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: vm2_ntf_pend_per_core_PROC 
            // default assign 0
            if ((j/8)!=2) // if { (j/8)!=2
            begin
              vm2_core_notify[i][j]      = 1'b0;
              vm2_core_req_pending[i][j] = 1'b0;
              vm2_core_irq_pending[i][j] = 1'b0;
            end
            else
            begin
              vm2_core_notify[i][j]      = vm2_ctrl_req_notify_r[j][i]; 
              vm2_core_req_pending[i][j] = vm2_ctrl_req_pending_r[j][i]; 
              vm2_core_irq_pending[i][j] = (vm2_ctrl_req_pending_r[j][i] && vm2_ctrl_notify_type_r[j][i]); 
            end // if (j/8)!=2 }

        end: vm2_ntf_pend_per_core_PROC // for AC_NUM }
      end: vm2_ntf_pend_PROC  // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm3_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: vm3_ntf_pend_per_core_PROC 
            // default assign 0
            if ((j/8)!=3) // if { (j/8)!=3
            begin
              vm3_core_notify[i][j]      = 1'b0;
              vm3_core_req_pending[i][j] = 1'b0;
              vm3_core_irq_pending[i][j] = 1'b0;
            end
            else
            begin
              vm3_core_notify[i][j]      = vm3_ctrl_req_notify_r[j][i]; 
              vm3_core_req_pending[i][j] = vm3_ctrl_req_pending_r[j][i]; 
              vm3_core_irq_pending[i][j] = (vm3_ctrl_req_pending_r[j][i] && vm3_ctrl_notify_type_r[j][i]); 
            end // if (j/8)!=3 }

        end: vm3_ntf_pend_per_core_PROC // for AC_NUM }
      end: vm3_ntf_pend_PROC  // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm4_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: vm4_ntf_pend_per_core_PROC 
            // default assign 0
            if ((j/8)!=4) // if { (j/8)!=4
            begin
              vm4_core_notify[i][j]      = 1'b0;
              vm4_core_req_pending[i][j] = 1'b0;
              vm4_core_irq_pending[i][j] = 1'b0;
            end
            else
            begin
              vm4_core_notify[i][j]      = vm4_ctrl_req_notify_r[j][i]; 
              vm4_core_req_pending[i][j] = vm4_ctrl_req_pending_r[j][i]; 
              vm4_core_irq_pending[i][j] = (vm4_ctrl_req_pending_r[j][i] && vm4_ctrl_notify_type_r[j][i]); 
            end // if (j/8)!=4 }

        end: vm4_ntf_pend_per_core_PROC // for AC_NUM }
      end: vm4_ntf_pend_PROC  // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm5_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: vm5_ntf_pend_per_core_PROC 
            // default assign 0
            if ((j/8)!=5) // if { (j/8)!=5
            begin
              vm5_core_notify[i][j]      = 1'b0;
              vm5_core_req_pending[i][j] = 1'b0;
              vm5_core_irq_pending[i][j] = 1'b0;
            end
            else
            begin
              vm5_core_notify[i][j]      = vm5_ctrl_req_notify_r[j][i]; 
              vm5_core_req_pending[i][j] = vm5_ctrl_req_pending_r[j][i]; 
              vm5_core_irq_pending[i][j] = (vm5_ctrl_req_pending_r[j][i] && vm5_ctrl_notify_type_r[j][i]); 
            end // if (j/8)!=5 }

        end: vm5_ntf_pend_per_core_PROC // for AC_NUM }
      end: vm5_ntf_pend_PROC  // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm6_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: vm6_ntf_pend_per_core_PROC 
            // default assign 0
            if ((j/8)!=6) // if { (j/8)!=6
            begin
              vm6_core_notify[i][j]      = 1'b0;
              vm6_core_req_pending[i][j] = 1'b0;
              vm6_core_irq_pending[i][j] = 1'b0;
            end
            else
            begin
              vm6_core_notify[i][j]      = vm6_ctrl_req_notify_r[j][i]; 
              vm6_core_req_pending[i][j] = vm6_ctrl_req_pending_r[j][i]; 
              vm6_core_irq_pending[i][j] = (vm6_ctrl_req_pending_r[j][i] && vm6_ctrl_notify_type_r[j][i]); 
            end // if (j/8)!=6 }

        end: vm6_ntf_pend_per_core_PROC // for AC_NUM }
      end: vm6_ntf_pend_PROC  // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm7_ntf_pend_PROC  
        for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
        begin: vm7_ntf_pend_per_core_PROC 
            // default assign 0
            if ((j/8)!=7) // if { (j/8)!=7
            begin
              vm7_core_notify[i][j]      = 1'b0;
              vm7_core_req_pending[i][j] = 1'b0;
              vm7_core_irq_pending[i][j] = 1'b0;
            end
            else
            begin
              vm7_core_notify[i][j]      = vm7_ctrl_req_notify_r[j][i]; 
              vm7_core_req_pending[i][j] = vm7_ctrl_req_pending_r[j][i]; 
              vm7_core_irq_pending[i][j] = (vm7_ctrl_req_pending_r[j][i] && vm7_ctrl_notify_type_r[j][i]); 
            end // if (j/8)!=7 }

        end: vm7_ntf_pend_per_core_PROC // for AC_NUM }
      end: vm7_ntf_pend_PROC  // for core_num/vproc }


end: ac_ntf_pend_PROC

always_comb  
begin: ac_ctrl_PROC
  ctrl_poll = !mmio_wdata[0];
  ctrl_wait =  mmio_wdata[0];
  ctrl_decr = !mmio_wdata[2];
  ctrl_incr =  mmio_wdata[2];
      /////////////////////////// Non-VM mode ///////////////////////////

    for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
    begin: ctrl_per_ac_PROC  

      for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
      begin: clst0_ctrl_per_core_PROC   
        
        
            ctrl_decr_req[j][i] = 1'b0; 
            ctrl_incr_req[j][i] = 1'b0; 
            ctrl_notify_type_nxt[j][i] = ctrl_notify_type_r[j][i];
            ctrl_req_pending_nxt[j][i] = ctrl_req_pending_r[j][i];
            ctrl_cmp_res_nxt[j][i]     = ctrl_cmp_res_r[j][i];
            ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|ctrl_req_pending_r[j])
                begin  
                  if (ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    ctrl_req_pending_nxt[j][i] = 1'b0;
                    ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  ctrl_req_pending_nxt[j][i] = ctrl_wait || ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|ac_control_wen[j] && ctrl_decr)
              begin
                if (ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    ctrl_req_pending_nxt[j][i] = 1'b0;
                    ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    ctrl_req_pending_nxt[j][i] = ctrl_wait || ctrl_req_pending_r[j][i] ;
                    ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    ctrl_req_pending_nxt[j][i] = 1'b0;
                    ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

      end: clst0_ctrl_per_core_PROC // for core_num/vproc }

        for (int unsigned i=(0+18); i<((0+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
        begin: clst0_ctrl_per_core_asign0_PROC
          ctrl_decr_req[j][i]        = 1'b0;
          ctrl_incr_req[j][i]        = 1'b0;
          ctrl_notify_type_nxt[j][i] = 1'b0;
          ctrl_req_pending_nxt[j][i] = 1'b0;
          ctrl_cmp_res_nxt[j][i]     = 1'b0;
          ctrl_req_notify_nxt[j][i]  = 1'b0;
        end: clst0_ctrl_per_core_asign0_PROC
      for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
      begin: clst1_ctrl_per_core_PROC   
        
        
            ctrl_decr_req[j][i] = 1'b0; 
            ctrl_incr_req[j][i] = 1'b0; 
            ctrl_notify_type_nxt[j][i] = ctrl_notify_type_r[j][i];
            ctrl_req_pending_nxt[j][i] = ctrl_req_pending_r[j][i];
            ctrl_cmp_res_nxt[j][i]     = ctrl_cmp_res_r[j][i];
            ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|ctrl_req_pending_r[j])
                begin  
                  if (ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    ctrl_req_pending_nxt[j][i] = 1'b0;
                    ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  ctrl_req_pending_nxt[j][i] = ctrl_wait || ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|ac_control_wen[j] && ctrl_decr)
              begin
                if (ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    ctrl_req_pending_nxt[j][i] = 1'b0;
                    ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    ctrl_req_pending_nxt[j][i] = ctrl_wait || ctrl_req_pending_r[j][i] ;
                    ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    ctrl_req_pending_nxt[j][i] = 1'b0;
                    ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

      end: clst1_ctrl_per_core_PROC // for core_num/vproc }

        for (int unsigned i=(32+4); i<((1+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
        begin: clst1_ctrl_per_core_asign0_PROC
          ctrl_decr_req[j][i]        = 1'b0;
          ctrl_incr_req[j][i]        = 1'b0;
          ctrl_notify_type_nxt[j][i] = 1'b0;
          ctrl_req_pending_nxt[j][i] = 1'b0;
          ctrl_cmp_res_nxt[j][i]     = 1'b0;
          ctrl_req_notify_nxt[j][i]  = 1'b0;
        end: clst1_ctrl_per_core_asign0_PROC
      for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
      begin: clst2_ctrl_per_core_PROC   
        
        
            ctrl_decr_req[j][i] = 1'b0; 
            ctrl_incr_req[j][i] = 1'b0; 
            ctrl_notify_type_nxt[j][i] = ctrl_notify_type_r[j][i];
            ctrl_req_pending_nxt[j][i] = ctrl_req_pending_r[j][i];
            ctrl_cmp_res_nxt[j][i]     = ctrl_cmp_res_r[j][i];
            ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|ctrl_req_pending_r[j])
                begin  
                  if (ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    ctrl_req_pending_nxt[j][i] = 1'b0;
                    ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  ctrl_req_pending_nxt[j][i] = ctrl_wait || ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|ac_control_wen[j] && ctrl_decr)
              begin
                if (ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    ctrl_req_pending_nxt[j][i] = 1'b0;
                    ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    ctrl_req_pending_nxt[j][i] = ctrl_wait || ctrl_req_pending_r[j][i] ;
                    ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    ctrl_req_pending_nxt[j][i] = 1'b0;
                    ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

      end: clst2_ctrl_per_core_PROC // for core_num/vproc }

        for (int unsigned i=(64+1); i<((2+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
        begin: clst2_ctrl_per_core_asign0_PROC
          ctrl_decr_req[j][i]        = 1'b0;
          ctrl_incr_req[j][i]        = 1'b0;
          ctrl_notify_type_nxt[j][i] = 1'b0;
          ctrl_req_pending_nxt[j][i] = 1'b0;
          ctrl_cmp_res_nxt[j][i]     = 1'b0;
          ctrl_req_notify_nxt[j][i]  = 1'b0;
        end: clst2_ctrl_per_core_asign0_PROC
    end: ctrl_per_ac_PROC // for AC_NUM }
    
      ///////////////////////////  VM mode ///////////////////////////

    for (int unsigned j=0; j<AC_NUM; j=j+1) // { for AC_NUM
    begin: ctrl_per_ac_PROC  

      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm0_ctrl_per_core_PROC   
        
          // default assign 0
          if ((j/8)!=0) // if { (j/8)!=0
          begin
            vm0_ctrl_decr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm0_ctrl_incr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm0_ctrl_notify_type_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm0_ctrl_req_pending_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm0_ctrl_cmp_res_nxt[j]        = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm0_ctrl_req_notify_nxt[j]     = {`ARCSYNC_VIRT_PROC{1'b0}};
          end
          else
          begin
        
            vm0_ctrl_decr_req[j][i] = 1'b0; 
            vm0_ctrl_incr_req[j][i] = 1'b0; 
            vm0_ctrl_notify_type_nxt[j][i] = vm0_ctrl_notify_type_r[j][i];
            vm0_ctrl_req_pending_nxt[j][i] = vm0_ctrl_req_pending_r[j][i];
            vm0_ctrl_cmp_res_nxt[j][i]     = vm0_ctrl_cmp_res_r[j][i];
            vm0_ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|vm0_ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (vm0_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  vm0_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  vm0_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|vm0_ctrl_req_pending_r[j])
                begin  
                  if (vm0_ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    vm0_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm0_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm0_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  vm0_ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (vm0_ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                vm0_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  vm0_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  vm0_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  vm0_ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  vm0_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  vm0_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm0_ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|vm0_ac_control_wen[j] && ctrl_decr)
              begin
                if (vm0_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  vm0_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  vm0_ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    vm0_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm0_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm0_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    vm0_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    vm0_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm0_ctrl_req_pending_r[j][i] ;
                    vm0_ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (vm0_ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    vm0_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm0_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm0_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              vm0_ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (vm0_ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                vm0_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                vm0_ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

          end // if (j/8)!=0 }
      end: vm0_ctrl_per_core_PROC // for core_num/vproc }

      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm1_ctrl_per_core_PROC   
        
          // default assign 0
          if ((j/8)!=1) // if { (j/8)!=1
          begin
            vm1_ctrl_decr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm1_ctrl_incr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm1_ctrl_notify_type_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm1_ctrl_req_pending_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm1_ctrl_cmp_res_nxt[j]        = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm1_ctrl_req_notify_nxt[j]     = {`ARCSYNC_VIRT_PROC{1'b0}};
          end
          else
          begin
        
            vm1_ctrl_decr_req[j][i] = 1'b0; 
            vm1_ctrl_incr_req[j][i] = 1'b0; 
            vm1_ctrl_notify_type_nxt[j][i] = vm1_ctrl_notify_type_r[j][i];
            vm1_ctrl_req_pending_nxt[j][i] = vm1_ctrl_req_pending_r[j][i];
            vm1_ctrl_cmp_res_nxt[j][i]     = vm1_ctrl_cmp_res_r[j][i];
            vm1_ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|vm1_ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (vm1_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  vm1_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  vm1_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|vm1_ctrl_req_pending_r[j])
                begin  
                  if (vm1_ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    vm1_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm1_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm1_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  vm1_ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (vm1_ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                vm1_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  vm1_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  vm1_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  vm1_ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  vm1_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  vm1_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm1_ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|vm1_ac_control_wen[j] && ctrl_decr)
              begin
                if (vm1_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  vm1_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  vm1_ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    vm1_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm1_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm1_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    vm1_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    vm1_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm1_ctrl_req_pending_r[j][i] ;
                    vm1_ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (vm1_ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    vm1_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm1_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm1_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              vm1_ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (vm1_ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                vm1_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                vm1_ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

          end // if (j/8)!=1 }
      end: vm1_ctrl_per_core_PROC // for core_num/vproc }

      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm2_ctrl_per_core_PROC   
        
          // default assign 0
          if ((j/8)!=2) // if { (j/8)!=2
          begin
            vm2_ctrl_decr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm2_ctrl_incr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm2_ctrl_notify_type_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm2_ctrl_req_pending_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm2_ctrl_cmp_res_nxt[j]        = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm2_ctrl_req_notify_nxt[j]     = {`ARCSYNC_VIRT_PROC{1'b0}};
          end
          else
          begin
        
            vm2_ctrl_decr_req[j][i] = 1'b0; 
            vm2_ctrl_incr_req[j][i] = 1'b0; 
            vm2_ctrl_notify_type_nxt[j][i] = vm2_ctrl_notify_type_r[j][i];
            vm2_ctrl_req_pending_nxt[j][i] = vm2_ctrl_req_pending_r[j][i];
            vm2_ctrl_cmp_res_nxt[j][i]     = vm2_ctrl_cmp_res_r[j][i];
            vm2_ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|vm2_ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (vm2_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  vm2_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  vm2_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|vm2_ctrl_req_pending_r[j])
                begin  
                  if (vm2_ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    vm2_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm2_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm2_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  vm2_ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (vm2_ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                vm2_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  vm2_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  vm2_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  vm2_ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  vm2_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  vm2_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm2_ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|vm2_ac_control_wen[j] && ctrl_decr)
              begin
                if (vm2_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  vm2_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  vm2_ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    vm2_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm2_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm2_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    vm2_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    vm2_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm2_ctrl_req_pending_r[j][i] ;
                    vm2_ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (vm2_ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    vm2_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm2_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm2_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              vm2_ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (vm2_ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                vm2_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                vm2_ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

          end // if (j/8)!=2 }
      end: vm2_ctrl_per_core_PROC // for core_num/vproc }

      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm3_ctrl_per_core_PROC   
        
          // default assign 0
          if ((j/8)!=3) // if { (j/8)!=3
          begin
            vm3_ctrl_decr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm3_ctrl_incr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm3_ctrl_notify_type_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm3_ctrl_req_pending_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm3_ctrl_cmp_res_nxt[j]        = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm3_ctrl_req_notify_nxt[j]     = {`ARCSYNC_VIRT_PROC{1'b0}};
          end
          else
          begin
        
            vm3_ctrl_decr_req[j][i] = 1'b0; 
            vm3_ctrl_incr_req[j][i] = 1'b0; 
            vm3_ctrl_notify_type_nxt[j][i] = vm3_ctrl_notify_type_r[j][i];
            vm3_ctrl_req_pending_nxt[j][i] = vm3_ctrl_req_pending_r[j][i];
            vm3_ctrl_cmp_res_nxt[j][i]     = vm3_ctrl_cmp_res_r[j][i];
            vm3_ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|vm3_ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (vm3_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  vm3_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  vm3_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|vm3_ctrl_req_pending_r[j])
                begin  
                  if (vm3_ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    vm3_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm3_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm3_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  vm3_ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (vm3_ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                vm3_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  vm3_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  vm3_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  vm3_ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  vm3_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  vm3_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm3_ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|vm3_ac_control_wen[j] && ctrl_decr)
              begin
                if (vm3_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  vm3_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  vm3_ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    vm3_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm3_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm3_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    vm3_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    vm3_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm3_ctrl_req_pending_r[j][i] ;
                    vm3_ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (vm3_ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    vm3_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm3_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm3_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              vm3_ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (vm3_ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                vm3_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                vm3_ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

          end // if (j/8)!=3 }
      end: vm3_ctrl_per_core_PROC // for core_num/vproc }

      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm4_ctrl_per_core_PROC   
        
          // default assign 0
          if ((j/8)!=4) // if { (j/8)!=4
          begin
            vm4_ctrl_decr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm4_ctrl_incr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm4_ctrl_notify_type_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm4_ctrl_req_pending_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm4_ctrl_cmp_res_nxt[j]        = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm4_ctrl_req_notify_nxt[j]     = {`ARCSYNC_VIRT_PROC{1'b0}};
          end
          else
          begin
        
            vm4_ctrl_decr_req[j][i] = 1'b0; 
            vm4_ctrl_incr_req[j][i] = 1'b0; 
            vm4_ctrl_notify_type_nxt[j][i] = vm4_ctrl_notify_type_r[j][i];
            vm4_ctrl_req_pending_nxt[j][i] = vm4_ctrl_req_pending_r[j][i];
            vm4_ctrl_cmp_res_nxt[j][i]     = vm4_ctrl_cmp_res_r[j][i];
            vm4_ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|vm4_ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (vm4_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  vm4_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  vm4_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|vm4_ctrl_req_pending_r[j])
                begin  
                  if (vm4_ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    vm4_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm4_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm4_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  vm4_ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (vm4_ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                vm4_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  vm4_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  vm4_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  vm4_ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  vm4_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  vm4_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm4_ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|vm4_ac_control_wen[j] && ctrl_decr)
              begin
                if (vm4_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  vm4_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  vm4_ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    vm4_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm4_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm4_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    vm4_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    vm4_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm4_ctrl_req_pending_r[j][i] ;
                    vm4_ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (vm4_ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    vm4_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm4_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm4_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              vm4_ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (vm4_ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                vm4_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                vm4_ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

          end // if (j/8)!=4 }
      end: vm4_ctrl_per_core_PROC // for core_num/vproc }

      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm5_ctrl_per_core_PROC   
        
          // default assign 0
          if ((j/8)!=5) // if { (j/8)!=5
          begin
            vm5_ctrl_decr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm5_ctrl_incr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm5_ctrl_notify_type_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm5_ctrl_req_pending_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm5_ctrl_cmp_res_nxt[j]        = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm5_ctrl_req_notify_nxt[j]     = {`ARCSYNC_VIRT_PROC{1'b0}};
          end
          else
          begin
        
            vm5_ctrl_decr_req[j][i] = 1'b0; 
            vm5_ctrl_incr_req[j][i] = 1'b0; 
            vm5_ctrl_notify_type_nxt[j][i] = vm5_ctrl_notify_type_r[j][i];
            vm5_ctrl_req_pending_nxt[j][i] = vm5_ctrl_req_pending_r[j][i];
            vm5_ctrl_cmp_res_nxt[j][i]     = vm5_ctrl_cmp_res_r[j][i];
            vm5_ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|vm5_ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (vm5_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  vm5_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  vm5_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|vm5_ctrl_req_pending_r[j])
                begin  
                  if (vm5_ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    vm5_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm5_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm5_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  vm5_ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (vm5_ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                vm5_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  vm5_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  vm5_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  vm5_ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  vm5_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  vm5_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm5_ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|vm5_ac_control_wen[j] && ctrl_decr)
              begin
                if (vm5_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  vm5_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  vm5_ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    vm5_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm5_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm5_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    vm5_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    vm5_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm5_ctrl_req_pending_r[j][i] ;
                    vm5_ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (vm5_ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    vm5_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm5_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm5_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              vm5_ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (vm5_ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                vm5_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                vm5_ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

          end // if (j/8)!=5 }
      end: vm5_ctrl_per_core_PROC // for core_num/vproc }

      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm6_ctrl_per_core_PROC   
        
          // default assign 0
          if ((j/8)!=6) // if { (j/8)!=6
          begin
            vm6_ctrl_decr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm6_ctrl_incr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm6_ctrl_notify_type_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm6_ctrl_req_pending_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm6_ctrl_cmp_res_nxt[j]        = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm6_ctrl_req_notify_nxt[j]     = {`ARCSYNC_VIRT_PROC{1'b0}};
          end
          else
          begin
        
            vm6_ctrl_decr_req[j][i] = 1'b0; 
            vm6_ctrl_incr_req[j][i] = 1'b0; 
            vm6_ctrl_notify_type_nxt[j][i] = vm6_ctrl_notify_type_r[j][i];
            vm6_ctrl_req_pending_nxt[j][i] = vm6_ctrl_req_pending_r[j][i];
            vm6_ctrl_cmp_res_nxt[j][i]     = vm6_ctrl_cmp_res_r[j][i];
            vm6_ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|vm6_ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (vm6_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  vm6_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  vm6_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|vm6_ctrl_req_pending_r[j])
                begin  
                  if (vm6_ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    vm6_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm6_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm6_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  vm6_ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (vm6_ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                vm6_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  vm6_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  vm6_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  vm6_ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  vm6_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  vm6_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm6_ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|vm6_ac_control_wen[j] && ctrl_decr)
              begin
                if (vm6_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  vm6_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  vm6_ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    vm6_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm6_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm6_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    vm6_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    vm6_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm6_ctrl_req_pending_r[j][i] ;
                    vm6_ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (vm6_ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    vm6_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm6_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm6_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              vm6_ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (vm6_ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                vm6_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                vm6_ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

          end // if (j/8)!=6 }
      end: vm6_ctrl_per_core_PROC // for core_num/vproc }

      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm7_ctrl_per_core_PROC   
        
          // default assign 0
          if ((j/8)!=7) // if { (j/8)!=7
          begin
            vm7_ctrl_decr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm7_ctrl_incr_req[j]           = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm7_ctrl_notify_type_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm7_ctrl_req_pending_nxt[j]    = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm7_ctrl_cmp_res_nxt[j]        = {`ARCSYNC_VIRT_PROC{1'b0}};
            vm7_ctrl_req_notify_nxt[j]     = {`ARCSYNC_VIRT_PROC{1'b0}};
          end
          else
          begin
        
            vm7_ctrl_decr_req[j][i] = 1'b0; 
            vm7_ctrl_incr_req[j][i] = 1'b0; 
            vm7_ctrl_notify_type_nxt[j][i] = vm7_ctrl_notify_type_r[j][i];
            vm7_ctrl_req_pending_nxt[j][i] = vm7_ctrl_req_pending_r[j][i];
            vm7_ctrl_cmp_res_nxt[j][i]     = vm7_ctrl_cmp_res_r[j][i];
            vm7_ctrl_req_notify_nxt[j][i]  = 1'b0;
            // semaphore ac handling
            if (cfg_bx_sem[j]) 
            begin
              if (|vm7_ac_control_wen[j] && ctrl_incr && ctrl_poll)
              begin 
                if (vm7_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  // a incr_poll request always returns successful comparison result
                  vm7_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  vm7_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                end  
                if (|vm7_ctrl_req_pending_r[j])
                begin  
                  if (vm7_ac_first_pending_core[j][i])
                  begin  
                    // If there is a pending core, there was no resource when it came
                    // That is, counter value is equal to zero
                    // The possible resource is only from one core releasing the resource 
                    // Clear the first pending core and keep the counter 0  
                    vm7_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm7_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm7_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end  
                end
                else  
                  // no waiting core so increment the counter
                  vm7_ctrl_incr_req[j][i] = 1'b1;                 
              end
              else if (vm7_ac_control_wen[j][i] && ctrl_decr) 
              begin
                // 0 for event, 1 for irq
                vm7_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                if (cfg_cnt_r[j]!={AC_WIDTH{1'b0}})
                begin  
                  // the core gets the available resource and send notification with wait request
                  // if there is an available resource, the request consumes that resource directly
                  // With a wait request, the notification is sent directly  
                  vm7_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                  vm7_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  vm7_ctrl_decr_req[j][i]        = 1'b1;                 
                end
                else
                begin  
                  // no available resource so the core needs to wait
                  vm7_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                  vm7_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm7_ctrl_req_pending_r[j][i] ;
                end  
              end
            end // semaphore ac handling  
            // barrier ac handling
            else if (cfg_bx_bar[j])
            begin  
              if (|vm7_ac_control_wen[j] && ctrl_decr)
              begin
                if (vm7_ac_control_wen[j][i])
                begin  
                  // 0 for event, 1 for irq
                  vm7_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                  // always decrement the counter with the barrier ac  
                  vm7_ctrl_decr_req[j][i]        = 1'b1;                 

                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    // if the core is the last core, send the notification directly
                    vm7_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm7_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm7_ctrl_req_notify_nxt[j][i]  = ctrl_wait;
                  end
                  else
                  begin
                    // the condition is not satisfied so the core needs to wait  
                    // If the core is pending and still sends request, the counter cannot be decremented
                    vm7_ctrl_cmp_res_nxt[j][i]     = 1'b0;
                    vm7_ctrl_req_pending_nxt[j][i] = ctrl_wait || vm7_ctrl_req_pending_r[j][i] ;
                    vm7_ctrl_req_notify_nxt[j][i]  = 1'b0;
                  end
                end  
                // clear all pending core when the request is from the last core
                else if (vm7_ctrl_req_pending_r[j][i])
                begin  
                  if (cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
                  begin  
                    vm7_ctrl_cmp_res_nxt[j][i]     = 1'b1;
                    vm7_ctrl_req_pending_nxt[j][i] = 1'b0;
                    vm7_ctrl_req_notify_nxt[j][i]  = 1'b1;
                  end
                end   
              end  
            end // barrier ac handling
            // index ac handling 
            else if (cfg_bx_idx[j])
            begin
              // no comparison result needed
              vm7_ctrl_cmp_res_nxt[j][i]     = 1'b0;
              if (vm7_ac_control_wen[j][i])
              begin  
                // 0 for event, 1 for irq
                vm7_ctrl_notify_type_nxt[j][i] = mmio_wdata[1];
                // incr immediately with incr & poll with index request
                vm7_ctrl_incr_req[j][i] = (ctrl_poll && ctrl_incr);                 
              end  
            end

          end // if (j/8)!=7 }
      end: vm7_ctrl_per_core_PROC // for core_num/vproc }

    end: ctrl_per_ac_PROC // for AC_NUM }
end: ac_ctrl_PROC  

//-------------------------------------------------------------------------------------------------------
// Counter Handling 
//-------------------------------------------------------------------------------------------------------
always_comb  
begin: cfg_cnt_PROC
  for (int unsigned j=0; j<AC_NUM; j=j+1)
  begin: cfg_cnt_per_ac_PROC
    cfg_cnt_nxt[j] = cfg_cnt_r[j];
    // Set the value to the initial value if it's written
    if (ac_config_wen[j]) 
        cfg_cnt_nxt[j] = cfg_cnt_ini[j];
    // With an increment request,
    // A semaphore ac with bound value saturates in the bound value
    // A index ac with bound value wraps back to 0
    // Otherwise, the counter increments
    else if ((|ctrl_incr_req[j]) | (|vm_ctrl_incr_req[j]))
    begin
      if (cfg_cnt_r[j]==cfg_bound_r[j])
      begin  
        if (!cfg_bx_sem[j])
          cfg_cnt_nxt[j] = {AC_WIDTH{1'b0}};
      end  
      else
          cfg_cnt_nxt[j] = cfg_cnt_r[j] + 1;
    end
    // With a decrement request,
    // A barrier ac with the last core request will set the counter to the bound value
    // A semaphore ac with 0 saturates in 0 
    // Otherwise, the counter decrements 
    else if ((|ctrl_decr_req[j]) | (|vm_ctrl_decr_req[j]))
    begin
      if (cfg_bx_bar[j] && cfg_cnt_r[j]=={{AC_WIDTH-1{1'b0}}, 1'b1})
        cfg_cnt_nxt[j] = cfg_bound_r[j];
      else
          cfg_cnt_nxt[j] = cfg_cnt_r[j] - 1;
    end  
  end: cfg_cnt_per_ac_PROC
end: cfg_cnt_PROC


always_comb 
begin: ac_reg_en_PROC
  for (int unsigned j=0; j<AC_NUM; j=j+1)
  begin: ac_reg_en_per_ac_PROC  
    ac_reg_en[j]         = (|ac_control_wen[j]) || ac_config_wen[j] || (|ctrl_req_notify_r[j]) || cfg_bx_idx[j] ||
                           (|vm_ac_control_wen[j]) || (|vm_ctrl_req_notify_r[j]);
  end: ac_reg_en_per_ac_PROC
end: ac_reg_en_PROC

always_ff @(posedge clk or posedge rst_a) 
begin: ac_reg_PROC
  if (rst_a) 
  begin
    for (int unsigned j=0; j<AC_NUM; j=j+1)
    begin: ac_reg_rst_PROC  
      cfg_cnt_r[j]    <= {AC_WIDTH{1'b0}};
      cfg_bound_r[j]  <= {AC_WIDTH{1'b0}};
      cfg_bx_r[j]     <= {2{1'b0}};

          /////////////////////////// Non-VM mode ///////////////////////////

          ctrl_req_pending_r[j] <={CORE_NUM{1'b0}};
          ctrl_req_notify_r[j]  <={CORE_NUM{1'b0}};
          ctrl_notify_type_r[j] <={CORE_NUM{1'b0}};
          ctrl_cmp_res_r[j]     <={CORE_NUM{1'b0}};

        
          ///////////////////////////  VM mode ///////////////////////////

          vm0_ctrl_req_pending_r[j] <={VIRT_PROC{1'b0}};
          vm0_ctrl_req_notify_r[j]  <={VIRT_PROC{1'b0}};
          vm0_ctrl_notify_type_r[j] <={VIRT_PROC{1'b0}};
          vm0_ctrl_cmp_res_r[j]     <={VIRT_PROC{1'b0}};

          vm1_ctrl_req_pending_r[j] <={VIRT_PROC{1'b0}};
          vm1_ctrl_req_notify_r[j]  <={VIRT_PROC{1'b0}};
          vm1_ctrl_notify_type_r[j] <={VIRT_PROC{1'b0}};
          vm1_ctrl_cmp_res_r[j]     <={VIRT_PROC{1'b0}};

          vm2_ctrl_req_pending_r[j] <={VIRT_PROC{1'b0}};
          vm2_ctrl_req_notify_r[j]  <={VIRT_PROC{1'b0}};
          vm2_ctrl_notify_type_r[j] <={VIRT_PROC{1'b0}};
          vm2_ctrl_cmp_res_r[j]     <={VIRT_PROC{1'b0}};

          vm3_ctrl_req_pending_r[j] <={VIRT_PROC{1'b0}};
          vm3_ctrl_req_notify_r[j]  <={VIRT_PROC{1'b0}};
          vm3_ctrl_notify_type_r[j] <={VIRT_PROC{1'b0}};
          vm3_ctrl_cmp_res_r[j]     <={VIRT_PROC{1'b0}};

          vm4_ctrl_req_pending_r[j] <={VIRT_PROC{1'b0}};
          vm4_ctrl_req_notify_r[j]  <={VIRT_PROC{1'b0}};
          vm4_ctrl_notify_type_r[j] <={VIRT_PROC{1'b0}};
          vm4_ctrl_cmp_res_r[j]     <={VIRT_PROC{1'b0}};

          vm5_ctrl_req_pending_r[j] <={VIRT_PROC{1'b0}};
          vm5_ctrl_req_notify_r[j]  <={VIRT_PROC{1'b0}};
          vm5_ctrl_notify_type_r[j] <={VIRT_PROC{1'b0}};
          vm5_ctrl_cmp_res_r[j]     <={VIRT_PROC{1'b0}};

          vm6_ctrl_req_pending_r[j] <={VIRT_PROC{1'b0}};
          vm6_ctrl_req_notify_r[j]  <={VIRT_PROC{1'b0}};
          vm6_ctrl_notify_type_r[j] <={VIRT_PROC{1'b0}};
          vm6_ctrl_cmp_res_r[j]     <={VIRT_PROC{1'b0}};

          vm7_ctrl_req_pending_r[j] <={VIRT_PROC{1'b0}};
          vm7_ctrl_req_notify_r[j]  <={VIRT_PROC{1'b0}};
          vm7_ctrl_notify_type_r[j] <={VIRT_PROC{1'b0}};
          vm7_ctrl_cmp_res_r[j]     <={VIRT_PROC{1'b0}};

    end: ac_reg_rst_PROC  
  end
  else 
  begin
    for (int unsigned j=0; j<AC_NUM; j=j+1)
    begin: ac_reg_per_ac_PROC  
      if (ac_reg_en[j])
      begin  
        cfg_cnt_r[j]    <= cfg_cnt_nxt[j];    
        cfg_bound_r[j]  <= cfg_bound_nxt[j];  
        cfg_bx_r[j]     <= cfg_bx_nxt[j]; 

            /////////////////////////// Non-VM mode ///////////////////////////


            ctrl_req_pending_r[j] <= ctrl_req_pending_nxt[j];
            ctrl_req_notify_r[j]  <= ctrl_req_notify_nxt[j];
            ctrl_notify_type_r[j] <= ctrl_notify_type_nxt[j];
            ctrl_cmp_res_r[j]     <= ctrl_cmp_res_nxt[j];
          
            ///////////////////////////  VM mode ///////////////////////////


            vm0_ctrl_req_pending_r[j] <= vm0_ctrl_req_pending_nxt[j];
            vm0_ctrl_req_notify_r[j]  <= vm0_ctrl_req_notify_nxt[j];
            vm0_ctrl_notify_type_r[j] <= vm0_ctrl_notify_type_nxt[j];
            vm0_ctrl_cmp_res_r[j]     <= vm0_ctrl_cmp_res_nxt[j];

            vm1_ctrl_req_pending_r[j] <= vm1_ctrl_req_pending_nxt[j];
            vm1_ctrl_req_notify_r[j]  <= vm1_ctrl_req_notify_nxt[j];
            vm1_ctrl_notify_type_r[j] <= vm1_ctrl_notify_type_nxt[j];
            vm1_ctrl_cmp_res_r[j]     <= vm1_ctrl_cmp_res_nxt[j];

            vm2_ctrl_req_pending_r[j] <= vm2_ctrl_req_pending_nxt[j];
            vm2_ctrl_req_notify_r[j]  <= vm2_ctrl_req_notify_nxt[j];
            vm2_ctrl_notify_type_r[j] <= vm2_ctrl_notify_type_nxt[j];
            vm2_ctrl_cmp_res_r[j]     <= vm2_ctrl_cmp_res_nxt[j];

            vm3_ctrl_req_pending_r[j] <= vm3_ctrl_req_pending_nxt[j];
            vm3_ctrl_req_notify_r[j]  <= vm3_ctrl_req_notify_nxt[j];
            vm3_ctrl_notify_type_r[j] <= vm3_ctrl_notify_type_nxt[j];
            vm3_ctrl_cmp_res_r[j]     <= vm3_ctrl_cmp_res_nxt[j];

            vm4_ctrl_req_pending_r[j] <= vm4_ctrl_req_pending_nxt[j];
            vm4_ctrl_req_notify_r[j]  <= vm4_ctrl_req_notify_nxt[j];
            vm4_ctrl_notify_type_r[j] <= vm4_ctrl_notify_type_nxt[j];
            vm4_ctrl_cmp_res_r[j]     <= vm4_ctrl_cmp_res_nxt[j];

            vm5_ctrl_req_pending_r[j] <= vm5_ctrl_req_pending_nxt[j];
            vm5_ctrl_req_notify_r[j]  <= vm5_ctrl_req_notify_nxt[j];
            vm5_ctrl_notify_type_r[j] <= vm5_ctrl_notify_type_nxt[j];
            vm5_ctrl_cmp_res_r[j]     <= vm5_ctrl_cmp_res_nxt[j];

            vm6_ctrl_req_pending_r[j] <= vm6_ctrl_req_pending_nxt[j];
            vm6_ctrl_req_notify_r[j]  <= vm6_ctrl_req_notify_nxt[j];
            vm6_ctrl_notify_type_r[j] <= vm6_ctrl_notify_type_nxt[j];
            vm6_ctrl_cmp_res_r[j]     <= vm6_ctrl_cmp_res_nxt[j];

            vm7_ctrl_req_pending_r[j] <= vm7_ctrl_req_pending_nxt[j];
            vm7_ctrl_req_notify_r[j]  <= vm7_ctrl_req_notify_nxt[j];
            vm7_ctrl_notify_type_r[j] <= vm7_ctrl_notify_type_nxt[j];
            vm7_ctrl_cmp_res_r[j]     <= vm7_ctrl_cmp_res_nxt[j];
      end  
    end: ac_reg_per_ac_PROC  
  end  
end: ac_reg_PROC

//-------------------------------------------------------------------------------------------------------
// Notification Handling 
//-------------------------------------------------------------------------------------------------------
always_comb 
begin: evt_send_PROC
      /////////////////////////// Non-VM mode ///////////////////////////
      for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
      begin: clst0_evt_send_per_core_PROC  
        irq_sending_nxt[i]  = irq_sending_r[i];
        evt_duration_nxt[i] = evt_duration_r[i];
        evt_sending_nxt[i]  = evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (ac_ack_irq_wen[i] && irq_sending_r[i])
        begin  
          irq_sending_nxt[i] = 1'b0;
        end  
        else if (|core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (core_notify[i][j] && ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (evt_duration_r[i] == EVT_DURATION)
          begin  
            evt_duration_nxt[i] = 'b0;
            evt_sending_nxt[i]  = 'b0;
          end 
          else  
            evt_duration_nxt[i] = evt_duration_r[i] + 1;
        end  
        else if (|core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (core_notify[i][j] && !ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (evt_duration_r[i]==0)
              begin  
                evt_duration_nxt[i] = evt_duration_r[i] + 1;
                evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: clst0_evt_send_per_core_PROC // for core_num/vproc }

        for (int unsigned i=(0+18); i<((0+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
        begin: clst0_evt_send_per_core_asign0_PROC
          irq_sending_nxt[i]  = 1'b0;
          evt_duration_nxt[i] = {(EVT_DUR_WIDTH+1){1'b0}};
          evt_sending_nxt[i]  = 1'b0;
        end: clst0_evt_send_per_core_asign0_PROC

      for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
      begin: clst1_evt_send_per_core_PROC  
        irq_sending_nxt[i]  = irq_sending_r[i];
        evt_duration_nxt[i] = evt_duration_r[i];
        evt_sending_nxt[i]  = evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (ac_ack_irq_wen[i] && irq_sending_r[i])
        begin  
          irq_sending_nxt[i] = 1'b0;
        end  
        else if (|core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (core_notify[i][j] && ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (evt_duration_r[i] == EVT_DURATION)
          begin  
            evt_duration_nxt[i] = 'b0;
            evt_sending_nxt[i]  = 'b0;
          end 
          else  
            evt_duration_nxt[i] = evt_duration_r[i] + 1;
        end  
        else if (|core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (core_notify[i][j] && !ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (evt_duration_r[i]==0)
              begin  
                evt_duration_nxt[i] = evt_duration_r[i] + 1;
                evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: clst1_evt_send_per_core_PROC // for core_num/vproc }

        for (int unsigned i=(32+4); i<((1+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
        begin: clst1_evt_send_per_core_asign0_PROC
          irq_sending_nxt[i]  = 1'b0;
          evt_duration_nxt[i] = {(EVT_DUR_WIDTH+1){1'b0}};
          evt_sending_nxt[i]  = 1'b0;
        end: clst1_evt_send_per_core_asign0_PROC

      for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
      begin: clst2_evt_send_per_core_PROC  
        irq_sending_nxt[i]  = irq_sending_r[i];
        evt_duration_nxt[i] = evt_duration_r[i];
        evt_sending_nxt[i]  = evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (ac_ack_irq_wen[i] && irq_sending_r[i])
        begin  
          irq_sending_nxt[i] = 1'b0;
        end  
        else if (|core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (core_notify[i][j] && ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (evt_duration_r[i] == EVT_DURATION)
          begin  
            evt_duration_nxt[i] = 'b0;
            evt_sending_nxt[i]  = 'b0;
          end 
          else  
            evt_duration_nxt[i] = evt_duration_r[i] + 1;
        end  
        else if (|core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (core_notify[i][j] && !ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (evt_duration_r[i]==0)
              begin  
                evt_duration_nxt[i] = evt_duration_r[i] + 1;
                evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: clst2_evt_send_per_core_PROC // for core_num/vproc }

        for (int unsigned i=(64+1); i<((2+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
        begin: clst2_evt_send_per_core_asign0_PROC
          irq_sending_nxt[i]  = 1'b0;
          evt_duration_nxt[i] = {(EVT_DUR_WIDTH+1){1'b0}};
          evt_sending_nxt[i]  = 1'b0;
        end: clst2_evt_send_per_core_asign0_PROC

    
      ///////////////////////////  VM mode ///////////////////////////
      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm0_evt_send_per_core_PROC  
        vm0_irq_sending_nxt[i]  = vm0_irq_sending_r[i];
        vm0_evt_duration_nxt[i] = vm0_evt_duration_r[i];
        vm0_evt_sending_nxt[i]  = vm0_evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (vm0_ac_ack_irq_wen[i] && vm0_irq_sending_r[i])
        begin  
          vm0_irq_sending_nxt[i] = 1'b0;
        end  
        else if (|vm0_core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (vm0_core_notify[i][j] && vm0_ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              vm0_irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (vm0_evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (vm0_evt_duration_r[i] == EVT_DURATION)
          begin  
            vm0_evt_duration_nxt[i] = 'b0;
            vm0_evt_sending_nxt[i]  = 'b0;
          end 
          else  
            vm0_evt_duration_nxt[i] = vm0_evt_duration_r[i] + 1;
        end  
        else if (|vm0_core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (vm0_core_notify[i][j] && !vm0_ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (vm0_evt_duration_r[i]==0)
              begin  
                vm0_evt_duration_nxt[i] = vm0_evt_duration_r[i] + 1;
                vm0_evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: vm0_evt_send_per_core_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm1_evt_send_per_core_PROC  
        vm1_irq_sending_nxt[i]  = vm1_irq_sending_r[i];
        vm1_evt_duration_nxt[i] = vm1_evt_duration_r[i];
        vm1_evt_sending_nxt[i]  = vm1_evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (vm1_ac_ack_irq_wen[i] && vm1_irq_sending_r[i])
        begin  
          vm1_irq_sending_nxt[i] = 1'b0;
        end  
        else if (|vm1_core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (vm1_core_notify[i][j] && vm1_ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              vm1_irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (vm1_evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (vm1_evt_duration_r[i] == EVT_DURATION)
          begin  
            vm1_evt_duration_nxt[i] = 'b0;
            vm1_evt_sending_nxt[i]  = 'b0;
          end 
          else  
            vm1_evt_duration_nxt[i] = vm1_evt_duration_r[i] + 1;
        end  
        else if (|vm1_core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (vm1_core_notify[i][j] && !vm1_ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (vm1_evt_duration_r[i]==0)
              begin  
                vm1_evt_duration_nxt[i] = vm1_evt_duration_r[i] + 1;
                vm1_evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: vm1_evt_send_per_core_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm2_evt_send_per_core_PROC  
        vm2_irq_sending_nxt[i]  = vm2_irq_sending_r[i];
        vm2_evt_duration_nxt[i] = vm2_evt_duration_r[i];
        vm2_evt_sending_nxt[i]  = vm2_evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (vm2_ac_ack_irq_wen[i] && vm2_irq_sending_r[i])
        begin  
          vm2_irq_sending_nxt[i] = 1'b0;
        end  
        else if (|vm2_core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (vm2_core_notify[i][j] && vm2_ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              vm2_irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (vm2_evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (vm2_evt_duration_r[i] == EVT_DURATION)
          begin  
            vm2_evt_duration_nxt[i] = 'b0;
            vm2_evt_sending_nxt[i]  = 'b0;
          end 
          else  
            vm2_evt_duration_nxt[i] = vm2_evt_duration_r[i] + 1;
        end  
        else if (|vm2_core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (vm2_core_notify[i][j] && !vm2_ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (vm2_evt_duration_r[i]==0)
              begin  
                vm2_evt_duration_nxt[i] = vm2_evt_duration_r[i] + 1;
                vm2_evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: vm2_evt_send_per_core_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm3_evt_send_per_core_PROC  
        vm3_irq_sending_nxt[i]  = vm3_irq_sending_r[i];
        vm3_evt_duration_nxt[i] = vm3_evt_duration_r[i];
        vm3_evt_sending_nxt[i]  = vm3_evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (vm3_ac_ack_irq_wen[i] && vm3_irq_sending_r[i])
        begin  
          vm3_irq_sending_nxt[i] = 1'b0;
        end  
        else if (|vm3_core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (vm3_core_notify[i][j] && vm3_ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              vm3_irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (vm3_evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (vm3_evt_duration_r[i] == EVT_DURATION)
          begin  
            vm3_evt_duration_nxt[i] = 'b0;
            vm3_evt_sending_nxt[i]  = 'b0;
          end 
          else  
            vm3_evt_duration_nxt[i] = vm3_evt_duration_r[i] + 1;
        end  
        else if (|vm3_core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (vm3_core_notify[i][j] && !vm3_ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (vm3_evt_duration_r[i]==0)
              begin  
                vm3_evt_duration_nxt[i] = vm3_evt_duration_r[i] + 1;
                vm3_evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: vm3_evt_send_per_core_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm4_evt_send_per_core_PROC  
        vm4_irq_sending_nxt[i]  = vm4_irq_sending_r[i];
        vm4_evt_duration_nxt[i] = vm4_evt_duration_r[i];
        vm4_evt_sending_nxt[i]  = vm4_evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (vm4_ac_ack_irq_wen[i] && vm4_irq_sending_r[i])
        begin  
          vm4_irq_sending_nxt[i] = 1'b0;
        end  
        else if (|vm4_core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (vm4_core_notify[i][j] && vm4_ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              vm4_irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (vm4_evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (vm4_evt_duration_r[i] == EVT_DURATION)
          begin  
            vm4_evt_duration_nxt[i] = 'b0;
            vm4_evt_sending_nxt[i]  = 'b0;
          end 
          else  
            vm4_evt_duration_nxt[i] = vm4_evt_duration_r[i] + 1;
        end  
        else if (|vm4_core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (vm4_core_notify[i][j] && !vm4_ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (vm4_evt_duration_r[i]==0)
              begin  
                vm4_evt_duration_nxt[i] = vm4_evt_duration_r[i] + 1;
                vm4_evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: vm4_evt_send_per_core_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm5_evt_send_per_core_PROC  
        vm5_irq_sending_nxt[i]  = vm5_irq_sending_r[i];
        vm5_evt_duration_nxt[i] = vm5_evt_duration_r[i];
        vm5_evt_sending_nxt[i]  = vm5_evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (vm5_ac_ack_irq_wen[i] && vm5_irq_sending_r[i])
        begin  
          vm5_irq_sending_nxt[i] = 1'b0;
        end  
        else if (|vm5_core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (vm5_core_notify[i][j] && vm5_ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              vm5_irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (vm5_evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (vm5_evt_duration_r[i] == EVT_DURATION)
          begin  
            vm5_evt_duration_nxt[i] = 'b0;
            vm5_evt_sending_nxt[i]  = 'b0;
          end 
          else  
            vm5_evt_duration_nxt[i] = vm5_evt_duration_r[i] + 1;
        end  
        else if (|vm5_core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (vm5_core_notify[i][j] && !vm5_ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (vm5_evt_duration_r[i]==0)
              begin  
                vm5_evt_duration_nxt[i] = vm5_evt_duration_r[i] + 1;
                vm5_evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: vm5_evt_send_per_core_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm6_evt_send_per_core_PROC  
        vm6_irq_sending_nxt[i]  = vm6_irq_sending_r[i];
        vm6_evt_duration_nxt[i] = vm6_evt_duration_r[i];
        vm6_evt_sending_nxt[i]  = vm6_evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (vm6_ac_ack_irq_wen[i] && vm6_irq_sending_r[i])
        begin  
          vm6_irq_sending_nxt[i] = 1'b0;
        end  
        else if (|vm6_core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (vm6_core_notify[i][j] && vm6_ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              vm6_irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (vm6_evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (vm6_evt_duration_r[i] == EVT_DURATION)
          begin  
            vm6_evt_duration_nxt[i] = 'b0;
            vm6_evt_sending_nxt[i]  = 'b0;
          end 
          else  
            vm6_evt_duration_nxt[i] = vm6_evt_duration_r[i] + 1;
        end  
        else if (|vm6_core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (vm6_core_notify[i][j] && !vm6_ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (vm6_evt_duration_r[i]==0)
              begin  
                vm6_evt_duration_nxt[i] = vm6_evt_duration_r[i] + 1;
                vm6_evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: vm6_evt_send_per_core_PROC // for core_num/vproc }


      for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
      begin: vm7_evt_send_per_core_PROC  
        vm7_irq_sending_nxt[i]  = vm7_irq_sending_r[i];
        vm7_evt_duration_nxt[i] = vm7_evt_duration_r[i];
        vm7_evt_sending_nxt[i]  = vm7_evt_sending_r[i];
        // When the acknoledgement comes for the interrupt, the interrupt becomes low
        if (vm7_ac_ack_irq_wen[i] && vm7_irq_sending_r[i])
        begin  
          vm7_irq_sending_nxt[i] = 1'b0;
        end  
        else if (|vm7_core_notify[i])
        begin
          for (int unsigned j=0; j<AC_NUM; j=j+1)
          begin: irq_send_per_ac_PROC 
            if (vm7_core_notify[i][j] && vm7_ctrl_notify_type_r[j][i])
            // notify_type 1 is for interrupt 
              vm7_irq_sending_nxt[i] = 1'b1;
          end: irq_send_per_ac_PROC 
        end

        // Keep sending the event to the defined duration
        if (vm7_evt_duration_r[i] != 'b0)
        begin  
        // An event is requested to have 5-cycle high 
          // When the event pulse is sent with the defined duration, the events are de-asserted
          if (vm7_evt_duration_r[i] == EVT_DURATION)
          begin  
            vm7_evt_duration_nxt[i] = 'b0;
            vm7_evt_sending_nxt[i]  = 'b0;
          end 
          else  
            vm7_evt_duration_nxt[i] = vm7_evt_duration_r[i] + 1;
        end  
        else if (|vm7_core_notify[i])
        begin
          for (int unsigned  j=0; j<AC_NUM; j=j+1)
          begin: evt_send_per_ac_PROC  
            if (vm7_core_notify[i][j] && !vm7_ctrl_notify_type_r[j][i])
            // notify_type 0 is for event 
            begin
              if (vm7_evt_duration_r[i]==0)
              begin  
                vm7_evt_duration_nxt[i] = vm7_evt_duration_r[i] + 1;
                vm7_evt_sending_nxt[i]  = 1'b1;
              end  
            end
          end: evt_send_per_ac_PROC
        end  
      end: vm7_evt_send_per_core_PROC // for core_num/vproc }



end: evt_send_PROC  


always_comb
begin: ac_irq_PROC
  //`for (8=0; 8<`ARCSYNC_NUM_CLUSTER; 8++)  `// { for cluster
  //  `let base = (8 * `ARCSYNC_MAX_CORES_PER_CL)
  //  `let cl_num_core  = `("ARCSYNC_NUM_CORE_CL"8) - 0 + (`NPU_HAS_L2ARC==0 ? 1 : 0)
      /////////////////////////// Non-VM mode ///////////////////////////

      for (int unsigned i=0; i<(18); i=i+1) // { for core_num/vproc
      begin: clst0_ac_ntf_PROC 
        ac_notify_reg_en[i]= (|core_notify[i]) || (ac_ack_irq_wen[i]) || (evt_duration_r[i] != 'b0) || irq_sending_r[i];
        ac_notify_src_nxt[i] = ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (ctrl_req_notify_r[j][i])
          begin  
            ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: clst0_ac_ntf_PROC // for core_num/vproc }

        for (int unsigned i=(0+18); i<((0+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
        begin: clst0_ac_ntf_asign0_PROC
          ac_notify_reg_en[i]  = 1'b0;
          ac_notify_src_nxt[i] = 16'h0;
        end: clst0_ac_ntf_asign0_PROC

      for (int unsigned i=32; i<(36); i=i+1) // { for core_num/vproc
      begin: clst1_ac_ntf_PROC 
        ac_notify_reg_en[i]= (|core_notify[i]) || (ac_ack_irq_wen[i]) || (evt_duration_r[i] != 'b0) || irq_sending_r[i];
        ac_notify_src_nxt[i] = ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (ctrl_req_notify_r[j][i])
          begin  
            ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: clst1_ac_ntf_PROC // for core_num/vproc }

        for (int unsigned i=(32+4); i<((1+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
        begin: clst1_ac_ntf_asign0_PROC
          ac_notify_reg_en[i]  = 1'b0;
          ac_notify_src_nxt[i] = 16'h0;
        end: clst1_ac_ntf_asign0_PROC

      for (int unsigned i=64; i<(65); i=i+1) // { for core_num/vproc
      begin: clst2_ac_ntf_PROC 
        ac_notify_reg_en[i]= (|core_notify[i]) || (ac_ack_irq_wen[i]) || (evt_duration_r[i] != 'b0) || irq_sending_r[i];
        ac_notify_src_nxt[i] = ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (ctrl_req_notify_r[j][i])
          begin  
            ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: clst2_ac_ntf_PROC // for core_num/vproc }

        for (int unsigned i=(64+1); i<((2+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
        begin: clst2_ac_ntf_asign0_PROC
          ac_notify_reg_en[i]  = 1'b0;
          ac_notify_src_nxt[i] = 16'h0;
        end: clst2_ac_ntf_asign0_PROC
    
      ///////////////////////////  VM mode ///////////////////////////

      for (int unsigned i=0; i<(3); i=i+1) // { for core_num/vproc
      begin: vm0_ac_ntf_PROC 
        vm0_ac_notify_reg_en[i]= (|vm0_core_notify[i]) || (vm0_ac_ack_irq_wen[i]) || (vm0_evt_duration_r[i] != 'b0) || vm0_irq_sending_r[i];
        vm0_ac_notify_src_nxt[i] = vm0_ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (vm0_ctrl_req_notify_r[j][i])
          begin  
            vm0_ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: vm0_ac_ntf_PROC // for core_num/vproc }


      for (int unsigned i=0; i<(3); i=i+1) // { for core_num/vproc
      begin: vm1_ac_ntf_PROC 
        vm1_ac_notify_reg_en[i]= (|vm1_core_notify[i]) || (vm1_ac_ack_irq_wen[i]) || (vm1_evt_duration_r[i] != 'b0) || vm1_irq_sending_r[i];
        vm1_ac_notify_src_nxt[i] = vm1_ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (vm1_ctrl_req_notify_r[j][i])
          begin  
            vm1_ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: vm1_ac_ntf_PROC // for core_num/vproc }


      for (int unsigned i=0; i<(3); i=i+1) // { for core_num/vproc
      begin: vm2_ac_ntf_PROC 
        vm2_ac_notify_reg_en[i]= (|vm2_core_notify[i]) || (vm2_ac_ack_irq_wen[i]) || (vm2_evt_duration_r[i] != 'b0) || vm2_irq_sending_r[i];
        vm2_ac_notify_src_nxt[i] = vm2_ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (vm2_ctrl_req_notify_r[j][i])
          begin  
            vm2_ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: vm2_ac_ntf_PROC // for core_num/vproc }


      for (int unsigned i=0; i<(3); i=i+1) // { for core_num/vproc
      begin: vm3_ac_ntf_PROC 
        vm3_ac_notify_reg_en[i]= (|vm3_core_notify[i]) || (vm3_ac_ack_irq_wen[i]) || (vm3_evt_duration_r[i] != 'b0) || vm3_irq_sending_r[i];
        vm3_ac_notify_src_nxt[i] = vm3_ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (vm3_ctrl_req_notify_r[j][i])
          begin  
            vm3_ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: vm3_ac_ntf_PROC // for core_num/vproc }


      for (int unsigned i=0; i<(3); i=i+1) // { for core_num/vproc
      begin: vm4_ac_ntf_PROC 
        vm4_ac_notify_reg_en[i]= (|vm4_core_notify[i]) || (vm4_ac_ack_irq_wen[i]) || (vm4_evt_duration_r[i] != 'b0) || vm4_irq_sending_r[i];
        vm4_ac_notify_src_nxt[i] = vm4_ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (vm4_ctrl_req_notify_r[j][i])
          begin  
            vm4_ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: vm4_ac_ntf_PROC // for core_num/vproc }


      for (int unsigned i=0; i<(3); i=i+1) // { for core_num/vproc
      begin: vm5_ac_ntf_PROC 
        vm5_ac_notify_reg_en[i]= (|vm5_core_notify[i]) || (vm5_ac_ack_irq_wen[i]) || (vm5_evt_duration_r[i] != 'b0) || vm5_irq_sending_r[i];
        vm5_ac_notify_src_nxt[i] = vm5_ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (vm5_ctrl_req_notify_r[j][i])
          begin  
            vm5_ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: vm5_ac_ntf_PROC // for core_num/vproc }


      for (int unsigned i=0; i<(3); i=i+1) // { for core_num/vproc
      begin: vm6_ac_ntf_PROC 
        vm6_ac_notify_reg_en[i]= (|vm6_core_notify[i]) || (vm6_ac_ack_irq_wen[i]) || (vm6_evt_duration_r[i] != 'b0) || vm6_irq_sending_r[i];
        vm6_ac_notify_src_nxt[i] = vm6_ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (vm6_ctrl_req_notify_r[j][i])
          begin  
            vm6_ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: vm6_ac_ntf_PROC // for core_num/vproc }


      for (int unsigned i=0; i<(3); i=i+1) // { for core_num/vproc
      begin: vm7_ac_ntf_PROC 
        vm7_ac_notify_reg_en[i]= (|vm7_core_notify[i]) || (vm7_ac_ack_irq_wen[i]) || (vm7_evt_duration_r[i] != 'b0) || vm7_irq_sending_r[i];
        vm7_ac_notify_src_nxt[i] = vm7_ac_notify_src_r[i] ;
        for (int unsigned j=0; j<AC_NUM; j=j+1)
        begin: ac_irq_per_core_PROC 
          // the notify source is set to the ac index triggering the notification
          // The value keeps until the new notification sends 
          if (vm7_ctrl_req_notify_r[j][i])
          begin  
            vm7_ac_notify_src_nxt[i] =  j;
          end  
        end: ac_irq_per_core_PROC
      end: vm7_ac_ntf_PROC // for core_num/vproc }

end: ac_irq_PROC

always_ff @(posedge clk or posedge rst_a)
begin: ac_ntf_reg_PROC
  if (rst_a) 
  begin
        /////////////////////////// Non-VM mode ///////////////////////////
        for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
        begin: clst0_ac_ntf_reg_rst_PROC 
          ac_notify_src_r[i] <= 16'hffff; 
          evt_sending_r[i]   <= 'b0;
          irq_sending_r[i]   <= 'b0;
          evt_duration_r[i]  <= 'b0;
        end: clst0_ac_ntf_reg_rst_PROC // for core_num/vproc }
        for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
        begin: clst1_ac_ntf_reg_rst_PROC 
          ac_notify_src_r[i] <= 16'hffff; 
          evt_sending_r[i]   <= 'b0;
          irq_sending_r[i]   <= 'b0;
          evt_duration_r[i]  <= 'b0;
        end: clst1_ac_ntf_reg_rst_PROC // for core_num/vproc }
        for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
        begin: clst2_ac_ntf_reg_rst_PROC 
          ac_notify_src_r[i] <= 16'hffff; 
          evt_sending_r[i]   <= 'b0;
          irq_sending_r[i]   <= 'b0;
          evt_duration_r[i]  <= 'b0;
        end: clst2_ac_ntf_reg_rst_PROC // for core_num/vproc }
      
        ///////////////////////////  VM mode ///////////////////////////
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm0_ac_ntf_reg_rst_PROC 
          vm0_ac_notify_src_r[i] <= 16'hffff; 
          vm0_evt_sending_r[i]   <= 'b0;
          vm0_irq_sending_r[i]   <= 'b0;
          vm0_evt_duration_r[i]  <= 'b0;
        end: vm0_ac_ntf_reg_rst_PROC // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm1_ac_ntf_reg_rst_PROC 
          vm1_ac_notify_src_r[i] <= 16'hffff; 
          vm1_evt_sending_r[i]   <= 'b0;
          vm1_irq_sending_r[i]   <= 'b0;
          vm1_evt_duration_r[i]  <= 'b0;
        end: vm1_ac_ntf_reg_rst_PROC // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm2_ac_ntf_reg_rst_PROC 
          vm2_ac_notify_src_r[i] <= 16'hffff; 
          vm2_evt_sending_r[i]   <= 'b0;
          vm2_irq_sending_r[i]   <= 'b0;
          vm2_evt_duration_r[i]  <= 'b0;
        end: vm2_ac_ntf_reg_rst_PROC // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm3_ac_ntf_reg_rst_PROC 
          vm3_ac_notify_src_r[i] <= 16'hffff; 
          vm3_evt_sending_r[i]   <= 'b0;
          vm3_irq_sending_r[i]   <= 'b0;
          vm3_evt_duration_r[i]  <= 'b0;
        end: vm3_ac_ntf_reg_rst_PROC // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm4_ac_ntf_reg_rst_PROC 
          vm4_ac_notify_src_r[i] <= 16'hffff; 
          vm4_evt_sending_r[i]   <= 'b0;
          vm4_irq_sending_r[i]   <= 'b0;
          vm4_evt_duration_r[i]  <= 'b0;
        end: vm4_ac_ntf_reg_rst_PROC // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm5_ac_ntf_reg_rst_PROC 
          vm5_ac_notify_src_r[i] <= 16'hffff; 
          vm5_evt_sending_r[i]   <= 'b0;
          vm5_irq_sending_r[i]   <= 'b0;
          vm5_evt_duration_r[i]  <= 'b0;
        end: vm5_ac_ntf_reg_rst_PROC // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm6_ac_ntf_reg_rst_PROC 
          vm6_ac_notify_src_r[i] <= 16'hffff; 
          vm6_evt_sending_r[i]   <= 'b0;
          vm6_irq_sending_r[i]   <= 'b0;
          vm6_evt_duration_r[i]  <= 'b0;
        end: vm6_ac_ntf_reg_rst_PROC // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm7_ac_ntf_reg_rst_PROC 
          vm7_ac_notify_src_r[i] <= 16'hffff; 
          vm7_evt_sending_r[i]   <= 'b0;
          vm7_irq_sending_r[i]   <= 'b0;
          vm7_evt_duration_r[i]  <= 'b0;
        end: vm7_ac_ntf_reg_rst_PROC // for core_num/vproc }

      for (int unsigned i=(0+18); i<((0+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
      begin: ac_reg_asign0_PROC_1
        ac_notify_src_r[i] <= 16'h0;
        evt_sending_r[i]   <= 1'b0;
        irq_sending_r[i]   <= 1'b0;
        evt_duration_r[i]  <= {(EVT_DUR_WIDTH+1){1'b0}};
      end: ac_reg_asign0_PROC_1
      for (int unsigned i=(32+4); i<((1+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
      begin: ac_reg_asign0_PROC_1
        ac_notify_src_r[i] <= 16'h0;
        evt_sending_r[i]   <= 1'b0;
        irq_sending_r[i]   <= 1'b0;
        evt_duration_r[i]  <= {(EVT_DUR_WIDTH+1){1'b0}};
      end: ac_reg_asign0_PROC_1
      for (int unsigned i=(64+1); i<((2+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
      begin: ac_reg_asign0_PROC_1
        ac_notify_src_r[i] <= 16'h0;
        evt_sending_r[i]   <= 1'b0;
        irq_sending_r[i]   <= 1'b0;
        evt_duration_r[i]  <= {(EVT_DUR_WIDTH+1){1'b0}};
      end: ac_reg_asign0_PROC_1
  end
  else 
  begin
        /////////////////////////// Non-VM mode ///////////////////////////
        for (int unsigned i=0; i<18; i=i+1) // { for core_num/vproc
        begin: clst0_ac_ntf_reg_set_PROC 
          if (ac_notify_reg_en[i]) 
          begin  
            ac_notify_src_r[i] <= ac_notify_src_nxt[i] ;
            evt_sending_r[i]   <= evt_sending_nxt[i];
            irq_sending_r[i]   <= irq_sending_nxt[i];
            evt_duration_r[i]  <= evt_duration_nxt[i];
          end  
        end: clst0_ac_ntf_reg_set_PROC  // for core_num/vproc }
        for (int unsigned i=32; i<36; i=i+1) // { for core_num/vproc
        begin: clst1_ac_ntf_reg_set_PROC 
          if (ac_notify_reg_en[i]) 
          begin  
            ac_notify_src_r[i] <= ac_notify_src_nxt[i] ;
            evt_sending_r[i]   <= evt_sending_nxt[i];
            irq_sending_r[i]   <= irq_sending_nxt[i];
            evt_duration_r[i]  <= evt_duration_nxt[i];
          end  
        end: clst1_ac_ntf_reg_set_PROC  // for core_num/vproc }
        for (int unsigned i=64; i<65; i=i+1) // { for core_num/vproc
        begin: clst2_ac_ntf_reg_set_PROC 
          if (ac_notify_reg_en[i]) 
          begin  
            ac_notify_src_r[i] <= ac_notify_src_nxt[i] ;
            evt_sending_r[i]   <= evt_sending_nxt[i];
            irq_sending_r[i]   <= irq_sending_nxt[i];
            evt_duration_r[i]  <= evt_duration_nxt[i];
          end  
        end: clst2_ac_ntf_reg_set_PROC  // for core_num/vproc }
      
        ///////////////////////////  VM mode ///////////////////////////
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm0_ac_ntf_reg_set_PROC 
          if (vm0_ac_notify_reg_en[i]) 
          begin  
            vm0_ac_notify_src_r[i] <= vm0_ac_notify_src_nxt[i] ;
            vm0_evt_sending_r[i]   <= vm0_evt_sending_nxt[i];
            vm0_irq_sending_r[i]   <= vm0_irq_sending_nxt[i];
            vm0_evt_duration_r[i]  <= vm0_evt_duration_nxt[i];
          end  
        end: vm0_ac_ntf_reg_set_PROC  // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm1_ac_ntf_reg_set_PROC 
          if (vm1_ac_notify_reg_en[i]) 
          begin  
            vm1_ac_notify_src_r[i] <= vm1_ac_notify_src_nxt[i] ;
            vm1_evt_sending_r[i]   <= vm1_evt_sending_nxt[i];
            vm1_irq_sending_r[i]   <= vm1_irq_sending_nxt[i];
            vm1_evt_duration_r[i]  <= vm1_evt_duration_nxt[i];
          end  
        end: vm1_ac_ntf_reg_set_PROC  // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm2_ac_ntf_reg_set_PROC 
          if (vm2_ac_notify_reg_en[i]) 
          begin  
            vm2_ac_notify_src_r[i] <= vm2_ac_notify_src_nxt[i] ;
            vm2_evt_sending_r[i]   <= vm2_evt_sending_nxt[i];
            vm2_irq_sending_r[i]   <= vm2_irq_sending_nxt[i];
            vm2_evt_duration_r[i]  <= vm2_evt_duration_nxt[i];
          end  
        end: vm2_ac_ntf_reg_set_PROC  // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm3_ac_ntf_reg_set_PROC 
          if (vm3_ac_notify_reg_en[i]) 
          begin  
            vm3_ac_notify_src_r[i] <= vm3_ac_notify_src_nxt[i] ;
            vm3_evt_sending_r[i]   <= vm3_evt_sending_nxt[i];
            vm3_irq_sending_r[i]   <= vm3_irq_sending_nxt[i];
            vm3_evt_duration_r[i]  <= vm3_evt_duration_nxt[i];
          end  
        end: vm3_ac_ntf_reg_set_PROC  // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm4_ac_ntf_reg_set_PROC 
          if (vm4_ac_notify_reg_en[i]) 
          begin  
            vm4_ac_notify_src_r[i] <= vm4_ac_notify_src_nxt[i] ;
            vm4_evt_sending_r[i]   <= vm4_evt_sending_nxt[i];
            vm4_irq_sending_r[i]   <= vm4_irq_sending_nxt[i];
            vm4_evt_duration_r[i]  <= vm4_evt_duration_nxt[i];
          end  
        end: vm4_ac_ntf_reg_set_PROC  // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm5_ac_ntf_reg_set_PROC 
          if (vm5_ac_notify_reg_en[i]) 
          begin  
            vm5_ac_notify_src_r[i] <= vm5_ac_notify_src_nxt[i] ;
            vm5_evt_sending_r[i]   <= vm5_evt_sending_nxt[i];
            vm5_irq_sending_r[i]   <= vm5_irq_sending_nxt[i];
            vm5_evt_duration_r[i]  <= vm5_evt_duration_nxt[i];
          end  
        end: vm5_ac_ntf_reg_set_PROC  // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm6_ac_ntf_reg_set_PROC 
          if (vm6_ac_notify_reg_en[i]) 
          begin  
            vm6_ac_notify_src_r[i] <= vm6_ac_notify_src_nxt[i] ;
            vm6_evt_sending_r[i]   <= vm6_evt_sending_nxt[i];
            vm6_irq_sending_r[i]   <= vm6_irq_sending_nxt[i];
            vm6_evt_duration_r[i]  <= vm6_evt_duration_nxt[i];
          end  
        end: vm6_ac_ntf_reg_set_PROC  // for core_num/vproc }
        for (int unsigned i=0; i<3; i=i+1) // { for core_num/vproc
        begin: vm7_ac_ntf_reg_set_PROC 
          if (vm7_ac_notify_reg_en[i]) 
          begin  
            vm7_ac_notify_src_r[i] <= vm7_ac_notify_src_nxt[i] ;
            vm7_evt_sending_r[i]   <= vm7_evt_sending_nxt[i];
            vm7_irq_sending_r[i]   <= vm7_irq_sending_nxt[i];
            vm7_evt_duration_r[i]  <= vm7_evt_duration_nxt[i];
          end  
        end: vm7_ac_ntf_reg_set_PROC  // for core_num/vproc }

      for (int unsigned i=(0+18); i<((0+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
      begin: ac_reg_asign0_PROC_1
        ac_notify_src_r[i] <= 16'h0;
        evt_sending_r[i]   <= 1'b0;
        irq_sending_r[i]   <= 1'b0;
        evt_duration_r[i]  <= {(EVT_DUR_WIDTH+1){1'b0}};
      end: ac_reg_asign0_PROC_1
      for (int unsigned i=(32+4); i<((1+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
      begin: ac_reg_asign0_PROC_1
        ac_notify_src_r[i] <= 16'h0;
        evt_sending_r[i]   <= 1'b0;
        irq_sending_r[i]   <= 1'b0;
        evt_duration_r[i]  <= {(EVT_DUR_WIDTH+1){1'b0}};
      end: ac_reg_asign0_PROC_1
      for (int unsigned i=(64+1); i<((2+1) * `ARCSYNC_MAX_CORES_PER_CL); i=i+1)
      begin: ac_reg_asign0_PROC_1
        ac_notify_src_r[i] <= 16'h0;
        evt_sending_r[i]   <= 1'b0;
        irq_sending_r[i]   <= 1'b0;
        evt_duration_r[i]  <= {(EVT_DUR_WIDTH+1){1'b0}};
      end: ac_reg_asign0_PROC_1
  end
end: ac_ntf_reg_PROC
//-------------------------------------------------------------------------------------------------------
// Properties
//-------------------------------------------------------------------------------------------------------

endmodule
