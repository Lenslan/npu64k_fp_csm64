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
`include "arcsync_defines.v"

module arcsync_top_stub
(





  //
  // Cluster # 0  pfx="" type=0  itf_stub=0

    // -l2arc
      // Power status                                                                                                     
  input logic                       nl2arc_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       nl2arc_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       nl2arc_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       nl2arc_pd_logic,    // Power down of power domain logics                     
  input logic                       nl2arc_pd_logic1,    // Power down of power domain logics                     
  input logic                       nl2arc_pd_logic2,    // Power down of power domain logics                     
      // NPU Group Power status
  input logic                       grp0_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp0_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp0_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp0_pd_logic,    // Power down of power domain logics                     
  input logic                       grp0_pd_logic1,    // Power down of power domain logics                     
  input logic                       grp0_pd_logic2,    // Power down of power domain logics                     
  // NPU Group Power status
  input logic                       grp1_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp1_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp1_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp1_pd_logic,    // Power down of power domain logics                     
  input logic                       grp1_pd_logic1,    // Power down of power domain logics                     
  input logic                       grp1_pd_logic2,    // Power down of power domain logics                     
  // NPU Group Power status
  input logic                       grp2_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp2_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp2_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp2_pd_logic,    // Power down of power domain logics                     
  input logic                       grp2_pd_logic1,    // Power down of power domain logics                     
  input logic                       grp2_pd_logic2,    // Power down of power domain logics                     
  // NPU Group Power status
  input logic                       grp3_isolate_n,   // Isolate control signal for power domain of component (active low)
  input logic                       grp3_isolate,     // Isolate control signal for power domain of component (active high)
  input logic                       grp3_pd_mem,      // Power down of power domain memories (SRAM)            
  input logic                       grp3_pd_logic,    // Power down of power domain logics                     
  input logic                       grp3_pd_logic1,    // Power down of power domain logics                     
  input logic                       grp3_pd_logic2,    // Power down of power domain logics                     
  // -sl`i l1arc
    // Power status                                                                                                     
  input logic                       sl0nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl0nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl0nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl0nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl0nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl0nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl1nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl1nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl1nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl1nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl1nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl1nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl2nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl2nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl2nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl2nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl2nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl2nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl3nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl3nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl3nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl3nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl3nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl3nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl4nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl4nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl4nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl4nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl4nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl4nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl5nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl5nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl5nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl5nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl5nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl5nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl6nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl6nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl6nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl6nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl6nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl6nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl7nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl7nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl7nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl7nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl7nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl7nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl8nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl8nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl8nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl8nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl8nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl8nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl9nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl9nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl9nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl9nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl9nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl9nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl10nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl10nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl10nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl10nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl10nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl10nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl11nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl11nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl11nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl11nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl11nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl11nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl12nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl12nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl12nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl12nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl12nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl12nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl13nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl13nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl13nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl13nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl13nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl13nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl14nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl14nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl14nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl14nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl14nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl14nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       sl15nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       sl15nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       sl15nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       sl15nl1arc_pd_logic,    // Power down of power domain logics                       
  input logic                       sl15nl1arc_pd_logic1,    // Power down of power domain logics                       
  input logic                       sl15nl1arc_pd_logic2,    // Power down of power domain logics                       







  //
  // Cluster # 1  pfx="v0" type=1  itf_stub=1

  //
  // VPX Clusters
  //
  //
  // VPX Clusters #v0##4#
  //
  input logic [40-1:16] v0csm_addr_base,
  input logic [40-1:16] v0periph_addr_base,

  input logic   [7:0]             v0clusternum,           // specify the cluster number ID
  // Boot
  input logic   [7:0]             v0c0arcnum,          // Specifies the processor ID
  input logic  [31:10]            v0c0intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  input logic                     v0c0rst_a,           // core reset
  input logic                     v0c0clk_en,          // Clock Enable
  // Halt
  input logic                     v0c0arc_halt_req,    // processor asynchronous halt request
  output  logic                     v0c0arc_halt_ack_a,  // processor halt request acknowledge
  output  logic                     v0c0ext_arc_halt_req_a, // External (CTI) halt request
  input logic                     v0c0ext_arc_halt_ack, // Extenrak (CTI) processor halt request ack
  // Run
  input logic                     v0c0arc_run_req,     // processor asynchronous run request
  output  logic                     v0c0arc_run_ack_a,   // processor run request acknowledge
  output  logic                     v0c0ext_arc_run_req_a, // external (CTI) processor run request
  input logic                     v0c0ext_arc_run_ack, // external (CTI) forward of run req ack
  // Status
  output  logic                     v0c0sys_sleep_r,     // If true then processor is sleeping
  output  logic   [2:0]             v0c0sys_sleep_mode_r,// Indicated sleep mode of processor
  output  logic                     v0c0sys_halt_r,      // If true then processor is halted
  output  logic                     v0c0sys_tf_halt_r,   // If true then processor is halted
  output  logic   [2:0]             v0c0pmode,           // Indicated pmode of processor
  // Reset
  // IRQ and Event
  input logic                     v0c0arc_irq0_a,   // An asynchronous interrupt inputs to core
  input logic                     v0c0arc_irq1_a,   // An asynchronous interrupt inputs to core
  input logic                     v0c0arc_event0_a, // An asynchronous interrupt inputs to core
  input logic                     v0c0arc_event1_a, // An asynchronous interrupt inputs to core
  // Boot
  input logic   [7:0]             v0c1arcnum,          // Specifies the processor ID
  input logic  [31:10]            v0c1intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  input logic                     v0c1rst_a,           // core reset
  input logic                     v0c1clk_en,          // Clock Enable
  // Halt
  input logic                     v0c1arc_halt_req,    // processor asynchronous halt request
  output  logic                     v0c1arc_halt_ack_a,  // processor halt request acknowledge
  output  logic                     v0c1ext_arc_halt_req_a, // External (CTI) halt request
  input logic                     v0c1ext_arc_halt_ack, // Extenrak (CTI) processor halt request ack
  // Run
  input logic                     v0c1arc_run_req,     // processor asynchronous run request
  output  logic                     v0c1arc_run_ack_a,   // processor run request acknowledge
  output  logic                     v0c1ext_arc_run_req_a, // external (CTI) processor run request
  input logic                     v0c1ext_arc_run_ack, // external (CTI) forward of run req ack
  // Status
  output  logic                     v0c1sys_sleep_r,     // If true then processor is sleeping
  output  logic   [2:0]             v0c1sys_sleep_mode_r,// Indicated sleep mode of processor
  output  logic                     v0c1sys_halt_r,      // If true then processor is halted
  output  logic                     v0c1sys_tf_halt_r,   // If true then processor is halted
  output  logic   [2:0]             v0c1pmode,           // Indicated pmode of processor
  // Reset
  // IRQ and Event
  input logic                     v0c1arc_irq0_a,   // An asynchronous interrupt inputs to core
  input logic                     v0c1arc_irq1_a,   // An asynchronous interrupt inputs to core
  input logic                     v0c1arc_event0_a, // An asynchronous interrupt inputs to core
  input logic                     v0c1arc_event1_a, // An asynchronous interrupt inputs to core
  // Boot
  input logic   [7:0]             v0c2arcnum,          // Specifies the processor ID
  input logic  [31:10]            v0c2intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  input logic                     v0c2rst_a,           // core reset
  input logic                     v0c2clk_en,          // Clock Enable
  // Halt
  input logic                     v0c2arc_halt_req,    // processor asynchronous halt request
  output  logic                     v0c2arc_halt_ack_a,  // processor halt request acknowledge
  output  logic                     v0c2ext_arc_halt_req_a, // External (CTI) halt request
  input logic                     v0c2ext_arc_halt_ack, // Extenrak (CTI) processor halt request ack
  // Run
  input logic                     v0c2arc_run_req,     // processor asynchronous run request
  output  logic                     v0c2arc_run_ack_a,   // processor run request acknowledge
  output  logic                     v0c2ext_arc_run_req_a, // external (CTI) processor run request
  input logic                     v0c2ext_arc_run_ack, // external (CTI) forward of run req ack
  // Status
  output  logic                     v0c2sys_sleep_r,     // If true then processor is sleeping
  output  logic   [2:0]             v0c2sys_sleep_mode_r,// Indicated sleep mode of processor
  output  logic                     v0c2sys_halt_r,      // If true then processor is halted
  output  logic                     v0c2sys_tf_halt_r,   // If true then processor is halted
  output  logic   [2:0]             v0c2pmode,           // Indicated pmode of processor
  // Reset
  // IRQ and Event
  input logic                     v0c2arc_irq0_a,   // An asynchronous interrupt inputs to core
  input logic                     v0c2arc_irq1_a,   // An asynchronous interrupt inputs to core
  input logic                     v0c2arc_event0_a, // An asynchronous interrupt inputs to core
  input logic                     v0c2arc_event1_a, // An asynchronous interrupt inputs to core
  // Boot
  input logic   [7:0]             v0c3arcnum,          // Specifies the processor ID
  input logic  [31:10]            v0c3intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  input logic                     v0c3rst_a,           // core reset
  input logic                     v0c3clk_en,          // Clock Enable
  // Halt
  input logic                     v0c3arc_halt_req,    // processor asynchronous halt request
  output  logic                     v0c3arc_halt_ack_a,  // processor halt request acknowledge
  output  logic                     v0c3ext_arc_halt_req_a, // External (CTI) halt request
  input logic                     v0c3ext_arc_halt_ack, // Extenrak (CTI) processor halt request ack
  // Run
  input logic                     v0c3arc_run_req,     // processor asynchronous run request
  output  logic                     v0c3arc_run_ack_a,   // processor run request acknowledge
  output  logic                     v0c3ext_arc_run_req_a, // external (CTI) processor run request
  input logic                     v0c3ext_arc_run_ack, // external (CTI) forward of run req ack
  // Status
  output  logic                     v0c3sys_sleep_r,     // If true then processor is sleeping
  output  logic   [2:0]             v0c3sys_sleep_mode_r,// Indicated sleep mode of processor
  output  logic                     v0c3sys_halt_r,      // If true then processor is halted
  output  logic                     v0c3sys_tf_halt_r,   // If true then processor is halted
  output  logic   [2:0]             v0c3pmode,           // Indicated pmode of processor
  // Reset
  // IRQ and Event
  input logic                     v0c3arc_irq0_a,   // An asynchronous interrupt inputs to core
  input logic                     v0c3arc_irq1_a,   // An asynchronous interrupt inputs to core
  input logic                     v0c3arc_event0_a, // An asynchronous interrupt inputs to core
  input logic                     v0c3arc_event1_a, // An asynchronous interrupt inputs to core

        input logic vpx_v0_vm0_irq0_a,
      input logic vpx_v0_vm0_irq_ac_a,

        input logic vpx_v0_vm0_evt0_a,
      input logic vpx_v0_vm0_evt_ac_a,
        input logic vpx_v0_vm1_irq0_a,
      input logic vpx_v0_vm1_irq_ac_a,

        input logic vpx_v0_vm1_evt0_a,
      input logic vpx_v0_vm1_evt_ac_a,
        input logic vpx_v0_vm2_irq0_a,
      input logic vpx_v0_vm2_irq_ac_a,

        input logic vpx_v0_vm2_evt0_a,
      input logic vpx_v0_vm2_evt_ac_a,
        input logic vpx_v0_vm3_irq0_a,
      input logic vpx_v0_vm3_irq_ac_a,

        input logic vpx_v0_vm3_evt0_a,
      input logic vpx_v0_vm3_evt_ac_a,
        input logic vpx_v0_vm4_irq0_a,
      input logic vpx_v0_vm4_irq_ac_a,

        input logic vpx_v0_vm4_evt0_a,
      input logic vpx_v0_vm4_evt_ac_a,
        input logic vpx_v0_vm5_irq0_a,
      input logic vpx_v0_vm5_irq_ac_a,

        input logic vpx_v0_vm5_evt0_a,
      input logic vpx_v0_vm5_evt_ac_a,
        input logic vpx_v0_vm6_irq0_a,
      input logic vpx_v0_vm6_irq_ac_a,

        input logic vpx_v0_vm6_evt0_a,
      input logic vpx_v0_vm6_evt_ac_a,
        input logic vpx_v0_vm7_irq0_a,
      input logic vpx_v0_vm7_irq_ac_a,

        input logic vpx_v0_vm7_evt0_a,
      input logic vpx_v0_vm7_evt_ac_a,

      // Power status                                                                                                     
  input logic                       v0c0_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       v0c0_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       v0c0_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       v0c0_pd_logic,    // Power down of power domain logics                       
  input logic                       v0c0_pd_logic1,    // Power down of power domain logics                       
  input logic                       v0c0_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       v0c1_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       v0c1_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       v0c1_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       v0c1_pd_logic,    // Power down of power domain logics                       
  input logic                       v0c1_pd_logic1,    // Power down of power domain logics                       
  input logic                       v0c1_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       v0c2_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       v0c2_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       v0c2_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       v0c2_pd_logic,    // Power down of power domain logics                       
  input logic                       v0c2_pd_logic1,    // Power down of power domain logics                       
  input logic                       v0c2_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  input logic                       v0c3_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  input logic                       v0c3_isolate,     // Isolate control signal for power domain 1 of component (active high)
  input logic                       v0c3_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  input logic                       v0c3_pd_logic,    // Power down of power domain logics                       
  input logic                       v0c3_pd_logic1,    // Power down of power domain logics                       
  input logic                       v0c3_pd_logic2,    // Power down of power domain logics                       






  //
  // Cluster # 2  pfx="h0" type=2  itf_stub=1


  // Host


  input logic      arcsync_clk,                     // clock, all logic clocked at posedge
  input logic      arcsync_rst_a                    // asynchronous reset, active high
);






  





  //VPX CL1
  assign v0c0arc_halt_ack_a     = '1;  // processor halt request acknowledge
  assign v0c0ext_arc_halt_req_a = '0;  // External (CTI) halt request
  assign v0c0arc_run_ack_a      = '1;  // processor run request acknowledge
  assign v0c0ext_arc_run_req_a  = '0;  // external (CTI) processor run request
  assign v0c0sys_sleep_r        = '0;  // If true then processor is sleeping
  assign v0c0sys_sleep_mode_r   = '0;  // Indicated sleep mode of processor
  assign v0c0sys_halt_r         = '0;  // If true then processor is halted
  assign v0c0sys_tf_halt_r      = '0;  // If true then processor is halted
  assign v0c0pmode              = 3'b0;// Indicated pmode of processor
  assign v0c1arc_halt_ack_a     = '1;  // processor halt request acknowledge
  assign v0c1ext_arc_halt_req_a = '0;  // External (CTI) halt request
  assign v0c1arc_run_ack_a      = '1;  // processor run request acknowledge
  assign v0c1ext_arc_run_req_a  = '0;  // external (CTI) processor run request
  assign v0c1sys_sleep_r        = '0;  // If true then processor is sleeping
  assign v0c1sys_sleep_mode_r   = '0;  // Indicated sleep mode of processor
  assign v0c1sys_halt_r         = '0;  // If true then processor is halted
  assign v0c1sys_tf_halt_r      = '0;  // If true then processor is halted
  assign v0c1pmode              = 3'b0;// Indicated pmode of processor
  assign v0c2arc_halt_ack_a     = '1;  // processor halt request acknowledge
  assign v0c2ext_arc_halt_req_a = '0;  // External (CTI) halt request
  assign v0c2arc_run_ack_a      = '1;  // processor run request acknowledge
  assign v0c2ext_arc_run_req_a  = '0;  // external (CTI) processor run request
  assign v0c2sys_sleep_r        = '0;  // If true then processor is sleeping
  assign v0c2sys_sleep_mode_r   = '0;  // Indicated sleep mode of processor
  assign v0c2sys_halt_r         = '0;  // If true then processor is halted
  assign v0c2sys_tf_halt_r      = '0;  // If true then processor is halted
  assign v0c2pmode              = 3'b0;// Indicated pmode of processor
  assign v0c3arc_halt_ack_a     = '1;  // processor halt request acknowledge
  assign v0c3ext_arc_halt_req_a = '0;  // External (CTI) halt request
  assign v0c3arc_run_ack_a      = '1;  // processor run request acknowledge
  assign v0c3ext_arc_run_req_a  = '0;  // external (CTI) processor run request
  assign v0c3sys_sleep_r        = '0;  // If true then processor is sleeping
  assign v0c3sys_sleep_mode_r   = '0;  // Indicated sleep mode of processor
  assign v0c3sys_halt_r         = '0;  // If true then processor is halted
  assign v0c3sys_tf_halt_r      = '0;  // If true then processor is halted
  assign v0c3pmode              = 3'b0;// Indicated pmode of processor

  





  


endmodule

