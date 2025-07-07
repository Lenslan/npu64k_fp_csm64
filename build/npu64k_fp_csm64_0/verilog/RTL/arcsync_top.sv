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

  //  ARCSync Usage
  //  +----------------------------------------------------+
  //  |                    ARCSync                         |
  //  +----------------------------------------------------+
  //      |     ^         | | | |             |    |||| 
  //      |     |a        | | | |             |    |||| 
  //      |     |x        | | | |             |    |||| 
  //  +------+  |i   +----------------+   +----------------+
  //  |      |  |    | V VPX Clusters |   | M NPU Clusters |
  //  | Host |  |    |    N cores     |   |    S slices    |
  //  |      |  |    |  per cluster   |   |  per cluster   |
  //  +------+  |    +----------------+   +----------------+
  //      |     |            |                    | 
  //  +----------------------------------------------------+
  //  |              Interconnect                          |
  //  +----------------------------------------------------+
  // 
  //   
  //  Todo: support configruation parameters
  //  The configuration numbers should include Cluster numbers, Slice numbers, Host type, PMU, GPRC, and so on
  //

`include "arcsync_defines.v"
`include "npu_axi_macros.svh"
`include "npu_macros.svh"


module arcsync_top
  import npu_types::*;
(
  //
  // MMIO
  //
  // The axi user signals are not used. set to 0.
// spyglass disable_block Ac_unsync01
// SMD: output not sync 
// SJ: Use A2X DW as CDC 
  // read command channel
  input  logic                        arcsync_axi_arvalid, // read command valid
  output logic                        arcsync_axi_arready, // read command accept
  input  logic          [16-1:0]  arcsync_axi_arid,    // read command ID
  input  logic          [40-1:0]   arcsync_axi_araddr  ,      // read command
  input  logic          [3:0]         arcsync_axi_arcache ,      // read command
  input  logic          [2:0]         arcsync_axi_arprot  ,      // read command
  input  logic          [1-1:0]         arcsync_axi_arlock  ,      // read command
  input  logic          [1:0]         arcsync_axi_arburst ,      // read command
  input  logic          [3:0]         arcsync_axi_arlen   ,      // read command
  input  logic          [2:0]         arcsync_axi_arsize  ,      // read command
  // read data channel
  output logic                        arcsync_axi_rvalid,  // read data valid
  input  logic                        arcsync_axi_rready,  // read data accept
  output logic          [16-1:0]  arcsync_axi_rid,     // read data id
  output logic          [64-1:0]   arcsync_axi_rdata,   // read data
  output logic          [1:0]         arcsync_axi_rresp,   // read response
  output logic                        arcsync_axi_rlast,   // read last
  // write command channel
  input  logic                        arcsync_axi_awvalid, // write command valid
  output logic                        arcsync_axi_awready, // write command accept
  input  logic          [16-1:0]  arcsync_axi_awid,    // write command ID
  input  logic          [40-1:0]   arcsync_axi_awaddr  ,      // read command
  input  logic          [3:0]         arcsync_axi_awcache ,      // read command
  input  logic          [2:0]         arcsync_axi_awprot  ,      // read command
  input  logic          [1-1:0]         arcsync_axi_awlock  ,      // read command
  input  logic          [1:0]         arcsync_axi_awburst ,      // read command
  input  logic          [3:0]         arcsync_axi_awlen   ,      // read command
  input  logic          [2:0]         arcsync_axi_awsize  ,      // read command
  // write data channel
  input  logic                        arcsync_axi_wvalid,  // write data valid
  output logic                        arcsync_axi_wready,  // write data accept
  input  logic          [64-1:0]   arcsync_axi_wdata,   // write data
  input  logic          [64/8-1:0] arcsync_axi_wstrb,   // write data strobe
  input  logic                        arcsync_axi_wlast,   // write data last
  // write response channel
  output logic                        arcsync_axi_bvalid,  // write response valid
  input  logic                        arcsync_axi_bready,  // write response accept
  output logic          [16-1:0]  arcsync_axi_bid,     // write response id
  output logic          [1:0]         arcsync_axi_bresp,   // write response,
// spyglass enable_block Ac_unsync01



  


  // --------------------------
  // NPX Connections
  //     cl id = 0
  //     prefix = 
  //
  output logic [7:0] nl2arc_clusternum,
  // l2arc #0 nl2arc0_
    output logic [31: 10]            nl2arc0_intvbase,             // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     nl2arc0_rst_a,                // L2 core reset
  output logic                     nl2arc0_clk_en,               // Clock Enable
  // Halt
  output logic                     nl2arc0_arc_halt_req,         // processor asynchronous halt request
  input  logic                     nl2arc0_arc_halt_ack_a,       // processor halt request acknowledge
  input  logic                     nl2arc0_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     nl2arc0_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     nl2arc0_arc_run_req,          // processor asynchronous run request
  input  logic                     nl2arc0_arc_run_ack_a,        // processor run request acknowledge
  input  logic                     nl2arc0_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     nl2arc0_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     nl2arc0_sys_sleep_r,          // If true then processor is sleeping
  input  logic   [2:0]             nl2arc0_sys_sleep_mode_r,     // Indicated sleep mode of processor
  input  logic                     nl2arc0_sys_halt_r,           // If true then processor is halted
  input  logic                     nl2arc0_sys_tf_halt_r,        // If true then processor is halted
  // IRQ and Event
  output logic   [17:0]             nl2arc0_arc_irq_a,              // Asynchronous interrupt outputs to core
  output logic   [17:0]             nl2arc0_arc_event_a,            // Asynchronous event output to core
  // l2arc #1 nl2arc1_
    output logic [31: 10]            nl2arc1_intvbase,             // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     nl2arc1_rst_a,                // L2 core reset
  output logic                     nl2arc1_clk_en,               // Clock Enable
  // Halt
  output logic                     nl2arc1_arc_halt_req,         // processor asynchronous halt request
  input  logic                     nl2arc1_arc_halt_ack_a,       // processor halt request acknowledge
  input  logic                     nl2arc1_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     nl2arc1_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     nl2arc1_arc_run_req,          // processor asynchronous run request
  input  logic                     nl2arc1_arc_run_ack_a,        // processor run request acknowledge
  input  logic                     nl2arc1_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     nl2arc1_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     nl2arc1_sys_sleep_r,          // If true then processor is sleeping
  input  logic   [2:0]             nl2arc1_sys_sleep_mode_r,     // Indicated sleep mode of processor
  input  logic                     nl2arc1_sys_halt_r,           // If true then processor is halted
  input  logic                     nl2arc1_sys_tf_halt_r,        // If true then processor is halted
  // IRQ and Event
  output logic   [17:0]             nl2arc1_arc_irq_a,              // Asynchronous interrupt outputs to core
  output logic   [17:0]             nl2arc1_arc_event_a,            // Asynchronous event output to core

  // l1arc from npu_slice
    // Boot
  output logic  [31:10]            sl0nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl0_rst_a,           // Slice reset
  output logic                     sl0_clk_en,          // Clock Enable
  // Halt
  output logic                     sl0nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl0nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl0nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl0nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl0nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl0nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl0nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl0nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl0nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl0nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl0nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl0nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl0nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl1nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl1_rst_a,           // Slice reset
  output logic                     sl1_clk_en,          // Clock Enable
  // Halt
  output logic                     sl1nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl1nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl1nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl1nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl1nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl1nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl1nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl1nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl1nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl1nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl1nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl1nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl1nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl2nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl2_rst_a,           // Slice reset
  output logic                     sl2_clk_en,          // Clock Enable
  // Halt
  output logic                     sl2nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl2nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl2nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl2nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl2nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl2nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl2nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl2nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl2nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl2nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl2nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl2nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl2nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl3nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl3_rst_a,           // Slice reset
  output logic                     sl3_clk_en,          // Clock Enable
  // Halt
  output logic                     sl3nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl3nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl3nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl3nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl3nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl3nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl3nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl3nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl3nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl3nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl3nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl3nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl3nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl4nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl4_rst_a,           // Slice reset
  output logic                     sl4_clk_en,          // Clock Enable
  // Halt
  output logic                     sl4nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl4nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl4nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl4nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl4nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl4nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl4nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl4nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl4nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl4nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl4nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl4nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl4nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl5nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl5_rst_a,           // Slice reset
  output logic                     sl5_clk_en,          // Clock Enable
  // Halt
  output logic                     sl5nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl5nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl5nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl5nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl5nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl5nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl5nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl5nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl5nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl5nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl5nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl5nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl5nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl6nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl6_rst_a,           // Slice reset
  output logic                     sl6_clk_en,          // Clock Enable
  // Halt
  output logic                     sl6nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl6nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl6nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl6nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl6nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl6nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl6nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl6nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl6nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl6nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl6nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl6nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl6nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl7nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl7_rst_a,           // Slice reset
  output logic                     sl7_clk_en,          // Clock Enable
  // Halt
  output logic                     sl7nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl7nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl7nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl7nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl7nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl7nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl7nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl7nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl7nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl7nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl7nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl7nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl7nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl8nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl8_rst_a,           // Slice reset
  output logic                     sl8_clk_en,          // Clock Enable
  // Halt
  output logic                     sl8nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl8nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl8nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl8nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl8nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl8nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl8nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl8nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl8nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl8nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl8nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl8nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl8nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl9nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl9_rst_a,           // Slice reset
  output logic                     sl9_clk_en,          // Clock Enable
  // Halt
  output logic                     sl9nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl9nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl9nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl9nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl9nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl9nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl9nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl9nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl9nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl9nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl9nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl9nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl9nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl10nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl10_rst_a,           // Slice reset
  output logic                     sl10_clk_en,          // Clock Enable
  // Halt
  output logic                     sl10nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl10nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl10nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl10nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl10nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl10nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl10nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl10nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl10nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl10nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl10nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl10nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl10nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl11nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl11_rst_a,           // Slice reset
  output logic                     sl11_clk_en,          // Clock Enable
  // Halt
  output logic                     sl11nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl11nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl11nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl11nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl11nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl11nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl11nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl11nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl11nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl11nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl11nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl11nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl11nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl12nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl12_rst_a,           // Slice reset
  output logic                     sl12_clk_en,          // Clock Enable
  // Halt
  output logic                     sl12nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl12nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl12nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl12nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl12nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl12nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl12nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl12nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl12nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl12nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl12nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl12nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl12nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl13nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl13_rst_a,           // Slice reset
  output logic                     sl13_clk_en,          // Clock Enable
  // Halt
  output logic                     sl13nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl13nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl13nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl13nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl13nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl13nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl13nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl13nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl13nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl13nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl13nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl13nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl13nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl14nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl14_rst_a,           // Slice reset
  output logic                     sl14_clk_en,          // Clock Enable
  // Halt
  output logic                     sl14nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl14nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl14nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl14nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl14nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl14nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl14nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl14nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl14nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl14nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl14nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl14nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl14nl1arc_arc_irq,         // An asynchronous interrupt outputs to core
  // Boot
  output logic  [31:10]            sl15nl1arc_intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     sl15_rst_a,           // Slice reset
  output logic                     sl15_clk_en,          // Clock Enable
  // Halt
  output logic                     sl15nl1arc_arc_halt_req,    // processor asynchronous halt request
  input  logic                     sl15nl1arc_arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     sl15nl1arc_ext_arc_halt_req_a,   // External (CTI) halt request
  output logic                     sl15nl1arc_ext_arc_halt_ack,     // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     sl15nl1arc_arc_run_req,     // processor asynchronous run request
  input  logic                     sl15nl1arc_arc_run_ack_a,   // processor run request acknowledge
  input  logic                     sl15nl1arc_ext_arc_run_req_a,      // external (CTI) processor run request
  output logic                     sl15nl1arc_ext_arc_run_ack,      // external (CTI) forward of run req ack
  // Status
  input  logic                     sl15nl1arc_sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             sl15nl1arc_sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     sl15nl1arc_sys_halt_r,      // If true then processor is halted
  input  logic                     sl15nl1arc_sys_tf_halt_r,   // If true then processor is halted
  // IRQ and Event
  output logic   [1:0]             sl15nl1arc_arc_irq,         // An asynchronous interrupt outputs to core

  // _pwr_dwn_a
  output logic                       nl2arc_pwr_dwn,
  output logic                       nl2arc0_pwr_dwn,
  output logic                       nl2arc1_pwr_dwn,
  output logic                       grp0_pwr_dwn,
  output logic                       grp1_pwr_dwn,
  output logic                       grp2_pwr_dwn,
  output logic                       grp3_pwr_dwn,
  output logic                       sl0nl1arc_pwr_dwn,
  output logic                       sl1nl1arc_pwr_dwn,
  output logic                       sl2nl1arc_pwr_dwn,
  output logic                       sl3nl1arc_pwr_dwn,
  output logic                       sl4nl1arc_pwr_dwn,
  output logic                       sl5nl1arc_pwr_dwn,
  output logic                       sl6nl1arc_pwr_dwn,
  output logic                       sl7nl1arc_pwr_dwn,
  output logic                       sl8nl1arc_pwr_dwn,
  output logic                       sl9nl1arc_pwr_dwn,
  output logic                       sl10nl1arc_pwr_dwn,
  output logic                       sl11nl1arc_pwr_dwn,
  output logic                       sl12nl1arc_pwr_dwn,
  output logic                       sl13nl1arc_pwr_dwn,
  output logic                       sl14nl1arc_pwr_dwn,
  output logic                       sl15nl1arc_pwr_dwn,

  // power domain
  // - pdm l2arc
    // Power status                                                                                                     
  output logic                       nl2arc_isolate_n,   // Isolate control signal for power domain of component (active low)
  output logic                       nl2arc_isolate,     // Isolate control signal for power domain of component (active high)
  output logic                       nl2arc_pd_mem,      // Power down of power domain memories (SRAM)            
  output logic                       nl2arc_pd_logic,    // Power down of power domain logics                     
  output logic                       nl2arc_pd_logic1,    // Power down of power domain logics                     
  output logic                       nl2arc_pd_logic2,    // Power down of power domain logics                     
  // NPU Group Power Domain Interface should be added and implemented later
     // NPU Group Power status
  output logic                       grp0_isolate_n,   // Isolate control signal for power domain of component (active low)
  output logic                       grp0_isolate,     // Isolate control signal for power domain of component (active high)
  output logic                       grp0_pd_mem,      // Power down of power domain memories (SRAM)            
  output logic                       grp0_pd_logic,    // Power down of power domain logics                     
  output logic                       grp0_pd_logic1,    // Power down of power domain logics                     
  output logic                       grp0_pd_logic2,    // Power down of power domain logics                     
  // NPU Group Power status
  output logic                       grp1_isolate_n,   // Isolate control signal for power domain of component (active low)
  output logic                       grp1_isolate,     // Isolate control signal for power domain of component (active high)
  output logic                       grp1_pd_mem,      // Power down of power domain memories (SRAM)            
  output logic                       grp1_pd_logic,    // Power down of power domain logics                     
  output logic                       grp1_pd_logic1,    // Power down of power domain logics                     
  output logic                       grp1_pd_logic2,    // Power down of power domain logics                     
  // NPU Group Power status
  output logic                       grp2_isolate_n,   // Isolate control signal for power domain of component (active low)
  output logic                       grp2_isolate,     // Isolate control signal for power domain of component (active high)
  output logic                       grp2_pd_mem,      // Power down of power domain memories (SRAM)            
  output logic                       grp2_pd_logic,    // Power down of power domain logics                     
  output logic                       grp2_pd_logic1,    // Power down of power domain logics                     
  output logic                       grp2_pd_logic2,    // Power down of power domain logics                     
  // NPU Group Power status
  output logic                       grp3_isolate_n,   // Isolate control signal for power domain of component (active low)
  output logic                       grp3_isolate,     // Isolate control signal for power domain of component (active high)
  output logic                       grp3_pd_mem,      // Power down of power domain memories (SRAM)            
  output logic                       grp3_pd_logic,    // Power down of power domain logics                     
  output logic                       grp3_pd_logic1,    // Power down of power domain logics                     
  output logic                       grp3_pd_logic2,    // Power down of power domain logics                     
  // - pdm sl16 l1arc
    // Power status                                                                                                     
  output logic                       sl0nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl0nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl0nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl0nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl0nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl0nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl1nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl1nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl1nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl1nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl1nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl1nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl2nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl2nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl2nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl2nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl2nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl2nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl3nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl3nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl3nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl3nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl3nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl3nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl4nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl4nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl4nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl4nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl4nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl4nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl5nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl5nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl5nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl5nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl5nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl5nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl6nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl6nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl6nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl6nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl6nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl6nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl7nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl7nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl7nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl7nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl7nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl7nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl8nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl8nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl8nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl8nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl8nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl8nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl9nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl9nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl9nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl9nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl9nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl9nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl10nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl10nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl10nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl10nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl10nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl10nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl11nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl11nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl11nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl11nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl11nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl11nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl12nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl12nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl12nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl12nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl12nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl12nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl13nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl13nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl13nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl13nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl13nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl13nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl14nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl14nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl14nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl14nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl14nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl14nl1arc_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       sl15nl1arc_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       sl15nl1arc_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       sl15nl1arc_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       sl15nl1arc_pd_logic,    // Power down of power domain logics                       
  output logic                       sl15nl1arc_pd_logic1,    // Power down of power domain logics                       
  output logic                       sl15nl1arc_pd_logic2,    // Power down of power domain logics                       

  output logic       nl2_rst,  //this signal should be driven by ARCSync internal logic

  output  logic                         grp0_rst_a,
  output  logic                         grp0_clk_en,
  output  logic                         grp1_rst_a,
  output  logic                         grp1_clk_en,
  output  logic                         grp2_rst_a,
  output  logic                         grp2_clk_en,
  output  logic                         grp3_rst_a,
  output  logic                         grp3_clk_en,





  



  // --------------------------
  // VPX/HS Connections
  //   cl_pfx   = v0
  //   vpxpfx   = 
  //   vpx_cnum = 4
  //
  output logic   [7:0]             v0clusternum,           // specify the cluster number ID
  // Boot
  output logic   [7:0]             v0c0arcnum,          // Specifies the processor ID
  output logic  [31:10]            v0c0intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     v0c0rst_a,           // core reset
  output logic                     v0c0clk_en,          // Clock Enable
  // Halt
  output logic                     v0c0arc_halt_req,    // processor asynchronous halt request
  input  logic                     v0c0arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     v0c0ext_arc_halt_req_a, // External (CTI) halt request
  output logic                     v0c0ext_arc_halt_ack, // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     v0c0arc_run_req,     // processor asynchronous run request
  input  logic                     v0c0arc_run_ack_a,   // processor run request acknowledge
  input  logic                     v0c0ext_arc_run_req_a, // external (CTI) processor run request
  output logic                     v0c0ext_arc_run_ack, // external (CTI) forward of run req ack
  // Status
  input  logic                     v0c0sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             v0c0sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     v0c0sys_halt_r,      // If true then processor is halted
  input  logic                     v0c0sys_tf_halt_r,   // If true then processor is halted
  input  logic   [2:0]             v0c0pmode,           // Indicated pmode of processor
  // Reset
  // IRQ and Event
  output logic                     v0c0arc_irq0_a,   // An asynchronous interrupt outputs to core
  output logic                     v0c0arc_irq1_a,   // An asynchronous interrupt outputs to core
  output logic                     v0c0arc_event0_a, // An asynchronous interrupt outputs to core
  output logic                     v0c0arc_event1_a, // An asynchronous interrupt outputs to core
  // Boot
  output logic   [7:0]             v0c1arcnum,          // Specifies the processor ID
  output logic  [31:10]            v0c1intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     v0c1rst_a,           // core reset
  output logic                     v0c1clk_en,          // Clock Enable
  // Halt
  output logic                     v0c1arc_halt_req,    // processor asynchronous halt request
  input  logic                     v0c1arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     v0c1ext_arc_halt_req_a, // External (CTI) halt request
  output logic                     v0c1ext_arc_halt_ack, // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     v0c1arc_run_req,     // processor asynchronous run request
  input  logic                     v0c1arc_run_ack_a,   // processor run request acknowledge
  input  logic                     v0c1ext_arc_run_req_a, // external (CTI) processor run request
  output logic                     v0c1ext_arc_run_ack, // external (CTI) forward of run req ack
  // Status
  input  logic                     v0c1sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             v0c1sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     v0c1sys_halt_r,      // If true then processor is halted
  input  logic                     v0c1sys_tf_halt_r,   // If true then processor is halted
  input  logic   [2:0]             v0c1pmode,           // Indicated pmode of processor
  // Reset
  // IRQ and Event
  output logic                     v0c1arc_irq0_a,   // An asynchronous interrupt outputs to core
  output logic                     v0c1arc_irq1_a,   // An asynchronous interrupt outputs to core
  output logic                     v0c1arc_event0_a, // An asynchronous interrupt outputs to core
  output logic                     v0c1arc_event1_a, // An asynchronous interrupt outputs to core
  // Boot
  output logic   [7:0]             v0c2arcnum,          // Specifies the processor ID
  output logic  [31:10]            v0c2intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     v0c2rst_a,           // core reset
  output logic                     v0c2clk_en,          // Clock Enable
  // Halt
  output logic                     v0c2arc_halt_req,    // processor asynchronous halt request
  input  logic                     v0c2arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     v0c2ext_arc_halt_req_a, // External (CTI) halt request
  output logic                     v0c2ext_arc_halt_ack, // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     v0c2arc_run_req,     // processor asynchronous run request
  input  logic                     v0c2arc_run_ack_a,   // processor run request acknowledge
  input  logic                     v0c2ext_arc_run_req_a, // external (CTI) processor run request
  output logic                     v0c2ext_arc_run_ack, // external (CTI) forward of run req ack
  // Status
  input  logic                     v0c2sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             v0c2sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     v0c2sys_halt_r,      // If true then processor is halted
  input  logic                     v0c2sys_tf_halt_r,   // If true then processor is halted
  input  logic   [2:0]             v0c2pmode,           // Indicated pmode of processor
  // Reset
  // IRQ and Event
  output logic                     v0c2arc_irq0_a,   // An asynchronous interrupt outputs to core
  output logic                     v0c2arc_irq1_a,   // An asynchronous interrupt outputs to core
  output logic                     v0c2arc_event0_a, // An asynchronous interrupt outputs to core
  output logic                     v0c2arc_event1_a, // An asynchronous interrupt outputs to core
  // Boot
  output logic   [7:0]             v0c3arcnum,          // Specifies the processor ID
  output logic  [31:10]            v0c3intvbase,        // Reset value for core interrupt vector table base address
  // CLK enable and core reset
  output logic                     v0c3rst_a,           // core reset
  output logic                     v0c3clk_en,          // Clock Enable
  // Halt
  output logic                     v0c3arc_halt_req,    // processor asynchronous halt request
  input  logic                     v0c3arc_halt_ack_a,  // processor halt request acknowledge
  input  logic                     v0c3ext_arc_halt_req_a, // External (CTI) halt request
  output logic                     v0c3ext_arc_halt_ack, // Extenrak (CTI) processor halt request ack
  // Run
  output logic                     v0c3arc_run_req,     // processor asynchronous run request
  input  logic                     v0c3arc_run_ack_a,   // processor run request acknowledge
  input  logic                     v0c3ext_arc_run_req_a, // external (CTI) processor run request
  output logic                     v0c3ext_arc_run_ack, // external (CTI) forward of run req ack
  // Status
  input  logic                     v0c3sys_sleep_r,     // If true then processor is sleeping
  input  logic   [2:0]             v0c3sys_sleep_mode_r,// Indicated sleep mode of processor
  input  logic                     v0c3sys_halt_r,      // If true then processor is halted
  input  logic                     v0c3sys_tf_halt_r,   // If true then processor is halted
  input  logic   [2:0]             v0c3pmode,           // Indicated pmode of processor
  // Reset
  // IRQ and Event
  output logic                     v0c3arc_irq0_a,   // An asynchronous interrupt outputs to core
  output logic                     v0c3arc_irq1_a,   // An asynchronous interrupt outputs to core
  output logic                     v0c3arc_event0_a, // An asynchronous interrupt outputs to core
  output logic                     v0c3arc_event1_a, // An asynchronous interrupt outputs to core

  output logic vpx_v0_vm0_irq0_a,
  output logic vpx_v0_vm0_irq_ac_a,

  output logic vpx_v0_vm0_evt0_a,
  output logic vpx_v0_vm0_evt_ac_a,
  output logic vpx_v0_vm1_irq0_a,
  output logic vpx_v0_vm1_irq_ac_a,

  output logic vpx_v0_vm1_evt0_a,
  output logic vpx_v0_vm1_evt_ac_a,
  output logic vpx_v0_vm2_irq0_a,
  output logic vpx_v0_vm2_irq_ac_a,

  output logic vpx_v0_vm2_evt0_a,
  output logic vpx_v0_vm2_evt_ac_a,
  output logic vpx_v0_vm3_irq0_a,
  output logic vpx_v0_vm3_irq_ac_a,

  output logic vpx_v0_vm3_evt0_a,
  output logic vpx_v0_vm3_evt_ac_a,
  output logic vpx_v0_vm4_irq0_a,
  output logic vpx_v0_vm4_irq_ac_a,

  output logic vpx_v0_vm4_evt0_a,
  output logic vpx_v0_vm4_evt_ac_a,
  output logic vpx_v0_vm5_irq0_a,
  output logic vpx_v0_vm5_irq_ac_a,

  output logic vpx_v0_vm5_evt0_a,
  output logic vpx_v0_vm5_evt_ac_a,
  output logic vpx_v0_vm6_irq0_a,
  output logic vpx_v0_vm6_irq_ac_a,

  output logic vpx_v0_vm6_evt0_a,
  output logic vpx_v0_vm6_evt_ac_a,
  output logic vpx_v0_vm7_irq0_a,
  output logic vpx_v0_vm7_irq_ac_a,

  output logic vpx_v0_vm7_evt0_a,
  output logic vpx_v0_vm7_evt_ac_a,

  output logic v0c0_pwr_dwn,
  output logic v0c1_pwr_dwn,
  output logic v0c2_pwr_dwn,
  output logic v0c3_pwr_dwn,
    // Power status                                                                                                     
  output logic                       v0c0_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       v0c0_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       v0c0_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       v0c0_pd_logic,    // Power down of power domain logics                       
  output logic                       v0c0_pd_logic1,    // Power down of power domain logics                       
  output logic                       v0c0_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       v0c1_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       v0c1_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       v0c1_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       v0c1_pd_logic,    // Power down of power domain logics                       
  output logic                       v0c1_pd_logic1,    // Power down of power domain logics                       
  output logic                       v0c1_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       v0c2_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       v0c2_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       v0c2_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       v0c2_pd_logic,    // Power down of power domain logics                       
  output logic                       v0c2_pd_logic1,    // Power down of power domain logics                       
  output logic                       v0c2_pd_logic2,    // Power down of power domain logics                       
  // Power status                                                                                                     
  output logic                       v0c3_isolate_n,   // Isolate control signal for power domain 1 of component (active low)
  output logic                       v0c3_isolate,     // Isolate control signal for power domain 1 of component (active high)
  output logic                       v0c3_pd_mem,      // Power down of power domain 1 memories (SRAM)            
  output logic                       v0c3_pd_logic,    // Power down of power domain logics                       
  output logic                       v0c3_pd_logic1,    // Power down of power domain logics                       
  output logic                       v0c3_pd_logic2,    // Power down of power domain logics                       

  output logic [40-1:16] v0csm_addr_base,
  output logic [40-1:16] v0periph_addr_base,



  




  // --------------------------
  // Host
  //   cl_pfx = h0
  //
  output logic  [1:0] h0host_irq,
  output logic  [1:0] h0host_event,

  output logic [15:0]  h0host_virt_evt_a,
  output logic [15:0]  h0host_virt_irq_a,



  //
  // clock and reset
  //
  input logic      arcsync_axi_clk,         // clock, all logic clocked at posedge
  input logic      arcsync_axi_rst_a,       // Reset from arcsync external 

  input logic      arcsync_core_iso_override,            //Isolate override control signal for power domain (used for test) when test_mode valid


  input logic      test_mode,  
  input logic      arcsync_clk,             // clock, all logic clocked at posedge
  input logic      arcsync_rst_a            // asynchronous reset, active high
);

  logic  arcsync_axi_arregion;
  logic  arcsync_axi_awregion;
  assign arcsync_axi_arregion = '0;
  assign arcsync_axi_awregion = '0;



  logic  v0c0_pu_rst;
  logic  v0c1_pu_rst;
  logic  v0c2_pu_rst;
  logic  v0c3_pu_rst;



//endmodule : arcsync_top


wire [`ARCSYNC_NUM_CLUSTER-1:0][`ARCSYNC_VIRT_MACHINES*(`ARCSYNC_NUM_EVT_PER_VPROC + 1)-1:0] cluster_vproc_evt;
wire [`ARCSYNC_NUM_CLUSTER-1:0][`ARCSYNC_VIRT_MACHINES*(`ARCSYNC_NUM_IRQ_PER_VPROC + 1)-1:0] cluster_vproc_irq;



      assign nl2arc0_arc_event_a[17:2] = cluster_vproc_evt[0];
      assign nl2arc0_arc_irq_a[17:2]   = cluster_vproc_irq[0];
      assign nl2arc1_arc_event_a[17:2] = cluster_vproc_evt[0];
      assign nl2arc1_arc_irq_a[17:2]   = cluster_vproc_irq[0];






            assign vpx_v0_vm0_irq_ac_a = cluster_vproc_irq[1][0*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 0];
            assign vpx_v0_vm0_irq0_a = cluster_vproc_irq[1][0*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 1];

            assign vpx_v0_vm0_evt_ac_a = cluster_vproc_evt[1][0*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 0];
            assign vpx_v0_vm0_evt0_a = cluster_vproc_evt[1][0*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 1];

            assign vpx_v0_vm1_irq_ac_a = cluster_vproc_irq[1][1*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 0];
            assign vpx_v0_vm1_irq0_a = cluster_vproc_irq[1][1*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 1];

            assign vpx_v0_vm1_evt_ac_a = cluster_vproc_evt[1][1*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 0];
            assign vpx_v0_vm1_evt0_a = cluster_vproc_evt[1][1*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 1];

            assign vpx_v0_vm2_irq_ac_a = cluster_vproc_irq[1][2*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 0];
            assign vpx_v0_vm2_irq0_a = cluster_vproc_irq[1][2*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 1];

            assign vpx_v0_vm2_evt_ac_a = cluster_vproc_evt[1][2*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 0];
            assign vpx_v0_vm2_evt0_a = cluster_vproc_evt[1][2*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 1];

            assign vpx_v0_vm3_irq_ac_a = cluster_vproc_irq[1][3*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 0];
            assign vpx_v0_vm3_irq0_a = cluster_vproc_irq[1][3*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 1];

            assign vpx_v0_vm3_evt_ac_a = cluster_vproc_evt[1][3*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 0];
            assign vpx_v0_vm3_evt0_a = cluster_vproc_evt[1][3*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 1];

            assign vpx_v0_vm4_irq_ac_a = cluster_vproc_irq[1][4*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 0];
            assign vpx_v0_vm4_irq0_a = cluster_vproc_irq[1][4*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 1];

            assign vpx_v0_vm4_evt_ac_a = cluster_vproc_evt[1][4*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 0];
            assign vpx_v0_vm4_evt0_a = cluster_vproc_evt[1][4*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 1];

            assign vpx_v0_vm5_irq_ac_a = cluster_vproc_irq[1][5*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 0];
            assign vpx_v0_vm5_irq0_a = cluster_vproc_irq[1][5*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 1];

            assign vpx_v0_vm5_evt_ac_a = cluster_vproc_evt[1][5*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 0];
            assign vpx_v0_vm5_evt0_a = cluster_vproc_evt[1][5*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 1];

            assign vpx_v0_vm6_irq_ac_a = cluster_vproc_irq[1][6*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 0];
            assign vpx_v0_vm6_irq0_a = cluster_vproc_irq[1][6*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 1];

            assign vpx_v0_vm6_evt_ac_a = cluster_vproc_evt[1][6*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 0];
            assign vpx_v0_vm6_evt0_a = cluster_vproc_evt[1][6*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 1];

            assign vpx_v0_vm7_irq_ac_a = cluster_vproc_irq[1][7*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 0];
            assign vpx_v0_vm7_irq0_a = cluster_vproc_irq[1][7*(`ARCSYNC_NUM_IRQ_PER_VPROC+1)+ 1];

            assign vpx_v0_vm7_evt_ac_a = cluster_vproc_evt[1][7*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 0];
            assign vpx_v0_vm7_evt0_a = cluster_vproc_evt[1][7*(`ARCSYNC_NUM_EVT_PER_VPROC+1)+ 1];







      assign h0host_virt_evt_a = cluster_vproc_evt[2];
      assign h0host_virt_irq_a = cluster_vproc_irq[2];


localparam CORE_NUM  = `ARCSYNC_NUM_CLUSTER * `ARCSYNC_MAX_CORES_PER_CL;
localparam NUM_CORE_C74  = { 8'd`ARCSYNC_NUM_CORE_CL7, 8'd`ARCSYNC_NUM_CORE_CL6
                           , 8'd`ARCSYNC_NUM_CORE_CL5, 8'd`ARCSYNC_NUM_CORE_CL4};
localparam NUM_CORE_C03  = { 8'd`ARCSYNC_NUM_CORE_CL3, 8'd`ARCSYNC_NUM_CORE_CL2
                           , 8'd`ARCSYNC_NUM_CORE_CL1, 8'd`ARCSYNC_NUM_CORE_CL0};

localparam PWR_DWN_TO_RST_A_DLY = 5; // it define how many cycle does slice/slice_grp/L2_grp_rst_a delayed than its corresponding pwr_dwn
localparam PWR_DWN_TO_RST_A_DLY_WIDTH = (PWR_DWN_TO_RST_A_DLY==0) ? 1 : $clog2(PWR_DWN_TO_RST_A_DLY);

  logic [CORE_NUM-1:0]          arcsync_core_exist               ; 
  logic [CORE_NUM-1:0]          arcsync_core_wr_enable           ; 
  logic [CORE_NUM-1:0]          core_arcsync_arc64               ;
  logic [`ARCSYNC_NUM_CLUSTER-1:0] npx_L2_grp_exist;
  logic [`ARCSYNC_NUM_CLUSTER-1:0][3:0] npx_L1_grp_exist;


  logic [`ARCSYNC_NUM_CLUSTER-1:0][40-1:16]       arcsync_core_periph_addr_base;
  logic [`ARCSYNC_NUM_CLUSTER-1:0][40-1:16]       arcsync_core_csm_addr_base;
  logic [`ARCSYNC_NUM_CLUSTER-1:0][3:0]            cl_grp_clk_en;
  logic [`ARCSYNC_NUM_CLUSTER-1:0][4:0]            cl_grp_rst;
  logic [`ARCSYNC_NUM_CLUSTER-1:0]                 cl_enable;
  logic [CORE_NUM-1:0][63:0]    arcsync_core_intvbase            ; 
  logic [CORE_NUM-1:0]          arcsync_core_halt_req            ; 
  logic [CORE_NUM-1:0]          core_arcsync_halt_ack            ; 
  logic [CORE_NUM-1:0]          arcsync_core_run_req             ; 
  logic [CORE_NUM-1:0]          core_arcsync_run_ack             ; 
  logic [CORE_NUM-1:0]          core_arcsync_sys_sleep           ; 
  logic [CORE_NUM-1:0][2:0]     core_arcsync_sys_sleep_mode      ; 
  logic [CORE_NUM-1:0]          core_arcsync_sys_halt            ; 
  logic [CORE_NUM-1:0]          core_arcsync_sys_tf_halt         ; 
  logic [CORE_NUM-1:0]          arcsync_core_rst_req             ; 
  logic [CORE_NUM-1:0]          arcsync_core_clk_en              ; 
  logic [CORE_NUM-1:0][(`ARCSYNC_NUM_IRQ_PER_CORE + 1)-1:0]     arcsync_core_irq                 ; 
  logic [CORE_NUM-1:0][(`ARCSYNC_NUM_EVT_PER_CORE + 1)-1:0]     arcsync_core_event               ; 
  logic [CORE_NUM-1:0][2:0]     core_arcsync_pmode               ; 
  logic [CORE_NUM-1:0][PWR_DWN_TO_RST_A_DLY-1:0]     core_rst_dly;
// for vpx  

//for npx
  logic [CORE_NUM-1:0]          arcsync_core_isolate_n           ; 
  logic [CORE_NUM-1:0]          arcsync_core_isolate             ; 
  logic [CORE_NUM-1:0]          arcsync_core_pd_mem              ; 
  logic [CORE_NUM-1:0]          arcsync_core_pd_logic            ;
  logic [CORE_NUM-1:0]          arcsync_core_pd_logic1           ;
  logic [CORE_NUM-1:0]          arcsync_core_pd_logic2           ;
  logic [CORE_NUM-1:0]          arcsync_core_pwr_down            ;
  logic [CORE_NUM-1:0]          arcsync_core_pu_rst              ;

  logic [`ARCSYNC_NUM_CLUSTER-1:0][3:0] arcsync_grp_isolate_n    ;
  logic [`ARCSYNC_NUM_CLUSTER-1:0][3:0] arcsync_grp_isolate      ;  
  logic [`ARCSYNC_NUM_CLUSTER-1:0][3:0] arcsync_grp_pd_logic     ;
  logic [`ARCSYNC_NUM_CLUSTER-1:0][3:0] arcsync_grp_pd_logic1    ;
  logic [`ARCSYNC_NUM_CLUSTER-1:0][3:0] arcsync_grp_pd_logic2    ;
  logic [`ARCSYNC_NUM_CLUSTER-1:0][3:0] arcsync_grp_pd_mem       ;   
  logic [`ARCSYNC_NUM_CLUSTER-1:0][3:0] arcsync_grp_pu_rst       ;   
  logic [`ARCSYNC_NUM_CLUSTER-1:0][3:0] arcsync_grp_pwr_down     ; 

  logic                         arcsync_core_rst                 ;
  logic                         arcsync_core_rstn                ;

  logic                        internal_axi_arvalid; // read command valid
  logic                        internal_axi_arready; // read command accept
  logic          [16-1:0]  internal_axi_arid;    // read command ID
  logic          [40-1:0]   internal_axi_araddr  ;      // read command
  logic          [3:0]         internal_axi_arcache ;      // read command
  logic          [2:0]         internal_axi_arprot  ;      // read command
  logic          [0:0]         internal_axi_arlock  ;      // read command
  logic          [1:0]         internal_axi_arburst ;      // read command
  logic          [3:0]         internal_axi_arlen   ;      // read command
  logic          [2:0]         internal_axi_arsize  ;      // read command
  logic          [1-1:0]       internal_axi_aruser  ;  // not used
  // read data channel
  logic                        internal_axi_rvalid;  // read data valid
  logic                        internal_axi_rready;  // read data accept
  logic          [16-1:0]  internal_axi_rid;     // read data id
  logic          [64-1:0]   internal_axi_rdata;   // read data
  logic          [1:0]         internal_axi_rresp;   // read response
  logic          [1-1:0]  internal_axi_ruser;   // read data user field
  logic                        internal_axi_rlast;   // read last
  // write command channel
  logic                        internal_axi_awvalid; // write command valid
  logic                        internal_axi_awready; // write command accept
  logic          [16-1:0]  internal_axi_awid;    // write command ID
  logic          [40-1:0]   internal_axi_awaddr  ;      // read command
  logic          [3:0]         internal_axi_awcache ;      // read command
  logic          [2:0]         internal_axi_awprot  ;      // read command
  logic          [0:0]         internal_axi_awlock  ;      // read command
  logic          [1:0]         internal_axi_awburst ;      // read command
  logic          [3:0]         internal_axi_awlen   ;      // read command
  logic          [2:0]         internal_axi_awsize  ;      // read command
  logic          [1-1:0]       internal_axi_awuser  ;  // not used
  // write data channel
  logic                        internal_axi_wvalid;  // write data valid
  logic                        internal_axi_wready;  // write data accept
  logic          [64-1:0]   internal_axi_wdata;   // write data
  logic          [64/8-1:0] internal_axi_wstrb;   // write data strobe
  logic          [1-1:0]  internal_axi_wuser;   // write data user field
  logic                        internal_axi_wlast;   // write data last
  // write response channel
  logic                        internal_axi_bvalid;  // write response valid
  logic                        internal_axi_bready;  // write response accept
  logic          [16-1:0]  internal_axi_bid;     // write response id
  logic          [1-1:0]  internal_axi_buser;   // read data user field
  logic          [1:0]         internal_axi_bresp;   // write response
  logic                        internal_busy_status;

  logic [64-1:0]               internal_axi_wdata_upd;


//============================================================================
//           Calculate offset of map_vm0_vproc
//============================================================================

//============================================================================
//           Calculate vm0_eid_adr
//============================================================================

//============================================================================
//           Each VM's EID, AC registers occupy 4KB address range
//============================================================================

  logic [40-1:0]  internal_axi_araddr_core;
  logic [40-1:0]  internal_axi_awaddr_core;
  //The address width changes with the config settings
  assign  internal_axi_araddr_core =  {{(40-17){1'b0}}, internal_axi_araddr[17-1:0]};
  assign  internal_axi_awaddr_core =  {{(40-17){1'b0}}, internal_axi_awaddr[17-1:0]};

// Indicate whether the core is defined
// if the core is defined, set corresponding bit to 1
always_comb
begin
    arcsync_core_exist = 'b0;
    arcsync_core_wr_enable = 'b0;
    npx_L2_grp_exist = 'b0;
    npx_L1_grp_exist = 'b0;

//      NPU Cluster: cluster 0 
//            l2arc0: core 0    -> CORE_NUM = 0
// npu_slice0 l1arc : core 1~n  -> CORE_NUM = (0+1)~(0+n)
//            l2arc1: core n+1  -> CORE_num = (0+n+1)


      npx_L2_grp_exist[0] = 1'b1;
 
      npx_L1_grp_exist[0][0] = 1'b1;
      npx_L1_grp_exist[0][1] = 1'b1;
      npx_L1_grp_exist[0][2] = 1'b1;
      npx_L1_grp_exist[0][3] = 1'b1;


    for (int i=0; i< 18; i++)
    begin
      arcsync_core_exist[i + (0 * `ARCSYNC_MAX_CORES_PER_CL)] = 1'b1;
      arcsync_core_wr_enable[i + (0 * `ARCSYNC_MAX_CORES_PER_CL)] = 1'b1 & cl_enable[0];
    end


//      VPX Cluster: cluster 1 
//           vpx_c0: core 0  -> CORE_NUM =32
//                ...
//           vpx_c#: core #  -> CORE_NUM =32 + #
    for (int i=0; i< 4; i++)
    begin
      arcsync_core_exist[i + (1 * `ARCSYNC_MAX_CORES_PER_CL)] = 1'b1;
      arcsync_core_wr_enable[i + (1 * `ARCSYNC_MAX_CORES_PER_CL)] = 1'b1 & cl_enable[1];
    end


//      host Cluster: cluster 2 
//           host_c#: core #  -> CORE_NUM =64 + #
    for (int i=0; i< 1; i++)
    begin
      arcsync_core_exist[i + (2 * `ARCSYNC_MAX_CORES_PER_CL)] = 1'b1;
      arcsync_core_wr_enable[i + (2 * `ARCSYNC_MAX_CORES_PER_CL)] = 1'b1 & cl_enable[2];
    end
end

always_ff @(posedge arcsync_clk or posedge arcsync_core_rst) 
begin: cl3_core_rst_dly_PROC
  if (arcsync_core_rst)
  begin
    for (int unsigned i=0; i<CORE_NUM; i++)
    begin
      core_rst_dly[i] <= {PWR_DWN_TO_RST_A_DLY{1'b1}};
    end
  end
  else
  begin
    for (int unsigned i=0; i<CORE_NUM; i++)
    begin
      core_rst_dly[i] <= {core_rst_dly[i][PWR_DWN_TO_RST_A_DLY-2:0],arcsync_core_rst_req[i]};
    end
  end
end: cl3_core_rst_dly_PROC

// Connect arcsync_top to arcsync_core
// Each core has a specific core_index





    logic [PWR_DWN_TO_RST_A_DLY-1:0] nl2_rst_dly;

    always_ff @(posedge arcsync_clk or posedge arcsync_core_rst) 
    begin: cl0_L2_grp_rst_dly_PROC
      if (arcsync_core_rst)
        nl2_rst_dly <= {PWR_DWN_TO_RST_A_DLY{1'b1}};
      else
      begin
        nl2_rst_dly <= {nl2_rst_dly[PWR_DWN_TO_RST_A_DLY-2:0],cl_grp_rst[0][0]};
      end
    end: cl0_L2_grp_rst_dly_PROC

    assign nl2_rst = nl2_rst_dly[PWR_DWN_TO_RST_A_DLY-1] 
                              | arcsync_core_pu_rst[0]
                            ;

      logic [PWR_DWN_TO_RST_A_DLY-1:0]     grp0_rst_a_dly;
      
      always_ff @(posedge arcsync_clk or posedge arcsync_core_rst) 
      begin: cl0_slc1_grp0_rst_dly_PROC
        if (arcsync_core_rst)
          grp0_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1:0] <= {PWR_DWN_TO_RST_A_DLY{1'b1}};
        else
        begin
          grp0_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1:0] <= {grp0_rst_a_dly[PWR_DWN_TO_RST_A_DLY-2:0], cl_grp_rst[0][0+1]};
        end
      end: cl0_slc1_grp0_rst_dly_PROC

      assign grp0_clk_en  = cl_grp_clk_en[0][0];
      assign grp0_rst_a = grp0_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1] 
                                      | arcsync_grp_pu_rst[0][0]
                                      ;
        assign grp0_pwr_dwn   = cl_grp_rst[0][0+1]
                                          | arcsync_grp_pwr_down[0][0]
                                          ;
        assign grp0_isolate_n = arcsync_grp_isolate_n[0][0];  
        assign grp0_isolate   = arcsync_grp_isolate[0][0]; 
        assign grp0_pd_mem    = arcsync_grp_pd_mem[0][0];    
        assign grp0_pd_logic  = arcsync_grp_pd_logic[0][0];
        assign grp0_pd_logic1  = arcsync_grp_pd_logic1[0][0];
        assign grp0_pd_logic2  = arcsync_grp_pd_logic2[0][0];
      logic [PWR_DWN_TO_RST_A_DLY-1:0]     grp1_rst_a_dly;
      
      always_ff @(posedge arcsync_clk or posedge arcsync_core_rst) 
      begin: cl0_slc1_grp1_rst_dly_PROC
        if (arcsync_core_rst)
          grp1_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1:0] <= {PWR_DWN_TO_RST_A_DLY{1'b1}};
        else
        begin
          grp1_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1:0] <= {grp1_rst_a_dly[PWR_DWN_TO_RST_A_DLY-2:0], cl_grp_rst[0][1+1]};
        end
      end: cl0_slc1_grp1_rst_dly_PROC

      assign grp1_clk_en  = cl_grp_clk_en[0][1];
      assign grp1_rst_a = grp1_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1] 
                                      | arcsync_grp_pu_rst[0][1]
                                      ;
        assign grp1_pwr_dwn   = cl_grp_rst[0][1+1]
                                          | arcsync_grp_pwr_down[0][1]
                                          ;
        assign grp1_isolate_n = arcsync_grp_isolate_n[0][1];  
        assign grp1_isolate   = arcsync_grp_isolate[0][1]; 
        assign grp1_pd_mem    = arcsync_grp_pd_mem[0][1];    
        assign grp1_pd_logic  = arcsync_grp_pd_logic[0][1];
        assign grp1_pd_logic1  = arcsync_grp_pd_logic1[0][1];
        assign grp1_pd_logic2  = arcsync_grp_pd_logic2[0][1];
      logic [PWR_DWN_TO_RST_A_DLY-1:0]     grp2_rst_a_dly;
      
      always_ff @(posedge arcsync_clk or posedge arcsync_core_rst) 
      begin: cl0_slc1_grp2_rst_dly_PROC
        if (arcsync_core_rst)
          grp2_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1:0] <= {PWR_DWN_TO_RST_A_DLY{1'b1}};
        else
        begin
          grp2_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1:0] <= {grp2_rst_a_dly[PWR_DWN_TO_RST_A_DLY-2:0], cl_grp_rst[0][2+1]};
        end
      end: cl0_slc1_grp2_rst_dly_PROC

      assign grp2_clk_en  = cl_grp_clk_en[0][2];
      assign grp2_rst_a = grp2_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1] 
                                      | arcsync_grp_pu_rst[0][2]
                                      ;
        assign grp2_pwr_dwn   = cl_grp_rst[0][2+1]
                                          | arcsync_grp_pwr_down[0][2]
                                          ;
        assign grp2_isolate_n = arcsync_grp_isolate_n[0][2];  
        assign grp2_isolate   = arcsync_grp_isolate[0][2]; 
        assign grp2_pd_mem    = arcsync_grp_pd_mem[0][2];    
        assign grp2_pd_logic  = arcsync_grp_pd_logic[0][2];
        assign grp2_pd_logic1  = arcsync_grp_pd_logic1[0][2];
        assign grp2_pd_logic2  = arcsync_grp_pd_logic2[0][2];
      logic [PWR_DWN_TO_RST_A_DLY-1:0]     grp3_rst_a_dly;
      
      always_ff @(posedge arcsync_clk or posedge arcsync_core_rst) 
      begin: cl0_slc1_grp3_rst_dly_PROC
        if (arcsync_core_rst)
          grp3_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1:0] <= {PWR_DWN_TO_RST_A_DLY{1'b1}};
        else
        begin
          grp3_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1:0] <= {grp3_rst_a_dly[PWR_DWN_TO_RST_A_DLY-2:0], cl_grp_rst[0][3+1]};
        end
      end: cl0_slc1_grp3_rst_dly_PROC

      assign grp3_clk_en  = cl_grp_clk_en[0][3];
      assign grp3_rst_a = grp3_rst_a_dly[PWR_DWN_TO_RST_A_DLY-1] 
                                      | arcsync_grp_pu_rst[0][3]
                                      ;
        assign grp3_pwr_dwn   = cl_grp_rst[0][3+1]
                                          | arcsync_grp_pwr_down[0][3]
                                          ;
        assign grp3_isolate_n = arcsync_grp_isolate_n[0][3];  
        assign grp3_isolate   = arcsync_grp_isolate[0][3]; 
        assign grp3_pd_mem    = arcsync_grp_pd_mem[0][3];    
        assign grp3_pd_logic  = arcsync_grp_pd_logic[0][3];
        assign grp3_pd_logic1  = arcsync_grp_pd_logic1[0][3];
        assign grp3_pd_logic2  = arcsync_grp_pd_logic2[0][3];


  
  // NPU_L2

      // NPU Clusters
      // NPU L2

      // l2arc from npu_core
      // Halt
      logic                     nl2arc0_arc_halt_ack_sync;        // from nl2arc0_arc_halt_ack_a,    
      logic                     nl2arc0_ext_arc_halt_req_sync;    // from nl2arc0_ext_arc_halt_req_a,
      // Run                                                       
      logic                     nl2arc0_arc_run_ack_sync;         // from nl2arc0_arc_run_ack_a,     
      logic                     nl2arc0_ext_arc_run_req_sync;     // from nl2arc0_ext_arc_run_req_a, 
      // Reset                                                     
      logic                     nl2arc0_arc_rst_ack_sync;         // from nl2arc0_arc_rst_ack_a,     
      // Status
      logic                     nl2arc0_sys_sleep_sync;           //from nl2arc0_sys_sleep_r,        
      logic   [2:0]             nl2arc0_sys_sleep_mode_sync;      //from nl2arc0_sys_sleep_mode_r    
      logic                     nl2arc0_sys_halt_sync;            //reset value is 1, from nl2arc0_sys_halt_r, 
      logic                     nl2arc0_sys_tf_halt_sync;         //from nl2arc0_sys_tf_halt_r,      

      logic                     nl2arc0_update_sys_sleep_mode_sync_mmio_r;
      reg [2:0]                 nl2arc0_sys_sleep_mode_sync_d1_r;
      reg [2:0]                 nl2arc0_sys_sleep_mode_sync_mmio_r;


        arcsync_cdc_sync #(
           .SYNC_FF_LEVELS(2), .WIDTH(10)
         ) u_nl2arc0_arc_cdc_sync (
           .clk        (arcsync_clk),
           .rst_a      (arcsync_core_rst),
           .din        ({
                         nl2arc0_arc_halt_ack_a,        //9
                         nl2arc0_ext_arc_halt_req_a,    //8
                         nl2arc0_arc_run_ack_a,         //7
                         nl2arc0_ext_arc_run_req_a,     //6
                         nl2arc0_sys_sleep_r,           //5
                         nl2arc0_sys_sleep_mode_r,      //4:2
                         nl2arc0_sys_halt_r,            //1
                         nl2arc0_sys_tf_halt_r          //0
                         }),
           .dout       ({
                         nl2arc0_arc_halt_ack_sync,        //9
                         nl2arc0_ext_arc_halt_req_sync,    //8
                         nl2arc0_arc_run_ack_sync,         //7
                         nl2arc0_ext_arc_run_req_sync,     //6
                         nl2arc0_sys_sleep_sync,           //5
                         nl2arc0_sys_sleep_mode_sync,      //4:2
                         nl2arc0_sys_halt_sync,            //1
                         nl2arc0_sys_tf_halt_sync          //0
                         })
         );

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
          nl2arc0_sys_sleep_mode_sync_d1_r <= 3'h0;
        else
          nl2arc0_sys_sleep_mode_sync_d1_r <= nl2arc0_sys_sleep_mode_sync;

      // spyglass disable_block Ac_conv03
      // sync DFF converge
      assign nl2arc0_update_sys_sleep_mode_sync_mmio_r = (nl2arc0_sys_sleep_mode_sync==nl2arc0_sys_sleep_mode_sync_d1_r) &
                                                               (nl2arc0_sys_sleep_mode_sync_d1_r!=nl2arc0_sys_sleep_mode_sync_mmio_r);
      // spyglass enable_block Ac_conv03

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
          nl2arc0_sys_sleep_mode_sync_mmio_r <= 3'h0;
        else if (nl2arc0_update_sys_sleep_mode_sync_mmio_r)
          nl2arc0_sys_sleep_mode_sync_mmio_r <= nl2arc0_sys_sleep_mode_sync_d1_r;

      logic nl2arc0_ext_arc_halt_req_sync_d1_r;
      logic nl2arc0_ext_arc_halt_req_sync_flag_r;
      logic nl2arc0_arc_halt_ack_sync_d1_r;
      logic set_nl2arc0_ext_arc_halt_req_sync_flag;
      logic clr_nl2arc0_ext_arc_halt_req_sync_flag;

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
        begin
          nl2arc0_ext_arc_halt_req_sync_d1_r <= 1'b0;
          nl2arc0_arc_halt_ack_sync_d1_r <= 1'b0;
        end
        else
        begin
          nl2arc0_ext_arc_halt_req_sync_d1_r <= nl2arc0_ext_arc_halt_req_sync;
          nl2arc0_arc_halt_ack_sync_d1_r <= nl2arc0_arc_halt_ack_sync;
        end

      assign set_nl2arc0_ext_arc_halt_req_sync_flag = nl2arc0_ext_arc_halt_req_sync & !nl2arc0_ext_arc_halt_req_sync_d1_r;
      assign clr_nl2arc0_ext_arc_halt_req_sync_flag = nl2arc0_ext_arc_halt_req_sync_flag_r &
                                                                   !nl2arc0_arc_halt_ack_sync &
                                                                   nl2arc0_arc_halt_ack_sync_d1_r;

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
          nl2arc0_ext_arc_halt_req_sync_flag_r <= 1'b0;
        else if (set_nl2arc0_ext_arc_halt_req_sync_flag)
          nl2arc0_ext_arc_halt_req_sync_flag_r <= 1'b1;
        else if (clr_nl2arc0_ext_arc_halt_req_sync_flag)
      // spyglass disable_block Ac_conv03
      // sync DFF converge
          nl2arc0_ext_arc_halt_req_sync_flag_r <= 1'b0;
      // spyglass enable_block Ac_conv03


      logic nl2arc0_ext_arc_run_req_sync_d1_r;
      logic nl2arc0_ext_arc_run_req_sync_flag_r;
      logic nl2arc0_arc_run_ack_sync_d1_r;
      logic set_nl2arc0_ext_arc_run_req_sync_flag;
      logic clr_nl2arc0_ext_arc_run_req_sync_flag;

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
        begin
          nl2arc0_ext_arc_run_req_sync_d1_r <= 1'b0;
          nl2arc0_arc_run_ack_sync_d1_r <= 1'b0;
        end
        else
        begin
          nl2arc0_ext_arc_run_req_sync_d1_r <= nl2arc0_ext_arc_run_req_sync;
          nl2arc0_arc_run_ack_sync_d1_r <= nl2arc0_arc_run_ack_sync;
        end

      assign set_nl2arc0_ext_arc_run_req_sync_flag = nl2arc0_ext_arc_run_req_sync & !nl2arc0_ext_arc_run_req_sync_d1_r;
      assign clr_nl2arc0_ext_arc_run_req_sync_flag = nl2arc0_ext_arc_run_req_sync_flag_r &
                                                                   !nl2arc0_arc_run_ack_sync &
                                                                   nl2arc0_arc_run_ack_sync_d1_r;

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
          nl2arc0_ext_arc_run_req_sync_flag_r <= 1'b0;
        else if (set_nl2arc0_ext_arc_run_req_sync_flag)
          nl2arc0_ext_arc_run_req_sync_flag_r <= 1'b1;
        else if (clr_nl2arc0_ext_arc_run_req_sync_flag)
      // spyglass disable_block Ac_conv03
      // sync DFF converge
          nl2arc0_ext_arc_run_req_sync_flag_r <= 1'b0;
      // spyglass enable_block Ac_conv03


      assign nl2arc_clusternum   = 0;
      assign nl2arc0_intvbase     = arcsync_core_intvbase[0][31:10];
      assign nl2arc0_arc_halt_req = arcsync_core_halt_req[0] | nl2arc0_ext_arc_halt_req_sync;
      assign nl2arc0_arc_run_req  = arcsync_core_run_req[0] | nl2arc0_ext_arc_run_req_sync;

      assign nl2arc0_rst_a   = core_rst_dly[0][PWR_DWN_TO_RST_A_DLY-1] 
                                          | arcsync_core_pu_rst[0]
                                          ;
      assign nl2arc0_pwr_dwn = arcsync_core_rst_req[0] 
                                          | arcsync_core_pwr_down[0]
                                          ;
      assign nl2arc0_clk_en  = arcsync_core_clk_en[0];

      assign nl2arc0_arc_irq_a[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[0];
      assign nl2arc0_arc_event_a[`ARCSYNC_NUM_EVT_PER_CORE:0]    = arcsync_core_event[0];
      
      assign core_arcsync_halt_ack[0]       = nl2arc0_arc_halt_ack_sync & !nl2arc0_ext_arc_halt_req_sync_flag_r;   
      assign nl2arc0_ext_arc_halt_ack    = nl2arc0_arc_halt_ack_sync & nl2arc0_ext_arc_halt_req_sync_flag_r;
      assign core_arcsync_run_ack[0]        = nl2arc0_arc_run_ack_sync & !nl2arc0_ext_arc_run_req_sync_flag_r;    
      assign nl2arc0_ext_arc_run_ack     = nl2arc0_arc_run_ack_sync & nl2arc0_ext_arc_run_req_sync_flag_r;
      assign core_arcsync_sys_sleep[0]      = nl2arc0_sys_sleep_sync;
      assign core_arcsync_sys_sleep_mode[0] = nl2arc0_sys_sleep_mode_sync_mmio_r;
      assign core_arcsync_sys_halt[0]       = nl2arc0_sys_halt_sync;
      assign core_arcsync_sys_tf_halt[0]    = nl2arc0_sys_tf_halt_sync;
      assign nl2arc_pwr_dwn   = cl_grp_rst[0][0]
                                       | arcsync_core_pwr_down[0]
                                       ;
      assign core_arcsync_pmode[0]          = {2'h0, arcsync_core_pwr_down[0 * `ARCSYNC_MAX_CORES_PER_CL]};
      assign nl2arc_isolate_n =   arcsync_core_isolate_n[0]; 
      assign nl2arc_isolate   =   arcsync_core_isolate[0]; 
      assign nl2arc_pd_mem    =   arcsync_core_pd_mem[0]; 
      assign nl2arc_pd_logic  =   arcsync_core_pd_logic[0];
      assign nl2arc_pd_logic1  =   arcsync_core_pd_logic1[0];
      assign nl2arc_pd_logic2  =   arcsync_core_pd_logic2[0];


      // NPU Clusters
      // NPU L2

      // l2arc from npu_core
      // Halt
      logic                     nl2arc1_arc_halt_ack_sync;        // from nl2arc1_arc_halt_ack_a,    
      logic                     nl2arc1_ext_arc_halt_req_sync;    // from nl2arc1_ext_arc_halt_req_a,
      // Run                                                       
      logic                     nl2arc1_arc_run_ack_sync;         // from nl2arc1_arc_run_ack_a,     
      logic                     nl2arc1_ext_arc_run_req_sync;     // from nl2arc1_ext_arc_run_req_a, 
      // Reset                                                     
      logic                     nl2arc1_arc_rst_ack_sync;         // from nl2arc1_arc_rst_ack_a,     
      // Status
      logic                     nl2arc1_sys_sleep_sync;           //from nl2arc1_sys_sleep_r,        
      logic   [2:0]             nl2arc1_sys_sleep_mode_sync;      //from nl2arc1_sys_sleep_mode_r    
      logic                     nl2arc1_sys_halt_sync;            //reset value is 1, from nl2arc1_sys_halt_r, 
      logic                     nl2arc1_sys_tf_halt_sync;         //from nl2arc1_sys_tf_halt_r,      

      logic                     nl2arc1_update_sys_sleep_mode_sync_mmio_r;
      reg [2:0]                 nl2arc1_sys_sleep_mode_sync_d1_r;
      reg [2:0]                 nl2arc1_sys_sleep_mode_sync_mmio_r;


        arcsync_cdc_sync #(
           .SYNC_FF_LEVELS(2), .WIDTH(10)
         ) u_nl2arc1_arc_cdc_sync (
           .clk        (arcsync_clk),
           .rst_a      (arcsync_core_rst),
           .din        ({
                         nl2arc1_arc_halt_ack_a,        //9
                         nl2arc1_ext_arc_halt_req_a,    //8
                         nl2arc1_arc_run_ack_a,         //7
                         nl2arc1_ext_arc_run_req_a,     //6
                         nl2arc1_sys_sleep_r,           //5
                         nl2arc1_sys_sleep_mode_r,      //4:2
                         nl2arc1_sys_halt_r,            //1
                         nl2arc1_sys_tf_halt_r          //0
                         }),
           .dout       ({
                         nl2arc1_arc_halt_ack_sync,        //10
                         nl2arc1_ext_arc_halt_req_sync,    //9
                         nl2arc1_arc_run_ack_sync,         //8
                         nl2arc1_ext_arc_run_req_sync,     //7
                         nl2arc1_sys_sleep_sync,           //5
                         nl2arc1_sys_sleep_mode_sync,      //4:2
                         nl2arc1_sys_halt_sync,            //1
                         nl2arc1_sys_tf_halt_sync          //0
                         })
         );

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
          nl2arc1_sys_sleep_mode_sync_d1_r <= 3'h0;
        else
          nl2arc1_sys_sleep_mode_sync_d1_r <= nl2arc1_sys_sleep_mode_sync;

      // spyglass disable_block Ac_conv03
      // sync DFF converge
      assign nl2arc1_update_sys_sleep_mode_sync_mmio_r = (nl2arc1_sys_sleep_mode_sync==nl2arc1_sys_sleep_mode_sync_d1_r) &
                                                               (nl2arc1_sys_sleep_mode_sync_d1_r!=nl2arc1_sys_sleep_mode_sync_mmio_r);
      // spyglass enable_block Ac_conv03

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
          nl2arc1_sys_sleep_mode_sync_mmio_r <= 3'h0;
        else if (nl2arc1_update_sys_sleep_mode_sync_mmio_r)
          nl2arc1_sys_sleep_mode_sync_mmio_r <= nl2arc1_sys_sleep_mode_sync_d1_r;

      logic nl2arc1_ext_arc_halt_req_sync_d1_r;
      logic nl2arc1_ext_arc_halt_req_sync_flag_r;
      logic nl2arc1_arc_halt_ack_sync_d1_r;
      logic set_nl2arc1_ext_arc_halt_req_sync_flag;
      logic clr_nl2arc1_ext_arc_halt_req_sync_flag;

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
        begin
          nl2arc1_ext_arc_halt_req_sync_d1_r <= 1'b0;
          nl2arc1_arc_halt_ack_sync_d1_r <= 1'b0;
        end
        else
        begin
          nl2arc1_ext_arc_halt_req_sync_d1_r <= nl2arc1_ext_arc_halt_req_sync;
          nl2arc1_arc_halt_ack_sync_d1_r <= nl2arc1_arc_halt_ack_sync;
        end

      assign set_nl2arc1_ext_arc_halt_req_sync_flag = nl2arc1_ext_arc_halt_req_sync & !nl2arc1_ext_arc_halt_req_sync_d1_r;
      assign clr_nl2arc1_ext_arc_halt_req_sync_flag = nl2arc1_ext_arc_halt_req_sync_flag_r &
                                                                   !nl2arc1_arc_halt_ack_sync &
                                                                   nl2arc1_arc_halt_ack_sync_d1_r;

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
          nl2arc1_ext_arc_halt_req_sync_flag_r <= 1'b0;
        else if (set_nl2arc1_ext_arc_halt_req_sync_flag)
          nl2arc1_ext_arc_halt_req_sync_flag_r <= 1'b1;
        else if (clr_nl2arc1_ext_arc_halt_req_sync_flag)
      // spyglass disable_block Ac_conv03
      // sync DFF converge
          nl2arc1_ext_arc_halt_req_sync_flag_r <= 1'b0;
      // spyglass enable_block Ac_conv03


      logic nl2arc1_ext_arc_run_req_sync_d1_r;
      logic nl2arc1_ext_arc_run_req_sync_flag_r;
      logic nl2arc1_arc_run_ack_sync_d1_r;
      logic set_nl2arc1_ext_arc_run_req_sync_flag;
      logic clr_nl2arc1_ext_arc_run_req_sync_flag;

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
        begin
          nl2arc1_ext_arc_run_req_sync_d1_r <= 1'b0;
          nl2arc1_arc_run_ack_sync_d1_r <= 1'b0;
        end
        else
        begin
          nl2arc1_ext_arc_run_req_sync_d1_r <= nl2arc1_ext_arc_run_req_sync;
          nl2arc1_arc_run_ack_sync_d1_r <= nl2arc1_arc_run_ack_sync;
        end

      assign set_nl2arc1_ext_arc_run_req_sync_flag = nl2arc1_ext_arc_run_req_sync & !nl2arc1_ext_arc_run_req_sync_d1_r;
      assign clr_nl2arc1_ext_arc_run_req_sync_flag = nl2arc1_ext_arc_run_req_sync_flag_r &
                                                                   !nl2arc1_arc_run_ack_sync &
                                                                   nl2arc1_arc_run_ack_sync_d1_r;

      always @(posedge arcsync_clk or posedge arcsync_core_rst)
        if (arcsync_core_rst)
          nl2arc1_ext_arc_run_req_sync_flag_r <= 1'b0;
        else if (set_nl2arc1_ext_arc_run_req_sync_flag)
          nl2arc1_ext_arc_run_req_sync_flag_r <= 1'b1;
        else if (clr_nl2arc1_ext_arc_run_req_sync_flag)
      // spyglass disable_block Ac_conv03
      // sync DFF converge
          nl2arc1_ext_arc_run_req_sync_flag_r <= 1'b0;
      // spyglass enable_block Ac_conv03


      assign nl2arc1_intvbase     = arcsync_core_intvbase[17][31:10];
      assign nl2arc1_arc_halt_req = arcsync_core_halt_req[17] | nl2arc1_ext_arc_halt_req_sync;
      assign nl2arc1_arc_run_req  = arcsync_core_run_req[17] | nl2arc1_ext_arc_run_req_sync;

      assign nl2arc1_rst_a   = core_rst_dly[17][PWR_DWN_TO_RST_A_DLY-1] 
                                          | arcsync_core_pu_rst[0]
                                          ;
      assign nl2arc1_pwr_dwn = arcsync_core_rst_req[17] 
                                          | arcsync_core_pwr_down[0]
                                          ;
      assign nl2arc1_clk_en  = arcsync_core_clk_en[17];

      assign nl2arc1_arc_irq_a[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[17];
      assign nl2arc1_arc_event_a[`ARCSYNC_NUM_EVT_PER_CORE:0]    = arcsync_core_event[17];
      
      assign core_arcsync_halt_ack[17]       = nl2arc1_arc_halt_ack_sync & !nl2arc1_ext_arc_halt_req_sync_flag_r;   
      assign nl2arc1_ext_arc_halt_ack    = nl2arc1_arc_halt_ack_sync & nl2arc1_ext_arc_halt_req_sync_flag_r;
      assign core_arcsync_run_ack[17]        = nl2arc1_arc_run_ack_sync & !nl2arc1_ext_arc_run_req_sync_flag_r;    
      assign nl2arc1_ext_arc_run_ack     = nl2arc1_arc_run_ack_sync & nl2arc1_ext_arc_run_req_sync_flag_r;
      assign core_arcsync_sys_sleep[17]      = nl2arc1_sys_sleep_sync;
      assign core_arcsync_sys_sleep_mode[17] = nl2arc1_sys_sleep_mode_sync_mmio_r;
      assign core_arcsync_sys_halt[17]       = nl2arc1_sys_halt_sync;
      assign core_arcsync_sys_tf_halt[17]    = nl2arc1_sys_tf_halt_sync;
      assign core_arcsync_pmode[17]          = {2'h0, arcsync_core_pwr_down[0 * `ARCSYNC_MAX_CORES_PER_CL]};


  // NPU_L1
  // Halt
  logic                   sl0nl1arc_arc_halt_ack_sync;     // from sl0nl1arc_arc_halt_ack_a
  logic                   sl0nl1arc_ext_arc_halt_req_sync; // from sl0nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl0nl1arc_arc_run_ack_sync;      // from sl0nl1arc_arc_run_ack_a
  logic                   sl0nl1arc_ext_arc_run_req_sync;  // from sl0nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl0nl1arc_arc_rst_ack_sync;      // from sl0nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl0nl1arc_sys_sleep_sync;        // from sl0nl1arc_sys_sleep_r
  logic   [2:0]           sl0nl1arc_sys_sleep_mode_sync;   // from sl0nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl0nl1arc_sys_halt_sync;         // from sl0nl1arc_sys_halt_r
  logic                   sl0nl1arc_sys_tf_halt_sync;      // from sl0nl1arc_sys_tf_halt_r

  logic                   sl0nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl0nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl0nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl0nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl0nl1arc_arc_halt_ack_a,        //9
                  sl0nl1arc_ext_arc_halt_req_a,    //8
                  sl0nl1arc_arc_run_ack_a,         //7
                  sl0nl1arc_ext_arc_run_req_a,     //6
                  sl0nl1arc_sys_sleep_r,           //5
                  sl0nl1arc_sys_sleep_mode_r,      //4:2
                  sl0nl1arc_sys_halt_r,            //1
                  sl0nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl0nl1arc_arc_halt_ack_sync,        //9
                  sl0nl1arc_ext_arc_halt_req_sync,    //8
                  sl0nl1arc_arc_run_ack_sync,         //7
                  sl0nl1arc_ext_arc_run_req_sync,     //6
                  sl0nl1arc_sys_sleep_sync,           //5
                  sl0nl1arc_sys_sleep_mode_sync,      //4:2
                  sl0nl1arc_sys_halt_sync,            //1
                  sl0nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl0nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl0nl1arc_sys_sleep_mode_sync_d1_r <= sl0nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl0nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl0nl1arc_sys_sleep_mode_sync==sl0nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl0nl1arc_sys_sleep_mode_sync_d1_r!=sl0nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl0nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl0nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl0nl1arc_sys_sleep_mode_sync_mmio_r <= sl0nl1arc_sys_sleep_mode_sync_d1_r;


logic sl0nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl0nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl0nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl0nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl0nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl0nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl0nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl0nl1arc_ext_arc_halt_req_sync_d1_r <= sl0nl1arc_ext_arc_halt_req_sync;
      sl0nl1arc_arc_halt_ack_sync_d1_r <= sl0nl1arc_arc_halt_ack_sync;
    end

  assign set_sl0nl1arc_ext_arc_halt_req_sync_flag = sl0nl1arc_ext_arc_halt_req_sync & !sl0nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl0nl1arc_ext_arc_halt_req_sync_flag = sl0nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl0nl1arc_arc_halt_ack_sync &
                                                               sl0nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl0nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl0nl1arc_ext_arc_halt_req_sync_flag)
      sl0nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl0nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl0nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl0nl1arc_ext_arc_run_req_sync_d1_r;
logic sl0nl1arc_ext_arc_run_req_sync_flag_r;
logic sl0nl1arc_arc_run_ack_sync_d1_r;
logic set_sl0nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl0nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl0nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl0nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl0nl1arc_ext_arc_run_req_sync_d1_r <= sl0nl1arc_ext_arc_run_req_sync;
      sl0nl1arc_arc_run_ack_sync_d1_r <= sl0nl1arc_arc_run_ack_sync;
    end

  assign set_sl0nl1arc_ext_arc_run_req_sync_flag = sl0nl1arc_ext_arc_run_req_sync & !sl0nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl0nl1arc_ext_arc_run_req_sync_flag = sl0nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl0nl1arc_arc_run_ack_sync &
                                                               sl0nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl0nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl0nl1arc_ext_arc_run_req_sync_flag)
      sl0nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl0nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl0nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl0nl1arc_intvbase     = arcsync_core_intvbase[1][31:10];

  assign sl0_rst_a                = core_rst_dly[1][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[1]
                                                ;

  assign sl0_clk_en               = arcsync_core_clk_en[1];

  assign sl0nl1arc_arc_halt_req = arcsync_core_halt_req[1] | sl0nl1arc_ext_arc_halt_req_sync;
  assign sl0nl1arc_arc_run_req  = arcsync_core_run_req[1] | sl0nl1arc_ext_arc_run_req_sync;

  assign sl0nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[1];  
  
  assign core_arcsync_halt_ack[1]         = sl0nl1arc_arc_halt_ack_sync & !sl0nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl0nl1arc_ext_arc_halt_ack = sl0nl1arc_arc_halt_ack_sync & sl0nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[1]          = sl0nl1arc_arc_run_ack_sync & !sl0nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl0nl1arc_ext_arc_run_ack  = sl0nl1arc_arc_run_ack_sync & sl0nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[1]        = sl0nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[1]   = sl0nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[1]         = sl0nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[1]      = sl0nl1arc_sys_tf_halt_sync;    

  assign sl0nl1arc_pwr_dwn      = arcsync_core_rst_req[1]
                                             | arcsync_core_pwr_down[1]
                                             ;
  assign core_arcsync_pmode[1]         = {2'h0, arcsync_core_pwr_down[1]};
  assign sl0nl1arc_isolate_n =   arcsync_core_isolate_n[1]; 
  assign sl0nl1arc_isolate   =   arcsync_core_isolate[1]; 
  assign sl0nl1arc_pd_mem    =   arcsync_core_pd_mem[1]; 
  assign sl0nl1arc_pd_logic  =   arcsync_core_pd_logic[1];
  assign sl0nl1arc_pd_logic1  =   arcsync_core_pd_logic1[1];
  assign sl0nl1arc_pd_logic2  =   arcsync_core_pd_logic2[1];

  // Halt
  logic                   sl1nl1arc_arc_halt_ack_sync;     // from sl1nl1arc_arc_halt_ack_a
  logic                   sl1nl1arc_ext_arc_halt_req_sync; // from sl1nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl1nl1arc_arc_run_ack_sync;      // from sl1nl1arc_arc_run_ack_a
  logic                   sl1nl1arc_ext_arc_run_req_sync;  // from sl1nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl1nl1arc_arc_rst_ack_sync;      // from sl1nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl1nl1arc_sys_sleep_sync;        // from sl1nl1arc_sys_sleep_r
  logic   [2:0]           sl1nl1arc_sys_sleep_mode_sync;   // from sl1nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl1nl1arc_sys_halt_sync;         // from sl1nl1arc_sys_halt_r
  logic                   sl1nl1arc_sys_tf_halt_sync;      // from sl1nl1arc_sys_tf_halt_r

  logic                   sl1nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl1nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl1nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl1nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl1nl1arc_arc_halt_ack_a,        //9
                  sl1nl1arc_ext_arc_halt_req_a,    //8
                  sl1nl1arc_arc_run_ack_a,         //7
                  sl1nl1arc_ext_arc_run_req_a,     //6
                  sl1nl1arc_sys_sleep_r,           //5
                  sl1nl1arc_sys_sleep_mode_r,      //4:2
                  sl1nl1arc_sys_halt_r,            //1
                  sl1nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl1nl1arc_arc_halt_ack_sync,        //9
                  sl1nl1arc_ext_arc_halt_req_sync,    //8
                  sl1nl1arc_arc_run_ack_sync,         //7
                  sl1nl1arc_ext_arc_run_req_sync,     //6
                  sl1nl1arc_sys_sleep_sync,           //5
                  sl1nl1arc_sys_sleep_mode_sync,      //4:2
                  sl1nl1arc_sys_halt_sync,            //1
                  sl1nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl1nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl1nl1arc_sys_sleep_mode_sync_d1_r <= sl1nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl1nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl1nl1arc_sys_sleep_mode_sync==sl1nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl1nl1arc_sys_sleep_mode_sync_d1_r!=sl1nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl1nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl1nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl1nl1arc_sys_sleep_mode_sync_mmio_r <= sl1nl1arc_sys_sleep_mode_sync_d1_r;


logic sl1nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl1nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl1nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl1nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl1nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl1nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl1nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl1nl1arc_ext_arc_halt_req_sync_d1_r <= sl1nl1arc_ext_arc_halt_req_sync;
      sl1nl1arc_arc_halt_ack_sync_d1_r <= sl1nl1arc_arc_halt_ack_sync;
    end

  assign set_sl1nl1arc_ext_arc_halt_req_sync_flag = sl1nl1arc_ext_arc_halt_req_sync & !sl1nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl1nl1arc_ext_arc_halt_req_sync_flag = sl1nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl1nl1arc_arc_halt_ack_sync &
                                                               sl1nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl1nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl1nl1arc_ext_arc_halt_req_sync_flag)
      sl1nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl1nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl1nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl1nl1arc_ext_arc_run_req_sync_d1_r;
logic sl1nl1arc_ext_arc_run_req_sync_flag_r;
logic sl1nl1arc_arc_run_ack_sync_d1_r;
logic set_sl1nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl1nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl1nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl1nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl1nl1arc_ext_arc_run_req_sync_d1_r <= sl1nl1arc_ext_arc_run_req_sync;
      sl1nl1arc_arc_run_ack_sync_d1_r <= sl1nl1arc_arc_run_ack_sync;
    end

  assign set_sl1nl1arc_ext_arc_run_req_sync_flag = sl1nl1arc_ext_arc_run_req_sync & !sl1nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl1nl1arc_ext_arc_run_req_sync_flag = sl1nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl1nl1arc_arc_run_ack_sync &
                                                               sl1nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl1nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl1nl1arc_ext_arc_run_req_sync_flag)
      sl1nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl1nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl1nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl1nl1arc_intvbase     = arcsync_core_intvbase[2][31:10];

  assign sl1_rst_a                = core_rst_dly[2][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[2]
                                                ;

  assign sl1_clk_en               = arcsync_core_clk_en[2];

  assign sl1nl1arc_arc_halt_req = arcsync_core_halt_req[2] | sl1nl1arc_ext_arc_halt_req_sync;
  assign sl1nl1arc_arc_run_req  = arcsync_core_run_req[2] | sl1nl1arc_ext_arc_run_req_sync;

  assign sl1nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[2];  
  
  assign core_arcsync_halt_ack[2]         = sl1nl1arc_arc_halt_ack_sync & !sl1nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl1nl1arc_ext_arc_halt_ack = sl1nl1arc_arc_halt_ack_sync & sl1nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[2]          = sl1nl1arc_arc_run_ack_sync & !sl1nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl1nl1arc_ext_arc_run_ack  = sl1nl1arc_arc_run_ack_sync & sl1nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[2]        = sl1nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[2]   = sl1nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[2]         = sl1nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[2]      = sl1nl1arc_sys_tf_halt_sync;    

  assign sl1nl1arc_pwr_dwn      = arcsync_core_rst_req[2]
                                             | arcsync_core_pwr_down[2]
                                             ;
  assign core_arcsync_pmode[2]         = {2'h0, arcsync_core_pwr_down[2]};
  assign sl1nl1arc_isolate_n =   arcsync_core_isolate_n[2]; 
  assign sl1nl1arc_isolate   =   arcsync_core_isolate[2]; 
  assign sl1nl1arc_pd_mem    =   arcsync_core_pd_mem[2]; 
  assign sl1nl1arc_pd_logic  =   arcsync_core_pd_logic[2];
  assign sl1nl1arc_pd_logic1  =   arcsync_core_pd_logic1[2];
  assign sl1nl1arc_pd_logic2  =   arcsync_core_pd_logic2[2];

  // Halt
  logic                   sl2nl1arc_arc_halt_ack_sync;     // from sl2nl1arc_arc_halt_ack_a
  logic                   sl2nl1arc_ext_arc_halt_req_sync; // from sl2nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl2nl1arc_arc_run_ack_sync;      // from sl2nl1arc_arc_run_ack_a
  logic                   sl2nl1arc_ext_arc_run_req_sync;  // from sl2nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl2nl1arc_arc_rst_ack_sync;      // from sl2nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl2nl1arc_sys_sleep_sync;        // from sl2nl1arc_sys_sleep_r
  logic   [2:0]           sl2nl1arc_sys_sleep_mode_sync;   // from sl2nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl2nl1arc_sys_halt_sync;         // from sl2nl1arc_sys_halt_r
  logic                   sl2nl1arc_sys_tf_halt_sync;      // from sl2nl1arc_sys_tf_halt_r

  logic                   sl2nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl2nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl2nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl2nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl2nl1arc_arc_halt_ack_a,        //9
                  sl2nl1arc_ext_arc_halt_req_a,    //8
                  sl2nl1arc_arc_run_ack_a,         //7
                  sl2nl1arc_ext_arc_run_req_a,     //6
                  sl2nl1arc_sys_sleep_r,           //5
                  sl2nl1arc_sys_sleep_mode_r,      //4:2
                  sl2nl1arc_sys_halt_r,            //1
                  sl2nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl2nl1arc_arc_halt_ack_sync,        //9
                  sl2nl1arc_ext_arc_halt_req_sync,    //8
                  sl2nl1arc_arc_run_ack_sync,         //7
                  sl2nl1arc_ext_arc_run_req_sync,     //6
                  sl2nl1arc_sys_sleep_sync,           //5
                  sl2nl1arc_sys_sleep_mode_sync,      //4:2
                  sl2nl1arc_sys_halt_sync,            //1
                  sl2nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl2nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl2nl1arc_sys_sleep_mode_sync_d1_r <= sl2nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl2nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl2nl1arc_sys_sleep_mode_sync==sl2nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl2nl1arc_sys_sleep_mode_sync_d1_r!=sl2nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl2nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl2nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl2nl1arc_sys_sleep_mode_sync_mmio_r <= sl2nl1arc_sys_sleep_mode_sync_d1_r;


logic sl2nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl2nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl2nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl2nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl2nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl2nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl2nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl2nl1arc_ext_arc_halt_req_sync_d1_r <= sl2nl1arc_ext_arc_halt_req_sync;
      sl2nl1arc_arc_halt_ack_sync_d1_r <= sl2nl1arc_arc_halt_ack_sync;
    end

  assign set_sl2nl1arc_ext_arc_halt_req_sync_flag = sl2nl1arc_ext_arc_halt_req_sync & !sl2nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl2nl1arc_ext_arc_halt_req_sync_flag = sl2nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl2nl1arc_arc_halt_ack_sync &
                                                               sl2nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl2nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl2nl1arc_ext_arc_halt_req_sync_flag)
      sl2nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl2nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl2nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl2nl1arc_ext_arc_run_req_sync_d1_r;
logic sl2nl1arc_ext_arc_run_req_sync_flag_r;
logic sl2nl1arc_arc_run_ack_sync_d1_r;
logic set_sl2nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl2nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl2nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl2nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl2nl1arc_ext_arc_run_req_sync_d1_r <= sl2nl1arc_ext_arc_run_req_sync;
      sl2nl1arc_arc_run_ack_sync_d1_r <= sl2nl1arc_arc_run_ack_sync;
    end

  assign set_sl2nl1arc_ext_arc_run_req_sync_flag = sl2nl1arc_ext_arc_run_req_sync & !sl2nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl2nl1arc_ext_arc_run_req_sync_flag = sl2nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl2nl1arc_arc_run_ack_sync &
                                                               sl2nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl2nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl2nl1arc_ext_arc_run_req_sync_flag)
      sl2nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl2nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl2nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl2nl1arc_intvbase     = arcsync_core_intvbase[3][31:10];

  assign sl2_rst_a                = core_rst_dly[3][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[3]
                                                ;

  assign sl2_clk_en               = arcsync_core_clk_en[3];

  assign sl2nl1arc_arc_halt_req = arcsync_core_halt_req[3] | sl2nl1arc_ext_arc_halt_req_sync;
  assign sl2nl1arc_arc_run_req  = arcsync_core_run_req[3] | sl2nl1arc_ext_arc_run_req_sync;

  assign sl2nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[3];  
  
  assign core_arcsync_halt_ack[3]         = sl2nl1arc_arc_halt_ack_sync & !sl2nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl2nl1arc_ext_arc_halt_ack = sl2nl1arc_arc_halt_ack_sync & sl2nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[3]          = sl2nl1arc_arc_run_ack_sync & !sl2nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl2nl1arc_ext_arc_run_ack  = sl2nl1arc_arc_run_ack_sync & sl2nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[3]        = sl2nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[3]   = sl2nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[3]         = sl2nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[3]      = sl2nl1arc_sys_tf_halt_sync;    

  assign sl2nl1arc_pwr_dwn      = arcsync_core_rst_req[3]
                                             | arcsync_core_pwr_down[3]
                                             ;
  assign core_arcsync_pmode[3]         = {2'h0, arcsync_core_pwr_down[3]};
  assign sl2nl1arc_isolate_n =   arcsync_core_isolate_n[3]; 
  assign sl2nl1arc_isolate   =   arcsync_core_isolate[3]; 
  assign sl2nl1arc_pd_mem    =   arcsync_core_pd_mem[3]; 
  assign sl2nl1arc_pd_logic  =   arcsync_core_pd_logic[3];
  assign sl2nl1arc_pd_logic1  =   arcsync_core_pd_logic1[3];
  assign sl2nl1arc_pd_logic2  =   arcsync_core_pd_logic2[3];

  // Halt
  logic                   sl3nl1arc_arc_halt_ack_sync;     // from sl3nl1arc_arc_halt_ack_a
  logic                   sl3nl1arc_ext_arc_halt_req_sync; // from sl3nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl3nl1arc_arc_run_ack_sync;      // from sl3nl1arc_arc_run_ack_a
  logic                   sl3nl1arc_ext_arc_run_req_sync;  // from sl3nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl3nl1arc_arc_rst_ack_sync;      // from sl3nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl3nl1arc_sys_sleep_sync;        // from sl3nl1arc_sys_sleep_r
  logic   [2:0]           sl3nl1arc_sys_sleep_mode_sync;   // from sl3nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl3nl1arc_sys_halt_sync;         // from sl3nl1arc_sys_halt_r
  logic                   sl3nl1arc_sys_tf_halt_sync;      // from sl3nl1arc_sys_tf_halt_r

  logic                   sl3nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl3nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl3nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl3nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl3nl1arc_arc_halt_ack_a,        //9
                  sl3nl1arc_ext_arc_halt_req_a,    //8
                  sl3nl1arc_arc_run_ack_a,         //7
                  sl3nl1arc_ext_arc_run_req_a,     //6
                  sl3nl1arc_sys_sleep_r,           //5
                  sl3nl1arc_sys_sleep_mode_r,      //4:2
                  sl3nl1arc_sys_halt_r,            //1
                  sl3nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl3nl1arc_arc_halt_ack_sync,        //9
                  sl3nl1arc_ext_arc_halt_req_sync,    //8
                  sl3nl1arc_arc_run_ack_sync,         //7
                  sl3nl1arc_ext_arc_run_req_sync,     //6
                  sl3nl1arc_sys_sleep_sync,           //5
                  sl3nl1arc_sys_sleep_mode_sync,      //4:2
                  sl3nl1arc_sys_halt_sync,            //1
                  sl3nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl3nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl3nl1arc_sys_sleep_mode_sync_d1_r <= sl3nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl3nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl3nl1arc_sys_sleep_mode_sync==sl3nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl3nl1arc_sys_sleep_mode_sync_d1_r!=sl3nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl3nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl3nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl3nl1arc_sys_sleep_mode_sync_mmio_r <= sl3nl1arc_sys_sleep_mode_sync_d1_r;


logic sl3nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl3nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl3nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl3nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl3nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl3nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl3nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl3nl1arc_ext_arc_halt_req_sync_d1_r <= sl3nl1arc_ext_arc_halt_req_sync;
      sl3nl1arc_arc_halt_ack_sync_d1_r <= sl3nl1arc_arc_halt_ack_sync;
    end

  assign set_sl3nl1arc_ext_arc_halt_req_sync_flag = sl3nl1arc_ext_arc_halt_req_sync & !sl3nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl3nl1arc_ext_arc_halt_req_sync_flag = sl3nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl3nl1arc_arc_halt_ack_sync &
                                                               sl3nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl3nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl3nl1arc_ext_arc_halt_req_sync_flag)
      sl3nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl3nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl3nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl3nl1arc_ext_arc_run_req_sync_d1_r;
logic sl3nl1arc_ext_arc_run_req_sync_flag_r;
logic sl3nl1arc_arc_run_ack_sync_d1_r;
logic set_sl3nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl3nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl3nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl3nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl3nl1arc_ext_arc_run_req_sync_d1_r <= sl3nl1arc_ext_arc_run_req_sync;
      sl3nl1arc_arc_run_ack_sync_d1_r <= sl3nl1arc_arc_run_ack_sync;
    end

  assign set_sl3nl1arc_ext_arc_run_req_sync_flag = sl3nl1arc_ext_arc_run_req_sync & !sl3nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl3nl1arc_ext_arc_run_req_sync_flag = sl3nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl3nl1arc_arc_run_ack_sync &
                                                               sl3nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl3nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl3nl1arc_ext_arc_run_req_sync_flag)
      sl3nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl3nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl3nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl3nl1arc_intvbase     = arcsync_core_intvbase[4][31:10];

  assign sl3_rst_a                = core_rst_dly[4][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[4]
                                                ;

  assign sl3_clk_en               = arcsync_core_clk_en[4];

  assign sl3nl1arc_arc_halt_req = arcsync_core_halt_req[4] | sl3nl1arc_ext_arc_halt_req_sync;
  assign sl3nl1arc_arc_run_req  = arcsync_core_run_req[4] | sl3nl1arc_ext_arc_run_req_sync;

  assign sl3nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[4];  
  
  assign core_arcsync_halt_ack[4]         = sl3nl1arc_arc_halt_ack_sync & !sl3nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl3nl1arc_ext_arc_halt_ack = sl3nl1arc_arc_halt_ack_sync & sl3nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[4]          = sl3nl1arc_arc_run_ack_sync & !sl3nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl3nl1arc_ext_arc_run_ack  = sl3nl1arc_arc_run_ack_sync & sl3nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[4]        = sl3nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[4]   = sl3nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[4]         = sl3nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[4]      = sl3nl1arc_sys_tf_halt_sync;    

  assign sl3nl1arc_pwr_dwn      = arcsync_core_rst_req[4]
                                             | arcsync_core_pwr_down[4]
                                             ;
  assign core_arcsync_pmode[4]         = {2'h0, arcsync_core_pwr_down[4]};
  assign sl3nl1arc_isolate_n =   arcsync_core_isolate_n[4]; 
  assign sl3nl1arc_isolate   =   arcsync_core_isolate[4]; 
  assign sl3nl1arc_pd_mem    =   arcsync_core_pd_mem[4]; 
  assign sl3nl1arc_pd_logic  =   arcsync_core_pd_logic[4];
  assign sl3nl1arc_pd_logic1  =   arcsync_core_pd_logic1[4];
  assign sl3nl1arc_pd_logic2  =   arcsync_core_pd_logic2[4];

  // Halt
  logic                   sl4nl1arc_arc_halt_ack_sync;     // from sl4nl1arc_arc_halt_ack_a
  logic                   sl4nl1arc_ext_arc_halt_req_sync; // from sl4nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl4nl1arc_arc_run_ack_sync;      // from sl4nl1arc_arc_run_ack_a
  logic                   sl4nl1arc_ext_arc_run_req_sync;  // from sl4nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl4nl1arc_arc_rst_ack_sync;      // from sl4nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl4nl1arc_sys_sleep_sync;        // from sl4nl1arc_sys_sleep_r
  logic   [2:0]           sl4nl1arc_sys_sleep_mode_sync;   // from sl4nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl4nl1arc_sys_halt_sync;         // from sl4nl1arc_sys_halt_r
  logic                   sl4nl1arc_sys_tf_halt_sync;      // from sl4nl1arc_sys_tf_halt_r

  logic                   sl4nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl4nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl4nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl4nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl4nl1arc_arc_halt_ack_a,        //9
                  sl4nl1arc_ext_arc_halt_req_a,    //8
                  sl4nl1arc_arc_run_ack_a,         //7
                  sl4nl1arc_ext_arc_run_req_a,     //6
                  sl4nl1arc_sys_sleep_r,           //5
                  sl4nl1arc_sys_sleep_mode_r,      //4:2
                  sl4nl1arc_sys_halt_r,            //1
                  sl4nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl4nl1arc_arc_halt_ack_sync,        //9
                  sl4nl1arc_ext_arc_halt_req_sync,    //8
                  sl4nl1arc_arc_run_ack_sync,         //7
                  sl4nl1arc_ext_arc_run_req_sync,     //6
                  sl4nl1arc_sys_sleep_sync,           //5
                  sl4nl1arc_sys_sleep_mode_sync,      //4:2
                  sl4nl1arc_sys_halt_sync,            //1
                  sl4nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl4nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl4nl1arc_sys_sleep_mode_sync_d1_r <= sl4nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl4nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl4nl1arc_sys_sleep_mode_sync==sl4nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl4nl1arc_sys_sleep_mode_sync_d1_r!=sl4nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl4nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl4nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl4nl1arc_sys_sleep_mode_sync_mmio_r <= sl4nl1arc_sys_sleep_mode_sync_d1_r;


logic sl4nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl4nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl4nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl4nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl4nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl4nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl4nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl4nl1arc_ext_arc_halt_req_sync_d1_r <= sl4nl1arc_ext_arc_halt_req_sync;
      sl4nl1arc_arc_halt_ack_sync_d1_r <= sl4nl1arc_arc_halt_ack_sync;
    end

  assign set_sl4nl1arc_ext_arc_halt_req_sync_flag = sl4nl1arc_ext_arc_halt_req_sync & !sl4nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl4nl1arc_ext_arc_halt_req_sync_flag = sl4nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl4nl1arc_arc_halt_ack_sync &
                                                               sl4nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl4nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl4nl1arc_ext_arc_halt_req_sync_flag)
      sl4nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl4nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl4nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl4nl1arc_ext_arc_run_req_sync_d1_r;
logic sl4nl1arc_ext_arc_run_req_sync_flag_r;
logic sl4nl1arc_arc_run_ack_sync_d1_r;
logic set_sl4nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl4nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl4nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl4nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl4nl1arc_ext_arc_run_req_sync_d1_r <= sl4nl1arc_ext_arc_run_req_sync;
      sl4nl1arc_arc_run_ack_sync_d1_r <= sl4nl1arc_arc_run_ack_sync;
    end

  assign set_sl4nl1arc_ext_arc_run_req_sync_flag = sl4nl1arc_ext_arc_run_req_sync & !sl4nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl4nl1arc_ext_arc_run_req_sync_flag = sl4nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl4nl1arc_arc_run_ack_sync &
                                                               sl4nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl4nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl4nl1arc_ext_arc_run_req_sync_flag)
      sl4nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl4nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl4nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl4nl1arc_intvbase     = arcsync_core_intvbase[5][31:10];

  assign sl4_rst_a                = core_rst_dly[5][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[5]
                                                ;

  assign sl4_clk_en               = arcsync_core_clk_en[5];

  assign sl4nl1arc_arc_halt_req = arcsync_core_halt_req[5] | sl4nl1arc_ext_arc_halt_req_sync;
  assign sl4nl1arc_arc_run_req  = arcsync_core_run_req[5] | sl4nl1arc_ext_arc_run_req_sync;

  assign sl4nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[5];  
  
  assign core_arcsync_halt_ack[5]         = sl4nl1arc_arc_halt_ack_sync & !sl4nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl4nl1arc_ext_arc_halt_ack = sl4nl1arc_arc_halt_ack_sync & sl4nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[5]          = sl4nl1arc_arc_run_ack_sync & !sl4nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl4nl1arc_ext_arc_run_ack  = sl4nl1arc_arc_run_ack_sync & sl4nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[5]        = sl4nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[5]   = sl4nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[5]         = sl4nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[5]      = sl4nl1arc_sys_tf_halt_sync;    

  assign sl4nl1arc_pwr_dwn      = arcsync_core_rst_req[5]
                                             | arcsync_core_pwr_down[5]
                                             ;
  assign core_arcsync_pmode[5]         = {2'h0, arcsync_core_pwr_down[5]};
  assign sl4nl1arc_isolate_n =   arcsync_core_isolate_n[5]; 
  assign sl4nl1arc_isolate   =   arcsync_core_isolate[5]; 
  assign sl4nl1arc_pd_mem    =   arcsync_core_pd_mem[5]; 
  assign sl4nl1arc_pd_logic  =   arcsync_core_pd_logic[5];
  assign sl4nl1arc_pd_logic1  =   arcsync_core_pd_logic1[5];
  assign sl4nl1arc_pd_logic2  =   arcsync_core_pd_logic2[5];

  // Halt
  logic                   sl5nl1arc_arc_halt_ack_sync;     // from sl5nl1arc_arc_halt_ack_a
  logic                   sl5nl1arc_ext_arc_halt_req_sync; // from sl5nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl5nl1arc_arc_run_ack_sync;      // from sl5nl1arc_arc_run_ack_a
  logic                   sl5nl1arc_ext_arc_run_req_sync;  // from sl5nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl5nl1arc_arc_rst_ack_sync;      // from sl5nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl5nl1arc_sys_sleep_sync;        // from sl5nl1arc_sys_sleep_r
  logic   [2:0]           sl5nl1arc_sys_sleep_mode_sync;   // from sl5nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl5nl1arc_sys_halt_sync;         // from sl5nl1arc_sys_halt_r
  logic                   sl5nl1arc_sys_tf_halt_sync;      // from sl5nl1arc_sys_tf_halt_r

  logic                   sl5nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl5nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl5nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl5nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl5nl1arc_arc_halt_ack_a,        //9
                  sl5nl1arc_ext_arc_halt_req_a,    //8
                  sl5nl1arc_arc_run_ack_a,         //7
                  sl5nl1arc_ext_arc_run_req_a,     //6
                  sl5nl1arc_sys_sleep_r,           //5
                  sl5nl1arc_sys_sleep_mode_r,      //4:2
                  sl5nl1arc_sys_halt_r,            //1
                  sl5nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl5nl1arc_arc_halt_ack_sync,        //9
                  sl5nl1arc_ext_arc_halt_req_sync,    //8
                  sl5nl1arc_arc_run_ack_sync,         //7
                  sl5nl1arc_ext_arc_run_req_sync,     //6
                  sl5nl1arc_sys_sleep_sync,           //5
                  sl5nl1arc_sys_sleep_mode_sync,      //4:2
                  sl5nl1arc_sys_halt_sync,            //1
                  sl5nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl5nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl5nl1arc_sys_sleep_mode_sync_d1_r <= sl5nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl5nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl5nl1arc_sys_sleep_mode_sync==sl5nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl5nl1arc_sys_sleep_mode_sync_d1_r!=sl5nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl5nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl5nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl5nl1arc_sys_sleep_mode_sync_mmio_r <= sl5nl1arc_sys_sleep_mode_sync_d1_r;


logic sl5nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl5nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl5nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl5nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl5nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl5nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl5nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl5nl1arc_ext_arc_halt_req_sync_d1_r <= sl5nl1arc_ext_arc_halt_req_sync;
      sl5nl1arc_arc_halt_ack_sync_d1_r <= sl5nl1arc_arc_halt_ack_sync;
    end

  assign set_sl5nl1arc_ext_arc_halt_req_sync_flag = sl5nl1arc_ext_arc_halt_req_sync & !sl5nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl5nl1arc_ext_arc_halt_req_sync_flag = sl5nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl5nl1arc_arc_halt_ack_sync &
                                                               sl5nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl5nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl5nl1arc_ext_arc_halt_req_sync_flag)
      sl5nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl5nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl5nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl5nl1arc_ext_arc_run_req_sync_d1_r;
logic sl5nl1arc_ext_arc_run_req_sync_flag_r;
logic sl5nl1arc_arc_run_ack_sync_d1_r;
logic set_sl5nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl5nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl5nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl5nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl5nl1arc_ext_arc_run_req_sync_d1_r <= sl5nl1arc_ext_arc_run_req_sync;
      sl5nl1arc_arc_run_ack_sync_d1_r <= sl5nl1arc_arc_run_ack_sync;
    end

  assign set_sl5nl1arc_ext_arc_run_req_sync_flag = sl5nl1arc_ext_arc_run_req_sync & !sl5nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl5nl1arc_ext_arc_run_req_sync_flag = sl5nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl5nl1arc_arc_run_ack_sync &
                                                               sl5nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl5nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl5nl1arc_ext_arc_run_req_sync_flag)
      sl5nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl5nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl5nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl5nl1arc_intvbase     = arcsync_core_intvbase[6][31:10];

  assign sl5_rst_a                = core_rst_dly[6][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[6]
                                                ;

  assign sl5_clk_en               = arcsync_core_clk_en[6];

  assign sl5nl1arc_arc_halt_req = arcsync_core_halt_req[6] | sl5nl1arc_ext_arc_halt_req_sync;
  assign sl5nl1arc_arc_run_req  = arcsync_core_run_req[6] | sl5nl1arc_ext_arc_run_req_sync;

  assign sl5nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[6];  
  
  assign core_arcsync_halt_ack[6]         = sl5nl1arc_arc_halt_ack_sync & !sl5nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl5nl1arc_ext_arc_halt_ack = sl5nl1arc_arc_halt_ack_sync & sl5nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[6]          = sl5nl1arc_arc_run_ack_sync & !sl5nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl5nl1arc_ext_arc_run_ack  = sl5nl1arc_arc_run_ack_sync & sl5nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[6]        = sl5nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[6]   = sl5nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[6]         = sl5nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[6]      = sl5nl1arc_sys_tf_halt_sync;    

  assign sl5nl1arc_pwr_dwn      = arcsync_core_rst_req[6]
                                             | arcsync_core_pwr_down[6]
                                             ;
  assign core_arcsync_pmode[6]         = {2'h0, arcsync_core_pwr_down[6]};
  assign sl5nl1arc_isolate_n =   arcsync_core_isolate_n[6]; 
  assign sl5nl1arc_isolate   =   arcsync_core_isolate[6]; 
  assign sl5nl1arc_pd_mem    =   arcsync_core_pd_mem[6]; 
  assign sl5nl1arc_pd_logic  =   arcsync_core_pd_logic[6];
  assign sl5nl1arc_pd_logic1  =   arcsync_core_pd_logic1[6];
  assign sl5nl1arc_pd_logic2  =   arcsync_core_pd_logic2[6];

  // Halt
  logic                   sl6nl1arc_arc_halt_ack_sync;     // from sl6nl1arc_arc_halt_ack_a
  logic                   sl6nl1arc_ext_arc_halt_req_sync; // from sl6nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl6nl1arc_arc_run_ack_sync;      // from sl6nl1arc_arc_run_ack_a
  logic                   sl6nl1arc_ext_arc_run_req_sync;  // from sl6nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl6nl1arc_arc_rst_ack_sync;      // from sl6nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl6nl1arc_sys_sleep_sync;        // from sl6nl1arc_sys_sleep_r
  logic   [2:0]           sl6nl1arc_sys_sleep_mode_sync;   // from sl6nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl6nl1arc_sys_halt_sync;         // from sl6nl1arc_sys_halt_r
  logic                   sl6nl1arc_sys_tf_halt_sync;      // from sl6nl1arc_sys_tf_halt_r

  logic                   sl6nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl6nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl6nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl6nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl6nl1arc_arc_halt_ack_a,        //9
                  sl6nl1arc_ext_arc_halt_req_a,    //8
                  sl6nl1arc_arc_run_ack_a,         //7
                  sl6nl1arc_ext_arc_run_req_a,     //6
                  sl6nl1arc_sys_sleep_r,           //5
                  sl6nl1arc_sys_sleep_mode_r,      //4:2
                  sl6nl1arc_sys_halt_r,            //1
                  sl6nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl6nl1arc_arc_halt_ack_sync,        //9
                  sl6nl1arc_ext_arc_halt_req_sync,    //8
                  sl6nl1arc_arc_run_ack_sync,         //7
                  sl6nl1arc_ext_arc_run_req_sync,     //6
                  sl6nl1arc_sys_sleep_sync,           //5
                  sl6nl1arc_sys_sleep_mode_sync,      //4:2
                  sl6nl1arc_sys_halt_sync,            //1
                  sl6nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl6nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl6nl1arc_sys_sleep_mode_sync_d1_r <= sl6nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl6nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl6nl1arc_sys_sleep_mode_sync==sl6nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl6nl1arc_sys_sleep_mode_sync_d1_r!=sl6nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl6nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl6nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl6nl1arc_sys_sleep_mode_sync_mmio_r <= sl6nl1arc_sys_sleep_mode_sync_d1_r;


logic sl6nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl6nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl6nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl6nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl6nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl6nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl6nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl6nl1arc_ext_arc_halt_req_sync_d1_r <= sl6nl1arc_ext_arc_halt_req_sync;
      sl6nl1arc_arc_halt_ack_sync_d1_r <= sl6nl1arc_arc_halt_ack_sync;
    end

  assign set_sl6nl1arc_ext_arc_halt_req_sync_flag = sl6nl1arc_ext_arc_halt_req_sync & !sl6nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl6nl1arc_ext_arc_halt_req_sync_flag = sl6nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl6nl1arc_arc_halt_ack_sync &
                                                               sl6nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl6nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl6nl1arc_ext_arc_halt_req_sync_flag)
      sl6nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl6nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl6nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl6nl1arc_ext_arc_run_req_sync_d1_r;
logic sl6nl1arc_ext_arc_run_req_sync_flag_r;
logic sl6nl1arc_arc_run_ack_sync_d1_r;
logic set_sl6nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl6nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl6nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl6nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl6nl1arc_ext_arc_run_req_sync_d1_r <= sl6nl1arc_ext_arc_run_req_sync;
      sl6nl1arc_arc_run_ack_sync_d1_r <= sl6nl1arc_arc_run_ack_sync;
    end

  assign set_sl6nl1arc_ext_arc_run_req_sync_flag = sl6nl1arc_ext_arc_run_req_sync & !sl6nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl6nl1arc_ext_arc_run_req_sync_flag = sl6nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl6nl1arc_arc_run_ack_sync &
                                                               sl6nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl6nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl6nl1arc_ext_arc_run_req_sync_flag)
      sl6nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl6nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl6nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl6nl1arc_intvbase     = arcsync_core_intvbase[7][31:10];

  assign sl6_rst_a                = core_rst_dly[7][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[7]
                                                ;

  assign sl6_clk_en               = arcsync_core_clk_en[7];

  assign sl6nl1arc_arc_halt_req = arcsync_core_halt_req[7] | sl6nl1arc_ext_arc_halt_req_sync;
  assign sl6nl1arc_arc_run_req  = arcsync_core_run_req[7] | sl6nl1arc_ext_arc_run_req_sync;

  assign sl6nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[7];  
  
  assign core_arcsync_halt_ack[7]         = sl6nl1arc_arc_halt_ack_sync & !sl6nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl6nl1arc_ext_arc_halt_ack = sl6nl1arc_arc_halt_ack_sync & sl6nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[7]          = sl6nl1arc_arc_run_ack_sync & !sl6nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl6nl1arc_ext_arc_run_ack  = sl6nl1arc_arc_run_ack_sync & sl6nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[7]        = sl6nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[7]   = sl6nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[7]         = sl6nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[7]      = sl6nl1arc_sys_tf_halt_sync;    

  assign sl6nl1arc_pwr_dwn      = arcsync_core_rst_req[7]
                                             | arcsync_core_pwr_down[7]
                                             ;
  assign core_arcsync_pmode[7]         = {2'h0, arcsync_core_pwr_down[7]};
  assign sl6nl1arc_isolate_n =   arcsync_core_isolate_n[7]; 
  assign sl6nl1arc_isolate   =   arcsync_core_isolate[7]; 
  assign sl6nl1arc_pd_mem    =   arcsync_core_pd_mem[7]; 
  assign sl6nl1arc_pd_logic  =   arcsync_core_pd_logic[7];
  assign sl6nl1arc_pd_logic1  =   arcsync_core_pd_logic1[7];
  assign sl6nl1arc_pd_logic2  =   arcsync_core_pd_logic2[7];

  // Halt
  logic                   sl7nl1arc_arc_halt_ack_sync;     // from sl7nl1arc_arc_halt_ack_a
  logic                   sl7nl1arc_ext_arc_halt_req_sync; // from sl7nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl7nl1arc_arc_run_ack_sync;      // from sl7nl1arc_arc_run_ack_a
  logic                   sl7nl1arc_ext_arc_run_req_sync;  // from sl7nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl7nl1arc_arc_rst_ack_sync;      // from sl7nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl7nl1arc_sys_sleep_sync;        // from sl7nl1arc_sys_sleep_r
  logic   [2:0]           sl7nl1arc_sys_sleep_mode_sync;   // from sl7nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl7nl1arc_sys_halt_sync;         // from sl7nl1arc_sys_halt_r
  logic                   sl7nl1arc_sys_tf_halt_sync;      // from sl7nl1arc_sys_tf_halt_r

  logic                   sl7nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl7nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl7nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl7nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl7nl1arc_arc_halt_ack_a,        //9
                  sl7nl1arc_ext_arc_halt_req_a,    //8
                  sl7nl1arc_arc_run_ack_a,         //7
                  sl7nl1arc_ext_arc_run_req_a,     //6
                  sl7nl1arc_sys_sleep_r,           //5
                  sl7nl1arc_sys_sleep_mode_r,      //4:2
                  sl7nl1arc_sys_halt_r,            //1
                  sl7nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl7nl1arc_arc_halt_ack_sync,        //9
                  sl7nl1arc_ext_arc_halt_req_sync,    //8
                  sl7nl1arc_arc_run_ack_sync,         //7
                  sl7nl1arc_ext_arc_run_req_sync,     //6
                  sl7nl1arc_sys_sleep_sync,           //5
                  sl7nl1arc_sys_sleep_mode_sync,      //4:2
                  sl7nl1arc_sys_halt_sync,            //1
                  sl7nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl7nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl7nl1arc_sys_sleep_mode_sync_d1_r <= sl7nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl7nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl7nl1arc_sys_sleep_mode_sync==sl7nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl7nl1arc_sys_sleep_mode_sync_d1_r!=sl7nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl7nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl7nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl7nl1arc_sys_sleep_mode_sync_mmio_r <= sl7nl1arc_sys_sleep_mode_sync_d1_r;


logic sl7nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl7nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl7nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl7nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl7nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl7nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl7nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl7nl1arc_ext_arc_halt_req_sync_d1_r <= sl7nl1arc_ext_arc_halt_req_sync;
      sl7nl1arc_arc_halt_ack_sync_d1_r <= sl7nl1arc_arc_halt_ack_sync;
    end

  assign set_sl7nl1arc_ext_arc_halt_req_sync_flag = sl7nl1arc_ext_arc_halt_req_sync & !sl7nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl7nl1arc_ext_arc_halt_req_sync_flag = sl7nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl7nl1arc_arc_halt_ack_sync &
                                                               sl7nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl7nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl7nl1arc_ext_arc_halt_req_sync_flag)
      sl7nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl7nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl7nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl7nl1arc_ext_arc_run_req_sync_d1_r;
logic sl7nl1arc_ext_arc_run_req_sync_flag_r;
logic sl7nl1arc_arc_run_ack_sync_d1_r;
logic set_sl7nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl7nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl7nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl7nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl7nl1arc_ext_arc_run_req_sync_d1_r <= sl7nl1arc_ext_arc_run_req_sync;
      sl7nl1arc_arc_run_ack_sync_d1_r <= sl7nl1arc_arc_run_ack_sync;
    end

  assign set_sl7nl1arc_ext_arc_run_req_sync_flag = sl7nl1arc_ext_arc_run_req_sync & !sl7nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl7nl1arc_ext_arc_run_req_sync_flag = sl7nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl7nl1arc_arc_run_ack_sync &
                                                               sl7nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl7nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl7nl1arc_ext_arc_run_req_sync_flag)
      sl7nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl7nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl7nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl7nl1arc_intvbase     = arcsync_core_intvbase[8][31:10];

  assign sl7_rst_a                = core_rst_dly[8][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[8]
                                                ;

  assign sl7_clk_en               = arcsync_core_clk_en[8];

  assign sl7nl1arc_arc_halt_req = arcsync_core_halt_req[8] | sl7nl1arc_ext_arc_halt_req_sync;
  assign sl7nl1arc_arc_run_req  = arcsync_core_run_req[8] | sl7nl1arc_ext_arc_run_req_sync;

  assign sl7nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[8];  
  
  assign core_arcsync_halt_ack[8]         = sl7nl1arc_arc_halt_ack_sync & !sl7nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl7nl1arc_ext_arc_halt_ack = sl7nl1arc_arc_halt_ack_sync & sl7nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[8]          = sl7nl1arc_arc_run_ack_sync & !sl7nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl7nl1arc_ext_arc_run_ack  = sl7nl1arc_arc_run_ack_sync & sl7nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[8]        = sl7nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[8]   = sl7nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[8]         = sl7nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[8]      = sl7nl1arc_sys_tf_halt_sync;    

  assign sl7nl1arc_pwr_dwn      = arcsync_core_rst_req[8]
                                             | arcsync_core_pwr_down[8]
                                             ;
  assign core_arcsync_pmode[8]         = {2'h0, arcsync_core_pwr_down[8]};
  assign sl7nl1arc_isolate_n =   arcsync_core_isolate_n[8]; 
  assign sl7nl1arc_isolate   =   arcsync_core_isolate[8]; 
  assign sl7nl1arc_pd_mem    =   arcsync_core_pd_mem[8]; 
  assign sl7nl1arc_pd_logic  =   arcsync_core_pd_logic[8];
  assign sl7nl1arc_pd_logic1  =   arcsync_core_pd_logic1[8];
  assign sl7nl1arc_pd_logic2  =   arcsync_core_pd_logic2[8];

  // Halt
  logic                   sl8nl1arc_arc_halt_ack_sync;     // from sl8nl1arc_arc_halt_ack_a
  logic                   sl8nl1arc_ext_arc_halt_req_sync; // from sl8nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl8nl1arc_arc_run_ack_sync;      // from sl8nl1arc_arc_run_ack_a
  logic                   sl8nl1arc_ext_arc_run_req_sync;  // from sl8nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl8nl1arc_arc_rst_ack_sync;      // from sl8nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl8nl1arc_sys_sleep_sync;        // from sl8nl1arc_sys_sleep_r
  logic   [2:0]           sl8nl1arc_sys_sleep_mode_sync;   // from sl8nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl8nl1arc_sys_halt_sync;         // from sl8nl1arc_sys_halt_r
  logic                   sl8nl1arc_sys_tf_halt_sync;      // from sl8nl1arc_sys_tf_halt_r

  logic                   sl8nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl8nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl8nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl8nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl8nl1arc_arc_halt_ack_a,        //9
                  sl8nl1arc_ext_arc_halt_req_a,    //8
                  sl8nl1arc_arc_run_ack_a,         //7
                  sl8nl1arc_ext_arc_run_req_a,     //6
                  sl8nl1arc_sys_sleep_r,           //5
                  sl8nl1arc_sys_sleep_mode_r,      //4:2
                  sl8nl1arc_sys_halt_r,            //1
                  sl8nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl8nl1arc_arc_halt_ack_sync,        //9
                  sl8nl1arc_ext_arc_halt_req_sync,    //8
                  sl8nl1arc_arc_run_ack_sync,         //7
                  sl8nl1arc_ext_arc_run_req_sync,     //6
                  sl8nl1arc_sys_sleep_sync,           //5
                  sl8nl1arc_sys_sleep_mode_sync,      //4:2
                  sl8nl1arc_sys_halt_sync,            //1
                  sl8nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl8nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl8nl1arc_sys_sleep_mode_sync_d1_r <= sl8nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl8nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl8nl1arc_sys_sleep_mode_sync==sl8nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl8nl1arc_sys_sleep_mode_sync_d1_r!=sl8nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl8nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl8nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl8nl1arc_sys_sleep_mode_sync_mmio_r <= sl8nl1arc_sys_sleep_mode_sync_d1_r;


logic sl8nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl8nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl8nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl8nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl8nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl8nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl8nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl8nl1arc_ext_arc_halt_req_sync_d1_r <= sl8nl1arc_ext_arc_halt_req_sync;
      sl8nl1arc_arc_halt_ack_sync_d1_r <= sl8nl1arc_arc_halt_ack_sync;
    end

  assign set_sl8nl1arc_ext_arc_halt_req_sync_flag = sl8nl1arc_ext_arc_halt_req_sync & !sl8nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl8nl1arc_ext_arc_halt_req_sync_flag = sl8nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl8nl1arc_arc_halt_ack_sync &
                                                               sl8nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl8nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl8nl1arc_ext_arc_halt_req_sync_flag)
      sl8nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl8nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl8nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl8nl1arc_ext_arc_run_req_sync_d1_r;
logic sl8nl1arc_ext_arc_run_req_sync_flag_r;
logic sl8nl1arc_arc_run_ack_sync_d1_r;
logic set_sl8nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl8nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl8nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl8nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl8nl1arc_ext_arc_run_req_sync_d1_r <= sl8nl1arc_ext_arc_run_req_sync;
      sl8nl1arc_arc_run_ack_sync_d1_r <= sl8nl1arc_arc_run_ack_sync;
    end

  assign set_sl8nl1arc_ext_arc_run_req_sync_flag = sl8nl1arc_ext_arc_run_req_sync & !sl8nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl8nl1arc_ext_arc_run_req_sync_flag = sl8nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl8nl1arc_arc_run_ack_sync &
                                                               sl8nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl8nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl8nl1arc_ext_arc_run_req_sync_flag)
      sl8nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl8nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl8nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl8nl1arc_intvbase     = arcsync_core_intvbase[9][31:10];

  assign sl8_rst_a                = core_rst_dly[9][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[9]
                                                ;

  assign sl8_clk_en               = arcsync_core_clk_en[9];

  assign sl8nl1arc_arc_halt_req = arcsync_core_halt_req[9] | sl8nl1arc_ext_arc_halt_req_sync;
  assign sl8nl1arc_arc_run_req  = arcsync_core_run_req[9] | sl8nl1arc_ext_arc_run_req_sync;

  assign sl8nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[9];  
  
  assign core_arcsync_halt_ack[9]         = sl8nl1arc_arc_halt_ack_sync & !sl8nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl8nl1arc_ext_arc_halt_ack = sl8nl1arc_arc_halt_ack_sync & sl8nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[9]          = sl8nl1arc_arc_run_ack_sync & !sl8nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl8nl1arc_ext_arc_run_ack  = sl8nl1arc_arc_run_ack_sync & sl8nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[9]        = sl8nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[9]   = sl8nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[9]         = sl8nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[9]      = sl8nl1arc_sys_tf_halt_sync;    

  assign sl8nl1arc_pwr_dwn      = arcsync_core_rst_req[9]
                                             | arcsync_core_pwr_down[9]
                                             ;
  assign core_arcsync_pmode[9]         = {2'h0, arcsync_core_pwr_down[9]};
  assign sl8nl1arc_isolate_n =   arcsync_core_isolate_n[9]; 
  assign sl8nl1arc_isolate   =   arcsync_core_isolate[9]; 
  assign sl8nl1arc_pd_mem    =   arcsync_core_pd_mem[9]; 
  assign sl8nl1arc_pd_logic  =   arcsync_core_pd_logic[9];
  assign sl8nl1arc_pd_logic1  =   arcsync_core_pd_logic1[9];
  assign sl8nl1arc_pd_logic2  =   arcsync_core_pd_logic2[9];

  // Halt
  logic                   sl9nl1arc_arc_halt_ack_sync;     // from sl9nl1arc_arc_halt_ack_a
  logic                   sl9nl1arc_ext_arc_halt_req_sync; // from sl9nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl9nl1arc_arc_run_ack_sync;      // from sl9nl1arc_arc_run_ack_a
  logic                   sl9nl1arc_ext_arc_run_req_sync;  // from sl9nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl9nl1arc_arc_rst_ack_sync;      // from sl9nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl9nl1arc_sys_sleep_sync;        // from sl9nl1arc_sys_sleep_r
  logic   [2:0]           sl9nl1arc_sys_sleep_mode_sync;   // from sl9nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl9nl1arc_sys_halt_sync;         // from sl9nl1arc_sys_halt_r
  logic                   sl9nl1arc_sys_tf_halt_sync;      // from sl9nl1arc_sys_tf_halt_r

  logic                   sl9nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl9nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl9nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl9nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl9nl1arc_arc_halt_ack_a,        //9
                  sl9nl1arc_ext_arc_halt_req_a,    //8
                  sl9nl1arc_arc_run_ack_a,         //7
                  sl9nl1arc_ext_arc_run_req_a,     //6
                  sl9nl1arc_sys_sleep_r,           //5
                  sl9nl1arc_sys_sleep_mode_r,      //4:2
                  sl9nl1arc_sys_halt_r,            //1
                  sl9nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl9nl1arc_arc_halt_ack_sync,        //9
                  sl9nl1arc_ext_arc_halt_req_sync,    //8
                  sl9nl1arc_arc_run_ack_sync,         //7
                  sl9nl1arc_ext_arc_run_req_sync,     //6
                  sl9nl1arc_sys_sleep_sync,           //5
                  sl9nl1arc_sys_sleep_mode_sync,      //4:2
                  sl9nl1arc_sys_halt_sync,            //1
                  sl9nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl9nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl9nl1arc_sys_sleep_mode_sync_d1_r <= sl9nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl9nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl9nl1arc_sys_sleep_mode_sync==sl9nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl9nl1arc_sys_sleep_mode_sync_d1_r!=sl9nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl9nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl9nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl9nl1arc_sys_sleep_mode_sync_mmio_r <= sl9nl1arc_sys_sleep_mode_sync_d1_r;


logic sl9nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl9nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl9nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl9nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl9nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl9nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl9nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl9nl1arc_ext_arc_halt_req_sync_d1_r <= sl9nl1arc_ext_arc_halt_req_sync;
      sl9nl1arc_arc_halt_ack_sync_d1_r <= sl9nl1arc_arc_halt_ack_sync;
    end

  assign set_sl9nl1arc_ext_arc_halt_req_sync_flag = sl9nl1arc_ext_arc_halt_req_sync & !sl9nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl9nl1arc_ext_arc_halt_req_sync_flag = sl9nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl9nl1arc_arc_halt_ack_sync &
                                                               sl9nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl9nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl9nl1arc_ext_arc_halt_req_sync_flag)
      sl9nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl9nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl9nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl9nl1arc_ext_arc_run_req_sync_d1_r;
logic sl9nl1arc_ext_arc_run_req_sync_flag_r;
logic sl9nl1arc_arc_run_ack_sync_d1_r;
logic set_sl9nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl9nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl9nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl9nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl9nl1arc_ext_arc_run_req_sync_d1_r <= sl9nl1arc_ext_arc_run_req_sync;
      sl9nl1arc_arc_run_ack_sync_d1_r <= sl9nl1arc_arc_run_ack_sync;
    end

  assign set_sl9nl1arc_ext_arc_run_req_sync_flag = sl9nl1arc_ext_arc_run_req_sync & !sl9nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl9nl1arc_ext_arc_run_req_sync_flag = sl9nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl9nl1arc_arc_run_ack_sync &
                                                               sl9nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl9nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl9nl1arc_ext_arc_run_req_sync_flag)
      sl9nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl9nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl9nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl9nl1arc_intvbase     = arcsync_core_intvbase[10][31:10];

  assign sl9_rst_a                = core_rst_dly[10][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[10]
                                                ;

  assign sl9_clk_en               = arcsync_core_clk_en[10];

  assign sl9nl1arc_arc_halt_req = arcsync_core_halt_req[10] | sl9nl1arc_ext_arc_halt_req_sync;
  assign sl9nl1arc_arc_run_req  = arcsync_core_run_req[10] | sl9nl1arc_ext_arc_run_req_sync;

  assign sl9nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[10];  
  
  assign core_arcsync_halt_ack[10]         = sl9nl1arc_arc_halt_ack_sync & !sl9nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl9nl1arc_ext_arc_halt_ack = sl9nl1arc_arc_halt_ack_sync & sl9nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[10]          = sl9nl1arc_arc_run_ack_sync & !sl9nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl9nl1arc_ext_arc_run_ack  = sl9nl1arc_arc_run_ack_sync & sl9nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[10]        = sl9nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[10]   = sl9nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[10]         = sl9nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[10]      = sl9nl1arc_sys_tf_halt_sync;    

  assign sl9nl1arc_pwr_dwn      = arcsync_core_rst_req[10]
                                             | arcsync_core_pwr_down[10]
                                             ;
  assign core_arcsync_pmode[10]         = {2'h0, arcsync_core_pwr_down[10]};
  assign sl9nl1arc_isolate_n =   arcsync_core_isolate_n[10]; 
  assign sl9nl1arc_isolate   =   arcsync_core_isolate[10]; 
  assign sl9nl1arc_pd_mem    =   arcsync_core_pd_mem[10]; 
  assign sl9nl1arc_pd_logic  =   arcsync_core_pd_logic[10];
  assign sl9nl1arc_pd_logic1  =   arcsync_core_pd_logic1[10];
  assign sl9nl1arc_pd_logic2  =   arcsync_core_pd_logic2[10];

  // Halt
  logic                   sl10nl1arc_arc_halt_ack_sync;     // from sl10nl1arc_arc_halt_ack_a
  logic                   sl10nl1arc_ext_arc_halt_req_sync; // from sl10nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl10nl1arc_arc_run_ack_sync;      // from sl10nl1arc_arc_run_ack_a
  logic                   sl10nl1arc_ext_arc_run_req_sync;  // from sl10nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl10nl1arc_arc_rst_ack_sync;      // from sl10nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl10nl1arc_sys_sleep_sync;        // from sl10nl1arc_sys_sleep_r
  logic   [2:0]           sl10nl1arc_sys_sleep_mode_sync;   // from sl10nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl10nl1arc_sys_halt_sync;         // from sl10nl1arc_sys_halt_r
  logic                   sl10nl1arc_sys_tf_halt_sync;      // from sl10nl1arc_sys_tf_halt_r

  logic                   sl10nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl10nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl10nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl10nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl10nl1arc_arc_halt_ack_a,        //9
                  sl10nl1arc_ext_arc_halt_req_a,    //8
                  sl10nl1arc_arc_run_ack_a,         //7
                  sl10nl1arc_ext_arc_run_req_a,     //6
                  sl10nl1arc_sys_sleep_r,           //5
                  sl10nl1arc_sys_sleep_mode_r,      //4:2
                  sl10nl1arc_sys_halt_r,            //1
                  sl10nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl10nl1arc_arc_halt_ack_sync,        //9
                  sl10nl1arc_ext_arc_halt_req_sync,    //8
                  sl10nl1arc_arc_run_ack_sync,         //7
                  sl10nl1arc_ext_arc_run_req_sync,     //6
                  sl10nl1arc_sys_sleep_sync,           //5
                  sl10nl1arc_sys_sleep_mode_sync,      //4:2
                  sl10nl1arc_sys_halt_sync,            //1
                  sl10nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl10nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl10nl1arc_sys_sleep_mode_sync_d1_r <= sl10nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl10nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl10nl1arc_sys_sleep_mode_sync==sl10nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl10nl1arc_sys_sleep_mode_sync_d1_r!=sl10nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl10nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl10nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl10nl1arc_sys_sleep_mode_sync_mmio_r <= sl10nl1arc_sys_sleep_mode_sync_d1_r;


logic sl10nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl10nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl10nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl10nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl10nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl10nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl10nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl10nl1arc_ext_arc_halt_req_sync_d1_r <= sl10nl1arc_ext_arc_halt_req_sync;
      sl10nl1arc_arc_halt_ack_sync_d1_r <= sl10nl1arc_arc_halt_ack_sync;
    end

  assign set_sl10nl1arc_ext_arc_halt_req_sync_flag = sl10nl1arc_ext_arc_halt_req_sync & !sl10nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl10nl1arc_ext_arc_halt_req_sync_flag = sl10nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl10nl1arc_arc_halt_ack_sync &
                                                               sl10nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl10nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl10nl1arc_ext_arc_halt_req_sync_flag)
      sl10nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl10nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl10nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl10nl1arc_ext_arc_run_req_sync_d1_r;
logic sl10nl1arc_ext_arc_run_req_sync_flag_r;
logic sl10nl1arc_arc_run_ack_sync_d1_r;
logic set_sl10nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl10nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl10nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl10nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl10nl1arc_ext_arc_run_req_sync_d1_r <= sl10nl1arc_ext_arc_run_req_sync;
      sl10nl1arc_arc_run_ack_sync_d1_r <= sl10nl1arc_arc_run_ack_sync;
    end

  assign set_sl10nl1arc_ext_arc_run_req_sync_flag = sl10nl1arc_ext_arc_run_req_sync & !sl10nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl10nl1arc_ext_arc_run_req_sync_flag = sl10nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl10nl1arc_arc_run_ack_sync &
                                                               sl10nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl10nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl10nl1arc_ext_arc_run_req_sync_flag)
      sl10nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl10nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl10nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl10nl1arc_intvbase     = arcsync_core_intvbase[11][31:10];

  assign sl10_rst_a                = core_rst_dly[11][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[11]
                                                ;

  assign sl10_clk_en               = arcsync_core_clk_en[11];

  assign sl10nl1arc_arc_halt_req = arcsync_core_halt_req[11] | sl10nl1arc_ext_arc_halt_req_sync;
  assign sl10nl1arc_arc_run_req  = arcsync_core_run_req[11] | sl10nl1arc_ext_arc_run_req_sync;

  assign sl10nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[11];  
  
  assign core_arcsync_halt_ack[11]         = sl10nl1arc_arc_halt_ack_sync & !sl10nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl10nl1arc_ext_arc_halt_ack = sl10nl1arc_arc_halt_ack_sync & sl10nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[11]          = sl10nl1arc_arc_run_ack_sync & !sl10nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl10nl1arc_ext_arc_run_ack  = sl10nl1arc_arc_run_ack_sync & sl10nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[11]        = sl10nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[11]   = sl10nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[11]         = sl10nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[11]      = sl10nl1arc_sys_tf_halt_sync;    

  assign sl10nl1arc_pwr_dwn      = arcsync_core_rst_req[11]
                                             | arcsync_core_pwr_down[11]
                                             ;
  assign core_arcsync_pmode[11]         = {2'h0, arcsync_core_pwr_down[11]};
  assign sl10nl1arc_isolate_n =   arcsync_core_isolate_n[11]; 
  assign sl10nl1arc_isolate   =   arcsync_core_isolate[11]; 
  assign sl10nl1arc_pd_mem    =   arcsync_core_pd_mem[11]; 
  assign sl10nl1arc_pd_logic  =   arcsync_core_pd_logic[11];
  assign sl10nl1arc_pd_logic1  =   arcsync_core_pd_logic1[11];
  assign sl10nl1arc_pd_logic2  =   arcsync_core_pd_logic2[11];

  // Halt
  logic                   sl11nl1arc_arc_halt_ack_sync;     // from sl11nl1arc_arc_halt_ack_a
  logic                   sl11nl1arc_ext_arc_halt_req_sync; // from sl11nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl11nl1arc_arc_run_ack_sync;      // from sl11nl1arc_arc_run_ack_a
  logic                   sl11nl1arc_ext_arc_run_req_sync;  // from sl11nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl11nl1arc_arc_rst_ack_sync;      // from sl11nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl11nl1arc_sys_sleep_sync;        // from sl11nl1arc_sys_sleep_r
  logic   [2:0]           sl11nl1arc_sys_sleep_mode_sync;   // from sl11nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl11nl1arc_sys_halt_sync;         // from sl11nl1arc_sys_halt_r
  logic                   sl11nl1arc_sys_tf_halt_sync;      // from sl11nl1arc_sys_tf_halt_r

  logic                   sl11nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl11nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl11nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl11nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl11nl1arc_arc_halt_ack_a,        //9
                  sl11nl1arc_ext_arc_halt_req_a,    //8
                  sl11nl1arc_arc_run_ack_a,         //7
                  sl11nl1arc_ext_arc_run_req_a,     //6
                  sl11nl1arc_sys_sleep_r,           //5
                  sl11nl1arc_sys_sleep_mode_r,      //4:2
                  sl11nl1arc_sys_halt_r,            //1
                  sl11nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl11nl1arc_arc_halt_ack_sync,        //9
                  sl11nl1arc_ext_arc_halt_req_sync,    //8
                  sl11nl1arc_arc_run_ack_sync,         //7
                  sl11nl1arc_ext_arc_run_req_sync,     //6
                  sl11nl1arc_sys_sleep_sync,           //5
                  sl11nl1arc_sys_sleep_mode_sync,      //4:2
                  sl11nl1arc_sys_halt_sync,            //1
                  sl11nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl11nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl11nl1arc_sys_sleep_mode_sync_d1_r <= sl11nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl11nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl11nl1arc_sys_sleep_mode_sync==sl11nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl11nl1arc_sys_sleep_mode_sync_d1_r!=sl11nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl11nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl11nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl11nl1arc_sys_sleep_mode_sync_mmio_r <= sl11nl1arc_sys_sleep_mode_sync_d1_r;


logic sl11nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl11nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl11nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl11nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl11nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl11nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl11nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl11nl1arc_ext_arc_halt_req_sync_d1_r <= sl11nl1arc_ext_arc_halt_req_sync;
      sl11nl1arc_arc_halt_ack_sync_d1_r <= sl11nl1arc_arc_halt_ack_sync;
    end

  assign set_sl11nl1arc_ext_arc_halt_req_sync_flag = sl11nl1arc_ext_arc_halt_req_sync & !sl11nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl11nl1arc_ext_arc_halt_req_sync_flag = sl11nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl11nl1arc_arc_halt_ack_sync &
                                                               sl11nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl11nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl11nl1arc_ext_arc_halt_req_sync_flag)
      sl11nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl11nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl11nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl11nl1arc_ext_arc_run_req_sync_d1_r;
logic sl11nl1arc_ext_arc_run_req_sync_flag_r;
logic sl11nl1arc_arc_run_ack_sync_d1_r;
logic set_sl11nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl11nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl11nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl11nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl11nl1arc_ext_arc_run_req_sync_d1_r <= sl11nl1arc_ext_arc_run_req_sync;
      sl11nl1arc_arc_run_ack_sync_d1_r <= sl11nl1arc_arc_run_ack_sync;
    end

  assign set_sl11nl1arc_ext_arc_run_req_sync_flag = sl11nl1arc_ext_arc_run_req_sync & !sl11nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl11nl1arc_ext_arc_run_req_sync_flag = sl11nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl11nl1arc_arc_run_ack_sync &
                                                               sl11nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl11nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl11nl1arc_ext_arc_run_req_sync_flag)
      sl11nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl11nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl11nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl11nl1arc_intvbase     = arcsync_core_intvbase[12][31:10];

  assign sl11_rst_a                = core_rst_dly[12][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[12]
                                                ;

  assign sl11_clk_en               = arcsync_core_clk_en[12];

  assign sl11nl1arc_arc_halt_req = arcsync_core_halt_req[12] | sl11nl1arc_ext_arc_halt_req_sync;
  assign sl11nl1arc_arc_run_req  = arcsync_core_run_req[12] | sl11nl1arc_ext_arc_run_req_sync;

  assign sl11nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[12];  
  
  assign core_arcsync_halt_ack[12]         = sl11nl1arc_arc_halt_ack_sync & !sl11nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl11nl1arc_ext_arc_halt_ack = sl11nl1arc_arc_halt_ack_sync & sl11nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[12]          = sl11nl1arc_arc_run_ack_sync & !sl11nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl11nl1arc_ext_arc_run_ack  = sl11nl1arc_arc_run_ack_sync & sl11nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[12]        = sl11nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[12]   = sl11nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[12]         = sl11nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[12]      = sl11nl1arc_sys_tf_halt_sync;    

  assign sl11nl1arc_pwr_dwn      = arcsync_core_rst_req[12]
                                             | arcsync_core_pwr_down[12]
                                             ;
  assign core_arcsync_pmode[12]         = {2'h0, arcsync_core_pwr_down[12]};
  assign sl11nl1arc_isolate_n =   arcsync_core_isolate_n[12]; 
  assign sl11nl1arc_isolate   =   arcsync_core_isolate[12]; 
  assign sl11nl1arc_pd_mem    =   arcsync_core_pd_mem[12]; 
  assign sl11nl1arc_pd_logic  =   arcsync_core_pd_logic[12];
  assign sl11nl1arc_pd_logic1  =   arcsync_core_pd_logic1[12];
  assign sl11nl1arc_pd_logic2  =   arcsync_core_pd_logic2[12];

  // Halt
  logic                   sl12nl1arc_arc_halt_ack_sync;     // from sl12nl1arc_arc_halt_ack_a
  logic                   sl12nl1arc_ext_arc_halt_req_sync; // from sl12nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl12nl1arc_arc_run_ack_sync;      // from sl12nl1arc_arc_run_ack_a
  logic                   sl12nl1arc_ext_arc_run_req_sync;  // from sl12nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl12nl1arc_arc_rst_ack_sync;      // from sl12nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl12nl1arc_sys_sleep_sync;        // from sl12nl1arc_sys_sleep_r
  logic   [2:0]           sl12nl1arc_sys_sleep_mode_sync;   // from sl12nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl12nl1arc_sys_halt_sync;         // from sl12nl1arc_sys_halt_r
  logic                   sl12nl1arc_sys_tf_halt_sync;      // from sl12nl1arc_sys_tf_halt_r

  logic                   sl12nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl12nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl12nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl12nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl12nl1arc_arc_halt_ack_a,        //9
                  sl12nl1arc_ext_arc_halt_req_a,    //8
                  sl12nl1arc_arc_run_ack_a,         //7
                  sl12nl1arc_ext_arc_run_req_a,     //6
                  sl12nl1arc_sys_sleep_r,           //5
                  sl12nl1arc_sys_sleep_mode_r,      //4:2
                  sl12nl1arc_sys_halt_r,            //1
                  sl12nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl12nl1arc_arc_halt_ack_sync,        //9
                  sl12nl1arc_ext_arc_halt_req_sync,    //8
                  sl12nl1arc_arc_run_ack_sync,         //7
                  sl12nl1arc_ext_arc_run_req_sync,     //6
                  sl12nl1arc_sys_sleep_sync,           //5
                  sl12nl1arc_sys_sleep_mode_sync,      //4:2
                  sl12nl1arc_sys_halt_sync,            //1
                  sl12nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl12nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl12nl1arc_sys_sleep_mode_sync_d1_r <= sl12nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl12nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl12nl1arc_sys_sleep_mode_sync==sl12nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl12nl1arc_sys_sleep_mode_sync_d1_r!=sl12nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl12nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl12nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl12nl1arc_sys_sleep_mode_sync_mmio_r <= sl12nl1arc_sys_sleep_mode_sync_d1_r;


logic sl12nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl12nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl12nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl12nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl12nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl12nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl12nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl12nl1arc_ext_arc_halt_req_sync_d1_r <= sl12nl1arc_ext_arc_halt_req_sync;
      sl12nl1arc_arc_halt_ack_sync_d1_r <= sl12nl1arc_arc_halt_ack_sync;
    end

  assign set_sl12nl1arc_ext_arc_halt_req_sync_flag = sl12nl1arc_ext_arc_halt_req_sync & !sl12nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl12nl1arc_ext_arc_halt_req_sync_flag = sl12nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl12nl1arc_arc_halt_ack_sync &
                                                               sl12nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl12nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl12nl1arc_ext_arc_halt_req_sync_flag)
      sl12nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl12nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl12nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl12nl1arc_ext_arc_run_req_sync_d1_r;
logic sl12nl1arc_ext_arc_run_req_sync_flag_r;
logic sl12nl1arc_arc_run_ack_sync_d1_r;
logic set_sl12nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl12nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl12nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl12nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl12nl1arc_ext_arc_run_req_sync_d1_r <= sl12nl1arc_ext_arc_run_req_sync;
      sl12nl1arc_arc_run_ack_sync_d1_r <= sl12nl1arc_arc_run_ack_sync;
    end

  assign set_sl12nl1arc_ext_arc_run_req_sync_flag = sl12nl1arc_ext_arc_run_req_sync & !sl12nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl12nl1arc_ext_arc_run_req_sync_flag = sl12nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl12nl1arc_arc_run_ack_sync &
                                                               sl12nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl12nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl12nl1arc_ext_arc_run_req_sync_flag)
      sl12nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl12nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl12nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl12nl1arc_intvbase     = arcsync_core_intvbase[13][31:10];

  assign sl12_rst_a                = core_rst_dly[13][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[13]
                                                ;

  assign sl12_clk_en               = arcsync_core_clk_en[13];

  assign sl12nl1arc_arc_halt_req = arcsync_core_halt_req[13] | sl12nl1arc_ext_arc_halt_req_sync;
  assign sl12nl1arc_arc_run_req  = arcsync_core_run_req[13] | sl12nl1arc_ext_arc_run_req_sync;

  assign sl12nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[13];  
  
  assign core_arcsync_halt_ack[13]         = sl12nl1arc_arc_halt_ack_sync & !sl12nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl12nl1arc_ext_arc_halt_ack = sl12nl1arc_arc_halt_ack_sync & sl12nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[13]          = sl12nl1arc_arc_run_ack_sync & !sl12nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl12nl1arc_ext_arc_run_ack  = sl12nl1arc_arc_run_ack_sync & sl12nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[13]        = sl12nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[13]   = sl12nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[13]         = sl12nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[13]      = sl12nl1arc_sys_tf_halt_sync;    

  assign sl12nl1arc_pwr_dwn      = arcsync_core_rst_req[13]
                                             | arcsync_core_pwr_down[13]
                                             ;
  assign core_arcsync_pmode[13]         = {2'h0, arcsync_core_pwr_down[13]};
  assign sl12nl1arc_isolate_n =   arcsync_core_isolate_n[13]; 
  assign sl12nl1arc_isolate   =   arcsync_core_isolate[13]; 
  assign sl12nl1arc_pd_mem    =   arcsync_core_pd_mem[13]; 
  assign sl12nl1arc_pd_logic  =   arcsync_core_pd_logic[13];
  assign sl12nl1arc_pd_logic1  =   arcsync_core_pd_logic1[13];
  assign sl12nl1arc_pd_logic2  =   arcsync_core_pd_logic2[13];

  // Halt
  logic                   sl13nl1arc_arc_halt_ack_sync;     // from sl13nl1arc_arc_halt_ack_a
  logic                   sl13nl1arc_ext_arc_halt_req_sync; // from sl13nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl13nl1arc_arc_run_ack_sync;      // from sl13nl1arc_arc_run_ack_a
  logic                   sl13nl1arc_ext_arc_run_req_sync;  // from sl13nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl13nl1arc_arc_rst_ack_sync;      // from sl13nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl13nl1arc_sys_sleep_sync;        // from sl13nl1arc_sys_sleep_r
  logic   [2:0]           sl13nl1arc_sys_sleep_mode_sync;   // from sl13nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl13nl1arc_sys_halt_sync;         // from sl13nl1arc_sys_halt_r
  logic                   sl13nl1arc_sys_tf_halt_sync;      // from sl13nl1arc_sys_tf_halt_r

  logic                   sl13nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl13nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl13nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl13nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl13nl1arc_arc_halt_ack_a,        //9
                  sl13nl1arc_ext_arc_halt_req_a,    //8
                  sl13nl1arc_arc_run_ack_a,         //7
                  sl13nl1arc_ext_arc_run_req_a,     //6
                  sl13nl1arc_sys_sleep_r,           //5
                  sl13nl1arc_sys_sleep_mode_r,      //4:2
                  sl13nl1arc_sys_halt_r,            //1
                  sl13nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl13nl1arc_arc_halt_ack_sync,        //9
                  sl13nl1arc_ext_arc_halt_req_sync,    //8
                  sl13nl1arc_arc_run_ack_sync,         //7
                  sl13nl1arc_ext_arc_run_req_sync,     //6
                  sl13nl1arc_sys_sleep_sync,           //5
                  sl13nl1arc_sys_sleep_mode_sync,      //4:2
                  sl13nl1arc_sys_halt_sync,            //1
                  sl13nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl13nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl13nl1arc_sys_sleep_mode_sync_d1_r <= sl13nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl13nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl13nl1arc_sys_sleep_mode_sync==sl13nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl13nl1arc_sys_sleep_mode_sync_d1_r!=sl13nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl13nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl13nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl13nl1arc_sys_sleep_mode_sync_mmio_r <= sl13nl1arc_sys_sleep_mode_sync_d1_r;


logic sl13nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl13nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl13nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl13nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl13nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl13nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl13nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl13nl1arc_ext_arc_halt_req_sync_d1_r <= sl13nl1arc_ext_arc_halt_req_sync;
      sl13nl1arc_arc_halt_ack_sync_d1_r <= sl13nl1arc_arc_halt_ack_sync;
    end

  assign set_sl13nl1arc_ext_arc_halt_req_sync_flag = sl13nl1arc_ext_arc_halt_req_sync & !sl13nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl13nl1arc_ext_arc_halt_req_sync_flag = sl13nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl13nl1arc_arc_halt_ack_sync &
                                                               sl13nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl13nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl13nl1arc_ext_arc_halt_req_sync_flag)
      sl13nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl13nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl13nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl13nl1arc_ext_arc_run_req_sync_d1_r;
logic sl13nl1arc_ext_arc_run_req_sync_flag_r;
logic sl13nl1arc_arc_run_ack_sync_d1_r;
logic set_sl13nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl13nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl13nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl13nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl13nl1arc_ext_arc_run_req_sync_d1_r <= sl13nl1arc_ext_arc_run_req_sync;
      sl13nl1arc_arc_run_ack_sync_d1_r <= sl13nl1arc_arc_run_ack_sync;
    end

  assign set_sl13nl1arc_ext_arc_run_req_sync_flag = sl13nl1arc_ext_arc_run_req_sync & !sl13nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl13nl1arc_ext_arc_run_req_sync_flag = sl13nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl13nl1arc_arc_run_ack_sync &
                                                               sl13nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl13nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl13nl1arc_ext_arc_run_req_sync_flag)
      sl13nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl13nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl13nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl13nl1arc_intvbase     = arcsync_core_intvbase[14][31:10];

  assign sl13_rst_a                = core_rst_dly[14][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[14]
                                                ;

  assign sl13_clk_en               = arcsync_core_clk_en[14];

  assign sl13nl1arc_arc_halt_req = arcsync_core_halt_req[14] | sl13nl1arc_ext_arc_halt_req_sync;
  assign sl13nl1arc_arc_run_req  = arcsync_core_run_req[14] | sl13nl1arc_ext_arc_run_req_sync;

  assign sl13nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[14];  
  
  assign core_arcsync_halt_ack[14]         = sl13nl1arc_arc_halt_ack_sync & !sl13nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl13nl1arc_ext_arc_halt_ack = sl13nl1arc_arc_halt_ack_sync & sl13nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[14]          = sl13nl1arc_arc_run_ack_sync & !sl13nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl13nl1arc_ext_arc_run_ack  = sl13nl1arc_arc_run_ack_sync & sl13nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[14]        = sl13nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[14]   = sl13nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[14]         = sl13nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[14]      = sl13nl1arc_sys_tf_halt_sync;    

  assign sl13nl1arc_pwr_dwn      = arcsync_core_rst_req[14]
                                             | arcsync_core_pwr_down[14]
                                             ;
  assign core_arcsync_pmode[14]         = {2'h0, arcsync_core_pwr_down[14]};
  assign sl13nl1arc_isolate_n =   arcsync_core_isolate_n[14]; 
  assign sl13nl1arc_isolate   =   arcsync_core_isolate[14]; 
  assign sl13nl1arc_pd_mem    =   arcsync_core_pd_mem[14]; 
  assign sl13nl1arc_pd_logic  =   arcsync_core_pd_logic[14];
  assign sl13nl1arc_pd_logic1  =   arcsync_core_pd_logic1[14];
  assign sl13nl1arc_pd_logic2  =   arcsync_core_pd_logic2[14];

  // Halt
  logic                   sl14nl1arc_arc_halt_ack_sync;     // from sl14nl1arc_arc_halt_ack_a
  logic                   sl14nl1arc_ext_arc_halt_req_sync; // from sl14nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl14nl1arc_arc_run_ack_sync;      // from sl14nl1arc_arc_run_ack_a
  logic                   sl14nl1arc_ext_arc_run_req_sync;  // from sl14nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl14nl1arc_arc_rst_ack_sync;      // from sl14nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl14nl1arc_sys_sleep_sync;        // from sl14nl1arc_sys_sleep_r
  logic   [2:0]           sl14nl1arc_sys_sleep_mode_sync;   // from sl14nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl14nl1arc_sys_halt_sync;         // from sl14nl1arc_sys_halt_r
  logic                   sl14nl1arc_sys_tf_halt_sync;      // from sl14nl1arc_sys_tf_halt_r

  logic                   sl14nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl14nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl14nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl14nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl14nl1arc_arc_halt_ack_a,        //9
                  sl14nl1arc_ext_arc_halt_req_a,    //8
                  sl14nl1arc_arc_run_ack_a,         //7
                  sl14nl1arc_ext_arc_run_req_a,     //6
                  sl14nl1arc_sys_sleep_r,           //5
                  sl14nl1arc_sys_sleep_mode_r,      //4:2
                  sl14nl1arc_sys_halt_r,            //1
                  sl14nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl14nl1arc_arc_halt_ack_sync,        //9
                  sl14nl1arc_ext_arc_halt_req_sync,    //8
                  sl14nl1arc_arc_run_ack_sync,         //7
                  sl14nl1arc_ext_arc_run_req_sync,     //6
                  sl14nl1arc_sys_sleep_sync,           //5
                  sl14nl1arc_sys_sleep_mode_sync,      //4:2
                  sl14nl1arc_sys_halt_sync,            //1
                  sl14nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl14nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl14nl1arc_sys_sleep_mode_sync_d1_r <= sl14nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl14nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl14nl1arc_sys_sleep_mode_sync==sl14nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl14nl1arc_sys_sleep_mode_sync_d1_r!=sl14nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl14nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl14nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl14nl1arc_sys_sleep_mode_sync_mmio_r <= sl14nl1arc_sys_sleep_mode_sync_d1_r;


logic sl14nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl14nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl14nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl14nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl14nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl14nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl14nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl14nl1arc_ext_arc_halt_req_sync_d1_r <= sl14nl1arc_ext_arc_halt_req_sync;
      sl14nl1arc_arc_halt_ack_sync_d1_r <= sl14nl1arc_arc_halt_ack_sync;
    end

  assign set_sl14nl1arc_ext_arc_halt_req_sync_flag = sl14nl1arc_ext_arc_halt_req_sync & !sl14nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl14nl1arc_ext_arc_halt_req_sync_flag = sl14nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl14nl1arc_arc_halt_ack_sync &
                                                               sl14nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl14nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl14nl1arc_ext_arc_halt_req_sync_flag)
      sl14nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl14nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl14nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl14nl1arc_ext_arc_run_req_sync_d1_r;
logic sl14nl1arc_ext_arc_run_req_sync_flag_r;
logic sl14nl1arc_arc_run_ack_sync_d1_r;
logic set_sl14nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl14nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl14nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl14nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl14nl1arc_ext_arc_run_req_sync_d1_r <= sl14nl1arc_ext_arc_run_req_sync;
      sl14nl1arc_arc_run_ack_sync_d1_r <= sl14nl1arc_arc_run_ack_sync;
    end

  assign set_sl14nl1arc_ext_arc_run_req_sync_flag = sl14nl1arc_ext_arc_run_req_sync & !sl14nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl14nl1arc_ext_arc_run_req_sync_flag = sl14nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl14nl1arc_arc_run_ack_sync &
                                                               sl14nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl14nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl14nl1arc_ext_arc_run_req_sync_flag)
      sl14nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl14nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl14nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl14nl1arc_intvbase     = arcsync_core_intvbase[15][31:10];

  assign sl14_rst_a                = core_rst_dly[15][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[15]
                                                ;

  assign sl14_clk_en               = arcsync_core_clk_en[15];

  assign sl14nl1arc_arc_halt_req = arcsync_core_halt_req[15] | sl14nl1arc_ext_arc_halt_req_sync;
  assign sl14nl1arc_arc_run_req  = arcsync_core_run_req[15] | sl14nl1arc_ext_arc_run_req_sync;

  assign sl14nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[15];  
  
  assign core_arcsync_halt_ack[15]         = sl14nl1arc_arc_halt_ack_sync & !sl14nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl14nl1arc_ext_arc_halt_ack = sl14nl1arc_arc_halt_ack_sync & sl14nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[15]          = sl14nl1arc_arc_run_ack_sync & !sl14nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl14nl1arc_ext_arc_run_ack  = sl14nl1arc_arc_run_ack_sync & sl14nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[15]        = sl14nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[15]   = sl14nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[15]         = sl14nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[15]      = sl14nl1arc_sys_tf_halt_sync;    

  assign sl14nl1arc_pwr_dwn      = arcsync_core_rst_req[15]
                                             | arcsync_core_pwr_down[15]
                                             ;
  assign core_arcsync_pmode[15]         = {2'h0, arcsync_core_pwr_down[15]};
  assign sl14nl1arc_isolate_n =   arcsync_core_isolate_n[15]; 
  assign sl14nl1arc_isolate   =   arcsync_core_isolate[15]; 
  assign sl14nl1arc_pd_mem    =   arcsync_core_pd_mem[15]; 
  assign sl14nl1arc_pd_logic  =   arcsync_core_pd_logic[15];
  assign sl14nl1arc_pd_logic1  =   arcsync_core_pd_logic1[15];
  assign sl14nl1arc_pd_logic2  =   arcsync_core_pd_logic2[15];

  // Halt
  logic                   sl15nl1arc_arc_halt_ack_sync;     // from sl15nl1arc_arc_halt_ack_a
  logic                   sl15nl1arc_ext_arc_halt_req_sync; // from sl15nl1arc_ext_arc_halt_req_a
  // Run                                                 
  logic                   sl15nl1arc_arc_run_ack_sync;      // from sl15nl1arc_arc_run_ack_a
  logic                   sl15nl1arc_ext_arc_run_req_sync;  // from sl15nl1arc_ext_arc_run_req_a
  // Reset                               
  logic                   sl15nl1arc_arc_rst_ack_sync;      // from sl15nl1arc_arc_rst_ack_a
  // Status                                              
  logic                   sl15nl1arc_sys_sleep_sync;        // from sl15nl1arc_sys_sleep_r
  logic   [2:0]           sl15nl1arc_sys_sleep_mode_sync;   // from sl15nl1arc_sys_sleep_mode_r[2:0]
  logic                   sl15nl1arc_sys_halt_sync;         // from sl15nl1arc_sys_halt_r
  logic                   sl15nl1arc_sys_tf_halt_sync;      // from sl15nl1arc_sys_tf_halt_r

  logic                   sl15nl1arc_update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               sl15nl1arc_sys_sleep_mode_sync_d1_r;
  reg [2:0]               sl15nl1arc_sys_sleep_mode_sync_mmio_r;



  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2), .WIDTH(10)
  ) u_sl15nl1arc_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                             //Bit position
    .din        ({
                  sl15nl1arc_arc_halt_ack_a,        //9
                  sl15nl1arc_ext_arc_halt_req_a,    //8
                  sl15nl1arc_arc_run_ack_a,         //7
                  sl15nl1arc_ext_arc_run_req_a,     //6
                  sl15nl1arc_sys_sleep_r,           //5
                  sl15nl1arc_sys_sleep_mode_r,      //4:2
                  sl15nl1arc_sys_halt_r,            //1
                  sl15nl1arc_sys_tf_halt_r          //0
                  }),                                              //Bit position
    .dout       ({
                  sl15nl1arc_arc_halt_ack_sync,        //9
                  sl15nl1arc_ext_arc_halt_req_sync,    //8
                  sl15nl1arc_arc_run_ack_sync,         //7
                  sl15nl1arc_ext_arc_run_req_sync,     //6
                  sl15nl1arc_sys_sleep_sync,           //5
                  sl15nl1arc_sys_sleep_mode_sync,      //4:2
                  sl15nl1arc_sys_halt_sync,            //1
                  sl15nl1arc_sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl15nl1arc_sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      sl15nl1arc_sys_sleep_mode_sync_d1_r <= sl15nl1arc_sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign sl15nl1arc_update_sys_sleep_mode_sync_mmio_r = (sl15nl1arc_sys_sleep_mode_sync==sl15nl1arc_sys_sleep_mode_sync_d1_r) &
                                                           (sl15nl1arc_sys_sleep_mode_sync_d1_r!=sl15nl1arc_sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl15nl1arc_sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (sl15nl1arc_update_sys_sleep_mode_sync_mmio_r)
      sl15nl1arc_sys_sleep_mode_sync_mmio_r <= sl15nl1arc_sys_sleep_mode_sync_d1_r;


logic sl15nl1arc_ext_arc_halt_req_sync_d1_r;
logic sl15nl1arc_ext_arc_halt_req_sync_flag_r;
logic sl15nl1arc_arc_halt_ack_sync_d1_r;
logic set_sl15nl1arc_ext_arc_halt_req_sync_flag;
logic clr_sl15nl1arc_ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl15nl1arc_ext_arc_halt_req_sync_d1_r <= 1'b0;
      sl15nl1arc_arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl15nl1arc_ext_arc_halt_req_sync_d1_r <= sl15nl1arc_ext_arc_halt_req_sync;
      sl15nl1arc_arc_halt_ack_sync_d1_r <= sl15nl1arc_arc_halt_ack_sync;
    end

  assign set_sl15nl1arc_ext_arc_halt_req_sync_flag = sl15nl1arc_ext_arc_halt_req_sync & !sl15nl1arc_ext_arc_halt_req_sync_d1_r;
  assign clr_sl15nl1arc_ext_arc_halt_req_sync_flag = sl15nl1arc_ext_arc_halt_req_sync_flag_r &
                                                               !sl15nl1arc_arc_halt_ack_sync &
                                                               sl15nl1arc_arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl15nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_sl15nl1arc_ext_arc_halt_req_sync_flag)
      sl15nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_sl15nl1arc_ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl15nl1arc_ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


logic sl15nl1arc_ext_arc_run_req_sync_d1_r;
logic sl15nl1arc_ext_arc_run_req_sync_flag_r;
logic sl15nl1arc_arc_run_ack_sync_d1_r;
logic set_sl15nl1arc_ext_arc_run_req_sync_flag;
logic clr_sl15nl1arc_ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      sl15nl1arc_ext_arc_run_req_sync_d1_r <= 1'b0;
      sl15nl1arc_arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      sl15nl1arc_ext_arc_run_req_sync_d1_r <= sl15nl1arc_ext_arc_run_req_sync;
      sl15nl1arc_arc_run_ack_sync_d1_r <= sl15nl1arc_arc_run_ack_sync;
    end

  assign set_sl15nl1arc_ext_arc_run_req_sync_flag = sl15nl1arc_ext_arc_run_req_sync & !sl15nl1arc_ext_arc_run_req_sync_d1_r;
  assign clr_sl15nl1arc_ext_arc_run_req_sync_flag = sl15nl1arc_ext_arc_run_req_sync_flag_r &
                                                               !sl15nl1arc_arc_run_ack_sync &
                                                               sl15nl1arc_arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      sl15nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_sl15nl1arc_ext_arc_run_req_sync_flag)
      sl15nl1arc_ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_sl15nl1arc_ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      sl15nl1arc_ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03


  assign sl15nl1arc_intvbase     = arcsync_core_intvbase[16][31:10];

  assign sl15_rst_a                = core_rst_dly[16][PWR_DWN_TO_RST_A_DLY-1] 
                                                | arcsync_core_pu_rst[16]
                                                ;

  assign sl15_clk_en               = arcsync_core_clk_en[16];

  assign sl15nl1arc_arc_halt_req = arcsync_core_halt_req[16] | sl15nl1arc_ext_arc_halt_req_sync;
  assign sl15nl1arc_arc_run_req  = arcsync_core_run_req[16] | sl15nl1arc_ext_arc_run_req_sync;

  assign sl15nl1arc_arc_irq[`ARCSYNC_NUM_IRQ_PER_CORE:0]      = arcsync_core_irq[16];  
  
  assign core_arcsync_halt_ack[16]         = sl15nl1arc_arc_halt_ack_sync & !sl15nl1arc_ext_arc_halt_req_sync_flag_r;   
  assign sl15nl1arc_ext_arc_halt_ack = sl15nl1arc_arc_halt_ack_sync & sl15nl1arc_ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[16]          = sl15nl1arc_arc_run_ack_sync & !sl15nl1arc_ext_arc_run_req_sync_flag_r;    
  assign sl15nl1arc_ext_arc_run_ack  = sl15nl1arc_arc_run_ack_sync & sl15nl1arc_ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[16]        = sl15nl1arc_sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[16]   = sl15nl1arc_sys_sleep_mode_sync_mmio_r; 
  assign core_arcsync_sys_halt[16]         = sl15nl1arc_sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[16]      = sl15nl1arc_sys_tf_halt_sync;    

  assign sl15nl1arc_pwr_dwn      = arcsync_core_rst_req[16]
                                             | arcsync_core_pwr_down[16]
                                             ;
  assign core_arcsync_pmode[16]         = {2'h0, arcsync_core_pwr_down[16]};
  assign sl15nl1arc_isolate_n =   arcsync_core_isolate_n[16]; 
  assign sl15nl1arc_isolate   =   arcsync_core_isolate[16]; 
  assign sl15nl1arc_pd_mem    =   arcsync_core_pd_mem[16]; 
  assign sl15nl1arc_pd_logic  =   arcsync_core_pd_logic[16];
  assign sl15nl1arc_pd_logic1  =   arcsync_core_pd_logic1[16];
  assign sl15nl1arc_pd_logic2  =   arcsync_core_pd_logic2[16];






// DBG: Connections for undefined cores
  //#18#32#18#
  assign core_arcsync_halt_ack[18]       =1'b0; 
  assign core_arcsync_run_ack[18]        =1'b0; 
  assign core_arcsync_sys_sleep[18]      =1'b0;
  assign core_arcsync_sys_sleep_mode[18] =3'b0;
  assign core_arcsync_sys_halt[18]       =1'b0; 
  assign core_arcsync_sys_tf_halt[18]    =1'b0;
 
  assign core_arcsync_pmode[18]        = 3'b0; 
  //#18#32#19#
  assign core_arcsync_halt_ack[19]       =1'b0; 
  assign core_arcsync_run_ack[19]        =1'b0; 
  assign core_arcsync_sys_sleep[19]      =1'b0;
  assign core_arcsync_sys_sleep_mode[19] =3'b0;
  assign core_arcsync_sys_halt[19]       =1'b0; 
  assign core_arcsync_sys_tf_halt[19]    =1'b0;
 
  assign core_arcsync_pmode[19]        = 3'b0; 
  //#18#32#20#
  assign core_arcsync_halt_ack[20]       =1'b0; 
  assign core_arcsync_run_ack[20]        =1'b0; 
  assign core_arcsync_sys_sleep[20]      =1'b0;
  assign core_arcsync_sys_sleep_mode[20] =3'b0;
  assign core_arcsync_sys_halt[20]       =1'b0; 
  assign core_arcsync_sys_tf_halt[20]    =1'b0;
 
  assign core_arcsync_pmode[20]        = 3'b0; 
  //#18#32#21#
  assign core_arcsync_halt_ack[21]       =1'b0; 
  assign core_arcsync_run_ack[21]        =1'b0; 
  assign core_arcsync_sys_sleep[21]      =1'b0;
  assign core_arcsync_sys_sleep_mode[21] =3'b0;
  assign core_arcsync_sys_halt[21]       =1'b0; 
  assign core_arcsync_sys_tf_halt[21]    =1'b0;
 
  assign core_arcsync_pmode[21]        = 3'b0; 
  //#18#32#22#
  assign core_arcsync_halt_ack[22]       =1'b0; 
  assign core_arcsync_run_ack[22]        =1'b0; 
  assign core_arcsync_sys_sleep[22]      =1'b0;
  assign core_arcsync_sys_sleep_mode[22] =3'b0;
  assign core_arcsync_sys_halt[22]       =1'b0; 
  assign core_arcsync_sys_tf_halt[22]    =1'b0;
 
  assign core_arcsync_pmode[22]        = 3'b0; 
  //#18#32#23#
  assign core_arcsync_halt_ack[23]       =1'b0; 
  assign core_arcsync_run_ack[23]        =1'b0; 
  assign core_arcsync_sys_sleep[23]      =1'b0;
  assign core_arcsync_sys_sleep_mode[23] =3'b0;
  assign core_arcsync_sys_halt[23]       =1'b0; 
  assign core_arcsync_sys_tf_halt[23]    =1'b0;
 
  assign core_arcsync_pmode[23]        = 3'b0; 
  //#18#32#24#
  assign core_arcsync_halt_ack[24]       =1'b0; 
  assign core_arcsync_run_ack[24]        =1'b0; 
  assign core_arcsync_sys_sleep[24]      =1'b0;
  assign core_arcsync_sys_sleep_mode[24] =3'b0;
  assign core_arcsync_sys_halt[24]       =1'b0; 
  assign core_arcsync_sys_tf_halt[24]    =1'b0;
 
  assign core_arcsync_pmode[24]        = 3'b0; 
  //#18#32#25#
  assign core_arcsync_halt_ack[25]       =1'b0; 
  assign core_arcsync_run_ack[25]        =1'b0; 
  assign core_arcsync_sys_sleep[25]      =1'b0;
  assign core_arcsync_sys_sleep_mode[25] =3'b0;
  assign core_arcsync_sys_halt[25]       =1'b0; 
  assign core_arcsync_sys_tf_halt[25]    =1'b0;
 
  assign core_arcsync_pmode[25]        = 3'b0; 
  //#18#32#26#
  assign core_arcsync_halt_ack[26]       =1'b0; 
  assign core_arcsync_run_ack[26]        =1'b0; 
  assign core_arcsync_sys_sleep[26]      =1'b0;
  assign core_arcsync_sys_sleep_mode[26] =3'b0;
  assign core_arcsync_sys_halt[26]       =1'b0; 
  assign core_arcsync_sys_tf_halt[26]    =1'b0;
 
  assign core_arcsync_pmode[26]        = 3'b0; 
  //#18#32#27#
  assign core_arcsync_halt_ack[27]       =1'b0; 
  assign core_arcsync_run_ack[27]        =1'b0; 
  assign core_arcsync_sys_sleep[27]      =1'b0;
  assign core_arcsync_sys_sleep_mode[27] =3'b0;
  assign core_arcsync_sys_halt[27]       =1'b0; 
  assign core_arcsync_sys_tf_halt[27]    =1'b0;
 
  assign core_arcsync_pmode[27]        = 3'b0; 
  //#18#32#28#
  assign core_arcsync_halt_ack[28]       =1'b0; 
  assign core_arcsync_run_ack[28]        =1'b0; 
  assign core_arcsync_sys_sleep[28]      =1'b0;
  assign core_arcsync_sys_sleep_mode[28] =3'b0;
  assign core_arcsync_sys_halt[28]       =1'b0; 
  assign core_arcsync_sys_tf_halt[28]    =1'b0;
 
  assign core_arcsync_pmode[28]        = 3'b0; 
  //#18#32#29#
  assign core_arcsync_halt_ack[29]       =1'b0; 
  assign core_arcsync_run_ack[29]        =1'b0; 
  assign core_arcsync_sys_sleep[29]      =1'b0;
  assign core_arcsync_sys_sleep_mode[29] =3'b0;
  assign core_arcsync_sys_halt[29]       =1'b0; 
  assign core_arcsync_sys_tf_halt[29]    =1'b0;
 
  assign core_arcsync_pmode[29]        = 3'b0; 
  //#18#32#30#
  assign core_arcsync_halt_ack[30]       =1'b0; 
  assign core_arcsync_run_ack[30]        =1'b0; 
  assign core_arcsync_sys_sleep[30]      =1'b0;
  assign core_arcsync_sys_sleep_mode[30] =3'b0;
  assign core_arcsync_sys_halt[30]       =1'b0; 
  assign core_arcsync_sys_tf_halt[30]    =1'b0;
 
  assign core_arcsync_pmode[30]        = 3'b0; 
  //#18#32#31#
  assign core_arcsync_halt_ack[31]       =1'b0; 
  assign core_arcsync_run_ack[31]        =1'b0; 
  assign core_arcsync_sys_sleep[31]      =1'b0;
  assign core_arcsync_sys_sleep_mode[31] =3'b0;
  assign core_arcsync_sys_halt[31]       =1'b0; 
  assign core_arcsync_sys_tf_halt[31]    =1'b0;
 
  assign core_arcsync_pmode[31]        = 3'b0; 







































// VPX cluster
  assign v0clusternum   = 1;     
  assign v0periph_addr_base = arcsync_core_periph_addr_base[1];
  assign v0csm_addr_base    = arcsync_core_csm_addr_base[1];


  //PDM

  // Halt
  logic                   v0c0arc_halt_ack_sync;     // from v0c0arc_halt_ack_a
  logic                   v0c0ext_arc_halt_req_sync; // from v0c0ext_arc_halt_req_a
  // Run                                                 
  logic                   v0c0arc_run_ack_sync;      // from v0c0arc_run_ack_a
  logic                   v0c0ext_arc_run_req_sync;  // from v0c0ext_arc_run_req_a
  // Status                                              
  logic                   v0c0sys_sleep_sync;        // from v0c0sys_sleep_r
  logic   [2:0]           v0c0sys_sleep_mode_sync;   // from v0c0sys_sleep_mode_r[2:0]
  logic                   v0c0sys_halt_sync;         // from v0c0sys_halt_r
  logic                   v0c0sys_tf_halt_sync;      // from v0c0sys_tf_halt_r

  logic                   v0c0update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               v0c0sys_sleep_mode_sync_d1_r;
  reg [2:0]               v0c0sys_sleep_mode_sync_mmio_r;

  logic [2:0]             v0c0pmode_sync;
  logic                   v0c0update_pmode_sync_mmio_r;
  reg [2:0]               v0c0pmode_sync_d1_r;
  reg [2:0]               v0c0pmode_sync_mmio_r;

  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2),
    .WIDTH(13)
  ) u_v0c0arcsync_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                    //Bit position
    .din        ({
                  v0c0pmode,                 //12:10
                  v0c0arc_halt_ack_a,        //9
                  v0c0ext_arc_halt_req_a,    //8
                  v0c0arc_run_ack_a,         //7
                  v0c0ext_arc_run_req_a,     //6
                  v0c0sys_sleep_r,           //5
                  v0c0sys_sleep_mode_r,      //4:2
                  v0c0sys_halt_r,            //1
                  v0c0sys_tf_halt_r          //0
                  }),                                     //Bit position
    .dout       ({
	              v0c0pmode_sync,               //12:10
                  v0c0arc_halt_ack_sync,        //9
                  v0c0ext_arc_halt_req_sync,    //8
                  v0c0arc_run_ack_sync,         //7
                  v0c0ext_arc_run_req_sync,     //6
                  v0c0sys_sleep_sync,           //5
                  v0c0sys_sleep_mode_sync,      //4:2
                  v0c0sys_halt_sync,            //1
                  v0c0sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c0sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      v0c0sys_sleep_mode_sync_d1_r <= v0c0sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign v0c0update_sys_sleep_mode_sync_mmio_r = (v0c0sys_sleep_mode_sync==v0c0sys_sleep_mode_sync_d1_r) &
                                                       (v0c0sys_sleep_mode_sync_d1_r!=v0c0sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c0sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (v0c0update_sys_sleep_mode_sync_mmio_r)
      v0c0sys_sleep_mode_sync_mmio_r <= v0c0sys_sleep_mode_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c0pmode_sync_d1_r <= 3'h0;
    else
      v0c0pmode_sync_d1_r <= v0c0pmode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign v0c0update_pmode_sync_mmio_r = (v0c0pmode_sync==v0c0pmode_sync_d1_r) &
                                                  (v0c0pmode_sync_d1_r!=v0c0pmode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c0pmode_sync_mmio_r <= 3'h0;
    else if (v0c0update_pmode_sync_mmio_r)
      v0c0pmode_sync_mmio_r <= v0c0pmode_sync_d1_r;

logic v0c0ext_arc_halt_req_sync_d1_r;
logic v0c0ext_arc_halt_req_sync_flag_r;
logic v0c0arc_halt_ack_sync_d1_r;
logic set_v0c0ext_arc_halt_req_sync_flag;
logic clr_v0c0ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      v0c0ext_arc_halt_req_sync_d1_r <= 1'b0;
      v0c0arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      v0c0ext_arc_halt_req_sync_d1_r <= v0c0ext_arc_halt_req_sync;
      v0c0arc_halt_ack_sync_d1_r <= v0c0arc_halt_ack_sync;
    end

  assign set_v0c0ext_arc_halt_req_sync_flag = v0c0ext_arc_halt_req_sync & !v0c0ext_arc_halt_req_sync_d1_r;
  assign clr_v0c0ext_arc_halt_req_sync_flag = v0c0ext_arc_halt_req_sync_flag_r &
                                                               !v0c0arc_halt_ack_sync &
                                                               v0c0arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c0ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_v0c0ext_arc_halt_req_sync_flag)
      v0c0ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_v0c0ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      v0c0ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03

logic v0c0ext_arc_run_req_sync_d1_r;
logic v0c0ext_arc_run_req_sync_flag_r;
logic v0c0arc_run_ack_sync_d1_r;
logic set_v0c0ext_arc_run_req_sync_flag;
logic clr_v0c0ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      v0c0ext_arc_run_req_sync_d1_r <= 1'b0;
      v0c0arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      v0c0ext_arc_run_req_sync_d1_r <= v0c0ext_arc_run_req_sync;
      v0c0arc_run_ack_sync_d1_r <= v0c0arc_run_ack_sync;
    end

  assign set_v0c0ext_arc_run_req_sync_flag = v0c0ext_arc_run_req_sync & !v0c0ext_arc_run_req_sync_d1_r;
  assign clr_v0c0ext_arc_run_req_sync_flag = v0c0ext_arc_run_req_sync_flag_r &
                                                               !v0c0arc_run_ack_sync &
                                                               v0c0arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c0ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_v0c0ext_arc_run_req_sync_flag)
      v0c0ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_v0c0ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      v0c0ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03




  assign v0c0arcnum   = 0;        
  assign v0c0intvbase = arcsync_core_intvbase[32][31:10];

  assign v0c0rst_a  = arcsync_core_rst_req[32] 
                              | arcsync_core_pu_rst[32]
                             ;
  assign v0c0clk_en = arcsync_core_clk_en[32];

  assign v0c0arc_halt_req = arcsync_core_halt_req[32] | v0c0ext_arc_halt_req_sync;   
  assign v0c0arc_run_req  = arcsync_core_run_req[32] | v0c0ext_arc_run_req_sync; 

  // Split VPX irq & event
  assign v0c0arc_irq0_a = arcsync_core_irq[32][0];
  assign v0c0arc_irq1_a = arcsync_core_irq[32][1];
  assign v0c0arc_event0_a = arcsync_core_event[32][0];
  assign v0c0arc_event1_a = arcsync_core_event[32][1];

  assign core_arcsync_halt_ack[32]       = v0c0arc_halt_ack_sync & !v0c0ext_arc_halt_req_sync_flag_r;   
  assign v0c0ext_arc_halt_ack        = v0c0arc_halt_ack_sync & v0c0ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[32]        = v0c0arc_run_ack_sync & !v0c0ext_arc_run_req_sync_flag_r;    
  assign v0c0ext_arc_run_ack         = v0c0arc_run_ack_sync & v0c0ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[32]      = v0c0sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[32] = v0c0sys_sleep_mode_sync_mmio_r;
  assign core_arcsync_sys_halt[32]       = v0c0sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[32]    = v0c0sys_tf_halt_sync;  

  assign v0c0_pwr_dwn        =   1'b0
                                       ||  arcsync_core_pwr_down[32]
                                       ;
  assign core_arcsync_pmode[32]        = v0c0pmode_sync_mmio_r;
  // The PMU mode of vpx is the same as npx
  assign v0c0_isolate_n      =   arcsync_core_isolate_n[32]; 
  assign v0c0_isolate        =   arcsync_core_isolate[32]; 
  assign v0c0_pd_mem         =   arcsync_core_pd_mem[32]; 
  assign v0c0_pd_logic       =   arcsync_core_pd_logic[32];
  assign v0c0_pd_logic1      =   arcsync_core_pd_logic1[32];
  assign v0c0_pd_logic2      =   arcsync_core_pd_logic2[32];
  assign v0c0_pu_rst         =   arcsync_core_pu_rst[32]; 


  //PDM

  // Halt
  logic                   v0c1arc_halt_ack_sync;     // from v0c1arc_halt_ack_a
  logic                   v0c1ext_arc_halt_req_sync; // from v0c1ext_arc_halt_req_a
  // Run                                                 
  logic                   v0c1arc_run_ack_sync;      // from v0c1arc_run_ack_a
  logic                   v0c1ext_arc_run_req_sync;  // from v0c1ext_arc_run_req_a
  // Status                                              
  logic                   v0c1sys_sleep_sync;        // from v0c1sys_sleep_r
  logic   [2:0]           v0c1sys_sleep_mode_sync;   // from v0c1sys_sleep_mode_r[2:0]
  logic                   v0c1sys_halt_sync;         // from v0c1sys_halt_r
  logic                   v0c1sys_tf_halt_sync;      // from v0c1sys_tf_halt_r

  logic                   v0c1update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               v0c1sys_sleep_mode_sync_d1_r;
  reg [2:0]               v0c1sys_sleep_mode_sync_mmio_r;

  logic [2:0]             v0c1pmode_sync;
  logic                   v0c1update_pmode_sync_mmio_r;
  reg [2:0]               v0c1pmode_sync_d1_r;
  reg [2:0]               v0c1pmode_sync_mmio_r;

  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2),
    .WIDTH(13)
  ) u_v0c1arcsync_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                    //Bit position
    .din        ({
                  v0c1pmode,                 //12:10
                  v0c1arc_halt_ack_a,        //9
                  v0c1ext_arc_halt_req_a,    //8
                  v0c1arc_run_ack_a,         //7
                  v0c1ext_arc_run_req_a,     //6
                  v0c1sys_sleep_r,           //5
                  v0c1sys_sleep_mode_r,      //4:2
                  v0c1sys_halt_r,            //1
                  v0c1sys_tf_halt_r          //0
                  }),                                     //Bit position
    .dout       ({
	              v0c1pmode_sync,               //12:10
                  v0c1arc_halt_ack_sync,        //9
                  v0c1ext_arc_halt_req_sync,    //8
                  v0c1arc_run_ack_sync,         //7
                  v0c1ext_arc_run_req_sync,     //6
                  v0c1sys_sleep_sync,           //5
                  v0c1sys_sleep_mode_sync,      //4:2
                  v0c1sys_halt_sync,            //1
                  v0c1sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c1sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      v0c1sys_sleep_mode_sync_d1_r <= v0c1sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign v0c1update_sys_sleep_mode_sync_mmio_r = (v0c1sys_sleep_mode_sync==v0c1sys_sleep_mode_sync_d1_r) &
                                                       (v0c1sys_sleep_mode_sync_d1_r!=v0c1sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c1sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (v0c1update_sys_sleep_mode_sync_mmio_r)
      v0c1sys_sleep_mode_sync_mmio_r <= v0c1sys_sleep_mode_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c1pmode_sync_d1_r <= 3'h0;
    else
      v0c1pmode_sync_d1_r <= v0c1pmode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign v0c1update_pmode_sync_mmio_r = (v0c1pmode_sync==v0c1pmode_sync_d1_r) &
                                                  (v0c1pmode_sync_d1_r!=v0c1pmode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c1pmode_sync_mmio_r <= 3'h0;
    else if (v0c1update_pmode_sync_mmio_r)
      v0c1pmode_sync_mmio_r <= v0c1pmode_sync_d1_r;

logic v0c1ext_arc_halt_req_sync_d1_r;
logic v0c1ext_arc_halt_req_sync_flag_r;
logic v0c1arc_halt_ack_sync_d1_r;
logic set_v0c1ext_arc_halt_req_sync_flag;
logic clr_v0c1ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      v0c1ext_arc_halt_req_sync_d1_r <= 1'b0;
      v0c1arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      v0c1ext_arc_halt_req_sync_d1_r <= v0c1ext_arc_halt_req_sync;
      v0c1arc_halt_ack_sync_d1_r <= v0c1arc_halt_ack_sync;
    end

  assign set_v0c1ext_arc_halt_req_sync_flag = v0c1ext_arc_halt_req_sync & !v0c1ext_arc_halt_req_sync_d1_r;
  assign clr_v0c1ext_arc_halt_req_sync_flag = v0c1ext_arc_halt_req_sync_flag_r &
                                                               !v0c1arc_halt_ack_sync &
                                                               v0c1arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c1ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_v0c1ext_arc_halt_req_sync_flag)
      v0c1ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_v0c1ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      v0c1ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03

logic v0c1ext_arc_run_req_sync_d1_r;
logic v0c1ext_arc_run_req_sync_flag_r;
logic v0c1arc_run_ack_sync_d1_r;
logic set_v0c1ext_arc_run_req_sync_flag;
logic clr_v0c1ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      v0c1ext_arc_run_req_sync_d1_r <= 1'b0;
      v0c1arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      v0c1ext_arc_run_req_sync_d1_r <= v0c1ext_arc_run_req_sync;
      v0c1arc_run_ack_sync_d1_r <= v0c1arc_run_ack_sync;
    end

  assign set_v0c1ext_arc_run_req_sync_flag = v0c1ext_arc_run_req_sync & !v0c1ext_arc_run_req_sync_d1_r;
  assign clr_v0c1ext_arc_run_req_sync_flag = v0c1ext_arc_run_req_sync_flag_r &
                                                               !v0c1arc_run_ack_sync &
                                                               v0c1arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c1ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_v0c1ext_arc_run_req_sync_flag)
      v0c1ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_v0c1ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      v0c1ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03




  assign v0c1arcnum   = 1;        
  assign v0c1intvbase = arcsync_core_intvbase[33][31:10];

  assign v0c1rst_a  = arcsync_core_rst_req[33] 
                              | arcsync_core_pu_rst[33]
                             ;
  assign v0c1clk_en = arcsync_core_clk_en[33];

  assign v0c1arc_halt_req = arcsync_core_halt_req[33] | v0c1ext_arc_halt_req_sync;   
  assign v0c1arc_run_req  = arcsync_core_run_req[33] | v0c1ext_arc_run_req_sync; 

  // Split VPX irq & event
  assign v0c1arc_irq0_a = arcsync_core_irq[33][0];
  assign v0c1arc_irq1_a = arcsync_core_irq[33][1];
  assign v0c1arc_event0_a = arcsync_core_event[33][0];
  assign v0c1arc_event1_a = arcsync_core_event[33][1];

  assign core_arcsync_halt_ack[33]       = v0c1arc_halt_ack_sync & !v0c1ext_arc_halt_req_sync_flag_r;   
  assign v0c1ext_arc_halt_ack        = v0c1arc_halt_ack_sync & v0c1ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[33]        = v0c1arc_run_ack_sync & !v0c1ext_arc_run_req_sync_flag_r;    
  assign v0c1ext_arc_run_ack         = v0c1arc_run_ack_sync & v0c1ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[33]      = v0c1sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[33] = v0c1sys_sleep_mode_sync_mmio_r;
  assign core_arcsync_sys_halt[33]       = v0c1sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[33]    = v0c1sys_tf_halt_sync;  

  assign v0c1_pwr_dwn        =   1'b0
                                       ||  arcsync_core_pwr_down[33]
                                       ;
  assign core_arcsync_pmode[33]        = v0c1pmode_sync_mmio_r;
  // The PMU mode of vpx is the same as npx
  assign v0c1_isolate_n      =   arcsync_core_isolate_n[33]; 
  assign v0c1_isolate        =   arcsync_core_isolate[33]; 
  assign v0c1_pd_mem         =   arcsync_core_pd_mem[33]; 
  assign v0c1_pd_logic       =   arcsync_core_pd_logic[33];
  assign v0c1_pd_logic1      =   arcsync_core_pd_logic1[33];
  assign v0c1_pd_logic2      =   arcsync_core_pd_logic2[33];
  assign v0c1_pu_rst         =   arcsync_core_pu_rst[33]; 


  //PDM

  // Halt
  logic                   v0c2arc_halt_ack_sync;     // from v0c2arc_halt_ack_a
  logic                   v0c2ext_arc_halt_req_sync; // from v0c2ext_arc_halt_req_a
  // Run                                                 
  logic                   v0c2arc_run_ack_sync;      // from v0c2arc_run_ack_a
  logic                   v0c2ext_arc_run_req_sync;  // from v0c2ext_arc_run_req_a
  // Status                                              
  logic                   v0c2sys_sleep_sync;        // from v0c2sys_sleep_r
  logic   [2:0]           v0c2sys_sleep_mode_sync;   // from v0c2sys_sleep_mode_r[2:0]
  logic                   v0c2sys_halt_sync;         // from v0c2sys_halt_r
  logic                   v0c2sys_tf_halt_sync;      // from v0c2sys_tf_halt_r

  logic                   v0c2update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               v0c2sys_sleep_mode_sync_d1_r;
  reg [2:0]               v0c2sys_sleep_mode_sync_mmio_r;

  logic [2:0]             v0c2pmode_sync;
  logic                   v0c2update_pmode_sync_mmio_r;
  reg [2:0]               v0c2pmode_sync_d1_r;
  reg [2:0]               v0c2pmode_sync_mmio_r;

  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2),
    .WIDTH(13)
  ) u_v0c2arcsync_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                    //Bit position
    .din        ({
                  v0c2pmode,                 //12:10
                  v0c2arc_halt_ack_a,        //9
                  v0c2ext_arc_halt_req_a,    //8
                  v0c2arc_run_ack_a,         //7
                  v0c2ext_arc_run_req_a,     //6
                  v0c2sys_sleep_r,           //5
                  v0c2sys_sleep_mode_r,      //4:2
                  v0c2sys_halt_r,            //1
                  v0c2sys_tf_halt_r          //0
                  }),                                     //Bit position
    .dout       ({
	              v0c2pmode_sync,               //12:10
                  v0c2arc_halt_ack_sync,        //9
                  v0c2ext_arc_halt_req_sync,    //8
                  v0c2arc_run_ack_sync,         //7
                  v0c2ext_arc_run_req_sync,     //6
                  v0c2sys_sleep_sync,           //5
                  v0c2sys_sleep_mode_sync,      //4:2
                  v0c2sys_halt_sync,            //1
                  v0c2sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c2sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      v0c2sys_sleep_mode_sync_d1_r <= v0c2sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign v0c2update_sys_sleep_mode_sync_mmio_r = (v0c2sys_sleep_mode_sync==v0c2sys_sleep_mode_sync_d1_r) &
                                                       (v0c2sys_sleep_mode_sync_d1_r!=v0c2sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c2sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (v0c2update_sys_sleep_mode_sync_mmio_r)
      v0c2sys_sleep_mode_sync_mmio_r <= v0c2sys_sleep_mode_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c2pmode_sync_d1_r <= 3'h0;
    else
      v0c2pmode_sync_d1_r <= v0c2pmode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign v0c2update_pmode_sync_mmio_r = (v0c2pmode_sync==v0c2pmode_sync_d1_r) &
                                                  (v0c2pmode_sync_d1_r!=v0c2pmode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c2pmode_sync_mmio_r <= 3'h0;
    else if (v0c2update_pmode_sync_mmio_r)
      v0c2pmode_sync_mmio_r <= v0c2pmode_sync_d1_r;

logic v0c2ext_arc_halt_req_sync_d1_r;
logic v0c2ext_arc_halt_req_sync_flag_r;
logic v0c2arc_halt_ack_sync_d1_r;
logic set_v0c2ext_arc_halt_req_sync_flag;
logic clr_v0c2ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      v0c2ext_arc_halt_req_sync_d1_r <= 1'b0;
      v0c2arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      v0c2ext_arc_halt_req_sync_d1_r <= v0c2ext_arc_halt_req_sync;
      v0c2arc_halt_ack_sync_d1_r <= v0c2arc_halt_ack_sync;
    end

  assign set_v0c2ext_arc_halt_req_sync_flag = v0c2ext_arc_halt_req_sync & !v0c2ext_arc_halt_req_sync_d1_r;
  assign clr_v0c2ext_arc_halt_req_sync_flag = v0c2ext_arc_halt_req_sync_flag_r &
                                                               !v0c2arc_halt_ack_sync &
                                                               v0c2arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c2ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_v0c2ext_arc_halt_req_sync_flag)
      v0c2ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_v0c2ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      v0c2ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03

logic v0c2ext_arc_run_req_sync_d1_r;
logic v0c2ext_arc_run_req_sync_flag_r;
logic v0c2arc_run_ack_sync_d1_r;
logic set_v0c2ext_arc_run_req_sync_flag;
logic clr_v0c2ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      v0c2ext_arc_run_req_sync_d1_r <= 1'b0;
      v0c2arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      v0c2ext_arc_run_req_sync_d1_r <= v0c2ext_arc_run_req_sync;
      v0c2arc_run_ack_sync_d1_r <= v0c2arc_run_ack_sync;
    end

  assign set_v0c2ext_arc_run_req_sync_flag = v0c2ext_arc_run_req_sync & !v0c2ext_arc_run_req_sync_d1_r;
  assign clr_v0c2ext_arc_run_req_sync_flag = v0c2ext_arc_run_req_sync_flag_r &
                                                               !v0c2arc_run_ack_sync &
                                                               v0c2arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c2ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_v0c2ext_arc_run_req_sync_flag)
      v0c2ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_v0c2ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      v0c2ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03




  assign v0c2arcnum   = 2;        
  assign v0c2intvbase = arcsync_core_intvbase[34][31:10];

  assign v0c2rst_a  = arcsync_core_rst_req[34] 
                              | arcsync_core_pu_rst[34]
                             ;
  assign v0c2clk_en = arcsync_core_clk_en[34];

  assign v0c2arc_halt_req = arcsync_core_halt_req[34] | v0c2ext_arc_halt_req_sync;   
  assign v0c2arc_run_req  = arcsync_core_run_req[34] | v0c2ext_arc_run_req_sync; 

  // Split VPX irq & event
  assign v0c2arc_irq0_a = arcsync_core_irq[34][0];
  assign v0c2arc_irq1_a = arcsync_core_irq[34][1];
  assign v0c2arc_event0_a = arcsync_core_event[34][0];
  assign v0c2arc_event1_a = arcsync_core_event[34][1];

  assign core_arcsync_halt_ack[34]       = v0c2arc_halt_ack_sync & !v0c2ext_arc_halt_req_sync_flag_r;   
  assign v0c2ext_arc_halt_ack        = v0c2arc_halt_ack_sync & v0c2ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[34]        = v0c2arc_run_ack_sync & !v0c2ext_arc_run_req_sync_flag_r;    
  assign v0c2ext_arc_run_ack         = v0c2arc_run_ack_sync & v0c2ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[34]      = v0c2sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[34] = v0c2sys_sleep_mode_sync_mmio_r;
  assign core_arcsync_sys_halt[34]       = v0c2sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[34]    = v0c2sys_tf_halt_sync;  

  assign v0c2_pwr_dwn        =   1'b0
                                       ||  arcsync_core_pwr_down[34]
                                       ;
  assign core_arcsync_pmode[34]        = v0c2pmode_sync_mmio_r;
  // The PMU mode of vpx is the same as npx
  assign v0c2_isolate_n      =   arcsync_core_isolate_n[34]; 
  assign v0c2_isolate        =   arcsync_core_isolate[34]; 
  assign v0c2_pd_mem         =   arcsync_core_pd_mem[34]; 
  assign v0c2_pd_logic       =   arcsync_core_pd_logic[34];
  assign v0c2_pd_logic1      =   arcsync_core_pd_logic1[34];
  assign v0c2_pd_logic2      =   arcsync_core_pd_logic2[34];
  assign v0c2_pu_rst         =   arcsync_core_pu_rst[34]; 


  //PDM

  // Halt
  logic                   v0c3arc_halt_ack_sync;     // from v0c3arc_halt_ack_a
  logic                   v0c3ext_arc_halt_req_sync; // from v0c3ext_arc_halt_req_a
  // Run                                                 
  logic                   v0c3arc_run_ack_sync;      // from v0c3arc_run_ack_a
  logic                   v0c3ext_arc_run_req_sync;  // from v0c3ext_arc_run_req_a
  // Status                                              
  logic                   v0c3sys_sleep_sync;        // from v0c3sys_sleep_r
  logic   [2:0]           v0c3sys_sleep_mode_sync;   // from v0c3sys_sleep_mode_r[2:0]
  logic                   v0c3sys_halt_sync;         // from v0c3sys_halt_r
  logic                   v0c3sys_tf_halt_sync;      // from v0c3sys_tf_halt_r

  logic                   v0c3update_sys_sleep_mode_sync_mmio_r;
  reg [2:0]               v0c3sys_sleep_mode_sync_d1_r;
  reg [2:0]               v0c3sys_sleep_mode_sync_mmio_r;

  logic [2:0]             v0c3pmode_sync;
  logic                   v0c3update_pmode_sync_mmio_r;
  reg [2:0]               v0c3pmode_sync_d1_r;
  reg [2:0]               v0c3pmode_sync_mmio_r;

  arcsync_cdc_sync #(
    .SYNC_FF_LEVELS(2),
    .WIDTH(13)
  ) u_v0c3arcsync_cdc_sync (
    .clk        (arcsync_clk),
    .rst_a      (arcsync_core_rst),                    //Bit position
    .din        ({
                  v0c3pmode,                 //12:10
                  v0c3arc_halt_ack_a,        //9
                  v0c3ext_arc_halt_req_a,    //8
                  v0c3arc_run_ack_a,         //7
                  v0c3ext_arc_run_req_a,     //6
                  v0c3sys_sleep_r,           //5
                  v0c3sys_sleep_mode_r,      //4:2
                  v0c3sys_halt_r,            //1
                  v0c3sys_tf_halt_r          //0
                  }),                                     //Bit position
    .dout       ({
	              v0c3pmode_sync,               //12:10
                  v0c3arc_halt_ack_sync,        //9
                  v0c3ext_arc_halt_req_sync,    //8
                  v0c3arc_run_ack_sync,         //7
                  v0c3ext_arc_run_req_sync,     //6
                  v0c3sys_sleep_sync,           //5
                  v0c3sys_sleep_mode_sync,      //4:2
                  v0c3sys_halt_sync,            //1
                  v0c3sys_tf_halt_sync          //0
                  })
 );

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c3sys_sleep_mode_sync_d1_r <= 3'h0;
    else
      v0c3sys_sleep_mode_sync_d1_r <= v0c3sys_sleep_mode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign v0c3update_sys_sleep_mode_sync_mmio_r = (v0c3sys_sleep_mode_sync==v0c3sys_sleep_mode_sync_d1_r) &
                                                       (v0c3sys_sleep_mode_sync_d1_r!=v0c3sys_sleep_mode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c3sys_sleep_mode_sync_mmio_r <= 3'h0;
    else if (v0c3update_sys_sleep_mode_sync_mmio_r)
      v0c3sys_sleep_mode_sync_mmio_r <= v0c3sys_sleep_mode_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c3pmode_sync_d1_r <= 3'h0;
    else
      v0c3pmode_sync_d1_r <= v0c3pmode_sync;

// spyglass disable_block Ac_conv03
// sync DFF converge
  assign v0c3update_pmode_sync_mmio_r = (v0c3pmode_sync==v0c3pmode_sync_d1_r) &
                                                  (v0c3pmode_sync_d1_r!=v0c3pmode_sync_mmio_r);
// spyglass enable_block Ac_conv03

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c3pmode_sync_mmio_r <= 3'h0;
    else if (v0c3update_pmode_sync_mmio_r)
      v0c3pmode_sync_mmio_r <= v0c3pmode_sync_d1_r;

logic v0c3ext_arc_halt_req_sync_d1_r;
logic v0c3ext_arc_halt_req_sync_flag_r;
logic v0c3arc_halt_ack_sync_d1_r;
logic set_v0c3ext_arc_halt_req_sync_flag;
logic clr_v0c3ext_arc_halt_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      v0c3ext_arc_halt_req_sync_d1_r <= 1'b0;
      v0c3arc_halt_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      v0c3ext_arc_halt_req_sync_d1_r <= v0c3ext_arc_halt_req_sync;
      v0c3arc_halt_ack_sync_d1_r <= v0c3arc_halt_ack_sync;
    end

  assign set_v0c3ext_arc_halt_req_sync_flag = v0c3ext_arc_halt_req_sync & !v0c3ext_arc_halt_req_sync_d1_r;
  assign clr_v0c3ext_arc_halt_req_sync_flag = v0c3ext_arc_halt_req_sync_flag_r &
                                                               !v0c3arc_halt_ack_sync &
                                                               v0c3arc_halt_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c3ext_arc_halt_req_sync_flag_r <= 1'b0;
    else if (set_v0c3ext_arc_halt_req_sync_flag)
      v0c3ext_arc_halt_req_sync_flag_r <= 1'b1;
    else if (clr_v0c3ext_arc_halt_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      v0c3ext_arc_halt_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03

logic v0c3ext_arc_run_req_sync_d1_r;
logic v0c3ext_arc_run_req_sync_flag_r;
logic v0c3arc_run_ack_sync_d1_r;
logic set_v0c3ext_arc_run_req_sync_flag;
logic clr_v0c3ext_arc_run_req_sync_flag;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
    begin
      v0c3ext_arc_run_req_sync_d1_r <= 1'b0;
      v0c3arc_run_ack_sync_d1_r <= 1'b0;
    end
    else
    begin
      v0c3ext_arc_run_req_sync_d1_r <= v0c3ext_arc_run_req_sync;
      v0c3arc_run_ack_sync_d1_r <= v0c3arc_run_ack_sync;
    end

  assign set_v0c3ext_arc_run_req_sync_flag = v0c3ext_arc_run_req_sync & !v0c3ext_arc_run_req_sync_d1_r;
  assign clr_v0c3ext_arc_run_req_sync_flag = v0c3ext_arc_run_req_sync_flag_r &
                                                               !v0c3arc_run_ack_sync &
                                                               v0c3arc_run_ack_sync_d1_r;

  always @(posedge arcsync_clk or posedge arcsync_core_rst)
    if (arcsync_core_rst)
      v0c3ext_arc_run_req_sync_flag_r <= 1'b0;
    else if (set_v0c3ext_arc_run_req_sync_flag)
      v0c3ext_arc_run_req_sync_flag_r <= 1'b1;
    else if (clr_v0c3ext_arc_run_req_sync_flag)
// spyglass disable_block Ac_conv03
// sync DFF converge
      v0c3ext_arc_run_req_sync_flag_r <= 1'b0;
// spyglass enable_block Ac_conv03




  assign v0c3arcnum   = 3;        
  assign v0c3intvbase = arcsync_core_intvbase[35][31:10];

  assign v0c3rst_a  = arcsync_core_rst_req[35] 
                              | arcsync_core_pu_rst[35]
                             ;
  assign v0c3clk_en = arcsync_core_clk_en[35];

  assign v0c3arc_halt_req = arcsync_core_halt_req[35] | v0c3ext_arc_halt_req_sync;   
  assign v0c3arc_run_req  = arcsync_core_run_req[35] | v0c3ext_arc_run_req_sync; 

  // Split VPX irq & event
  assign v0c3arc_irq0_a = arcsync_core_irq[35][0];
  assign v0c3arc_irq1_a = arcsync_core_irq[35][1];
  assign v0c3arc_event0_a = arcsync_core_event[35][0];
  assign v0c3arc_event1_a = arcsync_core_event[35][1];

  assign core_arcsync_halt_ack[35]       = v0c3arc_halt_ack_sync & !v0c3ext_arc_halt_req_sync_flag_r;   
  assign v0c3ext_arc_halt_ack        = v0c3arc_halt_ack_sync & v0c3ext_arc_halt_req_sync_flag_r;
  assign core_arcsync_run_ack[35]        = v0c3arc_run_ack_sync & !v0c3ext_arc_run_req_sync_flag_r;    
  assign v0c3ext_arc_run_ack         = v0c3arc_run_ack_sync & v0c3ext_arc_run_req_sync_flag_r;
  assign core_arcsync_sys_sleep[35]      = v0c3sys_sleep_sync;      
  assign core_arcsync_sys_sleep_mode[35] = v0c3sys_sleep_mode_sync_mmio_r;
  assign core_arcsync_sys_halt[35]       = v0c3sys_halt_sync;       
  assign core_arcsync_sys_tf_halt[35]    = v0c3sys_tf_halt_sync;  

  assign v0c3_pwr_dwn        =   1'b0
                                       ||  arcsync_core_pwr_down[35]
                                       ;
  assign core_arcsync_pmode[35]        = v0c3pmode_sync_mmio_r;
  // The PMU mode of vpx is the same as npx
  assign v0c3_isolate_n      =   arcsync_core_isolate_n[35]; 
  assign v0c3_isolate        =   arcsync_core_isolate[35]; 
  assign v0c3_pd_mem         =   arcsync_core_pd_mem[35]; 
  assign v0c3_pd_logic       =   arcsync_core_pd_logic[35];
  assign v0c3_pd_logic1      =   arcsync_core_pd_logic1[35];
  assign v0c3_pd_logic2      =   arcsync_core_pd_logic2[35];
  assign v0c3_pu_rst         =   arcsync_core_pu_rst[35]; 





// DBG: Connections for undefined cores
  //#4#32#36#
  assign core_arcsync_halt_ack[36]       =1'b0; 
  assign core_arcsync_run_ack[36]        =1'b0; 
  assign core_arcsync_sys_sleep[36]      =1'b0;
  assign core_arcsync_sys_sleep_mode[36] =3'b0;
  assign core_arcsync_sys_halt[36]       =1'b0; 
  assign core_arcsync_sys_tf_halt[36]    =1'b0;
 
  assign core_arcsync_pmode[36]        = 3'b0; 
  //#4#32#37#
  assign core_arcsync_halt_ack[37]       =1'b0; 
  assign core_arcsync_run_ack[37]        =1'b0; 
  assign core_arcsync_sys_sleep[37]      =1'b0;
  assign core_arcsync_sys_sleep_mode[37] =3'b0;
  assign core_arcsync_sys_halt[37]       =1'b0; 
  assign core_arcsync_sys_tf_halt[37]    =1'b0;
 
  assign core_arcsync_pmode[37]        = 3'b0; 
  //#4#32#38#
  assign core_arcsync_halt_ack[38]       =1'b0; 
  assign core_arcsync_run_ack[38]        =1'b0; 
  assign core_arcsync_sys_sleep[38]      =1'b0;
  assign core_arcsync_sys_sleep_mode[38] =3'b0;
  assign core_arcsync_sys_halt[38]       =1'b0; 
  assign core_arcsync_sys_tf_halt[38]    =1'b0;
 
  assign core_arcsync_pmode[38]        = 3'b0; 
  //#4#32#39#
  assign core_arcsync_halt_ack[39]       =1'b0; 
  assign core_arcsync_run_ack[39]        =1'b0; 
  assign core_arcsync_sys_sleep[39]      =1'b0;
  assign core_arcsync_sys_sleep_mode[39] =3'b0;
  assign core_arcsync_sys_halt[39]       =1'b0; 
  assign core_arcsync_sys_tf_halt[39]    =1'b0;
 
  assign core_arcsync_pmode[39]        = 3'b0; 
  //#4#32#40#
  assign core_arcsync_halt_ack[40]       =1'b0; 
  assign core_arcsync_run_ack[40]        =1'b0; 
  assign core_arcsync_sys_sleep[40]      =1'b0;
  assign core_arcsync_sys_sleep_mode[40] =3'b0;
  assign core_arcsync_sys_halt[40]       =1'b0; 
  assign core_arcsync_sys_tf_halt[40]    =1'b0;
 
  assign core_arcsync_pmode[40]        = 3'b0; 
  //#4#32#41#
  assign core_arcsync_halt_ack[41]       =1'b0; 
  assign core_arcsync_run_ack[41]        =1'b0; 
  assign core_arcsync_sys_sleep[41]      =1'b0;
  assign core_arcsync_sys_sleep_mode[41] =3'b0;
  assign core_arcsync_sys_halt[41]       =1'b0; 
  assign core_arcsync_sys_tf_halt[41]    =1'b0;
 
  assign core_arcsync_pmode[41]        = 3'b0; 
  //#4#32#42#
  assign core_arcsync_halt_ack[42]       =1'b0; 
  assign core_arcsync_run_ack[42]        =1'b0; 
  assign core_arcsync_sys_sleep[42]      =1'b0;
  assign core_arcsync_sys_sleep_mode[42] =3'b0;
  assign core_arcsync_sys_halt[42]       =1'b0; 
  assign core_arcsync_sys_tf_halt[42]    =1'b0;
 
  assign core_arcsync_pmode[42]        = 3'b0; 
  //#4#32#43#
  assign core_arcsync_halt_ack[43]       =1'b0; 
  assign core_arcsync_run_ack[43]        =1'b0; 
  assign core_arcsync_sys_sleep[43]      =1'b0;
  assign core_arcsync_sys_sleep_mode[43] =3'b0;
  assign core_arcsync_sys_halt[43]       =1'b0; 
  assign core_arcsync_sys_tf_halt[43]    =1'b0;
 
  assign core_arcsync_pmode[43]        = 3'b0; 
  //#4#32#44#
  assign core_arcsync_halt_ack[44]       =1'b0; 
  assign core_arcsync_run_ack[44]        =1'b0; 
  assign core_arcsync_sys_sleep[44]      =1'b0;
  assign core_arcsync_sys_sleep_mode[44] =3'b0;
  assign core_arcsync_sys_halt[44]       =1'b0; 
  assign core_arcsync_sys_tf_halt[44]    =1'b0;
 
  assign core_arcsync_pmode[44]        = 3'b0; 
  //#4#32#45#
  assign core_arcsync_halt_ack[45]       =1'b0; 
  assign core_arcsync_run_ack[45]        =1'b0; 
  assign core_arcsync_sys_sleep[45]      =1'b0;
  assign core_arcsync_sys_sleep_mode[45] =3'b0;
  assign core_arcsync_sys_halt[45]       =1'b0; 
  assign core_arcsync_sys_tf_halt[45]    =1'b0;
 
  assign core_arcsync_pmode[45]        = 3'b0; 
  //#4#32#46#
  assign core_arcsync_halt_ack[46]       =1'b0; 
  assign core_arcsync_run_ack[46]        =1'b0; 
  assign core_arcsync_sys_sleep[46]      =1'b0;
  assign core_arcsync_sys_sleep_mode[46] =3'b0;
  assign core_arcsync_sys_halt[46]       =1'b0; 
  assign core_arcsync_sys_tf_halt[46]    =1'b0;
 
  assign core_arcsync_pmode[46]        = 3'b0; 
  //#4#32#47#
  assign core_arcsync_halt_ack[47]       =1'b0; 
  assign core_arcsync_run_ack[47]        =1'b0; 
  assign core_arcsync_sys_sleep[47]      =1'b0;
  assign core_arcsync_sys_sleep_mode[47] =3'b0;
  assign core_arcsync_sys_halt[47]       =1'b0; 
  assign core_arcsync_sys_tf_halt[47]    =1'b0;
 
  assign core_arcsync_pmode[47]        = 3'b0; 
  //#4#32#48#
  assign core_arcsync_halt_ack[48]       =1'b0; 
  assign core_arcsync_run_ack[48]        =1'b0; 
  assign core_arcsync_sys_sleep[48]      =1'b0;
  assign core_arcsync_sys_sleep_mode[48] =3'b0;
  assign core_arcsync_sys_halt[48]       =1'b0; 
  assign core_arcsync_sys_tf_halt[48]    =1'b0;
 
  assign core_arcsync_pmode[48]        = 3'b0; 
  //#4#32#49#
  assign core_arcsync_halt_ack[49]       =1'b0; 
  assign core_arcsync_run_ack[49]        =1'b0; 
  assign core_arcsync_sys_sleep[49]      =1'b0;
  assign core_arcsync_sys_sleep_mode[49] =3'b0;
  assign core_arcsync_sys_halt[49]       =1'b0; 
  assign core_arcsync_sys_tf_halt[49]    =1'b0;
 
  assign core_arcsync_pmode[49]        = 3'b0; 
  //#4#32#50#
  assign core_arcsync_halt_ack[50]       =1'b0; 
  assign core_arcsync_run_ack[50]        =1'b0; 
  assign core_arcsync_sys_sleep[50]      =1'b0;
  assign core_arcsync_sys_sleep_mode[50] =3'b0;
  assign core_arcsync_sys_halt[50]       =1'b0; 
  assign core_arcsync_sys_tf_halt[50]    =1'b0;
 
  assign core_arcsync_pmode[50]        = 3'b0; 
  //#4#32#51#
  assign core_arcsync_halt_ack[51]       =1'b0; 
  assign core_arcsync_run_ack[51]        =1'b0; 
  assign core_arcsync_sys_sleep[51]      =1'b0;
  assign core_arcsync_sys_sleep_mode[51] =3'b0;
  assign core_arcsync_sys_halt[51]       =1'b0; 
  assign core_arcsync_sys_tf_halt[51]    =1'b0;
 
  assign core_arcsync_pmode[51]        = 3'b0; 
  //#4#32#52#
  assign core_arcsync_halt_ack[52]       =1'b0; 
  assign core_arcsync_run_ack[52]        =1'b0; 
  assign core_arcsync_sys_sleep[52]      =1'b0;
  assign core_arcsync_sys_sleep_mode[52] =3'b0;
  assign core_arcsync_sys_halt[52]       =1'b0; 
  assign core_arcsync_sys_tf_halt[52]    =1'b0;
 
  assign core_arcsync_pmode[52]        = 3'b0; 
  //#4#32#53#
  assign core_arcsync_halt_ack[53]       =1'b0; 
  assign core_arcsync_run_ack[53]        =1'b0; 
  assign core_arcsync_sys_sleep[53]      =1'b0;
  assign core_arcsync_sys_sleep_mode[53] =3'b0;
  assign core_arcsync_sys_halt[53]       =1'b0; 
  assign core_arcsync_sys_tf_halt[53]    =1'b0;
 
  assign core_arcsync_pmode[53]        = 3'b0; 
  //#4#32#54#
  assign core_arcsync_halt_ack[54]       =1'b0; 
  assign core_arcsync_run_ack[54]        =1'b0; 
  assign core_arcsync_sys_sleep[54]      =1'b0;
  assign core_arcsync_sys_sleep_mode[54] =3'b0;
  assign core_arcsync_sys_halt[54]       =1'b0; 
  assign core_arcsync_sys_tf_halt[54]    =1'b0;
 
  assign core_arcsync_pmode[54]        = 3'b0; 
  //#4#32#55#
  assign core_arcsync_halt_ack[55]       =1'b0; 
  assign core_arcsync_run_ack[55]        =1'b0; 
  assign core_arcsync_sys_sleep[55]      =1'b0;
  assign core_arcsync_sys_sleep_mode[55] =3'b0;
  assign core_arcsync_sys_halt[55]       =1'b0; 
  assign core_arcsync_sys_tf_halt[55]    =1'b0;
 
  assign core_arcsync_pmode[55]        = 3'b0; 
  //#4#32#56#
  assign core_arcsync_halt_ack[56]       =1'b0; 
  assign core_arcsync_run_ack[56]        =1'b0; 
  assign core_arcsync_sys_sleep[56]      =1'b0;
  assign core_arcsync_sys_sleep_mode[56] =3'b0;
  assign core_arcsync_sys_halt[56]       =1'b0; 
  assign core_arcsync_sys_tf_halt[56]    =1'b0;
 
  assign core_arcsync_pmode[56]        = 3'b0; 
  //#4#32#57#
  assign core_arcsync_halt_ack[57]       =1'b0; 
  assign core_arcsync_run_ack[57]        =1'b0; 
  assign core_arcsync_sys_sleep[57]      =1'b0;
  assign core_arcsync_sys_sleep_mode[57] =3'b0;
  assign core_arcsync_sys_halt[57]       =1'b0; 
  assign core_arcsync_sys_tf_halt[57]    =1'b0;
 
  assign core_arcsync_pmode[57]        = 3'b0; 
  //#4#32#58#
  assign core_arcsync_halt_ack[58]       =1'b0; 
  assign core_arcsync_run_ack[58]        =1'b0; 
  assign core_arcsync_sys_sleep[58]      =1'b0;
  assign core_arcsync_sys_sleep_mode[58] =3'b0;
  assign core_arcsync_sys_halt[58]       =1'b0; 
  assign core_arcsync_sys_tf_halt[58]    =1'b0;
 
  assign core_arcsync_pmode[58]        = 3'b0; 
  //#4#32#59#
  assign core_arcsync_halt_ack[59]       =1'b0; 
  assign core_arcsync_run_ack[59]        =1'b0; 
  assign core_arcsync_sys_sleep[59]      =1'b0;
  assign core_arcsync_sys_sleep_mode[59] =3'b0;
  assign core_arcsync_sys_halt[59]       =1'b0; 
  assign core_arcsync_sys_tf_halt[59]    =1'b0;
 
  assign core_arcsync_pmode[59]        = 3'b0; 
  //#4#32#60#
  assign core_arcsync_halt_ack[60]       =1'b0; 
  assign core_arcsync_run_ack[60]        =1'b0; 
  assign core_arcsync_sys_sleep[60]      =1'b0;
  assign core_arcsync_sys_sleep_mode[60] =3'b0;
  assign core_arcsync_sys_halt[60]       =1'b0; 
  assign core_arcsync_sys_tf_halt[60]    =1'b0;
 
  assign core_arcsync_pmode[60]        = 3'b0; 
  //#4#32#61#
  assign core_arcsync_halt_ack[61]       =1'b0; 
  assign core_arcsync_run_ack[61]        =1'b0; 
  assign core_arcsync_sys_sleep[61]      =1'b0;
  assign core_arcsync_sys_sleep_mode[61] =3'b0;
  assign core_arcsync_sys_halt[61]       =1'b0; 
  assign core_arcsync_sys_tf_halt[61]    =1'b0;
 
  assign core_arcsync_pmode[61]        = 3'b0; 
  //#4#32#62#
  assign core_arcsync_halt_ack[62]       =1'b0; 
  assign core_arcsync_run_ack[62]        =1'b0; 
  assign core_arcsync_sys_sleep[62]      =1'b0;
  assign core_arcsync_sys_sleep_mode[62] =3'b0;
  assign core_arcsync_sys_halt[62]       =1'b0; 
  assign core_arcsync_sys_tf_halt[62]    =1'b0;
 
  assign core_arcsync_pmode[62]        = 3'b0; 
  //#4#32#63#
  assign core_arcsync_halt_ack[63]       =1'b0; 
  assign core_arcsync_run_ack[63]        =1'b0; 
  assign core_arcsync_sys_sleep[63]      =1'b0;
  assign core_arcsync_sys_sleep_mode[63] =3'b0;
  assign core_arcsync_sys_halt[63]       =1'b0; 
  assign core_arcsync_sys_tf_halt[63]    =1'b0;
 
  assign core_arcsync_pmode[63]        = 3'b0; 





































  // Host Cluster
  assign h0host_irq      = arcsync_core_irq[64];
  assign h0host_event    = arcsync_core_event[64];
  assign core_arcsync_halt_ack[64]       = 1'b0; 
  assign core_arcsync_run_ack[64]        = 1'b0; 
  assign core_arcsync_sys_sleep[64]      = 1'b0; 
  assign core_arcsync_sys_sleep_mode[64] = 3'b0; 
  assign core_arcsync_sys_halt[64]       = 1'b0; 
  assign core_arcsync_sys_tf_halt[64]    = 1'b0; 

  assign core_arcsync_pmode[64]        = 3'b0;



// DBG: Connections for undefined cores
  //#1#32#65#
  assign core_arcsync_halt_ack[65]       =1'b0; 
  assign core_arcsync_run_ack[65]        =1'b0; 
  assign core_arcsync_sys_sleep[65]      =1'b0;
  assign core_arcsync_sys_sleep_mode[65] =3'b0;
  assign core_arcsync_sys_halt[65]       =1'b0; 
  assign core_arcsync_sys_tf_halt[65]    =1'b0;
 
  assign core_arcsync_pmode[65]        = 3'b0; 
  //#1#32#66#
  assign core_arcsync_halt_ack[66]       =1'b0; 
  assign core_arcsync_run_ack[66]        =1'b0; 
  assign core_arcsync_sys_sleep[66]      =1'b0;
  assign core_arcsync_sys_sleep_mode[66] =3'b0;
  assign core_arcsync_sys_halt[66]       =1'b0; 
  assign core_arcsync_sys_tf_halt[66]    =1'b0;
 
  assign core_arcsync_pmode[66]        = 3'b0; 
  //#1#32#67#
  assign core_arcsync_halt_ack[67]       =1'b0; 
  assign core_arcsync_run_ack[67]        =1'b0; 
  assign core_arcsync_sys_sleep[67]      =1'b0;
  assign core_arcsync_sys_sleep_mode[67] =3'b0;
  assign core_arcsync_sys_halt[67]       =1'b0; 
  assign core_arcsync_sys_tf_halt[67]    =1'b0;
 
  assign core_arcsync_pmode[67]        = 3'b0; 
  //#1#32#68#
  assign core_arcsync_halt_ack[68]       =1'b0; 
  assign core_arcsync_run_ack[68]        =1'b0; 
  assign core_arcsync_sys_sleep[68]      =1'b0;
  assign core_arcsync_sys_sleep_mode[68] =3'b0;
  assign core_arcsync_sys_halt[68]       =1'b0; 
  assign core_arcsync_sys_tf_halt[68]    =1'b0;
 
  assign core_arcsync_pmode[68]        = 3'b0; 
  //#1#32#69#
  assign core_arcsync_halt_ack[69]       =1'b0; 
  assign core_arcsync_run_ack[69]        =1'b0; 
  assign core_arcsync_sys_sleep[69]      =1'b0;
  assign core_arcsync_sys_sleep_mode[69] =3'b0;
  assign core_arcsync_sys_halt[69]       =1'b0; 
  assign core_arcsync_sys_tf_halt[69]    =1'b0;
 
  assign core_arcsync_pmode[69]        = 3'b0; 
  //#1#32#70#
  assign core_arcsync_halt_ack[70]       =1'b0; 
  assign core_arcsync_run_ack[70]        =1'b0; 
  assign core_arcsync_sys_sleep[70]      =1'b0;
  assign core_arcsync_sys_sleep_mode[70] =3'b0;
  assign core_arcsync_sys_halt[70]       =1'b0; 
  assign core_arcsync_sys_tf_halt[70]    =1'b0;
 
  assign core_arcsync_pmode[70]        = 3'b0; 
  //#1#32#71#
  assign core_arcsync_halt_ack[71]       =1'b0; 
  assign core_arcsync_run_ack[71]        =1'b0; 
  assign core_arcsync_sys_sleep[71]      =1'b0;
  assign core_arcsync_sys_sleep_mode[71] =3'b0;
  assign core_arcsync_sys_halt[71]       =1'b0; 
  assign core_arcsync_sys_tf_halt[71]    =1'b0;
 
  assign core_arcsync_pmode[71]        = 3'b0; 
  //#1#32#72#
  assign core_arcsync_halt_ack[72]       =1'b0; 
  assign core_arcsync_run_ack[72]        =1'b0; 
  assign core_arcsync_sys_sleep[72]      =1'b0;
  assign core_arcsync_sys_sleep_mode[72] =3'b0;
  assign core_arcsync_sys_halt[72]       =1'b0; 
  assign core_arcsync_sys_tf_halt[72]    =1'b0;
 
  assign core_arcsync_pmode[72]        = 3'b0; 
  //#1#32#73#
  assign core_arcsync_halt_ack[73]       =1'b0; 
  assign core_arcsync_run_ack[73]        =1'b0; 
  assign core_arcsync_sys_sleep[73]      =1'b0;
  assign core_arcsync_sys_sleep_mode[73] =3'b0;
  assign core_arcsync_sys_halt[73]       =1'b0; 
  assign core_arcsync_sys_tf_halt[73]    =1'b0;
 
  assign core_arcsync_pmode[73]        = 3'b0; 
  //#1#32#74#
  assign core_arcsync_halt_ack[74]       =1'b0; 
  assign core_arcsync_run_ack[74]        =1'b0; 
  assign core_arcsync_sys_sleep[74]      =1'b0;
  assign core_arcsync_sys_sleep_mode[74] =3'b0;
  assign core_arcsync_sys_halt[74]       =1'b0; 
  assign core_arcsync_sys_tf_halt[74]    =1'b0;
 
  assign core_arcsync_pmode[74]        = 3'b0; 
  //#1#32#75#
  assign core_arcsync_halt_ack[75]       =1'b0; 
  assign core_arcsync_run_ack[75]        =1'b0; 
  assign core_arcsync_sys_sleep[75]      =1'b0;
  assign core_arcsync_sys_sleep_mode[75] =3'b0;
  assign core_arcsync_sys_halt[75]       =1'b0; 
  assign core_arcsync_sys_tf_halt[75]    =1'b0;
 
  assign core_arcsync_pmode[75]        = 3'b0; 
  //#1#32#76#
  assign core_arcsync_halt_ack[76]       =1'b0; 
  assign core_arcsync_run_ack[76]        =1'b0; 
  assign core_arcsync_sys_sleep[76]      =1'b0;
  assign core_arcsync_sys_sleep_mode[76] =3'b0;
  assign core_arcsync_sys_halt[76]       =1'b0; 
  assign core_arcsync_sys_tf_halt[76]    =1'b0;
 
  assign core_arcsync_pmode[76]        = 3'b0; 
  //#1#32#77#
  assign core_arcsync_halt_ack[77]       =1'b0; 
  assign core_arcsync_run_ack[77]        =1'b0; 
  assign core_arcsync_sys_sleep[77]      =1'b0;
  assign core_arcsync_sys_sleep_mode[77] =3'b0;
  assign core_arcsync_sys_halt[77]       =1'b0; 
  assign core_arcsync_sys_tf_halt[77]    =1'b0;
 
  assign core_arcsync_pmode[77]        = 3'b0; 
  //#1#32#78#
  assign core_arcsync_halt_ack[78]       =1'b0; 
  assign core_arcsync_run_ack[78]        =1'b0; 
  assign core_arcsync_sys_sleep[78]      =1'b0;
  assign core_arcsync_sys_sleep_mode[78] =3'b0;
  assign core_arcsync_sys_halt[78]       =1'b0; 
  assign core_arcsync_sys_tf_halt[78]    =1'b0;
 
  assign core_arcsync_pmode[78]        = 3'b0; 
  //#1#32#79#
  assign core_arcsync_halt_ack[79]       =1'b0; 
  assign core_arcsync_run_ack[79]        =1'b0; 
  assign core_arcsync_sys_sleep[79]      =1'b0;
  assign core_arcsync_sys_sleep_mode[79] =3'b0;
  assign core_arcsync_sys_halt[79]       =1'b0; 
  assign core_arcsync_sys_tf_halt[79]    =1'b0;
 
  assign core_arcsync_pmode[79]        = 3'b0; 
  //#1#32#80#
  assign core_arcsync_halt_ack[80]       =1'b0; 
  assign core_arcsync_run_ack[80]        =1'b0; 
  assign core_arcsync_sys_sleep[80]      =1'b0;
  assign core_arcsync_sys_sleep_mode[80] =3'b0;
  assign core_arcsync_sys_halt[80]       =1'b0; 
  assign core_arcsync_sys_tf_halt[80]    =1'b0;
 
  assign core_arcsync_pmode[80]        = 3'b0; 
  //#1#32#81#
  assign core_arcsync_halt_ack[81]       =1'b0; 
  assign core_arcsync_run_ack[81]        =1'b0; 
  assign core_arcsync_sys_sleep[81]      =1'b0;
  assign core_arcsync_sys_sleep_mode[81] =3'b0;
  assign core_arcsync_sys_halt[81]       =1'b0; 
  assign core_arcsync_sys_tf_halt[81]    =1'b0;
 
  assign core_arcsync_pmode[81]        = 3'b0; 
  //#1#32#82#
  assign core_arcsync_halt_ack[82]       =1'b0; 
  assign core_arcsync_run_ack[82]        =1'b0; 
  assign core_arcsync_sys_sleep[82]      =1'b0;
  assign core_arcsync_sys_sleep_mode[82] =3'b0;
  assign core_arcsync_sys_halt[82]       =1'b0; 
  assign core_arcsync_sys_tf_halt[82]    =1'b0;
 
  assign core_arcsync_pmode[82]        = 3'b0; 
  //#1#32#83#
  assign core_arcsync_halt_ack[83]       =1'b0; 
  assign core_arcsync_run_ack[83]        =1'b0; 
  assign core_arcsync_sys_sleep[83]      =1'b0;
  assign core_arcsync_sys_sleep_mode[83] =3'b0;
  assign core_arcsync_sys_halt[83]       =1'b0; 
  assign core_arcsync_sys_tf_halt[83]    =1'b0;
 
  assign core_arcsync_pmode[83]        = 3'b0; 
  //#1#32#84#
  assign core_arcsync_halt_ack[84]       =1'b0; 
  assign core_arcsync_run_ack[84]        =1'b0; 
  assign core_arcsync_sys_sleep[84]      =1'b0;
  assign core_arcsync_sys_sleep_mode[84] =3'b0;
  assign core_arcsync_sys_halt[84]       =1'b0; 
  assign core_arcsync_sys_tf_halt[84]    =1'b0;
 
  assign core_arcsync_pmode[84]        = 3'b0; 
  //#1#32#85#
  assign core_arcsync_halt_ack[85]       =1'b0; 
  assign core_arcsync_run_ack[85]        =1'b0; 
  assign core_arcsync_sys_sleep[85]      =1'b0;
  assign core_arcsync_sys_sleep_mode[85] =3'b0;
  assign core_arcsync_sys_halt[85]       =1'b0; 
  assign core_arcsync_sys_tf_halt[85]    =1'b0;
 
  assign core_arcsync_pmode[85]        = 3'b0; 
  //#1#32#86#
  assign core_arcsync_halt_ack[86]       =1'b0; 
  assign core_arcsync_run_ack[86]        =1'b0; 
  assign core_arcsync_sys_sleep[86]      =1'b0;
  assign core_arcsync_sys_sleep_mode[86] =3'b0;
  assign core_arcsync_sys_halt[86]       =1'b0; 
  assign core_arcsync_sys_tf_halt[86]    =1'b0;
 
  assign core_arcsync_pmode[86]        = 3'b0; 
  //#1#32#87#
  assign core_arcsync_halt_ack[87]       =1'b0; 
  assign core_arcsync_run_ack[87]        =1'b0; 
  assign core_arcsync_sys_sleep[87]      =1'b0;
  assign core_arcsync_sys_sleep_mode[87] =3'b0;
  assign core_arcsync_sys_halt[87]       =1'b0; 
  assign core_arcsync_sys_tf_halt[87]    =1'b0;
 
  assign core_arcsync_pmode[87]        = 3'b0; 
  //#1#32#88#
  assign core_arcsync_halt_ack[88]       =1'b0; 
  assign core_arcsync_run_ack[88]        =1'b0; 
  assign core_arcsync_sys_sleep[88]      =1'b0;
  assign core_arcsync_sys_sleep_mode[88] =3'b0;
  assign core_arcsync_sys_halt[88]       =1'b0; 
  assign core_arcsync_sys_tf_halt[88]    =1'b0;
 
  assign core_arcsync_pmode[88]        = 3'b0; 
  //#1#32#89#
  assign core_arcsync_halt_ack[89]       =1'b0; 
  assign core_arcsync_run_ack[89]        =1'b0; 
  assign core_arcsync_sys_sleep[89]      =1'b0;
  assign core_arcsync_sys_sleep_mode[89] =3'b0;
  assign core_arcsync_sys_halt[89]       =1'b0; 
  assign core_arcsync_sys_tf_halt[89]    =1'b0;
 
  assign core_arcsync_pmode[89]        = 3'b0; 
  //#1#32#90#
  assign core_arcsync_halt_ack[90]       =1'b0; 
  assign core_arcsync_run_ack[90]        =1'b0; 
  assign core_arcsync_sys_sleep[90]      =1'b0;
  assign core_arcsync_sys_sleep_mode[90] =3'b0;
  assign core_arcsync_sys_halt[90]       =1'b0; 
  assign core_arcsync_sys_tf_halt[90]    =1'b0;
 
  assign core_arcsync_pmode[90]        = 3'b0; 
  //#1#32#91#
  assign core_arcsync_halt_ack[91]       =1'b0; 
  assign core_arcsync_run_ack[91]        =1'b0; 
  assign core_arcsync_sys_sleep[91]      =1'b0;
  assign core_arcsync_sys_sleep_mode[91] =3'b0;
  assign core_arcsync_sys_halt[91]       =1'b0; 
  assign core_arcsync_sys_tf_halt[91]    =1'b0;
 
  assign core_arcsync_pmode[91]        = 3'b0; 
  //#1#32#92#
  assign core_arcsync_halt_ack[92]       =1'b0; 
  assign core_arcsync_run_ack[92]        =1'b0; 
  assign core_arcsync_sys_sleep[92]      =1'b0;
  assign core_arcsync_sys_sleep_mode[92] =3'b0;
  assign core_arcsync_sys_halt[92]       =1'b0; 
  assign core_arcsync_sys_tf_halt[92]    =1'b0;
 
  assign core_arcsync_pmode[92]        = 3'b0; 
  //#1#32#93#
  assign core_arcsync_halt_ack[93]       =1'b0; 
  assign core_arcsync_run_ack[93]        =1'b0; 
  assign core_arcsync_sys_sleep[93]      =1'b0;
  assign core_arcsync_sys_sleep_mode[93] =3'b0;
  assign core_arcsync_sys_halt[93]       =1'b0; 
  assign core_arcsync_sys_tf_halt[93]    =1'b0;
 
  assign core_arcsync_pmode[93]        = 3'b0; 
  //#1#32#94#
  assign core_arcsync_halt_ack[94]       =1'b0; 
  assign core_arcsync_run_ack[94]        =1'b0; 
  assign core_arcsync_sys_sleep[94]      =1'b0;
  assign core_arcsync_sys_sleep_mode[94] =3'b0;
  assign core_arcsync_sys_halt[94]       =1'b0; 
  assign core_arcsync_sys_tf_halt[94]    =1'b0;
 
  assign core_arcsync_pmode[94]        = 3'b0; 
  //#1#32#95#
  assign core_arcsync_halt_ack[95]       =1'b0; 
  assign core_arcsync_run_ack[95]        =1'b0; 
  assign core_arcsync_sys_sleep[95]      =1'b0;
  assign core_arcsync_sys_sleep_mode[95] =3'b0;
  assign core_arcsync_sys_halt[95]       =1'b0; 
  assign core_arcsync_sys_tf_halt[95]    =1'b0;
 
  assign core_arcsync_pmode[95]        = 3'b0; 

































 

for (genvar i=0; i<CORE_NUM; i++)
begin
  // ARC64 cores are not supported 
  assign core_arcsync_arc64[i]   = 1'b0;
end

  arcsync_reset_ctrl
  u_arcsync_core_rst_ctrl
  (
   .clk        (arcsync_clk),
   .rst_a      (arcsync_rst_a),
   .rst        (arcsync_core_rst),
   .test_mode  (test_mode)
   );

  assign arcsync_core_rstn = ~arcsync_core_rst;

  arcsync_core #(
                 .CLUSTER_NUM    (`ARCSYNC_NUM_CLUSTER), 
                 .NUM_CORE_C03   (NUM_CORE_C03), 
                 .NUM_CORE_C74   (NUM_CORE_C74), 
                 .CORE_NUM       (CORE_NUM), 
                 .MAX_CORE_NUM   (`ARCSYNC_MAX_CORES_PER_CL),
                 .AC_NUM         (`ARCSYNC_NUM_ATOMIC_CNT),
                 .HAS_PMU        (`ARCSYNC_HAS_PMU),
                 .CORE_CLK_ENA_RST(`ARCSYNC_CORE_CLK_ENA_RST),
                 .AXI_ID_WIDTH   (16),
                 .AXI_ADDR_WIDTH(40),
                 .ARCSYNC_ADDR_WIDTH(40),
                 .BASE_ADDR_WIDTH(40),
                 .ARCSYNC_VIRT_MACHINES     (`ARCSYNC_VIRT_MACHINES),
                 .ARCSYNC_VIRT_PROC         (`ARCSYNC_VIRT_PROC),
                 .ARCSYNC_NUM_EVT_PER_CORE  (`ARCSYNC_NUM_EVT_PER_CORE),
                 .ARCSYNC_NUM_IRQ_PER_CORE  (`ARCSYNC_NUM_IRQ_PER_CORE),
                 .ARCSYNC_NUM_EVT_PER_VPROC (`ARCSYNC_NUM_EVT_PER_VPROC),
                 .ARCSYNC_NUM_IRQ_PER_VPROC (`ARCSYNC_NUM_IRQ_PER_VPROC),
                 .ADDR_EID_SEND_EVENT_0     (`ADDR_EID_SEND_EVENT_0),
                 .ADDR_EID_RAISE_IRQ_0      (`ADDR_EID_RAISE_IRQ_0),
                 .ADDR_EID_ACK_IRQ_0        (`ADDR_EID_ACK_IRQ_0),
                 .ADDR_VM0_EID_SEND_EVENT_0 (`ADDR_VM0_EID_SEND_EVENT_0), 
                 .ADDR_VM0_EID_RAISE_IRQ_0  (`ADDR_VM0_EID_RAISE_IRQ_0 ), 
                 .ADDR_VM0_EID_ACK_IRQ_0    (`ADDR_VM0_EID_ACK_IRQ_0   )
                )
     u_arcsync_core (
    .arcsync_core_exist          (arcsync_core_exist),
    .arcsync_core_wr_enable      (arcsync_core_wr_enable),
    .core_arcsync_arc64          (core_arcsync_arc64),
    .npx_L2_grp_exist            (npx_L2_grp_exist),
    .npx_L1_grp_exist            (npx_L1_grp_exist),
    .arcsync_core_intvbase       (arcsync_core_intvbase),
    .arcsync_core_csm_addr_base    (arcsync_core_csm_addr_base),
    .arcsync_core_periph_addr_base (arcsync_core_periph_addr_base),
    .cl_grp_clk_en               (cl_grp_clk_en),
    .cl_grp_rst                  (cl_grp_rst),
    .cl_enable                   (cl_enable),
    .arcsync_core_halt_req       (arcsync_core_halt_req),
    .core_arcsync_halt_ack       (core_arcsync_halt_ack),
    .arcsync_core_run_req        (arcsync_core_run_req),
    .core_arcsync_run_ack        (core_arcsync_run_ack),
    .core_arcsync_sys_sleep      (core_arcsync_sys_sleep),
    .core_arcsync_sys_sleep_mode (core_arcsync_sys_sleep_mode),
    .core_arcsync_sys_halt       (core_arcsync_sys_halt),
    .core_arcsync_sys_tf_halt    (core_arcsync_sys_tf_halt),
    .arcsync_core_rst_req        (arcsync_core_rst_req),
    .arcsync_core_clk_en         (arcsync_core_clk_en),
    .arcsync_core_irq            (arcsync_core_irq),
    .arcsync_core_event          (arcsync_core_event),
    .core_arcsync_pmode          (core_arcsync_pmode),
    .cluster_vproc_evt              (cluster_vproc_evt),
    .cluster_vproc_irq              (cluster_vproc_irq),
    .iso_override            (arcsync_core_iso_override),
    .arcsync_core_pd_mem     (arcsync_core_pd_mem),
    .arcsync_core_pd_logic   (arcsync_core_pd_logic),
    .arcsync_core_pd_logic1   (arcsync_core_pd_logic1),
    .arcsync_core_pd_logic2   (arcsync_core_pd_logic2),
    .arcsync_core_isolate    (arcsync_core_isolate),
    .arcsync_core_isolate_n  (arcsync_core_isolate_n),
    .arcsync_core_pwr_down   (arcsync_core_pwr_down),
    .arcsync_core_pu_rst     (arcsync_core_pu_rst),
    .arcsync_grp_isolate_n   (arcsync_grp_isolate_n),
    .arcsync_grp_isolate     (arcsync_grp_isolate  ),  
    .arcsync_grp_pd_logic    (arcsync_grp_pd_logic ),
    .arcsync_grp_pd_logic1   (arcsync_grp_pd_logic1 ),
    .arcsync_grp_pd_logic2   (arcsync_grp_pd_logic2 ),
    .arcsync_grp_pd_mem      (arcsync_grp_pd_mem   ),   
    .arcsync_grp_pu_rst      (arcsync_grp_pu_rst   ),   
    .arcsync_grp_pwr_down    (arcsync_grp_pwr_down ), 

    .arcsync_axi_arvalid  (internal_axi_arvalid),
    .arcsync_axi_arready  (internal_axi_arready),
    .arcsync_axi_arid     (internal_axi_arid),
    .arcsync_axi_araddr   (internal_axi_araddr_core),
    .arcsync_axi_arsize   (internal_axi_arsize),
    .arcsync_axi_arlen    (internal_axi_arlen),
    .arcsync_axi_arburst  (internal_axi_arburst),
    .arcsync_axi_arlock   (internal_axi_arlock),
    .arcsync_axi_arprot   (internal_axi_arprot),
    .arcsync_axi_arcache  (internal_axi_arcache),
    .arcsync_axi_awvalid  (internal_axi_awvalid),
    .arcsync_axi_awready  (internal_axi_awready),
    .arcsync_axi_awid     (internal_axi_awid),
    .arcsync_axi_awaddr   (internal_axi_awaddr_core),
    .arcsync_axi_awsize   (internal_axi_awsize),
    .arcsync_axi_awlen    (internal_axi_awlen),
    .arcsync_axi_awburst  (internal_axi_awburst),
    .arcsync_axi_awlock   (internal_axi_awlock),
    .arcsync_axi_awprot   (internal_axi_awprot),
    .arcsync_axi_awcache  (internal_axi_awcache),
    .arcsync_axi_rvalid   (internal_axi_rvalid),
    .arcsync_axi_rready   (internal_axi_rready),
    .arcsync_axi_rdata    (internal_axi_rdata),
    .arcsync_axi_rlast    (internal_axi_rlast),
    .arcsync_axi_rresp    (internal_axi_rresp),
    .arcsync_axi_rid      (internal_axi_rid),
    .arcsync_axi_wvalid   (internal_axi_wvalid),
    .arcsync_axi_wready   (internal_axi_wready),
    .arcsync_axi_wdata    (internal_axi_wdata_upd),
    .arcsync_axi_wstrb    (internal_axi_wstrb),
    .arcsync_axi_wlast    (internal_axi_wlast),
    .arcsync_axi_bid      (internal_axi_bid),
    .arcsync_axi_bvalid   (internal_axi_bvalid),
    .arcsync_axi_bresp    (internal_axi_bresp),
    .arcsync_axi_bready   (internal_axi_bready),
    .test_mode            (test_mode),
    .wdt_clk_en           (1'b1),
    .rst_a                (arcsync_core_rst),
    .clk                  (arcsync_clk)
  );

  logic  arcsync_axi_aruser;
  logic  arcsync_axi_awuser;
  logic  arcsync_axi_ruser;
  logic  arcsync_axi_wuser;
  logic  arcsync_axi_buser;

  assign internal_axi_ruser = 1'b0;
  assign internal_axi_buser = 1'b0;
  assign arcsync_axi_aruser = 1'b0;
  assign arcsync_axi_awuser = 1'b0;
  assign arcsync_axi_wuser = 1'b0;



  // CDC+slice
  npu_axi_cmd_t arcsync_axi_ar;
  npu_axi_cmd_t arcsync_axi_aw;
  
  assign arcsync_axi_ar.addr   =  arcsync_axi_araddr;
  assign arcsync_axi_ar.cache  =  arcsync_axi_arcache;
  assign arcsync_axi_ar.prot   =  arcsync_axi_arprot;
  assign arcsync_axi_ar.lock   =  npu_axi_lock_t'(arcsync_axi_arlock);
  assign arcsync_axi_ar.burst  =  npu_axi_burst_t'(arcsync_axi_arburst);
  assign arcsync_axi_ar.len    =  arcsync_axi_arlen;
  assign arcsync_axi_ar.size   =  arcsync_axi_arsize;
  
  assign arcsync_axi_aw.addr   =  arcsync_axi_awaddr;
  assign arcsync_axi_aw.cache  =  arcsync_axi_awcache;
  assign arcsync_axi_aw.prot   =  arcsync_axi_awprot;
  assign arcsync_axi_aw.lock   =  npu_axi_lock_t'(arcsync_axi_awlock);
  assign arcsync_axi_aw.burst  =  npu_axi_burst_t'(arcsync_axi_awburst);
  assign arcsync_axi_aw.len    =  arcsync_axi_awlen;
  assign arcsync_axi_aw.size   =  arcsync_axi_awsize;

  assign arcsync_axi_ar.region =  arcsync_axi_arregion;
  assign arcsync_axi_aw.region =  arcsync_axi_awregion;
  
  npu_axi_cmd_t internal_axi_ar;
  npu_axi_cmd_t internal_axi_aw;
  
  assign internal_axi_araddr   =  internal_axi_ar.addr;
  assign internal_axi_arcache  =  internal_axi_ar.cache;
  assign internal_axi_arprot   =  internal_axi_ar.prot;
  assign internal_axi_arlock   =  internal_axi_ar.lock;
  assign internal_axi_arburst  =  internal_axi_ar.burst;
  assign internal_axi_arlen    =  internal_axi_ar.len;
  assign internal_axi_arsize   =  internal_axi_ar.size;
  
  assign internal_axi_awaddr   =  internal_axi_aw.addr;
  assign internal_axi_awcache  =  internal_axi_aw.cache;
  assign internal_axi_awprot   =  internal_axi_aw.prot;
  assign internal_axi_awlock   =  internal_axi_aw.lock;
  assign internal_axi_awburst  =  internal_axi_aw.burst;
  assign internal_axi_awlen    =  internal_axi_aw.len;
  assign internal_axi_awsize   =  internal_axi_aw.size;




  `AXIWIRES(16,64,1,1,1,1,1,int_axi_);
  assign internal_axi_arvalid = int_axi_arvalid;
  assign internal_axi_arid    = int_axi_arid;
  assign internal_axi_aruser  = int_axi_aruser;
  assign internal_axi_ar      = int_axi_ar;
  assign internal_axi_rready  = int_axi_rready;
  assign internal_axi_awvalid = int_axi_awvalid;
  assign internal_axi_awid    = int_axi_awid;
  assign internal_axi_awuser  = int_axi_awuser;
  assign internal_axi_aw      = int_axi_aw;
  assign internal_axi_wvalid  = int_axi_wvalid;
  assign internal_axi_wdata   = int_axi_wdata;
  assign internal_axi_wstrb   = int_axi_wstrb;
  assign internal_axi_wuser   = int_axi_wuser;
  assign internal_axi_wlast   = int_axi_wlast;
  assign internal_axi_bready  = int_axi_bready;
  assign int_axi_arready      = internal_axi_arready;
  assign int_axi_rvalid       = internal_axi_rvalid;
  assign int_axi_rid          = internal_axi_rid;
  assign int_axi_rdata        = internal_axi_rdata;
  assign int_axi_ruser        = internal_axi_ruser;
  assign int_axi_rlast        = internal_axi_rlast;
  assign int_axi_awready      = internal_axi_awready;
  assign int_axi_wready       = internal_axi_wready;
  assign int_axi_bvalid       = internal_axi_bvalid;
  assign int_axi_bid          = internal_axi_bid;
  assign int_axi_buser        = internal_axi_buser;

  assign int_axi_rresp        = npu_axi_resp_t'(internal_axi_rresp);
  assign int_axi_bresp        = npu_axi_resp_t'(internal_axi_bresp);

  arcsync_async_bridge
    #(
      .AXIIDW         (16),
      .AXIDW          (64),
      .AXIAWUW        (1),
      .AXIWUW         (1),
      .AXIBUW         (1),
      .AXIARUW        (1),
      .AXIRUW         (1),
      // FIFO depth specification
      .AWFIFO_DEPTHL2 (1),
      .WFIFO_DEPTHL2  (1),
      .BFIFO_DEPTHL2  (1),
      .ARFIFO_DEPTHL2 (1),
      .RFIFO_DEPTHL2  (1),
      .CFG_INST       (0)   
    )
  u_arcsync_async_bridge
  (
     // clock and reset
     .axi_slv_clk       (arcsync_axi_clk),
     .axi_slv_rst_a     (arcsync_axi_rst_a),
     .axi_mst_clk       (arcsync_clk),
     .axi_mst_rst_a     (arcsync_rst_a),
     .test_mode         (test_mode),
     .tgt_pwr_dwn_a     (1'b0),
     .ini_pwr_dwn_a     (1'b0),

     // AXI slave interface
     `AXIINST(axi_slv_, arcsync_axi_),

     // AXI master interface
     `AXIINST(axi_mst_, int_axi_)
  );

  assign internal_axi_wdata_upd = internal_axi_wdata;


endmodule
