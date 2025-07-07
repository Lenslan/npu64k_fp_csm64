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
`include "arcsync_bus_gs_DW_axi_gs_all_includes.vh"

module arcsync_core
#(
  parameter CLUSTER_NUM     = 2,
  parameter NUM_CORE_C03    = 4,
  parameter NUM_CORE_C74    = 0,
  parameter MAX_CORE_NUM    = 4,
  parameter AC_NUM          = 3,
  parameter AC_WIDTH        = 8,
  parameter HAS_PMU         = 0,
  parameter CORE_CLK_ENA_RST= 1,
  parameter AXI_ID_WIDTH    = 16,
  parameter AXI_ADDR_WIDTH  = 32,
  parameter AXI_DATA_WIDTH  = 64,
  parameter AXI_WSTRB_WIDTH = 8,
  parameter CORE_NUM = CLUSTER_NUM * MAX_CORE_NUM,
  parameter ARCSYNC_DATA_WIDTH = 32,
  parameter ARCSYNC_ADDR_WIDTH = 32,
  parameter BASE_ADDR_WIDTH = 32,
  parameter ARCSYNC_VIRT_MACHINES     = 8,
  parameter ARCSYNC_VIRT_PROC         = 4,
  parameter ARCSYNC_NUM_EVT_PER_CORE  = 1,
  parameter ARCSYNC_NUM_IRQ_PER_CORE  = 1,
  parameter ARCSYNC_NUM_EVT_PER_VPROC = 1,
  parameter ARCSYNC_NUM_IRQ_PER_VPROC = 1,
  parameter ADDR_EID_RAISE_IRQ_0  = 32'h4000,
  parameter ADDR_EID_ACK_IRQ_0    = 32'h4A00,
  parameter ADDR_EID_SEND_EVENT_0 = 32'h4C80,
  parameter ADDR_VM0_EID_SEND_EVENT_0 = 32'h14000,
  parameter ADDR_VM0_EID_RAISE_IRQ_0  = 32'h14050,
  parameter ADDR_VM0_EID_ACK_IRQ_0    = 32'h14064
)
(
  //  ARCSync Usage
  //  +---------------------------------------------------------+
  //  | +------+  +-----+  +-----+  +----+  +-----+  +--------+ |
  //  | | GFRC |  | PMU |  | ACS |  | AC |  | EID |  | VM_EID | |
  //  | +------+  +-----+  +-----+  +----+  +-----+  +--------+ |
  //  |    |         |        |        |       |        |       |         
  //  |   <->       <->      <->      <->     <->      <->      |  
  //  |    |         |        |        |       |        |       |         
  //  |  +------------------------------------------------+     |
  //  |  |                  axi2reg (MMIO)                |     |
  //  |  +------------------------------------------------+     |
  //  |         |                         ARCSync               |
  //  +---------------------------------------------------------+
  //            ^     
  //            |axi     
  //    host----|     

  // sys base address
  // Per Cluster interfaces
  output    logic  [CLUSTER_NUM-1:0][BASE_ADDR_WIDTH-1:16]      arcsync_core_csm_addr_base,
  output    logic  [CLUSTER_NUM-1:0][BASE_ADDR_WIDTH-1:16]      arcsync_core_periph_addr_base,
  output    logic  [CLUSTER_NUM-1:0][3:0]                       cl_grp_clk_en,
  output    logic  [CLUSTER_NUM-1:0][4:0]                       cl_grp_rst, // NPX group rst, [0]: L2 grp_rst, [4:1]: L1 grp_rst
  output    logic  [CLUSTER_NUM-1:0]                            cl_enable, // cluster enable, 0: disable, 1: enable
  // Per Core interfaces
  // Core Type
  input     logic  [CORE_NUM-1:0]         arcsync_core_exist,                 
  input     logic  [CORE_NUM-1:0]         arcsync_core_wr_enable,
  input     logic  [CORE_NUM-1:0]         core_arcsync_arc64,                // ARC32 if '0'. ARC64 if '1'. 
  input     logic  [`ARCSYNC_NUM_CLUSTER-1:0]      npx_L2_grp_exist,
  input     logic  [`ARCSYNC_NUM_CLUSTER-1:0][3:0] npx_L1_grp_exist,
  // Boot                                                            
  output    logic  [CORE_NUM-1:0][63:0]   arcsync_core_intvbase,             // Reset value for core interrupt vector table base address
  // Halt
  output    logic  [CORE_NUM-1:0]         arcsync_core_halt_req,             // processor asynchronous halt request
  input     logic  [CORE_NUM-1:0]         core_arcsync_halt_ack,             // processor halt request acknowledge
  // Run
  output    logic  [CORE_NUM-1:0]         arcsync_core_run_req,              // processor asynchronous run request
  input     logic  [CORE_NUM-1:0]         core_arcsync_run_ack,              // processor run request acknowledge
  // Status
  input     logic  [CORE_NUM-1:0]         core_arcsync_sys_sleep,            // If true then processor is sleeping
  input     logic  [CORE_NUM-1:0][2:0]    core_arcsync_sys_sleep_mode,       // Indicated sleep mode of processor
  input     logic  [CORE_NUM-1:0]         core_arcsync_sys_halt,             // If true then processor is halted
  input     logic  [CORE_NUM-1:0]         core_arcsync_sys_tf_halt,          // If true then processor is halted due to triple fault exception
  // Reset
  output    logic  [CORE_NUM-1:0]         arcsync_core_rst_req,              // processor asynchronous reset request.
  // Clk_en
  output    logic  [CORE_NUM-1:0]         arcsync_core_clk_en,               // core clk_en.
  // IRQ and Event
  output    logic  [CORE_NUM-1:0][(ARCSYNC_NUM_IRQ_PER_CORE + 1)-1:0]    arcsync_core_irq,                  // Asynchronous irq. Plus 1 is ac irq
  output    logic  [CORE_NUM-1:0][(ARCSYNC_NUM_EVT_PER_CORE + 1)-1:0]    arcsync_core_event,                // Asynchronous event. Plus 1 is ac event
                                                                        // bit[0] from AC, bit[1] from EID
  // PMode   
  input     logic  [CORE_NUM-1:0][2:0]    core_arcsync_pmode,                // Power Mode Current State

  output logic [CLUSTER_NUM-1:0][(ARCSYNC_VIRT_MACHINES*(ARCSYNC_NUM_EVT_PER_VPROC + 1))-1:0]  cluster_vproc_evt,
  output logic [CLUSTER_NUM-1:0][(ARCSYNC_VIRT_MACHINES*(ARCSYNC_NUM_IRQ_PER_VPROC + 1))-1:0]  cluster_vproc_irq,


    //npx power interface
  // PMU
  output    logic  [CORE_NUM-1:0]         arcsync_core_isolate_n,        // Isolate control signal for power domain 1 of component (active low)
  output    logic  [CORE_NUM-1:0]         arcsync_core_isolate,          // Isolate control signal for power domain 1 of component (active high)
  output    logic  [CORE_NUM-1:0]         arcsync_core_pd_logic,               // Power down of power domain 1 logic
  output    logic  [CORE_NUM-1:0]         arcsync_core_pd_logic1,               // Power down of power domain 1 logic1
  output    logic  [CORE_NUM-1:0]         arcsync_core_pd_logic2,               // Power down of power domain 1 logic2
  output    logic  [CORE_NUM-1:0]         arcsync_core_pd_mem,           // Power down of power domain 1 memories (SRAM)
  output    logic  [CORE_NUM-1:0]         arcsync_core_pu_rst,               // Power up reset
  output    logic  [CORE_NUM-1:0]         arcsync_core_pwr_down,               // Power down

  output    logic  [CLUSTER_NUM-1:0][3:0]         arcsync_grp_isolate_n,  
  output    logic  [CLUSTER_NUM-1:0][3:0]         arcsync_grp_isolate,  
  output    logic  [CLUSTER_NUM-1:0][3:0]         arcsync_grp_pd_logic,
  output    logic  [CLUSTER_NUM-1:0][3:0]         arcsync_grp_pd_logic1,
  output    logic  [CLUSTER_NUM-1:0][3:0]         arcsync_grp_pd_logic2,
  output    logic  [CLUSTER_NUM-1:0][3:0]         arcsync_grp_pd_mem,   
  output    logic  [CLUSTER_NUM-1:0][3:0]         arcsync_grp_pu_rst,   // L1 group pu_rst
  output    logic  [CLUSTER_NUM-1:0][3:0]         arcsync_grp_pwr_down, 

  // AXI Interfaces
  input     logic                         arcsync_axi_arvalid,
  output    logic                         arcsync_axi_arready,
  input     logic   [AXI_ID_WIDTH-1:0]    arcsync_axi_arid,
  input     logic   [AXI_ADDR_WIDTH-1:0]  arcsync_axi_araddr,
  input     logic   [2:0]                 arcsync_axi_arsize,
  input     logic   [3:0]                 arcsync_axi_arlen,
  input     logic   [1:0]                 arcsync_axi_arburst,
  input     logic                         arcsync_axi_arlock,
  input     logic   [2:0]                 arcsync_axi_arprot,
  input     logic   [3:0]                 arcsync_axi_arcache,
  input     logic                         arcsync_axi_awvalid,
  output    logic                         arcsync_axi_awready,
  input     logic   [AXI_ID_WIDTH-1:0]    arcsync_axi_awid,
  input     logic   [AXI_ADDR_WIDTH-1:0]  arcsync_axi_awaddr,
  input     logic   [2:0]                 arcsync_axi_awsize,
  input     logic   [3:0]                 arcsync_axi_awlen,
  input     logic   [1:0]                 arcsync_axi_awburst,
  input     logic                         arcsync_axi_awlock,
  input     logic   [2:0]                 arcsync_axi_awprot,
  input     logic   [3:0]                 arcsync_axi_awcache,
  
  output    logic                         arcsync_axi_rvalid,
  input     logic                         arcsync_axi_rready,
  output    logic   [AXI_DATA_WIDTH-1:0]  arcsync_axi_rdata,
  output    logic                         arcsync_axi_rlast,
  output    logic   [1:0]                 arcsync_axi_rresp,
  output    logic   [AXI_ID_WIDTH-1:0]    arcsync_axi_rid,         
  
  input     logic                         arcsync_axi_wvalid,
  output    logic                         arcsync_axi_wready,
  input     logic   [AXI_DATA_WIDTH-1:0]  arcsync_axi_wdata,
  input     logic   [AXI_WSTRB_WIDTH-1:0] arcsync_axi_wstrb,
  input     logic                         arcsync_axi_wlast,
  
  output    logic    [AXI_ID_WIDTH-1:0]   arcsync_axi_bid,
  output    logic                         arcsync_axi_bvalid,
  output    logic    [1:0]                arcsync_axi_bresp,
  input     logic                         arcsync_axi_bready,

  // Clock, reset and configuration
  input     logic                         test_mode,  // Test mode

  input     logic                         iso_override,  //Isolate override control signal for power domain (used for test) when test_mode valid


  input     logic                         wdt_clk_en, // Watchdog timer clock enable
  input     logic                         rst_a,      // Asynchronous reset, active high
  input     logic                         clk         // Clock
);

localparam  ARCSYNC_VIRT_MACHINES_WIDTH = $clog2(ARCSYNC_VIRT_MACHINES);
localparam  CLUSTER_WIDTH = ($clog2(CLUSTER_NUM)==0) ? 1 : $clog2(CLUSTER_NUM);
localparam  TOTAL_VP_WIDTH = ($clog2(ARCSYNC_VIRT_MACHINES*ARCSYNC_VIRT_PROC)==0) ? 1 : $clog2(ARCSYNC_VIRT_MACHINES*ARCSYNC_VIRT_PROC);

  logic                    unused;
// spyglass disable_block Ac_conv03
// unused siganl
  assign unused = arcsync_axi_arlock || arcsync_axi_awlock || wdt_clk_en;
// spyglass enable_block Ac_conv03

//-------------------------------------------------------------------------------------------------------
// AXI2REG
//-------------------------------------------------------------------------------------------------------
    logic                            mmio_sel_gfrc; 
    logic                            mmio_sel_pmu; 
     logic                           mmio_sel_sfty; 
    logic                            mmio_sel_acs;  
    logic                            mmio_sel_eid;  
    logic                            mmio_sel_ac;   
    logic                            mmio_sel_map_vm_vproc;
    logic                            mmio_sel_vm_eid;
    logic   [AXI_ADDR_WIDTH-1:0]     mmio_addr;     
    logic                            mmio_wen;      
    logic                            mmio_ren;      
    logic                            mmio_gfrc_read_64b;      
    logic   [AXI_DATA_WIDTH-1:0]     mmio_rdata_gfrc; 
    logic   [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_pmu;  
    logic   [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_sfty;  
    logic   [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_acs;  
    logic   [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_eid;  
    logic   [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_ac;   
    logic   [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_map_vm_vproc;
    logic   [ARCSYNC_DATA_WIDTH-1:0] mmio_rdata_vm_eid;
    logic   [ARCSYNC_DATA_WIDTH-1:0] mmio_wdata;    
    logic   [1:0]                    mmio_resp_gfrc; 
    logic   [1:0]                    mmio_resp_pmu; 
    logic   [1:0]                    mmio_resp_sfty; 
    logic   [1:0]                    mmio_resp_acs;  
    logic   [1:0]                    mmio_resp_eid;  
    logic   [1:0]                    mmio_resp_ac; 
    logic   [1:0]                    mmio_resp_map_vm_vproc;
    logic   [1:0]                    mmio_resp_vm_eid;
    logic   [ARCSYNC_VIRT_MACHINES-1:0][CLUSTER_NUM-1:0] vm_vp_wr_enable;
    logic                            npu_ctrl_safety;
    logic   [1:0]                    num_vm;

    ///////////////// Non-VM mode AC IRQ/Event /////////////////
    logic       [CORE_NUM-1:0]    arcsync_core_ac_irq;
    logic       [CORE_NUM-1:0]    arcsync_core_ac_event;
    /////////////////  VM mode AC IRQ/Event /////////////////
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm0_arcsync_core_ac_irq;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm0_arcsync_core_ac_event;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm1_arcsync_core_ac_irq;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm1_arcsync_core_ac_event;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm2_arcsync_core_ac_irq;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm2_arcsync_core_ac_event;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm3_arcsync_core_ac_irq;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm3_arcsync_core_ac_event;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm4_arcsync_core_ac_irq;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm4_arcsync_core_ac_event;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm5_arcsync_core_ac_irq;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm5_arcsync_core_ac_event;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm6_arcsync_core_ac_irq;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm6_arcsync_core_ac_event;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm7_arcsync_core_ac_irq;
    logic       [ARCSYNC_VIRT_PROC-1:0]    vm7_arcsync_core_ac_event;

    logic   [CORE_NUM*ARCSYNC_NUM_IRQ_PER_CORE-1:0]           arcsync_core_eid_irq;
    logic   [CORE_NUM*ARCSYNC_NUM_EVT_PER_CORE-1:0]           arcsync_core_eid_event;
    logic   [CLUSTER_NUM-1:0]        core0_sys_sleep;

    //logic [ARCSYNC_VIRT_MACHINES-1:0][ARCSYNC_VIRT_PROC-1:0] vm_vproc_enable;
    logic [ARCSYNC_VIRT_MACHINES*ARCSYNC_VIRT_PROC-1:0][ARCSYNC_DATA_WIDTH-1:0] map_vm_vproc;

    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm0_core_exist;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm0_core_wr_enable;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm1_core_exist;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm1_core_wr_enable;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm2_core_exist;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm2_core_wr_enable;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm3_core_exist;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm3_core_wr_enable;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm4_core_exist;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm4_core_wr_enable;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm5_core_exist;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm5_core_wr_enable;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm6_core_exist;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm6_core_wr_enable;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm7_core_exist;
    logic       [ARCSYNC_VIRT_PROC-1:0] arcsync_vm7_core_wr_enable;

    logic [CLUSTER_NUM-1:0][(ARCSYNC_VIRT_MACHINES*ARCSYNC_NUM_EVT_PER_VPROC)-1:0]  cluster_vm_eid_evt;
    logic [CLUSTER_NUM-1:0][(ARCSYNC_VIRT_MACHINES*ARCSYNC_NUM_IRQ_PER_VPROC)-1:0]  cluster_vm_eid_irq;
    logic [CLUSTER_NUM-1:0][(ARCSYNC_VIRT_MACHINES)-1:0]  cluster_vm_ac_evt;
    logic [CLUSTER_NUM-1:0][(ARCSYNC_VIRT_MACHINES)-1:0]  cluster_vm_ac_irq;

      for (genvar i=0; i<CLUSTER_NUM; i++) // {
      begin: gen_cluster_vm_eid_loop_i
        for (genvar j=0; j<ARCSYNC_VIRT_MACHINES; j++) // {
        begin: gen_cluster_vm_eid_evt_loop_j
          for (genvar k=0; k<(ARCSYNC_NUM_EVT_PER_VPROC+1); k++) // {
          begin: gen_cluster_vm_eid_evt_loop_k
            if (k==0) begin: gen_cluster_vm_eid_evt_ac_connection
              assign cluster_vproc_evt[i][j*(ARCSYNC_NUM_EVT_PER_VPROC+1)] = cluster_vm_ac_evt[i][j];
            end
            else begin:gen_cluster_vm_eid_evt_eid_connection
              assign cluster_vproc_evt[i][j*(ARCSYNC_NUM_EVT_PER_VPROC+1) + k] = cluster_vm_eid_evt[i][j*ARCSYNC_NUM_EVT_PER_VPROC + (k-1)];
            end
          end // }

          for (genvar k=0; k<(ARCSYNC_NUM_IRQ_PER_VPROC+1); k++) // {
          begin: gen_cluster_vm_eid_irq_loop_k
            if (k==0) begin: gen_cluster_vm_eid_irq_ac_connection
              assign cluster_vproc_irq[i][j*(ARCSYNC_NUM_IRQ_PER_VPROC+1)] = cluster_vm_ac_irq[i][j];
            end
            else begin:gen_cluster_vm_eid_irq_eid_connection
              assign cluster_vproc_irq[i][j*(ARCSYNC_NUM_IRQ_PER_VPROC+1) + k] = cluster_vm_eid_irq[i][j*ARCSYNC_NUM_IRQ_PER_VPROC + (k-1)];
            end
          end // }
        end // }

        assign core0_sys_sleep[i] = core_arcsync_sys_sleep[i*MAX_CORE_NUM];
      end // }

      for (genvar i=0; i<CLUSTER_NUM; i++) // {
      begin: gen_cluster_vm_eid_irq_loop_i

      end // }



    for (genvar i=0; i<CORE_NUM; i++) // {
    begin: gen_arcsync_corq_irq_CORE_NUM_loop
      for (genvar j=0; j<(ARCSYNC_NUM_IRQ_PER_CORE+1); j++) // {
      begin: gen_arcsync_corq_irq_NUM_IRQ_loop
        if (j==0) begin: gen_ac_irq_connection
          assign arcsync_core_irq[i][j]   = arcsync_core_ac_irq[i];
        end
        else begin: gen_eid_irq_connection
          assign arcsync_core_irq[i][j]   = arcsync_core_eid_irq[(j-1)*CORE_NUM + i];
        end
      end // }
    end // }

    for (genvar i=0; i<CORE_NUM; i++) // {
    begin: gen_arcsync_corq_event_CORE_NUM_loop
      for (genvar j=0; j<(ARCSYNC_NUM_EVT_PER_CORE+1); j++) // {
      begin: gen_arcsync_corq_event_NUM_EVT_loop
        if (j==0) begin: gen_ac_event_connection
          assign arcsync_core_event[i][j]   = arcsync_core_ac_event[i];
        end
        else begin: gen_eid_event_connection
          assign arcsync_core_event[i][j]   = arcsync_core_eid_event[(j-1)*CORE_NUM + i];
        end
      end // }
    end // }

  assign npu_ctrl_safety = 1'b0;

  assign num_vm = 2'd2;

    arcsync_axi2reg #( 
                      .CLUSTER_NUM         (CLUSTER_NUM), 
                      .NUM_CORE_C03        (NUM_CORE_C03), 
                      .NUM_CORE_C74        (NUM_CORE_C74), 
                      .MAX_CORE_NUM        (MAX_CORE_NUM), 
                      .HAS_PMU             (HAS_PMU),
                      .AXI_ID_WIDTH        (AXI_ID_WIDTH),    
                      .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),  
                      .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),  
                      .ARCSYNC_ADDR_WIDTH  (ARCSYNC_ADDR_WIDTH),
                      .ARCSYNC_DATA_WIDTH  (ARCSYNC_DATA_WIDTH),  
                      .AXI_WSTRB_WIDTH     (AXI_WSTRB_WIDTH), 
                      .AC_NUM              (AC_NUM),
                      .CORE_NUM            (CORE_NUM),
                      .BASE_ADDR_WIDTH     (BASE_ADDR_WIDTH),
                      .ARCSYNC_VIRT_MACHINES(ARCSYNC_VIRT_MACHINES),
                      .CL_GRP_CLK_EN_RST   (CORE_CLK_ENA_RST)
                     )
       u_arcsync_axi2reg (
         .npx_L2_grp_exist              (npx_L2_grp_exist),
         .npx_L1_grp_exist              (npx_L1_grp_exist),
         .arcsync_core_csm_addr_base    (arcsync_core_csm_addr_base),
         .arcsync_core_periph_addr_base (arcsync_core_periph_addr_base),
         .cl_enable                     (cl_enable),
         .cl_grp_clk_en                 (cl_grp_clk_en),
         .cl_grp_rst                    (cl_grp_rst),
         .npu_ctrl_safety               (npu_ctrl_safety),
         .num_vm                        (num_vm),
         .arcsync_axi_arvalid   (arcsync_axi_arvalid),
         .arcsync_axi_arready   (arcsync_axi_arready),
         .arcsync_axi_arid      (arcsync_axi_arid),
         .arcsync_axi_araddr    (arcsync_axi_araddr),
         .arcsync_axi_arsize    (arcsync_axi_arsize),
         .arcsync_axi_arlen     (arcsync_axi_arlen),
         .arcsync_axi_arburst   (arcsync_axi_arburst),
         .arcsync_axi_arprot    (arcsync_axi_arprot),
         .arcsync_axi_arcache   (arcsync_axi_arcache),
         .arcsync_axi_awvalid   (arcsync_axi_awvalid),
         .arcsync_axi_awready   (arcsync_axi_awready),
         .arcsync_axi_awid      (arcsync_axi_awid),
         .arcsync_axi_awaddr    (arcsync_axi_awaddr),
         .arcsync_axi_awsize    (arcsync_axi_awsize),
         .arcsync_axi_awlen     (arcsync_axi_awlen),
         .arcsync_axi_awburst   (arcsync_axi_awburst),
         .arcsync_axi_awprot    (arcsync_axi_awprot),
         .arcsync_axi_awcache   (arcsync_axi_awcache),
         .arcsync_axi_rvalid    (arcsync_axi_rvalid),
         .arcsync_axi_rready    (arcsync_axi_rready),
         .arcsync_axi_rdata     (arcsync_axi_rdata),
         .arcsync_axi_rlast     (arcsync_axi_rlast),
         .arcsync_axi_rresp     (arcsync_axi_rresp),
         .arcsync_axi_rid       (arcsync_axi_rid),
         .arcsync_axi_wvalid    (arcsync_axi_wvalid),
         .arcsync_axi_wready    (arcsync_axi_wready),
         .arcsync_axi_wdata     (arcsync_axi_wdata),
         .arcsync_axi_wstrb     (arcsync_axi_wstrb),
         .arcsync_axi_wlast     (arcsync_axi_wlast),
         .arcsync_axi_bid       (arcsync_axi_bid),
         .arcsync_axi_bvalid    (arcsync_axi_bvalid),
         .arcsync_axi_bresp     (arcsync_axi_bresp),
         .arcsync_axi_bready    (arcsync_axi_bready),
         .mmio_sel_gfrc         (mmio_sel_gfrc),
         .mmio_sel_pmu          (mmio_sel_pmu),
         .mmio_sel_sfty         (mmio_sel_sfty),
         .mmio_sel_acs          (mmio_sel_acs),
         .mmio_sel_eid          (mmio_sel_eid),
         .mmio_sel_ac           (mmio_sel_ac),
         .mmio_sel_map_vm_vproc (mmio_sel_map_vm_vproc),
         .mmio_sel_vm_eid       (mmio_sel_vm_eid      ),
         .mmio_addr             (mmio_addr),
         .mmio_wen              (mmio_wen),
         .mmio_ren              (mmio_ren),
         .mmio_gfrc_read_64b    (mmio_gfrc_read_64b),
         .mmio_wdata            (mmio_wdata),
         .mmio_rdata_gfrc       (mmio_rdata_gfrc),
         .mmio_rdata_pmu        (mmio_rdata_pmu),
         .mmio_rdata_sfty       (mmio_rdata_sfty),
         .mmio_rdata_acs        (mmio_rdata_acs),
         .mmio_rdata_eid        (mmio_rdata_eid),
         .mmio_rdata_ac         (mmio_rdata_ac),
         .mmio_rdata_map_vm_vproc(mmio_rdata_map_vm_vproc),
         .mmio_rdata_vm_eid     (mmio_rdata_vm_eid      ),
         .mmio_resp_gfrc        (mmio_resp_gfrc),
         .mmio_resp_pmu         (mmio_resp_pmu),
         .mmio_resp_sfty        (mmio_resp_sfty),
         .mmio_resp_acs         (mmio_resp_acs),
         .mmio_resp_eid         (mmio_resp_eid),
         .mmio_resp_ac          (mmio_resp_ac),
         .mmio_resp_map_vm_vproc(mmio_resp_map_vm_vproc),
         .mmio_resp_vm_eid      (mmio_resp_vm_eid),
         .rst_a                 (rst_a),
         .clk                   (clk)
    );

//-------------------------------------------------------------------------------------------------------
// Global Free Runnung Clock
//-------------------------------------------------------------------------------------------------------
    arcsync_gfrc #( 
                  .ADDR_WIDTH(ARCSYNC_ADDR_WIDTH),
                  .DATA_WIDTH(AXI_DATA_WIDTH)
                )
       u_arcsync_gfrc (
         .mmio_sel              (mmio_sel_gfrc),
         .mmio_addr             (mmio_addr),
         .mmio_wen              (mmio_wen),
         .mmio_ren              (mmio_ren),
         .mmio_gfrc_read_64b    (mmio_gfrc_read_64b),
         .mmio_rdata            (mmio_rdata_gfrc),
         .mmio_wdata            ({32'b0, mmio_wdata}),
         .mmio_resp             (mmio_resp_gfrc),
         .rst_a                 (rst_a),
         .clk                   (clk)
    );
//-------------------------------------------------------------------------------------------------------
// Event and Interrupt Dispatch 
//-------------------------------------------------------------------------------------------------------
    arcsync_eid #( 
                  .ADDR_WIDTH(ARCSYNC_ADDR_WIDTH),
                  .DATA_WIDTH(ARCSYNC_DATA_WIDTH),
                  .CORE_NUM(CORE_NUM),
                  .NUM_IRQ_PER_CORE(ARCSYNC_NUM_IRQ_PER_CORE), 
                  .NUM_EVT_PER_CORE(ARCSYNC_NUM_EVT_PER_CORE),
                  .ADDR_EID_SEND_EVENT_0(ADDR_EID_SEND_EVENT_0),
                  .ADDR_EID_RAISE_IRQ_0 (ADDR_EID_RAISE_IRQ_0),
                  .ADDR_EID_ACK_IRQ_0   (ADDR_EID_ACK_IRQ_0)
                 )
       u_arcsync_eid (
         .arcsync_core_exist     (arcsync_core_exist),
         .arcsync_core_wr_enable (arcsync_core_wr_enable),
         .mmio_sel               (mmio_sel_eid),
         .mmio_addr              (mmio_addr),
         .mmio_wen               (mmio_wen),
         .mmio_ren               (mmio_ren),
         .mmio_rdata             (mmio_rdata_eid),
         .mmio_wdata             (mmio_wdata),
         .mmio_resp              (mmio_resp_eid),
         .sys_sleep              (core_arcsync_sys_sleep),
         .arcsync_core_irq       (arcsync_core_eid_irq),
         .arcsync_core_event     (arcsync_core_eid_event),
         .rst_a                  (rst_a),
         .clk                    (clk)
    );

//-------------------------------------------------------------------------------------------------------
// Virtual Machine Event and Interrupt Dispatch 
//-------------------------------------------------------------------------------------------------------
    arcsync_vm_eid
    #(
      .ADDR_WIDTH            (ARCSYNC_ADDR_WIDTH),
      .DATA_WIDTH            (ARCSYNC_DATA_WIDTH),
      .CLUSTER_NUM           (CLUSTER_NUM),
      .VIRT_MACHINES         (ARCSYNC_VIRT_MACHINES),
      .VIRT_PROC             (ARCSYNC_VIRT_PROC    ),
      .NUM_IRQ_PER_VPROC     (ARCSYNC_NUM_IRQ_PER_VPROC    ),
      .NUM_EVT_PER_VPROC     (ARCSYNC_NUM_EVT_PER_VPROC    ),
      .ADDR_VM0_EID_SEND_EVENT_0(ADDR_VM0_EID_SEND_EVENT_0),
      .ADDR_VM0_EID_RAISE_IRQ_0 (ADDR_VM0_EID_RAISE_IRQ_0 ),
      .ADDR_VM0_EID_ACK_IRQ_0   (ADDR_VM0_EID_ACK_IRQ_0   )
    )
    u_arcsync_vm_eid
    (
      .mmio_sel_map_vm_vproc    (mmio_sel_map_vm_vproc),
      .mmio_sel_vm_eid          (mmio_sel_vm_eid),
      .mmio_addr                (mmio_addr),
      .mmio_wen                 (mmio_wen ),
      .mmio_ren                 (mmio_ren ),
      .mmio_rdata_map_vm_vproc  (mmio_rdata_map_vm_vproc),
      .mmio_rdata_vm_eid        (mmio_rdata_vm_eid),
      .mmio_wdata               (mmio_wdata),
      .mmio_resp_map_vm_vproc   (mmio_resp_map_vm_vproc),
      .mmio_resp_vm_eid         (mmio_resp_vm_eid),
      .core0_sys_sleep          (core0_sys_sleep),
      .cluster_vm_evt           (cluster_vm_eid_evt),
      .cluster_vm_irq           (cluster_vm_eid_irq),
      //.vm_vproc_enable          (vm_vproc_enable),
      .map_vm_vproc             (map_vm_vproc),
      .vm_vp_wr_enable          (vm_vp_wr_enable),
      .rst_a                    (rst_a),
      .clk                      (clk)
    );

//-------------------------------------------------------------------------------------------------------
// Atomic Counter (include VM Atomic Counter)
//-------------------------------------------------------------------------------------------------------
    assign arcsync_vm0_core_exist[0] = map_vm_vproc[0*ARCSYNC_VIRT_PROC + 0][31] & (map_vm_vproc[0*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[0*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0])
          0: arcsync_vm0_core_wr_enable[0] = cl_enable[0] & arcsync_vm0_core_exist[0];
          1: arcsync_vm0_core_wr_enable[0] = cl_enable[1] & arcsync_vm0_core_exist[0];
          2: arcsync_vm0_core_wr_enable[0] = cl_enable[2] & arcsync_vm0_core_exist[0];
        default: arcsync_vm0_core_wr_enable[0] = 1'b0;
      endcase
    assign arcsync_vm0_core_exist[1] = map_vm_vproc[0*ARCSYNC_VIRT_PROC + 1][31] & (map_vm_vproc[0*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[0*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0])
          0: arcsync_vm0_core_wr_enable[1] = cl_enable[0] & arcsync_vm0_core_exist[1];
          1: arcsync_vm0_core_wr_enable[1] = cl_enable[1] & arcsync_vm0_core_exist[1];
          2: arcsync_vm0_core_wr_enable[1] = cl_enable[2] & arcsync_vm0_core_exist[1];
        default: arcsync_vm0_core_wr_enable[1] = 1'b0;
      endcase
    assign arcsync_vm0_core_exist[2] = map_vm_vproc[0*ARCSYNC_VIRT_PROC + 2][31] & (map_vm_vproc[0*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[0*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0])
          0: arcsync_vm0_core_wr_enable[2] = cl_enable[0] & arcsync_vm0_core_exist[2];
          1: arcsync_vm0_core_wr_enable[2] = cl_enable[1] & arcsync_vm0_core_exist[2];
          2: arcsync_vm0_core_wr_enable[2] = cl_enable[2] & arcsync_vm0_core_exist[2];
        default: arcsync_vm0_core_wr_enable[2] = 1'b0;
      endcase
  assign vm_vp_wr_enable[0] = arcsync_vm0_core_wr_enable;
    assign arcsync_vm1_core_exist[0] = map_vm_vproc[1*ARCSYNC_VIRT_PROC + 0][31] & (map_vm_vproc[1*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[1*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0])
          0: arcsync_vm1_core_wr_enable[0] = cl_enable[0] & arcsync_vm1_core_exist[0];
          1: arcsync_vm1_core_wr_enable[0] = cl_enable[1] & arcsync_vm1_core_exist[0];
          2: arcsync_vm1_core_wr_enable[0] = cl_enable[2] & arcsync_vm1_core_exist[0];
        default: arcsync_vm1_core_wr_enable[0] = 1'b0;
      endcase
    assign arcsync_vm1_core_exist[1] = map_vm_vproc[1*ARCSYNC_VIRT_PROC + 1][31] & (map_vm_vproc[1*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[1*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0])
          0: arcsync_vm1_core_wr_enable[1] = cl_enable[0] & arcsync_vm1_core_exist[1];
          1: arcsync_vm1_core_wr_enable[1] = cl_enable[1] & arcsync_vm1_core_exist[1];
          2: arcsync_vm1_core_wr_enable[1] = cl_enable[2] & arcsync_vm1_core_exist[1];
        default: arcsync_vm1_core_wr_enable[1] = 1'b0;
      endcase
    assign arcsync_vm1_core_exist[2] = map_vm_vproc[1*ARCSYNC_VIRT_PROC + 2][31] & (map_vm_vproc[1*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[1*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0])
          0: arcsync_vm1_core_wr_enable[2] = cl_enable[0] & arcsync_vm1_core_exist[2];
          1: arcsync_vm1_core_wr_enable[2] = cl_enable[1] & arcsync_vm1_core_exist[2];
          2: arcsync_vm1_core_wr_enable[2] = cl_enable[2] & arcsync_vm1_core_exist[2];
        default: arcsync_vm1_core_wr_enable[2] = 1'b0;
      endcase
  assign vm_vp_wr_enable[1] = arcsync_vm1_core_wr_enable;
    assign arcsync_vm2_core_exist[0] = map_vm_vproc[2*ARCSYNC_VIRT_PROC + 0][31] & (map_vm_vproc[2*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[2*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0])
          0: arcsync_vm2_core_wr_enable[0] = cl_enable[0] & arcsync_vm2_core_exist[0];
          1: arcsync_vm2_core_wr_enable[0] = cl_enable[1] & arcsync_vm2_core_exist[0];
          2: arcsync_vm2_core_wr_enable[0] = cl_enable[2] & arcsync_vm2_core_exist[0];
        default: arcsync_vm2_core_wr_enable[0] = 1'b0;
      endcase
    assign arcsync_vm2_core_exist[1] = map_vm_vproc[2*ARCSYNC_VIRT_PROC + 1][31] & (map_vm_vproc[2*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[2*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0])
          0: arcsync_vm2_core_wr_enable[1] = cl_enable[0] & arcsync_vm2_core_exist[1];
          1: arcsync_vm2_core_wr_enable[1] = cl_enable[1] & arcsync_vm2_core_exist[1];
          2: arcsync_vm2_core_wr_enable[1] = cl_enable[2] & arcsync_vm2_core_exist[1];
        default: arcsync_vm2_core_wr_enable[1] = 1'b0;
      endcase
    assign arcsync_vm2_core_exist[2] = map_vm_vproc[2*ARCSYNC_VIRT_PROC + 2][31] & (map_vm_vproc[2*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[2*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0])
          0: arcsync_vm2_core_wr_enable[2] = cl_enable[0] & arcsync_vm2_core_exist[2];
          1: arcsync_vm2_core_wr_enable[2] = cl_enable[1] & arcsync_vm2_core_exist[2];
          2: arcsync_vm2_core_wr_enable[2] = cl_enable[2] & arcsync_vm2_core_exist[2];
        default: arcsync_vm2_core_wr_enable[2] = 1'b0;
      endcase
  assign vm_vp_wr_enable[2] = arcsync_vm2_core_wr_enable;
    assign arcsync_vm3_core_exist[0] = map_vm_vproc[3*ARCSYNC_VIRT_PROC + 0][31] & (map_vm_vproc[3*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[3*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0])
          0: arcsync_vm3_core_wr_enable[0] = cl_enable[0] & arcsync_vm3_core_exist[0];
          1: arcsync_vm3_core_wr_enable[0] = cl_enable[1] & arcsync_vm3_core_exist[0];
          2: arcsync_vm3_core_wr_enable[0] = cl_enable[2] & arcsync_vm3_core_exist[0];
        default: arcsync_vm3_core_wr_enable[0] = 1'b0;
      endcase
    assign arcsync_vm3_core_exist[1] = map_vm_vproc[3*ARCSYNC_VIRT_PROC + 1][31] & (map_vm_vproc[3*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[3*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0])
          0: arcsync_vm3_core_wr_enable[1] = cl_enable[0] & arcsync_vm3_core_exist[1];
          1: arcsync_vm3_core_wr_enable[1] = cl_enable[1] & arcsync_vm3_core_exist[1];
          2: arcsync_vm3_core_wr_enable[1] = cl_enable[2] & arcsync_vm3_core_exist[1];
        default: arcsync_vm3_core_wr_enable[1] = 1'b0;
      endcase
    assign arcsync_vm3_core_exist[2] = map_vm_vproc[3*ARCSYNC_VIRT_PROC + 2][31] & (map_vm_vproc[3*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[3*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0])
          0: arcsync_vm3_core_wr_enable[2] = cl_enable[0] & arcsync_vm3_core_exist[2];
          1: arcsync_vm3_core_wr_enable[2] = cl_enable[1] & arcsync_vm3_core_exist[2];
          2: arcsync_vm3_core_wr_enable[2] = cl_enable[2] & arcsync_vm3_core_exist[2];
        default: arcsync_vm3_core_wr_enable[2] = 1'b0;
      endcase
  assign vm_vp_wr_enable[3] = arcsync_vm3_core_wr_enable;
    assign arcsync_vm4_core_exist[0] = map_vm_vproc[4*ARCSYNC_VIRT_PROC + 0][31] & (map_vm_vproc[4*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[4*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0])
          0: arcsync_vm4_core_wr_enable[0] = cl_enable[0] & arcsync_vm4_core_exist[0];
          1: arcsync_vm4_core_wr_enable[0] = cl_enable[1] & arcsync_vm4_core_exist[0];
          2: arcsync_vm4_core_wr_enable[0] = cl_enable[2] & arcsync_vm4_core_exist[0];
        default: arcsync_vm4_core_wr_enable[0] = 1'b0;
      endcase
    assign arcsync_vm4_core_exist[1] = map_vm_vproc[4*ARCSYNC_VIRT_PROC + 1][31] & (map_vm_vproc[4*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[4*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0])
          0: arcsync_vm4_core_wr_enable[1] = cl_enable[0] & arcsync_vm4_core_exist[1];
          1: arcsync_vm4_core_wr_enable[1] = cl_enable[1] & arcsync_vm4_core_exist[1];
          2: arcsync_vm4_core_wr_enable[1] = cl_enable[2] & arcsync_vm4_core_exist[1];
        default: arcsync_vm4_core_wr_enable[1] = 1'b0;
      endcase
    assign arcsync_vm4_core_exist[2] = map_vm_vproc[4*ARCSYNC_VIRT_PROC + 2][31] & (map_vm_vproc[4*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[4*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0])
          0: arcsync_vm4_core_wr_enable[2] = cl_enable[0] & arcsync_vm4_core_exist[2];
          1: arcsync_vm4_core_wr_enable[2] = cl_enable[1] & arcsync_vm4_core_exist[2];
          2: arcsync_vm4_core_wr_enable[2] = cl_enable[2] & arcsync_vm4_core_exist[2];
        default: arcsync_vm4_core_wr_enable[2] = 1'b0;
      endcase
  assign vm_vp_wr_enable[4] = arcsync_vm4_core_wr_enable;
    assign arcsync_vm5_core_exist[0] = map_vm_vproc[5*ARCSYNC_VIRT_PROC + 0][31] & (map_vm_vproc[5*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[5*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0])
          0: arcsync_vm5_core_wr_enable[0] = cl_enable[0] & arcsync_vm5_core_exist[0];
          1: arcsync_vm5_core_wr_enable[0] = cl_enable[1] & arcsync_vm5_core_exist[0];
          2: arcsync_vm5_core_wr_enable[0] = cl_enable[2] & arcsync_vm5_core_exist[0];
        default: arcsync_vm5_core_wr_enable[0] = 1'b0;
      endcase
    assign arcsync_vm5_core_exist[1] = map_vm_vproc[5*ARCSYNC_VIRT_PROC + 1][31] & (map_vm_vproc[5*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[5*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0])
          0: arcsync_vm5_core_wr_enable[1] = cl_enable[0] & arcsync_vm5_core_exist[1];
          1: arcsync_vm5_core_wr_enable[1] = cl_enable[1] & arcsync_vm5_core_exist[1];
          2: arcsync_vm5_core_wr_enable[1] = cl_enable[2] & arcsync_vm5_core_exist[1];
        default: arcsync_vm5_core_wr_enable[1] = 1'b0;
      endcase
    assign arcsync_vm5_core_exist[2] = map_vm_vproc[5*ARCSYNC_VIRT_PROC + 2][31] & (map_vm_vproc[5*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[5*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0])
          0: arcsync_vm5_core_wr_enable[2] = cl_enable[0] & arcsync_vm5_core_exist[2];
          1: arcsync_vm5_core_wr_enable[2] = cl_enable[1] & arcsync_vm5_core_exist[2];
          2: arcsync_vm5_core_wr_enable[2] = cl_enable[2] & arcsync_vm5_core_exist[2];
        default: arcsync_vm5_core_wr_enable[2] = 1'b0;
      endcase
  assign vm_vp_wr_enable[5] = arcsync_vm5_core_wr_enable;
    assign arcsync_vm6_core_exist[0] = map_vm_vproc[6*ARCSYNC_VIRT_PROC + 0][31] & (map_vm_vproc[6*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[6*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0])
          0: arcsync_vm6_core_wr_enable[0] = cl_enable[0] & arcsync_vm6_core_exist[0];
          1: arcsync_vm6_core_wr_enable[0] = cl_enable[1] & arcsync_vm6_core_exist[0];
          2: arcsync_vm6_core_wr_enable[0] = cl_enable[2] & arcsync_vm6_core_exist[0];
        default: arcsync_vm6_core_wr_enable[0] = 1'b0;
      endcase
    assign arcsync_vm6_core_exist[1] = map_vm_vproc[6*ARCSYNC_VIRT_PROC + 1][31] & (map_vm_vproc[6*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[6*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0])
          0: arcsync_vm6_core_wr_enable[1] = cl_enable[0] & arcsync_vm6_core_exist[1];
          1: arcsync_vm6_core_wr_enable[1] = cl_enable[1] & arcsync_vm6_core_exist[1];
          2: arcsync_vm6_core_wr_enable[1] = cl_enable[2] & arcsync_vm6_core_exist[1];
        default: arcsync_vm6_core_wr_enable[1] = 1'b0;
      endcase
    assign arcsync_vm6_core_exist[2] = map_vm_vproc[6*ARCSYNC_VIRT_PROC + 2][31] & (map_vm_vproc[6*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[6*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0])
          0: arcsync_vm6_core_wr_enable[2] = cl_enable[0] & arcsync_vm6_core_exist[2];
          1: arcsync_vm6_core_wr_enable[2] = cl_enable[1] & arcsync_vm6_core_exist[2];
          2: arcsync_vm6_core_wr_enable[2] = cl_enable[2] & arcsync_vm6_core_exist[2];
        default: arcsync_vm6_core_wr_enable[2] = 1'b0;
      endcase
  assign vm_vp_wr_enable[6] = arcsync_vm6_core_wr_enable;
    assign arcsync_vm7_core_exist[0] = map_vm_vproc[7*ARCSYNC_VIRT_PROC + 0][31] & (map_vm_vproc[7*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[7*ARCSYNC_VIRT_PROC + 0][CLUSTER_WIDTH-1:0])
          0: arcsync_vm7_core_wr_enable[0] = cl_enable[0] & arcsync_vm7_core_exist[0];
          1: arcsync_vm7_core_wr_enable[0] = cl_enable[1] & arcsync_vm7_core_exist[0];
          2: arcsync_vm7_core_wr_enable[0] = cl_enable[2] & arcsync_vm7_core_exist[0];
        default: arcsync_vm7_core_wr_enable[0] = 1'b0;
      endcase
    assign arcsync_vm7_core_exist[1] = map_vm_vproc[7*ARCSYNC_VIRT_PROC + 1][31] & (map_vm_vproc[7*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[7*ARCSYNC_VIRT_PROC + 1][CLUSTER_WIDTH-1:0])
          0: arcsync_vm7_core_wr_enable[1] = cl_enable[0] & arcsync_vm7_core_exist[1];
          1: arcsync_vm7_core_wr_enable[1] = cl_enable[1] & arcsync_vm7_core_exist[1];
          2: arcsync_vm7_core_wr_enable[1] = cl_enable[2] & arcsync_vm7_core_exist[1];
        default: arcsync_vm7_core_wr_enable[1] = 1'b0;
      endcase
    assign arcsync_vm7_core_exist[2] = map_vm_vproc[7*ARCSYNC_VIRT_PROC + 2][31] & (map_vm_vproc[7*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0] < ARCSYNC_VIRT_PROC);
    
    always @(*)
      case(map_vm_vproc[7*ARCSYNC_VIRT_PROC + 2][CLUSTER_WIDTH-1:0])
          0: arcsync_vm7_core_wr_enable[2] = cl_enable[0] & arcsync_vm7_core_exist[2];
          1: arcsync_vm7_core_wr_enable[2] = cl_enable[1] & arcsync_vm7_core_exist[2];
          2: arcsync_vm7_core_wr_enable[2] = cl_enable[2] & arcsync_vm7_core_exist[2];
        default: arcsync_vm7_core_wr_enable[2] = 1'b0;
      endcase
  assign vm_vp_wr_enable[7] = arcsync_vm7_core_wr_enable;

    arcsync_ac #( 
                  .ADDR_WIDTH(ARCSYNC_ADDR_WIDTH),
                  .DATA_WIDTH(ARCSYNC_DATA_WIDTH),
                  .AC_NUM(AC_NUM),
                  .AC_WIDTH(AC_WIDTH),
                  .CORE_NUM(CORE_NUM),
                  .VIRT_MACHINES (ARCSYNC_VIRT_MACHINES),
                  .CLUSTER_NUM   (CLUSTER_NUM)
                 )
       u_arcsync_ac (
         .arcsync_core_exist     (arcsync_core_exist),   
         .arcsync_core_wr_enable (arcsync_core_wr_enable),
         .arcsync_vm0_core_exist (arcsync_vm0_core_exist),
         .arcsync_vm0_core_wr_enable (arcsync_vm0_core_wr_enable),
         .arcsync_vm1_core_exist (arcsync_vm1_core_exist),
         .arcsync_vm1_core_wr_enable (arcsync_vm1_core_wr_enable),
         .arcsync_vm2_core_exist (arcsync_vm2_core_exist),
         .arcsync_vm2_core_wr_enable (arcsync_vm2_core_wr_enable),
         .arcsync_vm3_core_exist (arcsync_vm3_core_exist),
         .arcsync_vm3_core_wr_enable (arcsync_vm3_core_wr_enable),
         .arcsync_vm4_core_exist (arcsync_vm4_core_exist),
         .arcsync_vm4_core_wr_enable (arcsync_vm4_core_wr_enable),
         .arcsync_vm5_core_exist (arcsync_vm5_core_exist),
         .arcsync_vm5_core_wr_enable (arcsync_vm5_core_wr_enable),
         .arcsync_vm6_core_exist (arcsync_vm6_core_exist),
         .arcsync_vm6_core_wr_enable (arcsync_vm6_core_wr_enable),
         .arcsync_vm7_core_exist (arcsync_vm7_core_exist),
         .arcsync_vm7_core_wr_enable (arcsync_vm7_core_wr_enable),
         .mmio_sel               (mmio_sel_ac),
         .mmio_addr              (mmio_addr),
         .mmio_wen               (mmio_wen),
         .mmio_ren               (mmio_ren),
         .mmio_rdata             (mmio_rdata_ac),
         .mmio_wdata             (mmio_wdata),
         .mmio_resp              (mmio_resp_ac),

         ///////////////// Non-VM mode IRQ/Event /////////////////
         .arcsync_core_irq  (arcsync_core_ac_irq  ),
         .arcsync_core_event(arcsync_core_ac_event),

         /////////////////  VM mode IRQ/Event /////////////////
         .vm0_arcsync_core_irq  (vm0_arcsync_core_ac_irq  ),
         .vm0_arcsync_core_event(vm0_arcsync_core_ac_event),

         .vm1_arcsync_core_irq  (vm1_arcsync_core_ac_irq  ),
         .vm1_arcsync_core_event(vm1_arcsync_core_ac_event),

         .vm2_arcsync_core_irq  (vm2_arcsync_core_ac_irq  ),
         .vm2_arcsync_core_event(vm2_arcsync_core_ac_event),

         .vm3_arcsync_core_irq  (vm3_arcsync_core_ac_irq  ),
         .vm3_arcsync_core_event(vm3_arcsync_core_ac_event),

         .vm4_arcsync_core_irq  (vm4_arcsync_core_ac_irq  ),
         .vm4_arcsync_core_event(vm4_arcsync_core_ac_event),

         .vm5_arcsync_core_irq  (vm5_arcsync_core_ac_irq  ),
         .vm5_arcsync_core_event(vm5_arcsync_core_ac_event),

         .vm6_arcsync_core_irq  (vm6_arcsync_core_ac_irq  ),
         .vm6_arcsync_core_event(vm6_arcsync_core_ac_event),

         .vm7_arcsync_core_irq  (vm7_arcsync_core_ac_irq  ),
         .vm7_arcsync_core_event(vm7_arcsync_core_ac_event),


         .rst_a                  (rst_a),
         .clk                    (clk)
    );

always_comb
begin: cluster_vm_ac_evt_irq_route
  for (int unsigned cl=0; cl<(CLUSTER_NUM); cl++) // { 
  begin: gen_cluster_vm_ac_evt_irq_loop
    // cluster_vm_ac_evt/irq[cluster][vm]
    // vm<i>_arcsync_core_ac_evt/irq[VIRT_PROC-1:0]
    cluster_vm_ac_evt[cl]={(ARCSYNC_VIRT_MACHINES){1'b0}};
    cluster_vm_ac_irq[cl]={(ARCSYNC_VIRT_MACHINES){1'b0}};
 
      for (int unsigned vp=0; vp<(ARCSYNC_VIRT_PROC); vp++) // { for vp
      begin
        logic [31:0] vp_idx;
        vp_idx = 0*ARCSYNC_VIRT_PROC+vp;
        cluster_vm_ac_evt[cl][0] = cluster_vm_ac_evt[cl][0] | 
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm0_arcsync_core_ac_event[vp];

        cluster_vm_ac_irq[cl][0] = cluster_vm_ac_irq[cl][0] |
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm0_arcsync_core_ac_irq[vp];
        
      end // for vp }
      for (int unsigned vp=0; vp<(ARCSYNC_VIRT_PROC); vp++) // { for vp
      begin
        logic [31:0] vp_idx;
        vp_idx = 1*ARCSYNC_VIRT_PROC+vp;
        cluster_vm_ac_evt[cl][1] = cluster_vm_ac_evt[cl][1] | 
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm1_arcsync_core_ac_event[vp];

        cluster_vm_ac_irq[cl][1] = cluster_vm_ac_irq[cl][1] |
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm1_arcsync_core_ac_irq[vp];
        
      end // for vp }
      for (int unsigned vp=0; vp<(ARCSYNC_VIRT_PROC); vp++) // { for vp
      begin
        logic [31:0] vp_idx;
        vp_idx = 2*ARCSYNC_VIRT_PROC+vp;
        cluster_vm_ac_evt[cl][2] = cluster_vm_ac_evt[cl][2] | 
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm2_arcsync_core_ac_event[vp];

        cluster_vm_ac_irq[cl][2] = cluster_vm_ac_irq[cl][2] |
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm2_arcsync_core_ac_irq[vp];
        
      end // for vp }
      for (int unsigned vp=0; vp<(ARCSYNC_VIRT_PROC); vp++) // { for vp
      begin
        logic [31:0] vp_idx;
        vp_idx = 3*ARCSYNC_VIRT_PROC+vp;
        cluster_vm_ac_evt[cl][3] = cluster_vm_ac_evt[cl][3] | 
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm3_arcsync_core_ac_event[vp];

        cluster_vm_ac_irq[cl][3] = cluster_vm_ac_irq[cl][3] |
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm3_arcsync_core_ac_irq[vp];
        
      end // for vp }
      for (int unsigned vp=0; vp<(ARCSYNC_VIRT_PROC); vp++) // { for vp
      begin
        logic [31:0] vp_idx;
        vp_idx = 4*ARCSYNC_VIRT_PROC+vp;
        cluster_vm_ac_evt[cl][4] = cluster_vm_ac_evt[cl][4] | 
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm4_arcsync_core_ac_event[vp];

        cluster_vm_ac_irq[cl][4] = cluster_vm_ac_irq[cl][4] |
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm4_arcsync_core_ac_irq[vp];
        
      end // for vp }
      for (int unsigned vp=0; vp<(ARCSYNC_VIRT_PROC); vp++) // { for vp
      begin
        logic [31:0] vp_idx;
        vp_idx = 5*ARCSYNC_VIRT_PROC+vp;
        cluster_vm_ac_evt[cl][5] = cluster_vm_ac_evt[cl][5] | 
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm5_arcsync_core_ac_event[vp];

        cluster_vm_ac_irq[cl][5] = cluster_vm_ac_irq[cl][5] |
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm5_arcsync_core_ac_irq[vp];
        
      end // for vp }
      for (int unsigned vp=0; vp<(ARCSYNC_VIRT_PROC); vp++) // { for vp
      begin
        logic [31:0] vp_idx;
        vp_idx = 6*ARCSYNC_VIRT_PROC+vp;
        cluster_vm_ac_evt[cl][6] = cluster_vm_ac_evt[cl][6] | 
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm6_arcsync_core_ac_event[vp];

        cluster_vm_ac_irq[cl][6] = cluster_vm_ac_irq[cl][6] |
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm6_arcsync_core_ac_irq[vp];
        
      end // for vp }
      for (int unsigned vp=0; vp<(ARCSYNC_VIRT_PROC); vp++) // { for vp
      begin
        logic [31:0] vp_idx;
        vp_idx = 7*ARCSYNC_VIRT_PROC+vp;
        cluster_vm_ac_evt[cl][7] = cluster_vm_ac_evt[cl][7] | 
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm7_arcsync_core_ac_event[vp];

        cluster_vm_ac_irq[cl][7] = cluster_vm_ac_irq[cl][7] |
                                         {((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))} & vm7_arcsync_core_ac_irq[vp];
        
      end // for vp }
    
  end // }
end: cluster_vm_ac_evt_irq_route

//-------------------------------------------------------------------------------------------------------
// ARCSync Control and Status 
//-------------------------------------------------------------------------------------------------------
    arcsync_acs #( 
                  .ADDR_WIDTH(ARCSYNC_ADDR_WIDTH),
                  .DATA_WIDTH(ARCSYNC_DATA_WIDTH),
                  .CORE_NUM(CORE_NUM),
                  .CORE_CLK_ENA_RST(CORE_CLK_ENA_RST)
                 )
       u_arcsync_acs (
      .arcsync_core_exist                  (arcsync_core_exist),   
      .arcsync_core_wr_enable              (arcsync_core_wr_enable),
      .mmio_sel                            (mmio_sel_acs),
      .mmio_addr                           (mmio_addr),
      .mmio_wen                            (mmio_wen),
      .mmio_ren                            (mmio_ren),
      .mmio_rdata                          (mmio_rdata_acs),
      .mmio_wdata                          (mmio_wdata),
      .mmio_resp                           (mmio_resp_acs),
      .core_arcsync_arc64                  (core_arcsync_arc64),
      .arcsync_core_intvbase               (arcsync_core_intvbase),
      .arcsync_core_halt_req               (arcsync_core_halt_req),
      .core_arcsync_halt_ack               (core_arcsync_halt_ack),
      .arcsync_core_run_req                (arcsync_core_run_req),
      .core_arcsync_run_ack                (core_arcsync_run_ack),
      .core_arcsync_sys_sleep              (core_arcsync_sys_sleep),
      .core_arcsync_sys_sleep_mode         (core_arcsync_sys_sleep_mode),
      .core_arcsync_sys_halt               (core_arcsync_sys_halt),
      .core_arcsync_sys_tf_halt            (core_arcsync_sys_tf_halt),
      .arcsync_core_rst_req                (arcsync_core_rst_req),
      .arcsync_core_clk_en                 (arcsync_core_clk_en),
      .core_arcsync_pmode                  (core_arcsync_pmode),
      .rst_a                               (rst_a),
      .clk                                 (clk)
    );

//-------------------------------------------------------------------------------------------------------
// Power Management Unit 
//-------------------------------------------------------------------------------------------------------
    arcsync_pmu #( 
                  .ADDR_WIDTH(ARCSYNC_ADDR_WIDTH),
                  .DATA_WIDTH(ARCSYNC_DATA_WIDTH),
                  .MAX_CORE_NUM(MAX_CORE_NUM),
                  .CLUSTER_NUM(CLUSTER_NUM),
                  .CORE_NUM(CORE_NUM)
                 )
       u_arcsync_pmu (
         .cl_enable                        (cl_enable),
         .arcsync_core_wr_enable           (arcsync_core_wr_enable),
         .arcsync_core_pwr_down            (arcsync_core_pwr_down),
         .arcsync_core_isolate_n           (arcsync_core_isolate_n),
         .arcsync_core_isolate             (arcsync_core_isolate),
         .arcsync_core_pd_mem              (arcsync_core_pd_mem),
         .arcsync_core_pd_logic            (arcsync_core_pd_logic),
         .arcsync_core_pd_logic1           (arcsync_core_pd_logic1),
         .arcsync_core_pd_logic2           (arcsync_core_pd_logic2),
         .arcsync_core_pu_rst              (arcsync_core_pu_rst),
         .arcsync_core_exist               (arcsync_core_exist),
         .arcsync_grp_pwr_down             (arcsync_grp_pwr_down),
         .arcsync_grp_isolate_n            (arcsync_grp_isolate_n),
         .arcsync_grp_isolate              (arcsync_grp_isolate),
         .arcsync_grp_pd_mem               (arcsync_grp_pd_mem),
         .arcsync_grp_pd_logic             (arcsync_grp_pd_logic),
         .arcsync_grp_pd_logic1            (arcsync_grp_pd_logic1),
         .arcsync_grp_pd_logic2            (arcsync_grp_pd_logic2),
         .arcsync_grp_pu_rst               (arcsync_grp_pu_rst),
         .core_arcsync_pmode               (core_arcsync_pmode),

         .mmio_sel                         (mmio_sel_pmu),
         .mmio_addr                        (mmio_addr),
         .mmio_wen                         (mmio_wen),
         .mmio_ren                         (mmio_ren),
         .mmio_wdata                       (mmio_wdata),
         .mmio_rdata                       (mmio_rdata_pmu),
         .mmio_resp                        (mmio_resp_pmu),
         .iso_override                     (iso_override),
         .test_mode                        (test_mode),
         .rst_a                            (rst_a),
         .clk                              (clk)
    );


  // No Safety
  assign mmio_rdata_sfty = 'b0;
  assign mmio_resp_sfty = {2{mmio_sel_sfty}};  

`ifdef FORMAL_ASSERT_ON
  `include "prop_arcsync_core.sv"
`endif
endmodule
