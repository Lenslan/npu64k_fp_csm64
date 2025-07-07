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

module arcsync_vm_eid
#(
  parameter ADDR_WIDTH = 32,
  parameter DATA_WIDTH = 32,
  parameter logic [3:0] EVENT_PULSE_HIGH = 4'd5,
  parameter logic [3:0] EVENT_PULSE_LOW  = 4'd5,
  parameter CLUSTER_NUM = 4,
  parameter VIRT_MACHINES = 8,
  parameter VIRT_PROC = 4,
  parameter NUM_IRQ_PER_VPROC = 1,
  parameter NUM_EVT_PER_VPROC = 1,
  parameter ADDR_VM0_EID_SEND_EVENT_0 = 32'h14000,
  parameter ADDR_VM0_EID_RAISE_IRQ_0  = 32'h14050,
  parameter ADDR_VM0_EID_ACK_IRQ_0    = 32'h14064
)
(
  input     logic                           mmio_sel_map_vm_vproc,
  input     logic                           mmio_sel_vm_eid,       // select target register group, valid at the cycle when *en is high
  input     logic       [ADDR_WIDTH-1:0]    mmio_addr,  // register address, valid at the cycle when *en is high
  input     logic                           mmio_wen,   // write enable for register
  input     logic                           mmio_ren,   // read enable for register
  output    logic       [DATA_WIDTH-1:0]    mmio_rdata_map_vm_vproc,  // read data, valid at the cycle when ren is high
  output    logic       [DATA_WIDTH-1:0]    mmio_rdata_vm_eid,        // read data, valid at the cycle when ren is high
  input     logic       [DATA_WIDTH-1:0]    mmio_wdata, // write data, valid at the cycle when wen is high
  output    logic       [1:0]               mmio_resp_map_vm_vproc,  // {err, ack} the response is received at the cycle when *en is high
  output    logic       [1:0]               mmio_resp_vm_eid,        // {err, ack} the response is received at the cycle when *en is high
  input     logic       [CLUSTER_NUM-1:0]   core0_sys_sleep, // core0's sys_sleep of each cluster

  // IRQ and Event
  output    logic       [CLUSTER_NUM-1:0][(VIRT_MACHINES*NUM_EVT_PER_VPROC)-1:0] cluster_vm_evt,  // VM interrupt outputs for each cluster
  output    logic       [CLUSTER_NUM-1:0][(VIRT_MACHINES*NUM_IRQ_PER_VPROC)-1:0] cluster_vm_irq,  // VM event output for each cluster

  // vm map table
  output logic [VIRT_MACHINES*VIRT_PROC-1:0][DATA_WIDTH-1:0] map_vm_vproc,

  // vm_vp_wr_enable
  input logic [VIRT_MACHINES-1:0][CLUSTER_NUM-1:0] vm_vp_wr_enable,

  // Clock, reset and configuration
  input     logic                 rst_a,      // Asynchronous reset, active high
  input     logic                 clk         // Clock
);

localparam  CLUSTER_NUM_S = signed'(CLUSTER_NUM); //note:signed version for genvar type checking
localparam  VIRT_MACHINES_S = signed'(VIRT_MACHINES); //note:signed version for genvar type checking
localparam  VIRT_PROC_S = signed'(VIRT_PROC); //note:signed version for genvar type checking
localparam  CLUSTER_WIDTH = ($clog2(CLUSTER_NUM)==0) ? 1 : $clog2(CLUSTER_NUM);
localparam  VIRT_MACHINES_WIDTH = $clog2(VIRT_MACHINES);
localparam  TOTAL_VP_WIDTH = ($clog2(VIRT_MACHINES*VIRT_PROC)==0) ? 1 : $clog2(VIRT_MACHINES*VIRT_PROC);

logic [VIRT_MACHINES*VIRT_PROC-1:0] map_vm_vproc_ren;
logic [VIRT_MACHINES*VIRT_PROC-1:0] map_vm_vproc_wen;
logic [VIRT_MACHINES-1:0][VIRT_PROC-1:0] vm_vproc_enable;

logic [VIRT_MACHINES-1:0][(VIRT_PROC*NUM_EVT_PER_VPROC)-1:0] vm_evt;
logic [VIRT_MACHINES-1:0][(VIRT_PROC*NUM_IRQ_PER_VPROC)-1:0] vm_irq;

//logic [VIRT_MACHINES*VIRT_PROC-1:0][DATA_WIDTH-1:0] MAP_VM_VPROC_RDATA;
logic [VIRT_PROC-1:0][DATA_WIDTH-1:0] MAP_VM_VPROC_RDATA[VIRT_MACHINES-1:0];

///////////////////////////////////////////////////////////////////////////////
//                           Access MMIO of map_vm_vproc                     //
///////////////////////////////////////////////////////////////////////////////
for (genvar i=0; i<(VIRT_MACHINES_S*VIRT_PROC_S); i++) // { 
begin
  assign map_vm_vproc_ren[i] =  mmio_sel_map_vm_vproc && mmio_ren && (mmio_addr == (`ARCSYNC_ADDR_VM_CONFIG + 4*unsigned'(i)) )  ;
  assign map_vm_vproc_wen[i] =  mmio_sel_map_vm_vproc && mmio_wen && (mmio_addr == (`ARCSYNC_ADDR_VM_CONFIG + 4*unsigned'(i)) )  ;
  
  always @(posedge clk or posedge rst_a)
  begin: map_vm_vproc_PROC
    if (rst_a) 
      map_vm_vproc[i] <= 32'h0;
    else if (map_vm_vproc_wen[i])
      map_vm_vproc[i] <= {mmio_wdata[31], {(32-1-CLUSTER_WIDTH){1'b0}}, mmio_wdata[CLUSTER_WIDTH-1:0]};
  end: map_vm_vproc_PROC

end // }


for (genvar i=0; i<(VIRT_MACHINES_S); i++) // { 
begin
  for (genvar j=0; j<(VIRT_PROC_S); j++) // {  
  begin
    assign MAP_VM_VPROC_RDATA[i][j] = map_vm_vproc[i*VIRT_PROC_S+j];
  end // }
end // }

always_comb  
begin: mmio_rdata_map_vm_vproc_PROC
  mmio_rdata_map_vm_vproc  = {DATA_WIDTH{1'b0}};
  for (int i=0; i<(VIRT_MACHINES_S); i++) // { 
  begin
    for (int j=0; j<(VIRT_PROC_S); j++) // {
    begin // {
      logic [31:0] vp_idx;
      vp_idx = i*VIRT_PROC_S + j;
      if (map_vm_vproc_ren[vp_idx[TOTAL_VP_WIDTH-1:0]])
      begin
        mmio_rdata_map_vm_vproc = mmio_rdata_map_vm_vproc | MAP_VM_VPROC_RDATA[i][j];
      end
    end // }
  end // }
end: mmio_rdata_map_vm_vproc_PROC

///////////////////////////////////////////////////////////////////////////////
//                             VM_EID instantiate                            //
/////////////////////////////////////////////////////////////////////////////// 
logic [VIRT_MACHINES-1:0] mmio_sel_vm_eid_locl;
logic [VIRT_MACHINES-1:0][DATA_WIDTH-1:0] mmio_rdata_vm_eid_locl;
logic [VIRT_MACHINES-1:0][1:0] mmio_resp_vm_eid_locl;
logic [VIRT_MACHINES-1:0] mmio_resp_vm_eid_locl_err_bit;
logic [VIRT_MACHINES-1:0] mmio_resp_vm_eid_locl_ack_bit;
logic [VIRT_MACHINES-1:0][VIRT_PROC-1:0] vproc_sys_sleep;

always_comb
begin: vproc_sys_sleep_PROC
  for (int unsigned i=0; i<VIRT_MACHINES; i++)  // { for virt_machine
  begin: vproc_sys_sleep_PROC_i
    for (int unsigned j=0; j<VIRT_PROC; j++)  // { for virt_proc
    begin: vproc_sys_sleep_PROC_j
      logic [31:0] vp_idx;
      vp_idx = i*VIRT_PROC + j;
      if (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0] < VIRT_PROC)
        vproc_sys_sleep[i][j] = map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31] & core0_sys_sleep[map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]] & vm_vp_wr_enable[i][j];
      else
        vproc_sys_sleep[i][j] = 1'b0;

    end: vproc_sys_sleep_PROC_j // for virt_proc }
  end: vproc_sys_sleep_PROC_i // for virt_machine }
end: vproc_sys_sleep_PROC

for (genvar i=0; i<(VIRT_MACHINES_S); i++) // { 
begin: gen_vm_eid_inst

    assign mmio_sel_vm_eid_locl[i] = mmio_sel_vm_eid && (mmio_addr[ADDR_WIDTH-1:12] == ((`ARCSYNC_ADDR_VM0_EID + 13'h1000*unsigned'(i))>>12));
    assign mmio_resp_vm_eid_locl_err_bit[i] = mmio_resp_vm_eid_locl[i][1];
    assign mmio_resp_vm_eid_locl_ack_bit[i] = mmio_resp_vm_eid_locl[i][0];

  for (genvar j=0; j<VIRT_PROC; j++) // {
  begin: vm_vproc_en_map_PROC
    assign vm_vproc_enable[i][j] = map_vm_vproc[i*VIRT_PROC+j][31];
  end: vm_vproc_en_map_PROC // }

    arcsync_eid #( 
                  .ADDR_WIDTH(ADDR_WIDTH),
                  .DATA_WIDTH(DATA_WIDTH),
                  .CORE_NUM(VIRT_PROC),
                  .NUM_IRQ_PER_CORE(NUM_IRQ_PER_VPROC),
                  .NUM_EVT_PER_CORE(NUM_EVT_PER_VPROC),
                  .ADDR_EID_SEND_EVENT_0(ADDR_VM0_EID_SEND_EVENT_0 + i*4096),
                  .ADDR_EID_RAISE_IRQ_0 (ADDR_VM0_EID_RAISE_IRQ_0  + i*4096), 
                  .ADDR_EID_ACK_IRQ_0   (ADDR_VM0_EID_ACK_IRQ_0    + i*4096)
                 )
       u_arcsync_vm_eid (
         .arcsync_core_exist     (vm_vproc_enable[i]),
         .arcsync_core_wr_enable (vm_vp_wr_enable[i]),
         .mmio_sel               (mmio_sel_vm_eid_locl[i]),
         .mmio_addr              (mmio_addr),
         .mmio_wen               (mmio_wen),
         .mmio_ren               (mmio_ren),
         .mmio_rdata             (mmio_rdata_vm_eid_locl[i]),
         .mmio_wdata             (mmio_wdata),
         .mmio_resp              (mmio_resp_vm_eid_locl[i]),
         .sys_sleep              (vproc_sys_sleep[i]), // VIRT_PROC should equal to CLUSTER_NUM, VPROC order sys_sleep
         .arcsync_core_irq       (vm_irq[i]),
         .arcsync_core_event     (vm_evt[i]),
         .rst_a                  (rst_a),
         .clk                    (clk)
    );

end // }

always_comb  
begin: mmio_rdata_vm_eid_PROC
  mmio_rdata_vm_eid  = {DATA_WIDTH{1'b0}};
  for (int i=0; i<(VIRT_MACHINES_S); i++) // {
  begin
    if (mmio_sel_vm_eid_locl[i] & mmio_ren)
    begin
      mmio_rdata_vm_eid = mmio_rdata_vm_eid | mmio_rdata_vm_eid_locl[i];
    end
  end // }
end: mmio_rdata_vm_eid_PROC

always_comb
begin: cluster_vm_evt_irq_route
  for (int unsigned cl=0; cl<(CLUSTER_NUM_S); cl++) // { 
  begin: gen_cluster_vm_evt_loop_cluster
    
    cluster_vm_evt[cl]={(VIRT_MACHINES*NUM_EVT_PER_VPROC){1'b0}};
    cluster_vm_irq[cl]={(VIRT_MACHINES*NUM_IRQ_PER_VPROC){1'b0}};
 
    for (int unsigned vm=0; vm<(VIRT_MACHINES); vm++) // {
    begin
      for (int unsigned vp=0; vp<(VIRT_PROC); vp++) // {
      begin
        logic [31:0] vp_idx;
        vp_idx = vm*VIRT_PROC+vp;
        cluster_vm_evt[cl][vm*NUM_EVT_PER_VPROC+:NUM_EVT_PER_VPROC] = cluster_vm_evt[cl][vm*NUM_EVT_PER_VPROC+:NUM_EVT_PER_VPROC] |
                                                                      {NUM_EVT_PER_VPROC{((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))}} & vm_evt[vm][vp*NUM_EVT_PER_VPROC+:NUM_EVT_PER_VPROC];

        cluster_vm_irq[cl][vm*NUM_IRQ_PER_VPROC+:NUM_IRQ_PER_VPROC] = cluster_vm_irq[cl][vm*NUM_IRQ_PER_VPROC+:NUM_IRQ_PER_VPROC] |
                                                                      {NUM_IRQ_PER_VPROC{((map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][31]==1'b1) && (map_vm_vproc[vp_idx[TOTAL_VP_WIDTH-1:0]][CLUSTER_WIDTH-1:0]==cl))}} & vm_irq[vm][vp*NUM_IRQ_PER_VPROC+:NUM_IRQ_PER_VPROC];
        
      end // }
    end // }
    
  end // }
end: cluster_vm_evt_irq_route

assign mmio_resp_map_vm_vproc = {1'b0, mmio_sel_map_vm_vproc};
assign mmio_resp_vm_eid = {|mmio_resp_vm_eid_locl_err_bit, |mmio_resp_vm_eid_locl_ack_bit};


endmodule
