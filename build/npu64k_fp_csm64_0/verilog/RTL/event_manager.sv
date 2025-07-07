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

module event_manager #(
 parameter CNT_NUM=8,
 parameter CNT_WIDTH=8,
 parameter EVT_SEND_NUM=17,
 parameter EVT_DURATION=5
) (
// Event interface
  input  logic [CNT_NUM-1:0] events_in,
  output logic        [31:0] event_send,

// ARC interface
  input  logic               sys_sleep_r, 
// spyglass disable_block W240
//SMD:Input not read
//SJ :Ignore
  input  logic         [2:0] sys_sleep_mode_r,
// spyglass enable_block W240
  output logic               arc_event,          
  input logic         [27:0] arcsync_sys_base,

// APEX interface
  output logic        [27:0] evm_apex_arcsync_sys_base,
  output logic        [31:0] evm_apex_evt_send_exist, 
  output logic        [31:0] evm_apex_cnt_exist, 
  input  logic               apex_evm_cnt_wr,    
  input  logic         [4:0] apex_evm_cnt_sel,   
  input  logic        [31:0] apex_evm_cnt_val,  
  output logic        [31:0] evm_apex_cnt_val,  
  input  logic        [31:0] apex_evm_evt_send,  
  output logic               evm_apex_evt_sent,  

  input  logic               apex_evm_mode,      
  input  logic        [31:0] apex_evm_incr,      
  input  logic        [31:0] apex_evm_decr,      
  input  logic        [31:0] apex_evm_filter,    
  output logic        [31:0] evm_apex_nz,        

// Clock and Reset
  input  logic               clk,                // always on clock in
  input  logic               rst_a               //

);

localparam EVT_DUR_WIDTH=$clog2(EVT_DURATION);
localparam CNT_MSB=CNT_WIDTH-1;

logic [CNT_NUM-1:0] sync_events, events_r, events_occur; 
logic [CNT_NUM-1:0][CNT_MSB:0]   event_counters_r, event_counters_nxt;
logic [CNT_NUM-1:0][CNT_WIDTH:0] event_counters_res;
logic [CNT_NUM-1:0] evt_nz_all;        
logic               evt_cnt_reg_en; 
logic               arc_evt_nxt, arc_evt_r;
logic         [5:0] evt_cnt_num;
assign evt_cnt_num = CNT_NUM;

assign evm_apex_cnt_exist       = {{32-CNT_NUM{1'b0}}, {CNT_NUM{1'b1}}};
assign evm_apex_evt_send_exist  = {{32-EVT_SEND_NUM{1'b0}}, {EVT_SEND_NUM{1'b1}}};
assign evm_apex_arcsync_sys_base= arcsync_sys_base;
// Only send event when the core is sleeping
assign arc_event                = arc_evt_r && sys_sleep_r; 
// Track the posedge of events_in
assign events_occur  = ~events_r & events_in;
assign  evt_cnt_reg_en =  (|events_in) || (|events_r) || (|apex_evm_decr) || (|apex_evm_incr) || apex_evm_cnt_wr;
always_ff @(posedge clk or posedge rst_a) 
begin: evt_reg_PROC
  if (rst_a) 
  begin
    events_r  <= {CNT_NUM{1'b0}};
    arc_evt_r <= 1'b0;
    for (int i=0; i<CNT_NUM; i=i+1)
      event_counters_r[i] <= {CNT_WIDTH{1'b0}};
  end
  else 
  begin
    arc_evt_r <= arc_evt_nxt;
    if (evt_cnt_reg_en)
    begin
      events_r  <= events_in;
      for (int i=0; i<CNT_NUM; i=i+1)
        event_counters_r[i] <= event_counters_nxt[i];
    end  
  end
end: evt_reg_PROC

// The counter increments with incremental requests and decrements with decremental requests 
// If the counter reaches the maximum value, it's saturated if there are any decremental requests come
// If the counter is zero, it stays zero if there are any decremental requests come
// The counter is written with specific value if it's selected
always_comb 
begin: cnt_value_PROC
  for (int i=0; i<CNT_NUM; i=i+1) begin
    sync_events[i] = ((&event_counters_r[i][CNT_MSB:1]) && events_occur[i])? 
                              (!apex_evm_incr[i] && !event_counters_r[i][0]) : (events_occur[i]);
    event_counters_res[i] =  event_counters_r[i] + {{CNT_MSB{1'b0}},sync_events[i]}
                                              + {{CNT_MSB{apex_evm_decr[i]}},(apex_evm_decr[i]|apex_evm_incr[i])};
    event_counters_nxt[i] = (apex_evm_cnt_wr && apex_evm_cnt_sel==i) ? apex_evm_cnt_val[CNT_MSB:0]
                          : (~|event_counters_r[i] && apex_evm_decr[i])? {CNT_WIDTH{1'b0}}
                          : (&event_counters_r[i]  && apex_evm_incr[i])? {CNT_WIDTH{1'b1}}
                          : event_counters_res[i][CNT_MSB:0]; 
  end
end: cnt_value_PROC

// If the counter_n is non-zero, the bit_n is set
always_comb
begin: cnt_nz_PROC 
  evm_apex_nz = 32'h0;
  for (int i=0; i<CNT_NUM; i=i+1)
    evm_apex_nz[i] = (event_counters_r[i]!=0);
end: cnt_nz_PROC

// Check the nz counter for ALL mode
always_comb 
begin: evt_nz_PROC
  evt_nz_all = 'b0;
  if (|apex_evm_filter[CNT_NUM-1:0]) 
  begin
    for (int i=0; i<CNT_NUM; i=i+1) begin
      evt_nz_all[i] = apex_evm_filter[i]? evm_apex_nz[i] : 1'b1;
    end
  end 
end: evt_nz_PROC

// If the selected counter is read, the selected counter value is returned
// spyglass disable_block ImproperRangeIndex-ML
always_comb
begin: cnt_val_PROC
  evm_apex_cnt_val = ({1'b0,apex_evm_cnt_sel} < evt_cnt_num)? event_counters_r[apex_evm_cnt_sel] : 'b0;
end: cnt_val_PROC
// spyglass enable_block ImproperRangeIndex-ML

// apex_evm_mode==1: ANY mode. The asynchrouns event is sent if one or more of the event counters in the filter are already non-zero. 
// apex_evm_mode==0: ALL mode. The asynchrouns event is sent if all of the event counters in the filter are already non-zero.
// No event is sent if the core is not sleeping  
always_comb
begin: arc_evt_PROC
  arc_evt_nxt = (apex_evm_mode ? |(evm_apex_nz[CNT_NUM-1:0] & apex_evm_filter[CNT_NUM-1:0]) 
                               : (&evt_nz_all))
                && sys_sleep_r;
end: arc_evt_PROC

// The access to EVT_SEND triggers a direct event without passing ARCSync
// The duration is configurable 
logic [EVT_DUR_WIDTH:0] dir_evt_duration_r, dir_evt_duration_nxt;
logic [31:0]            evt_sending_r, evt_sending_nxt;
logic                   evt_reg_en; 

assign event_send = evt_sending_r;
assign evm_apex_evt_sent = (dir_evt_duration_r == EVT_DURATION);
assign evt_reg_en = (|apex_evm_evt_send) || (dir_evt_duration_r != 'b0);

always_ff @(posedge clk or posedge rst_a) 
begin: dir_evt_reg_PROC
  if (rst_a) begin
    dir_evt_duration_r <= 'b0;
    evt_sending_r      <= 'b0;
  end
  else begin
    if (evt_reg_en) 
    begin  
      dir_evt_duration_r <= dir_evt_duration_nxt;
      evt_sending_r      <= evt_sending_nxt;
    end  
  end
end: dir_evt_reg_PROC

always_comb 
begin: evt_send_PROC
  dir_evt_duration_nxt = dir_evt_duration_r;
  evt_sending_nxt      = evt_sending_r;
  // When event manager notice any bits in EVT_SEND is written, the event is sent
  if (|apex_evm_evt_send) 
  begin
    dir_evt_duration_nxt = dir_evt_duration_r + 1;
    evt_sending_nxt      = apex_evm_evt_send;
  end  
  // When the event pulse is sent with the defined duration, the events are de-asserted
  else if (dir_evt_duration_r == EVT_DURATION)
  begin
    dir_evt_duration_nxt = 'b0;
    evt_sending_nxt      = 'b0;
  end  
  // Keep sending the event to the defined duration
  else if (dir_evt_duration_r != 'b0)
    dir_evt_duration_nxt = dir_evt_duration_r + 1;
end: evt_send_PROC  


`ifdef FORMAL_ASSERT_ON
   `include "prop_evm.sv"
`endif  
endmodule
