// Library ARC_Trace-3.0.999999999



// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   producer_if_filters
//
// ===========================================================================
//
// Description:
//  producer interface and filter module to filter the producer data as it
//  programmed in the debugger
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_rtt_rst.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"




module npuarc_small_producer_if_filters #(parameter PTCM_WDT_PP = 120, parameter PC_PP = 31,
                                       parameter RTT_ADDR_PP = 32, parameter DUAL_ISSUE_PP = 0, parameter RTT_NUM_FILTERS_PP=4,
                                       parameter FILTER_BITLEN_PP = 4)
( rtt_clk,
  rst_a, // reset
  rtt_pr_sel,// producer select data
  pr0_src_en,
  pr0_rtt_inst_commit,
  pr0_pc,
  pr0_rtt_cond_valid,
  pr0_rtt_cond_pass,
  pr0_rtt_branch,
  pr0_rtt_branch_indir,
  pr0_rtt_branch_taddr,
  pr0_rtt_exception,
  pr0_rtt_exception_rtn,
  pr0_rtt_interrupt,
  pr0_rtt_zd_loop,
  pr0_rtt_dslot,
  pr0_process_id,
  pr0_pid_wr_en,
//`if ((0 || 0) && (`RTT_USE_EV==1)) // {
  rtt_vdsp_data,     // VDSP sw trigger data
  rtt_vdsp_val,      // VDSP sw trigger valid this cycle
  pr0_filter_type,
// leda NTL_CON13C off
  pr0_addr_filter0_start,
  pr0_addr_filter0_stop,
  pr0_addr_filter1_start,
  pr0_addr_filter1_stop,
  pr0_addr_filter2_start,
  pr0_addr_filter2_stop,
  pr0_addr_filter3_start,
  pr0_addr_filter3_stop,
// leda NTL_CON13C on
  pr0_trigger_reg,
  pr0_wp_enable,
  pr0_wp_status,
  pr0_filter_pc,
  pr0_inst_commit ,
  pr0_filter_cond_valid,
  pr0_filter_cond_pass,
  pr0_filter_branch_indir ,
  pr0_filter_branch_taddr ,
  pr0_filter_exception,
  pr0_filter_exception_rtn,
  pr0_filter_interrupt,
  pr0_filter_zd_loop,
  pr0_filter_branch,
  pr0_filter_rtt_dslot,
  pr0_otm_process_id,
  pr0_otm_ptd_wr_en,
//`if ((0 || 0) && (`RTT_USE_EV==1)) // {
  pr0_rtt_vdsp_data,     // VDSP sw trigger data
  pr0_rtt_vdsp_val,      // VDSP sw trigger valid this cycle
  cti_rtt_filters,
  cti_trace_start,
  cti_trace_stop,
  cti_ctrl_en,
  cti_trace_en_dslot,
  pr0_filter_under_run, // filter run state
  pr0_watchpoint_val
);

  input                          rtt_clk; //RTT clock
  input                          rst_a;//Active Low Reset
  input                             rtt_pr_sel; // rtt producer select data from control register
  input  [2-2:0]          pr0_src_en;         //producer 0 source select
  input  [PC_PP-1:0]               pr0_pc;            //Producer pc
  input                          pr0_rtt_inst_commit; //Indicates an instruction has committed
  input                          pr0_rtt_cond_valid;
  input                          pr0_rtt_cond_pass;
  input                          pr0_rtt_branch;
  input                          pr0_rtt_branch_indir;
  input  [PC_PP-1:0]               pr0_rtt_branch_taddr;
  input                          pr0_rtt_exception;
  input                          pr0_rtt_exception_rtn;
  input                          pr0_rtt_interrupt;
  input                          pr0_rtt_zd_loop;
  input                          pr0_rtt_dslot;
  input  [7:0]                   pr0_process_id;
  input                          pr0_pid_wr_en ;
//`if ((0 || 0) && (`RTT_USE_EV==1)) // {
  input  [`npuarc_VDSP_AUX_DATA-1:0]    rtt_vdsp_data;     // VDSP sw trigger data
  input                          rtt_vdsp_val;      // VDSP sw trigger valid this cycle
  input  [24-1:0]        pr0_filter_type;
// leda NTL_CON13C off
  input  [RTT_ADDR_PP-1:0]         pr0_addr_filter0_start; //Filter 0 start addres
  input  [RTT_ADDR_PP-1:0]         pr0_addr_filter0_stop;  //Filter 0 stop addres
  input  [RTT_ADDR_PP-1:0]         pr0_addr_filter1_start; //Filter 1 start addres
  input  [RTT_ADDR_PP-1:0]         pr0_addr_filter1_stop;  //Filter 1 stop addres
  input  [RTT_ADDR_PP-1:0]         pr0_addr_filter2_start; //Filter 2 start addres
  input  [RTT_ADDR_PP-1:0]         pr0_addr_filter2_stop;  //Filter 2 stop addres
  input  [RTT_ADDR_PP-1:0]         pr0_addr_filter3_start; //Filter 3 start addres
  input  [RTT_ADDR_PP-1:0]         pr0_addr_filter3_stop;  //Filter 3 stop addres
// leda NTL_CON13C on
  input  [`npuarc_RTT_TRG-1:0]           pr0_trigger_reg;
  input  [`npuarc_PR_WP-1:0]            pr0_wp_enable;
  input  [`npuarc_PR_WP-1:0]            pr0_wp_status;
  output [PC_PP-1:0]               pr0_filter_pc;    //Filtered PC output
  output                         pr0_inst_commit;  //Pc valid
  output                         pr0_filter_cond_valid   ;
  output                         pr0_filter_cond_pass    ;
  output                         pr0_filter_branch_indir ;
  output [PC_PP-1:0]               pr0_filter_branch_taddr ;
  output                         pr0_filter_exception    ;
  output                         pr0_filter_exception_rtn;
  output                         pr0_filter_interrupt    ;
  output                         pr0_filter_zd_loop      ;
  output                         pr0_filter_branch       ;
  output                         pr0_filter_rtt_dslot    ;
  output [7:0]                   pr0_otm_process_id;
  output                         pr0_otm_ptd_wr_en;
//`if ((0 || 0) && (`RTT_USE_EV==1)) // {
  output  [`npuarc_VDSP_AUX_DATA-1:0]   pr0_rtt_vdsp_data;     // VDSP sw trigger data
  output                         pr0_rtt_vdsp_val;      // VDSP sw trigger valid this cycle
  output reg [25:0]              cti_rtt_filters;
  input                          cti_trace_start;
  input                          cti_trace_stop;
  input                          cti_ctrl_en;
  output                         cti_trace_en_dslot;
  output                         pr0_filter_under_run;
  output  [`npuarc_PR_WP-1:0]           pr0_watchpoint_val;
//registers declaration
//  reg    [`I_CNT-1:0]            inst_cnt;
  wire                           prdcr_en;
  wire   [2-2:0]          prdcr0_src_en;
  wire                              pc_trigger_en;
  reg    [PC_PP-1:0]                pr0_filter_pc;    //Filtered PC output
  reg                               pr0_inst_commit;  //Pc valid
  reg                               pr0_filter_cond_valid   ;
  reg                               pr0_filter_cond_pass  ;
  reg                               pr0_filter_zd_loop      ;
  reg                               pr0_filter_branch_indir;
  reg    [PC_PP-1:0]                pr0_filter_branch_taddr ;
  reg                               pr0_filter_exception    ;
  reg                               pr0_filter_exception_rtn;
  reg                               pr0_filter_interrupt    ;
  reg                               pr0_filter_branch       ;
  reg                               pr0_filter_rtt_dslot  ;
  wire   [7:0]                      pr0_otm_process_id;
  wire                              pr0_otm_ptd_wr_en;
//`if ((0 || 0) && (`RTT_USE_EV==1)) // {
  wire   [`npuarc_VDSP_AUX_DATA-1:0]       pr0_rtt_vdsp_data;     // VDSP sw trigger data
  wire                              pr0_rtt_vdsp_val;      // VDSP sw trigger valid this cycle

  wire                              pc_tr0_stop;
  wire                              pc_tr0_start;
  reg                               pc_tr0_start_r;
  wire                              glen_pc_tr0_stop;
  wire                              glen_pc_tr0_start;
  reg                               glen_pc_tr0_start_r;

  wire                              pc_tr1_stop;
  wire                              pc_tr1_start;
  reg                               pc_tr1_start_r;
  wire                              glen_pc_tr1_stop;
  wire                              glen_pc_tr1_start;
  reg                               glen_pc_tr1_start_r;

  wire                              pc_tr2_stop;
  wire                              pc_tr2_start;
  reg                               pc_tr2_start_r;
  wire                              glen_pc_tr2_stop;
  wire                              glen_pc_tr2_start;
  reg                               glen_pc_tr2_start_r;

  wire                              pc_tr3_stop;
  wire                              pc_tr3_start;
  reg                               pc_tr3_start_r;
  wire                              glen_pc_tr3_stop;
  wire                              glen_pc_tr3_start;
  reg                               glen_pc_tr3_start_r;



  wire                              pr0_filter_under_run;
  wire    [`npuarc_PR_WP-1:0]               pr0_watchpoint_val;
//producer select logic
assign   prdcr_en = rtt_pr_sel;
//source enable
assign   prdcr0_src_en = pr0_src_en;

  // Global enable on either a PC range
  wire                          global_enable_range;
  // or a PC trigger (start,stop) pair.
  wire                          global_enable_trigger;
  // For syntactic convenience, the disjunction of the previous two.
  wire                          global_enable;
  // To retain global_en valus in case of bogus PC's
  reg    [PC_PP-1:0]              good_pr0_pc;
  wire   [PC_PP-1:0]              global_pr0_pc;
  wire                          valid_pc;

reg i_cti_trace_start_r;
wire i_cti_trace_en;
wire i_cti_trace_stop;
wire [25:0] i_cti_filters_a;
wire [7:0] cti_filt_start, cti_filt_stop, cti_filt_act;
wire cti_filt_d0, cti_filt_d1;

always @ (posedge rtt_clk or posedge rst_a)
begin
  if (rst_a == 1'b1)
  begin
    i_cti_trace_start_r <= 1'b0;
  end
  else
  begin
    if ((cti_trace_stop == 1'b1) || (~prdcr_en))
      i_cti_trace_start_r <= 1'b0;
    else if (cti_trace_start == 1'b1)
      i_cti_trace_start_r <= 1'b1;
  end
end

assign i_cti_trace_en = (cti_ctrl_en) ? (cti_trace_start | i_cti_trace_start_r) : 1'b1;
assign cti_trace_en_dslot = (cti_ctrl_en) ? (cti_trace_start | (i_cti_trace_start_r && ~((cti_trace_stop == 1'b1) || (~prdcr_en)))) : 1'b1;

//Qualified CTI trace stop to clear active trigger filters
assign i_cti_trace_stop = cti_ctrl_en & cti_trace_stop;

assign cti_filt_start[0] = (glen_pc_tr0_start | pc_tr0_start);
assign cti_filt_stop[0] = (glen_pc_tr0_stop | pc_tr0_stop);
assign cti_filt_act[0] = (glen_pc_tr0_start_r | pc_tr0_start_r);
assign cti_filt_start[1] = (glen_pc_tr1_start | pc_tr1_start);
assign cti_filt_stop[1] = (glen_pc_tr1_stop | pc_tr1_stop);
assign cti_filt_act[1] = (glen_pc_tr1_start_r | pc_tr1_start_r);
assign cti_filt_start[2] = (glen_pc_tr2_start | pc_tr2_start);
assign cti_filt_stop[2] = (glen_pc_tr2_stop | pc_tr2_stop);
assign cti_filt_act[2] = (glen_pc_tr2_start_r | pc_tr2_start_r);
assign cti_filt_start[3] = (glen_pc_tr3_start | pc_tr3_start);
assign cti_filt_stop[3] = (glen_pc_tr3_stop | pc_tr3_stop);
assign cti_filt_act[3] = (glen_pc_tr3_start_r | pc_tr3_start_r);
assign cti_filt_start[4] = 1'b0;
assign cti_filt_stop[4] = 1'b0;
assign cti_filt_act[4] = 1'b0;
assign cti_filt_start[5] = 1'b0;
assign cti_filt_stop[5] = 1'b0;
assign cti_filt_act[5] = 1'b0;
assign cti_filt_start[6] = 1'b0;
assign cti_filt_stop[6] = 1'b0;
assign cti_filt_act[6] = 1'b0;
assign cti_filt_start[7] = 1'b0;
assign cti_filt_stop[7] = 1'b0;
assign cti_filt_act[7] = 1'b0;
assign cti_filt_d0 = 1'b0;
assign cti_filt_d1 = 1'b0;

assign i_cti_filters_a = {cti_filt_d1, cti_filt_d0, cti_filt_act, cti_filt_stop, cti_filt_start};

always @(posedge rtt_clk or posedge rst_a)
begin : cti_filters_PROC
  if (rst_a == 1'b1)
    cti_rtt_filters <= 26'b0;
  else
    cti_rtt_filters <= i_cti_filters_a;
end


// Indicates that pr0_pc is valid (e.g., not speculative).
assign valid_pc = (pr0_rtt_inst_commit == 1'b1) || (pr0_rtt_interrupt == 1'b1) || (pr0_rtt_exception == 1'b1);

          wire pr0_pc_cmp0;
          wire pr0_pc_cmp1;
          wire pr0_pc_cmp2;
          wire pr0_pc_cmp3;

generate if ((RTT_ADDR_PP-PC_PP)>1) begin:_pad_pc_1
          assign pr0_pc_cmp0 = (global_pr0_pc >= pr0_addr_filter0_start[31:1]) && (global_pr0_pc <= pr0_addr_filter0_stop[31:1]);
          assign pr0_pc_cmp1 = (global_pr0_pc >= pr0_addr_filter1_start[31:1]) && (global_pr0_pc <= pr0_addr_filter1_stop[31:1]);
          assign pr0_pc_cmp2 = (global_pr0_pc >= pr0_addr_filter2_start[31:1]) && (global_pr0_pc <= pr0_addr_filter2_stop[31:1]);
          assign pr0_pc_cmp3 = (global_pr0_pc >= pr0_addr_filter3_start[31:1]) && (global_pr0_pc <= pr0_addr_filter3_stop[31:1]);
assign global_pr0_pc       = (valid_pc && prdcr_en) ?
                             pr0_pc :
                             good_pr0_pc;

end else begin:_pad_pc_0
          assign pr0_pc_cmp0 = (global_pr0_pc >= pr0_addr_filter0_start[31:1]) && (global_pr0_pc <= pr0_addr_filter0_stop[31:1]);
          assign pr0_pc_cmp1 = (global_pr0_pc >= pr0_addr_filter1_start[31:1]) && (global_pr0_pc <= pr0_addr_filter1_stop[31:1]);
          assign pr0_pc_cmp2 = (global_pr0_pc >= pr0_addr_filter2_start[31:1]) && (global_pr0_pc <= pr0_addr_filter2_stop[31:1]);
          assign pr0_pc_cmp3 = (global_pr0_pc >= pr0_addr_filter3_start[31:1]) && (global_pr0_pc <= pr0_addr_filter3_stop[31:1]);
assign global_pr0_pc       = (valid_pc && prdcr_en) ?
                             pr0_pc :
                             good_pr0_pc;

end
endgenerate

always @ (posedge rtt_clk or posedge rst_a)
begin : GOOD_pr0_pc_PROC
   if (rst_a == 1'b1) begin
     good_pr0_pc  <=     {PC_PP{1'b0}};
   end
   else if (valid_pc && prdcr_en) begin
     good_pr0_pc  <=     pr0_pc;
  end
 end




assign global_enable_range =
// See if a filter is programmed for global enable.
   (~pr0_trigger_reg[0] &&   // Is this a range (instead of trigger)?
     (pr0_filter_type[0+:3] == 3'b111) && pr0_pc_cmp0 ) ||
   (~pr0_trigger_reg[1] &&   // Is this a range (instead of trigger)?
     (pr0_filter_type[3+:3] == 3'b111) && pr0_pc_cmp1 ) ||
   (~pr0_trigger_reg[2] &&   // Is this a range (instead of trigger)?
     (pr0_filter_type[6+:3] == 3'b111) && pr0_pc_cmp2 ) ||
   (~pr0_trigger_reg[3] &&   // Is this a range (instead of trigger)?
     (pr0_filter_type[9+:3] == 3'b111) && pr0_pc_cmp3 ) ||
   // Enabled if no enable filter exists preventing it.
   (
    (pr0_filter_type[0+:3] != 3'b111) &&
    (pr0_filter_type[3+:3] != 3'b111) &&
    (pr0_filter_type[6+:3] != 3'b111) &&
    (pr0_filter_type[9+:3] != 3'b111));


// Global enable pc trigger enable and stop registers.
  assign  glen_pc_tr0_start =
      (pr0_filter_type[0+:3] ==3'b111) &&
      (global_pr0_pc == pr0_addr_filter0_start[31:1]) && valid_pc &&
      pr0_trigger_reg[0]   // Is this a trigger (instead of range)?
      ;
  assign  glen_pc_tr0_stop =
      (pr0_filter_type[0+:3] ==3'b111) &&
      (global_pr0_pc == pr0_addr_filter0_stop[31:1]) && (pr0_rtt_inst_commit == 1'b1) &&
      pr0_trigger_reg[0] &&   // Is this a trigger (instead of range)?
      glen_pc_tr0_start_r &&
      (~pr0_rtt_exception) && (~pr0_rtt_interrupt)
      ;

always @ (posedge rtt_clk or posedge rst_a)
begin : pc_GLEN_TRIGGER_START0_PROC
   if (rst_a == 1'b1) begin
     glen_pc_tr0_start_r <=     1'b0;
   end
     // Unlike all other trigger calculations, this one is NOT conditioned
     // on (~global_enable), as we are computing global enable here.
   else if (glen_pc_tr0_stop ||
           (i_cti_trace_stop) ||
           (~prdcr_en)) begin
     glen_pc_tr0_start_r  <= 1'b0;
  end
   else if (glen_pc_tr0_start) begin
     glen_pc_tr0_start_r  <= 1'b1;
  end
end
  assign  glen_pc_tr1_start =
      (pr0_filter_type[3+:3] ==3'b111) &&
      (global_pr0_pc == pr0_addr_filter1_start[31:1]) && valid_pc &&
      pr0_trigger_reg[1]   // Is this a trigger (instead of range)?
      ;
  assign  glen_pc_tr1_stop =
      (pr0_filter_type[3+:3] ==3'b111) &&
      (global_pr0_pc == pr0_addr_filter1_stop[31:1]) && (pr0_rtt_inst_commit == 1'b1) &&
      pr0_trigger_reg[1] &&   // Is this a trigger (instead of range)?
      glen_pc_tr1_start_r &&
      (~pr0_rtt_exception) && (~pr0_rtt_interrupt)
      ;

always @ (posedge rtt_clk or posedge rst_a)
begin : pc_GLEN_TRIGGER_START1_PROC
   if (rst_a == 1'b1) begin
     glen_pc_tr1_start_r <=     1'b0;
   end
     // Unlike all other trigger calculations, this one is NOT conditioned
     // on (~global_enable), as we are computing global enable here.
   else if (glen_pc_tr1_stop ||
           (i_cti_trace_stop) ||
           (~prdcr_en)) begin
     glen_pc_tr1_start_r  <= 1'b0;
  end
   else if (glen_pc_tr1_start) begin
     glen_pc_tr1_start_r  <= 1'b1;
  end
end
  assign  glen_pc_tr2_start =
      (pr0_filter_type[6+:3] ==3'b111) &&
      (global_pr0_pc == pr0_addr_filter2_start[31:1]) && valid_pc &&
      pr0_trigger_reg[2]   // Is this a trigger (instead of range)?
      ;
  assign  glen_pc_tr2_stop =
      (pr0_filter_type[6+:3] ==3'b111) &&
      (global_pr0_pc == pr0_addr_filter2_stop[31:1]) && (pr0_rtt_inst_commit == 1'b1) &&
      pr0_trigger_reg[2] &&   // Is this a trigger (instead of range)?
      glen_pc_tr2_start_r &&
      (~pr0_rtt_exception) && (~pr0_rtt_interrupt)
      ;

always @ (posedge rtt_clk or posedge rst_a)
begin : pc_GLEN_TRIGGER_START2_PROC
   if (rst_a == 1'b1) begin
     glen_pc_tr2_start_r <=     1'b0;
   end
     // Unlike all other trigger calculations, this one is NOT conditioned
     // on (~global_enable), as we are computing global enable here.
   else if (glen_pc_tr2_stop ||
           (i_cti_trace_stop) ||
           (~prdcr_en)) begin
     glen_pc_tr2_start_r  <= 1'b0;
  end
   else if (glen_pc_tr2_start) begin
     glen_pc_tr2_start_r  <= 1'b1;
  end
end
  assign  glen_pc_tr3_start =
      (pr0_filter_type[9+:3] ==3'b111) &&
      (global_pr0_pc == pr0_addr_filter3_start[31:1]) && valid_pc &&
      pr0_trigger_reg[3]   // Is this a trigger (instead of range)?
      ;
  assign  glen_pc_tr3_stop =
      (pr0_filter_type[9+:3] ==3'b111) &&
      (global_pr0_pc == pr0_addr_filter3_stop[31:1]) && (pr0_rtt_inst_commit == 1'b1) &&
      pr0_trigger_reg[3] &&   // Is this a trigger (instead of range)?
      glen_pc_tr3_start_r &&
      (~pr0_rtt_exception) && (~pr0_rtt_interrupt)
      ;

always @ (posedge rtt_clk or posedge rst_a)
begin : pc_GLEN_TRIGGER_START3_PROC
   if (rst_a == 1'b1) begin
     glen_pc_tr3_start_r <=     1'b0;
   end
     // Unlike all other trigger calculations, this one is NOT conditioned
     // on (~global_enable), as we are computing global enable here.
   else if (glen_pc_tr3_stop ||
           (i_cti_trace_stop) ||
           (~prdcr_en)) begin
     glen_pc_tr3_start_r  <= 1'b0;
  end
   else if (glen_pc_tr3_start) begin
     glen_pc_tr3_start_r  <= 1'b1;
  end
end

// Global enable pc trigger.
assign  global_enable_trigger =
    glen_pc_tr0_start_r || glen_pc_tr0_start ||
    glen_pc_tr1_start_r || glen_pc_tr1_start ||
    glen_pc_tr2_start_r || glen_pc_tr2_start ||
    glen_pc_tr3_start_r || glen_pc_tr3_start ||
    1'b0 ;

assign global_enable = (global_enable_range|global_enable_trigger)
                     & i_cti_trace_en
                       ;





// Programmable address Filters logic

//pc trigger enable and stop registers.

  assign  pc_tr0_start = ((pr0_filter_type[0+:3] ==3'b001) && (pr0_pc == pr0_addr_filter0_start[31:1]) && (pr0_trigger_reg[0] ) && valid_pc );
  assign  pc_tr0_stop = ((pr0_filter_type[0+:3] ==3'b001) && (pr0_pc == pr0_addr_filter0_stop[31:1]) && (pr0_trigger_reg[0]))  && pc_tr0_start_r &&
      (pr0_rtt_inst_commit == 1'b1) && (~pr0_rtt_exception) && (~pr0_rtt_interrupt)
     ;

always @ (posedge rtt_clk or posedge rst_a)
begin : pc_TRIGGER_START0_PROC
   if (rst_a == 1'b1) begin
     pc_tr0_start_r <=     1'b0;
   end
   else if (pc_tr0_stop || (~prdcr_en) ||
    (~global_enable) || i_cti_trace_stop) begin
     pc_tr0_start_r  <= 1'b0;
  end
   else if (pc_tr0_start) begin
     pc_tr0_start_r  <= 1'b1;
  end
end



  assign  pc_tr1_start = ((pr0_filter_type[3+:3] ==3'b001) && (pr0_pc == pr0_addr_filter1_start[31:1]) && (pr0_trigger_reg[1] ) && valid_pc );
  assign  pc_tr1_stop = ((pr0_filter_type[3+:3] ==3'b001) && (pr0_pc == pr0_addr_filter1_stop[31:1]) && (pr0_trigger_reg[1]))  && pc_tr1_start_r &&
      (pr0_rtt_inst_commit == 1'b1) && (~pr0_rtt_exception) && (~pr0_rtt_interrupt)
     ;

always @ (posedge rtt_clk or posedge rst_a)
begin : pc_TRIGGER_START1_PROC
   if (rst_a == 1'b1) begin
     pc_tr1_start_r <=     1'b0;
   end
   else if (pc_tr1_stop || (~prdcr_en) ||
    (~global_enable) || i_cti_trace_stop) begin
     pc_tr1_start_r  <= 1'b0;
  end
   else if (pc_tr1_start) begin
     pc_tr1_start_r  <= 1'b1;
  end
end



  assign  pc_tr2_start = ((pr0_filter_type[6+:3] ==3'b001) && (pr0_pc == pr0_addr_filter2_start[31:1]) && (pr0_trigger_reg[2] ) && valid_pc );
  assign  pc_tr2_stop = ((pr0_filter_type[6+:3] ==3'b001) && (pr0_pc == pr0_addr_filter2_stop[31:1]) && (pr0_trigger_reg[2]))  && pc_tr2_start_r &&
      (pr0_rtt_inst_commit == 1'b1) && (~pr0_rtt_exception) && (~pr0_rtt_interrupt)
     ;

always @ (posedge rtt_clk or posedge rst_a)
begin : pc_TRIGGER_START2_PROC
   if (rst_a == 1'b1) begin
     pc_tr2_start_r <=     1'b0;
   end
   else if (pc_tr2_stop || (~prdcr_en) ||
    (~global_enable) || i_cti_trace_stop) begin
     pc_tr2_start_r  <= 1'b0;
  end
   else if (pc_tr2_start) begin
     pc_tr2_start_r  <= 1'b1;
  end
end



  assign  pc_tr3_start = ((pr0_filter_type[9+:3] ==3'b001) && (pr0_pc == pr0_addr_filter3_start[31:1]) && (pr0_trigger_reg[3] ) && valid_pc );
  assign  pc_tr3_stop = ((pr0_filter_type[9+:3] ==3'b001) && (pr0_pc == pr0_addr_filter3_stop[31:1]) && (pr0_trigger_reg[3]))  && pc_tr3_start_r &&
      (pr0_rtt_inst_commit == 1'b1) && (~pr0_rtt_exception) && (~pr0_rtt_interrupt)
     ;

always @ (posedge rtt_clk or posedge rst_a)
begin : pc_TRIGGER_START3_PROC
   if (rst_a == 1'b1) begin
     pc_tr3_start_r <=     1'b0;
   end
   else if (pc_tr3_stop || (~prdcr_en) ||
    (~global_enable) || i_cti_trace_stop) begin
     pc_tr3_start_r  <= 1'b0;
  end
   else if (pc_tr3_start) begin
     pc_tr3_start_r  <= 1'b1;
  end
end




//PC trigger enable
assign  pc_trigger_en =
    pc_tr0_start_r || pc_tr0_start ||
    pc_tr1_start_r || pc_tr1_start ||
    pc_tr2_start_r || pc_tr2_start ||
    pc_tr3_start_r || pc_tr3_start ||
    1'b0 ;
//////////////////////////////////////////////////////


always @ (posedge rtt_clk or posedge rst_a)
begin : ADDR_PC_PROC
  if (rst_a == 1'b1) begin
          pr0_filter_pc            <=  0;
          pr0_inst_commit          <=  1'b0;
          pr0_filter_cond_valid    <=  1'b0;
          pr0_filter_cond_pass     <=  1'b0;
          pr0_filter_branch_indir  <=  1'b0;
          pr0_filter_branch_taddr  <=  0;
          pr0_filter_exception     <=  1'b0;
          pr0_filter_interrupt     <=  1'b0;
          pr0_filter_zd_loop       <=  1'b0;
          pr0_filter_branch        <=  1'b0;
          pr0_filter_rtt_dslot     <=  1'b0;
  end
  else if  (((prdcr_en == 1'b1) && (prdcr0_src_en[0] == 1'b1 && global_enable) && valid_pc) &&
           ((
           (
          ((pr0_filter_type[0+:3] == 3'b001) && ~pr0_trigger_reg[0] && pr0_pc_cmp0) ||
          ((pr0_filter_type[3+:3] == 3'b001) && ~pr0_trigger_reg[1] && pr0_pc_cmp1) ||
          ((pr0_filter_type[6+:3] == 3'b001) && ~pr0_trigger_reg[2] && pr0_pc_cmp2) ||
          ((pr0_filter_type[9+:3] == 3'b001) && ~pr0_trigger_reg[3] && pr0_pc_cmp3) ||
          1'b0 ) || (pc_trigger_en == 1'b1) ) ||
          // Enabled if no enable filter exists preventing it.
         (
          (pr0_filter_type[0+:3] != 3'b001) &&
          (pr0_filter_type[3+:3] != 3'b001) &&
          (pr0_filter_type[6+:3] != 3'b001) &&
          (pr0_filter_type[9+:3] != 3'b001))
          ) )

        begin
          pr0_filter_pc            <=  pr0_pc;
          pr0_inst_commit          <=  pr0_rtt_inst_commit;
          pr0_filter_cond_valid    <=  pr0_rtt_cond_valid;
          pr0_filter_cond_pass     <=  pr0_rtt_cond_pass;
          pr0_filter_branch_indir  <=  pr0_rtt_branch_indir ;
          pr0_filter_branch_taddr  <=  pr0_rtt_branch_taddr;
          pr0_filter_exception     <=  pr0_rtt_exception ;
          pr0_filter_interrupt     <=  pr0_rtt_interrupt;
          pr0_filter_zd_loop       <=  pr0_rtt_zd_loop;
          pr0_filter_branch        <=  pr0_rtt_branch;
          pr0_filter_rtt_dslot     <=  pr0_rtt_dslot;
        end //end of filter type if

    else begin // instruction commit else
     pr0_filter_pc            <=  0;
     pr0_inst_commit          <=  1'b0;
     pr0_filter_cond_valid    <=  1'b0;
     pr0_filter_cond_pass     <=  1'b0;
     pr0_filter_branch_indir  <=  1'b0;
     pr0_filter_branch_taddr  <=  0;
     pr0_filter_exception     <=  1'b0;
     pr0_filter_interrupt     <=  1'b0;
     pr0_filter_zd_loop       <=  1'b0;
     pr0_filter_branch        <=  1'b0;
     pr0_filter_rtt_dslot     <=  1'b0;
    end // instruction commit else end

 end // end of source always



always @ (posedge rtt_clk or posedge rst_a) 
begin : RTT_ST_PROC_1
  if (rst_a == 1'b1) begin
    pr0_filter_exception_rtn <=  1'b0 ;
  end
  else begin
    pr0_filter_exception_rtn <=  pr0_rtt_exception_rtn ;
  end
end

/// ***************** data filter section ********************************************************//
// leda N_7C_G off

// leda N_7C_G on


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///watchpoint messages
assign pr0_watchpoint_val[0] = rtt_pr_sel && pr0_wp_enable[0] && pr0_wp_status[0];
assign pr0_watchpoint_val[1] = rtt_pr_sel && pr0_wp_enable[1] && pr0_wp_status[1];
assign pr0_watchpoint_val[2] = rtt_pr_sel && pr0_wp_enable[2] && pr0_wp_status[2];
assign pr0_watchpoint_val[3] = rtt_pr_sel && pr0_wp_enable[3] && pr0_wp_status[3];
assign pr0_watchpoint_val[4] = rtt_pr_sel && pr0_wp_enable[4] && pr0_wp_status[4];
assign pr0_watchpoint_val[5] = rtt_pr_sel && pr0_wp_enable[5] && pr0_wp_status[5];
assign pr0_watchpoint_val[6] = rtt_pr_sel && pr0_wp_enable[6] && pr0_wp_status[6];
assign pr0_watchpoint_val[7] = rtt_pr_sel && pr0_wp_enable[7] && pr0_wp_status[7];

 //OTMs

assign pr0_otm_process_id =  (rtt_pr_sel && pr0_pid_wr_en) ? pr0_process_id : 8'b0;
assign pr0_otm_ptd_wr_en  =  (rtt_pr_sel) ?  pr0_pid_wr_en : 1'b0;
//`if ((0 || 0) && (`RTT_USE_EV==1)) // {
assign pr0_rtt_vdsp_data =  (rtt_pr_sel && rtt_vdsp_val) ? rtt_vdsp_data : `npuarc_VDSP_AUX_DATA'b0;
assign pr0_rtt_vdsp_val  =  (rtt_pr_sel) ?  rtt_vdsp_val : 1'b0;

// producer under run
assign  pr0_filter_under_run = prdcr_en && (
pr0_inst_commit
);
endmodule
