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
//   rtt_encapsulation_top
//
// ===========================================================================
//
// Description:
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_encapsulation_top.vpp
//
// ===========================================================================


`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"

module npuarc_rtt_small_encapsulation_top #(parameter PTCM_WDT_PP = 120, parameter PCM_WDT_PP = 80, parameter PTM_WDT_PP = 120, parameter PC_PP = 31, parameter RTT_ADDR_PP=32) (

 rtt_clk,
  rst_a,

  pr_num,
  rtt_ss_halt,
  rtt_sw_bp,
  rtt_hw_bp,
  rtt_hwe,
  rtt_enter_sleep,
  rtt_dbg_halt,
  core_rst,
  sys_halt_r,

  rtt_dslot,
  rtt_uop_is_leave,
  rtt_in_deslot,
  rtt_in_eslot,
  unfilter_exception    ,
  unfilter_interrupt    ,
  unfilter_zd_loop      ,
  rtt_branch_taddr,
  rtt_pr_sel,
  pr0_src_en ,
  pr0_dsm_en ,
  rtt_wp_val,
  pr0_watchpoint_val,

  pr0_pc,  //Unfiltered PC input
  pr0_filter_pc,  //Filtered PC input
  pr0_inst_commit,  //Pc valid
  pr0_filter_cond_valid   ,
  pr0_filter_cond_pass    ,
  rtt_inst_commit,  //Unfiltered Pc valid
  pr0_filter_branch_indir ,
  pr0_filter_exception    ,
  pr0_filter_exception_rtn,
  pr0_filter_interrupt    ,
  pr0_filter_zd_loop      ,
  pr0_filter_branch       ,
  pr0_time_stamp,   // Time stamp



 //input declarations
  pr0_cmpr_ptm_taddr,
  unfiltered_relative_pc,

  pr0_rtt_process_id,
  pr0_rtt_pid_wr_en,
  vdswm_en,
  vdspm_sbuf_num_fill,
  vdspm_sbuf_freeze,
  pr0_rtt_vdsp_data,     // VDSP sw trigger data
  pr0_rtt_vdsp_val,      // VDSP sw trigger valid this cycle

  rtt_time_stamp_en,
  flush_cmd,
  flush_done,
  filter_busy,
  compressor_busy,

  ptm_dropped,

  pt_sync_msg,
  pt_msg_valid_cmpr,
  pc_msg_valid_cmpr,

  p0_atb_syncreq,
 cti_trace_en_dslot,
  para_done,
  bhth,
  p0_cstimestamp,
  p0_csts_en,
  p0_req,
  p0_ack,
  p0_wdata,

  freeze_status,

  pc_sbuf_num_fill,
  ptc_sbuf_num_fill,
  pt_sbuf_num_fill,
  errm_sbuf_num_fill,
  otm_sbuf_num_fill,
  rfm_sbuf_num_fill,
  wpm_sbuf_num_fill,
  ds_sbuf_num_fill,
  encapsulation_top_busy,



  ds_sbuf_wr_en,
  ds_sbuf_rd_en,
  ds_sbuf_wr_data,
  ds_sbuf_rd_data,
  ds_sbuf_wr_ptr,
  ds_sbuf_rd_ptr,

  vdspm_sbuf_wr_en,
  vdspm_sbuf_rd_en,
  vdspm_sbuf_wr_data,
  vdspm_sbuf_rd_data,
  vdspm_sbuf_wr_ptr,
  vdspm_sbuf_rd_ptr,




  errm_sbuf_wr_en,
  errm_sbuf_rd_en,
  errm_sbuf_wr_data,
  errm_sbuf_rd_data,
  errm_sbuf_wr_ptr,
  errm_sbuf_rd_ptr,

  otm_sbuf_wr_en,
  otm_sbuf_rd_en,
  otm_sbuf_wr_data,
  otm_sbuf_rd_data,
  otm_sbuf_wr_ptr,
  otm_sbuf_rd_ptr,


  pc_sbuf_wr_en,
  pc_sbuf_rd_en,
  pc_sbuf_wr_data,
  pc_sbuf_rd_data,
  pc_sbuf_wr_ptr,
  pc_sbuf_rd_ptr,



  ptc_sbuf_wr_en,
  ptc_sbuf_rd_en,
  ptc_sbuf_wr_data,
  ptc_sbuf_rd_data,
  ptc_sbuf_wr_ptr,
  ptc_sbuf_rd_ptr,



  pt_sbuf_wr_en,
  pt_sbuf_rd_en,
  pt_sbuf_wr_data,
  pt_sbuf_rd_data,
  pt_sbuf_wr_ptr,
  pt_sbuf_rd_ptr,



  wpm_sbuf_wr_en,
  wpm_sbuf_rd_en,
  wpm_sbuf_wr_data,
  wpm_sbuf_rd_data,
  wpm_sbuf_wr_ptr,
  wpm_sbuf_rd_ptr,

  rfm_sbuf_wr_en,
  rfm_sbuf_rd_en,
  rfm_sbuf_wr_data,
  rfm_sbuf_rd_data,
  rfm_sbuf_wr_ptr,
  rfm_sbuf_rd_ptr




);

  input                        rtt_clk;
  input                        rst_a;

  input [`npuarc_PRNUM_WDT-1:0] pr_num;
  input rtt_ss_halt;
  input rtt_sw_bp;
  input rtt_hw_bp;
  input rtt_hwe;
  input rtt_enter_sleep;
  input rtt_dbg_halt;
  input core_rst;
  input sys_halt_r;

  input                        rtt_dslot;
  input                        rtt_uop_is_leave;
  input                        rtt_in_deslot;
  input                        rtt_in_eslot;
  input                        unfilter_exception    ;
  input                        unfilter_interrupt    ;
  input                        unfilter_zd_loop      ;
  input [PC_PP-1:0]            rtt_branch_taddr;
  input                        rtt_pr_sel;
  input [2-2:0]      pr0_src_en ;
  input                        pr0_dsm_en ;
  input  [7:0]           rtt_wp_val;
  input  [`npuarc_PR_WP-1:0]           pr0_watchpoint_val;

  input [PC_PP-1:0]             pr0_pc;  //Unfiltered PC input
  input [PC_PP-1:0]             pr0_filter_pc;  //Filtered PC input
  input                         pr0_inst_commit;  //Pc valid
  input                         pr0_filter_cond_valid   ;
  input                         pr0_filter_cond_pass    ;
  input                        rtt_inst_commit;

  input                         pr0_filter_branch_indir ;
  input                         pr0_filter_exception    ;
  input                         pr0_filter_exception_rtn;
  input                         pr0_filter_interrupt    ;
  input                         pr0_filter_zd_loop      ;
  input                         pr0_filter_branch       ;
  input [`npuarc_RTT_TIME_STMP-1:0]    pr0_time_stamp;   // Time stamp


 //input declarations
  input  [PC_PP-1:0]            pr0_cmpr_ptm_taddr;
  input  [PC_PP-1:0]            unfiltered_relative_pc;

  input  [`npuarc_RTT_PID-1:0]   pr0_rtt_process_id;
  input                   pr0_rtt_pid_wr_en;
  input                        vdswm_en;
  output [`npuarc_VDSPM_BUF_DEPTH:0]  vdspm_sbuf_num_fill;
  input                        vdspm_sbuf_freeze;
  input  [`npuarc_VDSP_AUX_DATA-1:0]  pr0_rtt_vdsp_data;     // VDSP sw trigger data
  input                        pr0_rtt_vdsp_val;      // VDSP sw trigger valid this cycle

  input                   rtt_time_stamp_en;
  input                   flush_cmd;
  input                   flush_done;
  input                   filter_busy;
  input                   compressor_busy;

  output                        ptm_dropped;

  output                        pt_sync_msg;
  output                        pt_msg_valid_cmpr;
  output                        pc_msg_valid_cmpr;


  output                        p0_req;
  input                         p0_ack;
  input                         p0_atb_syncreq;
  input                         cti_trace_en_dslot;
  output [120-1:0]        p0_wdata;
  output wire                   para_done;
  input [2:0]                   bhth;
  input  [63:0]                 p0_cstimestamp;
  input                         p0_csts_en;

//leda NTL_CON13C off
  input  [`npuarc_FR_STATUS-1:0]      freeze_status;
//leda NTL_CON13C on


  output [`npuarc_PCM_BUF_DEPTH:0]  pc_sbuf_num_fill;
  output [`npuarc_PTCM_BUF_DEPTH:0]  ptc_sbuf_num_fill;
  output [`npuarc_PTM_BUF_DEPTH:0]  pt_sbuf_num_fill;
  output [`npuarc_ERRM_BUF_DEPTH:0]  errm_sbuf_num_fill;
  output [`npuarc_OTM_BUF_DEPTH:0]  otm_sbuf_num_fill;
  output [`npuarc_RFM_BUF_DEPTH:0]  rfm_sbuf_num_fill;
  output [`npuarc_WPM_BUF_DEPTH:0]  wpm_sbuf_num_fill;
  output [`npuarc_DSM_BUF_DEPTH:0]  ds_sbuf_num_fill;

  output encapsulation_top_busy;


  output                                   ds_sbuf_wr_en;
  output                                   ds_sbuf_rd_en;
  output [(`npuarc_DSM_WDT)-1:0]                  ds_sbuf_wr_data;
  input  [(`npuarc_DSM_WDT)-1:0]                  ds_sbuf_rd_data;
  output [`npuarc_DSM_BUF_DEPTH-1:0]              ds_sbuf_wr_ptr;
  output [`npuarc_DSM_BUF_DEPTH-1:0]              ds_sbuf_rd_ptr;

  output                                      vdspm_sbuf_wr_en;
  output                                      vdspm_sbuf_rd_en;
  output [(`npuarc_VDSPSW_WDT)-1:0]                  vdspm_sbuf_wr_data;
  input  [(`npuarc_VDSPSW_WDT)-1:0]                  vdspm_sbuf_rd_data;
  output [`npuarc_VDSPM_BUF_DEPTH-1:0]               vdspm_sbuf_wr_ptr;
  output [`npuarc_VDSPM_BUF_DEPTH-1:0]               vdspm_sbuf_rd_ptr;





  output                                   errm_sbuf_wr_en;
  output                                   errm_sbuf_rd_en;
  output [(`npuarc_ERRM_WDT)-1:0]                 errm_sbuf_wr_data;
  input  [(`npuarc_ERRM_WDT)-1:0]                 errm_sbuf_rd_data;
  output [`npuarc_ERRM_BUF_DEPTH-1:0]             errm_sbuf_wr_ptr;
  output [`npuarc_ERRM_BUF_DEPTH-1:0]             errm_sbuf_rd_ptr;

  output                                   otm_sbuf_wr_en;
  output                                   otm_sbuf_rd_en;
  output [(`npuarc_OTM_WDT)-1:0]                  otm_sbuf_wr_data;
  input  [(`npuarc_OTM_WDT)-1:0]                  otm_sbuf_rd_data;
  output [`npuarc_OTM_BUF_DEPTH-1:0]              otm_sbuf_wr_ptr;
  output [`npuarc_OTM_BUF_DEPTH-1:0]              otm_sbuf_rd_ptr;


  output                                   pc_sbuf_wr_en;
  output                                   pc_sbuf_rd_en;
  output [(`npuarc_PCM_WDT)-1:0]                  pc_sbuf_wr_data;
  input  [(`npuarc_PCM_WDT)-1:0]                  pc_sbuf_rd_data;
  output [`npuarc_PCM_BUF_DEPTH-1:0]              pc_sbuf_wr_ptr;
  output [`npuarc_PCM_BUF_DEPTH-1:0]              pc_sbuf_rd_ptr;



  output                                   ptc_sbuf_wr_en;
  output                                   ptc_sbuf_rd_en;
  output [(PTCM_WDT_PP)-1:0]               ptc_sbuf_wr_data;
  input  [(PTCM_WDT_PP)-1:0]               ptc_sbuf_rd_data;
  output [`npuarc_PTCM_BUF_DEPTH-1:0]             ptc_sbuf_wr_ptr;
  output [`npuarc_PTCM_BUF_DEPTH-1:0]             ptc_sbuf_rd_ptr;



  output                                   pt_sbuf_wr_en;
  output                                   pt_sbuf_rd_en;
  output [(`npuarc_PTM_WDT)-1:0]                  pt_sbuf_wr_data;
  input  [(`npuarc_PTM_WDT)-1:0]                  pt_sbuf_rd_data;
  output [`npuarc_PTM_BUF_DEPTH-1:0]              pt_sbuf_wr_ptr;
  output [`npuarc_PTM_BUF_DEPTH-1:0]              pt_sbuf_rd_ptr;




  output                                   rfm_sbuf_wr_en;
  output                                   rfm_sbuf_rd_en;
  output [(`npuarc_RFM_WDT)-1:0]                  rfm_sbuf_wr_data;
  input  [(`npuarc_RFM_WDT)-1:0]                  rfm_sbuf_rd_data;
  output [`npuarc_RFM_BUF_DEPTH-1:0]              rfm_sbuf_wr_ptr;
  output [`npuarc_RFM_BUF_DEPTH-1:0]              rfm_sbuf_rd_ptr;




  output                                   wpm_sbuf_wr_en;
  output                                   wpm_sbuf_rd_en;
  output [(`npuarc_WPM_WDT)-1:0]                  wpm_sbuf_wr_data;
  input  [(`npuarc_WPM_WDT)-1:0]                  wpm_sbuf_rd_data;
  output [`npuarc_WPM_BUF_DEPTH-1:0]              wpm_sbuf_wr_ptr;
  output [`npuarc_WPM_BUF_DEPTH-1:0]              wpm_sbuf_rd_ptr;


  wire [`npuarc_I_CNT-1:0] i_cnt;
  wire [`npuarc_HIST_WDT-1:0] hist;

  wire                    ds_msg_valid;
  wire [`npuarc_DSM_WDT-1:0]     ds_msg;
  wire                    pc_msg_valid;
  wire [`npuarc_PCM_WDT-1:0]     pc_msg;
  wire                    ptc_msg_valid;
  wire                    ptc_msg_valid_i;
  wire                    ptc_msg_valid_r;
  wire [PTCM_WDT_PP-1:0]  ptc_msg;
  wire                    pt_msg_valid;
  wire [`npuarc_PTM_WDT-1:0]     pt_msg;
  wire                    err_msg_valid;
  wire [`npuarc_ERRM_WDT-1:0]    err_msg;
  wire                    ot_msg_valid;
  wire [`npuarc_OTM_WDT-1:0]     ot_msg;
  wire [`npuarc_VDSPSW_WDT-1:0]  vdsw_msg;            // VDSP sw trigger data
  wire                    vdsw_msg_valid;      // VDSP sw trigger valid this cycle
  wire                    rf_msg_valid;
  wire [`npuarc_RFM_WDT-1:0]     rf_msg;
  wire                    wp_msg_valid;
  wire [`npuarc_WPM_WDT-1:0]     wp_msg;

  wire                    cst_msg_valid;
  wire [`npuarc_CSTM_WDT-1:0]    cst_msg;
  wire [`npuarc_RCODE_WDT-1:0]   rfm_rcode;

  wire                     sbuf_msg_processing;
  wire                     ds_sbuf_wr_en;
  wire                     ds_sbuf_rd_en;
  wire                     ds_sbuf_rd_vld;

  wire [`npuarc_DSM_WDT-1:0]      ds_sbuf_rd_data;
  wire                     ds_sbuf_full;
  wire                     ds_sbuf_empty;
  wire [`npuarc_DSM_BUF_DEPTH:0]  ds_sbuf_num_fill;

  wire                     pc_sbuf_wr_en;
  wire                     pc_sbuf_rd_en;
  wire                     pc_sbuf_rd_vld;

  wire [`npuarc_PCM_WDT-1:0]      pc_sbuf_rd_data;
  wire                     pc_sbuf_full;
  wire                     pc_sbuf_empty;
  wire [`npuarc_PCM_BUF_DEPTH:0]  pc_sbuf_num_fill;

  wire                     ptc_sbuf_wr_en;
  wire                     ptc_sbuf_rd_en;
  wire                     ptc_sbuf_rd_vld;

  wire [PTCM_WDT_PP-1:0]   ptc_sbuf_rd_data;
  wire                     ptc_sbuf_full;
  wire                     ptc_sbuf_empty;
  wire [`npuarc_PTCM_BUF_DEPTH:0]  ptc_sbuf_num_fill;


  wire                     pt_sbuf_en;
  wire                     pt_sbuf_wr_en;
  wire                     pt_sbuf_rd_en;
  wire                     pt_sbuf_rd_vld;

  wire [`npuarc_PTM_WDT-1:0]      pt_sbuf_rd_data;
  wire                     pt_sbuf_full;
  wire                     pt_sbuf_empty;
  wire [`npuarc_PTM_BUF_DEPTH:0]  pt_sbuf_num_fill;



  wire                     errm_sbuf_wr_en;
  wire                     errm_sbuf_rd_en;
  wire                     errm_sbuf_rd_vld;

  wire [`npuarc_ERRM_WDT-1:0]      errm_sbuf_rd_data;
  wire                     errm_sbuf_full;
  wire                     errm_sbuf_empty;
  wire [`npuarc_ERRM_BUF_DEPTH:0]  errm_sbuf_num_fill;

  wire                     otm_sbuf_wr_en;
  wire                     otm_sbuf_rd_en;
  wire                     otm_sbuf_rd_vld;

  wire [`npuarc_OTM_WDT-1:0]      otm_sbuf_rd_data;
  wire                     otm_sbuf_full;
  wire                     otm_sbuf_empty;
  wire [`npuarc_OTM_BUF_DEPTH:0]  otm_sbuf_num_fill;
  wire                     vdspm_sbuf_wr_en;
  wire                     vdspm_sbuf_rd_en;
  wire                     vdspm_sbuf_rd_vld;

  wire [`npuarc_VDSPSW_WDT-1:0]      vdspm_sbuf_rd_data;
  wire                      vdspm_sbuf_full;
  wire                      vdspm_sbuf_empty;
  wire [`npuarc_VDSPM_BUF_DEPTH:0] vdspm_sbuf_num_fill;

  wire                     rfm_sbuf_wr_en;
  wire                     rfm_sbuf_rd_en;
  wire                     rfm_sbuf_rd_vld;

  wire [`npuarc_RFM_WDT-1:0]      rfm_sbuf_rd_data;
  wire                     rfm_sbuf_full;
  wire                     rfm_sbuf_empty;
  wire [`npuarc_RFM_BUF_DEPTH:0]  rfm_sbuf_num_fill;

  wire                     wpm_sbuf_wr_en;
  wire                     wpm_sbuf_rd_en;
  wire                     wpm_sbuf_rd_vld;

  wire [`npuarc_WPM_WDT-1:0]      wpm_sbuf_rd_data;
  wire                     wpm_sbuf_full;
  wire                     wpm_sbuf_empty;
  wire [`npuarc_WPM_BUF_DEPTH:0]  wpm_sbuf_num_fill;

  wire cstm_sbuf_wr_en;
  wire cstm_sbuf_rd_en;
  wire cstm_sbuf_rd_vld;
  wire cstm_sbuf_empty;
  wire cstm_sbuf_full;
  wire [`npuarc_CSTM_WDT -1:0] cstm_sbuf_wr_data;
  wire [`npuarc_CSTM_WDT -1:0] cstm_sbuf_rd_data;
  wire [180-1:0] data_in0, data_in1, data_in2, data_in3, data_in4, data_in5, data_in6;
  wire [180-1:0] data_in9, data_in10, data_in11, data_in12, data_in13;






 //wire declarations

  wire any_msg_valid;
  wire any_sbuf_wr_en;
  wire sbuf_empty;
  wire sbuf_empty_done;
  wire ptcm_done;

  //wire msg_buf_full;
  wire [`npuarc_MSG_TYPE_LOST_WDT-1:0] msg_type_lost_r;
  wire [11:0] msg_buf_full_sts;
  wire [11:0] msg_type_recovered;
  wire ds_lost;
  wire ict_lost;
  wire dac_lost;
  wire dtrm_lost;
  wire dtwm_lost;

  wire dtrm_recov;
  wire dtwm_recov;

  wire dsm_en;
  wire vd_lost1;
  wire vd_lost2;
  wire vd_lost3;
  wire ds_recov;
  wire vd_recov1;
  wire vd_recov2;
  wire vd_recov3;
  wire ict_recov;
  wire dac_recov;
  wire unfiltered_inst_commit;

  wire pt_sync_msg_i;
  wire evti_i;
  wire  [`npuarc_PR_EVTI-1:0] pr0_eic_reg_i;
  reg active_prdcr;

  wire p0_req;
  wire [120-1:0] p0_wdata;
  wire p0_atb_syncreq;

 wire [180-1:0] arb_src0, arb_src1, arb_src2;
 wire [2:0] atb_sbuf_ack;
 wire [2:0] arb_val;
 wire [`npuarc_NUM_MSG_SRC-1:0] atb_sbuf_rden;
 wire sbarb_done;

 wire  [6-1:0]   msg_seq_order_q_wr_ptr;
 wire  [6-1:0]   msg_seq_order_q_rd_ptr;
 wire  [10-1:0]  msg_seq_order_q_wdata;
 wire  [10-1:0]  msg_seq_order_q_rdata;
 wire            msg_seq_order_q_wr_en;
 wire            msg_seq_order_q_rd_en;
 wire            msg_seq_order_q_empty;
 wire            msg_seq_order_q_full;

 wire para_busy;
 wire arb_busy;

 assign arb_busy = |arb_val;
 assign encapsulation_top_busy =
                                 flush_cmd ||
                                 any_msg_valid || (~sbuf_empty_done) ||
                                 arb_busy || para_busy;

 assign dsm_en = rtt_pr_sel && pr0_dsm_en;
 assign unfiltered_inst_commit = rtt_pr_sel && rtt_inst_commit;


// spyglass disable_block Clock_delay01
// SMD: Flip-flop pairs whose data path delta delay is less than the difference in their clock path delta delays
// SJ: clock for pr_sel is free running clock and clock for active_prdcr is gated clock
 always @ (posedge rtt_clk or posedge rst_a)
   begin : ACTIVE_PRDCR_PROC
     if(rst_a == 1'b1)
       active_prdcr <= 1'b0;
     else if(rtt_pr_sel)
       active_prdcr <= 1'b1;
     else if(flush_done)
       active_prdcr <= 1'b0;
   end
// spyglass enable_block Clock_delay01

 assign evti_i = 1'b0;
 assign pr0_eic_reg_i = {`npuarc_PR_EVTI{1'b0}};

  assign ds_lost = (ds_sbuf_full && ds_msg_valid);
  assign vd_lost2 = 1'b0;
  assign vd_lost3 = 1'b0;
  assign ict_lost = 1'b0;
  assign vd_lost1 = 1'b0;
  assign dac_lost = (vdspm_sbuf_full && vdsw_msg_valid);
  assign dtrm_lost = 1'b0;
  assign dtwm_lost = 1'b0;

  assign ds_recov = ((~freeze_status[10]) && ds_msg_valid);
  assign vd_recov2 = 1'b0;
  assign vd_recov3 = 1'b0;
  assign ict_recov = 1'b0;
  assign vd_recov1 = 1'b0;
 assign dac_recov = ((~vdspm_sbuf_freeze) && vdsw_msg_valid);
  assign dtrm_recov = 1'b0;
  assign dtwm_recov = 1'b0;

assign msg_buf_full_sts = {1'b0,dtwm_lost,vd_lost3,vd_lost2,vd_lost1,ict_lost,dac_lost,ds_lost,
                           (otm_sbuf_full && ot_msg_valid),
                           (pt_sbuf_full && pt_msg_valid),dtrm_lost,(wpm_sbuf_full && wp_msg_valid)};
assign msg_type_recovered = {1'b0,dtwm_recov,vd_recov3,vd_recov2,vd_recov1,ict_recov,dac_recov,ds_recov,
                            ((~freeze_status[7]) && ot_msg_valid),
                            ((~freeze_status[2]) && pt_msg_valid),dtrm_recov,((~freeze_status[9]) && wp_msg_valid)};
assign pt_sync_msg_i = (msg_type_lost_r[2] && freeze_status[2]) || (rf_msg_valid && rfm_sbuf_full);

  assign any_msg_valid = ds_msg_valid || pc_msg_valid || pt_msg_valid ||
                         cst_msg_valid ||
                         vdsw_msg_valid ||
                         ot_msg_valid ||
                         wp_msg_valid  ;

  assign sbuf_empty = ds_sbuf_empty && pc_sbuf_empty && pt_sbuf_empty && ptc_sbuf_empty &&
                      vdspm_sbuf_empty &&
                      errm_sbuf_empty &&
                      otm_sbuf_empty &&
                      cstm_sbuf_empty &&
                      wpm_sbuf_empty && rfm_sbuf_empty;

wire hist_trig;
assign hist_trig = (bhth == 3'b001) ? hist[1] :
                   (bhth == 3'b010) ? hist[2] :
                   (bhth == 3'b011) ? hist[4] :
                   (bhth == 3'b100) ? hist[8] :
                   (bhth == 3'b101) ? hist[16] : hist[30];
assign sbuf_empty_done = sbuf_empty && (~p0_req);

assign sbuf_msg_processing = ds_sbuf_rd_vld || pc_sbuf_rd_vld || pt_sbuf_rd_vld || ptc_sbuf_rd_vld ||
                      cstm_sbuf_rd_vld ||
                      vdspm_sbuf_rd_vld ||
                      errm_sbuf_rd_vld ||
                      otm_sbuf_rd_vld ||
                      wpm_sbuf_rd_vld || rfm_sbuf_rd_vld;
assign cstm_sbuf_wr_data = cst_msg;
assign cstm_sbuf_wr_en = cst_msg_valid && ((cstm_sbuf_rd_en && cstm_sbuf_full) || cstm_sbuf_empty);


assign  ds_sbuf_wr_en = ds_msg_valid && (((~msg_type_lost_r[4]) && (~ds_sbuf_full)) || (~freeze_status[10]));
assign  pc_sbuf_wr_en = pc_msg_valid && (~pc_sbuf_full);
assign  ptc_sbuf_wr_en = ptc_msg_valid && (~ptc_sbuf_full);
assign  pt_sbuf_en = (((~msg_type_lost_r[2]) && (~pt_sbuf_full)) || (~freeze_status[2]));
assign  pt_sbuf_wr_en = pt_msg_valid && pt_sbuf_en;
assign  vdspm_sbuf_wr_en = vdsw_msg_valid && (((~msg_type_lost_r[5]) && (~vdspm_sbuf_full)) || (~vdspm_sbuf_freeze));
assign  errm_sbuf_wr_en = err_msg_valid && (~errm_sbuf_full);
assign  otm_sbuf_wr_en = ot_msg_valid && (((~msg_type_lost_r[3]) && (~otm_sbuf_full)) || (~freeze_status[7]));
assign  rfm_sbuf_wr_en = rf_msg_valid && (~rfm_sbuf_full);
assign  wpm_sbuf_wr_en = wp_msg_valid && (((~msg_type_lost_r[0]) && (~wpm_sbuf_full)) || (~freeze_status[9]));

assign any_sbuf_wr_en = ds_sbuf_wr_en   || pc_sbuf_wr_en  || ptc_sbuf_wr_en  || pt_sbuf_wr_en  || 
                        vdspm_sbuf_wr_en ||
                        otm_sbuf_wr_en ||
                        cstm_sbuf_wr_en ||
                        errm_sbuf_wr_en || rfm_sbuf_wr_en || wpm_sbuf_wr_en;
                        


assign ds_sbuf_wr_data = ds_msg;
assign pc_sbuf_wr_data = pc_msg;
assign ptc_sbuf_wr_data = ptc_msg;
assign wpm_sbuf_wr_data = wp_msg;
assign otm_sbuf_wr_data = ot_msg;
assign pt_sbuf_wr_data = pt_msg;

assign vdspm_sbuf_wr_data = vdsw_msg;
assign errm_sbuf_wr_data = err_msg;
assign rfm_sbuf_wr_data = rf_msg;



assign ptcm_done = sbuf_empty_done && (~sbuf_msg_processing) && ptc_msg_valid_r;


assign ptm_dropped = 1'b0;

wire rf_msg_valid_icnt;
assign rf_msg_valid_icnt = rf_msg_valid && (~pt_msg_valid);

npuarc_rtt_ds_encapsulation u_rtt_ds_encapsulation(

.rtt_clk(rtt_clk),

.sys_reset(rst_a),

.dsm_en(dsm_en),
.pr_num(pr_num),

.rtt_ss_halt(rtt_ss_halt),
.rtt_sw_bp(rtt_sw_bp),
.rtt_hw_bp(rtt_hw_bp),
.rtt_hwe(rtt_hwe),
.rtt_enter_sleep(rtt_enter_sleep),
.rtt_dbg_halt(rtt_dbg_halt),
.core_rst(core_rst),
.rtt_wp_val(rtt_wp_val),

.timestamp(pr0_time_stamp),

.ds_msg_valid(ds_msg_valid),
.ds_msg(ds_msg)

);



npuarc_rtt_pc_encapsulation #(.PCM_WDT_PP(PCM_WDT_PP), .PC_PP(PC_PP)) u_rtt_pc_encapsulation(

.rtt_clk(rtt_clk),

.sys_reset(rst_a),

.pr_num(pr_num),

.pr0_filter_pc(pr0_filter_pc),
.pr0_inst_commit(pr0_inst_commit),
.ptc_msg_valid(ptc_msg_valid_i),
.exception(pr0_filter_exception),
.interrupt(pr0_filter_interrupt),
.zd_loop(pr0_filter_zd_loop),

.timestamp(pr0_time_stamp),

.pc_msg_valid(pc_msg_valid),
.pc_msg(pc_msg)

);


npuarc_rtt_ptc_encapsulation #(.PTCM_WDT_PP(PTCM_WDT_PP), .PC_PP(PC_PP)) u_rtt_ptc_encapsulation(

.rtt_clk(rtt_clk),

.sys_reset(rst_a),
.pr_num(pr_num),

.i_cnt(i_cnt),
.hist(hist),

.exception(pr0_filter_exception),
.interrupt(pr0_filter_interrupt),
.zd_loop(pr0_filter_zd_loop),
.unfilter_exception(unfilter_exception),
.unfilter_interrupt(unfilter_interrupt),
.unfilter_zd_loop(unfilter_zd_loop),
.pr0_inst_commit(pr0_inst_commit),
.unfiltered_inst_commit(unfiltered_inst_commit),
.unfiltered_relative_pc(unfiltered_relative_pc),
.pc_msg_valid(pc_msg_valid),
.flush_cmd(flush_cmd),
.flush_done(flush_done),
.filter_busy(filter_busy),
.compressor_busy(compressor_busy),
.sbuf_empty(sbuf_empty_done),
.active_prdcr(active_prdcr),

.timestamp(pr0_time_stamp),

.ptc_msg_valid_r(ptc_msg_valid_r),
.ptc_msg_valid(ptc_msg_valid),
.ptc_msg_valid_i(ptc_msg_valid_i),
.ptc_msg(ptc_msg)

);


npuarc_rtt_pt_encapsulation #(.PTM_WDT_PP(PTM_WDT_PP), .PC_PP(PC_PP)) u_rtt_pt_encapsulation (

.rtt_clk(rtt_clk),

.sys_reset(rst_a),
.pt_sync_msg_i(pt_sync_msg_i),
.pt_en(pr0_src_en[0]),
.pr_num(pr_num),
.taddr(pr0_cmpr_ptm_taddr),
.rtt_uop_is_leave(rtt_uop_is_leave),
.rtt_in_deslot(rtt_in_deslot),
.rtt_in_eslot(rtt_in_eslot),
.inst_commit(pr0_inst_commit),
.cond_valid(pr0_filter_cond_valid),
.cond_pass(pr0_filter_cond_pass),
.unfiltered_inst_commit(unfiltered_inst_commit),
.unfiltered_pc(pr0_pc),
.rtt_dslot(rtt_dslot),
.branch(pr0_filter_branch),
.branch_indir(pr0_filter_branch_indir),
.exception(pr0_filter_exception),
.interrupt(pr0_filter_interrupt),
.zd_loop(pr0_filter_zd_loop),
.timestamp(pr0_time_stamp),
.resource_full(rf_msg_valid),
.ptc_msg_valid_i(ptc_msg_valid_i),
.unfiltered_taddr(rtt_branch_taddr),
.pr_sel(rtt_pr_sel),

.atb_syncreq(p0_atb_syncreq),
.cti_trace_en_dslot(cti_trace_en_dslot),  
.pt_sbuf_en(pt_sbuf_en),

.i_cnt_a(i_cnt),
.hist(hist),
.hist_trig(hist_trig),

.pt_sync_msg(pt_sync_msg),
.pt_msg_valid(pt_msg_valid),
.pt_msg(pt_msg)

);

assign pt_msg_valid_cmpr = pt_msg_valid;
assign pc_msg_valid_cmpr = pc_msg_valid;




npuarc_rtt_vdsp33_daqm_encapsulation u_rtt_vdswm_encapsulation (
.p0_msg_en(vdswm_en),
.ext_num(6'b0),
.timestamp(pr0_time_stamp),
.datain_val(pr0_rtt_vdsp_val),
.datain (pr0_rtt_vdsp_data),

.msg_valid(vdsw_msg_valid),
.msg(vdsw_msg)
);





// spyglass disable_block UnloadedOutTerm-ML
// MD: msg_type_lost_r conditionally used for small/med/full prdcr
npuarc_rtt_errm_encapsulation u_rtt_errm_encapsulation (

.rtt_clk(rtt_clk),

.sys_reset(rst_a),
.pr_num(pr_num),
.msg_type_lost(msg_buf_full_sts),
.msg_type_lost_r(msg_type_lost_r),
.msg_type_recovered(msg_type_recovered),

.timestamp(pr0_time_stamp),

.err_msg_valid(err_msg_valid),
.err_msg(err_msg)

);
// spyglass enable_block UnloadedOutTerm-ML



npuarc_rtt_otm_encapsulation u_rtt_otm_encapsulation (

.rtt_clk(rtt_clk),
.rst_a(rst_a),


.pid_wr_en(pr0_rtt_pid_wr_en),
.processid(pr0_rtt_process_id),

.pr_num(pr_num),

.timestamp(pr0_time_stamp),

.ot_msg_valid(ot_msg_valid),
.ot_msg(ot_msg)

);


npuarc_rtt_rfm_encapsulation u_rtt_rfm_encapsulation(

.rfm_en(rtt_pr_sel),
.pr_num(pr_num),
.sys_halt_r(sys_halt_r),

.i_cnt(i_cnt),
.hist(hist),
.hist_trig(hist_trig),
.inst_commit(pr0_inst_commit),
.ptc_msg_valid(ptc_msg_valid),
.pt_msg_valid(pt_msg_valid),

.rtt_time_stamp_en(rtt_time_stamp_en),
.timestamp(pr0_time_stamp),

.rcode(rfm_rcode),
.rf_msg_valid(rf_msg_valid),
.rf_msg(rf_msg)

);

npuarc_rtt_wpm_encapsulation u_rtt_wpm_encapsulation(

.pr0_watchpoint_val(pr0_watchpoint_val),

.pr_num(pr_num),
.timestamp(pr0_time_stamp),

.wp_msg_valid(wp_msg_valid),
.wp_msg(wp_msg)

);

npuarc_rtt_cstm_encapsulation u_rtt_cstm_encapsulation(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.cstm_en(rtt_pr_sel),
.p0_csts_en(p0_csts_en),
.atb_syncreq(p0_atb_syncreq),
.resource_full(rf_msg_valid),
.rfm_rcode(rfm_rcode),
.exception(pr0_filter_exception),
.exception_rtn(pr0_filter_exception_rtn),
.pr0_inst_commit(pr0_inst_commit),
.flush_cmd(1'b0),
.flush_done(flush_done),
.timestamp(pr0_time_stamp),
.cstimestamp(p0_cstimestamp),

.cst_msg_valid(cst_msg_valid),
.cst_msg(cst_msg)
);

npuarc_rtt_dsm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_DSM_WDT),
       .FIFO_SIZE(`npuarc_DSM_BUF_DEPTH)
      )
u_rtt_dsm_sbuf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(ds_sbuf_wr_en),
.rd_en(ds_sbuf_rd_en),
.rd_vld(ds_sbuf_rd_vld),

.wr_ptr(ds_sbuf_wr_ptr),
.rd_ptr(ds_sbuf_rd_ptr),
.full(ds_sbuf_full),
.empty(ds_sbuf_empty),
.num_fill(ds_sbuf_num_fill)
);

npuarc_rtt_pcm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_PCM_WDT),
       .FIFO_SIZE(`npuarc_PCM_BUF_DEPTH)
      )
u_pc_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(pc_sbuf_wr_en),
.rd_en(pc_sbuf_rd_en),
.rd_vld(pc_sbuf_rd_vld),

.wr_ptr(pc_sbuf_wr_ptr),
.rd_ptr(pc_sbuf_rd_ptr),
.full(pc_sbuf_full),
.empty(pc_sbuf_empty),
.num_fill(pc_sbuf_num_fill)
);

npuarc_rtt_ptcm_sbuf
  #(
       .FIFO_DATA_WIDTH(PTCM_WDT_PP),
       .FIFO_SIZE(`npuarc_PTCM_BUF_DEPTH)
      )
u_ptc_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(ptc_sbuf_wr_en),
.rd_en(ptc_sbuf_rd_en),
.rd_vld(ptc_sbuf_rd_vld),

.wr_ptr(ptc_sbuf_wr_ptr),
.rd_ptr(ptc_sbuf_rd_ptr),
.full(ptc_sbuf_full),
.empty(ptc_sbuf_empty),
.num_fill(ptc_sbuf_num_fill)
);


// spyglass disable_block SelfDeterminedExpr-ML
npuarc_rtt_ptm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_PTM_WDT),
       .FIFO_SIZE(`npuarc_PTM_BUF_DEPTH)
      )
u_pt_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(pt_sbuf_wr_en),
.rd_en(pt_sbuf_rd_en),
.rd_vld(pt_sbuf_rd_vld),

//.rd_data(pt_sbuf_rd_data),
.wr_ptr(pt_sbuf_wr_ptr),
.rd_ptr(pt_sbuf_rd_ptr),
.full(pt_sbuf_full),
.empty(pt_sbuf_empty),
.num_fill(pt_sbuf_num_fill)
);

// spyglass enable_block SelfDeterminedExpr-ML



npuarc_rtt_vdspm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_VDSPSW_WDT),
       .FIFO_SIZE(`npuarc_VDSPM_BUF_DEPTH)
      )
u_vdspm_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(vdspm_sbuf_wr_en),
.rd_en(vdspm_sbuf_rd_en),
.rd_vld(vdspm_sbuf_rd_vld),

//.rd_data(otm_sbuf_rd_data),
.wr_ptr(vdspm_sbuf_wr_ptr),
.rd_ptr(vdspm_sbuf_rd_ptr),
.full(vdspm_sbuf_full),
.empty(vdspm_sbuf_empty),
.num_fill(vdspm_sbuf_num_fill)
);

npuarc_rtt_errm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_ERRM_WDT),
       .FIFO_SIZE(`npuarc_ERRM_BUF_DEPTH)
      )
u_errm_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(errm_sbuf_wr_en),
.rd_en(errm_sbuf_rd_en),
.rd_vld(errm_sbuf_rd_vld),

//.rd_data(errm_sbuf_rd_data),
.rd_ptr(errm_sbuf_rd_ptr),
.wr_ptr(errm_sbuf_wr_ptr),
.full(errm_sbuf_full),
.empty(errm_sbuf_empty),
.num_fill(errm_sbuf_num_fill)
);

npuarc_rtt_otm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_OTM_WDT),
       .FIFO_SIZE(`npuarc_OTM_BUF_DEPTH)
      )
u_otm_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(otm_sbuf_wr_en),
.rd_en(otm_sbuf_rd_en),
.rd_vld(otm_sbuf_rd_vld),

//.rd_data(otm_sbuf_rd_data),
.wr_ptr(otm_sbuf_wr_ptr),
.rd_ptr(otm_sbuf_rd_ptr),
.full(otm_sbuf_full),
.empty(otm_sbuf_empty),
.num_fill(otm_sbuf_num_fill)
);

npuarc_rtt_rfm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_RFM_WDT),
       .FIFO_SIZE(`npuarc_RFM_BUF_DEPTH)
      )
u_rfm_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(rfm_sbuf_wr_en),
.rd_en(rfm_sbuf_rd_en),
.rd_vld(rfm_sbuf_rd_vld),

//.rd_data(rfm_sbuf_rd_data),
.rd_ptr(rfm_sbuf_rd_ptr),
.wr_ptr(rfm_sbuf_wr_ptr),
.full(rfm_sbuf_full),
.empty(rfm_sbuf_empty),
.num_fill(rfm_sbuf_num_fill)
);

npuarc_rtt_wpm_sbuf
  #(
       .FIFO_DATA_WIDTH(`npuarc_WPM_WDT),
       .FIFO_SIZE(`npuarc_WPM_BUF_DEPTH)
      )
u_wpm_source_buf
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(wpm_sbuf_wr_en),
.rd_en(wpm_sbuf_rd_en),
.rd_vld(wpm_sbuf_rd_vld),

.wr_ptr(wpm_sbuf_wr_ptr),
.rd_ptr(wpm_sbuf_rd_ptr),
.full(wpm_sbuf_full),
.empty(wpm_sbuf_empty),
.num_fill(wpm_sbuf_num_fill)
);

assign cstm_sbuf_full = ~cstm_sbuf_empty;
npuarc_rtt_cstm_sbuf #(
               .FIFO_DATA_WIDTH(`npuarc_CSTM_WDT),
               .FIFO_SIZE(`npuarc_CSTM_BUF_DEPTH)
               ) u_cstm_source_buf (
.rtt_clk(rtt_clk),
.rst_a(rst_a),
.wr_en(cstm_sbuf_wr_en),
.rd_en(cstm_sbuf_rd_en),
.rd_vld(cstm_sbuf_rd_vld),
.wr_data(cstm_sbuf_wr_data),

.rd_data(cstm_sbuf_rd_data),
.empty(cstm_sbuf_empty)
);

//leda BTTF_D002 off
//leda B_3200 off
//leda B_3208 off

assign data_in0 = {{(180-(`npuarc_OTM_WDT)){1'b0}},otm_sbuf_rd_data[`npuarc_OTM_WDT-1:0]};
assign data_in9 = {{(180-(`npuarc_VDSPSW_WDT)){1'b0}},vdspm_sbuf_rd_data[`npuarc_VDSPSW_WDT-1:0]};
assign data_in1 = {{(180-(`npuarc_RFM_WDT)){1'b0}},rfm_sbuf_rd_data[`npuarc_RFM_WDT-1:0]};
assign data_in2 = {{(180-(`npuarc_ERRM_WDT)){1'b0}},errm_sbuf_rd_data[`npuarc_ERRM_WDT-1:0]};
assign data_in3 = {{(180-(`npuarc_WPM_WDT)){1'b0}},wpm_sbuf_rd_data[`npuarc_WPM_WDT-1:0]};
assign data_in4 = {{(180-(`npuarc_PCM_WDT)){1'b0}},pc_sbuf_rd_data[`npuarc_PCM_WDT-1:0]};

assign data_in5 = 180'b0;
assign data_in6 = 180'b0;
assign data_in10 = {{(180-(`npuarc_PTM_WDT)){1'b0}},pt_sbuf_rd_data[`npuarc_PTM_WDT-1:0]};
generate if ((PTCM_WDT_PP) != 180) begin: pad_it
assign data_in11 = {{(180-(PTCM_WDT_PP)){1'b0}},ptc_sbuf_rd_data[PTCM_WDT_PP-1:0]};
end
else begin: no_pad
assign data_in11 = {ptc_sbuf_rd_data[PTCM_WDT_PP-1:0]};
end
endgenerate
assign data_in12 = {{(180-(`npuarc_DSM_WDT)){1'b0}},ds_sbuf_rd_data[`npuarc_DSM_WDT-1:0]};
assign data_in13 = {{(180-(`npuarc_CSTM_WDT)){1'b0}},cstm_sbuf_rd_data[`npuarc_CSTM_WDT -1:0]};

assign otm_sbuf_rd_en = atb_sbuf_rden[0];
assign rfm_sbuf_rd_en = atb_sbuf_rden[1];
assign errm_sbuf_rd_en = atb_sbuf_rden[2];
assign wpm_sbuf_rd_en = atb_sbuf_rden[3];
assign pc_sbuf_rd_en = atb_sbuf_rden[4];
assign vdspm_sbuf_rd_en = atb_sbuf_rden[9];
assign pt_sbuf_rd_en = atb_sbuf_rden[10];
assign ptc_sbuf_rd_en = atb_sbuf_rden[11];
assign ds_sbuf_rd_en = atb_sbuf_rden[12];
assign cstm_sbuf_rd_en = atb_sbuf_rden[13];

assign msg_seq_order_q_wr_en = any_sbuf_wr_en && (~msg_seq_order_q_full); 
assign msg_seq_order_q_wdata = {
                                cstm_sbuf_wr_en,
                                ds_sbuf_wr_en,
                                ptc_sbuf_wr_en, pt_sbuf_wr_en,
                                vdspm_sbuf_wr_en,
                                pc_sbuf_wr_en, wpm_sbuf_wr_en, errm_sbuf_wr_en, rfm_sbuf_wr_en
                                , otm_sbuf_wr_en};

npuarc_rtt_msg_seq_queue u_rtt_msg_seq_queue (
         .rtt_clk  (rtt_clk),
         .rst_a    (rst_a),
         .wr_en    (msg_seq_order_q_wr_en),
         .rd_en    (msg_seq_order_q_rd_en),
         .wr_data  (msg_seq_order_q_wdata),
         .rd_data  (msg_seq_order_q_rdata),
         .wr_ptr   (msg_seq_order_q_wr_ptr),
         .rd_ptr   (msg_seq_order_q_rd_ptr),
         .empty    (msg_seq_order_q_empty),
         .full     (msg_seq_order_q_full)
         );

// spyglass disable_block UnloadedOutTerm-ML
// MD: atb_sbuf_rden conditionally used for small/med/full prdcr
npuarc_rtt_atb_source_buf_arbitrator u_rtt_atb_source_buf_arbitrator (
        .rtt_clk(rtt_clk),
        .rst_a(rst_a),

        .rtt_time_stamp_en(rtt_time_stamp_en),
        .flush_done(flush_done),
        .ptcm_done(ptcm_done),
        .sbarb_done(sbarb_done),

        .sbuf_empty0(otm_sbuf_empty),
        .sbuf_empty1(rfm_sbuf_empty),
        .sbuf_empty2(errm_sbuf_empty),
        .sbuf_empty3(wpm_sbuf_empty),
        .sbuf_empty4(pc_sbuf_empty),
        .sbuf_empty5(1'b1),
        .sbuf_empty6(1'b1),
        .sbuf_empty9(vdspm_sbuf_empty),
        .sbuf_empty10(pt_sbuf_empty),
        .sbuf_empty11(ptc_sbuf_empty),
        .sbuf_empty12(ds_sbuf_empty),
        .sbuf_empty13(cstm_sbuf_empty),
        .data_in0(data_in0),
        .data_in1(data_in1),
        .data_in2(data_in2),
        .data_in3(data_in3),
        .data_in4(data_in4),
        .data_in9(data_in9),
        .data_in10(data_in10),
        .data_in11(data_in11),
        .data_in12(data_in12),
        .data_in13(data_in13),

        .msg_seq_order_q_rd_en(msg_seq_order_q_rd_en),
        .msg_seq_order_q_rdata(msg_seq_order_q_rdata),

        .arb_src0(arb_src0),
        .arb_src1(arb_src1),
        .arb_src2(arb_src2),
        .arb_val(arb_val),

        .atb_sbuf_ack(atb_sbuf_ack),
        .atb_sbuf_rden(atb_sbuf_rden)
        );
// spyglass enable_block UnloadedOutTerm-ML

npuarc_rtt_atb_msg_parallelize #(.BUMP_WDT(9)
              ) u_rtt_atb_msg_parallelize (
        .rtt_clk(rtt_clk),
        .rst_a(rst_a),

        .flush_cmd(flush_cmd),
        .flush_done(flush_done),
        .sbarb_done(sbarb_done),
        .para_done(para_done),
        .para_busy(para_busy),

        .sbuf_ack0(atb_sbuf_ack[0]),
        .sbuf_valid0(arb_val[0]),
        .sbuf_rdata0(arb_src0),
        .sbuf_ack1(atb_sbuf_ack[1]),
        .sbuf_valid1(arb_val[1]),
        .sbuf_rdata1(arb_src1),
        .sbuf_ack2(atb_sbuf_ack[2]),
        .sbuf_valid2(arb_val[2]),
        .sbuf_rdata2(arb_src2),

        .atb_fifo_req(p0_req),
        .atb_fifo_wdata(p0_wdata),
        .atb_fifo_ack(p0_ack)
        );



endmodule
