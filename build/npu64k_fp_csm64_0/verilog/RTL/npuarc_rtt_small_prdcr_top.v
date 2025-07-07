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
//   rtt_prdcr_top
//
// ===========================================================================
//
// Description:
//
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt_prdcr_top.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"

module npuarc_rtt_small_prdcr_top #(parameter PTCM_WDT_PP = 120, parameter PCM_WDT_PP = 70, parameter PTM_WDT_PP = 120,
                                 parameter PC_PP = 31, parameter RTT_ADDR_PP=32,
                                 parameter DUAL_ISSUE_PP = 0, parameter RTT_NUM_FILTERS_PP=4,
                                 parameter FILTER_BITLEN_PP = 4,
                                 parameter HAS_VEC_UNIT_PP = 0
                                 )
( rtt_clk, //RTT clock
  rst_a,          //Asynchronous reset
  pr_num,
  rtt_freeze,
  //Aux interface
  rtt_write_a,
//  rtt_drd_r,
 //Core signals for Debug status
  rtt_ss_halt,
  rtt_hw_bp,
  rtt_hw_exc,
  rtt_dbg_halt,
  rtt_rst_applied,
  sys_halt_r,

  //Core signals for PTM
  rtt_uop_is_leave,
  rtt_in_deslot,
  rtt_in_eslot,
  rtt_inst_commit,
  rtt_inst_addr,
  rtt_cond_valid,
  rtt_cond_pass,
  rtt_branch_taken,
  rtt_dslot,
  rtt_branch_indir,
  rtt_branch_taddr,
  rtt_exception,
  rtt_exception_rtn,
  rtt_interrupt,
  rtt_enter_sleep,
  rtt_zd_loop,
//leda NTL_CON13C off
//leda NTL_CON13C on
  rtt_wp_val,
  rtt_sw_bp,
  atb_syncreq,

  cti_rtt_filters,
  cti_trace_start,
  cti_trace_stop,
  cti_ctrl_en,

  para_done,
  bhth,
  atb_cstimestamp,
  pr0_csts_en,
  vdswm_en,

  rtt_process_id,
  rtt_pid_wr_en,
  rtt_vdsp_data,     // VDSP sw trigger data
  rtt_vdsp_val,      // VDSP sw trigger valid this cycle
// Programming IF start
  rtt_pr_sel,
  pr0_src_en,
  pr0_dsm_en,
  pr0_filter_type,
  pr0_addr_filter0_start,
  pr0_addr_filter0_stop,
  pr0_addr_filter1_start,
  pr0_addr_filter1_stop,
  pr0_addr_filter2_start,
  pr0_addr_filter2_stop,
  pr0_addr_filter3_start,
  pr0_addr_filter3_stop,
  pr0_trigger_reg,
  rtt_flush_command,
  rtt_time_stamp_en,
 // onchip_mem_addr_wen,
//  rtt_on_chip_mem_base,
//  rtt_on_chip_sz,
  pr0_wp_enable,
  pr0_wp_status,
  rtt_freeze_cntrl,

//programming if END

// time stamp counter
  time_stamp,
//trasport outputs
 //inputs to transport
prdcr_req,
prdcr_ack,
prdcr_data,




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
  rfm_sbuf_rd_ptr,

flush_done,

//transport output ends
//int_buf_num_fill,
prdcr_busy,
freeze_status


  );

///I/O declarations
//global signals

  input                     rtt_clk;
  input                     rst_a;
  input [`npuarc_PRNUM_WDT-1:0] pr_num;
  input                     rtt_write_a;

 //Core signals for Debug status
  input rtt_ss_halt;
  input rtt_hw_bp;
  input rtt_hw_exc;
  input rtt_dbg_halt;
  input rtt_rst_applied;
  input sys_halt_r;

    //Core signals for PTM
   input                     rtt_uop_is_leave;
   input                     rtt_in_deslot;
   input                     rtt_in_eslot;
   input                     rtt_inst_commit;
   input  [PC_PP-1:0]        rtt_inst_addr;
   input                     rtt_cond_valid;
   input                     rtt_cond_pass;
   input                     rtt_branch_taken;
   input                     rtt_branch_indir;
   input  [PC_PP-1:0]        rtt_branch_taddr;
   input                     rtt_dslot;
   input                     rtt_exception;
   input                     rtt_exception_rtn;
   input                     rtt_interrupt;
   input                     rtt_enter_sleep;
   input                     rtt_zd_loop;
//leda NTL_CON13C off
//leda NTL_CON13C on
   input  [7:0]       rtt_wp_val;
   input                     rtt_sw_bp;
  input                      atb_syncreq;
  output [25:0]              cti_rtt_filters;
  input                      cti_trace_start;
  input                      cti_trace_stop;
  input                      cti_ctrl_en;
  output wire [120-1:0] prdcr_data;
  output wire                para_done;
  input [2:0]                bhth;
  input [`npuarc_CST_WDT-1:0]       atb_cstimestamp;
  input                      pr0_csts_en;
  input                      vdswm_en;

  input  [7:0]            rtt_process_id;
  input                   rtt_pid_wr_en;
  input  [`npuarc_VDSP_AUX_DATA-1:0]  rtt_vdsp_data;     // VDSP sw trigger data
  input                        rtt_vdsp_val;      // VDSP sw trigger valid this cycle

//  output  [`AUX_DATA-1:0]rtt_drd_r ;

 // programming IP inputs
  input                             rtt_pr_sel;
  input   [2-2:0]         pr0_src_en ;
  input                             pr0_dsm_en;
  input   [24-1:0]          pr0_filter_type;
  input   [RTT_ADDR_PP-1:0]           pr0_addr_filter0_start;
  input   [RTT_ADDR_PP-1:0]           pr0_addr_filter0_stop;
  input   [RTT_ADDR_PP-1:0]           pr0_addr_filter1_start;
  input   [RTT_ADDR_PP-1:0]           pr0_addr_filter1_stop;
  input   [RTT_ADDR_PP-1:0]           pr0_addr_filter2_start;
  input   [RTT_ADDR_PP-1:0]           pr0_addr_filter2_stop;
  input   [RTT_ADDR_PP-1:0]           pr0_addr_filter3_start;
  input   [RTT_ADDR_PP-1:0]           pr0_addr_filter3_stop;
  input   [`npuarc_RTT_TRG-1:0]            pr0_trigger_reg;
//  input   [`OCM_BASE_ADDR-1:0]      rtt_on_chip_mem_base;
//  input   [`OCM_SZ-1:0]             rtt_on_chip_sz;
  input   [`npuarc_PR_WP-1:0]              pr0_wp_enable;
  input   [`npuarc_PR_WP-1:0]              pr0_wp_status;
  input                             rtt_flush_command;
  input                             rtt_time_stamp_en;
  input                                rtt_freeze_cntrl;
  input                                flush_done;


  input  [`npuarc_RTT_TIME_STMP-1:0]    time_stamp;

 //inputs to transport
output prdcr_req;
input prdcr_ack;
/////

//`if (`HAS_ON_CHIP_MEM)    // {     OFFLOAD_IF_PORTD_S

//output wr_accept;
//output wr_done;
//output err_wr;
//`endif             // }     OFFLOAD_IF_PORTD_S



//output onchip_mem_addr_wen;
//output [`OCM_BASE_ADDR-1:0]onchip_mem_addr;
//output [`OCM_SZ-1:0]onchip_mem_size;
//output [`PR_EVTI-1:0] pr0_eic_reg;

//transport ends here
output                        prdcr_busy;
output  [`npuarc_FR_STATUS-1:0]      freeze_status;

//output freeze;
output rtt_freeze;



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


  //nets declarations
  wire                             rtt_clk;
  wire                             rst_a;
  wire                             rtt_write_a;
//  wire  [`OCM_BASE_ADDR-1:0]       wr_ptr;
//  wire                             ocm_wr_ptr_en;
  wire  [`npuarc_PR_WP-1:0]               rtt_wp_val;
//  wire  [`AUX_DATA-1:0]          rtt_drd_r;  // Register read data
  wire                                rtt_pr_sel;
  wire  [2-2:0]          pr0_src_en;
  wire  [2-2:0]          pr0_src_en_ac;
  wire   [24-1:0]          pr0_filter_type;
  wire   [RTT_ADDR_PP-1:0]           pr0_addr_filter0_start;
  wire   [RTT_ADDR_PP-1:0]           pr0_addr_filter0_stop;
  wire   [RTT_ADDR_PP-1:0]           pr0_addr_filter1_start;
  wire   [RTT_ADDR_PP-1:0]           pr0_addr_filter1_stop;
  wire   [RTT_ADDR_PP-1:0]           pr0_addr_filter2_start;
  wire   [RTT_ADDR_PP-1:0]           pr0_addr_filter2_stop;
  wire   [RTT_ADDR_PP-1:0]           pr0_addr_filter3_start;
  wire   [RTT_ADDR_PP-1:0]           pr0_addr_filter3_stop;
  wire  [`npuarc_RTT_TRG-1:0]             pr0_trigger_reg;
  wire   [`npuarc_PR_WP-1:0]      pr0_wp_status;
  wire   [`npuarc_PR_WP-1:0]      pr0_wp_enable;

  wire                     cti_trace_en_dslot;

  //producer0 side band signals
   wire            rtt_inst_commit;
   wire  [PC_PP-1:0] rtt_inst_addr;
   wire            rtt_cond_valid;
   wire            rtt_cond_pass;
   wire            rtt_branch_taken;
   wire            rtt_branch_indir;
   wire  [PC_PP-1:0] rtt_branch_taddr;
   wire            rtt_exception;
   wire            rtt_exception_rtn;
   wire            rtt_interrupt;
   wire            rtt_enter_sleep;
   wire            rtt_zd_loop;
   wire  [7:0]     pr0_otm_process_id;
   wire            pr0_otm_ptd_wr_en;
   wire  [`npuarc_VDSP_AUX_DATA-1:0] pr0_rtt_vdsp_data;     // VDSP sw trigger data
   wire                       pr0_rtt_vdsp_val;      // VDSP sw trigger valid this cycle

  //producer interface filters outputs
  wire    [PC_PP-1:0]            pr0_filter_pc;  //Filtered PC output
  wire                           pr0_inst_commit;  //Pc valid
  wire                           pr0_filter_cond_valid   ;
  wire                           pr0_filter_cond_pass  ;
  wire                           pr0_filter_branch_indir;
  wire      [PC_PP-1:0]          pr0_filter_branch_taddr ;
  wire                           pr0_filter_exception    ;
  wire                           pr0_filter_exception_rtn;
  wire                           pr0_filter_interrupt    ;
  wire                           pr0_filter_zd_loop      ;
  wire                           pr0_filter_branch       ;
  wire                           pr0_filter_rtt_dslot  ;
   wire    [`npuarc_PR_WP-1:0]          pr0_watchpoint_val;
   wire  [`npuarc_RTT_TIME_STMP-1:0]    time_stamp;
   wire                           ptm_dropped;
   wire  [PC_PP-1:0]              pr0_cmpr_ptm_taddr;
   wire  [PC_PP-1:0]              unfiltered_relative_pc;
//transport module nets
   wire                           prdcr_req;
   wire                           prdcr_ack;

//   wire    [`OCM_BASE_ADDR-1:0]     onchip_mem_addr;
//   wire    [`OCM_SZ-1:0]     onchip_mem_size;
//   wire                           flush_cmd;
   wire                           rtt_flush_command;
//   wire     [`OCM_WR_PTR-1:0]   wr_ptr;
//   wire     [`OCM_BASE_ADDR-1:0] rtt_on_chip_mem_base;
//   wire     [`OCM_SZ-1:0]      rtt_on_chip_sz;
//   wire                        onchip_mem_addr_wen;
   wire                        flush_done;
   wire                        rtt_time_stamp_en;
   wire                        pr0_filter_under_run;
   wire                        pr0_cmpr_under_run;
   wire  [`npuarc_FR_STATUS-1:0]      freeze_status;
   wire                        rtt_freeze_cntrl;
   wire [`npuarc_PCM_BUF_DEPTH:0]  pc_sbuf_num_fill;
   wire [`npuarc_PTCM_BUF_DEPTH:0]  ptc_sbuf_num_fill;
   wire [`npuarc_PTM_BUF_DEPTH:0]  pt_sbuf_num_fill;
   wire [`npuarc_VDSPM_BUF_DEPTH:0] vdspm_sbuf_num_fill;
   wire                      vdspm_sbuf_freeze;
   wire [`npuarc_ERRM_BUF_DEPTH:0]  errm_sbuf_num_fill;
   wire [`npuarc_OTM_BUF_DEPTH:0]  otm_sbuf_num_fill;
   wire [`npuarc_RFM_BUF_DEPTH:0]  rfm_sbuf_num_fill;
   wire [`npuarc_WPM_BUF_DEPTH:0]  wpm_sbuf_num_fill;
   wire [`npuarc_DSM_BUF_DEPTH:0]  ds_sbuf_num_fill;
   wire encapsulation_top_busy;

   assign prdcr_busy = pr0_cmpr_under_run || pr0_filter_under_run || encapsulation_top_busy ||
                       rtt_write_a;
   assign pr0_src_en_ac =  ((rtt_pr_sel ? {(2-1){1'b1}} : {(2-1){1'b0}}) & pr0_src_en);

  //producer interface and filters module instantiation
  npuarc_small_producer_if_filters #(.PTCM_WDT_PP(PTCM_WDT_PP), .PC_PP(PC_PP), .RTT_ADDR_PP(RTT_ADDR_PP),
                                  .DUAL_ISSUE_PP(DUAL_ISSUE_PP), .RTT_NUM_FILTERS_PP(RTT_NUM_FILTERS_PP), .FILTER_BITLEN_PP(FILTER_BITLEN_PP)
  ) u_producer_if_filters( .rtt_clk (rtt_clk ),
    .rst_a (rst_a),
    .rtt_pr_sel (rtt_pr_sel),
    .pr0_src_en (pr0_src_en ),
    .pr0_rtt_inst_commit (rtt_inst_commit ),
    .pr0_pc (rtt_inst_addr  ),
    .pr0_rtt_cond_valid (rtt_cond_valid ),
    .pr0_rtt_cond_pass (rtt_cond_pass ),
    .pr0_rtt_dslot (rtt_dslot),
    .pr0_rtt_branch (rtt_branch_taken ),
    .pr0_rtt_branch_indir (rtt_branch_indir ),
    .pr0_rtt_branch_taddr (rtt_branch_taddr ),
    .pr0_rtt_exception (rtt_exception ),
    .pr0_rtt_exception_rtn (rtt_exception_rtn ),
    .pr0_rtt_interrupt (rtt_interrupt ),
    .pr0_rtt_zd_loop (rtt_zd_loop ),
    .pr0_process_id(rtt_process_id),
    .pr0_pid_wr_en (rtt_pid_wr_en),
    .rtt_vdsp_data(rtt_vdsp_data),     // VDSP sw trigger data
    .rtt_vdsp_val(rtt_vdsp_val),      // VDSP sw trigger valid this cycle

    .pr0_filter_type (pr0_filter_type ),
    .pr0_addr_filter0_start ( pr0_addr_filter0_start),
    .pr0_addr_filter0_stop  ( pr0_addr_filter0_stop),
    .pr0_addr_filter1_start ( pr0_addr_filter1_start),
    .pr0_addr_filter1_stop  ( pr0_addr_filter1_stop),
    .pr0_addr_filter2_start ( pr0_addr_filter2_start),
    .pr0_addr_filter2_stop  ( pr0_addr_filter2_stop),
    .pr0_addr_filter3_start ( pr0_addr_filter3_start),
    .pr0_addr_filter3_stop  ( pr0_addr_filter3_stop),
    .pr0_trigger_reg (pr0_trigger_reg),
    .pr0_wp_enable (pr0_wp_enable ),
    .pr0_wp_status (pr0_wp_status ),
    .pr0_filter_pc (  pr0_filter_pc ),
    .pr0_inst_commit  (pr0_inst_commit   ),
    .pr0_filter_cond_valid (pr0_filter_cond_valid ),
    .pr0_filter_cond_pass (pr0_filter_cond_pass ),
    .pr0_filter_branch_indir  (pr0_filter_branch_indir ),
    .pr0_filter_branch_taddr  (pr0_filter_branch_taddr ),
    .pr0_filter_exception (pr0_filter_exception ),
    .pr0_filter_exception_rtn (pr0_filter_exception_rtn ),
    .pr0_filter_interrupt (pr0_filter_interrupt ),
    .pr0_filter_zd_loop (pr0_filter_zd_loop ),
    .pr0_filter_branch (pr0_filter_branch ),
    .pr0_filter_rtt_dslot (pr0_filter_rtt_dslot),
    .pr0_otm_process_id (pr0_otm_process_id),
    .pr0_otm_ptd_wr_en (pr0_otm_ptd_wr_en),
    .pr0_rtt_vdsp_data(pr0_rtt_vdsp_data),     // VDSP sw trigger data
    .pr0_rtt_vdsp_val(pr0_rtt_vdsp_val),       // VDSP sw trigger valid this cycle
    .cti_rtt_filters(cti_rtt_filters),
    .cti_trace_start(cti_trace_start),
    .cti_trace_stop(cti_trace_stop),
    .cti_ctrl_en(cti_ctrl_en),
    .cti_trace_en_dslot(cti_trace_en_dslot),

    .pr0_filter_under_run (pr0_filter_under_run),
    .pr0_watchpoint_val  (pr0_watchpoint_val )
);
  wire         pt_sync_msg;
  wire         pt_msg_valid_cmpr;
  wire         pc_msg_valid_cmpr;

//compressor module instantiation
npuarc_small_compressor u_compressor(
  .rtt_clk (rtt_clk),
  .rst_a (rst_a),
  .rtt_inst_addr(rtt_inst_addr),
  .pr0_filter_pc (pr0_filter_pc),

  .pr0_filter_branch_taddr (pr0_filter_branch_taddr),
  .ptm_dropped (ptm_dropped),
  .pt_sync_msg(pt_sync_msg),
  .pt_msg_valid(pt_msg_valid_cmpr),
  .pc_msg_valid(pc_msg_valid_cmpr),
  .pr0_cmpr_under_run (pr0_cmpr_under_run),
  .pr0_cmpr_ptm_taddr (pr0_cmpr_ptm_taddr),
  .unfiltered_relative_pc(unfiltered_relative_pc)
);

//transport module instantiation


npuarc_rtt_small_encapsulation_top #(.PTCM_WDT_PP(PTCM_WDT_PP), .PCM_WDT_PP(PCM_WDT_PP), .PTM_WDT_PP(PTM_WDT_PP), .PC_PP(PC_PP), .RTT_ADDR_PP(RTT_ADDR_PP)) u_rtt_encapsulation_top(
  .rtt_clk (rtt_clk),
  .rst_a (rst_a),

  .pr_num(pr_num),
  .rtt_ss_halt(rtt_ss_halt),
  .rtt_sw_bp(rtt_sw_bp),
  .rtt_hw_bp(rtt_hw_bp),
  .rtt_hwe(rtt_hw_exc),
  .rtt_enter_sleep(rtt_enter_sleep),
  .rtt_dbg_halt(rtt_dbg_halt),
  .core_rst(rtt_rst_applied),
  .sys_halt_r(sys_halt_r),

    .cti_trace_en_dslot(cti_trace_en_dslot),

  .rtt_dslot(pr0_filter_rtt_dslot),
  .pr0_pc (rtt_inst_addr  ),
  .rtt_inst_commit(rtt_inst_commit),
  .rtt_uop_is_leave(rtt_uop_is_leave),
  .rtt_in_deslot(rtt_in_deslot),
  .rtt_in_eslot(rtt_in_eslot),
  .unfilter_exception     (rtt_exception),
  .unfilter_interrupt     (rtt_interrupt),
  .unfilter_zd_loop       (rtt_zd_loop),
  .rtt_branch_taddr(rtt_branch_taddr),
  .rtt_pr_sel (rtt_pr_sel),
  .pr0_src_en  (pr0_src_en_ac),
  .pr0_dsm_en  (pr0_dsm_en),
  .pr0_filter_pc (pr0_filter_pc),  //Filtered PC input
  .pr0_inst_commit (pr0_inst_commit),  //Pc valid
  .pr0_filter_cond_valid    (pr0_filter_cond_valid),
  .pr0_filter_cond_pass     (pr0_filter_cond_pass),
  .pr0_filter_branch_indir  (pr0_filter_branch_indir),
  .pr0_filter_exception     (pr0_filter_exception),
  .pr0_filter_exception_rtn (pr0_filter_exception_rtn),
  .pr0_filter_interrupt     (pr0_filter_interrupt),
  .pr0_filter_zd_loop       (pr0_filter_zd_loop),
  .pr0_filter_branch        (pr0_filter_branch),
  .pr0_time_stamp (time_stamp),
  .rtt_wp_val (rtt_wp_val),
  .pr0_watchpoint_val (pr0_watchpoint_val),
 // .pr0_wp_hit (pr0_wp_hit),
  .pr0_cmpr_ptm_taddr (pr0_cmpr_ptm_taddr),
  .unfiltered_relative_pc(unfiltered_relative_pc),
  .pr0_rtt_process_id(pr0_otm_process_id),
  .pr0_rtt_pid_wr_en(pr0_otm_ptd_wr_en),
  .pr0_rtt_vdsp_data(pr0_rtt_vdsp_data),     // VDSP sw trigger data
  .pr0_rtt_vdsp_val(pr0_rtt_vdsp_val),       // VDSP sw trigger valid this cycle
  .rtt_time_stamp_en (rtt_time_stamp_en),
  .flush_cmd(rtt_flush_command),
  .flush_done(flush_done),
  .filter_busy(pr0_filter_under_run),
  .compressor_busy(pr0_cmpr_under_run),
  .ptm_dropped (ptm_dropped),
  .pt_sync_msg (pt_sync_msg),
  .pt_msg_valid_cmpr (pt_msg_valid_cmpr),
  .pc_msg_valid_cmpr (pc_msg_valid_cmpr),

  .p0_req(prdcr_req),
  .p0_ack(prdcr_ack),
  .p0_wdata (prdcr_data),
  .p0_atb_syncreq(atb_syncreq),
  .para_done(para_done),
  .bhth(bhth),
  .p0_cstimestamp(atb_cstimestamp),
  .p0_csts_en(pr0_csts_en),

  .freeze_status (freeze_status),
  .pc_sbuf_num_fill(pc_sbuf_num_fill),
  .ptc_sbuf_num_fill(ptc_sbuf_num_fill),
  .pt_sbuf_num_fill(pt_sbuf_num_fill),
  .vdswm_en(vdswm_en),
  .vdspm_sbuf_num_fill(vdspm_sbuf_num_fill),
  .vdspm_sbuf_freeze(vdspm_sbuf_freeze),
  .errm_sbuf_num_fill(errm_sbuf_num_fill),
  .otm_sbuf_num_fill(otm_sbuf_num_fill),
  .rfm_sbuf_num_fill(rfm_sbuf_num_fill),
  .wpm_sbuf_num_fill(wpm_sbuf_num_fill),
  .ds_sbuf_num_fill(ds_sbuf_num_fill),
  .encapsulation_top_busy (encapsulation_top_busy),


.ds_sbuf_wr_en(ds_sbuf_wr_en),
.ds_sbuf_rd_en(ds_sbuf_rd_en),
.ds_sbuf_wr_data(ds_sbuf_wr_data),
.ds_sbuf_rd_data(ds_sbuf_rd_data),
.ds_sbuf_wr_ptr(ds_sbuf_wr_ptr),
.ds_sbuf_rd_ptr(ds_sbuf_rd_ptr),



.vdspm_sbuf_wr_en(vdspm_sbuf_wr_en),
.vdspm_sbuf_rd_en(vdspm_sbuf_rd_en),
.vdspm_sbuf_wr_data(vdspm_sbuf_wr_data),
.vdspm_sbuf_rd_data(vdspm_sbuf_rd_data),
.vdspm_sbuf_wr_ptr(vdspm_sbuf_wr_ptr),
.vdspm_sbuf_rd_ptr(vdspm_sbuf_rd_ptr),

.errm_sbuf_wr_en(errm_sbuf_wr_en),
.errm_sbuf_rd_en(errm_sbuf_rd_en),
.errm_sbuf_wr_data(errm_sbuf_wr_data),
.errm_sbuf_rd_data(errm_sbuf_rd_data),
.errm_sbuf_wr_ptr(errm_sbuf_wr_ptr),
.errm_sbuf_rd_ptr(errm_sbuf_rd_ptr),

.otm_sbuf_wr_en(otm_sbuf_wr_en),
.otm_sbuf_rd_en(otm_sbuf_rd_en),
.otm_sbuf_wr_data(otm_sbuf_wr_data),
.otm_sbuf_rd_data(otm_sbuf_rd_data),
.otm_sbuf_wr_ptr(otm_sbuf_wr_ptr),
.otm_sbuf_rd_ptr(otm_sbuf_rd_ptr),


.pc_sbuf_wr_en(pc_sbuf_wr_en),
.pc_sbuf_rd_en(pc_sbuf_rd_en),
.pc_sbuf_wr_data(pc_sbuf_wr_data),
.pc_sbuf_rd_data(pc_sbuf_rd_data),
.pc_sbuf_wr_ptr(pc_sbuf_wr_ptr),
.pc_sbuf_rd_ptr(pc_sbuf_rd_ptr),

.ptc_sbuf_wr_en(ptc_sbuf_wr_en),
.ptc_sbuf_rd_en(ptc_sbuf_rd_en),
.ptc_sbuf_wr_data(ptc_sbuf_wr_data),
.ptc_sbuf_rd_data(ptc_sbuf_rd_data),
.ptc_sbuf_wr_ptr(ptc_sbuf_wr_ptr),
.ptc_sbuf_rd_ptr(ptc_sbuf_rd_ptr),



.pt_sbuf_wr_en(pt_sbuf_wr_en),
.pt_sbuf_rd_en(pt_sbuf_rd_en),
.pt_sbuf_wr_data(pt_sbuf_wr_data),
.pt_sbuf_rd_data(pt_sbuf_rd_data),
.pt_sbuf_wr_ptr(pt_sbuf_wr_ptr),
.pt_sbuf_rd_ptr(pt_sbuf_rd_ptr),



.wpm_sbuf_wr_en(wpm_sbuf_wr_en),
.wpm_sbuf_rd_en(wpm_sbuf_rd_en),
.wpm_sbuf_wr_data(wpm_sbuf_wr_data),
.wpm_sbuf_rd_data(wpm_sbuf_rd_data),
.wpm_sbuf_wr_ptr(wpm_sbuf_wr_ptr),
.wpm_sbuf_rd_ptr(wpm_sbuf_rd_ptr),


.rfm_sbuf_wr_en(rfm_sbuf_wr_en),
.rfm_sbuf_rd_en(rfm_sbuf_rd_en),
.rfm_sbuf_wr_data(rfm_sbuf_wr_data),
.rfm_sbuf_rd_data(rfm_sbuf_rd_data),
.rfm_sbuf_wr_ptr(rfm_sbuf_wr_ptr),
.rfm_sbuf_rd_ptr(rfm_sbuf_rd_ptr)



);

npuarc_rtt_small_freeze_ctrl u_rtt_freeze_ctrl
(
.rtt_clk(rtt_clk),
.rst_a(rst_a),

.freeze_ctrl(rtt_freeze_cntrl),

.pc_sbuf_num_fill(pc_sbuf_num_fill),
.ptc_sbuf_num_fill(ptc_sbuf_num_fill),
.pt_sbuf_num_fill(pt_sbuf_num_fill),
.vdspm_sbuf_num_fill(vdspm_sbuf_num_fill),
.vdspm_sbuf_freeze(vdspm_sbuf_freeze),
.errm_sbuf_num_fill(errm_sbuf_num_fill),
.otm_sbuf_num_fill(otm_sbuf_num_fill),
.rfm_sbuf_num_fill(rfm_sbuf_num_fill),
.wpm_sbuf_num_fill(wpm_sbuf_num_fill),
.ds_sbuf_num_fill(ds_sbuf_num_fill),

.flush_done(flush_done),

.freeze_status(freeze_status),
.freeze(rtt_freeze)

);

endmodule
