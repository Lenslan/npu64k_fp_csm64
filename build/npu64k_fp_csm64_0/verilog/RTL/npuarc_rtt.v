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
//   rtt
//
// ===========================================================================
//
// Description:
//  This is the Real Time Trace top file.
//  All the modules instatiated in this file
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o rtt.vpp
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
// leda VER_1_6_4_1 off
// LMD: Do not include glue logic at top level
// LJ: RTT is not the top level. It is provisionally being run as top level

`include "npuarc_rtt_pkg_defines.v"



module npuarc_rtt (

    //I/O declarations
     input               rtt_clk,

    // CoreSight interface per core
   input              atclken,
   input              atresetn,

   input  [63:0]      atb_cstimestamp,

   output             rtt_prod_sel,

   //Core signals for Debug status
   input              rtt_write_a,
   input              rtt_read_a,
   input  [`npuarc_RTT_ADDR_RANGE] rtt_addr_r,
   input  [`npuarc_RTT_DATA-1:0]    rtt_dwr_r,
   output      [`npuarc_AUX_DATA-1:0]   rtt_drd_r ,
   output                    rtt_freeze,
   input                     rtt_ss_halt,
   input                     rtt_hw_bp,
   input                     rtt_hw_exc,
   input                     rtt_dbg_halt,
   input                     rtt_rst_applied,
   //Core signals for PTM
   input                     rtt_uop_is_leave,
   input                     rtt_in_deslot,
   input                     rtt_in_eslot,
   input                     rtt_inst_commit,
   input  [`npuarc_PC_RANGE]        rtt_inst_addr,
   input                     rtt_cond_valid,
   input                     rtt_cond_pass,
   input                     rtt_branch,
   input                     rtt_branch_indir,
   input  [`npuarc_PC_RANGE]        rtt_branch_taddr,
   input                     rtt_dslot,
   input                     rtt_exception,
   input                     rtt_exception_rtn,
   input                     rtt_interrupt,
   input                     rtt_sleep_mode,
   input                     rtt_zd_loop,
   input  [7:0]              rtt_wp_val,
   input                     rtt_wp_hit,
   input                     rtt_sw_bp,
   input                     sys_halt_r,


   input  [7:0]              rtt_process_id,
   input                     rtt_pid_wr_en,
   input  [`npuarc_VDSP_AUX_DATA-1:0]  rtt_swe_data,     // sw trigger data
   input                        rtt_swe_val,      // sw trigger valid this cycle


   // CoreSight interface per core
   input                       atready,
   output [`npuarc_ATDATA_WIDTH-1:0]  atdata,
   output [`npuarc_ATBYTE_WIDTH-1:0]  atbytes,
   output [6:0]                atid,
   output                      atvalid,

   input                       afvalid,
   output                      afready,
   input                       syncreq,

   // CTI signalling
   output [25:0]               cti_rtt_filters,
   input                       cti_trace_start,
   input                       cti_trace_stop,

   output  [7:0]               rtt_src_num,

    input                    pclkdbg_en,
    input                    presetdbgn,
    input [31:2]             arct0_paddrdbg,
    input                    arct0_pseldbg,
    input                    arct0_penabledbg,
    input                    arct0_pwritedbg,
    input [31:0]             arct0_pwdatadbg,

    output                   arct0_preadydbg,
    output [31:0]            arct0_prdatadbg,
    output                   arct0_pslverrdbg,

    input                    arct0_dbgen,
    input                    arct0_niden,


    // CoreSight interface per core
    input                           swe_atready,
    output [`npuarc_SWE_ATDATA_WIDTH-1:0]  swe_atdata,
    output [`npuarc_SWE_ATBYTE_WIDTH-1:0]  swe_atbytes,
    output [6:0]                    swe_atid,
    output                          swe_atvalid,

    input                           swe_afvalid,
    output                          swe_afready,
    input                           swe_syncreq,

  input  wire [32:0]             sl0_alt_rtt_swe_data,
  input  wire                    sl0_alt_rtt_swe_val,
  input  wire [7:0]              sl0_alt_rtt_swe_ext,
  output                         sl0_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl1_alt_rtt_swe_data,
  input  wire                    sl1_alt_rtt_swe_val,
  input  wire [7:0]              sl1_alt_rtt_swe_ext,
  output                         sl1_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl2_alt_rtt_swe_data,
  input  wire                    sl2_alt_rtt_swe_val,
  input  wire [7:0]              sl2_alt_rtt_swe_ext,
  output                         sl2_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl3_alt_rtt_swe_data,
  input  wire                    sl3_alt_rtt_swe_val,
  input  wire [7:0]              sl3_alt_rtt_swe_ext,
  output                         sl3_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl4_alt_rtt_swe_data,
  input  wire                    sl4_alt_rtt_swe_val,
  input  wire [7:0]              sl4_alt_rtt_swe_ext,
  output                         sl4_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl5_alt_rtt_swe_data,
  input  wire                    sl5_alt_rtt_swe_val,
  input  wire [7:0]              sl5_alt_rtt_swe_ext,
  output                         sl5_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl6_alt_rtt_swe_data,
  input  wire                    sl6_alt_rtt_swe_val,
  input  wire [7:0]              sl6_alt_rtt_swe_ext,
  output                         sl6_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl7_alt_rtt_swe_data,
  input  wire                    sl7_alt_rtt_swe_val,
  input  wire [7:0]              sl7_alt_rtt_swe_ext,
  output                         sl7_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl8_alt_rtt_swe_data,
  input  wire                    sl8_alt_rtt_swe_val,
  input  wire [7:0]              sl8_alt_rtt_swe_ext,
  output                         sl8_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl9_alt_rtt_swe_data,
  input  wire                    sl9_alt_rtt_swe_val,
  input  wire [7:0]              sl9_alt_rtt_swe_ext,
  output                         sl9_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl10_alt_rtt_swe_data,
  input  wire                    sl10_alt_rtt_swe_val,
  input  wire [7:0]              sl10_alt_rtt_swe_ext,
  output                         sl10_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl11_alt_rtt_swe_data,
  input  wire                    sl11_alt_rtt_swe_val,
  input  wire [7:0]              sl11_alt_rtt_swe_ext,
  output                         sl11_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl12_alt_rtt_swe_data,
  input  wire                    sl12_alt_rtt_swe_val,
  input  wire [7:0]              sl12_alt_rtt_swe_ext,
  output                         sl12_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl13_alt_rtt_swe_data,
  input  wire                    sl13_alt_rtt_swe_val,
  input  wire [7:0]              sl13_alt_rtt_swe_ext,
  output                         sl13_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl14_alt_rtt_swe_data,
  input  wire                    sl14_alt_rtt_swe_val,
  input  wire [7:0]              sl14_alt_rtt_swe_ext,
  output                         sl14_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl15_alt_rtt_swe_data,
  input  wire                    sl15_alt_rtt_swe_val,
  input  wire [7:0]              sl15_alt_rtt_swe_ext,
  output                         sl15_alt_rtt_swe_prdcr_en,

  input  wire [32:0]             sl16_alt_rtt_swe_data,
  input  wire                    sl16_alt_rtt_swe_val,
  input  wire [7:0]              sl16_alt_rtt_swe_ext,
  output                         sl16_alt_rtt_swe_prdcr_en,










    input                     test_mode,
    input                     rst_a

    );

localparam FILTER_BITLEN_PP = 4;

wire rst;

wire                    pif_arct0_rtt_write_a;
wire                    pif_arct0_rtt_read_a;
wire   [`npuarc_RTT_ADDR-1:0]  pif_arct0_rtt_addr_r;
wire   [`npuarc_AUX_DATA-1:0]  pif_arct0_rtt_dwr_r;
wire   [`npuarc_AUX_DATA-1:0]  pif_arct0_rtt_drd_r;
wire                              arct_apb2aux_write;
wire                              arct_apb2aux_read;
wire   [`npuarc_RTT_ADDR-1:0]            arct_apb2aux_address;
wire   [`npuarc_AUX_DATA-1:0]            arct_apb2aux_wdata;
wire   [`npuarc_AUX_DATA-1:0]            arct_apb2aux_rdata;



wire                 cu_clk;
wire [`npuarc_AUX_DATA-1:0] rtt_datar_cfg; 

wire atb_rst;

    //Core signals for Debug status
    reg                     rtt_ss_halt_r;
    reg                     rtt_hw_bp_r;
    reg                     rtt_hw_exc_r;
    reg                     rtt_dbg_halt_r;
    reg                     rtt_rst_applied_r;
    reg                     sys_halt_rr;
    //Core signals for PTM
    reg                     rtt_uop_is_leave_r;
    reg                     rtt_in_deslot_r;
    reg                     rtt_in_eslot_r;
    reg                     rtt_inst_commit_r;
    reg  [`npuarc_PC_RANGE]        rtt_inst_addr_r;
    reg                     rtt_cond_valid_r;
    reg                     rtt_cond_pass_r;
    reg                     rtt_branch_r;
    reg                     rtt_branch_indir_r;
    reg  [`npuarc_PC_RANGE]        rtt_branch_taddr_r;
    reg                     rtt_dslot_r;
    reg                     rtt_exception_r;
    reg                     rtt_exception_rtn_r;
    reg                     rtt_interrupt_r;
    reg                     rtt_sleep_mode_r;
    reg                     rtt_zd_loop_r;
    reg  [7:0]              rtt_wp_val_r;
    reg                     rtt_wp_hit_r;
    reg                     rtt_sw_bp_r;
    wire [25:0]              cti_rtt_filters_pre;
    wire                     cti_trace_start_s;
    wire                     cti_trace_stop_s;


    reg  [7:0]            rtt_process_id_r;
    reg                   rtt_pid_wr_en_r;
    reg  [`npuarc_VDSP_AUX_DATA-1:0]  rtt_vdsp_data_r;
    reg                        rtt_vdsp_val_r;

// spyglass disable_block W401
// SMD: not an input to design unit
// SJ: local gated clock
    wire                 prdcr_clk_0;
// spyglass enable_block W401

// spyglass disable_block Reset_sync04
// SMD: Asynchronous reset signal 'archipelago.rst_a' is synchronized at least twice
// spyglass disable_block W402b
// SMD: rst is gated or internally generated
// SJ: synchronized reset
  always @(posedge prdcr_clk_0 or posedge rst)
    begin : _in_reg_PROC // {
    if (rst == 1'b1)
      begin
        rtt_ss_halt_r <= 1'b0;
        rtt_hw_bp_r <= 1'b0;
        rtt_hw_exc_r <= 1'b0;
        rtt_dbg_halt_r <= 1'b0;
        rtt_rst_applied_r <= 1'b0;
        sys_halt_rr <= 1'b0;
        rtt_uop_is_leave_r <= 1'b0;
        rtt_in_deslot_r <= 1'b0;
        rtt_in_eslot_r <= 1'b0;
        rtt_inst_commit_r <= 0;
        rtt_inst_addr_r <= 31'b0;
        rtt_cond_valid_r <= 0;
        rtt_cond_pass_r <= 0;
        rtt_branch_r <= 0;
        rtt_branch_indir_r <= 0;
        rtt_branch_taddr_r <= 31'b0;
        rtt_dslot_r <= 0;
        rtt_exception_r <= 0;
        rtt_exception_rtn_r <= 0;
        rtt_interrupt_r <= 0;
        rtt_sleep_mode_r <= 0;
        rtt_zd_loop_r <= 0;
        rtt_wp_val_r <= 8'b0;
        rtt_wp_hit_r <= 0;
        rtt_sw_bp_r <= 0;


        rtt_process_id_r <= 8'b0;
        rtt_pid_wr_en_r <= 0;
        rtt_vdsp_data_r <= `npuarc_VDSP_AUX_DATA'b0;     // VDSP sw trigger data
        rtt_vdsp_val_r  <= 1'b0;                  // VDSP sw trigger valid this cycle

      end
    else
      begin
        rtt_ss_halt_r <= rtt_ss_halt;
        rtt_hw_bp_r <= rtt_hw_bp;
        rtt_hw_exc_r <= rtt_hw_exc;
        rtt_dbg_halt_r <= rtt_dbg_halt;
        rtt_rst_applied_r <= rtt_rst_applied;
        sys_halt_rr <= sys_halt_r;
        rtt_uop_is_leave_r <= rtt_uop_is_leave;
        rtt_in_deslot_r <= rtt_in_deslot;
        rtt_in_eslot_r <= rtt_in_eslot;
        rtt_inst_commit_r <= rtt_inst_commit;
        rtt_inst_addr_r <= rtt_inst_addr;
        rtt_cond_valid_r <= rtt_cond_valid;
        rtt_cond_pass_r <= rtt_cond_pass;
        rtt_branch_r <= rtt_branch;
        rtt_branch_indir_r <= rtt_branch_indir;
        rtt_branch_taddr_r <= rtt_branch_taddr;
        rtt_dslot_r <= rtt_dslot;
        rtt_exception_r <= rtt_exception;
        rtt_exception_rtn_r <= rtt_exception_rtn;
        rtt_interrupt_r <= rtt_interrupt;
        rtt_sleep_mode_r <= rtt_sleep_mode;
        rtt_zd_loop_r <= rtt_zd_loop;
        rtt_wp_val_r <= rtt_wp_val;
        rtt_wp_hit_r <= rtt_wp_hit;
        rtt_sw_bp_r <= rtt_sw_bp;


     rtt_process_id_r <= rtt_process_id;
     rtt_pid_wr_en_r <= rtt_pid_wr_en;
     rtt_vdsp_data_r <= rtt_swe_data;  // sw trigger data
     rtt_vdsp_val_r  <= rtt_swe_val;   // sw trigger valid this cycle

      end
    end  // } _in_reg_PROC
// spyglass enable_block Reset_sync04 W402b









  //nets declarations

  wire  [`npuarc_TR_STATUS-1:0]           tr_status;
  wire  [(3'd1-1):0]              rtt_pr_sel;


  wire   [`npuarc_PR_WP-1:0]              pr0_wp_status;
  wire   [`npuarc_PR_WP-1:0]              pr0_wp_enable;
  wire  [2-2:0]          pr0_src_en;
  wire                             pr0_dsm_en;
  wire   [24-1:0]          pr0_filter_type;
  wire   [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter0_start;
  wire   [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter0_stop;
  wire   [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter1_start;
  wire   [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter1_stop;
  wire   [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter2_start;
  wire   [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter2_stop;
  wire   [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter3_start;
  wire   [`npuarc_RTT_ADDR-1:0]           pr0_addr_filter3_stop;
  wire   [`npuarc_RTT_TRG-1:0]            pr0_trigger_reg;
  wire   [`npuarc_PRNUM_WDT-1:0]           pr0_num;
  wire   [`npuarc_SYNCRFR_WDT-1:0]        atb_syncrfr;
  wire                             cti_ctrl_en;
  wire   [`npuarc_ATID_WDT-1:0]           i_atid;
  wire                             ts_en;
  wire                             dm_en;
  wire                             para_done;
  wire                             prdcr_sel_0;
  wire   [2:0]                     bhth;
  wire                             csts_en;

  wire                          pr0_vdswm_en;



// spyglass disable_block W401
// SMD: not an input to design unit
// SJ: local gated clock
  wire                              swe_prdcr_clk;
// spyglass enable_block W401
  wire  [`npuarc_RTT_NUM_SWE_PORTS-1:0]   swe_prdcr_sel;
  wire                              swe_ts_en;
  wire                              swe_para_done;
  wire                              swe_prdcr_req;
  wire                              swe_prdcr_ack;
  wire  [120-1:0]        swe_prdcr_data;

  wire                              swe_prdcr_busy;
  wire                              swe_sbuf_empty;
  wire                              ored_swe_prdcr_sel;
  wire   [`npuarc_ATID_WDT-1:0]            swe_i_atid;
  wire   [`npuarc_SYNCRFR_WDT-1:0]         swe_atb_syncrfr;
  wire                              swe_flush_command;
  wire                              swe_flush_done;
  wire                              swe_dsuppress_nc; // not used
  wire                              swe_rttsyncreq;
  wire                              swe_atb_ctrl_busy;
  wire   [`npuarc_AUX_DATA-1:0]            swe_rtt_bcr_pad;
  wire                              swe_pif_arct0_rtt_write_a;
  wire                              swe_pif_arct0_rtt_read_a;
  wire   [`npuarc_RTT_ADDR-1:0]            swe_pif_arct0_rtt_addr_r;
  wire   [`npuarc_AUX_DATA-1:0]            swe_pif_arct0_rtt_dwr_r;
  wire   [`npuarc_AUX_DATA-1:0]            swe_pif_arct0_rtt_drd_r;

  wire                              swe_apb2aux_valid;
  wire                              swe_csts_en;

  reg [32:0]             sl0_alt_rtt_swe_data_r;
  reg                    sl0_alt_rtt_swe_val_r;
  reg [7:0]              sl0_alt_rtt_swe_ext_r;
  reg [32:0]             sl1_alt_rtt_swe_data_r;
  reg                    sl1_alt_rtt_swe_val_r;
  reg [7:0]              sl1_alt_rtt_swe_ext_r;
  reg [32:0]             sl2_alt_rtt_swe_data_r;
  reg                    sl2_alt_rtt_swe_val_r;
  reg [7:0]              sl2_alt_rtt_swe_ext_r;
  reg [32:0]             sl3_alt_rtt_swe_data_r;
  reg                    sl3_alt_rtt_swe_val_r;
  reg [7:0]              sl3_alt_rtt_swe_ext_r;
  reg [32:0]             sl4_alt_rtt_swe_data_r;
  reg                    sl4_alt_rtt_swe_val_r;
  reg [7:0]              sl4_alt_rtt_swe_ext_r;
  reg [32:0]             sl5_alt_rtt_swe_data_r;
  reg                    sl5_alt_rtt_swe_val_r;
  reg [7:0]              sl5_alt_rtt_swe_ext_r;
  reg [32:0]             sl6_alt_rtt_swe_data_r;
  reg                    sl6_alt_rtt_swe_val_r;
  reg [7:0]              sl6_alt_rtt_swe_ext_r;
  reg [32:0]             sl7_alt_rtt_swe_data_r;
  reg                    sl7_alt_rtt_swe_val_r;
  reg [7:0]              sl7_alt_rtt_swe_ext_r;
  reg [32:0]             sl8_alt_rtt_swe_data_r;
  reg                    sl8_alt_rtt_swe_val_r;
  reg [7:0]              sl8_alt_rtt_swe_ext_r;
  reg [32:0]             sl9_alt_rtt_swe_data_r;
  reg                    sl9_alt_rtt_swe_val_r;
  reg [7:0]              sl9_alt_rtt_swe_ext_r;
  reg [32:0]             sl10_alt_rtt_swe_data_r;
  reg                    sl10_alt_rtt_swe_val_r;
  reg [7:0]              sl10_alt_rtt_swe_ext_r;
  reg [32:0]             sl11_alt_rtt_swe_data_r;
  reg                    sl11_alt_rtt_swe_val_r;
  reg [7:0]              sl11_alt_rtt_swe_ext_r;
  reg [32:0]             sl12_alt_rtt_swe_data_r;
  reg                    sl12_alt_rtt_swe_val_r;
  reg [7:0]              sl12_alt_rtt_swe_ext_r;
  reg [32:0]             sl13_alt_rtt_swe_data_r;
  reg                    sl13_alt_rtt_swe_val_r;
  reg [7:0]              sl13_alt_rtt_swe_ext_r;
  reg [32:0]             sl14_alt_rtt_swe_data_r;
  reg                    sl14_alt_rtt_swe_val_r;
  reg [7:0]              sl14_alt_rtt_swe_ext_r;
  reg [32:0]             sl15_alt_rtt_swe_data_r;
  reg                    sl15_alt_rtt_swe_val_r;
  reg [7:0]              sl15_alt_rtt_swe_ext_r;
  reg [32:0]             sl16_alt_rtt_swe_data_r;
  reg                    sl16_alt_rtt_swe_val_r;
  reg [7:0]              sl16_alt_rtt_swe_ext_r;


// spyglass disable_block W402b
// SMD: rst is gated or internally generated
// SJ: synchronized reset
        always @(posedge swe_prdcr_clk or posedge rst)
        begin : swe_in_reg_PROC
        if (rst == 1'b1)
          begin
             sl0_alt_rtt_swe_data_r        <=32'b0;
             sl0_alt_rtt_swe_val_r         <=1'b0;
             sl0_alt_rtt_swe_ext_r        <=32'b0;
             sl1_alt_rtt_swe_data_r        <=32'b0;
             sl1_alt_rtt_swe_val_r         <=1'b0;
             sl1_alt_rtt_swe_ext_r        <=32'b0;
             sl2_alt_rtt_swe_data_r        <=32'b0;
             sl2_alt_rtt_swe_val_r         <=1'b0;
             sl2_alt_rtt_swe_ext_r        <=32'b0;
             sl3_alt_rtt_swe_data_r        <=32'b0;
             sl3_alt_rtt_swe_val_r         <=1'b0;
             sl3_alt_rtt_swe_ext_r        <=32'b0;
             sl4_alt_rtt_swe_data_r        <=32'b0;
             sl4_alt_rtt_swe_val_r         <=1'b0;
             sl4_alt_rtt_swe_ext_r        <=32'b0;
             sl5_alt_rtt_swe_data_r        <=32'b0;
             sl5_alt_rtt_swe_val_r         <=1'b0;
             sl5_alt_rtt_swe_ext_r        <=32'b0;
             sl6_alt_rtt_swe_data_r        <=32'b0;
             sl6_alt_rtt_swe_val_r         <=1'b0;
             sl6_alt_rtt_swe_ext_r        <=32'b0;
             sl7_alt_rtt_swe_data_r        <=32'b0;
             sl7_alt_rtt_swe_val_r         <=1'b0;
             sl7_alt_rtt_swe_ext_r        <=32'b0;
             sl8_alt_rtt_swe_data_r        <=32'b0;
             sl8_alt_rtt_swe_val_r         <=1'b0;
             sl8_alt_rtt_swe_ext_r        <=32'b0;
             sl9_alt_rtt_swe_data_r        <=32'b0;
             sl9_alt_rtt_swe_val_r         <=1'b0;
             sl9_alt_rtt_swe_ext_r        <=32'b0;
             sl10_alt_rtt_swe_data_r        <=32'b0;
             sl10_alt_rtt_swe_val_r         <=1'b0;
             sl10_alt_rtt_swe_ext_r        <=32'b0;
             sl11_alt_rtt_swe_data_r        <=32'b0;
             sl11_alt_rtt_swe_val_r         <=1'b0;
             sl11_alt_rtt_swe_ext_r        <=32'b0;
             sl12_alt_rtt_swe_data_r        <=32'b0;
             sl12_alt_rtt_swe_val_r         <=1'b0;
             sl12_alt_rtt_swe_ext_r        <=32'b0;
             sl13_alt_rtt_swe_data_r        <=32'b0;
             sl13_alt_rtt_swe_val_r         <=1'b0;
             sl13_alt_rtt_swe_ext_r        <=32'b0;
             sl14_alt_rtt_swe_data_r        <=32'b0;
             sl14_alt_rtt_swe_val_r         <=1'b0;
             sl14_alt_rtt_swe_ext_r        <=32'b0;
             sl15_alt_rtt_swe_data_r        <=32'b0;
             sl15_alt_rtt_swe_val_r         <=1'b0;
             sl15_alt_rtt_swe_ext_r        <=32'b0;
             sl16_alt_rtt_swe_data_r        <=32'b0;
             sl16_alt_rtt_swe_val_r         <=1'b0;
             sl16_alt_rtt_swe_ext_r        <=32'b0;
          end
        else
          begin
             sl0_alt_rtt_swe_data_r        <= sl0_alt_rtt_swe_data;
             sl0_alt_rtt_swe_val_r         <= sl0_alt_rtt_swe_val;
             sl0_alt_rtt_swe_ext_r        <= sl0_alt_rtt_swe_ext;
             sl1_alt_rtt_swe_data_r        <= sl1_alt_rtt_swe_data;
             sl1_alt_rtt_swe_val_r         <= sl1_alt_rtt_swe_val;
             sl1_alt_rtt_swe_ext_r        <= sl1_alt_rtt_swe_ext;
             sl2_alt_rtt_swe_data_r        <= sl2_alt_rtt_swe_data;
             sl2_alt_rtt_swe_val_r         <= sl2_alt_rtt_swe_val;
             sl2_alt_rtt_swe_ext_r        <= sl2_alt_rtt_swe_ext;
             sl3_alt_rtt_swe_data_r        <= sl3_alt_rtt_swe_data;
             sl3_alt_rtt_swe_val_r         <= sl3_alt_rtt_swe_val;
             sl3_alt_rtt_swe_ext_r        <= sl3_alt_rtt_swe_ext;
             sl4_alt_rtt_swe_data_r        <= sl4_alt_rtt_swe_data;
             sl4_alt_rtt_swe_val_r         <= sl4_alt_rtt_swe_val;
             sl4_alt_rtt_swe_ext_r        <= sl4_alt_rtt_swe_ext;
             sl5_alt_rtt_swe_data_r        <= sl5_alt_rtt_swe_data;
             sl5_alt_rtt_swe_val_r         <= sl5_alt_rtt_swe_val;
             sl5_alt_rtt_swe_ext_r        <= sl5_alt_rtt_swe_ext;
             sl6_alt_rtt_swe_data_r        <= sl6_alt_rtt_swe_data;
             sl6_alt_rtt_swe_val_r         <= sl6_alt_rtt_swe_val;
             sl6_alt_rtt_swe_ext_r        <= sl6_alt_rtt_swe_ext;
             sl7_alt_rtt_swe_data_r        <= sl7_alt_rtt_swe_data;
             sl7_alt_rtt_swe_val_r         <= sl7_alt_rtt_swe_val;
             sl7_alt_rtt_swe_ext_r        <= sl7_alt_rtt_swe_ext;
             sl8_alt_rtt_swe_data_r        <= sl8_alt_rtt_swe_data;
             sl8_alt_rtt_swe_val_r         <= sl8_alt_rtt_swe_val;
             sl8_alt_rtt_swe_ext_r        <= sl8_alt_rtt_swe_ext;
             sl9_alt_rtt_swe_data_r        <= sl9_alt_rtt_swe_data;
             sl9_alt_rtt_swe_val_r         <= sl9_alt_rtt_swe_val;
             sl9_alt_rtt_swe_ext_r        <= sl9_alt_rtt_swe_ext;
             sl10_alt_rtt_swe_data_r        <= sl10_alt_rtt_swe_data;
             sl10_alt_rtt_swe_val_r         <= sl10_alt_rtt_swe_val;
             sl10_alt_rtt_swe_ext_r        <= sl10_alt_rtt_swe_ext;
             sl11_alt_rtt_swe_data_r        <= sl11_alt_rtt_swe_data;
             sl11_alt_rtt_swe_val_r         <= sl11_alt_rtt_swe_val;
             sl11_alt_rtt_swe_ext_r        <= sl11_alt_rtt_swe_ext;
             sl12_alt_rtt_swe_data_r        <= sl12_alt_rtt_swe_data;
             sl12_alt_rtt_swe_val_r         <= sl12_alt_rtt_swe_val;
             sl12_alt_rtt_swe_ext_r        <= sl12_alt_rtt_swe_ext;
             sl13_alt_rtt_swe_data_r        <= sl13_alt_rtt_swe_data;
             sl13_alt_rtt_swe_val_r         <= sl13_alt_rtt_swe_val;
             sl13_alt_rtt_swe_ext_r        <= sl13_alt_rtt_swe_ext;
             sl14_alt_rtt_swe_data_r        <= sl14_alt_rtt_swe_data;
             sl14_alt_rtt_swe_val_r         <= sl14_alt_rtt_swe_val;
             sl14_alt_rtt_swe_ext_r        <= sl14_alt_rtt_swe_ext;
             sl15_alt_rtt_swe_data_r        <= sl15_alt_rtt_swe_data;
             sl15_alt_rtt_swe_val_r         <= sl15_alt_rtt_swe_val;
             sl15_alt_rtt_swe_ext_r        <= sl15_alt_rtt_swe_ext;
             sl16_alt_rtt_swe_data_r        <= sl16_alt_rtt_swe_data;
             sl16_alt_rtt_swe_val_r         <= sl16_alt_rtt_swe_val;
             sl16_alt_rtt_swe_ext_r        <= sl16_alt_rtt_swe_ext;
         end
        end
// spyglass enable_block W402b



  wire                                prdcr_busy;
  wire                                transport_sys_busy;
  wire                                nta_oQ_busy;



  wire                                    dsm_wr_en;
  wire                                    dsm_rd_en;
  wire  [(`npuarc_DSM_WDT)-1:0]                  dsm_wr_data;
  wire  [(`npuarc_DSM_WDT)-1:0]                  dsm_rd_data;
  wire  [`npuarc_DSM_BUF_DEPTH-1:0]              dsm_wr_ptr;
  wire  [`npuarc_DSM_BUF_DEPTH-1:0]              dsm_rd_ptr;


  wire                                    vdspm_wr_en;
  wire                                    vdspm_rd_en;
  wire  [(`npuarc_VDSPSW_WDT)-1:0]               vdspm_wr_data;
  wire  [(`npuarc_VDSPSW_WDT)-1:0]               vdspm_rd_data;
  wire  [`npuarc_VDSPM_BUF_DEPTH-1:0]            vdspm_wr_ptr;
  wire  [`npuarc_VDSPM_BUF_DEPTH-1:0]            vdspm_rd_ptr;

  wire                                    errm_wr_en;
  wire                                    errm_rd_en;
  wire  [(`npuarc_ERRM_WDT)-1:0]                 errm_wr_data;
  wire  [(`npuarc_ERRM_WDT)-1:0]                 errm_rd_data;
  wire  [`npuarc_ERRM_BUF_DEPTH-1:0]             errm_wr_ptr;
  wire  [`npuarc_ERRM_BUF_DEPTH-1:0]             errm_rd_ptr;

  wire                                    otm_wr_en;
  wire                                    otm_rd_en;
  wire  [(`npuarc_OTM_WDT)-1:0]                  otm_wr_data;
  wire  [(`npuarc_OTM_WDT)-1:0]                  otm_rd_data;
  wire  [`npuarc_OTM_BUF_DEPTH-1:0]              otm_wr_ptr;
  wire  [`npuarc_OTM_BUF_DEPTH-1:0]              otm_rd_ptr;


  wire                                    pcm_wr_en;
  wire                                    pcm_rd_en;
  wire  [(`npuarc_PCM_WDT)-1:0]                  pcm_wr_data;
  wire  [(`npuarc_PCM_WDT)-1:0]                  pcm_rd_data;
  wire  [`npuarc_PCM_BUF_DEPTH-1:0]              pcm_wr_ptr;
  wire  [`npuarc_PCM_BUF_DEPTH-1:0]              pcm_rd_ptr;



  wire                                    ptcm_wr_en;
  wire                                    ptcm_rd_en;
  wire  [(120)-1:0]                 ptcm_wr_data;
  wire  [(120)-1:0]                 ptcm_rd_data;
  wire  [`npuarc_PTCM_BUF_DEPTH-1:0]             ptcm_wr_ptr;
  wire  [`npuarc_PTCM_BUF_DEPTH-1:0]             ptcm_rd_ptr;



  wire                                    ptm_wr_en;
  wire                                    ptm_rd_en;
  wire  [(`npuarc_PTM_WDT)-1:0]                  ptm_wr_data;
  wire  [(`npuarc_PTM_WDT)-1:0]                  ptm_rd_data;
  wire  [`npuarc_PTM_BUF_DEPTH-1:0]              ptm_wr_ptr;
  wire  [`npuarc_PTM_BUF_DEPTH-1:0]              ptm_rd_ptr;




  wire                                    rfm_wr_en;
  wire                                    rfm_rd_en;
  wire  [(`npuarc_RFM_WDT)-1:0]                  rfm_wr_data;
  wire  [(`npuarc_RFM_WDT)-1:0]                  rfm_rd_data;
  wire  [`npuarc_RFM_BUF_DEPTH-1:0]              rfm_wr_ptr;
  wire  [`npuarc_RFM_BUF_DEPTH-1:0]              rfm_rd_ptr;




  wire                                    wpm_wr_en;
  wire                                    wpm_rd_en;
  wire  [(`npuarc_WPM_WDT)-1:0]                  wpm_wr_data;
  wire  [(`npuarc_WPM_WDT)-1:0]                  wpm_rd_data;
  wire  [`npuarc_WPM_BUF_DEPTH-1:0]              wpm_wr_ptr;
  wire  [`npuarc_WPM_BUF_DEPTH-1:0]              wpm_rd_ptr;

   wire                         prdcr_req;
   wire                         prdcr_ack;
   wire                           prdcr_busy_0;
   wire  [`npuarc_RTT_DATA-1:0]         pr0_rtt_datar;
   wire                           rttsyncreq;
   wire                           flush_done;
   wire                           flush_command;
   wire                           atb_ctrl_busy;
   wire                           ds_en;
   wire  [120-1:0]     prdcr_data;
   wire                           dsuppress;
   wire                           rtt_freeze_cntrl;
   wire  [`npuarc_FR_STATUS-1:0]         freeze_status;



   wire [`npuarc_RTT_TIME_STMP-1:0]       pr0_time_stamp;
//transport module nets


   wire                           rtt_flush_command;
   wire                           rtt_time_stamp_en;
   wire                           rtt_dbgr_msgs_en;

   wire [`npuarc_MEM_STRG_WDT-1:0] int_buf_wdata;
   wire                      pif_rtt_write_a;
   wire                      pif_rtt_read_a;
//leda NTL_CON13A off
   wire   [`npuarc_RTT_ADDR-1:0]    pif_rtt_addr_r;
//leda NTL_CON13A on
   wire   [`npuarc_RTT_DATA-1:0]    pif_rtt_dwr_r;

  wire ored_prdcr_sel_p;
  wire tmp_rst_a;

    assign    rtt_src_num = 8'd0;


npuarc_rtt_glue u_rtt_glue (
  .pr0_num(pr0_num),
  .prdcr_busy_0(prdcr_busy_0),
  .prdcr_sel_0(prdcr_sel_0),
  .ored_prdcr_sel_p(ored_prdcr_sel_p),


  .swe_prdcr_busy(swe_prdcr_busy),
  .swe_prdcr_sel(swe_prdcr_sel),
  .ored_swe_prdcr_sel(ored_swe_prdcr_sel),
  .sl0_alt_rtt_swe_prdcr_en(sl0_alt_rtt_swe_prdcr_en),
  .sl1_alt_rtt_swe_prdcr_en(sl1_alt_rtt_swe_prdcr_en),
  .sl2_alt_rtt_swe_prdcr_en(sl2_alt_rtt_swe_prdcr_en),
  .sl3_alt_rtt_swe_prdcr_en(sl3_alt_rtt_swe_prdcr_en),
  .sl4_alt_rtt_swe_prdcr_en(sl4_alt_rtt_swe_prdcr_en),
  .sl5_alt_rtt_swe_prdcr_en(sl5_alt_rtt_swe_prdcr_en),
  .sl6_alt_rtt_swe_prdcr_en(sl6_alt_rtt_swe_prdcr_en),
  .sl7_alt_rtt_swe_prdcr_en(sl7_alt_rtt_swe_prdcr_en),
  .sl8_alt_rtt_swe_prdcr_en(sl8_alt_rtt_swe_prdcr_en),
  .sl9_alt_rtt_swe_prdcr_en(sl9_alt_rtt_swe_prdcr_en),
  .sl10_alt_rtt_swe_prdcr_en(sl10_alt_rtt_swe_prdcr_en),
  .sl11_alt_rtt_swe_prdcr_en(sl11_alt_rtt_swe_prdcr_en),
  .sl12_alt_rtt_swe_prdcr_en(sl12_alt_rtt_swe_prdcr_en),
  .sl13_alt_rtt_swe_prdcr_en(sl13_alt_rtt_swe_prdcr_en),
  .sl14_alt_rtt_swe_prdcr_en(sl14_alt_rtt_swe_prdcr_en),
  .sl15_alt_rtt_swe_prdcr_en(sl15_alt_rtt_swe_prdcr_en),
  .sl16_alt_rtt_swe_prdcr_en(sl16_alt_rtt_swe_prdcr_en),

  .cu_clk(cu_clk),


  .rtt_clk(rtt_clk),

  .rst_a(rst_a),
  .tmp_rst_a(tmp_rst_a),
  .prdcr_busy(prdcr_busy)
);

// spyglass disable_block W402b
// SMD: The reset to the flop is gated or internally generated in the design.
// SJ: The signal "rst" is synchronized version of "rst_a" generated in the design. Will not cause any issues in the design.
// reset sync. module
npuarc_rtt_reset_ctrl u_rtt_reset_ctrl (
    .clk       (rtt_clk),
    .rst_a     (tmp_rst_a),
    .rst       (rst),
    .test_mode (test_mode)
);
// spyglass enable_block W402b

// spyglass disable_block W402b
// SMD: rst is gated or internally generated
// SJ: synchronized reset
// ATB/APB reset sync. module
npuarc_rtt_atb_rst_ctrl u_atb_reset_ctrl (
    .clk       (rtt_clk),
    .rst_a     (rst),
    .rst_in    (atresetn),
    .rst_out   (atb_rst),
    .test_mode (test_mode)
);
// spyglass enable_block W402b

wire apb_rst;
npuarc_rtt_apb_rst_ctrl u_rtt_apb_rst_ctrl
(
 .clk          (rtt_clk),
 .rst_a        (rst),
 .rst_in       (presetdbgn),
 .rst_out      (apb_rst),
 .test_mode    (test_mode)
);

npuarc_arct_dbg_if u_arct_dbg_if
(
 .pclkdbg      (rtt_clk),
 .pclkdbg_en   (pclkdbg_en),
 .presetdbgn   (apb_rst),
 .paddrdbg     (arct0_paddrdbg),
 .pseldbg      (arct0_pseldbg),
 .penabledbg   (arct0_penabledbg),
 .pwritedbg    (arct0_pwritedbg),
 .pwdatadbg    (arct0_pwdatadbg),
 .preadydbg    (arct0_preadydbg),
 .prdatadbg    (arct0_prdatadbg),
 .pslverrdbg   (arct0_pslverrdbg),
 .dbgen        (arct0_dbgen),
 .niden        (arct0_niden),
 .rtt_write    (arct_apb2aux_write),
 .rtt_read     (arct_apb2aux_read),
 .rtt_addr     (arct_apb2aux_address),
 .rtt_dataw    (arct_apb2aux_wdata),
 .rtt_datar    (arct_apb2aux_rdata),
 //TODO update bcr_pad value for rom_table 
 .rtt_bcr_pad  (32'b0),
 .has_rtt_iso_disable(1'b1)
);  

assign rtt_drd_r = rtt_read_a ? pif_arct0_rtt_drd_r :32'b0; 

assign arct_apb2aux_rdata = arct_apb2aux_read ? ( 
                                                 (arct_apb2aux_address[21:16] == 6'd0) ? pif_arct0_rtt_drd_r :
                                                 ((arct_apb2aux_address[21:16] >= 6'd1) && (arct_apb2aux_address[21:16] <= 6'd17)) ? swe_pif_arct0_rtt_drd_r :
                                                  32'b0) : 32'b0;

assign swe_apb2aux_valid = (arct_apb2aux_write || arct_apb2aux_read) && ((arct_apb2aux_address[21:16] >= 6'd1) && (arct_apb2aux_address[21:16] <= 6'd17));

assign swe_pif_arct0_rtt_write_a = swe_apb2aux_valid ? arct_apb2aux_write : 1'b0;
assign swe_pif_arct0_rtt_read_a  = swe_apb2aux_valid ? arct_apb2aux_read : 1'b0;
assign swe_pif_arct0_rtt_addr_r  = swe_apb2aux_valid ? arct_apb2aux_address : 32'b0;
assign swe_pif_arct0_rtt_dwr_r   = swe_apb2aux_valid ? arct_apb2aux_wdata : 32'b0;


// multi core programming interface
npuarc_rtt_programming_if u_rtt_programming_if (



.rtt_write_a (rtt_write_a),
.rtt_read_a  (rtt_read_a),
.rtt_addr_r  (rtt_addr_r),
.rtt_dwr_r   (rtt_dwr_r),


.pif_arct0_rtt_write_a  (pif_arct0_rtt_write_a),
.pif_arct0_rtt_read_a   (pif_arct0_rtt_read_a),
.pif_arct0_rtt_addr_r   (pif_arct0_rtt_addr_r),
.pif_arct0_rtt_dwr_r    (pif_arct0_rtt_dwr_r),


.arct_rtt_write_a (arct_apb2aux_write),
.arct_rtt_read_a (arct_apb2aux_read),
.arct_rtt_addr_r (arct_apb2aux_address),
.arct_rtt_dwr_r (arct_apb2aux_wdata)
);







npuarc_rtt_small_prdcr_regs u_rtt_small_prdcr_regs (

 .rtt_clk(rtt_clk),
 .rst_a(rst),
 .rtt_write(pif_arct0_rtt_write_a),
 .rtt_addr(pif_arct0_rtt_addr_r[8:0]),
 .rtt_dataw(pif_arct0_rtt_dwr_r) ,
 .rtt_read(pif_arct0_rtt_read_a),
 .pr0_rtt_datar(pif_arct0_rtt_drd_r),
 .freeze_status(freeze_status),
 .pr0_wp_val(rtt_wp_val_r),
 .pr0_wp_hit(rtt_wp_hit_r),
 .pr0_src_en(pr0_src_en),
 .pr0_dsm_en(pr0_dsm_en),
 .pr0_filter_type(pr0_filter_type),
 .pr0_addr_filter0_start(pr0_addr_filter0_start),
 .pr0_addr_filter0_stop(pr0_addr_filter0_stop),
 .pr0_addr_filter1_start(pr0_addr_filter1_start),
 .pr0_addr_filter1_stop(pr0_addr_filter1_stop),
 .pr0_addr_filter2_start(pr0_addr_filter2_start),
 .pr0_addr_filter2_stop(pr0_addr_filter2_stop),
 .pr0_addr_filter3_start(pr0_addr_filter3_start),
 .pr0_addr_filter3_stop(pr0_addr_filter3_stop),
 .pr0_cti_ctrl_en      (cti_ctrl_en),
 .pr0_atid             (i_atid),
 .pr0_syncrfr          (atb_syncrfr),
 .rtt_flush_command    (flush_command),
 .flush_done           (flush_done),
 .pr0_ds_en            (ds_en),
 .rtt_time_stamp_en    (ts_en),
//spyglass disable_block UnloadedOutTerm-ML
//SMD: Unloaded but driven output terminal of an instance detected
//SJ:  dm_en is used only in case of medium producer
 .rtt_dbgr_msgs_en     (dm_en),
//spyglass enable_block UnloadedOutTerm-ML
 .rtt_freeze_cntrl     (rtt_freeze_cntrl),
 .rtt_pr_sel           (prdcr_sel_0),
 .pr0_bhth             (bhth),
 .pr0_csts_en          (csts_en),
 .pr0_trigger_reg      (pr0_trigger_reg),
 .pr0_vdswm_en         (pr0_vdswm_en),
 .pr0_wp_enable        (pr0_wp_enable),
 .pr0_wp_status        (pr0_wp_status)

  );

//producer interface module instantiation
npuarc_rtt_small_prdcr_top #(.PTCM_WDT_PP(120), .PCM_WDT_PP(`npuarc_PCM_WDT), .PTM_WDT_PP(`npuarc_PTM_WDT), .PC_PP(31),.RTT_ADDR_PP(`npuarc_RTT_ADDR),
                          .DUAL_ISSUE_PP(`npuarc_RTT_DUAL_ISSUE), .RTT_NUM_FILTERS_PP(`npuarc_RTT_NUM_FILTERS), .FILTER_BITLEN_PP(FILTER_BITLEN_PP)
) u_rtt_small_prdcr_top(
.rtt_clk (prdcr_clk_0), //RTT clock
.rst_a(  rst),          //Asynchronous reset
.pr_num(pr0_num),
.rtt_freeze(  rtt_freeze),
  //Aux interface
.rtt_write_a(  pif_arct0_rtt_write_a),

 //Core signals for Debug status
.rtt_ss_halt(  rtt_ss_halt_r),
.rtt_hw_bp(  rtt_hw_bp_r),
.rtt_hw_exc(  rtt_hw_exc_r),
.rtt_dbg_halt(  rtt_dbg_halt_r),
.rtt_rst_applied(  rtt_rst_applied_r),
.sys_halt_r(  sys_halt_rr),

  //Core signals for PTM
.rtt_uop_is_leave(rtt_uop_is_leave_r),
.rtt_in_deslot(rtt_in_deslot_r),
.rtt_in_eslot(rtt_in_eslot_r),
.rtt_inst_commit(  rtt_inst_commit_r),
.rtt_inst_addr(  rtt_inst_addr_r),
.rtt_cond_valid(  rtt_cond_valid_r),
.rtt_cond_pass(  rtt_cond_pass_r),
.rtt_branch_taken(  rtt_branch_r),
.rtt_dslot(  rtt_dslot_r),
.rtt_branch_indir(  rtt_branch_indir_r),
.rtt_branch_taddr(  rtt_branch_taddr_r),
.rtt_exception(  rtt_exception_r),
.rtt_exception_rtn(  rtt_exception_rtn_r),
.rtt_interrupt(  rtt_interrupt_r),
.rtt_enter_sleep(  rtt_sleep_mode_r),
.rtt_zd_loop(  rtt_zd_loop_r),
.rtt_wp_val(  rtt_wp_val_r),
.rtt_sw_bp(  rtt_sw_bp_r),
.atb_syncreq(rttsyncreq),
.cti_rtt_filters(cti_rtt_filters_pre),
.cti_trace_start(cti_trace_start_s),
.cti_trace_stop(cti_trace_stop_s),
.cti_ctrl_en(cti_ctrl_en),
.para_done(para_done),
.bhth(bhth),
.atb_cstimestamp(atb_cstimestamp),
.pr0_csts_en(csts_en),
  .vdswm_en(pr0_vdswm_en),

.rtt_process_id(  rtt_process_id_r),
.rtt_pid_wr_en (rtt_pid_wr_en_r),
.rtt_vdsp_data(rtt_vdsp_data_r),     // VDSP sw trigger data
.rtt_vdsp_val(rtt_vdsp_val_r),      // VDSP sw trigger valid this cycle
// Programming IF start
.pr0_src_en(  pr0_src_en),
.pr0_dsm_en(  pr0_dsm_en),

.pr0_filter_type(  pr0_filter_type),
.pr0_addr_filter0_start(  pr0_addr_filter0_start),
.pr0_addr_filter0_stop(  pr0_addr_filter0_stop),
.pr0_addr_filter1_start(  pr0_addr_filter1_start),
.pr0_addr_filter1_stop(  pr0_addr_filter1_stop),
.pr0_addr_filter2_start(  pr0_addr_filter2_start),
.pr0_addr_filter2_stop(  pr0_addr_filter2_stop),
.pr0_addr_filter3_start(  pr0_addr_filter3_start),
.pr0_addr_filter3_stop(  pr0_addr_filter3_stop),
.pr0_trigger_reg(  pr0_trigger_reg),
.rtt_pr_sel(  prdcr_sel_0),
.rtt_flush_command(  flush_command),
.flush_done (flush_done),
.rtt_time_stamp_en(  ts_en),
.pr0_wp_enable(  pr0_wp_enable),
.pr0_wp_status(  pr0_wp_status),
.rtt_freeze_cntrl(rtt_freeze_cntrl),
//programming if END

// time stamp counter
.time_stamp (pr0_time_stamp),
//trasport outputs
 //inputs to transport


.ds_sbuf_wr_en(dsm_wr_en),
.ds_sbuf_rd_en(dsm_rd_en),
.ds_sbuf_wr_data(dsm_wr_data),
.ds_sbuf_rd_data(dsm_rd_data),
.ds_sbuf_wr_ptr(dsm_wr_ptr),
.ds_sbuf_rd_ptr(dsm_rd_ptr),


.vdspm_sbuf_wr_en(vdspm_wr_en),
.vdspm_sbuf_rd_en(vdspm_rd_en),
.vdspm_sbuf_wr_data(vdspm_wr_data),
.vdspm_sbuf_rd_data(vdspm_rd_data),
.vdspm_sbuf_wr_ptr(vdspm_wr_ptr),
.vdspm_sbuf_rd_ptr(vdspm_rd_ptr),

.errm_sbuf_wr_en(errm_wr_en),
.errm_sbuf_rd_en(errm_rd_en),
.errm_sbuf_wr_data(errm_wr_data),
.errm_sbuf_rd_data(errm_rd_data),
.errm_sbuf_wr_ptr(errm_wr_ptr),
.errm_sbuf_rd_ptr(errm_rd_ptr),

.otm_sbuf_wr_en(otm_wr_en),
.otm_sbuf_rd_en(otm_rd_en),
.otm_sbuf_wr_data(otm_wr_data),
.otm_sbuf_rd_data(otm_rd_data),
.otm_sbuf_wr_ptr(otm_wr_ptr),
.otm_sbuf_rd_ptr(otm_rd_ptr),


.pc_sbuf_wr_en(pcm_wr_en),
.pc_sbuf_rd_en(pcm_rd_en),
.pc_sbuf_wr_data(pcm_wr_data),
.pc_sbuf_rd_data(pcm_rd_data),
.pc_sbuf_wr_ptr(pcm_wr_ptr),
.pc_sbuf_rd_ptr(pcm_rd_ptr),



.ptc_sbuf_wr_en(ptcm_wr_en),
.ptc_sbuf_rd_en(ptcm_rd_en),
.ptc_sbuf_wr_data(ptcm_wr_data),
.ptc_sbuf_rd_data(ptcm_rd_data),
.ptc_sbuf_wr_ptr(ptcm_wr_ptr),
.ptc_sbuf_rd_ptr(ptcm_rd_ptr),



.pt_sbuf_wr_en(ptm_wr_en),
.pt_sbuf_rd_en(ptm_rd_en),
.pt_sbuf_wr_data(ptm_wr_data),
.pt_sbuf_rd_data(ptm_rd_data),
.pt_sbuf_wr_ptr(ptm_wr_ptr),
.pt_sbuf_rd_ptr(ptm_rd_ptr),




.rfm_sbuf_wr_en(rfm_wr_en),
.rfm_sbuf_rd_en(rfm_rd_en),
.rfm_sbuf_wr_data(rfm_wr_data),
.rfm_sbuf_rd_data(rfm_rd_data),
.rfm_sbuf_wr_ptr(rfm_wr_ptr),
.rfm_sbuf_rd_ptr(rfm_rd_ptr),

.wpm_sbuf_wr_en(wpm_wr_en),
.wpm_sbuf_rd_en(wpm_rd_en),
.wpm_sbuf_wr_data(wpm_wr_data),
.wpm_sbuf_rd_data(wpm_rd_data),
.wpm_sbuf_wr_ptr(wpm_wr_ptr),
.wpm_sbuf_rd_ptr(wpm_rd_ptr),


.prdcr_req(prdcr_req),
.prdcr_ack(prdcr_ack),
.prdcr_data(prdcr_data),
//transport output ends
.prdcr_busy (prdcr_busy_0),
.freeze_status(freeze_status)
); // end of prdcr top module

npuarc_arct_cti_pipeline # (.WIDTH(28), .STAGES(2 )) u_rtt_small_cti_pipeline 
(
  .clk   (rtt_clk),
  .din   ({cti_rtt_filters_pre,cti_trace_start,cti_trace_stop}),
  .dout  ({cti_rtt_filters,cti_trace_start_s,cti_trace_stop_s})
);


npuarc_rtt_swe_prdcr_regs u_rtt_swe_prdcr_regs (

 .rtt_clk(rtt_clk),
 .rst_a(rst),
 .rtt_addr(swe_pif_arct0_rtt_addr_r[8:0]),
 .rtt_dataw(swe_pif_arct0_rtt_dwr_r) ,
 .rtt_write(swe_pif_arct0_rtt_write_a),
 .rtt_read(swe_pif_arct0_rtt_read_a),
 .pr0_rtt_datar(swe_pif_arct0_rtt_drd_r),
 .swe_prdcr_sel        (swe_prdcr_sel),
 .pr0_atid             (swe_i_atid),
 .pr0_syncrfr          (swe_atb_syncrfr),
 .rtt_flush_command    (swe_flush_command),
 .flush_done           (swe_flush_done),
 .rtt_time_stamp_en    (swe_ts_en),
 .pr0_csts_en          (swe_csts_en),
 .swe_rtt_bcr_pad      (swe_rtt_bcr_pad)
  );

//producer interface module instantiation
npuarc_rtt_swe_prdcr_top  u_rtt_swe_prdcr_top(
.rtt_clk (swe_prdcr_clk), //RTT clock
.rst_a(  rst),          //Asynchronous reset

  //Aux interface
.rtt_write_a(swe_pif_arct0_rtt_write_a),
.para_done(swe_para_done),
 // programming IP inputs
.swe_pr_sel( swe_prdcr_sel ),
.rtt_flush_command(  swe_flush_command),
.flush_done (swe_flush_done),
.rtt_time_stamp_en(  swe_ts_en),
// time stamp counter
.time_stamp ( pr0_time_stamp),
.cstimestamp(atb_cstimestamp),
.swe_csts_en( swe_csts_en),
.atb_syncreq(swe_rttsyncreq),

.sl0_alt_rtt_swe_data( sl0_alt_rtt_swe_data_r),
.sl0_alt_rtt_swe_val ( sl0_alt_rtt_swe_val_r),
.sl0_alt_rtt_swe_ext ( sl0_alt_rtt_swe_ext_r),
.sl1_alt_rtt_swe_data( sl1_alt_rtt_swe_data_r),
.sl1_alt_rtt_swe_val ( sl1_alt_rtt_swe_val_r),
.sl1_alt_rtt_swe_ext ( sl1_alt_rtt_swe_ext_r),
.sl2_alt_rtt_swe_data( sl2_alt_rtt_swe_data_r),
.sl2_alt_rtt_swe_val ( sl2_alt_rtt_swe_val_r),
.sl2_alt_rtt_swe_ext ( sl2_alt_rtt_swe_ext_r),
.sl3_alt_rtt_swe_data( sl3_alt_rtt_swe_data_r),
.sl3_alt_rtt_swe_val ( sl3_alt_rtt_swe_val_r),
.sl3_alt_rtt_swe_ext ( sl3_alt_rtt_swe_ext_r),
.sl4_alt_rtt_swe_data( sl4_alt_rtt_swe_data_r),
.sl4_alt_rtt_swe_val ( sl4_alt_rtt_swe_val_r),
.sl4_alt_rtt_swe_ext ( sl4_alt_rtt_swe_ext_r),
.sl5_alt_rtt_swe_data( sl5_alt_rtt_swe_data_r),
.sl5_alt_rtt_swe_val ( sl5_alt_rtt_swe_val_r),
.sl5_alt_rtt_swe_ext ( sl5_alt_rtt_swe_ext_r),
.sl6_alt_rtt_swe_data( sl6_alt_rtt_swe_data_r),
.sl6_alt_rtt_swe_val ( sl6_alt_rtt_swe_val_r),
.sl6_alt_rtt_swe_ext ( sl6_alt_rtt_swe_ext_r),
.sl7_alt_rtt_swe_data( sl7_alt_rtt_swe_data_r),
.sl7_alt_rtt_swe_val ( sl7_alt_rtt_swe_val_r),
.sl7_alt_rtt_swe_ext ( sl7_alt_rtt_swe_ext_r),
.sl8_alt_rtt_swe_data( sl8_alt_rtt_swe_data_r),
.sl8_alt_rtt_swe_val ( sl8_alt_rtt_swe_val_r),
.sl8_alt_rtt_swe_ext ( sl8_alt_rtt_swe_ext_r),
.sl9_alt_rtt_swe_data( sl9_alt_rtt_swe_data_r),
.sl9_alt_rtt_swe_val ( sl9_alt_rtt_swe_val_r),
.sl9_alt_rtt_swe_ext ( sl9_alt_rtt_swe_ext_r),
.sl10_alt_rtt_swe_data( sl10_alt_rtt_swe_data_r),
.sl10_alt_rtt_swe_val ( sl10_alt_rtt_swe_val_r),
.sl10_alt_rtt_swe_ext ( sl10_alt_rtt_swe_ext_r),
.sl11_alt_rtt_swe_data( sl11_alt_rtt_swe_data_r),
.sl11_alt_rtt_swe_val ( sl11_alt_rtt_swe_val_r),
.sl11_alt_rtt_swe_ext ( sl11_alt_rtt_swe_ext_r),
.sl12_alt_rtt_swe_data( sl12_alt_rtt_swe_data_r),
.sl12_alt_rtt_swe_val ( sl12_alt_rtt_swe_val_r),
.sl12_alt_rtt_swe_ext ( sl12_alt_rtt_swe_ext_r),
.sl13_alt_rtt_swe_data( sl13_alt_rtt_swe_data_r),
.sl13_alt_rtt_swe_val ( sl13_alt_rtt_swe_val_r),
.sl13_alt_rtt_swe_ext ( sl13_alt_rtt_swe_ext_r),
.sl14_alt_rtt_swe_data( sl14_alt_rtt_swe_data_r),
.sl14_alt_rtt_swe_val ( sl14_alt_rtt_swe_val_r),
.sl14_alt_rtt_swe_ext ( sl14_alt_rtt_swe_ext_r),
.sl15_alt_rtt_swe_data( sl15_alt_rtt_swe_data_r),
.sl15_alt_rtt_swe_val ( sl15_alt_rtt_swe_val_r),
.sl15_alt_rtt_swe_ext ( sl15_alt_rtt_swe_ext_r),
.sl16_alt_rtt_swe_data( sl16_alt_rtt_swe_data_r),
.sl16_alt_rtt_swe_val ( sl16_alt_rtt_swe_val_r),
.sl16_alt_rtt_swe_ext ( sl16_alt_rtt_swe_ext_r),


.prdcr_req(swe_prdcr_req),
.prdcr_ack(swe_prdcr_ack),
.prdcr_data(swe_prdcr_data),
//transport output ends
.prdcr_busy (swe_prdcr_busy)
  );


npuarc_rtt_atb_if u_rtt_atb_if (
   .atclken(atclken),
  .ug_rtt_clk(rtt_clk),

  .prdcr_clk_0 (prdcr_clk_0),

  .rtt_flush_command_0(flush_command),
  .para_done_0(para_done),
  .atb_syncrfr_0(atb_syncrfr),
  .req_0(prdcr_req),
  .ack_0(prdcr_ack),
  .data_0(prdcr_data),

  .atb_done_0(flush_done),
  .atb_ctrl_busy_0(atb_ctrl_busy),
  .i_atid_0(i_atid),
  .ds_en_0(ds_en),
  .atready_0(atready),
  .atdata_0(atdata),
  .atbytes_0(atbytes),
  .atid_0(atid),
  .atvalid_0(atvalid),

  .afvalid_0(afvalid),
  .afready_0(afready),
  .syncreq_0(syncreq),

  .dsuppress_0(dsuppress),
  .rttsyncreq_0(rttsyncreq),


  .prdcr_clk_1 (swe_prdcr_clk),

  .rtt_flush_command_1(swe_flush_command),
  .para_done_1(swe_para_done),
  .atb_syncrfr_1(swe_atb_syncrfr),
  .req_1(swe_prdcr_req),
  .ack_1(swe_prdcr_ack),
  .data_1(swe_prdcr_data),

  .atb_done_1(swe_flush_done),
  .atb_ctrl_busy_1(swe_atb_ctrl_busy),
  .i_atid_1(swe_i_atid),
  .ds_en_1(1'b0),
  .atready_1(swe_atready),
  .atdata_1(swe_atdata),
  .atbytes_1(swe_atbytes),
  .atid_1(swe_atid),
  .atvalid_1(swe_atvalid),

  .afvalid_1(swe_afvalid),
  .afready_1(swe_afready),
  .syncreq_1(swe_syncreq),

  .dsuppress_1(swe_dsuppress_nc),
  .rttsyncreq_1(swe_rttsyncreq),

  .has_rtt_iso_disable(1'b1),

  .atresetn (atb_rst),
  .rst_a (rst)
);





npuarc_time_stamp_cntr u_time_stamp_cntr( .rtt_clk (cu_clk),
  .rst_a (rst),
  .pr0_time_stamp(pr0_time_stamp)
);



npuarc_rtt_prdcr_cgm u_rtt_prdcr0_cgm  (
.rtt_clk(rtt_clk),
.rst_a(rst),
.atb_ctrl_busy(atb_ctrl_busy),
.rtt_write_a (pif_arct0_rtt_write_a),
.prdcr_clk_en(prdcr_busy_0),
.prdcr_en(prdcr_sel_0),
.prdcr_clk(prdcr_clk_0)
);

assign rtt_prod_sel = prdcr_sel_0;


npuarc_rtt_prdcr_cgm u_rtt_swe_prdcr_cgm  (
.rtt_clk(rtt_clk),
.rst_a(rst),
.atb_ctrl_busy(swe_atb_ctrl_busy),
.rtt_write_a (swe_pif_arct0_rtt_write_a),
.prdcr_clk_en(swe_prdcr_busy),
.prdcr_en(ored_swe_prdcr_sel),
.prdcr_clk(swe_prdcr_clk)
);




npuarc_rtt_sbuf_array_top u_rtt_sbuf_array_top
(




.prdcr_clk_0(prdcr_clk_0),


.dsm_wr_en(dsm_wr_en),
.dsm_rd_en(dsm_rd_en),
.dsm_wr_data(dsm_wr_data),
.dsm_rd_data(dsm_rd_data),
.dsm_wr_ptr(dsm_wr_ptr),
.dsm_rd_ptr(dsm_rd_ptr),

.vdspm_wr_en(vdspm_wr_en),
.vdspm_rd_en(vdspm_rd_en),
.vdspm_wr_data(vdspm_wr_data),
.vdspm_rd_data(vdspm_rd_data),
.vdspm_wr_ptr(vdspm_wr_ptr),
.vdspm_rd_ptr(vdspm_rd_ptr),

.errm_wr_en(errm_wr_en),
.errm_rd_en(errm_rd_en),
.errm_wr_data(errm_wr_data),
.errm_rd_data(errm_rd_data),
.errm_wr_ptr(errm_wr_ptr),
.errm_rd_ptr(errm_rd_ptr),

.otm_wr_en(otm_wr_en),
.otm_rd_en(otm_rd_en),
.otm_wr_data(otm_wr_data),
.otm_rd_data(otm_rd_data),
.otm_wr_ptr(otm_wr_ptr),
.otm_rd_ptr(otm_rd_ptr),

.pcm_wr_en(pcm_wr_en),
.pcm_rd_en(pcm_rd_en),
.pcm_wr_data(pcm_wr_data),
.pcm_rd_data(pcm_rd_data),
.pcm_wr_ptr(pcm_wr_ptr),
.pcm_rd_ptr(pcm_rd_ptr),

.ptcm_wr_en(ptcm_wr_en),
.ptcm_rd_en(ptcm_rd_en),
.ptcm_wr_data(ptcm_wr_data),
.ptcm_rd_data(ptcm_rd_data),
.ptcm_wr_ptr(ptcm_wr_ptr),
.ptcm_rd_ptr(ptcm_rd_ptr),


.wpm_wr_en(wpm_wr_en),
.wpm_rd_en(wpm_rd_en),
.wpm_wr_data(wpm_wr_data),
.wpm_rd_data(wpm_rd_data),
.wpm_wr_ptr(wpm_wr_ptr),
.wpm_rd_ptr(wpm_rd_ptr),

.ptm_wr_en(ptm_wr_en),
.ptm_rd_en(ptm_rd_en),
.ptm_wr_data(ptm_wr_data),
.ptm_rd_data(ptm_rd_data),
.ptm_wr_ptr(ptm_wr_ptr),
.ptm_rd_ptr(ptm_rd_ptr),

.rfm_wr_en(rfm_wr_en),
.rfm_rd_en(rfm_rd_en),
.rfm_wr_data(rfm_wr_data),
.rfm_rd_data(rfm_rd_data),
.rfm_wr_ptr(rfm_wr_ptr),
.rfm_rd_ptr(rfm_rd_ptr),

.rst_a(rst)
);




endmodule
// leda VER_1_6_4_1 on


