// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2017 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
// work of Synopsys, Inc., and is fully protected under copyright and 
// trade secret laws. You may not view, use, disclose, copy, or distribute 
// this file or any information contained herein except pursuant to a 
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2017, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//    #      #####   #######  ###  #######  #     #  ######   #     #  #######
//   # #    #     #     #      #   #     #  ##    #  #     #  ##    #     #
//  #   #   #           #      #   #     #  # #   #  #     #  # #   #     #
// #     #  #           #      #   #     #  #  #  #  ######   #  #  #     #
// #######  #           #      #   #     #  #   # #  #        #   # #     #
// #     #  #     #     #      #   #     #  #    ##  #        #    ##     #
// #     #   #####      #     ###  #######  #     #  #        #     #     #
//
// ===========================================================================
//
// Description:
//
//  This module implements the configurable Actionpoints unit of the
//  ARCv2HS CPU.
// 
//  Pipeline (5-stage) for AP 
//  Post-commit w.r.t AR : Architectural AP Aux
//    AR :    A1,      A2,       A3,     A4,        A5
//    AP : Match, Trigger, Raise Ex, Commit, Writeback
//    BP :    X1,      X2,       X3,     CA,        WA
//    WP :    W1,      W2,       W3,     W4,        W5
//
//  This .vpp source file may be pre-processed with the Verilog Pre-Processor
//  (VPP) to produce the equivalent .v file using a command such as:
//
//   vpp +q +o alb_actionpoints.vpp
//
// ==========================================================================
//
// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"
`include "const.def"
// 
//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: {clk : "edc_clk" , ap_unit_clk : "edc_unit_clk" , ap_aux_clk : "edc_aux_clk"}, rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_actionpoints (

  ////////// General input signals /////////////////////////////////////////
  //
  input                       ap_unit_clk,          // AP Unit Clock
  input                       ap_aux_clk,           // AP Aux  Clock
  input                       rst_a,                // Async Reset
  // Clock Gating Signals
  input                       aux_aps_active,       // AP AUX  active
  output reg                  ap_unit_enable,       // AP Unit active

  ////////// Auxiliary Interface signals ///////////////////////////////////
  //
  // Aux Write Interface
  input                       aux_aps_wen_r,        // Aux Write En
  input      [4:0]            aux_aps_waddr_r,      // Aux write address
  input      [`npuarc_DATA_RANGE]    wa_sr_data_r,    // Aux write data
  // Aux Read Interface
  input                       aux_aps_ren_r,        // Aux Read En
  input      [4:0]            aux_aps_raddr_r,      // Aux Read address
  input                       aux_write,            // Aux write op
  output reg [`npuarc_DATA_RANGE]    aps_aux_rdata,        // Aux Read Data
  output reg                  aps_aux_illegal,      // SR/LR op is illegal
  output reg                  aps_aux_k_rd,         // op needs Kernel R perm
  output reg                  aps_aux_k_wr,         // op needs Kernel W perm
  output reg                  aps_aux_unimpl,       // Aux Reg not present
  output reg                  aps_aux_serial_sr,    // SR need serialize pipe
  output reg                  aps_aux_strict_sr,    // SR must serialize pipe

  ////////// Interface for detecting Actionpoint triggers //////////////////
  //
  // AP Exception Trigger 
  input      [`npuarc_INTEVT_RANGE]  excpn_evts       ,    // Excep Events
  input                       excpn_in_cg0     ,    // Excep Clock gate
  input                       excpn_in_prologue_nxt,// Excep in Prolg
  input                       excpn_in_prologue,    // Excep in Prolg
  input                       int_load_active_nxt,  // Interrupt pending, next cycle
  input                       int_load_active,      // Interrupt pending

  input                       ap_excpn_holdup, 

  ////////// Architectural state ///////////////////////////////////////////
  //
  input  [`npuarc_PC_RANGE]          ar_pc_r          ,    // AR PC for WP
  input  [`npuarc_DATA_RANGE]        ar_aux_status32_r,    // AR STATUS32
  input  [`npuarc_DATA_RANGE]        ar_aux_erstatus_r,    //
  input  [`npuarc_DATA_RANGE]        ar_aux_debug_r   ,    // AR Debug
  input                       ar_ae_r          ,    // AR STATUS32.AE bit
  input  [`npuarc_APS_RANGE]         ar_asr_r         ,    // ASR field of Debug
  input  [`npuarc_DATA_RANGE]        ar_aux_ecr_r     ,    // AR ECR
  input                       sys_halt_r       ,    // CPU is halted
  input                       db_active        ,    // Debug op. in progress
  input                       pipe_block_ints  ,    //

  ////////// CORE Pipeline Control /////////////////////////////////////////
  //
  input                       x1_pass,         // X1 Pass
  input       [`npuarc_PC_RANGE]     x1_pc_r,         // Breakpoint PC
  input                       x1_uop_inst_r,   // X1 UOP op
  input                       x1_iprot_viol_r, // X1 IPROT viol
  input                       x2_pass,         // X2 Pass
  input                       x2_enable,       // X2 Enable
  input                       x2_kill,         // X2 Kill
  input                       x2_uop_inst_r  , // X2 UOP seq
  input                       x2_lr_op_r,      // X2 LR op
  input                       x2_sr_op_r,      // X2 SR op
  input       [`npuarc_DATA_RANGE]   x2_aux_addr_r,   // X2 Aux addr
  input                       x2_load_r,       // X2 LD op
  input                       x2_store_r,      // X2 ST op
  input       [`npuarc_ADDR_RANGE]   x2_mem_addr_r,   // X2 Mem addr
  input                       x3_pass,         // X3 Pass
  input                       x3_enable,       // X3 Enable
  input                       x3_kill,         // X3 Kill
  input                       x3_lr_op_r,      // X3 LR 
  input                       x3_sr_op_r,      // X3 SR 
  input                       x3_load_r,       // X3 LD 
  input                       x3_store_r,      // X3 ST 
  output                      x3_aps_break_r,  // X3 Halt on AP BP
  output                      x3_aps_halt_r,   // X3 Halt on AP WP
  input                       ca_pass,         // CA Pass
  input                       ca_kill,         // CA Kill
  input                       ca_enable,       // CA Enable
  input                       ca_valid_r,      // CA Valid
  input                       ca_uop_active_r, // CA UOP active
  input                       ca_uop_active_nxt, // CA UOP active (next cycle)
  input                       ca_cmt_brk_evt,  // AP Break Ack
  input                       ca_ap_excpn_r,   // AP Excpn Ack
  input                       ca_lr_op_r,      // CA LR op
  input                       ca_sr_op_r,      // CA SR op
  input                       ca_load_r,       // CA LD op
  input                       ca_store_r,      // CA ST op
  input                       ar_pc_pass, 
  input                       ca_uop_commit_r, 
  input                       ca_cmt_uop_evt,
  input                       ca_uop_state_cg0,     // CA UOP CG
  input     [`npuarc_PFLAG_RANGE]    wa_aux_status32_nxt,  // CA STATUS32 next state
  input                       wa_aux_status32_pass, // CA updates STATUS32

  input                       wa_enable,       // Enable
  input       [`npuarc_PC_RANGE]     wa_pc,           // Watchpoint PC
  input                       wa_lr_op_r,      // LR 
  input                       wa_sr_op_r,      // SR
  input                       wa_rf_wenb0_r,   // AUX RF WR PORT
  input                       wa_store_r,        // Store
  input                       wa_load_r,         // Load
  input                       wa_pref_r,         // Prefetch



  ////////// Actionpoints output signals ///////////////////////////////////
  //
  output                      aps_hit_if,      // Hit on I-fetch AP
  output                      aps_hit_mr,   // Hit on Mem or aux-reg AP
  output      [`npuarc_APNUM_RANGE]  aps_active,      // Identity of active hit
  output                      aps_pcbrk,       // Break due to PC match
  output                      aps_halt_ack,    // AP module ready for halt
  output                      aps_halt,        // Halt due to AP match
  output                      aps_break,       // Break due to AP match
  output reg                  ap_tkn,
  output      [`npuarc_APS_RANGE]    aps_status    ,       // All triggered Actionpoints
  output reg                  aps_asr_serial,       // SR need clear ASR
  output reg  [`npuarc_APS_RANGE]    aps_aux_written       // Indicates write to AP[i]
); 

parameter AT_INST_ADDR   = 4'b0000;
parameter AT_INST_DATA   = 4'b0001;
parameter AT_LDST_ADDR   = 4'b0010;
parameter AT_LDST_DATA   = 4'b0011;
parameter AT_AUXS_ADDR   = 4'b0100;
parameter AT_AUXS_DATA   = 4'b0101;
parameter AT_E_PARAM_0   = 4'b0110;
parameter AT_E_PARAM_1   = 4'b0111;
parameter AT_INST_TYPE   = 3'b000;
parameter AT_EXT_TYPE    = 3'b011;

parameter APNUM_0        = `npuarc_APNUM_SIZE'd0;
parameter APNUM_1        = `npuarc_APNUM_SIZE'd1;
parameter APNUM_2        = `npuarc_APNUM_SIZE'd2;
parameter APNUM_3        = `npuarc_APNUM_SIZE'd3;
parameter APNUM_4        = `npuarc_APNUM_SIZE'd4;
parameter APNUM_5        = `npuarc_APNUM_SIZE'd5;
parameter APNUM_6        = `npuarc_APNUM_SIZE'd6;
parameter APNUM_7        = `npuarc_APNUM_SIZE'd7;

wire                   da_swap = 1'b0;
reg                           ca_bp_halt     ; // 
reg                           ca_bp_excpn     ; // 
reg                           ca_wp_halt     ; // 
reg                           ca_wp_excpn     ; // 
reg                           x3_bp_halt     ; // 
reg                           x3_bp_excpn     ; // 
reg                           x3_wp_halt     ; // 
reg                           x3_wp_excpn     ; // 

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Auxiliary registers, next state, select and write enable signals       //
//                                                                        //
// With a few exceptions, all auxiliary registers are dealt with in a     //
// regular form. For each aux reg, there are a number of flip-flops       //
// to hold the required bits, a next state wire or reg signal that has    //
// the updating value, a select signal decoded from the 12-bit base aux   //
// address on a pending SR op, and a write enable signal that allows      //
// the update to the register content.                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg       [`npuarc_DATA_RANGE]       ap_amv0_r;       // AP_AMV register
reg       [`npuarc_DATA_RANGE]       ap_amv0_nxt;     // next AP_AMV value
reg                           ap_amv0_sr;      // AP_AMV SR write enable
reg                           ap_amv0_wen;     // AP_AMV reg write enable

reg       [`npuarc_DATA_RANGE]       ap_amm0_r;       // AP_AMM register
reg                           ap_amm0_wen;     // AP_AMM write enable

reg       [`npuarc_APAC_RANGE]       ap_ac0_r;        // AP_AC register
reg                           ap_ac0_wen;      // AP_AC write enable
reg                           ap_ac0_wen_r;    // AP_AC write enable

reg       [`npuarc_APAC_RANGE]       ap2_ac0_r;       // AP2_AC register

reg       [`npuarc_DATA_RANGE]       ap_amv1_r;       // AP_AMV register
reg       [`npuarc_DATA_RANGE]       ap_amv1_nxt;     // next AP_AMV value
reg                           ap_amv1_sr;      // AP_AMV SR write enable
reg                           ap_amv1_wen;     // AP_AMV reg write enable

reg       [`npuarc_DATA_RANGE]       ap_amm1_r;       // AP_AMM register
reg                           ap_amm1_wen;     // AP_AMM write enable

reg       [`npuarc_APAC_RANGE]       ap_ac1_r;        // AP_AC register
reg                           ap_ac1_wen;      // AP_AC write enable
reg                           ap_ac1_wen_r;    // AP_AC write enable

reg       [`npuarc_APAC_RANGE]       ap2_ac1_r;       // AP2_AC register

reg       [`npuarc_DATA_RANGE]       ap_amv2_r;       // AP_AMV register
reg       [`npuarc_DATA_RANGE]       ap_amv2_nxt;     // next AP_AMV value
reg                           ap_amv2_sr;      // AP_AMV SR write enable
reg                           ap_amv2_wen;     // AP_AMV reg write enable

reg       [`npuarc_DATA_RANGE]       ap_amm2_r;       // AP_AMM register
reg                           ap_amm2_wen;     // AP_AMM write enable

reg       [`npuarc_APAC_RANGE]       ap_ac2_r;        // AP_AC register
reg                           ap_ac2_wen;      // AP_AC write enable
reg                           ap_ac2_wen_r;    // AP_AC write enable

reg       [`npuarc_APAC_RANGE]       ap2_ac2_r;       // AP2_AC register

reg       [`npuarc_DATA_RANGE]       ap_amv3_r;       // AP_AMV register
reg       [`npuarc_DATA_RANGE]       ap_amv3_nxt;     // next AP_AMV value
reg                           ap_amv3_sr;      // AP_AMV SR write enable
reg                           ap_amv3_wen;     // AP_AMV reg write enable

reg       [`npuarc_DATA_RANGE]       ap_amm3_r;       // AP_AMM register
reg                           ap_amm3_wen;     // AP_AMM write enable

reg       [`npuarc_APAC_RANGE]       ap_ac3_r;        // AP_AC register
reg                           ap_ac3_wen;      // AP_AC write enable
reg                           ap_ac3_wen_r;    // AP_AC write enable

reg       [`npuarc_APAC_RANGE]       ap2_ac3_r;       // AP2_AC register

reg       [`npuarc_DATA_RANGE]       ap_amv4_r;       // AP_AMV register
reg       [`npuarc_DATA_RANGE]       ap_amv4_nxt;     // next AP_AMV value
reg                           ap_amv4_sr;      // AP_AMV SR write enable
reg                           ap_amv4_wen;     // AP_AMV reg write enable

reg       [`npuarc_DATA_RANGE]       ap_amm4_r;       // AP_AMM register
reg                           ap_amm4_wen;     // AP_AMM write enable

reg       [`npuarc_APAC_RANGE]       ap_ac4_r;        // AP_AC register
reg                           ap_ac4_wen;      // AP_AC write enable
reg                           ap_ac4_wen_r;    // AP_AC write enable

reg       [`npuarc_APAC_RANGE]       ap2_ac4_r;       // AP2_AC register

reg       [`npuarc_DATA_RANGE]       ap_amv5_r;       // AP_AMV register
reg       [`npuarc_DATA_RANGE]       ap_amv5_nxt;     // next AP_AMV value
reg                           ap_amv5_sr;      // AP_AMV SR write enable
reg                           ap_amv5_wen;     // AP_AMV reg write enable

reg       [`npuarc_DATA_RANGE]       ap_amm5_r;       // AP_AMM register
reg                           ap_amm5_wen;     // AP_AMM write enable

reg       [`npuarc_APAC_RANGE]       ap_ac5_r;        // AP_AC register
reg                           ap_ac5_wen;      // AP_AC write enable
reg                           ap_ac5_wen_r;    // AP_AC write enable

reg       [`npuarc_APAC_RANGE]       ap2_ac5_r;       // AP2_AC register

reg       [`npuarc_DATA_RANGE]       ap_amv6_r;       // AP_AMV register
reg       [`npuarc_DATA_RANGE]       ap_amv6_nxt;     // next AP_AMV value
reg                           ap_amv6_sr;      // AP_AMV SR write enable
reg                           ap_amv6_wen;     // AP_AMV reg write enable

reg       [`npuarc_DATA_RANGE]       ap_amm6_r;       // AP_AMM register
reg                           ap_amm6_wen;     // AP_AMM write enable

reg       [`npuarc_APAC_RANGE]       ap_ac6_r;        // AP_AC register
reg                           ap_ac6_wen;      // AP_AC write enable
reg                           ap_ac6_wen_r;    // AP_AC write enable

reg       [`npuarc_APAC_RANGE]       ap2_ac6_r;       // AP2_AC register

reg       [`npuarc_DATA_RANGE]       ap_amv7_r;       // AP_AMV register
reg       [`npuarc_DATA_RANGE]       ap_amv7_nxt;     // next AP_AMV value
reg                           ap_amv7_sr;      // AP_AMV SR write enable
reg                           ap_amv7_wen;     // AP_AMV reg write enable

reg       [`npuarc_DATA_RANGE]       ap_amm7_r;       // AP_AMM register
reg                           ap_amm7_wen;     // AP_AMM write enable

reg       [`npuarc_APAC_RANGE]       ap_ac7_r;        // AP_AC register
reg                           ap_ac7_wen;      // AP_AC write enable
reg                           ap_ac7_wen_r;    // AP_AC write enable

reg       [`npuarc_APAC_RANGE]       ap2_ac7_r;       // AP2_AC register

reg                           ap1_ar_ub_r;        // UB Enable on AR
reg                           ap1_ar_ub_nxt;      // UB Enable on AR
reg                           ap1_ar_cg;          // UB Enable on AR
reg                           ap2_ar_ub_r;        // UB Enable on AR
reg                           ap2_ar_ub_nxt;      // UB Enable on AR
reg                           ap2_ar_cg;          // UB Enable on AR
reg                           ap3_ar_ub_r;        // UB Enable on AR
reg                           ap3_ar_ub_nxt;      // UB Enable on AR
reg                           ap3_ar_cg;          // UB Enable on AR
reg                           ap4_ar_ub_r;        // UB Enable on AR
reg                           ap4_ar_ub_nxt;      // UB Enable on AR
reg                           ap4_ar_cg;          // UB Enable on AR
reg       [`npuarc_DATA_RANGE]       x3_addr_r;          // Watchpoint address value
reg       [`npuarc_DATA_RANGE]       ca_addr_r;          // Watchpoint address value
reg       [`npuarc_DATA_RANGE]       wa_addr_r;          // Watchpoint address value

reg                           ap1_stat32_ae_r;    // Watchpoint op AE status

reg                           ap1_valid_op_r;     // Watchpoint op is valid

reg                           ap1_valid_op_nxt;   // next valid register
reg                           x3_addr_op_nxt;     // Incoming address operation

reg  [`npuarc_PC_RANGE]               wp_pc_r;              // Watchpoint PC
reg  [`npuarc_PC_RANGE]               wp_pc_nxt;            // Watchpoint PC NXT
reg                            wp_pc_cg;             // Watchpoint PC CG

reg                           x3_hit_if_r;        // Hit on I-fetch AP
reg                           x3_hit_mr_r;        // Hit on Mem or aux-reg AP
reg                           x3_hit_md_r;        // Hit on Mem or aux-reg data AP
reg                           x3_pcbrk_r;         // Halt on AP BP
reg                           x3_break_r;         // Halt on AP BP
reg                           x3_halt_r;          // Halt on AP WP

reg                           ca_break_r;         // AP Break commit
reg                           ca_pcbrk_r;         // AP Break commit
reg                           ca_halt_ack;

reg                           aps_halt_r;         // Halt due to AP match
reg       [`npuarc_APNUM_RANGE]      aps_active_r;       // Identity of active hit
reg       [`npuarc_APS_RANGE]        aps_status_r;       // All triggered Actionpoints
reg                           aps_status_cg;      // 
reg                           aps_pcbrk1_r;       // Retimed from aps_pcbrk_r

reg                           x3_hit_if_nxt;
reg                           x3_hit_mr_nxt;
reg                           x3_hit_md_nxt;
reg                           x3_break_nxt;
reg                           x3_halt_nxt;
reg                           x3_pcbrk_nxt;

reg                           ca_break_nxt;
reg                           ca_pcbrk_nxt;

reg                           aps_halt_nxt;
wire                          aps_pcbrk1_nxt; // Retimed from aps_pcbrk_r

reg  [`npuarc_APNUM_RANGE]           aps_active_comp;

reg  [`npuarc_APNUM_RANGE]           aps_active_nxt;
reg  [`npuarc_APS_RANGE]             aps_status_nxt;
reg                           aps_raw_cg;
reg                           aps_cg;

reg                           x3_hit_if_cg;
reg                           x3_hit_mr_cg;
reg                           x3_hit_md_cg;

reg  [`npuarc_PC_RANGE]              x2_pc_r;       // X2 PC
//
////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Param signals                                                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
//
//
////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Watch Point signals                                                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
//
reg                           wa2_lr_op_r;        // WA2 LR 
reg                           wa2_sr_op_r;        // WA2 SR
reg                           wa2_ast_r;       // WA2 Store
reg                           wa2_ald_r;        // WA2 LD 
reg                           wa2_ast_nxt;     // WA2 Store
reg                           wa2_ald_nxt;      // WA2 LD 
reg                           wa2_ast_cg;      // WA2 Store
reg                           wa2_ald_cg;       // WA2 LD 
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Actionpoints pipeline flow-control signals and pipeline enables        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
reg                           sys_halt_2r;

reg                           ap_dis_ntrig ;      // Disable New Triggers

reg                           aps_pending;

reg                           ap1_ctrl_en;        // Enable ap1_valid_op_r 
reg                           x3_addr_en;         // Enable x3_addr_r

reg                           ap1_enable;         // Top-level ap1 enable
reg                           ap1_pass;           // Pass ap1 to ap2

reg  [`npuarc_APS_RANGE]             ap_en         ;
reg  [`npuarc_APS_RANGE]             x3_ap_en_nxt  ;
reg                           ap_pipe_active     ;
reg                           ap_enb_ext_r       ; // Extend ap_unit_enable if needed
reg                           ap_enb_ext_nxt     ; // 

//
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Actionpoints pipeline flow- data                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//
reg  [`npuarc_PC_RANGE]         x2_wppc_r       ; // X2 WPPC
reg  [`npuarc_PC_RANGE]         x3_wppc_r       ; // X3 WPPC
reg  [`npuarc_PC_RANGE]         x3_wppc_nxt     ; // CA WPPC NXT
reg  [`npuarc_PC_RANGE]         ca_wppc_r       ; // CA WPPC
//
reg       [`npuarc_DATA_RANGE]       x2_amv0_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       x3_amv0_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       ca_amv0_r;      // CA_AMV register
reg       [`npuarc_DATA_RANGE]       x2_amv1_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       x3_amv1_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       ca_amv1_r;      // CA_AMV register
reg       [`npuarc_DATA_RANGE]       x2_amv2_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       x3_amv2_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       ca_amv2_r;      // CA_AMV register
reg       [`npuarc_DATA_RANGE]       x2_amv3_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       x3_amv3_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       ca_amv3_r;      // CA_AMV register
reg       [`npuarc_DATA_RANGE]       x2_amv4_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       x3_amv4_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       ca_amv4_r;      // CA_AMV register
reg       [`npuarc_DATA_RANGE]       x2_amv5_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       x3_amv5_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       ca_amv5_r;      // CA_AMV register
reg       [`npuarc_DATA_RANGE]       x2_amv6_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       x3_amv6_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       ca_amv6_r;      // CA_AMV register
reg       [`npuarc_DATA_RANGE]       x2_amv7_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       x3_amv7_r;      // X2_AMV register
reg       [`npuarc_DATA_RANGE]       ca_amv7_r;      // CA_AMV register

reg       [`npuarc_APS_RANGE]        x3_trig_comp;
reg       [`npuarc_APS_RANGE]        x3_trig_nxt ;
reg       [`npuarc_APS_RANGE]        x3_trig_r   ;
reg       [`npuarc_APS_RANGE]        x3_trigg_r  ;
reg       [`npuarc_APS_RANGE]        x3_bps_r    ; // X3 breakpoints

reg       [`npuarc_APS_RANGE]        x2_trig_comp;
reg       [`npuarc_APS_RANGE]        ca_trig_nxt ;
reg       [`npuarc_APS_RANGE]        ca_trig     ;

reg                           any_pc_addr;
reg                           any_sr_addr;
reg                           any_lr_addr;
reg                           any_st_addr;
reg                           any_ld_addr;

reg     [`npuarc_DATA_RANGE]         pc_value;


reg     [`npuarc_APS_RANGE]          tt_read;
reg     [`npuarc_APS_RANGE]          tt_write;
reg     [`npuarc_APS_RANGE]          mode;
reg     [`npuarc_APS_RANGE]          paired;
reg     [`npuarc_APS_RANGE]          action;
reg     [`npuarc_APS_RANGE]          quad;

reg     [`npuarc_APS_RANGE]          brkpt_en;   // Breakpoint trigger enables
reg     [`npuarc_APS_RANGE]          wchpt_en;   // Watchpoint trigger enables

reg                           wa_st_retire; 
reg                           wa_st_nopost; 
reg                           wa_ld_retire; 
reg                           wa_ld_nopost; 
reg  [`npuarc_APS_RANGE]             x1_cond; // APS condition met at X1 stage
reg                           x2_cond_nxt;
reg                           x2_cond_r;
reg  [`npuarc_DATA_RANGE]            mvalue_0;
reg  [`npuarc_DATA_RANGE]            bitand_0;
reg  [`npuarc_DATA_RANGE]            bitor_0;
reg  [`npuarc_DATA_RANGE]            mvalue_1;
reg  [`npuarc_DATA_RANGE]            bitand_1;
reg  [`npuarc_DATA_RANGE]            bitor_1;
reg  [`npuarc_DATA_RANGE]            mvalue_2;
reg  [`npuarc_DATA_RANGE]            bitand_2;
reg  [`npuarc_DATA_RANGE]            bitor_2;
reg  [`npuarc_DATA_RANGE]            mvalue_3;
reg  [`npuarc_DATA_RANGE]            bitand_3;
reg  [`npuarc_DATA_RANGE]            bitor_3;
reg  [`npuarc_DATA_RANGE]            mvalue_4;
reg  [`npuarc_DATA_RANGE]            bitand_4;
reg  [`npuarc_DATA_RANGE]            bitor_4;
reg  [`npuarc_DATA_RANGE]            mvalue_5;
reg  [`npuarc_DATA_RANGE]            bitand_5;
reg  [`npuarc_DATA_RANGE]            bitor_5;
reg  [`npuarc_DATA_RANGE]            mvalue_6;
reg  [`npuarc_DATA_RANGE]            bitand_6;
reg  [`npuarc_DATA_RANGE]            bitor_6;
reg  [`npuarc_DATA_RANGE]            mvalue_7;
reg  [`npuarc_DATA_RANGE]            bitand_7;
reg  [`npuarc_DATA_RANGE]            bitor_7;
reg     [`npuarc_APS_RANGE]          match;      // vector of raw AP matches
reg     [`npuarc_APS_RANGE]          match_r;    // vector of raw AP matches
reg     [`npuarc_APS_RANGE]          match_nxt;  // vector of raw AP matches
reg     [`npuarc_APS_RANGE]          match_cg;   // vector of raw AP matches
reg     [`npuarc_APS_RANGE]          match_vld_r; // Match is valid
reg     [`npuarc_APS_RANGE]          match_vld_nxt; // Match is valid
reg     [`npuarc_APS_RANGE]          mema_type;   // vector of Mem Address Type
reg     [`npuarc_APS_RANGE]          aux_type;   // vector of enabling type conditions
reg     [`npuarc_APS_RANGE]          inst_type;  // INST  slot Type detected

reg     [`npuarc_APS_RANGE]          wa_asr_r;   // Delayed ASR


reg                           i_halt_nxt; // Unqualified halt signal
reg     [`npuarc_APS_RANGE]          cond;       // vector of enabling type conditions
reg     [`npuarc_APS_RANGE]          hit;        // combined matches and enables
reg     [`npuarc_APS_RANGE]          trig;       // vector of triggered primary APs
reg     [`npuarc_APS_RANGE]          reloadamv;  // reload enables for each AP_AMVi
reg                           reload_pc ;  // reload enables for each WP PC

reg     [`npuarc_APS_RANGE]          if_ap;      // vector indicating breakpoint APs
reg     [`npuarc_APS_RANGE]          md_ap;      // vector indicating breakpoint APs
// Conditions 
reg                      trig_any_ap   ;
reg                      trig_any_h_wp ;
reg                      ca_ap_halt_cmt;
reg                      ca_ap_halt_ack;
reg                      ca_ap_expn_ack;
reg                      ap_done       ;
// Pipe control
reg                      x3_ap_pass    ;
reg                      ca_ap_pass    ;
reg                      ap_uop_act_r  ; 
reg                      ap_uop_act_nxt; 
reg                      ap_uop_act_cg  ; 
// ap_pend
reg                      ap_pend_nxt       ;
reg                      ap_pend_cg        ;
reg                      ap_pend_r         ;
reg                      ca_bp_nxt       ;
reg                ca_bp_cg        ;
reg                      ca_bp_r         ;
reg                      ca_dt_nxt       ;
reg [`npuarc_APS_RANGE]               ca_dt_cg        ;
reg                      ca_dt_r         ;
reg                      ca_dt_raw_cg    ;
reg                      ca_ex_nxt       ;
reg                ca_ex_cg        ;
reg                      ca_ex_r         ;
reg                      x3_bp_nxt       ;
reg                x3_bp_cg        ;
reg                      x3_bp_r         ;
reg                      x3_dt_nxt       ;
reg [`npuarc_APS_RANGE]               x3_dt_cg        ;
reg                      x3_dt_r         ;
reg                      x3_dt_raw_cg    ;
reg                      x3_ex_nxt       ;
reg                x3_ex_cg        ;
reg                      x3_ex_r         ;

reg  [`npuarc_APS_RANGE]        x3_ap_pend         ; // AP pending
reg                      ap_pend_any        ;
reg                      dis_ap_chk_all     ;
reg                      x3_pass_any        ;
reg                      x3_break_cg   ;
reg                      x3_halt_cg    ;
reg                      ca_break_cg   ;
reg                      ca_halt_cg    ;
reg                      x3_addr_cg    ;
reg                      ca_addr_cg    ;
reg                      wa_addr_cg    ;
reg       [`npuarc_DATA_RANGE]  x3_addr_nxt   ; // next Watchpoint address
reg                      x2_aux_op     ; // X2 Aux op (SR or LR)
reg       [`npuarc_APS_RANGE]   match_raw_cg;

reg                      clear_pend_ap_cg;
reg       [`npuarc_APS_RANGE]   clear_pend_ap_nxt;
reg                      clear_pend_ap_r;
reg                      excpn_epil_u_bit;
reg                      excpn_epil_u_bit_r;
// 

//
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for selecting aux register values for LR and SR     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : ap_aux_read_PROC

  aps_aux_rdata   = `npuarc_DATA_SIZE'd0;
  aps_aux_k_rd      = 1'b0;
  aps_aux_k_wr      = 1'b0;
  aps_aux_unimpl    = 1'b1;
  aps_aux_illegal   = 1'b0;
  aps_aux_serial_sr = 1'b0;
  aps_aux_strict_sr = 1'b0;

  case (1'b1)

  aux_aps_ren_r: // Action Points Aux Space
  begin
    
    case ({7'h11, aux_aps_raddr_r})

        12'd544 :           // K_RW
        begin
          aps_aux_rdata       = ap_amv0_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd545 :           // K_RW
        begin
          aps_aux_rdata       = ap_amm0_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd546 :           // K_RW
        begin
          aps_aux_rdata[`npuarc_APAC_RANGE] = ap_ac0_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end
        12'd547 :           // K_RW
        begin
          aps_aux_rdata       = ap_amv1_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd548 :           // K_RW
        begin
          aps_aux_rdata       = ap_amm1_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd549 :           // K_RW
        begin
          aps_aux_rdata[`npuarc_APAC_RANGE] = ap_ac1_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end
        12'd550 :           // K_RW
        begin
          aps_aux_rdata       = ap_amv2_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd551 :           // K_RW
        begin
          aps_aux_rdata       = ap_amm2_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd552 :           // K_RW
        begin
          aps_aux_rdata[`npuarc_APAC_RANGE] = ap_ac2_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end
        12'd553 :           // K_RW
        begin
          aps_aux_rdata       = ap_amv3_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd554 :           // K_RW
        begin
          aps_aux_rdata       = ap_amm3_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd555 :           // K_RW
        begin
          aps_aux_rdata[`npuarc_APAC_RANGE] = ap_ac3_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end
        12'd556 :           // K_RW
        begin
          aps_aux_rdata       = ap_amv4_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd557 :           // K_RW
        begin
          aps_aux_rdata       = ap_amm4_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd558 :           // K_RW
        begin
          aps_aux_rdata[`npuarc_APAC_RANGE] = ap_ac4_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end
        12'd559 :           // K_RW
        begin
          aps_aux_rdata       = ap_amv5_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd560 :           // K_RW
        begin
          aps_aux_rdata       = ap_amm5_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd561 :           // K_RW
        begin
          aps_aux_rdata[`npuarc_APAC_RANGE] = ap_ac5_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end
        12'd562 :           // K_RW
        begin
          aps_aux_rdata       = ap_amv6_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd563 :           // K_RW
        begin
          aps_aux_rdata       = ap_amm6_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd564 :           // K_RW
        begin
          aps_aux_rdata[`npuarc_APAC_RANGE] = ap_ac6_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end
        12'd565 :           // K_RW
        begin
          aps_aux_rdata       = ap_amv7_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd566 :           // K_RW
        begin
          aps_aux_rdata       = ap_amm7_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end

        12'd567 :           // K_RW
        begin
          aps_aux_rdata[`npuarc_APAC_RANGE] = ap_ac7_r;
          aps_aux_k_wr        = 1'b1;
          aps_aux_k_rd        = 1'b1;
          aps_aux_strict_sr   = aux_write;
          aps_aux_unimpl      = 1'b0;
        end
        `npuarc_AP_WP_PC:        // K_R
        begin
          aps_aux_rdata[`npuarc_PC_RANGE] = wp_pc_r;
          aps_aux_k_rd             = 1'b1;
          aps_aux_illegal          = aux_write;
          aps_aux_unimpl           = 1'b0;
        end
        
      default:
      begin
        aps_aux_rdata   = `npuarc_DATA_SIZE'd0;
        aps_aux_k_rd      = 1'b0;
        aps_aux_k_wr      = 1'b0;
        aps_aux_unimpl    = 1'b1;
        aps_aux_illegal   = 1'b0;
        aps_aux_serial_sr = 1'b0;
        aps_aux_strict_sr = 1'b0;
      end
    endcase
  end

    default:
    begin
      aps_aux_rdata   = `npuarc_DATA_SIZE'd0;
      aps_aux_k_rd      = 1'b0;
      aps_aux_k_wr      = 1'b0;
      aps_aux_unimpl    = 1'b1;
      aps_aux_illegal   = 1'b0;
      aps_aux_serial_sr = 1'b0;
      aps_aux_strict_sr = 1'b0;
    end
  endcase // AP Aux Registers
  
end // block : ap_aux_read_PROC

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational logic for selecting an SR                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aps_aux_wen_PROC

  aps_asr_serial   = 1'b0;
  aps_aux_written[0] = 1'b0;
  ap_amv0_sr       = 1'b0;
  ap_amm0_wen      = 1'b0;
  ap_ac0_wen       = 1'b0;
  aps_aux_written[1] = 1'b0;
  ap_amv1_sr       = 1'b0;
  ap_amm1_wen      = 1'b0;
  ap_ac1_wen       = 1'b0;
  aps_aux_written[2] = 1'b0;
  ap_amv2_sr       = 1'b0;
  ap_amm2_wen      = 1'b0;
  ap_ac2_wen       = 1'b0;
  aps_aux_written[3] = 1'b0;
  ap_amv3_sr       = 1'b0;
  ap_amm3_wen      = 1'b0;
  ap_ac3_wen       = 1'b0;
  aps_aux_written[4] = 1'b0;
  ap_amv4_sr       = 1'b0;
  ap_amm4_wen      = 1'b0;
  ap_ac4_wen       = 1'b0;
  aps_aux_written[5] = 1'b0;
  ap_amv5_sr       = 1'b0;
  ap_amm5_wen      = 1'b0;
  ap_ac5_wen       = 1'b0;
  aps_aux_written[6] = 1'b0;
  ap_amv6_sr       = 1'b0;
  ap_amm6_wen      = 1'b0;
  ap_ac6_wen       = 1'b0;
  aps_aux_written[7] = 1'b0;
  ap_amv7_sr       = 1'b0;
  ap_amm7_wen      = 1'b0;
  ap_ac7_wen       = 1'b0;

  case (1'b1)

  aux_aps_wen_r:
  begin
    case ({7'h11, aux_aps_waddr_r})
        12'd544 :           // K_RW
        begin
          ap_amv0_sr       = 1'b1;
          aps_aux_written[0] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd545 :           // K_RW
        begin
          ap_amm0_wen      = 1'b1;
          aps_aux_written[0] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd546 :           // K_RW
        begin
          ap_ac0_wen       = 1'b1;
          aps_aux_written[0] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end
        12'd547 :           // K_RW
        begin
          ap_amv1_sr       = 1'b1;
          aps_aux_written[1] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd548 :           // K_RW
        begin
          ap_amm1_wen      = 1'b1;
          aps_aux_written[1] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd549 :           // K_RW
        begin
          ap_ac1_wen       = 1'b1;
          aps_aux_written[1] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end
        12'd550 :           // K_RW
        begin
          ap_amv2_sr       = 1'b1;
          aps_aux_written[2] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd551 :           // K_RW
        begin
          ap_amm2_wen      = 1'b1;
          aps_aux_written[2] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd552 :           // K_RW
        begin
          ap_ac2_wen       = 1'b1;
          aps_aux_written[2] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end
        12'd553 :           // K_RW
        begin
          ap_amv3_sr       = 1'b1;
          aps_aux_written[3] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd554 :           // K_RW
        begin
          ap_amm3_wen      = 1'b1;
          aps_aux_written[3] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd555 :           // K_RW
        begin
          ap_ac3_wen       = 1'b1;
          aps_aux_written[3] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end
        12'd556 :           // K_RW
        begin
          ap_amv4_sr       = 1'b1;
          aps_aux_written[4] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd557 :           // K_RW
        begin
          ap_amm4_wen      = 1'b1;
          aps_aux_written[4] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd558 :           // K_RW
        begin
          ap_ac4_wen       = 1'b1;
          aps_aux_written[4] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end
        12'd559 :           // K_RW
        begin
          ap_amv5_sr       = 1'b1;
          aps_aux_written[5] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd560 :           // K_RW
        begin
          ap_amm5_wen      = 1'b1;
          aps_aux_written[5] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd561 :           // K_RW
        begin
          ap_ac5_wen       = 1'b1;
          aps_aux_written[5] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end
        12'd562 :           // K_RW
        begin
          ap_amv6_sr       = 1'b1;
          aps_aux_written[6] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd563 :           // K_RW
        begin
          ap_amm6_wen      = 1'b1;
          aps_aux_written[6] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd564 :           // K_RW
        begin
          ap_ac6_wen       = 1'b1;
          aps_aux_written[6] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end
        12'd565 :           // K_RW
        begin
          ap_amv7_sr       = 1'b1;
          aps_aux_written[7] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd566 :           // K_RW
        begin
          ap_amm7_wen      = 1'b1;
          aps_aux_written[7] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end

        12'd567 :           // K_RW
        begin
          ap_ac7_wen       = 1'b1;
          aps_aux_written[7] = 1'b1
                              ;
          aps_asr_serial      = 1'b1;
        end
      default:
      begin
        aps_asr_serial   = 1'b0;
        aps_aux_written[0] = 1'b0;
        ap_amv0_sr       = 1'b0;
        ap_amm0_wen      = 1'b0;
        ap_ac0_wen       = 1'b0;
        aps_aux_written[1] = 1'b0;
        ap_amv1_sr       = 1'b0;
        ap_amm1_wen      = 1'b0;
        ap_ac1_wen       = 1'b0;
        aps_aux_written[2] = 1'b0;
        ap_amv2_sr       = 1'b0;
        ap_amm2_wen      = 1'b0;
        ap_ac2_wen       = 1'b0;
        aps_aux_written[3] = 1'b0;
        ap_amv3_sr       = 1'b0;
        ap_amm3_wen      = 1'b0;
        ap_ac3_wen       = 1'b0;
        aps_aux_written[4] = 1'b0;
        ap_amv4_sr       = 1'b0;
        ap_amm4_wen      = 1'b0;
        ap_ac4_wen       = 1'b0;
        aps_aux_written[5] = 1'b0;
        ap_amv5_sr       = 1'b0;
        ap_amm5_wen      = 1'b0;
        ap_ac5_wen       = 1'b0;
        aps_aux_written[6] = 1'b0;
        ap_amv6_sr       = 1'b0;
        ap_amm6_wen      = 1'b0;
        ap_ac6_wen       = 1'b0;
        aps_aux_written[7] = 1'b0;
        ap_amv7_sr       = 1'b0;
        ap_amm7_wen      = 1'b0;
        ap_ac7_wen       = 1'b0;
      end
    endcase
  end

    default:
    begin
      aps_asr_serial   = 1'b0;
      aps_aux_written[0] = 1'b0;
      ap_amv0_sr       = 1'b0;
      ap_amm0_wen      = 1'b0;
      ap_ac0_wen       = 1'b0;
      aps_aux_written[1] = 1'b0;
      ap_amv1_sr       = 1'b0;
      ap_amm1_wen      = 1'b0;
      ap_ac1_wen       = 1'b0;
      aps_aux_written[2] = 1'b0;
      ap_amv2_sr       = 1'b0;
      ap_amm2_wen      = 1'b0;
      ap_ac2_wen       = 1'b0;
      aps_aux_written[3] = 1'b0;
      ap_amv3_sr       = 1'b0;
      ap_amm3_wen      = 1'b0;
      ap_ac3_wen       = 1'b0;
      aps_aux_written[4] = 1'b0;
      ap_amv4_sr       = 1'b0;
      ap_amm4_wen      = 1'b0;
      ap_ac4_wen       = 1'b0;
      aps_aux_written[5] = 1'b0;
      ap_amv5_sr       = 1'b0;
      ap_amm5_wen      = 1'b0;
      ap_ac5_wen       = 1'b0;
      aps_aux_written[6] = 1'b0;
      ap_amv6_sr       = 1'b0;
      ap_amm6_wen      = 1'b0;
      ap_ac6_wen       = 1'b0;
      aps_aux_written[7] = 1'b0;
      ap_amv7_sr       = 1'b0;
      ap_amm7_wen      = 1'b0;
      ap_ac7_wen       = 1'b0;
    end
  endcase // AP Aux Registers

end // block : aps_aux_wen_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for detecting Actionpoint trigger events            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

   

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Asynchronous logic for Actionpoint matching                            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : aps_brk_PROC

  // Define signals that indicate whether there are any PC or IR based
  // breakpoints defined by the AP_ACi registers currently.
  // These are used to gate the PC and IR values before they go into
  // the comparator network, to save dynamic power. These two signals
  // are dynamically stable, varying only when the Actionpoints are
  // programmed.
  //
  any_pc_addr    = (tt_read[0] & (ap_ac0_r[3:0] == AT_INST_ADDR))
                 | (tt_read[1] & (ap_ac1_r[3:0] == AT_INST_ADDR))
                 | (tt_read[2] & (ap_ac2_r[3:0] == AT_INST_ADDR))
                 | (tt_read[3] & (ap_ac3_r[3:0] == AT_INST_ADDR))
                 | (tt_read[4] & (ap_ac4_r[3:0] == AT_INST_ADDR))
                 | (tt_read[5] & (ap_ac5_r[3:0] == AT_INST_ADDR))
                 | (tt_read[6] & (ap_ac6_r[3:0] == AT_INST_ADDR))
                 | (tt_read[7] & (ap_ac7_r[3:0] == AT_INST_ADDR))
                 ;
                 
end // block : aps_brk_PROC

always @*
begin : aps_addr_PROC

  // Define the signals that indicate whether there are any 
  // enabled Actionpoints of each of the four Watchpoint types
  //
  any_sr_addr    = (tt_write[0] & (ap2_ac0_r[3:0] == AT_AUXS_ADDR))
                 | (tt_write[1] & (ap2_ac1_r[3:0] == AT_AUXS_ADDR))
                 | (tt_write[2] & (ap2_ac2_r[3:0] == AT_AUXS_ADDR))
                 | (tt_write[3] & (ap2_ac3_r[3:0] == AT_AUXS_ADDR))
                 | (tt_write[4] & (ap2_ac4_r[3:0] == AT_AUXS_ADDR))
                 | (tt_write[5] & (ap2_ac5_r[3:0] == AT_AUXS_ADDR))
                 | (tt_write[6] & (ap2_ac6_r[3:0] == AT_AUXS_ADDR))
                 | (tt_write[7] & (ap2_ac7_r[3:0] == AT_AUXS_ADDR))
                 ;
                                  
  any_lr_addr    = (tt_read[0] & (ap2_ac0_r[3:0] == AT_AUXS_ADDR))
                 | (tt_read[1] & (ap2_ac1_r[3:0] == AT_AUXS_ADDR))
                 | (tt_read[2] & (ap2_ac2_r[3:0] == AT_AUXS_ADDR))
                 | (tt_read[3] & (ap2_ac3_r[3:0] == AT_AUXS_ADDR))
                 | (tt_read[4] & (ap2_ac4_r[3:0] == AT_AUXS_ADDR))
                 | (tt_read[5] & (ap2_ac5_r[3:0] == AT_AUXS_ADDR))
                 | (tt_read[6] & (ap2_ac6_r[3:0] == AT_AUXS_ADDR))
                 | (tt_read[7] & (ap2_ac7_r[3:0] == AT_AUXS_ADDR))
                 ;

  any_st_addr    = (tt_write[0] & (ap2_ac0_r[3:0] == AT_LDST_ADDR))
                 | (tt_write[1] & (ap2_ac1_r[3:0] == AT_LDST_ADDR))
                 | (tt_write[2] & (ap2_ac2_r[3:0] == AT_LDST_ADDR))
                 | (tt_write[3] & (ap2_ac3_r[3:0] == AT_LDST_ADDR))
                 | (tt_write[4] & (ap2_ac4_r[3:0] == AT_LDST_ADDR))
                 | (tt_write[5] & (ap2_ac5_r[3:0] == AT_LDST_ADDR))
                 | (tt_write[6] & (ap2_ac6_r[3:0] == AT_LDST_ADDR))
                 | (tt_write[7] & (ap2_ac7_r[3:0] == AT_LDST_ADDR))
                 ;

  any_ld_addr    = (tt_read[0] & (ap2_ac0_r[3:0] == AT_LDST_ADDR))
                 | (tt_read[1] & (ap2_ac1_r[3:0] == AT_LDST_ADDR))
                 | (tt_read[2] & (ap2_ac2_r[3:0] == AT_LDST_ADDR))
                 | (tt_read[3] & (ap2_ac3_r[3:0] == AT_LDST_ADDR))
                 | (tt_read[4] & (ap2_ac4_r[3:0] == AT_LDST_ADDR))
                 | (tt_read[5] & (ap2_ac5_r[3:0] == AT_LDST_ADDR))
                 | (tt_read[6] & (ap2_ac6_r[3:0] == AT_LDST_ADDR))
                 | (tt_read[7] & (ap2_ac7_r[3:0] == AT_LDST_ADDR))
                 ;

  x3_addr_op_nxt = 1'b0
                  | (x2_sr_op_r & any_sr_addr)
                  | (x2_lr_op_r & any_lr_addr)
                  | (x2_store_r & any_st_addr)
                  | (x2_load_r  & any_ld_addr)
                  ;
                 
  // Enable the x3_addr_r register if any address-based Watchpoints
  // are enabled when the operation they depend upon is present in
  // the Commit stage.
  //

  x3_addr_en     = ap1_enable;

end // block : aps_addr_PROC

//
/*
                                                                        //
  Logic block for
  conditions to Update AP Internal Status
  1. AP triggered but not taken
  2. AP taken
    a. Exception taken for AP
    b. Break taken for AP

 AP Triggered Acknowledgement
 1. Break-point only on Pass or Kill
    a. No Watchpoints (Sticky) pending
 2. Any AP Exception taken
*/
//
//
always @*
begin :  ap_cond_PROC

  // Actionpoint
  trig_any_ap     = 1'b1
                       & |trig
                       & !ap_pend_any
                       ;

  // Watchpoint - Halt
  // 1. New Halt WP 
  // 2. Not in AP Halt
  // 3. No old pending
  trig_any_h_wp   = 1'b1
                       & |(trig & (~if_ap) & (~action))
                       & !ar_aux_debug_r[`npuarc_DEBUG_AH]
                       & !ap_pend_any
                       ;


  ca_ap_halt_cmt  = 1'b0
                       | ca_cmt_brk_evt
                       ;

  // The aps_halt_ack signal is asserted whenever the Actionpoints module
  // has no reason to delay the acknowledgement of a halt or debug event.
  // It is not asserted if the ap1 or ap2 stages still have valid matches 
  // that need to be handled before the external halt or debug operation. 
  // However, if the CPU is already halted there is no need to prevent a
  // halt or debug operation from taking place.
  //
  ca_ap_halt_ack  = 1'b1
                       & ( aps_break | aps_halt)
                       & ca_ap_halt_cmt
                       & !ar_aux_status32_r[`npuarc_H_FLAG]
                       ;

  // 1. AP exception committed
  // 2. Breakpoint killed at
  //    a. X3
  //    b. CA or committed non-breakpoint
  ca_ap_expn_ack  = 1'b0
                       | (ca_ap_excpn_r & excpn_evts[`npuarc_INTEVT_PROLOGUE])              // (1)
                       ;

  ap_tkn          =  1'b0
                       | (ca_ap_excpn_r & excpn_evts[`npuarc_INTEVT_PROLOGUE])
                       | ca_ap_halt_ack
                       ;


  // 1. AP exception committed
  // 2. AP halt committed
  // 3. ca_ap_pass
  // 4. Fail safe
  ap_done        =  1'b0
                       | ca_ap_expn_ack           // (1)
                       | ca_ap_halt_ack           // (2)
                       | ca_ap_pass               // (3)
                       | dis_ap_chk_all                // (4)
                       ;

end // block : ap_cond_PROC
//
//
always @*
begin : ap_pend_nxt_PROC

  ap_pend_nxt         = 1'b1
                       & trig_any_ap
                       & !ap_done
                       ;
   
  ap_pend_cg         = 1'b0
                      | trig_any_ap
                      | (ap_done & ap_pend_r)
                      | clear_pend_ap_r
                      | (x3_ap_pass & !ar_aux_debug_r[`npuarc_DEBUG_UB] 
                         & ar_aux_status32_r[`npuarc_U_FLAG] ) //trying to take ap when UB not set and in user mode
                      ;
   
end // block :  ap_pend_nxt_PROC
//
always @(posedge ap_unit_clk or posedge rst_a) 
begin : ap_pend_reg_PROC
  if (rst_a == 1'b1) begin
    ap_pend_r   <= 1'b0;
  end
  else if (ap_pend_cg) begin
    ap_pend_r <= ap_pend_nxt;
  end
end // block : ap_pend_reg_PROC
//
always @*
begin : ap_uop_act_nxt_PROC

  ap_uop_act_cg  =  1'b0
                      |  ca_cmt_uop_evt
                      | (ap_uop_act_r
                        & ar_pc_pass 
                        )
                      ;

  ap_uop_act_nxt =  1'b1
                      &  ca_cmt_uop_evt
                      & !(ar_pc_pass || ca_uop_commit_r)
                      ;

end // block : ap_uop_act_nxt_PROC
//
always @(posedge ap_unit_clk or posedge rst_a) 
begin : ap_uop_act_reg_PROC
  if (rst_a == 1'b1) begin
    ap_uop_act_r <= 1'b1;
  end
  else if (ap_uop_act_cg == 1'b1) begin
    ap_uop_act_r <= ap_uop_act_nxt;
  end
end // block : ap_uop_act_reg_PROC
//
always @*
begin : x3_pipe_ctrl_PROC

  // X3 AP Pass
  // 1. X3 BP Pass
  // 2. X3 BP Kill
  // 3. X3 WP Halt      Pass on any
  // 4. X3 WP Exception - sticky till really taken
  // 5. X3 check ECR for actionpoint and ap tkn then x3 gets cleared
  // 
  x3_ap_pass     = 1'b0
                      | (x3_dt_r &  x3_bp_r &                 x3_pass) // (1)
                      | (x3_dt_r &  x3_bp_r &                 x3_kill) // (2)
                      | (x3_dt_r & !x3_bp_r & !x3_ex_r & x3_pass_any 
                                      & !ca_uop_active_r
                                      & !ap_uop_act_r) // (3)
                      | (x3_dt_r & !x3_bp_r &  x3_ex_r & ap_tkn  & !ca_uop_active_r & !ap_uop_act_r) // (4)
                      | (x3_dt_r & !x3_bp_r &  x3_ex_r & excpn_evts[`npuarc_INTEVT_ENTER] 
                         & (ar_aux_ecr_r[`npuarc_ECR_VEC_RANGE] == 8'h7) & (ar_aux_ecr_r[`npuarc_ECR_CAUSE_RANGE] == 8'h2)) // (5)
                      ;

  // CA AP Pass
  // 1. CA BP Pass
  // 2. CA BP Kill
  // 3. CA WP Halt      Commit
  // 4. CA WP Exception Pass
  // 5. CA WP Exception killed due to any asynchronous event
  // 
  ca_ap_pass     = 1'b0
                      | (ca_dt_r &  ca_bp_r &                 ca_pass) // (1)
                      | (ca_dt_r &  ca_bp_r &                 ca_kill) // (2)
                      | (ca_dt_r & !ca_bp_r & !ca_ex_r & ca_ap_halt_cmt) // (3)
                      | (ca_dt_r & !ca_bp_r &  ca_ex_r & ca_pass) // (4)
                      | (ca_dt_r & !ca_bp_r &  ca_ex_r & ca_kill) // (5)
                      ;

end // block :  x3_pipe_ctrl_PROC
//
always @*
begin : x3_bp_nxt_PROC

  // 1. New detect
  // 1.a Hold back as X3 stalled for Halts
  // 2. AP Pass
  x3_bp_cg         = 1'b0
                      | ( x3_dt_nxt                                                   // 1
                        & ( !x3_dt_r
                          |  x3_ap_pass             // 1.a
                          )
                        )
                      | (x3_bp_r & x3_ap_pass)                                   // 2
                      ;
   
end // block :  x3_bp_nxt_PROC
//
always @*
begin : x3_ex_nxt_PROC

  // 1. New detect
  // 1.a Hold back as X3 stalled for Halts
  // 2. AP Pass
  x3_ex_cg         = 1'b0
                      | ( x3_dt_nxt
                        & ( !x3_dt_r
                          |  x3_ap_pass             // 1.a
                          )
                        )
                      | (x3_ex_r & x3_ap_pass)
                      ;
   
end // block :  x3_ex_nxt_PROC
//
always @*
begin : x3_dt_nxt_PROC

  // 1. New detect
  // 1.a Hold back as X3 stalled for Halts
  // 2. AP Pass
  // 3. Need to clear WP
  x3_dt_raw_cg     = 1'b0
                      | ( x3_dt_nxt
                        & ( !x3_dt_r
                          |  x3_ap_pass             // 1.a
                          )
                        )
                      | (x3_dt_r & x3_ap_pass)
                      | clear_pend_ap_r
                      ;

  x3_dt_cg[0] = x3_dt_raw_cg & x3_ap_en_nxt[0]; 
  x3_dt_cg[1] = x3_dt_raw_cg & x3_ap_en_nxt[1]; 
  x3_dt_cg[2] = x3_dt_raw_cg & x3_ap_en_nxt[2]; 
  x3_dt_cg[3] = x3_dt_raw_cg & x3_ap_en_nxt[3]; 
  x3_dt_cg[4] = x3_dt_raw_cg & x3_ap_en_nxt[4]; 
  x3_dt_cg[5] = x3_dt_raw_cg & x3_ap_en_nxt[5]; 
  x3_dt_cg[6] = x3_dt_raw_cg & x3_ap_en_nxt[6]; 
  x3_dt_cg[7] = x3_dt_raw_cg & x3_ap_en_nxt[7]; 

end // block :  x3_dt_nxt_PROC
//
always @*
begin : ca_bp_nxt_PROC

  // Pass to next stage unless BP kill
  ca_bp_nxt        = x3_bp_r
                      & !(x3_bp_r & x3_kill)
                      ;
   
  ca_bp_cg         = 1'b0
                      | (x3_bp_r & x3_ap_pass
                        & ( !ca_dt_r              // Unless a WP Halt is held up
                          | ca_ap_pass
                          )
                        )
                      | (ca_bp_r & ca_ap_pass)
                      ;
   
end // block :  ca_bp_nxt_PROC
//
always @*
begin : ca_ex_nxt_PROC

  // Pass to next stage unless BP kill
  ca_ex_nxt         = x3_ex_r
                       & !(x3_bp_r & x3_kill)
                       & !(ca_ex_r & (ca_ap_excpn_r & excpn_evts[`npuarc_INTEVT_PROLOGUE])) // X3 dt is fake for this condition
                       ;
   
  // `my_reg Clock gate
  // 1. X3 AP Exception detected
  //   a. taken
  //   i. AP exception taken 
  //   ii. WP Exception trial 
  //   b. Hold if previous AP held up
  // 2. CA AP EX taken
  // 
  ca_ex_cg         = 1'b0
                      | ( ( (                 x3_ex_r & x3_ap_pass)      // (1.a.i)
                          | (!x3_bp_r  & x3_ex_r & !ca_uop_active_r)   // (1.a.ii)
                          )
                        & ( !ca_dt_r                                          // (1.b)
                          | ca_ap_pass
                          )
                        )
                      | (ca_ex_r & ca_ap_pass)                           // (2)
                      ;
   
end // block :  ca_ex_nxt_PROC
//
always @*
begin : ca_dt_nxt_PROC

  // Pass to next stage unless BP kill
  ca_dt_nxt         = x3_dt_r
                       & !(x3_bp_r & x3_kill)
                       & !(ca_ex_r & (ca_ap_excpn_r & excpn_evts[`npuarc_INTEVT_PROLOGUE])) // X3 dt is fake for this condition
                       & !clear_pend_ap_r
                       ;
   
  // `my_reg Clock gate
  // 1. X3 AP detected
  //   a. Taken
  //   i.  AP exception taken 
  //   ii. WP Exception trial 
  //   iii.Keep AP Exception in sync with ca_ex_r
  //   b. Hold if previous AP held up
  // 2. CA AP taken
  // 
  ca_dt_raw_cg     = 1'b0
                      | ( ( ( x3_dt_r & (x3_ap_pass                       // (1.a.i)
                                             & ( !(!ar_aux_debug_r[`npuarc_DEBUG_UB] & ar_aux_status32_r[`npuarc_U_FLAG]
                                                  )                                 // check if in user mode and if ub bit is set
                                               | x3_ex_r                       // user mode/ub bit doesn't matter if excpn
                                               )
                                             )
                            )     
                          | (!x3_bp_r  & x3_ex_r
                                            & !ca_cmt_uop_evt
                                            & !ap_uop_act_r                    // (1.a.ii)
                                            & !ca_uop_active_r                 // (1.a.iii)
                             )
                          )
                        & ( !ca_dt_r                                           // (1.b)
                          | ca_ap_pass
                          )
                        )
                      | (ca_dt_r & ca_ap_pass)                            // (2)                             
                      ;
  ca_dt_cg[0] = ca_dt_raw_cg;
  ca_dt_cg[1] = ca_dt_raw_cg;
  ca_dt_cg[2] = ca_dt_raw_cg;
  ca_dt_cg[3] = ca_dt_raw_cg;
  ca_dt_cg[4] = ca_dt_raw_cg;
  ca_dt_cg[5] = ca_dt_raw_cg;
  ca_dt_cg[6] = ca_dt_raw_cg;
  ca_dt_cg[7] = ca_dt_raw_cg;
end // block :  ca_dt_nxt_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ca_bp_reg_PROC
  if (rst_a == 1'b1) begin
    ca_bp_r   <= 1'b0;
  end
  else if (ca_bp_cg) begin
    ca_bp_r <= ca_bp_nxt;
  end
end // block : ca_bp_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ca_dt_reg_PROC
  if (rst_a == 1'b1) begin
    ca_dt_r   <= 1'b0;
  end
  else if (ca_dt_raw_cg) begin
    ca_dt_r <= ca_dt_nxt;
  end
end // block : ca_dt_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ca_ex_reg_PROC
  if (rst_a == 1'b1) begin
    ca_ex_r   <= 1'b0;
  end
  else if (ca_ex_cg) begin
    ca_ex_r <= ca_ex_nxt;
  end
end // block : ca_ex_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : x3_bp_reg_PROC
  if (rst_a == 1'b1) begin
    x3_bp_r   <= 1'b0;
  end
  else if (x3_bp_cg) begin
    x3_bp_r <= x3_bp_nxt;
  end
end // block : x3_bp_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : x3_dt_reg_PROC
  if (rst_a == 1'b1) begin
    x3_dt_r   <= 1'b0;
  end
  else if (x3_dt_raw_cg) begin
    x3_dt_r <= x3_dt_nxt;
  end
end // block : x3_dt_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : x3_ex_reg_PROC
  if (rst_a == 1'b1) begin
    x3_ex_r   <= 1'b0;
  end
  else if (x3_ex_cg) begin
    x3_ex_r <= x3_ex_nxt;
  end
end // block : x3_ex_reg_PROC
//
always @*
begin : ap_any_PROC

  ap_pend_any  = 1'b0
               | ap_pend_r
               ;

  x3_pass_any  = 1'b0
               | x3_pass
               ;

  // X3 Action Point pending on 0
  x3_ap_pend [0]      = 1'b0
                       | ar_asr_r[0]                   // 2.b
                       | x3_trigg_r[0]            // 2.a
                       | (ca_dt_r & aps_status_r [0]) // 2.c
                       ;

  // X3 Action Point pending on 1
  x3_ap_pend [1]      = 1'b0
                       | ar_asr_r[1]                   // 2.b
                       | x3_trigg_r[1]            // 2.a
                       | (ca_dt_r & aps_status_r [1]) // 2.c
                       ;

  // X3 Action Point pending on 2
  x3_ap_pend [2]      = 1'b0
                       | ar_asr_r[2]                   // 2.b
                       | x3_trigg_r[2]            // 2.a
                       | (ca_dt_r & aps_status_r [2]) // 2.c
                       ;

  // X3 Action Point pending on 3
  x3_ap_pend [3]      = 1'b0
                       | ar_asr_r[3]                   // 2.b
                       | x3_trigg_r[3]            // 2.a
                       | (ca_dt_r & aps_status_r [3]) // 2.c
                       ;

  // X3 Action Point pending on 4
  x3_ap_pend [4]      = 1'b0
                       | ar_asr_r[4]                   // 2.b
                       | x3_trigg_r[4]            // 2.a
                       | (ca_dt_r & aps_status_r [4]) // 2.c
                       ;

  // X3 Action Point pending on 5
  x3_ap_pend [5]      = 1'b0
                       | ar_asr_r[5]                   // 2.b
                       | x3_trigg_r[5]            // 2.a
                       | (ca_dt_r & aps_status_r [5]) // 2.c
                       ;

  // X3 Action Point pending on 6
  x3_ap_pend [6]      = 1'b0
                       | ar_asr_r[6]                   // 2.b
                       | x3_trigg_r[6]            // 2.a
                       | (ca_dt_r & aps_status_r [6]) // 2.c
                       ;

  // X3 Action Point pending on 7
  x3_ap_pend [7]      = 1'b0
                       | ar_asr_r[7]                   // 2.b
                       | x3_trigg_r[7]            // 2.a
                       | (ca_dt_r & aps_status_r [7]) // 2.c
                       ;


end // block : ap_any_PROC
//
/***
*
*  Logic block for
*  AP trigger
*
***/
//
always @*
begin : ap_outputs_PROC

  ca_bp_excpn = ca_dt_r &  ca_bp_r &  ca_ex_r & !ar_ae_r;
  ca_bp_halt  = ca_dt_r &  ca_bp_r & !ca_ex_r;
  ca_wp_excpn = ca_dt_r & !ca_bp_r &  ca_ex_r
                        & !ar_ae_r
                        & !ca_uop_active_r
                        & !ca_cmt_uop_evt
                        & !int_load_active
                        & !pipe_block_ints
                        & !ap_uop_act_r
                        & !clear_pend_ap_r
                        ;
  ca_wp_halt  = ca_dt_r & !ca_bp_r & !ca_ex_r            & !ca_uop_active_r
                        & !int_load_active
                        & !pipe_block_ints
                        ;
  x3_bp_excpn = x3_dt_r &  x3_bp_r &  x3_ex_r & !ar_ae_r;
  x3_bp_halt  = x3_dt_r &  x3_bp_r & !x3_ex_r;
  x3_wp_excpn = x3_dt_r & !x3_bp_r &  x3_ex_r
                        & !ar_ae_r
                        & !ca_uop_active_r
                        & !ca_cmt_uop_evt
                        & !int_load_active
                        & !pipe_block_ints
                        & !ap_uop_act_r
                        & !clear_pend_ap_r
                        ;
  x3_wp_halt  = x3_dt_r & !x3_bp_r & !x3_ex_r            & !ca_uop_active_r
                        & !int_load_active
                        & !pipe_block_ints
                        ;

end // block :  ap_outputs_PROC
//
always @*
begin : trig__PROC


  // Action point speculative trigger on
  // 1. Respective AP a hit
  // 2. Disallow back-to-back AP
  //    a. Specultive trigger in pipe
  //    b. AP taken & under process
  // 3. Check for Pairing & Quad conditions
  // 
  trig[0] = 
          & hit[0]                    // 1
             & !x3_ap_pend[0]                 // 2
          & !quad[5]
          & !quad[6]
          & !quad[7]
          & !paired[7]
          & ( !paired[0]
            |  hit[1]
            )
          & ( !quad[0]
            | (  hit[1]
              &  hit[2]
              &  hit[3])
            )
          ;
  //


  // Action point speculative trigger on
  // 1. Respective AP a hit
  // 2. Disallow back-to-back AP
  //    a. Specultive trigger in pipe
  //    b. AP taken & under process
  // 3. Check for Pairing & Quad conditions
  // 
  trig[1] = 
          & hit[1]                    // 1
             & !x3_ap_pend[1]                 // 2
          & !quad[6]
          & !quad[7]
          & !quad[0]
          & !paired[0]
          & ( !paired[1]
            |  hit[2]
            )
          & ( !quad[1]
            | (  hit[2]
              &  hit[3]
              &  hit[4])
            )
          ;
  //


  // Action point speculative trigger on
  // 1. Respective AP a hit
  // 2. Disallow back-to-back AP
  //    a. Specultive trigger in pipe
  //    b. AP taken & under process
  // 3. Check for Pairing & Quad conditions
  // 
  trig[2] = 
          & hit[2]                    // 1
             & !x3_ap_pend[2]                 // 2
          & !quad[7]
          & !quad[0]
          & !quad[1]
          & !paired[1]
          & ( !paired[2]
            |  hit[3]
            )
          & ( !quad[2]
            | (  hit[3]
              &  hit[4]
              &  hit[5])
            )
          ;
  //


  // Action point speculative trigger on
  // 1. Respective AP a hit
  // 2. Disallow back-to-back AP
  //    a. Specultive trigger in pipe
  //    b. AP taken & under process
  // 3. Check for Pairing & Quad conditions
  // 
  trig[3] = 
          & hit[3]                    // 1
             & !x3_ap_pend[3]                 // 2
          & !quad[0]
          & !quad[1]
          & !quad[2]
          & !paired[2]
          & ( !paired[3]
            |  hit[4]
            )
          & ( !quad[3]
            | (  hit[4]
              &  hit[5]
              &  hit[6])
            )
          ;
  //


  // Action point speculative trigger on
  // 1. Respective AP a hit
  // 2. Disallow back-to-back AP
  //    a. Specultive trigger in pipe
  //    b. AP taken & under process
  // 3. Check for Pairing & Quad conditions
  // 
  trig[4] = 
          & hit[4]                    // 1
             & !x3_ap_pend[4]                 // 2
          & !quad[1]
          & !quad[2]
          & !quad[3]
          & !paired[3]
          & ( !paired[4]
            |  hit[5]
            )
          & ( !quad[4]
            | (  hit[5]
              &  hit[6]
              &  hit[7])
            )
          ;
  //


  // Action point speculative trigger on
  // 1. Respective AP a hit
  // 2. Disallow back-to-back AP
  //    a. Specultive trigger in pipe
  //    b. AP taken & under process
  // 3. Check for Pairing & Quad conditions
  // 
  trig[5] = 
          & hit[5]                    // 1
             & !x3_ap_pend[5]                 // 2
          & !quad[2]
          & !quad[3]
          & !quad[4]
          & !paired[4]
          & ( !paired[5]
            |  hit[6]
            )
          & ( !quad[5]
            | (  hit[6]
              &  hit[7]
              &  hit[0])
            )
          ;
  //


  // Action point speculative trigger on
  // 1. Respective AP a hit
  // 2. Disallow back-to-back AP
  //    a. Specultive trigger in pipe
  //    b. AP taken & under process
  // 3. Check for Pairing & Quad conditions
  // 
  trig[6] = 
          & hit[6]                    // 1
             & !x3_ap_pend[6]                 // 2
          & !quad[3]
          & !quad[4]
          & !quad[5]
          & !paired[5]
          & ( !paired[6]
            |  hit[7]
            )
          & ( !quad[6]
            | (  hit[7]
              &  hit[0]
              &  hit[1])
            )
          ;
  //


  // Action point speculative trigger on
  // 1. Respective AP a hit
  // 2. Disallow back-to-back AP
  //    a. Specultive trigger in pipe
  //    b. AP taken & under process
  // 3. Check for Pairing & Quad conditions
  // 
  trig[7] = 
          & hit[7]                    // 1
             & !x3_ap_pend[7]                 // 2
          & !quad[4]
          & !quad[5]
          & !quad[6]
          & !paired[6]
          & ( !paired[7]
            |  hit[0]
            )
          & ( !quad[7]
            | (  hit[0]
              &  hit[1]
              &  hit[2])
            )
          ;
  //


end // block : trig__PROC
//
always @*
begin : ap_amv_0_nxt_PROC

  case (1'b1)
  ap_amv0_sr:
  begin
    ap_amv0_nxt = wa_sr_data_r;
  end
  reloadamv[0]:
  begin
    ap_amv0_nxt = ca_amv0_r;
  end
  default:
  begin
    ap_amv0_nxt = ca_amv0_r;
  end
  endcase



  // 
  ap_amv0_wen = ap_amv0_sr
                 | reloadamv[0]
                 ;

end // block : ap_amv_0_nxt_PROC
//
always @*
begin : ap_amv_1_nxt_PROC

  case (1'b1)
  ap_amv1_sr:
  begin
    ap_amv1_nxt = wa_sr_data_r;
  end
  reloadamv[1]:
  begin
    ap_amv1_nxt = ca_amv1_r;
  end
  default:
  begin
    ap_amv1_nxt = ca_amv1_r;
  end
  endcase



  // 
  ap_amv1_wen = ap_amv1_sr
                 | reloadamv[1]
                 ;

end // block : ap_amv_1_nxt_PROC
//
always @*
begin : ap_amv_2_nxt_PROC

  case (1'b1)
  ap_amv2_sr:
  begin
    ap_amv2_nxt = wa_sr_data_r;
  end
  reloadamv[2]:
  begin
    ap_amv2_nxt = ca_amv2_r;
  end
  default:
  begin
    ap_amv2_nxt = ca_amv2_r;
  end
  endcase



  // 
  ap_amv2_wen = ap_amv2_sr
                 | reloadamv[2]
                 ;

end // block : ap_amv_2_nxt_PROC
//
always @*
begin : ap_amv_3_nxt_PROC

  case (1'b1)
  ap_amv3_sr:
  begin
    ap_amv3_nxt = wa_sr_data_r;
  end
  reloadamv[3]:
  begin
    ap_amv3_nxt = ca_amv3_r;
  end
  default:
  begin
    ap_amv3_nxt = ca_amv3_r;
  end
  endcase



  // 
  ap_amv3_wen = ap_amv3_sr
                 | reloadamv[3]
                 ;

end // block : ap_amv_3_nxt_PROC
//
always @*
begin : ap_amv_4_nxt_PROC

  case (1'b1)
  ap_amv4_sr:
  begin
    ap_amv4_nxt = wa_sr_data_r;
  end
  reloadamv[4]:
  begin
    ap_amv4_nxt = ca_amv4_r;
  end
  default:
  begin
    ap_amv4_nxt = ca_amv4_r;
  end
  endcase



  // 
  ap_amv4_wen = ap_amv4_sr
                 | reloadamv[4]
                 ;

end // block : ap_amv_4_nxt_PROC
//
always @*
begin : ap_amv_5_nxt_PROC

  case (1'b1)
  ap_amv5_sr:
  begin
    ap_amv5_nxt = wa_sr_data_r;
  end
  reloadamv[5]:
  begin
    ap_amv5_nxt = ca_amv5_r;
  end
  default:
  begin
    ap_amv5_nxt = ca_amv5_r;
  end
  endcase



  // 
  ap_amv5_wen = ap_amv5_sr
                 | reloadamv[5]
                 ;

end // block : ap_amv_5_nxt_PROC
//
always @*
begin : ap_amv_6_nxt_PROC

  case (1'b1)
  ap_amv6_sr:
  begin
    ap_amv6_nxt = wa_sr_data_r;
  end
  reloadamv[6]:
  begin
    ap_amv6_nxt = ca_amv6_r;
  end
  default:
  begin
    ap_amv6_nxt = ca_amv6_r;
  end
  endcase



  // 
  ap_amv6_wen = ap_amv6_sr
                 | reloadamv[6]
                 ;

end // block : ap_amv_6_nxt_PROC
//
always @*
begin : ap_amv_7_nxt_PROC

  case (1'b1)
  ap_amv7_sr:
  begin
    ap_amv7_nxt = wa_sr_data_r;
  end
  reloadamv[7]:
  begin
    ap_amv7_nxt = ca_amv7_r;
  end
  default:
  begin
    ap_amv7_nxt = ca_amv7_r;
  end
  endcase



  // 
  ap_amv7_wen = ap_amv7_sr
                 | reloadamv[7]
                 ;

end // block : ap_amv_7_nxt_PROC
//
always @*
begin : ctrl_PROC

  // Disable Actionpoints checks
  // 1. Actionpoint Halt
  // 2. Actionpoint Exception routine
  dis_ap_chk_all   = 1'b0
               | ar_aux_debug_r[`npuarc_DEBUG_AH]    // (1)
               | ( ar_ae_r                    // (2)
                 & ( ar_aux_ecr_r [`npuarc_ECR_VEC_RANGE]   == `npuarc_EV_PRIV_V )
                 & ( ar_aux_ecr_r [`npuarc_ECR_CAUSE_RANGE] == `npuarc_ECC_AP_HIT)
                 )
               ;

  tt_read[0]  = ap2_ac0_r[5];
  tt_write[0] = ap2_ac0_r[4];
  mode[0]     = ap2_ac0_r[6];
  paired[0]   = ap2_ac0_r[7];
  action[0]   = ap2_ac0_r[8];
  quad[0]     = ap2_ac0_r[9];

  // A2 stage evaluation
  // 1. Actionpoint already raised/pending
  // 2. Exception action in Exception routine
  // 3. Halt in User mode requires AR UserBreakpoint
  // 4. Debug Instruction
  // 


  // Breakpoint allowed
  // Conditions to be false 2, 3, 4
  brkpt_en[0] = 1'b1
               & !( 1'b0
                  | (  action[0]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[0]                                 // (3)
                    & ar_aux_status32_r[`npuarc_U_FLAG]
                    & !ar_aux_debug_r[`npuarc_DEBUG_UB]
                    )
                  | db_active                                     // (4)
                  )
               ;

  // Watchpoint allowed
  // Conditions to be false 2, 3, 4
  wchpt_en[0] =  1'b1
               & !( 1'b0
                  | (  action[0]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[0]                                 // (3)
                    & !ap2_ar_ub_r
                    )
                  | excpn_epil_u_bit_r
                  )
               ;

  // If in exception epilogue then check next user mode bit
  excpn_epil_u_bit = ar_aux_erstatus_r[`npuarc_U_FLAG]                  
                   & excpn_evts[`npuarc_INTEVT_EXIT];
  
  if_ap[0]    = (ap2_ac0_r[3:1] == AT_INST_TYPE);
  md_ap[0]    = (ap2_ac0_r[3:0] == AT_LDST_DATA)
               | (ap2_ac0_r[3:0] == AT_AUXS_DATA);
  tt_read[1]  = ap2_ac1_r[5];
  tt_write[1] = ap2_ac1_r[4];
  mode[1]     = ap2_ac1_r[6];
  paired[1]   = ap2_ac1_r[7];
  action[1]   = ap2_ac1_r[8];
  quad[1]     = ap2_ac1_r[9];

  // A2 stage evaluation
  // 1. Actionpoint already raised/pending
  // 2. Exception action in Exception routine
  // 3. Halt in User mode requires AR UserBreakpoint
  // 4. Debug Instruction
  // 


  // Breakpoint allowed
  // Conditions to be false 2, 3, 4
  brkpt_en[1] = 1'b1
               & !( 1'b0
                  | (  action[1]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[1]                                 // (3)
                    & ar_aux_status32_r[`npuarc_U_FLAG]
                    & !ar_aux_debug_r[`npuarc_DEBUG_UB]
                    )
                  | db_active                                     // (4)
                  )
               ;

  // Watchpoint allowed
  // Conditions to be false 2, 3, 4
  wchpt_en[1] =  1'b1
               & !( 1'b0
                  | (  action[1]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[1]                                 // (3)
                    & !ap2_ar_ub_r
                    )
                  | excpn_epil_u_bit_r
                  )
               ;

  // If in exception epilogue then check next user mode bit
  excpn_epil_u_bit = ar_aux_erstatus_r[`npuarc_U_FLAG]                  
                   & excpn_evts[`npuarc_INTEVT_EXIT];
  
  if_ap[1]    = (ap2_ac1_r[3:1] == AT_INST_TYPE);
  md_ap[1]    = (ap2_ac1_r[3:0] == AT_LDST_DATA)
               | (ap2_ac1_r[3:0] == AT_AUXS_DATA);
  tt_read[2]  = ap2_ac2_r[5];
  tt_write[2] = ap2_ac2_r[4];
  mode[2]     = ap2_ac2_r[6];
  paired[2]   = ap2_ac2_r[7];
  action[2]   = ap2_ac2_r[8];
  quad[2]     = ap2_ac2_r[9];

  // A2 stage evaluation
  // 1. Actionpoint already raised/pending
  // 2. Exception action in Exception routine
  // 3. Halt in User mode requires AR UserBreakpoint
  // 4. Debug Instruction
  // 


  // Breakpoint allowed
  // Conditions to be false 2, 3, 4
  brkpt_en[2] = 1'b1
               & !( 1'b0
                  | (  action[2]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[2]                                 // (3)
                    & ar_aux_status32_r[`npuarc_U_FLAG]
                    & !ar_aux_debug_r[`npuarc_DEBUG_UB]
                    )
                  | db_active                                     // (4)
                  )
               ;

  // Watchpoint allowed
  // Conditions to be false 2, 3, 4
  wchpt_en[2] =  1'b1
               & !( 1'b0
                  | (  action[2]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[2]                                 // (3)
                    & !ap2_ar_ub_r
                    )
                  | excpn_epil_u_bit_r
                  )
               ;

  // If in exception epilogue then check next user mode bit
  excpn_epil_u_bit = ar_aux_erstatus_r[`npuarc_U_FLAG]                  
                   & excpn_evts[`npuarc_INTEVT_EXIT];
  
  if_ap[2]    = (ap2_ac2_r[3:1] == AT_INST_TYPE);
  md_ap[2]    = (ap2_ac2_r[3:0] == AT_LDST_DATA)
               | (ap2_ac2_r[3:0] == AT_AUXS_DATA);
  tt_read[3]  = ap2_ac3_r[5];
  tt_write[3] = ap2_ac3_r[4];
  mode[3]     = ap2_ac3_r[6];
  paired[3]   = ap2_ac3_r[7];
  action[3]   = ap2_ac3_r[8];
  quad[3]     = ap2_ac3_r[9];

  // A2 stage evaluation
  // 1. Actionpoint already raised/pending
  // 2. Exception action in Exception routine
  // 3. Halt in User mode requires AR UserBreakpoint
  // 4. Debug Instruction
  // 


  // Breakpoint allowed
  // Conditions to be false 2, 3, 4
  brkpt_en[3] = 1'b1
               & !( 1'b0
                  | (  action[3]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[3]                                 // (3)
                    & ar_aux_status32_r[`npuarc_U_FLAG]
                    & !ar_aux_debug_r[`npuarc_DEBUG_UB]
                    )
                  | db_active                                     // (4)
                  )
               ;

  // Watchpoint allowed
  // Conditions to be false 2, 3, 4
  wchpt_en[3] =  1'b1
               & !( 1'b0
                  | (  action[3]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[3]                                 // (3)
                    & !ap2_ar_ub_r
                    )
                  | excpn_epil_u_bit_r
                  )
               ;

  // If in exception epilogue then check next user mode bit
  excpn_epil_u_bit = ar_aux_erstatus_r[`npuarc_U_FLAG]                  
                   & excpn_evts[`npuarc_INTEVT_EXIT];
  
  if_ap[3]    = (ap2_ac3_r[3:1] == AT_INST_TYPE);
  md_ap[3]    = (ap2_ac3_r[3:0] == AT_LDST_DATA)
               | (ap2_ac3_r[3:0] == AT_AUXS_DATA);
  tt_read[4]  = ap2_ac4_r[5];
  tt_write[4] = ap2_ac4_r[4];
  mode[4]     = ap2_ac4_r[6];
  paired[4]   = ap2_ac4_r[7];
  action[4]   = ap2_ac4_r[8];
  quad[4]     = ap2_ac4_r[9];

  // A2 stage evaluation
  // 1. Actionpoint already raised/pending
  // 2. Exception action in Exception routine
  // 3. Halt in User mode requires AR UserBreakpoint
  // 4. Debug Instruction
  // 


  // Breakpoint allowed
  // Conditions to be false 2, 3, 4
  brkpt_en[4] = 1'b1
               & !( 1'b0
                  | (  action[4]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[4]                                 // (3)
                    & ar_aux_status32_r[`npuarc_U_FLAG]
                    & !ar_aux_debug_r[`npuarc_DEBUG_UB]
                    )
                  | db_active                                     // (4)
                  )
               ;

  // Watchpoint allowed
  // Conditions to be false 2, 3, 4
  wchpt_en[4] =  1'b1
               & !( 1'b0
                  | (  action[4]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[4]                                 // (3)
                    & !ap2_ar_ub_r
                    )
                  | excpn_epil_u_bit_r
                  )
               ;

  // If in exception epilogue then check next user mode bit
  excpn_epil_u_bit = ar_aux_erstatus_r[`npuarc_U_FLAG]                  
                   & excpn_evts[`npuarc_INTEVT_EXIT];
  
  if_ap[4]    = (ap2_ac4_r[3:1] == AT_INST_TYPE);
  md_ap[4]    = (ap2_ac4_r[3:0] == AT_LDST_DATA)
               | (ap2_ac4_r[3:0] == AT_AUXS_DATA);
  tt_read[5]  = ap2_ac5_r[5];
  tt_write[5] = ap2_ac5_r[4];
  mode[5]     = ap2_ac5_r[6];
  paired[5]   = ap2_ac5_r[7];
  action[5]   = ap2_ac5_r[8];
  quad[5]     = ap2_ac5_r[9];

  // A2 stage evaluation
  // 1. Actionpoint already raised/pending
  // 2. Exception action in Exception routine
  // 3. Halt in User mode requires AR UserBreakpoint
  // 4. Debug Instruction
  // 


  // Breakpoint allowed
  // Conditions to be false 2, 3, 4
  brkpt_en[5] = 1'b1
               & !( 1'b0
                  | (  action[5]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[5]                                 // (3)
                    & ar_aux_status32_r[`npuarc_U_FLAG]
                    & !ar_aux_debug_r[`npuarc_DEBUG_UB]
                    )
                  | db_active                                     // (4)
                  )
               ;

  // Watchpoint allowed
  // Conditions to be false 2, 3, 4
  wchpt_en[5] =  1'b1
               & !( 1'b0
                  | (  action[5]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[5]                                 // (3)
                    & !ap2_ar_ub_r
                    )
                  | excpn_epil_u_bit_r
                  )
               ;

  // If in exception epilogue then check next user mode bit
  excpn_epil_u_bit = ar_aux_erstatus_r[`npuarc_U_FLAG]                  
                   & excpn_evts[`npuarc_INTEVT_EXIT];
  
  if_ap[5]    = (ap2_ac5_r[3:1] == AT_INST_TYPE);
  md_ap[5]    = (ap2_ac5_r[3:0] == AT_LDST_DATA)
               | (ap2_ac5_r[3:0] == AT_AUXS_DATA);
  tt_read[6]  = ap2_ac6_r[5];
  tt_write[6] = ap2_ac6_r[4];
  mode[6]     = ap2_ac6_r[6];
  paired[6]   = ap2_ac6_r[7];
  action[6]   = ap2_ac6_r[8];
  quad[6]     = ap2_ac6_r[9];

  // A2 stage evaluation
  // 1. Actionpoint already raised/pending
  // 2. Exception action in Exception routine
  // 3. Halt in User mode requires AR UserBreakpoint
  // 4. Debug Instruction
  // 


  // Breakpoint allowed
  // Conditions to be false 2, 3, 4
  brkpt_en[6] = 1'b1
               & !( 1'b0
                  | (  action[6]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[6]                                 // (3)
                    & ar_aux_status32_r[`npuarc_U_FLAG]
                    & !ar_aux_debug_r[`npuarc_DEBUG_UB]
                    )
                  | db_active                                     // (4)
                  )
               ;

  // Watchpoint allowed
  // Conditions to be false 2, 3, 4
  wchpt_en[6] =  1'b1
               & !( 1'b0
                  | (  action[6]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[6]                                 // (3)
                    & !ap2_ar_ub_r
                    )
                  | excpn_epil_u_bit_r
                  )
               ;

  // If in exception epilogue then check next user mode bit
  excpn_epil_u_bit = ar_aux_erstatus_r[`npuarc_U_FLAG]                  
                   & excpn_evts[`npuarc_INTEVT_EXIT];
  
  if_ap[6]    = (ap2_ac6_r[3:1] == AT_INST_TYPE);
  md_ap[6]    = (ap2_ac6_r[3:0] == AT_LDST_DATA)
               | (ap2_ac6_r[3:0] == AT_AUXS_DATA);
  tt_read[7]  = ap2_ac7_r[5];
  tt_write[7] = ap2_ac7_r[4];
  mode[7]     = ap2_ac7_r[6];
  paired[7]   = ap2_ac7_r[7];
  action[7]   = ap2_ac7_r[8];
  quad[7]     = ap2_ac7_r[9];

  // A2 stage evaluation
  // 1. Actionpoint already raised/pending
  // 2. Exception action in Exception routine
  // 3. Halt in User mode requires AR UserBreakpoint
  // 4. Debug Instruction
  // 


  // Breakpoint allowed
  // Conditions to be false 2, 3, 4
  brkpt_en[7] = 1'b1
               & !( 1'b0
                  | (  action[7]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[7]                                 // (3)
                    & ar_aux_status32_r[`npuarc_U_FLAG]
                    & !ar_aux_debug_r[`npuarc_DEBUG_UB]
                    )
                  | db_active                                     // (4)
                  )
               ;

  // Watchpoint allowed
  // Conditions to be false 2, 3, 4
  wchpt_en[7] =  1'b1
               & !( 1'b0
                  | (  action[7]                                 // (2)
                    &  ap1_stat32_ae_r
                    )
                  | ( !action[7]                                 // (3)
                    & !ap2_ar_ub_r
                    )
                  | excpn_epil_u_bit_r
                  )
               ;

  // If in exception epilogue then check next user mode bit
  excpn_epil_u_bit = ar_aux_erstatus_r[`npuarc_U_FLAG]                  
                   & excpn_evts[`npuarc_INTEVT_EXIT];
  
  if_ap[7]    = (ap2_ac7_r[3:1] == AT_INST_TYPE);
  md_ap[7]    = (ap2_ac7_r[3:0] == AT_LDST_DATA)
               | (ap2_ac7_r[3:0] == AT_AUXS_DATA);

end // block : ctrl_PROC

always @(posedge ap_unit_clk or posedge rst_a) 
begin: excpn_epil_u_bit_r_PROC
  if (rst_a == 1'b1) begin
    excpn_epil_u_bit_r <= 0;
  end
  else begin
    excpn_epil_u_bit_r <= excpn_epil_u_bit;
  end
end


//
//
always @*
begin : aps_pending_PROC

  aps_pending = x3_hit_if_r
                   | x3_hit_mr_r 
                   | x3_hit_md_r
                   | x3_halt_r
                   | aps_halt_r
                   | x3_break_r
                   | ca_break_r
                   ;

end // block : aps_pending_PROC
//
always @*
begin : x3_trig_cg__PROC

  // Breakpoint - Non Sticky
  x3_hit_if_cg  = 1'b0
                 | (x2_pass & x3_enable & (|trig))
                 | (x3_pass & x3_hit_if_r)
                 | (x3_kill)
                 ;

  // Watchpoint - Sticky
  x3_hit_mr_cg  = 1'b0
                 | (|trig)
                 | ( ca_enable 
                   & x3_hit_mr_r 
                   & (ca_ap_excpn_r & excpn_evts[`npuarc_INTEVT_PROLOGUE])
                   ) 
                 ;

  x3_hit_md_cg  = 1'b0
                 | (|trig)
                 | ( ca_enable 
                   & x3_hit_md_r
                   & (ca_ap_excpn_r & excpn_evts[`npuarc_INTEVT_PROLOGUE])
                   ) 
                 ;

end // block : x3_trig_cg__PROC
//
always @*
begin : x3_trig_nxt_PROC
// spyglass disable_block Ac_conv01 
// SMD: syncs converge on combinational gate
// SJ:  safe, causes no issues
  // Breakpoint - Avoid double fault
  x3_hit_if_nxt  = (|(x3_trig_comp & if_ap & action))
                      & (~(ca_ap_excpn_r & excpn_evts[`npuarc_INTEVT_PROLOGUE]))
                      & (~x2_kill)
                      & (~ar_ae_r)
                      & (~excpn_in_prologue)
                      & (~x3_hit_if_r)
                      & (~sys_halt_2r)
                      ;
// spyglass enable_block Ac_conv01 

  // Watchpoint - Avoid double fault
  x3_hit_mr_nxt = (|(x3_trig_comp & (~if_ap) & (~md_ap) & action))
                     & (~ar_ae_r)
                     & (~excpn_in_prologue)
                     & (~(ca_ap_excpn_r & excpn_evts[`npuarc_INTEVT_PROLOGUE]))
                     & (~sys_halt_2r)
                     & (!i_halt_nxt)
                     ;

  // Watchpoint - Avoid double fault
  x3_hit_md_nxt = (|(x3_trig_comp & (~if_ap) & md_ap & action))
                     & (~ar_ae_r)
                     & (~excpn_in_prologue)
                     & (~(ca_ap_excpn_r & excpn_evts[`npuarc_INTEVT_PROLOGUE]))
                     & (~sys_halt_2r)
                     & (!i_halt_nxt)
                     ;

end // block : x3_trig_nxt_PROC
//
always @*
begin : x3trig_nxt_PROC

  x3_trig_nxt =  x2_trig_comp
                   & ( {`npuarc_NUM_ACTIONPOINTS{~x2_kill}}
                     | (~if_ap)
                     )
                   ;

  x3_wppc_nxt = (x3_bp_nxt == 1'b1) 
                   ? x2_pc_r
                   : x2_wppc_r
                   ;

end // block : x3trig_nxt_PROC
//
always @*
begin : ca_trig__PROC

  ca_trig_nxt =  x3_trig_r
                   & ( {`npuarc_NUM_ACTIONPOINTS{~x3_kill}}
                     | (~x3_bps_r)
                     )
                   ;

end // block : ca_trig__PROC
//
/*
  CA stage :  AP status or Trigger info
*/
always @*
begin : aps_status__PROC

  aps_active_nxt = aps_active_comp;

  aps_status_nxt = x3_trigg_r
                      & ( {`npuarc_NUM_ACTIONPOINTS{~x3_kill}}
                        | (~x3_bps_r)
                        )
                      ;

  aps_raw_cg     =  1'b0
                      | (x3_dt_r &  x3_ap_pass)
                      ;

  aps_cg         = aps_raw_cg
                      & ap_unit_enable
                      ;

end // block : aps_status__PROC
//
//===================================================================
// Flow control logic - AP1 stage
//===================================================================
always @*
begin : ap1_cond_PROC

  ap1_pass        = x2_pass & (!ar_ae_r);
  ap1_enable      = x2_pass & x3_enable;

  ap1_valid_op_nxt = ap1_pass
                   & (   x3_addr_op_nxt
                     )
                   ;

  ap1_ctrl_en    = (ap1_enable & (ap1_valid_op_r & (!ap1_valid_op_nxt)))
                 | x3_addr_en
                 ;

end // block : ap1_cond_PROC
//
always @*
begin : mtype__PROC


  inst_type[0] = tt_read[0]
                     & x2_pass & x3_enable 
                     & !x2_uop_inst_r
                     & !db_active
                     ;

  mema_type[0]  = (wa2_ald_r & tt_read[0]) | (wa2_ast_r & tt_write[0]);
  aux_type[0]  = (wa2_lr_op_r & tt_read[0]) | (wa2_sr_op_r & tt_write[0]);


  inst_type[1] = tt_read[1]
                     & x2_pass & x3_enable 
                     & !x2_uop_inst_r
                     & !db_active
                     ;

  mema_type[1]  = (wa2_ald_r & tt_read[1]) | (wa2_ast_r & tt_write[1]);
  aux_type[1]  = (wa2_lr_op_r & tt_read[1]) | (wa2_sr_op_r & tt_write[1]);


  inst_type[2] = tt_read[2]
                     & x2_pass & x3_enable 
                     & !x2_uop_inst_r
                     & !db_active
                     ;

  mema_type[2]  = (wa2_ald_r & tt_read[2]) | (wa2_ast_r & tt_write[2]);
  aux_type[2]  = (wa2_lr_op_r & tt_read[2]) | (wa2_sr_op_r & tt_write[2]);


  inst_type[3] = tt_read[3]
                     & x2_pass & x3_enable 
                     & !x2_uop_inst_r
                     & !db_active
                     ;

  mema_type[3]  = (wa2_ald_r & tt_read[3]) | (wa2_ast_r & tt_write[3]);
  aux_type[3]  = (wa2_lr_op_r & tt_read[3]) | (wa2_sr_op_r & tt_write[3]);


  inst_type[4] = tt_read[4]
                     & x2_pass & x3_enable 
                     & !x2_uop_inst_r
                     & !db_active
                     ;

  mema_type[4]  = (wa2_ald_r & tt_read[4]) | (wa2_ast_r & tt_write[4]);
  aux_type[4]  = (wa2_lr_op_r & tt_read[4]) | (wa2_sr_op_r & tt_write[4]);


  inst_type[5] = tt_read[5]
                     & x2_pass & x3_enable 
                     & !x2_uop_inst_r
                     & !db_active
                     ;

  mema_type[5]  = (wa2_ald_r & tt_read[5]) | (wa2_ast_r & tt_write[5]);
  aux_type[5]  = (wa2_lr_op_r & tt_read[5]) | (wa2_sr_op_r & tt_write[5]);


  inst_type[6] = tt_read[6]
                     & x2_pass & x3_enable 
                     & !x2_uop_inst_r
                     & !db_active
                     ;

  mema_type[6]  = (wa2_ald_r & tt_read[6]) | (wa2_ast_r & tt_write[6]);
  aux_type[6]  = (wa2_lr_op_r & tt_read[6]) | (wa2_sr_op_r & tt_write[6]);


  inst_type[7] = tt_read[7]
                     & x2_pass & x3_enable 
                     & !x2_uop_inst_r
                     & !db_active
                     ;

  mema_type[7]  = (wa2_ald_r & tt_read[7]) | (wa2_ast_r & tt_write[7]);
  aux_type[7]  = (wa2_lr_op_r & tt_read[7]) | (wa2_sr_op_r & tt_write[7]);


end // block : mtype__PROC
//
////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Constrain the matchable PC and LD/ST address bits according to the         //
// configured PC_SIZE and ADDR_SIZE.                                          //
// This is achieved by copying the valid PC bits to pc_value, which           //
// is always 32-bits in size.                                                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
//
always @*
begin : sval_pc_PROC

  pc_value[`npuarc_DATA_RANGE]  = `npuarc_DATA_SIZE'd0;
  pc_value[`npuarc_PC_RANGE]    = x1_pc_r & {`npuarc_PC_BITS{any_pc_addr}};

end // block : sval_pc__PROC
//
always @*
begin : match__PROC

  match[0] = &bitor_0;
                      
  match[1] = &bitor_1;
                      
  match[2] = &bitor_2;
                      
  match[3] = &bitor_3;
                      
  match[4] = &bitor_4;
                      
  match[5] = &bitor_5;
                      
  match[6] = &bitor_6;
                      
  match[7] = &bitor_7;
                      

end // block : match__PROC
//
always @*
begin : mcond__PROC


  cond[0]     = 1'b0;

  case (ap2_ac0_r[3:0])
  AT_INST_ADDR: cond[0] = inst_type[0] & brkpt_en[0];
  AT_LDST_ADDR: cond[0] = mema_type[0]  & wchpt_en[0];
  AT_AUXS_ADDR: cond[0] = aux_type[0]  & wchpt_en[0];
  default: cond[0] = 1'b0;
  endcase


  cond[1]     = 1'b0;

  case (ap2_ac1_r[3:0])
  AT_INST_ADDR: cond[1] = inst_type[1] & brkpt_en[1];
  AT_LDST_ADDR: cond[1] = mema_type[1]  & wchpt_en[1];
  AT_AUXS_ADDR: cond[1] = aux_type[1]  & wchpt_en[1];
  default: cond[1] = 1'b0;
  endcase


  cond[2]     = 1'b0;

  case (ap2_ac2_r[3:0])
  AT_INST_ADDR: cond[2] = inst_type[2] & brkpt_en[2];
  AT_LDST_ADDR: cond[2] = mema_type[2]  & wchpt_en[2];
  AT_AUXS_ADDR: cond[2] = aux_type[2]  & wchpt_en[2];
  default: cond[2] = 1'b0;
  endcase


  cond[3]     = 1'b0;

  case (ap2_ac3_r[3:0])
  AT_INST_ADDR: cond[3] = inst_type[3] & brkpt_en[3];
  AT_LDST_ADDR: cond[3] = mema_type[3]  & wchpt_en[3];
  AT_AUXS_ADDR: cond[3] = aux_type[3]  & wchpt_en[3];
  default: cond[3] = 1'b0;
  endcase


  cond[4]     = 1'b0;

  case (ap2_ac4_r[3:0])
  AT_INST_ADDR: cond[4] = inst_type[4] & brkpt_en[4];
  AT_LDST_ADDR: cond[4] = mema_type[4]  & wchpt_en[4];
  AT_AUXS_ADDR: cond[4] = aux_type[4]  & wchpt_en[4];
  default: cond[4] = 1'b0;
  endcase


  cond[5]     = 1'b0;

  case (ap2_ac5_r[3:0])
  AT_INST_ADDR: cond[5] = inst_type[5] & brkpt_en[5];
  AT_LDST_ADDR: cond[5] = mema_type[5]  & wchpt_en[5];
  AT_AUXS_ADDR: cond[5] = aux_type[5]  & wchpt_en[5];
  default: cond[5] = 1'b0;
  endcase


  cond[6]     = 1'b0;

  case (ap2_ac6_r[3:0])
  AT_INST_ADDR: cond[6] = inst_type[6] & brkpt_en[6];
  AT_LDST_ADDR: cond[6] = mema_type[6]  & wchpt_en[6];
  AT_AUXS_ADDR: cond[6] = aux_type[6]  & wchpt_en[6];
  default: cond[6] = 1'b0;
  endcase


  cond[7]     = 1'b0;

  case (ap2_ac7_r[3:0])
  AT_INST_ADDR: cond[7] = inst_type[7] & brkpt_en[7];
  AT_LDST_ADDR: cond[7] = mema_type[7]  & wchpt_en[7];
  AT_AUXS_ADDR: cond[7] = aux_type[7]  & wchpt_en[7];
  default: cond[7] = 1'b0;
  endcase


end // block : mcond__PROC
/*
  
  Logic to get Match bit or
  
*/
//
always @*
begin : mbitor__PROC


  bitor_0     = (bitand_0 | ap_amm0_r) & 
                             {`npuarc_DATA_SIZE{ ~((
                                 x1_iprot_viol_r || 
                                 x1_uop_inst_r) && 
                                (ap_ac0_r[3:0] == AT_INST_DATA)) }};


  bitor_1     = (bitand_1 | ap_amm1_r) & 
                             {`npuarc_DATA_SIZE{ ~((
                                 x1_iprot_viol_r || 
                                 x1_uop_inst_r) && 
                                (ap_ac1_r[3:0] == AT_INST_DATA)) }};


  bitor_2     = (bitand_2 | ap_amm2_r) & 
                             {`npuarc_DATA_SIZE{ ~((
                                 x1_iprot_viol_r || 
                                 x1_uop_inst_r) && 
                                (ap_ac2_r[3:0] == AT_INST_DATA)) }};


  bitor_3     = (bitand_3 | ap_amm3_r) & 
                             {`npuarc_DATA_SIZE{ ~((
                                 x1_iprot_viol_r || 
                                 x1_uop_inst_r) && 
                                (ap_ac3_r[3:0] == AT_INST_DATA)) }};


  bitor_4     = (bitand_4 | ap_amm4_r) & 
                             {`npuarc_DATA_SIZE{ ~((
                                 x1_iprot_viol_r || 
                                 x1_uop_inst_r) && 
                                (ap_ac4_r[3:0] == AT_INST_DATA)) }};


  bitor_5     = (bitand_5 | ap_amm5_r) & 
                             {`npuarc_DATA_SIZE{ ~((
                                 x1_iprot_viol_r || 
                                 x1_uop_inst_r) && 
                                (ap_ac5_r[3:0] == AT_INST_DATA)) }};


  bitor_6     = (bitand_6 | ap_amm6_r) & 
                             {`npuarc_DATA_SIZE{ ~((
                                 x1_iprot_viol_r || 
                                 x1_uop_inst_r) && 
                                (ap_ac6_r[3:0] == AT_INST_DATA)) }};


  bitor_7     = (bitand_7 | ap_amm7_r) & 
                             {`npuarc_DATA_SIZE{ ~((
                                 x1_iprot_viol_r || 
                                 x1_uop_inst_r) && 
                                (ap_ac7_r[3:0] == AT_INST_DATA)) }};


end // block : mbitor__PROC
/*
  
  Logic to get Match bit and
  
*/
//
always @*
begin : mbitand__PROC


  bitand_0    = ~(mvalue_0 ^ ap_amv0_r);


  bitand_1    = ~(mvalue_1 ^ ap_amv1_r);


  bitand_2    = ~(mvalue_2 ^ ap_amv2_r);


  bitand_3    = ~(mvalue_3 ^ ap_amv3_r);


  bitand_4    = ~(mvalue_4 ^ ap_amv4_r);


  bitand_5    = ~(mvalue_5 ^ ap_amv5_r);


  bitand_6    = ~(mvalue_6 ^ ap_amv6_r);


  bitand_7    = ~(mvalue_7 ^ ap_amv7_r);


end // block : mbitand__PROC
/*
  
  Logic to get Match Value
  
*/
//
always @*
begin : mvalue__PROC


  mvalue_0    = `npuarc_DATA_SIZE'd0;

  case (ap_ac0_r[3:0])
  AT_INST_ADDR: mvalue_0 = pc_value;
  AT_AUXS_ADDR: mvalue_0 = wa_addr_r;
  AT_LDST_ADDR: mvalue_0 = wa_addr_r;
    default:
    begin
      mvalue_0    = `npuarc_DATA_SIZE'd0;
    end
  endcase

  mvalue_1    = `npuarc_DATA_SIZE'd0;

  case (ap_ac1_r[3:0])
  AT_INST_ADDR: mvalue_1 = pc_value;
  AT_AUXS_ADDR: mvalue_1 = wa_addr_r;
  AT_LDST_ADDR: mvalue_1 = wa_addr_r;
    default:
    begin
      mvalue_1    = `npuarc_DATA_SIZE'd0;
    end
  endcase

  mvalue_2    = `npuarc_DATA_SIZE'd0;

  case (ap_ac2_r[3:0])
  AT_INST_ADDR: mvalue_2 = pc_value;
  AT_AUXS_ADDR: mvalue_2 = wa_addr_r;
  AT_LDST_ADDR: mvalue_2 = wa_addr_r;
    default:
    begin
      mvalue_2    = `npuarc_DATA_SIZE'd0;
    end
  endcase

  mvalue_3    = `npuarc_DATA_SIZE'd0;

  case (ap_ac3_r[3:0])
  AT_INST_ADDR: mvalue_3 = pc_value;
  AT_AUXS_ADDR: mvalue_3 = wa_addr_r;
  AT_LDST_ADDR: mvalue_3 = wa_addr_r;
    default:
    begin
      mvalue_3    = `npuarc_DATA_SIZE'd0;
    end
  endcase

  mvalue_4    = `npuarc_DATA_SIZE'd0;

  case (ap_ac4_r[3:0])
  AT_INST_ADDR: mvalue_4 = pc_value;
  AT_AUXS_ADDR: mvalue_4 = wa_addr_r;
  AT_LDST_ADDR: mvalue_4 = wa_addr_r;
    default:
    begin
      mvalue_4    = `npuarc_DATA_SIZE'd0;
    end
  endcase

  mvalue_5    = `npuarc_DATA_SIZE'd0;

  case (ap_ac5_r[3:0])
  AT_INST_ADDR: mvalue_5 = pc_value;
  AT_AUXS_ADDR: mvalue_5 = wa_addr_r;
  AT_LDST_ADDR: mvalue_5 = wa_addr_r;
    default:
    begin
      mvalue_5    = `npuarc_DATA_SIZE'd0;
    end
  endcase

  mvalue_6    = `npuarc_DATA_SIZE'd0;

  case (ap_ac6_r[3:0])
  AT_INST_ADDR: mvalue_6 = pc_value;
  AT_AUXS_ADDR: mvalue_6 = wa_addr_r;
  AT_LDST_ADDR: mvalue_6 = wa_addr_r;
    default:
    begin
      mvalue_6    = `npuarc_DATA_SIZE'd0;
    end
  endcase

  mvalue_7    = `npuarc_DATA_SIZE'd0;

  case (ap_ac7_r[3:0])
  AT_INST_ADDR: mvalue_7 = pc_value;
  AT_AUXS_ADDR: mvalue_7 = wa_addr_r;
  AT_LDST_ADDR: mvalue_7 = wa_addr_r;
    default:
    begin
      mvalue_7    = `npuarc_DATA_SIZE'd0;
    end
  endcase

end // block : mvalue__PROC
/*
  
  Logic to get Match Condition
  Stage X1
  
*/
//
always @*
begin : x1_cond_PROC


  x1_cond [0]    = 1'b0;

  case (ap_ac0_r[3:0])
  AT_INST_ADDR: x1_cond [0] = x1_pass & x2_enable;
  AT_AUXS_DATA,
  AT_AUXS_ADDR: x1_cond [0] = (wa_lr_op_r & ap_ac0_r[5] & (~excpn_in_prologue)) 
                            | (wa_sr_op_r & ap_ac0_r[4] & (~excpn_in_prologue))
                            ;
  AT_LDST_ADDR: x1_cond [0] = (wa_load_r  & ap_ac0_r[5]) 
                            | (wa_store_r & ap_ac0_r[4]) 
                            ;
                             
    default:
    begin
      x1_cond [0] = 1'b0;
    end
  endcase

  x1_cond [1]    = 1'b0;

  case (ap_ac1_r[3:0])
  AT_INST_ADDR: x1_cond [1] = x1_pass & x2_enable;
  AT_AUXS_DATA,
  AT_AUXS_ADDR: x1_cond [1] = (wa_lr_op_r & ap_ac1_r[5] & (~excpn_in_prologue)) 
                            | (wa_sr_op_r & ap_ac1_r[4] & (~excpn_in_prologue))
                            ;
  AT_LDST_ADDR: x1_cond [1] = (wa_load_r  & ap_ac1_r[5]) 
                            | (wa_store_r & ap_ac1_r[4]) 
                            ;
                             
    default:
    begin
      x1_cond [1] = 1'b0;
    end
  endcase

  x1_cond [2]    = 1'b0;

  case (ap_ac2_r[3:0])
  AT_INST_ADDR: x1_cond [2] = x1_pass & x2_enable;
  AT_AUXS_DATA,
  AT_AUXS_ADDR: x1_cond [2] = (wa_lr_op_r & ap_ac2_r[5] & (~excpn_in_prologue)) 
                            | (wa_sr_op_r & ap_ac2_r[4] & (~excpn_in_prologue))
                            ;
  AT_LDST_ADDR: x1_cond [2] = (wa_load_r  & ap_ac2_r[5]) 
                            | (wa_store_r & ap_ac2_r[4]) 
                            ;
                             
    default:
    begin
      x1_cond [2] = 1'b0;
    end
  endcase

  x1_cond [3]    = 1'b0;

  case (ap_ac3_r[3:0])
  AT_INST_ADDR: x1_cond [3] = x1_pass & x2_enable;
  AT_AUXS_DATA,
  AT_AUXS_ADDR: x1_cond [3] = (wa_lr_op_r & ap_ac3_r[5] & (~excpn_in_prologue)) 
                            | (wa_sr_op_r & ap_ac3_r[4] & (~excpn_in_prologue))
                            ;
  AT_LDST_ADDR: x1_cond [3] = (wa_load_r  & ap_ac3_r[5]) 
                            | (wa_store_r & ap_ac3_r[4]) 
                            ;
                             
    default:
    begin
      x1_cond [3] = 1'b0;
    end
  endcase

  x1_cond [4]    = 1'b0;

  case (ap_ac4_r[3:0])
  AT_INST_ADDR: x1_cond [4] = x1_pass & x2_enable;
  AT_AUXS_DATA,
  AT_AUXS_ADDR: x1_cond [4] = (wa_lr_op_r & ap_ac4_r[5] & (~excpn_in_prologue)) 
                            | (wa_sr_op_r & ap_ac4_r[4] & (~excpn_in_prologue))
                            ;
  AT_LDST_ADDR: x1_cond [4] = (wa_load_r  & ap_ac4_r[5]) 
                            | (wa_store_r & ap_ac4_r[4]) 
                            ;
                             
    default:
    begin
      x1_cond [4] = 1'b0;
    end
  endcase

  x1_cond [5]    = 1'b0;

  case (ap_ac5_r[3:0])
  AT_INST_ADDR: x1_cond [5] = x1_pass & x2_enable;
  AT_AUXS_DATA,
  AT_AUXS_ADDR: x1_cond [5] = (wa_lr_op_r & ap_ac5_r[5] & (~excpn_in_prologue)) 
                            | (wa_sr_op_r & ap_ac5_r[4] & (~excpn_in_prologue))
                            ;
  AT_LDST_ADDR: x1_cond [5] = (wa_load_r  & ap_ac5_r[5]) 
                            | (wa_store_r & ap_ac5_r[4]) 
                            ;
                             
    default:
    begin
      x1_cond [5] = 1'b0;
    end
  endcase

  x1_cond [6]    = 1'b0;

  case (ap_ac6_r[3:0])
  AT_INST_ADDR: x1_cond [6] = x1_pass & x2_enable;
  AT_AUXS_DATA,
  AT_AUXS_ADDR: x1_cond [6] = (wa_lr_op_r & ap_ac6_r[5] & (~excpn_in_prologue)) 
                            | (wa_sr_op_r & ap_ac6_r[4] & (~excpn_in_prologue))
                            ;
  AT_LDST_ADDR: x1_cond [6] = (wa_load_r  & ap_ac6_r[5]) 
                            | (wa_store_r & ap_ac6_r[4]) 
                            ;
                             
    default:
    begin
      x1_cond [6] = 1'b0;
    end
  endcase

  x1_cond [7]    = 1'b0;

  case (ap_ac7_r[3:0])
  AT_INST_ADDR: x1_cond [7] = x1_pass & x2_enable;
  AT_AUXS_DATA,
  AT_AUXS_ADDR: x1_cond [7] = (wa_lr_op_r & ap_ac7_r[5] & (~excpn_in_prologue)) 
                            | (wa_sr_op_r & ap_ac7_r[4] & (~excpn_in_prologue))
                            ;
  AT_LDST_ADDR: x1_cond [7] = (wa_load_r  & ap_ac7_r[5]) 
                            | (wa_store_r & ap_ac7_r[4]) 
                            ;
                             
    default:
    begin
      x1_cond [7] = 1'b0;
    end
  endcase

end // block : x1_cond_PROC
/*
  
  Logic to remember Triggers
  
*/
//
always @*
begin : reload_PROC

  reloadamv[0] = ca_trig[0] 
                     & ap_tkn
                     ;

  reloadamv[1] = ca_trig[1] 
                     & ap_tkn
                     ;

  reloadamv[2] = ca_trig[2] 
                     & ap_tkn
                     ;

  reloadamv[3] = ca_trig[3] 
                     & ap_tkn
                     ;

  reloadamv[4] = ca_trig[4] 
                     & ap_tkn
                     ;

  reloadamv[5] = ca_trig[5] 
                     & ap_tkn
                     ;

  reloadamv[6] = ca_trig[6] 
                     & ap_tkn
                     ;

  reloadamv[7] = ca_trig[7] 
                     & ap_tkn
                     ;


  reload_pc =  ap_tkn & !ca_bp_r;

end // block : reload_PROC
//

always @*
begin : apamv_PROC

  aps_active_comp = {`npuarc_APNUM_SIZE{1'b0}};
  i_halt_nxt      = 1'b0;
  x3_trig_comp    = {`npuarc_NUM_ACTIONPOINTS{1'b0}};

  casez (trig)

    { {7{1'b?}}, 1'b1  }: // AP : 0
    begin
      aps_active_comp   = `npuarc_APNUM_SIZE'd0;
      i_halt_nxt        = !action[0];
      x3_trig_comp [0] = if_ap [0];
      x3_bp_nxt         = if_ap  [0];
      x3_ex_nxt         = action [0];
      x3_dt_nxt         = 1'b1
                             //& !(action [0] & (excpn_evts[`INTEVT_PROLOGUE] | excpn_in_prologue))
                             ;
    end

    { {6{1'b?}}, 1'b1 ,{1{1'b0}} }: // AP : 1
    begin
      aps_active_comp   = `npuarc_APNUM_SIZE'd1;
      i_halt_nxt        = !action[1];
      x3_trig_comp [1] = if_ap [1];
      x3_bp_nxt         = if_ap  [1];
      x3_ex_nxt         = action [1];
      x3_dt_nxt         = 1'b1
                             //& !(action [1] & (excpn_evts[`INTEVT_PROLOGUE] | excpn_in_prologue))
                             ;
    end

    { {5{1'b?}}, 1'b1 ,{2{1'b0}} }: // AP : 2
    begin
      aps_active_comp   = `npuarc_APNUM_SIZE'd2;
      i_halt_nxt        = !action[2];
      x3_trig_comp [2] = if_ap [2];
      x3_bp_nxt         = if_ap  [2];
      x3_ex_nxt         = action [2];
      x3_dt_nxt         = 1'b1
                             //& !(action [2] & (excpn_evts[`INTEVT_PROLOGUE] | excpn_in_prologue))
                             ;
    end

    { {4{1'b?}}, 1'b1 ,{3{1'b0}} }: // AP : 3
    begin
      aps_active_comp   = `npuarc_APNUM_SIZE'd3;
      i_halt_nxt        = !action[3];
      x3_trig_comp [3] = if_ap [3];
      x3_bp_nxt         = if_ap  [3];
      x3_ex_nxt         = action [3];
      x3_dt_nxt         = 1'b1
                             //& !(action [3] & (excpn_evts[`INTEVT_PROLOGUE] | excpn_in_prologue))
                             ;
    end

    { {3{1'b?}}, 1'b1 ,{4{1'b0}} }: // AP : 4
    begin
      aps_active_comp   = `npuarc_APNUM_SIZE'd4;
      i_halt_nxt        = !action[4];
      x3_trig_comp [4] = if_ap [4];
      x3_bp_nxt         = if_ap  [4];
      x3_ex_nxt         = action [4];
      x3_dt_nxt         = 1'b1
                             //& !(action [4] & (excpn_evts[`INTEVT_PROLOGUE] | excpn_in_prologue))
                             ;
    end

    { {2{1'b?}}, 1'b1 ,{5{1'b0}} }: // AP : 5
    begin
      aps_active_comp   = `npuarc_APNUM_SIZE'd5;
      i_halt_nxt        = !action[5];
      x3_trig_comp [5] = if_ap [5];
      x3_bp_nxt         = if_ap  [5];
      x3_ex_nxt         = action [5];
      x3_dt_nxt         = 1'b1
                             //& !(action [5] & (excpn_evts[`INTEVT_PROLOGUE] | excpn_in_prologue))
                             ;
    end

    { {1{1'b?}}, 1'b1 ,{6{1'b0}} }: // AP : 6
    begin
      aps_active_comp   = `npuarc_APNUM_SIZE'd6;
      i_halt_nxt        = !action[6];
      x3_trig_comp [6] = if_ap [6];
      x3_bp_nxt         = if_ap  [6];
      x3_ex_nxt         = action [6];
      x3_dt_nxt         = 1'b1
                             //& !(action [6] & (excpn_evts[`INTEVT_PROLOGUE] | excpn_in_prologue))
                             ;
    end

    {  1'b1 ,{7{1'b0}} }: // AP : 7
    begin
      aps_active_comp   = `npuarc_APNUM_SIZE'd7;
      i_halt_nxt        = !action[7];
      x3_trig_comp [7] = if_ap [7];
      x3_bp_nxt         = if_ap  [7];
      x3_ex_nxt         = action [7];
      x3_dt_nxt         = 1'b1
                             //& !(action [7] & (excpn_evts[`INTEVT_PROLOGUE] | excpn_in_prologue))
                             ;
    end
    default:
    begin
      aps_active_comp   = {`npuarc_APNUM_SIZE{1'b0}};
      i_halt_nxt        = 1'b0;
      x3_trig_comp      = {`npuarc_NUM_ACTIONPOINTS{1'b0}};
      x3_bp_nxt         = 1'b0;
      x3_ex_nxt         = 1'b0;
      x3_dt_nxt         = 1'b0;
    end
  endcase

end // block : apamv_PROC
//
always @*
begin : hit__PROC

  hit[0] = ((match_r[0] ^ mode[0]) & cond[0])
               & match_vld_r [0]
               & !( 1'b0
                  )
               ;

  hit[1] = ((match_r[1] ^ mode[1]) & cond[1])
               & match_vld_r [1]
               & !( 1'b0
                  )
               ;

  hit[2] = ((match_r[2] ^ mode[2]) & cond[2])
               & match_vld_r [2]
               & !( 1'b0
                  )
               ;

  hit[3] = ((match_r[3] ^ mode[3]) & cond[3])
               & match_vld_r [3]
               & !( 1'b0
                  )
               ;

  hit[4] = ((match_r[4] ^ mode[4]) & cond[4])
               & match_vld_r [4]
               & !( 1'b0
                  )
               ;

  hit[5] = ((match_r[5] ^ mode[5]) & cond[5])
               & match_vld_r [5]
               & !( 1'b0
                  )
               ;

  hit[6] = ((match_r[6] ^ mode[6]) & cond[6])
               & match_vld_r [6]
               & !( 1'b0
                  )
               ;

  hit[7] = ((match_r[7] ^ mode[7]) & cond[7])
               & match_vld_r [7]
               & !( 1'b0
                  )
               ;


end // block : hit__PROC
//
always @*
begin : x2_trig_PROC

  x2_trig_comp[0] = ( 1'b0
                          | (trig[0] & 1'b1)
                          | (trig[7] & paired[7])
                          | (trig[7] & quad[7])
                          | (trig[6] & quad[6])
                          | (trig[5] & quad[5])
                          )
                       ;

  x2_trig_comp[1] = ( 1'b0
                          | (trig[1] & 1'b1)
                          | (trig[0] & paired[0])
                          | (trig[0] & quad[0])
                          | (trig[7] & quad[7])
                          | (trig[6] & quad[6])
                          )
                       ;

  x2_trig_comp[2] = ( 1'b0
                          | (trig[2] & 1'b1)
                          | (trig[1] & paired[1])
                          | (trig[1] & quad[1])
                          | (trig[0] & quad[0])
                          | (trig[7] & quad[7])
                          )
                       ;

  x2_trig_comp[3] = ( 1'b0
                          | (trig[3] & 1'b1)
                          | (trig[2] & paired[2])
                          | (trig[2] & quad[2])
                          | (trig[1] & quad[1])
                          | (trig[0] & quad[0])
                          )
                       ;

  x2_trig_comp[4] = ( 1'b0
                          | (trig[4] & 1'b1)
                          | (trig[3] & paired[3])
                          | (trig[3] & quad[3])
                          | (trig[2] & quad[2])
                          | (trig[1] & quad[1])
                          )
                       ;

  x2_trig_comp[5] = ( 1'b0
                          | (trig[5] & 1'b1)
                          | (trig[4] & paired[4])
                          | (trig[4] & quad[4])
                          | (trig[3] & quad[3])
                          | (trig[2] & quad[2])
                          )
                       ;

  x2_trig_comp[6] = ( 1'b0
                          | (trig[6] & 1'b1)
                          | (trig[5] & paired[5])
                          | (trig[5] & quad[5])
                          | (trig[4] & quad[4])
                          | (trig[3] & quad[3])
                          )
                       ;

  x2_trig_comp[7] = ( 1'b0
                          | (trig[7] & 1'b1)
                          | (trig[6] & paired[6])
                          | (trig[6] & quad[6])
                          | (trig[5] & quad[5])
                          | (trig[4] & quad[4])
                          )
                       ;


end // block :  ca_trig_PROC
//

always @*
begin: x2_cond_nxt_PROC
  x2_cond_nxt = (x1_cond[0] & (|ap_ac0_r[5:4]))
                      | (x1_cond[1] & (|ap_ac1_r[5:4]) 
                        )
                      | (x1_cond[2] & (|ap_ac2_r[5:4]) 
                        )
                      | (x1_cond[3] & (|ap_ac3_r[5:4]) 
                        )
                      | (x1_cond[4] & (|ap_ac4_r[5:4]) 
                        )
                      | (x1_cond[5] & (|ap_ac5_r[5:4]) 
                        )
                      | (x1_cond[6] & (|ap_ac6_r[5:4]) 
                        )
                      | (x1_cond[7] & (|ap_ac7_r[5:4]) 
                        )
                      ; 
end

always @(posedge ap_unit_clk or posedge rst_a)
begin: x2_cond_reg_PROC
  if (rst_a == 1'b1) begin
    x2_cond_r <= 1'b0; 
  end
  else begin
    x2_cond_r <= x2_cond_nxt;
  end
end

// New Actionpoint clock gate based on aux regs tt_read and tt_write
always @*
begin : ap_enables_PROC

  // Pipe stage Enables
  x3_ap_en_nxt[0] = (tt_read[0] | tt_write[0])
                        ;
  x3_ap_en_nxt[1] = (tt_read[1] | tt_write[1])
                        ;
  x3_ap_en_nxt[2] = (tt_read[2] | tt_write[2])
                        ;
  x3_ap_en_nxt[3] = (tt_read[3] | tt_write[3])
                        ;
  x3_ap_en_nxt[4] = (tt_read[4] | tt_write[4])
                        ;
  x3_ap_en_nxt[5] = (tt_read[5] | tt_write[5])
                        ;
  x3_ap_en_nxt[6] = (tt_read[6] | tt_write[6])
                        ;
  x3_ap_en_nxt[7] = (tt_read[7] | tt_write[7])
                        ;

  // Individual AP Pipe Enables
  ap_en[0] = |ap_ac0_r[5:4]
                        ;
  ap_en[1] = |ap_ac1_r[5:4]
                        ;
  ap_en[2] = |ap_ac2_r[5:4]
                        ;
  ap_en[3] = |ap_ac3_r[5:4]
                        ;
  ap_en[4] = |ap_ac4_r[5:4]
                        ;
  ap_en[5] = |ap_ac5_r[5:4]
                        ;
  ap_en[6] = |ap_ac6_r[5:4]
                        ;
  ap_en[7] = |ap_ac7_r[5:4]
                        ;

  // AP Feature Enable
  ap_pipe_active = (1'b0
                 | (|ap_ac0_r[5:4])                     // 1.0
                 | (|ap_ac1_r[5:4])                     // 1.1
                 | (|ap_ac2_r[5:4])                     // 1.2
                 | (|ap_ac3_r[5:4])                     // 1.3
                 | (|ap_ac4_r[5:4])                     // 1.4
                 | (|ap_ac5_r[5:4])                     // 1.5
                 | (|ap_ac6_r[5:4])                     // 1.6
                 | (|ap_ac7_r[5:4])                     // 1.7
                    )
                 ;

  // 
  // AP Unit (with 1-cycle clocking delay) is enabled when 
  // 1. Aux unit is active (To ensure any corner case WP are sampled)
  // 2. Any of the Actionpoints are enabled
  // 3. Any Watchpoints that are pending after all the Actionpoints are disabled
  // 4. Additional clock due clocking delay after condition 1
  // 
  ap_unit_enable = 1'b0
                 | aux_aps_active
                 | ap_pipe_active
                 | aux_aps_wen_r
                 | ap_enb_ext_r
                 | aux_aps_ren_r
                 ;

  // 
  // When all AP pipes are disabled extension needs to be check for any terminal WP
  // Extend AP Unit if there are any pending Watchpoint in the AP pipe stages (AP1:AP-commit)
  // ap_enb_ext_r used to extend ap_unit_enable if ap_unit_enable is going low before transactions have finished
  // 
  ap_enb_ext_nxt = 1'b0
//                   | (|x1_cond)                         // AP1
                   | x2_cond_r                          // AP2
                   | x3_dt_r                            // AP3
                   | ca_dt_r                            // AP - Commit
                 ;

end // block : ap_enables_PROC
// 
always @(posedge ap_aux_clk or posedge rst_a) 
begin : ap_enb_ext_reg_PROC
  if (rst_a == 1'b1) begin
    ap_enb_ext_r         <= 1'b0;
  end
  else begin
    ap_enb_ext_r         <= ap_enb_ext_nxt;
  end
end // block : ap_enb_ext_reg_PROC
//
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining Actionpoints Match Value (X2)               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

reg                 ap1_in_excpn_r;
reg                 ap2_in_excpn_r;

// spyglass disable_block Reset_sync04
// SMD: reset signal synced multiple times in same domain
// SJ:  not an issue, tested and causes no issues, other resync spot in alb_reset_ctrl already waived
always @(posedge ap_unit_clk or posedge rst_a) 
begin : ap_excpn_reg_PROC
  if (rst_a == 1'b1) begin
    ap1_in_excpn_r  <= 1'b0;
    ap2_in_excpn_r  <= 1'b0;
  end
  else begin
    ap1_in_excpn_r  <= (|excpn_evts | excpn_in_prologue);
    ap2_in_excpn_r  <= ap1_in_excpn_r;
  end
end // block : ap_excpn_reg_PROC
// spyglass enable_block Reset_sync04

always @*
begin : match_comp_PROC

  match_raw_cg[0] = x1_cond [0]
                        ;

  match_cg[0]     = match_raw_cg[0] & ap_en[0];         

  match_raw_cg[1] = x1_cond [1]
                        ;

  match_cg[1]     = match_raw_cg[1] & ap_en[1];         

  match_raw_cg[2] = x1_cond [2]
                        ;

  match_cg[2]     = match_raw_cg[2] & ap_en[2];         

  match_raw_cg[3] = x1_cond [3]
                        ;

  match_cg[3]     = match_raw_cg[3] & ap_en[3];         

  match_raw_cg[4] = x1_cond [4]
                        ;

  match_cg[4]     = match_raw_cg[4] & ap_en[4];         

  match_raw_cg[5] = x1_cond [5]
                        ;

  match_cg[5]     = match_raw_cg[5] & ap_en[5];         

  match_raw_cg[6] = x1_cond [6]
                        ;

  match_cg[6]     = match_raw_cg[6] & ap_en[6];         

  match_raw_cg[7] = x1_cond [7]
                        ;

  match_cg[7]     = match_raw_cg[7] & ap_en[7];         


  match_nxt [0] = match[0];

  // A match is valid only if
  // 1. ASR bit is cleared
  match_vld_nxt [0] =  1'b1
                          & !wa_asr_r[0] // 1
                          & |ap_ac0_r[5:4]  // 2
                          & !(action [0] & ap2_in_excpn_r)
                          ; 

  match_nxt [1] = match[1];

  // A match is valid only if
  // 1. ASR bit is cleared
  match_vld_nxt [1] =  1'b1
                          & !wa_asr_r[1] // 1
                          & |ap_ac1_r[5:4]  // 2
                          & !(action [1] & ap2_in_excpn_r)
                          ; 

  match_nxt [2] = match[2];

  // A match is valid only if
  // 1. ASR bit is cleared
  match_vld_nxt [2] =  1'b1
                          & !wa_asr_r[2] // 1
                          & |ap_ac2_r[5:4]  // 2
                          & !(action [2] & ap2_in_excpn_r)
                          ; 

  match_nxt [3] = match[3];

  // A match is valid only if
  // 1. ASR bit is cleared
  match_vld_nxt [3] =  1'b1
                          & !wa_asr_r[3] // 1
                          & |ap_ac3_r[5:4]  // 2
                          & !(action [3] & ap2_in_excpn_r)
                          ; 

  match_nxt [4] = match[4];

  // A match is valid only if
  // 1. ASR bit is cleared
  match_vld_nxt [4] =  1'b1
                          & !wa_asr_r[4] // 1
                          & |ap_ac4_r[5:4]  // 2
                          & !(action [4] & ap2_in_excpn_r)
                          ; 

  match_nxt [5] = match[5];

  // A match is valid only if
  // 1. ASR bit is cleared
  match_vld_nxt [5] =  1'b1
                          & !wa_asr_r[5] // 1
                          & |ap_ac5_r[5:4]  // 2
                          & !(action [5] & ap2_in_excpn_r)
                          ; 

  match_nxt [6] = match[6];

  // A match is valid only if
  // 1. ASR bit is cleared
  match_vld_nxt [6] =  1'b1
                          & !wa_asr_r[6] // 1
                          & |ap_ac6_r[5:4]  // 2
                          & !(action [6] & ap2_in_excpn_r)
                          ; 

  match_nxt [7] = match[7];

  // A match is valid only if
  // 1. ASR bit is cleared
  match_vld_nxt [7] =  1'b1
                          & !wa_asr_r[7] // 1
                          & |ap_ac7_r[5:4]  // 2
                          & !(action [7] & ap2_in_excpn_r)
                          ; 


end // block : match_comp_PROC
//

wire [`npuarc_APS_RANGE] match_inter = {      // intermediate match
  match_cg[7] ? match_nxt[7]   : match_r[7],
  match_cg[6] ? match_nxt[6]   : match_r[6],
  match_cg[5] ? match_nxt[5]   : match_r[5],
  match_cg[4] ? match_nxt[4]   : match_r[4],
  match_cg[3] ? match_nxt[3]   : match_r[3],
  match_cg[2] ? match_nxt[2]   : match_r[2],
  match_cg[1] ? match_nxt[1]   : match_r[1],
  match_cg[0] ? match_nxt[0]     : match_r[0]
  };

wire [`npuarc_APS_RANGE] match_vld_inter = {  // intermediate match valid
  match_cg[7] ? match_vld_nxt[7] : match_vld_r[7],
  match_cg[6] ? match_vld_nxt[6] : match_vld_r[6],
  match_cg[5] ? match_vld_nxt[5] : match_vld_r[5],
  match_cg[4] ? match_vld_nxt[4] : match_vld_r[4],
  match_cg[3] ? match_vld_nxt[3] : match_vld_r[3],
  match_cg[2] ? match_vld_nxt[2] : match_vld_r[2],
  match_cg[1] ? match_vld_nxt[1] : match_vld_r[1],
  match_cg[0] ? match_vld_nxt[0]   : match_vld_r[0]
  };

always @(posedge ap_unit_clk or posedge rst_a)
begin : match_reg_PROC
  if (rst_a == 1'b1) begin
    match_r       <= {`npuarc_NUM_ACTIONPOINTS{1'b0}};
    match_vld_r   <= {`npuarc_NUM_ACTIONPOINTS{1'b0}};
  end
  else begin
    match_r       <= match_inter;
    match_vld_r   <= match_vld_inter;
  end
end // block : match_reg_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining Actionpoints Match Value (X2)               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge ap_unit_clk or posedge rst_a)
begin : x2_amv0_reg_PROC
  if (rst_a == 1'b1) begin
    x2_amv0_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (match_cg[0]) begin
    x2_amv0_r <= mvalue_0;
  end
end // block : x2_amv_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x2_amv1_reg_PROC
  if (rst_a == 1'b1) begin
    x2_amv1_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (match_cg[1]) begin
    x2_amv1_r <= mvalue_1;
  end
end // block : x2_amv_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x2_amv2_reg_PROC
  if (rst_a == 1'b1) begin
    x2_amv2_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (match_cg[2]) begin
    x2_amv2_r <= mvalue_2;
  end
end // block : x2_amv_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x2_amv3_reg_PROC
  if (rst_a == 1'b1) begin
    x2_amv3_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (match_cg[3]) begin
    x2_amv3_r <= mvalue_3;
  end
end // block : x2_amv_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x2_amv4_reg_PROC
  if (rst_a == 1'b1) begin
    x2_amv4_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (match_cg[4]) begin
    x2_amv4_r <= mvalue_4;
  end
end // block : x2_amv_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x2_amv5_reg_PROC
  if (rst_a == 1'b1) begin
    x2_amv5_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (match_cg[5]) begin
    x2_amv5_r <= mvalue_5;
  end
end // block : x2_amv_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x2_amv6_reg_PROC
  if (rst_a == 1'b1) begin
    x2_amv6_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (match_cg[6]) begin
    x2_amv6_r <= mvalue_6;
  end
end // block : x2_amv_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x2_amv7_reg_PROC
  if (rst_a == 1'b1) begin
    x2_amv7_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (match_cg[7]) begin
    x2_amv7_r <= mvalue_7;
  end
end // block : x2_amv_reg_PROC


always @(posedge ap_unit_clk or posedge rst_a)
begin : x2_wppc_reg_PROC
  if (rst_a == 1'b1) begin
    x2_wppc_r     <= `npuarc_PC_BITS'd0;
  end
  else if (|match_cg) begin
    x2_wppc_r    <= ca_uop_active_r
                    ? ar_pc_r         // UOP PC
                    : wa_pc           // Regular
                    ;
  end
end // block : x2_wppc_reg_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining Actionpoints Match Value (X3)               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//

always @(posedge ap_unit_clk or posedge rst_a)
begin : x3amv0_reg_PROC
  if (rst_a == 1'b1) begin
    x3_amv0_r  <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (x3_dt_cg[0] == 1'b1) begin
    x3_amv0_r <= x2_amv0_r;
  end
end // block : x3amv0_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x3amv1_reg_PROC
  if (rst_a == 1'b1) begin
    x3_amv1_r  <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (x3_dt_cg[1] == 1'b1) begin
    x3_amv1_r <= x2_amv1_r;
  end
end // block : x3amv1_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x3amv2_reg_PROC
  if (rst_a == 1'b1) begin
    x3_amv2_r  <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (x3_dt_cg[2] == 1'b1) begin
    x3_amv2_r <= x2_amv2_r;
  end
end // block : x3amv2_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x3amv3_reg_PROC
  if (rst_a == 1'b1) begin
    x3_amv3_r  <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (x3_dt_cg[3] == 1'b1) begin
    x3_amv3_r <= x2_amv3_r;
  end
end // block : x3amv3_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x3amv4_reg_PROC
  if (rst_a == 1'b1) begin
    x3_amv4_r  <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (x3_dt_cg[4] == 1'b1) begin
    x3_amv4_r <= x2_amv4_r;
  end
end // block : x3amv4_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x3amv5_reg_PROC
  if (rst_a == 1'b1) begin
    x3_amv5_r  <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (x3_dt_cg[5] == 1'b1) begin
    x3_amv5_r <= x2_amv5_r;
  end
end // block : x3amv5_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x3amv6_reg_PROC
  if (rst_a == 1'b1) begin
    x3_amv6_r  <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (x3_dt_cg[6] == 1'b1) begin
    x3_amv6_r <= x2_amv6_r;
  end
end // block : x3amv6_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : x3amv7_reg_PROC
  if (rst_a == 1'b1) begin
    x3_amv7_r  <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (x3_dt_cg[7] == 1'b1) begin
    x3_amv7_r <= x2_amv7_r;
  end
end // block : x3amv7_reg_PROC


always @(posedge ap_unit_clk or posedge rst_a)
begin : x3_trig_reg_PROC
  if (rst_a == 1'b1) begin
    x3_wppc_r     <= {`npuarc_PC_BITS{1'b0}}        ;
    x3_trig_r     <= {`npuarc_NUM_ACTIONPOINTS{1'b0}};
    x3_trigg_r    <= {`npuarc_NUM_ACTIONPOINTS{1'b0}};
    x3_bps_r      <= {`npuarc_NUM_ACTIONPOINTS{1'b0}};
  end
  else if (x3_dt_raw_cg == 1'b1) begin
    x3_wppc_r    <= x3_wppc_nxt ;
    x3_bps_r     <= if_ap            ;
    x3_trig_r    <= x3_trig_nxt ;
    x3_trigg_r   <= trig        ;
  end
end // block : x3_trig_reg_PROC

//

always @(posedge ap_unit_clk or posedge rst_a)
begin : caamv0_reg_PROC
  if (rst_a == 1'b1) begin
    ca_amv0_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (ca_dt_cg[0] == 1'b1) begin
    ca_amv0_r <= x3_amv0_r;
  end
end // block : caamv0_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : caamv1_reg_PROC
  if (rst_a == 1'b1) begin
    ca_amv1_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (ca_dt_cg[1] == 1'b1) begin
    ca_amv1_r <= x3_amv1_r;
  end
end // block : caamv1_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : caamv2_reg_PROC
  if (rst_a == 1'b1) begin
    ca_amv2_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (ca_dt_cg[2] == 1'b1) begin
    ca_amv2_r <= x3_amv2_r;
  end
end // block : caamv2_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : caamv3_reg_PROC
  if (rst_a == 1'b1) begin
    ca_amv3_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (ca_dt_cg[3] == 1'b1) begin
    ca_amv3_r <= x3_amv3_r;
  end
end // block : caamv3_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : caamv4_reg_PROC
  if (rst_a == 1'b1) begin
    ca_amv4_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (ca_dt_cg[4] == 1'b1) begin
    ca_amv4_r <= x3_amv4_r;
  end
end // block : caamv4_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : caamv5_reg_PROC
  if (rst_a == 1'b1) begin
    ca_amv5_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (ca_dt_cg[5] == 1'b1) begin
    ca_amv5_r <= x3_amv5_r;
  end
end // block : caamv5_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : caamv6_reg_PROC
  if (rst_a == 1'b1) begin
    ca_amv6_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (ca_dt_cg[6] == 1'b1) begin
    ca_amv6_r <= x3_amv6_r;
  end
end // block : caamv6_reg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : caamv7_reg_PROC
  if (rst_a == 1'b1) begin
    ca_amv7_r  <= `npuarc_DATA_SIZE'd0;
  end
  else if (ca_dt_cg[7] == 1'b1) begin
    ca_amv7_r <= x3_amv7_r;
  end
end // block : caamv7_reg_PROC


always @(posedge ap_unit_clk or posedge rst_a)
begin : ca_trig_reg_PROC
  if (rst_a == 1'b1) begin
    ca_wppc_r     <= `npuarc_PC_BITS'd0;
    ca_trig       <= `npuarc_NUM_ACTIONPOINTS'd0;
  end
  else if (ca_dt_raw_cg == 1'b1) begin
    ca_wppc_r    <= x3_wppc_r;
    ca_trig      <= ca_trig_nxt;
  end
end // block : ca_trig_reg_PROC
//

always @(posedge ap_unit_clk or posedge rst_a)
begin : ap2_aux_0_reg_PROC
  if (rst_a == 1'b1) begin
    ap2_ac0_r  <= 10'd0;
  end
  else if (ap_ac0_wen_r == 1'b1) begin
    ap2_ac0_r  <= ap_ac0_r;
  end
end // block : ap2_aux_0_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap2_aux_1_reg_PROC
  if (rst_a == 1'b1) begin
    ap2_ac1_r  <= 10'd0;
  end
  else if (ap_ac1_wen_r == 1'b1) begin
    ap2_ac1_r  <= ap_ac1_r;
  end
end // block : ap2_aux_1_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap2_aux_2_reg_PROC
  if (rst_a == 1'b1) begin
    ap2_ac2_r  <= 10'd0;
  end
  else if (ap_ac2_wen_r == 1'b1) begin
    ap2_ac2_r  <= ap_ac2_r;
  end
end // block : ap2_aux_2_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap2_aux_3_reg_PROC
  if (rst_a == 1'b1) begin
    ap2_ac3_r  <= 10'd0;
  end
  else if (ap_ac3_wen_r == 1'b1) begin
    ap2_ac3_r  <= ap_ac3_r;
  end
end // block : ap2_aux_3_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap2_aux_4_reg_PROC
  if (rst_a == 1'b1) begin
    ap2_ac4_r  <= 10'd0;
  end
  else if (ap_ac4_wen_r == 1'b1) begin
    ap2_ac4_r  <= ap_ac4_r;
  end
end // block : ap2_aux_4_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap2_aux_5_reg_PROC
  if (rst_a == 1'b1) begin
    ap2_ac5_r  <= 10'd0;
  end
  else if (ap_ac5_wen_r == 1'b1) begin
    ap2_ac5_r  <= ap_ac5_r;
  end
end // block : ap2_aux_5_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap2_aux_6_reg_PROC
  if (rst_a == 1'b1) begin
    ap2_ac6_r  <= 10'd0;
  end
  else if (ap_ac6_wen_r == 1'b1) begin
    ap2_ac6_r  <= ap_ac6_r;
  end
end // block : ap2_aux_6_reg_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap2_aux_7_reg_PROC
  if (rst_a == 1'b1) begin
    ap2_ac7_r  <= 10'd0;
  end
  else if (ap_ac7_wen_r == 1'b1) begin
    ap2_ac7_r  <= ap_ac7_r;
  end
end // block : ap2_aux_7_reg_PROC
//

always @*
begin : ap_ar_nxt_PROC

  // A1
  ap1_ar_ub_nxt  = 1'b0
                   | !ar_aux_status32_r[`npuarc_U_FLAG]
                   |  ar_aux_debug_r[`npuarc_DEBUG_UB]
                   ;

  ap1_ar_cg   = ap_unit_enable;


  // A2
  ap2_ar_ub_nxt  = 1'b0
                   | ap1_ar_ub_r
                   ;

  // A3
  ap3_ar_ub_nxt  = 1'b0
                   | ap2_ar_ub_r
                   ;

  // A4
  ap4_ar_ub_nxt  = 1'b0
                   | ap3_ar_ub_r
                   ;


  ap2_ar_cg   = ap_unit_enable
              & (|x1_cond)
              ;

  ap3_ar_cg   = ap_unit_enable
              & x3_dt_raw_cg
              ;

  ap4_ar_cg   = ap_unit_enable
              & ca_dt_raw_cg
              ;


end // block : ap_ar_nxt_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap_1_ar_reg_PROC
  if (rst_a == 1'b1) begin
    ap1_ar_ub_r  <= 1'b0;
  end
  else if (ap1_ar_cg == 1'b1) begin
    ap1_ar_ub_r  <=  ap1_ar_ub_nxt;
  end
end // block : ap_1_ar_reg_PROC
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap_2_ar_reg_PROC
  if (rst_a == 1'b1) begin
    ap2_ar_ub_r  <= 1'b0;
  end
  else if (ap2_ar_cg == 1'b1) begin
    ap2_ar_ub_r  <=  ap2_ar_ub_nxt;
  end
end // block : ap_2_ar_reg_PROC
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap_3_ar_reg_PROC
  if (rst_a == 1'b1) begin
    ap3_ar_ub_r  <= 1'b0;
  end
  else if (ap3_ar_cg == 1'b1) begin
    ap3_ar_ub_r  <=  ap3_ar_ub_nxt;
  end
end // block : ap_3_ar_reg_PROC
always @(posedge ap_unit_clk or posedge rst_a)
begin : ap_4_ar_reg_PROC
  if (rst_a == 1'b1) begin
    ap4_ar_ub_r  <= 1'b0;
  end
  else if (ap4_ar_cg == 1'b1) begin
    ap4_ar_ub_r  <=  ap4_ar_ub_nxt;
  end
end // block : ap_4_ar_reg_PROC
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining Actionpoints auxiliary registers            //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_amm_aux0_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amm0_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amm0_wen  == 1'b1) begin
    ap_amm0_r    <= wa_sr_data_r;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_amm_aux1_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amm1_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amm1_wen  == 1'b1) begin
    ap_amm1_r    <= wa_sr_data_r;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_amm_aux2_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amm2_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amm2_wen  == 1'b1) begin
    ap_amm2_r    <= wa_sr_data_r;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_amm_aux3_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amm3_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amm3_wen  == 1'b1) begin
    ap_amm3_r    <= wa_sr_data_r;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_amm_aux4_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amm4_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amm4_wen  == 1'b1) begin
    ap_amm4_r    <= wa_sr_data_r;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_amm_aux5_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amm5_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amm5_wen  == 1'b1) begin
    ap_amm5_r    <= wa_sr_data_r;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_amm_aux6_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amm6_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amm6_wen  == 1'b1) begin
    ap_amm6_r    <= wa_sr_data_r;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_amm_aux7_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amm7_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amm7_wen  == 1'b1) begin
    ap_amm7_r    <= wa_sr_data_r;
  end
end // block : ap_aux_reg_PROC
//

always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_wen_aux0_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac0_wen_r <= 1'b0;
  end
  else if (aux_aps_wen_r   == 1'b1) begin
    ap_ac0_wen_r <= ap_ac0_wen;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_wen_aux1_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac1_wen_r <= 1'b0;
  end
  else if (aux_aps_wen_r   == 1'b1) begin
    ap_ac1_wen_r <= ap_ac1_wen;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_wen_aux2_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac2_wen_r <= 1'b0;
  end
  else if (aux_aps_wen_r   == 1'b1) begin
    ap_ac2_wen_r <= ap_ac2_wen;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_wen_aux3_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac3_wen_r <= 1'b0;
  end
  else if (aux_aps_wen_r   == 1'b1) begin
    ap_ac3_wen_r <= ap_ac3_wen;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_wen_aux4_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac4_wen_r <= 1'b0;
  end
  else if (aux_aps_wen_r   == 1'b1) begin
    ap_ac4_wen_r <= ap_ac4_wen;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_wen_aux5_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac5_wen_r <= 1'b0;
  end
  else if (aux_aps_wen_r   == 1'b1) begin
    ap_ac5_wen_r <= ap_ac5_wen;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_wen_aux6_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac6_wen_r <= 1'b0;
  end
  else if (aux_aps_wen_r   == 1'b1) begin
    ap_ac6_wen_r <= ap_ac6_wen;
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_wen_aux7_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac7_wen_r <= 1'b0;
  end
  else if (aux_aps_wen_r   == 1'b1) begin
    ap_ac7_wen_r <= ap_ac7_wen;
  end
end // block : ap_aux_reg_PROC
//

always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_aux0_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac0_r     <= {10{1'b0}};
  end
  else if (ap_ac0_wen   == 1'b1) begin
    ap_ac0_r     <= wa_sr_data_r[9:0];
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_aux1_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac1_r     <= {10{1'b0}};
  end
  else if (ap_ac1_wen   == 1'b1) begin
    ap_ac1_r     <= wa_sr_data_r[9:0];
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_aux2_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac2_r     <= {10{1'b0}};
  end
  else if (ap_ac2_wen   == 1'b1) begin
    ap_ac2_r     <= wa_sr_data_r[9:0];
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_aux3_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac3_r     <= {10{1'b0}};
  end
  else if (ap_ac3_wen   == 1'b1) begin
    ap_ac3_r     <= wa_sr_data_r[9:0];
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_aux4_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac4_r     <= {10{1'b0}};
  end
  else if (ap_ac4_wen   == 1'b1) begin
    ap_ac4_r     <= wa_sr_data_r[9:0];
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_aux5_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac5_r     <= {10{1'b0}};
  end
  else if (ap_ac5_wen   == 1'b1) begin
    ap_ac5_r     <= wa_sr_data_r[9:0];
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_aux6_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac6_r     <= {10{1'b0}};
  end
  else if (ap_ac6_wen   == 1'b1) begin
    ap_ac6_r     <= wa_sr_data_r[9:0];
  end
end // block : ap_aux_reg_PROC
//
always @(posedge ap_aux_clk or posedge rst_a)
begin : ap_ac_aux7_reg_PROC
  if (rst_a == 1'b1) begin
    ap_ac7_r     <= {10{1'b0}};
  end
  else if (ap_ac7_wen   == 1'b1) begin
    ap_ac7_r     <= wa_sr_data_r[9:0];
  end
end // block : ap_aux_reg_PROC
//

always @(posedge ap_unit_clk or posedge rst_a)
begin : amv0aux_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amv0_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amv0_wen  == 1'b1) begin
    ap_amv0_r    <= ap_amv0_nxt;
  end
end // block : amv0aux_reg_PROC
always @(posedge ap_unit_clk or posedge rst_a)
begin : amv1aux_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amv1_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amv1_wen  == 1'b1) begin
    ap_amv1_r    <= ap_amv1_nxt;
  end
end // block : amv1aux_reg_PROC
always @(posedge ap_unit_clk or posedge rst_a)
begin : amv2aux_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amv2_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amv2_wen  == 1'b1) begin
    ap_amv2_r    <= ap_amv2_nxt;
  end
end // block : amv2aux_reg_PROC
always @(posedge ap_unit_clk or posedge rst_a)
begin : amv3aux_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amv3_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amv3_wen  == 1'b1) begin
    ap_amv3_r    <= ap_amv3_nxt;
  end
end // block : amv3aux_reg_PROC
always @(posedge ap_unit_clk or posedge rst_a)
begin : amv4aux_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amv4_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amv4_wen  == 1'b1) begin
    ap_amv4_r    <= ap_amv4_nxt;
  end
end // block : amv4aux_reg_PROC
always @(posedge ap_unit_clk or posedge rst_a)
begin : amv5aux_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amv5_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amv5_wen  == 1'b1) begin
    ap_amv5_r    <= ap_amv5_nxt;
  end
end // block : amv5aux_reg_PROC
always @(posedge ap_unit_clk or posedge rst_a)
begin : amv6aux_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amv6_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amv6_wen  == 1'b1) begin
    ap_amv6_r    <= ap_amv6_nxt;
  end
end // block : amv6aux_reg_PROC
always @(posedge ap_unit_clk or posedge rst_a)
begin : amv7aux_reg_PROC
  if (rst_a == 1'b1) begin
    ap_amv7_r    <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ap_amv7_wen  == 1'b1) begin
    ap_amv7_r    <= ap_amv7_nxt;
  end
end // block : amv7aux_reg_PROC



////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining WA pipeline data op registers               //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : wa2_addr_mem_nxt_PROC

  // WA2 Load nxt
  // 1. WA Load
  // 2. Not Prefetch
  // 3. Not Debug
  wa2_ald_nxt =  1'b1
                   &  wa_load_r  // (1)
                   & !wa_pref_r  // (2)
                   & !db_active       // (3)
                   ;

  // WA2 Store nxt
  // 1. WA Store
  // 2. Not Debug
  wa2_ast_nxt =  1'b1
                   &  wa_store_r  // (1)
                   & !db_active        // (2)
                   ;

end // block : wa2_addr_mem_nxt_PROC
//
//
always @*
begin : wa2_addr_mem_cg_PROC

  wa2_ald_cg  =  1'b0
                   | (wa2_ald_nxt & wa_enable)
                   | (wa2_ald_r   & wa_enable)
                   ;

  wa2_ast_cg  =  1'b0
                   | (wa2_ast_nxt & wa_enable)
                   | (wa2_ast_r   & wa_enable)
                   ;

end // block : wa2_addr_mem_cg_PROC
//
//

always @(posedge ap_unit_clk or posedge rst_a)
begin : wa2_ctrl_op_PROC
  if (rst_a == 1'b1) begin
    wa2_lr_op_r    <= 1'b0;
    wa2_sr_op_r    <= 1'b0;
  end
  else if (wa_enable & ap_unit_enable) begin
    wa2_lr_op_r   <= wa_lr_op_r & wa_rf_wenb0_r & (~db_active) & (~excpn_in_prologue);
    wa2_sr_op_r   <= wa_sr_op_r & (~db_active) & (~excpn_in_prologue);
  end
end


always @(posedge ap_unit_clk or posedge rst_a)
begin : wa2_ctrl_ast_PROC
  if (rst_a == 1'b1) begin
    wa2_ast_r      <= 1'b0;
  end
  else if (wa2_ast_cg & ap_unit_enable) begin
    wa2_ast_r   <= wa2_ast_nxt;
  end
end


always @(posedge ap_unit_clk or posedge rst_a)
begin : wa2_ctrl_ald_PROC
  if (rst_a == 1'b1) begin
    wa2_ald_r      <= 1'b0;
  end
  else if (wa2_ald_cg & ap_unit_enable) begin
    wa2_ald_r   <= wa2_ald_nxt;
  end
end







always @(posedge ap_unit_clk or posedge rst_a)
begin : wa2_ctrl_sys_halt_PROC
  if (rst_a == 1'b1) begin
    sys_halt_2r   <= 1'b0;
  end
  else begin
    sys_halt_2r   <= sys_halt_r;
  end
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining pipeline address register                   //
//                                                                        //
////////////////////////////////////////////////////////////////////////////


always @*
begin :  wa_addr_ctrl_PROC

  x3_addr_cg = (x2_pass & x3_enable & ap_unit_enable)
             & (1'b0
               | x2_lr_op_r
               | x2_sr_op_r
               | x2_load_r
               | x2_store_r
               )
             ;
// spyglass disable_block Ac_conv01
// SMD: syncs converging on gate
// SJ:  cdc syncs are independent and chance of glitch is very low
  ca_addr_cg = (x3_pass & ca_enable & ap_unit_enable)
             & (1'b0
               | x3_lr_op_r
               | x3_sr_op_r
               | x3_load_r
               | x3_store_r
               )
             ;
// spyglass enable_block Ac_conv01
  wa_addr_cg = (ca_pass & wa_enable & ap_unit_enable)
             & (1'b0
               | (ca_lr_op_r & (~excpn_in_prologue))
               | (ca_sr_op_r & (~excpn_in_prologue))
               | ca_store_r
               | ca_load_r
               )
             ;

end // block : wa_data_ctrl_PROC

always @*
begin : x3_addr_nxt_PROC

  x2_aux_op      = x2_lr_op_r | x2_sr_op_r;
  
  x3_addr_nxt    = (x2_aux_op == 1'b1) 
                      ? x2_aux_addr_r
                      : x2_mem_addr_r
                      ;

end // block : x3_addr_nxt_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : ap_x3_addr_PROC
  if (rst_a == 1'b1) begin
    x3_addr_r   <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (x3_addr_cg) begin
    x3_addr_r   <= x3_addr_nxt & {`npuarc_DATA_SIZE{!x2_kill}};
  end
end

always @(posedge ap_unit_clk or posedge rst_a)
begin : ap_ca_addr_PROC
  if (rst_a == 1'b1) begin
    ca_addr_r   <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (ca_addr_cg) begin
    ca_addr_r   <= x3_addr_r   & {`npuarc_DATA_SIZE{!x3_kill}};
  end
end

always @(posedge ap_unit_clk or posedge rst_a)
begin : ap_wa_addr_PROC
  if (rst_a == 1'b1) begin
    wa_addr_r   <= {`npuarc_DATA_SIZE{1'b0}};
  end
  else if (wa_addr_cg) begin
    wa_addr_r   <= ca_addr_r; // Committed cannot be killed
  end
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining ap1-stage pipeline registers                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge ap_unit_clk or posedge rst_a) 
begin : ap2_wp_ctrl_PROC
  if (rst_a == 1'b1) begin
    ap1_valid_op_r  <=  1'b0;
  end
  else if (ap1_ctrl_en == 1'b1) begin
    ap1_valid_op_r  <=  ap1_valid_op_nxt;
  end
end

always @(posedge ap_unit_clk or posedge rst_a)
begin : ap2_ae_PROC
  if (rst_a == 1'b1) begin
    ap1_stat32_ae_r <=  1'b0;
  end
  else begin
    ap1_stat32_ae_r <=  ar_ae_r;
  end
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// APS Halt Logic                                                         //
//                                                                        //
////////////////////////////////////////////////////////////////////////////


always @*
begin : aps_halt_PROC

  x3_break_cg = (x2_pass & x3_enable & (|trig))
              | (x3_enable & x3_break_r)
              ;

  ca_break_cg = (x3_pass & ca_enable & x3_break_r)
              | (wa_enable & ca_break_r)
              ;

  x3_halt_cg  = x3_dt_raw_cg ;



  ////////////////////////////////////////////////////////////////////////////
  // Break point Halt 
  // Any triggered primary AP that is also a breakpoint primary
  // will set the x3_break_r output signal.
  // (1) Prioritized action is Halt
  // (2) No Halt - safety
  // (3) Not a break point
  // (4) No pending 
  //
  x3_break_nxt   = (|(x3_trig_comp & if_ap & (~action)))
                 & (i_halt_nxt)                      // (1)
                 & (~ar_aux_status32_r[`npuarc_H_FLAG])     // (2)
                 & (~x2_kill)
                 & (~aps_pending)                    // (4)
                 ;

  ////////////////////////////////////////////////////////////////////////////
  // Watch point Halt 
  // Trigger is Watchpoint
  // (1) Prioritized action is Halt
  // (2) No Halt - safety
  // (3) Not a break point
  // (4) No pending 
  // 
  // 
  // X3 Watchpoint - Halt - Status Sticky
  // 1. Set    : Any new Halt WP
  // 2. Clear  : X3 pass
  x3_halt_nxt = trig_any_h_wp               // (1)
                   ;


  x3_pcbrk_nxt   = (|(x3_trig_comp & if_ap & (~action)))
                      &  x3_break_nxt 
                      ;

  ////////////////////////////////////////////////////////////////////////////
  // (1) Found Break point with Halt action
  // (2) Ensure Machine is not getting Halted due to previous Halt
  // (3) Ensure Machine is not getting Halted due to previous Halt
  // (4) AP Halt request consumed by CA
  // (5) AP Halt taken only if UB is set or Kernel mode

  ca_break_nxt   = x3_break_r                              // (1)
                 & (~( wa_aux_status32_pass
                    & wa_aux_status32_nxt[`npuarc_P_H_FLAG]))      // (2)
                 & (~ar_aux_status32_r[`npuarc_H_FLAG])           // (3)
                 & (~(aps_break & ca_valid_r) )              // (4)
                 & ( ~ar_aux_status32_r[`npuarc_U_FLAG]           // (5)
                   |  ar_aux_debug_r[`npuarc_DEBUG_UB]
                   )
                 ;

  ca_pcbrk_nxt   = x3_pcbrk_r  
                 & ca_break_nxt
                 ;

  aps_halt_nxt   =  ( x3_wp_halt
                         | (x3_dt_r & !x3_bp_r & !x3_ex_r
                           & !ca_uop_active_r
                           & !int_load_active
                           )
                         )
//                      & !ar_aux_status32_r[`H_FLAG]
                      ;
  
end // block : aps_halt_PROC


always @(posedge ap_unit_clk or posedge rst_a) 
begin : x3_break_regs_PROC
  if (rst_a == 1'b1) begin
    x3_break_r   <= 1'b0;
  end
  else if (x3_break_cg) begin
    x3_break_r <= x3_break_nxt;
  end
end // block : x3_break_regs_PROC


always @(posedge ap_unit_clk or posedge rst_a) 
begin : x3_halt_regs_PROC
  if (rst_a == 1'b1) begin
    x3_halt_r    <= 1'b0;
  end
  else if (x3_halt_cg) begin
    x3_halt_r  <= x3_halt_nxt;
  end
end // block : x3_halt_regs_PROC


always @(posedge ap_unit_clk or posedge rst_a) 
begin : x3_pcbrk_regs_PROC
  if (rst_a == 1'b1) begin
    x3_pcbrk_r   <= 1'b0;
  end
  else if (x3_break_cg) begin
    x3_pcbrk_r <= x3_pcbrk_nxt;
  end
end // block : x3_pcbrk_regs_PROC



always @(posedge ap_unit_clk or posedge rst_a)
begin : ca_break_regs_PROC
  if (rst_a == 1'b1) begin
    ca_break_r     <= 1'b0;
    ca_pcbrk_r     <= 1'b0;
  end
  else if (ca_break_cg) begin
    ca_break_r <= ca_break_nxt;
    ca_pcbrk_r <= ca_pcbrk_nxt;
  end
end // block : ca_brk_regs_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : aps_halt_regs_PROC
  if (rst_a == 1'b1) begin
    aps_halt_r     <= 1'b0;
  end
  else if (ca_dt_raw_cg) begin
    aps_halt_r <= aps_halt_nxt;
  end
end // block : aps_halt_regs_PROC



////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining ap2-stage result registers                  //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge ap_unit_clk or posedge rst_a)
begin : x3_outregs_PROC
  if (rst_a == 1'b1) begin
    x3_hit_if_r  <= 1'b0;
    x3_hit_mr_r  <= 1'b0;
    x3_hit_md_r  <= 1'b0;
  end
  else if ((|x3_dt_cg) == 1'b1) begin
    x3_hit_if_r <= x3_hit_if_nxt;
    x3_hit_mr_r <= x3_hit_mr_nxt;
    x3_hit_md_r <= x3_hit_md_nxt;
  end
end // block : x3_outregs_PROC

//
////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining Watchpoint PC register                      //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//
always @*
begin : wp_rslt_PROC

  wp_pc_cg     = 1'b0
               | reload_pc
               ;

  wp_pc_nxt     = {`npuarc_PC_BITS{1'b0}}
                | (ca_wppc_r &  {`npuarc_PC_BITS{reload_pc}})
                ;

end // block : wp_rslt_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : wp_rslt_reg_PROC
  if (rst_a == 1'b1) begin
    wp_pc_r      <= `npuarc_PC_BITS'd0;
  end
  else if (wp_pc_cg == 1'b1) begin
    wp_pc_r    <= wp_pc_nxt;
  end
end // block : wp_rslt_reg_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining pipeline PC register (x2 PC)                //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge ap_unit_clk or posedge rst_a)
begin : x2_pc_PROC
  if (rst_a == 1'b1) begin
    x2_pc_r      <= `npuarc_PC_BITS'd0;
  end
  else if (x1_pass & x2_enable) begin
    x2_pc_r      <= x1_pc_r;
  end
end // x2_pc_PROC



////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block defining Actionpoint hit status                      //
//                                                                        //
////////////////////////////////////////////////////////////////////////////
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : wa_asr_PROC
  if (rst_a == 1'b1) begin
    wa_asr_r   <= {`npuarc_NUM_ACTIONPOINTS{1'b0}};
  end
  else if (wa_enable && ap_unit_enable) begin
    wa_asr_r   <= ar_asr_r [`npuarc_APS_RANGE];
  end
end // wa_asr_PROC
//


//
always @*
begin : ap_status_PROC

  aps_status_cg   = 1'b0
                       | (ca_dt_raw_cg 
                         & !( 1'b1
                            & ca_dt_r
                            & ca_bp_r
                            & ca_ex_r
                            & ca_kill
                            )
                         )
                       | (!ca_dt_r & |aps_status_r & !ap_excpn_holdup)
                       | (x3_bp_excpn & x3_ap_pass & !ar_aux_debug_r[`npuarc_DEBUG_UB] 
                          & ar_aux_status32_r[`npuarc_U_FLAG] ) //allow status to update for bp excpn in user mode
                       ;

end // block : ap_status_PROC
//
always @(posedge ap_unit_clk or posedge rst_a)
begin : aps_active_PROC
  if (rst_a == 1'b1) begin
    aps_active_r  <= `npuarc_APNUM_SIZE'd0;
  end
  else if (x3_dt_raw_cg == 1'b1) begin
    aps_active_r  <= aps_active_nxt;
  end
end // block : aps_active_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : aps_status_PROC
  if (rst_a == 1'b1) begin
    aps_status_r  <= `npuarc_NUM_ACTIONPOINTS'd0;
  end
  else if (aps_status_cg == 1'b1) begin
    aps_status_r  <= aps_status_nxt;
  end
end // block : aps_status_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : aps_pcbrk1_PROC
  if (rst_a == 1'b1) begin
    aps_pcbrk1_r  <= 1'b0;
  end
  else begin
    aps_pcbrk1_r  <= aps_pcbrk1_nxt;
  end
end // block : aps_pcbrk1_PROC


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Logic to Clear Pending AP                                              //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : clear_pend_ap_cg_PROC
  //assert cg on every AP trig
  clear_pend_ap_cg  = trig_any_h_wp | x3_dt_raw_cg;
  //check if AP triggered was a wp and if it was disabled same cycle
  clear_pend_ap_nxt[0] = trig[0] & (trig_any_h_wp | action [0]) & !ap_en[0];
  clear_pend_ap_nxt[1] = trig[1] & (trig_any_h_wp | action [1]) & !ap_en[1];
  clear_pend_ap_nxt[2] = trig[2] & (trig_any_h_wp | action [2]) & !ap_en[2];
  clear_pend_ap_nxt[3] = trig[3] & (trig_any_h_wp | action [3]) & !ap_en[3];
  clear_pend_ap_nxt[4] = trig[4] & (trig_any_h_wp | action [4]) & !ap_en[4];
  clear_pend_ap_nxt[5] = trig[5] & (trig_any_h_wp | action [5]) & !ap_en[5];
  clear_pend_ap_nxt[6] = trig[6] & (trig_any_h_wp | action [6]) & !ap_en[6];
  clear_pend_ap_nxt[7] = trig[7] & (trig_any_h_wp | action [7]) & !ap_en[7];
end // block : clear_pend_ap_cg_PROC

always @(posedge ap_unit_clk or posedge rst_a)
begin : clear_pend_ap_r_PROC
  if (rst_a == 1'b1) begin
    clear_pend_ap_r  <= 1'b0;
  end
  else if (clear_pend_ap_cg == 1'b1) begin
    clear_pend_ap_r  <= |clear_pend_ap_nxt;
  end
end // block : clear_pend_ap_r_PROC

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Output assignments                                                     //
//                                                                        //
////////////////////////////////////////////////////////////////////////////


assign aps_hit_if   = x3_bp_excpn;
assign aps_hit_mr  = x3_wp_excpn;
assign aps_halt     = aps_halt_r
                    & (~db_active)
                    & (~ca_uop_active_r)
                    & (~int_load_active)
                    & ap4_ar_ub_r
                    & (~excpn_in_prologue)
                    & !pipe_block_ints
                    ;
assign aps_break    = ca_break_r
                    & (~db_active)
                    & (~ca_uop_active_r)
                    & (~int_load_active)
                    & ( ~ar_aux_status32_r[`npuarc_U_FLAG]
                      |  ar_aux_debug_r[`npuarc_DEBUG_UB]
                      )
                    & (~excpn_in_prologue)
                    ;
assign aps_pcbrk    = ca_pcbrk_r
                    & ca_break_r
                    & aps_pcbrk1_r
                    ;
assign aps_pcbrk1_nxt = (~db_active)
                    & (~(ca_uop_state_cg0 ? ca_uop_active_nxt : ca_uop_active_r))
                    & (~int_load_active_nxt)
                    & (~(excpn_in_cg0 ? excpn_in_prologue_nxt : excpn_in_prologue))
                    ;
assign aps_active   = aps_active_r;
assign aps_halt_ack = ca_ap_halt_ack;
assign x3_aps_break_r = x3_break_r | x3_bp_halt;
assign x3_aps_halt_r  = x3_halt_r;
assign aps_status   = {`npuarc_NUM_ACTIONPOINTS{1'b0}}
                    | (aps_status_r & {`npuarc_NUM_ACTIONPOINTS{ap_tkn}})
                    ;


endmodule // module : alb_actionpoints
