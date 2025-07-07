// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

//----------------------------------------------------------------------------
//
// ####### #     # #     #
// #        #   #  #     #
// #         # #   #     #
// #####      #    #     #
// #         # #   #     #
// #        #   #  #     #
// ####### #     #  #####
//
// ===========================================================================
//
// Description:
//
//  This module instantiates, and connects together, the control and
//  datapath elements of the Execution Unit.
//
//  The module hierarchy, at and below this module, is:
//
//         alb_exu
//            |
//            +-- alb_exec_pipe (HS3X) or mrl_exec_pipe (HS4X)
//            |      |
//            |      +-- alb_dec_regs
//            |      |      |
//            |      |      +-- alb_predecode
//            |      |      |
//            |      |      +-- alb_decode
//            |      |      |
//            |      |      +-- alb_uop_seq_al
//            |      |      |
//            |      |      +-- alb_uop_seq_da
//            |      |
//            |      +-- alb_opd_sel
//            |      |      |
//            |      |      +-- regfile_2r2w
//            |      |
//            |      +-- alb_exec1
//            |      |      |
//            |      |      +-- alb_agu
//            |      |      |
//            |      |      +-- alb_alu
//            |      |             |
//            |      |             +-- alb_maskgen
//            |      |             |
//            |      |             +-- alb_adder
//            |      |             |
//            |      |             +-- alb_logic_unit
//            |      |             |
//            |      |             +-- alb_shifter
//            |      |             |
//            |      |             +-- alb_byte_unit
//            |      |             |
//            |      |             +-- alb_bitscan
//            |      |
//            |      +-- alb_exec2
//            |      |
//            |      +-- alb_exec3
//            |      |
//            |      +-- alb_commit
//            |      |
//            |      +-- alb_writeback
//            |      |
//                   +-- alb_dep_pipe
//            |      |
//            |      +-- alb_dep_pipe
//            |
//            +-- alb_exu_ctrl
//
//
// ===========================================================================

// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//
`include "npuarc_ucode_const.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_exu (
  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,                  // clock signal
  input                       rst_a,                // reset signal

  input                       l1_clock_active,  //
  input     [7:0]             arcnum,
  input     [7:0]             clusternum,           // for cluster_id register
  input                       dmp_queue_empty,
  input                       iexcpn_discarded,
  input                       st_instrs_discarded,
  output                      holdup_excpn_r,



  input [1:0]                 dc4_dtlb_miss_r,
  input                       dc3_dtlb_miss_excpn_r,
  input                       dc3_dtlb_ovrlp_excpn_r,
  input                       dc3_dtlb_protv_excpn_r,
  input                       dc3_dtlb_ecc_excpn_r,
  output                      wa_jtlb_lookup_start_r,
  output                      wa_jtlb_cancel,

  output                      ca_tlb_miss_excpn,
  output [`npuarc_PD0_VPN_RANGE]     ca_tlb_miss_efa,
  output                      ca_m_chk_excpn,

  input                       mmu_en_r,
  output                      mpu_en_r,
  input                       x2_da0_transl,

  input                       clk_ungated,   
// Library ARCv2HS-3.5.999999999



  ////////// EIA user extension external input signals ///////////////////////
  //
  input   [95:0]  EventManager_evm_event_a,
  input           EventManager_evm_sleep,

  ////////// EIA user extension external output signals //////////////////////
  //
  output          EventManager_evm_wakeup,
  output  [63:0]  EventManager_evm_send,
  output  [31:0]  EventManager_vm_grp0_sid,
  output  [31:0]  EventManager_vm_grp0_ssid,
  output  [31:0]  EventManager_vm_grp1_sid,
  output  [31:0]  EventManager_vm_grp1_ssid,
  output  [31:0]  EventManager_vm_grp2_sid,
  output  [31:0]  EventManager_vm_grp3_sid,
  output  [31:0]  EventManager_vm_grp2_ssid,
  output  [31:0]  EventManager_vm_grp3_ssid,
  output          EventManager_evt_vm_irq,
  output  [3:0]  EventManager_evt_vm_sel,
  ////////// Fetch-Restart Interface /////////////////////////////////////////
  //
  output                      fch_restart,       // EXU requests IFU restart
  output                      fch_restart_vec,   //
  output [`npuarc_PC_RANGE]          fch_target,        //
  output [`npuarc_IM_LINE_BITS:3]    fch_target_successor,
  output                      fch_stop_r,        // EXU requests IFU halt
  output                      fch_iprot_replay,

  ////////// Instruction Issue Interface /////////////////////////////////////
  //
  input                       al_pass /* verilator public_flat */,
  input  [`npuarc_DATA_RANGE]        al_inst,
  input  [`npuarc_DATA_RANGE]        al_limm,


  input                       al_exception,
  input  [`npuarc_FCH_EXCPN_RANGE]   al_excpn_type,
  input [`npuarc_FCH_EINFO_RANGE]    al_excpn_info,
  input                       al_ifu_err_nxtpg,
  input                       al_iprot_viol,
  input                       al_is_predicted,
  input                       al_prediction,
  input  [`npuarc_PC_RANGE]          al_predicted_bta,
  input  [`npuarc_BR_TYPE_RANGE]     al_prediction_type,
  input                       al_error_branch,
  input  [`npuarc_BR_INFO_RANGE]     al_branch_info,
  input                       al_with_dslot,


  output                      da_holdup,


  ////////// Misprediction Interface /////////////////////////////////////////
  //
  output                      mpd_mispred,
  output                      mpd_direction,
  output                      mpd_error_branch,
  output                      mpd_is_predicted,
  output                      mpd_mispred_outcome,
  output                      mpd_mispred_bta,
  output [`npuarc_BR_INFO_RANGE]     mpd_branch_info,
  output                      mpd_dslot,
  output [`npuarc_PC_RANGE]          mpd_seq_next_pc,
  output [`npuarc_BR_TYPE_RANGE]     mpd_type,
  output [`npuarc_PC_RANGE]          mpd_pc,
  output                      mpd_tail_pc_3,
  output [`npuarc_ISIZE_RANGE]       mpd_commit_size,
  output                      mpd_secondary,
  output                      mpd_early,

  ////////// Branch Commit Interface /////////////////////////////////////////
  //
  output                      wa_pass,
  output [`npuarc_BR_TYPE_RANGE]     wa_type,
  output                      wa_secondary,
  output [`npuarc_PC_RANGE]          wa_pc,
  output                      wa_tail_pc_3,
  output                      wa_dslot,
  output [`npuarc_PC_RANGE]          wa_target,
  output [`npuarc_ISIZE_RANGE]       wa_commit_size,
  output                      wa_direction,
  output                      wa_error_branch,
  output                      wa_is_predicted,
  output                      wa_mispred_outcome,
  output                      wa_commit_mispred_bta,
  output [`npuarc_BR_INFO_RANGE]     wa_branch_info,
  output                      wa_restart_r,
  output                      wa_hlt_restart_r,
  output                      wa_restart_kill_r,

  output                      zol_depend_stall,

  ////////////// MPU interface for IFU ///////////////////////////////////////
  input  [`npuarc_PC_RGN_RANGE]      ifetch_addr_mpu,
  output                      ifetch_viol,

  ////////// EXU interface to DMP ////////////////////////////////////////////
  //
  output                      sa_dsync_op_r,        // SA is a DSYNC insn.
  output                      sa_dmb_op_r,          // SA is a DMB insn.
  output                      sa_dmb_dmp_stall,     // SA stall due to DMB
  // SA
  output                      sa_load_r,            // load operation at SA
  output                      sa_store_r,           // store operation at SA
  // AUX
  output                      dmp_aux_sr_op,        // dmp sr operation in CA, WA

  output [7:0]      aux_memseg_r,

  // X1
  //
  input                       dc1_stall,
  //
  output                      x1_valid_r,
  output                      x1_pass,
  output                      x1_load_r,
  output                      x1_store_r,
  output                      x1_pref_r,
  output                      x1_cache_byp_r,
  output [1:0]                x1_size_r,
  output [`npuarc_ADDR_RANGE]        x1_mem_addr0,
  output [`npuarc_ADDR_RANGE]        x1_mem_addr1,
  output [`npuarc_ADDR_RANGE]        x1_addr_base,
  output [`npuarc_ADDR_RANGE]        x1_addr_offset,
  output [1:0]                x1_bank_sel_lo,
  output [1:0]                x1_bank_sel_hi,
  output                      x1_uop_inst_r,
  // X2
  input                       dc2_stall,
  input                       dc2_addr_pass,
  input  [`npuarc_ADDR_RANGE]        dc2_aux_addr,
  output                      x2_valid_r,
  output                      x2_pass,
  output                      x2_enable,
  output                      x2_load_r,
  output                      x2_store_r,
  output                      x2_locked_r,
  output                      x2_pref_r,
  output [1:0]                x2_size_r,
  output                      x2_cache_byp_r,
  output                      x2_mpu_data_flt,      // 
  output [`npuarc_ADDR_RANGE]        x2_mem_addr_r,
  output                      x2_uop_inst_r,
  output                      x2_exu_stall,
  // X3
  input  [`npuarc_ADDR_RANGE]        dmp_dc3_dtlb_efa,
  input                       dmp_dc3_stall_r,
  input                       dmp_dc3_fast_byp,
  output                      x3_valid_r,
  output                      x3_pass,
  output                      x3_enable,
  output                      x3_load_r,
  output                      x3_store_r,
  output                      x3_locked_r,
  output                      x3_pref,              // PREFETCH into L1
  output                      x3_pref_l2,           // PREFETCH into L2
  output                      x3_prefw,             // PREFETCHW
  output                      x3_pre_alloc,         // PREALLOC
  output [1:0]                x3_size_r,
  output                      x3_sex_r,
  output                      x3_cache_byp_r,
  output [`npuarc_ADDR_RANGE]        x3_mem_addr_r,
  output                      x3_uop_inst_r,
  output                      x3_sync_op_r,
  output                      x3_brk_op_r,
  input                       dc3_excpn,            // DMP precise memory err exc
  input  [`npuarc_DMP_EXCPN_RANGE]   dc3_excpn_type,       // exception type
  input  [7:0]                dc3_excpn_code,       // cause code
  // CA
  input  [`npuarc_DATA_RANGE]        dmp_dc4_fast_data,
  input  [`npuarc_DATA_RANGE]        dmp_dc4_rf_wdata_lo,
  input                       dmp_dc4_stall,
  input                       dc4_waw_replay_r,
  input                       dmp_dc4_fast_byp_r,
  input                       dmp_dc4_fast_miss_r,

  output                      x3_store_may_grad,
  output [1:0]                ca_store_grad,
  output [1:0]                ca_store_grad_swap,
  output [`npuarc_GRAD_TAG_RANGE]    ca_store_grad_tag_lo,
  output [`npuarc_GRAD_TAG_RANGE]    ca_store_grad_tag_hi,
  output                      wa_retire1_valid,
  output [`npuarc_GRAD_TAG_RANGE]    wa_retire1_tag,


  output                      ca_valid_r,
  output                      ca_pass,
  output                      ca_enable,
  output                      ca_load_r,
//  output                      ca_pref_r,
  output                      rtt_ca_pref,        // load with null dest for trace
  output                      rtt_wa_spl_ld,      // Auxiliary load for trace
  output                      rtt_wa_store,       // WA Store for Trace
  output                      rtt_dmp_retire,     // DMP retire for Trace
  output                      rtt_dmp_null_ret,   // DMP null retire rpt for Trace
  output                      ca_grad_req,
  output                      ca_store_r /* verilator public_flat */,
  output [1:0]                ca_size_r  /* verilator public_flat */,
  output                      ca_sex_r,
  output                      ca_cache_byp_r,
  output                      ca_pref,              // PREFETCH into L1
  output                      ca_pref_l2,           // PREFETCH into L2
  output                      ca_prefw,             // PREFETCHW
  output                      ca_pre_alloc,         // PREALLOC
  output [`npuarc_ADDR_RANGE]        ca_mem_addr_r /* verilator public_flat */,
  input  [`npuarc_PADDR_RANGE]       ca_phys_addr_r,
  output                      ca_uop_inst_r,
  output                      db_active_r,
  output [`npuarc_DATA_RANGE]        dc4_write_data_lo /* verilator public_flat */,
  input  [`npuarc_DATA_RANGE]        dmp_dc4_rf_wdata_hi,
  output [`npuarc_DATA_RANGE]        dc4_write_data_hi,
  output                      ca_locked_r,          // LLOCK or SCOND indicator
  output                      wa_lock_flag_r,       // LF register
  output                      wa_lock_double_r,     // LF size
  output [`npuarc_PADDR_RANGE]       wa_lpa_r,             // LPA register
  output                      mem_excpn_ack_r,      // bus error excpn ack
  output                      excpn_exit_evt,       // Return from exception

  ////////// DMP Exception and Replay Interface //////////////////////////////
  //
  input                       dc4_replay,           // replay the instr at DC4
  input                       dc4_excpn,            // DMP is raising an excpn
  input [`npuarc_PADDR_RANGE]        dc4_excpn_mem_addr,   // address of the faulting
                                                    //  inst, may be imprecise
  input [`npuarc_DMP_EXCPN_RANGE]    dc4_excpn_type,       // exception type
  input                       dc4_excpn_user_mode_r,// DMP excpn privilege

  ////////// DMP Graduation and Retirement Interface /////////////////////////
  //
  input                       dc4_grad_req,         // DMP grad. request
  input                       dmp_retire_req,       // DMP retirement req.
  input  [`npuarc_GRAD_TAG_RANGE]    dmp_retire_tag,       // DMP tag of retirer
  input                       dmp_scond_zflag,      // DMP SCOND Z-flag result
  input                       dmp_clear_lf,         // DMP detects write to LPA
  output                      dmp_retire_ack,       // DMP retirement ack
  input                        rtt_dc4_scond_go,  // scond will be success
  output [`npuarc_ADDR_RANGE]        dmp_retire_ld_addr,   // DMP VA of retiring LD
  ////////// DMP pending post-commit mem operations /////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  dmp interface
  input                       dmp_wr_pending_r,     // DMP pending wr op
  input                       dmp_aux_pending_r,    // DMP pending cache instr
// leda NTL_CON13C on
  ////////// Common Graduation Interface /////////////////////////////////////
  //
  output                      ca_grad_ack,          // CA inst graduates
  output [`npuarc_GRAD_TAG_RANGE]    ca_grad_tag,          // graduating inst tag

  ////////// EXU AUX. Interface //////////////////////////////////////////////
  //
  output                      aux_read,             // aux_read
  output                      aux_write,            // aux_write
  output [`npuarc_DATA_RANGE]        wa_sr_data_r,         // aux write data
  input                       wdt_x3_stall,
  output                      x3_kill,

  output                      aux_dccm_ren_r,       //  (X3) Aux Reg Enable
  output                      aux_dccm_wen_r,       //  (WA) Aux Reg Enable
  input       [`npuarc_DATA_RANGE]   dccm_aux_rdata,       //  (X3) LR read data
  input                       dccm_aux_illegal,     //  (X3) SR/LR illegal
  input                       dccm_aux_k_rd,        //  (X3) needs Kernel Read
  input                       dccm_aux_k_wr,        //  (X3) needs Kernel Write
  input                       dccm_aux_unimpl,      //  (X3) Invalid Reg
  input                       dccm_aux_serial_sr,   //  (X3) SR group flush pipe
  input                       dccm_aux_strict_sr,   //  (X3) SR flush pipe
  output                      aux_dper_ren_r,       //  (X3) Aux Reg Enable
  output                      aux_dper_raddr_r,     //  (X3) Aux Reg Addr
  output                      aux_dper_wen_r,       //  (WA) Aux Reg Enable
  output                      aux_dper_waddr_r,     //  (WA) Aux Reg Addr
  input       [`npuarc_DATA_RANGE]   dper_aux_rdata,       //  (X3) LR read data
  input                       dper_aux_illegal,     //  (X3) SR/LR illegal
  input                       dper_aux_k_rd,        //  (X3) need Kernel Read
  input                       dper_aux_k_wr,        //  (X3) needs Kernel W perm
  input                       dper_aux_unimpl,      //  (X3) Invalid Reg
  input                       dper_aux_serial_sr,   //  (X3) SR group flush pipe
  input                       dper_aux_strict_sr,   //  (X3) SR flush pipe

  ////////// Auxiliary interface for (DC) SR/LR instructions ////////////
  //
  output                      aux_dc_ren_r,         //  (X3) Aux read enable
  output      [4:0]           aux_dc_raddr_r,       //  (X3) Aux Address
  output                      aux_dc_wen_r,         //  (WA) Aux write enable
  output      [4:0]           aux_dc_waddr_r,       //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   dc_aux_rdata,         //  (X3) LR read data
  input                       dc_aux_illegal,       //  (X3) SR/LR illegal
  input                       dc_aux_k_rd,          //  (X3) need Kernel Rd
  input                       dc_aux_k_wr,          //  (X3) need Kernel Wr
  input                       dc_aux_unimpl,        //  (X3) Invalid Reg
  input                       dc_aux_serial_sr,     //  (X3) SR group flush
  input                       dc_aux_strict_sr,     //  (X3) SR single flus  h
  input                       dc_aux_busy,          // Structural hazard

  // leda NTL_CON37 off
  // LMD: non driving port range
  // LJ:  Standard aux interface
  output                      aux_ic_ren_r,        //  (X3) Aux     Enable
  output      [3:0]           aux_ic_raddr_r,      //  (X3) Aux Address
  output                      aux_ic_wen_r,        //  (WA) Aux     Enable
  output      [3:0]           aux_ic_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   ic_aux_rdata,        //  (X3) LR read data
  input                       ic_aux_illegal,      //  (X3) SR/LR illegal
  input                       ic_aux_k_rd,         //  (X3) need Kernel Read
  input                       ic_aux_k_wr,         //  (X3) need Kernel Write
  input                       ic_aux_unimpl,       //  (X3) Invalid
  input                       ic_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       ic_aux_strict_sr,    //  (X3) SR flush pipe
  // leda NTL_CON37 on

  output                      aux_bpu_ren_r,        //  (X3) Aux Reg Enable
  output      [3:0]           aux_bpu_raddr_r,      //  (X3) Aux Address
  output                      aux_bpu_wen_r,        //  (WA) Aux Reg Enable
  output      [3:0]           aux_bpu_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   bpu_aux_rdata,        //  (X3) LR read data
  input                       bpu_aux_illegal,      //  (X3) SR/LR illegal
  input                       bpu_aux_k_rd,         //  (X3) need Kernel Read
  input                       bpu_aux_k_wr,         //  (X3) need Kernel Write
  input                       bpu_aux_unimpl,       //  (X3) Invalid Reg
  input                       bpu_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       bpu_aux_strict_sr,    //  (X3) SR flush pipe

  ////////// Auxiliary interface for (Timer) SR/LR instructions ////////////
  //
  output                      aux_tm0_ren_r,        //  (X3) Aux     Enable
  output      [1:0]           aux_tm0_raddr_r,      //  (X3) Aux Address
  output                      aux_tm0_wen_r,        //  (WA) Aux     Enable
  output      [1:0]           aux_tm0_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   tm0_aux_rdata,        //  (X3) LR read data
  input                       tm0_aux_illegal,      //  (X3) SR/LR illegal
  input                       tm0_aux_k_rd,         //  (X3) needs Kernel Read
  input                       tm0_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       tm0_aux_unimpl,       //  (X3) Invalid Reg
  input                       tm0_aux_serial_sr,    //  (X3) Serializing SR
  output                      aux_timer_active,    //  timer SR is active   

  output                      aux_wdt_ren_r,        //  (X3) Aux     Enable
  output      [3:0]           aux_wdt_raddr_r,      //  (X3) Aux Address
  output                      aux_wdt_wen_r,        //  (WA) Aux     Enable
  output      [3:0]           aux_wdt_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   wdt_aux_rdata,        //  (X3) LR read data
  input                       wdt_aux_illegal,      //  (X3) SR/LR illegal
  input                       wdt_aux_k_rd,         //  (X3) needs Kernel Read
  input                       wdt_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       wdt_aux_unimpl,       //  (X3) Invalid
  input                       wdt_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       wdt_aux_strict_sr,    //  (X3) SR flush pipe

/////////////output for pct////////////////////////////////////////////////////
  output                      do_aux_replay_r,

  output                      aux_rtc_ren_r,        //  (X3) Aux     Enable
  output      [2:0]           aux_rtc_raddr_r,      //  (X3) Aux Address
  output                      aux_rtc_wen_r,        //  (WA) Aux     Enable
  output      [2:0]           aux_rtc_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   rtc_aux_rdata,        //  (X3) LR read data
  input                       rtc_aux_illegal,      //  (X3) SR/LR illegal
  input                       rtc_aux_k_rd,         //  (X3) needs Kernel Read
  input                       rtc_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       rtc_aux_unimpl,       //  (X3) Invalid
  input                       rtc_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       rtc_aux_strict_sr,    //  (X3) SR flush pipe

  output                      rtc_na,               //   (CA) Non-atomic


  ////////// Auxiliary interface for common aux register accesses ////////////
  //
  output                      aux_rs_valid,         //  CCAUX valid rd request
  output [`npuarc_CCAUX_RGN_RANGE]   aux_rs_region,        //  CCAUX region identity
  output [`npuarc_CCAUX_ADDR_RANGE]  aux_rs_addr,          //  CCAUX region offset
  output                      aux_rs_read,          //  CCAUX read enable
  output                      aux_rs_write,         //  CCAUX write enable
  input  [`npuarc_DATA_RANGE]        aux_rs_data,          //  CCAUX LR data
  input  [`npuarc_CCAUX_STAT_RANGE]  aux_rs_status,        //  CCAUX credintials
  input                       aux_rs_accept,        //  CCAUX response read

  output                      aux_wr_valid,         //  CCAux wr valid
  output [`npuarc_CCAUX_RGN_RANGE]   aux_wr_region,        //  CCAux wr region
  output [`npuarc_CCAUX_ADDR_RANGE]  aux_wr_addr,          //  CCAux wr Address
  output [`npuarc_DATA_RANGE]        aux_wr_data,          //  CCAux wr data
  input                       aux_wr_allow,         //  CCAux new write allowed
  output                      aux_cm_phase,         //  CCAux in commit phase
  output                      aux_cm_valid,         //  CCAux commit is valid

  output                      aux_pct_active,       //  PCT SR is active
  output                      aux_pct_ren_r,        //  (X3) Aux     Enable
  output      [5:0]           aux_pct_raddr_r,      //  (X3) Aux Address
  output                      aux_pct_wen_r,        //  (WA) Aux     Enable
  output      [5:0]           aux_pct_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   pct_aux_rdata,        //  (X3) LR read data
  input                       pct_aux_illegal,      //  (X3) SR/LR illegal
  input                       pct_aux_k_rd,         //  (X3) needs Kernel Rd
  input                       pct_aux_k_wr,         //  (X3) needs Kernel Wr
  input                       pct_aux_unimpl,       //  (X3) Invalid
  input                       pct_aux_serial_sr,    //  (X3) SR group flush
  input                       pct_aux_strict_sr,    //  (X3) SR single flush

  output                      aux_mmu_ren_r,        //  (X3) Aux     Enable
  output      [4:0]           aux_mmu_raddr_r,      //  (X3) Aux Address
  output                      aux_mmu_wen_r,        //  (WA) Aux     Enable
  output      [4:0]           aux_mmu_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   mmu_aux_rdata,        //  (X3) LR read data
  input                       mmu_aux_illegal,      //  (X3) SR/LR illegal
  input                       mmu_aux_k_rd,         //  (X3) needs Kernel Read
  input                       mmu_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       mmu_aux_unimpl,       //  (X3) Invalid
  input                       mmu_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       mmu_aux_strict_sr,    //  (X3) SR flush pipe

  // halt status
  output                      dbg_bh_r,           // break halt
  output                      dbg_sh_r,           // self_halt
  output                      dbg_eh_r,           // external halt
  output                      dbg_ah_r,           // actionpoint halt



  output                      dbg_ra_r,

  input     [15:0]            ecc_flt_status,       //
  output    [`npuarc_DATA_RANGE]     ar_aux_ecc_ctrl_r,    //
  input     [`npuarc_DATA_RANGE]     ecc_sbe_count_r,
  output    [7:0]             ecc_sbe_clr,
  output                      ecc_sbe_dmp_clr,
  output                      ar_user_mode_r,       // STATUS32.U bit

  output                      ap_tkn,


  ////////// Interrupt signals ///////////////////////////////////////////////
  //

  input [`npuarc_IRQM_RANGE]         timer0_irq_1h,

  input [`npuarc_IRQM_RANGE]         wdt_int_timeout_1h_r,
  input  [`npuarc_IRQM_RANGE]         pct_int_overflow_r,
  input [`npuarc_IRQE_RANGE]         irq_r,          // synchronous output

  input [21:0]                      intvbase_in, // for external interrupt vector base configuring

  input                       irq_clk_en_r,

  output                      irq_preempts_nxt,


 // input                       clk_resync,
 // output                      irq_sync_req_a,



  output                      db_active,            // Clock + Timer

  ////////// Debug Interface /////////////////////////////////////////////////
  //
  input                       dbg_cmdval,           // |cmdval| from JTAG
  output                      dbg_cmdack,           // BVCI |cmd| acknowledge
  input  [`npuarc_DBG_ADDR_RANGE]    dbg_address,          // |addres|s from JTAG
  input  [`npuarc_DBG_BE_RANGE]      dbg_be,               // |be| from JTAG
  input  [`npuarc_DBG_CMD_RANGE]     dbg_cmd,              // |cmd| from JTAG
  input  [`npuarc_DBG_DATA_RANGE]    dbg_wdata,            // |wdata| from JTAG

  input                       dbg_rspack,           // |rspack| from JTAG
  output                      dbg_rspval,           // BVCI response valid
  output [`npuarc_DBG_DATA_RANGE]    dbg_rdata,            // BVCI response EOP
  output                      dbg_reop,             // BVCI response error
  output                      dbg_rerr,             // BVCI data to Debug host


  output                      debug_reset,
  output                      db_clock_enable_nxt,  // Clock needs to be enb
  input                       ar_clock_enable_r,    //

  output                      x3_1_db_exception,    // Debug LD/ST in X3 has exc
  output                      ca_db_exception,      // Debug instr in CA has Exception

  ////////// APB debug interface /////////////////////////////////////////////

  input                       dbg_prot_sel,

  input                       pclkdbg_en,
  input                     presetdbgn,
  input [31:2]                paddrdbg,
  input                       pseldbg,
  input                       penabledbg,
  input                       pwritedbg,
  input [31:0]                pwdatadbg,

  output                      preadydbg,
  output [31:0]               prdatadbg,
  output                      pslverrdbg,

  input                       dbgen,
  input                       niden,


  //////////  clock control block //////////////////////////////////////////
  //
  output                      hor_clock_enable_nxt, // Arch. Clock Enable
  input                       ar_save_clk,
  output                      ar_save_en_r,

  output  [`npuarc_DATA_RANGE]       ar_aux_debug_r,       // AUX Debug
  output  [`npuarc_DATA_RANGE]       ar_aux_status32_r,    // AUX Status 32
  output  [`npuarc_DATA_RANGE]       ar_aux_irq_act_r,     // AUX IRQ ACT
  output                      da_eslot_stall      ,
  output                      da_uop_stall        ,
  output                      x1_dslot_stall      ,
  output                      sa_flag_stall       , //
  output                      sa_stall_r15        ,
  output                      sa_stall_r1         , //
  output                      sa_acc_raw          , //
  output                      ca_acc_waw          , //
  output                      dep_bdcmstall,


  output                      ca_lp_lpcc_evt,
  output                      ca_br_taken,
  output                      ca_has_limm_r,        // (CA) Insn. has limm
  output                      ca_is_16bit_r,        // (CA) Insn. is 16 bit
  output                      ca_br_jmp_op,         // Insn. is BL, BLcc, BL_S, JL, JL_S, JLcc
  output                      ca_jump_r,            // Insn. is Jump
  output                      ca_bcc_r,             //
  output                      ca_brcc_bbit_r,       //
  output                      ca_sleep_evt,
  output                      ca_zol_branch,
  output                      ca_lr_op_r,           // Insn. is LR
  output                      ca_sr_op_r,           // Insn. is SR
  output     [4:0]            ca_q_field_r,         //
  output                      ca_byte_size_r,       //
  output                      ca_hit_lp_end,        // SA insn is at loop-end
  output     [`npuarc_DATA_RANGE]    ar_aux_lp_start_r,    // LP_START aux register
  output  [`npuarc_PC_RANGE]         ar_pc_r,
  output                      commit_normal_evt,
  output                      ca_dslot_r,
  output  [`npuarc_INTEVT_RANGE]     excpn_evts,
  output [`npuarc_INTEVT_RANGE]      int_evts,
  output  [`npuarc_DATA_RANGE]       ar_aux_lp_end_r,      // LP_END aux register
  output                      ca_trap_op_r,
  output [`npuarc_DATA_RANGE]        ar_aux_ecr_r,
  output                      ca_cmt_dbg_evt,
  input [7:0]                 rtt_src_num,
  output                      ca_zol_lp_jmp,        // late ZOL loop-back
  ////////// Auxiliary interface for (RTT) SR/LR instructions ////////////
  //
  output                      aux_rtt_active,       // enable RTT interf clk
  output                      aux_rtt_ren_r,        //  (X3) Aux     Enable
  output  [3:0]               aux_rtt_raddr_r,      //  (X3) Aux Address
  output                      aux_rtt_wen_r,        //  (WA) Aux     Enable
  output  [3:0]               aux_rtt_waddr_r,      //  (WA) Aux Address
  input   [`npuarc_DATA_RANGE]       rtt_aux_rdata,        //  (X3) LR read data
  input                       rtt_aux_illegal,      //  (X3) SR/LR illegal
  input                       rtt_aux_k_rd,         //  (X3) need Kernel Read
  input                       rtt_aux_k_wr,         //  (X3) need Kernel Write
  input                       rtt_aux_unimpl,       //  (X3) Invalid
  input                       rtt_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       rtt_aux_strict_sr,    //  (X3) SR flush pipe

  output  [`npuarc_PC_RANGE]         ar_pc_nxt,
  output  [`npuarc_PFLAG_RANGE]      wa_aux_status32_nxt,

  output                      ca_cond_inst,
  output                      ca_cond_met,

  output                      ca_br_or_jmp_all,
  output                      ca_indir_br,
  output                      ca_in_deslot,
  output                      ca_in_eslot_r,
  output                      rtt_leave_uop_cmt,
  output                      ca_cmt_brk_inst,    // Commit Break inst
  output                      ca_cmt_isi_evt,
  output                      dbg_halt_r,

  input                       da_rtt_stall_r,

  output      [`npuarc_APNUM_RANGE]  aps_active,      // Identity of active hit
  output                      aps_halt,    // Halt due to AP match
  output                      aps_break,   // Break due to AP match
  output      [`npuarc_APS_RANGE]    aps_status,      // All triggered Actionpoints
  output                      aps_excpn,   // Excpn due to AP match

  // AUX register read/write monitoring
  output                      wa_lr_op_r,
  output                      wa_sr_op_r,
  output [`npuarc_AUX_REG_RANGE]     wa_aux_addr_r,

  // Core register write monitoring
  output [`npuarc_RGF_ADDR_RANGE]    wa_rf_wa0_r,
  output                      wa_rf_wenb0_r,
  output [`npuarc_RGF_ADDR_RANGE]    wa_rf_wa1_r,
  output                      wa_rf_wenb1_r,

  output                      wa_rf_wenb0_64_r,
  output                      wa_rf_wenb1_64_r,

  output [`npuarc_DATA_RANGE]        wa_rf_wdata0_lo_r,
  output [`npuarc_DATA_RANGE]        wa_rf_wdata0_hi_r,
  output [`npuarc_DATA_RANGE]        wa_rf_wdata1_lo_r,
  output [`npuarc_DATA_RANGE]        wa_rf_wdata1_hi_r,

  ////////// Unit-level clock gating control outputs to clock_ctrl ///////////
  //
  output                      mpy_unit_enable,      // clk ctrl for multiplier
  input                       mpy_unit_clk,         // clk clk  for multiplier
  output                      div_unit_enable,      // clk ctrl for divider
  input                       div_unit_clk,         // clk clk  for divider
  output                      smt_unit_enable,      // clk ctrl for smart
  input                       smt_unit_clk,         // clk clk  for smart
  output                      ap_unit_enable,
  output                      aux_aps_active,       //
  input                       ap_aux_clk,           // clk for AP Aux
  input                       ap_unit_clk,          // clk for AP


  ////////// IFU/DMP/BIU Halt Interface //////////////////////////////////////
  //
  output                      hlt_wait_idle,        //

  input                       ifu_idle_r,           //
  input                       dmp_idle_r,           //
  input                       dmp_idle1_r,          //
  input                       biu_idle_r,           //

  //////////bist       test////////////////////////////////////



  ////////// External Event Interface /////////////////////////////////////////
  //
  input                       arc_event_r,          //
  output                      wake_from_wait,       // re-enable clock after wait



  ////////// External Halt Interface /////////////////////////////////////////
  //
  input                       gb_sys_halt_req_r,    //
  output                      gb_sys_halt_ack_r,    //
  //
  input                       gb_sys_run_req_r,     //
  output                      gb_sys_run_ack_r,     //
  //
  output                      gb_sys_halt_r,        // Machine halted state
  output                      gb_sys_tf_halt_r,     // Machine halted state (triple flt)
  output                      gb_sys_sleep_r,       // Machine sleeping state
  output                      sync_dsync_dmb_stall,  //  pct event for sync/dsync/dmb stall
  output [`npuarc_EXT_SMODE_RANGE]   gb_sys_sleep_mode_r

);

//////////////////////////////////////////////////////////////////////////////
// Output wires from the Execute Pipeline module                            //
//////////////////////////////////////////////////////////////////////////////


wire [`npuarc_DATA_RANGE]       db_data;
wire                     db_sel_limm0;
wire                     db_sel_limm1;
wire                     wa_aux_pc_wen;
wire                     ca_finish_sgl_step;


wire                        ca_pass_eslot;        // for smart: commit return from EI
wire [`npuarc_PC_RANGE]            ca_pc_jump;           // for smart
wire [`npuarc_PC_RANGE]            aux_eret_addr;        // for smart: exception return address

  ////////// Auxiliary interface for (SMT) SR/LR instructions ////////////
  //
wire                        aux_smt_active;       //  AUX smart is active
wire                        aux_smt_ren_r;        //  (X3) Aux     Enable
wire                        aux_smt_raddr_r;      //  (X3) Aux Address
wire                        aux_smt_wen_r;        //  (WA) Aux     Enable
wire                        aux_smt_waddr_r;      //  (WA) Aux Address
wire  [`npuarc_DATA_RANGE]         smt_aux_rdata;        //  (X3) LR read data
wire                        smt_aux_illegal;      //  (X3) SR/LR illegal
wire                        smt_aux_k_rd;         //  (X3) need Kernel Read
wire                        smt_aux_k_wr;         //  (X3) need Kernel Write
wire                        smt_aux_unimpl;       //  (X3) Invalid
wire                        smt_aux_serial_sr;    //  (X3) SR group flush pipe
wire                        smt_aux_strict_sr;    //  (X3) SR flush pipe

wire                        ca_br_evt;

wire                        wa_enable;
wire                        smt_cap_rst_vec;
wire [`npuarc_PC_RANGE]            ar_pc_save_r;
//////////////////////////////////////////////////////////////////////////////
// Output wires from the Execute Ctrl module                                //
//////////////////////////////////////////////////////////////////////////////

wire                     irq_req;
wire [7:0]               irq_num;
wire [`npuarc_IRQLGN_RANGE]     irq_w;

wire                     irq_ack;
wire [`npuarc_IRQLGN_RANGE]     irq_ack_w_r;
wire                     irq_preempts;
wire                     int_preempt;
wire [`npuarc_IRQN_RANGE]       cpu_accept_irq;
wire                     cpu_irq_select;
wire [7:0]               irq_ack_num;

wire                     aux_irq_ren_r;        //  (X3) Aux     Enable
wire     [11:0]          aux_irq_raddr_r;      //  (X3) Aux Address
wire                     aux_irq_wen_r;        //  (WA) Aux     Enable
wire     [11:0]          aux_irq_waddr_r;      //  (WA) Aux Address
wire     [`npuarc_DATA_RANGE]   irq_aux_rdata;        //  (X3) LR read data
wire                     irq_aux_illegal;      //  (X3) SR/LR illegal
wire                     irq_aux_k_rd;         //  (X3) needs Kernel Read
wire                     irq_aux_k_wr;         //  (X3) needs Kernel W perm
wire                     irq_aux_unimpl;       //  (X3) Invalid
wire                     irq_aux_serial_sr;    //  (X3) SR group flush pipe
wire                     irq_aux_strict_sr;    //  (X3) SR flush pipe

wire     [`npuarc_DATA_RANGE]   ar_aux_icause0_r;  // from alb_irq_unit)
wire     [`npuarc_DATA_RANGE]   ar_aux_icause1_r;  // from alb_irq_unit)
wire     [`npuarc_DATA_RANGE]   ar_aux_icause2_r;  // from alb_irq_unit)



wire                     dbg_we_r;
wire                     dbg_wf_r;

assign dbg_ra_r = ar_aux_debug_r[`npuarc_DEBUG_RA];
assign dbg_bh_r = ar_aux_debug_r[`npuarc_DEBUG_BH]; // break halt
assign dbg_sh_r = ar_aux_debug_r[`npuarc_DEBUG_SH]; // self_halt
assign dbg_eh_r = ar_aux_debug_r[`npuarc_DEBUG_EH]; // external halt
assign dbg_ah_r = ar_aux_debug_r[`npuarc_DEBUG_AH]; // actionpoint halt

assign gb_sys_tf_halt_r = ar_aux_debug_r[`npuarc_DEBUG_TF]; // triple fault  halt

wire                     db_valid;
wire                     db_restart;
wire [`npuarc_DATA_RANGE]       db_inst;
wire [`npuarc_DATA_RANGE]       db_limm;
wire                     ca_cmt_norm_evt;
wire                     ca_cmt_brk_evt;

wire                     gb_sys_reset_done_r;

wire                     ar_tags_empty_r;
wire                     ca_uop_active;
wire                     ct_replay;
wire                     excpn_hld_halt;
wire                     hlt_stop;
wire                     hlt_issue_reset;
wire                     hlt_do_halt;
wire                     hlt_do_unhalt;

wire                     sleep_hlt_wake;
wire                     wevt_wakeup_r;
wire                     wlfc_wakeup;
wire                     sys_halt_ack_r;
wire                     pipe_block_ints;
wire      [`npuarc_DATA_RANGE]  addr_r;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Module instantiation: Execution Pipeline                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_exec_pipe u_alb_exec_pipe (

  ////////// General input signals ///////////////////////////////////////////
  //
  .clk                  (clk                      ),
  .rst_a                (rst_a                    ),
  .arcnum               (arcnum                   ),
  .dmp_queue_empty      (dmp_queue_empty          ),
  .iexcpn_discarded     (iexcpn_discarded         ),
  .st_instrs_discarded  (st_instrs_discarded      ),
  .holdup_excpn_r       (holdup_excpn_r           ),
  .clusternum           (clusternum               ),
  .gb_sys_sleep_r       (gb_sys_sleep_r           ),
  .intvbase_in          (intvbase_in          ),



  .smt_cap_rst_vec        (smt_cap_rst_vec        ),
  .ar_pc_save_r           (ar_pc_save_r           ),

  .ar_save_clk    (ar_save_clk  ),
  .ar_save_en_r   (ar_save_en_r ),


  .dc4_dtlb_miss_r        (dc4_dtlb_miss_r       ),
  .dmp_dc3_dtlb_efa       (dmp_dc3_dtlb_efa      ),
  .dc3_dtlb_miss_excpn_r  (dc3_dtlb_miss_excpn_r ),
  .dc3_dtlb_ovrlp_excpn_r (dc3_dtlb_ovrlp_excpn_r),
  .dc3_dtlb_protv_excpn_r (dc3_dtlb_protv_excpn_r),
  .dc3_dtlb_ecc_excpn_r   (dc3_dtlb_ecc_excpn_r  ),
  .wa_jtlb_lookup_start_r (wa_jtlb_lookup_start_r),
  .wa_jtlb_cancel         (wa_jtlb_cancel        ),
  .ca_tlb_miss_excpn      (ca_tlb_miss_excpn     ),
  .ca_tlb_miss_efa        (ca_tlb_miss_efa       ),
  .ca_m_chk_excpn         (ca_m_chk_excpn        ),
  .x2_da0_transl          (x2_da0_transl         ),
  .mmu_en_r               (mmu_en_r              ),
  .mpu_en_r               (mpu_en_r              ),

  .clk_ungated            (clk_ungated           ),  
// Library ARCv2HS-3.5.999999999


  ////////// EIA user extension external input signals ///////////////////////
  //
  .EventManager_evm_event_a (EventManager_evm_event_a),
  .EventManager_evm_sleep (EventManager_evm_sleep),

  ////////// EIA user extension external output signals //////////////////////
  //
  .EventManager_evm_wakeup (EventManager_evm_wakeup),
  .EventManager_evm_send (EventManager_evm_send),
  .EventManager_vm_grp0_sid (EventManager_vm_grp0_sid),
  .EventManager_vm_grp0_ssid (EventManager_vm_grp0_ssid),
  .EventManager_vm_grp1_sid (EventManager_vm_grp1_sid),
  .EventManager_vm_grp1_ssid (EventManager_vm_grp1_ssid),
  .EventManager_vm_grp2_sid (EventManager_vm_grp2_sid),
  .EventManager_vm_grp3_sid (EventManager_vm_grp3_sid),
  .EventManager_vm_grp2_ssid (EventManager_vm_grp2_ssid),
  .EventManager_vm_grp3_ssid (EventManager_vm_grp3_ssid),
  .EventManager_evt_vm_irq (EventManager_evt_vm_irq),
  .EventManager_evt_vm_sel (EventManager_evt_vm_sel),

  ////////// Debug Interface /////////////////////////////////////////////////
  //
  .db_active            (db_active                ),
  .db_active_r          (db_active_r              ),
  .db_valid             (db_valid                 ),
  .db_inst              (db_inst                  ),
  .db_limm              (db_limm                  ),
  .db_data              (db_data                  ),
  .db_sel_limm0         (db_sel_limm0             ),
  .db_sel_limm1         (db_sel_limm1             ),
  .db_restart           (db_restart               ),

  .sys_halt_ack_r       (sys_halt_ack_r           ),

  .x3_1_db_exception    (x3_1_db_exception        ),
  .ca_cmt_dbg_evt       (ca_cmt_dbg_evt           ),
  .ca_db_exception      (ca_db_exception          ),

  .rtt_ca_pref          (rtt_ca_pref              ), // load with null dest for trace
  .rtt_wa_spl_ld        (rtt_wa_spl_ld            ), //
  .rtt_wa_store         (rtt_wa_store             ),
  .rtt_dmp_retire       (rtt_dmp_retire           ),
  .rtt_dmp_null_ret     (rtt_dmp_null_ret         ),
  .wa_rf_wenb0_r        (wa_rf_wenb0_r            ),
   .ar_aux_ecr_r         (ar_aux_ecr_r             ),
  .ca_cond_inst         (ca_cond_inst             ),
  .ca_cond_met          (ca_cond_met              ),

  .wa_rf_wa0_r          (wa_rf_wa0_r              ),
  .wa_rf_wa1_r          (wa_rf_wa1_r              ),
  .wa_rf_wenb1_r        (wa_rf_wenb1_r            ),

  .wa_rf_wenb0_64_r     (wa_rf_wenb0_64_r         ),
  .wa_rf_wenb1_64_r     (wa_rf_wenb1_64_r         ),

  .wa_lr_op_r           (wa_lr_op_r               ),
  .wa_sr_op_r           (wa_sr_op_r               ),
  .wa_aux_addr_r        (wa_aux_addr_r            ),

  .da_rtt_stall_r       (da_rtt_stall_r           ),

  .wa_rf_wdata0_lo_r    (wa_rf_wdata0_lo_r        ),
  .wa_rf_wdata1_lo_r    (wa_rf_wdata1_lo_r        ),
  .wa_rf_wdata0_hi_r    (wa_rf_wdata0_hi_r        ),
  .wa_rf_wdata1_hi_r    (wa_rf_wdata1_hi_r        ),
  .ca_cmt_norm_evt      (ca_cmt_norm_evt          ),
  .ca_cmt_brk_evt       (ca_cmt_brk_evt           ),
  .ca_cmt_isi_evt       (ca_cmt_isi_evt           ),
  .ca_sleep_evt         (ca_sleep_evt             ),
  .sleep_hlt_wake       (sleep_hlt_wake           ),
  .wevt_wakeup_r        (wevt_wakeup_r            ),
  .wlfc_wakeup          (wlfc_wakeup              ),

  ////////// Fetch-Restart Interface /////////////////////////////////////////
  //
  .fch_restart          (fch_restart              ),
  .fch_restart_vec      (fch_restart_vec          ),
  .fch_target           (fch_target               ),
  .fch_target_successor (fch_target_successor     ),
  .fch_stop_r           (fch_stop_r               ),
  .fch_iprot_replay     (fch_iprot_replay         ),

  ////////// Instruction Issue Interface /////////////////////////////////////
  //
  .al_pass              (al_pass                  ),
  .al_inst              (al_inst                  ),
  .al_limm              (al_limm                  ),

  .al_exception           (al_exception           ),
  .al_excpn_type          (al_excpn_type          ),
  .al_excpn_info          (al_excpn_info          ),
  .al_ifu_err_nxtpg       (al_ifu_err_nxtpg       ),
  .al_iprot_viol          (al_iprot_viol          ),
  .al_is_predicted        (al_is_predicted        ),
  .al_prediction          (al_prediction          ),
  .al_predicted_bta       (al_predicted_bta       ),
  .al_prediction_type     (al_prediction_type     ),
  .al_error_branch        (al_error_branch        ),
  .al_branch_info         (al_branch_info         ),
  .al_with_dslot          (al_with_dslot          ),

  .da_holdup            (da_holdup                ),
 


  ////////// Misprediction Interface /////////////////////////////////////////
  //
  .mpd_mispred          (mpd_mispred              ),
  .mpd_direction        (mpd_direction            ),
  .mpd_error_branch     (mpd_error_branch         ),
  .mpd_is_predicted     (mpd_is_predicted         ),
  .mpd_mispred_outcome  (mpd_mispred_outcome      ),
  .mpd_mispred_bta      (mpd_mispred_bta          ),
  .mpd_branch_info      (mpd_branch_info          ),
  .mpd_dslot            (mpd_dslot                ),
  .mpd_seq_next_pc      (mpd_seq_next_pc          ),
//  .mpd_pc_4_3           (mpd_pc_4_3               ),
  .mpd_type             (mpd_type                 ),
  .mpd_pc               (mpd_pc                   ),
  .mpd_tail_pc_3        (mpd_tail_pc_3            ),
  .mpd_commit_size      (mpd_commit_size          ),
  .mpd_secondary        (mpd_secondary            ),
  .mpd_early            (mpd_early                ),

  ////////// Branch Commit Interface /////////////////////////////////////////
  //
  .wa_pass              (wa_pass                  ),
  .wa_type              (wa_type                  ),
  .wa_secondary         (wa_secondary             ),
  .wa_pc                (wa_pc                    ),
  .wa_tail_pc_3         (wa_tail_pc_3             ),
  .wa_dslot             (wa_dslot                 ),
  .wa_target            (wa_target                ),
  .wa_commit_size       (wa_commit_size           ),
  .wa_direction         (wa_direction             ),
  .wa_error_branch      (wa_error_branch          ),
  .wa_is_predicted      (wa_is_predicted          ),
  .wa_mispred_outcome   (wa_mispred_outcome       ),
  .wa_commit_mispred_bta(wa_commit_mispred_bta    ),
  .wa_branch_info       (wa_branch_info           ),
  .wa_restart_r         (wa_restart_r             ),
  .wa_restart_kill_r    (wa_restart_kill_r        ),

  .zol_depend_stall     (zol_depend_stall         ),

  ////////////// MPU interface for IFU ///////////////////////////////////////
  .ifetch_addr_mpu      (ifetch_addr_mpu          ),
  .ifetch_viol          (ifetch_viol              ),

  ////////// EXU interface to DMP ////////////////////////////////////////////
  //
  .sa_dsync_op_r        (sa_dsync_op_r            ),
  .sa_dmb_op_r          (sa_dmb_op_r              ),
  .sa_dmb_dmp_stall     (sa_dmb_dmp_stall         ),
  // SA
  .sa_load_r            (sa_load_r                ),
  .sa_store_r           (sa_store_r               ),
  .dmp_aux_sr_op        (dmp_aux_sr_op            ),

  .dmp_wr_pending_r     (dmp_wr_pending_r         ),
  .dmp_aux_pending_r    (dmp_aux_pending_r        ),
  .aux_memseg_r         (aux_memseg_r             ),
  // X1
  .dc1_stall            (dc1_stall                ),
  .x1_valid_r           (x1_valid_r               ),
  .x1_pass              (x1_pass                  ),
  .x1_load_r            (x1_load_r                ),
  .x1_store_r           (x1_store_r               ),
  .x1_pref_r            (x1_pref_r                ),
  .x1_cache_byp_r       (x1_cache_byp_r           ),
  .x1_size_r            (x1_size_r                ),
  .x1_mem_addr0         (x1_mem_addr0             ),
  .x1_mem_addr1         (x1_mem_addr1             ),
  .x1_addr_base         (x1_addr_base             ),
  .x1_addr_offset       (x1_addr_offset           ),
  .x1_bank_sel_lo       (x1_bank_sel_lo           ),
  .x1_bank_sel_hi       (x1_bank_sel_hi           ),
  .x1_uop_inst_r        (x1_uop_inst_r            ),
  // X2
  .dc2_stall            (dc2_stall                ),
  .dc2_addr_pass        (dc2_addr_pass            ),
  .dc2_aux_addr         (dc2_aux_addr             ),
  .x2_valid_r           (x2_valid_r               ),
  .x2_pass              (x2_pass                  ),
  .x2_enable            (x2_enable                ),
  .x2_load_r            (x2_load_r                ),
  .x2_store_r           (x2_store_r               ),
  .x2_locked_r          (x2_locked_r              ),
  .x2_pref_r            (x2_pref_r                ),
  .x2_size_r            (x2_size_r                ),
  .x2_cache_byp_r       (x2_cache_byp_r           ),
  .x2_mpu_data_flt      (x2_mpu_data_flt          ),
  .x2_mem_addr_r        (x2_mem_addr_r            ),
  .x2_uop_inst_r        (x2_uop_inst_r            ),
  .x2_exu_stall         (x2_exu_stall             ),
  // X3
  .dmp_dc3_stall_r      (dmp_dc3_stall_r          ),
  .dmp_dc3_fast_byp     (dmp_dc3_fast_byp         ),
  .x3_valid_r           (x3_valid_r               ),
  .x3_pass              (x3_pass                  ),
  .x3_enable            (x3_enable                ),
  .x3_load_r            (x3_load_r                ),
  .x3_store_r           (x3_store_r               ),
  .x3_locked_r          (x3_locked_r              ),
  .x3_pref              (x3_pref                  ),
  .x3_pref_l2           (x3_pref_l2               ),
  .x3_prefw             (x3_prefw                 ),
  .x3_pre_alloc         (x3_pre_alloc             ),
  .x3_size_r            (x3_size_r                ),
  .x3_sex_r             (x3_sex_r                 ),
  .x3_cache_byp_r       (x3_cache_byp_r           ),
  .x3_mem_addr_r        (x3_mem_addr_r            ),
  .x3_uop_inst_r        (x3_uop_inst_r            ),
  .x3_sync_op_r         (x3_sync_op_r             ),
  .x3_brk_op_r          (x3_brk_op_r              ),
  .dc3_excpn            (dc3_excpn                ),
  .dc3_excpn_type       (dc3_excpn_type           ),
  .dc3_excpn_code       (dc3_excpn_code           ),
  // CA
  .dmp_dc4_stall        (dmp_dc4_stall            ),
  .dmp_dc4_fast_byp_r   (dmp_dc4_fast_byp_r       ),
  .dmp_dc4_fast_miss_r  (dmp_dc4_fast_miss_r      ),
  .dmp_dc4_fast_data    (dmp_dc4_fast_data        ),
  .dmp_dc4_rf_wdata_lo  (dmp_dc4_rf_wdata_lo      ),
  .dc4_waw_replay_r     (dc4_waw_replay_r         ),
  .ca_valid_r           (ca_valid_r               ),
  .ca_pass              (ca_pass                  ),
  .ca_pass_eslot        (ca_pass_eslot            ),
  .ca_pc_jump           (ca_pc_jump               ),
  .aux_eret_addr        (aux_eret_addr            ),  // exception return addr
  .ca_enable            (ca_enable                ),
  .wa_enable            (wa_enable                ),
  .ca_load_r            (ca_load_r                ),
//  .ca_pref_r            (ca_pref_r                ),
  .ca_grad_req          (ca_grad_req              ),
  .ca_store_r           (ca_store_r               ),
  .ca_size_r            (ca_size_r                ),
  .ca_sex_r             (ca_sex_r                 ),
  .ca_cache_byp_r       (ca_cache_byp_r           ),
  .ca_pref              (ca_pref                  ),
  .ca_pref_l2           (ca_pref_l2               ),
  .ca_prefw             (ca_prefw                 ),
  .ca_pre_alloc         (ca_pre_alloc             ),
  .ca_mem_addr_r        (ca_mem_addr_r            ),
  .ca_phys_addr_r       (ca_phys_addr_r           ),
  .ca_uop_inst_r        (ca_uop_inst_r            ),
  .dc4_write_data_lo    (dc4_write_data_lo        ),
  .dmp_dc4_rf_wdata_hi  (dmp_dc4_rf_wdata_hi      ),
  .dc4_write_data_hi    (dc4_write_data_hi        ),
  .dmp_idle_r           (dmp_idle_r               ),
  // DMP replay and exceptions
  .dc4_replay           (dc4_replay               ),
  .dc4_excpn            (dc4_excpn                ),
  .dc4_excpn_mem_addr   (dc4_excpn_mem_addr       ),
  .dc4_excpn_type       (dc4_excpn_type           ),
  .dc4_excpn_user_mode_r(dc4_excpn_user_mode_r    ),
  // DMP grad/retire
  .dc4_grad_req         (dc4_grad_req             ),
  .dmp_retire_req       (dmp_retire_req           ),
  .dmp_retire_tag       (dmp_retire_tag           ),
  .dmp_scond_zflag      (dmp_scond_zflag          ),
  .dmp_clear_lf         (dmp_clear_lf             ),
  .wa_lock_flag_r       (wa_lock_flag_r           ),
  .wa_lock_double_r     (wa_lock_double_r         ),
  .wa_lpa_r             (wa_lpa_r                 ),
  .ca_locked_r          (ca_locked_r              ),
  .dmp_retire_ack       (dmp_retire_ack           ),
  .rtt_dc4_scond_go     (rtt_dc4_scond_go         ),  // scond will be success

  .dmp_retire_ld_addr   (dmp_retire_ld_addr       ),
  // AR
  .ar_tags_empty_r      (ar_tags_empty_r          ),
  .ca_uop_active        (ca_uop_active            ),

  ////////// Bus error exception acknowledgement /////////////////////////////
  //
  .mem_excpn_ack_r      (mem_excpn_ack_r          ),

  ////////// Exception exit /////////////////////////////////////////////////
  //
  .excpn_exit_evt        (excpn_exit_evt          ),

  ////////// Common Graduation and Retirement Interface //////////////////////
  //
  .ca_grad_ack          (ca_grad_ack              ),
  .ca_grad_tag          (ca_grad_tag              ),

  ////////// Aux. Interfaces /////////////////////////////////////////////////
  //
  .x3_lr_op_r           (aux_read                 ),
  .x3_sr_op_r           (aux_write                ),
  .wa_sr_data_r         (wa_sr_data_r             ),

  .do_aux_replay_r         (do_aux_replay_r      ),
  .aux_dccm_ren_r       (aux_dccm_ren_r           ),
  .aux_dccm_wen_r       (aux_dccm_wen_r           ),
  .dccm_aux_rdata       (dccm_aux_rdata           ),
  .dccm_aux_illegal     (dccm_aux_illegal         ),
  .dccm_aux_k_rd        (dccm_aux_k_rd            ),
  .dccm_aux_k_wr        (dccm_aux_k_wr            ),
  .dccm_aux_unimpl      (dccm_aux_unimpl          ),
  .dccm_aux_serial_sr   (dccm_aux_serial_sr       ),
  .dccm_aux_strict_sr   (dccm_aux_strict_sr       ),

  .aux_dper_ren_r       (aux_dper_ren_r           ),
  .aux_dper_raddr_r     (aux_dper_raddr_r         ),
  .aux_dper_wen_r       (aux_dper_wen_r           ),
  .aux_dper_waddr_r     (aux_dper_waddr_r         ),
  .dper_aux_rdata       (dper_aux_rdata           ),
  .dper_aux_illegal     (dper_aux_illegal         ),
  .dper_aux_k_rd        (dper_aux_k_rd            ),
  .dper_aux_k_wr        (dper_aux_k_wr            ),
  .dper_aux_unimpl      (dper_aux_unimpl          ),
  .dper_aux_serial_sr   (dper_aux_serial_sr       ),
  .dper_aux_strict_sr   (dper_aux_strict_sr       ),
  .aux_dc_ren_r         (aux_dc_ren_r             ),
  .aux_dc_raddr_r       (aux_dc_raddr_r           ),
  .aux_dc_wen_r         (aux_dc_wen_r             ),
  .aux_dc_waddr_r       (aux_dc_waddr_r           ),
  .dc_aux_rdata         (dc_aux_rdata             ),
  .dc_aux_illegal       (dc_aux_illegal           ),
  .dc_aux_k_rd          (dc_aux_k_rd              ),
  .dc_aux_k_wr          (dc_aux_k_wr              ),
  .dc_aux_unimpl        (dc_aux_unimpl            ),
  .dc_aux_serial_sr     (dc_aux_serial_sr         ),
  .dc_aux_strict_sr     (dc_aux_strict_sr         ),
  .dc_aux_busy          (dc_aux_busy              ),

  .aux_ic_ren_r         (aux_ic_ren_r             ),
  .aux_ic_raddr_r       (aux_ic_raddr_r           ),
  .aux_ic_wen_r         (aux_ic_wen_r             ),
  .aux_ic_waddr_r       (aux_ic_waddr_r           ),
  .ic_aux_rdata         (ic_aux_rdata             ),
  .ic_aux_illegal       (ic_aux_illegal           ),
  .ic_aux_k_rd          (ic_aux_k_rd              ),
  .ic_aux_k_wr          (ic_aux_k_wr              ),
  .ic_aux_unimpl        (ic_aux_unimpl            ),
  .ic_aux_serial_sr     (ic_aux_serial_sr         ),
  .ic_aux_strict_sr     (ic_aux_strict_sr         ),

  .aux_bpu_ren_r        (aux_bpu_ren_r            ),
  .aux_bpu_raddr_r      (aux_bpu_raddr_r          ),
  .aux_bpu_wen_r        (aux_bpu_wen_r            ),
  .aux_bpu_waddr_r      (aux_bpu_waddr_r          ),
  .bpu_aux_rdata        (bpu_aux_rdata            ),
  .bpu_aux_illegal      (bpu_aux_illegal          ),
  .bpu_aux_k_rd         (bpu_aux_k_rd             ),
  .bpu_aux_k_wr         (bpu_aux_k_wr             ),
  .bpu_aux_unimpl       (bpu_aux_unimpl           ),
  .bpu_aux_serial_sr    (bpu_aux_serial_sr        ),
  .bpu_aux_strict_sr    (bpu_aux_strict_sr        ),

  .int_evts             (int_evts                 ),

  .aux_smt_active       (aux_smt_active           ),      
  .aux_smt_ren_r        (aux_smt_ren_r            ),
  .aux_smt_raddr_r      (aux_smt_raddr_r          ),
  .aux_smt_wen_r        (aux_smt_wen_r            ),
  .aux_smt_waddr_r      (aux_smt_waddr_r          ),
  .smt_aux_rdata        (smt_aux_rdata            ),
  .smt_aux_illegal      (smt_aux_illegal          ),
  .smt_aux_k_rd         (smt_aux_k_rd             ),
  .smt_aux_k_wr         (smt_aux_k_wr             ),
  .smt_aux_unimpl       (smt_aux_unimpl           ),
  .smt_aux_serial_sr    (smt_aux_serial_sr        ),
  .smt_aux_strict_sr    (smt_aux_strict_sr        ),

  .ca_br_evt            (ca_br_evt                ),


  .da_eslot_stall       (da_eslot_stall           ),
  .da_uop_stall         (da_uop_stall             ),
  .x1_dslot_stall       (x1_dslot_stall           ),
  .sa_flag_stall        (sa_flag_stall            ),
  .sa_stall_r15          ( sa_stall_r15        ),
  .sa_stall_r1          (sa_stall_r1              ),
  .sa_acc_raw           (sa_acc_raw               ),
  .ca_acc_waw           (ca_acc_waw               ),
  .dep_bdcmstall        (dep_bdcmstall            ),
  .ca_lp_lpcc_evt          (ca_lp_lpcc_evt              ),
  .ca_br_taken          (ca_br_taken              ),

  .ca_has_limm_r        (ca_has_limm_r            ),
  .ca_is_16bit_r        (ca_is_16bit_r            ),

  .ca_br_jmp_op         (ca_br_jmp_op             ),
  .ca_jump_r            (ca_jump_r                ),
  .ca_bcc_r             (ca_bcc_r                 ),
  .ca_brcc_bbit_r       (ca_brcc_bbit_r           ),
  .ca_zol_branch        (ca_zol_branch            ),
  .ca_lr_op_r           (ca_lr_op_r               ),
  .ca_sr_op_r           (ca_sr_op_r               ),
  .ca_q_field_r         (ca_q_field_r             ),
  .ca_byte_size_r       (ca_byte_size_r           ),
  .ca_hit_lp_end        (ca_hit_lp_end            ),
  .ar_aux_lp_start_r    (ar_aux_lp_start_r        ),
  .gb_sys_halt_r        (gb_sys_halt_r            ),
  .ar_pc_r              (ar_pc_r                  ),
  .excpn_evts           (excpn_evts               ),
  .ar_aux_lp_end_r      (ar_aux_lp_end_r          ),
  .ca_trap_op_r         (ca_trap_op_r             ),
  .ar_pc_nxt            (ar_pc_nxt                ),
  .wa_aux_status32_nxt  (wa_aux_status32_nxt      ),
  .ca_zol_lp_jmp        (ca_zol_lp_jmp            ),
  .wdt_x3_stall         (wdt_x3_stall             ),
  .x3_kill              (x3_kill                  ),

  .rtt_src_num          (rtt_src_num              ),

  .aux_rtt_active       (aux_rtt_active           ),
  .aux_rtt_ren_r        (aux_rtt_ren_r            ),
  .aux_rtt_raddr_r      (aux_rtt_raddr_r          ),
  .aux_rtt_wen_r        (aux_rtt_wen_r            ),
  .aux_rtt_waddr_r      (aux_rtt_waddr_r          ),
  .rtt_aux_rdata        (rtt_aux_rdata            ),
  .rtt_aux_illegal      (rtt_aux_illegal          ),
  .rtt_aux_k_rd         (rtt_aux_k_rd             ),
  .rtt_aux_k_wr         (rtt_aux_k_wr             ),
  .rtt_aux_unimpl       (rtt_aux_unimpl           ),
  .rtt_aux_serial_sr    (rtt_aux_serial_sr        ),
  .rtt_aux_strict_sr    (rtt_aux_strict_sr        ),

//.ca_cond_inst         (ca_cond_inst        ),
//.ca_cond_met          (ca_cond_met         ),
  .ca_br_or_jmp_all     (ca_br_or_jmp_all    ),
  .ca_indir_br          (ca_indir_br         ),
  .ca_in_deslot         (ca_in_deslot        ),
  .ca_in_eslot_r        (ca_in_eslot_r       ),
  .rtt_leave_uop_cmt      (rtt_leave_uop_cmt     ),
  .ca_cmt_brk_inst      (ca_cmt_brk_inst     ),
  .dbg_halt_r           (dbg_halt_r          ),

  .aps_active      (aps_active      ),
  .aps_halt        (aps_halt        ),
  .aps_break       (aps_break       ),
  .aps_status           (aps_status           ),
  .aps_excpn            (aps_excpn            ),

  .ap_tkn          (ap_tkn          ),

  .commit_normal_evt    (commit_normal_evt   ),
  .ca_dslot_r           (ca_dslot_r          ),
  .aux_tm0_ren_r        (aux_tm0_ren_r            ),
  .aux_tm0_raddr_r      (aux_tm0_raddr_r          ),
  .aux_tm0_wen_r        (aux_tm0_wen_r            ),
  .aux_tm0_waddr_r      (aux_tm0_waddr_r          ),
  .tm0_aux_rdata        (tm0_aux_rdata            ),
  .tm0_aux_illegal      (tm0_aux_illegal          ),
  .tm0_aux_k_rd         (tm0_aux_k_rd             ),
  .tm0_aux_k_wr         (tm0_aux_k_wr             ),
  .tm0_aux_unimpl       (tm0_aux_unimpl           ),
  .tm0_aux_serial_sr    (tm0_aux_serial_sr        ),

  .aux_timer_active     (aux_timer_active         ),    
  .aux_irq_ren_r        (aux_irq_ren_r            ),
  .aux_irq_raddr_r      (aux_irq_raddr_r          ),
  .aux_irq_wen_r        (aux_irq_wen_r            ),
  .aux_irq_waddr_r      (aux_irq_waddr_r          ),
  .irq_aux_rdata        (irq_aux_rdata            ),
  .irq_aux_illegal      (irq_aux_illegal          ),
  .irq_aux_k_rd         (irq_aux_k_rd             ),
  .irq_aux_k_wr         (irq_aux_k_wr             ),
  .irq_aux_unimpl       (irq_aux_unimpl           ),
  .irq_aux_serial_sr    (irq_aux_serial_sr        ),
  .irq_aux_strict_sr    (irq_aux_strict_sr        ),

  .aux_wdt_ren_r        (aux_wdt_ren_r            ),
  .aux_wdt_raddr_r      (aux_wdt_raddr_r          ),
  .aux_wdt_wen_r        (aux_wdt_wen_r            ),
  .aux_wdt_waddr_r      (aux_wdt_waddr_r          ),
  .wdt_aux_rdata        (wdt_aux_rdata            ),
  .wdt_aux_illegal      (wdt_aux_illegal          ),
  .wdt_aux_k_rd         (wdt_aux_k_rd             ),
  .wdt_aux_k_wr         (wdt_aux_k_wr             ),
  .wdt_aux_unimpl       (wdt_aux_unimpl           ),
  .wdt_aux_serial_sr    (wdt_aux_serial_sr        ),
  .wdt_aux_strict_sr    (wdt_aux_strict_sr        ),

  .aux_rtc_ren_r        (aux_rtc_ren_r            ),
  .aux_rtc_raddr_r      (aux_rtc_raddr_r          ),
  .aux_rtc_wen_r        (aux_rtc_wen_r            ),
  .aux_rtc_waddr_r      (aux_rtc_waddr_r          ),
  .rtc_aux_rdata        (rtc_aux_rdata            ),
  .rtc_aux_illegal      (rtc_aux_illegal          ),
  .rtc_aux_k_rd         (rtc_aux_k_rd             ),
  .rtc_aux_k_wr         (rtc_aux_k_wr             ),
  .rtc_aux_unimpl       (rtc_aux_unimpl           ),
  .rtc_aux_serial_sr    (rtc_aux_serial_sr        ),
  .rtc_aux_strict_sr    (rtc_aux_strict_sr        ),

  .rtc_na               (rtc_na                   ),
  .aux_rs_valid          (aux_rs_valid          ), //
  .aux_rs_region         (aux_rs_region         ), //
  .aux_rs_addr           (aux_rs_addr           ), //
  .aux_rs_read           (aux_rs_read           ), //
  .aux_rs_write          (aux_rs_write          ), //
  .aux_rs_data           (aux_rs_data           ), //
  .aux_rs_status         (aux_rs_status         ), //
  .aux_rs_accept         (aux_rs_accept         ), //

  .aux_wr_valid          (aux_wr_valid          ), //
  .aux_wr_region         (aux_wr_region         ), //
  .aux_wr_addr           (aux_wr_addr           ), //
  .aux_wr_allow          (aux_wr_allow          ), //
  .aux_cm_phase          (aux_cm_phase          ), //
  .aux_cm_valid          (aux_cm_valid          ), //
  .aux_pct_active       (aux_pct_active           ),     
  .aux_pct_ren_r        (aux_pct_ren_r            ),
  .aux_pct_raddr_r      (aux_pct_raddr_r          ),
  .aux_pct_wen_r        (aux_pct_wen_r            ),
  .aux_pct_waddr_r      (aux_pct_waddr_r          ),
  .pct_aux_rdata        (pct_aux_rdata            ),
  .pct_aux_illegal      (pct_aux_illegal          ),
  .pct_aux_k_rd         (pct_aux_k_rd             ),
  .pct_aux_k_wr         (pct_aux_k_wr             ),
  .pct_aux_unimpl       (pct_aux_unimpl           ),
  .pct_aux_serial_sr    (pct_aux_serial_sr        ),
  .pct_aux_strict_sr    (pct_aux_strict_sr        ),

  .aux_mmu_ren_r        (aux_mmu_ren_r            ),
  .aux_mmu_raddr_r      (aux_mmu_raddr_r          ),
  .aux_mmu_wen_r        (aux_mmu_wen_r            ),
  .aux_mmu_waddr_r      (aux_mmu_waddr_r          ),
  .mmu_aux_rdata        (mmu_aux_rdata            ),
  .mmu_aux_illegal      (mmu_aux_illegal          ),
  .mmu_aux_k_rd         (mmu_aux_k_rd             ),
  .mmu_aux_k_wr         (mmu_aux_k_wr             ),
  .mmu_aux_unimpl       (mmu_aux_unimpl           ),
  .mmu_aux_serial_sr    (mmu_aux_serial_sr        ),
  .mmu_aux_strict_sr    (mmu_aux_strict_sr        ),

  .ecc_flt_status       (ecc_flt_status           ),  //
  .ecc_sbe_count_r      (ecc_sbe_count_r          ),
  .ecc_sbe_clr            (ecc_sbe_clr          ),
  .ecc_sbe_dmp_clr      (ecc_sbe_dmp_clr          ),
  ////////// Machine Architectural state /////////////////////////////////////
  //
  .ar_aux_status32_r    (ar_aux_status32_r        ),
  .ar_aux_debug_r       (ar_aux_debug_r           ),
  .dbg_we_r             (dbg_we_r                 ),
  .dbg_wf_r             (dbg_wf_r                 ),

  .ar_aux_ecc_ctrl_r    (ar_aux_ecc_ctrl_r        ),  //

  ////////// Interrupt/Exception Interface ///////////////////////////////////
  //
  .irq_req              (irq_req                  ),
  .irq_num              (irq_num                  ),
  .irq_w                (irq_w                    ),
  .irq_preempts         (irq_preempts             ),
  .irq_ack_w_r          (irq_ack_w_r              ),
  .cpu_accept_irq       (cpu_accept_irq           ),
  .cpu_irq_select       (cpu_irq_select           ),
  .irq_ack              (irq_ack                  ),
  .irq_ack_num          (irq_ack_num              ),

  .ar_aux_icause0_r  (ar_aux_icause0_r      ),
  .ar_aux_icause1_r  (ar_aux_icause1_r      ),
  .ar_aux_icause2_r  (ar_aux_icause2_r      ),
  .ar_aux_irq_act_r     (ar_aux_irq_act_r         ),

  .int_preempt          (int_preempt              ),


  ////////// Global State retained by EXU ////////////////////////////////////
  //
  .gb_sys_reset_done_r  (gb_sys_reset_done_r      ),

  ////////// Unit-level clock gating control outputs to clock_ctrl ///////////
  //
  .mpy_unit_enable      (mpy_unit_enable          ),
  .mpy_unit_clk         (mpy_unit_clk             ),
  .div_unit_enable      (div_unit_enable          ),
  .div_unit_clk         (div_unit_clk             ),
  .ap_unit_enable       (ap_unit_enable           ),
  .aux_aps_active       (aux_aps_active           ),
  .ap_aux_clk           (ap_aux_clk               ),
  .ap_unit_clk          (ap_unit_clk              ),



  ////////// Halt Interface //////////////////////////////////////////////////
  //
  .hlt_do_halt          (hlt_do_halt              ),
  .hlt_do_unhalt        (hlt_do_unhalt            ),
  .pipe_block_ints      (pipe_block_ints          ),
  .wa_aux_pc_wen        (wa_aux_pc_wen            ),
  .ca_finish_sgl_step   (ca_finish_sgl_step       ),
  .excpn_restart        (excpn_restart            ),
  .ct_replay            (ct_replay                ),

//`if ((`HAS_SAFETY) && (`EDC_ERROR_INJECTION == 1) && (`SAFETY_LEVEL > 0))
//  .cpu_safety_diag_inject_edc (cpu_safety_diag_inject_edc),
//  .cpu_error_mask        (cpu_error_mask       ),
//  .cpu_valid_mask        (cpu_valid_mask       ),
//`endif

  .excpn_hld_halt       (excpn_hld_halt           ),
  .hlt_stop             (hlt_stop                 ),
  .hlt_issue_reset      (hlt_issue_reset          ),
   .sync_dsync_dmb_stall (sync_dsync_dmb_stall     ),// pct event for sync/dsync/dmb stall

  .hlt_restart          (wa_hlt_restart_r         )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Module instantiation: Execution Pipe Control                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_exec_ctrl u_alb_exec_ctrl (

  ////////// General input signals ///////////////////////////////////////////
  //
  .clk                  (clk                      ),
  .smt_unit_clk         (smt_unit_clk             ),     
  .rst_a                (rst_a                    ),
  .l1_clock_active      (l1_clock_active          ),  

  ////////// Machine Architectural state /////////////////////////////////////
  //
  .ar_aux_status32_r    (ar_aux_status32_r        ),
  .ar_aux_debug_r       (ar_aux_debug_r           ),
  .dbg_we_r             (dbg_we_r                 ),
  .dbg_wf_r             (dbg_wf_r                 ),

  ////////// Global Machine State ////////////////////////////////////////////
  //
  .gb_sys_reset_done_r  (gb_sys_reset_done_r      ),
  ////////// BVCI Debug Command Interface ////////////////////////////////////
  //
  .dbg_cmdval           (dbg_cmdval               ),
  .dbg_cmdack           (dbg_cmdack               ),
  .dbg_address          (dbg_address              ),
  .dbg_be               (dbg_be                   ),
  .dbg_cmd              (dbg_cmd                  ),
  .dbg_wdata            (dbg_wdata                ),
  .dbg_rspack           (dbg_rspack               ),
  .dbg_rspval           (dbg_rspval               ),
  .dbg_rdata            (dbg_rdata                ),
  .dbg_reop             (dbg_reop                 ),
  .dbg_rerr             (dbg_rerr                 ),

  .debug_reset          (debug_reset              ),

  ////////// APB debug interface /////////////////////////////////////////////

  .dbg_prot_sel         (dbg_prot_sel             ),
  .pclkdbg_en           (pclkdbg_en               ),
  .presetdbgn             (presetdbgn),
  .paddrdbg               (paddrdbg             ),
  .pseldbg                (pseldbg              ),
  .penabledbg             (penabledbg           ),
  .pwritedbg              (pwritedbg            ),
  .pwdatadbg              (pwdatadbg            ),
  .preadydbg              (preadydbg            ),
  .prdatadbg              (prdatadbg            ),
  .pslverrdbg             (pslverrdbg           ),
  .dbgen                  (dbgen                ),
  .niden                  (niden                ),
  .arcnum                 (arcnum),

  .ca_pass_eslot        (ca_pass_eslot            ),
  .ca_pc_jump           (ca_pc_jump               ),
  .aux_eret_addr        (aux_eret_addr            ),  // exception return addr
  .smt_cap_rst_vec       (smt_cap_rst_vec      ),
  .ar_pc_save_r          (ar_pc_save_r         ),
  .aux_write            (aux_write                ),
  .aux_read             (aux_read                 ),


  ////////// Interrupt signals ///////////////////////////////////////////////
  //
  .timer0_irq_1h        (timer0_irq_1h            ),

  .wdt_int_timeout_1h_r        ( wdt_int_timeout_1h_r   ),
  .pct_int_overflow_r          (pct_int_overflow_r   ),
 // .clk_resync           (clk_resync               ),
//  .irq_sync_req_a       (irq_sync_req_a           ),

  .irq_clk_en_r         (irq_clk_en_r             ),


  .irq_r                 (irq_r              ),


  ////////// Interrupt/Exception Interface ///////////////////////////////////
  //
  .irq_req              (irq_req                  ),
  .irq_num              (irq_num                  ),
  .irq_w                (irq_w                    ),
  .irq_preempts         (irq_preempts             ),
  .irq_preempts_nxt     (irq_preempts_nxt         ),
  .irq_ack_w_r          (irq_ack_w_r              ),
  .cpu_accept_irq       (cpu_accept_irq           ),
  .irq_ack              (irq_ack                  ),
  .irq_ack_num          (irq_ack_num              ),

  .int_preempt          (int_preempt              ),

  .ar_aux_icause0_r  (ar_aux_icause0_r      ),
  .ar_aux_icause1_r  (ar_aux_icause1_r      ),
  .ar_aux_icause2_r  (ar_aux_icause2_r      ),
  .ar_aux_irq_act_r     (ar_aux_irq_act_r         ),

  ////////// Interrupt aux register interface ////////////////////////////////
  //
  .aux_wdata            (wa_sr_data_r             ),

  .aux_irq_ren_r        (aux_irq_ren_r            ),
  .aux_irq_raddr_r      (aux_irq_raddr_r          ),
  .aux_irq_wen_r        (aux_irq_wen_r            ),
  .aux_irq_waddr_r      (aux_irq_waddr_r          ),
  .irq_aux_rdata        (irq_aux_rdata            ),
  .irq_aux_illegal      (irq_aux_illegal          ),
  .irq_aux_k_rd         (irq_aux_k_rd             ),
  .irq_aux_k_wr         (irq_aux_k_wr             ),
  .irq_aux_unimpl       (irq_aux_unimpl           ),
  .irq_aux_serial_sr    (irq_aux_serial_sr        ),
  .irq_aux_strict_sr    (irq_aux_strict_sr        ),


  ////////// Debug/Pipeline Interface ////////////////////////////////////////
  //
  .db_valid             (db_valid                 ),
  .db_active            (db_active                ),
  .db_active_r          (db_active_r              ),
  .db_inst              (db_inst                  ),
  .db_limm              (db_limm                  ),
  .db_data              (db_data                  ),
  .db_sel_limm0         (db_sel_limm0             ),
  .db_sel_limm1         (db_sel_limm1             ),
  .db_restart           (db_restart               ),

  .ca_cmt_dbg_evt       (ca_cmt_dbg_evt           ),
  .ca_db_exception_r    (ca_db_exception          ),

  ////////// Retirement Interface ////////////////////////////////////////////
  //
  .wa_rf_wdata0_lo_r    (wa_rf_wdata0_lo_r        ),
  .wa_rf_wdata1_lo_r    (wa_rf_wdata1_lo_r        ),

  //////////bist       test////////////////////////////////////

  ////////// Halt Interface to EXEC_PIPE /////////////////////////////////////
  //
  .ca_cmt_brk_evt       (ca_cmt_brk_evt           ),
  .ca_cmt_isi_evt       (ca_cmt_isi_evt           ),
  .ca_sleep_evt         (ca_sleep_evt             ),
  .sleep_hlt_wake       (sleep_hlt_wake           ),
  .arc_event_r          (arc_event_r              ),
  .wevt_wakeup_r        (wevt_wakeup_r            ),
  .wa_lock_flag_r       (wa_lock_flag_r           ),
  .wlfc_wakeup          (wlfc_wakeup              ),

  .wa_aux_pc_wen        (wa_aux_pc_wen            ),
  .ca_finish_sgl_step   (ca_finish_sgl_step       ),
  .wake_from_wait       (wake_from_wait           ),

  ////////// Halt Interface to EXEC_PIPE /////////////////////////////////////
  //
  .ar_tags_empty_r      (ar_tags_empty_r          ),
  .ca_uop_active        (ca_uop_active            ),
  .wa_restart_r         (wa_restart_r             ),
  .wa_restart_kill_r    (wa_restart_kill_r        ),
  .fch_stop_r           (fch_stop_r               ),
  .excpn_restart        (excpn_restart            ),
  .ct_replay            (ct_replay                ),
  .excpn_hld_halt       (excpn_hld_halt           ),
  .hlt_stop             (hlt_stop                 ),
  .hlt_restart_r        (wa_hlt_restart_r         ),
  .hlt_issue_reset      (hlt_issue_reset          ),
  .hor_clock_enable_nxt (hor_clock_enable_nxt     ),
  .hlt_do_halt          (hlt_do_halt              ),
  .hlt_do_unhalt        (hlt_do_unhalt            ),
  .pipe_block_ints      (pipe_block_ints          ),
  .hlt_wait_idle        (hlt_wait_idle            ),
  .db_clock_enable_nxt  (db_clock_enable_nxt      ),
  .ar_clock_enable_r    (ar_clock_enable_r        ),

  ////////// Aux. Interfaces /////////////////////////////////////////////////
  //
  .wa_sr_data_r         (wa_sr_data_r             ),
  .int_evts             (int_evts                 ),

  ////////// SmaRT Interface to EXEC_PIPE ///////////////////////////////////
  //
  .aux_smt_active       (aux_smt_active           ),       
  .aux_smt_ren_r        (aux_smt_ren_r            ),
  .aux_smt_raddr_r      (aux_smt_raddr_r          ),
  .aux_smt_wen_r        (aux_smt_wen_r            ),
  .aux_smt_waddr_r      (aux_smt_waddr_r          ),
  .smt_aux_rdata        (smt_aux_rdata            ),
  .smt_aux_illegal      (smt_aux_illegal          ),
  .smt_aux_k_rd         (smt_aux_k_rd             ),
  .smt_aux_k_wr         (smt_aux_k_wr             ),
  .smt_aux_unimpl       (smt_aux_unimpl           ),
  .smt_aux_serial_sr    (smt_aux_serial_sr        ),
  .smt_aux_strict_sr    (smt_aux_strict_sr        ),
  .smt_unit_enable      (smt_unit_enable          ),  

  .ca_br_evt            (ca_br_evt                ),


  .ca_pass              (ca_pass                  ),
  .ca_trap_op_r         (ca_trap_op_r             ),
  .ar_pc_nxt            (ar_pc_nxt                ),
  .ar_pc_r              (ar_pc_r                  ),
  .ar_aux_lp_end_r      (ar_aux_lp_end_r          ),
  .wa_aux_status32_nxt  (wa_aux_status32_nxt      ),
  .excpn_evts           (excpn_evts               ),
  .ca_zol_lp_jmp        (ca_zol_lp_jmp            ),
  .wa_pc_r              (wa_pc                    ),

  ////////// IFU/DMP Halt Interface //////////////////////////////////////////
  //
  .ifu_idle_r           (ifu_idle_r               ),
  .dmp_idle_r           (dmp_idle_r               ),
  .dmp_idle1_r          (dmp_idle1_r              ),
  .biu_idle_r           (biu_idle_r               ),

  ////////// External Halt Interface /////////////////////////////////////////
  //
  .gb_sys_halt_req_r    (gb_sys_halt_req_r        ),
  .gb_sys_halt_ack_r    (gb_sys_halt_ack_r        ),
  .sys_halt_ack_r       (sys_halt_ack_r           ),

  .gb_sys_run_req_r     (gb_sys_run_req_r         ),
  .gb_sys_run_ack_r     (gb_sys_run_ack_r         ),

  .gb_sys_halt_r        (gb_sys_halt_r            ),
  .gb_sys_sleep_r       (gb_sys_sleep_r           )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output Assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign gb_sys_sleep_mode_r = ar_aux_debug_r[`npuarc_DEBUG_SM];
assign ar_user_mode_r      = ar_aux_status32_r[`npuarc_U_FLAG];
assign aux_wr_data         = wa_sr_data_r;

assign ca_store_grad        = 2'b00;
assign ca_store_grad_swap   = 2'b00;
assign ca_store_grad_tag_lo = `npuarc_GRAD_TAG_BITS'd0;
assign ca_store_grad_tag_hi = `npuarc_GRAD_TAG_BITS'd0;
assign wa_retire0_valid = 1'b0;
assign wa_retire0_tag   = `npuarc_GRAD_TAG_BITS'd0;
assign wa_retire1_valid = 1'b0;
assign wa_retire1_tag   = `npuarc_GRAD_TAG_BITS'd0;




assign x3_store_may_grad = 1'b0;


endmodule // alb_exu
