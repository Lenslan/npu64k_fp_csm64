// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2014 Synopsys, Inc. All rights reserved.
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
//----------------------------------------------------------------------------
//
// #######  #     #  #######   #####          ######   ###  ######   #######
// #         #   #   #        #     #         #     #   #   #     #  #
// #          # #    #        #               #     #   #   #     #  #
// #####       #     #####    #               ######    #   ######   #####
// #          # #    #        #               #         #   #        #
// #         #   #   #        #     #         #         #   #        #
// #######  #     #  #######   #####   #####  #        ###  #        #######
//
// ===========================================================================
// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"
//
// Description:
//
//  This module instantiates, and connects together, the pipeline stages
//  responsible for executing the majority of instructions.
//  It is not responsible for memory-access instructions, nor for the
//  implementation of user-extension instructions. This pipeline includes
//  the Execute, Result-select, Commit and Writeback stages.
//
//  The module hierarchy, at and below this module, is:
//
//         alb_exec_pipe
//            |
//            +-- alb_dec_regs
//            |      |
//            |      +-- alb_predecode
//            |      |
//            |      +-- alb_decode
//            |      |
//            |      +-- alb_uop_seq_al
//            |      |
//            |      +-- alb_uop_seq_da
//            |
//            +-- alb_opd_sel
//            |      |
//            |      +-- regfile_2r2w
//            |
//            +-- alb_exec1
//            |      |
//            |      +-- alb_agu
//            |      |
//            |      +-- alb_alu
//            |             |
//            |             +-- alb_maskgen
//            |             |
//            |             +-- alb_adder
//            |             |
//            |             +-- alb_logic_unit
//            |             |
//            |             +-- alb_shifter
//            |             |
//            |             +-- alb_byte_unit
//            |             |
//            |             +-- alb_bitscan
//            |
//            +-- alb_exec2
//            |
//            +-- alb_exec3
//            |
//            +-- alb_commit
//            |
//            +-- alb_writeback
//            |
//            +-- alb_dep_pipe
//            |
//            +-- alb_aux_ctrl
//            |
//            +-- alb_mpy_pipe
//            |
//            +-- alb_eia_pipe
//            |
//            +-- alb_div_pipe
//            |
//            +-- alb_mpu
//            |
//            +-- alb_sc_pipe
//            |
//            +-- alb_actionpoints
//
//
// ===========================================================================

/// determine if EIA extensions have 64-bit result at commit or post-commit


// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//
`include "npuarc_ucode_const.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_exec_pipe (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,                // clock signal
  input                       rst_a,              // reset signal
  input     [7:0]             arcnum,             // processor ID
  input     [7:0]             clusternum,         // for cluster_id register
  input                       dmp_queue_empty,
  input                       iexcpn_discarded,
  input                       st_instrs_discarded,
  output                      holdup_excpn_r,
  input                       gb_sys_sleep_r,
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
  input                       gb_sys_halt_r,      // Machine halted state

  ////////// Debug Interface /////////////////////////////////////////////////
  //
  input                       db_active,          // debug operation is active
  input                       db_active_r,        // debug operation is active
  input                       db_valid,           //
  input  [`npuarc_DATA_RANGE]        db_inst,            //
  input  [`npuarc_DATA_RANGE]        db_limm,            //
  input  [`npuarc_DATA_RANGE]        db_data,            // Data for db_inst             
  input                       db_sel_limm0,       // select debug limm for opd_1  
  input                       db_sel_limm1,       // select debug limm for store  
  output                      db_restart,         // Debug is restarted

  input                       sys_halt_ack_r,     //

  output                      x3_1_db_exception,  //
  output                      ca_cmt_dbg_evt,     //
  output                      ca_db_exception,    //

  output [`npuarc_DATA_RANGE]        wa_rf_wdata0_lo_r /* verilator public_flat */,  // WA data bus port 0
  output [`npuarc_DATA_RANGE]        wa_rf_wdata1_lo_r /* verilator public_flat */,  // WA data bus port 1

  output [`npuarc_DATA_RANGE]        ar_aux_ecr_r,
  input [7:0]                 rtt_src_num,

  output                      rtt_ca_pref,        // load with null dest for trace
  output                      rtt_wa_spl_ld,      // Special Loads for Trace
  output                      rtt_wa_store,       // WA Store for Trace
  output                      rtt_dmp_retire,     // DMP retire for Trace
  output                      rtt_dmp_null_ret,   // DMP null retire rpt for Trace
  output [`npuarc_RGF_ADDR_RANGE]    wa_rf_wa0_r   /* verilator public_flat */,
  output                      wa_rf_wenb0_r /* verilator public_flat */,
  output [`npuarc_RGF_ADDR_RANGE]    wa_rf_wa1_r   /* verilator public_flat */,
  output                      wa_rf_wenb1_r /* verilator public_flat */,

  output [`npuarc_DATA_RANGE]        wa_rf_wdata0_hi_r,
  output                      wa_rf_wenb0_64_r,
  output [`npuarc_DATA_RANGE]        wa_rf_wdata1_hi_r,
  output                      wa_rf_wenb1_64_r,


  output                      wa_lr_op_r,
  output                      wa_sr_op_r,
  output     [`npuarc_AUX_REG_RANGE] wa_aux_addr_r,

  input                       da_rtt_stall_r,


  output                      ca_cmt_norm_evt,    // Commit Normal Insn.
  output                      ca_cmt_brk_evt,     // Commit BRK insn.
  output                      ca_cmt_isi_evt,     //
  output                      ca_sleep_evt,       //
  input                       sleep_hlt_wake,     // Sleep Halt Wake
  input                       wevt_wakeup_r,      // WEVT wakeup event
  input                       wlfc_wakeup,        // WLFC wakeup event

  ////////// Fetch-Restart Interface /////////////////////////////////////////
  //
  output reg                  fch_restart,        // Perform pipeline restart
  output reg                  fch_restart_vec,    // Restart from vector
  output reg [`npuarc_PC_RANGE]      fch_target,         // Restart location
  output reg [`npuarc_IM_LINE_BITS:3]fch_target_successor,
  output reg                  fch_stop_r,         // EXU requests IFU halt
  output reg                  fch_iprot_replay,

  ////////// Instruction Issue Interface /////////////////////////////////////
  //
  input                       al_pass,
  input  [`npuarc_DATA_RANGE]        al_inst,
  input  [`npuarc_DATA_RANGE]        al_limm,
  input                       al_exception,
  input  [`npuarc_FCH_EXCPN_RANGE]   al_excpn_type,
  input [`npuarc_FCH_EINFO_RANGE]    al_excpn_info,
  input                       al_iprot_viol,
  input                       al_is_predicted,
  input                       al_prediction,
  input  [`npuarc_PC_RANGE]          al_predicted_bta,
  input  [`npuarc_BR_TYPE_RANGE]     al_prediction_type,
  input                       al_error_branch,
  input  [`npuarc_BR_INFO_RANGE]     al_branch_info,
  input                       al_with_dslot,

  output                      da_holdup,

  output                      zol_depend_stall,



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
  output                      wa_restart_kill_r,
  output                      wa_aux_pc_wen,        // To Halt Manager (Debug PC write)
  output                      ca_finish_sgl_step,

  // MPU interface for IFU
  input  [`npuarc_PC_RGN_RANGE]      ifetch_addr_mpu, // fetch address from IFU
  output                      ifetch_viol,     // execute permission violation

  input [1:0]                 dc4_dtlb_miss_r,
  input [`npuarc_ADDR_RANGE]         dmp_dc3_dtlb_efa,
  input                       dc3_dtlb_miss_excpn_r,
  input                       dc3_dtlb_ovrlp_excpn_r,
  input                       dc3_dtlb_protv_excpn_r,
  input                       dc3_dtlb_ecc_excpn_r,
  output                      wa_jtlb_lookup_start_r,
  output                      wa_jtlb_cancel,

  input                       al_ifu_err_nxtpg,

  output                      ca_tlb_miss_excpn,
  output [`npuarc_PD0_VPN_RANGE]     ca_tlb_miss_efa,
  output                      ca_m_chk_excpn,
  input                       mmu_en_r,
  output                      mpu_en_r,
  input                       x2_da0_transl,

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
  ////////// DMP pending post-commit mem operations //////////////////////////
  //
  input                       dmp_wr_pending_r,     // DMP pending wr op
  input                       dmp_aux_pending_r,    // DMP pending cache instr

  ////////// Outputs for PCT /////////////////////////////////////////////////
  //
  output                      do_aux_replay_r, 


  // X1
  input                       dc1_stall,            // 
  output                      x1_valid_r,           //
  output                      x1_pass,              //
  output                      x1_load_r,            //
  output                      x1_store_r,           //
  output                      x1_pref_r,            //
  output                      x1_cache_byp_r,       //
  output [1:0]                x1_size_r,            //
  output [`npuarc_ADDR_RANGE]        x1_mem_addr0,         //
  output [`npuarc_ADDR_RANGE]        x1_mem_addr1,         //
  output [`npuarc_ADDR_RANGE]        x1_addr_base,         //
  output [`npuarc_ADDR_RANGE]        x1_addr_offset,       //
  output [1:0]                x1_bank_sel_lo,       //
  output [1:0]                x1_bank_sel_hi,       //  
  output                      x1_uop_inst_r,        // X1 is a multi-op insn.
  // X2
  input                       dc2_stall,            //
  input                       dc2_addr_pass,        //
  input  [`npuarc_ADDR_RANGE]        dc2_aux_addr,         //
  output                      x2_valid_r,           //
  output                      x2_pass,              //
  output                      x2_enable,            //
  output                      x2_load_r,            //
  output                      x2_store_r,           //
  output                      x2_locked_r,          //
  output                      x2_pref_r,            //
  output [1:0]                x2_size_r,            //
  output                      x2_cache_byp_r,       //
  output [`npuarc_ADDR_RANGE]        x2_mem_addr_r,        //
  output                      x2_uop_inst_r,        // X2 is a multi-op insn.
  output                      x2_exu_stall,         // 
  output                      x2_mpu_data_flt,      // 
  input                       dmp_dc3_stall_r, 
  // X3
  input                       dmp_dc3_fast_byp,     //
  output                      x3_valid_r,           //
  output                      x3_pass,              //
  output                      x3_enable,            //
  output                      x3_load_r,            //
  output                      x3_store_r,           //
  output                      x3_locked_r,          //
  output                      x3_pref,              // PREFETCH into L1
  output                      x3_pref_l2,           // PREFETCH into L2
  output                      x3_prefw,             // PREFETCHW
  output                      x3_pre_alloc,         // PREALLOC
    
  output [1:0]                x3_size_r,            //
  output                      x3_sex_r,             //
  output                      x3_cache_byp_r,       //
  output [`npuarc_ADDR_RANGE]        x3_mem_addr_r,        //
  output                      x3_uop_inst_r,        // X3 is a multi-op insn.
  output                      x3_sync_op_r,         // X3 is a SYNC insn.
  output                      x3_brk_op_r,          // X3 is a brk insn.
  input                       dc3_excpn,            // DMP precise memory err exc
  input  [`npuarc_DMP_EXCPN_RANGE]   dc3_excpn_type,       // exception type
  input  [7:0]                dc3_excpn_code,       // cause code
  // CA
  input                       dmp_dc4_stall,        //
  input                       dmp_dc4_fast_byp_r,   //
  input                       dmp_dc4_fast_miss_r,  //
  input  [`npuarc_DATA_RANGE]        dmp_dc4_fast_data,    //
  input  [`npuarc_DATA_RANGE]        dmp_dc4_rf_wdata_lo,  //
  input                       dc4_waw_replay_r,     //
  output                      ca_valid_r,           //
  output                      ca_pass,              //
  output                      ca_enable,            //
  output                      ca_pass_eslot,        // commit return from EI
  output [`npuarc_PC_RANGE]          ca_pc_jump,           // for smart
  output [`npuarc_PC_RANGE]          aux_eret_addr,        // for smart
  output                      wa_enable,            //
  output                      ca_load_r /* verilator public_flat */,            //
//  output                      ca_pref_r,            //
  output                      ca_grad_req,          //
  output                      ca_store_r,           //
  output                      ca_uop_inst_r,        //
  output [1:0]                ca_size_r,            //
  output                      ca_sex_r,             //
  output                      ca_cache_byp_r,       //
  output                      ca_pref,              // PREFETCH into L1
  output                      ca_pref_l2,           // PREFETCH into L2
  output                      ca_prefw,             // PREFETCHW
  output                      ca_pre_alloc,         // PREALLOC
  output [`npuarc_ADDR_RANGE]        ca_mem_addr_r,        //
  input [`npuarc_PADDR_RANGE]        ca_phys_addr_r,       //
  output [`npuarc_DATA_RANGE]        dc4_write_data_lo,    //
  input  [`npuarc_DATA_RANGE]        dmp_dc4_rf_wdata_hi,  //
  output [`npuarc_DATA_RANGE]        dc4_write_data_hi,    //
  input                       dmp_idle_r,           // DMP is inactive
  // AR
  output                      ar_tags_empty_r,      //
  output reg                  ca_uop_active,        //

  ////////// DMP Exception and Replay Interface //////////////////////////////
  //
  input                       dc4_replay,           // replay the instr at DC4
  input                       dc4_excpn,            // DMP is raising an excpn
  input [`npuarc_PADDR_RANGE]        dc4_excpn_mem_addr,   // address of the faulting 
                                                    //  inst, may be imprecise    
  input [`npuarc_DMP_EXCPN_RANGE]    dc4_excpn_type,       // exception type
  input                       dc4_excpn_user_mode_r,// DMP excpn privilege

  ////////// Bus error exception acknowledgement /////////////////////////////
  //
  output                      mem_excpn_ack_r,      // bus error excpn ack

  ////////// DMP Graduation and Retirement Interface /////////////////////////
  //
  input                       dc4_grad_req,         // DMP grad. request
  input                       dmp_retire_req /* verilator public_flat */,       // DMP retirement req.
  input  [`npuarc_GRAD_TAG_RANGE]    dmp_retire_tag,       // DMP tag of retirer
  input                       dmp_scond_zflag,      // DMP SCOND status
  input                       dmp_clear_lf,         // DMP detects write to LPA
  output                      wa_lock_flag_r,       // LF register to DMP
  output                      wa_lock_double_r,     // LF size to DMP
  output [`npuarc_PADDR_RANGE]       wa_lpa_r,             // LPA register to DMP
  output                      ca_locked_r,          // LLOCK or SCOND indicator
  output                      dmp_retire_ack,       // DMP retirement ack
  input                        rtt_dc4_scond_go,  // scond will be success
  output    [`npuarc_ADDR_RANGE]     dmp_retire_ld_addr,   // DMP VA of retiring LD

  ////////// Common Graduation and Retirement Interface //////////////////////
  //
  output                      ca_grad_ack,          // CA inst graduates
  output [`npuarc_GRAD_TAG_RANGE]    ca_grad_tag,          // graduating inst tag

  ////////// Aux. Interfaces /////////////////////////////////////////////////
  //
  output                      x3_lr_op_r,           // aux_read
  output                      x3_sr_op_r,           // aux_write
  output  [`npuarc_DATA_RANGE]       wa_sr_data_r,         // aux write data



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
  output                      aux_dper_waddr_r,     //  (X3) Aux Reg Addr
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
  input                       dc_aux_strict_sr,     //  (X3) SR single flush
  input                       dc_aux_busy,          // Structural hazard

  // leda NTL_CON37 off
  // LMD: non driving port range
  // LJ:  standard aux interface
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

  output                      aux_bpu_ren_r,       //  (X3) Aux     Enable
  output      [3:0]           aux_bpu_raddr_r,     //  (X3) Aux Address
  output                      aux_bpu_wen_r,       //  (WA) Aux     Enable
  output      [3:0]           aux_bpu_waddr_r,     //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   bpu_aux_rdata,       //  (X3) LR read data
  input                       bpu_aux_illegal,     //  (X3) SR/LR illegal
  input                       bpu_aux_k_rd,        //  (X3) need Kernel Read
  input                       bpu_aux_k_wr,        //  (X3) need Kernel Write
  input                       bpu_aux_unimpl,      //  (X3) Invalid    
  input                       bpu_aux_serial_sr,   //  (X3) SR group flush pipe
  input                       bpu_aux_strict_sr,   //  (X3) SR flush pipe


  output [`npuarc_INTEVT_RANGE]      int_evts,

  input [21:0]                      intvbase_in, // for external interrupt vector base configuring


  ////////// Auxiliary interface for (SMT) SR/LR instructions ////////////
  //
  output                      aux_smt_active,       //  RTT smart is active
  output                      aux_smt_ren_r,        //  (X3) Aux     Enable
  output                      aux_smt_raddr_r,      //  (X3) Aux Address
  output                      aux_smt_wen_r,        //  (WA) Aux     Enable
  output                      aux_smt_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   smt_aux_rdata,        //  (X3) LR read data
  input                       smt_aux_illegal,      //  (X3) SR/LR illegal
  input                       smt_aux_k_rd,         //  (X3) need Kernel Read
  input                       smt_aux_k_wr,         //  (X3) need Kernel Write
  input                       smt_aux_unimpl,       //  (X3) Invalid    
  input                       smt_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       smt_aux_strict_sr,    //  (X3) SR flush pipe
  //
  output                      ca_br_evt,
  input                       smt_cap_rst_vec,      // SmaRT needs capture
  output [`npuarc_PC_RANGE]          ar_pc_save_r,         // Saved AR PC

  input                       ar_save_clk,
  output                      ar_save_en_r,


  output      [`npuarc_PC_RANGE]     ar_pc_r /* verilator public_flat */,
  output      [`npuarc_DATA_RANGE]   ar_aux_lp_end_r,      // LP_END aux register
  output                      ca_trap_op_r,
  output      [`npuarc_INTEVT_RANGE] excpn_evts,


  output      [`npuarc_PC_RANGE]     ar_pc_nxt,
  output      [`npuarc_PFLAG_RANGE]  wa_aux_status32_nxt,
  output                      ca_zol_lp_jmp,        // late ZOL loop-back
  output                      excpn_exit_evt,

  ////////// Auxiliary interface for (SMT) SR/LR instructions ////////////
  //
  output                      aux_rtt_active,       // enable RTT interf clk
  output                      aux_rtt_ren_r,        //  (X3) Aux     Enable
  output      [3:0]           aux_rtt_raddr_r,      //  (X3) Aux Address
  output                      aux_rtt_wen_r,        //  (WA) Aux     Enable
  output      [3:0]           aux_rtt_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   rtt_aux_rdata,        //  (X3) LR read data
  input                       rtt_aux_illegal,      //  (X3) SR/LR illegal
  input                       rtt_aux_k_rd,         //  (X3) need Kernel Read
  input                       rtt_aux_k_wr,         //  (X3) need Kernel Write
  input                       rtt_aux_unimpl,       //  (X3) Invalid
  input                       rtt_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       rtt_aux_strict_sr,    //  (X3) SR flush pipe

  output                      ca_cond_inst,
  output                      ca_cond_met,
  output                      ca_br_or_jmp_all,
  output                      ca_indir_br,
  output                      ca_in_deslot,
  output                      ca_in_eslot_r,
  output                      rtt_leave_uop_cmt,    //ca stage is at leave uop inst.
  output                      ca_cmt_brk_inst,    // Commit Break inst
  output                      dbg_halt_r,

  output                      aps_halt,    // Halt due to AP match
  output                      aps_break,   // Break due to AP match
  output    [`npuarc_APNUM_RANGE]    aps_active,  // Identity of active hit
  output    [`npuarc_APS_RANGE]      aps_status,  // All triggered Actionpoints
  output                      aps_excpn,   // Excpn due to AP match


  output                      ap_tkn,


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
  output                      aux_timer_active,     // timer SR is active 
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
  input                       aux_wr_allow,         //  CCAux new write allowed
  output                      aux_cm_phase,         //  CCAux in commit phase
  output                      aux_cm_valid,         //  CCAux commit is valid


  output                      aux_irq_ren_r,        //  (X3) Aux     Enable
  output      [11:0]          aux_irq_raddr_r,      //  (X3) Aux Address
  output                      aux_irq_wen_r,        //  (WA) Aux     Enable
  output      [11:0]          aux_irq_waddr_r,      //  (WA) Aux Address
  input       [`npuarc_DATA_RANGE]   irq_aux_rdata,        //  (X3) LR read data
  input                       irq_aux_illegal,      //  (X3) SR/LR illegal
  input                       irq_aux_k_rd,         //  (X3) needs Kernel Read
  input                       irq_aux_k_wr,         //  (X3) needs Kernel W perm
  input                       irq_aux_unimpl,       //  (X3) Invalid    
  input                       irq_aux_serial_sr,    //  (X3) SR group flush pipe
  input                       irq_aux_strict_sr,    //  (X3) SR flush pipe

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

  output                      rtc_na,               //  RTC non-atomic (Commit Unit)
  output                      aux_pct_active,       // 
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
  output                      commit_normal_evt,
  output                      ca_dslot_r       ,
  output                      da_eslot_stall      ,
  output                      da_uop_stall        ,
  output                      x1_dslot_stall      ,
  output                      sa_flag_stall       , // 
  output                      sa_stall_r15        ,
  output                      sa_stall_r1         , // 
  output                      sa_acc_raw   ,    // 
  output                      ca_acc_waw   ,    // 
  output                      dep_bdcmstall , 
  output                      sync_dsync_dmb_stall , 

  output                      ca_lp_lpcc_evt,          //
  output                      ca_br_taken         , //
  output                      ca_jump_r,            // Insn. is Jump
  output                      ca_bcc_r,            // 
  output                      ca_brcc_bbit_r,      // 
  output                      ca_zol_branch,
  output                      ca_has_limm_r,        // (CA) Insn. has limm
  output                      ca_is_16bit_r,        // (CA) Insn. is 16 bit
  output                      ca_br_jmp_op,         // Insn. is BL, BLcc, BL_S, JL, JL_S, JLcc
  output     [4:0]            ca_q_field_r,         //
  output                      ca_byte_size_r,       //
  output                      ca_hit_lp_end,        // SA insn is at loop-end
  output                      ca_lr_op_r,           // Insn. is LR
  output                      ca_sr_op_r,           // Insn. is SR

  output     [`npuarc_DATA_RANGE]    ar_aux_lp_start_r,    // LP_START aux register


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


  input                       wdt_x3_stall,
  output                      x3_kill,
  ////////// Machine Architectural state /////////////////////////////////////
  //
  output  [`npuarc_DATA_RANGE]       ar_aux_status32_r /* verilator public_flat */,    //
  output  [`npuarc_DATA_RANGE]       ar_aux_debug_r,       // AUX DEBUG
  output                      dbg_we_r,             // Waiting for event
  output                      dbg_wf_r,             // Waiting for LF to clear
  output    [`npuarc_DATA_RANGE]     ar_aux_ecc_ctrl_r,    // ECC 

  input     [15:0]            ecc_flt_status,       // ECC 
  input   [`npuarc_DATA_RANGE]       ecc_sbe_count_r,
  output    [7:0]             ecc_sbe_clr,
  output                      ecc_sbe_dmp_clr,
  

  ////////// Interrupt/Exception Interface ///////////////////////////////////
  //
  input                       irq_req,              //
  input  [7:0]                irq_num,              //
  input   [`npuarc_IRQLGN_RANGE]     irq_w,                //
  input                       irq_preempts,         //
  output  [`npuarc_IRQLGN_RANGE]     irq_ack_w_r,          //

  output  [`npuarc_IRQN_RANGE]       cpu_accept_irq,       //
  output                      cpu_irq_select,       //
  output                      irq_ack,              //
  output  [7:0]               irq_ack_num,          //

  input     [`npuarc_DATA_RANGE]     ar_aux_icause0_r,  // from alb_irq_unit
  input     [`npuarc_DATA_RANGE]     ar_aux_icause1_r,  // from alb_irq_unit
  input     [`npuarc_DATA_RANGE]     ar_aux_icause2_r,  // from alb_irq_unit
  output    [`npuarc_DATA_RANGE]     ar_aux_irq_act_r /* verilator public_flat */,     // to alb_irq_unit


  ////////// Global State retained by EXU ////////////////////////////////////
  //
  output                      gb_sys_reset_done_r,  // Machine has left reset

  ////////// Unit-level clock gating control outputs to clock_ctrl ///////////
  //
  output                      mpy_unit_enable,      // clk ctrl for multiplier
  input                       mpy_unit_clk,         // clk clk  for multiplier
  output                      div_unit_enable,      // clk ctrl for divider
  input                       div_unit_clk,         // clk clk  for divider
  output                      ap_unit_enable,
  input                       ap_unit_clk,
  output                      aux_aps_active,       //
  input                       ap_aux_clk,           // clk for AP Aux
  ////////// Halt Interface //////////////////////////////////////////////////
  //
  input                       hlt_do_halt,          //
  input                       hlt_do_unhalt,        //
  input                       pipe_block_ints,      //
  output                      int_preempt,          //





  output                      excpn_restart,        //
  output                      ct_replay,            // Aux Replay
  output                      excpn_hld_halt,       // 
  input                       hlt_stop,             // Halt reqst. IFU stop
  input                       hlt_issue_reset,      // Halt issues reset
  input                       hlt_restart           // Halt logic reqs. flush
);

`ifdef npuarc_RTL_PIPEMON  // {
`ifdef SYNTHESIS // {
`undef npuarc_RTL_PIPEMON
`endif // }
`endif // }


wire                        holdup_excpn_nxt;
wire                        ca_uop_active_set;
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Decode stage                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire                        al_uop_snoops_pred;
wire                        al_uop_is_predicted;
wire                        al_uop_prediction;
wire [`npuarc_BR_TYPE_RANGE]       al_uop_prediction_type;
wire [`npuarc_BR_INFO_RANGE]       al_uop_branch_info;
wire                        al_uop_with_dslot;
wire                        al_uop_has_limm;
wire                        da_rtie_op_r;
wire                        da_pass;
wire                        al_uop_pass;
wire                        da_dslot;
wire                        al_uop_epil;
wire                        da_ei_op;
wire                        da_ldi_src0;
wire                        da_jli_src0;
wire                        da_uop_u7_pcl;
wire [`npuarc_ZNCV_RANGE]          da_zncv_wen;

wire                        da_uop_prol_r;
wire                        da_uop_busy_r;
wire                        da_uop_is_excpn_r;
wire                        da_uop_is_sirq_r;
//wire                        da_uop_is_gpr_r;

wire [`npuarc_PC_RANGE]            sa_pc_nxt;
wire [`npuarc_DATA_RANGE]          sa_limm_nxt;
wire [`npuarc_SA_CODE_WIDTH-1:0]   sa_code_nxt;
wire [`npuarc_PC_RANGE]            sa_seq_pc_nxt;
wire                        sa_is_pc_nxt;
wire [`npuarc_RGF_ADDR_RANGE]      da_rf_ra0_r;
wire [`npuarc_RGF_ADDR_RANGE]      da_rf_ra1_r;
wire                        da_rf_renb0_64_r;
wire                        da_rf_renb0_r;
wire                        da_rf_renb1_64_r;
wire                        da_rf_wenb0_64;
wire                        da_rf_wenb1_64;
wire                        da_rf_renb1_r;
wire [`npuarc_BR_TYPE_RANGE]       da_prediction_type_r;
wire                        da_iprot_viol_r;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Operand stage                                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire                        sa_valid_nxt;
wire                        sa_opds_in_sa_r;
wire                        sa_agu_uses_r0_r;
wire                        sa_agu_uses_r1_r;
wire                        sa_dslot_r;
wire [`npuarc_PC_RANGE]            sa_seq_pc_r;
wire [`npuarc_PC_RANGE]            sa_restart_pc;
wire [`npuarc_PC_RANGE]            sa_pc;
wire                        sa_ei_op_r;
wire                        sa_leave_op_r;
wire                        sa_sr_op_r;
wire                        sa_lr_op_r;
wire                        sa_uop_predictable_r;
wire                        sa_ldi_src0_r;
wire                        sa_jli_src0_r;
wire [`npuarc_ZNCV_RANGE]          sa_zncv_wen_r;
wire [4:0]                  sa_q_field_r;
wire                        sa_with_carry_r;
wire                        sa_uop_inst_r;
wire                        sa_rf_renb0_r;
wire                        sa_rf_renb0_64_r;
wire [`npuarc_RGF_ADDR_RANGE]      sa_rf_wa0_r;
wire                        sa_rf_wenb0_r;
wire                        sa_rf_wenb0_64_r;
wire                        sa_rf_renb1_r;
wire                        sa_rf_renb1_64_r;
wire [`npuarc_RGF_ADDR_RANGE]      sa_rf_wa1_r;
wire                        sa_rf_wenb1_r;
wire                        sa_rf_wenb1_64_r;
wire                        sa_reads_acc_r;
wire [`npuarc_RGF_ADDR_RANGE]      sa_rf_ra0_r;
wire [`npuarc_RGF_ADDR_RANGE]      sa_rf_ra1_r;

wire                        sa_pass;

wire [`npuarc_DATA_RANGE]          x1_src0_nxt;
wire [`npuarc_DATA_RANGE]          x1_src1_nxt;
wire [`npuarc_DATA_RANGE]          x1_src2_nxt;
wire [`npuarc_DATA_RANGE]          x1_src3_nxt;
wire                        sa_src0_pass;
wire                        sa_src1_pass;
wire                        sa_src2_pass;
wire                        sa_src3_pass;
wire [`npuarc_BR_TYPE_RANGE]       sa_br_type;
wire                        sa_secondary;
wire [`npuarc_ISIZE_RANGE]         sa_commit_size;
wire                        sa_iprot_viol_r;
wire [`npuarc_X1_CODE_WIDTH-1:0]   x1_code_nxt;
wire [`npuarc_BR_TYPE_RANGE]       sa_prediction_type_r;
wire                        sa_wa0_lpc_r;
wire                        sa_mpy_op_r;
wire                        sa_vector_op_r;
wire                        sa_half_size_r;
wire                        sa_dual_op_r;
wire                        sa_div_op_r; 

wire                        sa_link_r;
wire                        sa_branch_or_jump;
wire                        sa_multi_op_r;
wire  [2:0]                 sa_dmb_type_r;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Exec1 stage                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire                        x1_valid_nxt;
wire                        x1_fast_op_r;
wire                        x1_slow_op_r;
wire                        x1_opds_in_sa_r;
wire                        x1_opds_in_x1_r;
wire                        x1_agu_uses_r0_r;
wire [`npuarc_DATA_RANGE]          x1_byp_data0;
wire [`npuarc_DATA_RANGE]          x2_src0_nxt;
wire [`npuarc_DATA_RANGE]          x2_src1_nxt;
wire [`npuarc_PC_RANGE]            x2_target_nxt;
wire [`npuarc_PC_RANGE]            x1_link_addr;
wire                        x1_res_pass;
wire                        x1_src0_pass;
wire                        x1_src1_pass;
wire                        x1_addr_pass;
wire [`npuarc_ZNCV_RANGE]          x2_zncv_nxt;
wire [`npuarc_X2_CODE_WIDTH-1:0]   x2_code_nxt;
wire                        x2_lt_flag_nxt;

wire [`npuarc_PC_RANGE]            x1_br_target;
wire [`npuarc_PC_RANGE]            x1_br_fall_thru;
wire                        x1_br_direction;
wire                        x1_br_taken;
wire                        x1_bi_bta_mpd;

wire [`npuarc_RGF_ADDR_RANGE]      x1_rf_wa0_r;
wire                        x1_rf_wenb0_r;
wire                        x1_rf_wenb0_64_r;
wire [`npuarc_RGF_ADDR_RANGE]      x1_rf_wa1_r;
wire                        x1_rf_wenb1_r;
wire                        x1_rf_wenb1_64_r;
wire [`npuarc_RGF_ADDR_RANGE]      x1_rf_ra0_r;
wire [`npuarc_RGF_ADDR_RANGE]      x1_rf_ra1_r;
wire                        x1_rf_renb0_64_r;
wire                        x1_rf_renb1_64_r;

wire [`npuarc_ZNCV_RANGE]          x1_zncv_wen_r;
wire                        x1_flag_op_r;
wire                        x1_brk_op_r;
wire                        x1_sleep_op_r;
wire                        x1_cond;
wire [4:0]                  x1_q_field_r;
wire                        x1_signed_op_r;
wire                        x1_dslot_r;
wire                        x1_sr_op_r;
wire                        x1_uop_commit_r;
wire                        x1_uop_prol_r;
wire                        x1_uop_epil_r;
wire                        x1_with_carry_r;
wire                        x1_grab_src0;
wire                        x1_grab_src1;
wire                        x1_grab_src2;
wire                        x1_grab_src3;
wire                        x1_rgf_link_r;
wire                        x1_ei_op_r;
wire                        x1_btab_op_r;
wire                        x1_wa0_lpc_r;
wire                        x1_loop_op_r;

wire                        x1_mpy_op_r;
wire                        x1_half_size_r;
wire                        x1_dual_op_r;
wire                        x1_vector_op_r;
wire                        x1_quad_op_r;
wire [`npuarc_DATA_RANGE]          mp1_src0_nxt;
wire [`npuarc_DATA_RANGE]          mp1_src1_nxt;
wire [`npuarc_DATA_RANGE]          mp1_src2_nxt;
wire [`npuarc_DATA_RANGE]          mp1_src3_nxt;
wire                        x1_div_op_r;
wire                        x1_div_kind_r;
wire                        x2_predicate_nxt; // X1 evaluated condition
wire                        x1_iprot_viol_r;
wire                        x1_acc_wenb_r;
wire                        x1_dmb_op_r;
wire  [2:0]                 x1_dmb_type_r;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Exec2 stage                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire                        x2_valid_nxt;
wire     [4:0]              x2_q_field_r;
wire                        x2_dslot_r;
wire                        x2_slow_op_r;
wire [`npuarc_ZNCV_RANGE]          x2_zncv_r;
wire [`npuarc_ZNCV_RANGE]          x2_zncv_wen_r;
wire                        x2_wevt_op;  
wire                        x2_flag_op_r;
wire                        x2_signed_op_r;
wire                        x2_sync_op_r;
wire [`npuarc_DATA_RANGE]          x2_byp_data0;
wire [`npuarc_RGF_ADDR_RANGE]      x2_rf_wa0_r;
wire                        x2_rf_wenb0_r;
wire                        x2_rf_wenb0_64_r;
wire [`npuarc_RGF_ADDR_RANGE]      x2_rf_wa1_r;
wire                        x2_rf_wenb1_r;
wire                        x2_rf_wenb1_64_r;
wire [`npuarc_RGF_ADDR_RANGE]      x2_rf_ra0_r;
wire [`npuarc_RGF_ADDR_RANGE]      x2_rf_ra1_r;
wire                        x2_rf_renb0_64_r;
wire                        x2_rf_renb1_64_r;
wire  [`npuarc_DATA_RANGE]         x2_aux_addr_r;
wire                        x2_lr_op_r;
wire                        x2_sr_op_r;

wire                        x2_in_eslot_r;
wire                        x2_ei_op_r;

wire                        x2_invalid_instr_r;
wire                        x2_illegal_operand_r;
wire                        x2_jump_r;
wire                        x2_has_limm_r;
wire                        x2_rtie_op_r;
wire                        x2_rel_branch_r;

wire                        x2_leave_op_r;



wire [`npuarc_DATA_RANGE]          x3_src0_nxt;
wire [`npuarc_DATA_RANGE]          x3_src1_nxt;
wire [`npuarc_DATA_RANGE]          x3_res_nxt;
wire                        x2_src0_pass;
wire                        x2_src1_pass;
wire                        x2_res_pass;
wire                        x2_addr_pass;
wire [`npuarc_X3_CODE_WIDTH-1:0]   x3_code_nxt;
wire [`npuarc_PC_RANGE]            x3_target_nxt;
wire [`npuarc_ZNCV_RANGE]          x3_zncv_nxt;
wire                        x2_wa0_lpc_r;
wire                        x2_loop_op_r;

wire                        x2_kernel_op_r;
wire                        x2_rgf_link_r;
wire                        x2_brk_op_r;
wire                        x2_multi_op_r;
wire                        x2_btab_op_r;
wire                        x2_mpy_op_r;
wire                        x2_half_size_r;
wire                        x2_dual_op_r;
wire                        x2_vector_op_r;
wire                        x2_quad_op_r;
wire                        x2_div_op_r;
wire                        x2_acc_wenb_r;
wire                        x2_rf_renb0_r; 
wire                        x2_rf_renb1_r;
wire                        x2_sc_stall;
wire                        dp_x2_sp_r;
//`if (`HAS_MPU == 1) // {
//wire [`ADDR_RANGE]          x2_mem_addr1_r;
//`endif                // }
wire                        x2_dmb_op_r;
wire  [2:0]                 x2_dmb_type_r;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Exec3 stage                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
wire                        x3_valid_nxt;
wire     [4:0]              x3_q_field_r;
wire [`npuarc_ZNCV_RANGE]          x3_zncv_wen_r;
wire                        x3_wevt_op;
wire [`npuarc_DATA_RANGE]          x3_byp_data0;
wire [`npuarc_DATA_RANGE]          x3_src0_r;
wire [`npuarc_RGF_ADDR_RANGE]      x3_rf_wa0_r;
wire                        x3_rf_wenb0_r;
wire                        x3_rf_wenb0_64_r;
wire [`npuarc_RGF_ADDR_RANGE]      x3_rf_wa1_r;
wire                        x3_rf_wenb1_r;
wire                        x3_rf_wenb1_64_r;
wire [`npuarc_RGF_ADDR_RANGE]      x3_rf_ra0_r;
wire [`npuarc_RGF_ADDR_RANGE]      x3_rf_ra1_r;
wire                        x3_rf_renb0_64_r;
wire                        x3_rf_renb1_64_r;
wire                        x3_ei_op_r;

wire                        x3_flag_op_r;
wire                        x3_signed_op_r;
wire                        x3_wa0_lpc_r;
wire                        x3_loop_op_r;
wire                        ca_flag_wr_nxt;
wire [`npuarc_DATA_RANGE]          ca_src0_nxt;
wire [`npuarc_DATA_RANGE]          ca_src1_nxt;
wire [`npuarc_DATA_RANGE]          ca_res_nxt;
wire                        x3_src0_pass;
wire                        x3_src1_pass;
wire                        x3_res_pass;
wire                        x3_target_pass;
wire                        x3_addr_pass;
wire                        x3_add_op_pass;
wire                        x3_alu_code_pass;
wire                        x3_mask_src_pass;
wire [`npuarc_PC_INC_RANGE]        ca_pc_inc_nxt;
wire [`npuarc_ZNCV_RANGE]          ca_zncv_nxt;
wire [`npuarc_CA_CODE_WIDTH-1:0]   ca_code_nxt;
wire [`npuarc_CA_P0_RANGE]         ca_p0_nxt;
wire [`npuarc_CA_P1_RANGE]         ca_p1_nxt;
wire [`npuarc_CA_P2_RANGE]         ca_p2_nxt;
wire [`npuarc_CA_P3_RANGE]         ca_p3_nxt;
wire                        ca_cin_nxt;
wire [`npuarc_PC_RANGE]            ca_target_nxt;
wire                        x3_rtie_op_r;
wire                        x3_trap_op_r;

wire                        x3_mpy_op_r;
wire                        x3_half_size_r;
wire                        x3_acc_op_r;
wire                        x3_dual_op_r;
wire                        x3_vector_op_r;
wire                        x3_macu_r;
wire                        x3_quad_op_r;
wire                        x3_acc_wenb_r;
wire                        x3_div_op_r;
wire                        x3_iprot_viol_r;
wire                        x3_dmb_op_r;
wire  [2:0]                 x3_dmb_type_r;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not used in all configs
wire                        x3_pref_r;
// leda NTL_CON13A on
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the DMP block                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire                        dc4_q_replay;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Commit stage                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
wire                        ca_valid_nxt;
wire                        ca_with_carry_r;
wire                        ca_wa1_conflict;
wire                        ca_div_op_r;
wire                        div_retire_ack;
wire                        ca_retire_req;
wire [`npuarc_GRAD_TAG_RANGE]      ca_retire_tag;
wire                        ca_retire_ack;
wire [`npuarc_ZNCV_RANGE]          ca_retire_flags;
wire [`npuarc_GRAD_ADDR_RANGE]     ca_grad_rf_wa1;
wire [`npuarc_PC_RANGE]            ca_target_r;

wire [`npuarc_DATA_RANGE]          ca_src0_r;
wire [`npuarc_DATA_RANGE]          ca_src1_r;
//`if (`EXEC2_START == 1)
wire [`npuarc_DATA_RANGE]          ca_byp_data0_lo;
wire [`npuarc_DATA_RANGE]          ca_byp_data1_lo;
wire [`npuarc_DATA_RANGE]          ca_byp_data0_hi;
//`endif
wire [`npuarc_DATA_RANGE]          ca_byp_data1_hi;
wire                        ca_fast_op_r;
wire                        ca_rtie_op_r;
wire                        ca_ei_op_r;
wire                        cmt_ei_evt;
wire                        ca_btab_op_r;

wire                        ca_loop_op_r;
wire                        ca_aux_cond;
wire                        ca_brk_op_r;
//wire                        ca_sync_op_r;
 wire                        ca_enter_op_r;
wire                        ca_uop_predictable_r;
wire                        ca_uop_enter_r;
wire                        ca_uop_inprol_r;
wire                        ca_uop_commit_r;
wire                        ca_cond;
wire                        ca_predicate_r;
wire                        ca_mpy_op_r;
wire                        ca_vector_op_r;
wire                        ca_macu_r;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not used in some configs
wire                        ca_q_cond;
// leda NTL_CON13A on

wire                        sa_dest_cr_is_ext;
wire                        x1_dest_cr_is_ext;
wire                        x2_dest_cr_is_ext; 
wire                        x3_dest_cr_is_ext; 
wire                        ca_dest_cr_is_ext; 
wire                        gb_dest_cr_is_ext;
wire                        has_dest_cr_is_ext;
wire                        ar0_rf_valid_r;
wire                        ar0_rf_wenb1_r;
wire [`npuarc_GRAD_ADDR_RANGE]     ar0_rf_wa1_r;  
wire                        ar0_rf_wenb1_64_r;
wire                        ar0_dest_cr_is_ext;  
wire                        ar1_rf_valid_r;
wire                        ar1_rf_wenb1_r;
wire [`npuarc_GRAD_ADDR_RANGE]     ar1_rf_wa1_r;  
wire                        ar1_rf_wenb1_64_r;
wire                        ar1_dest_cr_is_ext;  
wire                        ar2_rf_valid_r;
wire                        ar2_rf_wenb1_r;
wire [`npuarc_GRAD_ADDR_RANGE]     ar2_rf_wa1_r;  
wire                        ar2_rf_wenb1_64_r;
wire                        ar2_dest_cr_is_ext;  
wire                        ar3_rf_valid_r;
wire                        ar3_rf_wenb1_r;
wire [`npuarc_GRAD_ADDR_RANGE]     ar3_rf_wa1_r;  
wire                        ar3_rf_wenb1_64_r;
wire                        ar3_dest_cr_is_ext;  
wire                        ar4_rf_valid_r;
wire                        ar4_rf_wenb1_r;
wire [`npuarc_GRAD_ADDR_RANGE]     ar4_rf_wa1_r;  
wire                        ar4_rf_wenb1_64_r;
wire                        ar4_dest_cr_is_ext;  
wire                        ar5_rf_valid_r;
wire                        ar5_rf_wenb1_r;
wire [`npuarc_GRAD_ADDR_RANGE]     ar5_rf_wa1_r;  
wire                        ar5_rf_wenb1_64_r;
wire                        ar5_dest_cr_is_ext;  
wire                        ar6_rf_valid_r;
wire                        ar6_rf_wenb1_r;
wire [`npuarc_GRAD_ADDR_RANGE]     ar6_rf_wa1_r;  
wire                        ar6_rf_wenb1_64_r;
wire                        ar6_dest_cr_is_ext;  
wire                        ar7_rf_valid_r;
wire                        ar7_rf_wenb1_r;
wire [`npuarc_GRAD_ADDR_RANGE]     ar7_rf_wa1_r;  
wire                        ar7_rf_wenb1_64_r;
wire                        ar7_dest_cr_is_ext;  

wire [`npuarc_ZNCV_RANGE]          ca_zncv_wen_r;
wire [`npuarc_RGF_ADDR_RANGE]      ca_rf_wa0_r;
wire                        ca_rf_wenb0_r;
wire                        ca_wa0_lpc_r;
wire                        ca_branch_evt;
wire [`npuarc_RGF_ADDR_RANGE]      wa_rf_wa1_nxt;
wire                        wa_rf_wenb1_nxt;
wire                        wa_rf_wuop_nxt; 
wire                        wa_rf_wenb1_64_nxt;
wire [`npuarc_DATA_RANGE]          wa_rf_wdata1_hi_nxt;
wire                        ca_data1_hi_pass;
wire [`npuarc_DATA_RANGE]          wa_rf_wdata0_lo_nxt;
wire                        ca_data0_lo_pass;
wire                        ca_rf_wenb0_64_r;
wire [`npuarc_DATA_RANGE]          wa_rf_wdata0_hi_nxt;
wire                        ca_data0_hi_pass;
wire [`npuarc_RGF_ADDR_RANGE]      ca_rf_wa1_r;
wire                        ca_rf_wenb1_r;
wire [`npuarc_DATA_RANGE]          wa_rf_wdata1_lo_nxt;
wire                        ca_data1_lo_pass;
wire                        ca_rf_wenb1_64_r;
wire [`npuarc_RGF_ADDR_RANGE]      ca_rf_ra0_r;
wire [`npuarc_RGF_ADDR_RANGE]      ca_rf_ra1_r;
wire                        ca_rf_renb0_64_r;
wire                        ca_rf_renb1_64_r;
wire                        wa_rf_wenb0_64_nxt;
wire [`npuarc_PC_RANGE]            ca_br_target;
wire [`npuarc_PC_RANGE]            ca_lp_end_nxt;
wire [`npuarc_PC_RANGE]            ca_br_fall_thru;
wire                        ca_br_direction;
wire                        ca_tail_pc_3;
wire                        ca_br_or_jmp;
wire                        ca_leave_op_r;
wire                        ca_uop_inst;
wire                        ca_writes_acc_r;
wire                        ca_acc_wenb_r;


wire                        wa_cmt_norm_evt_nxt;
wire                        wa_cmt_uop_evt_nxt;
wire                        wa_cmt_flag_evt_nxt;
wire                        wa_lf_set_nxt;
wire                        wa_lf_clear_nxt;
wire                        wa_lf_double_nxt;
wire [`npuarc_PADDR_RANGE]         wa_lpa_nxt;
wire [`npuarc_WA_CODE_WIDTH-1:0]   wa_code_nxt;

wire                        ar_pc_pass;
// WA AUX wires
wire                        wa_aux_status32_pass;
wire                        wa_aux_flags_pass;


wire                        wa_uopld_jli_base;
wire                        wa_uopld_ldi_base;
wire                        wa_uopld_ei_base;
wire                        wa_uopld_lp_count;
wire                        wa_uopld_lp_start;
wire                        wa_uopld_lp_end;

wire [`npuarc_DATA_RANGE]          wa_uopld_data;



// from alb_commit to alb_aux_regs

wire                        commit_inst;          //
wire                        ca_loop_evt;          //
wire                        ca_kflag_op;          //
wire [`npuarc_PC_RANGE]            ca_seq_pc_nxt;        //
wire                        ca_aux_s32_stall;     //
wire                        ca_in_kflag;

wire [`npuarc_DATA_RANGE]          ar_aux_irq_ctrl_r;
wire                        ar_aux_irq_ctrl_upt_r;
wire                        irq_ctrl_wen;
wire                        ar_aux_user_mode_r;   //arch. user mode

wire                        ca_cmt_uop_evt;
wire                        ca_sr_stall_rtie;
wire                        ca_uop_active_r; 
wire                        ca_uop_active_nxt;
wire                        wa_aux_uop_flag_pass;
wire                        ca_wevt_evt;
wire                        ca_wlfc_evt;
wire                        ca_wlfc_op;
wire                        ca_dmb_op_r;
wire  [2:0]                 ca_dmb_type_r;
wire                         rtt_ca_scond;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Writeback stage                                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire [`npuarc_PC_RANGE]            wa_restart_pc_r;
wire                        wa_valid_nxt;
wire                        wa_store_r;
wire                        wa_sleep_r;
wire                        wa_pref_r;
wire                        wa_load_r;
wire                        wa_wa0_lpc_r;
wire                        wa_loop_op_r;



wire [`npuarc_DATA_RANGE]          ca_acch_res;
wire [`npuarc_DATA_RANGE]          byp_acc_lo;
wire [`npuarc_DATA_RANGE]          byp_acc_hi;
wire [`npuarc_DATA_RANGE]          wa_accl_nxt;
wire [`npuarc_DATA_RANGE]          wa_acch_nxt;
wire                        wa_acc_wenb;
wire                        sel_byp_acc;
wire                        wa_acc_wenb_r;
wire                        wa_writes_acc_r;
wire [`npuarc_DATA_RANGE]          accl_r;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Not all bits of bus used
wire [`npuarc_DATA_RANGE]          acch_r;
// leda NTL_CON13A on
wire                        wa_cmt_flag_evt_r;
wire                        wa_uopld_status32;
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires for hazards on 64-bit write port 0                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
wire                        x1_cc_byp_64_haz_r;
wire                        x2_cc_byp_64_haz_r;
wire                        x3_cc_byp_64_haz_r;
wire                        ca_cc_byp_64_haz_r;
wire                        wa_cc_byp_64_haz_r;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Multiplier Pipe                                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
// leda NTL_CON13A off
// LMD: non driving internal net Range
// LJ:  Multiplier pipe outputs

wire [`npuarc_DATA_RANGE]          mp3_s_lo;
wire [`npuarc_DATA_RANGE]          mp3_c_lo;
wire [`npuarc_DATA_RANGE]          mp4_s_hi_r;
wire [`npuarc_DATA_RANGE]          mp4_c_hi_r;
wire                        mp4_s_65_r;
wire                        mp4_c_65_r;
// leda NTL_CON13A on
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Divide Unit                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
wire                        div_busy_r;
wire                        div_divz_r;
wire                        div_grad_req;
wire [`npuarc_RGF_ADDR_RANGE]      div_grad_rf_wa;
wire                        div_retire_req;
wire [`npuarc_GRAD_TAG_RANGE]      div_retire_tag;
wire [`npuarc_DATA_RANGE]          div_rf_wdata_lo;
wire                        div_retire_overflow_r;
wire                        div_retire_sign_r;
wire                        div_retire_zero_r;

assign div_grad_rf_wa = ca_rf_wa0_r;



wire                        eia_grad_rf_64;
wire                        eia_exu_grad_req;
wire [`npuarc_RGF_ADDR_RANGE]      eia_grad_rf_wa;

assign eia_grad_rf_wa = ca_rf_wa0_r;
assign eia_grad_rf_64 = ca_rf_wenb0_64_r;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Dependency Pipe                                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// SA
 wire                       sa_dmb_stall;
//
wire                        fwd_x1_sa0_lo;
wire                        fwd_x2_sa0_lo;
wire                        fwd_x3_sa0_lo;
wire                        fwd_ca0_lo_sa0_lo;
wire                        fwd_ca1_lo_sa0_lo;
wire                        fwd_wa0_lo_sa0_lo;
wire                        fwd_wa1_lo_sa0_lo;
wire                        fwd_ca0_hi_sa0_lo;
wire                        fwd_wa0_hi_sa0_lo;
wire                        fwd_ca1_hi_sa0_lo;
wire                        fwd_wa1_hi_sa0_lo;
wire                        fwd_wa0_hi_sa0_hi;
wire                        fwd_wa1_hi_sa0_hi;
wire                        fwd_x1_sa1_lo;
wire                        fwd_x2_sa1_lo;
wire                        fwd_x3_sa1_lo;
wire                        fwd_ca0_lo_sa1_lo;
wire                        fwd_ca1_lo_sa1_lo;
wire                        fwd_wa0_lo_sa1_lo;
wire                        fwd_wa1_lo_sa1_lo;
wire                        fwd_ca0_hi_sa1_lo;
wire                        fwd_wa0_hi_sa1_lo;
wire                        fwd_ca1_hi_sa1_lo;
wire                        fwd_wa1_hi_sa1_lo;
wire                        fwd_wa0_hi_sa1_hi;
wire                        fwd_wa1_hi_sa1_hi;
wire                        fwd_wa0_lo_sa1_hi;
wire                        fwd_wa1_lo_sa1_hi;
wire                        fwd_wa0_lo_sa0_hi;
wire                        fwd_wa1_lo_sa0_hi;

// X1
//
wire                        fwd_x1_r0_dmp_fast;
wire                        fwd_x1_r1_dmp_fast;
wire                        fwd_x1_r0_wa_w0_lo;
wire                        fwd_x1_r1_wa_w0_lo;
wire                        fwd_x1_r0_wa_w1_lo;
wire                        fwd_x1_r1_wa_w1_lo;
wire                        fwd_x1_r0_ca_w1_hi;
wire                        fwd_x1_r1_ca_w1_hi;
wire                        fwd_x1_r0h_ca_w1_hi;
wire                        fwd_x1_r1h_ca_w1_hi;
wire                        fwd_x1_r0_wa_w1_hi;
wire                        fwd_x1_r1_wa_w1_hi;
wire                        fwd_x1_r0h_wa_w1_hi;
wire                        fwd_x1_r1h_wa_w1_hi;
wire                        fwd_x1_r1h_wa_w0_lo;
wire                        fwd_x1_r1h_wa_w1_lo;
wire                        fwd_x1_r0_x2_w0;
wire                        fwd_x1_r1_x2_w0;
wire                        fwd_x1_r0h_x2_w0;
wire                        fwd_x1_r1h_x2_w0;
wire                        fwd_x1_r0_x3_w0;
wire                        fwd_x1_r1_x3_w0;
wire                        fwd_x1_r0h_x3_w0;
wire                        fwd_x1_r1h_x3_w0;
wire                        fwd_x1_r0_ca_w0_lo;
wire                        fwd_x1_r1_ca_w0_lo;
wire                        fwd_x1_r0_ca_w1_lo;
wire                        fwd_x1_r1_ca_w1_lo;
wire                        fwd_x1_r0_ca_w0_hi;
wire                        fwd_x1_r1_ca_w0_hi;
wire                        fwd_x1_r0_wa_w0_hi;
wire                        fwd_x1_r1_wa_w0_hi;
wire                        fwd_x1_r0h_ca_w0_lo;
wire                        fwd_x1_r0h_ca_w0_hi;
wire                        fwd_x1_r1h_ca_w0_lo;
wire                        fwd_x1_r1h_ca_w0_hi;
wire                        fwd_x1_r0h_ca_w1_lo;
wire                        fwd_x1_r1h_ca_w1_lo;
wire                        fwd_x1_r0h_wa_w0_lo;
wire                        fwd_x1_r0h_wa_w0_hi;
wire                        fwd_x1_r0h_wa_w1_lo;
wire                        fwd_x1_r1h_wa_w0_hi;
wire [`npuarc_ZNCV_RANGE]          fwd_zncv_x1;
wire [`npuarc_ZNCV_RANGE]          fwd_zncv_x1_x2;
wire [`npuarc_ZNCV_RANGE]          fwd_zncv_x1_ca;
wire                        fwd_zncv_x1_ar;

// X2 bypass control signals
//
wire                        fwd_x2_r0_wa_w0_lo;
wire                        fwd_x2_r0_wa_w1_lo;
wire                        fwd_x2_r1_wa_w0_lo;
wire                        fwd_x2_r1_wa_w1_lo;
wire                        fwd_x2_r0_wa_w0_hi;
wire                        fwd_x2_r1_wa_w0_hi;
wire                        fwd_x2_r0_wa_w1_hi;
wire                        fwd_x2_r1_wa_w1_hi;
wire                        fwd_x2_r1h_wa_w0_lo;
wire                        fwd_x2_r1h_wa_w1_lo;
wire                        fwd_x2_r1h_wa_w0_hi;
wire                        fwd_x2_r1h_wa_w1_hi;

// X3 bypass control signals
//
wire                        fwd_x3_r0_ca_w0_lo;
wire                        fwd_x3_r0_ca_w1_lo;
wire                        fwd_x3_r0_wa_w0_lo;
wire                        fwd_x3_r0_wa_w1_lo;
wire                        fwd_x3_r1_ca_w0_lo;
wire                        fwd_x3_r1_ca_w1_lo;
wire                        fwd_x3_r1_wa_w0_lo;
wire                        fwd_x3_r1_wa_w1_lo;
wire                        fwd_x3_r0_ca_w0_hi;
wire                        fwd_x3_r0_wa_w0_hi;
wire                        fwd_x3_r1_ca_w0_hi;
wire                        fwd_x3_r1_wa_w0_hi;
wire                        fwd_x3_r0_wa_w1_hi;
wire                        fwd_x3_r1_wa_w1_hi;
wire                        fwd_x3_r0_ca_w1_hi;
wire                        fwd_x3_r1_ca_w1_hi;
wire                        fwd_x3_r1h_ca_w0_lo;
wire                        fwd_x3_r1h_ca_w1_lo;
wire                        fwd_x3_r1h_wa_w0_lo;
wire                        fwd_x3_r1h_wa_w1_lo;
wire                        fwd_x3_r1h_ca_w0_hi;
wire                        fwd_x3_r1h_wa_w0_hi;
wire                        fwd_x3_r1h_ca_w1_hi;
wire                        fwd_x3_r1h_wa_w1_hi;

// CA bypass control signals
//
wire                        fwd_ca_r0_wa_w0_lo;
wire                        fwd_ca_r0_wa_w1_lo;
wire                        fwd_ca_r1_wa_w0_lo;
wire                        fwd_ca_r1_wa_w1_lo;
wire                        fwd_ca_r0_wa_w0_hi;
wire                        fwd_ca_r1_wa_w0_hi;
wire                        fwd_ca_r0_wa_w1_hi;
wire                        fwd_ca_r1_wa_w1_hi;
wire                        fwd_ca_r1h_wa_w0_lo;
wire                        fwd_ca_r1h_wa_w1_lo;
wire                        fwd_ca_r1h_wa_w0_hi;
wire                        fwd_ca_r1h_wa_w1_hi;

// Pipeline enable signals
//  note, enables for X2, X3 and CA are outputs of this module
//
wire                        da_enable;
wire                        sa_enable;
wire                        x1_enable;

// Pipeline stage kill signals
//  note, kill signals for DA etc, are outputs of this module
//

wire                        da_kill;
wire                        sa_kill;
wire                        x1_kill;
wire                        x2_kill;
wire                        ca_kill;


// Pipeline stage retention signals
//
wire                        x1_retain;
wire                        x2_retain;
wire                        x3_retain;

// Pipeline stage stall signals
//
wire                        ca_stall;

wire                        x2_read_r0_r;
wire                        x2_read_r1_r;
wire                        x3_read_r0_r;
wire                        x3_read_r1_r;

// Pipeline validity signals 
//  note, valid signals for X1, X2, X3, and CA are outputs of this module
//
wire                        sa_valid_r;
wire                        wa_valid_r;

// Completion status of ALU operation when it has reached each of
// the stages from X2 to CA.
//
wire                        x2_done_r;
wire                        x2_has_w0;
wire                        x3_done_r;
wire                        ca_done_r;
// Readiness of branch/jump conditional and branch target registers
// at X1 stage. These depend on flag availability and the resolution of
// any register read dependencies already at the X1 stage.
//
wire                        x1_cond_ready;
wire                        x1_bta_ready;

// Hazards that need to be reported to the Commit stage
//
wire                        ca_replay;
wire                        ca_dc4_replay;

// Writeback, pipeline flush control signals
//
wire                        x2_excpn_stall;
wire                        ct_excpn_trap_r;
wire                        ct_excpn_trap_nxt; // TRAP in CA

wire                        in_dbl_fault_excpn_r; // In double fault
wire [`npuarc_PC_RANGE]            excpn_restart_pc;
wire                        wa_restart_vec_r;
wire [`npuarc_WA_RCMD_RANGE]       wa_restart_cmd_r;


wire [`npuarc_DATA_RANGE]          ca_irq_act_nxt;

// Retirement interface signals
//
wire                        dp_retire_rf_wenb;
wire [`npuarc_GRAD_ADDR_RANGE]     dp_retire_rf_wa;
wire [`npuarc_ZNCV_RANGE]          dp_retire_zncv;
wire                        ar_zncv_upt_r;
wire                        dp_retire_rf_64;
wire                        dp_retire_writes_acc;
wire                        dp_retire_scond;
wire                        dmp_retire_is_load;

wire                        ca_pass_no_hlt;
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Prediction Pipe                                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire [`npuarc_PC_RANGE]            x1_pc_r;           // X1 PC

wire                        da_is_eslot;

wire                        da_in_dslot_r; 
wire                        sa_in_dslot_r;
wire                        x1_in_dslot_r;
wire                        x2_in_dslot_r;
wire                        x3_in_dslot_r;
wire                        ca_in_dslot_r;
//
wire                        da_is_predicted_r;
wire                        da_prediction_r;
wire                        da_orphan_dslot_r;
wire [`npuarc_PC_RANGE]            da_pred_bta_r;
wire                        da_error_branch_r;
//
wire                        sa_is_predicted_r;
wire                        sa_with_dslot_r;
wire                        sa_prediction_r;
wire [`npuarc_PC_RANGE]            sa_pred_bta_r;
wire                        sa_error_branch_r;  // fragged errors only
wire                        sa_error_branch;    // fragged or aliased errors
//
wire                        x1_predictable_r;
wire                        x1_error_branch_r;
wire                        x1_is_eslot_r;
wire [`npuarc_PC_RANGE]            x1_pred_bta_r;
//
wire                        x2_restart_r;
wire [`npuarc_PC_RANGE]            x2_restart_pc_r;
wire                        x2_mispred_r;
wire                        x2_fragged_r;
wire                        x2_error_branch_r;
//wire                        x2_late_pred_r;
//
wire                        x3_error_branch_r;
wire                        x3_late_pred_r;
//
wire                        ca_is_predicted_r;
wire                        ca_prediction_r;
wire [`npuarc_BR_TYPE_RANGE]       ca_br_type_r;
wire [`npuarc_PC_RANGE]            ca_pred_bta_r;
wire                        ca_fragged_r;
wire                        ca_error_branch_r;
wire                        ca_iprot_viol_r;
wire                        ca_iprot_replay;
wire                        ca_pass_no_iprot;
wire                        wa_iprot_replay_r;

wire                        wa_mispred_r;
wire                        wa_stop_r;

// X1 branch resolution dependency conditions
wire                        x1_no_eval;
wire                        x2_done_nxt;
wire                        x1_wa_dslot;    
wire                        x2_wa_dslot;
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Zero Overhead Loop Pipe                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire                        sa_zol_stall;     // SA hazard due to ZOL
wire                        sa_zol_hazard;
wire                        x1_zol_hazard_r;
wire                        sa_hit_lp_end;    // SA insn is at last ZOL insn
wire [`npuarc_LPC_RANGE]           sa_lp_count_r;    // speculative LP_COUNT reg
wire                        x1_zol_stall;     // X1 hazard due to ZOL
wire                        x1_zol_mpd_dir;   // early ZOL mispred dir
wire                        x1_early_pred_r;  // X1 has early ZOL prediction

wire                        x2_zol_ill_seq_r; // illegal inst sequence (ZOL)
wire                        ca_zol_mpd_dir;   // late ZOL mispred dir
wire                        ca_zol_mpd_bta;   // late ZOL mispred BTA
wire                        x3_predicate_r;   // LPcc predicate at X3
wire                        da_valid_r;
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Auxiliary Control                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
// AUX -> Dependency Pipe
wire                        aux_x3_stall;         //

// AUX <-> EXU Aux interface
wire  [`npuarc_DATA_RANGE]         aux_ca_lr_data;       //
 wire                        aux_ca_serial_sr;     //
 wire                        aux_ca_strict_sr;     //

// AUX <-> Exception Pipeline
wire                        x3_aux_unimpl_r;      //
wire                        x3_aux_illegal_r;     //
wire                        x3_aux_k_ro_r;        //
wire                        x3_aux_k_wr_r;        //

// AUX -> DEP Hazard detect
wire                        aux_x2_r4_sr;         // core region 4 SR at X2
wire                        aux_x3_r4_sr_r;       // core region 4 SR at X3
wire                        aux_ca_r4_sr_r;       // core region 4 SR at CA

// Core aux regs module -> AUX
wire  [`npuarc_DATA_RANGE]         core_aux_rdata;       //
wire                        core_aux_illegal;     //
wire                        core_aux_k_rd;        //
wire                        core_aux_k_wr;        //
wire                        core_aux_unimpl;      //
wire                        core_aux_serial_sr;   //
wire                        core_aux_strict_sr;   //
wire                        core_aux_stall;       //
wire                        aux_core_ren_r;       //
wire                        aux_cr1_ren_r;        //
wire                        aux_cr2_ren_r;        //
wire                        aux_cr3_ren_r;        //
wire                        aux_cr4_ren_r;        //
wire                        aux_cr5_ren_r;        //
wire [10:0]                 aux_core_raddr_r;     //
wire                        aux_core_wen_r;       //
wire [10:0]                 aux_core_waddr_r;     //

// BCR aux regs module -> AUX
wire                        aux_bcr_ren_r;        //
wire  [`npuarc_BCR_REG_RANGE]      aux_bcr_raddr_r;      //
wire  [`npuarc_DATA_RANGE]         bcr_aux_rdata;        //
wire                        bcr_aux_illegal;      //
wire                        bcr_aux_k_rd;         //

// EIA aux regs module -> AUX
wire [`npuarc_DATA_RANGE]          aux_eia_raddr_r;      //  (X3) Aux Unit LR Address
wire [`npuarc_DATA_RANGE]          aux_eia_waddr_r;      //  (WA) Aux Unit SR Address
wire                        aux_eia_ren_r;        //
wire                        aux_eia_wen_r;        //
wire [`npuarc_DATA_RANGE]          eia_aux_rdata;        //
wire                        eia_aux_illegal;      //
wire                        eia_aux_k_rd;         //
wire                        eia_aux_k_wr;         //
wire                        eia_aux_unimpl;       //
wire                        eia_aux_serial_sr;    //
wire                        eia_aux_strict_sr;    //
wire                        eia_aux_stall;        //

// Action Points aux regs module -> AUX
wire                        aux_aps_ren_r;        //  
wire  [4:0]                 aux_aps_raddr_r;      //  
wire                        aux_aps_wen_r;        //  
wire  [4:0]                 aux_aps_waddr_r;      //  
wire  [`npuarc_DATA_RANGE]         aps_aux_rdata;        //  
wire                        aps_aux_illegal;      //  
wire                        aps_aux_k_rd;         //  
wire                        aps_aux_k_wr;         //  
wire                        aps_aux_unimpl;       //  
wire                        aps_aux_serial_sr;    //  
wire                        aps_aux_strict_sr;    //  

// MPU aux regs module -> AUX
// MPU aux regs module -> AUX
wire                        aux_mpu_ren_r;        //
wire  [6:0]                 aux_mpu_raddr_r;      //
wire                        aux_mpu_wen_r;        //
wire  [6:0]                 aux_mpu_waddr_r;      //
wire  [`npuarc_DATA_RANGE]         mpu_aux_rdata;        //
wire                        mpu_aux_illegal;      //
wire                        mpu_aux_k_rd;         //
wire                        mpu_aux_k_wr;         //
wire                        mpu_aux_unimpl;       //
wire                        mpu_aux_serial_sr;    //
wire                        mpu_aux_strict_sr;    //

// WA-stage SR to special aux. registers.
//
wire                        wa_status32_wen;      // WA writes STATUS32
wire                        wa_erstatus_wen;      // WA writes ERSTATUS
wire                        wa_eret_wen;          // WA writes ERET
wire                        wa_erbta_wen;         // WA writes ERBTA
wire                        wa_ecr_wen;           // WA writes ECR
wire                        wa_efa_wen;           // WA writes EFA
wire                        wa_efae_wen;          // WA writes EFA_EXT
wire                        ca_triple_fault_set;

wire                        wa_debug_wen;         // WA writes DEBUG
// WA-stage status32, it keeps unchanged until prologue sequence is finished
//
wire [`npuarc_PFLAG_RANGE]         wa_aux_status32_r;    //


// EIA declarations
//
wire                        al_is_cond_inst;      // conditional instruction
wire                        sa_flags_ready;       // assures flags valid at sa

wire  [`npuarc_ISA32_GRP_RANGE]    da_group_code;        // Major group opcode

wire  [`npuarc_ISA32_DOP_RANGE]    da_dop_code_32;       // Dual-opd opcode   (32-bit)
wire  [`npuarc_ISA32_SOP_RANGE]    da_sop_code_32;       // Single-opd opcode (32-bit)
wire  [`npuarc_ISA32_ZOP_RANGE]    da_zop_code_32;       // zero-opd opcode   (32-bit)

wire  [`npuarc_ISA16_DOP_RANGE]    da_dop_code_16;       // Dual-opd opcode   (16-bit)
wire  [`npuarc_ISA16_SOP_RANGE]    da_sop_code_16;       // Single-opd opcode (16-bit)
wire  [`npuarc_ISA16_ZOP_RANGE]    da_zop_code_16;       // zero-opd opcode   (16-bit)

wire  [`npuarc_ISA32_Q_RANGE]      da_q_field;           // Instruction predicate
wire                        da_f_bit;             // Flag update enable (F bit)

wire                        eia_da_valid;         // valid eia inst was decoded
wire                        eia_da_src64;         // eia inst has 64-bit source opds
wire                        eia_da_multi_cycle;   // eia inst is multi-cycle or untimed 
wire                        eia_da_illegal_cond;  // Illegal extension condition

wire                        eia_da_flag_wen;      // Execute inst defines flags
wire                        eia_da_dst_wen;       // Execute inst writes to explicit reg
 
wire                        eia_da_ra0_ext;       // ra0 is ext core register
wire                        eia_da_ra1_ext;       // ra1 is ext core register
wire                        eia_da_wa0_ext;       // wa0 is ext core register
wire                        eia_da_wa1_ext;       // wa1 is ext core register

wire                        da_rf_wenb0;          // Register write enable  0
wire  [`npuarc_RGF_ADDR_RANGE]     da_rf_wa0;            // Register write address 0

wire                        da_rf_wenb1;          // Register write enable  1
wire  [`npuarc_RGF_ADDR_RANGE]     da_rf_wa1;            // Register write address 1

wire                        eia_sa_hazard;        // Stall at sa stage (mid cycle)
wire                        eia_exu_sa_hold;      // blocking eia instr ahead
wire                        eia_exu_x2_hold;      // src64 blocking in x2
wire  [`npuarc_DATA_RANGE]         eia_sa_rf_rdata0;     // Ext. core register on port 0
wire  [`npuarc_DATA_RANGE]         eia_sa_rf_rdata0_hi;  // Ext. core register on port 0 hi
wire  [`npuarc_DATA_RANGE]         eia_sa_rf_rdata1;     // Ext. core register on port 1
wire  [`npuarc_DATA_RANGE]         eia_sa_rf_rdata1_hi;  // Ext. core register on port 1 hi

wire                        eia_da_kernel_instr;  // eia instr requires kernel priv
wire                        eia_da_illegal;       // illegal access to core reg

wire                        eia_x2_is_eia_instr;  // x3 stage opcode is eia instr
wire                        eia_x2_kernel_cc;     // eia cond code needs kernel priv 
wire                        eia_x2_kernel_cr;     // eia core reg needs kernel priv 
wire  [5:0]                 eia_x3_kernel_param;  // ECR param for eia kernel viol

wire                        eia_x1_ext_cond;      // EIA extension condition
wire                        eia_ca_ext_cond;      // EIA extension condition

wire                        eia_exu_x1_eia_op;    // valid eia instr at x1
wire                        eia_exu_ca_eia_op;    // valid eia instr at ca
wire                        eia_exu_x1_hold;      // for multi-cycle non-blocking
wire                        eia_exu_x1_res_valid; // explicit result valid  in x1
wire                        eia_exu_x1_fast_op_r; //
wire  [`npuarc_DATA_RANGE]         eia_exu_x1_res_data;  // explicit result data   in x1
wire  [`npuarc_DATA_RANGE]         eia_exu_x1_res_data_hi; // explicit result data in x1
wire  [`npuarc_ZNCV_RANGE]         eia_exu_x1_res_flags; // explicit result bflags in x1

wire                        eia_exu_ca_res_valid; // explicit result valid  in ca
wire  [`npuarc_DATA_RANGE]         eia_exu_ca_res_data;  // explicit result data   in ca
wire  [`npuarc_DATA_RANGE]         eia_exu_ca_res_data_hi; // explicit result data in x1
wire  [`npuarc_ZNCV_RANGE]         eia_exu_ca_res_flags; // explicit result bflags in ca

wire                        eia_retire_req;       // retire request from gb
wire  [`npuarc_GRAD_TAG_RANGE]     eia_retire_tag;       // retire tag from gb
wire  [`npuarc_DATA_RANGE]         eia_retire_wdata_lo;  // explicit result data   from gb
wire  [`npuarc_ZNCV_RANGE]         eia_retire_flags;     // explicit result bflags from gb
wire                        eia_retire_ack;       // retire ack from exu commit logic
wire                        eia_exu_idle;         // No pending EIA activity

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the core auxiliary register module                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire [`npuarc_DATA_RANGE]          ar_aux_bta_r;         // BTA aux register
wire [`npuarc_DATA_RANGE]          ar_aux_intvbase_r;    // INTVBASE aux register
wire [`npuarc_DATA_RANGE]          ar_aux_stack_base_r;  // STACK_BASE aux register
wire [`npuarc_DATA_RANGE]          ar_aux_stack_top_r;   // STACK_TOP aux register
wire                        ar_sc_r;
wire                        ar_ae_r;              // 

wire [`npuarc_APS_RANGE]           ar_asr_r;             // ASR bits of Debug
wire [`npuarc_DATA_RANGE]          ar_aux_erstatus_r;    // ERSTATUS32 aux. register
wire [`npuarc_DATA_RANGE]          ar_aux_eret_r;        // ERET aux register
wire [`npuarc_DATA_RANGE]          ar_aux_erbta_r;       // ERBTA aux. register
wire [`npuarc_DATA_RANGE]          ar_aux_efa_r;         // EFA aux. register
wire [`npuarc_DATA_RANGE]          ar_aux_efae_r;        // EFA EXT aux. register
wire [`npuarc_DATA_RANGE]          ar_aux_jli_base_r;    // JLI_BASE aux register
wire [`npuarc_DATA_RANGE]          ar_aux_ldi_base_r;    // LDI_BASE aux register
wire [`npuarc_DATA_RANGE]          ar_aux_ei_base_r;     // EI_BASE aux register
wire [`npuarc_DATA_RANGE]          ar_aux_debugi_r;      // DEBUGI aux register

wire [`npuarc_LPC_RANGE]           ar_lp_count_r;        // speculative LP_COUNT reg


  wire [21:0]               intvbase_in_r; // registered at 1st clk after reset

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Exception module                                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire                        ca_ap_excpn_r;        // 


wire                        excpn_in_prologue_r;

wire                        excpn_in_prologue;    //

wire                        ca_db_exception_r;
wire                        int_rtie_replay_r;
wire                        sp_kinv_r        ;
wire                        int_ilink_evt    ;
wire                        al_uop_sirq_haz  ;
wire                        int_load_active  ; 


wire                        da_ifu_exception_r;
wire                        da_ifu_err_nxtpg_r;
wire                        x2_pg_xing_replay_r;
wire                        x2_pg_xing_dslot_r;
wire                        ca_pg_xing_replay_r;
wire                        x2_fa0_transl;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Action Points module                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire                        aps_asr_serial;      // ASR clear on APS AUX
wire                        aps_halt_ack;        // 
wire                        aps_hit_if;          // > Excpn
wire                        aps_hit_mr;          // > Excpn
wire                        aps_pcbrk;           // 
wire [`npuarc_APS_RANGE]           aps_aux_written;     // Indicates write to AP[i]
wire                        x3_aps_break_r;      // 
wire                        x3_aps_halt_r;       // 



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Miscellaneous wires                                                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  don't care carry
reg                         dont_care;
// leda NTL_CON13A on
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the MPU module                                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire                        x3_mpu_iprotv_r;      //
wire                        x3_mpu_dprotv_r;      //
wire [`npuarc_ADDR_RANGE]          x3_mpu_efa_r;         // 
wire                        ca_mpu_excpn_r;       //

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output wires from the Stack Checking module                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

wire                       x3_sc_protv_r;         //
wire [`npuarc_DATA_RANGE]         x3_sc_efa_r;           //
wire                     wa_cmt_norm_evt_r;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Decode stage (alb_dec_regs) module instantiation                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

`ifdef npuarc_RTL_PIPEMON // {
wire Pda_is_16bit_r;
wire Pda_has_limm_r;
wire [`npuarc_DATA_RANGE] Pda_inst_r;
wire [`npuarc_DATA_RANGE] Pda_limm_r;
`endif // }

npuarc_alb_dec_regs u_alb_dec_regs(
  .clk                      (clk                       ),
  .rst_a                    (rst_a                     ),
  .in_dbl_fault_excpn_r     (in_dbl_fault_excpn_r      ),
`ifdef npuarc_RTL_PIPEMON // {
  .Pda_is_16bit_r        (Pda_is_16bit_r  ),
  .Pda_has_limm_r        (Pda_has_limm_r  ),
  .Pda_inst_r       (Pda_inst_r      ),
  .Pda_limm_r       (Pda_limm_r      ),
`endif // }
  .db_active                (db_active                 ),
  .db_valid                 (db_valid                  ),
  .db_inst                  (db_inst                   ),
  .db_limm                  (db_limm                   ),
  .ar_pc_r                  (ar_pc_r                   ),
  .fch_restart              (fch_restart               ),
  .fch_restart_vec          (fch_restart_vec           ),
  .fch_target               (fch_target                ),
  .al_pass                  (al_pass                   ),
  .al_inst                  (al_inst                   ),
  .al_limm                  (al_limm                   ),
  .al_exception             (al_exception              ),
  .al_excpn_type            (al_excpn_type             ),
  .al_iprot_viol            (al_iprot_viol             ),
  .al_is_predicted          (al_is_predicted           ),
  .al_prediction            (al_prediction             ),
  .al_prediction_type       (al_prediction_type        ),
  .al_branch_info           (al_branch_info            ),
  .al_with_dslot            (al_with_dslot             ),

  .al_uop_snoops_pred       (al_uop_snoops_pred        ),
  .al_uop_is_predicted      (al_uop_is_predicted       ),
  .al_uop_prediction        (al_uop_prediction         ),
  .al_uop_prediction_type   (al_uop_prediction_type    ),
  .al_uop_branch_info       (al_uop_branch_info        ),
  .al_uop_with_dslot        (al_uop_with_dslot         ),
  .al_uop_has_limm          (al_uop_has_limm           ),

  .da_is_eslot           (da_is_eslot        ),
  .da_is_predicted_r     (da_is_predicted_r  ),
  .da_prediction_r       (da_prediction_r    ),
  .da_in_dslot_r         (da_in_dslot_r      ),
  .da_pred_bta_r         (da_pred_bta_r      ),
  .da_error_branch_r     (da_error_branch_r  ),
  .da_orphan_dslot_r     (da_orphan_dslot_r  ),
  
  .sa_is_predicted_r     (sa_is_predicted_r  ),
  .sa_prediction_r       (sa_prediction_r    ),
  .sa_pred_bta_r         (sa_pred_bta_r      ),
  .sa_ei_op_r            (sa_ei_op_r         ),
  .sa_seq_pc_r           (sa_seq_pc_r        ),
  
  .ar_aux_status32_r     (ar_aux_status32_r  ),
  .ar_aux_irq_act_r      (ar_aux_irq_act_r   ),
  .int_rtie_replay_r     (int_rtie_replay_r  ),
  .da_rtie_op_r          (da_rtie_op_r       ),
  .ar_aux_irq_ctrl_r     (ar_aux_irq_ctrl_r  ),
  .ar_aux_irq_ctrl_upt_r (ar_aux_irq_ctrl_upt_r),
  .irq_ctrl_wen          (irq_ctrl_wen       ),
  .ar_aux_eret_r         (ar_aux_eret_r      ),
  .ar_aux_erstatus_r     (ar_aux_erstatus_r  ),
  .ar_aux_debug_r        (ar_aux_debug_r     ),
  .ar_aux_debugi_r       (ar_aux_debugi_r    ),
  .ca_irq_act_nxt        (ca_irq_act_nxt     ),
  .da_enable             (da_enable          ),
  .da_kill               (da_kill            ),
  .wa_restart_r          (wa_restart_r       ),
  .wa_restart_cmd_r      (wa_restart_cmd_r   ),

  .al_is_cond_inst       (al_is_cond_inst   ),

  .da_group_code         (da_group_code      ),  
  .da_dop_code_32        (da_dop_code_32     ), 
  .da_sop_code_32        (da_sop_code_32     ), 
  .da_zop_code_32        (da_zop_code_32     ), 
  .da_dop_code_16        (da_dop_code_16     ), 
  .da_sop_code_16        (da_sop_code_16     ), 
  .da_zop_code_16        (da_zop_code_16     ), 

  .da_q_field            (da_q_field         ),     
  .da_f_bit              (da_f_bit           ),       

  .eia_inst_valid        (eia_da_valid       ),        
  .eia_decode_src64      (eia_da_src64       ),        
  .eia_illegal_cond      (eia_da_illegal_cond), 
  .eia_kernel            (eia_da_kernel_instr), 
  .eia_illegal_cr_access (eia_da_illegal     ),

  .eia_multi_cycle       (eia_da_multi_cycle ),
  .eia_flag_wen          (eia_da_flag_wen    ),     
  .eia_dst_wen           (eia_da_dst_wen     ),      
 
  .eia_ra0_is_ext        (eia_da_ra0_ext     ), 
  .eia_ra1_is_ext        (eia_da_ra1_ext     ), 
  .eia_wa0_is_ext        (eia_da_wa0_ext     ), 
  .eia_wa1_is_ext        (eia_da_wa1_ext     ), 

  .da_rf_wenb0           (da_rf_wenb0        ),
  .da_rf_wa0             (da_rf_wa0          ),      
  .da_rf_wenb0_64        ( da_rf_wenb0_64    ),

  .da_rf_wenb1           ( da_rf_wenb1       ),  
  .da_rf_wa1             ( da_rf_wa1         ),     
  .da_rf_wenb1_64        ( da_rf_wenb1_64    ),

  .sa_pc_nxt             (sa_pc_nxt          ),
  .sa_limm_nxt           (sa_limm_nxt        ),
  .sa_code_nxt           (sa_code_nxt        ),
  .sa_seq_pc_nxt         (sa_seq_pc_nxt      ),
  .sa_is_16bit_nxt       (sa_is_pc_nxt       ),
  .da_iprot_viol_r       (da_iprot_viol_r    ),


  .da_pass               (da_pass            ),
  .al_uop_pass           (al_uop_pass        ),
  .da_dslot              (da_dslot           ),
  .al_uop_epil           (al_uop_epil        ),
  .da_ei_op              (da_ei_op           ),
  .da_ldi_src0           (da_ldi_src0        ),
  .da_jli_src0           (da_jli_src0        ),
  .da_uop_u7_pcl         (da_uop_u7_pcl      ),
  .da_zncv_wen           (da_zncv_wen        ),
  .da_uop_stall          (da_uop_stall       ),
  .da_uop_prol_r         (da_uop_prol_r      ),
  .da_uop_busy_r         (da_uop_busy_r      ),
  .da_uop_is_excpn_r     (da_uop_is_excpn_r  ),
  .al_uop_sirq_haz       (al_uop_sirq_haz    ),
  .da_uop_is_sirq_r      (da_uop_is_sirq_r   ),
//  .da_uop_is_gpr_r       (da_uop_is_gpr_r    ),
  .da_valid_r            (da_valid_r         ),
  .da_rf_ra0_r           (da_rf_ra0_r        ),
  .da_rf_ra1_r           (da_rf_ra1_r        ),
  .da_rf_renb0_64_r      (da_rf_renb0_64_r   ),
  .da_rf_renb0_r         (da_rf_renb0_r      ),
  .da_rf_renb1_64_r      (da_rf_renb1_64_r   ),
  .da_rf_renb1_r         (da_rf_renb1_r      )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Operand Select (alb_opd_sel) module instantiation                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_opd_sel u_alb_opd_sel(
  .clk                  (clk                ),
  .rst_a                (rst_a              ),
  .ar_aux_jli_base_r    (ar_aux_jli_base_r  ),
  .ar_aux_ldi_base_r    (ar_aux_ldi_base_r  ),
  .ar_aux_ei_base_r     (ar_aux_ei_base_r   ),

  .sa_pc_nxt            (sa_pc_nxt          ),
  .sa_limm_nxt          (sa_limm_nxt        ),


  .sa_code_nxt          (sa_code_nxt        ),
  .sa_seq_pc_nxt        (sa_seq_pc_nxt      ),
  .sa_is_16bit_nxt      (sa_is_pc_nxt       ),
  .da_iprot_viol_r      (da_iprot_viol_r    ),
  .da_in_dslot_r        (da_in_dslot_r      ),
  .da_uop_u7_pcl        (da_uop_u7_pcl      ),

  .sa_error_branch      (sa_error_branch    ),
  .sa_pred_bta_r        (sa_pred_bta_r      ),
  
  .da_pass              (da_pass            ),
  .sa_pass              (sa_pass            ),
  .sa_kill              (sa_kill            ),
  .sa_valid_r           (sa_valid_r         ),
  .sa_enable            (sa_enable          ),
  .da_error_branch_r    (da_error_branch_r  ),
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on mux
// SJ:  functionally independant signals
  .x1_byp_data0         (x1_byp_data0       ),
// spyglass enable_block Ac_conv01
  .x2_byp_data0         (x2_byp_data0       ),
  .x3_byp_data0         (x3_byp_data0       ),
  .ca_byp_data0_lo      (ca_byp_data0_lo    ),
  .ca_byp_data0_hi      (ca_byp_data0_hi    ),
  .ca_byp_data1_lo      (ca_byp_data1_lo    ),
  .ca_byp_data1_hi      (ca_byp_data1_hi    ),
  .wa_rf_wenb0_r        (wa_rf_wenb0_r      ),
  .wa_rf_wa0_r          (wa_rf_wa0_r        ),
  .wa_rf_wdata0_lo_r    (wa_rf_wdata0_lo_r  ),
  .wa_rf_wenb0_64_r     (wa_rf_wenb0_64_r   ),
  .wa_rf_wdata0_hi_r    (wa_rf_wdata0_hi_r  ),
  .wa_rf_wenb1_r        (wa_rf_wenb1_r      ),
  .wa_rf_wa1_r          (wa_rf_wa1_r        ),
  .wa_rf_wdata1_lo_r    (wa_rf_wdata1_lo_r  ),
  .wa_rf_wenb1_64_r     (wa_rf_wenb1_64_r   ),
  .wa_rf_wdata1_hi_r    (wa_rf_wdata1_hi_r  ),
  .wa_accl_nxt          (wa_accl_nxt        ),
  .wa_acch_nxt          (wa_acch_nxt        ),
  .wa_acc_wenb          (wa_acc_wenb        ),
  .accl_r               (accl_r             ),
  .acch_r               (acch_r             ),
  .fwd_x1_sa0_lo        (fwd_x1_sa0_lo      ),
  .fwd_x2_sa0_lo        (fwd_x2_sa0_lo      ),
  .fwd_x3_sa0_lo        (fwd_x3_sa0_lo      ),
  .fwd_ca0_lo_sa0_lo    (fwd_ca0_lo_sa0_lo  ),
  .fwd_ca1_lo_sa0_lo    (fwd_ca1_lo_sa0_lo  ),
  .fwd_wa0_lo_sa0_lo    (fwd_wa0_lo_sa0_lo  ),
  .fwd_wa1_lo_sa0_lo    (fwd_wa1_lo_sa0_lo  ),
  .fwd_ca0_hi_sa0_lo    (fwd_ca0_hi_sa0_lo  ),
  .fwd_wa0_hi_sa0_lo    (fwd_wa0_hi_sa0_lo  ),
  .fwd_ca1_hi_sa0_lo    (fwd_ca1_hi_sa0_lo  ),
  .fwd_ca1_hi_sa1_lo    (fwd_ca1_hi_sa1_lo  ),
  .fwd_wa1_hi_sa0_lo    (fwd_wa1_hi_sa0_lo  ),
  .fwd_wa1_hi_sa1_lo    (fwd_wa1_hi_sa1_lo  ),
  .fwd_wa0_hi_sa0_hi    (fwd_wa0_hi_sa0_hi  ),
  .fwd_wa1_hi_sa0_hi    (fwd_wa1_hi_sa0_hi  ),
  .fwd_x1_sa1_lo        (fwd_x1_sa1_lo      ),
  .fwd_x2_sa1_lo        (fwd_x2_sa1_lo      ),
  .fwd_x3_sa1_lo        (fwd_x3_sa1_lo      ),
  .fwd_ca0_lo_sa1_lo    (fwd_ca0_lo_sa1_lo  ),
  .fwd_ca1_lo_sa1_lo    (fwd_ca1_lo_sa1_lo  ),
  .fwd_wa0_lo_sa1_lo    (fwd_wa0_lo_sa1_lo  ),
  .fwd_wa1_lo_sa1_lo    (fwd_wa1_lo_sa1_lo  ),
  .fwd_ca0_hi_sa1_lo    (fwd_ca0_hi_sa1_lo  ),
  .fwd_wa0_hi_sa1_lo    (fwd_wa0_hi_sa1_lo  ),
  .fwd_wa0_lo_sa0_hi    (fwd_wa0_lo_sa0_hi  ),
  .fwd_wa1_lo_sa0_hi    (fwd_wa1_lo_sa0_hi  ),
  .fwd_wa0_hi_sa1_hi    (fwd_wa0_hi_sa1_hi  ),
  .fwd_wa0_lo_sa1_hi    (fwd_wa0_lo_sa1_hi  ),
  .fwd_wa1_lo_sa1_hi    (fwd_wa1_lo_sa1_hi  ),
  .fwd_wa1_hi_sa1_hi    (fwd_wa1_hi_sa1_hi  ),

  .int_ilink_evt        (int_ilink_evt      ),
  .wa_pc                (wa_pc              ),


  .ar_lp_count_r        (ar_lp_count_r      ),
  .sa_hit_lp_end        (sa_hit_lp_end      ),

  .sa_valid_nxt         (sa_valid_nxt       ),
  .sa_opds_in_sa_r      (sa_opds_in_sa_r    ),
  .sa_agu_uses_r0_r     (sa_agu_uses_r0_r   ),
  .sa_agu_uses_r1_r     (sa_agu_uses_r1_r   ),
  .sa_dslot_r           (sa_dslot_r         ),
  .sa_link_r            (sa_link_r          ),
  .sa_wa0_lpc_r         (sa_wa0_lpc_r       ),
  .sa_ei_op_r           (sa_ei_op_r         ),
  .sa_ldi_src0_r        (sa_ldi_src0_r      ),
  .sa_jli_src0_r        (sa_jli_src0_r      ),
  .sa_leave_op_r        (sa_leave_op_r      ),
  .sa_branch_or_jump    (sa_branch_or_jump  ),
  .sa_multi_op_r        (sa_multi_op_r      ),
  .sa_sr_op_r           (sa_sr_op_r         ),
  .sa_dest_cr_is_ext_r  (sa_dest_cr_is_ext  ),
  .sa_lr_op_r           (sa_lr_op_r         ),
  .sa_uop_predictable_r (sa_uop_predictable_r),
  .sa_zncv_wen_r        (sa_zncv_wen_r      ),
  .sa_q_field_r         (sa_q_field_r       ),
  .sa_with_carry_r      (sa_with_carry_r    ),
  .sa_uop_inst_r        (sa_uop_inst_r      ),
  .sa_seq_pc_r          (sa_seq_pc_r        ),
  .sa_restart_pc        (sa_restart_pc      ),
  .sa_pc                (sa_pc              ),
  .eia_ra0_is_ext       (eia_da_ra0_ext     ), 
  .eia_ra1_is_ext       (eia_da_ra1_ext     ), 
  .eia_sa_reg0          (eia_sa_rf_rdata0   ),
  .eia_sa_reg0_hi       (eia_sa_rf_rdata0_hi),
  .eia_sa_reg1          (eia_sa_rf_rdata1   ),
  .eia_sa_reg1_hi       (eia_sa_rf_rdata1_hi),
  .sa_rf_ra0_r          (sa_rf_ra0_r        ),
  .sa_rf_ra1_r          (sa_rf_ra1_r        ),
  .sa_rf_renb0_r        (sa_rf_renb0_r      ),
  .sa_rf_renb0_64_r     (sa_rf_renb0_64_r   ),
  .sa_rf_wa0_r          (sa_rf_wa0_r        ),
  .sa_rf_wenb0_r        (sa_rf_wenb0_r      ),
  .sa_rf_wenb0_64_r     (sa_rf_wenb0_64_r   ),
  .sa_rf_renb1_r        (sa_rf_renb1_r      ),
  .sa_rf_renb1_64_r     (sa_rf_renb1_64_r   ),
  .sa_rf_wa1_r          (sa_rf_wa1_r        ),
  .sa_rf_wenb1_r        (sa_rf_wenb1_r      ),
  .sa_rf_wenb1_64_r     (sa_rf_wenb1_64_r   ),
  .sa_reads_acc_r       (sa_reads_acc_r     ),
  .sa_dsync_op_r        (sa_dsync_op_r      ),
  .sa_dmb_op_r          (sa_dmb_op_r        ),
  .sa_dmb_type_r        (sa_dmb_type_r      ),
  .sa_mpy_op_r          (sa_mpy_op_r        ),
  .sa_vector_op_r       (sa_vector_op_r     ),
  .sa_half_size_r       (sa_half_size_r     ),
  .sa_dual_op_r         (sa_dual_op_r       ),
  .sa_div_op_r          (sa_div_op_r        ),
  .sa_load_r            (sa_load_r          ),
  .sa_store_r           (sa_store_r         ),
  .sa_br_type           (sa_br_type         ),
  .sa_secondary         (sa_secondary       ),
  .sa_commit_size       (sa_commit_size     ),
  .sa_iprot_viol_r      (sa_iprot_viol_r    ),



  .x1_src0_nxt          (x1_src0_nxt        ),
  .x1_src1_nxt          (x1_src1_nxt        ),
  .x1_src2_nxt          (x1_src2_nxt        ),
  .x1_src3_nxt          (x1_src3_nxt        ),
  .sa_src0_pass         (sa_src0_pass       ),
  .sa_src1_pass         (sa_src1_pass       ),
  .sa_src2_pass         (sa_src2_pass       ),
  .sa_src3_pass         (sa_src3_pass       ),
  .x1_code_nxt          (x1_code_nxt        )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Execution Stage 1 (alb_exec1) module instantiation                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_exec1 u_alb_exec1(
  .clk                  (clk                ),
  .rst_a                (rst_a              ),
  .db_active            (db_active          ),
  .ar_aux_status32_r    (ar_aux_status32_r  ),
  .ar_aux_erstatus_r    (ar_aux_erstatus_r  ),
  .ar_aux_user_mode_r   (ar_aux_user_mode_r ),
  
  .x1_src0_nxt          (x1_src0_nxt        ),
  .x1_src1_nxt          (x1_src1_nxt        ),
  .x1_src2_nxt          (x1_src2_nxt        ),
  .x1_src3_nxt          (x1_src3_nxt        ),
  .sa_restart_pc        (sa_restart_pc      ),

  .sa_src0_pass         (sa_src0_pass       ),
  .sa_src1_pass         (sa_src1_pass       ),
  .sa_src2_pass         (sa_src2_pass       ),
  .sa_src3_pass         (sa_src3_pass       ),

  .x1_code_nxt          (x1_code_nxt        ),

  .sa_pass              (sa_pass            ),

  .x1_valid_r           (x1_valid_r         ),
  .x1_pass              (x1_pass            ),
  .x1_retain            (x1_retain          ),
  .x1_enable            (x1_enable          ),
  .x1_bta_ready         (x1_bta_ready       ),
  .x1_no_eval           (x1_no_eval         ),
  .x2_done_nxt          (x2_done_nxt        ),

  .sa_error_branch_r    (sa_error_branch_r  ),
  .x1_predictable_r     (x1_predictable_r   ),
  .x1_error_branch_r    (x1_error_branch_r  ),
  .x1_is_eslot_r        (x1_is_eslot_r      ),
  .x1_pred_bta_r        (x1_pred_bta_r      ),
//  .x2_kill              (x2_kill            ),
//  .x1_wa_dslot          (x1_wa_dslot        ),
// .x2_wa_dslot           (x2_wa_dslot        ),

//  .x1_zol_lp_jmp        (x1_zol_lp_jmp      ),

  .x1_eia_res_valid     (eia_exu_x1_res_valid), 
  .x1_eia_fast_op_r     (eia_exu_x1_fast_op_r),
  .x1_eia_res_data      (eia_exu_x1_res_data ),  
///   `if (64 == 64) // {
///   .x1_eia_res_data_hi   (eia_exu_x1_res_data_hi ),  
///   `endif                // }
  .x1_eia_res_flags     (eia_exu_x1_res_flags), 

  .x1_addr_base         (x1_addr_base       ),    
  .x1_addr_offset       (x1_addr_offset     ),  

//  .x2_valid_r           (x2_valid_r         ),
//  .x2_dslot_r           (x2_dslot_r         ),
  .x2_zncv_r            (x2_zncv_r          ),
  
  .dmp_dc4_fast_data    (dmp_dc4_fast_data  ),
  .wa_rf_wdata0_lo      (wa_rf_wdata0_lo_r  ),
  .wa_rf_wdata1_lo      (wa_rf_wdata1_lo_r  ),
  .ca_byp_data1_hi      (ca_byp_data1_hi    ),
  .wa_rf_wdata1_hi      (wa_rf_wdata1_hi_r  ),
  .x2_byp_data0         (x2_byp_data0       ),
  .x3_byp_data0         (x3_byp_data0       ),
  .ca_byp_data0_lo      (ca_byp_data0_lo    ),
  .ca_byp_data1_lo      (ca_byp_data1_lo    ),
  .ca_byp_data0_hi      (ca_byp_data0_hi    ),
  .wa_rf_wdata0_hi      (wa_rf_wdata0_hi_r  ),
  .fwd_x1_r0_dmp_fast   (fwd_x1_r0_dmp_fast ),
  .fwd_x1_r1_dmp_fast   (fwd_x1_r1_dmp_fast ),
  .fwd_x1_r0_wa_w0_lo   (fwd_x1_r0_wa_w0_lo ),
  .fwd_x1_r1_wa_w0_lo   (fwd_x1_r1_wa_w0_lo ),
  .fwd_x1_r0_wa_w1_lo   (fwd_x1_r0_wa_w1_lo ),
  .fwd_x1_r1_wa_w1_lo   (fwd_x1_r1_wa_w1_lo ),
  .fwd_x1_r0_ca_w1_hi   (fwd_x1_r0_ca_w1_hi ),
  .fwd_x1_r1_ca_w1_hi   (fwd_x1_r1_ca_w1_hi ),
  .fwd_x1_r0h_ca_w1_hi  (fwd_x1_r0h_ca_w1_hi),
  .fwd_x1_r1h_ca_w1_hi  (fwd_x1_r1h_ca_w1_hi),
  .fwd_x1_r0_wa_w1_hi   (fwd_x1_r0_wa_w1_hi ),
  .fwd_x1_r1_wa_w1_hi   (fwd_x1_r1_wa_w1_hi ),
  .fwd_x1_r0h_wa_w1_hi  (fwd_x1_r0h_wa_w1_hi),
  .fwd_x1_r1h_wa_w1_hi  (fwd_x1_r1h_wa_w1_hi),
  .fwd_x1_r1h_wa_w0_lo  (fwd_x1_r1h_wa_w0_lo),
  .fwd_x1_r1h_wa_w1_lo  (fwd_x1_r1h_wa_w1_lo),
  .fwd_x1_r0_x2_w0      (fwd_x1_r0_x2_w0    ),
  .fwd_x1_r1_x2_w0      (fwd_x1_r1_x2_w0    ),
  .fwd_x1_r0h_x2_w0     (fwd_x1_r0h_x2_w0   ),
  .fwd_x1_r1h_x2_w0     (fwd_x1_r1h_x2_w0   ),
  .fwd_x1_r0_x3_w0      (fwd_x1_r0_x3_w0    ),
  .fwd_x1_r1_x3_w0      (fwd_x1_r1_x3_w0    ),
  .fwd_x1_r0h_x3_w0     (fwd_x1_r0h_x3_w0   ),
  .fwd_x1_r1h_x3_w0     (fwd_x1_r1h_x3_w0   ),
  .fwd_x1_r0_ca_w0_lo   (fwd_x1_r0_ca_w0_lo ),
  .fwd_x1_r1_ca_w0_lo   (fwd_x1_r1_ca_w0_lo ),
  .fwd_x1_r0_ca_w1_lo   (fwd_x1_r0_ca_w1_lo ),
  .fwd_x1_r1_ca_w1_lo   (fwd_x1_r1_ca_w1_lo ),
  .fwd_x1_r0_ca_w0_hi   (fwd_x1_r0_ca_w0_hi ),
  .fwd_x1_r1_ca_w0_hi   (fwd_x1_r1_ca_w0_hi ),
  .fwd_x1_r0_wa_w0_hi   (fwd_x1_r0_wa_w0_hi ),
  .fwd_x1_r1_wa_w0_hi   (fwd_x1_r1_wa_w0_hi ),
  .fwd_x1_r0h_ca_w0_lo  (fwd_x1_r0h_ca_w0_lo),
  .fwd_x1_r0h_ca_w0_hi  (fwd_x1_r0h_ca_w0_hi),
  .fwd_x1_r1h_ca_w0_lo  (fwd_x1_r1h_ca_w0_lo),
  .fwd_x1_r1h_ca_w0_hi  (fwd_x1_r1h_ca_w0_hi),

  .fwd_x1_r0h_ca_w1_lo  (fwd_x1_r0h_ca_w1_lo),
  .fwd_x1_r1h_ca_w1_lo  (fwd_x1_r1h_ca_w1_lo),

  .fwd_x1_r0h_wa_w0_lo  (fwd_x1_r0h_wa_w0_lo),
  .fwd_x1_r0h_wa_w0_hi  (fwd_x1_r0h_wa_w0_hi),
  .fwd_x1_r0h_wa_w1_lo  (fwd_x1_r0h_wa_w1_lo),
  .fwd_x1_r1h_wa_w0_hi  (fwd_x1_r1h_wa_w0_hi),
  .fwd_zncv_x1          (fwd_zncv_x1        ),
  .fwd_zncv_x1_x2       (fwd_zncv_x1_x2     ),
  .fwd_zncv_x1_ca       (fwd_zncv_x1_ca     ),
  .fwd_zncv_x1_ar       (fwd_zncv_x1_ar     ),
  .dp_retire_zncv       (dp_retire_zncv     ),
  .ca_retire_flags      (ca_retire_flags    ),
  
  .wa_aux_status32_nxt  (wa_aux_status32_nxt),
  
  .x1_byp_data0         (x1_byp_data0       ),
  .x2_src0_nxt          (x2_src0_nxt        ),
  .x2_src1_nxt          (x2_src1_nxt        ),
  .x2_target_nxt        (x2_target_nxt      ),
  .x1_res_pass          (x1_res_pass        ),
  .x1_src0_pass         (x1_src0_pass       ),
  .x1_src1_pass         (x1_src1_pass       ),
  
  .x2_zncv_nxt          (x2_zncv_nxt        ),
  .x2_code_nxt          (x2_code_nxt        ),
  .x2_lt_flag_nxt       (x2_lt_flag_nxt     ),
  
  .x1_br_target         (x1_br_target       ),
  .x1_br_fall_thru      (x1_br_fall_thru    ),
  .x1_br_taken          (x1_br_taken        ),
  .x1_br_direction      (x1_br_direction    ),
  .x1_bi_bta_mpd        (x1_bi_bta_mpd      ),
  .x1_link_addr         (x1_link_addr       ),

  .x1_rf_ra0_r          (x1_rf_ra0_r        ),
  .x1_rf_ra1_r          (x1_rf_ra1_r        ),
  .x1_rf_wa0_r          (x1_rf_wa0_r        ),
  .x1_rf_wenb0_r        (x1_rf_wenb0_r      ),
  .x1_rf_wenb0_64_r     (x1_rf_wenb0_64_r   ),
  .x1_cc_byp_64_haz_r   (x1_cc_byp_64_haz_r ),
  .x1_rf_wa1_r          (x1_rf_wa1_r        ),
  .x1_rf_wenb1_r        (x1_rf_wenb1_r      ),
  .x1_rf_wenb1_64_r     (x1_rf_wenb1_64_r   ),
  .x1_rf_renb0_64_r     (x1_rf_renb0_64_r   ),
  .x1_rf_renb1_64_r     (x1_rf_renb1_64_r   ),
  .x1_acc_wenb_r        (x1_acc_wenb_r      ),
  .x1_zncv_wen_r        (x1_zncv_wen_r      ),
  .x1_flag_op_r         (x1_flag_op_r       ),
  .x1_brk_op_r          (x1_brk_op_r        ),
  .x1_sleep_op_r        (x1_sleep_op_r      ),
  .x1_cond              (x1_cond            ),
  .x1_q_field_r         (x1_q_field_r       ),
  .x1_signed_op_r       (x1_signed_op_r     ),

  
  .x1_uop_inst_r        (x1_uop_inst_r      ),

  .x1_wa0_lpc_r         (x1_wa0_lpc_r       ),
  .x1_loop_op_r         (x1_loop_op_r       ),


  .x1_valid_nxt         (x1_valid_nxt       ),
  .x1_fast_op_r         (x1_fast_op_r       ),
  .x1_slow_op_r         (x1_slow_op_r       ),
  .x1_dslot_r           (x1_dslot_r         ),
  .x1_sr_op_r           (x1_sr_op_r         ),
  .x1_uop_commit_r      (x1_uop_commit_r    ),
  .x1_uop_prol_r        (x1_uop_prol_r      ),
  .x1_uop_epil_r        (x1_uop_epil_r      ),
  .x1_with_carry_r      (x1_with_carry_r    ),
  .x1_grab_src0         (x1_grab_src0       ),
  .x1_grab_src1         (x1_grab_src1       ),
  .x1_grab_src2         (x1_grab_src2       ),
  .x1_grab_src3         (x1_grab_src3       ),
  .x1_rgf_link          (x1_rgf_link_r      ),
  .x1_dmb_op_r          (x1_dmb_op_r        ),
  .x1_dmb_type_r        (x1_dmb_type_r      ),
  .x1_ei_op_r           (x1_ei_op_r         ),
  .x1_btab_op_r         (x1_btab_op_r       ),
  .x1_opds_in_sa_r      (x1_opds_in_sa_r    ),
  .x1_opds_in_x1_r      (x1_opds_in_x1_r    ),
  .x1_agu_uses_r0_r     (x1_agu_uses_r0_r   ),
  .x1_mpy_op_r          (x1_mpy_op_r        ),
  .x1_half_size_r       (x1_half_size_r     ),
  .x1_dual_op_r         (x1_dual_op_r       ),
  .x1_vector_op_r       (x1_vector_op_r     ),
  .x1_quad_op_r         (x1_quad_op_r       ),
  .mp1_src0_nxt         (mp1_src0_nxt       ),
  .mp1_src1_nxt         (mp1_src1_nxt       ),
  .mp1_src2_nxt         (mp1_src2_nxt       ),
  .mp1_src3_nxt         (mp1_src3_nxt       ),
  .x1_div_op_r          (x1_div_op_r        ),
  .x1_div_kind_r        (x1_div_kind_r      ),
  .x2_predicate_nxt     (x2_predicate_nxt   ), // X1 eval condition
  .x1_iprot_viol_r      (x1_iprot_viol_r    ),
  .eia_ext_cond         (eia_x1_ext_cond    ),
  .x1_dest_cr_is_ext_r  (x1_dest_cr_is_ext  ),
  .x1_addr_pass         (x1_addr_pass       ),
  .x1_size_r            (x1_size_r          ),
  .x1_load_r            (x1_load_r          ),
  .x1_store_r           (x1_store_r         ),
  .x1_pref_r            (x1_pref_r          ),
  .x1_cache_byp_r       (x1_cache_byp_r     ),
  .x1_mem_addr0         (x1_mem_addr0       ),
  .x1_mem_addr1         (x1_mem_addr1       ),
  .x1_bank_sel_lo       (x1_bank_sel_lo     ),  
  .x1_bank_sel_hi       (x1_bank_sel_hi     )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Execution Stage 2 (alb_exec2) module instantiation                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_exec2 u_alb_exec2(
  .clk                  (clk                ),
  .rst_a                (rst_a              ),
  .db_active            (db_active          ),
  .db_data              (db_data            ),
  .db_sel_limm0         (db_sel_limm0       ),
  .db_sel_limm1         (db_sel_limm1       ),

  .x2_q_field_r         (x2_q_field_r       ),

  .x2_src0_nxt          (x2_src0_nxt        ),
  .x2_src1_nxt          (x2_src1_nxt        ),
  .x1_byp_data0         (x1_byp_data0       ),
  .x1_src0_pass         (x1_src0_pass       ),
  .x1_src1_pass         (x1_src1_pass       ),
  .x1_res_pass          (x1_res_pass        ),
  .x2_zncv_nxt          (x2_zncv_nxt        ),
  .x2_code_nxt          (x2_code_nxt        ),
  .x2_lt_flag_nxt       (x2_lt_flag_nxt     ),
  .x2_target_nxt        (x2_target_nxt      ),
  
  .x1_mem_addr0         (x1_mem_addr0       ),
  .x1_addr_pass         (x1_addr_pass       ),
  
  .x2_valid_r           (x2_valid_r         ),
  .x2_done_r            (x2_done_r          ),
  .x2_pass              (x2_pass            ),
  .x2_enable            (x2_enable          ),
  .x2_retain            (x2_retain          ),
  .x2_read_r0_r         (x2_read_r0_r       ),
  .x2_read_r1_r         (x2_read_r1_r       ),
  .x1_pass              (x1_pass            ),
  .x2_fragged_r         (x2_fragged_r       ),
  .x2_error_branch_r    (x2_error_branch_r  ),
  .ar_aux_jli_base_r    (ar_aux_jli_base_r  ),
  .ar_aux_ldi_base_r    (ar_aux_ldi_base_r  ),
  .ar_aux_ei_base_r     (ar_aux_ei_base_r   ),
  .ar_aux_status32_r    (ar_aux_status32_r  ),
  .ar_aux_user_mode_r   (ar_aux_user_mode_r ),
  .ar_aux_lp_start_r    (ar_aux_lp_start_r  ),
  .ar_aux_lp_end_r      (ar_aux_lp_end_r    ),
  .fwd_x2_r0_wa_w0_lo   (fwd_x2_r0_wa_w0_lo ),
  .fwd_x2_r0_wa_w1_lo   (fwd_x2_r0_wa_w1_lo ),
  .fwd_x2_r1_wa_w0_lo   (fwd_x2_r1_wa_w0_lo ),
  .fwd_x2_r1_wa_w1_lo   (fwd_x2_r1_wa_w1_lo ),
  .fwd_x2_r0_wa_w0_hi   (fwd_x2_r0_wa_w0_hi ),
  .fwd_x2_r1_wa_w0_hi   (fwd_x2_r1_wa_w0_hi ),
  .fwd_x2_r0_wa_w1_hi   (fwd_x2_r0_wa_w1_hi ),
  .fwd_x2_r1_wa_w1_hi   (fwd_x2_r1_wa_w1_hi ),
  .fwd_x2_r1h_wa_w0_lo  (fwd_x2_r1h_wa_w0_lo),
  .fwd_x2_r1h_wa_w1_lo  (fwd_x2_r1h_wa_w1_lo),
  .fwd_x2_r1h_wa_w0_hi  (fwd_x2_r1h_wa_w0_hi),
  .fwd_x2_r1h_wa_w1_hi  (fwd_x2_r1h_wa_w1_hi),
  .wa_rf_wdata0_lo_r    (wa_rf_wdata0_lo_r  ),
  .wa_rf_wdata1_lo_r    (wa_rf_wdata1_lo_r  ),
  .wa_rf_wdata0_hi_r    (wa_rf_wdata0_hi_r  ),
  .wa_rf_wdata1_hi_r    (wa_rf_wdata1_hi_r  ),

  .x2_mem_addr_r        (x2_mem_addr_r      ),
//`if (`HAS_MPU == 1) // {
//  .x2_mem_addr1_r       (x2_mem_addr1_r      ),
//`endif                // }
  .x2_uop_inst_r        (x2_uop_inst_r      ),
  
  .x2_dslot_r           (x2_dslot_r         ),
  .x2_in_eslot_r        (x2_in_eslot_r      ),

  .x2_sync_op_r         (x2_sync_op_r       ),
  .x2_slow_op_r         (x2_slow_op_r       ),
  .x2_load_r            (x2_load_r          ),
  .x2_pref_r            (x2_pref_r          ),
  .x2_store_r           (x2_store_r         ),
  .x2_size_r            (x2_size_r          ),
  .x2_zncv_r            (x2_zncv_r          ),
  .x2_zncv_wen_r        (x2_zncv_wen_r      ),
  .x2_wevt_op           (x2_wevt_op         ),
  .x2_flag_op_r         (x2_flag_op_r       ),
  .x2_signed_op_r       (x2_signed_op_r     ),
  .x2_invalid_instr_r   (x2_invalid_instr_r ),
  .x2_illegal_operand_r (x2_illegal_operand_r),
  .x2_jump_r            (x2_jump_r          ),
  .x2_has_limm_r        (x2_has_limm_r      ),
  .x2_rtie_op_r         (x2_rtie_op_r       ),
  .x2_leave_op_r        (x2_leave_op_r      ),
  .x2_cache_byp_r       (x2_cache_byp_r     ),
  .x2_rel_branch_r      (x2_rel_branch_r    ),
  .x2_kernel_op_r       (x2_kernel_op_r     ),
  .x2_rgf_link_r        (x2_rgf_link_r      ),
  .x2_brk_op_r          (x2_brk_op_r        ),
  .x2_multi_op_r        (x2_multi_op_r      ),
  .x2_btab_op_r         (x2_btab_op_r       ),
  .x2_byp_data0         (x2_byp_data0       ),
  .x2_rf_ra0_r          (x2_rf_ra0_r        ),
  .x2_rf_ra1_r          (x2_rf_ra1_r        ),
  .x2_rf_wa0_r          (x2_rf_wa0_r        ),
  .x2_rf_wenb0_r        (x2_rf_wenb0_r      ),
  .x2_rf_wenb0_64_r     (x2_rf_wenb0_64_r   ),
  .x2_cc_byp_64_haz_r   (x2_cc_byp_64_haz_r ),
  .x2_rf_wa1_r          (x2_rf_wa1_r        ),
  .x2_rf_wenb1_r        (x2_rf_wenb1_r      ),
  .x2_rf_wenb1_64_r     (x2_rf_wenb1_64_r   ),
  .x2_rf_renb0_64_r     (x2_rf_renb0_64_r   ),
  .x2_rf_renb1_64_r     (x2_rf_renb1_64_r   ),
  .x2_acc_wenb_r        (x2_acc_wenb_r      ),
  .x2_rf_renb0_r        (x2_rf_renb0_r      ),
  .x2_rf_renb1_r        (x2_rf_renb1_r      ),
  .x2_locked_r          (x2_locked_r        ),

  .x2_aux_addr_r        (x2_aux_addr_r      ),
  .x2_lr_op_r           (x2_lr_op_r         ),
  .x2_sr_op_r           (x2_sr_op_r         ),

  .x2_valid_nxt         (x2_valid_nxt       ),
  .x2_ei_op_r           (x2_ei_op_r         ),
  .x2_dmb_op_r          (x2_dmb_op_r        ),
  .x2_dmb_type_r        (x2_dmb_type_r      ),
 
  .x2_wa0_lpc_r         (x2_wa0_lpc_r       ),
  .x2_loop_op_r         (x2_loop_op_r       ),
  
  .x2_mpy_op_r          (x2_mpy_op_r        ),
  .x2_half_size_r       (x2_half_size_r     ),
  .x2_dual_op_r         (x2_dual_op_r       ),
  .x2_vector_op_r       (x2_vector_op_r     ),
  .x2_quad_op_r         (x2_quad_op_r       ),
  .x2_div_op_r          (x2_div_op_r        ),
  .x2_dest_cr_is_ext_r  (x2_dest_cr_is_ext  ),

  .x3_src0_nxt          (x3_src0_nxt        ),
  .x3_src1_nxt          (x3_src1_nxt        ),
  .x3_res_nxt           (x3_res_nxt         ),
  .x2_src0_pass         (x2_src0_pass       ),
  .x2_src1_pass         (x2_src1_pass       ),
  .x2_res_pass          (x2_res_pass        ),
  .x2_addr_pass         (x2_addr_pass       ),
  .x3_code_nxt          (x3_code_nxt        ),
  .x3_target_nxt        (x3_target_nxt      ),
  .x3_zncv_nxt          (x3_zncv_nxt        )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Execution Stage 3 (alb_exec3) module instantiation                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_exec3 u_alb_exec3(
  .clk                 (clk                ),
  .rst_a               (rst_a              ),

  .db_active           (db_active          ),

  .x3_q_field_r        (x3_q_field_r       ),

  .x3_src0_nxt         (x3_src0_nxt        ),
  .x3_src1_nxt         (x3_src1_nxt        ),
  .x3_res_nxt          (x3_res_nxt         ),
  .x2_mem_addr_r       (x2_mem_addr_r      ),
  .x2_src0_pass        (x2_src0_pass       ),
  .x2_src1_pass        (x2_src1_pass       ),
  .x2_res_pass         (x2_res_pass        ),
  .x2_addr_pass        (x2_addr_pass       ),
  .dc2_addr_pass       (dc2_addr_pass      ),
  .dc2_aux_addr        (dc2_aux_addr       ),      

  .x3_code_nxt         (x3_code_nxt        ),
  .x3_target_nxt       (x3_target_nxt      ),
  .x3_zncv_nxt         (x3_zncv_nxt        ),
  
  .x3_done_r           (x3_done_r          ),
  .x3_read_r0_r        (x3_read_r0_r       ),
  .x3_read_r1_r        (x3_read_r1_r       ),
  .x3_enable           (x3_enable          ),
  .x3_retain           (x3_retain          ),
  .x2_pass             (x2_pass            ),
  .x3_pass             (x3_pass            ),
  
  .x3_late_pred_r      (x3_late_pred_r     ),
  
  .fwd_x3_r0_ca_w0_lo  (fwd_x3_r0_ca_w0_lo ),
  .fwd_x3_r0_ca_w1_lo  (fwd_x3_r0_ca_w1_lo ),
  .fwd_x3_r0_wa_w0_lo  (fwd_x3_r0_wa_w0_lo ),
  .fwd_x3_r0_wa_w1_lo  (fwd_x3_r0_wa_w1_lo ),
  
  .fwd_x3_r1_ca_w0_lo  (fwd_x3_r1_ca_w0_lo ),
  .fwd_x3_r1_ca_w1_lo  (fwd_x3_r1_ca_w1_lo ),
  .fwd_x3_r1_wa_w0_lo  (fwd_x3_r1_wa_w0_lo ),
  .fwd_x3_r1_wa_w1_lo  (fwd_x3_r1_wa_w1_lo ),
  .fwd_x3_r0_ca_w0_hi  (fwd_x3_r0_ca_w0_hi ),
  .fwd_x3_r0_wa_w0_hi  (fwd_x3_r0_wa_w0_hi ),
  .fwd_x3_r1_ca_w0_hi  (fwd_x3_r1_ca_w0_hi ),
  .fwd_x3_r1_wa_w0_hi  (fwd_x3_r1_wa_w0_hi ),
  .fwd_x3_r0_wa_w1_hi  (fwd_x3_r0_wa_w1_hi ),
  .fwd_x3_r1_wa_w1_hi  (fwd_x3_r1_wa_w1_hi ),
  .fwd_x3_r0_ca_w1_hi  (fwd_x3_r0_ca_w1_hi ),
  .fwd_x3_r1_ca_w1_hi  (fwd_x3_r1_ca_w1_hi ),
  .fwd_x3_r1h_ca_w0_lo (fwd_x3_r1h_ca_w0_lo),
  .fwd_x3_r1h_ca_w1_lo (fwd_x3_r1h_ca_w1_lo),
  .fwd_x3_r1h_wa_w0_lo (fwd_x3_r1h_wa_w0_lo), 
  .fwd_x3_r1h_wa_w1_lo (fwd_x3_r1h_wa_w1_lo),
  .fwd_x3_r1h_ca_w0_hi (fwd_x3_r1h_ca_w0_hi),
  .fwd_x3_r1h_wa_w0_hi (fwd_x3_r1h_wa_w0_hi),
  .fwd_x3_r1h_ca_w1_hi (fwd_x3_r1h_ca_w1_hi),
  .fwd_x3_r1h_wa_w1_hi (fwd_x3_r1h_wa_w1_hi),
  .ca_byp_data0_lo     (ca_byp_data0_lo    ),
  .ca_byp_data1_lo     (ca_byp_data1_lo    ),
  .wa_rf_wdata0_lo_r   (wa_rf_wdata0_lo_r  ),
  .wa_rf_wdata1_lo_r   (wa_rf_wdata1_lo_r  ),
  .ca_byp_data0_hi     (ca_byp_data0_hi    ),
  .wa_rf_wdata0_hi_r   (wa_rf_wdata0_hi_r  ),
  .ca_byp_data1_hi     (ca_byp_data1_hi    ),
  .wa_rf_wdata1_hi_r   (wa_rf_wdata1_hi_r  ),

  .x3_load_r           (x3_load_r          ),
  .x3_store_r          (x3_store_r         ),
  .x3_pref_r           (x3_pref_r          ),
  .x3_size_r           (x3_size_r          ),
  .x3_sex_r            (x3_sex_r           ),
  .x3_cache_byp_r      (x3_cache_byp_r     ),
  .x3_flag_op_r        (x3_flag_op_r       ),
  .x3_signed_op_r      (x3_signed_op_r     ),
  .x3_sync_op_r        (x3_sync_op_r       ),
  .x3_ei_op_r          (x3_ei_op_r         ),
  .x3_lr_op_r          (x3_lr_op_r         ),
  .x3_sr_op_r          (x3_sr_op_r         ),
  .x3_div_op_r         (x3_div_op_r        ),
  .x3_iprot_viol_r     (x3_iprot_viol_r    ),
  .x3_rtie_op_r        (x3_rtie_op_r       ),
  .x3_brk_op_r         (x3_brk_op_r        ),
  .x3_trap_op_r        (x3_trap_op_r       ),
  .x3_locked_r         (x3_locked_r        ),
  .x3_dmb_op_r         (x3_dmb_op_r        ),
  .x3_dmb_type_r       (x3_dmb_type_r      ),

  .x3_pref             (x3_pref            ),
  .x3_pref_l2          (x3_pref_l2         ),
  .x3_prefw            (x3_prefw           ),
  .x3_pre_alloc        (x3_pre_alloc       ),

  .x3_wa0_lpc_r        (x3_wa0_lpc_r       ),
  .x3_loop_op_r        (x3_loop_op_r       ),
  .x3_predicate_r      (x3_predicate_r     ),

  .x3_byp_data0        (x3_byp_data0       ),

  .x3_rf_ra0_r         (x3_rf_ra0_r        ),
  .x3_rf_ra1_r         (x3_rf_ra1_r        ),
  .x3_rf_wa0_r         (x3_rf_wa0_r        ),
  .x3_rf_wenb0_r       (x3_rf_wenb0_r      ),
  .x3_rf_wenb0_64_r    (x3_rf_wenb0_64_r   ),
  .x3_cc_byp_64_haz_r  (x3_cc_byp_64_haz_r ),
  .x3_rf_wa1_r         (x3_rf_wa1_r        ),
  .x3_rf_wenb1_r       (x3_rf_wenb1_r      ),
  .x3_rf_wenb1_64_r    (x3_rf_wenb1_64_r   ),
  .x3_rf_renb0_64_r    (x3_rf_renb0_64_r   ),
  .x3_rf_renb1_64_r    (x3_rf_renb1_64_r   ),
  .x3_acc_wenb_r       (x3_acc_wenb_r      ),

  .x3_mpy_op_r         (x3_mpy_op_r        ),
  .x3_half_size_r      (x3_half_size_r     ),
  .mp3_s_lo            (mp3_s_lo           ),
  .mp3_c_lo            (mp3_c_lo           ),
  .x3_acc_op_r         (x3_acc_op_r        ),
  .x3_dual_op_r        (x3_dual_op_r       ),
  .x3_vector_op_r      (x3_vector_op_r     ),
  .x3_macu_r           (x3_macu_r          ),
  .x3_quad_op_r        (x3_quad_op_r       ),

  .x3_dest_cr_is_ext_r (x3_dest_cr_is_ext  ),
  .x3_src0_r           (x3_src0_r          ),
  .x3_valid_nxt        (x3_valid_nxt       ),
  .x3_zncv_wen_r       (x3_zncv_wen_r      ),
  .x3_wevt_op          (x3_wevt_op         ),
  .ca_flag_wr_nxt      (ca_flag_wr_nxt     ),
  .ca_src0_nxt         (ca_src0_nxt        ),
  .ca_src1_nxt         (ca_src1_nxt        ),
  .ca_res_nxt          (ca_res_nxt         ),
  .ca_target_nxt       (ca_target_nxt      ),
  .ca_p0_nxt           (ca_p0_nxt          ),
  .ca_p1_nxt           (ca_p1_nxt          ),
  .ca_p2_nxt           (ca_p2_nxt          ),
  .ca_p3_nxt           (ca_p3_nxt          ),
  .ca_cin_nxt          (ca_cin_nxt         ),
  .x3_mem_addr_r       (x3_mem_addr_r      ),
  .x3_uop_inst_r       (x3_uop_inst_r      ),
  .x3_src0_pass        (x3_src0_pass       ),
  .x3_src1_pass        (x3_src1_pass       ),
  .x3_res_pass         (x3_res_pass        ),
  .x3_target_pass      (x3_target_pass     ),
  .x3_addr_pass        (x3_addr_pass       ),
  .x3_add_op_pass      (x3_add_op_pass     ),
  .x3_alu_code_pass    (x3_alu_code_pass   ),
  .x3_mask_src_pass    (x3_mask_src_pass   ),
  .ca_pc_inc_nxt       (ca_pc_inc_nxt      ),
  .ca_zncv_nxt         (ca_zncv_nxt        ),
  .ca_code_nxt         (ca_code_nxt        )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Commit Stage (alb_commit) module instantiation                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_commit u_alb_commit(
  .clk                   (clk                ),
  .rst_a                 (rst_a              ),
  .wa_restart_r          (wa_restart_r       ),
  .wa_restart_kill_r     (wa_restart_kill_r  ),
  .hlt_restart_r         (hlt_restart        ),
  .dc4_dtlb_miss_r       (dc4_dtlb_miss_r),
  .wa_jtlb_lookup_start_r (wa_jtlb_lookup_start_r),
  .wa_jtlb_cancel        (wa_jtlb_cancel     ),

  .db_active             (db_active          ),
  .db_active_r           (db_active_r        ),

  .ca_cmt_dbg_evt        (ca_cmt_dbg_evt     ),
  .holdup_excpn_r        (holdup_excpn_r     ),
  .ca_uop_active_set     (ca_uop_active_set),
  .ca_finish_sgl_step    (ca_finish_sgl_step ),
  .ca_cmt_norm_evt       (ca_cmt_norm_evt    ),
  .ca_cmt_uop_evt        (ca_cmt_uop_evt     ),
  .ca_cmt_brk_evt        (ca_cmt_brk_evt     ),
  .ca_cmt_isi_evt        (ca_cmt_isi_evt     ),
  .aps_break             (aps_break          ),  // 
  .aps_halt              (aps_halt           ),  // 
  .ca_sr_stall_rtie      (ca_sr_stall_rtie     ),
  .gb_sys_reset_done_r   (gb_sys_reset_done_r),
  .ar_pc_r               (ar_pc_r            ),
  .ar_aux_status32_r     (ar_aux_status32_r  ),
  .ar_aux_user_mode_r    (ar_aux_user_mode_r ),
  .ar_aux_erstatus_r     (ar_aux_erstatus_r  ),
  .int_load_active       (int_load_active    ),

  .ar_aux_bta_r          (ar_aux_bta_r       ),
  .ar_aux_lp_start_r     (ar_aux_lp_start_r  ),
  .ar_aux_debug_r        (ar_aux_debug_r     ),
  .ar_tags_empty_r       (ar_tags_empty_r    ),
  .ca_flag_wr_nxt        (ca_flag_wr_nxt     ),
  .ca_src0_nxt           (ca_src0_nxt        ),
  .ca_src1_nxt           (ca_src1_nxt        ),
  .ca_res_nxt            (ca_res_nxt         ),
  .ca_target_nxt         (ca_target_nxt      ),
  .ca_target_r           (ca_target_r        ),
  .x3_mem_addr_r         (x3_mem_addr_r      ),
  .x3_src0_pass          (x3_src0_pass       ),
  .x3_src1_pass          (x3_src1_pass       ),
  .x3_res_pass           (x3_res_pass        ),
  .x3_target_pass        (x3_target_pass     ),
  .x3_addr_pass          (x3_addr_pass       ),
  .x3_add_op_pass        (x3_add_op_pass     ),
  .x3_alu_code_pass      (x3_alu_code_pass   ),
  .ca_pc_inc_nxt         (ca_pc_inc_nxt      ),
  .ca_zncv_nxt           (ca_zncv_nxt        ),
  .ca_code_nxt           (ca_code_nxt        ),
  .ca_p0_nxt             (ca_p0_nxt          ),
  .ca_p1_nxt             (ca_p1_nxt          ),
  .ca_p2_nxt             (ca_p2_nxt          ),
  .ca_p3_nxt             (ca_p3_nxt          ),
  .ca_cin_nxt            (ca_cin_nxt         ),
  .ca_pass               (ca_pass            ),
  .ca_pass_no_iprot      (ca_pass_no_iprot   ),
  .ca_enable             (ca_enable          ),
  .ca_stall              (ca_stall           ),
  .ca_valid_r            (ca_valid_r         ),
  .ca_done_r             (ca_done_r          ),
  .x3_pass               (x3_pass            ),
  
  .ca_valid_nxt          (ca_valid_nxt       ),
  .ca_wa1_conflict       (ca_wa1_conflict    ),
  .commit_inst           (commit_inst        ),
  .ca_q_cond             (ca_q_cond          ),

  .ca_with_carry_r       (ca_with_carry_r    ),

  .eia_ext_cond          (eia_ca_ext_cond     ),
  .ca_eia_res_valid      (eia_exu_ca_res_valid), 
  .ca_eia_res_data       (eia_exu_ca_res_data ),  
  .ca_eia_res_data_hi    (eia_exu_ca_res_data_hi ),  
  .ca_eia_res_flags      (eia_exu_ca_res_flags), 
  .ca_dest_cr_is_ext_r   (ca_dest_cr_is_ext   ),

  .ca_writes_acc_r       (ca_writes_acc_r    ),
  .ca_acc_wenb_r         (ca_acc_wenb_r      ),
  .ca_locked_r           (ca_locked_r        ),
  .ca_wlfc_op            (ca_wlfc_op         ),
  .ca_q_field_r          (ca_q_field_r       ),

  .ca_grad_req           (ca_grad_req        ),
  .dp_retire_rf_wenb     (dp_retire_rf_wenb  ),
  .dp_retire_rf_wa       (dp_retire_rf_wa    ),
  .dp_retire_zncv        (dp_retire_zncv     ),
  .ar_zncv_upt_r         (ar_zncv_upt_r      ),
  .dp_retire_rf_64       (dp_retire_rf_64    ),
  .dp_retire_writes_acc  (dp_retire_writes_acc),
  .dmp_retire_req        (dmp_retire_req     ),
  .dmp_retire_tag        (dmp_retire_tag     ),
  .dmp_scond_zflag       (dmp_scond_zflag    ),
  .dp_retire_scond       (dp_retire_scond    ),
  .dmp_retire_ack        (dmp_retire_ack     ),
  
  .div_retire_req        (div_retire_req     ),
  .div_retire_tag        (div_retire_tag     ),
  .div_rf_wdata_lo       (div_rf_wdata_lo    ),
  .div_retire_ovfl       (div_retire_overflow_r),
  .div_retire_sign       (div_retire_sign_r  ),
  .div_retire_zero       (div_retire_zero_r  ),
  .div_retire_ack        (div_retire_ack     ),

  .eia_retire_req        (eia_retire_req     ),
  .eia_retire_tag        (eia_retire_tag     ),
  .eia_rf_wdata_lo       (eia_retire_wdata_lo),
  .eia_retire_flags      (eia_retire_flags   ),
  .eia_retire_ack        (eia_retire_ack     ),

  .eia_disable_w0        (eia_exu_grad_req   ),

  .do_aux_replay_r         (do_aux_replay_r      ),
  .ca_retire_req         (ca_retire_req      ),
  .ca_retire_tag         (ca_retire_tag      ),
  .ca_retire_ack         (ca_retire_ack      ),
  
  .byp_acc_hi            (byp_acc_hi         ),
  .ca_acch_res           (ca_acch_res        ),
  .fwd_ca_r0_wa_w0_lo    (fwd_ca_r0_wa_w0_lo ),
  .fwd_ca_r0_wa_w1_lo    (fwd_ca_r0_wa_w1_lo ),
  .fwd_ca_r1_wa_w0_lo    (fwd_ca_r1_wa_w0_lo ),
  .fwd_ca_r1_wa_w1_lo    (fwd_ca_r1_wa_w1_lo ),
  .fwd_ca_r0_wa_w0_hi    (fwd_ca_r0_wa_w0_hi ),
  .fwd_ca_r1_wa_w0_hi    (fwd_ca_r1_wa_w0_hi ),
  .fwd_ca_r0_wa_w1_hi    (fwd_ca_r0_wa_w1_hi ),
  .fwd_ca_r1_wa_w1_hi    (fwd_ca_r1_wa_w1_hi ),
  .fwd_ca_r1h_wa_w0_lo   (fwd_ca_r1h_wa_w0_lo),
  .fwd_ca_r1h_wa_w1_lo   (fwd_ca_r1h_wa_w1_lo),
  .fwd_ca_r1h_wa_w0_hi   (fwd_ca_r1h_wa_w0_hi),
  .fwd_ca_r1h_wa_w1_hi   (fwd_ca_r1h_wa_w1_hi),
  .wa_rf_wdata0_lo_r     (wa_rf_wdata0_lo_r  ),
  .wa_rf_wdata1_lo_r     (wa_rf_wdata1_lo_r  ),
  .wa_rf_wdata0_hi_r     (wa_rf_wdata0_hi_r  ),
  .wa_rf_wdata1_hi_r     (wa_rf_wdata1_hi_r  ),
  .wa_cmt_norm_evt_r     (wa_cmt_norm_evt_r  ),

  .ca_fragged_r          (ca_fragged_r       ),
  .ca_error_branch_r     (ca_error_branch_r  ),
  .dc4_replay            (dc4_q_replay       ),
  .dc4_excpn             (dc4_excpn          ),
  .dc4_excpn_type        (dc4_excpn_type     ),

  .ca_br_type_r          (ca_br_type_r       ),

  .ca_zol_lp_jmp         (ca_zol_lp_jmp      ),
 
  .aux_ca_lr_data        (aux_ca_lr_data     ),
  .aux_ca_serial_sr      (aux_ca_serial_sr   ),
  .aux_ca_strict_sr      (aux_ca_strict_sr   ),
  .wa_sr_data_r          (wa_sr_data_r       ),
  .wa_status32_wen       (wa_status32_wen    ),
  .wa_debug_wen          (wa_debug_wen       ),
  .wa_pc_wen             (wa_aux_pc_wen      ),
  .ca_in_kflag           (ca_in_kflag        ),

  .rtc_na                (rtc_na             ),

  .dc4_write_data_lo     (dc4_write_data_lo  ),
  .dc4_write_data_hi     (dc4_write_data_hi  ),
  .dmp_dc4_rf_wdata_lo   (dmp_dc4_rf_wdata_lo),
  .dmp_dc4_rf_wdata_hi   (dmp_dc4_rf_wdata_hi),
  .mp4_s_hi_r            (mp4_s_hi_r         ),
  .mp4_c_hi_r            (mp4_c_hi_r         ),
  .mp4_s_65_r            (mp4_s_65_r         ),
  .mp4_c_65_r            (mp4_c_65_r         ),
  .ca_src0_r             (ca_src0_r          ),
  .ca_src1_r             (ca_src1_r          ),
  .ca_byp_data0_lo       (ca_byp_data0_lo    ),
  .ca_byp_data1_lo       (ca_byp_data1_lo    ),
  .ca_byp_data0_hi       (ca_byp_data0_hi    ),
  .ca_byp_data1_hi       (ca_byp_data1_hi    ),
  .ca_mem_addr_r         (ca_mem_addr_r      ),
  .ca_phys_addr_r        (ca_phys_addr_r     ),
  .ca_fast_op_r          (ca_fast_op_r       ),
  .ca_load_r             (ca_load_r          ),
//  .ca_pref_r             (ca_pref_r          ),
  .ca_store_r            (ca_store_r         ),
  .ca_uop_inst_r         (ca_uop_inst_r      ),
  .ca_size_r             (ca_size_r          ),
  .ca_sex_r              (ca_sex_r           ),
  .ca_cache_byp_r        (ca_cache_byp_r     ),
  .ca_pref               (ca_pref            ),   
  .ca_pref_l2            (ca_pref_l2         ),   
  .ca_prefw              (ca_prefw           ),   
  .ca_pre_alloc          (ca_pre_alloc       ), 
  .ca_zncv_wen_r         (ca_zncv_wen_r      ),
  .ca_dslot_r            (ca_dslot_r         ),
  .ca_jump_r             (ca_jump_r          ),
  .ca_bcc_r             (ca_bcc_r            ),
  .ca_brcc_bbit_r       (ca_brcc_bbit_r      ),
  .ca_lr_op_r            (ca_lr_op_r         ),
  .ca_sr_op_r            (ca_sr_op_r         ),
  .ca_aux_cond           (ca_aux_cond        ),
  .ca_in_deslot          (ca_in_deslot       ),
  .ca_ei_op_r            (ca_ei_op_r         ),
  .cmt_ei_evt            (cmt_ei_evt         ),
  .ca_in_eslot_r         (ca_in_eslot_r      ),
  .ca_btab_op_r          (ca_btab_op_r       ),
  .ca_dmb_op_r           (ca_dmb_op_r        ),
  .ca_dmb_type_r         (ca_dmb_type_r      ),
  .ca_br_evt             (ca_br_evt          ),

  .ca_has_limm_r         (ca_has_limm_r      ),
  .ca_is_16bit           (ca_is_16bit_r      ),
  .ca_br_jmp_op          (ca_br_jmp_op       ),
  .ca_lp_lpcc_evt                            (ca_lp_lpcc_evt),
  .commit_normal_evt     (commit_normal_evt  ),
  .ca_cond_inst          (ca_cond_inst       ),
  .ca_cond_met           (ca_cond_met        ),
  .ca_br_or_jmp_all      (ca_br_or_jmp_all   ),
  .ca_indir_br           (ca_indir_br        ),
  .ca_cmt_brk_inst       (ca_cmt_brk_inst    ),
  .rtt_leave_uop_cmt     (rtt_leave_uop_cmt  ),
  .rtt_dmp_retire        (rtt_dmp_retire     ),
  .rtt_dmp_null_ret      (rtt_dmp_null_ret   ),
  .rtt_ca_pref           (rtt_ca_pref        ), // load with null dest for trace
  .dmp_retire_is_load    (dmp_retire_is_load ),
  .rtt_ca_scond          (rtt_ca_scond       ),

  .ca_trap_op_r          (ca_trap_op_r       ),
  .ca_rtie_op_r          (ca_rtie_op_r       ),
  .ca_enter_op           (ca_enter_op_r      ),
  .ca_uop_active_r       (ca_uop_active_r    ),
  .ca_uop_active_nxt     (ca_uop_active_nxt  ),
  .ca_uop_predictable_r  (ca_uop_predictable_r),
  .ca_uop_enter_r        (ca_uop_enter_r ),
  .ca_uop_inprol_r       (ca_uop_inprol_r    ),
  .ca_uop_commit_r       (ca_uop_commit_r    ),
  .ca_byte_size_r        (ca_byte_size_r     ),
  .ca_cond               (ca_cond            ),
  .ca_seq_pc_nxt         (ca_seq_pc_nxt      ),
  .ca_aux_s32_stall      (ca_aux_s32_stall   ),
  .ca_loop_evt           (ca_loop_evt        ),
  .ca_sleep_evt          (ca_sleep_evt       ),
  .ca_wevt_evt           (ca_wevt_evt        ),
  .ca_wlfc_evt           (ca_wlfc_evt        ),
  .ca_kflag_op           (ca_kflag_op        ),
  .ca_brk_op_r           (ca_brk_op_r        ),
  .ca_div_op_r           (ca_div_op_r        ),
  .ca_mpy_op_r           (ca_mpy_op_r        ),
  .ca_vector_op_r        (ca_vector_op_r     ),
  .ca_macu_r             (ca_macu_r          ),
  .sel_byp_acc           (sel_byp_acc        ),
  .ca_grad_rf_wa1        (ca_grad_rf_wa1     ),
  .ca_retire_flags       (ca_retire_flags    ),
  .ca_iprot_viol_r       (ca_iprot_viol_r    ),
  .ca_predicate_r        (ca_predicate_r     ),
  .ca_wa0_lpc_r          (ca_wa0_lpc_r       ),
  .ca_loop_op_r          (ca_loop_op_r       ),
  .ca_branch_evt         (ca_branch_evt      ),
  
  .ca_br_direction       (ca_br_direction    ),
  .ca_br_target          (ca_br_target       ),
  .ca_lp_end_nxt         (ca_lp_end_nxt      ),
  .ca_br_fall_thru       (ca_br_fall_thru    ),
  .ca_br_taken           (ca_br_taken        ),
  .ca_br_or_jmp          (ca_br_or_jmp       ),
  .ca_iprot_replay       (ca_iprot_replay    ),
  .ca_leave_op_r         (ca_leave_op_r      ),
  .ca_uop_inst           (ca_uop_inst        ),
  
  .ca_tail_pc_3          (ca_tail_pc_3       ),

  .excpn_restart         (excpn_restart      ),
  .excpn_restart_pc      (excpn_restart_pc   ),
  .excpn_evts            (excpn_evts         ),
  .ct_excpn_trap_r       (ct_excpn_trap_r    ),
  .int_evts              (int_evts           ),

  .wa_lock_flag_r        (wa_lock_flag_r     ),
  .hlt_do_halt           (hlt_do_halt        ),
  .hlt_do_unhalt         (hlt_do_unhalt      ),
  .ca_triple_fault_set   (ca_triple_fault_set),
  .ct_replay             (ct_replay          ),
  .ca_rf_ra0_r           (ca_rf_ra0_r        ),
  .ca_rf_ra1_r           (ca_rf_ra1_r        ),
  .ca_rf_wa0_r           (ca_rf_wa0_r        ),
  .ca_rf_wenb0_r         (ca_rf_wenb0_r      ),
  .wa_rf_wa1_nxt         (wa_rf_wa1_nxt      ),
  .wa_rf_wenb1_nxt       (wa_rf_wenb1_nxt    ),
  .wa_rf_wuop_nxt        (wa_rf_wuop_nxt     ), 
  .wa_rf_wenb1_64_nxt    (wa_rf_wenb1_64_nxt ),
  .wa_rf_wdata1_hi_nxt   (wa_rf_wdata1_hi_nxt),
  .ca_data1_hi_pass      (ca_data1_hi_pass   ),
  .wa_rf_wdata0_lo_nxt   (wa_rf_wdata0_lo_nxt),
  .ca_data0_lo_pass      (ca_data0_lo_pass   ),
  .ca_rf_wenb0_64_r      (ca_rf_wenb0_64_r   ),
  .ca_cc_byp_64_haz_r    (ca_cc_byp_64_haz_r ),
  .wa_rf_wdata0_hi_nxt   (wa_rf_wdata0_hi_nxt),
  .ca_data0_hi_pass      (ca_data0_hi_pass   ),
  .ca_rf_wa1_r           (ca_rf_wa1_r        ),
  .ca_rf_wenb1_r         (ca_rf_wenb1_r      ),
  .wa_rf_wdata1_lo_nxt   (wa_rf_wdata1_lo_nxt),
  .ca_data1_lo_pass      (ca_data1_lo_pass   ),
  .ca_rf_wenb1_64_r      (ca_rf_wenb1_64_r   ),
  .ca_rf_renb0_64_r      (ca_rf_renb0_64_r   ),
  .ca_rf_renb1_64_r      (ca_rf_renb1_64_r   ),
  .wa_rf_wenb0_64_nxt    (wa_rf_wenb0_64_nxt ),
  .wa_cmt_norm_evt_nxt   (wa_cmt_norm_evt_nxt),
  .wa_cmt_uop_evt_nxt    (wa_cmt_uop_evt_nxt ),
  .wa_cmt_flag_evt_nxt   (wa_cmt_flag_evt_nxt),
  .wa_lf_set_nxt         (wa_lf_set_nxt      ),
  .wa_lf_clear_nxt       (wa_lf_clear_nxt    ),
  .wa_lf_double_nxt      (wa_lf_double_nxt   ),
  .wa_lpa_nxt            (wa_lpa_nxt         ),
  .wa_code_nxt           (wa_code_nxt        ),
  .ar_pc_nxt             (ar_pc_nxt          ),
  .ar_pc_pass            (ar_pc_pass         ),
  .wa_aux_status32_nxt   (wa_aux_status32_nxt),
  .wa_aux_uop_flag_pass  (wa_aux_uop_flag_pass),
  .wa_aux_flags_pass     (wa_aux_flags_pass   ),
  .wa_aux_status32_pass  (wa_aux_status32_pass)
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Writeback Stage (alb_writeback) module instantiation                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_writeback u_alb_writeback(
  .clk                   (clk                  ),
  .rst_a                 (rst_a                ),
  .ar_aux_status32_r     (ar_aux_status32_r    ),
  .ar_aux_user_mode_r    (ar_aux_user_mode_r   ),
  .ar_pc_r               (ar_pc_r              ),
  .wa_cmt_norm_evt_nxt   (wa_cmt_norm_evt_nxt  ),
  .wa_cmt_uop_evt_nxt    (wa_cmt_uop_evt_nxt   ),
  .wa_cmt_flag_evt_nxt   (wa_cmt_flag_evt_nxt  ),
  .wa_lf_set_nxt         (wa_lf_set_nxt        ),
  .wa_lf_clear_nxt       (wa_lf_clear_nxt      ),
  .wa_lf_double_nxt      (wa_lf_double_nxt     ),
  .wa_lpa_nxt            (wa_lpa_nxt           ),
  .wa_code_nxt           (wa_code_nxt          ),
  .ar_pc_nxt             (ar_pc_nxt            ),
  .ar_pc_pass            (ar_pc_pass           ),
  .wa_aux_status32_nxt   (wa_aux_status32_nxt  ),
  .wa_aux_uop_flag_pass  (wa_aux_uop_flag_pass ),
  .wa_aux_flags_pass     (wa_aux_flags_pass    ),
  .wa_aux_status32_pass  (wa_aux_status32_pass ),
  .wa_rf_wa1_nxt         (wa_rf_wa1_nxt        ),
  .wa_rf_wenb1_nxt       (wa_rf_wenb1_nxt      ),
  .wa_rf_wuop_nxt        (wa_rf_wuop_nxt       ), 
  .wa_rf_wenb1_64_nxt    (wa_rf_wenb1_64_nxt   ),
  .wa_rf_wdata1_hi_nxt   (wa_rf_wdata1_hi_nxt  ),
  .ca_data1_hi_pass      (ca_data1_hi_pass     ),
  .wa_rf_wdata0_lo_nxt   (wa_rf_wdata0_lo_nxt  ),
  .ca_data0_lo_pass      (ca_data0_lo_pass     ),
  .wa_rf_wdata1_lo_nxt   (wa_rf_wdata1_lo_nxt  ),
  .ca_data1_lo_pass      (ca_data1_lo_pass     ),
  .wa_rf_wdata0_hi_nxt   (wa_rf_wdata0_hi_nxt  ),
  .ca_data0_hi_pass      (ca_data0_hi_pass     ),
  .ca_uop_active_r       (ca_uop_active_r      ),
  .ca_uop_inprol_r       (ca_uop_inprol_r      ),
  .wa_valid_r            (wa_valid_r           ),
  .wa_enable             (wa_enable            ),
  .ca_pass               (ca_pass              ),
  .ca_tail_pc_3          (ca_tail_pc_3         ),
  .x2_pg_xing_dslot_r    (x2_pg_xing_dslot_r   ),
  .mpd_pc                (mpd_pc               ),
  .ca_fragged_r          (ca_fragged_r         ),
  .wa_restart_kill_r     (wa_restart_kill_r    ),
  .sp_kinv_r             (sp_kinv_r            ),
  .int_rtie_replay_r     (int_rtie_replay_r    ),
  .excpn_restart         (excpn_restart        ),
  .wa_pc                 (wa_pc                ),
  .wa_tail_pc_3          (wa_tail_pc_3         ),
  .wa_dslot              (wa_dslot             ),

  .wa_sr_op_r            (wa_sr_op_r           ),
  .wa_store_r            (wa_store_r           ),
  .wa_sleep              (wa_sleep_r           ),
  .dmp_clear_lf          (dmp_clear_lf         ),
  .wa_lr_op_r            (wa_lr_op_r           ),
  .rtt_wa_spl_ld         (rtt_wa_spl_ld        ),
  .rtt_wa_store          (rtt_wa_store         ),
  .rtt_ca_scond          (rtt_ca_scond         ),
  .rtt_dc4_scond_go      (rtt_dc4_scond_go     ),  // scond will be success
  .wa_pref_r             (wa_pref_r            ),
  .wa_load_r             (wa_load_r            ),

  .wa_sr_data_r          (wa_sr_data_r         ),
  .wa_aux_status32_r     (wa_aux_status32_r    ),

  .wa_valid_nxt          (wa_valid_nxt         ),
  
  .wa_wa0_lpc_r          (wa_wa0_lpc_r         ),
  .wa_loop_op_r          (wa_loop_op_r         ),

  .smt_cap_rst_vec       (smt_cap_rst_vec      ),
  .ar_pc_save_r          (ar_pc_save_r         ),

  .ar_save_clk    (ar_save_clk  ),
  .ar_save_en_r   (ar_save_en_r ),

  .ca_acch_res           (ca_acch_res          ),
  .accl_r                (accl_r               ),
  .acch_r                (acch_r               ),
  .byp_acc_lo            (byp_acc_lo           ),
  .byp_acc_hi            (byp_acc_hi           ),
  .wa_accl_nxt           (wa_accl_nxt          ),
  .wa_acch_nxt           (wa_acch_nxt          ),
  .wa_acc_wenb           (wa_acc_wenb          ),

  .wa_uopld_jli_base     (wa_uopld_jli_base    ),
  .wa_uopld_ldi_base     (wa_uopld_ldi_base    ),
  .wa_uopld_ei_base      (wa_uopld_ei_base     ),
  .wa_uopld_lp_count     (wa_uopld_lp_count    ),
  .wa_uopld_lp_start     (wa_uopld_lp_start    ),
  .wa_uopld_lp_end       (wa_uopld_lp_end      ),
  .wa_uopld_status32     (wa_uopld_status32    ),

  .wa_uopld_data         (wa_uopld_data        ),


  .wa_cmt_norm_evt_r     (wa_cmt_norm_evt_r    ),  
  .wa_cmt_flag_evt_r     (wa_cmt_flag_evt_r    ),  

  .wa_rf_wdata0_hi_r     (wa_rf_wdata0_hi_r    ),
  .wa_rf_wenb0_64_r      (wa_rf_wenb0_64_r     ),
  .wa_cc_byp_64_haz_r    (wa_cc_byp_64_haz_r   ),
  .wa_rf_wa0_r           (wa_rf_wa0_r          ),
  .wa_rf_wdata0_lo_r     (wa_rf_wdata0_lo_r    ),
  .wa_rf_wenb0_r         (wa_rf_wenb0_r        ),
  .wa_rf_wdata1_hi_r     (wa_rf_wdata1_hi_r    ),
  .wa_rf_wenb1_64_r      (wa_rf_wenb1_64_r     ),
  .wa_writes_acc_r       (wa_writes_acc_r      ),
  .wa_acc_wenb_r         (wa_acc_wenb_r        ),
  .wa_lock_flag_r        (wa_lock_flag_r       ),
  .wa_lock_double_r      (wa_lock_double_r     ),
  .wa_lpa_r              (wa_lpa_r             ),
  .wa_rf_wa1_r           (wa_rf_wa1_r          ),
  .wa_rf_wdata1_lo_r     (wa_rf_wdata1_lo_r    ),



  .wa_rf_wenb1_r         (wa_rf_wenb1_r        )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Dependency Pipeline (alb_dep_pipe) module instantiation                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_dep_pipe u_alb_dep_pipe (
  .clk                   (clk                  ),
  .rst_a                 (rst_a                ),
  .da_valid_r            (da_valid_r           ),
  .da_uop_busy_r         (da_uop_busy_r        ),
  .da_uop_prol_r         (da_uop_prol_r        ),
  .da_uop_is_excpn_r     (da_uop_is_excpn_r    ),
  .da_uop_is_sirq_r      (da_uop_is_sirq_r     ),
  .int_load_active       (int_load_active      ),
  .da_eslot_stall        (da_eslot_stall       ),
  .da_ei_op              (da_ei_op             ),
  .da_ldi_src0           (da_ldi_src0          ),
  .da_jli_src0           (da_jli_src0          ),
  .da_zncv_wen           (da_zncv_wen          ),
  .da_rtie_op_r          (da_rtie_op_r         ),
  .int_in_prologue        (int_evts[`npuarc_INTEVT_INPROL]),

  .da_rtt_stall_r        (da_rtt_stall_r       ),
  .sa_flag_stall         (sa_flag_stall        ),
  .sa_stall_r1           (sa_stall_r1          ),
  .sa_stall_r15          (sa_stall_r15         ),
  
  .sa_acc_raw            (sa_acc_raw           ),
  .ca_acc_waw            (ca_acc_waw           ),

  .sa_valid_nxt          (sa_valid_nxt         ),
  .sa_opds_in_sa_r       (sa_opds_in_sa_r      ),
  .sa_agu_uses_r0_r      (sa_agu_uses_r0_r     ),
  .sa_agu_uses_r1_r      (sa_agu_uses_r1_r     ),
  .sa_dslot_r            (sa_dslot_r           ),
  .sa_link_r             (sa_link_r            ),
  .sa_store_r            (sa_store_r           ),
  .sa_load_r             (sa_load_r            ),
  .sa_dmb_op_r           (sa_dmb_op_r          ),
  .sa_dmb_type_r         (sa_dmb_type_r        ),
  .sa_dsync_op_r         (sa_dsync_op_r        ),
  .sa_dmb_stall          (sa_dmb_stall         ),     
  .sa_ei_op_r            (sa_ei_op_r           ),
  .sa_sr_op_r            (sa_sr_op_r           ),
  .sa_ldi_src0_r         (sa_ldi_src0_r        ),
  .sa_jli_src0_r         (sa_jli_src0_r        ),
  .sa_zncv_wen_r         (sa_zncv_wen_r        ),
  .sa_q_field_r          (sa_q_field_r         ),
  .sa_with_carry_r       (sa_with_carry_r      ),
  .sa_reads_acc_r        (sa_reads_acc_r       ),
  .eia_grad_rf_64        (eia_grad_rf_64       ),
  .sa_flags_ready        (sa_flags_ready       ),
  .sa_eia_hazard         (eia_sa_hazard        ),
  .ca_dest_cr_is_ext_r   (ca_dest_cr_is_ext    ),
  .gb_dest_cr_is_ext     (gb_dest_cr_is_ext    ),
  .ar0_rf_valid_r     (ar0_rf_valid_r    ),
  .ar0_rf_wenb1_r     (ar0_rf_wenb1_r    ),
  .ar0_rf_wa1_r       (ar0_rf_wa1_r      ),  
  .ar0_rf_wenb1_64_r  (ar0_rf_wenb1_64_r ),
  .ar0_dest_cr_is_ext (ar0_dest_cr_is_ext),  
  .ar1_rf_valid_r     (ar1_rf_valid_r    ),
  .ar1_rf_wenb1_r     (ar1_rf_wenb1_r    ),
  .ar1_rf_wa1_r       (ar1_rf_wa1_r      ),  
  .ar1_rf_wenb1_64_r  (ar1_rf_wenb1_64_r ),
  .ar1_dest_cr_is_ext (ar1_dest_cr_is_ext),  
  .ar2_rf_valid_r     (ar2_rf_valid_r    ),
  .ar2_rf_wenb1_r     (ar2_rf_wenb1_r    ),
  .ar2_rf_wa1_r       (ar2_rf_wa1_r      ),  
  .ar2_rf_wenb1_64_r  (ar2_rf_wenb1_64_r ),
  .ar2_dest_cr_is_ext (ar2_dest_cr_is_ext),  
  .ar3_rf_valid_r     (ar3_rf_valid_r    ),
  .ar3_rf_wenb1_r     (ar3_rf_wenb1_r    ),
  .ar3_rf_wa1_r       (ar3_rf_wa1_r      ),  
  .ar3_rf_wenb1_64_r  (ar3_rf_wenb1_64_r ),
  .ar3_dest_cr_is_ext (ar3_dest_cr_is_ext),  
  .ar4_rf_valid_r     (ar4_rf_valid_r    ),
  .ar4_rf_wenb1_r     (ar4_rf_wenb1_r    ),
  .ar4_rf_wa1_r       (ar4_rf_wa1_r      ),  
  .ar4_rf_wenb1_64_r  (ar4_rf_wenb1_64_r ),
  .ar4_dest_cr_is_ext (ar4_dest_cr_is_ext),  
  .ar5_rf_valid_r     (ar5_rf_valid_r    ),
  .ar5_rf_wenb1_r     (ar5_rf_wenb1_r    ),
  .ar5_rf_wa1_r       (ar5_rf_wa1_r      ),  
  .ar5_rf_wenb1_64_r  (ar5_rf_wenb1_64_r ),
  .ar5_dest_cr_is_ext (ar5_dest_cr_is_ext),  
  .ar6_rf_valid_r     (ar6_rf_valid_r    ),
  .ar6_rf_wenb1_r     (ar6_rf_wenb1_r    ),
  .ar6_rf_wa1_r       (ar6_rf_wa1_r      ),  
  .ar6_rf_wenb1_64_r  (ar6_rf_wenb1_64_r ),
  .ar6_dest_cr_is_ext (ar6_dest_cr_is_ext),  
  .ar7_rf_valid_r     (ar7_rf_valid_r    ),
  .ar7_rf_wenb1_r     (ar7_rf_wenb1_r    ),
  .ar7_rf_wa1_r       (ar7_rf_wa1_r      ),  
  .ar7_rf_wenb1_64_r  (ar7_rf_wenb1_64_r ),
  .ar7_dest_cr_is_ext (ar7_dest_cr_is_ext),  

  .aux_x2_r4_sr          (aux_x2_r4_sr         ),
  .aux_x3_r4_sr_r        (aux_x3_r4_sr_r       ),
  .aux_ca_r4_sr_r        (aux_ca_r4_sr_r       ),

  .sa_is_predicted_r     (sa_is_predicted_r    ),
  .sa_with_dslot_r       (sa_with_dslot_r      ),  
  .sa_error_branch_r     (sa_error_branch_r    ),
  .sa_zol_stall          (sa_zol_stall         ),
  .x1_zol_stall          (x1_zol_stall         ),
  .x1_valid_nxt          (x1_valid_nxt         ),
  .x1_load_r             (x1_load_r            ),
  .x1_store_r            (x1_store_r           ),
  .x1_fast_op_r          (x1_fast_op_r         ),
  .x1_eia_op_r           (eia_exu_x1_eia_op    ),
  .ca_eia_op_r           (eia_exu_ca_eia_op    ),
  .x1_eia_fast_op_r      (eia_exu_x1_fast_op_r ),
  .x1_eia_hold           (eia_exu_x1_hold      ), 
  .sa_eia_hold           (eia_exu_sa_hold      ),
  .x2_eia_hold           (eia_exu_x2_hold      ),
  .x1_slow_op_r          (x1_slow_op_r         ),
  .x1_zncv_wen_r         (x1_zncv_wen_r        ),
  .x1_flag_op_r          (x1_flag_op_r         ),
  .x1_brk_op_r           (x1_brk_op_r          ),
  .x1_sleep_op_r         (x1_sleep_op_r        ),
  .x1_cond               (x1_cond              ),
  .x1_q_field_r          (x1_q_field_r         ),
  .x1_signed_op_r        (x1_signed_op_r       ),
  .x1_opds_in_sa_r       (x1_opds_in_sa_r      ),
  .x1_opds_in_x1_r       (x1_opds_in_x1_r      ),
  .x1_agu_uses_r0_r      (x1_agu_uses_r0_r     ),
  .x1_sr_op_r            (x1_sr_op_r           ),
  .x1_uop_commit_r       (x1_uop_commit_r      ),
  .x1_uop_prol_r         (x1_uop_prol_r        ),
  .x1_uop_epil_r         (x1_uop_epil_r        ),
  .x1_with_carry_r       (x1_with_carry_r      ),
  .x1_grab_src0          (x1_grab_src0         ),
  .x1_grab_src1          (x1_grab_src1         ),
  .x1_grab_src2          (x1_grab_src2         ),
  .x1_grab_src3          (x1_grab_src3         ),
  .x1_rgf_link_r         (x1_rgf_link_r        ),
  .x1_dmb_op_r           (x1_dmb_op_r          ),
  .x1_dmb_type_r         (x1_dmb_type_r        ),
  .x1_div_op_r           (x1_div_op_r          ),
  .div_busy_r            (div_busy_r           ),

  .x2_valid_nxt          (x2_valid_nxt         ),
  .x2_q_field_r          (x2_q_field_r         ),
  .x2_zncv_wen_r         (x2_zncv_wen_r        ),
  .x2_wevt_op            (x2_wevt_op           ),
  .x2_brk_op_r           (x2_brk_op_r          ), 
  .x2_slow_op_r          (x2_slow_op_r         ),
  .x2_flag_op_r          (x2_flag_op_r         ),
  .x2_signed_op_r        (x2_signed_op_r       ),
  .x2_dslot_r            (x2_dslot_r           ),
  .x2_sync_op_r          (x2_sync_op_r         ),
  .x2_load_r             (x2_load_r            ),
  .x2_store_r            (x2_store_r           ),
  .x2_excpn_stall        (x2_excpn_stall       ),
  .x2_sc_stall           (x2_sc_stall          ),  //
  .dp_x2_sp_r            (dp_x2_sp_r           ),
  .x2_locked_r           (x2_locked_r          ),
  .x2_dmb_op_r           (x2_dmb_op_r          ),
  .x2_dmb_type_r         (x2_dmb_type_r        ),
  .x2_sr_op_r            (x2_sr_op_r           ),
  .x2_pg_xing_replay_r   (x2_pg_xing_replay_r  ),
  .x2_exu_stall          (x2_exu_stall         ),
  .dmp_dc3_stall_r       (dmp_dc3_stall_r      ),
  .x3_valid_nxt          (x3_valid_nxt         ),
  .x3_q_field_r          (x3_q_field_r         ),
  .x3_zncv_wen_r         (x3_zncv_wen_r        ),
  .x3_flag_op_r          (x3_flag_op_r         ),
  .x3_signed_op_r        (x3_signed_op_r       ), 
  .aux_x3_stall          (aux_x3_stall         ),
  .wdt_x3_stall          (wdt_x3_stall         ),
  .x3_sync_op_r          (x3_sync_op_r         ),
  .x3_rtie_op_r          (x3_rtie_op_r         ),
  .x3_brk_op_r           (x3_brk_op_r          ),
  .x3_trap_op_r          (x3_trap_op_r         ),
  .x3_locked_r           (x3_locked_r          ),
  .x3_store_r            (x3_store_r           ),
  .x3_vector_op_r        (x3_vector_op_r       ),
  .x3_macu_r             (x3_macu_r            ),
  .x3_dmb_op_r           (x3_dmb_op_r          ),
  .x3_dmb_type_r         (x3_dmb_type_r        ),
  .x3_load_r             (x3_load_r            ),
  .x3_sr_op_r            (x3_sr_op_r           ),
  .x3_wevt_op            (x3_wevt_op           ),
  .ca_valid_nxt          (ca_valid_nxt         ),
  .ca_q_cond             (ca_q_cond            ),
  .ca_fast_op_r          (ca_fast_op_r         ),
  .ca_load_r             (ca_load_r            ),
  .ca_mem_addr_r         (ca_mem_addr_r        ),
  .ca_store_r            (ca_store_r           ),
  .ca_zncv_wen_r         (ca_zncv_wen_r        ),
  .ca_normal_evt         (wa_cmt_norm_evt_nxt  ),
  .ca_predicate_r        (ca_predicate_r       ),
  .ca_rtie_op_r          (ca_rtie_op_r         ),
  .ca_sr_stall_rtie      (ca_sr_stall_rtie     ),
  .ca_div_op_r           (ca_div_op_r          ),
  .ca_mpy_op_r           (ca_mpy_op_r          ),
  .ca_vector_op_r        (ca_vector_op_r       ),
  .ca_macu_r             (ca_macu_r            ),
  .ca_q_field_r          (ca_q_field_r         ),
  .ca_with_carry_r       (ca_with_carry_r      ),
  .ca_dmb_op_r           (ca_dmb_op_r          ),
  .ca_dmb_type_r         (ca_dmb_type_r        ),
  .ca_sr_op_r            (ca_sr_op_r           ),
  .ca_pg_xing_replay_r   (ca_pg_xing_replay_r  ),
  .wa_valid_nxt          (wa_valid_nxt         ),
  .wa_cmt_flag_evt_r     (wa_cmt_flag_evt_r    ),
  .wa_rf_wenb0_64_nxt    (wa_rf_wenb0_64_nxt   ),
  .wa_store_r            (wa_store_r           ),
  .wa_load_r             (wa_load_r            ),
  .wa_sr_op_r            (wa_sr_op_r           ),
  .da_rf_ra0_r           (da_rf_ra0_r          ),
  .da_rf_renb0_r         (da_rf_renb0_r        ),
  .da_rf_renb0_64_r      (da_rf_renb0_64_r     ),
  .da_rf_ra1_r           (da_rf_ra1_r          ),
  .da_rf_renb1_r         (da_rf_renb1_r        ),
  .da_rf_renb1_64_r      (da_rf_renb1_64_r     ),

  .sa_rf_ra0_r           (sa_rf_ra0_r          ),
  .sa_rf_ra1_r           (sa_rf_ra1_r          ),
  .x1_rf_ra0_r           (x1_rf_ra0_r          ),
  .x1_rf_ra1_r           (x1_rf_ra1_r          ),
  .x2_rf_ra0_r           (x2_rf_ra0_r          ),
  .x2_rf_ra1_r           (x2_rf_ra1_r          ),
  .x3_rf_ra0_r           (x3_rf_ra0_r          ),
  .x3_rf_ra1_r           (x3_rf_ra1_r          ),
  .ca_rf_ra0_r           (ca_rf_ra0_r          ),
  .ca_rf_ra1_r           (ca_rf_ra1_r          ),
  .sa_rf_renb0_64_r      (sa_rf_renb0_64_r     ),
  .sa_rf_wa0_r           (sa_rf_wa0_r          ),
  .sa_rf_wenb0_r         (sa_rf_wenb0_r        ),
  .sa_rf_wenb0_64_r      (sa_rf_wenb0_64_r     ),
  .sa_rf_renb1_64_r      (sa_rf_renb1_64_r     ),
  .sa_rf_wa1_r           (sa_rf_wa1_r          ),
  .sa_rf_wenb1_r         (sa_rf_wenb1_r        ),
  .sa_rf_wenb1_64_r      (sa_rf_wenb1_64_r     ),
  .x1_rf_wa0_r           (x1_rf_wa0_r          ),
  .x1_rf_wenb0_r         (x1_rf_wenb0_r        ),
  .x1_rf_wenb0_64_r      (x1_rf_wenb0_64_r     ),
  .x1_rf_wa1_r           (x1_rf_wa1_r          ),
  .x1_rf_wenb1_r         (x1_rf_wenb1_r        ),
  .x1_rf_wenb1_64_r      (x1_rf_wenb1_64_r     ),
  .x1_acc_wenb_r         (x1_acc_wenb_r        ),
  .dc1_stall             (dc1_stall            ),
  .x2_rf_wa0_r           (x2_rf_wa0_r          ),
  .x2_rf_wenb0_r         (x2_rf_wenb0_r        ),
  .x2_rf_wenb0_64_r      (x2_rf_wenb0_64_r     ),
  .x2_rf_wa1_r           (x2_rf_wa1_r          ),
  .x2_rf_wenb1_r         (x2_rf_wenb1_r        ),
  .x2_rf_wenb1_64_r      (x2_rf_wenb1_64_r     ),
  .x2_acc_wenb_r         (x2_acc_wenb_r        ),
  .dc2_stall             (dc2_stall            ),
  .x3_rf_wa0_r           (x3_rf_wa0_r          ),
  .x3_rf_wenb0_r         (x3_rf_wenb0_r        ),
  .x3_rf_wenb0_64_r      (x3_rf_wenb0_64_r     ),
  .x3_rf_wa1_r           (x3_rf_wa1_r          ),
  .x3_rf_wenb1_r         (x3_rf_wenb1_r        ),
  .x3_rf_wenb1_64_r      (x3_rf_wenb1_64_r     ),
  .x3_acc_wenb_r         (x3_acc_wenb_r        ),
  .x3_acc_op_r           (x3_acc_op_r          ),
  .dmp_dc3_fast_byp      (dmp_dc3_fast_byp     ),
  .ca_rf_wa0_r           (ca_rf_wa0_r          ),
  .ca_rf_wenb0_r         (ca_rf_wenb0_r        ),
  .ca_rf_wenb0_64_r      (ca_rf_wenb0_64_r     ),
  .ca_rf_wa1_r           (ca_rf_wa1_r          ),
  .ca_rf_wenb1_r         (ca_rf_wenb1_r        ),
  .ca_rf_wenb1_64_r      (ca_rf_wenb1_64_r     ),
  .ca_writes_acc_r       (ca_writes_acc_r      ),
  .ca_acc_wenb_r         (ca_acc_wenb_r        ),
  .ca_locked_r           (ca_locked_r          ),
  .ca_wlfc_op            (ca_wlfc_op           ),
  .dmp_dc4_fast_byp_r    (dmp_dc4_fast_byp_r   ),
  .dmp_dc4_fast_miss_r   (dmp_dc4_fast_miss_r  ),
  .dmp_aux_pending_r     (dmp_aux_pending_r    ),
  .dmp_wr_pending_r      (dmp_wr_pending_r     ),
  .dc4_stall             (dmp_dc4_stall        ),
  .dc4_replay            (dc4_q_replay         ),
  .dc4_waw_replay_r      (dc4_waw_replay_r     ), 

  .ct_replay             (ct_replay            ),
  .wa_cmt_isi_evt        (ca_cmt_isi_evt       ),
  .excpn_restart         (excpn_restart        ),
  .hlt_restart           (hlt_restart          ),
  .aps_break             (aps_break            ),
  .aps_halt              (aps_halt             ),
  .x3_aps_break_r        (x3_aps_break_r       ),
  .x3_aps_halt_r         (x3_aps_halt_r        ),
  .wa_uopld_status32     (wa_uopld_status32    ),
  .wa_rf_wa0_r           (wa_rf_wa0_r          ),
  .wa_rf_wenb0_r         (wa_rf_wenb0_r        ),
  .wa_rf_wenb0_64_r      (wa_rf_wenb0_64_r     ),
  .wa_rf_wa1_r           (wa_rf_wa1_r          ),
  .wa_rf_wenb1_r         (wa_rf_wenb1_r        ),
  .wa_rf_wenb1_64_r      (wa_rf_wenb1_64_r     ),
 .wa_writes_acc_r        (wa_writes_acc_r      ),
  .wa_acc_wenb_r         (wa_acc_wenb_r        ),

  .x1_rf_renb0_64_r      (x1_rf_renb0_64_r     ),
  .x2_rf_renb0_64_r      (x2_rf_renb0_64_r     ),
  .x3_rf_renb0_64_r      (x3_rf_renb0_64_r     ),
  .ca_rf_renb0_64_r      (ca_rf_renb0_64_r     ),

  .x1_rf_renb1_64_r      (x1_rf_renb1_64_r     ),
  .x2_rf_renb1_64_r      (x2_rf_renb1_64_r     ),
  .x3_rf_renb1_64_r      (x3_rf_renb1_64_r     ),
  .ca_rf_renb1_64_r      (ca_rf_renb1_64_r     ),

  .x1_cc_byp_64_haz_r    (x1_cc_byp_64_haz_r   ),
  .x2_cc_byp_64_haz_r    (x2_cc_byp_64_haz_r   ),
  .x3_cc_byp_64_haz_r    (x3_cc_byp_64_haz_r   ),
  .ca_cc_byp_64_haz_r    (ca_cc_byp_64_haz_r   ),
  .wa_cc_byp_64_haz_r    (wa_cc_byp_64_haz_r   ),

  .da_in_dslot_r         (da_in_dslot_r        ),
  .sa_in_dslot_r         (sa_in_dslot_r        ),
  .x1_in_dslot_r         (x1_in_dslot_r        ),
  .x1_dslot_stall        (x1_dslot_stall       ),
  .x2_in_dslot_r         (x2_in_dslot_r        ),
  .x3_in_dslot_r         (x3_in_dslot_r        ),
  .ca_in_dslot_r         (ca_in_dslot_r        ),

  .x2_restart_r          (x2_restart_r         ),
  .x2_mispred_r          (x2_mispred_r         ),
  .holdup_excpn_r        (holdup_excpn_r       ),
  .holdup_excpn_nxt      (holdup_excpn_nxt     ),
  .x2_error_branch_r     (x2_error_branch_r    ),
  .x2_fragged_r          (x2_fragged_r         ),
  .x3_error_branch_r     (x3_error_branch_r    ),
  .ca_fragged_r          (ca_fragged_r         ),
  .ca_error_branch_r     (ca_error_branch_r    ),
  .wa_error_branch       (wa_error_branch      ),

  .wa_restart            (wa_restart_r         ),
  .excpn_in_prologue_r   (excpn_in_prologue_r  ),
  .wa_mispred_r          (wa_mispred_r         ),

  .dc4_grad_req          (dc4_grad_req         ), 
  .dc4_grad_rf_wa        (ca_grad_rf_wa1       ),
  .dc4_grad_rf_64        (ca_rf_wenb1_64_r     ),
  .dmp_idle_r            (dmp_idle_r           ),
  .dmp_retire_req        (dmp_retire_req       ),
  
  .div_grad_req          (div_grad_req         ), 
  .div_grad_rf_wa        (div_grad_rf_wa       ),

  .eia_grad_req          (eia_exu_grad_req     ), 
  .eia_grad_rf_wa        (eia_grad_rf_wa       ),

  .ca_grad_req           (ca_grad_req          ),
  .ca_grad_ack           (ca_grad_ack          ),
  .ca_grad_tag           (ca_grad_tag          ),
  .ca_replay             (ca_replay            ),
  .ca_dc4_replay         (ca_dc4_replay        ),
  .ca_retire_req         (ca_retire_req        ),
  .ca_retire_tag         (ca_retire_tag        ),
  .ca_wa1_conflict       (ca_wa1_conflict      ),
  .ca_retire_ack         (ca_retire_ack        ),
  .commit_inst           (commit_inst          ),
  .dp_retire_rf_64       (dp_retire_rf_64      ),
  .dp_retire_rf_wenb     (dp_retire_rf_wenb    ),
  .dp_retire_rf_wa       (dp_retire_rf_wa      ),
  .dp_retire_zncv        (dp_retire_zncv       ),
  .ar_zncv_upt_r         (ar_zncv_upt_r        ),
  .dp_retire_scond       (dp_retire_scond      ),

  .dp_retire_writes_acc  (dp_retire_writes_acc ),
  .dp_retire_ld_addr     (dmp_retire_ld_addr   ), 
  .dp_retire_is_load     (dmp_retire_is_load   ), 
  //
  // SA forwarding controls
  //
  .fwd_x1_sa0_lo         (fwd_x1_sa0_lo        ),
  .fwd_x2_sa0_lo         (fwd_x2_sa0_lo        ),
  .fwd_x3_sa0_lo         (fwd_x3_sa0_lo        ),
  .fwd_ca0_lo_sa0_lo     (fwd_ca0_lo_sa0_lo    ),
  .fwd_ca1_lo_sa0_lo     (fwd_ca1_lo_sa0_lo    ),
  .fwd_wa0_lo_sa0_lo     (fwd_wa0_lo_sa0_lo    ),
  .fwd_wa1_lo_sa0_lo     (fwd_wa1_lo_sa0_lo    ),
  .fwd_ca0_hi_sa0_lo     (fwd_ca0_hi_sa0_lo    ),
  .fwd_wa0_hi_sa0_lo     (fwd_wa0_hi_sa0_lo    ),

  .fwd_ca1_hi_sa0_lo     (fwd_ca1_hi_sa0_lo    ),
  .fwd_ca1_hi_sa1_lo     (fwd_ca1_hi_sa1_lo    ),
  .fwd_wa1_hi_sa0_lo     (fwd_wa1_hi_sa0_lo    ),
  .fwd_wa1_hi_sa1_lo     (fwd_wa1_hi_sa1_lo    ),
  .fwd_wa0_hi_sa0_hi     (fwd_wa0_hi_sa0_hi    ),
  .fwd_wa1_hi_sa0_hi     (fwd_wa1_hi_sa0_hi    ),
  .fwd_x1_sa1_lo         (fwd_x1_sa1_lo        ),
  .fwd_x2_sa1_lo         (fwd_x2_sa1_lo        ),
  .fwd_x3_sa1_lo         (fwd_x3_sa1_lo        ),
  .fwd_ca0_lo_sa1_lo     (fwd_ca0_lo_sa1_lo    ),
  .fwd_ca1_lo_sa1_lo     (fwd_ca1_lo_sa1_lo    ),
  .fwd_wa0_lo_sa1_lo     (fwd_wa0_lo_sa1_lo    ),
  .fwd_wa1_lo_sa1_lo     (fwd_wa1_lo_sa1_lo    ),
  .fwd_ca0_hi_sa1_lo     (fwd_ca0_hi_sa1_lo    ),
  .fwd_wa0_hi_sa1_lo     (fwd_wa0_hi_sa1_lo    ),
  .fwd_wa0_lo_sa0_hi     (fwd_wa0_lo_sa0_hi    ),
  .fwd_wa1_lo_sa0_hi     (fwd_wa1_lo_sa0_hi    ),
  .fwd_wa0_hi_sa1_hi     (fwd_wa0_hi_sa1_hi    ),
  .fwd_wa0_lo_sa1_hi     (fwd_wa0_lo_sa1_hi    ),
  .fwd_wa1_lo_sa1_hi     (fwd_wa1_lo_sa1_hi    ),
  .fwd_wa1_hi_sa1_hi     (fwd_wa1_hi_sa1_hi    ),
  //
  // X1 forwarding controls
  //
  .fwd_x1_r0_dmp_fast    (fwd_x1_r0_dmp_fast   ),
  .fwd_x1_r1_dmp_fast    (fwd_x1_r1_dmp_fast   ),
  .fwd_x1_r0_wa_w0_lo    (fwd_x1_r0_wa_w0_lo   ),
  .fwd_x1_r1_wa_w0_lo    (fwd_x1_r1_wa_w0_lo   ),
  .fwd_x1_r0_wa_w1_lo    (fwd_x1_r0_wa_w1_lo   ),
  .fwd_x1_r1_wa_w1_lo    (fwd_x1_r1_wa_w1_lo   ),
  .fwd_x1_r0_ca_w1_hi    (fwd_x1_r0_ca_w1_hi   ),
  .fwd_x1_r1_ca_w1_hi    (fwd_x1_r1_ca_w1_hi   ),
  .fwd_x1_r0h_ca_w1_hi   (fwd_x1_r0h_ca_w1_hi  ),
  .fwd_x1_r1h_ca_w1_hi   (fwd_x1_r1h_ca_w1_hi  ),
  .fwd_x1_r0_wa_w1_hi    (fwd_x1_r0_wa_w1_hi   ),
  .fwd_x1_r1_wa_w1_hi    (fwd_x1_r1_wa_w1_hi   ),
  .fwd_x1_r0h_wa_w1_hi   (fwd_x1_r0h_wa_w1_hi  ),
  .fwd_x1_r1h_wa_w1_hi   (fwd_x1_r1h_wa_w1_hi  ),
  .fwd_x1_r1h_wa_w0_lo   (fwd_x1_r1h_wa_w0_lo  ),
  .fwd_x1_r1h_wa_w1_lo   (fwd_x1_r1h_wa_w1_lo  ),
  .fwd_x1_r0_x2_w0       (fwd_x1_r0_x2_w0      ),
  .fwd_x1_r1_x2_w0       (fwd_x1_r1_x2_w0      ),
  .fwd_x1_r0h_x2_w0      (fwd_x1_r0h_x2_w0     ),
  .fwd_x1_r1h_x2_w0      (fwd_x1_r1h_x2_w0     ),
  .fwd_x1_r0_x3_w0       (fwd_x1_r0_x3_w0      ),
  .fwd_x1_r1_x3_w0       (fwd_x1_r1_x3_w0      ),
  .fwd_x1_r0h_x3_w0      (fwd_x1_r0h_x3_w0     ),
  .fwd_x1_r1h_x3_w0      (fwd_x1_r1h_x3_w0     ),
  .fwd_x1_r0_ca_w0_lo    (fwd_x1_r0_ca_w0_lo   ),
  .fwd_x1_r1_ca_w0_lo    (fwd_x1_r1_ca_w0_lo   ),
  .fwd_x1_r0_ca_w1_lo    (fwd_x1_r0_ca_w1_lo   ),
  .fwd_x1_r1_ca_w1_lo    (fwd_x1_r1_ca_w1_lo   ),
  .fwd_x1_r0_ca_w0_hi    (fwd_x1_r0_ca_w0_hi   ),
  .fwd_x1_r1_ca_w0_hi    (fwd_x1_r1_ca_w0_hi   ),
  .fwd_x1_r0_wa_w0_hi    (fwd_x1_r0_wa_w0_hi   ),
  .fwd_x1_r1_wa_w0_hi    (fwd_x1_r1_wa_w0_hi   ),
  .fwd_x1_r0h_ca_w0_lo  (fwd_x1_r0h_ca_w0_lo   ),
  .fwd_x1_r0h_ca_w0_hi  (fwd_x1_r0h_ca_w0_hi   ),
  .fwd_x1_r1h_ca_w0_lo  (fwd_x1_r1h_ca_w0_lo   ),
  .fwd_x1_r1h_ca_w0_hi  (fwd_x1_r1h_ca_w0_hi   ),

  .fwd_x1_r0h_ca_w1_lo  (fwd_x1_r0h_ca_w1_lo   ),
  .fwd_x1_r1h_ca_w1_lo  (fwd_x1_r1h_ca_w1_lo   ),

  .fwd_x1_r0h_wa_w0_lo  (fwd_x1_r0h_wa_w0_lo   ),
  .fwd_x1_r0h_wa_w0_hi  (fwd_x1_r0h_wa_w0_hi   ),
  .fwd_x1_r0h_wa_w1_lo  (fwd_x1_r0h_wa_w1_lo   ),
  .fwd_x1_r1h_wa_w0_hi   (fwd_x1_r1h_wa_w0_hi  ),
  .fwd_zncv_x1           (fwd_zncv_x1          ),
  .fwd_zncv_x1_x2        (fwd_zncv_x1_x2       ),
  .fwd_zncv_x1_ca        (fwd_zncv_x1_ca       ),
  .fwd_zncv_x1_ar        (fwd_zncv_x1_ar       ),
  //
  // X2 forwarding controls
  //
  .fwd_x2_r0_wa_w0_lo    (fwd_x2_r0_wa_w0_lo   ),
  .fwd_x2_r0_wa_w1_lo    (fwd_x2_r0_wa_w1_lo   ),
  .fwd_x2_r1_wa_w0_lo    (fwd_x2_r1_wa_w0_lo   ),
  .fwd_x2_r1_wa_w1_lo    (fwd_x2_r1_wa_w1_lo   ),
  .fwd_x2_r0_wa_w0_hi    (fwd_x2_r0_wa_w0_hi   ),
  .fwd_x2_r1_wa_w0_hi    (fwd_x2_r1_wa_w0_hi   ),
  .fwd_x2_r0_wa_w1_hi    (fwd_x2_r0_wa_w1_hi   ),
  .fwd_x2_r1_wa_w1_hi    (fwd_x2_r1_wa_w1_hi   ),
  .fwd_x2_r1h_wa_w0_lo   (fwd_x2_r1h_wa_w0_lo  ),
  .fwd_x2_r1h_wa_w1_lo   (fwd_x2_r1h_wa_w1_lo  ),
  .fwd_x2_r1h_wa_w0_hi   (fwd_x2_r1h_wa_w0_hi  ),
  .fwd_x2_r1h_wa_w1_hi   (fwd_x2_r1h_wa_w1_hi  ),
  //
  // X3 forwarding controls
  //
  .fwd_x3_r0_ca_w0_lo    (fwd_x3_r0_ca_w0_lo   ),
  .fwd_x3_r0_ca_w1_lo    (fwd_x3_r0_ca_w1_lo   ),
  .fwd_x3_r0_wa_w0_lo    (fwd_x3_r0_wa_w0_lo   ),
  .fwd_x3_r0_wa_w1_lo    (fwd_x3_r0_wa_w1_lo   ),
  .fwd_x3_r1_ca_w0_lo    (fwd_x3_r1_ca_w0_lo   ),
  .fwd_x3_r1_ca_w1_lo    (fwd_x3_r1_ca_w1_lo   ),
  .fwd_x3_r1_wa_w0_lo    (fwd_x3_r1_wa_w0_lo   ),
  .fwd_x3_r1_wa_w1_lo    (fwd_x3_r1_wa_w1_lo   ),
  .fwd_x3_r0_ca_w0_hi    (fwd_x3_r0_ca_w0_hi   ),
  .fwd_x3_r0_wa_w0_hi    (fwd_x3_r0_wa_w0_hi   ),
  .fwd_x3_r1_ca_w0_hi    (fwd_x3_r1_ca_w0_hi   ),
  .fwd_x3_r1_wa_w0_hi    (fwd_x3_r1_wa_w0_hi   ),
  .fwd_x3_r0_wa_w1_hi    (fwd_x3_r0_wa_w1_hi   ),
  .fwd_x3_r1_wa_w1_hi    (fwd_x3_r1_wa_w1_hi   ),
  .fwd_x3_r0_ca_w1_hi    (fwd_x3_r0_ca_w1_hi   ),
  .fwd_x3_r1_ca_w1_hi    (fwd_x3_r1_ca_w1_hi   ),
  .fwd_x3_r1h_ca_w0_lo   (fwd_x3_r1h_ca_w0_lo  ),
  .fwd_x3_r1h_ca_w1_lo   (fwd_x3_r1h_ca_w1_lo  ),
  .fwd_x3_r1h_wa_w0_lo   (fwd_x3_r1h_wa_w0_lo  ), 
  .fwd_x3_r1h_wa_w1_lo   (fwd_x3_r1h_wa_w1_lo  ),
  .fwd_x3_r1h_ca_w0_hi   (fwd_x3_r1h_ca_w0_hi  ),
  .fwd_x3_r1h_wa_w0_hi   (fwd_x3_r1h_wa_w0_hi  ),
  .fwd_x3_r1h_ca_w1_hi   (fwd_x3_r1h_ca_w1_hi  ),
  .fwd_x3_r1h_wa_w1_hi   (fwd_x3_r1h_wa_w1_hi  ),
  //
  // CA forwarding controls
  //
  .fwd_ca_r0_wa_w0_lo    (fwd_ca_r0_wa_w0_lo   ),
  .fwd_ca_r0_wa_w1_lo    (fwd_ca_r0_wa_w1_lo   ),
  .fwd_ca_r1_wa_w0_lo    (fwd_ca_r1_wa_w0_lo   ),
  .fwd_ca_r1_wa_w1_lo    (fwd_ca_r1_wa_w1_lo   ),
  .fwd_ca_r0_wa_w0_hi    (fwd_ca_r0_wa_w0_hi   ),
  .fwd_ca_r1_wa_w0_hi    (fwd_ca_r1_wa_w0_hi   ),
  .fwd_ca_r0_wa_w1_hi    (fwd_ca_r0_wa_w1_hi   ),
  .fwd_ca_r1_wa_w1_hi    (fwd_ca_r1_wa_w1_hi   ),
  .fwd_ca_r1h_wa_w0_lo   (fwd_ca_r1h_wa_w0_lo  ),
  .fwd_ca_r1h_wa_w1_lo   (fwd_ca_r1h_wa_w1_lo  ),
  .fwd_ca_r1h_wa_w0_hi   (fwd_ca_r1h_wa_w0_hi  ),
  .fwd_ca_r1h_wa_w1_hi   (fwd_ca_r1h_wa_w1_hi  ),

  // X1 branch resolution dependency conditions
  //
  .x1_cond_ready         (x1_cond_ready        ),
  .x1_bta_ready          (x1_bta_ready         ),
  .x1_no_eval            (x1_no_eval           ),
  .x2_done_nxt           (x2_done_nxt          ),
  
  // Pipeline stage control signal
  //
  .da_holdup             (da_holdup            ),
  .da_enable             (da_enable            ),
  .sa_enable             (sa_enable            ),
  .x1_enable             (x1_enable            ),
  .x2_enable             (x2_enable            ),
  .x3_enable             (x3_enable            ),
  .ca_enable             (ca_enable            ),
  .wa_enable             (wa_enable            ),
  .da_pass               (da_pass              ),
  .sa_pass               (sa_pass              ),
  .x1_pass               (x1_pass              ),
  .x2_pass               (x2_pass              ),
  .x3_pass               (x3_pass              ),
  .ca_pass               (ca_pass              ),
  .ca_pass_no_hlt        (ca_pass_no_hlt       ),
  .ca_iprot_viol_r       (ca_iprot_viol_r      ),
  .ca_pass_no_iprot      (ca_pass_no_iprot     ),
  .sa_valid_r            (sa_valid_r           ),
  .x1_valid_r            (x1_valid_r           ),
  .x2_valid_r            (x2_valid_r           ),
  .x3_valid_r            (x3_valid_r           ),
  .ca_valid_r            (ca_valid_r           ),
  .wa_valid_r            (wa_valid_r           ),
  .da_kill               (da_kill              ),
  .sa_kill               (sa_kill              ),
  .x1_kill               (x1_kill              ),
  .x2_kill               (x2_kill              ),
  .x3_kill               (x3_kill              ),
  .ca_kill               (ca_kill              ),
  .x1_wa_dslot           (x1_wa_dslot          ),
  .x2_wa_dslot           (x2_wa_dslot          ),
  .x1_retain             (x1_retain            ),
  .x2_retain             (x2_retain            ),
  .x3_retain             (x3_retain            ),
  .ca_stall              (ca_stall             ),
  .x2_done_r             (x2_done_r            ),
  .x2_has_w0             (x2_has_w0            ),
  .x2_read_r0_r          (x2_read_r0_r         ),
  .x2_read_r1_r          (x2_read_r1_r         ),
  .x3_read_r0_r          (x3_read_r0_r         ),
  .x3_read_r1_r          (x3_read_r1_r         ),
  .x3_done_r             (x3_done_r            ),
  .ca_done_r             (ca_done_r            ),
  .ar_tags_empty_r       (ar_tags_empty_r      )
);


assign dep_bdcmstall = 0;
assign sync_dsync_dmb_stall = 0;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Branch Prediction Pipeline (alb_pred_pipe) module instantiation          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_pred_pipe u_alb_pred_pipe (
  .clk                    (clk                  ),
  .rst_a                  (rst_a                ),
  .db_active              (db_active            ),
  .ar_aux_debug_r         (ar_aux_debug_r       ),
  .ar_aux_status32_r      (ar_aux_status32_r    ),
  .ar_aux_lp_start_r      (ar_aux_lp_start_r    ),

  .fch_restart            (fch_restart          ),

  .al_pass                (al_pass              ),
  .al_is_predicted        (al_is_predicted      ),
  .al_prediction          (al_prediction        ),
  .al_predicted_bta       (al_predicted_bta     ),
  .al_prediction_type     (al_prediction_type   ),
  .al_error_branch        (al_error_branch      ),
  .al_branch_info         (al_branch_info       ),
  .al_with_dslot          (al_with_dslot        ),

  .al_uop_is_predicted    (al_uop_is_predicted  ),
  .al_uop_prediction      (al_uop_prediction    ),
  .al_uop_prediction_type (al_uop_prediction_type),
  .al_uop_with_dslot      (al_uop_with_dslot    ),

  .al_uop_pass            (al_uop_pass          ),
  .da_enable              (da_enable            ),
  .da_holdup              (da_holdup            ),
  .da_pass                (da_pass              ),
  .sa_enable              (sa_enable            ),
  .sa_pass                (sa_pass              ),
  .x1_enable              (x1_enable            ),
  .x1_pass                (x1_pass              ),
  .x1_cond_ready          (x1_cond_ready        ),
  .x1_bta_ready           (x1_bta_ready         ),
  .x2_enable              (x2_enable            ),
  .x2_pass                (x2_pass              ),
  .x3_enable              (x3_enable            ),
  .x3_pass                (x3_pass              ),
  .ca_enable              (ca_enable            ),
  .ca_pass                (ca_pass              ),
  .wa_enable              (wa_enable            ),

  .da_valid_r             (da_valid_r           ),
  .sa_valid_r             (sa_valid_r           ),
  .x1_valid_r             (x1_valid_r           ),
  .x2_valid_r             (x2_valid_r           ),
  .x3_valid_r             (x3_valid_r           ),
  .ca_valid_r             (ca_valid_r           ),
  .x1_kill                (x1_kill              ),

  .da_orphan_dslot_r      (da_orphan_dslot_r    ),
  .da_dslot               (da_dslot             ),
  .da_uop_prol_r          (da_uop_prol_r        ),
  .da_uop_busy_r          (da_uop_busy_r        ),
  .da_ifu_exception_r     (da_ifu_exception_r   ),
  .da_ifu_err_nxtpg_r     (da_ifu_err_nxtpg_r   ),
  .sa_link_r              (sa_link_r            ),
  .sa_dslot_r             (sa_dslot_r           ),
  .x1_dslot_r             (x1_dslot_r           ),
  .x1_uop_epil_r          (x1_uop_epil_r        ),
  .ar_aux_bta_r           (ar_aux_bta_r         ),
  .sa_seq_pc_r            (sa_seq_pc_r          ),
  .sa_ei_op_r             (sa_ei_op_r           ),
  .sa_leave_op_r          (sa_leave_op_r        ),
  .x1_ei_op_r             (x1_ei_op_r           ),
  .x1_btab_op_r           (x1_btab_op_r         ),
  .x2_ei_op_r             (x2_ei_op_r           ),
  .x3_ei_op_r             (x3_ei_op_r           ),
  .ca_ei_op_r             (ca_ei_op_r           ),
  .ca_btab_op_r           (ca_btab_op_r         ),
  .ca_dslot_r             (ca_dslot_r           ),
  .ca_jump_r              (ca_jump_r            ),
  .sa_pc                  (sa_pc                ),
  .x1_pc_r                (x1_pc_r              ),
  .sa_br_type             (sa_br_type           ),
  .sa_secondary           (sa_secondary         ),
  .sa_commit_size         (sa_commit_size       ),
  .sa_uop_inst_r          (sa_uop_inst_r        ),
  .sa_uop_predictable_r   (sa_uop_predictable_r),
  .sa_iprot_viol_r        (sa_iprot_viol_r      ),

  .x1_uop_inst_r          (x1_uop_inst_r        ),

  .x1_br_direction        (x1_br_direction      ),
  .x1_br_taken            (x1_br_taken          ),
  .x1_br_target           (x1_br_target         ),
  .x1_br_fall_thru        (x1_br_fall_thru      ),
  .x1_bi_bta_mpd          (x1_bi_bta_mpd        ),
  .x2_target_nxt          (x2_target_nxt        ),
  .x1_link_addr           (x1_link_addr         ),
  .x1_predictable_r       (x1_predictable_r     ),
  .x1_is_eslot_r          (x1_is_eslot_r        ),
  .x1_pred_bta_r          (x1_pred_bta_r        ),

  .x1_early_pred_r        (x1_early_pred_r      ),
  .x1_zol_mpd_dir         (x1_zol_mpd_dir       ),
  .sa_zol_hazard          (sa_zol_hazard        ),
  .x1_zol_hazard_r        (x1_zol_hazard_r      ),
  
  .ar_pc_r                (ar_pc_r              ),
  .ca_br_or_jmp           (ca_br_or_jmp         ),
  .ca_br_direction        (ca_br_direction      ),
  .ca_br_target           (ca_br_target         ),
  .ca_br_fall_thru        (ca_br_fall_thru      ),
  .ca_leave_op_r          (ca_leave_op_r        ),
  .ca_uop_inst            (ca_uop_inst          ),
  .ca_uop_active_r        (ca_uop_active_r      ),
  .ca_uop_predictable_r     (ca_uop_predictable_r   ),
  .ca_uop_enter_r         (ca_uop_enter_r       ),
  .ca_uop_commit_r        (ca_uop_commit_r      ),
  .ca_tail_pc_3           (ca_tail_pc_3         ),
  .ca_br_taken            (ca_br_taken          ),

  .wa_cmt_norm_evt_nxt    (wa_cmt_norm_evt_nxt  ),
  .ct_excpn_trap_nxt      (ct_excpn_trap_nxt    ),// TRAP in CA
  .ca_sleep_evt           (ca_sleep_evt         ), // SLEEP in CA
  .ca_cmt_brk_evt         (ca_cmt_brk_evt       ), // BREAK in CA
  .ca_iprot_viol_r        (ca_iprot_viol_r      ),
  .ca_iprot_replay        (ca_iprot_replay      ),
 
  .ca_hit_lp_end          (ca_hit_lp_end        ), 
  .ca_branch_evt          (ca_branch_evt        ),                             
  .ca_zol_mpd_dir         (ca_zol_mpd_dir       ),
  .ca_zol_mpd_bta         (ca_zol_mpd_bta       ),
  .ca_zol_lp_jmp          (ca_zol_lp_jmp        ),
  .ca_zol_branch          (ca_zol_branch        ),

  .dc4_replay             (ca_replay            ),

  .excpn_restart          (excpn_restart        ),
  .excpn_restart_pc       (excpn_restart_pc     ),
  .hlt_stop               (hlt_stop             ),
  .hlt_restart            (hlt_restart          ),
  .ct_replay              (ct_replay            ),
  .da_is_eslot            (da_is_eslot          ),
  .da_eslot_stall         (da_eslot_stall       ),
  .da_in_dslot_r          (da_in_dslot_r        ),
  .sa_in_dslot_r          (sa_in_dslot_r        ),
  .x1_in_dslot_r          (x1_in_dslot_r        ),
  .x2_in_dslot_r          (x2_in_dslot_r        ),
  .x3_in_dslot_r          (x3_in_dslot_r        ),
  .ca_in_dslot_r          (ca_in_dslot_r        ),
  
  .da_is_predicted_r      (da_is_predicted_r    ),
  .da_prediction_r        (da_prediction_r      ),
  .da_pred_bta_r          (da_pred_bta_r        ),
  .da_prediction_type_r   (da_prediction_type_r ),
  .da_error_branch_r      (da_error_branch_r    ),
  
  .sa_is_predicted_r      (sa_is_predicted_r    ),
  .sa_with_dslot_r        (sa_with_dslot_r      ),
  .sa_prediction_r        (sa_prediction_r      ),
  .sa_prediction_type_r   (sa_prediction_type_r ),
  .sa_pred_bta_r          (sa_pred_bta_r        ),
  .sa_error_branch_r      (sa_error_branch_r    ),
  .sa_error_branch        (sa_error_branch      ),
  
  .x1_dslot_stall         (x1_dslot_stall       ),
  .x1_error_branch_r      (x1_error_branch_r    ),

  .x2_restart_r           (x2_restart_r         ),
  .x2_restart_pc_r        (x2_restart_pc_r      ),
  .x2_mispred_r           (x2_mispred_r         ),
  .x2_fragged_r           (x2_fragged_r         ),
  .x2_error_branch_r      (x2_error_branch_r    ),
  .x2_pg_xing_replay_r    (x2_pg_xing_replay_r  ),
  .x2_pg_xing_dslot_r     (x2_pg_xing_dslot_r   ),
  .x3_error_branch_r      (x3_error_branch_r    ),
  .x3_late_pred_r         (x3_late_pred_r       ),
  
  .ca_is_predicted_r      (ca_is_predicted_r    ),
  .ca_prediction_r        (ca_prediction_r      ),
  .ca_br_type_r           (ca_br_type_r         ),
  .ca_pred_bta_r          (ca_pred_bta_r        ),
  .ca_fragged_r           (ca_fragged_r         ),
  .ca_error_branch_r      (ca_error_branch_r    ),
  .ca_pg_xing_replay_r    (ca_pg_xing_replay_r  ),

  .wa_mispred_r           (wa_mispred_r         ),
  .wa_restart_r           (wa_restart_r         ),
  .wa_restart_kill_r      (wa_restart_kill_r    ),
  .wa_restart_pc_r        (wa_restart_pc_r      ),
  .wa_stop_r              (wa_stop_r            ),
  .wa_iprot_replay_r      (wa_iprot_replay_r    ),
  
  .mpd_mispred            (mpd_mispred          ),
  .mpd_direction          (mpd_direction        ),
  .mpd_error_branch       (mpd_error_branch     ),
  .mpd_is_predicted       (mpd_is_predicted     ),
  .mpd_mispred_outcome    (mpd_mispred_outcome  ),
  .mpd_mispred_bta        (mpd_mispred_bta      ),
  .mpd_branch_info        (mpd_branch_info      ),
  .mpd_dslot              (mpd_dslot            ),
  .mpd_seq_next_pc        (mpd_seq_next_pc      ),
  .mpd_pc                 (mpd_pc               ),
  .mpd_type               (mpd_type             ),
  .mpd_early              (mpd_early            ),
  .mpd_tail_pc_3          (mpd_tail_pc_3        ),
  .mpd_commit_size        (mpd_commit_size      ),
  .mpd_secondary          (mpd_secondary        ),
  .wa_pass                (wa_pass              ),
  .wa_type                (wa_type              ),
  .wa_commit_size         (wa_commit_size       ),
  .wa_secondary           (wa_secondary         ),
  .wa_direction           (wa_direction         ),
  .wa_target              (wa_target            ),
  .wa_error_branch        (wa_error_branch      ),
  .wa_is_predicted        (wa_is_predicted      ),
  .wa_mispred_outcome     (wa_mispred_outcome   ),
  .wa_commit_mispred_bta  (wa_commit_mispred_bta),
  .wa_branch_info         (wa_branch_info       )

);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Zero Overhead Loop Pipeline (alb_zol_pipe) module instantiation          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_zol_pipe u_alb_zol_pipe (
  .clk                    (clk                  ),
  .rst_a                  (rst_a                ),
  .db_active              (db_active            ),
  .ar_aux_status32_r      (ar_aux_status32_r    ),
  .ar_aux_lp_start_r      (ar_aux_lp_start_r    ),
  .ar_aux_lp_end_r        (ar_aux_lp_end_r      ),
  .sa_error_branch        (sa_error_branch      ),
  .ca_is_predicted_r      (ca_is_predicted_r    ),
  .ca_prediction_r        (ca_prediction_r      ),
  .ca_pred_bta_r          (ca_pred_bta_r        ),
  .da_pass                (da_pass              ),
  .sa_enable              (sa_enable            ),
  .sa_pass                (sa_pass              ),
  .sa_in_dslot_r          (sa_in_dslot_r        ),
  .x1_in_dslot_r          (x1_in_dslot_r        ),
  .x1_enable              (x1_enable            ),
  .x1_pass                (x1_pass              ),
  .x2_enable              (x2_enable            ),
  .x2_pass                (x2_pass              ),
  .x3_enable              (x3_enable            ),
  .x3_pass                (x3_pass              ),
  .ca_enable              (ca_enable            ),
  .wa_enable              (wa_enable            ),
  .sa_branch_or_jump      (sa_branch_or_jump    ),
  .sa_multi_op_r          (sa_multi_op_r        ),
  .wa_wa0_lpc_r           (wa_wa0_lpc_r         ),
  .x1_loop_op_r           (x1_loop_op_r         ), 
  .x2_loop_op_r           (x2_loop_op_r         ),

  .x3_loop_op_r           (x3_loop_op_r         ),
  .ca_loop_op_r           (ca_loop_op_r         ),
  .ca_uop_commit_r        (ca_uop_commit_r      ),
  .ca_uop_inprol_r        (ca_uop_inprol_r      ),
  .ca_cmt_brk_evt         (ca_cmt_brk_evt       ),
  .wa_loop_op_r           (wa_loop_op_r         ),
  .x2_valid_r             (x2_valid_r           ),
  .x3_valid_r             (x3_valid_r           ),
  .ca_valid_r             (ca_valid_r           ),
  .x2_error_branch_r      (x2_error_branch_r    ),
  .x3_error_branch_r      (x3_error_branch_r    ),
  .da_rf_ra0_r            (da_rf_ra0_r          ),
  .da_rf_renb0_r          (da_rf_renb0_r        ),
  .da_rf_ra1_r            (da_rf_ra1_r          ),
  .da_rf_renb1_r          (da_rf_renb1_r        ),
  .sa_seq_pc_nxt          (sa_seq_pc_nxt        ),
  .sa_seq_pc_r            (sa_seq_pc_r          ),
  .ca_seq_pc_nxt          (ca_seq_pc_nxt        ),
  .wa_cmt_norm_evt_nxt    (wa_cmt_norm_evt_nxt  ),
  .ca_branch_evt          (ca_branch_evt        ),
  .ca_uop_inst            (ca_uop_inst          ),
  .ca_error_branch_r      (ca_error_branch_r    ),
  .wa_rf_wdata0_lo_r      (wa_rf_wdata0_lo_r    ),
  .wa_uopld_lp_count      (wa_uopld_lp_count    ),
  .wa_uopld_data          (wa_uopld_data        ),
  .ar_lp_count_r          (ar_lp_count_r        ),
  .sa_zol_stall           (sa_zol_stall         ),
  .sa_hit_lp_end          (sa_hit_lp_end        ),
  .sa_zol_hazard          (sa_zol_hazard        ),
  .sa_lp_count_r          (sa_lp_count_r        ),
  .x1_zol_stall           (x1_zol_stall         ),
  .x1_zol_mpd_dir         (x1_zol_mpd_dir       ),
  .x1_zol_hazard_r        (x1_zol_hazard_r      ),
  .x1_early_pred_r        (x1_early_pred_r      ),
  .x2_zol_ill_seq_r       (x2_zol_ill_seq_r     ),
  .zol_depend_stall       (zol_depend_stall     ),
  .ca_hit_lp_end          (ca_hit_lp_end        ),
  .ca_zol_mpd_dir         (ca_zol_mpd_dir       ),
  .ca_zol_mpd_bta         (ca_zol_mpd_bta       ),
  .ca_zol_lp_jmp          (ca_zol_lp_jmp        ),
  .ca_zol_branch          (ca_zol_branch        )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Exception Pipeline (alb_excpn_pipe) module instantiation                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
npuarc_alb_excpn_pipe u_alb_excpn_pipe (
  .clk                    (clk                  ),
  .rst_a                  (rst_a                ),
  .gb_sys_sleep_r         (gb_sys_sleep_r       ),
  .dmp_queue_empty        (dmp_queue_empty      ),
  .iexcpn_discarded       (iexcpn_discarded     ),
  .st_instrs_discarded    (st_instrs_discarded  ),
  .db_active              (db_active            ),
  .x3_db_exception        (x3_1_db_exception    ),
  .ca_db_exception_r      (ca_db_exception_r    ),
  .ca_db_exception        (ca_db_exception      ),
  .excpn_hld_halt         (excpn_hld_halt       ),
  .ca_triple_fault_set    (ca_triple_fault_set  ),
  .holdup_excpn_r         (holdup_excpn_r       ),
  .holdup_excpn_nxt       (holdup_excpn_nxt     ),
  .ca_uop_active_set      (ca_uop_active_set    ),
  .hlt_issue_reset        (hlt_issue_reset      ),
  .ar_aux_intvbase_r      (ar_aux_intvbase_r    ),
  .ar_aux_status32_r      (ar_aux_status32_r    ),
  .ar_aux_user_mode_r     (ar_aux_user_mode_r   ),
  .ar_aux_debug_r         (ar_aux_debug_r       ),
  .ar_aux_bta_r           (ar_aux_bta_r         ),
  .sp_aux_status32_r      (ar_aux_status32_r    ), 
  .wa_aux_status32_r      (wa_aux_status32_r    ), 
  .ar_tags_empty_r        (ar_tags_empty_r      ),

  .x2_fa0_transl          (x2_fa0_transl        ),
  .x3_lr_op_r             (x3_lr_op_r            ),
  .x3_sr_op_r             (x3_sr_op_r            ),
  .aux_mmu_ren_r          (aux_mmu_ren_r         ),
  .aux_mmu_raddr_r        (aux_mmu_raddr_r       ),
  .x3_src0_r              (x3_src0_r             ),

  .dmp_dc3_dtlb_efa       (dmp_dc3_dtlb_efa      ),
  .dc3_dtlb_miss_excpn_r  (dc3_dtlb_miss_excpn_r ),
  .dc3_dtlb_ovrlp_excpn_r (dc3_dtlb_ovrlp_excpn_r),
  .dc3_dtlb_protv_excpn_r (dc3_dtlb_protv_excpn_r),
  .dc3_dtlb_ecc_excpn_r   (dc3_dtlb_ecc_excpn_r  ),
  .al_ifu_err_nxtpg       (al_ifu_err_nxtpg      ),
  .da_in_dslot_r          (da_in_dslot_r         ),
  .da_orphan_dslot_r      (da_orphan_dslot_r     ),
  .sa_link_r              (sa_link_r             ),
  .ca_seq_pc_nxt          (ca_seq_pc_nxt         ),

  .ca_tlb_miss_excpn      (ca_tlb_miss_excpn     ),
  .ca_tlb_miss_efa        (ca_tlb_miss_efa       ),
  .ca_m_chk_excpn         (ca_m_chk_excpn        ),

  .ar_aux_irq_act_r       (ar_aux_irq_act_r     ),
  .pipe_block_ints        (pipe_block_ints      ),
  .ar_pc_r                (ar_pc_r              ),
  .ar_pc_nxt              (ar_pc_nxt            ),
  .ar_aux_erstatus_r      (ar_aux_erstatus_r    ),
  .ar_aux_eret_r          (ar_aux_eret_r        ),
  .ar_aux_ecr_r           (ar_aux_ecr_r         ),
  .ar_aux_efa_r           (ar_aux_efa_r         ),
  .ar_aux_efae_r          (ar_aux_efae_r        ),
  .wa_pc                  (wa_pc                ),
  .ar_aux_erbta_r         (ar_aux_erbta_r       ),
  .x2_restart_r           (x2_restart_r         ),
  .wa_restart_r           (wa_restart_r         ),
  .hlt_restart            (hlt_restart          ),
  .wa_restart_kill_r      (wa_restart_kill_r    ),
  .wa_sleep               (wa_sleep_r           ),
  .x2_valid_r             (x2_valid_r           ),
  .x2_uop_inst_r          (x2_uop_inst_r        ),
  .x2_invalid_instr_r     (x2_invalid_instr_r   ),
  .x2_illegal_operand_r   (x2_illegal_operand_r ),
  .x2_jump_r              (x2_jump_r            ),
  .x2_has_limm_r          (x2_has_limm_r        ),
  .x2_rtie_op_r           (x2_rtie_op_r         ),
  .x2_leave_op_r          (x2_leave_op_r        ),
  .da_uop_u7_pcl          (da_uop_u7_pcl        ),
  .x2_rel_branch_r        (x2_rel_branch_r      ),
  .x2_kernel_op_r         (x2_kernel_op_r       ),
  .x2_rgf_link_r          (x2_rgf_link_r        ),
  .x2_brk_op_r            (x2_brk_op_r          ),
  .x2_multi_op_r          (x2_multi_op_r        ),
  .x2_btab_op_r           (x2_btab_op_r         ),
  .x1_in_dslot_r          (x1_in_dslot_r        ),
  .x2_in_dslot_r          (x2_in_dslot_r        ),
  .x2_ei_op_r             (x2_ei_op_r           ),
  .x2_in_eslot_r          (x2_in_eslot_r        ),
  .x2_loop_op_r           (x2_loop_op_r         ),
  .x2_zol_ill_seq_r       (x2_zol_ill_seq_r     ),
  .x3_valid_r             (x3_valid_r           ),
  .x3_uop_inst_r          (x3_uop_inst_r        ),
  .x3_load_r              (x3_load_r            ),
  .x3_store_r             (x3_store_r           ),

  .x3_pref_r              (x3_pref_r            ),
  .x3_mem_addr_r          (x3_mem_addr_r        ),
  .x3_predicate_r         (x3_predicate_r       ),
  .x2_load_r              (x2_load_r            ),
  .x2_store_r             (x2_store_r           ),
  .x2_size_r              (x2_size_r            ),
  .x2_pref_r              (x2_pref_r            ),
  .x2_locked_r            (x2_locked_r          ),
  .x2_mem_addr_r          (x2_mem_addr_r        ),

  .x3_div_op_r            (x3_div_op_r          ),
  .div_divz_r             (div_divz_r           ),
  .x3_iprot_viol_r        (x3_iprot_viol_r      ),
  .eia_x2_is_eia_instr    ( eia_x2_is_eia_instr ),
  .eia_x2_kernel_cc       ( eia_x2_kernel_cc    ),
  .eia_x2_kernel_cr       ( eia_x2_kernel_cr    ),
  .eia_x3_kernel_param    ( eia_x3_kernel_param ),
  .wa_sr_data_r           (wa_sr_data_r         ),
  .wa_erstatus_wen        (wa_erstatus_wen      ),
  .wa_eret_wen            (wa_eret_wen          ),
  .wa_erbta_wen           (wa_erbta_wen         ),
  .wa_ecr_wen             (wa_ecr_wen           ),
  .wa_efa_wen             (wa_efa_wen           ),
  .wa_efae_wen            (wa_efae_wen          ),
  .al_pass                (al_pass              ),
  .al_exception           (al_exception         ),
  .al_excpn_type          (al_excpn_type        ),
  .al_excpn_info          (al_excpn_info        ),
  .ca_uop_inprol_r        (ca_uop_inprol_r      ),
  .dc3_excpn              (dc3_excpn            ),
  .dc3_excpn_type         (dc3_excpn_type       ),
  .dc3_excpn_code         (dc3_excpn_code       ),
  .x3_aux_unimpl_r        (x3_aux_unimpl_r      ),
  .x3_aux_illegal_r       (x3_aux_illegal_r     ),
  .x3_aux_k_ro_r          (x3_aux_k_ro_r        ),
  .x3_aux_k_wr_r          (x3_aux_k_wr_r        ),
  .ca_replay              (ca_replay            ),
  .ca_dc4_replay          (ca_dc4_replay        ),
  .dc4_excpn              (dc4_excpn            ),
  .dc4_excpn_mem_addr     (dc4_excpn_mem_addr   ),
  .dc4_excpn_type         (dc4_excpn_type       ),
  .dc4_excpn_user_mode_r  (dc4_excpn_user_mode_r),
  .ca_mem_addr_r          (ca_mem_addr_r        ),
  .x3_mpu_iprotv_r        (x3_mpu_iprotv_r      ),
  .x3_mpu_dprotv_r        (x3_mpu_dprotv_r      ),
  .x3_mpu_efa_r           (x3_mpu_efa_r         ),
  .ca_mpu_excpn_r         (ca_mpu_excpn_r       ),
  .x3_sc_protv_r          (x3_sc_protv_r        ),
  .x3_sc_efa_r            (x3_sc_efa_r          ),
  .ca_valid_r             (ca_valid_r           ),
  .ca_trap_op_r           (ca_trap_op_r         ),
  .ca_rtie_op_r           (ca_rtie_op_r         ),
  .ca_cmt_norm_evt        (ca_cmt_norm_evt      ),
  .ca_cmt_uop_evt         (ca_cmt_uop_evt       ),
  .ca_uop_commit_r        (ca_uop_commit_r      ),
  .ca_uop_active_r        (ca_uop_active_r      ),
  .ca_byte_size_r         (ca_byte_size_r       ),
  .ca_cmt_isi_evt         (ca_cmt_isi_evt       ),
  .ct_replay              (ct_replay            ),
  .ca_src1_r              (ca_src1_r            ),

  .ca_load_r              (ca_load_r            ),
  .ca_store_r             (ca_store_r           ),
  .ca_lr_op_r             (ca_lr_op_r           ),
  .ca_sr_op_r             (ca_sr_op_r           ),
  .al_uop_epil            (al_uop_epil          ),
  .al_uop_has_limm        (al_uop_has_limm      ),
  .da_uop_busy_r          (da_uop_busy_r        ),
  .da_kill                (da_kill              ),
  .da_enable              (da_enable            ),
  .da_pass                (da_pass              ),
  .da_holdup              (da_holdup            ),
  .sa_kill                (sa_kill              ),
  .sa_enable              (sa_enable            ),
  .sa_pass                (sa_pass              ),
  .x1_kill                (x1_kill              ),
  .x1_enable              (x1_enable            ),
  .x1_pass                (x1_pass              ),
  .x2_kill                (x2_kill              ),
  .x2_enable              (x2_enable            ),
  .x2_pass                (x2_pass              ),
  .x3_kill                (x3_kill              ),
  .x3_enable              (x3_enable            ),
  .x3_pass                (x3_pass              ),
  .ca_enable              (ca_enable            ),
  .ca_pass                (ca_pass              ),
  .ca_kill                (ca_kill              ),
  .x2_error_branch_r      (x2_error_branch_r    ),
  .x3_error_branch_r      (x3_error_branch_r    ),
  .ca_in_deslot           (ca_in_deslot         ),
  .ca_zol_lp_jmp          (ca_zol_lp_jmp        ),
  .ar_aux_lp_start_r      (ar_aux_lp_start_r    ),
  .irq_req                (irq_req              ),
  .irq_num                (irq_num              ),
  .irq_w                  (irq_w                ),
  .irq_preempts           (irq_preempts         ),
  .cpu_accept_irq         (cpu_accept_irq       ),
  .cpu_irq_select         (cpu_irq_select       ),
  .irq_ack_w_r            (irq_ack_w_r          ),
  .irq_ack                (irq_ack              ),
  .irq_ack_num            (irq_ack_num          ),
  .int_evts               (int_evts             ),
  .ca_irq_act_nxt         (ca_irq_act_nxt       ),
  .sp_kinv_r              (sp_kinv_r            ),
  .int_rtie_replay_r      (int_rtie_replay_r    ),
  .int_ilink_evt          (int_ilink_evt        ),
  .al_uop_sirq_haz        (al_uop_sirq_haz      ),
  .int_load_active        (int_load_active      ),
  .int_preempt            (int_preempt          ),
  .aps_hit_if             (aps_hit_if           ),
  .aps_hit_mr             (aps_hit_mr           ),
  .aps_active             (aps_active           ), 
  .aps_pcbrk              (aps_pcbrk            ), 
  .ca_ap_excpn_r          (ca_ap_excpn_r        ),
  .excpn_in_prologue      (excpn_in_prologue    ),

  .da_ifu_exception_r     (da_ifu_exception_r   ),
  .da_ifu_err_nxtpg_r     (da_ifu_err_nxtpg_r   ),
  .x2_excpn_stall         (x2_excpn_stall       ),
  .ct_excpn_trap_r        (ct_excpn_trap_r      ),
  .ct_excpn_trap_nxt      (ct_excpn_trap_nxt    ),
  .in_dbl_fault_excpn_r   (in_dbl_fault_excpn_r  ),
  .excpn_evts             (excpn_evts           ),
  .excpn_in_prologue_r    (excpn_in_prologue_r  ),
  .excpn_exit_evt         (excpn_exit_evt       ),
  .mem_excpn_ack_r        (mem_excpn_ack_r      ),
  .excpn_restart          (excpn_restart        ),
  .excpn_restart_pc       (excpn_restart_pc     ),
  .wa_restart_vec_r       (wa_restart_vec_r     ),
  .wa_restart_cmd_r       (wa_restart_cmd_r     )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Auxiliary Control (alb_aux_ctrl) module instantiation                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_aux_ctrl u_alb_aux_ctrl (
  // X2 Stage Control
  .x2_pass                (x2_pass              ),
  .x2_aux_addr_r          (x2_aux_addr_r        ),
  .x2_lr_op_r             (x2_lr_op_r           ),
  .x2_sr_op_r             (x2_sr_op_r           ),
  // X3 Stage Control
  .x3_pass                (x3_pass              ),
  .x3_enable              (x3_enable            ),
  .x3_lr_op_r             (x3_lr_op_r           ),
  .x3_sr_op_r             (x3_sr_op_r           ),
  .aux_x3_stall           (aux_x3_stall         ),
  .fch_restart            (wa_restart_r         ),

  // CA Stage Control
  .ca_pass                (ca_pass              ),
  .ca_enable              (ca_enable            ),
  .ca_lr_op_r             (ca_lr_op_r           ),
  .ca_sr_op_r             (ca_sr_op_r           ),
  .ca_aux_cond            (ca_aux_cond          ),

  // WA Stage Control
  .wa_enable              (wa_enable            ),
  .wa_sr_op_r             (wa_sr_op_r           ),

  // AUX <-> EXU IF
  .aux_ca_lr_data         (aux_ca_lr_data       ),
  .aux_ca_serial_sr       (aux_ca_serial_sr     ),
   .aux_ca_strict_sr       (aux_ca_strict_sr     ),

  .aux_x2_r4_sr           (aux_x2_r4_sr         ),
  .aux_x3_r4_sr_r         (aux_x3_r4_sr_r       ),
  .aux_ca_r4_sr_r         (aux_ca_r4_sr_r       ),

  .aux_core_ren_r         (aux_core_ren_r       ),
  .aux_cr1_ren_r          (aux_cr1_ren_r        ),
  .aux_cr2_ren_r          (aux_cr2_ren_r        ),
  .aux_cr3_ren_r          (aux_cr3_ren_r        ),
  .aux_cr4_ren_r          (aux_cr4_ren_r        ),
  .aux_cr5_ren_r          (aux_cr5_ren_r        ),
  .aux_core_raddr_r       (aux_core_raddr_r     ),
  .aux_core_wen_r         (aux_core_wen_r       ),
  .aux_core_waddr_r       (aux_core_waddr_r     ),

  .core_aux_rdata         (core_aux_rdata       ),
  .core_aux_illegal       (core_aux_illegal     ),
  .core_aux_k_rd          (core_aux_k_rd        ),
  .core_aux_k_wr          (core_aux_k_wr        ),
  .core_aux_unimpl        (core_aux_unimpl      ),
  .core_aux_serial_sr     (core_aux_serial_sr   ),
  .core_aux_strict_sr     (core_aux_strict_sr   ),
  .core_aux_stall         (core_aux_stall       ),

  .aux_bcr_ren_r          (aux_bcr_ren_r        ),
  .aux_bcr_raddr_r        (aux_bcr_raddr_r      ),
  .bcr_aux_rdata          (bcr_aux_rdata        ),
  .bcr_aux_illegal        (bcr_aux_illegal      ),
  .bcr_aux_k_rd           (bcr_aux_k_rd         ),

  .dmp_aux_sr_op          (dmp_aux_sr_op        ),
 
  .aux_dc_ren_r           (aux_dc_ren_r         ),
  .aux_dc_raddr_r         (aux_dc_raddr_r       ),
  .aux_dc_wen_r           (aux_dc_wen_r         ),
  .aux_dc_waddr_r         (aux_dc_waddr_r       ),
  .dc_aux_rdata           (dc_aux_rdata         ),
  .dc_aux_illegal         (dc_aux_illegal       ),
  .dc_aux_k_rd            (dc_aux_k_rd          ),
  .dc_aux_k_wr            (dc_aux_k_wr          ),
  .dc_aux_unimpl          (dc_aux_unimpl        ),
  .dc_aux_serial_sr       (dc_aux_serial_sr     ),
  .dc_aux_strict_sr       (dc_aux_strict_sr     ),
  .dc_aux_busy            (dc_aux_busy          ),
  
  .aux_eia_ren_r          (aux_eia_ren_r        ),
  .aux_eia_raddr_r        (aux_eia_raddr_r      ),
  .aux_eia_wen_r          (aux_eia_wen_r        ),
  .aux_eia_waddr_r        (aux_eia_waddr_r      ),
  .eia_aux_rdata          (eia_aux_rdata        ),
  .eia_aux_illegal        (eia_aux_illegal      ),
  .eia_aux_k_rd           (eia_aux_k_rd         ),
  .eia_aux_k_wr           (eia_aux_k_wr         ),
  .eia_aux_unimpl         (eia_aux_unimpl       ),
  .eia_aux_serial_sr      (eia_aux_serial_sr    ),
  .eia_aux_strict_sr      (eia_aux_strict_sr    ),
  .eia_aux_stall          (eia_aux_stall        ),

  .aux_ic_ren_r           (aux_ic_ren_r         ),
  .aux_ic_raddr_r         (aux_ic_raddr_r       ),
  .aux_ic_wen_r           (aux_ic_wen_r         ),
  .aux_ic_waddr_r         (aux_ic_waddr_r       ),
  .ic_aux_rdata           (ic_aux_rdata         ),
  .ic_aux_illegal         (ic_aux_illegal       ),
  .ic_aux_k_rd            (ic_aux_k_rd          ),
  .ic_aux_k_wr            (ic_aux_k_wr          ),
  .ic_aux_unimpl          (ic_aux_unimpl        ),
  .ic_aux_serial_sr       (ic_aux_serial_sr     ),
  .ic_aux_strict_sr       (ic_aux_strict_sr     ),

  .aux_bpu_ren_r          (aux_bpu_ren_r        ),
  .aux_bpu_raddr_r        (aux_bpu_raddr_r      ),
  .aux_bpu_wen_r          (aux_bpu_wen_r        ),
  .aux_bpu_waddr_r        (aux_bpu_waddr_r      ),
  .bpu_aux_rdata          (bpu_aux_rdata        ),
  .bpu_aux_illegal        (bpu_aux_illegal      ),
  .bpu_aux_k_rd           (bpu_aux_k_rd         ),
  .bpu_aux_k_wr           (bpu_aux_k_wr         ),
  .bpu_aux_unimpl         (bpu_aux_unimpl       ),
  .bpu_aux_serial_sr      (bpu_aux_serial_sr    ),
  .bpu_aux_strict_sr      (bpu_aux_strict_sr    ),

  .aux_smt_active         (aux_smt_active       ),       
  .aux_smt_ren_r          (aux_smt_ren_r        ),
  .aux_smt_raddr_r        (aux_smt_raddr_r      ),
  .aux_smt_wen_r          (aux_smt_wen_r        ),
  .aux_smt_waddr_r        (aux_smt_waddr_r      ),
  .smt_aux_rdata          (smt_aux_rdata        ),
  .smt_aux_illegal        (smt_aux_illegal      ),
  .smt_aux_k_rd           (smt_aux_k_rd         ),
  .smt_aux_k_wr           (smt_aux_k_wr         ),
  .smt_aux_unimpl         (smt_aux_unimpl       ),
  .smt_aux_serial_sr      (smt_aux_serial_sr    ),
  .smt_aux_strict_sr      (smt_aux_strict_sr    ),

  .aux_rtt_active         (aux_rtt_active       ),       
  .aux_rtt_ren_r          (aux_rtt_ren_r        ),
  .aux_rtt_raddr_r        (aux_rtt_raddr_r      ),
  .aux_rtt_wen_r          (aux_rtt_wen_r        ),
  .aux_rtt_waddr_r        (aux_rtt_waddr_r      ),
  .rtt_aux_rdata          (rtt_aux_rdata        ),
  .rtt_aux_illegal        (rtt_aux_illegal      ),
  .rtt_aux_k_rd           (rtt_aux_k_rd         ),
  .rtt_aux_k_wr           (rtt_aux_k_wr         ),
  .rtt_aux_unimpl         (rtt_aux_unimpl       ),
  .rtt_aux_serial_sr      (rtt_aux_serial_sr    ),
  .rtt_aux_strict_sr      (rtt_aux_strict_sr    ),



  .aux_tm0_ren_r          (aux_tm0_ren_r        ),
  .aux_tm0_raddr_r        (aux_tm0_raddr_r      ),
  .aux_tm0_wen_r          (aux_tm0_wen_r        ),
  .aux_tm0_waddr_r        (aux_tm0_waddr_r      ),
  .tm0_aux_rdata          (tm0_aux_rdata        ),
  .tm0_aux_illegal        (tm0_aux_illegal      ),
  .tm0_aux_k_rd           (tm0_aux_k_rd         ),
  .tm0_aux_k_wr           (tm0_aux_k_wr         ),
  .tm0_aux_unimpl         (tm0_aux_unimpl       ),
  .tm0_aux_serial_sr      (tm0_aux_serial_sr    ),

  .aux_timer_active      (aux_timer_active      ),   

  .aux_irq_ren_r          (aux_irq_ren_r        ),
  .aux_irq_raddr_r        (aux_irq_raddr_r      ),
  .aux_irq_wen_r          (aux_irq_wen_r        ),
  .aux_irq_waddr_r        (aux_irq_waddr_r      ),
  .irq_aux_rdata          (irq_aux_rdata        ),
  .irq_aux_illegal        (irq_aux_illegal      ),
  .irq_aux_k_rd           (irq_aux_k_rd         ),
  .irq_aux_k_wr           (irq_aux_k_wr         ),
  .irq_aux_unimpl         (irq_aux_unimpl       ),
  .irq_aux_serial_sr      (irq_aux_serial_sr    ),
  .irq_aux_strict_sr      (irq_aux_strict_sr    ),

  .x2_rtie_op_r           (x2_rtie_op_r         ),
  .x3_rtie_op_r           (x3_rtie_op_r         ),

  .aux_wdt_ren_r          (aux_wdt_ren_r        ),
  .aux_wdt_raddr_r        (aux_wdt_raddr_r      ),
  .aux_wdt_wen_r          (aux_wdt_wen_r        ),
  .aux_wdt_waddr_r        (aux_wdt_waddr_r      ),
  .wdt_aux_rdata          (wdt_aux_rdata        ),
  .wdt_aux_illegal        (wdt_aux_illegal      ),
  .wdt_aux_k_rd           (wdt_aux_k_rd         ),
  .wdt_aux_k_wr           (wdt_aux_k_wr         ),
  .wdt_aux_unimpl         (wdt_aux_unimpl       ),
  .wdt_aux_serial_sr      (wdt_aux_serial_sr    ),
  .wdt_aux_strict_sr      (wdt_aux_strict_sr    ),

  .aux_rtc_ren_r          (aux_rtc_ren_r        ),
  .aux_rtc_raddr_r        (aux_rtc_raddr_r      ),
  .aux_rtc_wen_r          (aux_rtc_wen_r        ),
  .aux_rtc_waddr_r        (aux_rtc_waddr_r      ),
  .rtc_aux_rdata          (rtc_aux_rdata        ),
  .rtc_aux_illegal        (rtc_aux_illegal      ),
  .rtc_aux_k_rd           (rtc_aux_k_rd         ),
  .rtc_aux_k_wr           (rtc_aux_k_wr         ),
  .rtc_aux_unimpl         (rtc_aux_unimpl       ),
  .rtc_aux_serial_sr      (rtc_aux_serial_sr    ),
  .rtc_aux_strict_sr      (rtc_aux_strict_sr    ),

  .aux_pct_active         (aux_pct_active       ),       
  .aux_pct_ren_r          (aux_pct_ren_r        ),
  .aux_pct_raddr_r        (aux_pct_raddr_r      ),
  .aux_pct_wen_r          (aux_pct_wen_r        ),
  .aux_pct_waddr_r        (aux_pct_waddr_r      ),
  .pct_aux_rdata          (pct_aux_rdata        ),
  .pct_aux_illegal        (pct_aux_illegal      ),
  .pct_aux_k_rd           (pct_aux_k_rd         ),
  .pct_aux_k_wr           (pct_aux_k_wr         ),
  .pct_aux_unimpl         (pct_aux_unimpl       ),
  .pct_aux_serial_sr      (pct_aux_serial_sr    ),
  .pct_aux_strict_sr      (pct_aux_strict_sr    ),

  .aux_mpu_ren_r          (aux_mpu_ren_r        ),
  .aux_mpu_raddr_r        (aux_mpu_raddr_r      ),
  .aux_mpu_wen_r          (aux_mpu_wen_r        ),
  .aux_mpu_waddr_r        (aux_mpu_waddr_r      ),
  .mpu_aux_rdata          (mpu_aux_rdata        ),
  .mpu_aux_illegal        (mpu_aux_illegal      ),
  .mpu_aux_k_rd           (mpu_aux_k_rd         ),
  .mpu_aux_k_wr           (mpu_aux_k_wr         ),
  .mpu_aux_unimpl         (mpu_aux_unimpl       ),
  .mpu_aux_serial_sr      (mpu_aux_serial_sr    ),
  .mpu_aux_strict_sr      (mpu_aux_strict_sr    ),

  .aux_mmu_ren_r          (aux_mmu_ren_r        ),
  .aux_mmu_raddr_r        (aux_mmu_raddr_r      ),
  .aux_mmu_wen_r          (aux_mmu_wen_r        ),
  .aux_mmu_waddr_r        (aux_mmu_waddr_r      ),
  .mmu_aux_rdata          (mmu_aux_rdata        ),
  .mmu_aux_illegal        (mmu_aux_illegal      ),
  .mmu_aux_k_rd           (mmu_aux_k_rd         ),
  .mmu_aux_k_wr           (mmu_aux_k_wr         ),
  .mmu_aux_unimpl         (mmu_aux_unimpl       ),
  .mmu_aux_serial_sr      (mmu_aux_serial_sr    ),
  .mmu_aux_strict_sr      (mmu_aux_strict_sr    ),

  .aux_dccm_ren_r         (aux_dccm_ren_r       ),
  .aux_dccm_wen_r         (aux_dccm_wen_r       ),
  .dccm_aux_rdata         (dccm_aux_rdata       ),
  .dccm_aux_illegal       (dccm_aux_illegal     ),
  .dccm_aux_k_rd          (dccm_aux_k_rd        ),
  .dccm_aux_k_wr          (dccm_aux_k_wr        ),
  .dccm_aux_unimpl        (dccm_aux_unimpl      ),
  .dccm_aux_serial_sr     (dccm_aux_serial_sr   ),
  .dccm_aux_strict_sr     (dccm_aux_strict_sr   ),

  .aux_dper_ren_r         (aux_dper_ren_r       ),
  .aux_dper_raddr_r       (aux_dper_raddr_r     ),
  .aux_dper_wen_r         (aux_dper_wen_r       ),
  .aux_dper_waddr_r       (aux_dper_waddr_r     ),
  .dper_aux_rdata         (dper_aux_rdata       ),
  .dper_aux_illegal       (dper_aux_illegal     ),
  .dper_aux_k_rd          (dper_aux_k_rd        ),
  .dper_aux_k_wr          (dper_aux_k_wr        ),
  .dper_aux_unimpl        (dper_aux_unimpl      ),
  .dper_aux_serial_sr     (dper_aux_serial_sr   ),
  .dper_aux_strict_sr     (dper_aux_strict_sr   ),
  .aux_aps_active        (aux_aps_active        ),       
  .aux_aps_ren_r         (aux_aps_ren_r         ),
  .aux_aps_raddr_r       (aux_aps_raddr_r       ),
  .aux_aps_wen_r         (aux_aps_wen_r         ),
  .aux_aps_waddr_r       (aux_aps_waddr_r       ),
  .aps_aux_rdata         (aps_aux_rdata         ),
  .aps_aux_illegal       (aps_aux_illegal       ),
  .aps_aux_k_rd          (aps_aux_k_rd          ),
  .aps_aux_k_wr          (aps_aux_k_wr          ),
  .aps_aux_unimpl        (aps_aux_unimpl        ),
  .aps_aux_serial_sr     (aps_aux_serial_sr     ),
  .aps_aux_strict_sr     (aps_aux_strict_sr     ),

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


  .x3_aux_unimpl_r       (x3_aux_unimpl_r       ),
  .x3_aux_illegal_r      (x3_aux_illegal_r      ),
  .x3_aux_k_ro_r         (x3_aux_k_ro_r         ),
  .x3_aux_k_wr_r         (x3_aux_k_wr_r         ),

  .wa_aux_rtt_addr_r         (wa_aux_addr_r         ),


  .clk                   (clk                   ),
  .rst_a                 (rst_a                 )
);


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Build Configuration Registers (alb_bc_regs) module instantiation         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_bc_regs u_alb_bc_regs (
  .rtt_src_num          (rtt_src_num            ),

  .intvbase_in_r          (intvbase_in_r        ),
  .aux_bcr_ren_r        (aux_bcr_ren_r          ),
  .aux_write            (x3_sr_op_r             ),
  .aux_bcr_raddr_r      (aux_bcr_raddr_r        ),
  .bcr_aux_rdata        (bcr_aux_rdata          ),
  .bcr_aux_illegal      (bcr_aux_illegal        ),
  .bcr_aux_k_rd         (bcr_aux_k_rd           )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Core Auxiliary Registers (alb_aux_reg) module instantiation              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_aux_regs u_alb_aux_regs (
  .clk                    (clk                  ),
  .rst_a                  (rst_a                ),
  .arcnum                 (arcnum               ),
  .clusternum             (clusternum           ), 
  .intvbase_in            (intvbase_in          ),
  .intvbase_in_r          (intvbase_in_r        ),
  .aux_write              (x3_sr_op_r           ),
  .aux_cr1_ren_r          (aux_cr1_ren_r        ),
  .aux_cr2_ren_r          (aux_cr2_ren_r        ),
  .aux_cr3_ren_r          (aux_cr3_ren_r        ),
  .aux_cr4_ren_r          (aux_cr4_ren_r        ),
  .aux_cr5_ren_r          (aux_cr5_ren_r        ),
  .aux_core_raddr_r       (aux_core_raddr_r     ),
  .aux_core_wen_r         (aux_core_wen_r       ),
  .aux_core_waddr_r       (aux_core_waddr_r     ),
  .wa_sr_data_r           (wa_sr_data_r         ),
  .ca_src1_r              (ca_src1_r            ),
  .core_aux_rdata         (core_aux_rdata       ),
  .core_aux_illegal       (core_aux_illegal     ),
  .core_aux_k_rd          (core_aux_k_rd        ),
  .core_aux_k_wr          (core_aux_k_wr        ),
  .core_aux_unimpl        (core_aux_unimpl      ),
  .core_aux_serial_sr     (core_aux_serial_sr   ),
  .core_aux_strict_sr     (core_aux_strict_sr   ),
  .core_aux_stall         (core_aux_stall       ),
  .sys_halt_ack_r         (sys_halt_ack_r       ),
  .db_active_r            (db_active_r          ),
  .dbg_halt_r             (dbg_halt_r           ),

  .x3_src0_r              (x3_src0_r            ),
  .ar_pc_r                (ar_pc_r              ),
  .ca_target_r            (ca_target_r          ),
  .ecc_flt_status         (ecc_flt_status       ),
  .ar_aux_ecc_ctrl_r      (ar_aux_ecc_ctrl_r    ), 
  .ecc_sbe_count_r        (ecc_sbe_count_r      ),
  .ecc_sbe_clr            (ecc_sbe_clr          ),
  .ecc_sbe_dmp_clr        (ecc_sbe_dmp_clr      ),
  .ar_aux_status32_r      (ar_aux_status32_r    ),
  .ca_aux_s32_stall       (ca_aux_s32_stall     ),
  .ar_aux_erstatus_r      (ar_aux_erstatus_r    ),
  .ar_aux_eret_r          (ar_aux_eret_r        ),
  .ar_aux_ecr_r           (ar_aux_ecr_r         ),
  .ar_aux_erbta_r         (ar_aux_erbta_r       ),
  .ar_aux_efa_r           (ar_aux_efa_r         ),
  .ar_aux_efae_r          (ar_aux_efae_r        ),
  .wa_aux_status32_nxt    (wa_aux_status32_nxt  ),
  .wa_aux_status32_pass   (wa_aux_status32_pass ),
  .wa_aux_status32_r      (wa_aux_status32_r    ),


  .wa_status32_wen        (wa_status32_wen      ),
  .ca_in_kflag            (ca_in_kflag          ),
  .wa_debug_wen           (wa_debug_wen         ),
  .wa_erstatus_wen        (wa_erstatus_wen      ),
  .wa_eret_wen            (wa_eret_wen          ),
  .wa_erbta_wen           (wa_erbta_wen         ),
  .wa_ecr_wen             (wa_ecr_wen           ),
  .wa_efa_wen             (wa_efa_wen           ),
  .wa_efae_wen            (wa_efae_wen          ),
  .ca_cmt_brk_evt         (ca_cmt_brk_evt       ),
  .ca_normal_evt          (wa_cmt_norm_evt_nxt  ),
  .ca_sleep_evt           (ca_sleep_evt         ),
  .ca_wevt_evt            (ca_wevt_evt          ),
  .ca_wlfc_evt            (ca_wlfc_evt          ),
  .sleep_hlt_wake         (sleep_hlt_wake       ),
  .wevt_wakeup_r          (wevt_wakeup_r        ),
  .wlfc_wakeup            (wlfc_wakeup          ),
  .ca_uop_evt             (wa_cmt_uop_evt_nxt   ),
  .excpn_evts             (excpn_evts           ),
  .ca_ei_op_r             (ca_ei_op_r           ),
  .cmt_0_ei_evt           (cmt_ei_evt           ),
  .ca_finish_sgl_step     (ca_finish_sgl_step   ),
  .ca_dslot_r             (ca_dslot_r           ),
  .ca_br_taken            (ca_br_taken          ),
  .ca_br_target           (ca_br_target         ),
  .ca_lp_end_nxt          (ca_lp_end_nxt        ),
  .ca_loop_op_r           (ca_loop_op_r         ), 
  .ca_brk_op_r            (ca_brk_op_r          ),
  .ca_loop_evt            (ca_loop_evt          ),
  .ca_seq_pc_nxt          (ca_seq_pc_nxt        ),
  .ca_aux_pc_wen          (wa_aux_pc_wen        ),
  .ar_aux_bta_r           (ar_aux_bta_r         ),
  .aux_memseg_r           (aux_memseg_r         ),
  .ar_aux_stack_base_r    (ar_aux_stack_base_r  ),
  .ar_aux_stack_top_r     (ar_aux_stack_top_r   ),
  .ar_sc_r                (ar_sc_r              ),
  .ar_ae_r                (ar_ae_r              ),

  .ar_asr_r               (ar_asr_r             ), 

  .aps_aux_written        (aps_aux_written      ), 
  .aps_aux_serial_sr      (aps_asr_serial       ),
  .aps_status             (aps_status           ),
  .ca_ap_excpn_r          (ca_ap_excpn_r        ),
  .aps_halt_ack           (aps_halt_ack         ),
  .ar_aux_jli_base_r      (ar_aux_jli_base_r    ),
  .ar_aux_ldi_base_r      (ar_aux_ldi_base_r    ),
  .ar_aux_ei_base_r       (ar_aux_ei_base_r     ),

  .ar_aux_irq_ctrl_r      (ar_aux_irq_ctrl_r    ),
  .ar_aux_irq_ctrl_upt_r  (ar_aux_irq_ctrl_upt_r),
  .irq_ctrl_wen           (irq_ctrl_wen         ),
  .wa_uopld_jli_base      (wa_uopld_jli_base    ),
  .wa_uopld_ldi_base      (wa_uopld_ldi_base    ),
  .wa_uopld_ei_base       (wa_uopld_ei_base     ),
  .wa_uopld_lp_start      (wa_uopld_lp_start    ),
  .wa_uopld_lp_end        (wa_uopld_lp_end      ),
  .wa_uopld_data          (wa_uopld_data        ),
  .ar_aux_icause0_r    (ar_aux_icause0_r  ),
  .ar_aux_icause1_r    (ar_aux_icause1_r  ),
  .ar_aux_icause2_r    (ar_aux_icause2_r  ),
  .ca_irq_act_nxt         (ca_irq_act_nxt       ),
  .ar_aux_irq_act_r       (ar_aux_irq_act_r     ),
  .ca_int_enter_evt       (int_evts[`npuarc_INTEVT_ENTER]),
  .ca_int_exit_evt        (int_evts[`npuarc_INTEVT_EXIT]),

  .ca_triple_fault_set    (ca_triple_fault_set  ),
  .hlt_do_unhalt          (hlt_do_unhalt        ),

  .ar_aux_debug_r         (ar_aux_debug_r       ),
  .ar_aux_debugi_r        (ar_aux_debugi_r      ),
  .dbg_we_r               (dbg_we_r             ),
  .dbg_wf_r               (dbg_wf_r             ),



  .ar_aux_intvbase_r      (ar_aux_intvbase_r    ),
  .ar_aux_lp_start_r      (ar_aux_lp_start_r    ),
  .ar_aux_lp_end_r        (ar_aux_lp_end_r      )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Memory Protection Unit (alb_mpu) instantiation                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_mpu u_alb_mpu (
  .clk                 (clk                 ), 
  .rst_a               (rst_a               ),
  .kernel_mode         (~ar_aux_status32_r[`npuarc_U_FLAG] ),
  .db_active           (db_active           ),
  .mmu_en_r            (mmu_en_r            ),
  .mpu_en_r            (mpu_en_r            ),  
  .x2_fa0_transl       (x2_fa0_transl       ),
  .x2_da0_transl       (x2_da0_transl       ),

  .sa_pass             (sa_pass             ),
  .sa_pc_r             (sa_pc               ),

  .x1_pass             (x1_pass             ),
  .x1_enable           (x1_enable           ),

  .x2_pass             (x2_pass             ),
  .x2_enable           (x2_enable           ),
  .x2_kill             (x2_kill             ),
  .x2_uop_inst_r       (x2_uop_inst_r       ),
  .x2_load_r           (x2_load_r           ), 
  .x2_store_r          (x2_store_r          ),
  .x2_pref_r           (x2_pref_r           ),
  .x2_mem_addr0_r      (x2_mem_addr_r       ),
  .x2_mpu_data_flt     (x2_mpu_data_flt     ),

  .x3_pass             (x3_pass             ),
  .x3_enable           (x3_enable           ),
  .mpu_exec_viol_r     (x3_mpu_iprotv_r     ),
  .mpu_data_viol_r     (x3_mpu_dprotv_r     ),
  .mpu_efa_r           (x3_mpu_efa_r        ),

  // MPU interface for IFU
  .ifetch_addr_mpu     (ifetch_addr_mpu     ),
  .ifetch_viol         (ifetch_viol         ),

  .int_evts            (int_evts            ),
  .irq_u_ctrl           (ar_aux_irq_ctrl_r[11]),
  .irq_u_act           (ar_aux_irq_act_r[`npuarc_IRQ_ACT_U_BIT]),
  .irq_act_nxt         (ca_irq_act_nxt[`npuarc_IRQ_ACT_ACT_RANGE]),
  .ca_rtie_op_r        (ca_rtie_op_r        ),

  .aux_mpu_wen_r       (aux_mpu_wen_r       ),
  .aux_mpu_waddr_r     (aux_mpu_waddr_r     ),
  .wa_sr_data_r        (wa_sr_data_r        ),

  .aux_mpu_ren_r       (aux_mpu_ren_r       ),
  .aux_mpu_raddr_r     (aux_mpu_raddr_r     ),
  .aux_write           (x3_sr_op_r          ),
  .mpu_aux_rdata       (mpu_aux_rdata       ),
  .mpu_aux_illegal     (mpu_aux_illegal     ),
  .mpu_aux_k_rd        (mpu_aux_k_rd        ),
  .mpu_aux_k_wr        (mpu_aux_k_wr        ),
  .mpu_aux_unimpl      (mpu_aux_unimpl      ),
  .mpu_aux_serial_sr   (mpu_aux_serial_sr   ),
  .mpu_aux_strict_sr   (mpu_aux_strict_sr   ),

  .ca_enable           (ca_enable           ),
  .ca_mpu_excpn_r      (ca_mpu_excpn_r      ),
  .ca_uop_inprol_r     (ca_uop_inprol_r     ),
  .excpn_in_prologue_r (excpn_in_prologue_r ),
  .excpn_prologue_evt  (excpn_evts[`npuarc_INTEVT_PROLOGUE])
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Fixed-point multiplier pipeline (alb_mpy_pipe) module instantiation      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_mpy_pipe u_alb_mpy_pipe (
  .clk                    (mpy_unit_clk         ),
  .rst_a                  (rst_a                ),

  .x1_pass                (x1_pass              ),
  .x1_mpy_op_r            (x1_mpy_op_r          ),
  .x1_half_size_r         (x1_half_size_r       ),
  .x1_dual_op_r           (x1_dual_op_r         ),
  .x1_vector_op_r         (x1_vector_op_r       ),
  .x1_quad_op_r           (x1_quad_op_r         ),
  .mp1_src0_nxt           (mp1_src0_nxt         ),
  .mp1_src1_nxt           (mp1_src1_nxt         ),
  .mp1_src2_nxt           (mp1_src2_nxt         ),
  .mp1_src3_nxt           (mp1_src3_nxt         ),

  .x2_enable              (x2_enable            ),
  .x2_pass                (x2_pass              ),
  .x2_mpy_op_r            (x2_mpy_op_r          ),
  .x2_signed_op_r         (x2_signed_op_r       ),
  .x2_half_size_r         (x2_half_size_r       ),
  .x2_dual_op_r           (x2_dual_op_r         ),
  .x2_vector_op_r         (x2_vector_op_r       ),
  .x2_quad_op_r           (x2_quad_op_r         ),

  .x3_enable              (x3_enable            ),
  .x3_pass                (x3_pass              ),
  .x3_mpy_op_r            (x3_mpy_op_r          ),
  .x3_half_size_r         (x3_half_size_r       ),

  .mp3_s_lo               (mp3_s_lo             ),
  .mp3_c_lo               (mp3_c_lo             ),

  .x3_acc_op_r            (x3_acc_op_r          ),
  .x3_dual_op_r           (x3_dual_op_r         ),
  .x3_vector_op_r         (x3_vector_op_r       ),
  .x3_quad_op_r           (x3_quad_op_r         ),

  .ca_enable              (ca_enable            ),
  .mp4_s_hi_r             (mp4_s_hi_r           ),
  .mp4_c_hi_r             (mp4_c_hi_r           ),
  .mp4_s_65_r             (mp4_s_65_r           ),
  .mp4_c_65_r             (mp4_c_65_r           ),
  .ca_src0_r              (ca_src0_r            ),
  .ca_src1_r              (ca_src1_r            ),
  .sel_byp_acc            (sel_byp_acc          ),
  .byp_acc_lo             (byp_acc_lo           ),
  .byp_acc_hi             (byp_acc_hi           ),

  .sa_mpy_op_r            (sa_mpy_op_r          ),
  .sa_vector_op_r         (sa_vector_op_r       ),
  .sa_half_size_r         (sa_half_size_r       ),
  .sa_dual_op_r           (sa_dual_op_r         ),
  .mpy_unit_enable        (mpy_unit_enable      ), 

  .wa_restart_r           (wa_restart_r         )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Stack Checking (alb_sc_pipe) instantiation                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_sc_pipe u_alb_sc_pipe (
  .clk                 (clk                 ),
  .rst_a               (rst_a               ),

  .ar_sc_r             (ar_sc_r             ),
  .ar_aux_stack_base_r (ar_aux_stack_base_r ),
  .ar_aux_stack_top_r  (ar_aux_stack_top_r  ),
  .db_active           (db_active           ),

  .div_busy_r          (div_busy_r          ),
  .x1_pass             (x1_pass             ),



  .x2_pass             (x2_pass             ),
  .x2_enable           (x2_enable           ),
  .x2_kill             (x2_kill             ),
  .x2_load_r           (x2_load_r           ),
  .x2_store_r          (x2_store_r          ),
  .x2_pref_r           (x2_pref_r           ),
  .x2_uop_inst_r       (x2_uop_inst_r       ),
  .x2_div_op_r         (x2_div_op_r         ),
  .x2_mem_addr_r       (x2_mem_addr_r       ),
  .x2_rf_ra0_r         (x2_rf_ra0_r         ),
  .x2_rf_renb0_r       (x2_rf_renb0_r       ),
  .x2_rf_ra1_r         (x2_rf_ra1_r         ),
  .x2_rf_renb1_r       (x2_rf_renb1_r       ),
  .x2_rf_wenb0_r       (x2_rf_wenb0_r       ),
  .x2_rf_wa0_r         (x2_rf_wa0_r         ),
  .x2_rf_wenb1_r       (x2_rf_wenb1_r       ),
  .x2_rf_wa1_r         (x2_rf_wa1_r         ),
  .x2_sc_stall         (x2_sc_stall         ),
  .dp_x2_sp_r          (dp_x2_sp_r          ),

  .x3_enable           (x3_enable           ),
  .x3_stack_viol_r     (x3_sc_protv_r       ),
  .x3_sc_efa_r         (x3_sc_efa_r         ),
  .x3_rf_wa0_r         (x3_rf_wa0_r         ),
  .x3_rf_wenb0_r       (x3_rf_wenb0_r       ),
  .x3_rf_wa1_r         (x3_rf_wa1_r         ),
  .x3_rf_wenb1_r       (x3_rf_wenb1_r       ),

  .ca_rf_wa0_r         (ca_rf_wa0_r         ),
  .ca_rf_wenb0_r       (ca_rf_wenb0_r       ),

  .wa_rf_wenb1_r       (wa_rf_wenb1_r       ),
  .wa_rf_wa1_r         (wa_rf_wa1_r         ),
  .wa_rf_wdata1_lo_r   (wa_rf_wdata1_lo_r   ),
  .wa_rf_wenb0_r       (wa_rf_wenb0_r       ),
  .wa_rf_wa0_r         (wa_rf_wa0_r         ),
  .wa_rf_wdata0_lo_r   (wa_rf_wdata0_lo_r   )   // 
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Action Points (alb_actionpoints) instantiation                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_actionpoints u_alb_actionpoints (
  .ap_unit_clk         (ap_unit_clk         ),
  .ap_aux_clk          (ap_aux_clk          ),
  .ap_unit_enable      (ap_unit_enable      ),
  .aux_aps_active      (aux_aps_active      ),

  .rst_a               (rst_a               ),
  .db_active           (db_active_r         ),
  .sys_halt_r          (gb_sys_halt_r       ),

  .aux_aps_wen_r       (aux_aps_wen_r       ),
  .aux_aps_waddr_r     (aux_aps_waddr_r     ),
  .wa_sr_data_r        (wa_sr_data_r        ),
  .aux_aps_ren_r       (aux_aps_ren_r       ),
  .aux_aps_raddr_r     (aux_aps_raddr_r     ),
  .aux_write           (x3_sr_op_r          ),
  .aps_aux_rdata       (aps_aux_rdata       ),
  .aps_aux_illegal     (aps_aux_illegal     ),
  .aps_aux_k_rd        (aps_aux_k_rd        ),
  .aps_aux_k_wr        (aps_aux_k_wr        ),
  .aps_aux_unimpl      (aps_aux_unimpl      ),
  .aps_aux_serial_sr   (aps_aux_serial_sr   ),
  .aps_aux_strict_sr   (aps_aux_strict_sr   ),

  .aps_aux_written     (aps_aux_written     ),

  .ar_ae_r             (ar_ae_r             ),

  .ar_asr_r            (ar_asr_r            ),

  .ar_aux_status32_r   (ar_aux_status32_r   ),
  .ar_aux_erstatus_r   (ar_aux_erstatus_r   ),
  .ar_aux_debug_r      (ar_aux_debug_r      ),


  .ca_ap_excpn_r       (ca_ap_excpn_r       ),
  .excpn_in_prologue   (excpn_in_prologue   ),
  .excpn_evts          (excpn_evts          ),


  .x1_pass             (x1_pass             ),

  .x1_pc_r             (x1_pc_r             ),

  .x1_iprot_viol_r     (x1_iprot_viol_r     ),
  .x1_uop_inst_r       (x1_uop_inst_r       ),

  .x2_pass             (x2_pass             ),
  .x2_enable           (x2_enable           ),
  .x2_kill             (x2_kill             ),
  .x2_lr_op_r          (x2_lr_op_r          ),
  .x2_sr_op_r          (x2_sr_op_r          ),
  .x2_load_r           (x2_load_r           ),
  .x2_store_r          (x2_store_r          ),
  .x2_mem_addr_r       (x2_mem_addr_r       ),
  .x2_aux_addr_r       (x2_aux_addr_r       ),

  .x3_pass             (x3_pass             ),
  .x3_enable           (x3_enable           ),
  .x3_kill             (x3_kill             ),
  .x3_load_r           (x3_load_r           ),
  .x3_store_r          (x3_store_r          ),
  .x3_lr_op_r          (x3_lr_op_r          ),
  .x3_sr_op_r          (x3_sr_op_r          ),

  .ca_pass             (ca_pass             ),
  .ca_enable           (ca_enable           ),
  .ca_valid_r          (ca_valid_r          ),
  .ar_pc_r             (ar_pc_r             ),


  .ca_uop_active_r     (ca_uop_active_r     ),
  .int_load_active     (int_load_active     ),
  .ca_load_r           (ca_load_r           ),
  .ca_store_r          (ca_store_r          ),
  .ca_lr_op_r          (ca_lr_op_r          ),
  .ca_sr_op_r          (ca_sr_op_r          ),
  .ca_cmt_brk_evt      (ca_cmt_brk_evt      ),
  .wa_aux_status32_nxt (wa_aux_status32_nxt ),
  .wa_aux_status32_pass (wa_aux_status32_pass ),

  .wa_enable           (wa_enable           ),
  .wa_pc               (wa_pc               ),
  .wa_lr_op_r          (wa_lr_op_r          ),
  .wa_sr_op_r          (wa_sr_op_r          ),
  .wa_store_r          (wa_store_r          ),
  .wa_load_r           (wa_load_r           ),
  .wa_pref_r           (wa_pref_r           ),

  .aps_asr_serial      (aps_asr_serial      ),


  .excpn_in_cg0 (1'b0), //alb_excpn_pipe
  .excpn_in_prologue_nxt (1'b0), //alb_excpn_pipe
  .int_load_active_nxt (1'b0), //alb_commit
  .ap_excpn_holdup (1'b0),
  .ar_aux_ecr_r        (ar_aux_ecr_r),
  .pipe_block_ints     (pipe_block_ints),
  .x2_uop_inst_r       (x2_uop_inst_r),
  .ca_kill             (ca_kill),
  .ca_uop_active_nxt   (ca_uop_active_nxt),
  .ar_pc_pass          (ar_pc_pass),
  .ca_uop_commit_r     (ca_uop_commit_r),
  .ca_cmt_uop_evt      (ca_cmt_uop_evt ),
  .ca_uop_state_cg0 (1'b0), //alb_commit
  .wa_rf_wenb0_r       (wa_rf_wenb0_r),
  .ap_tkn              (ap_tkn              ),
  .x3_aps_break_r      (x3_aps_break_r      ),
  .x3_aps_halt_r       (x3_aps_halt_r       ),
  .aps_halt_ack        (aps_halt_ack        ),
  .aps_hit_if          (aps_hit_if          ),
  .aps_hit_mr          (aps_hit_mr          ),
  .aps_halt            (aps_halt            ),
  .aps_break           (aps_break           ),
  .aps_pcbrk           (aps_pcbrk           ),
  .aps_active          (aps_active          ),
  .aps_status          (aps_status          )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Fixed-point divider pipeline (alb_div_pipe) module instantiation         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

npuarc_alb_div_pipe u_alb_div_pipe (
  .clk                    (div_unit_clk         ),
  .rst_a                  (rst_a                ),
  .div_busy_r             (div_busy_r           ),
  .x1_pass                (x1_pass              ),
  .x1_cond                (x2_predicate_nxt     ), // X1 eval cond
  .x2_enable              (x2_enable            ),
  .sa_div_op_r            (sa_div_op_r          ),
  .x1_div_op_r            (x1_div_op_r          ),
  .x1_div_kind_r          (x1_div_kind_r        ),
  .x1_signed_op_r         (x1_signed_op_r       ),
  .x2_src0_nxt            (x2_src0_nxt          ),
  .x2_src1_nxt            (x2_src1_nxt          ),
  .x2_div_op_r            (x2_div_op_r          ),
  .x3_div_op_r            (x3_div_op_r          ),
  
  .x2_kill                (x2_kill              ),
  .x3_kill                (x3_kill              ),
  .ca_kill                (ca_kill              ),
  .ca_div_op_r            (ca_div_op_r          ),
  .ca_commit              (wa_cmt_norm_evt_nxt  ),
  .ca_predicate_r         (ca_predicate_r       ),
  .div_unit_enable        (div_unit_enable      ),
  .div_divz_r             (div_divz_r           ),

  .div_grad_req           (div_grad_req         ),
  .ca_div_grad_ack        (ca_grad_ack          ),
  .ca_div_grad_tag        (ca_grad_tag          ),
 
  .div_retire_req_r       (div_retire_req       ),
  .div_retire_tag_r       (div_retire_tag       ),
  .ca_div_retire_ack      (div_retire_ack       ),
  .div_retire_result_r    (div_rf_wdata_lo      ),
  .div_retire_overflow_r  (div_retire_overflow_r),
  .div_retire_sign_r      (div_retire_sign_r    ),
  .div_retire_zero_r      (div_retire_zero_r    )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Eia Interface Logic pipeline (alb_eia_pipe) module instantiation         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// eia register dependency logic - merge all pending dest signals
assign has_dest_cr_is_ext = 
                            x1_dest_cr_is_ext & x1_valid_r |
                            x2_dest_cr_is_ext & x2_valid_r |
                            x3_dest_cr_is_ext & x3_valid_r |
                            ca_dest_cr_is_ext & ca_valid_r |
                            gb_dest_cr_is_ext;

npuarc_alb_eia_pipe u_alb_eia_pipe(

  ////////// General input signals ///////////////////////////////////////////
  //
  .clk                       ( clk                      ),
  .clk_ungated               ( clk_ungated              ),
  .rst_a                     ( rst_a                    ),

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

  .da_holdup                 ( da_holdup                ),    
  .x1_retain                 ( x1_retain                ),    
  .x2_retain                 ( x2_retain                ),    
  .x3_retain                 ( x3_retain                ),    

  .da_valid_r                ( da_valid_r               ),   
  .sa_valid_r                ( sa_valid_r               ),   
  .x1_valid_r                ( x1_valid_r               ),   
  .x2_valid_r                ( x2_valid_r               ),   
  .x3_valid_r                ( x3_valid_r               ),   
  .ca_valid_r                ( ca_valid_r               ),   

  .al_pass                   ( al_pass                  ),      
  .da_pass                   ( da_pass                  ),      
  .sa_pass                   ( sa_pass                  ),      
  .x1_pass                   ( x1_pass                  ),      
  .x2_pass                   ( x2_pass                  ),      
  .x3_pass                   ( x3_pass                  ),      
  .ca_pass                   ( ca_pass                  ),      

  .da_enable                 ( da_enable                ),    
  .sa_enable                 ( sa_enable                ),    
  .x1_enable                 ( x1_enable                ),    
  .x2_enable                 ( x2_enable                ),    
  .x3_enable                 ( x3_enable                ),    
  .ca_enable                 ( ca_enable                ),    

  .da_kill                   ( da_kill                  ),      
  .sa_kill                   ( sa_kill                  ),      
  .x1_kill                   ( x1_kill                  ),      
  .x2_kill                   ( x2_kill                  ),      
  .x3_kill                   ( x3_kill                  ),      
  .ca_kill                   ( ca_kill                  ),      

  .x1_no_eval                (x1_no_eval                ),
  .x2_predicate_nxt          (x2_predicate_nxt          ),

  .ca_commit                 ( wa_cmt_norm_evt_nxt      ),    
  .ca_predicate_r            ( ca_predicate_r           ),
  .ca_q_cond                 ( ca_q_cond                ),    

  .eia_exu_grad_req          ( eia_exu_grad_req         ),  
  .exu_eia_grad_ack          ( ca_grad_ack              ), 
  .exu_eia_grad_tag          ( ca_grad_tag              ),

  .eia_exu_retire_req        ( eia_retire_req           ),
  .eia_exu_retire_tag        ( eia_retire_tag           ),
  .eia_exu_retire_res_data   ( eia_retire_wdata_lo      ),
  .eia_exu_retire_res_flags  ( eia_retire_flags         ),
  .exu_eia_retire_ack        ( eia_retire_ack           ),

  .al_is_cond_inst           ( al_is_cond_inst          ),

  .da_group_code             ( da_group_code            ),
  .da_dop_code_32            ( da_dop_code_32           ), 
  .da_sop_code_32            ( da_sop_code_32           ), 
  .da_zop_code_32            ( da_zop_code_32           ), 
  .da_dop_code_16            ( da_dop_code_16           ), 
  .da_sop_code_16            ( da_sop_code_16           ), 
  .da_zop_code_16            ( da_zop_code_16           ), 

  .da_q_field                ( da_q_field               ),     
  .sa_q_field                ( sa_q_field_r             ),
  .x1_q_field                ( x1_q_field_r             ),
  .da_f_bit                  ( da_f_bit                 ),       

  .eia_da_valid              ( eia_da_valid             ),        
  .eia_da_src64              ( eia_da_src64             ),        
  .eia_da_multi_cycle        ( eia_da_multi_cycle       ),  
  .eia_da_illegal_cond       ( eia_da_illegal_cond      ), 
  .eia_da_flag_wen           ( eia_da_flag_wen          ),     
  .eia_da_dst_wen            ( eia_da_dst_wen           ),      
 
  .eia_da_ra0_ext            ( eia_da_ra0_ext           ), 
  .eia_da_ra1_ext            ( eia_da_ra1_ext           ), 
  .eia_da_wa0_ext            ( eia_da_wa0_ext           ), 
  .eia_da_wa1_ext            ( eia_da_wa1_ext           ), 

  .has_dest_cr_is_ext        ( has_dest_cr_is_ext       ),
  .sa_dest_cr_is_ext         ( sa_dest_cr_is_ext        ),
  .x1_dest_cr_is_ext         ( x1_dest_cr_is_ext        ),
  .x2_dest_cr_is_ext         ( x2_dest_cr_is_ext        ),
  .x3_dest_cr_is_ext         ( x3_dest_cr_is_ext        ),
  .ca_dest_cr_is_ext         ( ca_dest_cr_is_ext        ),

  .ar0_rf_valid_r         (ar0_rf_valid_r         ),
  .ar0_rf_wenb1_r         (ar0_rf_wenb1_r         ),
  .ar0_rf_wa1_r           (ar0_rf_wa1_r           ), 
  .ar0_rf_wenb1_64_r      (ar0_rf_wenb1_64_r      ),
  .ar0_dest_cr_is_ext     (ar0_dest_cr_is_ext     ),  
  .ar1_rf_valid_r         (ar1_rf_valid_r         ),
  .ar1_rf_wenb1_r         (ar1_rf_wenb1_r         ),
  .ar1_rf_wa1_r           (ar1_rf_wa1_r           ), 
  .ar1_rf_wenb1_64_r      (ar1_rf_wenb1_64_r      ),
  .ar1_dest_cr_is_ext     (ar1_dest_cr_is_ext     ),  
  .ar2_rf_valid_r         (ar2_rf_valid_r         ),
  .ar2_rf_wenb1_r         (ar2_rf_wenb1_r         ),
  .ar2_rf_wa1_r           (ar2_rf_wa1_r           ), 
  .ar2_rf_wenb1_64_r      (ar2_rf_wenb1_64_r      ),
  .ar2_dest_cr_is_ext     (ar2_dest_cr_is_ext     ),  
  .ar3_rf_valid_r         (ar3_rf_valid_r         ),
  .ar3_rf_wenb1_r         (ar3_rf_wenb1_r         ),
  .ar3_rf_wa1_r           (ar3_rf_wa1_r           ), 
  .ar3_rf_wenb1_64_r      (ar3_rf_wenb1_64_r      ),
  .ar3_dest_cr_is_ext     (ar3_dest_cr_is_ext     ),  
  .ar4_rf_valid_r         (ar4_rf_valid_r         ),
  .ar4_rf_wenb1_r         (ar4_rf_wenb1_r         ),
  .ar4_rf_wa1_r           (ar4_rf_wa1_r           ), 
  .ar4_rf_wenb1_64_r      (ar4_rf_wenb1_64_r      ),
  .ar4_dest_cr_is_ext     (ar4_dest_cr_is_ext     ),  
  .ar5_rf_valid_r         (ar5_rf_valid_r         ),
  .ar5_rf_wenb1_r         (ar5_rf_wenb1_r         ),
  .ar5_rf_wa1_r           (ar5_rf_wa1_r           ), 
  .ar5_rf_wenb1_64_r      (ar5_rf_wenb1_64_r      ),
  .ar5_dest_cr_is_ext     (ar5_dest_cr_is_ext     ),  
  .ar6_rf_valid_r         (ar6_rf_valid_r         ),
  .ar6_rf_wenb1_r         (ar6_rf_wenb1_r         ),
  .ar6_rf_wa1_r           (ar6_rf_wa1_r           ), 
  .ar6_rf_wenb1_64_r      (ar6_rf_wenb1_64_r      ),
  .ar6_dest_cr_is_ext     (ar6_dest_cr_is_ext     ),  
  .ar7_rf_valid_r         (ar7_rf_valid_r         ),
  .ar7_rf_wenb1_r         (ar7_rf_wenb1_r         ),
  .ar7_rf_wa1_r           (ar7_rf_wa1_r           ), 
  .ar7_rf_wenb1_64_r      (ar7_rf_wenb1_64_r      ),
  .ar7_dest_cr_is_ext     (ar7_dest_cr_is_ext     ),  

  .da_rf_renb0_r             ( da_rf_renb0_r            ),  
  .da_rf_ra0_r               ( da_rf_ra0_r              ),    
  .da_rf_renb0_64_r          ( da_rf_renb0_64_r         ),

  .da_rf_renb1_r             ( da_rf_renb1_r            ),  
  .da_rf_ra1_r               ( da_rf_ra1_r              ),    
  .da_rf_renb1_64_r          ( da_rf_renb1_64_r         ),

  .da_rf_wenb0               ( da_rf_wenb0              ),
  .da_rf_wa0                 ( da_rf_wa0                ),     
  .da_rf_wenb0_64            ( da_rf_wenb0_64           ),

  .da_rf_wenb1               ( da_rf_wenb1              ),  
  .da_rf_wa1                 ( da_rf_wa1                ),     
  .da_rf_wenb1_64            ( da_rf_wenb1_64           ),

  .sa_rf_wenb0_r             ( sa_rf_wenb0_r            ),
  .sa_rf_wa0_r               ( sa_rf_wa0_r              ),     
  .sa_rf_wenb0_64_r          ( sa_rf_wenb0_64_r         ),

  .sa_rf_wenb1_r             ( sa_rf_wenb1_r            ),  
  .sa_rf_wa1_r               ( sa_rf_wa1_r              ),     
  .sa_rf_wenb1_64_r          ( sa_rf_wenb1_64_r         ),

  .x1_rf_wenb0_r             ( x1_rf_wenb0_r            ),
  .x1_rf_wa0_r               ( x1_rf_wa0_r              ),     
  .x1_rf_wenb0_64_r          ( x1_rf_wenb0_64_r         ),

  .x1_rf_wenb1_r             ( x1_rf_wenb1_r            ),  
  .x1_rf_wa1_r               ( x1_rf_wa1_r              ),     
  .x1_rf_wenb1_64_r          ( x1_rf_wenb1_64_r         ),

  .x2_rf_wenb0_r             ( x2_rf_wenb0_r            ),
  .x2_rf_wa0_r               ( x2_rf_wa0_r              ),     
  .x2_rf_wenb0_64_r          ( x2_rf_wenb0_64_r         ),

  .x2_rf_wenb1_r             ( x2_rf_wenb1_r            ),  
  .x2_rf_wa1_r               ( x2_rf_wa1_r              ),     
  .x2_rf_wenb1_64_r          ( x2_rf_wenb1_64_r         ),

  .x3_rf_wenb0_r             ( x3_rf_wenb0_r            ),
  .x3_rf_wa0_r               ( x3_rf_wa0_r              ),     
  .x3_rf_wenb0_64_r          ( x3_rf_wenb0_64_r         ),

  .x3_rf_wenb1_r             ( x3_rf_wenb1_r            ),  
  .x3_rf_wa1_r               ( x3_rf_wa1_r              ),     
  .x3_rf_wenb1_64_r          ( x3_rf_wenb1_64_r         ),

  .ca_rf_wenb0_r             ( ca_rf_wenb0_r            ),
  .ca_rf_wa0_r               ( ca_rf_wa0_r              ),     
  .ca_rf_wenb0_64_r          ( ca_rf_wenb0_64_r         ),

  .ca_rf_wenb1_r             ( ca_rf_wenb1_r            ),  
  .ca_rf_wa1_r               ( ca_rf_wa1_r              ),     
  .ca_rf_wenb1_64_r          ( ca_rf_wenb1_64_r         ),

  .sa_sr_op_r                ( sa_sr_op_r               ),
  .sa_lr_op_r                ( sa_lr_op_r               ),

  .sa_src_operand_0          ( x1_src0_nxt              ),
  .sa_src_operand_1          ( x1_src1_nxt              ),
  .x1_src_operand_0_lo       ( mp1_src0_nxt             ),
  .x1_src_operand_0_hi       ( mp1_src2_nxt             ),
  .x1_src_operand_1_lo       ( mp1_src1_nxt             ),
  .x1_src_operand_1_hi       ( mp1_src3_nxt             ),

  .x1_src_zncv               ( x2_zncv_r                ),

  .wa_rf_wenb0_r             ( wa_rf_wenb0_r            ),    
  .wa_rf_wenb0_64_r          ( wa_rf_wenb0_64_r         ),
  .wa_rf_wdata0_hi_r         ( wa_rf_wdata0_hi_r        ),
  .wa_rf_wa0_r               ( wa_rf_wa0_r              ),      
  .wa_rf_wdata0_lo_r         ( wa_rf_wdata0_lo_r        ),

  .wa_rf_wenb1_r             ( wa_rf_wenb1_r            ),    
  .wa_rf_wenb1_64_r          ( wa_rf_wenb1_64_r         ),
  .wa_rf_wdata1_hi_r         ( wa_rf_wdata1_hi_r        ),
  .wa_rf_wa1_r               ( wa_rf_wa1_r              ),      
  .wa_rf_wdata1_lo_r         ( wa_rf_wdata1_lo_r        ),

  .exu_sa_bflags_ready       (sa_flags_ready            ),
  .eia_sa_hazard             ( eia_sa_hazard            ),   

  .eia_sa_rf_rdata0          ( eia_sa_rf_rdata0         ),
  .eia_sa_rf_rdata0_hi       ( eia_sa_rf_rdata0_hi      ),
  .eia_sa_rf_rdata1          ( eia_sa_rf_rdata1         ),
  .eia_sa_rf_rdata1_hi       ( eia_sa_rf_rdata1_hi      ),

  .eia_da_kernel_instr       ( eia_da_kernel_instr      ), 
  .eia_da_illegal            ( eia_da_illegal           ),

  .eia_x2_is_eia_instr       ( eia_x2_is_eia_instr      ),
  .eia_x2_kernel_cc          ( eia_x2_kernel_cc         ),
  .eia_x2_kernel_cr          ( eia_x2_kernel_cr         ),
  .eia_x3_kernel_param       ( eia_x3_kernel_param      ),

  .eia_x1_ext_cond           ( eia_x1_ext_cond          ), 
  .eia_ca_ext_cond           ( eia_ca_ext_cond          ), 

  .eia_exu_x1_eia_op         ( eia_exu_x1_eia_op        ), 
  .eia_exu_ca_eia_op         ( eia_exu_ca_eia_op        ),
  .eia_exu_x1_hold           ( eia_exu_x1_hold          ), 
  .eia_exu_x1_res_valid      ( eia_exu_x1_res_valid     ), 
  .eia_exu_x1_fast_op_r      ( eia_exu_x1_fast_op_r     ),                                                      
  .eia_exu_x1_res_data       ( eia_exu_x1_res_data      ),  
  .eia_exu_x1_res_data_hi    ( eia_exu_x1_res_data_hi   ),  
  .eia_exu_x1_res_flags      ( eia_exu_x1_res_flags     ), 

  .eia_exu_sa_hold           ( eia_exu_sa_hold          ),
  .eia_exu_x2_hold           ( eia_exu_x2_hold          ),

  .eia_exu_ca_res_valid      ( eia_exu_ca_res_valid     ), 
  .eia_exu_ca_res_data       ( eia_exu_ca_res_data      ),  
  .eia_exu_ca_res_data_hi    ( eia_exu_ca_res_data_hi   ),  
  .eia_exu_ca_res_flags      ( eia_exu_ca_res_flags     ), 

  .aux_eia_ren_r             ( aux_eia_ren_r            ),
  .aux_read                  ( x3_lr_op_r               ),    
  .aux_write                 ( x3_sr_op_r               ),   
  .aux_eia_raddr_r           ( aux_eia_raddr_r          ),

  .eia_aux_rdata             ( eia_aux_rdata            ),
  .eia_aux_k_rd              ( eia_aux_k_rd             ),
  .eia_aux_k_wr              ( eia_aux_k_wr             ),
  .eia_aux_serial_sr         ( eia_aux_serial_sr        ),
  .eia_aux_strict_sr         ( eia_aux_strict_sr        ),
  .eia_aux_illegal           ( eia_aux_illegal          ),
  .eia_aux_unimpl            ( eia_aux_unimpl           ),
  .eia_aux_stall             ( eia_aux_stall            ),

  .aux_eia_wen_r             ( aux_eia_wen_r            ),
  .aux_eia_waddr_r           ( aux_eia_waddr_r          ),
  .aux_eia_wdata_r           ( wa_sr_data_r             ),
  
  .eia_exu_idle              ( eia_exu_idle             )
);

`ifdef npuarc_RTL_PIPEMON // {
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// RTL pipe monitor support in RASCAL                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// Move PC through the pipeline for pipemon's benefit.
wire x1_pc_cg0 = sa_pass & x1_enable;
wire x2_pc_cg0 = x1_pass & x2_enable;
wire x3_pc_cg0 = x2_pass & x3_enable;
wire ca_pc_cg0 = x3_pass & ca_enable;

// P = pipemon.
reg [`npuarc_PC_RANGE] Px1_pc_r;  // Clash with x1_pc_r elsewhere, so make our own.
reg [`npuarc_PC_RANGE] Px2_pc_r;
reg [`npuarc_PC_RANGE] Px3_pc_r;
reg [`npuarc_PC_RANGE] Pca_pc_r;

wire [`npuarc_PC_RANGE] Px1_pc_nxt = sa_pc; // _r;  But it's registered anyway.
wire [`npuarc_PC_RANGE] Px2_pc_nxt = Px1_pc_r;
wire [`npuarc_PC_RANGE] Px3_pc_nxt = Px2_pc_r;
wire [`npuarc_PC_RANGE] Pca_pc_nxt = Px3_pc_r;

always @(posedge clk or posedge rst_a)
begin: ca_pc_reg_PROC
  if (rst_a == 1'b1)
    begin
    Px1_pc_r <= 0;
    Px2_pc_r <= 0;
    Px3_pc_r <= 0;
    Pca_pc_r <= 0;
    end
  else
    begin
    if (x1_pc_cg0) Px1_pc_r <= Px1_pc_nxt;
    if (x2_pc_cg0) Px2_pc_r <= Px2_pc_nxt;
    if (x3_pc_cg0) Px3_pc_r <= Px3_pc_nxt;
    if (ca_pc_cg0) Pca_pc_r <= Pca_pc_nxt;
    end
end

`define PAD_PC_TO_32(x) { x, 1'b0 }

npuarc_rtl_pipemon u_pipemon (

  .wa_pass            (wa_pass         ),
  .wa_type            (wa_type         ),
  .wa_target          (`PAD_PC_TO_32(wa_target) ),
  .da_0_valid_r       (da_valid_r     ),
  .da_0_pass          (da_pass        ),
  .da_0_is_16bit_r    (Pda_is_16bit_r  ),  // from dec_regs
  .da_0_inst_r        (Pda_inst_r      ),  // from dec_regs
  .da_0_has_limm_r    (Pda_has_limm_r  ),  // from dec_regs
  .da_0_limm_r        (Pda_limm_r      ),  // from dec_regs
  
  .sa_0_pass          (sa_pass        ),
  .x1_0_pass          (x1_pass        ),
  .x2_0_pass          (x2_pass        ),
  .x3_0_pass          (x3_pass        ),
  .ca_0_pass          (ca_pass        ),
  .ca_0_pc            (`PAD_PC_TO_32(Pca_pc_r) ),
  
  .ar_pc              (`PAD_PC_TO_32(ar_pc_r)            ),
  .ar_zncv            (ar_aux_status32_r[`npuarc_ZNCV_RANGE]),
  
  .db_active          (db_active        ),
  .ca_uop_active_r    (ca_uop_active_r  ),
  
  .ca_load_r          (ca_load_r      ),
  .ca_store_r         (ca_store_r     ),
  .ca_size_r          ({1'b0, ca_size_r}),
  .ca_store_grad      (2'b00    ),  // Yes, we have data
  .ca_mem_addr_r      (ca_mem_addr_r    ),
  .ca_write_data_lo   (dc4_write_data_lo), 
  
  .wa_rf_wenb0_r      (wa_rf_wenb0_r    ),      
  .wa_rf_wa0_r        (wa_rf_wa0_r      ),          
  .wa_rf_wdata0_lo_r  (wa_rf_wdata0_lo_r),    
  .wa_rf_wenb0_hi_r   (wa_rf_wenb0_64_r),     // Second register of pair.
  .wa_rf_wdata0_hi_r  (wa_rf_wdata0_hi_r),    

  .wa_rf_wenb1_r      (wa_rf_wenb1_r    ),      
  .wa_rf_wa1_r        (wa_rf_wa1_r      ),          
  .wa_rf_wdata1_lo_r  (wa_rf_wdata1_lo_r),
  .wa_rf_wenb1_hi_r   (wa_rf_wenb1_64_r),     // Second register of pair.
  .wa_rf_wdata1_hi_r  (wa_rf_wdata1_hi_r),    

  .clk                (clk              ),
  .rst_a              (rst_a            )

  );
`endif // }
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Pipeline Restart prioritisation logic                                    //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: fch_restart_PROC

  //==========================================================================
  // Restart the IFU/Front-end in response to a restart request from either
  // the writeback or execute2 stages.
  //
  fch_restart            = (x2_restart_r | wa_restart_r)
                         ;

  //==========================================================================
  // Restart takes place from an exception vector location.
  //
  fch_restart_vec        = wa_restart_vec_r
                         ;

  //==========================================================================
  // On restart, writeback restarts take priority over those originating
  // from upstream. 
  //
  fch_target             = (wa_restart_r == 1'b1)
                         ? wa_restart_pc_r
                         : x2_restart_pc_r
                         ;

  //==========================================================================
  // On restart, provide the fetch target successor address low-order bits.
  //
// leda B_3208 off
// LMD: Unequal length LHS and RHS in assignment
// LJ:  wraparound pointer arithmetic calculation, carry is a dont_care
  {dont_care, fch_target_successor} = {1'b0, fch_target[`npuarc_IM_LINE_BITS-1:3]}
                                    + {{(`npuarc_IM_LINE_BITS-3){1'b0}}, 1'b1}
                                    ;
// leda B_3208 on

  //==========================================================================
  // Writeback requests IFU halt.
  //
  fch_stop_r             = wa_stop_r;

  //UOP active including instructions that can triggers it
  //One cycle early to stop halt fsm  
  //
  ca_uop_active          = ca_uop_active_nxt | ca_uop_active_r; 
 
  //==========================================================================
  // Set the fch_iprot_replay signal if this is a restart from WA, and the
  // reason for a restart is an ifetch protection replay, or of the 
  // restart is due to a vector fetch (never speculative, and always makes
  // its own region unprotected).
  //
  fch_iprot_replay          = (wa_restart_r & wa_iprot_replay_r)
                            ;

end // block: fch_restart_PROC

assign dc4_q_replay          = dc4_replay
                             & (~wa_restart_kill_r)
                             & (ca_store_r | ca_load_r)
                             ;

assign db_restart            = ca_replay;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output assignments for Actionpoints                                      //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
assign aps_excpn = ca_ap_excpn_r;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output assignments for ucode signals                                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
assign sa_dmb_dmp_stall = sa_dmb_stall;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output assignments for smart                                             //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign ca_pass_eslot = ca_valid_r & ca_pass & ca_in_eslot_r;
assign ca_pc_jump    = ca_zol_lp_jmp ? ca_seq_pc_nxt : ar_pc_r;
assign aux_eret_addr = ar_aux_eret_r[`npuarc_PC_RANGE];

endmodule // alb_exec_pipe
