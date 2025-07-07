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
//----------------------------------------------------------------------------
//
//
//  #####   ######   ######           #####   #######  #        
// #     #  #     #  #     #         #     #  #        #        
// #     #  #     #  #     #         #        #        #        
// #     #  ######   #     #          #####   #####    #        
// #     #  #        #     #               #  #        #        
// #     #  #        #     #         #     #  #        #        
//  #####   #        ######   #####   #####   #######  #######  
//
// ===========================================================================
// @f:opd_sel:
// Description:
// @p
//  The alb_opd_sel module implements the Operand-select stage of the Albacore 
//  pipeline, which is primarily responsible for reading source registers and
//  forwarding speculative results to the Exec1 stage.
//
//  The module hierarchy, at and below this module, is:
//
//        alb_opd_sel
//           |
//           +-- alb_regfile_2r2w
//
// @e
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants.
//
`include "npuarc_ucode_const.v"

// Set simulation timescale
//
//`include "const.def"

module npuarc_alb_opd_sel (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,              // clock signal
  input                       rst_a,            // reset signal

  ////////// Architecturally-committed state ////////////////////////////////
  //
// leda NTL_CON13C off
// LMD: non driving port
// LJ:  unused port range
  input   [`npuarc_DATA_RANGE]       ar_aux_jli_base_r,// JLI_BASE aux register
  input   [`npuarc_DATA_RANGE]       ar_aux_ldi_base_r,// LDI_BASE register
  input   [`npuarc_DATA_RANGE]       ar_aux_ei_base_r, // EI_BASE aux register
// leda NTL_CON13C on
  ////////// Inputs from the Decode stage ////////////////////////////////////
  //
  input   [`npuarc_PC_RANGE]         sa_pc_nxt,        // PC of decoded instruction
  input   [`npuarc_DATA_RANGE]       sa_limm_nxt,      // LIMM of incoming instruction


  input  [`npuarc_SA_CODE_WIDTH-1:0] sa_code_nxt,      // decoded control vector
  input   [`npuarc_PC_RANGE]         sa_seq_pc_nxt,    // next sequential SA-stage PC
  input                       sa_is_16bit_nxt,  // is_16bit for insn in DA stage 
  input                       da_iprot_viol_r,
  input                       da_in_dslot_r,
  input                       da_uop_u7_pcl,    // LEAVE_S u7 pcl bit

  ////////// Inputs from the Prediction Pipe /////////////////////////////////
  //
  input                       sa_error_branch,  // Erroroneous prediction at SA
  input   [`npuarc_PC_RANGE]         sa_pred_bta_r,    // SA predicted branch target
    
  ////////// Pipeline control inputs /////////////////////////////////////////
  //
  input                       da_pass,          // passing a valid instruction
  input                       sa_pass,          // passing a valid instruction
  input                       sa_kill,          // kill an instruction
  input                       sa_valid_r,       // valid insn at Operand stage
  input                       sa_enable,        // enable SA pipeline regs
  input                       da_error_branch_r,// incoming error-branch packet

  output                      sa_dest_cr_is_ext_r,
  input                       eia_ra0_is_ext, 
  input                       eia_ra1_is_ext,  
  input   [`npuarc_DATA_RANGE]       eia_sa_reg0,      // eia core regs port 0 out
  input   [`npuarc_DATA_RANGE]       eia_sa_reg0_hi,
  input   [`npuarc_DATA_RANGE]       eia_sa_reg1,      // eia core regs port 1 out
  input   [`npuarc_DATA_RANGE]       eia_sa_reg1_hi,

  ////////// Bypass and retirement result data from the Execute Pipeline /////
  //
  input   [`npuarc_DATA_RANGE]       x1_byp_data0,     // Exec1 forwarding result
  input   [`npuarc_DATA_RANGE]       x2_byp_data0,     // Exec2 forwarding result
  input   [`npuarc_DATA_RANGE]       x3_byp_data0,     // Exec3 forwarding result
  //
  input   [`npuarc_DATA_RANGE]       ca_byp_data0_lo,  // data0[31:0] at Commit stage
  input   [`npuarc_DATA_RANGE]       ca_byp_data0_hi,  // data0[63:32] at Commit stage
  //
  input   [`npuarc_DATA_RANGE]       ca_byp_data1_lo,  // data1[31:0] at Commit stage
  input   [`npuarc_DATA_RANGE]       ca_byp_data1_hi,  // data1[63:32] at Commit stage
  //
  input                       wa_rf_wenb0_r,    // retiring data0 en
  input   [`npuarc_RGF_ADDR_RANGE]   wa_rf_wa0_r,      // retiring data0 addr
  input   [`npuarc_DATA_RANGE]       wa_rf_wdata0_lo_r,// retiring data0[31:0]
  input                       wa_rf_wenb0_64_r, //
  input   [`npuarc_DATA_RANGE]       wa_rf_wdata0_hi_r,// retiring data0[63:32]
  //
  input                       wa_rf_wenb1_r,    // retiring data1 en
  input   [`npuarc_RGF_ADDR_RANGE]   wa_rf_wa1_r,      // retiring data1 addr
  input   [`npuarc_DATA_RANGE]       wa_rf_wdata1_lo_r,// retiring data1[31:0]
  input                       wa_rf_wenb1_64_r, //
  input   [`npuarc_DATA_RANGE]       wa_rf_wdata1_hi_r,// retiring data1[63:32]

  ////////// Implicit writeback to the accumulator ///////////////////////////
  //
  input   [`npuarc_DATA_RANGE]       wa_accl_nxt,        // next implicit ACCL value
  input   [`npuarc_DATA_RANGE]       wa_acch_nxt,        // next implicit ACCH value
  input                       wa_acc_wenb,        // implicit ACC write enb

  output  [`npuarc_DATA_RANGE]       accl_r,             // ACCL register value  
  output  [`npuarc_DATA_RANGE]       acch_r,             // ACCH register value  

  input                       int_ilink_evt,      //push pc to ilink at start of interrupt
  input   [`npuarc_PC_RANGE]         wa_pc, 


  ////////// Bypass control signals from alb_dep_pipe module /////////////////
  //
  input                       fwd_x1_sa0_lo,
  input                       fwd_x2_sa0_lo,
  input                       fwd_x3_sa0_lo,
  input                       fwd_ca0_lo_sa0_lo,
  input                       fwd_ca1_lo_sa0_lo,
  input                       fwd_wa0_lo_sa0_lo,
  input                       fwd_wa1_lo_sa0_lo,
  input                       fwd_ca0_hi_sa0_lo,
  input                       fwd_wa0_hi_sa0_lo,
  input                       fwd_ca1_hi_sa0_lo,
  input                       fwd_ca1_hi_sa1_lo,
  input                       fwd_wa1_hi_sa0_lo,
  input                       fwd_wa1_hi_sa1_lo,
  input                       fwd_wa0_hi_sa0_hi,
  input                       fwd_wa1_hi_sa0_hi,
  input                       fwd_x1_sa1_lo,
  input                       fwd_x2_sa1_lo,
  input                       fwd_x3_sa1_lo,
  input                       fwd_ca0_lo_sa1_lo,
  input                       fwd_ca1_lo_sa1_lo,
  input                       fwd_wa0_lo_sa1_lo,
  input                       fwd_wa1_lo_sa1_lo,
  input                       fwd_ca0_hi_sa1_lo,
  input                       fwd_wa0_hi_sa1_lo,
  input                       fwd_wa0_lo_sa0_hi,
  input                       fwd_wa1_lo_sa0_hi,
  input                       fwd_wa0_hi_sa1_hi,
  input                       fwd_wa0_lo_sa1_hi,
  input                       fwd_wa1_lo_sa1_hi,
  input                       fwd_wa1_hi_sa1_hi,

  ////////// Inputs from the ZOL pipeline ////////////////////////////////////
  // 
  input   [`npuarc_LPC_RANGE]        ar_lp_count_r,    // architectural LP_COUNT reg
  input                       sa_hit_lp_end,    // SA is at last insn of ZOL

  ////////// Outputs to Dependency and Control Pipeline //////////////////////
  //
  output reg                  sa_valid_nxt,     // valid insn to Operand stage
  output                      sa_opds_in_sa_r,  // insn requires opds at SA
  output                      sa_agu_uses_r0_r, // AGU uses reg0 as source
  output                      sa_agu_uses_r1_r, // AGU uses reg1 as source
  output                      sa_dslot_r,       // Operand-stage insn has dslot
  output                      sa_link_r,        // Operand-stage insn upt link
  output                      sa_wa0_lpc_r,     // SA insn writes to LP_COUNT
  output                      sa_ei_op_r,       // Operand-stage insn has EI_S
  output                      sa_ldi_src0_r,    // LDI insn at SA
  output                      sa_jli_src0_r,    // LDI insn at SA
  output                      sa_leave_op_r,    // LEAVE_S insn at SA
  output reg                  sa_branch_or_jump, // br or jmp at SA
  output                      sa_multi_op_r,    // UOP insn at SA
  output                      sa_sr_op_r,       // SR insn at SA
  output                      sa_lr_op_r,       // LR insn at SA
  output reg                  sa_uop_predictable_r, // uop seq with predictable
                                                    // branch at SA
  output     [`npuarc_ZNCV_RANGE]    sa_zncv_wen_r,    //
  output     [4:0]            sa_q_field_r,     //
  output                      sa_with_carry_r,  //
  output                      sa_uop_inst_r,    // SA insn is part of a uop
  output reg [`npuarc_PC_RANGE]      sa_seq_pc_r,      // seq PC after SA insn
  output reg [`npuarc_PC_RANGE]      sa_restart_pc,    // restart PC for error branch
  output     [`npuarc_PC_RANGE]      sa_pc,            // PC at SA stage
  output [`npuarc_RGF_ADDR_RANGE]    sa_rf_ra0_r,      // reg-read address 0 at SA
  output [`npuarc_RGF_ADDR_RANGE]    sa_rf_ra1_r,      // reg-read address 1 at SA
  output                      sa_rf_renb0_r,    // reg0 at Opd_Sel is read
  output                      sa_rf_renb0_64_r, // reg0+1 at Opd_Sel is read
  output     [`npuarc_RGF_ADDR_RANGE]sa_rf_wa0_r,      //
  output                      sa_rf_wenb0_r,    // 
  output                      sa_rf_wenb0_64_r, //
  output                      sa_rf_renb1_r,    // reg1 at Opd_Sel is read
  output                      sa_rf_renb1_64_r, // reg1+1 at Opd_Sel is read
  output     [`npuarc_RGF_ADDR_RANGE]sa_rf_wa1_r,      // 
  output                      sa_rf_wenb1_r,    //
  output                      sa_rf_wenb1_64_r, //
  output                      sa_reads_acc_r,   // explicit ACC read at SA
  output                      sa_dsync_op_r,    // DSYNC insn at SA
  output                      sa_dmb_op_r,      // DMB insn at SA
  output     [2:0]            sa_dmb_type_r,    // DMB u3 operand

  ///////// Outputs to the Multiplier Pipeline ///////////////////////////////
  //
  output                      sa_mpy_op_r,      // MPY operation at SA 
  output                      sa_vector_op_r,   // vector operation at SA
  output                      sa_half_size_r,   // 16-bit operation size at SA
  output                      sa_dual_op_r,     // dual mpy operation at SA

  ///////// Outputs to the Divider Pipeline //////////////////////////////////
  //
  output                      sa_div_op_r,      // divider operation at SA 

  
  ///////// Outputs to the Data Memory pipeline //////////////////////////////
  //
  output                      sa_load_r,        // load operation at SA 
  output                      sa_store_r,       // store operation at SA 

  ////////// Outputs to the Prediction Pipeline //////////////////////////////
  //
  output reg [`npuarc_BR_TYPE_RANGE] sa_br_type,       // actual branch type at SA
  output reg                  sa_secondary,
  output reg [`npuarc_ISIZE_RANGE]   sa_commit_size,
  output                      sa_iprot_viol_r,  // replay on iprot violation



  ////////// Outputs to the Exec1 stage //////////////////////////////////////
  //
  output reg [`npuarc_DATA_RANGE]    x1_src0_nxt,      // X1 source value 0
  output reg [`npuarc_DATA_RANGE]    x1_src1_nxt,      // X1 source value 1
  output reg [`npuarc_DATA_RANGE]    x1_src2_nxt,      // X1 source value 2
  output reg [`npuarc_DATA_RANGE]    x1_src3_nxt,      // X1 source value 3
  //
  output reg                  sa_src0_pass,     // x1_src0_nxt is active
  output reg                  sa_src1_pass,     // x1_src1_nxt is active
  output reg                  sa_src2_pass,     // x1_src2_nxt is active
  output reg                  sa_src3_pass,     // x1_src3_nxt is active
  //
  output [`npuarc_X1_CODE_WIDTH-1:0] x1_code_nxt       // instruction control vector
);

//////////////////////////////////////////////////////////////////////////////
// Registers, register next value signals, and register update signals      //
//////////////////////////////////////////////////////////////////////////////

reg     [`npuarc_PC_RANGE]           sa_pc_r;          // Operands-stage PC
reg     [`npuarc_DATA_RANGE]         sa_limm_r;        // limm operand
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg     [`npuarc_SA_CODE_WIDTH-1:0]  sa_code_r;        // Execute-stage ucode vector
// leda NTL_CON32 on
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  ucode generated
// Library ARCv2HS-3.5.999999999
// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.

// Certain materials incorporated herein are copyright (C) 2010 - 2011,
// The University Court of the University of Edinburgh. All Rights Reserved.

assign sa_rf_wa0_r  = sa_code_r[`npuarc_RF_WA0_RANGE];  // generated code
assign sa_rf_wenb0_r  = sa_code_r[`npuarc_RF_WENB0_RANGE];  // generated code
assign sa_rf_wenb0_64_r  = sa_code_r[`npuarc_RF_WENB0_64_RANGE];  // generated code
wire   sa_cc_byp_64_haz_r;  // generated code
assign sa_cc_byp_64_haz_r  = sa_code_r[`npuarc_CC_BYP_64_HAZ_RANGE];  // generated code
wire   sa_has_limm_r;  // generated code
assign sa_has_limm_r  = sa_code_r[`npuarc_HAS_LIMM_RANGE];  // generated code
wire   sa_is_16bit_r;  // generated code
assign sa_is_16bit_r  = sa_code_r[`npuarc_IS_16BIT_RANGE];  // generated code
assign sa_sr_op_r   = sa_code_r[`npuarc_SR_OP_RANGE];  // generated code
wire   sa_loop_op_r;  // generated code
assign sa_loop_op_r  = sa_code_r[`npuarc_LOOP_OP_RANGE];  // generated code
wire   sa_locked_r;  // generated code
assign sa_locked_r  = sa_code_r[`npuarc_LOCKED_RANGE];  // generated code
assign sa_wa0_lpc_r  = sa_code_r[`npuarc_WA0_LPC_RANGE];  // generated code
assign sa_dslot_r   = sa_code_r[`npuarc_DSLOT_RANGE];  // generated code
wire   sa_sleep_op_r;  // generated code
assign sa_sleep_op_r  = sa_code_r[`npuarc_SLEEP_OP_RANGE];  // generated code
wire   sa_acc_wenb_r;  // generated code
assign sa_acc_wenb_r  = sa_code_r[`npuarc_ACC_WENB_RANGE];  // generated code
wire   sa_writes_acc_r;  // generated code
assign sa_writes_acc_r  = sa_code_r[`npuarc_WRITES_ACC_RANGE];  // generated code
assign sa_lr_op_r   = sa_code_r[`npuarc_LR_OP_RANGE];  // generated code
wire   sa_jump_r;  // generated code
assign sa_jump_r  = sa_code_r[`npuarc_JUMP_RANGE];  // generated code
assign sa_load_r    = sa_code_r[`npuarc_LOAD_RANGE];  // generated code
wire   sa_pref_r;  // generated code
assign sa_pref_r  = sa_code_r[`npuarc_PREF_RANGE];  // generated code
assign sa_store_r   = sa_code_r[`npuarc_STORE_RANGE];  // generated code
wire   sa_uop_prol_r;  // generated code
assign sa_uop_prol_r  = sa_code_r[`npuarc_UOP_PROL_RANGE];  // generated code
assign sa_rf_wa1_r  = sa_code_r[`npuarc_RF_WA1_RANGE];  // generated code
assign sa_rf_wenb1_r  = sa_code_r[`npuarc_RF_WENB1_RANGE];  // generated code
assign sa_rf_wenb1_64_r  = sa_code_r[`npuarc_RF_WENB1_64_RANGE];  // generated code
wire   sa_signed_op_r;  // generated code
assign sa_signed_op_r  = sa_code_r[`npuarc_SIGNED_OP_RANGE];  // generated code
wire   sa_double_size_r;  // generated code
assign sa_double_size_r  = sa_code_r[`npuarc_DOUBLE_SIZE_RANGE];  // generated code
assign sa_half_size_r  = sa_code_r[`npuarc_HALF_SIZE_RANGE];  // generated code
wire   sa_byte_size_r;  // generated code
assign sa_byte_size_r  = sa_code_r[`npuarc_BYTE_SIZE_RANGE];  // generated code
wire   sa_rtie_op_r;  // generated code
assign sa_rtie_op_r  = sa_code_r[`npuarc_RTIE_OP_RANGE];  // generated code
wire   sa_enter_op_r;  // generated code
assign sa_enter_op_r  = sa_code_r[`npuarc_ENTER_OP_RANGE];  // generated code
assign sa_leave_op_r  = sa_code_r[`npuarc_LEAVE_OP_RANGE];  // generated code
wire   sa_trap_op_r;  // generated code
assign sa_trap_op_r  = sa_code_r[`npuarc_TRAP_OP_RANGE];  // generated code
wire   sa_sync_op_r;  // generated code
assign sa_sync_op_r  = sa_code_r[`npuarc_SYNC_OP_RANGE];  // generated code
wire   sa_brk_op_r;  // generated code
assign sa_brk_op_r  = sa_code_r[`npuarc_BRK_OP_RANGE];  // generated code
wire   sa_invalid_instr_r;  // generated code
assign sa_invalid_instr_r  = sa_code_r[`npuarc_INVALID_INSTR_RANGE];  // generated code
wire   sa_rgf_link_r;  // generated code
assign sa_rgf_link_r  = sa_code_r[`npuarc_RGF_LINK_RANGE];  // generated code
wire   sa_prod_sign_r;  // generated code
assign sa_prod_sign_r  = sa_code_r[`npuarc_PROD_SIGN_RANGE];  // generated code
wire   sa_macu_r;  // generated code
assign sa_macu_r  = sa_code_r[`npuarc_MACU_RANGE];  // generated code
wire   sa_quad_op_r;  // generated code
assign sa_quad_op_r  = sa_code_r[`npuarc_QUAD_OP_RANGE];  // generated code
wire   sa_acc_op_r;  // generated code
assign sa_acc_op_r  = sa_code_r[`npuarc_ACC_OP_RANGE];  // generated code
assign sa_vector_op_r  = sa_code_r[`npuarc_VECTOR_OP_RANGE];  // generated code
assign sa_dual_op_r  = sa_code_r[`npuarc_DUAL_OP_RANGE];  // generated code
assign sa_mpy_op_r  = sa_code_r[`npuarc_MPY_OP_RANGE];  // generated code
wire   sa_z_wen_r;  // generated code
assign sa_z_wen_r  = sa_code_r[`npuarc_Z_WEN_RANGE];  // generated code
wire   sa_n_wen_r;  // generated code
assign sa_n_wen_r  = sa_code_r[`npuarc_N_WEN_RANGE];  // generated code
wire   sa_c_wen_r;  // generated code
assign sa_c_wen_r  = sa_code_r[`npuarc_C_WEN_RANGE];  // generated code
wire   sa_v_wen_r;  // generated code
assign sa_v_wen_r  = sa_code_r[`npuarc_V_WEN_RANGE];  // generated code
wire   sa_kernel_op_r;  // generated code
assign sa_kernel_op_r  = sa_code_r[`npuarc_KERNEL_OP_RANGE];  // generated code
wire   sa_flag_op_r;  // generated code
assign sa_flag_op_r  = sa_code_r[`npuarc_FLAG_OP_RANGE];  // generated code
wire   sa_bcc_r;  // generated code
assign sa_bcc_r  = sa_code_r[`npuarc_BCC_RANGE];  // generated code
assign sa_link_r    = sa_code_r[`npuarc_LINK_RANGE];  // generated code
wire   sa_brcc_bbit_r;  // generated code
assign sa_brcc_bbit_r  = sa_code_r[`npuarc_BRCC_BBIT_RANGE];  // generated code
wire   sa_cache_byp_r;  // generated code
assign sa_cache_byp_r  = sa_code_r[`npuarc_CACHE_BYP_RANGE];  // generated code
wire   sa_slow_op_r;  // generated code
assign sa_slow_op_r  = sa_code_r[`npuarc_SLOW_OP_RANGE];  // generated code
wire   sa_fast_op_r;  // generated code
assign sa_fast_op_r  = sa_code_r[`npuarc_FAST_OP_RANGE];  // generated code
assign sa_div_op_r  = sa_code_r[`npuarc_DIV_OP_RANGE];  // generated code
wire   sa_btab_op_r;  // generated code
assign sa_btab_op_r  = sa_code_r[`npuarc_BTAB_OP_RANGE];  // generated code
assign sa_ei_op_r   = sa_code_r[`npuarc_EI_OP_RANGE];  // generated code
wire   sa_in_eslot_r;  // generated code
assign sa_in_eslot_r  = sa_code_r[`npuarc_IN_ESLOT_RANGE];  // generated code
wire   sa_rel_branch_r;  // generated code
assign sa_rel_branch_r  = sa_code_r[`npuarc_REL_BRANCH_RANGE];  // generated code
wire   sa_illegal_operand_r;  // generated code
assign sa_illegal_operand_r  = sa_code_r[`npuarc_ILLEGAL_OPERAND_RANGE];  // generated code
wire   sa_swap_op_r;  // generated code
assign sa_swap_op_r  = sa_code_r[`npuarc_SWAP_OP_RANGE];  // generated code
wire   sa_setcc_op_r;  // generated code
assign sa_setcc_op_r  = sa_code_r[`npuarc_SETCC_OP_RANGE];  // generated code
wire [2:0]  sa_cc_field_r;  // generated code
assign sa_cc_field_r  = sa_code_r[`npuarc_CC_FIELD_RANGE];  // generated code
assign sa_q_field_r  = sa_code_r[`npuarc_Q_FIELD_RANGE];  // generated code
assign sa_dest_cr_is_ext_r  = sa_code_r[`npuarc_DEST_CR_IS_EXT_RANGE];  // generated code
wire   sa_add_op_r;  // generated code
assign sa_add_op_r  = sa_code_r[`npuarc_ADD_OP_RANGE];  // generated code
wire   sa_and_op_r;  // generated code
assign sa_and_op_r  = sa_code_r[`npuarc_AND_OP_RANGE];  // generated code
wire   sa_or_op_r;  // generated code
assign sa_or_op_r  = sa_code_r[`npuarc_OR_OP_RANGE];  // generated code
wire   sa_xor_op_r;  // generated code
assign sa_xor_op_r  = sa_code_r[`npuarc_XOR_OP_RANGE];  // generated code
wire   sa_mov_op_r;  // generated code
assign sa_mov_op_r  = sa_code_r[`npuarc_MOV_OP_RANGE];  // generated code
assign sa_with_carry_r  = sa_code_r[`npuarc_WITH_CARRY_RANGE];  // generated code
wire   sa_simple_shift_op_r;  // generated code
assign sa_simple_shift_op_r  = sa_code_r[`npuarc_SIMPLE_SHIFT_OP_RANGE];  // generated code
wire   sa_left_shift_r;  // generated code
assign sa_left_shift_r  = sa_code_r[`npuarc_LEFT_SHIFT_RANGE];  // generated code
wire   sa_rotate_op_r;  // generated code
assign sa_rotate_op_r  = sa_code_r[`npuarc_ROTATE_OP_RANGE];  // generated code
wire   sa_inv_src1_r;  // generated code
assign sa_inv_src1_r  = sa_code_r[`npuarc_INV_SRC1_RANGE];  // generated code
wire   sa_inv_src2_r;  // generated code
assign sa_inv_src2_r  = sa_code_r[`npuarc_INV_SRC2_RANGE];  // generated code
wire   sa_bit_op_r;  // generated code
assign sa_bit_op_r  = sa_code_r[`npuarc_BIT_OP_RANGE];  // generated code
wire   sa_mask_op_r;  // generated code
assign sa_mask_op_r  = sa_code_r[`npuarc_MASK_OP_RANGE];  // generated code
wire   sa_src2_mask_sel_r;  // generated code
assign sa_src2_mask_sel_r  = sa_code_r[`npuarc_SRC2_MASK_SEL_RANGE];  // generated code
wire   sa_uop_commit_r;  // generated code
assign sa_uop_commit_r  = sa_code_r[`npuarc_UOP_COMMIT_RANGE];  // generated code
wire   sa_uop_epil_r;  // generated code
assign sa_uop_epil_r  = sa_code_r[`npuarc_UOP_EPIL_RANGE];  // generated code
wire   sa_uop_excpn_r;  // generated code
assign sa_uop_excpn_r  = sa_code_r[`npuarc_UOP_EXCPN_RANGE];  // generated code
wire   sa_predicate_r;  // generated code
assign sa_predicate_r  = sa_code_r[`npuarc_PREDICATE_RANGE];  // generated code
assign sa_rf_renb0_r  = sa_code_r[`npuarc_RF_RENB0_RANGE];  // generated code
assign sa_rf_renb1_r  = sa_code_r[`npuarc_RF_RENB1_RANGE];  // generated code
assign sa_rf_renb0_64_r  = sa_code_r[`npuarc_RF_RENB0_64_RANGE];  // generated code
assign sa_rf_renb1_64_r  = sa_code_r[`npuarc_RF_RENB1_64_RANGE];  // generated code
assign sa_rf_ra0_r  = sa_code_r[`npuarc_RF_RA0_RANGE];  // generated code
assign sa_rf_ra1_r  = sa_code_r[`npuarc_RF_RA1_RANGE];  // generated code
assign sa_jli_src0_r  = sa_code_r[`npuarc_JLI_SRC0_RANGE];  // generated code
assign sa_uop_inst_r  = sa_code_r[`npuarc_UOP_INST_RANGE];  // generated code
wire   sa_vec_shimm_r;  // generated code
assign sa_vec_shimm_r  = sa_code_r[`npuarc_VEC_SHIMM_RANGE];  // generated code
assign sa_iprot_viol_r  = sa_code_r[`npuarc_IPROT_VIOL_RANGE];  // generated code
assign sa_dmb_op_r  = sa_code_r[`npuarc_DMB_OP_RANGE];  // generated code
assign sa_dmb_type_r  = sa_code_r[`npuarc_DMB_TYPE_RANGE];  // generated code
wire   sa_force_cin_r;  // generated code
assign sa_force_cin_r  = sa_code_r[`npuarc_FORCE_CIN_RANGE];  // generated code
wire   sa_opd3_sel_r;  // generated code
assign sa_opd3_sel_r  = sa_code_r[`npuarc_OPD3_SEL_RANGE];  // generated code
assign sa_multi_op_r  = sa_code_r[`npuarc_MULTI_OP_RANGE];  // generated code
wire   sa_abs_op_r;  // generated code
assign sa_abs_op_r  = sa_code_r[`npuarc_ABS_OP_RANGE];  // generated code
wire   sa_min_op_r;  // generated code
assign sa_min_op_r  = sa_code_r[`npuarc_MIN_OP_RANGE];  // generated code
wire   sa_max_op_r;  // generated code
assign sa_max_op_r  = sa_code_r[`npuarc_MAX_OP_RANGE];  // generated code
wire   sa_norm_op_r;  // generated code
assign sa_norm_op_r  = sa_code_r[`npuarc_NORM_OP_RANGE];  // generated code
assign sa_ldi_src0_r  = sa_code_r[`npuarc_LDI_SRC0_RANGE];  // generated code
wire   sa_pre_addr_r;  // generated code
assign sa_pre_addr_r  = sa_code_r[`npuarc_PRE_ADDR_RANGE];  // generated code
wire   sa_stimm_op_r;  // generated code
assign sa_stimm_op_r  = sa_code_r[`npuarc_STIMM_OP_RANGE];  // generated code
wire   sa_src2_sh1_r;  // generated code
assign sa_src2_sh1_r  = sa_code_r[`npuarc_SRC2_SH1_RANGE];  // generated code
wire   sa_src2_sh2_r;  // generated code
assign sa_src2_sh2_r  = sa_code_r[`npuarc_SRC2_SH2_RANGE];  // generated code
wire   sa_src2_sh3_r;  // generated code
assign sa_src2_sh3_r  = sa_code_r[`npuarc_SRC2_SH3_RANGE];  // generated code
wire   sa_barrel_shift_op_r;  // generated code
assign sa_barrel_shift_op_r  = sa_code_r[`npuarc_BARREL_SHIFT_OP_RANGE];  // generated code
wire   sa_opds_in_x1_r;  // generated code
assign sa_opds_in_x1_r  = sa_code_r[`npuarc_OPDS_IN_X1_RANGE];  // generated code
assign sa_agu_uses_r0_r  = sa_code_r[`npuarc_AGU_USES_R0_RANGE];  // generated code
assign sa_opds_in_sa_r  = sa_code_r[`npuarc_OPDS_IN_SA_RANGE];  // generated code
wire   sa_limm0_64_r;  // generated code
assign sa_limm0_64_r  = sa_code_r[`npuarc_LIMM0_64_RANGE];  // generated code
wire   sa_limm1_64_r;  // generated code
assign sa_limm1_64_r  = sa_code_r[`npuarc_LIMM1_64_RANGE];  // generated code
assign sa_may_graduate_r  = sa_code_r[`npuarc_MAY_GRADUATE_RANGE];  // generated code
assign sa_agu_uses_r1_r  = sa_code_r[`npuarc_AGU_USES_R1_RANGE];  // generated code
assign sa_reads_acc_r  = sa_code_r[`npuarc_READS_ACC_RANGE];  // generated code
assign sa_dsync_op_r  = sa_code_r[`npuarc_DSYNC_OP_RANGE];  // generated code
wire   sa_src2_shifts_r;  // generated code
assign sa_src2_shifts_r  = sa_code_r[`npuarc_SRC2_SHIFTS_RANGE];  // generated code
wire   sa_sel_shimm_r;  // generated code
assign sa_sel_shimm_r  = sa_code_r[`npuarc_SEL_SHIMM_RANGE];  // generated code
wire [31:0]  sa_shimm_r;  // generated code
assign sa_shimm_r  = sa_code_r[`npuarc_SHIMM_RANGE];  // generated code
wire   sa_limm_r0_r;  // generated code
assign sa_limm_r0_r  = sa_code_r[`npuarc_LIMM_R0_RANGE];  // generated code
wire   sa_limm_r1_r;  // generated code
assign sa_limm_r1_r  = sa_code_r[`npuarc_LIMM_R1_RANGE];  // generated code
wire [31:0]  sa_offset_r;  // generated code
assign sa_offset_r  = sa_code_r[`npuarc_OFFSET_RANGE];  // generated code

// leda NTL_CON13A on
reg   [`npuarc_X1_CODE_WIDTH-1:0]    ucode_out;        // output ucode for next stage
reg                           sa_code_cg0;      // enable input ctrl regs
reg                           sa_limm_cg0;      // enable update to sa_limm_r
reg                           sa_pc_cg0;        // enable for SA PC register

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Operand Selection Logic                                                  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// @sa_opd_byp_PROC
//
reg                           sa_ra0_is_eia;    // register da to sa
reg                           sa_ra1_is_eia;    // register da to sa

reg                           sa_is_rdata0_lo;  // select rdata0

reg                           sa_is_rdata0_hi;  // select rdata0_hi
reg                           sa_is_rdata1_lo;  // select rdata1
reg                           sa_is_rdata1_hi;  // select rdata1_hi
reg     [`npuarc_DATA_RANGE]         sa_rdata0;        // low 32 bits from rf port 0
wire    [`npuarc_DATA_RANGE]         br_rdata0_hi;     // high 32-bits from rf port 1
reg     [`npuarc_DATA_RANGE]         sa_rdata0_hi;     // muxed eia/rf port 0
reg     [`npuarc_DATA_RANGE]         sa_rdata1;        // low 32 bits from rf port 1
wire    [`npuarc_DATA_RANGE]         br_rdata1_hi;     // high 32 bits from rf port 1
reg     [`npuarc_DATA_RANGE]         sa_rdata1_hi;     // muxed eia/rf port 1
wire    [`npuarc_DATA_RANGE]         br_rdata0;        // basecase register from port 0
wire    [`npuarc_DATA_RANGE]         br_rdata1;        // basecase register from port 1
reg     [`npuarc_DATA_RANGE]         s6_imm_lo;        // low 32 bits of s6 store data
reg     [`npuarc_DATA_RANGE]         s6_imm_hi;        // high 32 bits of s6 store data
reg     [`npuarc_DATA_RANGE]         byp_reg0_lo;      // bypassed data for reg0_lo
reg     [`npuarc_DATA_RANGE]         byp_reg0_hi;      // bypassed data for reg0_hi
reg     [`npuarc_DATA_RANGE]         byp_reg1_lo;      // bypassed data for reg1_hi
reg     [`npuarc_DATA_RANGE]         byp_reg1_hi;      // bypassed data for reg1_hi
reg     [`npuarc_DATA_RANGE]         sa_link_addr;     // link address or fall-thru PC
reg     [`npuarc_DATA_RANGE]         sa_pc_data;       // value {sa_pc_r,0} for src3

reg     [`npuarc_DATA_RANGE]         br_target_data;   // DATA_RANGE branch target
reg                           sel_br_target;    // x1_src2_nxt is branch target
reg                           sel_store_reg1;   // SA ST insn stores a register
reg                           sel_ext_s6;       // SA ST insn stores an s6 imm.
reg                           sa_is_cti;        // SA insn is a CTI
reg                           sel_link_addr;    // Select link_addr for src3
reg                           sel_reg1_hi;      // Select reg1_hi for src3
reg                           sel_imm_hi;       // Select s6 imm on src3
reg                           sel_sa_pc;        // Select sa_pc_r on src3

// @sa_br_type_PROC
reg                           blink_target;     // SA insn jumps to blink
reg                           unconditional;    // SA insn is unconditional
reg                           leave_pcl;        // SA insn is LEAVE with jump
reg                           sa_uop_predictable_nxt;
reg                           sa_secondary_type;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Instantiate the register file module                                     //
//                                                                          //
//    alb_regfile_2r2w = register file, 2 reads, 1 or 2 writes              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// We store the next PC to ilink at the start of the interrupt prologue.
// We are sure there is no other rf access because CA stage is killed by 
// the interrupt. As ILINK0_REG=29, we need to write to hi port of regfile
// for 64 bit option other wise we write to lo port.
//
reg wa_int_ilink_evt_r;
wire wa_rf_wenb0 ;
assign wa_rf_wenb0                     =  wa_int_ilink_evt_r | wa_rf_wenb0_r;
wire [`npuarc_RGF_ADDR_RANGE] wa_rf_wa0;
assign wa_rf_wa0                       = (wa_int_ilink_evt_r)
                                       ? `npuarc_ILINK0_REG
                                       : wa_rf_wa0_r;

wire [`npuarc_DATA_RANGE]     wa_rf_wdata0_lo;
assign                 wa_rf_wdata0_lo = (wa_int_ilink_evt_r)
                                       ? {wa_pc, `npuarc_PC_LSB'b0}
                                       : wa_rf_wdata0_lo_r; 

wire [`npuarc_DATA_RANGE]     wa_rf_wdata0_hi;
assign                 wa_rf_wdata0_hi = (wa_int_ilink_evt_r)
                                       ? {wa_pc, `npuarc_PC_LSB'b0}
                                       : wa_rf_wdata0_hi_r; 

npuarc_alb_regfile_2r2w u_alb_regfile_2r2w(
  .clk                (clk                ),
  .rst_a              (rst_a              ),
  .ra0                (sa_rf_ra0_r        ),
  .rdata0             (br_rdata0          ),
  .rdata0_hi          (br_rdata0_hi       ),
  .ra1                (sa_rf_ra1_r        ),
  .rdata1             (br_rdata1          ),
  .rdata1_hi          (br_rdata1_hi       ),
  .wa0                (wa_rf_wa0          ),
  .wenb0              (wa_rf_wenb0        ),
  .wdata0             (wa_rf_wdata0_lo    ),
  .wenb0_64           (wa_rf_wenb0_64_r   ),
  .wdata0_hi          (wa_rf_wdata0_hi  ),
  .wenb1              (wa_rf_wenb1_r      ),
  .wa1                (wa_rf_wa1_r        ),
  .wdata1             (wa_rf_wdata1_lo_r  ),
  .wenb1_64           (wa_rf_wenb1_64_r   ),
  .wdata1_hi          (wa_rf_wdata1_hi_r  ),
  .accl_r             (accl_r             ), 
  .acch_r             (acch_r             ),
  .accl_nxt           (wa_accl_nxt        ),
  .acch_nxt           (wa_acch_nxt        ),
  .acc_wenb           (wa_acc_wenb        ),


  .lp_count_r         (ar_lp_count_r      ),
  .pcl                (sa_pc_r[`npuarc_PC_MSB:2] )
);

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Link-address selection logic                                             //
//                                                                          //
// Select the correct link address for BLcc or JLcc instructions, on the    //
// basis of whether the current instruction has a delay-slot or not.        //
// If it does, then the link address is provided by the next sequential PC  //
// of the immediately following instruction (which will be the delay-slot). //
// If it does not have a delay-slot, then the link address is the next      //
// sequential PC of the current instruction, held in sa_seq_pc_r.           //
//                                                                          //
// sa_link_addr also provides the fall-through address for any type of      //
// conditional branch or jump, as well as computing the next LP_START value //
// when executing an LPcc instruction.                                      // 
//                                                                          //
// sa_pc_data contains a 32-bit copy of sa_pc_r that can be forwarded to    //
// x1_src3_nxt when the SA stage contains an LR operation. This is in case  //
// the LR operation attempts to read PC_AUX, in which case the X3 stage     //
// will have a copy of PC that was obtained at SA, and then passed forward  //
// via x1_src3_r and then x2_src0_r.                                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : link_addr_PROC

  sa_link_addr            = `npuarc_DATA_SIZE'd0;
  sa_link_addr[`npuarc_PC_RANGE] = sa_dslot_r ? sa_seq_pc_nxt : sa_seq_pc_r;
  
  sa_pc_data              = `npuarc_DATA_SIZE'd0;
  sa_pc_data[`npuarc_PC_RANGE]   = sa_pc_r;

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process for PC-based computations in the Operand stage.     //
//                                                                          //
// This includes the computation of relative branch or jump targets,        //
// the next sequential PC value, and the selection of the next target       //
// address from the PC-relative branch target and other sources of a        //
// branch target.                                                           //
//                                                                          //
// The ARC instruction set specifies branch displacements as 16-bit half    //
// word displacements relative to the 32-bit aligned PC of the branch       //
// instruction. Hence, we add sa_offset_r[`PC_RANGE] to                     //
// {sa_pc_r[`PC_MSB:2],1'b0} to get the 31-bit target address.              //
//                                                                          //
// The displacement calculation currently uses an inferred adder, which     //
// for reasons of speed and synthesis tool independence can be replaced     //
// by an explicit parallel prefix adder if necessary.                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg     [`npuarc_PC_RANGE]           sa_br_target;     // target of relative branch
// leda NTL_CON13A off
// LMD: non driving internal net
// LJ:  unused carry bit
reg                           unused0;          // unused carry-out
// leda NTL_CON13A on
reg     [`npuarc_PC_RANGE]           sa_adder_src1;    // first input to SA adder
reg     [`npuarc_PC_RANGE]           sa_adder_src2;    // second input to SA adder
reg                           sa_adder_cin;     // carry-in to SA adder

always @*
begin : sa_target_PROC

  //==========================================================================
  // Select the first input to the SA adder. This may be one of the following
  // possible values:
  //
  // (a). JLI_BASE, when performing a JLI_S instruction (sa_jli_src0_r == 1)
  //
  // (b). EI_BASE, when performing an EI_S instruction (sa_ei_op_r == 1)
  //
  // (c). sa_pred_bta_r, for a BI or BIH instruction (sa_btab_op_r == 1)
  //
  // (d). PCL at SA, for all other cases (relative branch and LPcc instrs)
  //
  casez ({ sa_jli_src0_r, sa_ei_op_r, sa_btab_op_r })
    3'b1??:  sa_adder_src1 = { ar_aux_jli_base_r[`npuarc_PC_MSB:2], 1'b0  };
    3'b01?:  sa_adder_src1 = {  ar_aux_ei_base_r[`npuarc_PC_MSB:2], 1'b0  };
    3'b001:  sa_adder_src1 = sa_pred_bta_r;
    default: sa_adder_src1 = {           sa_pc_r[`npuarc_PC_MSB:2], 1'b0  };
  endcase
  
  //==========================================================================
  // Select the second input to the SA adder. This may be one of the following
  // possible values:
  //
  // (a). 1's complement of sa_seq_pc_r, for BI or BIH instructions
  //
  // (b). sa_offset_r, for all other cases.
  //
  sa_adder_src2 = sa_btab_op_r ? (~sa_seq_pc_r) : sa_offset_r[`npuarc_PC_RANGE];

  //==========================================================================
  // Select the carry-in to the SA target adder. This is set to the ucode
  // signal sa_btab_op_r, as the adder will perform a subtraction operation
  // when handling a BI or BIH instruction at this stage. This allows a BI
  // or BIH instruction to compute (sa_pred_bta_r - sa_seq_pc_r), which is
  // then used in the X1 stage to compare with the scaled BI/BIH offset.
  // If they are equal, then the sa_pred_bta_r value was a correct prediction
  // of the value (sa_seq_pc_r + scaled_offset).
  //
  sa_adder_cin  = sa_btab_op_r;
  
  //==========================================================================
  // Compute the target sum calculation, inferring a 31-bit adder with cin.
  //
// leda B_3208 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in arithmetic assignment 
// LJ:  address arithmetic (dont_care carry bit)
// spyglass disable_block W164b
// SMD: Unequal length LHS and RHS in arithmetic assignment 
  {unused0, sa_br_target} = sa_adder_src1 + sa_adder_src2 + sa_adder_cin;
                                      
// leda B_3200 on
// leda B_3208 on  
// spyglass enable_block W164b

end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to determine the branch type for predictions       //
// Also calculate 'secondary' and 'commit_size' for branches.               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : sa_br_type_PROC

  //==========================================================================
  // Decode the branch attributes that are used to determine sa_br_type.
  //
  leave_pcl       = sa_leave_op_r & (da_uop_u7_pcl == 1);
  sa_uop_predictable_nxt = (leave_pcl & sa_pass)
                         | (sa_uop_predictable_r & (~sa_uop_commit_r) &
                           (~sa_kill));

  sa_branch_or_jump  = sa_bcc_r  // includes EI_S and JLI_S
                  | sa_brcc_bbit_r
                  | sa_jump_r
                  | sa_loop_op_r
                  | sa_btab_op_r
                  | sa_in_eslot_r
                  | leave_pcl
                  ;
  
  blink_target    = (   sa_jump_r
                      & (   (sa_rf_renb0_r & (sa_rf_ra0_r == `npuarc_BLINK_REG))
                          | (sa_rf_renb1_r & (sa_rf_ra1_r == `npuarc_BLINK_REG))
                        )
                    )
                  | leave_pcl
                  ;
                  
  //==========================================================================
  // Determine if the branch is unconditional. This will be the case for any
  // Bcc instruction with zero q_field. This case also encodes EI_S and JLI_S.
  // If the SA instruction is in the execution-slot of an EI_S instruction,
  // then the in_eslot ucode bit will have been set at DA. This is used here
  // to indicate that a pseudo-unconditional jump is required.
  //
  unconditional   = ((sa_bcc_r | sa_jump_r) & (sa_q_field_r == 5'd0))
                  | sa_in_eslot_r
                  | leave_pcl
                  | sa_btab_op_r
                  ;

  //==========================================================================
  // Branch prediction of EI_S instructions:
  // Use a phantom subroutine call and return for EI_S and EI_S target.
  // Encode the EI_S instruction as a branch of type unconditional call `BR_CALL.
  // Encode the EI_S target as a branch of type unconditional return `BR_RETURN.

  sa_secondary_type = 1'b0;  
  casez ({  sa_branch_or_jump,
            sa_link_r,
            blink_target,
            unconditional,
            sa_ei_op_r,
            sa_in_eslot_r, 
            sa_hit_lp_end // forced to 0 in zol_pipe when simple version is used
         })
  7'b11?0???: sa_br_type = 3'd`npuarc_BR_COND_CALL;
  7'b11?1???: sa_br_type = 3'd`npuarc_BR_CALL;
  7'b1010???: sa_br_type = 3'd`npuarc_BR_COND_RETURN;
  7'b1011???: sa_br_type = 3'd`npuarc_BR_RETURN;
  7'b1000???: 
     begin
       sa_br_type = 3'd`npuarc_BR_CONDITIONAL;
       sa_secondary_type = 1'b1;
     end
  7'b100100?: sa_br_type = 3'd`npuarc_BR_UNCONDITIONAL;
  7'b10011??: sa_br_type = 3'd`npuarc_BR_CALL;
  7'b100101?: sa_br_type = 3'd`npuarc_BR_RETURN;
  7'b0000001: sa_br_type = 3'd`npuarc_BR_CONDITIONAL;
  default:    sa_br_type = 3'd`npuarc_BR_NOT_PREDICTED;
  endcase

  //==========================================================================
  // Determine a secondary branch:
  // It must be a regular conditional PC-relative branch with type 
  // BR_CONDITIONAL and one of the opcodes Bcc, BRcc, BBIT0, BBIT1, BEQ_S, 
  // BNE_S, BREQ_S, BRNE_S for BEQ_S the q_field[3:0]==4'b0001
  // for BNE_S the q_field[3:0]==4'b0010
  //
  sa_secondary  = sa_secondary_type 
                & ( (   sa_bcc_r 
                      & (   ~sa_is_16bit_r
                          | (sa_q_field_r[3:0] == 4'b0001)
                          | (sa_q_field_r[3:0] == 4'b0010)
                        )
                    )
                   | sa_brcc_bbit_r
                  )
                ;

  if (sa_dslot_r)
    casez({sa_is_16bit_r, sa_is_16bit_nxt})
    2'b11: sa_commit_size = 2'd1;
    2'b10: sa_commit_size = 2'd2;
    2'b01: sa_commit_size = 2'd2;
    2'b00: sa_commit_size = 2'd3;
    endcase
  else
    sa_commit_size     = {sa_has_limm_r, ~sa_is_16bit_r};  

end // sa_br_type_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Property Assertions for operand bypassing logic                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// The following property assertions encapsulate the assumptions upon which //
// the operand selection multiplexers depend.                               //
//                                                                          //
// assert property ( !(sa_stimm_op_r &  sel2_br_target   ) );               //
// assert property ( !(sa_stimm_op_r & (!sa_store_r)       ) );               //
// assert property ( !(sa_stimm_op_r &  sa_jump_r        ) );               //
// assert property ( !(sa_store_r    &  sel2_br_target   ) );               //
// assert property ( !(sa_jump_r     &  sel2_br_target   ) );               //
// assert property ( !(sa_jump_r     &  sa_store_r       ) );               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Operand bypass logic                                                     //
//                                                                          //
// 1. byp_reg0_lo                                                           //
//                                                                          //
// 2. byp_reg0_hi                                                           //
//                                                                          //
// 3. byp_reg1_lo                                                           //
//                                                                          //
// 4. byp_reg1_hi                                                           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : sa_opd_byp_PROC

  //==========================================================================
  // Select pre-bypass register values from the register file output or the
  // limmm, or from EIA if it is included in the core configuration.
  //
  sa_rdata0         =
                       sa_ra0_is_eia ?  eia_sa_reg0 :
                       br_rdata0[`npuarc_DATA_RANGE];
  sa_rdata0_hi      =
                       sa_ra0_is_eia ?  eia_sa_reg0_hi :
                       br_rdata0_hi[`npuarc_DATA_RANGE];
                 
  sa_rdata1         =
                       sa_ra1_is_eia ?  eia_sa_reg1 :
                       br_rdata1[`npuarc_DATA_RANGE];                
  sa_rdata1_hi      =
                       sa_ra1_is_eia ?  eia_sa_reg1_hi :
                       br_rdata1_hi[`npuarc_DATA_RANGE];


  //==========================================================================
  // Assert sa_is_rdata0_lo when read register port 0 is enabled and there
  // is no long-immediate data selected for that port, and no currently
  // available bypass signals.
  //
  sa_is_rdata0_lo   = sa_rf_renb0_r
                    & (~(    sa_limm_r0_r
                          | fwd_x1_sa0_lo
                          | fwd_x2_sa0_lo
                          | fwd_x3_sa0_lo
                          | fwd_ca0_lo_sa0_lo
                          | fwd_ca1_lo_sa0_lo
                          | fwd_wa0_lo_sa0_lo
                          | fwd_wa1_lo_sa0_lo
                          | fwd_ca0_hi_sa0_lo
                          | fwd_wa0_hi_sa0_lo
                          | fwd_ca1_hi_sa0_lo
                          | fwd_wa1_hi_sa0_lo
                          | sa_btab_op_r
                          | sa_ldi_src0_r
                      ) )
                    ;
                
  //==========================================================================
  // Multiplex all possible sources of bypass result with the regfile output
  // for the lower 32 bits of the reg0 operand.
  //
  byp_reg0_lo       = ( {`npuarc_DATA_SIZE{sa_is_rdata0_lo}}   & sa_rdata0         )
                    | ( {`npuarc_DATA_SIZE{sa_limm_r0_r}}      & sa_limm_r         )
                    | ( {`npuarc_DATA_SIZE{fwd_x1_sa0_lo}}     & x1_byp_data0      )
                    | ( {`npuarc_DATA_SIZE{fwd_x2_sa0_lo}}     & x2_byp_data0      )
                    | ( {`npuarc_DATA_SIZE{fwd_x3_sa0_lo}}     & x3_byp_data0      )
                    | ( {`npuarc_DATA_SIZE{fwd_ca0_lo_sa0_lo}} & ca_byp_data0_lo   )
                    | ( {`npuarc_DATA_SIZE{fwd_ca1_lo_sa0_lo}} & ca_byp_data1_lo   )
                    | ( {`npuarc_DATA_SIZE{fwd_wa0_lo_sa0_lo}} & wa_rf_wdata0_lo_r )
                    | ( {`npuarc_DATA_SIZE{fwd_wa1_lo_sa0_lo}} & wa_rf_wdata1_lo_r )
                    | ( {`npuarc_DATA_SIZE{fwd_ca0_hi_sa0_lo}} & ca_byp_data0_hi   )
                    | ( {`npuarc_DATA_SIZE{fwd_wa0_hi_sa0_lo}} & wa_rf_wdata0_hi_r )
                    | ( {`npuarc_DATA_SIZE{fwd_ca1_hi_sa0_lo}} & ca_byp_data1_hi   )
                    | ( {`npuarc_DATA_SIZE{fwd_wa1_hi_sa0_lo}} & wa_rf_wdata1_hi_r )
                    | {({`npuarc_PC_BITS{sa_btab_op_r}}        & sa_seq_pc_r), 1'b0}
                    | ( {`npuarc_DATA_SIZE{sa_ldi_src0_r}}     & ar_aux_ldi_base_r )
                    ;

  //==========================================================================
  // Assert sa_is_rdata1_lo when read register port 1 is enabled and there
  // is no long-immediate data selected for that port, and no currently
  // available bypass signals.
  //
  sa_is_rdata1_lo   = sa_rf_renb1_r
                    & (~(    sa_limm_r1_r
                          | fwd_x1_sa1_lo
                          | fwd_x2_sa1_lo
                          | fwd_x3_sa1_lo
                          | fwd_ca0_lo_sa1_lo
                          | fwd_ca1_lo_sa1_lo
                          | fwd_wa0_lo_sa1_lo
                          | fwd_wa1_lo_sa1_lo
                          | fwd_ca0_hi_sa1_lo
                          | fwd_wa0_hi_sa1_lo
                          | fwd_ca1_hi_sa1_lo
                          | fwd_wa1_hi_sa1_lo
                      ) )
                    ;

  //==========================================================================
  // Multiplex all possible sources of bypass result with the regfile output
  // for the lower 32 bits of the reg1 operand.
  //
  byp_reg1_lo       = ( {`npuarc_DATA_SIZE{sa_is_rdata1_lo}}   & sa_rdata1         )
                    | ( {`npuarc_DATA_SIZE{sa_limm_r1_r}}      & sa_limm_r         )
                    | ( {`npuarc_DATA_SIZE{fwd_x1_sa1_lo}}     & x1_byp_data0      )
                    | ( {`npuarc_DATA_SIZE{fwd_x2_sa1_lo}}     & x2_byp_data0      )
                    | ( {`npuarc_DATA_SIZE{fwd_x3_sa1_lo}}     & x3_byp_data0      )
                    | ( {`npuarc_DATA_SIZE{fwd_ca0_lo_sa1_lo}} & ca_byp_data0_lo   )
                    | ( {`npuarc_DATA_SIZE{fwd_ca1_lo_sa1_lo}} & ca_byp_data1_lo   )
                    | ( {`npuarc_DATA_SIZE{fwd_wa0_lo_sa1_lo}} & wa_rf_wdata0_lo_r )
                    | ( {`npuarc_DATA_SIZE{fwd_wa1_lo_sa1_lo}} & wa_rf_wdata1_lo_r )
                    | ( {`npuarc_DATA_SIZE{fwd_ca0_hi_sa1_lo}} & ca_byp_data0_hi   )
                    | ( {`npuarc_DATA_SIZE{fwd_wa0_hi_sa1_lo}} & wa_rf_wdata0_hi_r )
                    | ( {`npuarc_DATA_SIZE{fwd_ca1_hi_sa1_lo}} & ca_byp_data1_hi   )
                    | ( {`npuarc_DATA_SIZE{fwd_wa1_hi_sa1_lo}} & wa_rf_wdata1_hi_r )
                    ;

  //==========================================================================
  // Assert sa_is_rdata0_hi when read register port 0 is enabled for 64-bit
  // access and there is no currently available bypass signals.
  //
  sa_is_rdata0_hi   = sa_rf_renb0_r
                    & sa_rf_renb0_64_r
                    & (~(    fwd_wa0_hi_sa0_hi
                          | fwd_wa0_lo_sa0_hi
                          | fwd_wa1_lo_sa0_hi
                          | fwd_wa1_hi_sa0_hi
                      ))
                    ;

  //==========================================================================
  // Multiplex all possible sources of bypass result with the regfile output
  // for the upper 32 bits of the reg1 operand.
  //
  byp_reg0_hi       = ( {`npuarc_DATA_SIZE{sa_is_rdata0_hi}}   & sa_rdata0_hi      )
                    | ( {`npuarc_DATA_SIZE{fwd_wa0_hi_sa0_hi
                                  | fwd_wa0_lo_sa0_hi}} & wa_rf_wdata0_hi_r )
                    | ( {`npuarc_DATA_SIZE{fwd_wa1_hi_sa0_hi
                                  | fwd_wa1_lo_sa0_hi}} & wa_rf_wdata1_hi_r )
                    ;

  //==========================================================================
  // Assert sa_is_rdata1_hi when read register port 1 is enabled for 64-bit
  // access and there is no currently available bypass signals.
  //
  sa_is_rdata1_hi   = sa_rf_renb1_r
                    & sa_rf_renb1_64_r
                    & (~(    sa_limm_r1_r
                          | fwd_wa0_lo_sa1_hi
                          | fwd_wa1_lo_sa1_hi
                          | fwd_wa0_hi_sa1_hi
                          | fwd_wa1_hi_sa1_hi
                      ))
                    ;

  //==========================================================================
  // Multiplex all possible sources of bypass result with the regfile output
  // for the upper 32 bits of the reg1 operand.
  //
  byp_reg1_hi       = ( {`npuarc_DATA_SIZE{sa_is_rdata1_hi}}   & sa_rdata1_hi      )
                    | ( {`npuarc_DATA_SIZE{fwd_wa0_hi_sa1_hi}} & wa_rf_wdata0_hi_r )
                    | ( {`npuarc_DATA_SIZE{fwd_wa0_lo_sa1_hi}} & wa_rf_wdata0_lo_r )
                    | ( {`npuarc_DATA_SIZE{fwd_wa1_hi_sa1_hi
                                  | fwd_wa1_lo_sa1_hi}} & wa_rf_wdata1_hi_r )
                    ;

end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Operand selection for x1_src0_nxt and x1_src1_nxt                        //
//                                                                          //
// This process selects x1_src1_nxt, which is the second operand of the     //
// instruction that we are about to dispatch to the Exec1 stage.            //
//                                                                          //
// This operand is may be a register or long-immediate value, which would   //
// be taken from the sa_limm_r input (from the previous pipeline stage) or  //
// it may come from a speculative result at a downstream pipeline stage.    //
//                                                                          //
// Operand 2 may also be provided by sa_shimm_r, which contains any signed  //
// or unsigned short-immediate (shimm) that was contained entirely within   //
// the instruction itself.                                                  //
//                                                                          //
// During debug SR, data is provided by debug module                        //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : sa_sel_src0_src1_PROC

  x1_src0_nxt       = byp_reg0_lo;

  x1_src1_nxt       = sa_sel_shimm_r
                    ? ( sa_vec_shimm_r
                        ? {sa_shimm_r[15:0], sa_shimm_r[15:0]} 
                        : sa_shimm_r
                      ) 
                    : byp_reg1_lo
                    ; 

  //==========================================================================
  // We must pass values on x1_src0_nxt and x1_src1_nxt even if we are not
  // reading a register or using a limm. This is to ensure that zero operands
  // are correctly inserted into the x1_src0_r and x1_src1_r input registers.
  //
  sa_src0_pass      = sa_pass;
  sa_src1_pass      = sa_pass;
  
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Operand selection for x1_src2_nxt and x1_src3_nxt                        //
//                                                                          //
// Select the x1_src2_nxt value from the following possible inputs:         //
//                                                                          //
// (a). byp_reg1_lo, if we have a memory write operation that does not      //
//      use an s6 short immediate store data value.                         //
//                                                                          //
// (b). s6_imm_lo, if we have a memory write operation that uses an s6      //
//      short immediate store data value.                                   //
//                                                                          //
// (c). sa_br_target, if we have an LPcc, Bcc, BLcc, BRcc or BBITn type     //
//      of instruction. In this case the x1_src2_nxt value passes the       //
//      target of a branch, or the LP_END value for LPcc instructions.      //
//      BI and BIH instructions pass the difference between the predicted   //
//      target (sa_pred_bta_r) and the next sequential PC after the BI/BIH  //
//      instruction on x1_src2_nxt, as a timing optimization for the X1     //
//      stage detection of BTA mispredictions for those instructions.       //
//                                                                          //
// (d). byp_reg0_hi, if we have any 64-bit operation that requires reg0.    //
//                                                                          //
// Select the x1_src3_nxt value from the following possible inputs:         //
//                                                                          //
// (e). byp_reg1_hi, if we have a 64-bit memory write operation that does   //
//      not use an s6 short immediate store data value, or we have a 64-bit //
//      extension that needs 64-bit source registers.                       //
//                                                                          //
// (f). 32 copies of the sign bit of the s6 operand, if the instruction is  //
//      storing an s6 short immediate value.                                //
//                                                                          //
// (g). sa_link_addr, if the instruction is any kind of branch, jump or     //
//      LPcc instruction.                                                   //
//                                                                          //
// (h). sa_pc_r, if the instruction is an LR. This allows LR from AUX_PC    //
//      to access the current PC later on, in the X3 stage.                 //
//                                                                          //
// (j). LIMM data sign extension, if the sa_limm1_64_r signal is set.       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : sa_sel_src2_src3_PROC

  //==========================================================================
  // Widen sa_br_target to `DATA_SIZE bit-width prior to selecting it as
  // x1_src2_nxt.
  //
  br_target_data            = `npuarc_DATA_SIZE'd0;
  br_target_data[`npuarc_PC_RANGE] = sa_br_target;
  
  //==========================================================================
  // Define the s6 short immediate store-data value, sign extending to full
  // store-data value width.
  //
  s6_imm_lo         = { {26{sa_rf_ra1_r[5]}}, sa_rf_ra1_r };
  s6_imm_hi         = {`npuarc_DATA_SIZE{sa_rf_ra1_r[5]}};
  
  //==========================================================================
  // sel_store_reg1 indicates that the current instruction will store the
  // value read via register read port 1.
  //
  sel_store_reg1    = sa_store_r & (~sa_stimm_op_r);                      // (a)

  //==========================================================================
  // sel_ext_s6 indicates that x1_src2_nxt should be defined by the s6 short
  // immediate data value.
  // In 64-bit builds, the x1_src3_nxt value contains the upper 32 bits of
  // the sign-extended s6 operand. 
  //
  sel_ext_s6        = sa_store_r & sa_stimm_op_r;                       // (b,e)
  
  //==========================================================================
  // sel_br_target indicates that the current instruction is some kind of
  // relative branch or loop operation. 
  //
  // BI instructions transmit (sa_pred_bta_r - sa_seq_pc_r) to the X1 stage
  // via x1_src2_nxt. For this we need to set sel_br_target when the ucode
  // signal sa_btab_op_r == 1.
  //
  sel_br_target     = sa_loop_op_r                                      // (c)
                    | sa_bcc_r
                    | sa_brcc_bbit_r
                    | sa_rel_branch_r
                    | sa_btab_op_r
                    ;
  
  //==========================================================================
  // sa_is_cti is asserted whenever the SA instruction is a control transfer
  // instruction (CTI) of any description. The SA stage must pass the fall-
  // through address (or linkage value) for every CTI, to x1_src3_r.
  //
  sa_is_cti         = sel_br_target 
                    | sa_jump_r
                    | sa_ei_op_r
                    | sa_jli_src0_r
                    | sa_btab_op_r
                    ;
  
  //==========================================================================
  // x1_src2_nxt is the next input to x1_src2_r
  //
  x1_src2_nxt       = ( ({`npuarc_DATA_SIZE{sel_store_reg1}}   & byp_reg1_lo)    // (a)
                      | ({`npuarc_DATA_SIZE{sel_ext_s6}}       & s6_imm_lo)      // (b)
                      | ({`npuarc_DATA_SIZE{sel_br_target}}    & br_target_data) // (c)
                      | ({`npuarc_DATA_SIZE{sa_rf_renb0_64_r}} & byp_reg0_hi)    // (d)
                      )
                    ;

  
  //==========================================================================
  // Select the appropriate PC value to use as the restart PC when reporting
  // a branch misprediction. This will be the current SA-stage PC when an
  // erroneous branch prediction is associated with the SA-stage instruction.
  // At all other times, it will be the next sequential PC at the SA stage
  // when there is no SA dslot, or the next sequential PC at the DA stage
  // when there is an SA dslot. This is already computed by sa_link_addr
  // for use with BL, JL versus BL.D, JL.D.
  //
  sa_restart_pc     = sa_error_branch 
                    ? sa_pc_r
                    : sa_link_addr[`npuarc_PC_RANGE]
                    ;
                    
  //==========================================================================
  // Disable the selection signals for x1_src3_nxt when there is an
  // erroneous branch prediction in this stage. When this happens,
  // the x1_src3_nxt bus must carry the sa_pc_data value to allow it
  // to be used as the fch_restart value during misprediction.
  //
  sel_link_addr     = sa_is_cti        & (~sa_error_branch);
  
  sel_reg1_hi       = sa_rf_renb1_64_r & (~sa_error_branch);

  sel_imm_hi        = sel_ext_s6       & (~sa_error_branch);
  
  sel_sa_pc         = sa_lr_op_r       | sa_error_branch;
  
  //==========================================================================
  // x1_src3_nxt is the next input to x1_src3_r
  // 
  x1_src3_nxt       = ({`npuarc_DATA_SIZE{sel_link_addr}}    & sa_link_addr)   // (g)
                    | ({`npuarc_DATA_SIZE{sel_reg1_hi}}      & byp_reg1_hi)    // (e)
                    | ({`npuarc_DATA_SIZE{sa_limm1_64_r & sa_limm_r[31]}})     // (j)
                    | ({`npuarc_DATA_SIZE{sel_imm_hi}}       & s6_imm_hi)      // (f)
                    | ({`npuarc_DATA_SIZE{sel_sa_pc}}        & sa_pc_data)     // (h)
                    ;

  //==========================================================================
  // sa_src2_pass indicates whether a new value for x1_src2_r is being
  // produced by the Operand Select stage. It is asserted for all control-
  // transfer operations and all store operations.
  //
  sa_src2_pass      = sa_store_r 
                    | sel_br_target
                    | sa_rf_renb0_64_r
                    ;

  //==========================================================================
  // sa_src3_pass indicates whether a new value for x1_src3_r is being
  // produced by the Operand stage. It is asserted for all control-
  // transfer operations, all 64-bit store operations (if supported),
  // and all 64-bit dyadic operators (if supported).
  //
  sa_src3_pass      = sa_is_cti 
                    | sa_rf_renb1_64_r
                    | sa_limm1_64_r
                    | sel_ext_s6
                    | sa_lr_op_r
                    | sa_error_branch
                    ;
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process for controlling the Operand-stage register updates  //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : sa_ctrl_PROC

  //==========================================================================
  // sa_valid_nxt:  1 => Operands stage receives a valid instruction
  //  This is asserted when the Decode stage asserts da_pass, to
  //  indicate a valid instruction is being forwarded to this stage.
  //
  sa_valid_nxt    = da_pass;

  //==========================================================================
  // sa_code_cg0 enables the update of sa_code_r, and is asserted whenever
  // the sa_enable signal is asserted and there is either an incoming or an
  // outgoing valid instruction at SA.
  //
  sa_code_cg0     = sa_enable & (sa_valid_r | sa_valid_nxt);
  
  //==========================================================================
  // sa_pc_cg0 enables the update of sa_pc_r and sa_seq_pc_r, and is asserted
  // whenever the sa_enable signal is asserted and there is an incoming 
  // valid instruction at SA. 
  // There is no need to update the PC registers when a bubble is
  // inserted at SA, and neitehr sa_pc_r nor sa_seq_pc_r may be updated
  // when a uop is received into the SA stage.
  //
  sa_pc_cg0       = sa_enable 
                  & (   da_pass
                      | da_error_branch_r
                    )
                  ;
  
  //==========================================================================
  // sa_limm_cg0 enables the update of sa_limm_r, and is asserted whenever
  // the sa_enable signal is asserted and there is an incoming limm value
  // at the SA inputs. There is no need to update sa_limm_r register at any
  // other time.
  //
  sa_limm_cg0     = sa_enable & sa_valid_nxt & sa_code_nxt[`npuarc_HAS_LIMM_RANGE];
  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous process to define the ucode sent to the Exec1 stage         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : sa_ucode_PROC

  //==========================================================================
  // Copy operand-select stage micro-code to micro-code output
  //
  ucode_out = sa_code_r[`npuarc_X1_CODE_WIDTH-1:0];

  //==========================================================================
  // If the SA instruction is a branch or jump with linkage and a delay slot
  // then OR the iprot_viol signal from the delay-slot instruction into the
  // branch instruction. The branch has to be replayed as it will not know
  // the size of the delay-slot instruction first time through.
  //
  if (sa_dslot_r & sa_link_r & (!da_in_dslot_r))
    ucode_out[`npuarc_IPROT_VIOL_RANGE] = sa_iprot_viol_r | da_iprot_viol_r;

  //==========================================================================
  // Set the cc_byp_64_haz microcode bit if the SA instruction is conditional,
  // and it defines a 64-bit result, but does not have 64-bit operands.
  // In this case, the instruction cannot perform the normal forwarding
  // of its default source operand in case of a false predicate. This signal
  // is used in the dependency logic to stall subsequent SA-stage
  // instructions that are dependent on the conditional result of this
  // instruction. All instructions, for which this signal gets set to 1,
  // are guaranteed to evaluate their predicate in X1. This signal is 
  // cleared down to 0 at the X1 stage if the predicate is true.
  //
  ucode_out[`npuarc_CC_BYP_64_HAZ_RANGE] = sa_rf_wenb0_64_r
                                  & (~(sa_rf_renb0_64_r | sa_rf_renb1_64_r))
                                  & (sa_q_field_r != 5'd0)
                                  ;
  
  // Kill micro-code bits selectively (reduces fan-out)
  //
  if ((sa_pass == 1'b0) || (sa_error_branch == 1'b1))
  begin
`include "npuarc_ucode_kill_x1.v"
  end

  //==========================================================================
  // The invalid_instr and rgf_link microcode bits are special, as they
  // must be cleared when not passing forward a new instruction. 
  // However, they are not classed as control signals, as they must not
  // be cleared when conditionally-executed instructions are disabled
  // by a false condition.
  //
  if (sa_pass == 1'b0)
  begin
    ucode_out[`npuarc_INVALID_INSTR_RANGE] = 1'b0;
    ucode_out[`npuarc_RGF_LINK_RANGE]      = 1'b0;
  end

end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Synchronous blocks defining Operand-stage pipeline input registers       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

// Pipeline registers for incoming instruction, updated whenever a 
// new instruction is received from the Decode stage.

always @(posedge clk or posedge rst_a)
begin: sa_inst_regs_PROC
  if (rst_a == 1'b1)
    begin
      sa_pc_r         <= `npuarc_PC_BITS'd`npuarc_RESET_PC;
      sa_seq_pc_r     <= `npuarc_PC_BITS'd4;
    end
  else if (sa_pc_cg0 == 1'b1)
    begin
      sa_pc_r         <= sa_pc_nxt;
      sa_seq_pc_r     <= sa_seq_pc_nxt;
    end
end

// Pipeline register for incoming LIMM value, updated whenever a 
// new limm value is received from the Decode stage.

always @(posedge clk or posedge rst_a)
begin: sa_limm_reg_PROC
  if (rst_a == 1'b1)
    begin
      sa_limm_r       <= `npuarc_DATA_SIZE'd0;
    end
  else if (sa_limm_cg0 == 1'b1)
    begin
      sa_limm_r       <= sa_limm_nxt;
   end
end


// Pipeline registers for incoming control and status information, updated
// whenever an instruction arrives or departs this pipeline stage.

always @(posedge clk or posedge rst_a)
begin: sa_code_reg_PROC
  if (rst_a == 1'b1)
    begin
      sa_code_r       <= `npuarc_SA_CODE_WIDTH'd0;
    end
  else if (sa_code_cg0 == 1'b1)
    begin
      sa_code_r       <= sa_code_nxt;
    end
end

always @(posedge clk or posedge rst_a)
begin: sa_uop_predictable_reg_PROC
  if (rst_a == 1'b1)
    begin
      sa_uop_predictable_r <= 1'b0;
    end
  else
    begin
      sa_uop_predictable_r <= sa_uop_predictable_nxt;
    end
end

// Pipeline registers for incoming register source

always @(posedge clk or posedge rst_a)
begin: sa_eia_reg_PROC
  if (rst_a == 1'b1)
    begin
      sa_ra0_is_eia   <= 1'b0;
      sa_ra1_is_eia   <= 1'b0;
    end
  else if (sa_code_cg0 == 1'b1)
    begin
      sa_ra0_is_eia   <= eia_ra0_is_ext;
      sa_ra1_is_eia   <= eia_ra1_is_ext;
    end
end

//int_ilink_evt is from ca stage
//we delay it by one cycle to wa stage
//we are also sure there is no stall at wa stage when int_link_evt = 1
//
always @(posedge clk or posedge rst_a)
begin: wa_ilink_PROC
  if (rst_a == 1'b1) begin
    wa_int_ilink_evt_r <= 1'b0;
  end
  else begin
    wa_int_ilink_evt_r <= int_ilink_evt;
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign  x1_code_nxt     = ucode_out;
assign  sa_pc           = sa_pc_r;
assign  sa_zncv_wen_r   = { sa_z_wen_r, sa_n_wen_r, sa_c_wen_r, sa_v_wen_r };


endmodule // alb_opd_sel
