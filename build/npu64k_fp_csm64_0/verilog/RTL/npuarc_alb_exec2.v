// Library ARCv2HS-3.5.999999999
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2012, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//
//  ####### #     # #######  #####   #####
//  #        #   #  #       #     # #     #
//  #         # #   #       #             #
//  #####      #    #####   #        #####
//  #         # #   #       #       #
//  #        #   #  #       #     # #
//  ####### #     # #######  #####  #######
//
//============================================================================
// @f:execute:
// Description:
// @p
//  This module implements the second execution stage of the Albacore pipeline.
//
//  This module implements the completion of 2-cycle ALU operations that were
//  started in X1, and initiates early correction of branch mispredictions
//  that were detected in X1. This module handles the forwarding of flag
//  updates to X1, in cases where the X2 instruction is flag-modifying and
//  was evaluated at X1.
//
//  The module hierarchy, at and below this module, is:
//
//         alb_exec2
//
//  This stage is aligned with the DC2 stage of the Data Memory Pipeline,
//  with the MP2 stage of the Multiplier Pipeline, and with the FP2 stage
//  of the FPU pipeline.
// @e
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//
`include "npuarc_ucode_const.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_exec2 (
  ////////// General input signals /////////////////////////////////////////
  //
  input                       clk,               // Processor clock
  input                       rst_a,             // Asynchronous reset

  ////////// Inputs from the Debug unit //////////////////////////////////////
  // 
  input                       db_active,         // debug operation is active
  input  [`npuarc_DATA_RANGE]        db_data,           // data for debug SR or ST             
  input                       db_sel_limm0,      // select debug data for SR  
  input                       db_sel_limm1,      // select debug data for ST  

  ////////// Inputs from Exec1 stage /////////////////////////////////////////
  //
  input      [`npuarc_DATA_RANGE]    x2_src0_nxt,       //
  input      [`npuarc_DATA_RANGE]    x2_src1_nxt,       //
  input      [`npuarc_DATA_RANGE]    x1_byp_data0,      //
  input                       x1_src0_pass,      //
  input                       x1_src1_pass,      //
  input                       x1_res_pass,       //
  input      [`npuarc_ZNCV_RANGE]    x2_zncv_nxt,       //

  input  [`npuarc_X2_CODE_WIDTH-1:0] x2_code_nxt,       //
  input                       x2_lt_flag_nxt,    //
  input      [`npuarc_PC_RANGE]      x2_target_nxt,     //

  input      [`npuarc_ADDR_RANGE]    x1_mem_addr0,      // memory address from X1
  input                       x1_addr_pass,      // X1 passing valid mem addr

  ////////// Inputs from Dependency Pipeline /////////////////////////////////
  //
  input                       x2_valid_r,        //
  input                       x2_done_r,         //
  input                       x2_pass,           //
  input                       x2_enable,         //
  input                       x2_retain,         //
  input                       x2_read_r0_r,      //
  input                       x2_read_r1_r,      //
  input                       x1_pass,           //
  
  ////////// Inputs from Prediction Pipeline /////////////////////////////////
  //
  input                       x2_fragged_r,      //
  input                       x2_error_branch_r, //

  ////////// Architecturally-committed state ////////////////////////////////
  //
  input   [`npuarc_DATA_RANGE]       ar_aux_jli_base_r,// JLI_BASE aux register
  input   [`npuarc_DATA_RANGE]       ar_aux_ldi_base_r,// LDI_BASE register
  input   [`npuarc_DATA_RANGE]       ar_aux_ei_base_r, // EI_BASE aux register
  // leda NTL_CON13C off
  // LMD: non driving port
  // LJ:  Bit 7 is updated by other signal
  input   [`npuarc_DATA_RANGE]       ar_aux_status32_r, //status32
  // leda NTL_CON13C on
  input                       ar_aux_user_mode_r,//arch. user mode 
  input   [`npuarc_DATA_RANGE]       ar_aux_lp_start_r, //
  input   [`npuarc_DATA_RANGE]       ar_aux_lp_end_r,   //

  ////////// Forwarding Interface ////////////////////////////////////////////
  //
  input                       fwd_x2_r0_wa_w0_lo,//
  input                       fwd_x2_r0_wa_w1_lo,//
  input                       fwd_x2_r1_wa_w0_lo,//
  input                       fwd_x2_r1_wa_w1_lo,//
  input                       fwd_x2_r0_wa_w0_hi,//
  input                       fwd_x2_r1_wa_w0_hi,//
  input                       fwd_x2_r0_wa_w1_hi,//
  input                       fwd_x2_r1_wa_w1_hi,//
  input                       fwd_x2_r1h_wa_w0_lo,
  input                       fwd_x2_r1h_wa_w1_lo,
  input                       fwd_x2_r1h_wa_w0_hi,
  input                       fwd_x2_r1h_wa_w1_hi,

  //
  input      [`npuarc_DATA_RANGE]    wa_rf_wdata0_lo_r, //
  input      [`npuarc_DATA_RANGE]    wa_rf_wdata1_lo_r, //
  input      [`npuarc_DATA_RANGE]    wa_rf_wdata0_hi_r, //
  input      [`npuarc_DATA_RANGE]    wa_rf_wdata1_hi_r, //

  ////////// Exec2 Stage Outputs /////////////////////////////////////////////
  //
  output reg [`npuarc_ADDR_RANGE]    x2_mem_addr_r,     // registered X2 mem address
//`if (`HAS_MPU == 1)
//  output reg [`ADDR_RANGE]    x2_mem_addr1_r,    // registered X2 mem address
//`endif
  output                      x2_uop_inst_r,     // Insn. at X2 is uop.

  ////////// output to eia dependency logic //////////////////////////////////
  //
  output                      x2_dest_cr_is_ext_r, // to eia dep logic

  ////////// Pipe outputs ////////////////////////////////////////////////////
  //
  output   [`npuarc_Q_FIELD_RANGE]   x2_q_field_r,      //
  output                      x2_dslot_r,        //
  output                      x2_in_eslot_r,
  output                      x2_sync_op_r,      //
  output                      x2_slow_op_r,      //
  output                      x2_load_r,         //
  output                      x2_store_r,        //
  output                      x2_pref_r,         //
  output reg [1:0]            x2_size_r,         //
  output reg [`npuarc_ZNCV_RANGE]    x2_zncv_r,         //
  output     [`npuarc_ZNCV_RANGE]    x2_zncv_wen_r,     //
  output                      x2_wevt_op,        // 
  output                      x2_flag_op_r,      //
  output                      x2_signed_op_r,    //
  output                      x2_invalid_instr_r,//
  output                      x2_illegal_operand_r,//
  output                      x2_jump_r,         //
  output                      x2_has_limm_r,     //
  output                      x2_rtie_op_r,      //
  output                      x2_leave_op_r,      //
  output                      x2_cache_byp_r,    //
  output                      x2_rel_branch_r,   //
  output                      x2_kernel_op_r,    // Insn at X2 requires kern.
  output                      x2_rgf_link_r,     // Insn at X2 accesses ILINK
  output                      x2_brk_op_r,       // Insn at X2 is BRK(_S)
  output                      x2_multi_op_r,     // Insn at X2 is multi-op class
  output                      x2_btab_op_r,      // Insn at X2 is BI{,H,C}
  output reg [`npuarc_DATA_RANGE]    x2_byp_data0,      //
  output [`npuarc_RGF_ADDR_RANGE]    x2_rf_ra0_r,       // reg-read address 0 at X2
  output [`npuarc_RGF_ADDR_RANGE]    x2_rf_ra1_r,       // reg-read address 1 at X2
  output [`npuarc_RGF_ADDR_RANGE]    x2_rf_wa0_r,       //
  output                      x2_rf_wenb0_r,     //
  output                      x2_rf_wenb0_64_r,  //
  output                      x2_cc_byp_64_haz_r,// X2 insn cannot bypass r0h
  output  [`npuarc_RGF_ADDR_RANGE]   x2_rf_wa1_r,       //
  output                      x2_rf_wenb1_r,     //
  output                      x2_rf_wenb1_64_r,  //
  output                      x2_rf_renb0_64_r,  //
  output                      x2_rf_renb1_64_r,  //
  output                      x2_acc_wenb_r,     //

  output                      x2_rf_renb0_r,     // 
  output                      x2_rf_renb1_r,     // 
  output                      x2_locked_r,       //
  ////////// LR/SR AUX. Interface ////////////////////////////////////////////
  //
  output     [`npuarc_DATA_RANGE]    x2_aux_addr_r,     //
  output                      x2_lr_op_r,        //
  output                      x2_sr_op_r,        //

  ////////// Outputs to Dependency Pipeline //////////////////////////////////
  //
  output reg                  x2_valid_nxt,      //
  output                      x2_ei_op_r,        //
  output                      x2_dmb_op_r,      // DMB insn at X2
  output     [2:0]            x2_dmb_type_r,    // DMB u3 operand at X2

  ////////// Outputs to the ZOL pipeline /////////////////////////////////////
  //
  output                      x2_wa0_lpc_r,     //
  output                      x2_loop_op_r,     //
  
  ////////// Outputs to Multiplier Pipeline //////////////////////////////////
  //
  output                      x2_mpy_op_r,      // mpy op in X2
  output                      x2_half_size_r,   // scalar operand is 16 bits
  output                      x2_dual_op_r,     // dual SIMD operation
  output                      x2_vector_op_r,   // independent channels
  output                      x2_quad_op_r,     // quad SIMD operation

  ////////// Outputs to Divide unit //////////////////////////////////////////
  //
  output                      x2_div_op_r,      // DIV, REM at X2 stage

  ////////// Outputs to Exec3 ////////////////////////////////////////////////
  //
  output reg [`npuarc_DATA_RANGE]    x3_src0_nxt,      //
  output reg [`npuarc_DATA_RANGE]    x3_src1_nxt,      //
  output reg [`npuarc_DATA_RANGE]    x3_res_nxt,       //
  output reg                  x2_src0_pass,     //
  output reg                  x2_src1_pass,     //
  output reg                  x2_res_pass,      //
  output reg                  x2_addr_pass,     //
  output [`npuarc_X3_CODE_WIDTH-1:0] x3_code_nxt,      //
  output reg [`npuarc_PC_RANGE]      x3_target_nxt,    //
  output     [`npuarc_ZNCV_RANGE]    x3_zncv_nxt       //
);

// @x2_bypass_PROC
//
reg                           r0_lo_wa_byp;         // src0 gets bypass from WA
reg                           r1_lo_wa_byp;         // src1 gets bypass from WA
reg                           r0_lo_no_byp;         // src0 does not bypass
reg                           r1_lo_no_byp;         // src1 does not bypass
reg [`npuarc_DATA_RANGE]             r0_wa_byp_data;       // WA bypass data for src0
reg [`npuarc_DATA_RANGE]             r1_wa_byp_data;       // WA bypass data for src1
reg [`npuarc_DATA_RANGE]             x2_next_src0;         // next value for x2_src0_r
reg [`npuarc_DATA_RANGE]             x2_next_src1;         // next value for x2_src1_r
reg                           x2_uop_prol_r1;       // read reg1 in uop prol
reg                           x2_uop_sel_status32;  // sel STATUS32 in uop seq

reg [`npuarc_DATA_RANGE]             uop_aux_status32;     // STATUS32 to save by uop

reg                           x2_uop_sel_jli_base;  // sel JLI_BASE in uop seq
reg                           x2_uop_sel_ei_base;
reg                           x2_uop_sel_ldi_base;
reg                           x2_uop_sel_lp_start;
reg                           x2_uop_sel_lp_end;
reg [`npuarc_DATA_RANGE]             r1_uop_st_data;
reg                           x2_src1_is_uop;
 

// @x2_result_PROC
//
reg                           x2_is_mem_op;
reg                           x2_is_branch;

// @x2_ctrl_PROC
//
reg                           x2_grab_src0;       // grab a WA bypass for src0
reg                           x2_grab_src1;       // grab a WA bypass for src1
reg                           x2_code_cg0;
reg                           x2_res_cg0;
reg                           x2_src0_cg0;
reg                           x2_src1_cg0;

reg                           x2_target_cg0;
reg                           x2_mem_addr_cg0;

// @x2_ucode_PROC
//
reg [`npuarc_X3_CODE_WIDTH-1:0]      ucode_out;

// @x2_src_regs_PROC
//
reg [`npuarc_DATA_RANGE]             x2_src0_r;
reg [`npuarc_DATA_RANGE]             x2_src1_r;
reg [`npuarc_DATA_RANGE]             x2_res_r;
reg                           x2_lt_flag_r;
reg [`npuarc_PC_RANGE]               x2_target_r;

// @x2_ctrl_regs_PROC
//
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some addr bits unused
reg [`npuarc_X2_CODE_WIDTH-1:0]      x2_code_r;
// leda NTL_CON32 on
// Assign each microcode field to a named wire or wire-vector
//
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

assign x2_rf_wa0_r  = x2_code_r[`npuarc_RF_WA0_RANGE];  // generated code
assign x2_rf_wenb0_r  = x2_code_r[`npuarc_RF_WENB0_RANGE];  // generated code
assign x2_rf_wenb0_64_r  = x2_code_r[`npuarc_RF_WENB0_64_RANGE];  // generated code
assign x2_cc_byp_64_haz_r  = x2_code_r[`npuarc_CC_BYP_64_HAZ_RANGE];  // generated code
assign x2_has_limm_r  = x2_code_r[`npuarc_HAS_LIMM_RANGE];  // generated code
wire   x2_is_16bit_r;  // generated code
assign x2_is_16bit_r  = x2_code_r[`npuarc_IS_16BIT_RANGE];  // generated code
assign x2_sr_op_r   = x2_code_r[`npuarc_SR_OP_RANGE];  // generated code
assign x2_loop_op_r  = x2_code_r[`npuarc_LOOP_OP_RANGE];  // generated code
assign x2_locked_r  = x2_code_r[`npuarc_LOCKED_RANGE];  // generated code
assign x2_wa0_lpc_r  = x2_code_r[`npuarc_WA0_LPC_RANGE];  // generated code
assign x2_dslot_r   = x2_code_r[`npuarc_DSLOT_RANGE];  // generated code
wire   x2_sleep_op_r;  // generated code
assign x2_sleep_op_r  = x2_code_r[`npuarc_SLEEP_OP_RANGE];  // generated code
assign x2_acc_wenb_r  = x2_code_r[`npuarc_ACC_WENB_RANGE];  // generated code
wire   x2_writes_acc_r;  // generated code
assign x2_writes_acc_r  = x2_code_r[`npuarc_WRITES_ACC_RANGE];  // generated code
assign x2_lr_op_r   = x2_code_r[`npuarc_LR_OP_RANGE];  // generated code
assign x2_jump_r    = x2_code_r[`npuarc_JUMP_RANGE];  // generated code
assign x2_load_r    = x2_code_r[`npuarc_LOAD_RANGE];  // generated code
assign x2_pref_r    = x2_code_r[`npuarc_PREF_RANGE];  // generated code
assign x2_store_r   = x2_code_r[`npuarc_STORE_RANGE];  // generated code
wire   x2_uop_prol_r;  // generated code
assign x2_uop_prol_r  = x2_code_r[`npuarc_UOP_PROL_RANGE];  // generated code
assign x2_rf_wa1_r  = x2_code_r[`npuarc_RF_WA1_RANGE];  // generated code
assign x2_rf_wenb1_r  = x2_code_r[`npuarc_RF_WENB1_RANGE];  // generated code
assign x2_rf_wenb1_64_r  = x2_code_r[`npuarc_RF_WENB1_64_RANGE];  // generated code
assign x2_signed_op_r  = x2_code_r[`npuarc_SIGNED_OP_RANGE];  // generated code
assign x2_double_size_r  = x2_code_r[`npuarc_DOUBLE_SIZE_RANGE];  // generated code
assign x2_half_size_r  = x2_code_r[`npuarc_HALF_SIZE_RANGE];  // generated code
wire   x2_byte_size_r;  // generated code
assign x2_byte_size_r  = x2_code_r[`npuarc_BYTE_SIZE_RANGE];  // generated code
assign x2_rtie_op_r  = x2_code_r[`npuarc_RTIE_OP_RANGE];  // generated code
wire   x2_enter_op_r;  // generated code
assign x2_enter_op_r  = x2_code_r[`npuarc_ENTER_OP_RANGE];  // generated code
assign x2_leave_op_r  = x2_code_r[`npuarc_LEAVE_OP_RANGE];  // generated code
wire   x2_trap_op_r;  // generated code
assign x2_trap_op_r  = x2_code_r[`npuarc_TRAP_OP_RANGE];  // generated code
assign x2_sync_op_r  = x2_code_r[`npuarc_SYNC_OP_RANGE];  // generated code
assign x2_brk_op_r  = x2_code_r[`npuarc_BRK_OP_RANGE];  // generated code
assign x2_invalid_instr_r  = x2_code_r[`npuarc_INVALID_INSTR_RANGE];  // generated code
assign x2_rgf_link_r  = x2_code_r[`npuarc_RGF_LINK_RANGE];  // generated code
wire   x2_prod_sign_r;  // generated code
assign x2_prod_sign_r  = x2_code_r[`npuarc_PROD_SIGN_RANGE];  // generated code
wire   x2_macu_r;  // generated code
assign x2_macu_r  = x2_code_r[`npuarc_MACU_RANGE];  // generated code
assign x2_quad_op_r  = x2_code_r[`npuarc_QUAD_OP_RANGE];  // generated code
wire   x2_acc_op_r;  // generated code
assign x2_acc_op_r  = x2_code_r[`npuarc_ACC_OP_RANGE];  // generated code
assign x2_vector_op_r  = x2_code_r[`npuarc_VECTOR_OP_RANGE];  // generated code
assign x2_dual_op_r  = x2_code_r[`npuarc_DUAL_OP_RANGE];  // generated code
assign x2_mpy_op_r  = x2_code_r[`npuarc_MPY_OP_RANGE];  // generated code
wire   x2_z_wen_r;  // generated code
assign x2_z_wen_r  = x2_code_r[`npuarc_Z_WEN_RANGE];  // generated code
wire   x2_n_wen_r;  // generated code
assign x2_n_wen_r  = x2_code_r[`npuarc_N_WEN_RANGE];  // generated code
wire   x2_c_wen_r;  // generated code
assign x2_c_wen_r  = x2_code_r[`npuarc_C_WEN_RANGE];  // generated code
wire   x2_v_wen_r;  // generated code
assign x2_v_wen_r  = x2_code_r[`npuarc_V_WEN_RANGE];  // generated code
assign x2_kernel_op_r  = x2_code_r[`npuarc_KERNEL_OP_RANGE];  // generated code
assign x2_flag_op_r  = x2_code_r[`npuarc_FLAG_OP_RANGE];  // generated code
wire   x2_bcc_r;  // generated code
assign x2_bcc_r  = x2_code_r[`npuarc_BCC_RANGE];  // generated code
wire   x2_link_r;  // generated code
assign x2_link_r  = x2_code_r[`npuarc_LINK_RANGE];  // generated code
wire   x2_brcc_bbit_r;  // generated code
assign x2_brcc_bbit_r  = x2_code_r[`npuarc_BRCC_BBIT_RANGE];  // generated code
assign x2_cache_byp_r  = x2_code_r[`npuarc_CACHE_BYP_RANGE];  // generated code
assign x2_slow_op_r  = x2_code_r[`npuarc_SLOW_OP_RANGE];  // generated code
wire   x2_fast_op_r;  // generated code
assign x2_fast_op_r  = x2_code_r[`npuarc_FAST_OP_RANGE];  // generated code
assign x2_div_op_r  = x2_code_r[`npuarc_DIV_OP_RANGE];  // generated code
assign x2_btab_op_r  = x2_code_r[`npuarc_BTAB_OP_RANGE];  // generated code
assign x2_ei_op_r   = x2_code_r[`npuarc_EI_OP_RANGE];  // generated code
assign x2_in_eslot_r  = x2_code_r[`npuarc_IN_ESLOT_RANGE];  // generated code
assign x2_rel_branch_r  = x2_code_r[`npuarc_REL_BRANCH_RANGE];  // generated code
assign x2_illegal_operand_r  = x2_code_r[`npuarc_ILLEGAL_OPERAND_RANGE];  // generated code
wire   x2_swap_op_r;  // generated code
assign x2_swap_op_r  = x2_code_r[`npuarc_SWAP_OP_RANGE];  // generated code
wire   x2_setcc_op_r;  // generated code
assign x2_setcc_op_r  = x2_code_r[`npuarc_SETCC_OP_RANGE];  // generated code
wire [2:0]  x2_cc_field_r;  // generated code
assign x2_cc_field_r  = x2_code_r[`npuarc_CC_FIELD_RANGE];  // generated code
assign x2_q_field_r  = x2_code_r[`npuarc_Q_FIELD_RANGE];  // generated code
assign x2_dest_cr_is_ext_r  = x2_code_r[`npuarc_DEST_CR_IS_EXT_RANGE];  // generated code
wire   x2_add_op_r;  // generated code
assign x2_add_op_r  = x2_code_r[`npuarc_ADD_OP_RANGE];  // generated code
wire   x2_and_op_r;  // generated code
assign x2_and_op_r  = x2_code_r[`npuarc_AND_OP_RANGE];  // generated code
wire   x2_or_op_r;  // generated code
assign x2_or_op_r  = x2_code_r[`npuarc_OR_OP_RANGE];  // generated code
wire   x2_xor_op_r;  // generated code
assign x2_xor_op_r  = x2_code_r[`npuarc_XOR_OP_RANGE];  // generated code
wire   x2_mov_op_r;  // generated code
assign x2_mov_op_r  = x2_code_r[`npuarc_MOV_OP_RANGE];  // generated code
wire   x2_with_carry_r;  // generated code
assign x2_with_carry_r  = x2_code_r[`npuarc_WITH_CARRY_RANGE];  // generated code
wire   x2_simple_shift_op_r;  // generated code
assign x2_simple_shift_op_r  = x2_code_r[`npuarc_SIMPLE_SHIFT_OP_RANGE];  // generated code
wire   x2_left_shift_r;  // generated code
assign x2_left_shift_r  = x2_code_r[`npuarc_LEFT_SHIFT_RANGE];  // generated code
wire   x2_rotate_op_r;  // generated code
assign x2_rotate_op_r  = x2_code_r[`npuarc_ROTATE_OP_RANGE];  // generated code
wire   x2_inv_src1_r;  // generated code
assign x2_inv_src1_r  = x2_code_r[`npuarc_INV_SRC1_RANGE];  // generated code
wire   x2_inv_src2_r;  // generated code
assign x2_inv_src2_r  = x2_code_r[`npuarc_INV_SRC2_RANGE];  // generated code
wire   x2_bit_op_r;  // generated code
assign x2_bit_op_r  = x2_code_r[`npuarc_BIT_OP_RANGE];  // generated code
wire   x2_mask_op_r;  // generated code
assign x2_mask_op_r  = x2_code_r[`npuarc_MASK_OP_RANGE];  // generated code
wire   x2_src2_mask_sel_r;  // generated code
assign x2_src2_mask_sel_r  = x2_code_r[`npuarc_SRC2_MASK_SEL_RANGE];  // generated code
wire   x2_uop_commit_r;  // generated code
assign x2_uop_commit_r  = x2_code_r[`npuarc_UOP_COMMIT_RANGE];  // generated code
wire   x2_uop_epil_r;  // generated code
assign x2_uop_epil_r  = x2_code_r[`npuarc_UOP_EPIL_RANGE];  // generated code
wire   x2_uop_excpn_r;  // generated code
assign x2_uop_excpn_r  = x2_code_r[`npuarc_UOP_EXCPN_RANGE];  // generated code
wire   x2_predicate_r;  // generated code
assign x2_predicate_r  = x2_code_r[`npuarc_PREDICATE_RANGE];  // generated code
assign x2_rf_renb0_r  = x2_code_r[`npuarc_RF_RENB0_RANGE];  // generated code
assign x2_rf_renb1_r  = x2_code_r[`npuarc_RF_RENB1_RANGE];  // generated code
assign x2_rf_renb0_64_r  = x2_code_r[`npuarc_RF_RENB0_64_RANGE];  // generated code
assign x2_rf_renb1_64_r  = x2_code_r[`npuarc_RF_RENB1_64_RANGE];  // generated code
assign x2_rf_ra0_r  = x2_code_r[`npuarc_RF_RA0_RANGE];  // generated code
assign x2_rf_ra1_r  = x2_code_r[`npuarc_RF_RA1_RANGE];  // generated code
wire   x2_jli_src0_r;  // generated code
assign x2_jli_src0_r  = x2_code_r[`npuarc_JLI_SRC0_RANGE];  // generated code
assign x2_uop_inst_r  = x2_code_r[`npuarc_UOP_INST_RANGE];  // generated code
wire   x2_vec_shimm_r;  // generated code
assign x2_vec_shimm_r  = x2_code_r[`npuarc_VEC_SHIMM_RANGE];  // generated code
wire   x2_iprot_viol_r;  // generated code
assign x2_iprot_viol_r  = x2_code_r[`npuarc_IPROT_VIOL_RANGE];  // generated code
assign x2_dmb_op_r  = x2_code_r[`npuarc_DMB_OP_RANGE];  // generated code
assign x2_dmb_type_r  = x2_code_r[`npuarc_DMB_TYPE_RANGE];  // generated code
wire   x2_force_cin_r;  // generated code
assign x2_force_cin_r  = x2_code_r[`npuarc_FORCE_CIN_RANGE];  // generated code
wire   x2_opd3_sel_r;  // generated code
assign x2_opd3_sel_r  = x2_code_r[`npuarc_OPD3_SEL_RANGE];  // generated code
assign x2_multi_op_r  = x2_code_r[`npuarc_MULTI_OP_RANGE];  // generated code
wire   x2_abs_op_r;  // generated code
assign x2_abs_op_r  = x2_code_r[`npuarc_ABS_OP_RANGE];  // generated code
wire   x2_min_op_r;  // generated code
assign x2_min_op_r  = x2_code_r[`npuarc_MIN_OP_RANGE];  // generated code
wire   x2_max_op_r;  // generated code
assign x2_max_op_r  = x2_code_r[`npuarc_MAX_OP_RANGE];  // generated code
wire   x2_norm_op_r;  // generated code
assign x2_norm_op_r  = x2_code_r[`npuarc_NORM_OP_RANGE];  // generated code
wire   x2_ldi_src0_r;  // generated code
assign x2_ldi_src0_r  = x2_code_r[`npuarc_LDI_SRC0_RANGE];  // generated code
wire   x2_pre_addr_r;  // generated code
assign x2_pre_addr_r  = x2_code_r[`npuarc_PRE_ADDR_RANGE];  // generated code

// leda NTL_CON13A on

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to define the operand datapath at X2               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           src0_no_fwd;
reg                           src1_no_fwd;
reg                           src0_wa_w0_lo;
reg                           src0_wa_w1_lo;
reg                           src0_wa_w0_hi;
reg                           src0_wa_w1_hi;
reg                           x2_std_op;

always @*
begin: x2_bypass_PROC

  //==========================================================================
  // Define the STATUS32 value for use when saving context during an interrupt
  // prologue sequence. This is the architectural STATUS32 register with the
  // U bit set to the architecturally-committed User Mode flag.
  //
  uop_aux_status32          = ar_aux_status32_r;
  uop_aux_status32[`npuarc_U_FLAG] = ar_aux_user_mode_r;

  //==========================================================================
  // Decode auxiliary register source operands that are required as store 
  // data during interrupt prologue uop sequences.
  //
  x2_uop_prol_r1      = x2_uop_prol_r & x2_rf_renb1_r;
  
  x2_uop_sel_jli_base = x2_uop_prol_r1 & (x2_rf_ra1_r == `npuarc_JLI_BASE_REG);
  x2_uop_sel_ei_base  = x2_uop_prol_r1 & (x2_rf_ra1_r == `npuarc_EI_BASE_REG );
  x2_uop_sel_ldi_base = x2_uop_prol_r1 & (x2_rf_ra1_r == `npuarc_LDI_BASE_REG);
  x2_uop_sel_status32 = x2_uop_prol_r1 & (x2_rf_ra1_r == `npuarc_STATUS32_REG);
  x2_uop_sel_lp_start = x2_uop_prol_r1 & (x2_rf_ra1_r == `npuarc_LP_START_REG);
  x2_uop_sel_lp_end   = x2_uop_prol_r1 & (x2_rf_ra1_r == `npuarc_LP_END_REG  );

  x2_src1_is_uop      = x2_uop_sel_status32
                      | x2_uop_sel_lp_start
                      | x2_uop_sel_lp_end
                      | x2_uop_sel_jli_base
                      | x2_uop_sel_ei_base
                      | x2_uop_sel_ldi_base
                      ;

  r1_uop_st_data      = ({`npuarc_DATA_SIZE{x2_uop_sel_status32}} & uop_aux_status32 )
                      | ({`npuarc_DATA_SIZE{x2_uop_sel_jli_base}} & ar_aux_jli_base_r)
                      | ({`npuarc_DATA_SIZE{x2_uop_sel_ei_base}}  & ar_aux_ei_base_r )
                      | ({`npuarc_DATA_SIZE{x2_uop_sel_ldi_base}} & ar_aux_ldi_base_r)
                      | ({`npuarc_DATA_SIZE{x2_uop_sel_lp_start}} & ar_aux_lp_start_r)
                      | ({`npuarc_DATA_SIZE{x2_uop_sel_lp_end}}   & ar_aux_lp_end_r  )
                      ;

                      
  //==========================================================================
  // Define the conditions under which each WA-stage bypass result is to be
  // forwarded to the x3_src0_nxt operand.
  // There are two cases where each bypass result is required by x3_src0_nxt,
  // either (a) when the result is needed by the first source operand of
  // a deferred ALU operation, or (b) when the result is needed by a 64-bit
  // STD operation to provide the upper 32 bits of store data.
  //
  x2_std_op       = x2_store_r & x2_double_size_r;
  
  src0_wa_w0_lo   = x2_std_op ? fwd_x2_r1h_wa_w0_lo : fwd_x2_r0_wa_w0_lo;
  src0_wa_w1_lo   = x2_std_op ? fwd_x2_r1h_wa_w1_lo : fwd_x2_r0_wa_w1_lo;
  src0_wa_w0_hi   = x2_std_op ? fwd_x2_r1h_wa_w0_hi : fwd_x2_r0_wa_w0_hi;
  src0_wa_w1_hi   = x2_std_op ? fwd_x2_r1h_wa_w1_hi : fwd_x2_r0_wa_w1_hi;

  //==========================================================================
  // Instructions that do not have a read flag set for reg0 should not 
  // include forwarded results from WA, as they will have already been taken.
  //
  src0_no_fwd     = !x2_std_op & (!x2_read_r0_r);
  
  //==========================================================================
  // Instructions that have a false predicate, and define a 64-bit non-load
  // result, must not have their src1 operand value updated at the X2 stage.
  // This is because it is already resolved at this point, and contains the
  // x1_false_res_hi value for use when forwarding that result at CA and WA.
  // 
  src1_no_fwd     = !x2_read_r1_r
                  | (x2_rf_wenb0_64_r & (!x2_predicate_r))
                  ;
  
  //==========================================================================
  // 
  r0_lo_wa_byp    = src0_wa_w0_lo
                  | src0_wa_w1_lo
                  | src0_wa_w0_hi
                  | src0_wa_w1_hi
                  ;

  //==========================================================================
  //
  r0_lo_no_byp    = (~r0_lo_wa_byp)
                  | x2_lr_op_r
                  | src0_no_fwd
                  ;

  //==========================================================================
  //
  r0_wa_byp_data  = ( {`npuarc_DATA_SIZE{src0_wa_w0_lo}} & wa_rf_wdata0_lo_r )
                  | ( {`npuarc_DATA_SIZE{src0_wa_w1_lo}} & wa_rf_wdata1_lo_r )
                  | ( {`npuarc_DATA_SIZE{src0_wa_w0_hi}} & wa_rf_wdata0_hi_r )
                  | ( {`npuarc_DATA_SIZE{src0_wa_w1_hi}} & wa_rf_wdata1_hi_r )
                  ;

  //==========================================================================
  //
  x3_src0_nxt     = db_sel_limm0
                  ? db_data                                            // dbg
                  : (r0_lo_no_byp ? x2_src0_r : r0_wa_byp_data)
                  ;

  //==========================================================================
  //
// spyglass disable_block Ac_conv01
// SMD: synchronizers converge on combinational gate
// SJ:  functionally independent signals
  x2_next_src0    = x2_retain ? r0_wa_byp_data : x2_src0_nxt;
// spyglass enable_block Ac_conv01
  //==========================================================================
  //
  r1_lo_wa_byp    = fwd_x2_r1_wa_w0_lo
                  | fwd_x2_r1_wa_w1_lo
                  | fwd_x2_r1_wa_w0_hi
                  | fwd_x2_r1_wa_w1_hi
                  ;
 
  //==========================================================================
  //
  r1_lo_no_byp    = (~r1_lo_wa_byp)
                  | src1_no_fwd
                  ;

  //==========================================================================
  //
  r1_wa_byp_data  = ( {`npuarc_DATA_SIZE{fwd_x2_r1_wa_w0_lo}} & wa_rf_wdata0_lo_r )
                  | ( {`npuarc_DATA_SIZE{fwd_x2_r1_wa_w1_lo}} & wa_rf_wdata1_lo_r )
                  | ( {`npuarc_DATA_SIZE{fwd_x2_r1_wa_w0_hi}} & wa_rf_wdata0_hi_r )
                  | ( {`npuarc_DATA_SIZE{fwd_x2_r1_wa_w1_hi}} & wa_rf_wdata1_hi_r )
                  ;

  //==========================================================================
  //
  casez ({ 
          db_sel_limm1
         ,x2_src1_is_uop
        })
  2'b1?:    x3_src1_nxt = db_data;                                      // (c)
  2'b01:    x3_src1_nxt = r1_uop_st_data;                               // (d)
  default:  x3_src1_nxt = r1_lo_no_byp 
                        ? x2_src1_r                                     // (a)
                        : r1_wa_byp_data                                // (b)
                        ;
  endcase

  //==========================================================================
  //
  x2_next_src1    = x2_retain ? r1_wa_byp_data : x2_src1_nxt;
  
  //==========================================================================
  //
  x3_target_nxt   = x2_target_r
                  ;

end // block: x2_bypass_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                 sel_src0;
reg                 sel_src1;

always @*
begin: x2_result_PROC

  x2_is_mem_op    = x2_load_r
                  | x2_store_r;

  x2_is_branch    = x2_loop_op_r
                  | x2_bcc_r
                  | x2_jump_r
                  | x2_brcc_bbit_r
                  | x2_rtie_op_r
                  | x2_btab_op_r
                  ;
                  
  //==========================================================================
  //
  sel_src0        = (~x2_done_r)
                  & (   (x2_min_op_r &  x2_lt_flag_r)
                      | (x2_max_op_r & (~x2_lt_flag_r))
                    )
                  ;

  //==========================================================================
  //
  sel_src1        = (~x2_done_r)
                  & (   (x2_min_op_r & (~x2_lt_flag_r))
                      | (x2_max_op_r &  x2_lt_flag_r)
                      | (x2_abs_op_r &  x2_res_r[`npuarc_DATA_MSB])
                    )
                  ;

  //==========================================================================
  // x3_res_nxt is the result value to be passed from X2 to X3.
  //
  x3_res_nxt      = (sel_src0 == 1'b0)
                  ? (   (sel_src1 == 1'b0)
                      ? x2_res_r
                      : x2_src1_r
                    )
                  : x2_src0_r
                  ;

  //==========================================================================
  // x2_byp_data0 is the forwarding result from the X2 stage, going back
  // to X1 and SA.
  //
  x2_byp_data0    = x3_res_nxt;
                  

end // block: x2_result_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: x2_ctrl_PROC

  //==========================================================================
  // x2_valid_nxt:  1 => X2 stage receives a valid instruction
  //  This is asserted when the X1 stage asserts x1_pass, to indicate that
  //  an instruction is available and is not going to be squashed.
  //
  x2_valid_nxt    = x1_pass;

  //==========================================================================
  // x2_code_cg0 enables the update of x2_code_r
  //
  // x2_code_cg0 is asserted when:
  //
  //  (a). the X2 stage is enabled to receive new input, and
  //  (b). either x2_valid_r or x2_valid_nxt
  //
  // Condition (b) ensures that the X2 ucode vector is updated whenever a
  // new instruction arrives or an exising instruction leaves. It does not
  // clock the ucode vector when it is already empty and nothing is arriving.
  //
  x2_code_cg0     = x2_enable & (x2_valid_r | x2_valid_nxt);

  //==========================================================================
  // x2_src<n>_cg0 enables the update of x2_src<n>_r. These signals have
  // functional significance, and are not solely for saving dynamic power.
  //
  // x2_src<n>_cg0 is asserted when:
  //
  //  (a). the X2 stage is enabled to receive new input, and the X1 stage
  //       indicates there is a relevant value on x2_src<n>_nxt, or
  // 
  //  (b). the X2-stage instruction is retained, and the WA-stage has the
  //       bypass value required by that stalled X2 instruction, and forwarding
  //       is not disabled by the respective src<n>_no_fwd signal.
  //       This specific condition is indicated by x2_grab_src<n>.
  //
  x2_grab_src0    = (   x2_retain
                      & r0_lo_wa_byp
                      & (!src0_no_fwd)      // do not update if fwd disabled
                    )
                 ;
                  
  x2_grab_src1    = (   x2_retain
                      & r1_lo_wa_byp
                      & (!src1_no_fwd)      // do not update if fwd disabled
                    )
                  ;
                  
  x2_src0_cg0     = (x2_enable & x1_src0_pass)          // (a)
                  | x2_grab_src0                        // (b)
                  ;
  
  x2_src1_cg0     = (x2_enable & x1_src1_pass)          // (a)
                  | x2_grab_src1                        // (b)
                  ;

  //==========================================================================
  // x2_res_cg0 enables the update of x2_res_r
  //
  x2_res_cg0      = x2_enable & x1_res_pass;

  //==========================================================================
  // x2_target_cg0 enables the update of x2_target_r
  //
  x2_target_cg0 = x2_enable; 

  //==========================================================================
  // x2_mem_addr_cg0 enables the update of x2_mem_addr_r, and is asserted
  // by X2 whenever it passes forward a memory-accessing instruction.
  //
  x2_mem_addr_cg0 = x2_enable & x1_addr_pass;

  //==========================================================================
  // x2_res_pass is asserted when X2 has a result value to pass on to X3.
  // This will be the case if the current X2 instruction was evaluated at
  // X1, and this is indicated by x2_done_r.
  //
  x2_res_pass   = (   x2_pass
                    & (   x2_done_r     // was evaluated at X1 already
                        | x2_link_r     // link value always available
                        | x2_dslot_r    // b.d, j.d value always available
                        | x2_slow_op_r  // 2-cycle insn always available in X2
                       )
                  )
                | db_active
                ;

  //==========================================================================
  // x2_addr_pass is asserted whenever a memory operation is passed from
  // this stage to X3.
  //
  x2_addr_pass    = x2_pass & (x2_is_mem_op | x2_is_branch);

  //==========================================================================
  // x2_src0_pass is asserted when passing the src0 operand to X2
  //
  x2_src0_pass  = x2_pass;

  //==========================================================================
  // x2_src1_pass is asserted when passing the src1 operand to X2
  //
  x2_src1_pass  = x2_pass;

  //==========================================================================
  // X2 provides the re-encoded memory operand size field <zz> from the
  // current instruction, for use by the DMP. (00-b, 01-h, 10-w, 11-dw)
  //
  // Logically this is equivalent to:
  //
  //   x2_size_r     = { ((~x2_half_size_r) & (~x2_byte_size_r)),
  //                     (x2_half_size_r | x2_double_size_r)
  //                   };
  //
  casez ({   x2_half_size_r
           , x2_byte_size_r
           , x2_double_size_r
         })
    3'b1??:  x2_size_r = 2'b01; // 16-bit operation
    3'b01?:  x2_size_r = 2'b00; //  8-bit operation
    3'b001:  x2_size_r = 2'b11; // 64-bit operation
    3'b000:  x2_size_r = 2'b10; // 32-bit operation
    default: x2_size_r = 2'b10; // 32-bit operation in the default
  endcase

end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: x2_ucode_PROC

  //==========================================================================
  //
  ucode_out       = x2_code_r[`npuarc_X3_CODE_WIDTH-1:0];

  //==========================================================================
  // If there is an error branch, then set the outgoing ucode signal for an
  // invalid instruction to 0. This is to avoid triggering an invalid 
  // instruction exception for an instruction that is going to be discarded
  // in CA. The same action is taken for the illegal_operand signal.
  //
  if (x2_error_branch_r == 1'b1)
  begin
    ucode_out[`npuarc_INVALID_INSTR_RANGE]   = 1'b0;
    ucode_out[`npuarc_ILLEGAL_OPERAND_RANGE] = 1'b0;
  end
  
  //==========================================================================
  //
  if ((x2_pass == 1'b0) || (x2_fragged_r == 1'b1))
  begin
`include "npuarc_ucode_kill_x3.v"
  end

end // block: x2_ucode_PROC
//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x2_zncv_reg_PROC
  if (rst_a == 1'b1)
  begin
    x2_zncv_r         <= 4'h0;
  end
  else
  begin
    x2_zncv_r         <= x2_zncv_nxt;
  end
end

// leda NTL_RST03 off
// LMD: A flipflop without reset
// LJ:  pipeline data registers not requiring reset
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  pipeline data registers not requiring reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin: x2_src0_regs_PROC
  if (x2_src0_cg0 == 1'b1)
    x2_src0_r     <= x2_next_src0;
end

always @(posedge clk)
begin: x2_src1_regs_PROC
  if (x2_src1_cg0 == 1'b1)
    x2_src1_r     <= x2_next_src1;
end

always @(posedge clk)
begin: x2_res_regs_PROC
  if (x2_res_cg0 == 1'b1)
  begin
    x2_res_r      <= x1_byp_data0;
    x2_lt_flag_r  <= x2_lt_flag_nxt;
  end
end
// leda NTL_RST03 on
// leda S_1C_R on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01

always @(posedge clk or posedge rst_a)
begin: x2_mem_addr_PROC
  if (rst_a == 1'b1)
    x2_mem_addr_r <= `npuarc_ADDR_SIZE'd0;
  else if (x2_mem_addr_cg0 == 1'b1)
    x2_mem_addr_r <= x1_mem_addr0;
end

always @(posedge clk or posedge rst_a)
begin: x2_target_PROC
  if (rst_a == 1'b1)
    x2_target_r   <= `npuarc_PC_BITS'd0;
  else if (x2_target_cg0 == 1'b1)
    x2_target_r   <= x2_target_nxt;
end


always @(posedge clk or posedge rst_a)
begin: x2_ctrl_regs_PROC
  if (rst_a == 1'b1)
  begin
    x2_code_r     <= `npuarc_X2_CODE_WIDTH'd0;
  end
  else if (x2_code_cg0 == 1'b1)
  begin
    x2_code_r     <= x2_code_nxt;
  end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output Assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign x3_zncv_nxt       = x2_zncv_r;
assign x3_code_nxt       = ucode_out;
assign x2_zncv_wen_r     = {x2_z_wen_r,x2_n_wen_r,x2_c_wen_r,x2_v_wen_r};
assign x2_wevt_op        = x2_sleep_op_r & x2_half_size_r & (~x2_byte_size_r);
assign x2_aux_addr_r     = x2_src1_r;

endmodule // alb_exec2
