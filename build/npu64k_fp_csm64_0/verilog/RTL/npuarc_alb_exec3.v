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

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Include definitions for the microcode constants, including both ARC
// base-case and any User extension instructions which may be defined.
//
`include "npuarc_ucode_const.v"

// Set simulation timescale
//
//`include "const.def"

module npuarc_alb_exec3 (

  ////////// General input signals /////////////////////////////////////////
  //
  input                           clk,                // Processor clock
  input                           rst_a,              // Asynchronous reset
  input                           db_active,          //
  ////////// Inputs from Exec2 stage /////////////////////////////////////////
  //
  input      [`npuarc_DATA_RANGE]        x3_src0_nxt,        //
  input      [`npuarc_DATA_RANGE]        x3_src1_nxt,        //
  input      [`npuarc_DATA_RANGE]        x3_res_nxt,         //
  input      [`npuarc_ADDR_RANGE]        x2_mem_addr_r,      //
  input                           x2_src0_pass,       //
  input                           x2_src1_pass,       //
  input                           x2_res_pass,        //
  input                           x2_addr_pass,       //
  input                           dc2_addr_pass,      // 
  input      [`npuarc_ADDR_RANGE]        dc2_aux_addr,       //
  input      [`npuarc_X3_CODE_WIDTH-1:0] x3_code_nxt,        //
  input      [`npuarc_PC_RANGE]          x3_target_nxt,      //
  input      [`npuarc_ZNCV_RANGE]        x3_zncv_nxt,        //

  ////////// Inputs from Dependency Pipeline /////////////////////////////////
  //
  input                           x3_done_r,          //
  input                           x3_read_r0_r,       //
  input                           x3_read_r1_r,       //
  input                           x3_enable,          //
  input                           x3_retain,          //
  input                           x2_pass,            //
  input                           x3_pass,            //

  ////////// Inputs from Prediction Pipeline /////////////////////////////////
  //
  input                           x3_late_pred_r,     //

  ////////// output to eia dependency logic //////////////////////////////////
  //
  output                          x3_dest_cr_is_ext_r,  // to eia dep logic

  ////////// Forwarding/Bypass Interface /////////////////////////////////////
  //
  input                           fwd_x3_r0_ca_w0_lo, //
  input                           fwd_x3_r0_ca_w1_lo, //
  input                           fwd_x3_r0_wa_w0_lo, //
  input                           fwd_x3_r0_wa_w1_lo, //
  //
  input                           fwd_x3_r1_ca_w0_lo, //
  input                           fwd_x3_r1_ca_w1_lo, //
  input                           fwd_x3_r1_wa_w0_lo, //
  input                           fwd_x3_r1_wa_w1_lo, //
  input                           fwd_x3_r0_ca_w0_hi, //
  input                           fwd_x3_r0_wa_w0_hi, //
  //
  input                           fwd_x3_r1_ca_w0_hi, //
  input                           fwd_x3_r1_wa_w0_hi, //
  input                           fwd_x3_r0_wa_w1_hi, //
  input                           fwd_x3_r1_wa_w1_hi, //
  input                           fwd_x3_r0_ca_w1_hi, //
  input                           fwd_x3_r1_ca_w1_hi, //
  input                           fwd_x3_r1h_ca_w0_lo,
  input                           fwd_x3_r1h_ca_w1_lo,
  input                           fwd_x3_r1h_wa_w0_lo,
  input                           fwd_x3_r1h_wa_w1_lo,
  input                           fwd_x3_r1h_ca_w0_hi,
  input                           fwd_x3_r1h_wa_w0_hi,
  input                           fwd_x3_r1h_ca_w1_hi,
  input                           fwd_x3_r1h_wa_w1_hi,
  //
  input      [`npuarc_DATA_RANGE]        ca_byp_data0_lo,    //
  input      [`npuarc_DATA_RANGE]        ca_byp_data1_lo,    //
  input      [`npuarc_DATA_RANGE]        wa_rf_wdata0_lo_r,  //
  input      [`npuarc_DATA_RANGE]        wa_rf_wdata1_lo_r,  //
  //
  input      [`npuarc_DATA_RANGE]        ca_byp_data0_hi,    //
  input      [`npuarc_DATA_RANGE]        wa_rf_wdata0_hi_r,  //
  //
  input      [`npuarc_DATA_RANGE]        ca_byp_data1_hi,    //
  input      [`npuarc_DATA_RANGE]        wa_rf_wdata1_hi_r,  //

  ////////// Pipeline Control output /////////////////////////////////////////
  //
  output   [`npuarc_Q_FIELD_RANGE]       x3_q_field_r,       //
  output                          x3_load_r,          //
  output                          x3_store_r,         //
  output                          x3_pref_r,          //
  output reg [1:0]                x3_size_r,          //
  output                          x3_sex_r,           //
  output                          x3_cache_byp_r,     //
  output                          x3_flag_op_r,       //
  output                          x3_signed_op_r,     //
  output                          x3_sync_op_r,       //
  output                          x3_ei_op_r,         //
  output                          x3_lr_op_r,         //
  output                          x3_sr_op_r,         //
  output                          x3_div_op_r,        //
  output                          x3_rtie_op_r,       //
  output                          x3_brk_op_r,        //
  output                          x3_trap_op_r,       //
  output                          x3_locked_r,        //
  output                          x3_dmb_op_r,        // DMB insn at X3
  output     [2:0]                x3_dmb_type_r,      // DMB u3 operand at X3
  output                          x3_iprot_viol_r,    // iprot viol at X3


  ///////////////// Outputs to the DMP //////////////////////////////////////////
  //
  output                          x3_pref,            // PREFETCH into L1
  output                          x3_pref_l2,         // PREFETCH into L2
  output                          x3_prefw,           // PREFETCHW
  output                          x3_pre_alloc,       // PREALLOC

  ////////// Outputs to the ZOL pipeline /////////////////////////////////////
  //
  output                          x3_wa0_lpc_r,       //
  output                          x3_loop_op_r,       //
  output                          x3_predicate_r,     // LPcc predicate at X3

  ////////// Forwarding to Upstream stages ///////////////////////////////////
  //
  output reg [`npuarc_DATA_RANGE]        x3_byp_data0,       //

  output     [`npuarc_RGF_ADDR_RANGE]    x3_rf_ra0_r,        // reg-read addr 0 at X3
  output     [`npuarc_RGF_ADDR_RANGE]    x3_rf_ra1_r,        // reg-read addr 1 at X3
  output     [`npuarc_RGF_ADDR_RANGE]    x3_rf_wa0_r,        //
  output                          x3_rf_wenb0_r,      //
  output                          x3_rf_wenb0_64_r,   //
  output                          x3_cc_byp_64_haz_r, // X3 insn cannot bypass r0h
  output     [`npuarc_RGF_ADDR_RANGE]    x3_rf_wa1_r,        //
  output                          x3_rf_wenb1_r,      //
  output                          x3_rf_wenb1_64_r,   //
  output                          x3_rf_renb0_64_r,  //
  output                          x3_rf_renb1_64_r,  //
  output                          x3_acc_wenb_r,      //

  ////////// Interface to the multiplier pipeline ////////////////////////////
  //
  output                          x3_mpy_op_r,        // mpy op in X3
  output                          x3_half_size_r,     // scalar opd is 16 bits
  output                          x3_acc_op_r,        // accumulate operation
  output                          x3_dual_op_r,       // dual SIMD operation
  output                          x3_vector_op_r,     // independent channels
  output                          x3_macu_r,          // MACU-type op at X3
  output                          x3_quad_op_r,       // quad SIMD operation
  input  [`npuarc_DATA_RANGE]            mp3_s_lo,           // mp3 sum lsb 32 bits
  input  [`npuarc_DATA_RANGE]            mp3_c_lo,           // mp3 carry lsb 32 bits

  ////////// Outputs to Auxiliary Registers //////////////////////////////////
  //
  output reg [`npuarc_DATA_RANGE]        x3_src0_r,          // carries PC to aux_regs

  ////////// Outputs to Dependency Pipeline //////////////////////////////////
  //
  output reg                      x3_valid_nxt,       //
  output     [`npuarc_ZNCV_RANGE]        x3_zncv_wen_r,      //
  output                          x3_wevt_op,         //

  ////////// Outputs to the Commit stage /////////////////////////////////////
  //
  output reg                      ca_flag_wr_nxt,     //
  output reg [`npuarc_DATA_RANGE]        ca_src0_nxt,        //
  output reg [`npuarc_DATA_RANGE]        ca_src1_nxt,        //
  output reg [`npuarc_DATA_RANGE]        ca_res_nxt,         //
  output reg [`npuarc_PC_RANGE]          ca_target_nxt,      //
  output reg [`npuarc_CA_P0_RANGE]       ca_p0_nxt,          //
  output reg [`npuarc_CA_P1_RANGE]       ca_p1_nxt,          //
  output reg [`npuarc_CA_P2_RANGE]       ca_p2_nxt,          //
  output reg [`npuarc_CA_P3_RANGE]       ca_p3_nxt,          //
  output reg                      ca_cin_nxt,         //
  output reg [`npuarc_ADDR_RANGE]        x3_mem_addr_r,      //
  output                          x3_uop_inst_r,      // Insn. at X3 is uop.
  output reg                      x3_src0_pass,       //
  output reg                      x3_src1_pass,       //
  output reg                      x3_res_pass,        //
  output reg                      x3_target_pass,     //
  output reg                      x3_addr_pass,       //
  output reg                      x3_add_op_pass,     //
  output reg                      x3_mask_src_pass,   //
  output reg                      x3_alu_code_pass,   //
  output     [`npuarc_PC_INC_RANGE]      ca_pc_inc_nxt,      // Next PC increment
  output     [`npuarc_ZNCV_RANGE]        ca_zncv_nxt,        //
  output     [`npuarc_CA_CODE_WIDTH-1:0] ca_code_nxt         // ucode from X3 to CA
);

// @x3_bypass_PROC
//
reg [`npuarc_DATA_RANGE]             x3_byp_src0;
reg [`npuarc_DATA_RANGE]             x3_byp_src1;

// @x3_ctrl_PROC
//
reg                           x3_is_mem_op;
reg                           x3_is_branch;
reg [2:0]                     pc_increment_seq;
reg [`npuarc_PC_INC_RANGE]           pc_increment;
reg                           x3_mem_addr_cg0;
reg [`npuarc_ADDR_RANGE]             x3_mem_addr_nxt;
reg                           x3_src0_cg0;
reg                           x3_src1_cg0;
reg                           x3_grab_src0;
reg                           x3_grab_src1;
reg                           x3_res_cg0;

// @x3_ucode_PROC
//
reg [`npuarc_CA_CODE_WIDTH-1:0]      ucode_out;

// @x3_reg_PROC
//
reg [`npuarc_DATA_RANGE]             x3_src1_r;
reg [`npuarc_DATA_RANGE]             x3_res_r;
reg [`npuarc_PC_RANGE]               x3_target_r;
reg [`npuarc_ZNCV_RANGE]             x3_zncv_r;

// @x3_ctrl_regs_PROC
//
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [`npuarc_X3_CODE_WIDTH-1:0]      x3_code_r;
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

assign x3_rf_wa0_r  = x3_code_r[`npuarc_RF_WA0_RANGE];  // generated code
assign x3_rf_wenb0_r  = x3_code_r[`npuarc_RF_WENB0_RANGE];  // generated code
assign x3_rf_wenb0_64_r  = x3_code_r[`npuarc_RF_WENB0_64_RANGE];  // generated code
assign x3_cc_byp_64_haz_r  = x3_code_r[`npuarc_CC_BYP_64_HAZ_RANGE];  // generated code
wire   x3_has_limm_r;  // generated code
assign x3_has_limm_r  = x3_code_r[`npuarc_HAS_LIMM_RANGE];  // generated code
wire   x3_is_16bit_r;  // generated code
assign x3_is_16bit_r  = x3_code_r[`npuarc_IS_16BIT_RANGE];  // generated code
assign x3_sr_op_r   = x3_code_r[`npuarc_SR_OP_RANGE];  // generated code
assign x3_loop_op_r  = x3_code_r[`npuarc_LOOP_OP_RANGE];  // generated code
assign x3_locked_r  = x3_code_r[`npuarc_LOCKED_RANGE];  // generated code
assign x3_wa0_lpc_r  = x3_code_r[`npuarc_WA0_LPC_RANGE];  // generated code
wire   x3_dslot_r;  // generated code
assign x3_dslot_r  = x3_code_r[`npuarc_DSLOT_RANGE];  // generated code
wire   x3_sleep_op_r;  // generated code
assign x3_sleep_op_r  = x3_code_r[`npuarc_SLEEP_OP_RANGE];  // generated code
assign x3_acc_wenb_r  = x3_code_r[`npuarc_ACC_WENB_RANGE];  // generated code
wire   x3_writes_acc_r;  // generated code
assign x3_writes_acc_r  = x3_code_r[`npuarc_WRITES_ACC_RANGE];  // generated code
assign x3_lr_op_r   = x3_code_r[`npuarc_LR_OP_RANGE];  // generated code
wire   x3_jump_r;  // generated code
assign x3_jump_r  = x3_code_r[`npuarc_JUMP_RANGE];  // generated code
assign x3_load_r    = x3_code_r[`npuarc_LOAD_RANGE];  // generated code
assign x3_pref_r    = x3_code_r[`npuarc_PREF_RANGE];  // generated code
assign x3_store_r   = x3_code_r[`npuarc_STORE_RANGE];  // generated code
wire   x3_uop_prol_r;  // generated code
assign x3_uop_prol_r  = x3_code_r[`npuarc_UOP_PROL_RANGE];  // generated code
assign x3_rf_wa1_r  = x3_code_r[`npuarc_RF_WA1_RANGE];  // generated code
assign x3_rf_wenb1_r  = x3_code_r[`npuarc_RF_WENB1_RANGE];  // generated code
assign x3_rf_wenb1_64_r  = x3_code_r[`npuarc_RF_WENB1_64_RANGE];  // generated code
assign x3_signed_op_r  = x3_code_r[`npuarc_SIGNED_OP_RANGE];  // generated code
wire   x3_double_size_r;  // generated code
assign x3_double_size_r  = x3_code_r[`npuarc_DOUBLE_SIZE_RANGE];  // generated code
assign x3_half_size_r  = x3_code_r[`npuarc_HALF_SIZE_RANGE];  // generated code
wire   x3_byte_size_r;  // generated code
assign x3_byte_size_r  = x3_code_r[`npuarc_BYTE_SIZE_RANGE];  // generated code
assign x3_rtie_op_r  = x3_code_r[`npuarc_RTIE_OP_RANGE];  // generated code
wire   x3_enter_op_r;  // generated code
assign x3_enter_op_r  = x3_code_r[`npuarc_ENTER_OP_RANGE];  // generated code
wire   x3_leave_op_r;  // generated code
assign x3_leave_op_r  = x3_code_r[`npuarc_LEAVE_OP_RANGE];  // generated code
assign x3_trap_op_r  = x3_code_r[`npuarc_TRAP_OP_RANGE];  // generated code
assign x3_sync_op_r  = x3_code_r[`npuarc_SYNC_OP_RANGE];  // generated code
assign x3_brk_op_r  = x3_code_r[`npuarc_BRK_OP_RANGE];  // generated code
wire   x3_invalid_instr_r;  // generated code
assign x3_invalid_instr_r  = x3_code_r[`npuarc_INVALID_INSTR_RANGE];  // generated code
wire   x3_rgf_link_r;  // generated code
assign x3_rgf_link_r  = x3_code_r[`npuarc_RGF_LINK_RANGE];  // generated code
wire   x3_prod_sign_r;  // generated code
assign x3_prod_sign_r  = x3_code_r[`npuarc_PROD_SIGN_RANGE];  // generated code
assign x3_macu_r    = x3_code_r[`npuarc_MACU_RANGE];  // generated code
assign x3_quad_op_r  = x3_code_r[`npuarc_QUAD_OP_RANGE];  // generated code
assign x3_acc_op_r  = x3_code_r[`npuarc_ACC_OP_RANGE];  // generated code
assign x3_vector_op_r  = x3_code_r[`npuarc_VECTOR_OP_RANGE];  // generated code
assign x3_dual_op_r  = x3_code_r[`npuarc_DUAL_OP_RANGE];  // generated code
assign x3_mpy_op_r  = x3_code_r[`npuarc_MPY_OP_RANGE];  // generated code
wire   x3_z_wen_r;  // generated code
assign x3_z_wen_r  = x3_code_r[`npuarc_Z_WEN_RANGE];  // generated code
wire   x3_n_wen_r;  // generated code
assign x3_n_wen_r  = x3_code_r[`npuarc_N_WEN_RANGE];  // generated code
wire   x3_c_wen_r;  // generated code
assign x3_c_wen_r  = x3_code_r[`npuarc_C_WEN_RANGE];  // generated code
wire   x3_v_wen_r;  // generated code
assign x3_v_wen_r  = x3_code_r[`npuarc_V_WEN_RANGE];  // generated code
wire   x3_kernel_op_r;  // generated code
assign x3_kernel_op_r  = x3_code_r[`npuarc_KERNEL_OP_RANGE];  // generated code
assign x3_flag_op_r  = x3_code_r[`npuarc_FLAG_OP_RANGE];  // generated code
wire   x3_bcc_r;  // generated code
assign x3_bcc_r  = x3_code_r[`npuarc_BCC_RANGE];  // generated code
wire   x3_link_r;  // generated code
assign x3_link_r  = x3_code_r[`npuarc_LINK_RANGE];  // generated code
wire   x3_brcc_bbit_r;  // generated code
assign x3_brcc_bbit_r  = x3_code_r[`npuarc_BRCC_BBIT_RANGE];  // generated code
assign x3_cache_byp_r  = x3_code_r[`npuarc_CACHE_BYP_RANGE];  // generated code
wire   x3_slow_op_r;  // generated code
assign x3_slow_op_r  = x3_code_r[`npuarc_SLOW_OP_RANGE];  // generated code
wire   x3_fast_op_r;  // generated code
assign x3_fast_op_r  = x3_code_r[`npuarc_FAST_OP_RANGE];  // generated code
assign x3_div_op_r  = x3_code_r[`npuarc_DIV_OP_RANGE];  // generated code
wire   x3_btab_op_r;  // generated code
assign x3_btab_op_r  = x3_code_r[`npuarc_BTAB_OP_RANGE];  // generated code
assign x3_ei_op_r   = x3_code_r[`npuarc_EI_OP_RANGE];  // generated code
wire   x3_in_eslot_r;  // generated code
assign x3_in_eslot_r  = x3_code_r[`npuarc_IN_ESLOT_RANGE];  // generated code
wire   x3_rel_branch_r;  // generated code
assign x3_rel_branch_r  = x3_code_r[`npuarc_REL_BRANCH_RANGE];  // generated code
wire   x3_illegal_operand_r;  // generated code
assign x3_illegal_operand_r  = x3_code_r[`npuarc_ILLEGAL_OPERAND_RANGE];  // generated code
wire   x3_swap_op_r;  // generated code
assign x3_swap_op_r  = x3_code_r[`npuarc_SWAP_OP_RANGE];  // generated code
wire   x3_setcc_op_r;  // generated code
assign x3_setcc_op_r  = x3_code_r[`npuarc_SETCC_OP_RANGE];  // generated code
wire [2:0]  x3_cc_field_r;  // generated code
assign x3_cc_field_r  = x3_code_r[`npuarc_CC_FIELD_RANGE];  // generated code
assign x3_q_field_r  = x3_code_r[`npuarc_Q_FIELD_RANGE];  // generated code
assign x3_dest_cr_is_ext_r  = x3_code_r[`npuarc_DEST_CR_IS_EXT_RANGE];  // generated code
wire   x3_add_op_r;  // generated code
assign x3_add_op_r  = x3_code_r[`npuarc_ADD_OP_RANGE];  // generated code
wire   x3_and_op_r;  // generated code
assign x3_and_op_r  = x3_code_r[`npuarc_AND_OP_RANGE];  // generated code
wire   x3_or_op_r;  // generated code
assign x3_or_op_r  = x3_code_r[`npuarc_OR_OP_RANGE];  // generated code
wire   x3_xor_op_r;  // generated code
assign x3_xor_op_r  = x3_code_r[`npuarc_XOR_OP_RANGE];  // generated code
wire   x3_mov_op_r;  // generated code
assign x3_mov_op_r  = x3_code_r[`npuarc_MOV_OP_RANGE];  // generated code
assign x3_with_carry_r  = x3_code_r[`npuarc_WITH_CARRY_RANGE];  // generated code
wire   x3_simple_shift_op_r;  // generated code
assign x3_simple_shift_op_r  = x3_code_r[`npuarc_SIMPLE_SHIFT_OP_RANGE];  // generated code
wire   x3_left_shift_r;  // generated code
assign x3_left_shift_r  = x3_code_r[`npuarc_LEFT_SHIFT_RANGE];  // generated code
wire   x3_rotate_op_r;  // generated code
assign x3_rotate_op_r  = x3_code_r[`npuarc_ROTATE_OP_RANGE];  // generated code
wire   x3_inv_src1_r;  // generated code
assign x3_inv_src1_r  = x3_code_r[`npuarc_INV_SRC1_RANGE];  // generated code
wire   x3_inv_src2_r;  // generated code
assign x3_inv_src2_r  = x3_code_r[`npuarc_INV_SRC2_RANGE];  // generated code
wire   x3_bit_op_r;  // generated code
assign x3_bit_op_r  = x3_code_r[`npuarc_BIT_OP_RANGE];  // generated code
wire   x3_mask_op_r;  // generated code
assign x3_mask_op_r  = x3_code_r[`npuarc_MASK_OP_RANGE];  // generated code
wire   x3_src2_mask_sel_r;  // generated code
assign x3_src2_mask_sel_r  = x3_code_r[`npuarc_SRC2_MASK_SEL_RANGE];  // generated code
wire   x3_uop_commit_r;  // generated code
assign x3_uop_commit_r  = x3_code_r[`npuarc_UOP_COMMIT_RANGE];  // generated code
wire   x3_uop_epil_r;  // generated code
assign x3_uop_epil_r  = x3_code_r[`npuarc_UOP_EPIL_RANGE];  // generated code
wire   x3_uop_excpn_r;  // generated code
assign x3_uop_excpn_r  = x3_code_r[`npuarc_UOP_EXCPN_RANGE];  // generated code
assign x3_predicate_r  = x3_code_r[`npuarc_PREDICATE_RANGE];  // generated code
wire   x3_rf_renb0_r;  // generated code
assign x3_rf_renb0_r  = x3_code_r[`npuarc_RF_RENB0_RANGE];  // generated code
wire   x3_rf_renb1_r;  // generated code
assign x3_rf_renb1_r  = x3_code_r[`npuarc_RF_RENB1_RANGE];  // generated code
assign x3_rf_renb0_64_r  = x3_code_r[`npuarc_RF_RENB0_64_RANGE];  // generated code
assign x3_rf_renb1_64_r  = x3_code_r[`npuarc_RF_RENB1_64_RANGE];  // generated code
assign x3_rf_ra0_r  = x3_code_r[`npuarc_RF_RA0_RANGE];  // generated code
assign x3_rf_ra1_r  = x3_code_r[`npuarc_RF_RA1_RANGE];  // generated code
wire   x3_jli_src0_r;  // generated code
assign x3_jli_src0_r  = x3_code_r[`npuarc_JLI_SRC0_RANGE];  // generated code
assign x3_uop_inst_r  = x3_code_r[`npuarc_UOP_INST_RANGE];  // generated code
wire   x3_vec_shimm_r;  // generated code
assign x3_vec_shimm_r  = x3_code_r[`npuarc_VEC_SHIMM_RANGE];  // generated code
assign x3_iprot_viol_r  = x3_code_r[`npuarc_IPROT_VIOL_RANGE];  // generated code
assign x3_dmb_op_r  = x3_code_r[`npuarc_DMB_OP_RANGE];  // generated code
assign x3_dmb_type_r  = x3_code_r[`npuarc_DMB_TYPE_RANGE];  // generated code
wire   x3_force_cin_r;  // generated code
assign x3_force_cin_r  = x3_code_r[`npuarc_FORCE_CIN_RANGE];  // generated code
wire   x3_opd3_sel_r;  // generated code
assign x3_opd3_sel_r  = x3_code_r[`npuarc_OPD3_SEL_RANGE];  // generated code

// leda NTL_CON13A on

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg                           r0_lo_ca_byp;         // src0 gets bypass from CA
reg                           r1_lo_ca_byp;         // src1 gets bypass from CA
reg                           r0_lo_wa_byp;         // src0 gets bypass from WA
reg                           r1_lo_wa_byp;         // src1 gets bypass from WA
reg                           r0_lo_no_byp;         // src0 does not bypass
reg                           r1_lo_no_byp;         // src1 does not bypass
reg [`npuarc_DATA_RANGE]             r0_wa_byp_data;       // WA bypass data for r0
reg [`npuarc_DATA_RANGE]             r1_wa_byp_data;       // WA bypass data for r1
reg [`npuarc_DATA_RANGE]             x3_next_src0;         // next value for x3_src0_r
reg [`npuarc_DATA_RANGE]             x3_next_src1;         // next value for x3_src1_r

reg                           src0_no_fwd;
reg                           src1_no_fwd;
reg                           src0_ca_w0_lo;
reg                           src0_ca_w1_lo;
reg                           src0_wa_w0_lo;
reg                           src0_wa_w1_lo;
reg                           src0_ca_w0_hi;
reg                           src0_wa_w0_hi;
reg                           src0_ca_w1_hi;
reg                           x3_std_op;
reg                           src0_wa_w1_hi;

always @*
begin: x3_bypass_PROC

  //==========================================================================
  // Define the conditions under which each WA-stage bypass result is to be
  // forwarded to the ca_src0_nxt operand, via x3_byp_src0.
  // There are two cases where each bypass result is required by ca_src0_nxt,
  // either (a) when the result is needed by the first source operand of
  // a deferred ALU operation, or (b) when the result is needed by a 64-bit
  // STD operation to provide the upper 32 bits of store data.
  //
  x3_std_op       = x3_store_r & x3_double_size_r;
  
  src0_ca_w0_lo   = x3_store_r ? fwd_x3_r1h_ca_w0_lo : fwd_x3_r0_ca_w0_lo;
  src0_ca_w1_lo   = x3_store_r ? fwd_x3_r1h_ca_w1_lo : fwd_x3_r0_ca_w1_lo;
  src0_wa_w0_lo   = x3_store_r ? fwd_x3_r1h_wa_w0_lo : fwd_x3_r0_wa_w0_lo;
  src0_wa_w1_lo   = x3_store_r ? fwd_x3_r1h_wa_w1_lo : fwd_x3_r0_wa_w1_lo;
  src0_ca_w0_hi   = x3_store_r ? fwd_x3_r1h_ca_w0_hi : fwd_x3_r0_ca_w0_hi;
  src0_wa_w0_hi   = x3_store_r ? fwd_x3_r1h_wa_w0_hi : fwd_x3_r0_wa_w0_hi;
  src0_ca_w1_hi   = x3_store_r ? fwd_x3_r1h_ca_w1_hi : fwd_x3_r0_ca_w1_hi;
  src0_wa_w1_hi   = x3_store_r ? fwd_x3_r1h_wa_w1_hi : fwd_x3_r0_wa_w1_hi;

  //==========================================================================
  // Instructions that do not have a read flag set for reg0 should not 
  // include forwarded results from WA, as they will have already been taken.
  // The exception is for STD instructions that can forward the upper 32 bits
  // of store data via x3_byp_src0.
  //
  src0_no_fwd     = !x3_std_op & (!x3_read_r0_r);

  //==========================================================================
  // Instructions that have a false predicate, and define a 64-bit non-load
  // result, must not have their src1 operand value updated at the X3 stage.
  // This is because it is already resolved at this point, and contains the
  // x1_false_res_hi value for use when forwarding that result at CA and WA.
  // 
  src1_no_fwd     = !x3_read_r1_r
                  | (x3_rf_wenb0_64_r & (!x3_predicate_r))
                  ;
  
  //==========================================================================
  //
  r0_lo_wa_byp    = src0_wa_w0_lo
                  | src0_wa_w1_lo
                  | src0_wa_w0_hi
                  | src0_wa_w1_hi
                  ;

  r0_lo_ca_byp    = src0_ca_w0_lo
                  | src0_ca_w1_lo
                  | src0_ca_w0_hi
                  | src0_ca_w1_hi
                  ;

  //==========================================================================
  //
  r0_lo_no_byp    = ~(r0_lo_wa_byp | r0_lo_ca_byp) | src0_no_fwd;

  //==========================================================================
  //
  r0_wa_byp_data  = ( {`npuarc_DATA_SIZE{src0_wa_w0_lo & (!src0_no_fwd)}} & wa_rf_wdata0_lo_r )
                  | ( {`npuarc_DATA_SIZE{src0_wa_w1_lo & (!src0_no_fwd)}} & wa_rf_wdata1_lo_r )
                  | ( {`npuarc_DATA_SIZE{src0_wa_w0_hi & (!src0_no_fwd)}} & wa_rf_wdata0_hi_r )
                  | ( {`npuarc_DATA_SIZE{src0_wa_w1_hi & (!src0_no_fwd)}} & wa_rf_wdata1_hi_r )
                  ;

  //==========================================================================
  //
  x3_byp_src0     = r0_wa_byp_data
                  | ( {`npuarc_DATA_SIZE{r0_lo_no_byp}}  & x3_src0_r         )
                  | ( {`npuarc_DATA_SIZE{src0_ca_w0_lo & (!src0_no_fwd)}} & ca_byp_data0_lo   )
                  | ( {`npuarc_DATA_SIZE{src0_ca_w1_lo & (!src0_no_fwd)}} & ca_byp_data1_lo   )
                  | ( {`npuarc_DATA_SIZE{src0_ca_w0_hi & (!src0_no_fwd)}} & ca_byp_data0_hi   )
                  | ( {`npuarc_DATA_SIZE{src0_ca_w1_hi & (!src0_no_fwd)}} & ca_byp_data1_hi   )
                  ;

  //==========================================================================
  //
  x3_next_src0    = x3_retain ? r0_wa_byp_data : x3_src0_nxt;
  

  //==========================================================================
  //
  ca_src0_nxt     = (x3_mpy_op_r & x3_predicate_r)
                  ? mp3_s_lo
                  : x3_byp_src0
                  ;

  //==========================================================================
  //
  r1_lo_wa_byp    = fwd_x3_r1_wa_w0_lo
                  | fwd_x3_r1_wa_w1_lo
                  | fwd_x3_r1_wa_w0_hi
                  | fwd_x3_r1_wa_w1_hi
                  ;

  r1_lo_ca_byp    = fwd_x3_r1_ca_w0_lo
                  | fwd_x3_r1_ca_w1_lo
                  | fwd_x3_r1_ca_w0_hi
                  | fwd_x3_r1_ca_w1_hi
                  ;

  //==========================================================================
  //
  r1_lo_no_byp    = ~(r1_lo_wa_byp | r1_lo_ca_byp) | src1_no_fwd;

  //==========================================================================
  //
  r1_wa_byp_data  = (   {`npuarc_DATA_SIZE{fwd_x3_r1_wa_w0_lo & (!src1_no_fwd)}}
                      & wa_rf_wdata0_lo_r )
                  | (   {`npuarc_DATA_SIZE{fwd_x3_r1_wa_w1_lo & (!src1_no_fwd)}}
                      & wa_rf_wdata1_lo_r )
                  | (   {`npuarc_DATA_SIZE{fwd_x3_r1_wa_w0_hi & (!src1_no_fwd)}}
                      & wa_rf_wdata0_hi_r )
                  | (   {`npuarc_DATA_SIZE{fwd_x3_r1_wa_w1_hi & (!src1_no_fwd)}}
                      & wa_rf_wdata1_hi_r )
                  ;

  //==========================================================================
  //
  x3_byp_src1     = r1_wa_byp_data
                  | (   {`npuarc_DATA_SIZE{r1_lo_no_byp                     }}
                      & x3_src1_r                                          )
                  | (   {`npuarc_DATA_SIZE{fwd_x3_r1_ca_w0_lo & (!src1_no_fwd)}}
                      & ca_byp_data0_lo                                    )
                  | (   {`npuarc_DATA_SIZE{fwd_x3_r1_ca_w1_lo & (!src1_no_fwd)}}
                      & ca_byp_data1_lo                                    )
                  | (   {`npuarc_DATA_SIZE{fwd_x3_r1_ca_w0_hi & (!src1_no_fwd)}}
                      & ca_byp_data0_hi                                    )
                  | (   {`npuarc_DATA_SIZE{fwd_x3_r1_ca_w1_hi & (!src1_no_fwd)}}
                      & ca_byp_data1_hi                                    )
                  ;
  //==========================================================================
  //
  x3_next_src1    = x3_retain ? r1_wa_byp_data : x3_src1_nxt;
  

  //==========================================================================
  //
  ca_src1_nxt     = (x3_mpy_op_r & x3_predicate_r)
                  ? mp3_c_lo
                  : x3_byp_src1
                  ;

  //==========================================================================
  // ca_res_nxt is the result value to be passed from X3 to CA.
  //
  ca_res_nxt      = x3_res_r;
                  

  //==========================================================================
  // ca_target_nxt is the branch/jump target to be passed from X3 to CA.
  //
  case ({x3_jump_r, x3_opd3_sel_r})
    2'b11:   ca_target_nxt = ca_src1_nxt[`npuarc_PC_RANGE];
    2'b10:   ca_target_nxt = ca_src0_nxt[`npuarc_PC_RANGE];
    default: ca_target_nxt = x3_target_r;
  endcase
  
 //==========================================================================
  // x3_byp_data0 is the forwarding result from the X3 stage, going back
  // to X2, X1 and SA.
  //
  x3_byp_data0    = ca_res_nxt;
                  

end // block: x3_bypass_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// x3_ctrl_PROC: Combinational process to derive X3 control state.          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: x3_ctrl_PROC
                  
  x3_is_mem_op    = x3_load_r
                  | x3_store_r
                  ;

  x3_is_branch    = x3_loop_op_r
                  | x3_bcc_r
                  | x3_jump_r
                  | x3_brcc_bbit_r
                  | x3_rtie_op_r
                  | x3_btab_op_r
                  ;
                  
  //==========================================================================
  // X3 provides the re-encoded memory operand size field <zz> from the
  // current instruction, for use by the DMP. (00-b, 01-h, 10-w, 11-dw)
  //
  // Logically this is equivalent to:
  //
  //   x3_size_r     = { ((~x3_half_size_r) & (~x3_byte_size_r)),
  //                     (x3_half_size_r | x3_double_size_r)
  //                   };
  //
  casez ({   x3_half_size_r
           , x3_byte_size_r
           , x3_double_size_r
         })
    3'b1??:  x3_size_r = 2'b01; // 16-bit operation
    3'b01?:  x3_size_r = 2'b00; //  8-bit operation
    3'b001:  x3_size_r = 2'b11; // 64-bit operation
    3'b000:  x3_size_r = 2'b10; // 32-bit operation
    default: x3_size_r = 2'b10; // 32-bit operation in the default
  endcase

  //==========================================================================
  // Derive the value of the PC increment as a trivial function of the
  // instruction length.
  //
  case ({x3_is_16bit_r, x3_has_limm_r})
    2'b01:  pc_increment_seq = 3'd4;
    2'b10:  pc_increment_seq = 3'd1;
    2'b11:  pc_increment_seq = 3'd3;
    default:pc_increment_seq = 3'd2;
  endcase

  //==========================================================================
  // It is not possible to determine the PC increment for multi-ops
  // since the the final terminal instruction of the sequence on which
  // the sequence is committed may differ from the size of the
  // initiating instruction (RTIE, ENTER_S/LEAVE_S).
  //
  pc_increment    = x3_uop_commit_r ? 3'd1 : pc_increment_seq;

  //==========================================================================
  // x3_valid_nxt:  1 => X3 stage receives a valid instruction
  //  This is asserted when the X2 stage asserts x2_pass, to indicate that
  //  an instruction is available and is not going to be squashed.
  //
  x3_valid_nxt    = x2_pass;

  //==========================================================================
  // x3_addr_pass is asserted whenever a memory operation is passed from
  // this stage to CA.
  //
  x3_addr_pass    = x3_pass & (x3_is_mem_op | x3_is_branch);

  //==========================================================================
  // x3_res_pass is asserted when X3 has a result value to pass on to CA.
  // This will be the case if the current X3 instruction was evaluated at
  // X1, and this is indicated by x3_done_r.
  //
  x3_res_pass   = (x3_pass & (x3_done_r | x3_link_r | x3_dslot_r))
                | db_active
                ;

  //==========================================================================
  // x3_target_pass is asserted when X3 has a target address to pass on to CA.
  // This will be the case if the current X3 instruction was evaluated at
  // X1, or has since received its input register target value, and this is
  // indicated by x3_done_r.
  //
  x3_target_pass = x3_pass;

  //==========================================================================
  // x3_src0_pass is asserted when operand in x3_src0_r needs to be passed
  // to ca_src0_r in the current cycle. This occurs in one of the following
  // cases, provided x3_pass is also asserted.
  //
  //  (a) the current X3 instruction is not already evaluated in early ALU
  //  (b) the X3 instruction is a STD, so src0 carries store data hi value
  //  (c) X3 instruction is an LR, so src0 carries possible PC_AUX value
  //  (d) X3 instruction is a branch/jump that is not evaluated early.
  //
  x3_src0_pass  = x3_pass
                & (   !x3_done_r
                    |  (x3_store_r & x3_double_size_r)
                    |  x3_lr_op_r
                    |  x3_late_pred_r
                  )
                ;

  //==========================================================================
  // x3_src1_pass is asserted when operand in x3_src1_r needs to be passed
  // to ca_src1_r in the current cycle. This occurs in one of the following
  // cases, provided x3_pass is also asserted.
  //
  //  (a) the current X3 instruction is not already evaluated in early ALU
  //  (b) the X3 instruction is a ST, so src1 carries store data lo value
  //  (c) X3 instruction is an SR or AEX, so src1 carries SR data
  //  (d) X3 instruction is a branch/jump that is not evaluated early.
  //  (e) X3 instruction is a flag operation
  //  (f) X3 instruction is a trap operation
  //  (g) X3 instruction is a sleep operation
  //
  x3_src1_pass  = x3_pass
                & (   !x3_done_r
                    | x3_store_r
                    | x3_sr_op_r
                    | x3_late_pred_r
                    | x3_flag_op_r
                    | x3_trap_op_r
                    | x3_sleep_op_r
                  )
                ;

  //==========================================================================
  // x3_add_op_pass is asserted when the X3 stage passes an instruction to
  // the CA stage, and the instruction requires to use the CA-stage Adder
  // for a late-evaluating ADD/SUB/CMP operation or the completion of a
  // pipelined MPY operation.
  //
  x3_add_op_pass  = x3_pass
                  & (!x3_done_r | x3_late_pred_r)
                  &  (   x3_add_op_r
                       | x3_mpy_op_r
                     )
                  ;

  //==========================================================================
  // x3_alu_code_pass is asserted when the X3 stage passes an instruction to
  // the CA stage, and the instruction requires to use the CA-stage ALU
  // for a late-evaluating ALU operation. This includes all operations that
  // go through the adder (ADD, SUB, CMP, MPY) and all operations that
  // use the logic unit.
  //
  x3_alu_code_pass  = x3_pass
                    & (!x3_done_r | x3_late_pred_r)
                    & (   x3_add_op_r
                        | x3_mov_op_r
                        | x3_or_op_r
                        | x3_and_op_r
                        | x3_xor_op_r
                        | x3_brcc_bbit_r
                        | x3_setcc_op_r
                        | x3_simple_shift_op_r
                        | x3_mpy_op_r
                      )
                    ;

  //==========================================================================
  // x3_mask_src_pass is asserted when the X3 stage passes an instruction to
  // the CA stage, and the instruction involves a mask as the second source
  // operand, and the instruction will be evaluated in the CA-stage ALU.
  //
  x3_mask_src_pass  = x3_pass
                    & (!x3_done_r | x3_late_pred_r)
                    & x3_src2_mask_sel_r
                    ;
                    
  //==========================================================================
  // x3_mem_addr_cg0 enables the update of x3_mem_addr_r, and is asserted
  // by X3 whenever it passes forward a memory-accessing instruction.
  // The x3_mem_addr is also updated on the request of the Data Cache aux
  // for a special tag lookup (cache instruction)
  //

  x3_mem_addr_cg0 =   (x3_enable & x2_addr_pass)
                    | dc2_addr_pass
                    ;
  
  //==========================================================================
  // x3_mem_addr_nxt is either x2_mem_addr_r or the aux address required to
  // perform tag lookup. Both dc2_addr and  dc2_addr_pass are available 
  // very early in the cycle
  //
  x3_mem_addr_nxt = dc2_addr_pass ? dc2_aux_addr : x2_mem_addr_r; 

  //==========================================================================
  // x3_src<n>_cg0 enables the update of x3_src<n>_r. These signals have
  // functional significance, and are not solely for saving dynamic power.
  //
  // x3_src<n>_cg0 is asserted when:
  //
  //  (a). the X3 stage is enabled to receive new input, and the X2 stage
  //       indicates there is a relevant value on x3_src<n>_nxt, or
  // 
  //  (b). the X3-stage instruction is retained, and the WA-stage has the
  //       bypass value required by that stalled X3 instruction.
  //       This specific condition is indicated by x3_grab_src<n>.
  //
  x3_grab_src0    = (   x3_retain
                      & r0_lo_wa_byp
                      & (!src0_no_fwd)      // do not update if fwd disabled
                    )
                  ;
                  
  x3_grab_src1    = (   x3_retain
                      & r1_lo_wa_byp
                      & (!src1_no_fwd)      // do not update if fwd disabled
                    )
                  ;
                  
  x3_src0_cg0     = (x3_enable & x2_src0_pass)          // (a)
                  | x3_grab_src0                        // (b)
                  ;
  
  x3_src1_cg0     = (x3_enable & x2_src1_pass)          // (a)
                  | x3_grab_src1                        // (b)
                  ;

  //==========================================================================
  // x3_res_cg0 enables the update of x3_res_r
  //
  x3_res_cg0      = x3_enable & x2_res_pass;

  //==========================================================================
  // ca_flag_wr is used to determine Auxiliary Stall
  // ca_flag_wr_r pending in CA stalls dependent instructions
  //
  ca_flag_wr_nxt    = (x3_z_wen_r | x3_n_wen_r | x3_c_wen_r | x3_v_wen_r)
                    & x3_pass
                    ;

end // block: x3_ctrl_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Combinational process to define the next value for the adder controls    //
// at the Commit stage.                                                     //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

reg   [7:0]                 x3_alu_opcode;
// leda NTL_CON13A off
// LMD: non driving internal net Range
// leda NTL_CON12A off
// LMD: undriven internal net Range
// LJ:  Not all bits used
reg   [14:0]                ca_ctrl_vec;
// leda NTL_CON12A on
// leda NTL_CON13A on
parameter ADD_OPC       = 8'b0000_0000;
parameter SUB_OPC       = 8'b0000_0011;
parameter RSUB_OPC      = 8'b0000_0101;
// spyglass disable_block W444
// leda B_3204 off
// LMD: '?' in based number constant
// LJ:  base is binary and constant is used in casez item
parameter NOVEC_MPY_OPC = 8'b1???_0???;
// leda B_3204 on
// spyglass enable_block W444
parameter VADD2H_OPC    = 8'b0110_1000;
parameter VSUB2H_OPC    = 8'b0110_1011;
parameter VADDSUB2H_OPC = 8'b0110_1001;
parameter VSUBADD2H_OPC = 8'b0110_1010;
parameter VMPY2HX_OPC   = 8'b1110_1000;
parameter VADD4H_OPC    = 8'b0101_1000;
parameter VSUB4H_OPC    = 8'b0101_1011;
parameter VADDSUB4H_OPC = 8'b0101_1001;
parameter VSUBADD4H_OPC = 8'b0101_1010;
parameter VADD2_OPC     = 8'b0010_1000;
parameter VSUB2_OPC     = 8'b0010_1011;
parameter VADDSUB_OPC   = 8'b0010_1001;
parameter VSUBADD_OPC   = 8'b0010_1010;
  
always @* 
begin: x3_pX_nxt_PROC

  x3_alu_opcode   = { x3_mpy_op_r,
                      x3_half_size_r,
                      x3_dual_op_r,
                      x3_quad_op_r,
                      x3_vector_op_r,
                      x3_inv_src1_r,
                      x3_inv_src2_r,
                      x3_force_cin_r
                    }
                  ;

  casez (x3_alu_opcode)
    // ---------------------------------------------------
    //                                P0   P1   P2  P3 Cin
    // -------- basecase ALU operations ------------------
    ADD_OPC:        ca_ctrl_vec = 15'b0000_0000_001_000_0;
    SUB_OPC:        ca_ctrl_vec = 15'b0000_0011_001_000_1;
    RSUB_OPC:       ca_ctrl_vec = 15'b0011_0000_001_000_1;
    //
    // -------- MPY_OPTION < 8 operations ----------------
    NOVEC_MPY_OPC:  ca_ctrl_vec = 15'b0000_0000_111_000_0;
    VADD2H_OPC:     ca_ctrl_vec = 15'b0000_0000_000_000_0;
    VSUB2H_OPC:     ca_ctrl_vec = 15'b0000_0011_001_001_1;
    VADDSUB2H_OPC:  ca_ctrl_vec = 15'b0000_0010_001_001_0;
    VSUBADD2H_OPC:  ca_ctrl_vec = 15'b0000_0001_000_000_1;
    //
    // -------- MPY_OPTION 8 operations ------------------
    VMPY2HX_OPC:    ca_ctrl_vec = 15'b0000_0000_101_000_0;
    //
    // -------- MPY_OPTION 9 operations ------------------
    VADD4H_OPC:     ca_ctrl_vec = 15'b0000_0000_000_000_0;
    VSUB4H_OPC:     ca_ctrl_vec = 15'b0000_1111_111_111_1;
    VADDSUB4H_OPC:  ca_ctrl_vec = 15'b0000_1010_101_101_0;
    VSUBADD4H_OPC:  ca_ctrl_vec = 15'b0000_0101_010_010_1;
    VADD2_OPC:      ca_ctrl_vec = 15'b0000_0000_101_000_0;
    VSUB2_OPC:      ca_ctrl_vec = 15'b0000_1111_111_010_1;
    VADDSUB_OPC:    ca_ctrl_vec = 15'b0000_1100_111_010_0;
    VSUBADD_OPC:    ca_ctrl_vec = 15'b0000_0011_101_000_1;
    default:        ca_ctrl_vec = 15'b0000_0000_001_000_0;
  endcase

  ca_p0_nxt   = ca_ctrl_vec[14:11];
  ca_p1_nxt   = ca_ctrl_vec[10:7];
  ca_p2_nxt   = ca_ctrl_vec[6:4];
  ca_p3_nxt   = ca_ctrl_vec[3:1];
  ca_cin_nxt  = ca_ctrl_vec[0];

end // block: x3_pX_nxt_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin: x3_ucode_PROC

  //==========================================================================
  //
  ucode_out       = x3_code_r[`npuarc_CA_CODE_WIDTH-1:0];

  //==========================================================================
  // Defeat the outgoing acc_wenb ucode signal if the X3 predicate is false.
  // Note, that all predicated accumulator instructions (e.g. DMACH.GE)
  // have their predicate evaluated at X1, so the X3 predicate is known
  // for certain.
  //
  ucode_out[`npuarc_ACC_WENB_RANGE] = x3_acc_wenb_r & x3_predicate_r;
  
  //==========================================================================
  //
  if (x3_pass == 1'b0)
  begin
`include "npuarc_ucode_kill_ca.v"
  end

end // block: x3_ucode_PROC


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                                                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x3_reg_PROC
  if (rst_a == 1'b1)
  begin
    x3_target_r     <= `npuarc_PC_BITS'd0;
    x3_zncv_r       <= 4'd0;
  end
  else if (x3_enable == 1'b1)
  begin
    x3_target_r     <= x3_target_nxt;
    x3_zncv_r       <= x3_zncv_nxt;
  end
end // block: x3_reg_PROC

always @(posedge clk or posedge rst_a)
begin: x3_src_reg_PROC
  if (rst_a == 1'b1)
  begin
    x3_src0_r       <= `npuarc_DATA_SIZE'd0;
    x3_src1_r       <= `npuarc_DATA_SIZE'd0;
    x3_res_r        <= `npuarc_DATA_SIZE'd0;
  end
  else
  begin
    if (x3_src0_cg0 == 1'b1)
      x3_src0_r     <= x3_next_src0;
      
    if (x3_src1_cg0 == 1'b1)
      x3_src1_r     <= x3_next_src1;
      
    if (x3_res_cg0 == 1'b1)
      x3_res_r      <= x3_res_nxt;
  end
end // block: x3_reg_PROC


always @(posedge clk or posedge rst_a)
begin: x3_mem_addr_PROC
  if (rst_a == 1'b1)
    x3_mem_addr_r <= `npuarc_ADDR_SIZE'd0;
  else if (x3_mem_addr_cg0 == 1'b1)
    x3_mem_addr_r <= x3_mem_addr_nxt;
end // block: x3_mem_addr_PROC


always @(posedge clk or posedge rst_a)
begin: x3_ctrl_regs_PROC
  if (rst_a == 1'b1)
  begin
    x3_code_r       <= `npuarc_X3_CODE_WIDTH'd0;
  end
  else if (x3_enable == 1'b1)
  begin
    x3_code_r       <= x3_code_nxt;
  end
end // block: x3_ctrl_regs_PROC



//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output Assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign ca_zncv_nxt       = x3_zncv_r;
assign ca_code_nxt       = ucode_out;
assign x3_zncv_wen_r     = {x3_z_wen_r,x3_n_wen_r,x3_c_wen_r,x3_v_wen_r};
assign x3_sex_r          = x3_signed_op_r;
assign ca_pc_inc_nxt     = pc_increment;
assign x3_pref      = x3_pref_r & (~x3_sex_r) & (~x3_cache_byp_r);
assign x3_pref_l2   = 1'b0;
assign x3_prefw     = x3_pref_r & (~x3_sex_r) &   x3_cache_byp_r;
assign x3_pre_alloc = x3_pref_r &   x3_sex_r  & (~x3_cache_byp_r);
assign x3_wevt_op   = x3_sleep_op_r & x3_half_size_r & (~x3_byte_size_r);

endmodule // alb_exec3
