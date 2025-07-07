// Library ARCv2HS-3.5.999999999
// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.

// Certain materials incorporated herein are copyright (C) 2010 - 2011,
// The University Court of the University of Edinburgh. All Rights Reserved.

assign ca_rf_wa0_r  = ca_code_r[`npuarc_RF_WA0_RANGE];  // generated code
assign ca_rf_wenb0_r  = ca_code_r[`npuarc_RF_WENB0_RANGE];  // generated code
assign ca_rf_wenb0_64_r  = ca_code_r[`npuarc_RF_WENB0_64_RANGE];  // generated code
assign ca_cc_byp_64_haz_r  = ca_code_r[`npuarc_CC_BYP_64_HAZ_RANGE];  // generated code
assign ca_has_limm_r  = ca_code_r[`npuarc_HAS_LIMM_RANGE];  // generated code
assign ca_is_16bit_r  = ca_code_r[`npuarc_IS_16BIT_RANGE];  // generated code
assign ca_sr_op_r   = ca_code_r[`npuarc_SR_OP_RANGE];  // generated code
assign ca_loop_op_r  = ca_code_r[`npuarc_LOOP_OP_RANGE];  // generated code
assign ca_locked_r  = ca_code_r[`npuarc_LOCKED_RANGE];  // generated code
assign ca_wa0_lpc_r  = ca_code_r[`npuarc_WA0_LPC_RANGE];  // generated code
assign ca_dslot_r   = ca_code_r[`npuarc_DSLOT_RANGE];  // generated code
wire   ca_sleep_op_r;  // generated code
assign ca_sleep_op_r  = ca_code_r[`npuarc_SLEEP_OP_RANGE];  // generated code
assign ca_acc_wenb_r  = ca_code_r[`npuarc_ACC_WENB_RANGE];  // generated code
assign ca_writes_acc_r  = ca_code_r[`npuarc_WRITES_ACC_RANGE];  // generated code
assign ca_lr_op_r   = ca_code_r[`npuarc_LR_OP_RANGE];  // generated code
assign ca_jump_r    = ca_code_r[`npuarc_JUMP_RANGE];  // generated code
assign ca_load_r    = ca_code_r[`npuarc_LOAD_RANGE];  // generated code
wire   ca_pref_r;  // generated code
assign ca_pref_r  = ca_code_r[`npuarc_PREF_RANGE];  // generated code
assign ca_store_r   = ca_code_r[`npuarc_STORE_RANGE];  // generated code
wire   ca_uop_prol_r;  // generated code
assign ca_uop_prol_r  = ca_code_r[`npuarc_UOP_PROL_RANGE];  // generated code
assign ca_rf_wa1_r  = ca_code_r[`npuarc_RF_WA1_RANGE];  // generated code
assign ca_rf_wenb1_r  = ca_code_r[`npuarc_RF_WENB1_RANGE];  // generated code
assign ca_rf_wenb1_64_r  = ca_code_r[`npuarc_RF_WENB1_64_RANGE];  // generated code
wire   ca_signed_op_r;  // generated code
assign ca_signed_op_r  = ca_code_r[`npuarc_SIGNED_OP_RANGE];  // generated code
wire   ca_double_size_r;  // generated code
assign ca_double_size_r  = ca_code_r[`npuarc_DOUBLE_SIZE_RANGE];  // generated code
wire   ca_half_size_r;  // generated code
assign ca_half_size_r  = ca_code_r[`npuarc_HALF_SIZE_RANGE];  // generated code
assign ca_byte_size_r  = ca_code_r[`npuarc_BYTE_SIZE_RANGE];  // generated code
assign ca_rtie_op_r  = ca_code_r[`npuarc_RTIE_OP_RANGE];  // generated code
wire   ca_enter_op_r;  // generated code
assign ca_enter_op_r  = ca_code_r[`npuarc_ENTER_OP_RANGE];  // generated code
assign ca_leave_op_r  = ca_code_r[`npuarc_LEAVE_OP_RANGE];  // generated code
assign ca_trap_op_r  = ca_code_r[`npuarc_TRAP_OP_RANGE];  // generated code
wire   ca_sync_op_r;  // generated code
assign ca_sync_op_r  = ca_code_r[`npuarc_SYNC_OP_RANGE];  // generated code
assign ca_brk_op_r  = ca_code_r[`npuarc_BRK_OP_RANGE];  // generated code
wire   ca_invalid_instr_r;  // generated code
assign ca_invalid_instr_r  = ca_code_r[`npuarc_INVALID_INSTR_RANGE];  // generated code
wire   ca_rgf_link_r;  // generated code
assign ca_rgf_link_r  = ca_code_r[`npuarc_RGF_LINK_RANGE];  // generated code
wire   ca_prod_sign_r;  // generated code
assign ca_prod_sign_r  = ca_code_r[`npuarc_PROD_SIGN_RANGE];  // generated code
assign ca_macu_r    = ca_code_r[`npuarc_MACU_RANGE];  // generated code
wire   ca_quad_op_r;  // generated code
assign ca_quad_op_r  = ca_code_r[`npuarc_QUAD_OP_RANGE];  // generated code
wire   ca_acc_op_r;  // generated code
assign ca_acc_op_r  = ca_code_r[`npuarc_ACC_OP_RANGE];  // generated code
assign ca_vector_op_r  = ca_code_r[`npuarc_VECTOR_OP_RANGE];  // generated code
wire   ca_dual_op_r;  // generated code
assign ca_dual_op_r  = ca_code_r[`npuarc_DUAL_OP_RANGE];  // generated code
assign ca_mpy_op_r  = ca_code_r[`npuarc_MPY_OP_RANGE];  // generated code
wire   ca_z_wen_r;  // generated code
assign ca_z_wen_r  = ca_code_r[`npuarc_Z_WEN_RANGE];  // generated code
wire   ca_n_wen_r;  // generated code
assign ca_n_wen_r  = ca_code_r[`npuarc_N_WEN_RANGE];  // generated code
wire   ca_c_wen_r;  // generated code
assign ca_c_wen_r  = ca_code_r[`npuarc_C_WEN_RANGE];  // generated code
wire   ca_v_wen_r;  // generated code
assign ca_v_wen_r  = ca_code_r[`npuarc_V_WEN_RANGE];  // generated code
wire   ca_kernel_op_r;  // generated code
assign ca_kernel_op_r  = ca_code_r[`npuarc_KERNEL_OP_RANGE];  // generated code
wire   ca_flag_op_r;  // generated code
assign ca_flag_op_r  = ca_code_r[`npuarc_FLAG_OP_RANGE];  // generated code
assign ca_bcc_r     = ca_code_r[`npuarc_BCC_RANGE];  // generated code
wire   ca_link_r;  // generated code
assign ca_link_r  = ca_code_r[`npuarc_LINK_RANGE];  // generated code
assign ca_brcc_bbit_r  = ca_code_r[`npuarc_BRCC_BBIT_RANGE];  // generated code
assign ca_cache_byp_r  = ca_code_r[`npuarc_CACHE_BYP_RANGE];  // generated code
wire   ca_slow_op_r;  // generated code
assign ca_slow_op_r  = ca_code_r[`npuarc_SLOW_OP_RANGE];  // generated code
assign ca_fast_op_r  = ca_code_r[`npuarc_FAST_OP_RANGE];  // generated code
assign ca_div_op_r  = ca_code_r[`npuarc_DIV_OP_RANGE];  // generated code
assign ca_btab_op_r  = ca_code_r[`npuarc_BTAB_OP_RANGE];  // generated code
assign ca_ei_op_r   = ca_code_r[`npuarc_EI_OP_RANGE];  // generated code
assign ca_in_eslot_r  = ca_code_r[`npuarc_IN_ESLOT_RANGE];  // generated code
wire   ca_rel_branch_r;  // generated code
assign ca_rel_branch_r  = ca_code_r[`npuarc_REL_BRANCH_RANGE];  // generated code
wire   ca_illegal_operand_r;  // generated code
assign ca_illegal_operand_r  = ca_code_r[`npuarc_ILLEGAL_OPERAND_RANGE];  // generated code
wire   ca_swap_op_r;  // generated code
assign ca_swap_op_r  = ca_code_r[`npuarc_SWAP_OP_RANGE];  // generated code
wire   ca_setcc_op_r;  // generated code
assign ca_setcc_op_r  = ca_code_r[`npuarc_SETCC_OP_RANGE];  // generated code
wire [2:0]  ca_cc_field_r;  // generated code
assign ca_cc_field_r  = ca_code_r[`npuarc_CC_FIELD_RANGE];  // generated code
assign ca_q_field_r  = ca_code_r[`npuarc_Q_FIELD_RANGE];  // generated code
assign ca_dest_cr_is_ext_r  = ca_code_r[`npuarc_DEST_CR_IS_EXT_RANGE];  // generated code
wire   ca_add_op_r;  // generated code
assign ca_add_op_r  = ca_code_r[`npuarc_ADD_OP_RANGE];  // generated code
wire   ca_and_op_r;  // generated code
assign ca_and_op_r  = ca_code_r[`npuarc_AND_OP_RANGE];  // generated code
wire   ca_or_op_r;  // generated code
assign ca_or_op_r  = ca_code_r[`npuarc_OR_OP_RANGE];  // generated code
wire   ca_xor_op_r;  // generated code
assign ca_xor_op_r  = ca_code_r[`npuarc_XOR_OP_RANGE];  // generated code
wire   ca_mov_op_r;  // generated code
assign ca_mov_op_r  = ca_code_r[`npuarc_MOV_OP_RANGE];  // generated code
assign ca_with_carry_r  = ca_code_r[`npuarc_WITH_CARRY_RANGE];  // generated code
wire   ca_simple_shift_op_r;  // generated code
assign ca_simple_shift_op_r  = ca_code_r[`npuarc_SIMPLE_SHIFT_OP_RANGE];  // generated code
wire   ca_left_shift_r;  // generated code
assign ca_left_shift_r  = ca_code_r[`npuarc_LEFT_SHIFT_RANGE];  // generated code
wire   ca_rotate_op_r;  // generated code
assign ca_rotate_op_r  = ca_code_r[`npuarc_ROTATE_OP_RANGE];  // generated code
wire   ca_inv_src1_r;  // generated code
assign ca_inv_src1_r  = ca_code_r[`npuarc_INV_SRC1_RANGE];  // generated code
wire   ca_inv_src2_r;  // generated code
assign ca_inv_src2_r  = ca_code_r[`npuarc_INV_SRC2_RANGE];  // generated code
wire   ca_bit_op_r;  // generated code
assign ca_bit_op_r  = ca_code_r[`npuarc_BIT_OP_RANGE];  // generated code
wire   ca_mask_op_r;  // generated code
assign ca_mask_op_r  = ca_code_r[`npuarc_MASK_OP_RANGE];  // generated code
wire   ca_src2_mask_sel_r;  // generated code
assign ca_src2_mask_sel_r  = ca_code_r[`npuarc_SRC2_MASK_SEL_RANGE];  // generated code
assign ca_uop_commit_r  = ca_code_r[`npuarc_UOP_COMMIT_RANGE];  // generated code
wire   ca_uop_epil_r;  // generated code
assign ca_uop_epil_r  = ca_code_r[`npuarc_UOP_EPIL_RANGE];  // generated code
wire   ca_uop_excpn_r;  // generated code
assign ca_uop_excpn_r  = ca_code_r[`npuarc_UOP_EXCPN_RANGE];  // generated code
assign ca_predicate_r  = ca_code_r[`npuarc_PREDICATE_RANGE];  // generated code
wire   ca_rf_renb0_r;  // generated code
assign ca_rf_renb0_r  = ca_code_r[`npuarc_RF_RENB0_RANGE];  // generated code
wire   ca_rf_renb1_r;  // generated code
assign ca_rf_renb1_r  = ca_code_r[`npuarc_RF_RENB1_RANGE];  // generated code
assign ca_rf_renb0_64_r  = ca_code_r[`npuarc_RF_RENB0_64_RANGE];  // generated code
assign ca_rf_renb1_64_r  = ca_code_r[`npuarc_RF_RENB1_64_RANGE];  // generated code
assign ca_rf_ra0_r  = ca_code_r[`npuarc_RF_RA0_RANGE];  // generated code
assign ca_rf_ra1_r  = ca_code_r[`npuarc_RF_RA1_RANGE];  // generated code
wire   ca_jli_src0_r;  // generated code
assign ca_jli_src0_r  = ca_code_r[`npuarc_JLI_SRC0_RANGE];  // generated code
assign ca_uop_inst_r  = ca_code_r[`npuarc_UOP_INST_RANGE];  // generated code
wire   ca_vec_shimm_r;  // generated code
assign ca_vec_shimm_r  = ca_code_r[`npuarc_VEC_SHIMM_RANGE];  // generated code
assign ca_iprot_viol_r  = ca_code_r[`npuarc_IPROT_VIOL_RANGE];  // generated code
assign ca_dmb_op_r  = ca_code_r[`npuarc_DMB_OP_RANGE];  // generated code
assign ca_dmb_type_r  = ca_code_r[`npuarc_DMB_TYPE_RANGE];  // generated code

