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

