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

