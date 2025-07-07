// Library ARCv2HS-3.5.999999999
// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.

// Certain materials incorporated herein are copyright (C) 2010 - 2011,
// The University Court of the University of Edinburgh. All Rights Reserved.

assign da_rf_wa0    = da_code[`npuarc_RF_WA0_RANGE];  // generated code
assign da_rf_wenb0  = da_code[`npuarc_RF_WENB0_RANGE];  // generated code
assign da_rf_wenb0_64  = da_code[`npuarc_RF_WENB0_64_RANGE];  // generated code
wire   da_cc_byp_64_haz;  // generated code
assign da_cc_byp_64_haz  = da_code[`npuarc_CC_BYP_64_HAZ_RANGE];  // generated code
wire   da_has_limm;  // generated code
assign da_has_limm  = da_code[`npuarc_HAS_LIMM_RANGE];  // generated code
wire   da_is_16bit;  // generated code
assign da_is_16bit  = da_code[`npuarc_IS_16BIT_RANGE];  // generated code
wire   da_sr_op;  // generated code
assign da_sr_op  = da_code[`npuarc_SR_OP_RANGE];  // generated code
wire   da_loop_op;  // generated code
assign da_loop_op  = da_code[`npuarc_LOOP_OP_RANGE];  // generated code
wire   da_locked;  // generated code
assign da_locked  = da_code[`npuarc_LOCKED_RANGE];  // generated code
wire   da_wa0_lpc;  // generated code
assign da_wa0_lpc  = da_code[`npuarc_WA0_LPC_RANGE];  // generated code
assign da_dslot     = da_code[`npuarc_DSLOT_RANGE];  // generated code
wire   da_sleep_op;  // generated code
assign da_sleep_op  = da_code[`npuarc_SLEEP_OP_RANGE];  // generated code
wire   da_acc_wenb;  // generated code
assign da_acc_wenb  = da_code[`npuarc_ACC_WENB_RANGE];  // generated code
wire   da_writes_acc;  // generated code
assign da_writes_acc  = da_code[`npuarc_WRITES_ACC_RANGE];  // generated code
wire   da_lr_op;  // generated code
assign da_lr_op  = da_code[`npuarc_LR_OP_RANGE];  // generated code
wire   da_jump;  // generated code
assign da_jump  = da_code[`npuarc_JUMP_RANGE];  // generated code
wire   da_load;  // generated code
assign da_load  = da_code[`npuarc_LOAD_RANGE];  // generated code
wire   da_pref;  // generated code
assign da_pref  = da_code[`npuarc_PREF_RANGE];  // generated code
wire   da_store;  // generated code
assign da_store  = da_code[`npuarc_STORE_RANGE];  // generated code
wire   da_uop_prol;  // generated code
assign da_uop_prol  = da_code[`npuarc_UOP_PROL_RANGE];  // generated code
assign da_rf_wa1    = da_code[`npuarc_RF_WA1_RANGE];  // generated code
assign da_rf_wenb1  = da_code[`npuarc_RF_WENB1_RANGE];  // generated code
assign da_rf_wenb1_64  = da_code[`npuarc_RF_WENB1_64_RANGE];  // generated code
wire   da_signed_op;  // generated code
assign da_signed_op  = da_code[`npuarc_SIGNED_OP_RANGE];  // generated code
wire   da_double_size;  // generated code
assign da_double_size  = da_code[`npuarc_DOUBLE_SIZE_RANGE];  // generated code
wire   da_half_size;  // generated code
assign da_half_size  = da_code[`npuarc_HALF_SIZE_RANGE];  // generated code
wire   da_byte_size;  // generated code
assign da_byte_size  = da_code[`npuarc_BYTE_SIZE_RANGE];  // generated code
wire   da_rtie_op;  // generated code
assign da_rtie_op  = da_code[`npuarc_RTIE_OP_RANGE];  // generated code
wire   da_enter_op;  // generated code
assign da_enter_op  = da_code[`npuarc_ENTER_OP_RANGE];  // generated code
wire   da_leave_op;  // generated code
assign da_leave_op  = da_code[`npuarc_LEAVE_OP_RANGE];  // generated code
wire   da_trap_op;  // generated code
assign da_trap_op  = da_code[`npuarc_TRAP_OP_RANGE];  // generated code
wire   da_sync_op;  // generated code
assign da_sync_op  = da_code[`npuarc_SYNC_OP_RANGE];  // generated code
wire   da_brk_op;  // generated code
assign da_brk_op  = da_code[`npuarc_BRK_OP_RANGE];  // generated code
wire   da_invalid_instr;  // generated code
assign da_invalid_instr  = da_code[`npuarc_INVALID_INSTR_RANGE];  // generated code
wire   da_rgf_link;  // generated code
assign da_rgf_link  = da_code[`npuarc_RGF_LINK_RANGE];  // generated code
wire   da_prod_sign;  // generated code
assign da_prod_sign  = da_code[`npuarc_PROD_SIGN_RANGE];  // generated code
wire   da_macu;  // generated code
assign da_macu  = da_code[`npuarc_MACU_RANGE];  // generated code
wire   da_quad_op;  // generated code
assign da_quad_op  = da_code[`npuarc_QUAD_OP_RANGE];  // generated code
wire   da_acc_op;  // generated code
assign da_acc_op  = da_code[`npuarc_ACC_OP_RANGE];  // generated code
wire   da_vector_op;  // generated code
assign da_vector_op  = da_code[`npuarc_VECTOR_OP_RANGE];  // generated code
wire   da_dual_op;  // generated code
assign da_dual_op  = da_code[`npuarc_DUAL_OP_RANGE];  // generated code
assign da_mpy_op    = da_code[`npuarc_MPY_OP_RANGE];  // generated code
wire   da_z_wen;  // generated code
assign da_z_wen  = da_code[`npuarc_Z_WEN_RANGE];  // generated code
wire   da_n_wen;  // generated code
assign da_n_wen  = da_code[`npuarc_N_WEN_RANGE];  // generated code
wire   da_c_wen;  // generated code
assign da_c_wen  = da_code[`npuarc_C_WEN_RANGE];  // generated code
wire   da_v_wen;  // generated code
assign da_v_wen  = da_code[`npuarc_V_WEN_RANGE];  // generated code
wire   da_kernel_op;  // generated code
assign da_kernel_op  = da_code[`npuarc_KERNEL_OP_RANGE];  // generated code
wire   da_flag_op;  // generated code
assign da_flag_op  = da_code[`npuarc_FLAG_OP_RANGE];  // generated code
wire   da_bcc;  // generated code
assign da_bcc  = da_code[`npuarc_BCC_RANGE];  // generated code
wire   da_link;  // generated code
assign da_link  = da_code[`npuarc_LINK_RANGE];  // generated code
wire   da_brcc_bbit;  // generated code
assign da_brcc_bbit  = da_code[`npuarc_BRCC_BBIT_RANGE];  // generated code
wire   da_cache_byp;  // generated code
assign da_cache_byp  = da_code[`npuarc_CACHE_BYP_RANGE];  // generated code
wire   da_slow_op;  // generated code
assign da_slow_op  = da_code[`npuarc_SLOW_OP_RANGE];  // generated code
wire   da_fast_op;  // generated code
assign da_fast_op  = da_code[`npuarc_FAST_OP_RANGE];  // generated code
wire   da_div_op;  // generated code
assign da_div_op  = da_code[`npuarc_DIV_OP_RANGE];  // generated code
wire   da_btab_op;  // generated code
assign da_btab_op  = da_code[`npuarc_BTAB_OP_RANGE];  // generated code
assign da_ei_op     = da_code[`npuarc_EI_OP_RANGE];  // generated code
wire   da_in_eslot;  // generated code
assign da_in_eslot  = da_code[`npuarc_IN_ESLOT_RANGE];  // generated code
wire   da_rel_branch;  // generated code
assign da_rel_branch  = da_code[`npuarc_REL_BRANCH_RANGE];  // generated code
wire   da_illegal_operand;  // generated code
assign da_illegal_operand  = da_code[`npuarc_ILLEGAL_OPERAND_RANGE];  // generated code
wire   da_swap_op;  // generated code
assign da_swap_op  = da_code[`npuarc_SWAP_OP_RANGE];  // generated code
wire   da_setcc_op;  // generated code
assign da_setcc_op  = da_code[`npuarc_SETCC_OP_RANGE];  // generated code
wire [2:0]  da_cc_field;  // generated code
assign da_cc_field  = da_code[`npuarc_CC_FIELD_RANGE];  // generated code
assign da_q_field   = da_code[`npuarc_Q_FIELD_RANGE];  // generated code
assign da_dest_cr_is_ext  = da_code[`npuarc_DEST_CR_IS_EXT_RANGE];  // generated code
wire   da_add_op;  // generated code
assign da_add_op  = da_code[`npuarc_ADD_OP_RANGE];  // generated code
wire   da_and_op;  // generated code
assign da_and_op  = da_code[`npuarc_AND_OP_RANGE];  // generated code
wire   da_or_op;  // generated code
assign da_or_op  = da_code[`npuarc_OR_OP_RANGE];  // generated code
wire   da_xor_op;  // generated code
assign da_xor_op  = da_code[`npuarc_XOR_OP_RANGE];  // generated code
wire   da_mov_op;  // generated code
assign da_mov_op  = da_code[`npuarc_MOV_OP_RANGE];  // generated code
wire   da_with_carry;  // generated code
assign da_with_carry  = da_code[`npuarc_WITH_CARRY_RANGE];  // generated code
wire   da_simple_shift_op;  // generated code
assign da_simple_shift_op  = da_code[`npuarc_SIMPLE_SHIFT_OP_RANGE];  // generated code
wire   da_left_shift;  // generated code
assign da_left_shift  = da_code[`npuarc_LEFT_SHIFT_RANGE];  // generated code
wire   da_rotate_op;  // generated code
assign da_rotate_op  = da_code[`npuarc_ROTATE_OP_RANGE];  // generated code
wire   da_inv_src1;  // generated code
assign da_inv_src1  = da_code[`npuarc_INV_SRC1_RANGE];  // generated code
wire   da_inv_src2;  // generated code
assign da_inv_src2  = da_code[`npuarc_INV_SRC2_RANGE];  // generated code
wire   da_bit_op;  // generated code
assign da_bit_op  = da_code[`npuarc_BIT_OP_RANGE];  // generated code
wire   da_mask_op;  // generated code
assign da_mask_op  = da_code[`npuarc_MASK_OP_RANGE];  // generated code
wire   da_src2_mask_sel;  // generated code
assign da_src2_mask_sel  = da_code[`npuarc_SRC2_MASK_SEL_RANGE];  // generated code
wire   da_uop_commit;  // generated code
assign da_uop_commit  = da_code[`npuarc_UOP_COMMIT_RANGE];  // generated code
wire   da_uop_epil;  // generated code
assign da_uop_epil  = da_code[`npuarc_UOP_EPIL_RANGE];  // generated code
wire   da_uop_excpn;  // generated code
assign da_uop_excpn  = da_code[`npuarc_UOP_EXCPN_RANGE];  // generated code
wire   da_predicate;  // generated code
assign da_predicate  = da_code[`npuarc_PREDICATE_RANGE];  // generated code
wire   da_rf_renb0;  // generated code
assign da_rf_renb0  = da_code[`npuarc_RF_RENB0_RANGE];  // generated code
wire   da_rf_renb1;  // generated code
assign da_rf_renb1  = da_code[`npuarc_RF_RENB1_RANGE];  // generated code
wire   da_rf_renb0_64;  // generated code
assign da_rf_renb0_64  = da_code[`npuarc_RF_RENB0_64_RANGE];  // generated code
wire   da_rf_renb1_64;  // generated code
assign da_rf_renb1_64  = da_code[`npuarc_RF_RENB1_64_RANGE];  // generated code
wire [5:0]  da_rf_ra0;  // generated code
assign da_rf_ra0  = da_code[`npuarc_RF_RA0_RANGE];  // generated code
wire [5:0]  da_rf_ra1;  // generated code
assign da_rf_ra1  = da_code[`npuarc_RF_RA1_RANGE];  // generated code
assign da_jli_src0  = da_code[`npuarc_JLI_SRC0_RANGE];  // generated code
wire   da_uop_inst;  // generated code
assign da_uop_inst  = da_code[`npuarc_UOP_INST_RANGE];  // generated code
wire   da_vec_shimm;  // generated code
assign da_vec_shimm  = da_code[`npuarc_VEC_SHIMM_RANGE];  // generated code
wire   da_iprot_viol;  // generated code
assign da_iprot_viol  = da_code[`npuarc_IPROT_VIOL_RANGE];  // generated code
wire   da_dmb_op;  // generated code
assign da_dmb_op  = da_code[`npuarc_DMB_OP_RANGE];  // generated code
wire [2:0]  da_dmb_type;  // generated code
assign da_dmb_type  = da_code[`npuarc_DMB_TYPE_RANGE];  // generated code
wire   da_force_cin;  // generated code
assign da_force_cin  = da_code[`npuarc_FORCE_CIN_RANGE];  // generated code
wire   da_opd3_sel;  // generated code
assign da_opd3_sel  = da_code[`npuarc_OPD3_SEL_RANGE];  // generated code
wire   da_multi_op;  // generated code
assign da_multi_op  = da_code[`npuarc_MULTI_OP_RANGE];  // generated code
wire   da_abs_op;  // generated code
assign da_abs_op  = da_code[`npuarc_ABS_OP_RANGE];  // generated code
wire   da_min_op;  // generated code
assign da_min_op  = da_code[`npuarc_MIN_OP_RANGE];  // generated code
wire   da_max_op;  // generated code
assign da_max_op  = da_code[`npuarc_MAX_OP_RANGE];  // generated code
wire   da_norm_op;  // generated code
assign da_norm_op  = da_code[`npuarc_NORM_OP_RANGE];  // generated code
assign da_ldi_src0  = da_code[`npuarc_LDI_SRC0_RANGE];  // generated code
wire   da_pre_addr;  // generated code
assign da_pre_addr  = da_code[`npuarc_PRE_ADDR_RANGE];  // generated code
wire   da_stimm_op;  // generated code
assign da_stimm_op  = da_code[`npuarc_STIMM_OP_RANGE];  // generated code
wire   da_src2_sh1;  // generated code
assign da_src2_sh1  = da_code[`npuarc_SRC2_SH1_RANGE];  // generated code
wire   da_src2_sh2;  // generated code
assign da_src2_sh2  = da_code[`npuarc_SRC2_SH2_RANGE];  // generated code
wire   da_src2_sh3;  // generated code
assign da_src2_sh3  = da_code[`npuarc_SRC2_SH3_RANGE];  // generated code
wire   da_barrel_shift_op;  // generated code
assign da_barrel_shift_op  = da_code[`npuarc_BARREL_SHIFT_OP_RANGE];  // generated code
wire   da_opds_in_x1;  // generated code
assign da_opds_in_x1  = da_code[`npuarc_OPDS_IN_X1_RANGE];  // generated code
wire   da_agu_uses_r0;  // generated code
assign da_agu_uses_r0  = da_code[`npuarc_AGU_USES_R0_RANGE];  // generated code
wire   da_opds_in_sa;  // generated code
assign da_opds_in_sa  = da_code[`npuarc_OPDS_IN_SA_RANGE];  // generated code
wire   da_limm0_64;  // generated code
assign da_limm0_64  = da_code[`npuarc_LIMM0_64_RANGE];  // generated code
wire   da_limm1_64;  // generated code
assign da_limm1_64  = da_code[`npuarc_LIMM1_64_RANGE];  // generated code
assign da_may_graduate  = da_code[`npuarc_MAY_GRADUATE_RANGE];  // generated code
wire   da_agu_uses_r1;  // generated code
assign da_agu_uses_r1  = da_code[`npuarc_AGU_USES_R1_RANGE];  // generated code
wire   da_reads_acc;  // generated code
assign da_reads_acc  = da_code[`npuarc_READS_ACC_RANGE];  // generated code
wire   da_dsync_op;  // generated code
assign da_dsync_op  = da_code[`npuarc_DSYNC_OP_RANGE];  // generated code
wire   da_src2_shifts;  // generated code
assign da_src2_shifts  = da_code[`npuarc_SRC2_SHIFTS_RANGE];  // generated code
wire   da_sel_shimm;  // generated code
assign da_sel_shimm  = da_code[`npuarc_SEL_SHIMM_RANGE];  // generated code
wire [31:0]  da_shimm;  // generated code
assign da_shimm  = da_code[`npuarc_SHIMM_RANGE];  // generated code
wire   da_limm_r0;  // generated code
assign da_limm_r0  = da_code[`npuarc_LIMM_R0_RANGE];  // generated code
wire   da_limm_r1;  // generated code
assign da_limm_r1  = da_code[`npuarc_LIMM_R1_RANGE];  // generated code
wire [31:0]  da_offset;  // generated code
assign da_offset  = da_code[`npuarc_OFFSET_RANGE];  // generated code

