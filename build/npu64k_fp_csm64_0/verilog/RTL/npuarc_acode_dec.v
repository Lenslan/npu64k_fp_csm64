// Library ARCv2HS-3.5.999999999
// *SYNOPSYS CONFIDENTIAL*
// 
// This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
// protected under copyright and trade secret laws.  You may not view, use, 
// disclose, copy, or distribute this file or any information contained herein 
// except pursuant to a valid written license from Synopsys.

// Certain materials incorporated herein are copyright (C) 2010 - 2011,
// The University Court of the University of Edinburgh. All Rights Reserved.

reg  [5:0] rf_wa0;  // Register address for write port 0
reg rf_wenb0;  // Register write enable for write port 0
reg rf_wenb0_64;  // 64-bit write enable for write port 0
reg cc_byp_64_haz;  // Unable to bypass 64-bit result to SA
reg has_limm;  // Instruction has LIMM data
reg is_16bit;  // Instruction is 16-bit encoded
reg sr_op;  // Decodes an |SR| instruction
reg loop_op;  // Decodes an |LPcc| instruction
reg locked;  // Set if mem-op is locked
reg wa0_lpc;  // Set if write port 0 selects |LP_COUNT| register
reg dslot;  // Set if control transfer has a delay slot instruction
reg sleep_op;  // Decodes the |SLEEP| instruction
reg acc_wenb;  // Set if implicit write to the accumulator
reg writes_acc;  // ACCL or ACCH is an explicit register destination
reg lr_op;  // Decodes an |LR| instruction
reg jump;  // Decodes jump instructions |Jcc| and |JLcc|
reg load;  // Decodes all forms of |load| instruction
reg pref;  // Set if |load| is a pref instruction
reg store;  // Decodes all forms of |store| instruction
reg uop_prol;  // Instruction is terminal of PROL sequence
reg  [5:0] rf_wa1;  // Register address for write port 1
reg rf_wenb1;  // Register write enable for write port 1
reg rf_wenb1_64;  // 64-bit write enable for write port 1
reg signed_op;  // Set if operation is signed
reg double_size;  // Set if operation is 64-bit
reg half_size;  // Set if operation is 16-bit
reg byte_size;  // Set if operation is 8-bit
reg rtie_op;  // Decodes the |RTIE| instruction
reg enter_op;  // Decodes the |ENTER_S| instruction
reg leave_op;  // Decodes the |LEAVE_S| instruction
reg trap_op;  // Decodes the |TRAP0| or |TRAP_S| instruction
reg sync_op;  // Decodes the |SYNC| instruction
reg brk_op;  // Decodes the |BRK| or |BRK_S| instruction
reg invalid_instr;  // Set if instruction is not recognised
reg rgf_link;  // Set if ILINK regs are accessed
reg prod_sign;  // sign of 32x32 mac product
reg macu;  // indicates MACU, MACDU, MPYU or MPYDU operation
reg quad_op;  // Set if performing dual SIMD operation
reg acc_op;  // Set if accumulator is used by fixed-point operation
reg vector_op;  // Set if performing vector operation
reg dual_op;  // Set if performing dual SIMD operation
reg mpy_op;  // Set if performing multiply operation
reg z_wen;  // Write enable for |Z| bit in |STATUS32| register
reg n_wen;  // Write enable for |N| bit in |STATUS32| register
reg c_wen;  // Write enable for |C| bit in |STATUS32| register
reg v_wen;  // Write enable for |V| bit in |STATUS32| register
reg kernel_op;  // Set if instruction is privileged
reg flag_op;  // Decodes |FLAG| instruction
reg bcc;  // Decodes branch instructions |Bcc| and |BLcc|
reg link;  // Set if jump or branch enables linkage semantics (|JLcc|, |BLcc|)
reg brcc_bbit;  // Decodes compare-branch instructions |BRcc| and |BBITn|
reg cache_byp;  // Set if |load| or |store| bypasses the cache
reg slow_op;  // Indicates 2-cycle ALU op (must evaluate in X1 and X2)
reg fast_op;  // Indicates 1-cycle ALU op (can evaluate in X1 or CA)
reg div_op;  // Decodes |DIV|, |DIVU|, |REM| and |REMU|
reg btab_op;  // Perform a BI_S or BIH_S instruction
reg ei_op;  // Select EI_BASE as base addr in rel-branch, and do EI_S instruction
reg in_eslot;  // Instruction is in the exec-slot of a previous EI_S instruction
reg rel_branch;  // Set if control transfer uses a relative displacement
reg illegal_operand;  // Set if operand is illegal
reg swap_op;  // Decodes |SWAP| instruction
reg setcc_op;  // Decodes |SETcc| instructions
reg  [2:0] cc_field;  // Selects |BRcc|, |BBITn| or |SETcc| operator
reg  [4:0] q_field;  // Instruction predicate or branch condition
reg dest_cr_is_ext;  // Instruction has explicit extension core register destination
reg add_op;  // Set if Adder is enabled for this instruction
reg and_op;  // Set if logical AND operation is required for this instruction
reg or_op;  // Set if logical OR operation is required for this instruction
reg xor_op;  // Set if logical XOR operation is required for this instruction
reg mov_op;  // Set if operand 2 is moved to the destination
reg with_carry;  // Set if arithmetic or shift operation uses the |STATUS32.C| bit
reg simple_shift_op;  // Set if single-bit shift or rotate is required
reg left_shift;  // 1 $\rightarrow$ shift-left; 0 $\rightarrow$ shift-right
reg rotate_op;  // 1 $\rightarrow$ rotate; 0 $\rightarrow$ linear shift
reg inv_src1;  // Set if source operand 1 is to be inverted
reg inv_src2;  // Set if source operand 2 is to be inverted
reg bit_op;  // Selects a one-hot bit-mask in |maskgen| module
reg mask_op;  // Selects a bit-field mask in |maskgen| module for |BMSK| instruction
reg src2_mask_sel;  // Selects |maskgen|'s bit-mask as source operand 2
reg uop_commit;  // Instruction terminates uop. sequence
reg uop_epil;  // Instruction is terminal of EPIL sequence
reg uop_excpn;  // Instruction is terminal of Exception Epilogue
reg predicate;  // Instruction predicate, 0 => result updated is not allowed
reg rf_renb0;  // Register read enable for read port 0
reg rf_renb1;  // Register read enable for read port 1
reg rf_renb0_64;  // 64-bit read enable for read port 0
reg rf_renb1_64;  // 64-bit read enable for read port 1
reg  [5:0] rf_ra0;  // Register address for read port 0
reg  [5:0] rf_ra1;  // Register address for read port 1
reg jli_src0;  // Select JLI_BASE rather than PC as base addr in rel-branch
reg uop_inst;  // Instruction is part of a uop sequence
reg vec_shimm;  // vector of 16-bit SHIMM opds required
reg iprot_viol;  // speculative instruction fetch protection violation
reg dmb_op;  // Decodes the |DMB| instruction
reg  [2:0] dmb_type;  // Decodes the |DMB| sub-type
reg force_cin;  // Forces carry-in of 1 for Adder operation
reg opd3_sel;  // Select source 3: 1 $\rightarrow$ register 1; 0 $\rightarrow$ register 0
reg multi_op;  // Decodes a multi-operation insn.
reg abs_op;  // Decodes the |ABS| instruction
reg min_op;  // Decodes |MIN| instruction
reg max_op;  // Decodes |MAX| instruction
reg norm_op;  // Decodes |NORM| instruction
reg ldi_src0;  // Select LDI_BASE as base for register address calculation
reg pre_addr;  // Set if addressing mode uses pre-modified value
reg stimm_op;  // Indicates a store-immediate operation
reg src2_sh1;  // Enables 1-bit shift of source operand 2
reg src2_sh2;  // Enables 2-bit shift of source operand 2
reg src2_sh3;  // Enables 3-bit shift of source operand 2
reg barrel_shift_op;  // Set if multi-bit shift or rotate is required
reg opds_in_x1;  // Indicates op will require operands in X1 (starts in X2)
reg agu_uses_r0;  // AGU uses reg0 as a source operand
reg opds_in_sa;  // Indicates op will require operands in SA (starts in X1)
reg limm0_64;  // 64-bit LIMM required on read port 0
reg limm1_64;  // 64-bit LIMM required on read port 1
reg may_graduate;  // ACCL/ACCH could be explicit dest and insn may graduate
reg agu_uses_r1;  // AGU uses reg1 as a source operand
reg reads_acc;  // ACCL or ACCH is an explicit register operand
reg dsync_op;  // Decodes the |DSYNC| instruction
reg src2_shifts;  // Source operand 2 is shifted 1, 2 or 3 bits before the adder
reg sel_shimm;  // Selects a short-immediate operand (i.e. |S12|, |U6|, etc) as source operand 2
reg  [31:0] shimm;  // The short immediate operand, extended to 32-bits as required by the instruction
reg limm_r0;  // Set if register operand {\sf\bf b} is actually LIMM data
reg limm_r1;  // Set if register operand {\sf\bf c} is actually LIMM data
reg  [31:0] offset;  // Relative branch offset, sign-extended to 32-bits

