;; ============================================================================
;;
;; Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
;;
;; SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
;; work of Synopsys, Inc., and is fully protected under copyright and 
;; trade secret laws. You may not view, use, disclose, copy, or distribute 
;; this file or any information contained herein except pursuant to a 
;; valid written license from Synopsys, Inc.
;;
;; The entire notice above must be reproduced on all authorized copies.
;;
;; Description:
;;   Macros file containing registers and macros used in tests
;;  
;; ============================================================================


	.include 	"code.s"

	;; ===================================================================
	;;
	;;  TEST SECTION
	;;
	;; ===================================================================

	.equ	ONES_MASK_0,	0x00000000
	.equ	ONES_MASK_1,	0x00000001
	.equ	ONES_MASK_2,	0x00000003
	.equ	ONES_MASK_3,	0x00000007
	.equ	ONES_MASK_4,	0x0000000F
	.equ	ONES_MASK_5,	0x0000001F
	.equ	ONES_MASK_6,	0x0000003F
	.equ	ONES_MASK_7,	0x0000007F
	.equ	ONES_MASK_8,	0x000000FF
	.equ	ONES_MASK_9,	0x000001FF
	.equ	ONES_MASK_10,	0x000003FF
	.equ	ONES_MASK_11,	0x000007FF
	.equ	ONES_MASK_12,	0x00000FFF
	.equ	ONES_MASK_13,	0x00001FFF
	.equ	ONES_MASK_14,	0x00003FFF
	.equ	ONES_MASK_15,	0x00007FFF
	.equ	ONES_MASK_16,	0x0000FFFF
	.equ	ONES_MASK_17,	0x0001FFFF
	.equ	ONES_MASK_18,	0x0003FFFF
	.equ	ONES_MASK_19,	0x0007FFFF
	.equ	ONES_MASK_20,	0x000FFFFF
	.equ	ONES_MASK_21,	0x001FFFFF
	.equ	ONES_MASK_22,	0x003FFFFF
	.equ	ONES_MASK_23,	0x007FFFFF
	.equ	ONES_MASK_24,	0x00FFFFFF
	.equ	ONES_MASK_25,	0x01FFFFFF
	.equ	ONES_MASK_26,	0x03FFFFFF
	.equ	ONES_MASK_27,	0x07FFFFFF
	.equ	ONES_MASK_28,	0x0FFFFFFF
	.equ	ONES_MASK_29,	0x1FFFFFFF
	.equ	ONES_MASK_30,	0x3FFFFFFF
	.equ	ONES_MASK_31,	0x7FFFFFFF
	.equ	ONES_MASK_32,	0xFFFFFFFF

	.equ	IDENTITY6000,	0x00010140

	.equ 	REG_AUX_IDENTITY,	0x04

	;;  TODO
	.equ	REG_AUX_ISA_CONFIG, 	0x0C1
	.equ	BIT_CODE_DENSITY,	24
	.equ	BIT_ATOMIC,		21
	.equ	BIT_SWAP,		21
	.equ	BIT_BITSCAN,		20
	.equ	BIT_HAS_SHIFTER,	19
	.equ	BIT_SHIFT_ASSIST,	18
	.equ	BIT_RGF_NUM_REGS,	17

	.equ	REG_AUX_I_CACHE_BUILD,	0x77

	.equ	REG_AUX_IC_IVIC,	0x10
	.equ	REG_AUX_IC_TAG,		0x1B
	.equ	REG_AUX_ERET,		0x400

	.equ	REG_AUX_IC_CTRL, 	0x11
	.equ	BIT_IC_EN,		0x0
	.equ	REG_AUX_STATUS32,	0x00A
	.equ	BIT_IRQ1_EN,		0x02
	.equ	BIT_IRQ2_EN,		0x04

	.equ	REG_AUX_IRQ_LEV,	0x200
	.equ	REG_AUX_IRQ_HINT,	0x201
	.equ	REG_AUX_IRQ_LV12,	0x043
	.equ	REG_AUX_IENABLE,	0x40C
	.equ	REG_AUX_VECBASE_AC_BUILD, 0x68

	.equ	REG_AUX_CACHE_LIMIT,	0x5D

	.equ	REG_DCCM_BUILD,		0x074
	.equ	REG_BARREL_BUILD,	0x07F

	;; -------------------------------------------------------------------
	;; Check processor identity (cfg_verify_id)
	;;
	;; Verify the processor ID. Set bit 0 of the return register r0 to 1
	;; if the configuration is not skipjack.
	;;
	;; -------------------------------------------------------------------

cfg_verify_id_skipjack:
	mov 	r10, REG_AUX_IDENTITY
	lr	r0, [r10]
	cmp	r0, IDENTITY6000
	bset.ne	r0, r0, 1
	;; Temporarily disable until the ID register remains constant
	;; across development builds.
	mov	r0, 0
	j	[blink]

	;; Not implemented
cfg_verify_has_icache:
	lr	r0, [REG_AUX_I_CACHE_BUILD]
	mov.z	r0, 1
	mov	r0, 0
	j	[blink]

	;; Not implemented
cfg_verify_has_dcache:
	mov	r0, 0
	j	[blink]

	;; Not implemented
cfg_verify_has_dc_uncached_region:
	mov	r0, 0
	j	[blink]

	;; Not implemented
cfg_verify_bitscan_option:
	mov	r0, 0
	j	[blink]

	;; Not implemented
cfg_verify_has_dmp_peripheral:
	mov	r0, 0
	j	[blink]

	;; Not implemented
cfg_verify_atomic_option:
	lr	r0, [REG_AUX_ISA_CONFIG]
	btst	r0, BIT_ATOMIC
	mov.z	r0, 1
	j	[blink]

cfg_verify_code_density_option:
	lr	r0, [REG_AUX_ISA_CONFIG]
	btst 	r0, BIT_CODE_DENSITY
	mov.z	r0, 1
	;; TODO: ISA_CONFIG returns zero at present
	mov	r0, 0
	j	[blink]

cfg_verify_has_shift_assist:
	lr	r0, [REG_BARREL_BUILD]
	btst	r0, 8
	mov.z	r0, 1
	;; TODO: ISA_CONFIG returns zero at present
	mov	r0, 0
	j	[blink]

	;; Return (in R0) the value of MPY_OPTION
cfg_mpy_option:
	mov 	r0, 0
	j	[blink]

cfg_verify_has_mpy_loop_end:
	and	r0, r0, 0x3
	j	[blink]

cfg_verify_has_32_registers:
	lr	r0, [REG_AUX_ISA_CONFIG]
	btst 	r0, BIT_RGF_NUM_REGS
	mov.z	r0, 1
	j	[blink]

cfg_verify_has_dccm:
	lr	r0, [REG_DCCM_BUILD]
	and.f	r0, r0, 0xf
	mov.nz	r0, 1
	j	[blink]

	;; -------------------------------------------------------------------
	;; Test pass/fail routines
	;; -------------------------------------------------------------------

	.equ	BIT_PASS, 0x1
	.equ	BIT_FAIL, 0x2

	;; Define TSREG as the register through which status information is
	;; returned to the simulator.
	;;
	.define TSREG,	r26

	;; Test pass routine
	;;
	;; Standardised routines used to indicate whether the current test
	;; passed or failed. Constants are defined in "code.s".
	;;
	.global pass
pass:
	mov 	TSREG, 0|CORE|ASSEMBLER|0|CORETEST|PASSED
	mov	r0, 0
	nop
	nop
	flag	1
	nop
	nop

	;;  Test fail routine
	;;
	.global fail
fail:
	mov 	TSREG, 0|CORE|ASSEMBLER|0|CORETEST|FAILED
	mov	r0, 1
	nop
	nop
	flag	1
	nop
	nop
