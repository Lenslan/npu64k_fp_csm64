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
;;   Macros file for Actionpoints test 
;;  
;; ============================================================================


	.EQU	Z_BIT, 0x800
	.EQU	H_BIT, 0x001

	.macro	switch, a, b

	ror	a, b
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	ror	a, a
	.endm

	.macro	basl, a, b, c
	mov	LP_COUNT, c
	mov	a, b
	lp	2f

1:

	asl\&$suffix	a, a
	nop

2:
	.endm

	.macro	blsr, a, b, c
	mov	LP_COUNT, c
	mov	a, b
	lp	2f

1:

	lsr\&$suffix	a, a
	nop

2:
	.endm

	.macro	basr, a, b, c
	mov	LP_COUNT, c
	mov	a, b
	lp	2f

1:

	asr\&$suffix	a, a
	nop

2:
	.endm

	.macro	bror, a, b, c
	mov	LP_COUNT, c
	mov	a, b
	lp	2f

1:

	ror\&$suffix	a, a
	nop

2:
	.endm


	.macro	stop, a
	nop
	b\&$suffix	1f	; Branch to flag code if condition true.
	bal	2f	; Jump to end of stop macro if false.
1:
	flag	(a&Z_BIT)
	flag	H_BIT
2:
	.endm

	.macro	setcond, m1
	flag\&$suffix	m1
	.endm
