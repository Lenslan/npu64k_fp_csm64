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
;;   ** make file inclusion conditional
;;                                                             
;; ============================================================================


; Macros file containing registers and macros used in tests
;
;
; ** make file inclusion conditional

.ifndef MACROS_S
.equ    MACROS_S, 0xABADCAFE

; Required to support 16/32 register file test code
;
.define tsreg, r26


; These are the Build Configuration Registers.
; They reflect the configuration of an ARC.
;
; |31 -----Config Information ----- 8|7 --Version-- 0|
; |__________________________________|_______________|
;                 |                          |
;    This part reflects the            This part reflects
;    configuration of a                which version of the
;    particular extension              extension is used.
;

    .extAuxRegister  BCR_VER ,            0x60, r
	.extAuxRegister  BTA_LINK_BCR ,       0x63, r
    .extAuxRegister  VECBASE_AC_BCR ,     0x68, r
    .extAuxRegister  MPU_BCR ,            0x6d, r
    .extAuxRegister  RF_BCR ,             0x6e, r
    .extAuxRegister  DCACHE_BCR ,         0x72, r
    .extAuxRegister  DCCM_BCR ,           0x74, r
    .extAuxRegister  TIMER_BCR ,          0x75, r
    .extAuxRegister  AP_BCR ,             0x76, r
    .extAuxRegister  ICACHE_BCR ,         0x77, r
    .extAuxRegister  ICCM_BCR ,           0x78, r
    .extAuxRegister  MULTIPLY_BCR ,       0x7b, r
    .extAuxRegister  SWAP_BCR ,           0x7c, r
    .extAuxRegister  NORM_BCR ,           0x7d, r
    .extAuxRegister  MINMAX_BCR ,         0x7e, r
    .extAuxRegister  BARREL_BCR ,         0x7f, r
    .extAuxRegister  BPU_BCR ,            0xc0, r
    .extAuxRegister  ISA_CONFIG_BCR ,     0xc1, r
    .extAuxRegister  STACK_REGION_BCR ,   0xc5, r
    .extAuxRegister  ECC_BCR ,            0xc7, r
    .extAuxRegister  FPU_BCR ,            0xc8, r
    .extAuxRegister  IRQ_BCR ,            0xf3, r
    .extAuxRegister  PDM_DVFS_BCR ,       0xf7, r
    .extAuxRegister  SMART_BCR ,          0xff, r

	.extAuxRegister  STATUS32 ,           0x00A, r|w
	.extAuxRegister  STATUS32_P0 ,        0x00B, r|w

;; Timer auxiliary registers
    .extAuxRegister  t0_count ,           0x21,  r|w
    .extAuxRegister  t0_control ,         0x22,  r|w
    .extAuxRegister  t0_limit ,           0x23,  r|w
    .extAuxRegister  t1_count ,           0x100, r|w
    .extAuxRegister  t1_control ,         0x101, r|w
    .extAuxRegister  t1_limit ,           0x102, r|w

;; IRQ auxiliary registers
    .extAuxRegister  irq_select ,         0x40b, r|w
    .extAuxRegister  irq_trigger ,        0x40d, r|w
    .extAuxRegister  irq_priority ,       0x206, r|w
    .extAuxRegister  irq_enable ,         0x40c, r|w


; ** changed definitions to new flag instruction format

.equ    ZZERO,      0x800
.equ    NZERO,      0x700
.equ    POS,        0xb00
.equ    NEG,        0x400
.equ    CARRY,      0x200
.equ    NCARRY,     0xd00
.equ    OVERFL,     0x100
.equ    NOVERFL,    0xe00
.equ    GREATR1,    0x700
.equ    GREATR2,    0x200
.equ    GEQUAL1,    0x500
.equ    GEQUAL2,    0xa00
.equ    LESSTH1,    0x400
.equ    LESSTH2,    0x100
.equ    HIGHER,     0x500
.equ    LOWER1,     0x200
.equ    LOWER2,     0x800
.equ    POSNZ,      0x300
.equ    H_BIT,      0x01

.equ    ____, 0x0
.equ    ___V, 0x100
.equ    __C_, 0x200
.equ    __CV, 0x300
.equ    _N__, 0x400
.equ    _N_V, 0x500
.equ    _NC_, 0x600
.equ    _NCV, 0x700
.equ    Z___, 0x800
.equ    Z__V, 0x900
.equ    Z_C_, 0xa00
.equ    Z_CV, 0xb00
.equ    ZN__, 0xc00
.equ    ZN_V, 0xd00
.equ    ZNC_, 0xe00
.equ    ZNCV, 0xf00

; Flags to disable interrupts using status register

.equ    EI, 0x06     ; Constant to enable both interrupt levels
.equ    DI, 0x00     ; Constant to disable both

;----------------------------------- Macros -----------------------------------

.macro switch, a, b

    ror a , b
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    ror a , a
    .endm

.macro basl, a, b, c
    mov LP_COUNT,c
    mov a,b
    lp  2f

1:

    asl\&$suffix a,a
    nop

2:
    .endm

.macro blsr, a, b, c
    mov LP_COUNT,c
    mov a,b
    lp  2f

1:

    lsr\&$suffix a,a
    nop

2:
    .endm

.macro basr, a, b, c
    mov LP_COUNT,c
    mov a,b
    lp  2f

1:

    asr\&$suffix a,a
    nop

2:
    .endm

.macro bror, a, b, c
    mov LP_COUNT,c
    mov a,b
    lp  2f

1:

    ror\&$suffix a,a
    nop

2:
    .endm


.macro stop, a,dep,sys,part,code,def
    nop
    b\&$suffix      1f        ; Branch to flag code if condition true.
    bal             2f        ; Jump to end of stop macro if false.
1:
    sub.f           0,def,0x00000001 ;if PASSED.....
    beq             3f
    mov.f           tsreg, dep|sys|part<<12|code|def
3:
    flag            (a & ZZERO)
    flag            H_BIT
2:
.endm

; Macro to set flag conditions for checking the 'S' Flag.

    .macro setcondb, a
        MULU            0,a,a ; Initialise accumulator to known value.
        MAC.f           0,0,0 ; Set flag based on contents of accumulator.
        flag\&$suffix   a     ; Set standard flags.
        .endm

.macro setcond,m1
    flag\&$suffix  m1
.endm

; Macro to produce multiple NOPs
.macro nops,num
	.rept num
	      nop
	.endr
.endm
;------------------------------------------------------------------------------

.endif  ; MACROS_S

.macro initregs

	mov r0,0
	mov r1,0
	mov r2,0
	mov r3,0
		mov r4,0
	mov r5,0
	mov r6,0
	mov r7,0
	mov r8,0
	mov r9,0
	
	mov r10,0
	mov r11,0
	mov r12,0
	mov r13,0
	mov r14,0
	mov r15,0
		mov r16,0
	mov r17,0
	mov r18,0
	mov r19,0
	mov r20,0
	mov r21,0
	mov r22,0
	mov r23,0
	mov r24,0
	mov r25,0
	
	mov r26,0
	mov r27,0
	mov r28,0
	mov r29,0
	mov r30,0
	mov r31,0

    .endm

    
.macro get_code_address, address
       lr address, [VECBASE_AC_BUILD] 
       and address, address, VECBASE_MASK
.endm

.macro init_llm, llm_address
        mov temp0, llm_address
        mov temp1, 0x580

init_llm_loop:
        st.di temp1, [temp0];
        add temp0, temp0, 4
        sub temp1, temp1, 4
        cmp.f temp1, 0
        bne init_llm_loop

        mov temp0, llm_address
        mov temp1, 0x580
read_llm_loop:
        ld.di read_value, [temp0];
        add temp0, temp0, 4
        sub temp1, temp1, 4
        cmp.f temp1, 0
        bne read_llm_loop

        mov temp0, llm_address
        mov temp1, 0x580
cmp_llm:
        ld.di read_value, [temp0];
        cmp.f read_value, temp1
        bne test_failed
        add temp0, temp0, 4
        sub temp1, temp1, 4
        cmp.f temp1, 0
        bne cmp_llm

.endm

.macro init_llm_32k, llm_address
        mov temp0, llm_address
        mov temp1, 0x8000

init_llm_32_loop:
        st.di temp1, [temp0];
        add temp0, temp0, 4
        sub temp1, temp1, 4
        cmp.f temp1, 0
        bne init_llm_32_loop

        mov temp0, llm_address
        mov temp1, 0x8000
read_llm_32_loop:
        ld.di read_value, [temp0]
        add temp0, temp0, 4
        sub temp1, temp1, 4
        cmp.f temp1, 0
        bne read_llm_32_loop

        mov temp0, llm_address
        mov temp1, 0x8000
        sub temp1, temp1, 4
        add temp0, temp0, temp1
        st.di temp1, [temp0]
.endm
.macro get_value, llm_address
        mov temp0, llm_address
        mov temp1, core_id
        lsl temp1, temp1
        add write_value, temp0, temp1
.endm
