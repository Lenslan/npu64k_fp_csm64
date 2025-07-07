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
;;    Macros for basic_alu_dense cct
;;  
;; ============================================================================


.macro  mstop
  ; this macro covers all "mstop.cc"
  add         tsreg, tsreg, 0x000001000     ; Add one to test count subfield
  b\&$suffix  failure                       ; If condition is true: branch to failure
.endm

.macro  mtr, expected_res, actual_res       ; Macro Test Result
  cmp       expected_res, actual_res        ; Compare actual result with expected
  mstop.nz
.endm

; ** mask for testing flags modified to not mask halt bit
; ** this was required to run tests properly in scac iss
.macro  mtf, expected_flag        ; Macro test flag  
  lr        r27, [STATUS32]         ; read flags
  and       r27, r27, H_BIT + ZNCV  ; mask flags, keep halt bit
  rcmp      r27, expected_flag      ; Compare flags with expected flags 
  mstop.nz
.endm

.macro  test0, flags, op1, op2, add_res, sub_res, add_flg, sub_flg
  ; tests ADC, SBC instructions and flags
  mov	  r1, op1
  mov	  r2, op2
  flag    flags
  adc.f   r0, r1, r2
  mtf	  add_flg
  mtr	  add_res, r0
  flag    flags
  sbc.f   r3, r1, r2
  mtf	  sub_flg
  mtr	  sub_res, r3
.endm

.macro  test1, flags, op1, op2, add_res, sub_res, add_flg, sub_flg
  ; tests ADD, SUB instructions and flags
  mov	  r1, op1
  mov	  r2, op2
  flag    flags
  add.f   r0, r1, r2
  mtf	  add_flg
  mtr	  add_res, r0
  flag    flags
  sub.f   r3, r1, r2
  mtf	  sub_flg
  mtr	  sub_res, r3
.endm

.macro  test2, op1, op2, op3, add_res, sub_res
  ; add/sub set flags for adc/sbc
  mov	  r1, op1
  mov	  r2, op2
  mov	  r3, op3
  flag    ____
  add.f   r10, r1, r2
  adc	  r11, r10, r3
  mtr	  add_res, r11
  flag    ____
  sub.f   r10, r1, r2
  sbc	  r11, r10, r3
  mtr	  sub_res, r11
.endm

.macro  test3, flags, op1, op2, op3, add_res, sub_res
; adc/sbc set flag for adc/sbc
  mov	  r1, op1
  mov	  r2, op2
  mov	  r3, op3
  flag    flags
  adc.f   r10, r1, r2
  adc	  r11, r10, r3
  mtr	  add_res, r11
  flag    flags
  sbc.f   r10, r1, r2
  sbc	  r11, r10, r3
  mtr	  sub_res, r11
.endm

.macro  test4, flags, op1, op2, res1, res2, res3, res4, flg1, flg2, flg3, flg4
  ; Testing sign and zero extend for both word and byte inputs
  mov	  r1, op1
  mov	  r2, op2
  flag    flags
  sexw.f  r10, r1
  mtf	  flg1
  mtr	  res1, r10
  flag    flags
  extw.f  r10, r1
  mtf	  flg2
  mtr	  res2, r10
  flag    flags
  sexb.f  r10, r2
  mtf	  flg3
  mtr	  res3, r10
  flag    flags
  extb.f  r10, r2
  mtf	  flg4
  mtr	  res4, r10
.endm

.macro  test5, op1, op2, res1, res2, res3, res4, flg1, flg2, flg3, flg4
  ; Testing Logical insts result and flags
  mov	  r1, op1
  mov	  r2, op2
  and.f   r10, r1, r2
  mtf	  flg1
  mtr	  res1, r10
  or.f    r10, r1, r2
  mtf	  flg2
  mtr	  res2, r10
  xor.f   r10, r1, r2
  mtf	  flg3
  mtr	  res3, r10
  bic.f   r10, r1, r2
  mtf	  flg4
  mtr	  res4, r10
.endm

.macro  test6, op1, op2, op3, res
  ; Tesing logical and arthimetic operations
  mov	  r1,  op1
  and	  r10, r1,  op2
  or	  r11, r10, op3
  add	  r12, r11, r10
  xor	  r13, r12, r11
  bic	  r14, r13, r12
  sub	  r15, r14, r10
  xor	  r2,  r15, r11
  mtr	  res, r2
.endm





; SHIFT tests - enabled only with shift_option arcpragma

.macro  test7, flags, op, res, flg
  flag    flags
  rrc.f   r10, op
  mtf	  flg
  mtr	  res, r10
.endm

.macro  test8, flags, op, res, flg
  flag    flags
  rlc.f   r10, op
  mtf	  flg
  mtr	  res, r10
.endm

.macro  test9, flags, op, res, flg
  flag    flags
  asl.f   r10, op
  mtf	  flg
  mtr	  res, r10
.endm

.macro  test10, flags, op, res, flg
  flag    flags
  lsr.f   r10, op
  mtf	  flg
  mtr	  res, r10
.endm

.macro  test11, flags, op, res, flg
  flag    flags
  asr.f   r10, op
  mtf	  flg
  mtr	  res, r10
.endm

; End of SHIFT tests.




.macro  test12, flags, res
  ; Test all condition codes
  flag	  flags
  mov	  r0,  0x00000000
  add.al  r0,  r0, 1
  add.eq  r0,  r0, 2
  add.ne  r0,  r0, 4
  add.pl  r0,  r0, 8
  add.mi  r0,  r0, 16
  add.cs  r0,  r0, 32
  add.cc  r0,  r0, 64
  add.vs  r0,  r0, 128
  add.vc  r0,  r0, 256
  add.gt  r0,  r0, 512
  add.ge  r0,  r0, 1024
  add.lt  r0,  r0, 2048
  add.le  r0,  r0, 4096
  add.hi  r0,  r0, 8192
  add.ls  r0,  r0, 16384
  add.pnz r0,  r0, 32768   ; Calculate unique value for condition code
  mtr	  res, r0
.endm

.macro  test13, flags, op1, op2, flg
  ;Tesing logical inst flag setting 
  mov	  r0,   op1
  flag    flags
  xor.f   0,    r0, op2
  mtf	  flg
.endm



.equ rf_32_entry,1

;==============================================================================
; Interrupt Vectors
;==============================================================================

.section    .vectors,text            ; Vector to start of code

reset:    .long     _start
mem_err:  .long     mem_err_handler
ins_err:  .long     ins_err_handler
ivector3: .long     vect3_routine
ivector4: .long     vect4_routine
ivector5: .long     vect5_routine
ivector6: .long     vect6_routine
ivector7: .long     vect7_routine

          nop     ; required nops to avoid 'x' in prefetch/decode
          nop
          nop
          nop
          nop
          nop

;===============================================================================
; Program Start
;===============================================================================
          .text                   ; Program code starts here
          .global _start

_start:
        mov     tsreg, 0x00000000 ; Clear the combined test status/number counter 

