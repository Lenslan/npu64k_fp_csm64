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
;;
;; This file contains the vector table for load store tests
;;
;; PLEASE READ - IMPORTANT NOTE
;; All instructions in this code are location sensitive
;; and you should not move the existing code in anyway.
;; the code may be extended by adding new instructions
;; after the final NOP instructions only.
;; 
;; ============================================================================

	.include macros.s
        .include test.s 
; ** make file inclusion conditional

.ifndef VECTORS_S
.equ    VECTORS_S, 0xABADCAFE

	.section .vectors, text           

; Reset vector (start of code)
;
reset_vector:   .long     _start

; Memory exception.
;
; Set z=0, fail on receipt.
;
mem_err:        .long     mem_err_handler

; Illegal instruction handler. 
;
ins_err:        .long     ins_err_handle              

; Exception vectors [3:13]
;
evec3:		.long	evec_handler
evec4: 		.long	evec_handler
evec5:		.long	evec_handler
evec6:		.long	evec_handler
evec7:		.long	evec_handler
evec8:		.long	evec_handler
evec9:		.long	evec_handler
evec10:		.long	evec_handler
evec11:		.long	evec_handler
evec12:		.long	evec_handler
evec13:		.long	evec_handler
;

; Unused vectors in the vector table [14:15]
emptvec14:	.long	emptvec_handler	
emptvec15:	.long	emptvec_handler
;
;
; Interrupt vectors [16:255]
;
ivec16:          .long     emptvec_handler
ivec17:          .long     emptvec_handler
ivec18:          .long     emptvec_handler
;
;
;			   Unused interrupts
ivec19:          .long     emptvec_handler
ivec20:          .long     emptvec_handler 
ivec21:          .long     emptvec_handler
ivec22:          .long     emptvec_handler
ivec23:          .long     emptvec_handler
ivec24:          .long     emptvec_handler
ivec25:          .long     emptvec_handler
ivec26:          .long     emptvec_handler
ivec27:          .long     emptvec_handler
ivec28:          .long     emptvec_handler
ivec29:          .long     emptvec_handler
ivec30:          .long     emptvec_handler
;
;
;
;
; Note that the following interrupts are not interrupt vectors, but used by the testbench to
; jump to interrupt test code.
;
irq_test:       .long     irq_test_code_l1
;
;
;
;
;
;ivec255: 	.long	   emptvec_handler       ;; To use all 240 interrupts, vector space in "common.map" 
						 ;; must be updated to accomodate all interrupts.
;
; End of Vector Table

            

; Pipeline flushing NOP's
; These Nops are used by hostmod (from v1.66) to flush the pipeline.
; (Hence the absolute address of the first NOP instruction is hard coded 
; within the pipeline flushing procedure)
        NOP
        NOP
        NOP
        NOP




.text


;Vector Handlers

mem_err_handler:
                flag    ____	; Z=0, fail on memory exception
                flag    H_BIT	;
                nop
                nop
                nop

ins_err_handle: 
		bne     fail
		nop

evec_handler:
		bne	fail
		nop

emptvec_handler:
		nop
		nop
		nop


.endif	; VECTORS_S
