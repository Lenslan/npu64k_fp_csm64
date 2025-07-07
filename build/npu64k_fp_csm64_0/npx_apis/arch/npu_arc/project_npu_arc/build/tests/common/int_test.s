;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; *SYNOPSYS CONFIDENTIAL*
; 
; This is an unpublished, proprietary work of Synopsys, Inc., and is fully 
; protected under copyright and trade secret laws.  You may not view, use, 
; disclose, copy, or distribute this file or any information contained herein 
; except pursuant to a valid written license from Synopsys.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 
; This file contains the interrupt test code for coretest and testxalu
;
; It also contains the interrupt vectors
;  - except the illegal instruction exception handler.
;
; ** include file for condition names (needed for stop macro anyway?)
; ** modified flag instructions to use symbolic names

	.include macros.s

; ** make file inclusion conditional

.ifndef INT_TEST_S
.equ    INT_TEST_S, 0xABADCAFE

	.text
;; Code here is omitted unless the core supports 1k program sizes
;; Otherwise this overhead code itself exceeds 512B, the smallest CCM for v2.

ivic3_handler:
                mov     r0,0
                xor.f   0,ilink1,0xdeadbeef         ; check ilink1 /= deadbeef
                nop
                stop.z  0, CORE, ASSEMBLER, CORETEST, 0, FAILED                   
        
                mov     r0,3
                flag    ZZERO                               ; set zero flag
                flag    H_BIT
                nop
                nop
                nop

ivic4_handler:
                mov     r0,0                        ; int not yet successful
                xor.f   0,ilink1,0xdeadbeef         ; check ilink1 /= deadbeef
                nop
                stop.z  0, CORE, ASSEMBLER, CORETEST, 0, FAILED                   
        
                mov     r0,4                        ; interrupt successful
                flag    ZZERO                               ; set zero flag
                flag    H_BIT
                nop
                nop
                nop

ivic5_handler:
                mov     r0,0                        ; int not yet successful
                xor.f   0,ilink1,0xdeadbeef         ; check ilink1 /= deadbeef
                nop
                stop.z  0, CORE, ASSEMBLER, CORETEST, 0, FAILED                   
        
                mov     r0,5
                flag    ZZERO                               ; set zero flag
                flag    H_BIT
                nop
                nop
                nop

ivic6_handler:
                mov     r0,0                        ; int not yet successful
                xor.f   0,ilink2,0xdeadbeef         ; check ilink2 /= deadbeef
                nop
                stop.z  0, CORE, ASSEMBLER, CORETEST, 0, FAILED                   
        
                mov     r0,6
                flag    ZZERO                               ; set zero flag
                flag    H_BIT
                nop
                nop
                nop

ivic7_handler:
                mov     r0,0                        ; int not yet successful
                xor.f   0,ilink2,0xdeadbeef         ; check ilink2 /= deadbeef
                nop
                stop.z  0, CORE, ASSEMBLER, CORETEST, 0, FAILED                   
        
                mov     r0,7
                flag    ZZERO                               ; set zero flag
                flag    H_BIT
                nop
                nop
                nop

ilink_value:    .long       0xdeadbeef


;-----------------------------------------------------------------------

; Interrupt test code
;
; Keep looping until all the bits in the interrupt register have been
; set.
;
; This code is started from the testbench, which starts the ARC at
; irq_test_l1 (0x40).
;
; The code will fail if all the interrupts have not been received and
; serviced within 500 loops.
;
; ** link scoreboard: This code will continuously loop loading ilink1
; to ensure that link scoreboarding works correctly. It requires that
; the load delay is more than 1 (or 2?) cycles.
;


irq_test_code_l1:
                mov             lp_count,500
                mov             r0,ilink_value
                ld              ilink1,[r0]
                lp              itloop_end
                ld              ilink1,[r0]
                ld              ilink1,[r0]
itloop_end:
                stop            0, CORE, ASSEMBLER, CORETEST, 0, FAILED


irq_test_code_l2:
                mov             lp_count,500
                mov             r0,ilink_value
                ld              ilink2,[r0]
                lp              itloop_endl2
                ld              ilink2,[r0]
                ld              ilink2,[r0]
itloop_endl2:
                stop            0, CORE, ASSEMBLER, CORETEST, 0, FAILED



.endif	; INT_TEST_S
