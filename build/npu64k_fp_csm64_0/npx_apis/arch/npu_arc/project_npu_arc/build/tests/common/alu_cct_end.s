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
;;    Macros file for ALU tests
;;  
;; ============================================================================

success:
        mov     tsreg, 0|CORE|ASSEMBLER|0|CORETEST|PASSED
        nop
        nop
        nop
        flag    H_BIT + Z___    ; zero and halt bits set
        nops    5

failure:
        or      tsreg, tsreg, 0|CORE|ASSEMBLER|0|CORETEST|FAILED
        nop
        nop
        nop
        flag    H_BIT + Z___    ; zero and halt bits set
        nop
        nop
        nop

;==============================================================================
; Interrupt service routines
;==============================================================================

mem_err_handler:
ins_err_handler:
vect3_routine:
vect4_routine:  
vect5_routine:
vect6_routine:
vect7_routine: 
                ; A zero test number indicates the test failed here
        mov     tsreg, 0|CORE|ASSEMBLER|0|CORETEST|FAILED
        nop
        nop
        nop
        flag    H_BIT + Z___    ; zero and halt bits set1  
        nop
        nop
        nop

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
;;  
;; ============================================================================




