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
;; Register r26 (GP) : contains the fields required to describe the
;; error....
;;

;;register r26=32 bits
;;
;;  0000.0000.0000.0000.0000.0000.0000.0000
;;  -+-- -+-- ------+------- ----+---- -+--
;;   |    |         |            |      |
;;   |    |         |            |      +--> Error definition 
;;   |    |         |            |
;;   |    |         |            +---------> Part under test
;;   |    |         |
;;   |    |         +----------------------> Part test number
;;   |    |
;;   |    +--------------------------------> Test system
;;   |
;;   +-------------------------------------> Responsible department
;;
;;
;;  
;; ============================================================================


.ifndef CODE_S
.equ    CODE_S, 0xABADCAFE

; Error definition: (3-0)
; ----------------
;    1 : passed
;    2 : warning
;    3 : failed

.equ PASSED,     0x00000001
.equ WARNING,    0x00000002
.equ FAILED,     0x00000003

; Part under test: (11-4)
; ---------------
.equ ALL,        0x00000010

; CORE
; ----
.equ CORETEST,   0x00000020
.equ RASCTEST,   0x00000030
.equ BRK,        0x00000040
.equ CONFIG_REG, 0x00000050
.equ SLEEP,      0x00000060
.equ INST_STEP,  0x00000070
.equ LINK,       0x00000080
.equ PORTED,     0x00000090
.equ MPU,        0x000000A0
.equ DHRY,       0x000000B0
.equ QUEENS,     0x000000C0
.equ FFT,        0x000000D0
.equ PMU,        0x00000100
    
; SYS_ENG
; -------
.equ SWAP,       0x00000020
.equ MUL64,      0x00000030
.equ SHIFT,      0x00000050
.equ MINMAX,     0x00000060
.equ LDSTRAM,    0x00000070
.equ TIMER,      0x00000080
.equ ACTIONPT1,  0x00000090
.equ ACTIONPT2,  0x000000A0
.equ MWIC1,      0x000000B0
.equ MWIC2,      0x000000C0
.equ MWIC3,      0x000000D0
.equ MADI,       0x000000E0
.equ DMCC,       0x000000F0
.equ JTAG,       0x00000100
.equ PCPORT,     0x00000200
.equ MWDC,       0x00000300
.equ HARVARD,    0x00000400
.equ BIGENDIAN,  0x00000500
.equ SmaRT,      0x00000600
.equ DPFPfast,   0x00000700
.equ DPFPcompact,   0x00000800
.equ SPFPfast,   0x00000900
.equ SPFPcompact,   0x00000A00
.equ tutorial_shift4bit, 0x00000B00
.equ tutorial_simd, 0x00000C00

; All user extensions (EIA)
; -------------------------
.equ USEREXT,     0x00000FF0


; Test System: (27-24)
; -----------
;    1 : assembler ARC
;    2 : C/C++ 
;    3 : VHDL TB
;    4 : Verilog TB
;    5 : Unix scripts
;    6 : NT/DOS scripts

.equ ASSEMBLER,  0x01000000
.equ CPLUSPLUS,  0x02000000
.equ VHDL,       0x03000000
.equ VERILOG,    0x04000000
.equ UNIX,       0x05000000
.equ WINDOWS,    0x06000000
 
; Responsible Department: (31-28)
; ----------------
;    1 : Core
;    2 : DSP
;    3 : System eng
;    4 : EDA
;    5 : Software
;    6 : System int
;    7 : Market eng
;    8 : Peripheral

.equ CORE,       0x10000000
.equ DSP,        0x20000000
.equ SYS_ENG,    0x30000000
.equ EDA,        0x40000000
.equ SOFTWARE,   0x50000000
.equ SYS_INT,    0x60000000
.equ MARKET,     0x70000000
.equ PERIPHERAL, 0x80000000

.equ CUSTOMER,   0xF0000000
.equ VECBASE_MASK, 0xfffffc00
.equ VECBASE_AC_BUILD, 0x68       
.endif                           ;CODE_S
