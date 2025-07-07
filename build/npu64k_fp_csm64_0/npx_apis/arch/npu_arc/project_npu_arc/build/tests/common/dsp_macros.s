; *********************************
; Macros to be used in EM-DSP CCTs
; *********************************
.macro  mstop
  ; this macro covers all "mstop.cc"
;  add         tsreg, tsreg, 0x000001000     ; Add one to test count subfield
  b\&$suffix  FAIL                          ; If condition is true: branch to FAIL routine
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

; Macro to check accumulator high flags
.macro  mtf_ahi, expected_flag         ; Macro test accumulator high flag  
  lr        r27, [REG_AUX_DSP_ACC0_GHI]
  and       r27, r27, GVCNZ            ; mask flags
  rcmp      r27, expected_flag         ; Compare flags with expected flags 
  mstop.nz
.endm

; Macro to check accumulator low flags
.macro  mtf_alo, expected_flag         ; Macro test accumulator low flag  
  lr        r27, [REG_AUX_DSP_ACC0_GLO]
  and       r27, r27, GVCNZ            ; mask flags
  rcmp      r27, expected_flag         ; Compare flags with expected flags 
  mstop.nz
.endm

; Defines required to reference DSP Aux registers
; TODO : This list is incomplete

.equ     REG_AUX_DSP_ACC0_LO,  0x0000580
.equ     REG_AUX_DSP_ACC0_GLO, 0x0000581
.equ     REG_AUX_DSP_ACC0_HI,  0x0000582
.equ     REG_AUX_DSP_ACC0_GHI, 0x0000583
.equ     BIT_DSP_ACC_FLAG_Z,   16
.equ     BIT_DSP_ACC_FLAG_N,   17
.equ     BIT_DSP_ACC_FLAG_C,   18
.equ     BIT_DSP_ACC_FLAG_V,   19
.equ     BIT_DSP_ACC_FLAG_G,   20


.equ     REG_AUX_DSP_CTRL,     0x000059f
.equ     BIT_DSP_CTRL_SAT,     16

.equ     REG_AUX_DSP_BFLY,     0x0000598
.equ     REG_AUX_DSP_FFT_CTRL, 0x000059e

.equ   _____, 0x000000
.equ   ____Z, 0x010000
.equ   ___N_, 0x020000
.equ   ___NZ, 0x030000
.equ   __C__, 0x040000
.equ   __C_Z, 0x050000
.equ   __CN_, 0x060000
.equ   __CNZ, 0x070000
.equ   _V___, 0x080000
.equ   _V__Z, 0x090000
.equ   _V_N_, 0x0a0000
.equ   _V_NZ, 0x0b0000
.equ   _VC__, 0x0c0000
.equ   _VC_Z, 0x0d0000
.equ   _VCN_, 0x0e0000
.equ   _VCNZ, 0x0f0000
.equ   G____, 0x100000
.equ   G___Z, 0x110000
.equ   G__N_, 0x120000
.equ   G__NZ, 0x130000
.equ   G_C__, 0x140000
.equ   G_C_Z, 0x150000
.equ   G_CN_, 0x160000
.equ   G_CNZ, 0x170000
.equ   GV___, 0x180000
.equ   GV__Z, 0x190000
.equ   GV_N_, 0x1a0000
.equ   GV_NZ, 0x1b0000
.equ   GVC__, 0x1c0000
.equ   GVC_Z, 0x1d0000
.equ   GVCN_, 0x1e0000
.equ   GVCNZ, 0x1f0000

