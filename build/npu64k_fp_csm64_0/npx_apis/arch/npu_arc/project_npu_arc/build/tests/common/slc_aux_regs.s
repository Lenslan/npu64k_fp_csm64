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
;;  Project     : TigerShark
;; Description:
;;          This file contains the aux registers used in L2 cache verification along with their permissions
;;  
;; ===========================================================================
;
;
;-----------------------------------------------------------------------
; Definitions of Auxiliary registers used by the L2 cache to allow the 
; software tools to display the register contents during debug sessions:
;
; L2 cache ID register.
;--------------------------------------
    .extAuxRegister SLC_ID, 0x900, r

; L2 cache CONFIG register.
;--------------------------------------
    .extAuxRegister SLC_CONFIG, 0x901, r

; L2 cache CTRL register.
;--------------------------------------
    .extAuxRegister SLC_CTRL, 0x903, r|w

; L2 cache Flush register.
;--------------------------------------
    .extAuxRegister SLC_FLSH, 0x904, w

; L2 cache Invalidation register.
;--------------------------------------
    .extAuxRegister SLC_IVDC, 0x905, w

; L2 cache Line Lock registers.
;--------------------------------------
    .extAuxRegister SLC_LDL_LO, 0x90E, w
    .extAuxRegister SLC_LDL_HI, 0x90F, w

; L2 cache Line Invalidate registers.
;--------------------------------------
    .extAuxRegister SLC_IVDL_LO, 0x910, w
    .extAuxRegister SLC_IVDL_HI, 0x911, w

; L2 cache Line Flush registers.
;--------------------------------------
    .extAuxRegister SLC_FLDL_LO, 0x912, w
    .extAuxRegister SLC_FLDL_HI, 0x913, w


; L2 cache Region Start registers.
;--------------------------------------
    .extAuxRegister SLC_RGN_STRT_LO, 0x914, w
    .extAuxRegister SLC_RGN_STRT_HI, 0x915, w

; L2 cache Region End registers.
;--------------------------------------
    .extAuxRegister SLC_RGN_END_LO, 0x916, w
    .extAuxRegister SLC_RGN_END_HI, 0x917, w


; L2 cache RAM ADDR registers.
;--------------------------------------
    .extAuxRegister SLC_RAM_ADDR_LO, 0x918, w
    .extAuxRegister SLC_RAM_ADDR_HI, 0x919, w

; L2 cache Direct Access registers.
;--------------------------------------
    .extAuxRegister SLC_DIRECT_ACCESS, 0x91A, w

; L2 cache TAG registers.
;--------------------------------------
    .extAuxRegister SLC_TAG_LO, 0x91B, r|w
    .extAuxRegister SLC_TAG_HI, 0x91C, r|w


; L2 cache STATUS register.
;--------------------------------------
    .extAuxRegister SLC_STATUS, 0x91D, r|w

; L2 cache Data registers.
;--------------------------------------
    .extAuxRegister SLC_DATA0, 0x91F, r|w
    .extAuxRegister SLC_DATA1, 0x920, r|w
    .extAuxRegister SLC_DATA2, 0x921, r|w
    .extAuxRegister SLC_DATA3, 0x922, r|w

; L2 cache FAULT ADDR registers.
;--------------------------------------
    .extAuxRegister SLC_FAULT_ADDR_LO, 0x923, r
    .extAuxRegister SLC_FAULT_ADDR_HI, 0x924, r

; L2 cache FAULT STATUS register.
;--------------------------------------
    .extAuxRegister SLC_FAULT_STATUS, 0x925, r|w

; L2 cache PMU CMD register.
;--------------------------------------
    .extAuxRegister SLC_PMU_CMD, 0x926, r|w

; L2 cache PMU EVENT ENABLE register.
;--------------------------------------
    .extAuxRegister SLC_PMU_EVT_EN, 0x927, r

; L2 cache PMU Counter Overflow register.
;--------------------------------------
    .extAuxRegister SLC_PMU_CNT_OV, 0x928, r|w

; L2 cache PMU Event Counter register.
;--------------------------------------
    .extAuxRegister SLC_PMU_EVT_CNT_LO, 0x929, r|w
    .extAuxRegister SLC_PMU_EVT_CNT_HI, 0x92a, r|w

; L2 cache Debug and Trace register.
;--------------------------------------
    .extAuxRegister SLC_DBG_TRC, 0x92c, r|w


