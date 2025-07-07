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
;;       This file contains the macros that used in SLC verification.
;; ===========================================================================


; ------------------------------------------------------------
;  Get Cached Address
; ------------------------------------------------------------


 ; .set cached_region, 0
 ; .set cached_addr,   0

.macro get_cached_addr
 
.equ vol_disable, 0

.while ( 0 || \
( 7 == cached_region ) || \
( ( 15 >= cached_region) && ( 15 <= cached_region) && !(vol_disable)) || 0 )
.set cached_region, cached_region+1
.endw
.set cached_addr, cached_region << 28

.endm

