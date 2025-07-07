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
;  Get Cached Region
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

; ------------------------------------------------------------
;         SLC Line Operations
; ------------------------------------------------------------

; Lock Line address in SLC
.macro slc_ldl, addr_lo, addr_hi

  .if (addrsize == 40)
    mov  dbg2_reg, addr_hi
    sr   dbg2_reg, [SLC_LDL_HI]
  .endif  

    mov  dbg1_reg, addr_lo
    sr   dbg1_reg, [SLC_LDL_LO]

    check_slc_bs

.endm

; Invalidate Line address in SLC
.macro slc_ivdl, addr_lo, addr_hi

  .if (addrsize == 40)
    mov   dbg2_reg, addr_hi
    sr    dbg2_reg, [SLC_IVDL_HI]
  .endif  

    mov   dbg1_reg, addr_lo
    sr    dbg1_reg, [SLC_IVDL_LO]

    check_slc_bs

.endm

; Flush Line address in SLC
.macro slc_fldl, addr_lo, addr_hi

  .if (addrsize == 40)
    mov   dbg2_reg, addr_hi
    sr    dbg2_reg, [SLC_FLDL_HI]
  .endif  

    mov   dbg1_reg, addr_lo
    sr    dbg1_reg, [SLC_FLDL_LO]

    check_slc_bs

.endm

; ------------------------------------------------------------
;         SLC Region Start and End
; ------------------------------------------------------------

; Write Region start address 
.macro slc_rgn_strt, addr_lo, addr_hi

  .if (addrsize == 40)
    mov   dbg2_reg, addr_hi
    sr    dbg2_reg, [SLC_RGN_STRT_HI]
  .endif  

    mov   dbg1_reg, addr_lo
    sr    dbg1_reg, [SLC_RGN_STRT_LO]

    check_slc_bs

.endm

; Write Region end address 
.macro slc_rgn_end, addr_lo, addr_hi

  .if (addrsize == 40)
    mov   dbg2_reg, addr_hi
    sr    dbg2_reg, [SLC_RGN_END_HI]
  .endif  

    mov   dbg1_reg, addr_lo
    sr    dbg1_reg, [SLC_RGN_END_LO]

.endm

; ------------------------------------------------------------
;         SLC Cache operations
; ------------------------------------------------------------

; SLC Flush
.macro slc_flush

    mov dbg1_reg, 0x1
    sr  dbg1_reg, [SLC_FLSH]
    check_slc_bs

.endm

; SLC Invalidate
.macro slc_invalidate, err_num   

    mov dbg1_reg, 0x1
    sr  dbg1_reg, [SLC_IVDC]
    ;check_slc_ivdc_bs err_num  
    check_slc_bs

.endm

; ------------------------------------------------------------
;         Macros related to functionality checks
; ------------------------------------------------------------

; SLC_CTRL.SB bit check ; Bit 2 which represents operation success
.macro check_slc_sb, err_num

    lr           dbg1_reg, [SLC_CTRL]
    btst         dbg1_reg, slc_ctrl_SB
    fail\&$suffix err_num

.endm

; Wait for Busy status bit in control register (for a valid flush).
; ------------------------------------------------------------------
; This macro checks the state of the SLC_CTRL.BS bit in the control register.
; If the bit is set, the code will loop until it is cleared.

.macro check_slc_bs 
    ; nopx 2
  1:
    lr           dbg1_reg, [SLC_CTRL]
    lr           dbg1_reg, [SLC_CTRL]
    btst         dbg1_reg, slc_ctrl_BS
    jnz          1b

.endm


; Check SLC_CTRL.BS bit after SLC invalidation.
; If CTRL.BS=1 means flush happend whcih should happen only CTRL.IM=1
; CTRL.BS=0 does not mean flush not happened. For ex : IF SLC has very few dirty lines and SLC_CTRL.IM=1, flush will occur immediately

.macro check_slc_ivdc_bs, err_num

    lr           dbg1_reg, [SLC_CTRL]
    btst         dbg1_reg, slc_ctrl_BS
    jnz          2f
  1:
    lr           dbg1_reg, [SLC_CTRL]
    btst         dbg1_reg, slc_ctrl_BS
    jnz          1b
    nop
    .exitm
  2:
    btst         dbg1_reg, slc_ctrl_IM
    fail.nz      err_num

.endm

; Rotate Left.
; .macro  rol, a, b
;     add.f        a, b, b
;     adc          a, a, 0
; .endm

; Set particular bit in SLC register.
.macro  slc_reg_bit_set, reg, bit_pos

    lr           dbg1_reg, [reg]
    bset         dbg1_reg, dbg1_reg, bit_pos
    sr           dbg1_reg, [reg]
    lr           dbg1_reg, [reg]

.endm

; Clear particular bit in SLC register.
.macro  slc_reg_bit_clear, bit_pos

    lr           dbg1_reg, [reg]
    bclr         dbg1_reg, dbg1_reg, bit_pos
    sr           dbg1_reg, [reg]

.endm

; Check a SLC  Register Value.
.macro  check_aux_reg, reg, exp_value, err_num

    lr           dbg1_reg, [reg]
    sub.f        0, dbg1_reg, exp_value
    fail.ne      err_num

.endm

; Perform multiple nop operations.
; --------------------------------
.macro  nopx, a
  .rep    a
    nop
  .endr
.endm

; Write SLC TAG register
;--------------------------------
.macro slc_write_tag, addr1_reg, addr2_reg, way, val

    mov          dbg1_reg, addr1_reg
    mov          dbg2_reg, addr2_reg

    mov          dbg3_reg, way  
  .if (slclinesize == 128)
    and          dbg1_reg, dbg1_reg, 0xFFFF_FF80
  .endif
  .if (slclinesize == 64)
    and          dbg1_reg, dbg1_reg, 0xFFFF_FFC0
  .endif
    asl          dbg3_reg, dbg3_reg, 0x2
    or           tag_reg, dbg1_reg, dbg3_reg

  .if (val == 1)
    bset         tag_reg, tag_reg, slc_tag_V
  .endif
  .if (addrsize == 40)
    sr           dbg2_reg, [SLC_TAG_HI]
  .endif
    sr           tag_reg, [SLC_TAG_LO]

.endm

; Write SLC STATUS register
;--------------------------------
.macro slc_write_status, lru, dirty, lk

  .if (slcways == 4)
    mov          dbg1_reg, lru
    and          status_reg, dbg1_reg, 0x7
  .endif  
  .if (slcways == 8)
    mov          dbg1_reg, lru
    and          status_reg, dbg1_reg, 0x7f
  .endif  
  .if (slcways == 16)
    mov          dbg1_reg, lru
    and          status_reg, dbg1_reg, 0x7fff 
  .endif  
    asl          status_reg, status_reg, 0x7
    mov          dirty_reg, dirty
    asl          dirty_reg, dirty_reg, 0x2
    or           status_reg, status_reg, dirty_reg
  .if (lk == 1)
    bset         status_reg, status_reg, slc_tag_LK
  .endif
    sr           status_reg, [SLC_STATUS]

.endm

; Prepare value that used to write into SLC direct access reg
;--------------------------------
.macro prepare_direct_access_reg, addr1_reg, rw, td, sd, dd, way

    mov          dbg2_reg, addr1_reg
    and          dbg1_reg, dbg2_reg, 0x0007_FFF0
    or           dbg1_reg, dbg1_reg, way
  .if (rw == 1)
    bset         dbg1_reg, dbg1_reg, slc_direct_RW 
  .endif  
  .if (td == 1)
    bset         dbg1_reg, dbg1_reg, slc_direct_TD
  .endif  
  .if (sd == 1)
    bset         dbg1_reg, dbg1_reg, slc_direct_SD
  .endif  
  .if (dd == 1)
    bset         dbg1_reg, dbg1_reg, slc_direct_DD
  .endif  
    mov          direct_access_reg, dbg1_reg

.endm

; check data present in the data rams using direct access
;----------------------------------------------------------------
.macro check_slc_data, direct_access_reg, data, error_num

    mov           data_reg, data
  .rep (slclinesize/16)                                     ; Read data from data rams. 

    sr            direct_access_reg, [SLC_DIRECT_ACCESS]     ; Write directe access reg after we perform write to tag, status and data regs
    check_slc_bs

    lr            dbg1_reg, [SLC_DATA0]
    sub.f         0, dbg1_reg, data_reg
    fail.nz       error_num
    asl           data_reg, data_reg, 0x1
    lr            dbg1_reg, [SLC_DATA1]
    sub.f         0, dbg1_reg, data_reg
    fail.nz       error_num
    asl           data_reg, data_reg, 0x1
    lr            dbg1_reg, [SLC_DATA2]
    sub.f         0, dbg1_reg, data_reg
    fail.nz       error_num
    asl           data_reg, data_reg, 0x1
    lr            dbg1_reg, [SLC_DATA3]
    sub.f         0, dbg1_reg, data_reg
    fail.nz       error_num

    add           direct_access_reg, direct_access_reg, 0x10 ; Increment the data bank index for each iteration
    asl           data_reg, data_reg, 0x1

  .endr

.endm

; Check the content of the SLC RAMs
;--------------------------------------------
.macro check_slc_line, addr1, addr2, data, rw, td, sd, dd, way, dirty, lk, val, lru

    mov          addr1_reg, addr1
    mov          addr2_reg, addr2

    lr            dbg1_reg, [SLC_CTRL]    ; Clear AT bit in slc_ctrl
    bclr          dbg1_reg, dbg1_reg, 5
    sr            dbg1_reg, [SLC_CTRL]

    prepare_direct_access_reg addr1_reg, rw, td, sd, dd, way
    sr            direct_access_reg, [SLC_DIRECT_ACCESS]
    check_slc_bs

    .set slc_ctrl_at_type, 0x0
    check_slc_rams addr1_reg, addr2_reg, direct_access_reg, data, way, dirty, lk, val, lru, slc_ctrl_at_type

.endm

.macro check_slc_rams, addr1_reg, addr2_reg, ram_addr_reg, data, way, dirty, lk, val, lru, slc_ctrl_at_type
    lr            tag_reg, [SLC_TAG_LO]
    btst          tag_reg, slc_tag_V  

  .if (val == 1)                       ; Check for valid bit
    fail.z        0x10
    .if (slclinesize == 128)           ; Check for tag and index values if the line is valid
      and         dbg1_reg, tag_reg, 0xFFFF_FF80
      and         dbg2_reg, addr1_reg, 0xFFFF_FF80
    .endif
    .if (slclinesize == 64)
      and         dbg1_reg, tag_reg, 0xFFFF_FFC0
      and         dbg2_reg, addr1_reg, 0xFFFF_FFC0
    .endif
    sub.f         0, dbg2_reg, dbg1_reg
    fail.nz       0x11

    .if (slc_ctrl_at_type == 0)
    check_slc_data ram_addr_reg, data, 0x12
    .endif
  .else
    fail.nz       0x13
  .endif

    ; Check STATUS reg fields
    lr            status_reg, [SLC_STATUS]
    btst          status_reg, slc_tag_LK       ; Check for lock bit.
  .if (lk == 1)  
    fail.z        0x14
  .else
    fail.nz       0x15
  .endif
    and           dbg2_reg, status_reg, 0x3c
    lsr           dbg2_reg, dbg2_reg, 0x2      ; Only dirty bits from SLC_TAG ; Right shift by 2

    mov           dbg3_reg, dirty  
  .if (slclinesize == 64)                      ; Mask the expected dirty bits based on slc line size
    and           dbg3_reg, dbg3_reg, 0x3
  .endif
    sub.f         0, dbg3_reg, dbg2_reg        ; Compare dirty bits of status register
    fail.nz       0x16

  ; Disable LRU check from this macro. If required, verify without this macro
 ;    mov           dbg3_reg, lru
 ;   lsr           dbg2_reg, status_reg, 0x7 
 ; .if (slcways == 4)
 ;   and           dbg3_reg, dbg3_reg, 0x7
 ;   and           dbg2_reg, dbg2_reg, 0x7
 ; .endif

 ; .if (slcways == 8)
 ;   and           dbg3_reg, dbg3_reg, 0x7f
 ;   and           dbg2_reg, dbg2_reg, 0x7f
 ; .endif
 ; 
 ; .if (slcways == 16)
 ;   and           dbg3_reg, dbg3_reg, 0x7fff
 ;   and           dbg2_reg, dbg2_reg, 0x7fff
 ; .endif
 ;   sub.f           0,dbg2_reg, dbg3_reg
 ;   fail.nz         0x16
  

  .if (val == 0)                               ; Stop checking SLC_TAG reg when valid is zero
    .exitm
  .endif
  .if (slc_ctrl_at_type == 0)
    ; Check SLC_TAG reg fields
    lr            tag_reg, [SLC_TAG_LO]
    and           dbg1_reg, tag_reg, 0x3c
    lsr           dbg1_reg, dbg1_reg, 0x2      ; Only way bits from SLC_TAG ; Right shift by 2

    mov           dbg3_reg, way  
    sub.f         0, dbg3_reg, dbg1_reg        ; Compare way bits of tag register
    fail.nz       0x17
  .endif

.endm

; Fill the slc rams using direct access.
;---------------------------------------------------
.macro fill_slc_line, addr1, addr2, data, rw, td, sd, dd, way, dirty, lk, val, lru
   
    mov           addr1_reg, addr1
    mov           addr2_reg, addr2

    lr            dbg1_reg, [SLC_CTRL] ; Clear AT bit in slc_ctrl
    bclr          dbg1_reg, dbg1_reg, 5
    sr            dbg1_reg, [SLC_CTRL]

    slc_write_tag    addr1_reg, addr2_reg, way, val         ; Write slc tag reg
    slc_write_status lru, dirty, lk                         ; Write slc status reg

    prepare_direct_access_reg addr1_reg, rw, td, sd, dd, way ; Prepare the value that used to write into SLC direct access reg

    mov           data_reg, data
  .rep (slclinesize/16)                                     ; Write data to the data rams. 

    sr            data_reg, [SLC_DATA0]
    asl           data_reg, data_reg, 0x1
    sr            data_reg, [SLC_DATA1]
    asl           data_reg, data_reg, 0x1
    sr            data_reg, [SLC_DATA2]
    asl           data_reg, data_reg, 0x1
    sr            data_reg, [SLC_DATA3]

    sr            direct_access_reg, [SLC_DIRECT_ACCESS]     ; Write directe access reg after we perform write to tag, status and data regs
    check_slc_bs
    add           direct_access_reg, direct_access_reg, 0x10 ; Increment the data bank index for each iteration
    asl           data_reg, data_reg, 0x1

  .endr
    
.endm

; Fill a line to main memory, bypassing the cache.
; ------------------------------------------------
; This macro loads a line into memory, bypassing the cache. The data
; is simply rotated for each lword in the line.
; Arguments can be reg or limmdata
;
.macro  fill_mem_line, addr_reg, data_reg
    mov          dbg1_reg, addr_reg
    mov          dbg2_reg, data_reg
    mov          dbg3_reg, slclinesize_reg
    st\&$suffix  dbg2_reg, [dbg1_reg]
    sub.f        dbg3_reg, dbg3_reg, 0x4
1:
    asl          dbg2_reg, dbg2_reg 
    st.a\&$suffix dbg2_reg, [dbg1_reg, 4]
    sub.f        dbg3_reg, dbg3_reg, 0x4
    jnz          1b

    sync


.endm


; Check A line was flushed.
; -------------------------
; This macro checks that a line exists in main memory after a flush
; operation.
;
    .macro  check_mem_line, addr_reg, data_reg, error_num

; Initialise the line counter.
;
    mov          dbg1_reg, data_reg
    mov          dbg2_reg, addr_reg
    mov          dbg3_reg, slclinesize_reg

3:; Load the data direct from memory.
;
    ld\&$suffix  dbg4_reg, [dbg2_reg]

; Check that the data is correct.
;
    cmp          dbg4_reg, dbg1_reg
    fail.nz      error_num

; Set up the data and address for the next lword in the line.
;
    asl          dbg1_reg, dbg1_reg  ; the data
    add          dbg2_reg, dbg2_reg, 0x4 ; the addr

; Repeat for every lword in the line.
;
    sub.f        dbg3_reg, dbg3_reg, 0x4
    bnz          3b

    sync

.endm

.macro check_slc_line_exists, addr1, addr2, data, way, dirty, lk, val, lru
    slc_reg_bit_set SLC_CTRL, slc_ctrl_AT
    .set slc_ctrl_at_type, 0x1

    mov          addr1_reg, addr1
    mov          addr2_reg, addr2

  .if (addrsize == 40)
    sr           addr2_reg, [SLC_RAM_ADDR_HI]
  .endif
    sr           addr1_reg, [SLC_RAM_ADDR_LO]
    check_slc_bs

    check_slc_rams addr1_reg, addr2_reg, addr1_reg, data, way, dirty, lk, val, lru, slc_ctrl_at_type

.endm


; Update Error Code Register and Clear ZERO Flag and Halt the ARCompact
; ---------------------------------------------------------------------
    .macro  fail, error_num

; Branch to flag code if condition true.
;
    b\&$suffix  1f
    nop

; Jump to end of stop macro if false.
;
    bal 2f

1:
; Update the error code to reflect the error number that failed.
;
;    mov test_status_reg,  test_fail_code
;    mov err_num_Reg, error_num
;    add error_code_reg, error_code_reg, error_num*test_num_offset

     flag    0
     mov TEST_STATUS_REG, TEST_FAIL
     mov ERR_NUM, error_num	  
     jal failed

2:
; Stop expanding macro if condition is false
   .exitm
    .endm

