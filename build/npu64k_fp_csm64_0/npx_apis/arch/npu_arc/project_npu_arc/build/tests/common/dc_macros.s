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
;;     Macros file for data cache tests
;;  
;; ============================================================================


  .macro lsr_multi, register, position
   add     fn1_reg, position       ;   Number of bits to shift right
repeat:
   sub.f   fn1_reg, r1, r1, 1      ;   Subtract one
   bne.d   repeat                  ;   Repeat if not zero  
   lsr     register,register       ;   Execute lsr in BDS
  .endm



; Unlock (invalidate) a Cache Line.
; ---------------------------------
    .macro  ivdl, line
    sr  line, [DC_IVDL]
    .endm

; Lock a Cache Line.
; ------------------
    .macro  ldl, line
    sr  line, [DC_LDL]
    .endm

; Invalidate the cache only.
; --------------------------
    .macro  ivdc
    sr  0x1, [DC_IVDC]
    .endm

; Invalidate the cache and check the flush status bit.
; ----------------------------------------------------
    .macro  ivdc_fs, error_num
    ivdc
    lr  fn_reg, [DC_CTRL]
    tst fn_reg, dc_ctrl_FS
    bz  2f
1:  lr  fn_reg, [DC_CTRL]
    tst fn_reg, dc_ctrl_FS
    bnz 1b
    nop
    b   3f
2:
    tst fn_reg, dc_ctrl_IM
    fail.nz error_num   ; <- fail if FS=0 straight after a flsh op
3:
    .endm

; Check flush status bit in control register (for a valid flush).
; ---------------------------------------------------------------
; This macro checks the state of the fs bit in the control register
; and fails if the fs bit=0 when it is first read. If the bit is
; stuck at zero, the code will get stuck in this checking loop.
;
    .macro  chk_fs, error_num
    lr  fn_reg, [DC_CTRL]
    tst fn_reg, dc_ctrl_FS
    fail.z  error_num   ; <- fail if FS=0 straight after a flsh op
1:  lr  fn_reg, [DC_CTRL]
    tst fn_reg, dc_ctrl_FS
    bnz 1b
    .endm

; Wait for flush status bit in control register (for a valid flush).
; ------------------------------------------------------------------
; This macro checks the state of the fs bit in the control register.
; If the bit is set, the code will loop until it is cleared.
;
    .macro  check_fs
1:  lr  fn_reg, [DC_CTRL]
    tst fn_reg, dc_ctrl_FS
    bnz 1b
    .endm

; Check flush status bit in control register (no flush).
; ------------------------------------------------------------------
; This macro checks the state of the fs bit in the control register
; and fails if the fs bit=1 two cycles after the flush operation 
; occurred.
;
    .macro  chk_no_fs, error_num
    lr  fn_reg, [DC_CTRL]
    tst fn_reg, dc_ctrl_FS
    fail.nz error_num   ; <- fail if FS=1 straight after a flsh op
    lr  fn_reg, [DC_CTRL]
    tst fn_reg, dc_ctrl_FS
    fail.nz error_num
    .endm

; Flush the cache.
; ----------------
    .macro  flsh_fs, error_num
    sr  0x1, [DC_FLSH]
    check_fs; chk_fs  error_num
    .endm

; Flush the cache only.
; ---------------------
    .macro  flsh
    sr  0x1, [DC_FLSH]
    .endm

; Flush a Cache Line.
; -------------------
    .macro  fldl, line
    sr  line, [DC_FLDL]
    .endm

; Flush a Cache Region.
; -------------------
    .macro  flshr, startr, endr
       sr endr,   [DC_ENDR]
       sr startr, [DC_STARTR]
    .endm

; Flush a Cache Region and check fs status.
; -------------------
    .macro  flshr_sb, startr, endr, error_num
       sr endr,   [DC_ENDR]
       sr startr, [DC_STARTR]
       chk_sb_true error_num
    .endm

; Perform multiple nop operations.
; --------------------------------
    .macro  nopx, a
    .rep    a
    nop
    .endr
    .endm

; Rotate Left.
; ------------
    .macro  rol, a, b
    add.f   a, b, b
    adc a, a, 0
    .endm

; Update Cache Reg. bit position with 1.
; --------------------------------------
    .macro  update_reg_1, reg, bit_pos
    lr  fn_reg, [reg]
    or  fn_reg, fn_reg, bit_pos
    sr  fn_reg, [reg]
    .endm

; Update Cache Reg. bit position with 0.
; --------------------------------------
    .macro  update_reg_0, reg, bit_pos
    lr  fn_reg, [reg]
    bic fn_reg, fn_reg, bit_pos
    sr  fn_reg, [reg]
    .endm

; Disable the Cache.
; ------------------
    .macro  dc_disable
    update_reg_1    DC_CTRL, dc_ctrl_DC
    .endm

; Enable the Cache.
; -----------------
    .macro  dc_enable
    update_reg_0    DC_CTRL, dc_ctrl_DC
    .endm

; Enable Bypass Mode.
; -------------------
    .macro  enable_bypass
    update_reg_1    DC_CTRL, dc_ctrl_EB
    .endm

; Disable Bypass Mode.
; --------------------
    .macro  disable_bypass
    update_reg_0    DC_CTRL, dc_ctrl_EB
    .endm

; Random Replacement Algorithm Enabled.
; -------------------------------------
    .macro  roundrobin_wp
    update_reg_1    DC_CTRL, dc_ctrl_RA0
    lr  macro_reg, [DC_CTRL]
    tst macro_reg, dc_ctrl_RA1
    fail.nz 0x3255434
    tst macro_reg, dc_ctrl_RA0
    fail.z  0x32455434
    .endm

; Round Robin Replacement Algorithm Disabled.
; -------------------------------------------
    .macro  random_wp
    update_reg_0    DC_CTRL, dc_ctrl_RA
    lr  macro_reg, [DC_CTRL]
    tst macro_reg, dc_ctrl_RA1
    fail.nz 0x4554534
    tst macro_reg, dc_ctrl_RA0
    fail.nz 0x54534
    .endm

; Enable Cache Controlled RAM Access Mode.
; ----------------------------------------
    .macro  cache_access
    update_reg_1    DC_CTRL, dc_ctrl_AT
    .endm

; Enable Direct Cache RAM Access Mode.
; ------------------------------------
    .macro  direct_access
    update_reg_0    DC_CTRL, dc_ctrl_AT
    .endm

; Invalidate and Flush mode.
; --------------------------
    .macro  set_IM_1
    update_reg_1    DC_CTRL, dc_ctrl_IM
    .endm

; Invalidate Only Mode.
; ---------------------
    .macro  set_IM_0
    update_reg_0    DC_CTRL, dc_ctrl_IM
    .endm

; Flush locked lines mode.
; ------------------------
    .macro  set_LM_1
    update_reg_1    DC_CTRL, dc_ctrl_LM
    .endm

; Don't Flush Locked Lines Mode.
; ------------------------------
    .macro  set_LM_0
    update_reg_0    DC_CTRL, dc_ctrl_LM
    .endm

; Check a Cache Register Value.
; -----------------------------
    .macro  chk_aux_reg, reg, value, error_num
    lr  fn_reg, [reg]
    cmp fn_reg, value
    fail.ne error_num
    .endm

; Update Test Number
; ------------------
    .macro  update_test_num, test

    mov error_code_reg, fail_code
    add error_code_reg, error_code_reg, test*test_num_offset

    .endm

; Get a way pointer value for an address in cache.
; ------------------------------------------------
; This macro returns the way of a system address in the cache.
;
    .macro  get_way, addrreg, wpreg

    cache_access
    sr  addrreg, [DC_RAM_ADDR]
    lr  wpreg, [DC_WP]

; Check the success bit.
;
    lr  macro_reg, [DC_CTRL]
    tst macro_reg, dc_ctrl_SB
    bnz 1f  ; Branch if the SB is set.

; There is no tag match if this point is reached.
;
    cmp 0, 1    ; clear the zero flag
    b   2f

1:; There is a tag match, set the zero flag.
;
    cmp 0, 0    ; set the zero flag

2:; End of macro.

    .endm

; Convert a System memory address to a direct cache address.
; ----------------------------------------------------------
; This macro constructs a physical address from the system address 
; given (addr_reg). The tag value is discarded. The way pointer (wp_reg)
; is added to the final address to form a physical cache address.
;
    .macro  conv_sys2cache, addrreg, wpreg

; Mask off the Tag field from the address.
;
    bic addrreg, addrreg, tag_mask

; Concatenate the way pointer with the address.
;
    mov fn_reg, wpreg
    cmp fn_reg, 0
    bz  2f
1:
    add addrreg, addrreg, dcwaysize
    sub.f   fn_reg, fn_reg, 0x1
    bnz 1b
2:

    .endm

; Check a Tag Flag value.
; -----------------------
; This macro checks the value of a tag flag value.
;
    .macro  chk_tag, addrreg, flag_bit
    sr  addrreg, [DC_RAM_ADDR]
    lr  fn_reg, [DC_TAG]
    and.f   fn_reg, fn_reg, flag_bit
    .endm

; Fill a cache Line.
; ------------------
; This macro manually fills a cache line into the way specified 
; (wp_reg). The system address (addr_reg) is converted into a physical
; address pointing to a specific way (wp_reg). The tag is obtained by
; merging the system address with the dirty, lock and valid bits 
; (dlv_reg). The data is then sequentially entered into the line with
; a rotating data pattern (data_reg).
; Unlike a cache operation, this macro does not update the way pointer
; and does not check that the entry is in the cache.
;
    .macro  fill_line, addrreg, datareg, dlvreg, wpreg

    direct_access

; Initialise the line counter.
;
    mov line_reg, dclinesize_reg

; Obtain the physical address for the line from the system address
; and update the cache ram address with the new value.
;
    mov macro_reg, addrreg
    mov macro1_reg, addrreg
    conv_sys2cache  macro1_reg, wpreg
    sr  macro1_reg, [DC_RAM_ADDR]

; Set up the tag for this line.
; Mask off the tag field from the system address and add the tag
; flags to form a tag entry.
;
    and macro_reg, macro_reg, tag_mask
    add macro_reg, macro_reg, dlvreg
    sr  macro_reg, [DC_TAG]

    mov macro2_reg, datareg

1:; Fill the line with a rotating data pattern.
;
    sr  macro2_reg, [DC_DATA]
    rol macro2_reg, macro2_reg
    add macro1_reg, macro1_reg, 4
    sr  macro1_reg, [DC_RAM_ADDR]
    sub.f   line_reg, line_reg, 4
    bnz 1b

    .endm

; Check A line was flushed.
; -------------------------
; This macro checks that a line exists in main memory after a flush
; operation.
;
    .macro  chk_mem_line, addrreg, datareg, error_num

; Initialise the line counter.
;
    mov line_reg, dclinesize_reg
    mov macro1_reg, datareg
    mov macro2_reg, addrreg

3:; Load the data direct from memory.
;
    ld.di   macro_reg, [macro2_reg]

; Check that the data is correct.
;
    cmp macro_reg, macro1_reg
    fail.nz error_num

; Set up the data and address for the next lword in the line.
;
    rol macro1_reg, macro1_reg  ; the data
    add macro2_reg, macro2_reg, 0x4 ; the addr

; Repeat for every lword in the line.
;
    sub.f   line_reg, line_reg, 0x4
    bnz 3b

    .endm

; Check the current cache line is locked.
; ---------------------------------------
; This macro checks the line that the address maps to is locked.
; The actual address depends on the access debug type (AT) in the
; Control register. The macro assumes that the line is actually in 
; the cache and is valid.
;
    .macro  chk_line_locked, addrreg, error_num
    cache_access
    sr  addrreg, [DC_RAM_ADDR]
    lr  macro_reg, [DC_TAG]
    chk_sb_true error_num
    tst macro_reg, dc_tag_L
    fail.z  error_num
    .endm
    .macro  chk_line_locked_false, addrreg, error_num
    cache_access
    sr  addrreg, [DC_RAM_ADDR]
    lr  macro_reg, [DC_TAG]
    chk_sb_true error_num
    tst macro_reg, dc_tag_L
    fail.nz  error_num
    .endm

; Check the current cache line is Dirty.
; --------------------------------------
; This macro checks the line that the address maps to is dirty.
; The macro assumes that the line is actually in the cache and is 
; valid.
;
    .macro  chk_line_dirty, addrreg, error_num
    cache_access
    sr  addrreg, [DC_RAM_ADDR]
    lr  macro_reg, [DC_TAG]
    chk_sb_true error_num
    tst macro_reg, dc_tag_DT
    fail.z  error_num
    .endm


    .macro  chk_line_dirty_false, addrreg, error_num
    cache_access
    sr  addrreg, [DC_RAM_ADDR]
    lr  macro_reg, [DC_TAG]
    chk_sb_true error_num
    tst macro_reg, dc_tag_DT
    fail.nz  error_num
    .endm

    .macro  chk_line_valid, addrreg, error_num
    cache_access
    sr  addrreg, [DC_RAM_ADDR]
    lr  macro_reg, [DC_TAG]
    chk_sb_true error_num
    tst macro_reg, dc_tag_V
    fail.z  error_num
    .endm

    .macro  chk_line_valid_false, addrreg, error_num
    cache_access
    sr  addrreg, [DC_RAM_ADDR]
    lr  macro_reg, [DC_TAG]
    chk_sb_false error_num
    tst macro_reg, dc_tag_V
    fail.nz  error_num
    .endm

    .macro  chk_vlineinvalidation, addrreg, error_num
    direct_access
    sr  addrreg, [DC_RAM_ADDR]
    lr  macro_reg, [DC_TAG]
    tst macro_reg, dc_tag_V
    fail.nz  error_num
    .endm
    .macro  chk_dlineinvalidation, addrreg, error_num
    direct_access
    sr  addrreg, [DC_RAM_ADDR]
    lr  macro_reg, [DC_TAG]
    tst macro_reg, dc_tag_DT
    fail.nz  error_num
    .endm
    .macro  chk_llineinvalidation, addrreg, error_num
    direct_access
    sr  addrreg, [DC_RAM_ADDR]
    lr  macro_reg, [DC_TAG]
    tst macro_reg, dc_tag_L
    fail.nz  error_num
    .endm

; Check the current cache line is loaded.
; ---------------------------------------
; This macro can only be executed when cache RAM access mode is
; enabled. It assumes that the line is in the cache and valid and 
; checks that the data is correct in the line. The address should
; be aligned to a line boundary.
;
    .macro  chk_line, addrreg, datareg, error_num
    cache_access
    mov line_reg, dclinesize_reg
    mov macro_reg, addrreg
    mov macro1_reg, datareg
3:
    sr  macro_reg, [DC_RAM_ADDR]
    lr  macro2_reg, [DC_DATA]
    chk_sb_true error_num
    cmp macro2_reg, macro1_reg
    fail.nz error_num

; Repeat for each lword in the line.
;
    rol macro1_reg, macro1_reg
    add macro_reg, macro_reg, 0x4
    sub.f   line_reg, line_reg, 0x4
    bnz 3b
    .endm

; Load a line to main memory, bypassing the cache.
; ------------------------------------------------
; This macro loads a line into memory, bypassing the cache. The data
; is simply rotated for each lword in the line.
;
    .macro  load_mem_line, addrreg, datareg
    mov macro_reg, addrreg
    mov macro1_reg, datareg
    mov line_reg, dclinesize_reg
    st.di   macro1_reg, [macro_reg]
    sub.f   line_reg, line_reg, 0x4
1:
    rol macro1_reg, macro1_reg
    st.a.di macro1_reg, [macro_reg, 4]
    sub.f   line_reg, line_reg, 0x4
    bnz 1b
    .endm

; Caclulate the next free way pointer value.
; ------------------------------------------
; This macro returns the next way pointer value for a particular
; set based upon a cache hit or miss. The value in wp_reg is the 
; current way pointer value, which is overwritten with the calculated 
; value.
;
    .macro  calc_wp, ramaddr, wpreg

; Set up registers for this macro.
;
    mov macro_reg, ramaddr
    mov macro1_reg, dcways

3:; Point to the next way in the set and determine if the entry is
; unlocked or not.
;
    add wpreg, wpreg, 1
    and wpreg, wpreg, wp_mask
    conv_sys2cache  macro_reg, wpreg
    direct_access
    sr  macro_reg, [DC_RAM_ADDR]
    lr  macro2_reg, [DC_TAG]

; Exit the loop if the way is unlocked.
;
    tst macro2_reg, dc_tag_L
    bz  4f
    sub.f   macro1_reg, macro1_reg, 1
    bnz 3b

; If this section is reached, the whole set is locked.
; Reset the way pointer to zero.
;
    mov wpreg, 0x0

4:; End of macro.

    .endm

; Halt ARCompact & Set ZERO Flag Accordingly.
; -------------------------------------------
    .macro  stop, a
    nop

; Branch to flag code if condition true.
;
    b\&$suffix  1f

; Jump to end of stop macro if false.
;
    bal 2f
1:
    flag    (a&Z_BIT)
    flag    H_BIT
2:
    .endm

; Check the Success bit in the ctrl register.
; -------------------------------------------
    .macro  chk_sb_true, error_num
    lr  fn_reg, [DC_CTRL]
    tst fn_reg, dc_ctrl_SB
    fail.z  error_num
    .endm
    .macro  chk_lk_true, error_num
    lr  fn_reg, [DC_TAG]
    tst fn_reg, dc_tag_L
    fail.z  error_num
    .endm
    .macro  chk_lk_false, error_num
    lr  fn_reg, [DC_TAG]
    tst fn_reg, dc_tag_L
    fail.nz  error_num
    .endm


; Check the Success bit in the ctrl register.
; -------------------------------------------
    .macro  chk_sb_false, error_num
    lr  fn_reg, [DC_CTRL]
    tst fn_reg, dc_ctrl_SB
    fail.nz error_num
    .endm

; Increment an Auxiliary Register to the next line.
; -------------------------------------------------
; this macro increments an auxiliary register by the supplied 
; increment.
;
    .macro  incr_aux_reg, reg, incr
    lr  fn_reg, [reg]
    add fn_reg, fn_reg, incr
    sr  fn_reg, [reg]
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
;    mov error_reg, error_num
;    mov error_code_reg, fail_code
;    add error_code_reg, error_code_reg, error_num*test_num_offset

     flag    0

     mov r20, fail_code
     mov r20, TEST_FAIL
     add r20, r20, error_num*test_num_offset	  
     st.di r20, [TEST_STATUS_ADDRESS]	
     jal failed


2:

;; Branch to flag code if condition true.
;;
;    b\&$suffix  1f
;    nop
;
;; Jump to end of stop macro if false.
;
;    bal 2f
;1:
; Update the error code to reflect the error number that failed.
;
;    mov error_reg, error_num
;    mov error_code_reg, fail_code
;    add error_code_reg, error_code_reg, error_num*test_num_offset
;
;    flag    0
;    flag    H_BIT
;
;2:
    .endm

;-----------------------------------------------------------------------
;   compute a distinct pattern based on r0 (way), r1(line), r2(word)    
;   and store it in reg
;-----------------------------------------------------------------------
    .macro  create_pattern, reg
    add reg, MEM_PTR, 0 ;   move MEM_PTR to reg
    .endm
;-----------------------------------------------------------------------

    .macro  usermode
    trap_s  1
    .endm

    .macro  kernelmode
    trap_s  2
    .endm
    .macro  set_SB_1
    update_reg_1    DC_CTRL, dc_ctrl_SB
    .endm

;the macro is used only for dccm
    .macro  chk_line_dccm, addrreg, datareg, error_num
    cache_access
    mov line_reg, dclinesize_reg
    mov macro_reg, addrreg
    mov macro1_reg, datareg
3:
    sr  macro_reg, [DC_RAM_ADDR]
    chk_sb_true error_num  
    lr  macro2_reg, [DC_DATA]
    cmp macro2_reg, macro1_reg
    fail.z error_num

; Repeat for each lword in the line.
;
    rol macro1_reg, macro1_reg
    add macro_reg, macro_reg, 0x4
    sub.f   line_reg, line_reg, 0x4
    bnz 3b
    .endm


