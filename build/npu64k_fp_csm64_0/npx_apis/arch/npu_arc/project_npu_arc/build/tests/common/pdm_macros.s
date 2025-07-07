.ifndef ARCv2HS_PDM_MACROS_INCLUDED
; *********************************
; Macros to be used in HS-PDM CCTs
; *********************************

; Defines for PDM registers
.equ      PDM_DVFS_BUILD,    0x0f7   
.equ      PDM_PSTAT,		 0x610
.equ      RTT_PDM_PSTAT,	 0x611
.equ      PDM_PMODE,	     0x613
.equ      PDM_CC_PMODE,	     0x620
.equ      PDM_CC_PSTAT,      0x621
.equ      PDM_SCM_PMODE,     0x622
.equ      PDM_SCM_PSTAT,     0x623
.equ	  PDM_SLC_PMODE,	 0x624
.equ	  PDM_SLC_PSTAT,	 0x625
.equ      DVFS_CC_PL,        0x626

; Defined for PDM registers's field
.equ 	  PDM_VERSION,  	 0x04

; Defined for Dcache
.equ 	  DC_FLSH,			 0x4b

; Defined for CSM
.equ 	  CSM_BUILD,			 0x0e5
.equ 	  CSM_ENABLE,    		 0x9a0

;Defined for SLC
.equ	  SLC_CTRL,			0x903
.equ 	  SLC_BUILD,		0xce

; Defined for Cluster Build
.equ 	  CLUSTER_BUILD,		 0xCF

; Defined for DMA
.equ 	  DMASTAT0,				0x686

;; --------------------------------------------------------------
;;
;;	check pdm build
;;
;; --------------------------------------------------------------
;; 1. Check PDM version
;; 2. Check whether PDM is set or not 
;; 3. Test should fail if 1) or 2) is not correct
.macro check_pdm_build
		;check pdm version
        lr    r1, [PDM_DVFS_BCR]
        and   r1, r1, 0xff
        cmp.f r1, PDM_VERSION ; make sure the correct PDM version
		bne   my_fail		  ; else, the version of PDM is not correct and the test fail

		lr     r1, [PDM_DVFS_BCR]
        and.f  r1, r1, 0x100  ; make sure that pdm is present in build
        bz     my_fail        ; else- terminate test
.endm


;; --------------------------------------------------------------
;;
;;	check pdm pstat
;;
;; --------------------------------------------------------------
;; 1. Check the previous core power mode
;; 2. If the previous power mode is PM1 or PM2, jump to restore sequence

.macro check_pstat, pstat_ppm, restore
		lr  r0, [PDM_PSTAT]   ; check previous core power mode
        and r0,  r0, pstat_ppm	  ; check if the current power mode is PM1 mode 
        cmp.f  r0, 0
        bne restore			  ;
.endm


;; --------------------------------------------------------------
;;
;;	Set IRQ for the specified interrupt 
;;
;; --------------------------------------------------------------
.macro set_irq, irq_number
		;SET  IRQ
		mov 	r1,    irq_number		;
		sr	    r1,    [irq_select]     ; set IRQ_SELECT to select the specified irq

		mov     r1,    0x0
		sr 	    r1,    [irq_trigger]     ; set IRQ_TRIGGER to level sensitive 

		mov     r1,    0x0
		sr      r1,    [irq_priority]     ; set IRQ_PRIORITY to highest priority

		mov     r1,    0x1
		sr      r1,    [irq_enable]     ; set IRQ_ENABLE to enable the specified irq
.endm

;;  ------------------------------------------------------------------
;;
;;   core_power_down_sequence
;;
;;  ------------------------------------------------------------------
;;
;; Two arguments needed:
;; --1. "pmode" is used to set the expected Power-down modes (PM1/PM2)
;;
.macro core_power_down_sequence, pmode
        
		; Disable Interrupt
		        clri 0x0
		
        
		; Save architectural states to external memory
		; User must save all architectural status to external memory
		; If PM2, the contents in CCMs also need to be saved
		; Here just take PC register as an example
		mov		r3,    0+0x700
		st.di	r63,   [r3]
		add     r3, r3, 4

		; IF DMA is congigured, software should make sure DMA is idle
				;Execute Sync instruction
		sync

		;; If DCACHE is configured, flush data cache
		;Read DCACHE_BCR to see whether Dcache is configured or not
	    lr 	    r3,    [DCACHE_BCR]
        and     r3,    r3,   0xf000
        cmp     r3,    0x0
        beq     program_to_power_down
        
		mov     r3,    0x1
        sr      r3,    [DC_FLSH]         ; flush dcache
        sync							 ; wait the flush operation done
		
		;; If STU is configured, software should program STU to disable this core's interface

        ;; Power down core with the mode specified with "pmode"
program_to_power_down:
        core_power_down pmode
.endm

;;  ------------------------------------------------------------------
;;
;;   core_power_down
;;
;;  ------------------------------------------------------------------
;; Power down core in specified mode
;; Notes: 1)Set sleep.[4] bit to 1 to enable interrupts after sleep.
;;        2)Set interrupt threshold of Sleep instruction to a proper
;;        value to make sure power-up timer's interrupt priority is
;;        higher than sleep.[3:0] bits (which will be updated to 
;;        STATUS32.E[3:0])
;;
.macro core_power_down, mode
        ;; Program "PDM_PMODE" AUX register to set processor power down modes
        sr        mode, [PDM_PMODE]
        ;; Execute Sleep Instruction
        sleep     0x18                ;set interrupt threshold to 8
.endm

;;  ------------------------------------------------------------------
;;
;;   cc_top_power_down
;;
;;  ------------------------------------------------------------------
;; Power down cc_top in specified mode
.macro cc_top_power_down, mode
        ;; Program "PDM_PMODE" AUX register to set processor power down modes
        sr        mode, [PDM_CC_PMODE]
		;;
		sync
.endm

;;  ------------------------------------------------------------------
;;
;;   scm_power_down
;;
;;  ------------------------------------------------------------------
;; Power down scm in specified mode
.macro scm_power_down, mode
        ;; Program "PDM_PMODE" AUX register to set processor power down modes
        sr        mode, [PDM_SCM_PMODE]
		;;
		sync
.endm

;;  ------------------------------------------------------------------
;;
;;   scm_power_down_sequence
;;
;;  ------------------------------------------------------------------
.macro scm_power_down_sequence
        
		;;Flush core cache before disable CSM   

		;; Program SCM_ENABLE register to bypass SCM first
		mov r1, 0x0
		sr  r1, [CSM_ENABLE]

		;; Software need to make sure the SCM become idle
		sync
		nop
		nop
		nop
		nop
		;; Save SCM architectural states

.endm

;;  ------------------------------------------------------------------
;;
;;   slc_power_down
;;
;;  ------------------------------------------------------------------
;; Power down SLC to specified mode
.macro slc_power_down, mode
		;; Program "PDM_SLC_PMODE" AUX register to set SLC power down modes
		sr mode, [PDM_SLC_PMODE]
		;;
		sync
.endm

;;  ------------------------------------------------------------------
;;
;;   scm_power_down_sequence
;;
;;  ------------------------------------------------------------------
.macro slc_power_down_sequence
		;;Disable SLC
		lr r1, [SLC_CTRL]  
		lr r1, [SLC_CTRL] ; read twice for some suggestion 
		or r1, r1, 0x1
		sr r1, [SLC_CTRL]  
		sync
		nop
		nop
		nop
		nop
.endm
;;  ------------------------------------------------------------------
;;
;;   core_power_up_restore
;;
;;  ------------------------------------------------------------------
;; Restore architectural states from main memory after power-up.
;;
;; One arguments needed:
;; -- "addr_reg" is used to set the core register index (r0/r1/...) which contains
;;       the start address of system memory for processor machine state restoring
;;
;; Notes: The restore macro should be in accordance with the save macro.
;;
.macro core_power_up_restore
; Part of baseline auxiliary registers to be restored.
; Restore architectual status 
; User must restore all architectural status from external memory
; If PM2, the contents in CCMs also need to be restored
; Here just take PC valuse as an example
		mov		r3,    0+0x700
		ld.di 	r1,  [r3]   ; Restore the pc value
		add     r3, r3, 4
    
.endm


.define ARCv2HS_PDM_MACROS_INCLUDED
.endif

