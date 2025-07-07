.ifndef ARCv2EM_DMAC_MACROS_INCLUDED
; *********************************
; Macros to be used in EM-DMAC CCTs
; *********************************
; Defines for DMAC registers
.equ     REG_AUX_DMACTRL,      0x0000680
.equ     REG_AUX_DMACENB,      0x0000681
.equ     REG_AUX_DMACDSB,      0x0000682
.equ     REG_AUX_DMACHPRI,     0x0000683
.equ     REG_AUX_DMACNPRI,     0x0000684
.equ     REG_AUX_DMACREQ,      0x0000685
.equ     REG_AUX_DMASTAT0,     0x000686
.equ     REG_AUX_DMASTAT1,     0x000687
.equ     REG_AUX_DMACIRQ,      0x000688
.equ     REG_AUX_DMACBASE,     0x000689

; Channel 0 Registers
.equ     REG_AUX_DMACTRL0,     0x000690
.equ     REG_AUX_DMASAR0,      0x000691
.equ     REG_AUX_DMADAR0,      0x000692

; Build Configuration Registers

.equ     REG_AUX_DMAC_BCR,     0x0000CD
.equ     REG_AUX_DCCM_BCR,     0x000074
.equ     REG_AUX_ICCM_BCR,     0x000078
.equ     REG_AUX_XY_BCR,       0x000079
.define ARCv2EM_DMAC_MACROS_INCLUDED
.endif

