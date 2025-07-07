.ifndef ARCv2HS_STU_MACROS_INCLUDED
; *********************************
; Macros to be used in HS-STU CCTs
; *********************************
; Defines for STU registers
.equ      STU_BUILD,                  0x0E4   
.equ      STU_ENTRY_NUM,              0x980   
.equ      STU_NEXT_FREE,              0x981   
.equ      STU_FREE_NUM,               0x982   
.equ      STU_NEXT_FREE_INC,          0x983   
.equ      STU_ENTRY_SELECT,           0x984   
.equ      STU_ENTRY_STAT,             0x985   
.equ      STU_BASE_L,                 0x986   
.equ      STU_BASE_H,                 0x987   
.equ      STU_WEIGHT,                 0x988   
.equ      STU_EVENT,                  0x989   
.equ      STU_DONE_IRQ,               0x98A   
.equ      STU_ERR_IRQ,                0x98B   
.equ      STU_COH_ENABLE0,            0x98C   
.equ      STU_COH_AP0_BASE_L,         0x98D   
.equ      STU_COH_AP0_BASE_H,         0x98E   
.equ      STU_COH_AP0_SIZE,           0x98F   
.equ      STU_COH_ENABLE1,            0x990   
.equ      STU_COH_AP1_BASE_L,         0x991   
.equ      STU_COH_AP1_BASE_H,         0x992   
.equ      STU_COH_AP1_SIZE,           0x993   
.equ      STU_CORE_DISABLE,           0x994   
.equ      STU_DISABLE_RECORD,         0x995   
.equ      STU_CORE_IDLE,              0x996   
.equ      CSM_ENABLE,                 0x9A0   


.define ARCv2HS_STU_MACROS_INCLUDED
.endif

