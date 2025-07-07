
; Assembler directives for eia extensions in this design
.set apex_eventmanager_present,1
.set apex_eventmanager_present,1
.extAuxRegister EVT_CTRL,0xf02,r|w
.extAuxRegister EVT_FILTER_LO,0xf04,r|w
.extAuxRegister EVT_FILTER_HI,0xf05,r|w
.extAuxRegister EVT_CNT_SEL,0xf0a,r|w
.extAuxRegister EVT_CNT_VAL,0xf0b,r|w
.extAuxRegister EVT_VM_SEL,0xf00,r|w
.extAuxRegister EVT_VM_MAP,0xf01,r|w
.extAuxRegister EVT_GRP_SEL,0xf07,r|w
.extAuxRegister EVT_SID,0xf08,r|w
.extAuxRegister EVT_SSID,0xf09,r|w
.extAuxRegister EVT_IRQ,0xf03,r|w
.extInstruction EVTMASKCHK,7,0,SUFFIX_FLAG,SYNTAX_2OP
.extInstruction EVTMASKALL,7,1,SUFFIX_FLAG,SYNTAX_2OP
.extInstruction EVTMASKANY,7,2,SUFFIX_FLAG,SYNTAX_2OP
.extInstruction EVTMASKDECR,7,3,SUFFIX_FLAG,SYNTAX_2OP
.extInstruction EVTMASKINCR,7,4,SUFFIX_FLAG,SYNTAX_2OP
.extInstruction EVTMASKSEND,7,5,SUFFIX_FLAG,SYNTAX_2OP
.extInstruction EVTVMCHK,7,6,SUFFIX_FLAG,SYNTAX_2OP

