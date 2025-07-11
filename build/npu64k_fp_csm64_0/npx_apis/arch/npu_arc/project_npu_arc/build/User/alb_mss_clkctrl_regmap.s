;
; Clock control registers
.equ  MSS_CLKCTRL_CFG_CTRL_ADDR,            0xc0000000
; clock divider registers
.equ  MSS_CLKCTRL_CLK_DIV_ADDR,       0xc0000004
.equ  MSS_CLKCTRL_WDT_CLK_DIV_ADDR,       0xc0000008
.equ  MSS_CLKCTRL_RTT_CLK_DIV_ADDR,       0xc000000c
.equ  MSS_CLKCTRL_MSS_CLK_DIV_ADDR,       0xc0000010
; clock enable ratio and status registers
.equ  MSS_CLKCTRL_MBUS_CLK_EN_RATIO_ADDR,     0xc0000014
.equ  MSS_CLKCTRL_MBUS_CLK_EN_STAT_ADDR,      0xc0000018
.equ  MSS_CLKCTRL_MSS_FAB_MST0_CLK_EN_RATIO_ADDR,     0xc000001c
.equ  MSS_CLKCTRL_MSS_FAB_MST0_CLK_EN_STAT_ADDR,      0xc0000020
.equ  MSS_CLKCTRL_MSS_FAB_MST1_CLK_EN_RATIO_ADDR,     0xc0000024
.equ  MSS_CLKCTRL_MSS_FAB_MST1_CLK_EN_STAT_ADDR,      0xc0000028
.equ  MSS_CLKCTRL_MSS_FAB_SLV0_CLK_EN_RATIO_ADDR,     0xc000002c
.equ  MSS_CLKCTRL_MSS_FAB_SLV0_CLK_EN_STAT_ADDR,      0xc0000030
.equ  MSS_CLKCTRL_MSS_FAB_SLV1_CLK_EN_RATIO_ADDR,     0xc0000034
.equ  MSS_CLKCTRL_MSS_FAB_SLV1_CLK_EN_STAT_ADDR,      0xc0000038
.equ  MSS_CLKCTRL_MSS_FAB_SLV2_CLK_EN_RATIO_ADDR,     0xc000003c
.equ  MSS_CLKCTRL_MSS_FAB_SLV2_CLK_EN_STAT_ADDR,      0xc0000040
.equ  MSS_CLKCTRL_LBUS0_CLK_EN_RATIO_ADDR,     0xc0000044
.equ  MSS_CLKCTRL_LBUS0_CLK_EN_STAT_ADDR,      0xc0000048
.equ  MSS_CLKCTRL_DBUS_CLK_EN_RATIO_ADDR,     0xc000004c
.equ  MSS_CLKCTRL_DBUS_CLK_EN_STAT_ADDR,      0xc0000050
.equ  MSS_CLKCTRL_LBUS1_CLK_EN_RATIO_ADDR,     0xc0000054
.equ  MSS_CLKCTRL_LBUS1_CLK_EN_STAT_ADDR,      0xc0000058
.equ  MSS_CLKCTRL_NMI_COUNTER,            0xc000005c
