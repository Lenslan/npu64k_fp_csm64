/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */
`ifndef ARCSYNC_DEFINES_INCLUDED
`define ARCSYNC_DEFINES_INCLUDED
/*
 * Copyright (C) 2021-2023 Synopsys, Inc. All rights reserved.
 *
 * SYNOPSYS CONFIDENTIAL - This is an unpublished, confidential, and
 * proprietary work of Synopsys, Inc., and may be subject to patent,
 * copyright, trade secret, and other legal or contractual protection.
 * This work may be used only pursuant to the terms and conditions of a
 * written license agreement with Synopsys, Inc. All other use, reproduction,
 * distribution, or disclosure of this work is strictly prohibited.
 *
 * The entire notice above must be reproduced on all authorized copies.
 */

`ifndef ARCSYNC_EXPORTED_DEFINES_INCLUDED
`define ARCSYNC_EXPORTED_DEFINES_INCLUDED

`define ARCSYNC_NUM_CLUSTER           3
`define ARCSYNC_MAX_CORES_PER_CL      32
`define ARCSYNC_TYPE_CL_NPUSLICE      0
`define ARCSYNC_TYPE_CL_NPX           0
`define ARCSYNC_TYPE_CL_VPX           1
`define ARCSYNC_TYPE_CL_HOST          2
`define ARCSYNC_NUM_CORE_CL0          18
`define ARCSYNC_TYPE_CL0              0
`define ARCSYNC_ITF_CL0               0
`define ARCSYNC_ITF_STUB_CL0          0
`define ARCSYNC_PFX_CL0               
`define ARCSYNC_NUM_CORE_CL1          4
`define ARCSYNC_TYPE_CL1              1
`define ARCSYNC_ITF_CL1               1
`define ARCSYNC_ITF_STUB_CL1          1
`define ARCSYNC_PFX_CL1               v0
`define ARCSYNC_NUM_CORE_CL2          1
`define ARCSYNC_TYPE_CL2              2
`define ARCSYNC_ITF_CL2               1
`define ARCSYNC_ITF_STUB_CL2          1
`define ARCSYNC_PFX_CL2               h0
`define ARCSYNC_NUM_CORE_CL3          0
`define ARCSYNC_TYPE_CL3              0
`define ARCSYNC_ITF_CL3               0
`define ARCSYNC_ITF_STUB_CL3          0
`define ARCSYNC_PFX_CL3               
`define ARCSYNC_NUM_CORE_CL4          0
`define ARCSYNC_TYPE_CL4              0
`define ARCSYNC_ITF_CL4               0
`define ARCSYNC_ITF_STUB_CL4          0
`define ARCSYNC_PFX_CL4               
`define ARCSYNC_NUM_CORE_CL5          0
`define ARCSYNC_TYPE_CL5              0
`define ARCSYNC_ITF_CL5               0
`define ARCSYNC_ITF_STUB_CL5          0
`define ARCSYNC_PFX_CL5               
`define ARCSYNC_NUM_CORE_CL6          0
`define ARCSYNC_TYPE_CL6              0
`define ARCSYNC_ITF_CL6               0
`define ARCSYNC_ITF_STUB_CL6          0
`define ARCSYNC_PFX_CL6               
`define ARCSYNC_NUM_CORE_CL7          0
`define ARCSYNC_TYPE_CL7              0
`define ARCSYNC_ITF_CL7               0
`define ARCSYNC_ITF_STUB_CL7          0
`define ARCSYNC_PFX_CL7               
`define ARCSYNC_NUM_CORE_CL8          0
`define ARCSYNC_TYPE_CL8              0
`define ARCSYNC_ITF_CL8               0
`define ARCSYNC_ITF_STUB_CL8          0
`define ARCSYNC_PFX_CL8               
`define ARCSYNC_NUM_CORE_CL9          0
`define ARCSYNC_TYPE_CL9              0
`define ARCSYNC_ITF_CL9               0
`define ARCSYNC_ITF_STUB_CL9          0
`define ARCSYNC_PFX_CL9               
`define ARCSYNC_NUM_CORE_CL10          0
`define ARCSYNC_TYPE_CL10              0
`define ARCSYNC_ITF_CL10               0
`define ARCSYNC_ITF_STUB_CL10          0
`define ARCSYNC_PFX_CL10               
`define ARCSYNC_NUM_CORE_CL11          0
`define ARCSYNC_TYPE_CL11              0
`define ARCSYNC_ITF_CL11               0
`define ARCSYNC_ITF_STUB_CL11          0
`define ARCSYNC_PFX_CL11               
`define ARCSYNC_NUM_CORE_CL12          0
`define ARCSYNC_TYPE_CL12              0
`define ARCSYNC_ITF_CL12               0
`define ARCSYNC_ITF_STUB_CL12          0
`define ARCSYNC_PFX_CL12               
`define ARCSYNC_NUM_CORE_CL13          0
`define ARCSYNC_TYPE_CL13              0
`define ARCSYNC_ITF_CL13               0
`define ARCSYNC_ITF_STUB_CL13          0
`define ARCSYNC_PFX_CL13               
`define ARCSYNC_NUM_CORE_CL14          0
`define ARCSYNC_TYPE_CL14              0
`define ARCSYNC_ITF_CL14               0
`define ARCSYNC_ITF_STUB_CL14          0
`define ARCSYNC_PFX_CL14               
`define ARCSYNC_NUM_CORE_CL15          0
`define ARCSYNC_TYPE_CL15              0
`define ARCSYNC_ITF_CL15               0
`define ARCSYNC_ITF_STUB_CL15          0
`define ARCSYNC_PFX_CL15               

`define ARCSYNC_VIRT_MACHINES         8
`define ARCSYNC_NUM_IRQ_PER_CORE      1
`define ARCSYNC_NUM_EVT_PER_CORE      1
`define ARCSYNC_NUM_IRQ_PER_VPROC     1
`define ARCSYNC_NUM_EVT_PER_VPROC     1
`define ARCSYNC_VIRT_PROC             3

`define ARCSYNC_NUM_ATOMIC_CNT        64
`define ARCSYNC_NUM_GFRC              1
`define ARCSYNC_HAS_PMU               1
`define ARCSYNC_PMU_RESET_PMODE       1
`define ARCSYNC_CORE_CLK_ENA_RST      0

`define ARCSYNC_SAFETY_LEVEL          0

`define ARCSYNC_HAS_PAE40             1

`define ARCSYNC_ARC_DEV               0



`endif  //ARCSYNC_EXPORTED_DEFINES_INCLUDED




  `define ARCSYNC_HAS_ATOMIC_CNT       1

`define ARCSYNC_ATOMIC_CNT_WIDTH      8
`define ARCSYNC_PDM_HAS_FG            1
`define ARCSYNC_PMU_VPX_MODE          1
`define ARCSYNC_BASE_ADDR             868352
`define ARCSYNC_HAS_CDC               1

// derived defs
`define  ARCSYNC_CORE_NUM             3*32
`define  ARCSYNC_AC_NUM               64
`define  ARCSYNC_BASE_OFFSET          32'h1000

//============================================================================
//           Build Configuration 
//============================================================================
`define  ARCSYNC_REG_CONFIG_M1       2
`define  ARCSYNC_ADDR_CONFIG         32'h0
`define  ADDR_AS_BLD_CFG             32'h0
`define  ADDR_AS_NUM_CORE_C03        32'h4
`define  ADDR_AS_NUM_CORE_C47        32'h8
`define  ARCSYNC_ADDR_CONFIG_MAX     `ARCSYNC_ADDR_CONFIG + 4* (`ARCSYNC_REG_CONFIG_M1)

`define  ARCSYNC_CSM_INIT_BASE               24'h004000
`define  ARCSYNC_PERIPH_INIT_BASE            24'h009000


//============================================================================
//            ARCsync_SAFETY
//============================================================================

//the address of the registers
`define  ARCSYNC_REG_SFTY_M1       4
`define  ARCSYNC_ADDR_SFTY         32'h34
`define  ARCSYNC_ADDR_SFTY_MAX     `ARCSYNC_ADDR_SFTY + 4* (`ARCSYNC_REG_SFTY_M1)
`define  ADDR_SFTY_PASSWD          32'h34
`define  ADDR_SFTY_DIAG            32'h38
`define  ADDR_SFTY_STATUS          32'h3C
`define  ADDR_SFTY_CTRL            32'h40
//============================================================================
//            ARCsync_GFRC
//============================================================================
// width of the global GFRC counter, default is 64-bit
// DATA_WIDTH is the read data width 32-bit or 64-bit

`define  DATA_WIDTH          32    
`define  GFRC_HBITS_RANGE    63:32  
`define  GFRC_LBITS_RANGE    31:0 

//the address of the registers
`define  ARCSYNC_REG_GFRC_M1       3 
`define  ARCSYNC_ADDR_GFRC         32'h20
`define  ARCSYNC_ADDR_GFRC_MAX     `ARCSYNC_ADDR_GFRC + 4* (`ARCSYNC_REG_GFRC_M1)
`define  ADDR_GFRC_ENABLE          32'h20
`define  ADDR_GFRC_CLEAR           32'h24
`define  ADDR_GFRC_READ_LO         32'h28
`define  ADDR_GFRC_READ_HI         32'h2C

//============================================================================
//           Cluster Control
//============================================================================
//
`define  ARCSYNC_REG_CL_CONTROL_REGION_M1 3* (3) - 1
`define  ADDR_CL_ENABLE              32'h1000
`define  ADDR_CL_GRP_CLK_EN          `ADDR_CL_ENABLE + 4* (3)
`define  ADDR_CL_GRP_RESET           `ADDR_CL_ENABLE + 8* (3)
`define  ADDR_CL_CONTROL_MAX         `ADDR_CL_ENABLE + 4* (`ARCSYNC_REG_CL_CONTROL_REGION_M1)

`define  ADDR_CSM_ADDR_BASE          `ADDR_CL_ENABLE + 16* (3)
`define  ADDR_CL_PERIPH_ADDR_BASE    `ADDR_CL_ENABLE + 20* (3)

//============================================================================
//            ARCsyncPower Management Unit 
//============================================================================
// 4-byte register for each cluster
`define  ARCSYNC_REG_PMU_REGION_0_M1        11* (3) - 1
`define  ARCSYNC_ADDR_PMU_REGION_0          `ADDR_CL_ENABLE + 32* (3)
`define  ARCSYNC_ADDR_PMU_REGION_0_MAX      `ARCSYNC_ADDR_PMU_REGION_0 + 4* (`ARCSYNC_REG_PMU_REGION_0_M1)
`define  ADDR_PMU_SET_RSTCNT                `ARCSYNC_ADDR_PMU_REGION_0
`define  ADDR_PMU_SET_PUCNT                 `ADDR_CL_ENABLE + 36* (3)
`define  ADDR_PMU_SET_PDCNT                 `ADDR_CL_ENABLE + 40* (3)
`define  ADDR_CL_GRP0_PMODE                 `ADDR_CL_ENABLE + 44* (3)
`define  ADDR_CL_GRP1_PMODE                 `ADDR_CL_ENABLE + 48* (3)
`define  ADDR_CL_GRP2_PMODE                 `ADDR_CL_ENABLE + 52* (3)
`define  ADDR_CL_GRP3_PMODE                 `ADDR_CL_ENABLE + 56* (3)
`define  ADDR_PMU_SET_CORE_LOGIC1           `ADDR_CL_ENABLE + 60* (3)
`define  ADDR_PMU_SET_CORE_LOGIC2           `ADDR_CL_ENABLE + 64* (3)
`define  ADDR_PMU_SET_GRP_LOGIC1            `ADDR_CL_ENABLE + 68* (3)
`define  ADDR_PMU_SET_GRP_LOGIC2            `ADDR_CL_ENABLE + 72* (3)

// 4-byte register for each core
`define  ARCSYNC_REG_PMU_REGION_1_M1        1 * `ARCSYNC_CORE_NUM - 1
`define  ARCSYNC_ADDR_PMU_REGION_1          32'h2000
`define  ARCSYNC_ADDR_PMU_REGION_1_MAX      `ARCSYNC_ADDR_PMU_REGION_1 + 4* (`ARCSYNC_REG_PMU_REGION_1_M1)
`define  ADDR_CORE_PMODE                    `ARCSYNC_ADDR_PMU_REGION_1
// if pdm has fg ---> `PD1_NUM = 3,pd1_mem,pd1_pd,_pd1_fg; `PD1_NUM = 2,pd1_mem,pd1_pd
`define  PD1_NUM                   3
`define  PDM_HAS_FG                1
//define the VPX PMU MODE 
`define  PMU_VPX_MODE              1

//============================================================================
//            ARCsync Control and Status
//============================================================================
`define  ARCSYNC_REG_ACS_M1        7 * `ARCSYNC_CORE_NUM - 1
`define  ARCSYNC_ADDR_ACS          `ADDR_CORE_PMODE +  4*`ARCSYNC_CORE_NUM
`define  ARCSYNC_ADDR_ACS_MAX      `ARCSYNC_ADDR_ACS + 4* (`ARCSYNC_REG_ACS_M1)
`define  ADDR_CORE_RUN             `ARCSYNC_ADDR_ACS
`define  ADDR_CORE_HALT            `ARCSYNC_ADDR_ACS +  4*`ARCSYNC_CORE_NUM
`define  ADDR_CORE_BOOT_IVB_LO     `ARCSYNC_ADDR_ACS +  8*`ARCSYNC_CORE_NUM
`define  ADDR_CORE_BOOT_IVB_HI     `ARCSYNC_ADDR_ACS + 12*`ARCSYNC_CORE_NUM
`define  ADDR_CORE_STATUS          `ARCSYNC_ADDR_ACS + 16*`ARCSYNC_CORE_NUM
`define  ADDR_CORE_RESET           `ARCSYNC_ADDR_ACS + 20*`ARCSYNC_CORE_NUM
`define  ADDR_CORE_CLK_EN          `ARCSYNC_ADDR_ACS + 24*`ARCSYNC_CORE_NUM

//============================================================================
//           Event and Interrupt Dispatch 
//============================================================================
`define  ARCSYNC_REG_EID_M1        12 * `ARCSYNC_CORE_NUM - 1
`define  ARCSYNC_ADDR_EID          32'h4000
`define  ARCSYNC_ADDR_EID_MAX      `ARCSYNC_ADDR_EID + 4* (`ARCSYNC_REG_EID_M1)
`define  ADDR_EID_SEND_EVENT_0     `ARCSYNC_ADDR_EID
`define  ADDR_EID_SEND_EVENT_1     `ARCSYNC_ADDR_EID + 4*`ARCSYNC_CORE_NUM
`define  ADDR_EID_SEND_EVENT_2     `ARCSYNC_ADDR_EID + 8*`ARCSYNC_CORE_NUM
`define  ADDR_EID_SEND_EVENT_3     `ARCSYNC_ADDR_EID + 12*`ARCSYNC_CORE_NUM
`define  ADDR_EID_SEND_EVENT_MAX   `ARCSYNC_ADDR_EID + (4*1)*`ARCSYNC_CORE_NUM
`define  ADDR_EID_RAISE_IRQ_0      `ARCSYNC_ADDR_EID + 16*`ARCSYNC_CORE_NUM
`define  ADDR_EID_ACK_IRQ_0        `ARCSYNC_ADDR_EID + 20*`ARCSYNC_CORE_NUM
`define  ADDR_EID_RAISE_IRQ_1      `ARCSYNC_ADDR_EID + 24*`ARCSYNC_CORE_NUM
`define  ADDR_EID_ACK_IRQ_1        `ARCSYNC_ADDR_EID + 28*`ARCSYNC_CORE_NUM
`define  ADDR_EID_RAISE_IRQ_2      `ARCSYNC_ADDR_EID + 32*`ARCSYNC_CORE_NUM
`define  ADDR_EID_ACK_IRQ_2        `ARCSYNC_ADDR_EID + 36*`ARCSYNC_CORE_NUM
`define  ADDR_EID_RAISE_IRQ_3      `ARCSYNC_ADDR_EID + 40*`ARCSYNC_CORE_NUM
`define  ADDR_EID_ACK_IRQ_3        `ARCSYNC_ADDR_EID + 44*`ARCSYNC_CORE_NUM
`define  ADDR_EID_ACK_IRQ_MAX      `ARCSYNC_ADDR_EID + (16 + 4*2*1)*`ARCSYNC_CORE_NUM

//============================================================================
//           Atomic Counter 
//============================================================================
`define  ARCSYNC_REG_AC_M1         2 * `ARCSYNC_CORE_NUM - 1
`define  ARCSYNC_ADDR_AC           `ARCSYNC_ADDR_EID + 48*`ARCSYNC_CORE_NUM
`define  ARCSYNC_ADDR_AC_MAX       `ARCSYNC_ADDR_AC  + 4* (`ARCSYNC_REG_AC_M1)
`define  ADDR_AC_NOTIFY_SRC        `ARCSYNC_ADDR_EID + 48*`ARCSYNC_CORE_NUM
`define  ADDR_AC_ACK_IRQ           `ARCSYNC_ADDR_EID + 52*`ARCSYNC_CORE_NUM
//`define  ADDR_AC_ACK_IRQ_MAX       `ARCSYNC_ADDR_EID + 56*`ARCSYNC_CORE_NUM -4 // grep /npu/arch/arcsync and not find RTL use it.

`define  ADDR_AC_CONFIG            32'h8000
`define  ADDR_AC_CONFIG_MAX        `ADDR_AC_CONFIG + 4*`ARCSYNC_AC_NUM - 4
`define  ADDR_AC_CONTROL           32'h9000 
`define  ADDR_AC_CONTROL_MAX       `ADDR_AC_CONTROL + 4*`ARCSYNC_AC_NUM*`ARCSYNC_CORE_NUM - 4

//============================================================================
//           Virtual Machine Configuration
//============================================================================
`define ARCSYNC_REG_MAP_VM_CONFIG_M1  8 * `ARCSYNC_VIRT_PROC - 1
`define ARCSYNC_ADDR_VM_CONFIG        `ADDR_AC_CONTROL + 24576
`define ARCSYNC_ADDR_VM_CONFIG_MAX    `ARCSYNC_ADDR_VM_CONFIG + 4 * (`ARCSYNC_REG_MAP_VM_CONFIG_M1)
`define ADDR_MAP_VM_VPROC             `ARCSYNC_ADDR_VM_CONFIG
`define ADDR_MAP_VM_VPROC_MAX         `ADDR_MAP_VM_VPROC + 4 * (`ARCSYNC_REG_MAP_VM_CONFIG_M1)

//============================================================================
//           Virtual Machine Access: Event and Interrupt Dispatch, Atomic
//           Counter
//           Each VM registers occupy a full 4KB address range
//           Below is register set in one VM
//============================================================================

`define ARCSYNC_REG_VM0_EID_M1         12* `ARCSYNC_VIRT_PROC - 1
`define ARCSYNC_ADDR_VM0_EID          `ARCSYNC_ADDR_VM_CONFIG + 4096
`define ARCSYNC_ADDR_VM0_EID_MAX      `ARCSYNC_ADDR_VM0_EID + 4* (`ARCSYNC_REG_VM0_EID_M1)

`define ARCSYNC_VM_GFRC_LO_OFFSET     40*`ARCSYNC_VIRT_PROC
`define ARCSYNC_VM_GFRC_HI_OFFSET     40*`ARCSYNC_VIRT_PROC+4


  //== VM0 EID/AC base address
  `define ADDR_VM0_EID_SEND_EVENT_0     `ARCSYNC_ADDR_VM0_EID + 4096*0
  `define ADDR_VM0_EID_SEND_EVENT_1     `ARCSYNC_ADDR_VM0_EID + 4096*0 + 4*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_SEND_EVENT_2     `ARCSYNC_ADDR_VM0_EID + 4096*0 + 8*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_SEND_EVENT_3     `ARCSYNC_ADDR_VM0_EID + 4096*0 + 12*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_SEND_EVENT_MAX   `ARCSYNC_ADDR_VM0_EID + 4096*0 + (4*`ARCSYNC_NUM_EVT_PER_VPROC)*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_RAISE_IRQ_0      `ARCSYNC_ADDR_VM0_EID + 4096*0 + 16*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_ACK_IRQ_0        `ARCSYNC_ADDR_VM0_EID + 4096*0 + 20*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_RAISE_IRQ_1      `ARCSYNC_ADDR_VM0_EID + 4096*0 + 24*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_ACK_IRQ_1        `ARCSYNC_ADDR_VM0_EID + 4096*0 + 28*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_RAISE_IRQ_2      `ARCSYNC_ADDR_VM0_EID + 4096*0 + 32*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_ACK_IRQ_2        `ARCSYNC_ADDR_VM0_EID + 4096*0 + 36*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_RAISE_IRQ_3      `ARCSYNC_ADDR_VM0_EID + 4096*0 + 40*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_ACK_IRQ_3        `ARCSYNC_ADDR_VM0_EID + 4096*0 + 44*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_EID_ACK_IRQ_MAX      `ADDR_VM0_EID_RAISE_IRQ_0 + 4096*0 + 4*2*`ARCSYNC_NUM_IRQ_PER_VPROC*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_AC_NOTIFY_SRC        `ARCSYNC_ADDR_VM0_EID + 4096*0 + 48*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_AC_ACK_IRQ           `ARCSYNC_ADDR_VM0_EID + 4096*0 + 52*`ARCSYNC_VIRT_PROC
  `define ADDR_VM0_AC_CONTROL           `ARCSYNC_ADDR_VM0_EID + 4096*0 + 56*`ARCSYNC_VIRT_PROC + 4*(64/8)
  `define ADDR_VM0_AC_MAX               `ADDR_VM0_AC_CONTROL + 4096*0 + 4*((64/8)*`ARCSYNC_VIRT_PROC)

  //== VM1 EID/AC base address
  `define ADDR_VM1_EID_SEND_EVENT_0     `ARCSYNC_ADDR_VM0_EID + 4096*1
  `define ADDR_VM1_EID_SEND_EVENT_1     `ARCSYNC_ADDR_VM0_EID + 4096*1 + 4*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_SEND_EVENT_2     `ARCSYNC_ADDR_VM0_EID + 4096*1 + 8*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_SEND_EVENT_3     `ARCSYNC_ADDR_VM0_EID + 4096*1 + 12*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_SEND_EVENT_MAX   `ARCSYNC_ADDR_VM0_EID + 4096*1 + (4*`ARCSYNC_NUM_EVT_PER_VPROC)*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_RAISE_IRQ_0      `ARCSYNC_ADDR_VM0_EID + 4096*1 + 16*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_ACK_IRQ_0        `ARCSYNC_ADDR_VM0_EID + 4096*1 + 20*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_RAISE_IRQ_1      `ARCSYNC_ADDR_VM0_EID + 4096*1 + 24*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_ACK_IRQ_1        `ARCSYNC_ADDR_VM0_EID + 4096*1 + 28*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_RAISE_IRQ_2      `ARCSYNC_ADDR_VM0_EID + 4096*1 + 32*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_ACK_IRQ_2        `ARCSYNC_ADDR_VM0_EID + 4096*1 + 36*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_RAISE_IRQ_3      `ARCSYNC_ADDR_VM0_EID + 4096*1 + 40*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_ACK_IRQ_3        `ARCSYNC_ADDR_VM0_EID + 4096*1 + 44*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_EID_ACK_IRQ_MAX      `ADDR_VM0_EID_RAISE_IRQ_0 + 4096*1 + 4*2*`ARCSYNC_NUM_IRQ_PER_VPROC*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_AC_NOTIFY_SRC        `ARCSYNC_ADDR_VM0_EID + 4096*1 + 48*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_AC_ACK_IRQ           `ARCSYNC_ADDR_VM0_EID + 4096*1 + 52*`ARCSYNC_VIRT_PROC
  `define ADDR_VM1_AC_CONTROL           `ARCSYNC_ADDR_VM0_EID + 4096*1 + 56*`ARCSYNC_VIRT_PROC + 4*(64/8)
  `define ADDR_VM1_AC_MAX               `ADDR_VM0_AC_CONTROL + 4096*1 + 4*((64/8)*`ARCSYNC_VIRT_PROC)

  //== VM2 EID/AC base address
  `define ADDR_VM2_EID_SEND_EVENT_0     `ARCSYNC_ADDR_VM0_EID + 4096*2
  `define ADDR_VM2_EID_SEND_EVENT_1     `ARCSYNC_ADDR_VM0_EID + 4096*2 + 4*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_SEND_EVENT_2     `ARCSYNC_ADDR_VM0_EID + 4096*2 + 8*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_SEND_EVENT_3     `ARCSYNC_ADDR_VM0_EID + 4096*2 + 12*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_SEND_EVENT_MAX   `ARCSYNC_ADDR_VM0_EID + 4096*2 + (4*`ARCSYNC_NUM_EVT_PER_VPROC)*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_RAISE_IRQ_0      `ARCSYNC_ADDR_VM0_EID + 4096*2 + 16*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_ACK_IRQ_0        `ARCSYNC_ADDR_VM0_EID + 4096*2 + 20*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_RAISE_IRQ_1      `ARCSYNC_ADDR_VM0_EID + 4096*2 + 24*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_ACK_IRQ_1        `ARCSYNC_ADDR_VM0_EID + 4096*2 + 28*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_RAISE_IRQ_2      `ARCSYNC_ADDR_VM0_EID + 4096*2 + 32*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_ACK_IRQ_2        `ARCSYNC_ADDR_VM0_EID + 4096*2 + 36*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_RAISE_IRQ_3      `ARCSYNC_ADDR_VM0_EID + 4096*2 + 40*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_ACK_IRQ_3        `ARCSYNC_ADDR_VM0_EID + 4096*2 + 44*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_EID_ACK_IRQ_MAX      `ADDR_VM0_EID_RAISE_IRQ_0 + 4096*2 + 4*2*`ARCSYNC_NUM_IRQ_PER_VPROC*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_AC_NOTIFY_SRC        `ARCSYNC_ADDR_VM0_EID + 4096*2 + 48*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_AC_ACK_IRQ           `ARCSYNC_ADDR_VM0_EID + 4096*2 + 52*`ARCSYNC_VIRT_PROC
  `define ADDR_VM2_AC_CONTROL           `ARCSYNC_ADDR_VM0_EID + 4096*2 + 56*`ARCSYNC_VIRT_PROC + 4*(64/8)
  `define ADDR_VM2_AC_MAX               `ADDR_VM0_AC_CONTROL + 4096*2 + 4*((64/8)*`ARCSYNC_VIRT_PROC)

  //== VM3 EID/AC base address
  `define ADDR_VM3_EID_SEND_EVENT_0     `ARCSYNC_ADDR_VM0_EID + 4096*3
  `define ADDR_VM3_EID_SEND_EVENT_1     `ARCSYNC_ADDR_VM0_EID + 4096*3 + 4*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_SEND_EVENT_2     `ARCSYNC_ADDR_VM0_EID + 4096*3 + 8*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_SEND_EVENT_3     `ARCSYNC_ADDR_VM0_EID + 4096*3 + 12*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_SEND_EVENT_MAX   `ARCSYNC_ADDR_VM0_EID + 4096*3 + (4*`ARCSYNC_NUM_EVT_PER_VPROC)*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_RAISE_IRQ_0      `ARCSYNC_ADDR_VM0_EID + 4096*3 + 16*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_ACK_IRQ_0        `ARCSYNC_ADDR_VM0_EID + 4096*3 + 20*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_RAISE_IRQ_1      `ARCSYNC_ADDR_VM0_EID + 4096*3 + 24*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_ACK_IRQ_1        `ARCSYNC_ADDR_VM0_EID + 4096*3 + 28*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_RAISE_IRQ_2      `ARCSYNC_ADDR_VM0_EID + 4096*3 + 32*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_ACK_IRQ_2        `ARCSYNC_ADDR_VM0_EID + 4096*3 + 36*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_RAISE_IRQ_3      `ARCSYNC_ADDR_VM0_EID + 4096*3 + 40*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_ACK_IRQ_3        `ARCSYNC_ADDR_VM0_EID + 4096*3 + 44*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_EID_ACK_IRQ_MAX      `ADDR_VM0_EID_RAISE_IRQ_0 + 4096*3 + 4*2*`ARCSYNC_NUM_IRQ_PER_VPROC*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_AC_NOTIFY_SRC        `ARCSYNC_ADDR_VM0_EID + 4096*3 + 48*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_AC_ACK_IRQ           `ARCSYNC_ADDR_VM0_EID + 4096*3 + 52*`ARCSYNC_VIRT_PROC
  `define ADDR_VM3_AC_CONTROL           `ARCSYNC_ADDR_VM0_EID + 4096*3 + 56*`ARCSYNC_VIRT_PROC + 4*(64/8)
  `define ADDR_VM3_AC_MAX               `ADDR_VM0_AC_CONTROL + 4096*3 + 4*((64/8)*`ARCSYNC_VIRT_PROC)

  //== VM4 EID/AC base address
  `define ADDR_VM4_EID_SEND_EVENT_0     `ARCSYNC_ADDR_VM0_EID + 4096*4
  `define ADDR_VM4_EID_SEND_EVENT_1     `ARCSYNC_ADDR_VM0_EID + 4096*4 + 4*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_SEND_EVENT_2     `ARCSYNC_ADDR_VM0_EID + 4096*4 + 8*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_SEND_EVENT_3     `ARCSYNC_ADDR_VM0_EID + 4096*4 + 12*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_SEND_EVENT_MAX   `ARCSYNC_ADDR_VM0_EID + 4096*4 + (4*`ARCSYNC_NUM_EVT_PER_VPROC)*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_RAISE_IRQ_0      `ARCSYNC_ADDR_VM0_EID + 4096*4 + 16*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_ACK_IRQ_0        `ARCSYNC_ADDR_VM0_EID + 4096*4 + 20*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_RAISE_IRQ_1      `ARCSYNC_ADDR_VM0_EID + 4096*4 + 24*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_ACK_IRQ_1        `ARCSYNC_ADDR_VM0_EID + 4096*4 + 28*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_RAISE_IRQ_2      `ARCSYNC_ADDR_VM0_EID + 4096*4 + 32*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_ACK_IRQ_2        `ARCSYNC_ADDR_VM0_EID + 4096*4 + 36*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_RAISE_IRQ_3      `ARCSYNC_ADDR_VM0_EID + 4096*4 + 40*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_ACK_IRQ_3        `ARCSYNC_ADDR_VM0_EID + 4096*4 + 44*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_EID_ACK_IRQ_MAX      `ADDR_VM0_EID_RAISE_IRQ_0 + 4096*4 + 4*2*`ARCSYNC_NUM_IRQ_PER_VPROC*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_AC_NOTIFY_SRC        `ARCSYNC_ADDR_VM0_EID + 4096*4 + 48*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_AC_ACK_IRQ           `ARCSYNC_ADDR_VM0_EID + 4096*4 + 52*`ARCSYNC_VIRT_PROC
  `define ADDR_VM4_AC_CONTROL           `ARCSYNC_ADDR_VM0_EID + 4096*4 + 56*`ARCSYNC_VIRT_PROC + 4*(64/8)
  `define ADDR_VM4_AC_MAX               `ADDR_VM0_AC_CONTROL + 4096*4 + 4*((64/8)*`ARCSYNC_VIRT_PROC)

  //== VM5 EID/AC base address
  `define ADDR_VM5_EID_SEND_EVENT_0     `ARCSYNC_ADDR_VM0_EID + 4096*5
  `define ADDR_VM5_EID_SEND_EVENT_1     `ARCSYNC_ADDR_VM0_EID + 4096*5 + 4*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_SEND_EVENT_2     `ARCSYNC_ADDR_VM0_EID + 4096*5 + 8*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_SEND_EVENT_3     `ARCSYNC_ADDR_VM0_EID + 4096*5 + 12*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_SEND_EVENT_MAX   `ARCSYNC_ADDR_VM0_EID + 4096*5 + (4*`ARCSYNC_NUM_EVT_PER_VPROC)*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_RAISE_IRQ_0      `ARCSYNC_ADDR_VM0_EID + 4096*5 + 16*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_ACK_IRQ_0        `ARCSYNC_ADDR_VM0_EID + 4096*5 + 20*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_RAISE_IRQ_1      `ARCSYNC_ADDR_VM0_EID + 4096*5 + 24*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_ACK_IRQ_1        `ARCSYNC_ADDR_VM0_EID + 4096*5 + 28*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_RAISE_IRQ_2      `ARCSYNC_ADDR_VM0_EID + 4096*5 + 32*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_ACK_IRQ_2        `ARCSYNC_ADDR_VM0_EID + 4096*5 + 36*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_RAISE_IRQ_3      `ARCSYNC_ADDR_VM0_EID + 4096*5 + 40*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_ACK_IRQ_3        `ARCSYNC_ADDR_VM0_EID + 4096*5 + 44*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_EID_ACK_IRQ_MAX      `ADDR_VM0_EID_RAISE_IRQ_0 + 4096*5 + 4*2*`ARCSYNC_NUM_IRQ_PER_VPROC*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_AC_NOTIFY_SRC        `ARCSYNC_ADDR_VM0_EID + 4096*5 + 48*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_AC_ACK_IRQ           `ARCSYNC_ADDR_VM0_EID + 4096*5 + 52*`ARCSYNC_VIRT_PROC
  `define ADDR_VM5_AC_CONTROL           `ARCSYNC_ADDR_VM0_EID + 4096*5 + 56*`ARCSYNC_VIRT_PROC + 4*(64/8)
  `define ADDR_VM5_AC_MAX               `ADDR_VM0_AC_CONTROL + 4096*5 + 4*((64/8)*`ARCSYNC_VIRT_PROC)

  //== VM6 EID/AC base address
  `define ADDR_VM6_EID_SEND_EVENT_0     `ARCSYNC_ADDR_VM0_EID + 4096*6
  `define ADDR_VM6_EID_SEND_EVENT_1     `ARCSYNC_ADDR_VM0_EID + 4096*6 + 4*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_SEND_EVENT_2     `ARCSYNC_ADDR_VM0_EID + 4096*6 + 8*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_SEND_EVENT_3     `ARCSYNC_ADDR_VM0_EID + 4096*6 + 12*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_SEND_EVENT_MAX   `ARCSYNC_ADDR_VM0_EID + 4096*6 + (4*`ARCSYNC_NUM_EVT_PER_VPROC)*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_RAISE_IRQ_0      `ARCSYNC_ADDR_VM0_EID + 4096*6 + 16*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_ACK_IRQ_0        `ARCSYNC_ADDR_VM0_EID + 4096*6 + 20*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_RAISE_IRQ_1      `ARCSYNC_ADDR_VM0_EID + 4096*6 + 24*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_ACK_IRQ_1        `ARCSYNC_ADDR_VM0_EID + 4096*6 + 28*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_RAISE_IRQ_2      `ARCSYNC_ADDR_VM0_EID + 4096*6 + 32*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_ACK_IRQ_2        `ARCSYNC_ADDR_VM0_EID + 4096*6 + 36*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_RAISE_IRQ_3      `ARCSYNC_ADDR_VM0_EID + 4096*6 + 40*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_ACK_IRQ_3        `ARCSYNC_ADDR_VM0_EID + 4096*6 + 44*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_EID_ACK_IRQ_MAX      `ADDR_VM0_EID_RAISE_IRQ_0 + 4096*6 + 4*2*`ARCSYNC_NUM_IRQ_PER_VPROC*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_AC_NOTIFY_SRC        `ARCSYNC_ADDR_VM0_EID + 4096*6 + 48*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_AC_ACK_IRQ           `ARCSYNC_ADDR_VM0_EID + 4096*6 + 52*`ARCSYNC_VIRT_PROC
  `define ADDR_VM6_AC_CONTROL           `ARCSYNC_ADDR_VM0_EID + 4096*6 + 56*`ARCSYNC_VIRT_PROC + 4*(64/8)
  `define ADDR_VM6_AC_MAX               `ADDR_VM0_AC_CONTROL + 4096*6 + 4*((64/8)*`ARCSYNC_VIRT_PROC)

  //== VM7 EID/AC base address
  `define ADDR_VM7_EID_SEND_EVENT_0     `ARCSYNC_ADDR_VM0_EID + 4096*7
  `define ADDR_VM7_EID_SEND_EVENT_1     `ARCSYNC_ADDR_VM0_EID + 4096*7 + 4*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_SEND_EVENT_2     `ARCSYNC_ADDR_VM0_EID + 4096*7 + 8*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_SEND_EVENT_3     `ARCSYNC_ADDR_VM0_EID + 4096*7 + 12*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_SEND_EVENT_MAX   `ARCSYNC_ADDR_VM0_EID + 4096*7 + (4*`ARCSYNC_NUM_EVT_PER_VPROC)*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_RAISE_IRQ_0      `ARCSYNC_ADDR_VM0_EID + 4096*7 + 16*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_ACK_IRQ_0        `ARCSYNC_ADDR_VM0_EID + 4096*7 + 20*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_RAISE_IRQ_1      `ARCSYNC_ADDR_VM0_EID + 4096*7 + 24*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_ACK_IRQ_1        `ARCSYNC_ADDR_VM0_EID + 4096*7 + 28*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_RAISE_IRQ_2      `ARCSYNC_ADDR_VM0_EID + 4096*7 + 32*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_ACK_IRQ_2        `ARCSYNC_ADDR_VM0_EID + 4096*7 + 36*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_RAISE_IRQ_3      `ARCSYNC_ADDR_VM0_EID + 4096*7 + 40*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_ACK_IRQ_3        `ARCSYNC_ADDR_VM0_EID + 4096*7 + 44*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_EID_ACK_IRQ_MAX      `ADDR_VM0_EID_RAISE_IRQ_0 + 4096*7 + 4*2*`ARCSYNC_NUM_IRQ_PER_VPROC*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_AC_NOTIFY_SRC        `ARCSYNC_ADDR_VM0_EID + 4096*7 + 48*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_AC_ACK_IRQ           `ARCSYNC_ADDR_VM0_EID + 4096*7 + 52*`ARCSYNC_VIRT_PROC
  `define ADDR_VM7_AC_CONTROL           `ARCSYNC_ADDR_VM0_EID + 4096*7 + 56*`ARCSYNC_VIRT_PROC + 4*(64/8)
  `define ADDR_VM7_AC_MAX               `ADDR_VM0_AC_CONTROL + 4096*7 + 4*((64/8)*`ARCSYNC_VIRT_PROC)

`endif  //ARCSYNC_DEFINES_INCLUDED
