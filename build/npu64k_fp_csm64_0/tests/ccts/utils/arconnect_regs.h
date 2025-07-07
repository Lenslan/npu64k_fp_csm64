/*************************************************************************/
/**                                                                     **/
/** Copyright (C) 2016-2018 Synopsys, Inc.                              **/
/** All Rights Reserved.                                                **/
/**                                                                     **/
/** This Synopsys software and all associated documentation are         **/
/** proprietary to Synopsys, Inc. and may only be used pursuant to the  **/
/** terms and conditions of a written license agreement with Synopsys,  **/
/** Inc. All other use, reproduction, modification, or distribution of  **/
/** this Synopsys software or the associated documentation is strictly  **/
/** prohibited.                                                         **/
/**                                                                     **/
/*************************************************************************/

// ARConnect (a.k.a. MCIP) register list

#ifndef __ARCCONNECT_REGS_h__
#define __ARCCONNECT_REGS_h__

// ----------------------------------------------------------------------------
// Address on the AUX interface
// ----------------------------------------------------------------------------

// Control registers : command, write data and read data
#define CONNECT_REG_CMD            0x0
#define CONNECT_REG_WDATA          0x1
#define CONNECT_REG_READBACK       0x2

// AUX register seen by the ARC HS
#define CONNECT_AUX_BASE           0x600
#define CONNECT_AUX_CMD            (CONNECT_AUX_BASE + CONNECT_REG_CMD)
#define CONNECT_AUX_WDATA          (CONNECT_AUX_BASE + CONNECT_REG_WDATA)
#define CONNECT_AUX_READBACK       (CONNECT_AUX_BASE + CONNECT_REG_READBACK)

// Build Configuration registers seen only by the ARC HS
#define CONNECT_SYSTEM_BUILD       0x0D0
#define CONNECT_SEMA_BUILD         0x0D1
#define CONNECT_MESSAGE_BUILD      0x0D2
#define CONNECT_PMU_BUILD          0x0D3
#define CONNECT_IDU_BUILD          0x0D5
#define CONNECT_GFRC_BUILD         0x0D6
#define CONNECT_ICI_BUILD          0x0E0
#define CONNECT_ICD_BUILD          0x0E1
#define CONNECT_ASI_BUILD          0x0E2
#define CONNECT_PDM_BUILD          0x0E3

// ----------------------------------------------------------------------------
// Commands : lower 8 bits of CONNECT_REG_CMD register
// ----------------------------------------------------------------------------

#define CONNECT_CMD_CHECK_CORE_ID            0x00

// Inter-Core Interrupt Unit
#define CONNECT_CMD_INTRPT_GENERATE_IRQ      0x01
#define CONNECT_CMD_INTRPT_GENERATE_ACK      0x02
#define CONNECT_CMD_INTRPT_READ_STATUS       0x03
#define CONNECT_CMD_INTRPT_CHECK_SOURCE      0x04
#define CONNECT_CMD_INTRPT_ACK_BIT_MASK      0x05
// Inter-Core Semaphore unit
#define CONNECT_CMD_SEMA_CLAIM_AND_READ      0x11
#define CONNECT_CMD_SEMA_RELEASE             0x12
#define CONNECT_CMD_SEMA_FORCE_RELEASE       0x13
// Inter-core Message Unit
#define CONNECT_CMD_MSG_SRAM_SET_ADDR        0x21
#define CONNECT_CMD_MSG_SRAM_READ_ADDR       0x22
#define CONNECT_CMD_MSG_SRAM_SET_ADDR_OFFS   0x23
#define CONNECT_CMD_MSG_SRAM_READ_ADDR_OFF   0x24
#define CONNECT_CMD_MSG_SRAM_WRITE           0x25
#define CONNECT_CMD_MSG_SRAM_WRITE_INC       0x26
#define CONNECT_CMD_MSG_SRAM_WRITE_IMM       0x27
#define CONNECT_CMD_MSG_SRAM_READ            0x28
#define CONNECT_CMD_MSG_SRAM_READ_INC        0x29
#define CONNECT_CMD_MSG_SRAM_READ_IMM        0x2A
#define CONNECT_CMD_MSG_SET_ECC_CTRL         0x2B
#define CONNECT_CMD_MSG_READ_ECC_CTRL        0x2C
// Inter-core Debug Unit
#define CONNECT_CMD_DEBUG_RESET              0x31
#define CONNECT_CMD_DEBUG_HALT               0x32
#define CONNECT_CMD_DEBUG_RUN                0x33
#define CONNECT_CMD_DEBUG_SET_MASK           0x34
#define CONNECT_CMD_DEBUG_READ_MASK          0x35
#define CONNECT_CMD_DEBUG_SET_SELECT         0x36
#define CONNECT_CMD_DEBUG_READ_SELECT        0x37
#define CONNECT_CMD_DEBUG_READ_EN            0x38
#define CONNECT_CMD_DEBUG_READ_CMD           0x39
#define CONNECT_CMD_DEBUG_READ_CORE          0x3A
// Global Real-Time Counter
#define CONNECT_CMD_GRTC_CLEAR               0x41
#define CONNECT_CMD_GRTC_READ_LO             0x42
#define CONNECT_CMD_GRTC_READ_HI             0x43
#define CONNECT_CMD_GFRC_ENABLE              0x44
#define CONNECT_CMD_GFRC_DISABLE             0x45
#define CONNECT_CMD_GFRC_READ_DISABLE        0x46
#define CONNECT_CMD_GFRC_SET_CORE            0x47
#define CONNECT_CMD_GFRC_READ_CORE           0x48
#define CONNECT_CMD_GFRC_READ_HALT           0x49
#define CONNECT_CMD_GRTC_CLK_ENABLE          0x4A
#define CONNECT_CMD_GRTC_CLK_DISABLE         0x4B
#define CONNECT_CMD_GRTC_READ_CLK_STATUS     0x4C
// Power Management Unit
#define CONNECT_CMD_PMU_SET_PMODE            0x51
#define CONNECT_CMD_PMU_READ_PSTATUS         0x52
#define CONNECT_CMD_PMU_SET_PCNT             0x53
#define CONNECT_CMD_PMU_READ_PCNT            0x54
#define CONNECT_CMD_PMU_SET_DVFS             0x55
#define CONNECT_CMD_PMU_READ_DVFS            0x56
// Interrupt Distribution Unit
#define CONNECT_CMD_IDU_ENABLE               0x71
#define CONNECT_CMD_IDU_DISABLE              0x72
#define CONNECT_CMD_IDU_READ_ENABLE          0x73
#define CONNECT_CMD_IDU_SET_MODE             0x74
#define CONNECT_CMD_IDU_READ_MODE            0x75
#define CONNECT_CMD_IDU_SET_DEST             0x76
#define CONNECT_CMD_IDU_READ_DEST            0x77
#define CONNECT_CMD_IDU_GEN_CIRQ             0x78
#define CONNECT_CMD_IDU_ACK_CIRQ             0x79
#define CONNECT_CMD_IDU_CHECK_STATUS         0x7A
#define CONNECT_CMD_IDU_CHECK_SOURCE         0x7B
#define CONNECT_CMD_IDU_SET_MASK             0x7C
#define CONNECT_CMD_IDU_READ_MASK            0x7D
#define CONNECT_CMD_IDU_CHECK_FIRST          0x7E
// Power Domain Manager
#define CONNECT_CMD_PDM_SET_PM               0x81
#define CONNECT_CMD_PDM_READ_PSTATUS         0x82

#endif // __ARCCONNECT_REGS_h__
