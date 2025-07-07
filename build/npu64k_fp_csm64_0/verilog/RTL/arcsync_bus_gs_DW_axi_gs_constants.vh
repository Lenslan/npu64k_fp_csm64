// ---------------------------------------------------------------------
//
// ------------------------------------------------------------------------------
//
// Copyright 2005 - 2020 Synopsys, INC.
//
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
//
// Component Name   : DW_axi_gs
// Component Version: 2.04a
// Release Type     : GA
// ------------------------------------------------------------------------------

//
// Release version :  2.04a
// File Version     :        $Revision: #1 $
// Revision: $Id: //dwh/DW_ocb/DW_axi_gs/amba_dev/src/DW_axi_gs_constants.vh#1 $
//
// -------------------------------------------------------------------------

//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`define ARCSYNC_REG___GUARD__DW_AXI_GS_CONSTANTS__VH__

`define ARCSYNC_REG_GS_RESP_W         2
`define ARCSYNC_REG_GS_SRESP_OK_R     2'b00
`define ARCSYNC_REG_GS_SRESP_OK_W     2'b01
`define ARCSYNC_REG_GS_SRESP_SLVERR_R 2'b10
`define ARCSYNC_REG_GS_SRESP_SLVERR_W 2'b11

`define ARCSYNC_REG_GS_LOCK_NORM    2'b00
`define ARCSYNC_REG_GS_LOCK_EX      2'b01
`define ARCSYNC_REG_GS_LOCK_LOCK    2'b10

`define ARCSYNC_REG_GS_BURST_W      2
`define ARCSYNC_REG_GS_BURST_FIXED  2'b00
`define ARCSYNC_REG_GS_BURST_INCR   2'b01
`define ARCSYNC_REG_GS_BURST_WRAP   2'b10
`define ARCSYNC_REG_GS_BURST_UINCR  2'b11

`define ARCSYNC_REG_GS_AXI_FIXED 2'b00
`define ARCSYNC_REG_GS_AXI_INCR  2'b01
`define ARCSYNC_REG_GS_AXI_WRAP  2'b10
`define ARCSYNC_REG_GS_AXI_RESVD 2'b11

`define ARCSYNC_REG_GS_AXI_OKAY   2'b00
`define ARCSYNC_REG_GS_AXI_EXOKAY 2'b01
`define ARCSYNC_REG_GS_AXI_SLVERR 2'b10
`define ARCSYNC_REG_GS_AXI_DECERR 2'b11

`define ARCSYNC_REG_GS_SIZE_W   3
`define ARCSYNC_REG_GS_SIZE_8   3'b0
`define ARCSYNC_REG_GS_SIZE_16  3'b1
`define ARCSYNC_REG_GS_SIZE_32  3'b10
`define ARCSYNC_REG_GS_SIZE_64  3'b11
`define ARCSYNC_REG_GS_SIZE_128 3'b100
`define ARCSYNC_REG_GS_SIZE_256 3'b101
`define ARCSYNC_REG_GS_SIZE_512 3'b110

`define ARCSYNC_REG_AXI_LTW ((`ARCSYNC_REG_GS_AXI_INTERFACE_TYPE == 0) ? 2: 1)

`define ARCSYNC_REG_GS_W_QOS   4
`define ARCSYNC_REG_GS_W_REGION 4

//==============================================================================
// End Guard
//==============================================================================
