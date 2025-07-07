//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2012 Synopsys, Inc. All rights reserved.
//
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary
// work of Synopsys, Inc., and is fully protected under copyright and
// trade secret laws. You may not view, use, disclose, copy, or distribute
// this file or any information contained herein except pursuant to a
// valid written license from Synopsys, Inc.
//
// Certain materials incorporated herein are copyright (C) 2010 - 2012, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   alb_mss_mem_defines: Extract parameters for bus generation
//
// ===========================================================================
//
// Description:
//   VPP file to derive parameters from a set of cores
//
// ===========================================================================

// include the Memory Controller specific configuration options

















`define ALB_MSS_MEM_USER_SIGNAL_WIDTH   1
`define ALB_MSS_MEM_PORT_ID_WIDTH       3
`define ALB_MSS_MEM_ID_WIDTH            8
`define ALB_MSS_MEM_AW                  32
`define ALB_MSS_MEM_DW                  128
`define ALB_MSS_MEM_REG_W               1
`define ALB_MSS_MEM_NUM_REG             1
`define ALB_MSS_MEM_REG0_BASE_ADDR 0
`define ALB_MSS_MEM_REG0_APER_WIDTH 32
`define ALB_MSS_MEM_REG0_SZ         268435456
`define ALB_MSS_MEM_REG0_ATTR        2 //O:read-only;1:write-only;2:read-write
`define ALB_MSS_MEM_REG0_SECURE      0 //O:non-sec region 1: sec region

`define ALB_MSS_MEM_REG0_DEF_LAT_RD    0
`define ALB_MSS_MEM_REG0_LAT_RD        0
`define ALB_MSS_MEM_REG0_DEF_LAT_WR    0
`define ALB_MSS_MEM_REG0_LAT_WR        0
`define ALB_MSS_MEM_REG0_DEF_LAT       100
`define ALB_MSS_MEM_REG0_LAT           128


`define ALB_MSS_MEM_REG0_LATL2      7

`define ALB_MSS_MEM_WR_RSP_AHEAD  0
`define ALB_MSS_MEM_CONFLICT_FREE 0
`define ALB_MSS_MEM_CFREE_NUM         0

`define MSS_ONLY_ASSERTION_EN
`define MSS_ASSERTION_ON

`define PSS_RUNTIME_DEBUG 0
`define PSS_LICENSE_CHECK `PSS_LICENSE_CHECK
`define PSS_MSG_ADDR `PSS_MSG_ADDR
