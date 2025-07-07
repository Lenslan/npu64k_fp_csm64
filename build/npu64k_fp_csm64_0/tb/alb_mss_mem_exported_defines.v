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
//   alb_mss_mem_exported defines: Extract parameters for bus generation
//
// ===========================================================================
//
// Description:
//   VPP file to derive parameters from a set of cores
//
// ===========================================================================

// include the Memory Controller specific configuration options






   

   

   

// core is ARCv2MSS compliant
`define ALB_MSS_MEM_ARCV2MSS                 1
// core has no master, one slave
`define ALB_MSS_MEM_ENDIAN                   none
`define ALB_MSS_MEM_NUM_MST                  0
`define ALB_MSS_MEM_NUM_SLV                  1
`define ALB_MSS_MEM_CLK_NAME                 mss_clk
`define ALB_MSS_MEM_CLKEN
// Specify attributes of the slave interface
`define ALB_MSS_MEM_SLV0_IS_DEFAULT_SLAVE    0
`define ALB_MSS_MEM_SLV0_DEFAULT_SPACE       32
`define ALB_MSS_MEM_SLV0_PREF                mss_mem_
`define ALB_MSS_MEM_SLV0_CLK_NAME            mss_clk
`define ALB_MSS_MEM_SLV0_CLK_EN
`define ALB_MSS_MEM_SLV0_PROT                bus
`define ALB_MSS_MEM_SLV0_DATA_WIDTH          128
`define ALB_MSS_MEM_SLV0_ADDR_WIDTH          -1
`define ALB_MSS_MEM_SLV0_SUPPORT_RATIO       0
`define ALB_MSS_MEM_SLV0_REG_W               1
`define ALB_MSS_MEM_SLV0_NUM_REG             1
`define ALB_MSS_MEM_SLV0_REG0_BASE_ADDR 0
`define ALB_MSS_MEM_SLV0_REG0_APER_WIDTH 32



`define ALB_MSS_MEM_SLV0_REG0_DEF_LAT_RD    100


`define ALB_MSS_MEM_SLV0_REG0_LAT_RD        128


`define ALB_MSS_MEM_SLV0_REG0_DEF_LAT_WR    100


`define ALB_MSS_MEM_SLV0_REG0_LAT_WR        128

`define ALB_MSS_MEM_SLV0_CONFLICT_FREE      0

`define ALB_MSS_MEM_IS_MEM
`define ALB_MSS_MEM_REGION_NUM              1

`define ALB_MSS_MEM_MSS_CLK_NUM              0


