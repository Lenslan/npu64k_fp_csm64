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
//   alb_mss_fab_exported_defines: Exported parameters for bus generation
//
// ===========================================================================
//
// Description:
//   VPP file to derive parameters from a set of cores
//
// ===========================================================================



// include the Fabic specific configuration options




`define ALB_MSS_CCM_BASE 262144
// core is ARCv2MSS compliant
`define ALB_MSS_FAB_ARCV2MSS   1
// core itself has no master, no slave
`define ALB_MSS_FAB_ENDIAN     none
`define ALB_MSS_FAB_NUM_MST    0
`define ALB_MSS_FAB_NUM_SLV    0
`define ALB_MSS_FAB_CLK_NAME   mss_clk
`define ALB_MSS_FAB_CLKEN

`define ALB_MSS_FAB_DEF_LAT_W    0 

`define ALB_MSS_FAB_DEF_LAT_R    0 

`define ALB_MSS_FAB_DEF_WR_BW    0
`define ALB_MSS_FAB_DEF_RD_BW    0
`define ALB_MSS_FAB_LAT        0

`define ALB_MSS_FAB_PERF_TRANSPARENT   0
`define ALB_MSS_FAB_NEW_SWITCH     1

`define ALB_MSS_FAB_MSS_CLK_NUM           1

`define ALB_MSS_FAB_MSS_CLK0_NAME         mss_clk
`define ALB_MSS_FAB_MSS_CLK0_DEF_DIV2REF  2

` //                          axi:  {3'b0, axprot[1]}
` //                          ahb5: {hprot[6:4], hnonsec}
` //                          ahb:  {4'b0}
` //                          bvci: {4'b0}
`define ALB_MSS_FAB_USER_SIGNAL_WIDTH     4

`define ALB_MSS_FAB_CDC_FIFO_EN     0

