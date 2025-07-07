// Library ARC_Trace-3.0.999999999
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
// Certain materials incorporated herein are copyright (C) 2010 - 2011, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
// synchronizer
// ===========================================================================
//
// Description:
//
// Synchronizer for a clock-domain crossing input signal (async input).
// The number synchronizing FF levels is controlled by SYNC_FF_LEVELS.
//
// Note: This is a behavioral block that may be replaced by the RDF flow before
// synthesis. The replacement block intantiates the propoer synchronizer cell
// of the synthesis library
//
// ===========================================================================

`include "npuarc_arc_rtt_defines.v"
`include "npuarc_rtt_pkg_defines.v"
module npuarc_rtt_cdc_sync 
  #(
  parameter SYNC_FF_LEVELS = `npuarc_RTT_SYNC_FF_LEVELS    // SYNC_FF_LEVELS >= 2
  )
// spyglass disable_block FlopDataConstant LogicDepth MergeFlops-ML
  (
  input   clk,         // target (receiving) clock domain clk
  input   rst_a,

  input   din,         // single bit wide input

  output  dout
);

// spyglass disable_block Ac_unsync02
// SMD: Unsynchronized Crossing.
// SJ:  This module is instantiated with SYNC_FF_LEVELS = 2 ,resulting in a two-stage synchronizer.

// spyglass disable_block Reset_check07
// SMD: Clear pin of sequential element is driven by combinational logic
// SJ:  support for power domains

// spyglass disable_block Reset_sync04
// SMD: Asynchronous reset signal 'rst_a' is synchronized at least twice
// SJ:  We do need to synchronize the rst_a
  npuarc_DWbb_bcm21_atv #(.WIDTH(1), .F_SYNC_TYPE(SYNC_FF_LEVELS), .VERIF_EN(`npuarc_RTT_SYNC_VERIF_EN), .SVA_TYPE(`npuarc_RTT_SYNC_SVA_TYPE),
                  .TMR_CDC(`npuarc_RTT_SYNC_TMR_CDC)) u_sync_wrp ( 
          .rst_d_n        (~rst_a), 
          .data_s         ({(`npuarc_RTT_SYNC_TMR_CDC*2+1){din}}),
          .clk_d          (clk), 
          .data_d         (dout)      );
// spyglass enable_block FlopDataConstant LogicDepth MergeFlops-ML
// spyglass enable_block Ac_unsync02
// spyglass enable_block Reset_sync04 Reset_check07
endmodule // cdc_sync
