// Library ARCv2HS-3.5.999999999
//----------------------------------------------------------------------------
//
// Copyright (C) 2010-2013 Synopsys, Inc. All rights reserved.
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
//
// 
// 
// 
// 
// CPU_GLUE
// 
// 
// 
// 
//
// ===========================================================================
//
// @f:cpu_glue
//
// Description:
// @p
//  The |cpu_glue| module contains all glue logics between modules at alb_cpu
//  level.
// @e
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"
// Set simulation timescale
//
`include "const.def"

// 0
// Glue logic has registers 0


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true } }

module npuarc_alb_cpu_glue (



  input              arc_halt_req,
  input              arc_run_req,
  output wire        gb_sys_halt_req_r,
  output wire        gb_sys_run_req_r
);


assign gb_sys_halt_req_r = arc_halt_req;
assign gb_sys_run_req_r  = arc_run_req;





endmodule

