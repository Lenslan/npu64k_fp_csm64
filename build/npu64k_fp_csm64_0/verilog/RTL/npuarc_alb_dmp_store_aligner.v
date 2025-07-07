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
//   ALB_DMP_STORE_ALIGNER                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module aligns the store data with respect to the data banks.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_store_aligner.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_store_aligner (
  input       [3:0]               addr_3_to_0,
  input       [`npuarc_DMP_DATA_RANGE]   data,
  
  output reg  [`npuarc_DOUBLE_RANGE]     bank0_data,  // hi-lo
  output reg  [`npuarc_DOUBLE_RANGE]     bank1_data   // hi-lo
);

// Local declarations
//
// leda NTL_CON12A off
// LMD: undriven internal net 
// LJ:  code readibility
reg       [ 63:0]             align_row0;
reg       [ 71:0]             align_row1;
reg       [ 87:0]             align_row2;
reg       [119:0]             align_row3;
reg                           b0_sel;
reg                           b1_sel;
// leda NTL_CON12A on
// leda NTL_CON13A oon

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Asynchronous logic for the data alignement                               //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

always @*
begin : data_extended_PROC
  b0_sel      =  addr_3_to_0[3] & (|addr_3_to_0[2:0]);
  b1_sel      = !addr_3_to_0[3] & (|addr_3_to_0[2:0]);  
  align_row0  = data;
  align_row1  = addr_3_to_0[0] ? {align_row0,  8'd0} : { 8'd0, align_row0};
  align_row2  = addr_3_to_0[1] ? {align_row1, 16'd0} : {16'd0, align_row1};
  align_row3  = addr_3_to_0[2] ? {align_row2, 32'd0} : {32'd0, align_row2};  
  bank0_data  = b0_sel ?  {8'd0, align_row3[119:64]} : { align_row3[63:0]};             
  bank1_data  = b1_sel ?  {8'd0, align_row3[119:64]} : { align_row3[63:0]};
end
endmodule // alb_dmp_store_aligner
