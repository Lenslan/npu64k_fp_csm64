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
// ALB_DMP_DCCM_AUX
// 
// 
// 
// 
//
// ===========================================================================
//
// Description:
//  This module implements the DCCM aux registers.
//    
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_dccm_aux.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 }, edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }


module npuarc_alb_dmp_dccm_aux (
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some inputs are not used in certain configurations
  ////////// General input signals ///////////////////////////////////////////
  //
  input                     clk,            // clock
  input                     rst_a,          // reset

  ////////// Interface with aux ctl ///////////////////////////////////////////
  //
  input                     aux_ren_r,       //  (X3) Aux Reg Enable
  input                     aux_wen_r,       //  (WA) Aux Reg Enable
  input  [`npuarc_DATA_RANGE]      aux_wdata_r,     //  (WA) Aux write data
  
  output reg [`npuarc_DATA_RANGE]  aux_rdata,       //  (X3) LR read data
  output reg                aux_illegal,     //  (X3) SR/LR illegal
  output reg                aux_k_rd,        //  (X3) needs Kernel Read
  output reg                aux_k_wr,        //  (X3) needs Kernel Write
  output reg                aux_unimpl,      //  (X3) Invalid Reg
  output reg                aux_serial_sr,   //  (X3) SR group flush pipe
  output reg                aux_strict_sr,   //  (X3) SR flush pipe

  //////////// Interface with DMP ////////////////////////////////////////// 
  //
  output reg [3:0]          aux_dccm_r
// leda NTL_CON13C on
);


// Local declarations.
//
reg [3:0] aux_dccm_nxt;

//////////////////////////////////////////////////////////////////////////////
// Reads
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_read_PROC
  aux_rdata      = {`npuarc_DATA_SIZE{1'b0}};       
  aux_illegal    = 1'b0;     
  aux_k_rd       = 1'b0;        
  aux_k_wr       = 1'b0;       
  aux_unimpl     = 1'b1;      
  aux_serial_sr  = 1'b0;  
  aux_strict_sr  = 1'b0;
  
  if (aux_ren_r)
  begin
    // We have got selected
    //
    aux_rdata[`npuarc_ADDR_MSB:`npuarc_ADDR_MSB-3] = aux_dccm_r;       
    aux_k_rd                         = 1'b1;    
    aux_k_wr                         = 1'b1;    
    aux_serial_sr                    = 1'b1;  
    aux_unimpl                       = 1'b0;    
  end
end

//!BCR { num: 24, val: 1879048192, name: "AUX_DCCM" }

//////////////////////////////////////////////////////////////////////////////
// Writes
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : aux_write_PROC
  aux_dccm_nxt = aux_wdata_r[`npuarc_ADDR_MSB:`npuarc_ADDR_MSB-3];
end

//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
//
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : aux_dccm_reg_PROC
  if (rst_a == 1'b1)
  begin
    aux_dccm_r <= 4'd`npuarc_DCCM_BASE;
  end
  else if (aux_wen_r)
  begin
    aux_dccm_r <= aux_dccm_nxt;
  end
end
endmodule // alb_dmp_dccm_aux

