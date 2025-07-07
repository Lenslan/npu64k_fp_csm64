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
//  ALB_DMP_BANK_SEL                
//                   
//                   
//
// ===========================================================================
//
// Description:
//  This module implements the bank selection information that will select  
//  the data banks from the available data banks that are required by the load/
//  store instruction.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_bank_sel.vpp
//
// ===========================================================================
// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_bank_sel (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used

  ////////// Interface to the X1 stage /////////////////////////////////
  //
  input  [1:0]                   x1_size_r,      // 00-b, 01-h, 10-w, 11-dw
  input                          x1_cache_byp_r, // .di
  input                          x1_pref_r,      // pref ucode bit
  input  [`npuarc_ADDR_RANGE]           x1_mem_addr0,   // X1 mem addr
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input  [`npuarc_ADDR_RANGE]           x1_mem_addr1,   // X1 mem addr
// spyglass enable_block W240
  input                          db_active_r,     // Debug inserted
    
  ////////// Aux base registers /////////////////////////////////
  //
  input [3:0]                    aux_dccm_r,
  /////////// Outputs /////////////////////////////////////////////
  //
  output reg [`npuarc_DCCM_ADR_RANGE]   dc1_dccm_addr0,
  output reg [`npuarc_DCCM_ADR_RANGE]   dc1_dccm_addr1,
  output reg [1:0]               dc1_dt_bank_sel,
  output reg [`npuarc_DC_IDX_RANGE]     dc1_dt_addr0,
  output reg [`npuarc_DC_IDX_RANGE]     dc1_dt_addr1,
  output reg [`npuarc_DC_ADR_RANGE]     dc1_dd_addr0,
  output reg [`npuarc_DC_ADR_RANGE]     dc1_dd_addr1,
  output reg                     dc1_dt_line_cross,
  output reg [`npuarc_DMP_TARGET_RANGE] dc1_target

// leda NTL_CON13C on
// leda NTL_CON37  on
);


// Local Declarations
//
wire  dc1_dccm_sel;
wire  dc1_iccm_sel;
wire  dc1_vec_mem_sel;
wire  dc1_dc_sel;
wire  dc1_uncached;
//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asynchronous block defining the data bank addr              
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_dccm_addr_PROC
  if (x1_mem_addr0[3] == 1'b0)
  begin
    dc1_dccm_addr0     = x1_mem_addr0[`npuarc_DCCM_ADR_RANGE];
    dc1_dccm_addr1     = x1_mem_addr1[`npuarc_DCCM_ADR_RANGE];
    dc1_dd_addr0       = x1_mem_addr0[`npuarc_DC_ADR_RANGE];
    dc1_dd_addr1       = x1_mem_addr1[`npuarc_DC_ADR_RANGE];
  end  
  else
  begin
    dc1_dccm_addr0     = x1_mem_addr1[`npuarc_DCCM_ADR_RANGE];
    dc1_dccm_addr1     = x1_mem_addr0[`npuarc_DCCM_ADR_RANGE]; 
    dc1_dd_addr0       = x1_mem_addr1[`npuarc_DC_ADR_RANGE];
    dc1_dd_addr1       = x1_mem_addr0[`npuarc_DC_ADR_RANGE]; 
  end  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Asyncrhonous logic to check the crossing of cache lines            
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_dt_line_cross_PROC
  // Byte   -> never crosses
  // Half   -> crosses when [(11111)]
  // Word   -> crosses when [(111, > 00)]
  // Double -> crosses when [(11,  > 000)]
  //
  case (x1_size_r)
  2'b01:
    // Half-Word
    //
    dc1_dt_line_cross = (& x1_mem_addr0[`npuarc_DC_BLK_MSB:0]);
  2'b10:
    // Word
    //
    dc1_dt_line_cross = (  (& x1_mem_addr0[`npuarc_DC_BLK_MSB:2])
                         & (| x1_mem_addr0 [1:0]));
  2'b11:
    // Double Word
    //
    dc1_dt_line_cross = (  (& x1_mem_addr0[`npuarc_DC_BLK_MSB:3])
                         & (| x1_mem_addr0 [2:0]));
  default:
    // Byte
    //
    dc1_dt_line_cross = 1'b0;
  endcase  
end

//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic defining for the tag bank selection             
//                                                                        
//////////////////////////////////////////////////////////////////////////
always @*
begin : dc1_dt_bank_sel_PROC
  dc1_dt_bank_sel[0] =  (x1_mem_addr0[`npuarc_DC_TAG_BANK_ID] == 1'b0)
                       | dc1_dt_line_cross;
  dc1_dt_bank_sel[1] =  (x1_mem_addr0[`npuarc_DC_TAG_BANK_ID] == 1'b1)
                       | dc1_dt_line_cross;
end

//////////////////////////////////////////////////////////////////////////
//                                                                        
// Asyncrhonous logic defining for the tag bank address             
//                                                                        
//////////////////////////////////////////////////////////////////////////

always @*
begin : dc1_dt_addr_PROC
  if (x1_mem_addr0[`npuarc_DC_TAG_BANK_ID] == 1'b0)
  begin
    dc1_dt_addr0       = x1_mem_addr0[`npuarc_DC_IDX_RANGE];
    dc1_dt_addr1       = x1_mem_addr1[`npuarc_DC_IDX_RANGE];
  end
  else
  begin
    dc1_dt_addr0       = x1_mem_addr1[`npuarc_DC_IDX_RANGE];
    dc1_dt_addr1       = x1_mem_addr0[`npuarc_DC_IDX_RANGE];
  end
end

//////////////////////////////////////////////////////////////////////////////
//                                                                          
//  DMP target selection based on the address             
//                                                                           
//////////////////////////////////////////////////////////////////////////////
assign dc1_dccm_sel    =   1'b0
                         |  (x1_mem_addr0[31:28] == aux_dccm_r) 
                         ;
assign dc1_iccm_sel    =   1'b0
                         ;
assign dc1_vec_mem_sel =  1'b0
                         ;

assign dc1_dc_sel      =  1'b0
                        | 1'b1                 
                        ;

assign dc1_uncached     =   x1_cache_byp_r 
                         & ( (~x1_pref_r) | db_active_r);

//////////////////////////////////////////////////////////////////////////////
//                                                                          
//  DMP target selection based on the address             
//                                                                           
//////////////////////////////////////////////////////////////////////////////
// leda W547 off
// LMD: Redundant case expression
// LJ:  Code more readable; will be optimized by synthesizer
always @*
begin : dc1_target_PROC
  // dc1_target[] = f(dc1_mem_addr0);
  // 
  
  // Priority: ICCM > DCCM > VMEM
  //
  
  casez ({dc1_iccm_sel, dc1_dccm_sel, dc1_vec_mem_sel, dc1_dc_sel})
  4'b1???:  dc1_target = `npuarc_DMP_TARGET_ICCM;
  4'b01??:  dc1_target = `npuarc_DMP_TARGET_DCCM;
  4'b001?:  dc1_target = `npuarc_DMP_TARGET_VMEM;
  4'b0001:  dc1_target =  dc1_uncached ? `npuarc_DMP_TARGET_MEM : `npuarc_DMP_TARGET_DC;
  default:  dc1_target = `npuarc_DMP_TARGET_MEM;
  endcase
end
//leda W547 on

endmodule // alb_dmp_bank_sel
