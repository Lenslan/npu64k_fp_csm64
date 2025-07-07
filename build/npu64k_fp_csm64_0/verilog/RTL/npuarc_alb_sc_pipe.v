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
// Certain materials incorporated herein are copyright (C) 2010 - 2013, The
// University Court of the University of Edinburgh. All Rights Reserved.
//
// The entire notice above must be reproduced on all authorized copies.
//
//----------------------------------------------------------------------------
//
//   ###      ### 
//  #   #    #   #
//  #        #    
//  #        #    
//   ###     #    
//      #    #    
//      #    #    
//  #   #    #   #
//   ###      ### 
//
// ===========================================================================
//
// @f:commit
//
// Description:
// @p
//  This module implements the configurable Stack Checking of the ARCv2HS CPU.
//  
//  
// @e
// ==========================================================================


// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_sc_pipe (

  ////////// General input signals ///////////////////////////////////////////
  //
  input                       clk,                 // global clock
  input                       rst_a,               // asynchronous reset

  // Aux Reg Interface
  input                       ar_sc_r,             // SC bit of status32
  input   [`npuarc_DATA_RANGE]       ar_aux_stack_base_r, // STACK_BASE aux register
  input   [`npuarc_DATA_RANGE]       ar_aux_stack_top_r,  // STACK_TOP  aux register
  input                       db_active,           //

  input                       div_busy_r,           // Post-commit Div pending

  // X1 Stage
  input                       x1_pass,             //

  // X2 Stage
  input                       x2_pass,             //
  input                       x2_enable,           //
  input                       x2_kill,             //
  input                       x2_load_r,           // 
  input                       x2_store_r,          // 
  input                       x2_pref_r,           //
  input   [`npuarc_ADDR_RANGE]       x2_mem_addr_r,       // X2 memory address
  input                       x2_uop_inst_r,       // 
  input                       x2_div_op_r,         // 
  input   [`npuarc_RGF_ADDR_RANGE]   x2_rf_ra0_r,         //
  input                       x2_rf_renb0_r,       //
  input   [`npuarc_RGF_ADDR_RANGE]   x2_rf_ra1_r,         //
  input                       x2_rf_renb1_r,       //
  input                       x2_rf_wenb0_r,       // 
  input   [`npuarc_RGF_ADDR_RANGE]   x2_rf_wa0_r,         // 
  input                       x2_rf_wenb1_r,       // 
  input   [`npuarc_RGF_ADDR_RANGE]   x2_rf_wa1_r,         // 
  output                      x2_sc_stall,         //
  input                       dp_x2_sp_r,          //

  // X3 Stage
  input                       x3_enable,
  input                       x3_rf_wenb0_r,       // 
  input   [`npuarc_RGF_ADDR_RANGE]   x3_rf_wa0_r,         // 
  input                       x3_rf_wenb1_r,       // 
  input   [`npuarc_RGF_ADDR_RANGE]   x3_rf_wa1_r,         // 
  output reg                  x3_stack_viol_r,     // To Exception
  output reg [`npuarc_DATA_RANGE]    x3_sc_efa_r,         // (X3) EFA

  // CA Stage
  input                       ca_rf_wenb0_r,       // 
  input   [`npuarc_RGF_ADDR_RANGE]   ca_rf_wa0_r,         // 

  // WA Stage
  input                       wa_rf_wenb1_r,       // retiring data1 en
  input   [`npuarc_RGF_ADDR_RANGE]   wa_rf_wa1_r,         // retiring data1 addr
  input   [`npuarc_DATA_RANGE]       wa_rf_wdata1_lo_r,   // retiring data1[31:0]
  input                       wa_rf_wenb0_r,       // retiring data0 en
  input   [`npuarc_RGF_ADDR_RANGE]   wa_rf_wa0_r,         // retiring data0 addr
  input   [`npuarc_DATA_RANGE]       wa_rf_wdata0_lo_r    // retiring data0[31:0]


);

////////////////////////////////////////////////////////////////////////////
//                                                                        //
//                                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

// Shadow SP - 1 perregister bank
reg  [`npuarc_ADDR_RANGE]          ar_ssp_r;           // Shadow Stack    Pointer

reg                         x2_stack_viol;      // Stack checking violation
reg                         x2_sp_ex_op;        // SP used for LD/ST Data & not Address
reg                         x2_sp_read;         // 
reg                         x2_sp_write;        // 
reg                         x2_sp_mem_op;       //
reg                         x2_stack_au;        //
reg  [`npuarc_ADDR_RANGE]          x2_ssp_r;           //

reg  [`npuarc_ADDR_RANGE]          x2_limit_val;       // Address for limit check 1

reg                         x2_limit_chk1;      // Limit check 1
reg                         x2_limit_chk2;      // Limit check 2
reg                         x2_limit_chk3;      // Limit check 3

reg                         x3_cg0;
reg                         x3_addr_cg0;

reg                         sp_pending;         // SP update is pending
reg                         x2_div_cg0;
reg                         x2_div_pend_nxt;
reg                         x2_div_pend_r;


////////////////////////////////////////////////////////////////////////////
//                                                                        //
// X2 Stage Control                                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : x2_ctrl_PROC

  x2_div_cg0      = (x2_enable & x1_pass)
                  | x2_div_pend_r
                  ;

  x2_div_pend_nxt = ( x2_div_op_r & x2_sp_write )
                  | ( x2_div_pend_r & div_busy_r )
                  ;

end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// X2 Stage Values                                                        //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: x2_div_reg_PROC
  if (rst_a == 1'b1)
    begin
      x2_div_pend_r   <= 1'b0;
    end
  else if (x2_div_cg0 == 1'b1)
    begin
      x2_div_pend_r   <= x2_div_pend_nxt;
    end
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Synchronous block for Shadow Stack Pointer                             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : ar_ssp_PROC
  if (rst_a == 1'b1)
    ar_ssp_r             <= `npuarc_ADDR_SIZE'd0;
  else if ((wa_rf_wa1_r == `npuarc_SP_REG) & (wa_rf_wenb1_r))
    ar_ssp_r             <= wa_rf_wdata1_lo_r [`npuarc_ADDR_RANGE];
  else if ((wa_rf_wa0_r == `npuarc_SP_REG) & (wa_rf_wenb0_r))
    ar_ssp_r             <= wa_rf_wdata0_lo_r [`npuarc_ADDR_RANGE];
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Detect Stack Protection Violations.                                    //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : stack_checking_PROC

  sp_pending    = 1'b0
                | x2_div_pend_r
                ;

//////////////////////////////////////////////////////////////////////////
// Stack Based memory operations
//
//  (1) SP on RA0 for Store
//  (2) SP on RA1 for Load but not Store
//
// 

  x2_sp_read    = (   (x2_rf_ra0_r == `npuarc_SP_REG)
                   && x2_rf_renb0_r)
                 | (  (x2_rf_ra1_r == `npuarc_SP_REG)
                   && x2_rf_renb1_r && x2_load_r && (~x2_store_r))
                ;

  x2_sp_ex_op   = 1'b1
                & x2_load_r 
                & x2_store_r
                & !x2_rf_renb0_r
                & ( (x2_rf_ra1_r == `npuarc_SP_REG)
                    & x2_rf_renb1_r )
                & ( ( x2_rf_wa1_r == `npuarc_SP_REG) 
                    & x2_rf_wenb1_r )
                ;

  x2_sp_write = (  (x2_rf_wa0_r == `npuarc_SP_REG) 
                 & x2_rf_wenb0_r)
              | (  (x2_rf_wa1_r == `npuarc_SP_REG) 
                 & x2_rf_wenb1_r)
              ;

  // Stack Based operation
  x2_sp_mem_op  =  (x2_load_r | x2_store_r) 
                & x2_sp_read
                & !x2_sp_ex_op
                ;

  // Stack Pointer
  x2_ssp_r      = `npuarc_ADDR_SIZE'd0;
  x2_ssp_r      = ar_ssp_r;

  // Stack Pointer Auto Update
  x2_stack_au   =  x2_uop_inst_r
                | (x2_sp_write & !x2_sp_ex_op)
                ;

  x2_limit_val =  x2_sp_mem_op
                 ? ar_aux_stack_base_r [`npuarc_ADDR_RANGE]
                 : ar_aux_stack_top_r [`npuarc_ADDR_RANGE]
                ;

//========================================
//  Stack Violation =
//  1. Non SP operation  :  (Address <  SSP) 
//                        & (Address >= TOP)
//
//  2. SP operation :  
//     a. No Auto Update :  (Address >= BASE) 
//                        | (Address <  SSP) 
//                        | (Address <  TOP) 
//
//     b. Auto Update    :  (address <  TOP) 
//                        | (address >= BASE) 

  x2_limit_chk1 =  (x2_mem_addr_r [`npuarc_ADDR_RANGE] <  x2_ssp_r[`npuarc_ADDR_RANGE])
                ;

  x2_limit_chk2 = (x2_mem_addr_r [`npuarc_ADDR_RANGE] >= x2_limit_val [`npuarc_ADDR_RANGE])
                ;

  x2_limit_chk3 = (x2_mem_addr_r [`npuarc_ADDR_RANGE] < ar_aux_stack_top_r [`npuarc_ADDR_RANGE])
                ;

  x2_stack_viol =  ar_sc_r
                 & (~sp_pending)
                 & (~x2_pref_r)
                 & (x2_load_r | x2_store_r)
                 & (~x2_sp_mem_op
                    ? (x2_limit_chk1 & x2_limit_chk2)
                    : (~x2_stack_au
                       ? (  x2_limit_chk1 
                          | x2_limit_chk2
                          | x2_limit_chk3)
                       : (x2_limit_chk2
                          | x2_limit_chk3)
                       ))
                ;


end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// X3 Stage Control                                                       //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @*
begin : x3_ctrl_PROC
  // This is enable when the x3 stage is enabled
  //
  x3_cg0  = x3_enable;
  
  // This is enabled when only when a new LS address is moving from X2 to X3
  //
  x3_addr_cg0 = (x2_load_r | x2_store_r) & x2_pass & x3_enable;
end

////////////////////////////////////////////////////////////////////////////
//                                                                        //
// Outputs to Exception Logic                                             //
//                                                                        //
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin: sc_viol_regs_PROC
  if (rst_a == 1'b1)
  begin
      x3_stack_viol_r  <= 1'b0;
      x3_sc_efa_r      <= `npuarc_DATA_SIZE'd0;
  end
  else 
  begin
      if (x3_cg0 == 1'b1)
      begin
        x3_stack_viol_r  <= x2_stack_viol & (~x2_kill) & (~db_active);
      end
      
      if (x3_addr_cg0 == 1'b1)
      begin
        x3_sc_efa_r      <= x2_mem_addr_r[`npuarc_DATA_RANGE];
      end
  end
end


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
// Output Assignments                                                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

assign x2_sc_stall =  (x2_load_r | x2_store_r)
                   & ar_sc_r
                   & (~x2_stack_au)
                   & (  ((wa_rf_wa0_r == `npuarc_SP_REG) && wa_rf_wenb0_r)
                      | ((ca_rf_wa0_r == `npuarc_SP_REG) && ca_rf_wenb0_r)
                      | ((x3_rf_wa0_r == `npuarc_SP_REG) && x3_rf_wenb0_r)
                      | ((x3_rf_wa1_r == `npuarc_SP_REG) && x3_rf_wenb1_r)
                      | dp_x2_sp_r
                     )
                   ;

endmodule // alb_sc_pipe
