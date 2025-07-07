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
//   ALB_DMP_LQ_PORT                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Load Queue interface to ICCM/MEM.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_lq_port.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_lq_port (
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  ////////// General input signals ///////////////////////////////////////////
  //
  input                          clk,               // clock
  input                          rst_a,             // reset

  ////////// Interface with cmd FIFO /////////////////////////////////////////
  //
  input                          lq_fifo_cmd_valid,         // top of FIFO
  input [`npuarc_PADDR_RANGE]           lq_fifo_cmd_addr,          // top of FIFO
  input [`npuarc_PADDR_RANGE]           lq_fifo_cmd_addr1,         // top of FIFO
  input                          lq_fifo_cmd_target,        // target
  input                          lq_fifo_cmd_unaligned,     // top of FIFO
  input                          lq_fifo_cmd_1k_cross,
  input                          lq_fifo_empty_r,

  
  ////////// Command handshake ///////////////////////////////////////////
  //
  output reg                     lq_cmd_valid,  
  output reg [`npuarc_PADDR_RANGE]      lq_cmd_addr,
  output reg                     lq_cmd_burst_size,   
  input                          lq_cmd_accept, 
 
  ////////// Popping  LQ  cmd FIFO ///////////////////////////////////////////
  //
  output reg                     lq_cmd_to_fifo,
  output reg                     lq_cmd_pop,
  
  //////////  Data handshake /////////////////////////////////////////////////
  //
  input                          lq_rd_valid,
  input                          lq_rd_excl_ok,
  input                          lq_err_rd,
  input                          lq_rd_accept,
  
  input [`npuarc_PADDR_RANGE]           lq_fifo_addr,
  input                          lq_fifo_unaligned,
  input                          lq_fifo_llock,
  output reg                     lq_toggle_arb_ok,
  output reg                     lq_data_even_cg0,
  output reg                     lq_data_odd_cg0,
  output reg                     lq_pass,
  output reg                     lq_pass_err
// leda NTL_CON13C on  
);


// Local declarations
// 

reg                lq_cmd_state_cg0;
reg                lq_cmd_state_nxt;
reg                lq_cmd_state_r;

reg                lq_addr_cross_cg0;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [`npuarc_PADDR_RANGE] lq_addr_cross_r;
// leda NTL_CON32 on
reg [`npuarc_PADDR_RANGE] lq_addr_cross_nxt;

//////////////////////////////////////////////////////////////////////////////
// Command transfer FSM
// 
//////////////////////////////////////////////////////////////////////////////

parameter LQ_CMD_DEFAULT         = 1'b0;
parameter LQ_CMD_BOUNDARY_CROSS  = 1'b1;

always @*
begin : lq_cmd_fsm_PROC
  // Check if we have any new command to be sent out
  //
  lq_cmd_valid      =    lq_fifo_cmd_valid
                      & lq_fifo_cmd_target;
  
  lq_cmd_addr       = lq_fifo_cmd_addr; 
  lq_cmd_burst_size =     lq_fifo_cmd_unaligned
                      & (~lq_fifo_cmd_1k_cross);
  
  lq_addr_cross_cg0 = 1'b0;
  lq_addr_cross_nxt = lq_addr_cross_r;
  
  lq_cmd_state_cg0  = !lq_fifo_empty_r;
  lq_cmd_state_nxt  = lq_cmd_state_r;
  lq_cmd_to_fifo    = 1'b0;
  lq_cmd_pop        = 1'b0;
  
  case (lq_cmd_state_r)
  LQ_CMD_DEFAULT:
  begin
    if (  lq_cmd_valid
        & lq_cmd_accept)
    begin
      // Command has been transferred to the mem
      //
      lq_cmd_to_fifo    = 1'b1;
      
      if (  lq_fifo_cmd_unaligned
         &  lq_fifo_cmd_1k_cross)
      begin
        // Watch out, this is an unaligned transfer
        //
        lq_addr_cross_cg0 = 1'b1;
// leda BTTF_D002 off
// leda W484 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  implicit 32-bit value
        lq_addr_cross_nxt      = lq_fifo_cmd_addr1;
// leda W484 on    
// leda BTTF_D002 on    
        lq_cmd_state_nxt  = LQ_CMD_BOUNDARY_CROSS;
      end
      else
      begin
        // Just pop the command.
        //
        lq_cmd_pop       = 1'b1;
      end
    end
  end
  
  default: // LQ_CMD_BOUNDARY_CROSS
  begin
    // We need to transfer the second command
    //
    lq_cmd_valid      = 1'b1;
    lq_cmd_addr       = lq_addr_cross_r;
    lq_cmd_burst_size = 1'b0;
    
    if (lq_cmd_accept)
    begin
      lq_cmd_pop       = 1'b1;
      lq_cmd_state_nxt = LQ_CMD_DEFAULT;
    end
  end  
  endcase  
end


//////////////////////////////////////////////////////////////////////////////
// Data transfer FSM
// 
//////////////////////////////////////////////////////////////////////////////
reg   lq_data_state_cg0;
reg   lq_data_state_nxt;
reg   lq_data_state_r;

reg   lq_bank_even_cg0;
reg   lq_bank_even_nxt;
reg   lq_bank_even_r;

reg   lq_first_err_cg0;
reg   lq_first_err_nxt;
reg   lq_first_err_r;

parameter LQ_DATA_DEFAULT    = 1'b0;
parameter LQ_DATA_UNALIGNED  = 1'b1;

always @*
begin : lq_data_fsm_PROC
  lq_data_state_cg0   = !lq_fifo_empty_r;
  lq_data_state_nxt   = lq_data_state_r;
  
  lq_bank_even_cg0    = 1'b0;
  lq_bank_even_nxt    = lq_bank_even_r;
  
  lq_data_even_cg0    = 1'b0;
  lq_data_odd_cg0     = 1'b0;
  
  lq_toggle_arb_ok    = 1'b1;
  
  lq_first_err_cg0    = 1'b0;
  lq_first_err_nxt    = lq_first_err_r;
  
  lq_pass             = 1'b0;
  lq_pass_err         = 1'b0;
  
  case (lq_data_state_r)
  LQ_DATA_DEFAULT:
  begin
    if (  (lq_rd_valid | lq_err_rd)
        & lq_rd_accept)
    begin
      lq_data_even_cg0    = !lq_fifo_addr[3];
      lq_data_odd_cg0     = lq_fifo_addr[3];
      lq_first_err_cg0    = lq_fifo_unaligned;
      
      if (lq_fifo_unaligned)
      begin
        lq_bank_even_cg0    = 1'b1;
        lq_toggle_arb_ok    = 1'b0;
        lq_bank_even_nxt    = lq_fifo_addr[3];
        lq_first_err_nxt    = lq_err_rd;
        lq_data_state_nxt   = LQ_DATA_UNALIGNED;
      end
      else
      begin
        // Aligned
        //
        lq_pass             = 1'b1;
        lq_pass_err         =   lq_err_rd
                              | (lq_fifo_llock & (~lq_rd_excl_ok))
                              ;
      end
    end
  end
  
  default: // LQ_DATA_UNALIGNED:
  begin
    // Do not let the arbiter to toggle arbitration
    //
    lq_toggle_arb_ok = 1'b0;
    
    if (  (lq_rd_valid | lq_err_rd)
        & lq_rd_accept)
    begin
      lq_data_even_cg0    = lq_bank_even_r;
      lq_data_odd_cg0     = !lq_bank_even_r;
      lq_first_err_cg0    = 1'b1;
      
      lq_pass             = 1'b1;
      lq_pass_err         = lq_first_err_r | lq_err_rd;
      lq_first_err_nxt    = 1'b0;
      lq_data_state_nxt   = LQ_DATA_DEFAULT;
    end
  end  
  endcase  
end

//////////////////////////////////////////////////////////////////////////////
// Synchronous processes
// 
//////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : lq_cmd_state_reg_PROC
  if (rst_a == 1'b1) 
  begin
    lq_cmd_state_r   <= LQ_CMD_DEFAULT;
  end
  else
  begin  
    if (lq_cmd_state_cg0)
    begin
      lq_cmd_state_r <= lq_cmd_state_nxt;
    end
  end
end

// leda NTL_RST03 off
// leda S_1C_R off
// LMD: A flipflop without reset
// LJ:  Data path signals that dont require a reset
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
always @(posedge clk)
begin : lq_addr_cross_reg_PROC
  if (lq_addr_cross_cg0 == 1'b1)                       
  begin                                            
    lq_addr_cross_r <= lq_addr_cross_nxt;  
  end                                              
end
// leda S_1C_R on
// leda NTL_RST03 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01


always @(posedge clk or posedge rst_a)
begin : lq_data_state_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq_data_state_r    <= LQ_DATA_DEFAULT;
  end
  else
  begin  
    if (lq_data_state_cg0)
    begin
      lq_data_state_r  <= lq_data_state_nxt;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : lq_bank_even_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq_bank_even_r    <= 1'b0;
  end
  else
  begin  
    if (lq_bank_even_cg0)
    begin
      lq_bank_even_r <= lq_bank_even_nxt;
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : lq_first_err_reg_PROC
  if (rst_a == 1'b1)
  begin
    lq_first_err_r    <= 1'b0;
  end
  else
  begin  
    if (lq_first_err_cg0)
    begin
      lq_first_err_r <= lq_first_err_nxt;
    end
  end
end

endmodule // alb_dmp_lq_port
