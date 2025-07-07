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
//   ALB_DCCM_IF                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module acts as an interface to DCCM in case of a multi-core implementation
//  with shared DCCM.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dccm_if.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//

// Set simulation timescale
//
// synopsys translate_off

///////////////////////////////////////////////////////////////////////////
// Common Verilog definitions
///////////////////////////////////////////////////////////////////////////

// Verilog simulator timescale definition for all modules
//
`timescale 1 ns / 10 ps

// synopsys translate_on


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }


module npuarc_alb_dccm_if (

  ////////// Core0 interface ///////////////////////////////////////////
  //
  input                         core0_bank0_cs_lo_r,
  input                         core0_bank0_cs_hi_r,
  input  [10:0]     core0_bank0_addr_lo_r,
  input  [10:0]     core0_bank0_addr_hi_r,
  input                         core0_bank0_we_lo_r,
  input                         core0_bank0_we_hi_r,
  input  [9:0]   core0_bank0_wem_r,
  input  [77:0]      core0_bank0_din_r,
  
  input                         core0_bank0_busy_lo_nxt,   
  input                         core0_bank0_busy_hi_nxt,   
  
  output [77:0]      core0_bank0_dout,   
  output                        dccm_core0_bank0_wait_lo,
  output                        dccm_core0_bank0_wait_hi,

  input                         core0_bank1_cs_lo_r,
  input                         core0_bank1_cs_hi_r,
  input  [10:0]     core0_bank1_addr_lo_r,
  input  [10:0]     core0_bank1_addr_hi_r,
  input                         core0_bank1_we_lo_r,
  input                         core0_bank1_we_hi_r,
  input  [9:0]   core0_bank1_wem_r,
  input  [77:0]      core0_bank1_din_r,
  
  input                         core0_bank1_busy_lo_nxt,   
  input                         core0_bank1_busy_hi_nxt,   
  
  output [77:0]      core0_bank1_dout,   
  output                        dccm_core0_bank1_wait_lo,
  output                        dccm_core0_bank1_wait_hi,

  ////////// DCCM (sram) interface /////////////////////////////////////////
  //

  output                          clk_bank0_lo,   
  output                          clk_bank0_hi,   
  output reg                      dccm_bank0_cs_lo,   
  output reg                      dccm_bank0_cs_hi,   
  output reg [10:0]   dccm_bank0_addr_lo, 
  output reg [10:0]   dccm_bank0_addr_hi, 
  output reg                      dccm_bank0_we_lo,   
  output reg                      dccm_bank0_we_hi,   
  output reg [9:0] dccm_bank0_wem,  
  output reg [77:0]    dccm_bank0_din,
  
  input  [77:0]        dccm_bank0_dout,  

  output                          clk_bank1_lo,   
  output                          clk_bank1_hi,   
  output reg                      dccm_bank1_cs_lo,   
  output reg                      dccm_bank1_cs_hi,   
  output reg [10:0]   dccm_bank1_addr_lo, 
  output reg [10:0]   dccm_bank1_addr_hi, 
  output reg                      dccm_bank1_we_lo,   
  output reg                      dccm_bank1_we_hi,   
  output reg [9:0] dccm_bank1_wem,  
  output reg [77:0]    dccm_bank1_din,
  
  input  [77:0]        dccm_bank1_dout,  


  ////////// General input signals ///////////////////////////////////////////
  //
  input                         clk,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs
  input                         rst_a
// spyglass enable_block W240
);


// Local declarations
//
reg [1:0]   dccm_bank_busy_clock_en;
reg [1:0]   dccm_bank_busy_lo_nxt;
reg [1:0]   dccm_bank_busy_hi_nxt;
reg [1:0]   dccm_bank_busy_lo_next;
reg [1:0]   dccm_bank_busy_hi_next;
reg [1:0]   dccm_bank_busy_lo_r;
reg [1:0]   dccm_bank_busy_hi_r;


reg                     dccm_bank0_clock_en_lo;
reg                     dccm_bank0_clock_en_hi;
reg                     dccm_bank1_clock_en_lo;
reg                     dccm_bank1_clock_en_hi;


//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block defining the clock enable for the busy info            
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dccm_bank_busy_clock_en_PROC
  dccm_bank_busy_clock_en[0] =   dccm_bank_busy_lo_r[0]
                                | dccm_bank_busy_hi_r[0]
                                | core0_bank0_busy_lo_nxt
                                | core0_bank0_busy_hi_nxt
                                ;
  dccm_bank_busy_clock_en[1] =   dccm_bank_busy_lo_r[1]
                                | dccm_bank_busy_hi_r[1]
                                | core0_bank1_busy_lo_nxt
                                | core0_bank1_busy_hi_nxt
                                ;
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Asynchronous block defining the busy nxt value            
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dccm_bank_busy_nxt_PROC
  dccm_bank_busy_lo_nxt[0] = core0_bank0_busy_lo_nxt;
  dccm_bank_busy_hi_nxt[0] = core0_bank0_busy_hi_nxt;
  
  dccm_bank_busy_lo_nxt[1] = core0_bank1_busy_lo_nxt;
  dccm_bank_busy_hi_nxt[1] = core0_bank1_busy_hi_nxt;
  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
//  Asynchronous block defining the module output: bank_wait
//                                                                           
//////////////////////////////////////////////////////////////////////////////
assign  dccm_core0_bank0_wait_lo = dccm_bank_busy_lo_r[0];
assign  dccm_core0_bank0_wait_hi = dccm_bank_busy_hi_r[0];
    
    
assign  dccm_core0_bank1_wait_lo = dccm_bank_busy_lo_r[1];
assign  dccm_core0_bank1_wait_hi = dccm_bank_busy_hi_r[1];
    
    


//////////////////////////////////////////////////////////////////////////////
//                                                                           
//  Asynchronous block defining the SRAM interface
//                                                                           
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dccm_bank_sram_ctl_PROC

  dccm_bank0_cs_lo    = core0_bank0_cs_lo_r;  
  dccm_bank0_cs_hi    = core0_bank0_cs_hi_r;  
  dccm_bank0_addr_lo  = core0_bank0_addr_lo_r;
  dccm_bank0_addr_hi  = core0_bank0_addr_hi_r;
  dccm_bank0_we_lo    = core0_bank0_we_lo_r;
  dccm_bank0_we_hi    = core0_bank0_we_hi_r;
  dccm_bank0_wem      = core0_bank0_wem_r;
  dccm_bank0_din      = core0_bank0_din_r;
  
  dccm_bank1_cs_lo    = core0_bank1_cs_lo_r;  
  dccm_bank1_cs_hi    = core0_bank1_cs_hi_r;  
  dccm_bank1_addr_lo  = core0_bank1_addr_lo_r;
  dccm_bank1_addr_hi  = core0_bank1_addr_hi_r;
  dccm_bank1_we_lo    = core0_bank1_we_lo_r;
  dccm_bank1_we_hi    = core0_bank1_we_hi_r;
  dccm_bank1_wem      = core0_bank1_wem_r;
  dccm_bank1_din      = core0_bank1_din_r;
  
end

//////////////////////////////////////////////////////////////////////////////
//                                                                           
// Output drivers
//                                                                           
//////////////////////////////////////////////////////////////////////////////
assign core0_bank0_dout = dccm_bank0_dout;
assign core0_bank1_dout = dccm_bank1_dout;


//////////////////////////////////////////////////////////////////////////////
//                                                                           
//  Module instantiation: clockgates 
//                                                                           
//////////////////////////////////////////////////////////////////////////////

always @*
begin : dccm_bank_clock_en_PROC
  
  // Clock enables
  //
  dccm_bank0_clock_en_lo = core0_bank0_cs_lo_r;
  dccm_bank0_clock_en_hi = core0_bank0_cs_hi_r;
  dccm_bank1_clock_en_lo = core0_bank1_cs_lo_r;
  dccm_bank1_clock_en_hi = core0_bank1_cs_hi_r;

  
end




npuarc_clkgate u_clkgate_dccm_0_lo (
  .clk_in            (clk                      ),
  .clock_enable      (dccm_bank0_clock_en_lo),
  .clk_out           (clk_bank0_lo          )
);

npuarc_clkgate u_clkgate_dccm_0_hi (
  .clk_in            (clk                      ),
  .clock_enable      (dccm_bank0_clock_en_hi),
  .clk_out           (clk_bank0_hi          )
);

npuarc_clkgate u_clkgate_dccm_1_lo (
  .clk_in            (clk                      ),
  .clock_enable      (dccm_bank1_clock_en_lo),
  .clk_out           (clk_bank1_lo          )
);

npuarc_clkgate u_clkgate_dccm_1_hi (
  .clk_in            (clk                      ),
  .clock_enable      (dccm_bank1_clock_en_hi),
  .clk_out           (clk_bank1_hi          )
);




//////////////////////////////////////////////////////////////////////////////
//                                                                          
// Synchronous elements                         
//                                                                          
//////////////////////////////////////////////////////////////////////////////

always @*
begin : dccm_bank_busy_comb_PROC
   dccm_bank_busy_lo_next = dccm_bank_busy_lo_r;
   dccm_bank_busy_hi_next = dccm_bank_busy_hi_r;
    if (dccm_bank_busy_clock_en[0])
    begin
      dccm_bank_busy_lo_next[0] = dccm_bank_busy_lo_nxt[0];
      dccm_bank_busy_hi_next[0] = dccm_bank_busy_hi_nxt[0];
    end
    
    if (dccm_bank_busy_clock_en[1])
    begin
      dccm_bank_busy_lo_next[1] = dccm_bank_busy_lo_nxt[1];
      dccm_bank_busy_hi_next[1] = dccm_bank_busy_hi_nxt[1];
    end
    
end

always @(posedge clk or posedge rst_a)
begin : dccm_bank_busy_reg_PROC
  if (rst_a == 1'b1)
  begin
    dccm_bank_busy_lo_r   <= 2'b00;
    dccm_bank_busy_hi_r   <= 2'b00;
  end
  else
  begin
    dccm_bank_busy_lo_r <= dccm_bank_busy_lo_next;
    dccm_bank_busy_hi_r <= dccm_bank_busy_hi_next;
  end    
end


endmodule // alb_dmp_dccm_ctrl


