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
// ALB_DMP_LQWQ_IF
// 
// 
// 
// 
//
// ===========================================================================
//
// Description:
//  This module unifies the LQ/WQ interface towards the BIU
//    
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_lqwq_if.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }
//D: error_signal { name: "alb_dmp_ibp_buf0_err" }
//D: error_signal { name: "alb_dmp_ibp_buf1_err" }

module npuarc_alb_dmp_lqwq_if (
  ////////// LQ CMD channel ///////////////////////////////////////////////
  //
  input                       i0_cmd_valid, 
  input                       i0_cmd_burst_size,                   
  input                       i0_cmd_read,                  
  output reg                  i0_cmd_accept,                
  input [`npuarc_PADDR_RANGE]        i0_cmd_addr,                  
  input                       i0_cmd_lock,                  
  input                       i0_cmd_excl,
  input [2:0]                 i0_cmd_data_size,                  
  input [1:0]                 i0_cmd_prot,                  

  ////////// LQ RD DATA channel ///////////////////////////////////////////////
  //
  output                      i0_rd_valid,                  
  output                      i0_err_rd,                  
  output                      i0_rd_excl_ok,
  output                      i0_rd_last,                   
  input                       i0_rd_accept,                 
  output  [`npuarc_DOUBLE_RANGE]     i0_rd_data,     
  
  ////////// WQ CMD channel /////////////////////////////////////////////////
  //
  input                       i1_cmd_valid,   
  input                       i1_cmd_cache,   
  input                       i1_cmd_burst_size,   
  output reg                  i1_cmd_accept,  
  input [`npuarc_PADDR_RANGE]        i1_cmd_addr,    
  input [2:0]                 i1_cmd_data_size,    
  input                       i1_cmd_lock,                  
  input                       i1_cmd_excl,
  input [1:0]                 i1_cmd_prot,                  
  
  ////////// WQ WR DATA channel ///////////////////////////////////////////////
  //
  input                       i1_wr_valid,    
  input                       i1_wr_last,    
  output reg                  i1_wr_accept,   
  input [`npuarc_DOUBLE_BE_RANGE]    i1_wr_mask,         
  input [`npuarc_DOUBLE_RANGE]       i1_wr_data,    
  
  ////////// WQ WR RESPONSE channel ///////////////////////////////////////////////
  //
  output                      i1_wr_done,
  output                      i1_wr_excl_done,
  output                      i1_err_wr,
  input                       i1_wr_resp_accept,

  ////////// Unified interface with BIU ////////////////////////////////////////
  //
  output                      o_cmd_valid, 
  output                      o_cmd_cache, 
  output                      o_cmd_burst_size,                   
  output                      o_cmd_read,                  
  input                       o_cmd_accept,                
  output [`npuarc_PADDR_RANGE]       o_cmd_addr,                  
  output                      o_cmd_lock,                  
  output                      o_cmd_excl,
  output [2:0]                o_cmd_data_size,                  
  output [1:0]                o_cmd_prot,                  

  output                      o_wr_valid,    
  output                      o_wr_last,    
  input                       o_wr_accept,   
  output [`npuarc_DOUBLE_BE_RANGE]   o_wr_mask,         
  output [`npuarc_DOUBLE_RANGE]      o_wr_data,    
  
  input                       o_rd_valid,                  
  input                       o_err_rd,                  
  input                       o_rd_excl_ok,
  input                       o_rd_last,                   
  output                      o_rd_accept,                 
  input  [`npuarc_DOUBLE_RANGE]      o_rd_data,     
  
  input                       o_wr_done,
  input                       o_wr_excl_done,
  input                       o_err_wr,
  output                      o_wr_resp_accept,
  
  ////////// Clock and reset /////////////////////////////////////////////////
  //
  input                       clk,
  input                       rst_a
);

/////////////////////////////////////////////////////////////////////////////
//  Local declaration: cmd interface
//
//////////////////////////////////////////////////////////////////////////////

reg                  i_cmd_valid;
reg [50-1:0] i_cmd_data;
wire                 i_cmd_accept;

/////////////////////////////////////////////////////////////////////////////
//  Local declaration: wr interface
//
//////////////////////////////////////////////////////////////////////////////
reg                 i1_wr_valid_qual;

reg                 i_wr_incr;
reg                 i_wr_decr;
reg                 i_wr_data_outstanding_cg0;
reg [2:0]           i_wr_data_outstanding_r;
reg [2:0]           i_wr_data_outstanding_nxt;

/////////////////////////////////////////////////////////////////////////////
// Unified command channel: the IBP inputs are mutually exlcusive, i.e.: they
// never assert command valid simultaneously
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : i_cmd_PROC
  // Prepare cmd package to the IBP buf
  //
  i_cmd_valid = i0_cmd_valid | i1_cmd_valid;
  
  if (i1_cmd_valid)
  begin
    i_cmd_data  = {i1_cmd_burst_size,
                   1'b0,                // cmd_read
                   i1_cmd_addr,
                   i1_cmd_data_size,
                   i1_cmd_lock,
                   i1_cmd_excl,
                   i1_cmd_prot,
                   i1_cmd_cache};
  end
  else
  begin
    i_cmd_data  = {i0_cmd_burst_size,
                   i0_cmd_read,        // cmd_read
                   i0_cmd_addr,
                   i0_cmd_data_size,
                   i0_cmd_lock,
                   i0_cmd_excl,
                   i0_cmd_prot,
                   1'b0};             // cmd_cache 
  end
end



npuarc_alb_dmp_ibp_buf # (
  .WIDTH (50)
) alb_dmp_ibp_buf0 (
  .i_valid   (i_cmd_valid),
  .i_ready   (i_cmd_accept),
  .i_data    (i_cmd_data),
  
  .o_valid   (o_cmd_valid),
  .o_ready   (o_cmd_accept),
  .o_data    ({o_cmd_burst_size,
               o_cmd_read,
               o_cmd_addr,
               o_cmd_data_size,
               o_cmd_lock,
               o_cmd_excl,
               o_cmd_prot,
               o_cmd_cache}),

  .clk       (clk),
  .rst_a     (rst_a)
);

/////////////////////////////////////////////////////////////////////////////
// Command acceptance
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : i_cmd_accept_PROC
  i0_cmd_accept = i_cmd_accept;
  i1_cmd_accept = i_cmd_accept;
end


/////////////////////////////////////////////////////////////////////////////
// WR data interface
//
//////////////////////////////////////////////////////////////////////////////

wire i1_wr_accept_prel;

npuarc_alb_dmp_ibp_buf # (
  .WIDTH (73)
) alb_dmp_ibp_buf1 (
  .i_valid   (i1_wr_valid_qual),
  .i_ready   (i1_wr_accept_prel),
  .i_data    ({i1_wr_last,
               i1_wr_mask,
               i1_wr_data}),
  
  .o_valid   (o_wr_valid),
  .o_ready   (o_wr_accept),
  .o_data    ({o_wr_last,
               o_wr_mask,
               o_wr_data}),

  .clk       (clk),
  .rst_a     (rst_a)
);

/////////////////////////////////////////////////////////////////////////////
// WR valid
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : i_wr_valid_PROC
  // Avoid sending wr_valid before cmd_valid. 
  // 
  i1_wr_valid_qual =  (i1_wr_valid & i1_cmd_accept)
                    | (i1_wr_valid & (|i_wr_data_outstanding_r));
end
/////////////////////////////////////////////////////////////////////////////
// WR acceptance
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : i_wr_accept_PROC
  // We can't accept the write data before the write command is accepted
  //
  i1_wr_accept =   (i1_wr_accept_prel & i1_cmd_accept)
                 | (i1_wr_accept_prel & (|i_wr_data_outstanding_r));
end

/////////////////////////////////////////////////////////////////////////////
// Track pending writes
//
//////////////////////////////////////////////////////////////////////////////

// spyglass disable_block W484
// SMD: Possible loss of carry/borrow in addition/subtraction LHS
// SJ: Pointer arithmetic: incremented value will not overflow
//
// spyglass disable_block W164a
// SMD: LHS width < RHS in assignment
// SJ:  correct width will be used

always @*
begin : i_outstanding_wr_PROC
  // Increment the number of outstanding writes when the write commannd is sent
  // out
  //
  i_wr_incr = i1_cmd_valid & i1_cmd_accept;
  
  // Decrement the number of outstanding writes (data pahse) when the last 
  // write data is accepted
  //
  i_wr_decr = i1_wr_valid & i1_wr_last & i1_wr_accept;
  
  // Clock gate: Only enable the clock when either incrementing or decrementing
  //
  i_wr_data_outstanding_cg0 = i_wr_incr | i_wr_decr;
  
  // Next value for the number of outstanding writes
  //
  i_wr_data_outstanding_nxt =  i_wr_data_outstanding_r 
                             + i_wr_incr 
                             - i_wr_decr;
end

// spyglass enable_block W164a
// spyglass enable_block W484


reg [2:0] i_wr_data_outstanding_cnxt;
reg i_wr_data_outstanding_ccg;
//
always @*
begin : i_wr_data_outstanding_cnxt_PROC

  i_wr_data_outstanding_cnxt =
                       i_wr_data_outstanding_nxt;

  i_wr_data_outstanding_ccg = 1'b0
                  |   i_wr_data_outstanding_cg0
                  ;

end // block : 

always @(posedge clk or posedge rst_a)
begin : i_wr_data_outstanding_reg_PROC
  if (rst_a == 1'b1)
  begin
    i_wr_data_outstanding_r <= 3'b000;
  end
  else if (i_wr_data_outstanding_ccg == 1'b1)
  begin
    i_wr_data_outstanding_r <= i_wr_data_outstanding_cnxt;
  end
end

/////////////////////////////////////////////////////////////////////////////
// Output assignments (pass through)
//
//////////////////////////////////////////////////////////////////////////////
assign  i0_rd_valid      = o_rd_valid;               
assign  i0_err_rd        = o_err_rd;               
assign  i0_rd_excl_ok    = o_rd_excl_ok;
assign  i0_rd_last       = o_rd_last;              
assign  i0_rd_data       = o_rd_data;   

assign  o_rd_accept      = i0_rd_accept;  


assign i1_wr_done        = o_wr_done;
assign i1_wr_excl_done   = o_wr_excl_done;
assign i1_err_wr         = o_err_wr;

assign o_wr_resp_accept  = i1_wr_resp_accept; // 1'b1

endmodule // alb_dmp_lqwq_if

