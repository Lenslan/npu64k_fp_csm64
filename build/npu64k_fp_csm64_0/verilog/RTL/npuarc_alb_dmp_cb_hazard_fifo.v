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
//   ALB_DMP_CB_HAZARD_FIFO                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the copy back hazard fifo. This module is 
//  responsible for capturing the eviction addresses that are sent out and 
//  perform hazard detection
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_cb_hazard_fifo.vpp
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


//POST_PROCESS { prefix:"//D:", wire_prefix:"t_", edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  rst: "rst_a", edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_err", encode_reset: true, add_reset_sensitivity: 1 } }


module npuarc_alb_dmp_cb_hazard_fifo (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some inputs are not used in certain configurations
  ////////// General input signals ///////////////////////////////////////////
  //
  input                        clk,                 
  input                        rst_a,               
  
  ////////// Entry of the FIFO ////////////////////////////////////////
  //
  input                        cb_wr_push,        // command sent out
  input [39:0]         cb_wr_addr,        // command address
  input                        cb_evict_error_r, // ecc error during eviction 

  ////////// Removal from the FIFO ////////////////////////////////////////
  //
  input                        cb_wr_done,
  input                        cb_err_wr,
  
  ////////// Conflict detection ///////////////////////////////////////////
  //
  input                        x3_load_r,       // X3 load  
  input                        x3_store_r,      // X3 load  
  input [39:0]         x3_mem_addr0_r,  // X3 memory address
  input [39:0]         x3_mem_addr1_r,  // X3 memory address
  input                        dc3_dc_target,   // X3 memory target
  input                        dc3_dt_line_cross_r,  // addr1 is valid
  
  output wire                  cbh_pending,      // copy back pending
  output wire                  cbh_hit,          // hit in the hazard fifo
  output wire                  cbh_full,         // fifo is full
  
  ////////// Bus errors ///////////////////////////////////////////////////
  //
  output reg [39:6]  cbh_err_addr,      // top address
  output reg                   cbh_err_req_r,     // bus error during eviction
  input                        cbh_err_ack        // err ack by EXU
// leda NTL_CON37 on
// leda NTL_CON13C on
);


// Local declarations
// 
// This computes the log2 of the depth paramter
//

reg [2-1:0]         cbh_valid_r;
reg [2-1:0]         cbh_valid_nxt;
reg [2-1:0]         cbh_err_r;
reg [2-1:0]         cbh_err_nxt;
reg [39:6]    cbh_addr_r[2-1:0];
reg [39:6]    cbh_addr_r0;
reg [39:6]    cbh_addr_r1;
reg [1:0]           cbh_wr_ptr_nxt; 
reg [1:0]           cbh_rd_ptr_nxt;
reg [1:0]           cbh_wr_ptr_r; 
reg [1:0]           cbh_rd_ptr_r;

reg [2-1:0]         cbh_addr0_match;
reg [2-1:0]         cbh_addr1_match;

reg                     cbh_err_cg0;       
reg                     cbh_err_req_nxt;   
reg                     cbh_err_pop;       
reg                     cbh_err_state_r; 
reg                     cbh_err_state_nxt;

reg                     cbh_hit0;
reg                     cbh_hit1;

wire [1-1:0]        wr_ptr0_r;
wire [1-1:0]        rd_ptr0_r;

wire                    cb_wr_pop;
wire                    error_2bit;
//////////////////////////////////////////////////////////////////////////////
// Handy variables
//
//////////////////////////////////////////////////////////////////////////////
assign cb_wr_pop = (  (cb_wr_done)
                      & (~error_2bit)          
                   ) 
                   | cbh_err_pop;

assign wr_ptr0_r = cbh_wr_ptr_r[1-1:0];
assign rd_ptr0_r = cbh_rd_ptr_r[1-1:0];

assign dc3_addr0_valid = (x3_load_r | x3_store_r) & dc3_dc_target;
assign dc3_addr1_valid = (x3_load_r | x3_store_r) & dc3_dc_target & dc3_dt_line_cross_r;

assign error_2bit  = cbh_err_r[rd_ptr0_r];
//////////////////////////////////////////////////////////////////////////////
// Conflict detection
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : cbh_addr0_match_PROC
  integer i;
  
  cbh_addr0_match = {2{1'b0}};
  
  for (i = 0; i < 2; i = i + 1) 
  begin  
    cbh_addr0_match[i] = (    x3_mem_addr0_r[39:6]  
                             ==  cbh_addr_r[i]); 
  end
end

always @*
begin : cbh_addr1_match_PROC
  integer i;
  
  cbh_addr1_match = {2{1'b0}};
  
  for (i = 0; i < 2; i = i + 1) 
  begin  
    cbh_addr1_match[i] = (    x3_mem_addr1_r[39:6]  
                             ==  cbh_addr_r[i]); 
  end
end



always @*
begin : cbh_hit0_PROC
  integer i;
  
  cbh_hit0 = 1'b0;
  
  for (i = 0; i < 2; i = i + 1) 
  begin  
    cbh_hit0 =    cbh_hit0 
               || (     cbh_valid_r[i]
                     && cbh_addr0_match[i]   
                     && dc3_addr0_valid
                   );    
  end
end

always @*
begin : cbh_hit1_PROC
  integer i;
  
  cbh_hit1 = 1'b0;
  
  for (i = 0; i < 2; i = i + 1) 
  begin  
    cbh_hit1 =    cbh_hit1 
               || (     cbh_valid_r[i]
                     && cbh_addr1_match[i]   
                     && dc3_addr1_valid
                   );    
  end
end



////////////////////////////////////////////////////////////////////////////
// Outputs
//
////////////////////////////////////////////////////////////////////////////
assign cbh_pending  = (| cbh_valid_r);
assign cbh_hit      = (cbh_hit0 | cbh_hit1);
assign cbh_full     = (& cbh_valid_r);

//////////////////////////////////////////////////////////////////////////////
//FSM to report bus error on flushes
//
//////////////////////////////////////////////////////////////////////////////

parameter CBH_ERR_DEFAULT  = 1'b0;
parameter CBH_ERR_WAIT_ACK = 1'b1;

always @*
begin : dmu_err_state_fsm_PROC
  
  cbh_err_req_nxt      = cbh_err_req_r;
  
  cbh_err_cg0          = | cbh_valid_r;
  cbh_err_addr         = cbh_addr_r[rd_ptr0_r];
  cbh_err_pop          = 1'b0;
  cbh_err_state_nxt    = cbh_err_state_r;
  
  case (cbh_err_state_r)
  CBH_ERR_DEFAULT:
  begin
    if (   cb_err_wr
         | (error_2bit & (cb_err_wr | cb_wr_done))
       )
    begin
      cbh_err_req_nxt      = 1'b1;
      cbh_err_state_nxt    = CBH_ERR_WAIT_ACK;
    end
  end
  
  default: // DMU_ERR_WAIT_ACK
  begin
    if (cbh_err_ack)
    begin
      // We are now raising a bus error exception
      //
      cbh_err_pop          = 1'b1;
      cbh_err_req_nxt      = 1'b0;
      cbh_err_state_nxt    = CBH_ERR_DEFAULT;
    end
  end
  endcase
end


////////////////////////////////////////////////////////////////////////////
// Synchronous processes
//
////////////////////////////////////////////////////////////////////////////

// leda FM_1_7 off
// LMD: Signal assigned more than once in a single flow of control
// LJ:  Conflict covered by assertions
//
// leda NTL_RST03 off
// LMD: All registers must be asynchronously set or reset Range:0-51
// LJ:  Synthesis will take care
//
// spyglass disable_block STARC-2.3.4.3 Ar_resetcross01
// SMD: Has neither asynchronous set nor asynchronous reset
// SJ:  Datapath items not reset
//
// spyglass disable_block STARC05-1.3.1.3
// SMD: rst_nmi_a used as synchronous reset for mq_addr_r
// SJ:  functionally works as intended
always @*
begin : cbh_sync_nxt_PROC
  cbh_valid_nxt      = cbh_valid_r;
  cbh_err_nxt        = cbh_err_r;
  begin
    if (cb_wr_push)
    begin
      cbh_valid_nxt[wr_ptr0_r]     = 1'b1;
      cbh_err_nxt[wr_ptr0_r]       =  cb_evict_error_r
                                   ;
    end

    if (   cbh_valid_r[rd_ptr0_r]
        & cb_evict_error_r)
    begin
      // Two-bit ECC/parity error when reading data memories for eviction
      //
      cbh_err_nxt[rd_ptr0_r] = 1'b1;
    end
    
    if (cb_wr_pop)
    begin
      cbh_valid_nxt[rd_ptr0_r]     = 1'b0;
      cbh_err_nxt[rd_ptr0_r]       = 1'b0;
    end
  end
end
always @(posedge clk or posedge rst_a)
begin : cbh_sync_PROC
  if (rst_a == 1'b1)
  begin
    cbh_valid_r     <= {2{1'b0}};
    cbh_err_r       <= {2{1'b0}};
  end
  else
  begin
    cbh_valid_r     <= cbh_valid_nxt;
    cbh_err_r       <= cbh_err_nxt;
  end
end
// spyglass enable_block STARC05-1.3.1.3

// spyglass disable_block ResetFlop-ML
// SMD: Has neither asynchronous set/reset nor synchronous set/reset
// SJ:  Datapath items not reset
always @*
begin : cbh_addr_sync_comb_PROC
    cbh_addr_r[0]      = cbh_addr_r0;
    cbh_addr_r[1]      = cbh_addr_r1;
end
always @(posedge clk)
begin : cbh_addr_sync0_PROC
  if ((cb_wr_push) & (wr_ptr0_r == 0))
  begin
    cbh_addr_r0  <= cb_wr_addr[39:6];
  end
end
always @(posedge clk)
begin : cbh_addr_sync1_PROC
  if ((cb_wr_push) & (wr_ptr0_r == 1))
  begin
    cbh_addr_r1  <= cb_wr_addr[39:6];
  end
end
// spyglass enable_block ResetFlop-ML

// leda NTL_RST03 on
// leda FM_1_7 on
// spyglass enable_block STARC-2.3.4.3 Ar_resetcross01


// leda BTTF_D002 off
// leda B_3200 off
// LMD: Unequal length LHS and RHS in assignment LHS
// LJ:  One bit incrementor. Never overflows

// leda W484 off
// LMD: Possible loss of carry/borrow in addition/subtraction LHS
// LJ: Pointer arithmetic: incremented value will not overflow
// Helpers
always @*
begin : cbh_ptr_sync_nxt_PROC
  cbh_wr_ptr_nxt = cbh_wr_ptr_r;
  cbh_rd_ptr_nxt = cbh_rd_ptr_r;
  begin
    if (cb_wr_push)
    begin
      cbh_wr_ptr_nxt = cbh_wr_ptr_r + 1'b1;
    end
    
    if (cb_wr_pop)
    begin
      cbh_rd_ptr_nxt = cbh_rd_ptr_r + 1'b1;
    end
  end
end
always @(posedge clk or posedge rst_a)
begin : cbh_ptr_sync_PROC
  if (rst_a == 1'b1)
  begin
    cbh_wr_ptr_r <= {(1+1){1'b0}};
    cbh_rd_ptr_r <= {(1+1){1'b0}};
  end
  else
  begin
    cbh_wr_ptr_r <= cbh_wr_ptr_nxt;
    cbh_rd_ptr_r <= cbh_rd_ptr_nxt;
  end
end
// leda W484 on
// leda BTTF_D002 on
// leda B_3200 on

always @(posedge clk or posedge rst_a)
begin : cbh_err_sync_PROC
  if (rst_a == 1'b1)
  begin
    cbh_err_state_r <= CBH_ERR_DEFAULT;
    cbh_err_req_r   <= 1'b0;
  end
  else if (cbh_err_cg0)
  begin
    cbh_err_state_r <= cbh_err_state_nxt; 
    cbh_err_req_r   <= cbh_err_req_nxt;  
  end
end

endmodule //  alb_dmp_cb_hazard_fifo


