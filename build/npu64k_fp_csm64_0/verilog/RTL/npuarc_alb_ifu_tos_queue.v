// Library ARCv2HS-3.5.999999999
///---------------------------------------------------------------------------
///
/// Copyright (C) 2012-2013 Synopsys, Inc. All rights reserved.
///
/// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary 
/// work of Synopsys, Inc., and is fully protected under copyright and 
/// trade secret laws. You may not view, use, disclose, copy, or distribute 
/// this file or any information contained herein except pursuant to a 
/// valid written license from Synopsys, Inc.
///
/// The entire notice above must be reproduced on all authorized copies.
///
///---------------------------------------------------------------------------
//
//  IFU TOS QUEUE
//
// ===========================================================================
//
// Description:
// This module implements the TOS Queue.
// The TOS (Top of Stack) info from the branch predictor is stored in this queue instead 
// passing the info directly to the execte block. Based on the outcome of the 
// branch (mispredict, commit), the branch info is fed back to the branch 
// predictor, so that the predictor can update the algorithm based on the
// outcome of the branch in the execute state 
// ===========================================================================
// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


//POST_PROCESS { edc_results: { OK: "2'b01", ERR: "2'b10", range: "[1:0]", comparator:2 },  edc: { suffix: "auto", clk: "edc_clk", rst: "rst_a", change_kind: function(obj) { return obj.bits <= 16 ? 'par' : null; }, error_signal:"%m_edc_err", encode_reset: true, add_reset_sensitivity: 1 } }

module npuarc_alb_ifu_tos_queue 
  (
  input                        clk             , // clock input 
  input                        rst_a           , // async reset in


// Fetch Restart
  input                        fch_restart     , // Restart from EXU

// TOS info from the BPU 
  input                        br_info_valid  , // branch info is valid
  input [`npuarc_PC_RANGE]            br_info        , // branch info 

  output                       tosq_holdup    , // stall signal from tosq

// holdup fron next stage
//  input                        holdup_in      , // holdup from Fetch buffer

// To the execute stage
  output     [`npuarc_BR_TOSQ_RANGE]  tos_indx       , // index of the the TOSQ

// Mispredict inputs from the Execute Unit
  input                        mpd_mispredict   , // indicates a mispredict 
  input      [`npuarc_BR_TOSQ_RANGE]  mpd_tos_indx     , // index of the mipredict branch from mpd
//  input                        mpd_dslot        , // indicates a mispredict 
 // input                        mpd_error_branch , // indicates error branch 

// Commit input signasl from the Execute Unit
  input                        wa_pass      ,  // indicates a brach commit 
  input      [`npuarc_BR_TOSQ_RANGE]  wa_tos_indx  ,  // index of the mispredict branch from commit 

// Outputs to the BPU 
  output reg [`npuarc_PC_RANGE]       mpd_tos      , // branch info for the mispredict from mpd
  output reg [`npuarc_PC_RANGE]       wa_tos         // branch info for the mispredict from commit
   );
 
// Signal Declarations 
reg [`npuarc_PC_RANGE]    buf_0, buf_0_nxt;
reg [`npuarc_PC_RANGE]    buf_1, buf_1_nxt;
reg [`npuarc_PC_RANGE]    buf_2, buf_2_nxt;
reg [`npuarc_PC_RANGE]    buf_3, buf_3_nxt;
reg [`npuarc_PC_RANGE]    buf_4, buf_4_nxt;

reg  [`npuarc_BR_TOSQ_RANGE] buf_wrptr,buf_wrptr_nxt;
reg  [`npuarc_BR_TOSQ_RANGE] buf_wrptr_d1,buf_wrptr_d1_nxt;
reg  [`npuarc_BR_TOSQ_RANGE] buf_rdptr,buf_rdptr_nxt;

reg        buf_rd_of,buf_rd_of_nxt;
reg        buf_wr_of,buf_wr_of_nxt;

wire       wa_pass_int;
wire       mpd_mispred_int;

wire       buf_full;
wire       buf_empty;

wire [`npuarc_BR_TOSQ_RANGE]  mpd_branch_indx_int;
wire [`npuarc_BR_TOSQ_RANGE]  wa_branch_indx_int;
wire [`npuarc_PC_RANGE]       br_info_tos;
wire [`npuarc_BR_TOSQ_RANGE] mpd_wr_ptr;

////////////////////////////////////////////////////////////////////////////////
// Logic
////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////
// hold the state when buffer is full
//
assign tosq_holdup = buf_full & (!wa_pass);

assign buf_wr = br_info_valid & (!fch_restart) & (!buf_full);

assign br_info_tos = br_info;

////////////////////////////////////////////////////////////////////////////////
// write branch info to the QUEUE when buffer is not full
////////////////////////////////////////////////////////////////////////////////
// leda DFT_022 off
// LMD : Incomplete case statement
// LJ  : Based on TOSQ entries, the case may be partial, which is OK

always @(posedge clk or posedge rst_a)
begin: buf_reg_PROC
  if (rst_a == 1'b1) begin
     buf_0  <= {`npuarc_PC_BITS{1'b0}};
     buf_1  <= {`npuarc_PC_BITS{1'b0}};
     buf_2  <= {`npuarc_PC_BITS{1'b0}};
     buf_3  <= {`npuarc_PC_BITS{1'b0}};
     buf_4  <= {`npuarc_PC_BITS{1'b0}};
  end 
  else begin
    buf_0  <= buf_0_nxt;
    buf_1  <= buf_1_nxt;
    buf_2  <= buf_2_nxt;
    buf_3  <= buf_3_nxt;
    buf_4  <= buf_4_nxt;
  end
end  //block: buf_reg_PROC

always @ *
begin: buf_nxt_PROC
  buf_0_nxt  = buf_0;
  buf_1_nxt  = buf_1;
  buf_2_nxt  = buf_2;
  buf_3_nxt  = buf_3;
  buf_4_nxt  = buf_4;
  if (buf_wr) begin
    case (buf_wrptr)
    0: buf_0_nxt  = br_info_tos;
    1: buf_1_nxt  = br_info_tos;
    2: buf_2_nxt  = br_info_tos;
    3: buf_3_nxt  = br_info_tos;
    4: buf_4_nxt  = br_info_tos;
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
    default: ;
// spyglass enable_block W193
    endcase      
  end
end  //block: buf_reg_PROC
//leda  DFT_022 on

////////////////////////////////////////////////////////////////////////////////
// branch info indx is last written location of the buffer. 
//
assign tos_indx = (buf_wr) ? buf_wrptr : buf_wrptr_d1;

////////////////////////////////////////////////////////////////////////////////
// Delay the wr_ptr as the indx should remain same until the next buffer write
////////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : wr_ptr_delay_reg_PROC
  if (rst_a == 1'b1)
    buf_wrptr_d1 <= {`npuarc_BR_TOSQ_BITS{1'b0}};
  else  
    buf_wrptr_d1 <= buf_wrptr_d1_nxt;
end  //block : wr_ptr_delay_reg_PROC

always @ *
begin : wr_ptr_delay_nxt_PROC
  buf_wrptr_d1_nxt = buf_wrptr_d1;
  if (fch_restart & (!mpd_mispredict)) 
    buf_wrptr_d1_nxt = buf_rdptr;
  else if (fch_restart) 
    buf_wrptr_d1_nxt = mpd_tos_indx;
  else if (buf_wr)
    buf_wrptr_d1_nxt = buf_wrptr;
end  //block : wr_ptr_delay_reg_PROC

////////////////////////////////////////////////////////////////////////////////
//
//
assign mpd_mispred_int = !buf_empty & mpd_mispredict;

////////////////////////////////////////////////////////////////////////////////
//
//
assign wa_pass_int = !buf_empty & wa_pass;

assign mpd_wr_ptr = mpd_tos_indx;

////////////////////////////////////////////////////////////////////////////////
// Write pointer for the buffer
////////////////////////////////////////////////////////////////////////////////
// leda  W484 off
// leda  BTTF_D002 off
// LMD : Unequal length LHS and RHS in assignment
// LJ  : The compare logic ensures the addition results don't overflow

always @(posedge clk or posedge rst_a)
begin: wr_ptr_reg_PROC
  if (rst_a == 1'b1) begin
     buf_wrptr <= {`npuarc_BR_TOSQ_BITS{1'b0}};
     buf_wr_of <= 1'b0;
  end   
  else  begin
     buf_wrptr <= buf_wrptr_nxt;
     buf_wr_of <= buf_wr_of_nxt;
  end   
end  //block: wr_ptr_reg_PROC

always @ *
begin: wr_ptr_nxt_PROC
  buf_wrptr_nxt = buf_wrptr;
  buf_wr_of_nxt = buf_wr_of;
  if (fch_restart & (!mpd_mispredict)) begin
    if(buf_rdptr < `npuarc_BR_TOSQ_ENTRIES_M1) begin
      buf_wrptr_nxt = buf_rdptr + 1;
      buf_wr_of_nxt = buf_rd_of;
    end   
    else begin
      buf_wrptr_nxt = {`npuarc_BR_TOSQ_BITS{1'b0}};
      buf_wr_of_nxt = !buf_rd_of;
    end
  end
  else if (mpd_mispred_int) begin
    if(mpd_wr_ptr < `npuarc_BR_TOSQ_ENTRIES_M1) begin
      
      buf_wrptr_nxt = mpd_wr_ptr +1;
      if(buf_rdptr == mpd_tos_indx) begin
         buf_wr_of_nxt = buf_rd_of; 
      end
      else if((mpd_tos_indx) > buf_wrptr) begin
         buf_wr_of_nxt = !buf_wr_of; 
      end
    end
    else begin
      buf_wrptr_nxt = mpd_wr_ptr -`npuarc_BR_TOSQ_ENTRIES_M1 ;
      if(buf_rdptr == mpd_tos_indx) begin
         buf_wr_of_nxt = !buf_rd_of; 
      end
      else if(buf_wr_of == buf_rd_of) begin
         buf_wr_of_nxt = !buf_wr_of; 
      end
    end
  end  
  else if (buf_wr) begin
    if(buf_wrptr < `npuarc_BR_TOSQ_ENTRIES_M1) begin
      buf_wrptr_nxt = buf_wrptr + 1; 
    end
    else begin
      buf_wrptr_nxt = {`npuarc_BR_TOSQ_BITS{1'b0}};
      buf_wr_of_nxt = !buf_wr_of;
    end
  end
end  //block: wr_ptr_reg_PROC
//leda  BTTF_D002 on
// leda  W484 on
 
////////////////////////////////////////////////////////////////////////////////
// read pointer 
////////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : buf_rdptr_reg_PROC
  if (rst_a == 1'b1) begin
    buf_rdptr <= {`npuarc_BR_TOSQ_BITS{1'b0}};
    buf_rd_of <= 1'b0;
  end   
  else begin
    buf_rdptr <= buf_rdptr_nxt;
    buf_rd_of <= buf_rd_of_nxt;
  end
end  // block : buf_rdptr_reg_PROC

always @ *
begin : buf_rdptr_nxt_PROC
  buf_rdptr_nxt = buf_rdptr; 
  buf_rd_of_nxt = buf_rd_of;
  if (fch_restart& (!mpd_mispredict)) begin
    buf_rd_of_nxt = buf_rd_of;        // retain the value 
  end   
  else if (wa_pass_int ) begin
    buf_rdptr_nxt = wa_tos_indx; 

    if(wa_tos_indx < buf_rdptr ) begin
      buf_rd_of_nxt = !buf_rd_of;
    end
  end
end  // block : buf_rdptr_reg_PROC

////////////////////////////////////////////////////////////////////////////////
// Buffer full condition
// 
assign buf_full = (buf_wr_of != buf_rd_of) & (buf_rdptr == buf_wrptr);

////////////////////////////////////////////////////////////////////////////////
// Buffer empty condition
// 
assign buf_empty = (buf_wr_of == buf_rd_of) & (buf_rdptr == buf_wrptr);


////////////////////////////////////////////////////////////////////////////////
// buffer read pointer for the mispredict
//
assign mpd_branch_indx_int = mpd_tos_indx; 

////////////////////////////////////////////////////////////////////////////////
// buffer read pointer for commit
//
assign wa_branch_indx_int = wa_tos_indx; 

////////////////////////////////////////////////////////////////////////////////
// Read the buffer content for commit info
////////////////////////////////////////////////////////////////////////////////
always @ *
begin : wa_br_info_PROC
    wa_tos  = buf_0;
   case (wa_branch_indx_int)
    0: wa_tos = buf_0;
    1: wa_tos = buf_1;
    2: wa_tos = buf_2;
    3: wa_tos = buf_3;
    4: wa_tos = buf_4;
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
    default: ;
// spyglass enable_block W193
    endcase      
end

////////////////////////////////////////////////////////////////////////////////
// Read the buffer content for mispredict info
////////////////////////////////////////////////////////////////////////////////
always @ *
begin : mpd_br_info_PROC
    mpd_tos  = buf_0;
    case (mpd_branch_indx_int)
    0: mpd_tos = buf_0;
    1: mpd_tos = buf_1;
    2: mpd_tos = buf_2;
    3: mpd_tos = buf_3;
    4: mpd_tos = buf_4;
// spyglass disable_block W193 
// SMD: empty statements
// SJ:  empty default statements kept
    default: ;
// spyglass enable_block W193
    endcase      
end  // block : mpd_br_info_PROC


endmodule  // alb_ifu_tos_queue
