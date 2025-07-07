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
//  IFU Branch INFO Buffer
//
// ===========================================================================
//
// Description:
// This module implements the branch info queue.
// The branch info from the branch predictor is stored in this queue instead 
// passing the info directly to the execute block. Based on the outcome of the 
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

module npuarc_alb_ifu_brinfo_buf 
  (
  input                            clk             ,  // clock input 
  input                            rst_a           ,  // async reset in

// Fetch Restart
  input                            fch_restart     ,  // Restart from EXU

// Interface to the alignment unit of IFU  slot 0
  input                            br_info_valid   ,  // branch info is valid
  input      [`npuarc_BR_BUF_INFO_RANGE]  br_info         ,  // branch info 

  input                            da_holdup       ,  // da_holdup from EXU


  output                           brq_holdup      ,  // stall signal from brinfo_buf

// To the execute stage
  output     [`npuarc_BR_INFO_BUF_RANGE]  br_info_indx    ,  // index of the the 
                                                      // br_info in the queue (write pointer)

// mispredict signals from the Execute Unit
  input                            mpd_mispredict  ,  // indicates a mispredict 
  input      [`npuarc_BR_INFO_BUF_RANGE]  mpd_branch_indx ,  // index of the mipredict branch from mpd
  input                            mpd_dslot       ,  // indicates a mispredict 
  input                            mpd_error_branch,  // indicates error branch 

// commit signals from the Execute Unit

  input                            wa_pass         ,  // indicates a brach commit 
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ:  buf interface
// spyglass disable_block W240
// SMD: Signal declared but not used
// SJ:  not used in all configs
  input      [`npuarc_BR_INFO_BUF_RANGE]  wa_branch_indx  ,  // index of the mispredict branch from commit 
// leda NTL_CON13C on
// leda NTL_CON37 on
// spyglass enable_block W240
  output reg [`npuarc_BR_BUF_INFO_RANGE]  mpd_branch_info  , // branch info for the mispredict from mpd
  output reg [`npuarc_BR_BUF_INFO_RANGE]  wa_branch_info     // branch info for the mispredict from commit
   );

//////////////////////////////////////////////////////////////////////////////// 
// Local Signal Declarations 
//
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_0;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_0_nxt;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_1;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_1_nxt;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_2;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_2_nxt;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_3;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_3_nxt;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_4;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_4_nxt;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_5;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_5_nxt;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_6;
reg [`npuarc_BR_BUF_INFO_RANGE]    buf_6_nxt;

wire [`npuarc_BR_INFO_BUF_RANGE]  buf_wrptr_next;
wire [`npuarc_BR_INFO_BUF_RANGE]  buf_rdptr_next;
reg  [`npuarc_BR_INFO_BUF_RANGE]  buf_wrptr,buf_wrptr_nxt;
reg  [`npuarc_BR_INFO_BUF_RANGE]  buf_wrptr_d1, buf_wrptr_d1_nxt;
reg  [`npuarc_BR_INFO_BUF_RANGE]  buf_rdptr, buf_rdptr_nxt;
wire [`npuarc_BR_INFO_BUF_RANGE]  buf_rdptr_tmp;

wire [`npuarc_BR_INFO_BUF_RANGE]  mpd_branch_indx_int;
wire [`npuarc_BR_INFO_BUF_RANGE]  wa_branch_indx_int;
wire [`npuarc_BR_INFO_BUF_RANGE]  mpd_wr_ptr;

wire       mpd_dslot_int;

reg        buf_rd_of;
reg        buf_wr_of;

reg        buf_rd_of_nxt;
wire       buf_rd_of_next;
reg        buf_wr_of_nxt;
wire       buf_wr_of_next;

wire       wa_pass_int;
wire       mpd_mispred_int;

wire       buf_full;
wire       buf_empty;
wire       brinfo_val_int;


////////////////////////////////////////////////////////////////////////////////
// Logic  
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// hold the state when buffer is full
//
assign brq_holdup = buf_full & (!wa_pass);


////////////////////////////////////////////////////////////////////////////////
// Buffer is writen when instruction is valid and there is no holdup from da 
// and when buffer is not full
//
assign buf_wr = br_info_valid & (!da_holdup) & (!brq_holdup);

////////////////////////////////////////////////////////////////////////////////
// If buffer is full, make the valid 0
//
assign brinfo_val_int = br_info_valid & (!brq_holdup);


////////////////////////////////////////////////////////////////////////////////
// write branch info to the QUEUE when buffer is not full
////////////////////////////////////////////////////////////////////////////////
// leda  DFT_022 off
// LMD : Incomplete case statement
// LJ  : Based on BRINFO entries, the case may be partial, which is OK

always @(posedge clk or posedge rst_a)
begin: buf_reg_PROC
  if (rst_a == 1'b1) begin
     buf_0  <= {(`npuarc_BR_BUF_INFO_MSB-`npuarc_BR_FULL_INFO_LSB+1){1'b0}};
     buf_1  <= {(`npuarc_BR_BUF_INFO_MSB-`npuarc_BR_FULL_INFO_LSB+1){1'b0}};
     buf_2  <= {(`npuarc_BR_BUF_INFO_MSB-`npuarc_BR_FULL_INFO_LSB+1){1'b0}};
     buf_3  <= {(`npuarc_BR_BUF_INFO_MSB-`npuarc_BR_FULL_INFO_LSB+1){1'b0}};
     buf_4  <= {(`npuarc_BR_BUF_INFO_MSB-`npuarc_BR_FULL_INFO_LSB+1){1'b0}};
     buf_5  <= {(`npuarc_BR_BUF_INFO_MSB-`npuarc_BR_FULL_INFO_LSB+1){1'b0}};
     buf_6  <= {(`npuarc_BR_BUF_INFO_MSB-`npuarc_BR_FULL_INFO_LSB+1){1'b0}};
  end 
  else begin
      buf_0  <= buf_0_nxt;
      buf_1  <= buf_1_nxt;
      buf_2  <= buf_2_nxt;
      buf_3  <= buf_3_nxt;
      buf_4  <= buf_4_nxt;
      buf_5  <= buf_5_nxt;
      buf_6  <= buf_6_nxt;
  end
end  //block: buf_reg_PROC

always @ *
begin: buf_nxt_PROC
      buf_0_nxt  = buf_0;
      buf_1_nxt  = buf_1;
      buf_2_nxt  = buf_2;
      buf_3_nxt  = buf_3;
      buf_4_nxt  = buf_4;
      buf_5_nxt  = buf_5;
      buf_6_nxt  = buf_6;
  if (buf_wr) begin
    case (buf_wrptr)
      0: begin
            buf_0_nxt  = br_info;
          end
      1: begin
            buf_1_nxt  = br_info;
          end
      2: begin
            buf_2_nxt  = br_info;
          end
      3: begin
            buf_3_nxt  = br_info;
          end
      4: begin
            buf_4_nxt  = br_info;
          end
      5: begin
            buf_5_nxt  = br_info;
          end
      6: begin
            buf_6_nxt  = br_info;
          end
    default:  buf_0_nxt  = br_info;
    endcase      
  end
end  //block: buf_reg_PROC

////////////////////////////////////////////////////////////////////////////////
// branch info indx is last written location of the buffer. 
//
assign br_info_indx = (brinfo_val_int) ? buf_wrptr : buf_wrptr_d1;


////////////////////////////////////////////////////////////////////////////////
// Delay the wr_ptr as the indx should remain same until the next buffer write
////////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : wr_ptr_delay_reg_PROC
  if (rst_a == 1'b1)
    buf_wrptr_d1 <= {`npuarc_BR_INFO_BUF_SIZE{1'b0}};
  else  
    buf_wrptr_d1 <= buf_wrptr_d1_nxt;
end  //block : wr_ptr_delay_reg_PROC

always @ *
begin : wr_ptr_delay_nxt_PROC
  buf_wrptr_d1_nxt = buf_wrptr_d1;
  if (fch_restart) 
    buf_wrptr_d1_nxt = {`npuarc_BR_INFO_BUF_SIZE{1'b0}};
  else if (buf_wr)
    buf_wrptr_d1_nxt = buf_wrptr;
end  //block : wr_ptr_delay_reg_PROC

////////////////////////////////////////////////////////////////////////////////
// Pointer adjustments
// 1. mpd_is_predicted=1: In this case set write_ptr<=mpd_branch_info+1.
// 2. wa_pass=1: In this case set the read_ptr=wa_branch_info+1: 
//  When a predicted branch is committed we increment the read_ptr for the 
//  committed branch: read_ptr <= read_ptr+1
//  When a branch is mispredicted (case 1 or case 2) and simultaneously a 
//  predicted branch is committed, then we do both: write_ptr<=mpd_branch_info+1 
//  as well as read_ptr <= read_ptr+1
//  This also works when the mispredict occurs in the commit stage and there 
//  are no other pending branches
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// update read pointer only when buffer is not empty 
//
assign mpd_mispred_int = (!buf_empty) & mpd_mispredict;

////////////////////////////////////////////////////////////////////////////////
// update read pointer only when buffer is not empty
//
assign wa_pass_int = (!buf_empty) & wa_pass;

////////////////////////////////////////////////////////////////////////////////
// if there is error branch, do not take delay slot into account
//
assign  mpd_dslot_int = mpd_dslot & (!mpd_error_branch);

// leda  W484 off
// leda  B_3200 off
// leda  B_3219 off
// leda  BTTF_D002 off
// LMD : Unequal length LHS and RHS in assignment
// LJ  : Max mpd_branch_indx is 6. max mpd_dslot_int is 1. So it cannot overflow
// spyglass disable_block W484 W164a
// SMD: LHS width is less than RHS
// SMD: Possible assignment overflow
// SJ: Max mpd_branch_indx is 6. max mpd_dslot_int is 1. So it cannot overflow 
assign mpd_wr_ptr = mpd_branch_indx + mpd_dslot_int;
//leda  BTTF_D002 on
// leda  B_3200 on
// leda  B_3219 on
// leda  W484 on
// spyglass enable_block W484 W164a

////////////////////////////////////////////////////////////////////////////////
// Write pointer for the buffer
// If there is restart without mispredict, adjust the write pointer to the 
// read pointer. Reset the flag to 0
// if there is mispredict, set the write pointer to the next pointer after the
// mispredicted branch + delay slot 
// For normal writes to the buffer, increment the pointer by 1.
////////////////////////////////////////////////////////////////////////////////
// leda  W484 off
// leda  BTTF_D002 off
// LMD : Unequal length LHS and RHS in assignment
// LJ  : The comparisons make sure addition and subtraction result don't overflow 
assign buf_wrptr_next =
                        buf_wrptr_nxt;
assign buf_wr_of_next =
                        buf_wr_of_nxt;

always @(posedge clk or posedge rst_a)
begin: wr_ptr_reg_PROC
  if (rst_a == 1'b1) begin
     buf_wrptr <= {`npuarc_BR_INFO_BUF_SIZE{1'b0}};
     buf_wr_of <= 1'b0;
  end   
  else begin
     buf_wrptr <= buf_wrptr_next;
     buf_wr_of <= buf_wr_of_next;
  end
end  //block: wr_ptr_reg_PROC

always @ *
begin: wr_ptr_nxt_PROC
  buf_wrptr_nxt = buf_wrptr;
  buf_wr_of_nxt = buf_wr_of;
  if (fch_restart & (!mpd_mispredict)) begin
     buf_wrptr_nxt = buf_rdptr;
     buf_wr_of_nxt = 1'b0;
  end   
  else if (mpd_mispred_int) begin
    if(mpd_wr_ptr < `npuarc_BR_INFO_ENTRIES_M1) begin
      buf_wrptr_nxt = mpd_wr_ptr +1;
      if(mpd_branch_indx == buf_rdptr) begin
         buf_wr_of_nxt = buf_rd_of; 
      end
      else if((mpd_branch_indx) > buf_wrptr) begin
         buf_wr_of_nxt = !buf_wr_of; 
      end
    end
    else begin
      buf_wrptr_nxt = mpd_wr_ptr -`npuarc_BR_INFO_ENTRIES_M1 ;
      if(mpd_branch_indx == buf_rdptr) begin
         buf_wr_of_nxt = !buf_rd_of; 
      end
      else if(buf_wr_of == buf_rd_of) begin
         buf_wr_of_nxt = !buf_wr_of; 
      end
    end
  end
  else if (buf_wr) begin
    if(buf_wrptr < `npuarc_BR_INFO_ENTRIES_M1) begin
      buf_wrptr_nxt  = buf_wrptr + 1; 
    end
    else begin
      buf_wrptr_nxt  = {`npuarc_BR_INFO_BUF_SIZE{1'b0}};
      buf_wr_of_nxt  = !buf_wr_of;
    end
  end
end  //block: wr_ptr_reg_PROC
//leda  BTTF_D002 on
// leda  W484 on
 

////////////////////////////////////////////////////////////////////////////////
// read pointer 
////////////////////////////////////////////////////////////////////////////////

always @ * 
begin : buf_rdptr_nxt_PROC
  buf_rdptr_nxt = buf_rdptr; 
  buf_rd_of_nxt = buf_rd_of;
  if (fch_restart& (!mpd_mispredict)) begin
    buf_rd_of_nxt = 1'b0;
  end   
  else if (wa_pass_int ) begin
    if(buf_rdptr < `npuarc_BR_INFO_ENTRIES_M1) begin
      buf_rdptr_nxt = buf_rdptr_tmp; 


    end
    else begin
      buf_rdptr_nxt = {`npuarc_BR_INFO_BUF_SIZE{1'b0}};
      buf_rd_of_nxt = !buf_rd_of;
    end
  end
end  // block : buf_rdptr_reg_PROC

assign buf_rdptr_next =
                        buf_rdptr_nxt;
assign buf_rd_of_next =
                        buf_rd_of_nxt;

always @(posedge clk or posedge rst_a)
begin : buf_rdptr_reg_PROC
  if (rst_a == 1'b1) begin
    buf_rdptr <= {`npuarc_BR_INFO_BUF_SIZE{1'b0}};
    buf_rd_of <= 1'b0;
  end
  else begin   
    buf_rdptr <= buf_rdptr_next;
    buf_rd_of <= buf_rd_of_next;
  end
end  // block : buf_rdptr_reg_PROC


// Next read pointer
// leda  W484 off
// LMD : Possible loss of carry/borrow in addition/subtraction LHS : 3, RHS : 4
// leda  BTTF_D002 off
// LMD : Unequal length LHS and RHS in assignment
// LJ  : Max buf_rdptr is 6. So it cannot overflow
assign buf_rdptr_tmp = buf_rdptr +1;
//leda  BTTF_D002 on
// leda  W484 on

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
assign mpd_branch_indx_int = mpd_branch_indx; 

////////////////////////////////////////////////////////////////////////////////
// buffer read pointer for commit
//
assign wa_branch_indx_int = buf_rdptr; 

////////////////////////////////////////////////////////////////////////////////
// Read the buffer content for commit info
////////////////////////////////////////////////////////////////////////////////
always @ *
begin : wa_br_info_PROC
  wa_branch_info  = buf_0;
  case (wa_branch_indx_int)
         0: wa_branch_info = buf_0;
         1: wa_branch_info = buf_1;
         2: wa_branch_info = buf_2;
         3: wa_branch_info = buf_3;
         4: wa_branch_info = buf_4;
         5: wa_branch_info = buf_5;
         6: wa_branch_info = buf_6;
  default:  wa_branch_info = buf_0;
  endcase      
end

////////////////////////////////////////////////////////////////////////////////
// Read the buffer content for mispredict info
////////////////////////////////////////////////////////////////////////////////
always @ *
begin : mpd_br_info_PROC
  mpd_branch_info  = buf_0;
  case (mpd_branch_indx_int)
       0: mpd_branch_info = buf_0;
       1: mpd_branch_info = buf_1;
       2: mpd_branch_info = buf_2;
       3: mpd_branch_info = buf_3;
       4: mpd_branch_info = buf_4;
       5: mpd_branch_info = buf_5;
       6: mpd_branch_info = buf_6;
 default:mpd_branch_info = buf_0 ; 
  endcase      
end  // block : mpd_br_info_PROC

endmodule  // alb_ifu_brinfo_buf
