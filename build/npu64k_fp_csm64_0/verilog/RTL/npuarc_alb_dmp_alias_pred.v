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
//   ALB_DMP_ALIAS_PRED                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the Data Cache aliasing prediction.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_alias_pred.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"


module npuarc_alb_dmp_alias_pred (
// leda NTL_CON13C off
// leda NTL_CON37 off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used

  ////////// General input signals ///////////////////////////////////////////
  //
  input                               clk,            
  input                               rst_a,          

  input                               mmu_en_r,     // Enable TLB lookups
  input                               db_active_r,  // debug inserted instr
  
  ////////// Interface to the X1/DC1 stage ///////////////////////////////
  //
  input                               x1_load_r,      
  input                               x1_store_r,     
  input                               x1_pass,           
  input                               x1_uop_inst_r,           
  input [`npuarc_ADDR_RANGE]                 x1_addr_base,
  input [`npuarc_ADDR_RANGE]                 x1_addr_offset,
  input [`npuarc_ADDR_RANGE]                 x1_mem_addr0,
  input [`npuarc_ADDR_RANGE]                 x1_mem_addr1,
  
  ////////// Interface to the X2/DC2 stage ///////////////////////////////
  //
  input                               x2_load_r,      
  input                               x2_store_r,     
  input                               x2_pass,           
  input                               x2_enable,           
  input                               x2_uop_inst_r,           
  output reg [`npuarc_DC_PRED_BIT_RANGE]     dc2_pred0_r,
  output reg [`npuarc_DC_PRED_BIT_RANGE]     dc2_pred1_r,
  
  ////////// Interface to the X3/DC3 stage ///////////////////////////////
  //
  input                               x3_load_r,      
  input                               x3_store_r,     
  input                               x3_pass,           
  input                               x3_enable, 
  input                               x3_uop_inst_r, 
  input [1:0]                         dc3_dtlb_miss_r,
  input                               dc3_page_cross,          
  input [`npuarc_PADDR_RANGE]                dc3_mem_addr0_r,
  input [`npuarc_PADDR_RANGE]                dc3_mem_addr1_r,
  input [`npuarc_DMP_TARGET_RANGE]           dc3_target_r,

  output reg                          dc3_mispred,
  
  ////////// Interface to the CA stage ///////////////////////////////////
  //
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input                               ca_pass,
// spyglass enable_block W240
  input                               ca_enable,
  input                               ca_uop_inst_r,
// spyglass disable_block W240
// SMD: input declared but unused
// SJ:  unused in some configs 
  input      [1:0]                    dc4_dtlb_miss_r,
// spyglass enable_block W240

  ////////// Interface to the writeback stage ///////////////////////
  //
  input                               wa_restart_r,   // WB restart the pipeline
  input                               wa_replay_r,    // WB restart from DMP
  
  ////////// Interface to performance counters ////////////////////////////
  //
  output reg                          dc_pct_dcpm,    // Prediction miss
  
  ///////// Interface to the JTLB stage   ///////////////////////////////
  //
  input                               jrsp_dtlb_update,
  input                               jrsp_dtlb_update_hit,
  input                               jrsp_dtlb_multi_hit,
  input [`npuarc_UTLB_ENTRY_RANGE]           jtlb_update_data
// leda NTL_CON37  on
// leda NTL_CON13C on
); 


// Local Declarations
//

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
// naming convention: alp -> aliasing prediction
//
reg [`npuarc_DC_PRED_BIT_RANGE]      alp_physical_r[`npuarc_DC_PRED_ENTRIES-1:0];
// leda NTL_CON32 on

// leda NTL_CON13A off
// LMD: undriven internal net Range:8-12,31
// LJ:  code readibility
reg [`npuarc_ADDR_RANGE]             alp_base_xor_offset;
// leda NTL_CON13A on
reg [`npuarc_DC_PRED_ENTRIES_RANGE]  alp_hash0;
reg [`npuarc_DC_PRED_ENTRIES_RANGE]  alp_hash1;
reg [`npuarc_DC_PRED_ENTRIES_RANGE]  alp_hash2;
reg [`npuarc_DC_PRED_ENTRIES_RANGE]  alp_hash3;

reg [`npuarc_DC_PRED_ENTRIES_RANGE]  alp_hash_addr0;
reg [`npuarc_DC_PRED_ENTRIES_RANGE]  alp_hash_addr1;
reg                           dc1_dc4_xor_same;
reg                           alp_base_xor_offset_same;

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
// DC2
//
reg [`npuarc_DC_PRED_ENTRIES_RANGE]  dc2_hash0_r;
reg                           dc1_dc4_xor_same_set_cg0;
reg                           dc1_dc4_xor_same_clr_cg0;
reg                           uop_seq_cross_r;
reg [7:0]                     dc2_base_xor_offset_r;
reg                           dc2_uop_middle_cg0;
reg                           dc2_uop_middle_r;

// DC3
//
reg [`npuarc_DC_PRED_ENTRIES_RANGE]  dc3_hash0_r;
reg [`npuarc_DC_PRED_BIT_RANGE]      dc3_pred0_r;
reg [`npuarc_DC_PRED_BIT_RANGE]      dc3_pred1_r;
reg [7:0]                     dc3_base_xor_offset_r;
reg                           dc3_uop_middle_r;

// DC4
//
reg [`npuarc_DC_PRED_ENTRIES_RANGE]  dc4_dtlb_hash_r;
reg [`npuarc_DC_PRED_ENTRIES_RANGE]  dc4_hash0_r;
reg [`npuarc_DC_PRED_BIT_RANGE]      dc4_physical0_r;
reg [`npuarc_DC_PRED_BIT_RANGE]      dc4_physical1_r;
reg [1:0]                     dc4_pred_miss_r;
reg [7:0]                     dc4_base_xor_offset_r;
reg                           dc4_mispred_uop_middle_r;
reg                           dc4_mispred_uop_middle_set_cg0;
reg                           dc4_mispred_uop_middle_clr_cg0;

reg                           alp_write;
// leda NTL_CON32 on
////////////////////////////////////////////////////////////////////////////
// Asynchronous process to compute the hashed index
//  
////////////////////////////////////////////////////////////////////////////
// Example: 8KB page size, 32KB Data Cache:
//
// A[31:0] = Virtual address base
// B[31:0] = Virtual address offset
// C[31:0] = A[31:0] xor B[31:0]

// hash[4:0] = C[17:13] xor C[22:18] xor C[27:23] xor {1'b0, C[31:28]}

always @*
begin : alp_base_xor_offset_PROC
  // Hash the virtual base with the virtual offset
  //
  alp_base_xor_offset      = x1_addr_base ^ x1_addr_offset;

  // dc1_base_xor_offset matches with the dc4_base_xor_offset
  //
  // (1) Make sure that there is an uop sequence
  // (2) Make sure that the uop had a mis-prediction earlier
  // (3) The x1_xor_offset matches with the earlier one that missed 
  //
  dc1_dc4_xor_same         =   x1_uop_inst_r                      // (1) 
                             & dc4_mispred_uop_middle_r           // (2)
                             & (~( | (  alp_base_xor_offset[7:0]  // (3)   
                                      ^ dc4_base_xor_offset_r[7:0]
                               ) )   )
                             & x1_pass;
    
  // The following (uop_seq_cross_r) indicates that LDs/STs that are part of an UOP
  // that cross a page and resides in the next page
  // should not use the regular hash, such that it will use hash1

  dc1_dc4_xor_same_set_cg0 = dc1_dc4_xor_same & x2_enable & (~alp_write);

  dc1_dc4_xor_same_clr_cg0 =     alp_write                                     // during a table update, clear this
                            | (~x1_uop_inst_r & (x1_load_r | x1_store_r))      // When there is no X1 uop
                            | wa_restart_r                                     // When there is a wa_restart
                            | wa_replay_r                                      // When there is a wa_replay
                            ;
  // The base_xor_offset is same as _r (applicable only during uops)
  //
  // (1) This makes sure that there is an uop
  //
  // (2) The dc1 xor matches with the missed xor base_offset and the following seq
  //
  alp_base_xor_offset_same =   x1_uop_inst_r                        // (1)
                             & (dc1_dc4_xor_same | uop_seq_cross_r) // (2)    
                             ;
end

always @*
begin : dc2_uop_middle_cg0_PROC
  // Identify the middle of uop
  //
  dc2_uop_middle_cg0 =     (x1_uop_inst_r & x2_uop_inst_r)
                         & (x1_load_r | x1_store_r)
                         & (x2_load_r | x2_store_r)
                         & x1_pass
                         & x2_enable;
end

always @*
begin : alp_hash_PROC
  // Compute intermediate terms
  //
  alp_hash0 = alp_base_xor_offset[16:12];
  alp_hash1 = alp_base_xor_offset[21:17];
  alp_hash2 = alp_base_xor_offset[26:22];
  alp_hash3 = {1'd0,alp_base_xor_offset[30:27]};

  // Put it all together. 
  //
  alp_hash_addr0 =   alp_hash0
                   ^ alp_hash1
                   ^ alp_hash2
                   ^ alp_hash3
                   ;
  // Make sure that consequetive page address does not hash in to the same location
  //       
  alp_hash_addr0[0] =   (alp_base_xor_offset_same) 
                      ? (~alp_hash_addr0[0])
                      : alp_hash_addr0[0] 
                      ;     
  // The entry1 is for unaligned accesses crossing page boundaries
  //
  alp_hash_addr1    = alp_hash_addr0;
  alp_hash_addr1[0] = ~alp_hash_addr0[0];
end

reg  alp_bypass0;
reg  alp_bypass1;

////////////////////////////////////////////////////////////////////////////
// Asynchronous process for reading  from the predictor
//  
////////////////////////////////////////////////////////////////////////////
always @*
begin : alp_bypass_PROC
  // Bypass predictor when
  // - Accessing untranslated memory, i.e.: bit 31 is set (1)
  // - The MMU is disabled (2)
  // - The load/store instruction is inserted by the debugger (3)
  //
  alp_bypass0 =  x1_mem_addr0[`npuarc_ADDR_MSB] // (1)
               | (~mmu_en_r)             // (2)
               | db_active_r;            // (3)
       
  alp_bypass1 =  x1_mem_addr1[`npuarc_ADDR_MSB] // (1)
               | (~mmu_en_r)             // (2)
               | db_active_r;            // (3)
       
end

////////////////////////////////////////////////////////////////////////////
// Asynchronous process for reading  from the predictor
//  
////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DC_PRED_BIT_RANGE]  alp_physical0;
reg [`npuarc_DC_PRED_BIT_RANGE]  alp_physical1;

always @*
begin : alp_read_PROC
  alp_physical0 =   alp_bypass0
                  ? x1_mem_addr0[`npuarc_DC_PRED_BIT_RANGE]
                  : alp_physical_r[alp_hash_addr0];

  alp_physical1 =   alp_bypass1
                  ? x1_mem_addr1[`npuarc_DC_PRED_BIT_RANGE]
                  : alp_physical_r[alp_hash_addr1];
end

reg dc1_load_store;
reg dc2_load_store;
reg dc3_load_store;
////////////////////////////////////////////////////////////////////////////
// Handy assignments
//  
////////////////////////////////////////////////////////////////////////////
always @*
begin : dc123_ld_store_PROC
  dc1_load_store = x1_load_r | x1_store_r;
  dc2_load_store = x2_load_r | x2_store_r;
  dc3_load_store = x3_load_r | x3_store_r;
end

////////////////////////////////////////////////////////////////////////////
// Clock gate
//  
////////////////////////////////////////////////////////////////////////////
reg    dc2_cg0;
reg    dc3_cg0;
reg    dc4_cg0;

always @*
begin : alp_cg0_PROC
  // DC2 clock gate enable
  //
  dc2_cg0 = dc1_load_store & x1_pass & x2_enable;
  
  // DC3 clock gate enable
  //
  dc3_cg0 = dc2_load_store & x2_pass & x3_enable;
  
  // DC4 clock gate enable
  //
  dc4_cg0 = dc3_load_store & x3_pass & ca_enable;
end


////////////////////////////////////////////////////////////////////////////
// Prediction validation (DC3)
//  
////////////////////////////////////////////////////////////////////////////
reg   dc3_mispred0;
reg   dc3_mispred1;

always @*
begin : dc3_mispred_PROC
  // Compare the actual physical address of the aliasing bits with the predicted
  // address.
  //
  dc3_mispred0 =   (x3_load_r | x3_store_r)
                 & (dc3_mem_addr0_r[`npuarc_DC_PRED_BIT_RANGE] != dc3_pred0_r)
                 & (dc3_target_r == `npuarc_DMP_TARGET_DC)
                 ;
  // Unaligned instructions crossing a memory page boundary
  //
  dc3_mispred1 =   (x3_load_r | x3_store_r)
                 & (dc3_mem_addr1_r[`npuarc_DC_PRED_BIT_RANGE] != dc3_pred1_r)
                 & (dc3_target_r == `npuarc_DMP_TARGET_DC)
                 & dc3_page_cross
                 ;
  // Misprediction
  //
  dc3_mispred =     (dc3_mispred0 | dc3_mispred1)
                 & (~(| dc3_dtlb_miss_r))
                 ;
end

////////////////////////////////////////////////////////////////////////////
// 
//  
////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_mispred_uop_middle_cg0_PROC
  // Capture the missed base_xor_offset 
  //
  // (1) When uop is in the middle
  // (2) There is a mis-prediction
  // 
  dc4_mispred_uop_middle_set_cg0 =   dc3_uop_middle_r                                         // (1)
                                   & (dc3_mispred & (~(|dc4_pred_miss_r)) & (~dc3_mispred1))  // (2)
                                   & x3_pass
                                   & ca_enable;

  // The following assumption is made while clearing the special mechanism that gets triggered when an uop
  // crosses two pages
  //
  // (1) When there is an x3 instruction and its not a uop.                                                         
  // (2) There is a mis-prediction for the new uop. This can be due to an interrupt sequence is prempted by high level interrupt, 
  //     so the same interrupt sequence which started earlier was not started  and a new sequence is started,
  //     which will have a misprediction during the start
  // (3) The uop sequecnce that had a mis-prediction earlier have come back again
  //
  dc4_mispred_uop_middle_clr_cg0 =   ( (x3_load_r | x3_store_r) & (~x3_uop_inst_r) & x3_pass) // (1)
                                   | (  dc3_mispred & x3_uop_inst_r 
                                      & (~(|dc4_pred_miss_r)) & dc4_mispred_uop_middle_r)     // (2)
                                   | (uop_seq_cross_r & x3_pass)                              // (3)
                                   ;
end    
////////////////////////////////////////////////////////////////////////////
// Handy assignments
//  
////////////////////////////////////////////////////////////////////////////
reg                          dc3_miss;
reg [`npuarc_DC_PRED_ENTRIES_RANGE] dc4_hash1;

always @*
begin : alp_handy_PROC
  // DC3 prediction miss or DC3 DTLB miss
  //
  dc3_miss  =   (dc3_mispred | (| dc3_dtlb_miss_r))
              & (dc3_target_r == `npuarc_DMP_TARGET_DC);
              
  // Crossing page boundaries
  //
  dc4_hash1    = dc4_hash0_r;
  dc4_hash1[0] = ~dc4_hash0_r[0];
end


////////////////////////////////////////////////////////////////////////////
// Control FSM
//  
////////////////////////////////////////////////////////////////////////////
reg [`npuarc_DC_PRED_ENTRIES_RANGE]  alp_addr;
reg [`npuarc_DC_PRED_BIT_RANGE]      alp_data;

reg [1:0]                     alp_state_r;
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
reg [1:0]                     alp_state_nxt;
// leda NTL_CON32 on

parameter ALP_DEFAULT      = 2'b00;
parameter ALP_UPDATE_DTLB  = 2'b01;
parameter ALP_UPDATE_MISS  = 2'b10;

always @*
begin : alp_state_fsm_PROC
  alp_write                  = 1'b0;
  alp_addr                   = dc4_hash0_r;
  alp_data                   = dc4_physical0_r;
  alp_state_nxt              = alp_state_r;

  dc_pct_dcpm                = 1'b0;
      
// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
//
  case (alp_state_r) 
  ALP_DEFAULT:
  begin
    // State transition triggered by a either a prediction or DTLB miss
    // mooving on to DC4
    //
    if (  dc3_miss
        & x3_pass
        & ca_enable)
    begin
      // When both DTLB 0 and 1 are misses, then dont update the prediction table, wait for both dtlb misses
      // to be resolved and then update the prediction table. 
      //
      alp_state_nxt     = (^dc3_dtlb_miss_r)       // Any one miss
                        ? ALP_UPDATE_DTLB 
                        : (  dc3_mispred           
                           ? ALP_UPDATE_MISS 
                           : ALP_DEFAULT           // Both DTLB miss (rare event) then stay in the ALP_DEFAULT  
                          );
    end
  end
  
  ALP_UPDATE_DTLB:
  begin
    // Predictor update:
    // (1) DTLB misses
    // UPdate the predictor together with the DTLB update
    //
    alp_write     =   jrsp_dtlb_update 
                    & jrsp_dtlb_update_hit
                    & (~jrsp_dtlb_multi_hit); 
    alp_addr      = dc4_dtlb_hash_r;
    alp_data      = jtlb_update_data[`npuarc_PCKD_PTE_PPN_LSB+`npuarc_DC_PRED_BIT_WIDTH-1:`npuarc_PCKD_PTE_PPN_LSB];
      
    if (  (x1_load_r | x1_store_r)
        & x1_pass)
    begin
      // Wait until the pipe is released
      //
      alp_state_nxt = ALP_DEFAULT;
    end
  end
  
  ALP_UPDATE_MISS:
  begin
    // This is a genuine pedictor miss. Update predictor right away
    //
    alp_write     = 1'b1;
    alp_addr      = (dc4_mispred_uop_middle_r & ca_uop_inst_r) ? dc4_hash1 
                    : (dc4_pred_miss_r[0] ? dc4_hash0_r     : dc4_hash1);
    alp_data      = (dc4_mispred_uop_middle_r & ca_uop_inst_r) ? dc4_physical1_r 
                    : (dc4_pred_miss_r[0] ? dc4_physical0_r : dc4_physical1_r);
    dc_pct_dcpm   = 1'b1;
    alp_state_nxt = ALP_DEFAULT;
  end
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept   
  default:
    ;
  endcase
// spyglass enable_block W193
// leda NTL_CON32 on
end

////////////////////////////////////////////////////////////////////////////
// Synchronous process for writing new information into the predictor
//  
////////////////////////////////////////////////////////////////////////////
integer i;

always @(posedge clk or posedge rst_a)
begin : alp_write_reg_PROC
  if (rst_a == 1'b1)
  begin
    for (i = 0; i < `npuarc_DC_PRED_ENTRIES; i = i + 1)
    begin
      // Initialize the predictor table
      //
      alp_physical_r[i] <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
    end
  end
  else
  begin
    // Write into the prediction
    //
    if (alp_write)
    begin
      alp_physical_r[alp_addr] <= alp_data;
    end
  end
end

////////////////////////////////////////////////////////////////////////////
// DC2 prediction
//  
////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : alp_dc2_pred_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_pred0_r <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
    dc2_pred1_r <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
  end
  else
  begin
    if (dc2_cg0)
    begin
      dc2_pred0_r <= alp_physical0;
      dc2_pred1_r <= alp_physical1;
    end
  end
end

///////////////////////////////////////////////////////////////////////////////////
//
// The following (uop_seq_cross_r) indicates that LDs/STs that are part of an UOP 
// that cross a page and resides in the next page
// should not use the regular hash
// 
///////////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : uop_seq_cross_reg_PROC
  if (rst_a == 1'b1)
  begin
    uop_seq_cross_r   <= 1'b0;
  end
  else
  begin
    if (dc1_dc4_xor_same_set_cg0)
    begin
      uop_seq_cross_r <= 1'b1;
   end
   else if (dc1_dc4_xor_same_clr_cg0)
   begin
      uop_seq_cross_r <= 1'b0;
   end   
  end
end

////////////////////////////////////////////////////////////////////////////
// DC2 hash index
//  
////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : alp_dc2_hash_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_hash0_r             <= {`npuarc_DC_PRED_ENTRIES_DEPTH{1'b0}};
    dc2_base_xor_offset_r   <= 8'h00;
  end
  else
  begin
    if (dc2_cg0)
    begin
      dc2_hash0_r           <= alp_hash_addr0;
      dc2_base_xor_offset_r <= alp_base_xor_offset[7:0];
    end    
  end
end

always @(posedge clk or posedge rst_a)
begin : dc2_uop_middle_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc2_uop_middle_r   <= 1'b0;
  end
  else
  begin
    if (dc2_uop_middle_cg0)
    begin
      dc2_uop_middle_r <= 1'b1;
    end
    else if (~x1_uop_inst_r & x3_enable)
    begin
      dc2_uop_middle_r <= 1'b0;
    end    
  end
end

////////////////////////////////////////////////////////////////////////////
// DC3 flops
//  
////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : alp_dc3_pred_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_pred0_r <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
    dc3_pred1_r <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
  end
  else
  begin
    if (dc3_cg0)
    begin
      dc3_pred0_r <= dc2_pred0_r;
      dc3_pred1_r <= dc2_pred1_r;
    end
  end
end

// leda NTL_CON32 off
// LMD: Change on net has no effect on any of the outputs Range
// LJ:  Some bits unused
always @(posedge clk or posedge rst_a)
begin : alp_dc3_hash_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc3_hash0_r             <= {`npuarc_DC_PRED_ENTRIES_DEPTH{1'b0}};
    dc3_base_xor_offset_r   <= 8'h00;
    dc3_uop_middle_r        <= 1'b0;
  end
  else
  begin
    if (dc3_cg0)
    begin
      dc3_hash0_r           <= dc2_hash0_r;
      dc3_base_xor_offset_r <= dc2_base_xor_offset_r;
      dc3_uop_middle_r      <= dc2_uop_middle_r;
    end
    else if (~x3_uop_inst_r & ca_enable)
    begin
      dc3_uop_middle_r      <= 1'b0;
    end    
  end
end
// leda NTL_CON32 on
////////////////////////////////////////////////////////////////////////////
// DC4 flops
//  
////////////////////////////////////////////////////////////////////////////
always @(posedge clk or posedge rst_a)
begin : alp_dc4_hash_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_hash0_r        <= {`npuarc_DC_PRED_ENTRIES_DEPTH{1'b0}};
    dc4_dtlb_hash_r    <= {`npuarc_DC_PRED_ENTRIES_DEPTH{1'b0}};
  end
  else
  begin
    if (dc4_cg0)
    begin
      dc4_hash0_r      <= dc3_hash0_r;
      dc4_dtlb_hash_r  <= dc3_dtlb_miss_r[0] 
                        ? dc3_hash0_r 
                        : {dc3_hash0_r[`npuarc_DC_PRED_ENTRIES_MSB:1], ~dc3_hash0_r[0]};
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : alp_dc4_physical_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_physical0_r <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
    dc4_physical1_r <= {`npuarc_DC_PRED_BIT_WIDTH{1'b0}};
  end
  else
  begin
    if (dc4_cg0)
    begin
      dc4_physical0_r <= dc3_mem_addr0_r[`npuarc_DC_PRED_BIT_RANGE];
      dc4_physical1_r <= dc3_mem_addr1_r[`npuarc_DC_PRED_BIT_RANGE];
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : alp_dc4_miss_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_pred_miss_r <= 2'b00;
  end
  else
  begin
    if (dc4_cg0)
    begin
      dc4_pred_miss_r <= {dc3_mispred1, dc3_mispred0};
    end
  end
end

always @(posedge clk or posedge rst_a)
begin : dc4_mispred_uop_middle_reg_PROC
  if (rst_a == 1'b1)
  begin
    dc4_mispred_uop_middle_r   <= 1'b0;
    dc4_base_xor_offset_r      <= 8'h00;
  end
  else
  begin
    if (dc4_mispred_uop_middle_clr_cg0)
    begin
      dc4_mispred_uop_middle_r <= 1'b0;
      dc4_base_xor_offset_r    <= 8'h00;
    end
    else if (dc4_mispred_uop_middle_set_cg0)
    begin
      dc4_mispred_uop_middle_r <= 1'b1;
      dc4_base_xor_offset_r    <= dc3_base_xor_offset_r;
    end 
  end
end

////////////////////////////////////////////////////////////////////////////
//
//  
////////////////////////////////////////////////////////////////////////////

always @(posedge clk or posedge rst_a)
begin : alp_fsm_reg_PROC
  if (rst_a == 1'b1)
  begin
    alp_state_r <= ALP_DEFAULT;
  end
  else
  begin
    alp_state_r <= alp_state_nxt;
  end
end



endmodule // alb_dmp_alias_pred
