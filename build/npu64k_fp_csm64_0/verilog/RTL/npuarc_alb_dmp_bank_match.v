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
//   ALB_DMP_BANK_MATCH                 
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the bank matching logic that will be required during
//   by-passing the store data to the load in X3.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_bank_match.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_bank_match (

  //////////////// DC3 inputs ////////////////////////////////////////////////
  // 
  input [3:0]               dc3_mask,          // load mask 
  
  //////////////// DC4, WQ store mask /////////////////////////////////////////
  // 
  input [3:0]               dc40_mask,       
  input [3:0]               dc41_mask,       
  input [3:0]               wq0_mask,        
  input [3:0]               wq1_mask,        
  input [3:0]               wq2_mask,        
  input [3:0]               wq3_mask,        
  
  //////////////// Address matching ///////////////////////////////////////////
  // 
  input                     dc40_addr_match, 
  input                     dc41_addr_match, 
  input                     wq0_addr_match,  
  input                     wq1_addr_match,  
  input                     wq2_addr_match,  
  input                     wq3_addr_match,  
  
  //////////////// Most recent WQ entry ///////////////////////////////////////
  // 
  input  [`npuarc_DMP_FIFO_RANGE]  wq_recent_wr_r,

  //////////////// Forwarding mux control  ////////////////////////////////////
  // 
  output reg                match_dc40,
  output reg                match_dc41,
  output reg                match_wq0,
  output reg                match_wq1,
  output reg                match_wq2,
  output reg                match_wq3,

  //////////////// Replay and FWD  conditions /////////////////////////////////
  // 
  output reg                replay,
  output reg                fwd_enable
);


// Local Declarations.
//
reg [3:0]  dc40_and_dc3;
reg [3:0]  dc41_and_dc3;
reg [3:0]  wq0_and_dc3;
reg [3:0]  wq1_and_dc3;
reg [3:0]  wq2_and_dc3;
reg [3:0]  wq3_and_dc3;

reg        dc40_any_match;
reg        dc41_any_match;
reg        wq0_any_match;
reg        wq1_any_match;
reg        wq2_any_match;
reg        wq3_any_match;

reg        dc40_match_dc3;
reg        dc41_match_dc3;
reg        wq0_match_dc3;
reg        wq1_match_dc3;
reg        wq2_match_dc3;
reg        wq3_match_dc3;

reg        dc40_partial_match;
reg        dc41_partial_match;
reg        wq0_partial_match;
reg        wq1_partial_match;
reg        wq2_partial_match;
reg        wq3_partial_match;

reg        dc40_partial_replay;
reg        dc41_partial_replay;
reg        wq0_partial_replay;
reg        wq1_partial_replay;
reg        wq2_partial_replay;
reg        wq3_partial_replay;

reg        dc40_full_match;
reg        dc41_full_match;
reg        wq0_full_match;
reg        wq1_full_match;
reg        wq2_full_match;
reg        wq3_full_match;

//////////////////////////////////////////////////////////////////////////////
// Full match of the bank mask
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_and_dc3_PROC
  //
  // The individual bank mask information of the DC3 instruction is ANDed with 
  // DC4 and WQ
  //
  dc40_and_dc3 = dc3_mask & dc40_mask;
  dc41_and_dc3 = dc3_mask & dc41_mask;
  wq0_and_dc3  = dc3_mask & wq0_mask;
  wq1_and_dc3  = dc3_mask & wq1_mask;
  wq2_and_dc3  = dc3_mask & wq2_mask;
  wq3_and_dc3  = dc3_mask & wq3_mask;
end

//////////////////////////////////////////////////////////////////////////////
// Mask Full Match Condition
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_match_dc3_PROC
  //
  // Now make sure that the mask of DC4 instruction and WQ matchs with the
  // DC3 instruction. This is a FULL Match condition.
  //
  dc40_match_dc3 = (dc40_and_dc3 == dc3_mask) & (|dc3_mask);
  dc41_match_dc3 = (dc41_and_dc3 == dc3_mask) & (|dc3_mask);
  wq0_match_dc3  = (wq0_and_dc3  == dc3_mask) & (|dc3_mask);
  wq1_match_dc3  = (wq1_and_dc3  == dc3_mask) & (|dc3_mask);
  wq2_match_dc3  = (wq2_and_dc3  == dc3_mask) & (|dc3_mask);
  wq3_match_dc3  = (wq3_and_dc3  == dc3_mask) & (|dc3_mask);

end


//////////////////////////////////////////////////////////////////////////////
// DC3 instruction has FULL Match
//
//////////////////////////////////////////////////////////////////////////////
wire   dc4_full_match;
assign dc4_full_match = (dc40_full_match | dc41_full_match);

always @*
begin : match_dc4_wq_PROC
  // When there is a FULL match with the address and the mask. 
  // When there is a FULL match with CA instruction, (because CA has 
  // the most recent information) then ignore the FULL match in WQ match
  //
  dc40_full_match = dc40_match_dc3 & dc40_addr_match;
  dc41_full_match = dc41_match_dc3 & dc41_addr_match;
  wq0_full_match  = wq0_match_dc3  & wq0_addr_match & (~dc4_full_match);
  wq1_full_match  = wq1_match_dc3  & wq1_addr_match & (~dc4_full_match); 
  wq2_full_match  = wq2_match_dc3  & wq2_addr_match & (~dc4_full_match);
  wq3_full_match  = wq3_match_dc3  & wq3_addr_match & (~dc4_full_match);
end


//////////////////////////////////////////////////////////////////////////////
// Mask Partial Match Condition 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_any_match_PROC
  // 
  // In case of a partial match with in the bank mask
  //
  dc40_any_match = | (dc40_and_dc3);
  dc41_any_match = | (dc41_and_dc3);
  wq0_any_match  = | (wq0_and_dc3);
  wq1_any_match  = | (wq1_and_dc3);
  wq2_any_match  = | (wq2_and_dc3);
  wq3_any_match  = | (wq3_and_dc3);
end

//////////////////////////////////////////////////////////////////////////////
// Partial match for the bank mask 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_partial_match_PROC
  // Partial match is assetred only when there is no FULL match condition
  //
  dc40_partial_match = dc40_any_match & (!dc40_match_dc3);
  dc41_partial_match = dc41_any_match & (!dc41_match_dc3);
  wq0_partial_match  = wq0_any_match  & (!wq0_match_dc3);
  wq1_partial_match  = wq1_any_match  & (!wq1_match_dc3);
  wq2_partial_match  = wq2_any_match  & (!wq2_match_dc3);
  wq3_partial_match  = wq3_any_match  & (!wq3_match_dc3);
end

//////////////////////////////////////////////////////////////////////////////
// Partial Match Replay Condition
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_partial_replay_PROC
  //
  // match should include the valid bits for the wq
  // There is an address match and a partial match with the bank mask
  //
  dc40_partial_replay = (dc40_addr_match & dc40_partial_match); 
  dc41_partial_replay = (dc41_addr_match & dc41_partial_match); 
  wq0_partial_replay  = (wq0_addr_match  & wq0_partial_match);
  wq1_partial_replay  = (wq1_addr_match  & wq1_partial_match);
  wq2_partial_replay  = (wq2_addr_match  & wq2_partial_match);
  wq3_partial_replay  = (wq3_addr_match  & wq3_partial_match);
end

//////////////////////////////////////////////////////////////////////////////
// 
// Check for the recent match in WQ
//
//////////////////////////////////////////////////////////////////////////////
reg wq_recent_full_match;

always @*
begin : wq_recent_full_match_PROC
  // 
  // Check whether WQ entries have a recent match.
  // 
  wq_recent_full_match     =   (wq0_full_match & wq_recent_wr_r[0])
                             | (wq1_full_match & wq_recent_wr_r[1])
                             | (wq2_full_match & wq_recent_wr_r[2])
                             | (wq3_full_match & wq_recent_wr_r[3]);
end
//////////////////////////////////////////////////////////////////////////////
// WQ0 has a match and other WQ entries also have a match
//
//////////////////////////////////////////////////////////////////////////////
reg  wq0_more_than_one_match;

always @*
begin : wq0_more_than_one_match_PROC
  //
  // When WQ0 has a FULL match and its not the recent and also some other WQ has a FULL match
  // 
  wq0_more_than_one_match  =  (wq0_full_match & (~wq_recent_wr_r[0]))
                            & (  wq1_full_match
                               | wq2_full_match  
                               | wq3_full_match
                              );
end

//////////////////////////////////////////////////////////////////////////////
// WQ1 has a match and other WQ entries also have a match
//
//////////////////////////////////////////////////////////////////////////////
reg  wq1_more_than_one_match;

always @*
begin : wq1_more_than_one_match_PROC
  //
  // When WQ1 has a FULL match and its not the recent and also some other WQ has a FULL match
  // 
  wq1_more_than_one_match  =  (wq1_full_match & (~wq_recent_wr_r[1]))
                            & (  wq0_full_match
                               | wq2_full_match
                               | wq3_full_match
                              );   
end

//////////////////////////////////////////////////////////////////////////////
// WQ2 has a match and other WQ entries also have a match
//
//////////////////////////////////////////////////////////////////////////////
reg  wq2_more_than_one_match;

always @*
begin : wq2_more_than_one_match_PROC
  //
  // When WQ2 has a FULL match and its not the recent and also some other WQ has a FULL match
  //        
  wq2_more_than_one_match  =  (wq2_full_match & (~wq_recent_wr_r[2]))
                            & (  wq0_full_match
                               | wq1_full_match
                               | wq3_full_match
                              );           
end

//////////////////////////////////////////////////////////////////////////////
// WQ3 has a match and other WQ entries also have a match
//
//////////////////////////////////////////////////////////////////////////////
reg  wq3_more_than_one_match;

always @*
begin : wq3_more_than_one_match_PROC
  //
  // When WQ3 has a FULL match and its not the recent and also some other WQ has a FULL match
  //        
  wq3_more_than_one_match  =  (wq3_full_match & (~wq_recent_wr_r[3]))
                            & (  wq0_full_match
                               | wq1_full_match
                               | wq2_full_match
                              );
end


//////////////////////////////////////////////////////////////////////////////
// Partial Match Replay and Full Match Replay
//
//////////////////////////////////////////////////////////////////////////////
reg match_partial_replay;
reg match_more_than_one_replay;

always @*
begin : match_partial_replay_PROC
  // 
  // Group all the partial match replay conditions
  //
  match_partial_replay       =  dc40_partial_replay
                              | dc41_partial_replay
                              | wq0_partial_replay
                              | wq1_partial_replay
                              | wq2_partial_replay
                              | wq3_partial_replay;
  //
  // Only do a FULL match replay when there is no WQ recent full match
  //    
  match_more_than_one_replay =  ~wq_recent_full_match
                               & (  wq0_more_than_one_match    
                                  | wq1_more_than_one_match
                                  | wq2_more_than_one_match
                                  | wq3_more_than_one_match);
end

//////////////////////////////////////////////////////////////////////////////
// Consolidate all the Replays
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : replay_PROC
  // 
  // Consolidate all the partial and full replay conditions 
  // There will not be a replay when there is a DC4 FULL match
  //
  replay =   (~dc4_full_match)
           & (  match_partial_replay
              | match_more_than_one_replay);
end


/////////////////////////////////////////////////////////////////////////////
//
//Mux control to forward the data when there is not more than one match
//
////////////////////////////////////////////////////////////////////////////
always @*
begin : fwd_data_PROC
  match_dc40 = dc40_full_match; 
  match_dc41 = dc41_full_match;
  
  // (1) When there is a recent match, then forward the recent data
  // (2) When there is no match, then forward the full match data
  // 
  match_wq0  =  (wq0_full_match & wq_recent_wr_r[0])              // (1)
              | (wq0_full_match & (~wq0_more_than_one_match));    // (2)
    
  match_wq1  =  (wq1_full_match & wq_recent_wr_r[1])              // (1)
              | (wq1_full_match & (~wq1_more_than_one_match));    // (2)
    
  match_wq2  =  (wq2_full_match & wq_recent_wr_r[2])              // (1)
              | (wq2_full_match & (~wq2_more_than_one_match));    // (2)
    
  match_wq3  =  (wq3_full_match & wq_recent_wr_r[3])              // (1)
              | (wq3_full_match & (~wq3_more_than_one_match));    // (2)
end

//////////////////////////////////////////////////////////////////////////////
// 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : fwd_enable_PROC
  // This is used to enable the four banks in case of forwarding based on 
  // the full match condition
  //
  fwd_enable =  (dc40_any_match & dc40_addr_match)
              | (dc41_any_match & dc41_addr_match)
              | (wq0_any_match  & wq0_addr_match)
              | (wq1_any_match  & wq1_addr_match)
              | (wq2_any_match  & wq2_addr_match)
              | (wq3_any_match  & wq3_addr_match);
end

endmodule // alb_dmp_bank_match
