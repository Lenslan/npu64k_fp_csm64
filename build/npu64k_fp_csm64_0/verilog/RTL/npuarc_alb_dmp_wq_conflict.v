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
//   ALB_DMP_WQ_CONLICT                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module implements the check required to resolve memory disambiguation
//  that requires stall cycles, i.e.: it cant be resolved by forwarding the 
//  store data directly from DC4 or WQ
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_wq_conflict.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_wq_conflict #(parameter ADDR_MSB = 11)
(


  ////////// Inputs from X2 ///////////////////////////////////////////////
  //
  input                         x2_load_r,
  input [1:0]                   x2_size_r,           //
  input [ADDR_MSB:0]            x2_mem_addr0_r,      // X3 memory address
  input [ADDR_MSB:0]            x2_mem_addr1_r,      // X3 memory address
  input [3:0]                   x2_bank_sel_r,       //

  ////////// Inputs from X3 /////////////////////////////////////////////
  //
  input                         x3_store_r,          // X3 store 
  input                         x3_store_may_grad,
  input [ADDR_MSB:0]            x3_mem_addr0_r,      // X3 memory address
  input [ADDR_MSB:0]            x3_mem_addr1_r,      // X3 memory address
  input [3:0]                   x3_bank_sel_r,       //
  input [7:0]                   x30_mask_bank0,
  input [7:0]                   x30_mask_bank1,
  input [7:0]                   x31_mask_bank0,
  input [7:0]                   x31_mask_bank1,
  
  ////////// Inputs from CA /////////////////////////////////////////////
  //
  input                         ca_store_r,          // X3 store 
  input                         ca_grad_r,
  input [ADDR_MSB:0]            ca_mem_addr0_r,      // X3 memory address
  input [ADDR_MSB:0]            ca_mem_addr1_r,      // X3 memory address
  input [3:0]                   ca_bank_sel_r,       //
  input [7:0]                   ca0_mask_bank0,
  input [7:0]                   ca0_mask_bank1,
  input [7:0]                   ca1_mask_bank0,
  input [7:0]                   ca1_mask_bank1,
  
  ////////// Inputs from WQ fifo ///////////////////////////////////////
  //
  input [`npuarc_DMP_FIFO_RANGE]       wq_recent_wr_r,
  input                         wq0_valid_r,
  input                         wq0_grad_r,
  input [ADDR_MSB:0]            wq0_addr_r,     
  input [7:0]                   wq0_mask_bank0,
  input [7:0]                   wq0_mask_bank1,
  input                         wq1_valid_r,
  input                         wq1_grad_r,
  input [ADDR_MSB:0]            wq1_addr_r,     
  input [7:0]                   wq1_mask_bank0,
  input [7:0]                   wq1_mask_bank1,
  input                         wq2_valid_r,
  input                         wq2_grad_r,
  input [ADDR_MSB:0]            wq2_addr_r,     
  input [7:0]                   wq2_mask_bank0,
  input [7:0]                   wq2_mask_bank1,
  input                         wq3_valid_r,
  input                         wq3_grad_r,
  input [ADDR_MSB:0]            wq3_addr_r,     
  input [7:0]                   wq3_mask_bank0,
  input [7:0]                   wq3_mask_bank1,
  
  ////////// Outputs ////////////////////////////////////////////////////
  //
  output reg                    dc2_grad_conflict,
  output reg                    dc2_partial_match_conflict,  
  output                        dc2_multi_match_conflict   
);


task automatic load_conflict;
  output  reg        load_conflict;
  
  input              load_valid;
  input [ADDR_MSB:4] load_addr;
  input [15:0]       load_mask;
  
  input              store_valid;
  input [ADDR_MSB:4] store_addr;
  input [15:0]       store_mask;
  
  reg   addr_match;
  reg   mask_conflict;

  begin  
    addr_match        = load_addr == store_addr;
    // In case of ECC/Parity, any mask should be used as the complete bank will be valid
    //
    mask_conflict     = (|load_mask[3:0]   & (|store_mask[3:0]))
                      | (|load_mask[7:4]   & (|store_mask[7:4]))
                      | (|load_mask[11:8]  & (|store_mask[11:8]))
                      | (|load_mask[15:12] & (|store_mask[15:12]));
    load_conflict     = load_valid
                      & store_valid
                      & addr_match
                      & mask_conflict;
  end      
endtask

task automatic addr_mask_match;
  // This computes the conflict between dc2 versus X3, CA and WQ
  //
  output reg          full_match;
  output reg          partial_match;

  input               load_valid;
  input [ADDR_MSB:4]  load_addr;
  input [3:0]         load_mask;

  input               store_valid;
  input [ADDR_MSB:4]  store_addr;
  input [3:0]         store_mask;
   
  reg                 addr_match;

  begin
    // Check for the addr match and LD ST valid
    //
    addr_match        = (load_addr == store_addr);
      
    // Check for the full mask match
    //   
    full_match        = addr_match
                      & load_valid
                      & store_valid
                      & (|load_mask)    
                      & ((load_mask & store_mask) == load_mask)
                      ;
    // Check for the partial mask match
    //    
    partial_match     = addr_match
                      & load_valid
                      & store_valid
                      & (|(load_mask & store_mask))
                      & (~full_match)
                      ;
  end      
endtask

//////////////////////////////////////////////////////////////////////////////
// Module instantiation
// 
//////////////////////////////////////////////////////////////////////////////
wire [2:0]   dc2_size0_r;
wire [2:0]   dc2_size1_r;

npuarc_alb_dmp_pre_size_aligner u_alb_dmp_pre_size_aligner_0 (
  .addr_2_to_0                  (x2_mem_addr0_r[2:0]),
  .size                         (x2_size_r         ),
  .bank_sel                     (x2_bank_sel_r),

  .aln_size0                    (dc2_size0_r),
  .aln_size1                    (dc2_size1_r)
);



wire [7:0]   dc20_mask_bank0; // hi-lo {1,0}
wire [7:0]   dc20_mask_bank1; // hi-lo {3,2}

wire [7:0]   dc21_mask_bank0; // hi-lo {1,0}
wire [7:0]   dc21_mask_bank1; // hi-lo {3,2}


npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_0 (
  .size           (dc2_size0_r        ),
  .addr_3_to_0    (x2_mem_addr0_r[3:0]),
  .valid_r        (1'b1               ), 
  
  .bank0_mask     (dc20_mask_bank0    ), // hi-lo
  .bank1_mask     (dc20_mask_bank1    )  // hi-lo
);

npuarc_alb_dmp_mask_aligner u_alb_dmp_mask_aligner_1 (
  .size           (dc2_size1_r        ),
  .addr_3_to_0    (4'b0000            ), // addr1 always start with 0's
  .valid_r        (1'b1               ), 
  
  .bank0_mask     (dc21_mask_bank0    ), // hi-lo
  .bank1_mask     (dc21_mask_bank1    )  // hi-lo
);

reg dc21_valid;
reg dc31_valid;
reg dc41_valid;

always @*
begin : unaligned_valid_PROC
  // This process checks the validity of unaligned stores, i.e.: the ones
  // that cross a 16-byte boundary
  //
  dc21_valid = x2_bank_sel_r[3] & x2_bank_sel_r[0];
  dc31_valid = x3_bank_sel_r[3] & x3_bank_sel_r[0];
  dc41_valid = ca_bank_sel_r[3] & ca_bank_sel_r[0];
end

reg dc20_dc30_addr_conflict;  // dc2_addr0 versus dc3_addr0
reg dc20_dc31_addr_conflict;  // dc2_addr0 versus dc3_addr1
reg dc21_dc30_addr_conflict;  // dc2_addr1 versus dc3_addr0
reg dc2_dc3_addr_conflict;    

reg dc20_dc40_addr_conflict;  // dc2_addr0 versus dc4_addr0
reg dc20_dc41_addr_conflict;  // dc2_addr0 versus dc4_addr1
reg dc21_dc40_addr_conflict;  // dc2_addr1 versus dc4_addr0
reg dc2_dc4_addr_conflict;    

reg dc20_wq0_addr_conflict;
reg dc21_wq0_addr_conflict;
reg dc2_wq0_addr_conflict;
reg dc20_wq1_addr_conflict;
reg dc21_wq1_addr_conflict;
reg dc2_wq1_addr_conflict;
reg dc20_wq2_addr_conflict;
reg dc21_wq2_addr_conflict;
reg dc2_wq2_addr_conflict;
reg dc20_wq3_addr_conflict;
reg dc21_wq3_addr_conflict;
reg dc2_wq3_addr_conflict;

//////////////////////////////////////////////////////////////////////////////
//
// DC2 LD conflicts with downstream stalls
//
//////////////////////////////////////////////////////////////////////////////

always @*
begin : dc2_conflict_PROC
  // DC2 load conflicts with DC3 store
  //
  load_conflict(dc20_dc30_addr_conflict,
                    
                x2_load_r,
                x2_mem_addr0_r[ADDR_MSB:4],
                {dc20_mask_bank1, dc20_mask_bank0},
                
                x3_store_r,
                x3_mem_addr0_r[ADDR_MSB:4],
                {x30_mask_bank1, x30_mask_bank0});
  
  
  load_conflict(dc20_dc31_addr_conflict,
                    
                x2_load_r,
                x2_mem_addr0_r[ADDR_MSB:4],
                {dc20_mask_bank1, dc20_mask_bank0},
                
                (x3_store_r & dc31_valid),
                x3_mem_addr1_r[ADDR_MSB:4],
                {x31_mask_bank1, x31_mask_bank0});
  
  load_conflict(dc21_dc30_addr_conflict,
                    
                (x2_load_r & dc21_valid),
                x2_mem_addr1_r[ADDR_MSB:4],
                {dc21_mask_bank1, dc21_mask_bank0},
                
                x3_store_r,
                x3_mem_addr0_r[ADDR_MSB:4],
                {x30_mask_bank1, x30_mask_bank0});
  
  // Putting it all together
  //
  dc2_dc3_addr_conflict = dc20_dc30_addr_conflict
                        | dc20_dc31_addr_conflict
                        | dc21_dc30_addr_conflict
                        ;
  
  // DC2 load conflicts with DC4 store
  //
  load_conflict(dc20_dc40_addr_conflict,
                    
                x2_load_r,
                x2_mem_addr0_r[ADDR_MSB:4],
                {dc20_mask_bank1, dc20_mask_bank0},
                
                ca_store_r,
                ca_mem_addr0_r[ADDR_MSB:4],
                {ca0_mask_bank1, ca0_mask_bank0});
                    
                    
  load_conflict(dc20_dc41_addr_conflict,
                    
                x2_load_r,
                x2_mem_addr0_r[ADDR_MSB:4],
                {dc20_mask_bank1, dc20_mask_bank0},
                
                (ca_store_r & dc41_valid),
                ca_mem_addr1_r[ADDR_MSB:4],
                {ca1_mask_bank1, ca1_mask_bank0});
                    
  load_conflict(dc21_dc40_addr_conflict,
                    
                (x2_load_r & dc21_valid),
                x2_mem_addr1_r[ADDR_MSB:4],
                {dc21_mask_bank1, dc21_mask_bank0},
                
                ca_store_r,
                ca_mem_addr0_r[ADDR_MSB:4],
                {ca0_mask_bank1, ca0_mask_bank0});
                    
  // Putting it all together
  //
  dc2_dc4_addr_conflict = dc20_dc40_addr_conflict
                        | dc20_dc41_addr_conflict
                        | dc21_dc40_addr_conflict
                        ;
  
                    
  // DC2 load conflicts with WQ
  //
  
  load_conflict(dc20_wq0_addr_conflict,
                    
                x2_load_r,
                x2_mem_addr0_r[ADDR_MSB:4],
                {dc20_mask_bank1, dc20_mask_bank0},
                
                wq0_valid_r,
                wq0_addr_r[ADDR_MSB:4],
                {wq0_mask_bank1, wq0_mask_bank0});
  
  load_conflict(dc21_wq0_addr_conflict,
                    
                (x2_load_r & dc21_valid),
                x2_mem_addr1_r[ADDR_MSB:4],
                {dc21_mask_bank1, dc21_mask_bank0},
               
                wq0_valid_r,
                wq0_addr_r[ADDR_MSB:4],
                {wq0_mask_bank1, wq0_mask_bank0});
  
  
  load_conflict(dc20_wq1_addr_conflict,
                    
                x2_load_r,
                x2_mem_addr0_r[ADDR_MSB:4],
                {dc20_mask_bank1, dc20_mask_bank0},
                
                wq1_valid_r,
                wq1_addr_r[ADDR_MSB:4],
                {wq1_mask_bank1, wq1_mask_bank0});
  
  load_conflict(dc21_wq1_addr_conflict,
                    
                (x2_load_r & dc21_valid),
                x2_mem_addr1_r[ADDR_MSB:4],
                {dc21_mask_bank1, dc21_mask_bank0},
               
                wq1_valid_r,
                wq1_addr_r[ADDR_MSB:4],
                {wq1_mask_bank1, wq1_mask_bank0});
  
  
  load_conflict(dc20_wq2_addr_conflict,
                    
                x2_load_r,
                x2_mem_addr0_r[ADDR_MSB:4],
                {dc20_mask_bank1, dc20_mask_bank0},
                
                wq2_valid_r,
                wq2_addr_r[ADDR_MSB:4],
                {wq2_mask_bank1, wq2_mask_bank0});
  
  load_conflict(dc21_wq2_addr_conflict,
                    
                (x2_load_r & dc21_valid),
                x2_mem_addr1_r[ADDR_MSB:4],
                {dc21_mask_bank1, dc21_mask_bank0},
               
                wq2_valid_r,
                wq2_addr_r[ADDR_MSB:4],
                {wq2_mask_bank1, wq2_mask_bank0});
  
  
  load_conflict(dc20_wq3_addr_conflict,
                    
                x2_load_r,
                x2_mem_addr0_r[ADDR_MSB:4],
                {dc20_mask_bank1, dc20_mask_bank0},
                
                wq3_valid_r,
                wq3_addr_r[ADDR_MSB:4],
                {wq3_mask_bank1, wq3_mask_bank0});
  
  load_conflict(dc21_wq3_addr_conflict,
                    
                (x2_load_r & dc21_valid),
                x2_mem_addr1_r[ADDR_MSB:4],
                {dc21_mask_bank1, dc21_mask_bank0},
               
                wq3_valid_r,
                wq3_addr_r[ADDR_MSB:4],
                {wq3_mask_bank1, wq3_mask_bank0});
  
  
  // Putting it all together
  //
  dc2_wq0_addr_conflict = dc20_wq0_addr_conflict
                           | dc21_wq0_addr_conflict
                           ; 

  dc2_wq1_addr_conflict = dc20_wq1_addr_conflict
                           | dc21_wq1_addr_conflict
                           ; 

  dc2_wq2_addr_conflict = dc20_wq2_addr_conflict
                           | dc21_wq2_addr_conflict
                           ; 

  dc2_wq3_addr_conflict = dc20_wq3_addr_conflict
                           | dc21_wq3_addr_conflict
                           ; 

end

///////////////////////////////////////////////////////////////////////////////////
//
//  Compute partial and full match on a per bank basis: from DC2 to
//  downstream stalls
//
///////////////////////////////////////////////////////////////////////////////////

reg [3:0] dc20_dc30_partial_match;  // one per bank
reg [3:0] dc20_dc31_partial_match;  // one per bank
reg [3:0] dc21_dc30_partial_match;  // one per bank

reg [3:0] dc20_dc30_full_match;     // one per bank
reg [3:0] dc20_dc31_full_match;     // one per bank
reg [3:0] dc21_dc30_full_match;     // one per bank

reg [3:0] dc2_dc3_full_match;       // one per bank
reg [3:0] dc2_dc3_partial_match;    // one per bank

reg [3:0] dc20_dc40_partial_match;  // one per bank
reg [3:0] dc20_dc41_partial_match;  // one per bank
reg [3:0] dc21_dc40_partial_match;  // one per bank

reg [3:0] dc20_dc40_full_match;     // one per bank
reg [3:0] dc20_dc41_full_match;     // one per bank
reg [3:0] dc21_dc40_full_match;     // one per bank

reg [3:0] dc2_dc4_full_match;       // one per bank
reg [3:0] dc2_dc4_partial_match;    // one per bank

reg [3:0] dc20_wq0_partial_match;  // one per bank
reg [3:0] dc21_wq0_partial_match;  // one per bank

reg [3:0] dc20_wq0_full_match;     // one per bank
reg [3:0] dc21_wq0_full_match;     // one per bank
reg [3:0] dc2_wq0_full_match;      // one per bank
reg [3:0] dc20_wq1_partial_match;  // one per bank
reg [3:0] dc21_wq1_partial_match;  // one per bank

reg [3:0] dc20_wq1_full_match;     // one per bank
reg [3:0] dc21_wq1_full_match;     // one per bank
reg [3:0] dc2_wq1_full_match;      // one per bank
reg [3:0] dc20_wq2_partial_match;  // one per bank
reg [3:0] dc21_wq2_partial_match;  // one per bank

reg [3:0] dc20_wq2_full_match;     // one per bank
reg [3:0] dc21_wq2_full_match;     // one per bank
reg [3:0] dc2_wq2_full_match;      // one per bank
reg [3:0] dc20_wq3_partial_match;  // one per bank
reg [3:0] dc21_wq3_partial_match;  // one per bank

reg [3:0] dc20_wq3_full_match;     // one per bank
reg [3:0] dc21_wq3_full_match;     // one per bank
reg [3:0] dc2_wq3_full_match;      // one per bank

// spyglass disable_block W553
always @*
begin : dc2_bank0_match_PROC
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr0 with dc3 addr0
  //
  addr_mask_match(dc20_dc30_full_match[0],
                  dc20_dc30_partial_match[0],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[3:0],
                  
                  x3_store_r,
                  x3_mem_addr0_r[ADDR_MSB:4],
                  x30_mask_bank0[3:0]
                 );   
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr0 with dc3 addr1
  //
  addr_mask_match(dc20_dc31_full_match[0],
                  dc20_dc31_partial_match[0],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[3:0],
                  
                  (x3_store_r & dc31_valid),
                  x3_mem_addr1_r[ADDR_MSB:4],
                  x31_mask_bank0[3:0]
                 );   
  
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr1 with dc3 addr0
  //
  addr_mask_match(dc21_dc30_full_match[0],
                  dc21_dc30_partial_match[0],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank0[3:0],
                  
                  x3_store_r,
                  x3_mem_addr0_r[ADDR_MSB:4],
                  x30_mask_bank0[3:0]
                 );   
  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // dc2 addr0 with dc4 addr0
  //
  addr_mask_match(dc20_dc40_full_match[0],
                  dc20_dc40_partial_match[0],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[3:0],
                  
                  ca_store_r,
                  ca_mem_addr0_r[ADDR_MSB:4],
                  ca0_mask_bank0[3:0]
                 );   

  
  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // dc2 addr0 with dc4 addr1
  //
  addr_mask_match(dc20_dc41_full_match[0],
                  dc20_dc41_partial_match[0],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[3:0],
                  
                  (ca_store_r & dc41_valid),
                  ca_mem_addr1_r[ADDR_MSB:4],
                  ca1_mask_bank0[3:0]
                 );   

  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // DC2 addr1 with dc4 addr0
  //
  addr_mask_match(dc21_dc40_full_match[0],
                  dc21_dc40_partial_match[0],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc21_mask_bank0[3:0],
                  
                  ca_store_r,
                  ca_mem_addr1_r[ADDR_MSB:4],
                  ca0_mask_bank0[3:0]
                 );   
  
  ////////////////////  DC2 -> WQ   ////////////////////////
  //
  // dc2 addr0 with WQ0 addr0
  //
  addr_mask_match(dc20_wq0_full_match[0],
                  dc20_wq0_partial_match[0],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[3:0],
                  
                  wq0_valid_r,
                  wq0_addr_r[ADDR_MSB:4],
                  wq0_mask_bank0[3:0]
                 );   

  // dc2 addr1 with WQ0 addr0
  //
  addr_mask_match(dc21_wq0_full_match[0],
                  dc21_wq0_partial_match[0],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank0[3:0],
                  
                  wq0_valid_r,
                  wq0_addr_r[ADDR_MSB:4],
                  wq0_mask_bank0[3:0]
                 );   

  // dc2 addr0 with WQ1 addr0
  //
  addr_mask_match(dc20_wq1_full_match[0],
                  dc20_wq1_partial_match[0],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[3:0],
                  
                  wq1_valid_r,
                  wq1_addr_r[ADDR_MSB:4],
                  wq1_mask_bank0[3:0]
                 );   

  // dc2 addr1 with WQ1 addr0
  //
  addr_mask_match(dc21_wq1_full_match[0],
                  dc21_wq1_partial_match[0],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank0[3:0],
                  
                  wq1_valid_r,
                  wq1_addr_r[ADDR_MSB:4],
                  wq1_mask_bank0[3:0]
                 );   

  // dc2 addr0 with WQ2 addr0
  //
  addr_mask_match(dc20_wq2_full_match[0],
                  dc20_wq2_partial_match[0],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[3:0],
                  
                  wq2_valid_r,
                  wq2_addr_r[ADDR_MSB:4],
                  wq2_mask_bank0[3:0]
                 );   

  // dc2 addr1 with WQ2 addr0
  //
  addr_mask_match(dc21_wq2_full_match[0],
                  dc21_wq2_partial_match[0],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank0[3:0],
                  
                  wq2_valid_r,
                  wq2_addr_r[ADDR_MSB:4],
                  wq2_mask_bank0[3:0]
                 );   

  // dc2 addr0 with WQ3 addr0
  //
  addr_mask_match(dc20_wq3_full_match[0],
                  dc20_wq3_partial_match[0],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[3:0],
                  
                  wq3_valid_r,
                  wq3_addr_r[ADDR_MSB:4],
                  wq3_mask_bank0[3:0]
                 );   

  // dc2 addr1 with WQ3 addr0
  //
  addr_mask_match(dc21_wq3_full_match[0],
                  dc21_wq3_partial_match[0],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank0[3:0],
                  
                  wq3_valid_r,
                  wq3_addr_r[ADDR_MSB:4],
                  wq3_mask_bank0[3:0]
                 );   


end
always @*
begin : dc2_bank1_match_PROC
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr0 with dc3 addr0
  //
  addr_mask_match(dc20_dc30_full_match[1],
                  dc20_dc30_partial_match[1],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[7:4],
                  
                  x3_store_r,
                  x3_mem_addr0_r[ADDR_MSB:4],
                  x30_mask_bank0[7:4]
                 );   
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr0 with dc3 addr1
  //
  addr_mask_match(dc20_dc31_full_match[1],
                  dc20_dc31_partial_match[1],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[7:4],
                  
                  (x3_store_r & dc31_valid),
                  x3_mem_addr1_r[ADDR_MSB:4],
                  x31_mask_bank0[7:4]
                 );   
  
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr1 with dc3 addr0
  //
  addr_mask_match(dc21_dc30_full_match[1],
                  dc21_dc30_partial_match[1],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank0[7:4],
                  
                  x3_store_r,
                  x3_mem_addr0_r[ADDR_MSB:4],
                  x30_mask_bank0[7:4]
                 );   
  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // dc2 addr0 with dc4 addr0
  //
  addr_mask_match(dc20_dc40_full_match[1],
                  dc20_dc40_partial_match[1],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[7:4],
                  
                  ca_store_r,
                  ca_mem_addr0_r[ADDR_MSB:4],
                  ca0_mask_bank0[7:4]
                 );   

  
  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // dc2 addr0 with dc4 addr1
  //
  addr_mask_match(dc20_dc41_full_match[1],
                  dc20_dc41_partial_match[1],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[7:4],
                  
                  (ca_store_r & dc41_valid),
                  ca_mem_addr1_r[ADDR_MSB:4],
                  ca1_mask_bank0[7:4]
                 );   

  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // DC2 addr1 with dc4 addr0
  //
  addr_mask_match(dc21_dc40_full_match[1],
                  dc21_dc40_partial_match[1],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc21_mask_bank0[7:4],
                  
                  ca_store_r,
                  ca_mem_addr1_r[ADDR_MSB:4],
                  ca0_mask_bank0[7:4]
                 );   
  
  ////////////////////  DC2 -> WQ   ////////////////////////
  //
  // dc2 addr0 with WQ0 addr0
  //
  addr_mask_match(dc20_wq0_full_match[1],
                  dc20_wq0_partial_match[1],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[7:4],
                  
                  wq0_valid_r,
                  wq0_addr_r[ADDR_MSB:4],
                  wq0_mask_bank0[7:4]
                 );   

  // dc2 addr1 with WQ0 addr0
  //
  addr_mask_match(dc21_wq0_full_match[1],
                  dc21_wq0_partial_match[1],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank0[7:4],
                  
                  wq0_valid_r,
                  wq0_addr_r[ADDR_MSB:4],
                  wq0_mask_bank0[7:4]
                 );   

  // dc2 addr0 with WQ1 addr0
  //
  addr_mask_match(dc20_wq1_full_match[1],
                  dc20_wq1_partial_match[1],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[7:4],
                  
                  wq1_valid_r,
                  wq1_addr_r[ADDR_MSB:4],
                  wq1_mask_bank0[7:4]
                 );   

  // dc2 addr1 with WQ1 addr0
  //
  addr_mask_match(dc21_wq1_full_match[1],
                  dc21_wq1_partial_match[1],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank0[7:4],
                  
                  wq1_valid_r,
                  wq1_addr_r[ADDR_MSB:4],
                  wq1_mask_bank0[7:4]
                 );   

  // dc2 addr0 with WQ2 addr0
  //
  addr_mask_match(dc20_wq2_full_match[1],
                  dc20_wq2_partial_match[1],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[7:4],
                  
                  wq2_valid_r,
                  wq2_addr_r[ADDR_MSB:4],
                  wq2_mask_bank0[7:4]
                 );   

  // dc2 addr1 with WQ2 addr0
  //
  addr_mask_match(dc21_wq2_full_match[1],
                  dc21_wq2_partial_match[1],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank0[7:4],
                  
                  wq2_valid_r,
                  wq2_addr_r[ADDR_MSB:4],
                  wq2_mask_bank0[7:4]
                 );   

  // dc2 addr0 with WQ3 addr0
  //
  addr_mask_match(dc20_wq3_full_match[1],
                  dc20_wq3_partial_match[1],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank0[7:4],
                  
                  wq3_valid_r,
                  wq3_addr_r[ADDR_MSB:4],
                  wq3_mask_bank0[7:4]
                 );   

  // dc2 addr1 with WQ3 addr0
  //
  addr_mask_match(dc21_wq3_full_match[1],
                  dc21_wq3_partial_match[1],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank0[7:4],
                  
                  wq3_valid_r,
                  wq3_addr_r[ADDR_MSB:4],
                  wq3_mask_bank0[7:4]
                 );   


end
always @*
begin : dc2_bank2_match_PROC
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr0 with dc3 addr0
  //
  addr_mask_match(dc20_dc30_full_match[2],
                  dc20_dc30_partial_match[2],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[3:0],
                  
                  x3_store_r,
                  x3_mem_addr0_r[ADDR_MSB:4],
                  x30_mask_bank1[3:0]
                 );   
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr0 with dc3 addr1
  //
  addr_mask_match(dc20_dc31_full_match[2],
                  dc20_dc31_partial_match[2],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[3:0],
                  
                  (x3_store_r & dc31_valid),
                  x3_mem_addr1_r[ADDR_MSB:4],
                  x31_mask_bank1[3:0]
                 );   
  
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr1 with dc3 addr0
  //
  addr_mask_match(dc21_dc30_full_match[2],
                  dc21_dc30_partial_match[2],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank1[3:0],
                  
                  x3_store_r,
                  x3_mem_addr0_r[ADDR_MSB:4],
                  x30_mask_bank1[3:0]
                 );   
  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // dc2 addr0 with dc4 addr0
  //
  addr_mask_match(dc20_dc40_full_match[2],
                  dc20_dc40_partial_match[2],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[3:0],
                  
                  ca_store_r,
                  ca_mem_addr0_r[ADDR_MSB:4],
                  ca0_mask_bank1[3:0]
                 );   

  
  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // dc2 addr0 with dc4 addr1
  //
  addr_mask_match(dc20_dc41_full_match[2],
                  dc20_dc41_partial_match[2],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[3:0],
                  
                  (ca_store_r & dc41_valid),
                  ca_mem_addr1_r[ADDR_MSB:4],
                  ca1_mask_bank1[3:0]
                 );   

  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // DC2 addr1 with dc4 addr0
  //
  addr_mask_match(dc21_dc40_full_match[2],
                  dc21_dc40_partial_match[2],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc21_mask_bank1[3:0],
                  
                  ca_store_r,
                  ca_mem_addr1_r[ADDR_MSB:4],
                  ca0_mask_bank1[3:0]
                 );   
  
  ////////////////////  DC2 -> WQ   ////////////////////////
  //
  // dc2 addr0 with WQ0 addr0
  //
  addr_mask_match(dc20_wq0_full_match[2],
                  dc20_wq0_partial_match[2],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[3:0],
                  
                  wq0_valid_r,
                  wq0_addr_r[ADDR_MSB:4],
                  wq0_mask_bank1[3:0]
                 );   

  // dc2 addr1 with WQ0 addr0
  //
  addr_mask_match(dc21_wq0_full_match[2],
                  dc21_wq0_partial_match[2],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank1[3:0],
                  
                  wq0_valid_r,
                  wq0_addr_r[ADDR_MSB:4],
                  wq0_mask_bank1[3:0]
                 );   

  // dc2 addr0 with WQ1 addr0
  //
  addr_mask_match(dc20_wq1_full_match[2],
                  dc20_wq1_partial_match[2],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[3:0],
                  
                  wq1_valid_r,
                  wq1_addr_r[ADDR_MSB:4],
                  wq1_mask_bank1[3:0]
                 );   

  // dc2 addr1 with WQ1 addr0
  //
  addr_mask_match(dc21_wq1_full_match[2],
                  dc21_wq1_partial_match[2],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank1[3:0],
                  
                  wq1_valid_r,
                  wq1_addr_r[ADDR_MSB:4],
                  wq1_mask_bank1[3:0]
                 );   

  // dc2 addr0 with WQ2 addr0
  //
  addr_mask_match(dc20_wq2_full_match[2],
                  dc20_wq2_partial_match[2],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[3:0],
                  
                  wq2_valid_r,
                  wq2_addr_r[ADDR_MSB:4],
                  wq2_mask_bank1[3:0]
                 );   

  // dc2 addr1 with WQ2 addr0
  //
  addr_mask_match(dc21_wq2_full_match[2],
                  dc21_wq2_partial_match[2],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank1[3:0],
                  
                  wq2_valid_r,
                  wq2_addr_r[ADDR_MSB:4],
                  wq2_mask_bank1[3:0]
                 );   

  // dc2 addr0 with WQ3 addr0
  //
  addr_mask_match(dc20_wq3_full_match[2],
                  dc20_wq3_partial_match[2],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[3:0],
                  
                  wq3_valid_r,
                  wq3_addr_r[ADDR_MSB:4],
                  wq3_mask_bank1[3:0]
                 );   

  // dc2 addr1 with WQ3 addr0
  //
  addr_mask_match(dc21_wq3_full_match[2],
                  dc21_wq3_partial_match[2],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank1[3:0],
                  
                  wq3_valid_r,
                  wq3_addr_r[ADDR_MSB:4],
                  wq3_mask_bank1[3:0]
                 );   


end
always @*
begin : dc2_bank3_match_PROC
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr0 with dc3 addr0
  //
  addr_mask_match(dc20_dc30_full_match[3],
                  dc20_dc30_partial_match[3],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[7:4],
                  
                  x3_store_r,
                  x3_mem_addr0_r[ADDR_MSB:4],
                  x30_mask_bank1[7:4]
                 );   
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr0 with dc3 addr1
  //
  addr_mask_match(dc20_dc31_full_match[3],
                  dc20_dc31_partial_match[3],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[7:4],
                  
                  (x3_store_r & dc31_valid),
                  x3_mem_addr1_r[ADDR_MSB:4],
                  x31_mask_bank1[7:4]
                 );   
  
  
  ////////////////////  DC2 -> DC3   ////////////////////////
  //
  // dc2 addr1 with dc3 addr0
  //
  addr_mask_match(dc21_dc30_full_match[3],
                  dc21_dc30_partial_match[3],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank1[7:4],
                  
                  x3_store_r,
                  x3_mem_addr0_r[ADDR_MSB:4],
                  x30_mask_bank1[7:4]
                 );   
  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // dc2 addr0 with dc4 addr0
  //
  addr_mask_match(dc20_dc40_full_match[3],
                  dc20_dc40_partial_match[3],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[7:4],
                  
                  ca_store_r,
                  ca_mem_addr0_r[ADDR_MSB:4],
                  ca0_mask_bank1[7:4]
                 );   

  
  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // dc2 addr0 with dc4 addr1
  //
  addr_mask_match(dc20_dc41_full_match[3],
                  dc20_dc41_partial_match[3],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[7:4],
                  
                  (ca_store_r & dc41_valid),
                  ca_mem_addr1_r[ADDR_MSB:4],
                  ca1_mask_bank1[7:4]
                 );   

  
  ////////////////////  DC2 -> DC4   ////////////////////////
  //
  // DC2 addr1 with dc4 addr0
  //
  addr_mask_match(dc21_dc40_full_match[3],
                  dc21_dc40_partial_match[3],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc21_mask_bank1[7:4],
                  
                  ca_store_r,
                  ca_mem_addr1_r[ADDR_MSB:4],
                  ca0_mask_bank1[7:4]
                 );   
  
  ////////////////////  DC2 -> WQ   ////////////////////////
  //
  // dc2 addr0 with WQ0 addr0
  //
  addr_mask_match(dc20_wq0_full_match[3],
                  dc20_wq0_partial_match[3],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[7:4],
                  
                  wq0_valid_r,
                  wq0_addr_r[ADDR_MSB:4],
                  wq0_mask_bank1[7:4]
                 );   

  // dc2 addr1 with WQ0 addr0
  //
  addr_mask_match(dc21_wq0_full_match[3],
                  dc21_wq0_partial_match[3],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank1[7:4],
                  
                  wq0_valid_r,
                  wq0_addr_r[ADDR_MSB:4],
                  wq0_mask_bank1[7:4]
                 );   

  // dc2 addr0 with WQ1 addr0
  //
  addr_mask_match(dc20_wq1_full_match[3],
                  dc20_wq1_partial_match[3],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[7:4],
                  
                  wq1_valid_r,
                  wq1_addr_r[ADDR_MSB:4],
                  wq1_mask_bank1[7:4]
                 );   

  // dc2 addr1 with WQ1 addr0
  //
  addr_mask_match(dc21_wq1_full_match[3],
                  dc21_wq1_partial_match[3],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank1[7:4],
                  
                  wq1_valid_r,
                  wq1_addr_r[ADDR_MSB:4],
                  wq1_mask_bank1[7:4]
                 );   

  // dc2 addr0 with WQ2 addr0
  //
  addr_mask_match(dc20_wq2_full_match[3],
                  dc20_wq2_partial_match[3],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[7:4],
                  
                  wq2_valid_r,
                  wq2_addr_r[ADDR_MSB:4],
                  wq2_mask_bank1[7:4]
                 );   

  // dc2 addr1 with WQ2 addr0
  //
  addr_mask_match(dc21_wq2_full_match[3],
                  dc21_wq2_partial_match[3],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank1[7:4],
                  
                  wq2_valid_r,
                  wq2_addr_r[ADDR_MSB:4],
                  wq2_mask_bank1[7:4]
                 );   

  // dc2 addr0 with WQ3 addr0
  //
  addr_mask_match(dc20_wq3_full_match[3],
                  dc20_wq3_partial_match[3],  
                  
                  x2_load_r,
                  x2_mem_addr0_r[ADDR_MSB:4],
                  dc20_mask_bank1[7:4],
                  
                  wq3_valid_r,
                  wq3_addr_r[ADDR_MSB:4],
                  wq3_mask_bank1[7:4]
                 );   

  // dc2 addr1 with WQ3 addr0
  //
  addr_mask_match(dc21_wq3_full_match[3],
                  dc21_wq3_partial_match[3],  
                  
                  (x2_load_r & dc21_valid),
                  x2_mem_addr1_r[ADDR_MSB:4],
                  dc21_mask_bank1[7:4],
                  
                  wq3_valid_r,
                  wq3_addr_r[ADDR_MSB:4],
                  wq3_mask_bank1[7:4]
                 );   


end
// spyglass enable_block W553

always @*
begin : dc2_full_match_PROC
  // This determines whether there is a full_match with DC2 and DC3/CA/WQ
  //
  
  dc2_dc3_full_match = dc20_dc30_full_match 
                     | dc20_dc31_full_match 
                     | dc21_dc30_full_match;

  dc2_dc4_full_match = dc20_dc40_full_match 
                     | dc20_dc41_full_match 
                     | dc21_dc40_full_match;

  dc2_wq0_full_match =  dc20_wq0_full_match 
                         | dc21_wq0_full_match
                         ; 
  dc2_wq1_full_match =  dc20_wq1_full_match 
                         | dc21_wq1_full_match
                         ; 
  dc2_wq2_full_match =  dc20_wq2_full_match 
                         | dc21_wq2_full_match
                         ; 
  dc2_wq3_full_match =  dc20_wq3_full_match 
                         | dc21_wq3_full_match
                         ; 
end

//////////////////////////////////////////////////////////////////////////////
//
// DC2 LD conflicts with ST graduation
//
//////////////////////////////////////////////////////////////////////////////

reg dc2_dc3_grad_conflict;           // DC2 LD  conflicts with downstream grad ST
reg dc2_dc4_grad_conflict;           // DC2 LD  conflicts with downstream grad ST
reg dc2_wq0_grad_conflict;       // DC2 LD  conflicts with downstream grad ST
reg dc2_wq1_grad_conflict;       // DC2 LD  conflicts with downstream grad ST
reg dc2_wq2_grad_conflict;       // DC2 LD  conflicts with downstream grad ST
reg dc2_wq3_grad_conflict;       // DC2 LD  conflicts with downstream grad ST

// DC2 Load conficts with store grad
//
always @*
begin : dc2_grad_conflict_PROC 
  // This computes the individual componentes of the DC2 load conflict
  // against grad stores
  //
  dc2_dc3_grad_conflict    = dc2_dc3_addr_conflict & x3_store_may_grad;
  dc2_dc4_grad_conflict    = dc2_dc4_addr_conflict & ca_grad_r;
  dc2_wq0_grad_conflict = dc2_wq0_addr_conflict & wq0_grad_r; 
  dc2_wq1_grad_conflict = dc2_wq1_addr_conflict & wq1_grad_r; 
  dc2_wq2_grad_conflict = dc2_wq2_addr_conflict & wq2_grad_r; 
  dc2_wq3_grad_conflict = dc2_wq3_addr_conflict & wq3_grad_r; 
  
  // Putting it all together
  // 
  dc2_grad_conflict = dc2_dc3_grad_conflict
                    | dc2_dc4_grad_conflict
                    | dc2_wq0_grad_conflict
                    | dc2_wq1_grad_conflict
                    | dc2_wq2_grad_conflict
                    | dc2_wq3_grad_conflict
                    ;  
end

//////////////////////////////////////////////////////////////////////////////
//
// DC2 LD partial match conflicts
//
//////////////////////////////////////////////////////////////////////////////
reg       dc2_dc3_any_match;     
reg       dc2_dc4_any_match;     

reg       dc2_dc3_complete_match;    // DC3 completes satisfies DC2
reg       dc2_dc4_complete_match;    // DC4 completes satisfies DC2
always @*
begin : dc2_complete_PROC
   // Determines if there is any match between DC2 and DC3
   //
  dc2_dc3_any_match = (| dc2_dc3_full_match) 
                    | (| dc2_dc3_partial_match)
                    ;
   // Determines if there is any match between DC2 and DC4
   //
  dc2_dc4_any_match = (| dc2_dc4_full_match) 
                    | (| dc2_dc4_partial_match)
                    ;
  
   // Complete match means all banks are completely satisfied. A DC2 load
   // is completely satisfied by a DC3 store when all banks needed by the 
   // load have a full match with the store
   //
  dc2_dc3_complete_match = dc2_dc3_full_match == x2_bank_sel_r
                         ;
   
  dc2_dc4_complete_match = (dc2_dc4_full_match == x2_bank_sel_r)
                         & (~dc2_dc3_any_match)
                         ;
end

reg [3:0] dc2_wq_partial_match;       // one per bank
reg [3:0] dc2_partial_match_conflict_prel;

reg [3:0] wq_recent_full_match;
always @*
begin : wq_recent_full_match_PROC
  //
  // This identifies whether there is a recent full match that could able to satisfy a load
  //
wq_recent_full_match[0] = ~(x3_store_r & ca_store_r)
                         &  (
                             | (dc20_wq0_full_match[0] & wq_recent_wr_r[0])
                             | (dc21_wq0_full_match[0] & wq_recent_wr_r[0])
                             | (dc20_wq1_full_match[0] & wq_recent_wr_r[1])
                             | (dc21_wq1_full_match[0] & wq_recent_wr_r[1])
                             | (dc20_wq2_full_match[0] & wq_recent_wr_r[2])
                             | (dc21_wq2_full_match[0] & wq_recent_wr_r[2])
                             | (dc20_wq3_full_match[0] & wq_recent_wr_r[3])
                             | (dc21_wq3_full_match[0] & wq_recent_wr_r[3])
                            )
                         ;
wq_recent_full_match[1] = ~(x3_store_r & ca_store_r)
                         &  (
                             | (dc20_wq0_full_match[1] & wq_recent_wr_r[0])
                             | (dc21_wq0_full_match[1] & wq_recent_wr_r[0])
                             | (dc20_wq1_full_match[1] & wq_recent_wr_r[1])
                             | (dc21_wq1_full_match[1] & wq_recent_wr_r[1])
                             | (dc20_wq2_full_match[1] & wq_recent_wr_r[2])
                             | (dc21_wq2_full_match[1] & wq_recent_wr_r[2])
                             | (dc20_wq3_full_match[1] & wq_recent_wr_r[3])
                             | (dc21_wq3_full_match[1] & wq_recent_wr_r[3])
                            )
                         ;
wq_recent_full_match[2] = ~(x3_store_r & ca_store_r)
                         &  (
                             | (dc20_wq0_full_match[2] & wq_recent_wr_r[0])
                             | (dc21_wq0_full_match[2] & wq_recent_wr_r[0])
                             | (dc20_wq1_full_match[2] & wq_recent_wr_r[1])
                             | (dc21_wq1_full_match[2] & wq_recent_wr_r[1])
                             | (dc20_wq2_full_match[2] & wq_recent_wr_r[2])
                             | (dc21_wq2_full_match[2] & wq_recent_wr_r[2])
                             | (dc20_wq3_full_match[2] & wq_recent_wr_r[3])
                             | (dc21_wq3_full_match[2] & wq_recent_wr_r[3])
                            )
                         ;
wq_recent_full_match[3] = ~(x3_store_r & ca_store_r)
                         &  (
                             | (dc20_wq0_full_match[3] & wq_recent_wr_r[0])
                             | (dc21_wq0_full_match[3] & wq_recent_wr_r[0])
                             | (dc20_wq1_full_match[3] & wq_recent_wr_r[1])
                             | (dc21_wq1_full_match[3] & wq_recent_wr_r[1])
                             | (dc20_wq2_full_match[3] & wq_recent_wr_r[2])
                             | (dc21_wq2_full_match[3] & wq_recent_wr_r[2])
                             | (dc20_wq3_full_match[3] & wq_recent_wr_r[3])
                             | (dc21_wq3_full_match[3] & wq_recent_wr_r[3])
                            )
                         ;
end

always @*
begin : dc2_partial_match_PROC
  // Check for partial match on a per-bank basis
  //
  dc2_dc3_partial_match  = dc20_dc30_partial_match
                         | dc20_dc31_partial_match
                         | dc21_dc30_partial_match
                         ;

  dc2_dc4_partial_match  = dc20_dc40_partial_match 
                         | dc20_dc41_partial_match 
                         | dc21_dc40_partial_match
                         ;
  
  dc2_wq_partial_match   = 4'b0000
                         | (dc20_wq0_partial_match & (~wq_recent_full_match))
                         | (dc21_wq0_partial_match & (~wq_recent_full_match))
                         | (dc20_wq1_partial_match & (~wq_recent_full_match))
                         | (dc21_wq1_partial_match & (~wq_recent_full_match))
                         | (dc20_wq2_partial_match & (~wq_recent_full_match))
                         | (dc21_wq2_partial_match & (~wq_recent_full_match))
                         | (dc20_wq3_partial_match & (~wq_recent_full_match))
                         | (dc21_wq3_partial_match & (~wq_recent_full_match))
                         ;
  
  // Check partial match conflicts. There are three checks
  // 
  // Partial match with DC3                                     (1)
  // Partial match with DC4, eliminating DC3 full match         (2)
  // Partial match with WQ, eliminating DC3 and DC4 full match  (3)
  //
  dc2_partial_match_conflict_prel[0] = (dc2_dc3_partial_match[0])           // (1)
                                      | (  (~dc2_dc3_full_match[0]) 
                                         & dc2_dc4_partial_match[0])       // (2)
                                      | (  (~dc2_dc3_full_match[0])
                                         & (~dc2_dc4_full_match[0]) 
                                         & dc2_wq_partial_match[0])        // (3)
                                      ;
  dc2_partial_match_conflict_prel[1] = (dc2_dc3_partial_match[1])           // (1)
                                      | (  (~dc2_dc3_full_match[1]) 
                                         & dc2_dc4_partial_match[1])       // (2)
                                      | (  (~dc2_dc3_full_match[1])
                                         & (~dc2_dc4_full_match[1]) 
                                         & dc2_wq_partial_match[1])        // (3)
                                      ;
  dc2_partial_match_conflict_prel[2] = (dc2_dc3_partial_match[2])           // (1)
                                      | (  (~dc2_dc3_full_match[2]) 
                                         & dc2_dc4_partial_match[2])       // (2)
                                      | (  (~dc2_dc3_full_match[2])
                                         & (~dc2_dc4_full_match[2]) 
                                         & dc2_wq_partial_match[2])        // (3)
                                      ;
  dc2_partial_match_conflict_prel[3] = (dc2_dc3_partial_match[3])           // (1)
                                      | (  (~dc2_dc3_full_match[3]) 
                                         & dc2_dc4_partial_match[3])       // (2)
                                      | (  (~dc2_dc3_full_match[3])
                                         & (~dc2_dc4_full_match[3]) 
                                         & dc2_wq_partial_match[3])        // (3)
                                      ;

  dc2_partial_match_conflict = (|dc2_partial_match_conflict_prel);      
end
///there could be a partial match and a full match and wq recent could able to satisfy the LD
//
//////////////////////////////////////////////////////////////////////////////
//
// DC2 LD multi match conflicts
//
//////////////////////////////////////////////////////////////////////////////
// Partial match has already covered the multi - partial matches, (i.e) we stall when there is
// any partial match and no full match
//
// However, there could be many, full- multi matches,
wire [3:0] dc2_wq_full_multi_match;

assign dc2_wq_full_multi_match = (dc2_wq0_full_match & dc2_wq1_full_match)
                               | (dc2_wq0_full_match & dc2_wq2_full_match)
                               | (dc2_wq0_full_match & dc2_wq3_full_match)
                               | (dc2_wq1_full_match & dc2_wq2_full_match)
                               | (dc2_wq1_full_match & dc2_wq3_full_match)
                               | (dc2_wq2_full_match & dc2_wq3_full_match)
                               ;

reg [3:0] dc2_multi_match_conflict_prel;

always @*
begin : dc2_multi_match_conflict_prel_PROC
  //
  //
  //
  dc2_multi_match_conflict_prel[0] = dc2_wq_full_multi_match[0]
                                    & (~wq_recent_full_match[0]);
  dc2_multi_match_conflict_prel[1] = dc2_wq_full_multi_match[1]
                                    & (~wq_recent_full_match[1]);
  dc2_multi_match_conflict_prel[2] = dc2_wq_full_multi_match[2]
                                    & (~wq_recent_full_match[2]);
  dc2_multi_match_conflict_prel[3] = dc2_wq_full_multi_match[3]
                                    & (~wq_recent_full_match[3]);
end

assign dc2_multi_match_conflict = |dc2_multi_match_conflict_prel;

endmodule // alb_dmp_wq_conflict
