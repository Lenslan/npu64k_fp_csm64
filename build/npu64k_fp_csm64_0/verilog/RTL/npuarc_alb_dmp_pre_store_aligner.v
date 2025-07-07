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
//   ALB_DMP_PRE_STORE_ALIGNER                  
//                     
//                     
//                     
//
// ===========================================================================
//
// Description:
//  This module alignes the store data in accordance with the data banks. This 
//  helps in Write Queue on-the-fly alignement to always store the bank aligned
//  data.
//
//  This .vpp source file must be pre-processed with the Verilog
//  Pre-Processor (VPP) to produce the equivalent .v file using a command
//  such as:
//
//   vpp +q +o alb_dmp_pre_store_aligner.vpp
//
// ===========================================================================

// Configuration-dependent macro definitions
//
`include "npuarc_defines.v"

// Set simulation timescale
//
`include "const.def"

module npuarc_alb_dmp_pre_store_aligner (
// leda NTL_CON13C off
// LMD: non driving port
// LJ: some bits of inputs vectors are not used
  input                           ecc_dmp_disable,
  input                           ca_store_r,
  input                           ca_load_r,
  input                           ca_cache_byp_r,      
  input [`npuarc_PADDR_RANGE]            ca_mem_addr0_r,
  input [1:0]                     ca_size_r,
  input [`npuarc_DMP_DATA_RANGE]         ca_wr_data_r, 
  input [`npuarc_PADDR_RANGE]            dc4_mem_addr1_r,
  input [2:0]                     dc4_size0_r,
  input [2:0]                     dc4_size1_r,
  
  input [`npuarc_DMP_TARGET_RANGE]       dc4_target_r,
  input [1:0]                     dc4_hit0_way_hot,
  input [1:0]                     dc4_hit1_way_hot,
  input [1:0]                     dc4_data_bank_sel_lo_r,
  input [1:0]                     dc4_data_bank_sel_hi_r,
  input                           dc4_dt_line_cross_r,
  // DC4_data flops
  input [3:0]                     dc4_rmw_r,
  input [`npuarc_DATA_RANGE]             dc4_data_even_lo_r,
  input [`npuarc_DATA_RANGE]             dc4_data_even_hi_r,
  input [`npuarc_DATA_RANGE]             dc4_data_odd_lo_r,
  input [`npuarc_DATA_RANGE]             dc4_data_odd_hi_r,
  input [`npuarc_DATA_RANGE]             dc4_dd_data_even_lo_r,
  input [`npuarc_DATA_RANGE]             dc4_dd_data_even_hi_r,
  input [`npuarc_DATA_RANGE]             dc4_dd_data_odd_lo_r,
  input [`npuarc_DATA_RANGE]             dc4_dd_data_odd_hi_r,
  input [3:0]                     dc4_ecc_sb_error_r,
  input                           dc4_ecc_db_error_r,
  input [`npuarc_DATA_RANGE]             dc4_ecc_data_even_lo,
  input [`npuarc_DATA_RANGE]             dc4_ecc_data_even_hi,
  input [`npuarc_DATA_RANGE]             dc4_ecc_data_odd_lo,
  input [`npuarc_DATA_RANGE]             dc4_ecc_data_odd_hi,
  // WQ Forwarding 
  input [3:0]                     wq_fwd_bank_r,
  input [`npuarc_DATA_RANGE]             wq_fwd_data_bank0_lo_r,
  input [`npuarc_DATA_RANGE]             wq_fwd_data_bank0_hi_r,
  input [`npuarc_DATA_RANGE]             wq_fwd_data_bank1_lo_r,
  input [`npuarc_DATA_RANGE]             wq_fwd_data_bank1_hi_r,
  
  output reg                      dc4_wq_write0,
  output reg  [2:0]               dc4_wq_size0,
  output reg  [`npuarc_PADDR_RANGE]      dc4_wq_addr0,    
  output reg  [`npuarc_DMP_TARGET_RANGE] dc4_wq_target0,  
  output reg  [1:0]               dc4_wq_bank_lo0, 
  output reg  [1:0]               dc4_wq_bank_hi0,
  output reg  [`npuarc_DC_WAY_RANGE]     dc4_wq_way_hot0,
  output reg  [`npuarc_DMP_DATA_RANGE]   dc4_wq_data0,   
  output [`npuarc_DMP_BE_RANGE]          dc4_wq_ecc_data_mask0, 
  output reg                      dc4_wq_write1,
  output reg  [2:0]               dc4_wq_size1,
  output reg  [`npuarc_DMP_DATA_RANGE]   dc4_wq_data1,   
  output reg  [`npuarc_DMP_TARGET_RANGE] dc4_wq_target1,  
  output reg  [1:0]               dc4_wq_bank_lo1, 
  output reg  [1:0]               dc4_wq_bank_hi1,
  output reg  [`npuarc_DC_WAY_RANGE]     dc4_wq_way_hot1,
  output [`npuarc_DMP_BE_RANGE]          dc4_wq_ecc_data_mask1,            

  output reg  [`npuarc_PADDR_RANGE]      dc4_wq_addr1   
// leda NTL_CON13C on
);


// Local declarations
//

// leda NTL_CON12A off
// leda NTL_CON13A off
// LMD: undriven internal net Range:0-7
// LJ:  code readibility
reg [`npuarc_DOUBLE_RANGE]         data_extended;
reg [`npuarc_DOUBLE_RANGE]         data_pre_aln1;

reg [`npuarc_DMP_DATA_RANGE]       wq_data1;

reg  [`npuarc_DATA_RANGE]          dc4_rd_data0;
reg  [`npuarc_DATA_RANGE]          dc4_rd_data1;

wire [`npuarc_DMP_DATA_RANGE]      wq_ecc_data0;
wire [`npuarc_DMP_DATA_RANGE]      wq_ecc_data1;

wire [`npuarc_DMP_BE_RANGE]       wr_data_mask0; 
wire [`npuarc_DMP_BE_RANGE]       wr_data_mask1; 
wire                        ca_store_byte;  
wire                        ca_store_half;  
wire                        ca_store_word;  
wire                        ca_store_double;
reg [`npuarc_DMP_DATA_RANGE]       ca_wr_data_qual;
reg                         dc4_dc_target;
reg                         dc4_target_dc_dccm;
// leda NTL_CON12A on
// leda NTL_CON13A on


//////////////////////////////////////////////////////////////////////////////
//
//  MUX to select the data inputs 
//////////////////////////////////////////////////////////////////////////////
wire [`npuarc_DATA_RANGE]       dc4_data_even_lo; 
wire [`npuarc_DATA_RANGE]       dc4_data_even_hi; 
wire [`npuarc_DATA_RANGE]       dc4_data_odd_lo; 
wire [`npuarc_DATA_RANGE]       dc4_data_odd_hi;

assign dc4_data_even_lo =   wq_fwd_bank_r[0]
                          ? wq_fwd_data_bank0_lo_r
                          : (  dc4_ecc_sb_error_r[0]
                             ? dc4_ecc_data_even_lo
                             : ( (dc4_target_r == `npuarc_DMP_TARGET_DCCM)
                                ? dc4_data_even_lo_r : dc4_dd_data_even_lo_r)
                            )
                            ;     

assign dc4_data_even_hi =   wq_fwd_bank_r[1]
                          ? wq_fwd_data_bank0_hi_r
                          : (  dc4_ecc_sb_error_r[1]
                             ? dc4_ecc_data_even_hi 
                             : ( (dc4_target_r == `npuarc_DMP_TARGET_DCCM)
                                ? dc4_data_even_hi_r : dc4_dd_data_even_hi_r)
                            )
                            ;     

assign dc4_data_odd_lo =    wq_fwd_bank_r[2]
                          ? wq_fwd_data_bank1_lo_r
                          : (  dc4_ecc_sb_error_r[2]
                             ? dc4_ecc_data_odd_lo
                             : ( (dc4_target_r == `npuarc_DMP_TARGET_DCCM)
                                ? dc4_data_odd_lo_r : dc4_dd_data_odd_lo_r)
                            )
                            ;    

assign dc4_data_odd_hi =    wq_fwd_bank_r[3]
                          ? wq_fwd_data_bank1_hi_r
                          : (  dc4_ecc_sb_error_r[3]
                             ? dc4_ecc_data_odd_hi
                             : ( (dc4_target_r == `npuarc_DMP_TARGET_DCCM)
                                ? dc4_data_odd_hi_r : dc4_dd_data_odd_hi_r)
                            )
                            ;     

always @*
begin : dc4_target_PROC
  dc4_dc_target      =  (dc4_target_r == `npuarc_DMP_TARGET_DC) & (!ca_cache_byp_r);
  dc4_target_dc_dccm =  1'b0
                      | (dc4_target_r == `npuarc_DMP_TARGET_DC)
                      | (dc4_target_r == `npuarc_DMP_TARGET_DCCM)
                      ; 
end 

//////////////////////////////////////////////////////////////////////////////
// @ 
//
//////////////////////////////////////////////////////////////////////////////
// Incase of a single bit error, the dc4_rd_data should get the data from the 
// ecc_correction. When there is no error then the rd_data depends on the 
// partial stores (dc4_rmw_r)
//
wire [3:0] dc4_rd_data_sel;
assign dc4_rd_data_sel =  {dc4_data_bank_sel_hi_r[1], dc4_data_bank_sel_lo_r[1],
                           dc4_data_bank_sel_hi_r[0], dc4_data_bank_sel_lo_r[0]}
                        & ({4{dc4_target_dc_dccm}});
always @*
begin : dc4_rd_gata_PROC 
  case (dc4_rd_data_sel)
  4'b0111:
  begin
    // Banks 2,1,0
    //
    dc4_rd_data0 =  dc4_data_even_lo;  

    dc4_rd_data1 =  dc4_data_odd_lo;
  end
  
  4'b1110:
  begin
    // Banks 3,2,1
    //
    dc4_rd_data0 =  dc4_data_even_hi;  
 
    dc4_rd_data1 =  dc4_data_odd_hi;
  end
 
  4'b1101:
  begin
    // Banks 0,3,2
    //
    dc4_rd_data0 =  dc4_data_odd_lo;

    dc4_rd_data1 =  dc4_data_even_lo;
  end
  
  4'b1011:
  begin
    // Banks 1,0,3
    //
    dc4_rd_data0 =  dc4_data_odd_hi;
  
    dc4_rd_data1 =  dc4_data_even_hi;
  end

  4'b0001,
  4'b0011:
  begin
    // Start Bank 0
    //
    dc4_rd_data0 =  dc4_data_even_lo;
  
    dc4_rd_data1 =  dc4_data_even_hi;
  end
  
  4'b0010,
  4'b0110:
  begin
    // Start Bank 1
    //
    dc4_rd_data0 =  dc4_data_even_hi;
   
    dc4_rd_data1 =  dc4_data_odd_lo;
  end
  
  4'b0100,
  4'b1100:
  begin
    // Start bank 2
    //
    dc4_rd_data0 =  dc4_data_odd_lo;

    dc4_rd_data1 =  dc4_data_odd_hi;
  end
  
  default:   // 4'b1000,4'b1001:
  begin
    // Start bank 3
    //
    dc4_rd_data0 =  dc4_data_odd_hi;

    dc4_rd_data1 =  dc4_data_even_lo;
  end
  endcase
end  
  
//////////////////////////////////////////////////////////////////////////////
// Data1 (Data0 plus size) alignment  
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : data_pre_aln1_PROC 
  data_extended = ca_wr_data_qual;

  case ({ca_mem_addr0_r[2:0]})
  3'b001:
  begin
    data_pre_aln1   = { {56{1'b0}}, data_extended[63:56]};
  end     
  3'b010:
  begin
    data_pre_aln1   = { {48{1'b0}}, data_extended[63:48]};
  end
  3'b011:
  begin
    data_pre_aln1   = { {40{1'b0}}, data_extended[63:40]};
  end
  3'b100:
  begin
    data_pre_aln1   = { {32{1'b0}}, data_extended[63:32]};
  end
  3'b101:
  begin
    data_pre_aln1   = { {24{1'b0}}, data_extended[63:24]};
  end
  3'b110:
  begin
    data_pre_aln1   = { {16{1'b0}}, data_extended[63:16]};
  end
  default: // 3'b111:
  begin
    data_pre_aln1   = { {8{1'b0}}, data_extended[63:8]};
  end
  endcase
end


//////////////////////////////////////////////////////////////////////////////
// Data1 (Data0 plus size) alignment  
//
//////////////////////////////////////////////////////////////////////////////

always @*
begin : wq_data1_PROC 
  wq_data1 = data_pre_aln1;
end

//////////////////////////////////////////////////////////////////////////////
// 
//////////////////////////////////////////////////////////////////////////////
reg dc4_bank10_cross;
reg dc4_bank01_cross;
reg dc4_bank_any_cross;
always @*
begin : dc4_bank10_cross_PROC
  // An unaligned access may cause the write of two entries in the wq.
  // Two entries are written when a write needs bank0 and bank1
  //
  //   ________________________________________________________________
  //  |       bank 1         bank 1   |       bank 0         bank 0    |
  //  |     sel_hi[1]     sel_lo[1]   |     sel_hi[0]     sel_lo[0]    |
  //  |    _________      _________   |   _________       _________    |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |<------->|    |<------->|  |  |<------->|     |<------->|   |
  //  |   |   32B   |    |   32B   |  |  |   32B   |     |   32B   |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |         |    |         |  |  |         |     |         |   |
  //  |   |_________|    |_________|  |  |_________|     |_________|   |
  //  |                               |                                |
  //  |                               |                                |
  //  |_______________________________|________________________________|
  //  
  //
  dc4_bank10_cross   = dc4_data_bank_sel_hi_r[1] & dc4_data_bank_sel_lo_r[0];
  dc4_bank01_cross   = dc4_data_bank_sel_lo_r[1] & dc4_data_bank_sel_hi_r[0]; 
  dc4_bank_any_cross =  (dc4_data_bank_sel_lo_r[0] & dc4_data_bank_sel_hi_r[0])
                      | (dc4_data_bank_sel_hi_r[0] & dc4_data_bank_sel_lo_r[1])
                      | (dc4_data_bank_sel_lo_r[1] & dc4_data_bank_sel_hi_r[1])
                      ;
end

//////////////////////////////////////////////////////////////////////////////
//
// Write0 and Write1 signal generation
//
//////////////////////////////////////////////////////////////////////////////
// When there is a single bit error, theere will be two writes happening
// one for each bank.
//
wire dc4_ecc_only_sb_error;
assign dc4_ecc_only_sb_error = ((|dc4_ecc_sb_error_r) & (~dc4_ecc_db_error_r));

always @*
begin : dc4_wq_write_PROC
  // This indicates the store is for the the Data Cache
  //
  if (dc4_dc_target)
  begin
    dc4_wq_write0  =   (ca_store_r & (| dc4_hit0_way_hot))
                     | (ca_store_r & (~dc4_dc_target));
    dc4_wq_write1  =   dc4_dt_line_cross_r
                     ? (ca_store_r & (| dc4_hit1_way_hot))
                     : (  ca_store_r 
                        & ( dc4_bank10_cross 
                           | (dc4_bank01_cross   & dc4_dc_target & (|dc4_rmw_r))
                           )       
                        & (| dc4_hit0_way_hot));

  end
  else
  begin
    dc4_wq_write0 =   ca_store_r
                    | dc4_ecc_only_sb_error
                    ;
    dc4_wq_write1 = (  ca_store_r 
                     | dc4_ecc_only_sb_error
                    )     
                  & (  dc4_bank10_cross
                     | (    dc4_bank01_cross   & dc4_target_dc_dccm
                         & ( (|dc4_ecc_sb_error_r) | (|dc4_rmw_r) )
                       )
                    )
                    ;
  end
end

//////////////////////////////////////////////////////////////////////////////
//
// Address 0 and Address 1 
//
//////////////////////////////////////////////////////////////////////////////
// spyglass disable_block STARC05-2.8.1.3
// spyglass disable_block W398
// SMD: Possible case covered by multiple case statments.
// SJ:  Cases have priority, code more readable, optimized by synthesizer.
always @*
begin : dc4_wq_addr_PROC

  if (dc4_target_dc_dccm & (~ecc_dmp_disable))
  begin
    dc4_wq_addr0 =   {ca_mem_addr0_r[`npuarc_PADDR_MSB:2],  2'b00};
    // When there is bank01 or bank10 cross, a new entry will be created
    // in WQ. Hence wq_addr1 should be calculated accordingly.
    //
    casez ({dc4_bank10_cross, dc4_bank01_cross}) 
    2'b1?:   dc4_wq_addr1 = {dc4_mem_addr1_r[`npuarc_PADDR_MSB:2], 2'b00};
    2'b?1:   dc4_wq_addr1 = {ca_mem_addr0_r[`npuarc_PADDR_MSB:4],  4'b1000};
    default: dc4_wq_addr1 = {dc4_mem_addr1_r[`npuarc_PADDR_MSB:2], 2'b00};
    endcase
  end
  else
  begin
    dc4_wq_addr0 = ca_mem_addr0_r;
    dc4_wq_addr1 = dc4_mem_addr1_r;
  end
end

npuarc_alb_dmp_ecc_store_aligner u_alb_dmp_ecc_store_aligner (
  .addr_r        (ca_mem_addr0_r[2:0]),
  .size_r        (ca_size_r          ),
  .wr_data_r     (ca_wr_data_r       ),
  .rd_data0      (dc4_rd_data0       ),
  .rd_data1      (dc4_rd_data1       ),
  
  .wq_ecc_data0  (wq_ecc_data0       ),
  .wq_ecc_data1  (wq_ecc_data1       ),

  .wr_data0_mask (wr_data_mask0      ), 
  .wr_data1_mask (wr_data_mask1      ) 
);

assign ca_store_byte   = (ca_size_r == 2'b00);
assign ca_store_half   = (ca_size_r == 2'b01);
assign ca_store_word   = (ca_size_r == 2'b10);
assign ca_store_double = (ca_size_r == 2'b11);
// spyglass enable_block W398
// spyglass enable_block STARC05-2.8.1.3
//////////////////////////////////////////////////////////////////////////////
//
// Data0 and Data1 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : ca_wr_data_qual_PROC 
  ca_wr_data_qual = {`npuarc_DOUBLE_SIZE{1'b0}};
  case (1'b1)
  ca_store_byte:   ca_wr_data_qual[7:0]  = ca_wr_data_r[7:0];
  ca_store_half:   ca_wr_data_qual[15:0] = ca_wr_data_r[15:0];
  ca_store_word:   ca_wr_data_qual[31:0] = ca_wr_data_r[31:0];
  ca_store_double: ca_wr_data_qual[63:0] = ca_wr_data_r[63:0];
// spyglass disable_block W193
// SMD: empty statement
// SJ:  empty defaults kept 
  default:;
// spyglass enable_block W193
  endcase
end
//////////////////////////////////////////////////////////////////////////////
//
// Data0 and Data1 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_data_PROC
  if (  dc4_target_dc_dccm
       & (  
             (ca_store_r & (|dc4_rmw_r))  
          |  (ca_load_r  & (|dc4_ecc_sb_error_r))
         )
     ) 
  begin
    // Incase of a single bit eror and when there is a bank cross,
    // the wr_data should be aligned to 64 bit banks.
    //
    if ( (|dc4_ecc_sb_error_r) & (dc4_bank_any_cross | dc4_bank10_cross) ) 
    begin
      casez(dc4_rd_data_sel)
      4'b0011,
      4'b0111:
      begin
         dc4_wq_data0 = {dc4_data_even_hi,  dc4_data_even_lo};
         dc4_wq_data1 = {dc4_data_odd_hi,   dc4_data_odd_lo };
      end
      4'b0110,
      4'b1110:
      begin
        dc4_wq_data0 = {dc4_data_even_hi, dc4_data_even_hi};
        dc4_wq_data1 = {dc4_data_odd_hi,  dc4_data_odd_lo };
      end
      4'b1100,
      4'b1101:
      begin
        dc4_wq_data0 = {dc4_data_odd_hi,  dc4_data_odd_lo };
        dc4_wq_data1 = {dc4_data_even_hi, dc4_data_even_lo};
      end
      default:  // 4'b1001, 4'b1011:
      begin
        dc4_wq_data0 = {dc4_data_odd_hi,  dc4_data_odd_hi };
        dc4_wq_data1 = {dc4_data_even_hi, dc4_data_even_lo};
      end
      endcase  
    end
    else
    begin
      dc4_wq_data0 = (|dc4_ecc_sb_error_r) ? ({{32{1'b0}}, dc4_rd_data0}) : wq_ecc_data0;
      dc4_wq_data1 = (|dc4_ecc_sb_error_r) ? ({{32{1'b0}}, dc4_rd_data1}) : wq_ecc_data1;
    end  
  end
  else
  begin
    dc4_wq_data0 = ca_wr_data_qual;
    dc4_wq_data1 = wq_data1;
  end
end

//
// assigning the mask
//
assign dc4_wq_ecc_data_mask0 = dc4_target_dc_dccm ? wr_data_mask0 : {8{1'b1}};
assign dc4_wq_ecc_data_mask1 = dc4_target_dc_dccm ? wr_data_mask1 : {8{1'b1}};
//////////////////////////////////////////////////////////////////////////////
//
// Bank0 and Bank1 selection
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_bank_PROC
  if (dc4_bank10_cross)
  begin
    dc4_wq_bank_lo0 = {dc4_data_bank_sel_lo_r[1], 1'b0};
    dc4_wq_bank_hi0 = {1'b1, 1'b0};
 
    dc4_wq_bank_lo1 = {1'b0, 1'b1};
    dc4_wq_bank_hi1 = {1'b0, dc4_data_bank_sel_hi_r[0]};
  end
  else if (  dc4_bank01_cross & dc4_target_dc_dccm
           & (
                 (ca_store_r & (|dc4_rmw_r))
              |  (ca_load_r  & (|dc4_ecc_sb_error_r))
             ) 
          ) 
  begin
    dc4_wq_bank_lo0 = {1'b0, dc4_data_bank_sel_lo_r[0]};
    dc4_wq_bank_hi0 = {1'b0, 1'b1};
    
    dc4_wq_bank_lo1 = {1'b1, 1'b0};
    dc4_wq_bank_hi1 = {dc4_data_bank_sel_hi_r[1], 1'b0};
  end
  else
  begin   
    dc4_wq_bank_lo0 = dc4_data_bank_sel_lo_r;
    dc4_wq_bank_hi0 = dc4_data_bank_sel_hi_r;
      
    dc4_wq_bank_lo1 = {1'b0, 1'b0};
    dc4_wq_bank_hi1 = {1'b0, 1'b0};
  end
end

//////////////////////////////////////////////////////////////////////////////
//
// Size0 and Size1 
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_size_PROC
  if (   dc4_target_dc_dccm
      & (
             (ca_store_r & (|dc4_rmw_r))
          |  (ca_load_r  & (|dc4_ecc_sb_error_r))
        )
     )  
  begin
    // When the start address is middle of Bank0-lo or Bank1-lo
    // This covers double-word, word and haf-word conditions
    //
    if (  ((&ca_size_r) & (!ca_mem_addr0_r[2])                         ) // double-word
        | (ca_size_r[1] & (!ca_mem_addr0_r[2]) & (dc4_bank_any_cross)  ) // word
        | (ca_size_r[0] & (!ca_mem_addr0_r[2]) & (&ca_mem_addr0_r[1:0])))// half-word
    begin
      dc4_wq_size0 = 3'b011;  
      dc4_wq_size1 = 3'b010;
    end
    // For 1110 and 1011, size1 should be double-word
    // 
    else if ((&ca_size_r) & dc4_rd_data_sel[3] & dc4_rd_data_sel[1])
    begin 
      dc4_wq_size0 = 3'b010;
      dc4_wq_size1 = 3'b011; 
    end
    else
    begin
      dc4_wq_size0 = 3'b010;    
      dc4_wq_size1 = 3'b010;
    end  
  end
  else
  begin
    dc4_wq_size0 = dc4_bank10_cross ? dc4_size0_r : {1'b0, ca_size_r};
    dc4_wq_size1 = dc4_size1_r;
  end
end

//////////////////////////////////////////////////////////////////////////////
//
// Target0 and Traget1
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_target_PROC
  dc4_wq_target0 = dc4_target_r;
  dc4_wq_target1 = dc4_target_r;
end

//////////////////////////////////////////////////////////////////////////////
//
// Way hit information
//
//////////////////////////////////////////////////////////////////////////////
always @*
begin : dc4_wq_way_PROC
  dc4_wq_way_hot0 = dc4_hit0_way_hot;
  dc4_wq_way_hot1 = dc4_dt_line_cross_r ? dc4_hit1_way_hot : dc4_hit0_way_hot;
end


endmodule // alb_dmp_pre_store_aligner
